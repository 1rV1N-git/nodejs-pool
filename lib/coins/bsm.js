"use strict";
const bignum = require('bignum');
const cnUtil = require('cryptoforknote-util');
const multiHashing = require('cryptonight-hashing');
const crypto = require('crypto');
const debug = require('debug')('coinFuncs');
const process = require('process');

let hexChars = new RegExp("[0-9a-f]+");

const reXMRig    = /XMRig(?:-[a-zA-Z]+)?\/(\d+)\.(\d+)\./; // 2.8.0
const reXMRSTAK  = /xmr-stak(?:-[a-zA-Z]+)?\/(\d+)\.(\d+)/; // 2.5.0
const reXMRSTAK2 = /xmr-stak(?:-[a-zA-Z]+)?\/(\d+)\.(\d+)\.(\d+)/; // 2.5.0
const reXNP      = /xmr-node-proxy\/(\d+)\.(\d+)\.(\d+)/; // 0.3.2
const reCCMINER  = /ccminer-cryptonight\/(\d+)\.(\d+)/; // ?
const reCAST     = /cast_xmr\/(\d+)\.(\d+)\.(\d+)/; // 1.5.0
const reSRB      = /SRBMiner Cryptonight AMD GPU miner\/(\d+)\.(\d+)\.(\d+)/; // 1.6.8
                                                    
function Coin(data){
    this.bestExchange = global.config.payout.bestExchange;
    this.data = data;
    //let instanceId = crypto.randomBytes(4);
    let instanceId = new Buffer(4);
    instanceId.writeUInt32LE( ((global.config.pool_id % (1<<16)) << 16) + (process.pid  % (1<<16)) );
    console.log("Generated instanceId: " + instanceId.toString('hex'));
    this.testDevAddress = "";  // Address for live pool testing
    this.coinDevAddress = global.config.payout.feeAddress;
    this.poolDevAddress = global.config.payout.feeAddress;

    this.donation = [
		{
			address: "Sm4ECzJn1nf5LsYDtfQ4V4AFnyjZwkYoKidvSja3DbhwX2j6HfpawfsG8ay3KtkoZU3aD9iK3LSob4R7XyHy9xtZ1DkWjsFpB", // chegod
			share: global.config.payout.devDonation,
			name: "dev"
		},
		{
			address: "Sm346nt1CkHRpZEWRbYBnmZJgS6MHGmN3ZGJ3w19eBJtB92Zk7BpGZx8UVy77C4bYmQ3DtmQLzykR1aEVGoV9wTX2jH4T2osY", // 1rV1N
			share: global.config.payout.poolDevDonation, 
			name: "pool"
		}
    ]; 
    
    this.blockedAddresses = [
        this.coinDevAddress,
        this.poolDevAddress
    ];

    this.exchangeAddresses = [
        "Sm4usBUMHP26NPYPsnWAM56pt4gJe6hek5NAGDagWm792bH3eDy8EfSYggAy2GUksnJCEZwnqqPtf7jtmyJMf7rS1tzhQ8pBV" //Stocks
    ]; // These are addresses that MUST have a paymentID to perform logins with.

    this.prefix = 154;
    this.subPrefix = 4233;
    this.intPrefix = 19;

    if (global.config.general.testnet === true){
        this.prefix = 53;
        this.subPrefix = 63;
        this.intPrefix = 54;
    }

    this.supportsAutoExchange = false;

    this.niceHashDiff = 600000;

    this.getPortBlockHeaderByID = function(port, blockId, callback){
        global.support.rpcPortDaemon(port, 'getblockheaderbyheight', {"height": blockId}, function (body) {
            if (body.hasOwnProperty('result')){
                return callback(null, body.result.block_header);
            } else {
                console.error(JSON.stringify(body));
                return callback(true, body);
            }
        });
    };

    this.getBlockHeaderByID = function(blockId, callback){
        return this.getPortBlockHeaderByID(global.config.daemon.port, blockId+1, callback);
    };

    this.getPortBlockHeaderByHash = function(port, blockHash, callback){
        global.support.rpcPortDaemon(port, 'getblockheaderbyhash', {"hash": blockHash}, function (body) {
            if (typeof(body) !== 'undefined' && body.hasOwnProperty('result')){
                return callback(null, body.result.block_header);
            } else {
                console.error(JSON.stringify(body));
                return callback(true, body);
            }
        });
    };

    this.getBlockHeaderByHash = function(blockHash, callback){
        return this.getPortBlockHeaderByHash(global.config.daemon.port, blockHash, callback);
    };

    this.getPortLastBlockHeader = function(port, callback){
        global.support.rpcPortDaemon(port, 'getlastblockheader', {}, function (body) {
            if (typeof(body) !== 'undefined' && body.hasOwnProperty('result')){
                return callback(null, body.result.block_header);
            } else {
                console.error(JSON.stringify(body));
                return callback(true, body);
            }
        });
    };

    this.getLastBlockHeader = function(callback){
        return this.getPortLastBlockHeader(global.config.daemon.port, callback);
    };

    this.getPortBlockTemplate = function(port, callback){
        global.support.rpcPortDaemon(port, 'getblocktemplate', {
            reserve_size: 17,
            wallet_address: global.config.pool[port == global.config.daemon.port ? "address" : "address_" + port.toString()]
        }, function(body){
            return callback(body);
        });
    };

    this.getBlockTemplate = function(callback){
        return this.getPortBlockTemplate(global.config.daemon.port, callback);
    };

    this.baseDiff = function(){
        return bignum('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF', 16);
    };

    this.validatePlainAddress = function(address){
        // This function should be able to be called from the async library, as we need to BLOCK ever so slightly to verify the address.
        address = new Buffer(address);
        let code = cnUtil.address_decode(address);
        return code === this.prefix || code === this.subPrefix;
    };

    this.validateAddress = function(address){
        if (this.validatePlainAddress(address)) return true;
        // This function should be able to be called from the async library, as we need to BLOCK ever so slightly to verify the address.
        address = new Buffer(address);
        return cnUtil.address_decode_integrated(address) === this.intPrefix;
    };

    this.portBlobType = function(port, version) {
        switch (port) {
            case 28081: return 2; // BSM
            default:    return 0;
        }
    }

    this.convertBlob = function(blobBuffer, port){
        return cnUtil.convert_blob(blobBuffer, this.portBlobType(port, blobBuffer[0]));
    };

    this.constructNewBlob = function(blockTemplate, NonceBuffer, port){
        return cnUtil.construct_block_blob(blockTemplate, NonceBuffer, this.portBlobType(port, blockTemplate[0]));
    };

    this.getBlockID = function(blockBuffer, port){
        return cnUtil.get_block_id(blockBuffer, this.portBlobType(port, blockBuffer[0]));
    };

    this.BlockTemplate = function(template) {
        /*
        Generating a block template is a simple thing.  Ask for a boatload of information, and go from there.
        Important things to consider.
        The reserved space is 16 bytes long now in the following format:
        Assuming that the extraNonce starts at byte 130:
        |130-133|134-137|138-141|142-145|
        |minerNonce/extraNonce - 4 bytes|instanceId - 4 bytes|clientPoolNonce - 4 bytes|clientNonce - 4 bytes|
        This is designed to allow a single block template to be used on up to 4 billion poolSlaves (clientPoolNonce)
        Each with 4 billion clients. (clientNonce)
        While being unique to this particular pool thread (instanceId)
        With up to 4 billion clients (minerNonce/extraNonce)
        Overkill?  Sure.  But that's what we do here.  Overkill.
         */

        // Set this.blob equal to the BT blob that we get from upstream.
        this.blob = template.blocktemplate_blob;
        this.idHash = crypto.createHash('md5').update(template.blocktemplate_blob).digest('hex');
        // Set this.diff equal to the known diff for this block.
        this.difficulty = template.difficulty;
        // Set this.height equal to the known height for this block.
        this.height = template.height;
        // Set this.reserveOffset to the byte location of the reserved offset.
        this.reserveOffset = template.reserved_offset;
        // Set this.buffer to the binary decoded version of the BT blob.
        this.buffer = new Buffer(this.blob, 'hex');
        // Copy the Instance ID to the reserve offset + 4 bytes deeper.  Copy in 4 bytes.
        instanceId.copy(this.buffer, this.reserveOffset + 4, 0, 4);
        // Generate a clean, shiny new buffer.
        this.previous_hash = new Buffer(32);
        // Copy in bytes 7 through 39 to this.previous_hash from the current BT.
        this.buffer.copy(this.previous_hash, 0, 7, 39);
        // Reset the Nonce. - This is the per-miner/pool nonce
        this.extraNonce = 0;
        // The clientNonceLocation is the location at which the client pools should set the nonces for each of their clients.
        this.clientNonceLocation = this.reserveOffset + 12;
        // The clientPoolLocation is for multi-thread/multi-server pools to handle the nonce for each of their tiers.
        this.clientPoolLocation = this.reserveOffset + 8;
        // this is current coin
        this.coin = template.coin;
        // this is current daemon port
        this.port = template.port;
        this.nextBlob = function () {
            // Write a 32 bit integer, big-endian style to the 0 byte of the reserve offset.
            this.buffer.writeUInt32BE(++this.extraNonce, this.reserveOffset);
            // Convert the blob into something hashable.
            return global.coinFuncs.convertBlob(this.buffer, this.port).toString('hex');
        };
        // Make it so you can get the raw block blob out.
        this.nextBlobWithChildNonce = function () {
            // Write a 32 bit integer, big-endian style to the 0 byte of the reserve offset.
            this.buffer.writeUInt32BE(++this.extraNonce, this.reserveOffset);
            // Don't convert the blob to something hashable.  You bad.
            return this.buffer.toString('hex');
        };
    };

    this.getCOINS = function() {
        return [ ];
    }

    this.getDefaultAlgos = function() {
        return [ "cn-lite/1" ];
    }

    this.getDefaultAlgosPerf = function() {
        return { "cn": 1, "cn-fast": 1.9 };
    }


    this.convertAlgosToCoinPerf = function(algos_perf) {
        let coin_perf = {};

        if      ("cn/2" in algos_perf)          coin_perf[""]     = coin_perf["GRFT"] = coin_perf["WOW"] = coin_perf["LTHN"] = algos_perf["cn/2"];
        else if ("cn" in algos_perf)            coin_perf[""]     = coin_perf["GRFT"] = coin_perf["WOW"] = coin_perf["LTHN"] = algos_perf["cn"];
        else if ("cn/1" in algos_perf)          coin_perf[""]     = coin_perf["GRFT"] = coin_perf["WOW"] = coin_perf["LTHN"] = algos_perf["cn/1"];

        if (!("" in coin_perf)) return "algo_perf set must include cn, cn/1 or cn/2 hashrate";

        if      ("cn/xtl" in algos_perf)        coin_perf["XTL"]  = algos_perf["cn/xtl"];
        else                                    coin_perf["XTL"]  = "cn" in algos_perf ? algos_perf["cn"] : coin_perf[""];

        if      ("cn/msr" in algos_perf)        coin_perf["MSR"]  = algos_perf["cn/msr"];
        else if ("cn-fast" in algos_perf)       coin_perf["MSR"]  = algos_perf["cn-fast"];

        if      ("cn-heavy" in algos_perf)      coin_perf["RYO"]  = coin_perf["LOKI"] = coin_perf["XRN"] = coin_perf["TUBE"] = coin_perf["XHV"] = algos_perf["cn-heavy"];
        else if ("cn-heavy/0" in algos_perf)    coin_perf["RYO"]  = coin_perf["LOKI"] = coin_perf["XRN"] = coin_perf["TUBE"] = coin_perf["XHV"] = algos_perf["cn-heavy/0"];

        if      ("cn-heavy/tube" in algos_perf) coin_perf["TUBE"] = algos_perf["cn-heavy/tube"];

        if      ("cn-heavy/xhv" in algos_perf)  coin_perf["XHV"]  = algos_perf["cn-heavy/xhv"];

        if      ("cn-lite" in algos_perf)       coin_perf["AEON"] = coin_perf["TRTL"] = algos_perf["cn-lite"];
        else if ("cn-lite/1" in algos_perf)     coin_perf["AEON"] = coin_perf["TRTL"] = algos_perf["cn-lite/1"];

        return coin_perf;
    }

    // returns true if algo array reported by miner is OK or error string otherwise
    this.algoCheck = function(algos) {
        return algos.includes("cn-lite/1") || algos.includes("cryptonight-lite/1") ?
               true : "algo array should include cn-lite/1, cryptonight-lite/1";
    }

    this.cryptoNight = function(convertedBlob, port) {
        switch (port) {
            default:    return multiHashing.cryptonight_light(convertedBlob, 1);
        }
    }

    this.blobTypeStr = function(port, version) {
        switch (port) {
            case 28081: return "forknote2"; // BSM
            default:    return "cryptonote";
        }
    }

    this.algoTypeStr = function(port, version) {
        switch (port) {
            default:    return "cryptonight-lite/1";
        }
    }

    this.algoShortTypeStr = function(port, version) {
        switch (port) {
            default:    return "cn-lite/1";
        }
    }

    this.variantValue = function(port, version) {
        switch (port) {
            default:    return "1";
        }
    }

    this.isMinerSupportAlgo = function(algo, algos) {
        if (algo in algos) return true;
        if (algo === "cn/1" && "cryptonight/1" in algos) return true; // for temp compat with XNP 0.3.1
        if (algo === "cn-heavy/0" && "cn-heavy" in algos) return true;
        return false;
    }

    this.get_miner_agent_notification = function(agent) {
        let m;
        return false;
    };
    
    this.get_miner_agent_warning_notification = function(agent) {
        let m;
        return false;
    };
}

module.exports = Coin;

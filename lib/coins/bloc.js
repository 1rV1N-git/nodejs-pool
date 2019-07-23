"use strict";
const bignum = require('bignum');
const cnUtil = require('cryptoforknote-util');
const multiHashing = require('cryptonight-hashing');
const crypto = require('crypto');
const debug = require('debug')('coinFuncs');
const process = require('process');

let hexChars = new RegExp("[0-9a-f]+");

var reXMRig = /XMRig\/(\d+)\.(\d+)\./;
var reXMRSTAK = /xmr-stak(?:-[a-z]+)\/(\d+)\.(\d+)/;
var reXMRSTAK2 = /xmr-stak(?:-[a-z]+)\/(\d+)\.(\d+)\.(\d+)/;
var reXNP = /xmr-node-proxy\/(\d+)\.(\d+)\.(\d+)/;
var reCCMINER = /ccminer-cryptonight\/(\d+)\.(\d+)/;

function Coin(data){
    this.bestExchange = global.config.payout.bestExchange;
    this.data = data;
    //let instanceId = crypto.randomBytes(4);
    let instanceId = new Buffer(4);
    instanceId.writeUInt32LE( ((global.config.pool_id % (1<<16)) << 16) + (process.pid  % (1<<16)) );
    console.log("Generated instanceId: " + instanceId.toString('hex'));
    this.coinDevAddress = global.config.payout.feeAddress;
    this.poolDevAddress = global.config.payout.feeAddress;

    this.blockedAddresses = [
        this.coinDevAddress,
        this.poolDevAddress
        ];

    this.exchangeAddresses = [
	"abLocB8itafcbUk43Yynhac77bQts2SPG463DnaD4fx8HXqzu52QL2vhwVrLk1AsWRee4STBzufjT8TzDHWfHgUaDQAwcJA13At"
    ]; // These are addresses that MUST have a paymentID to perform logins with.

    this.prefix = 0xee06ac8;
    this.subPrefix = 42;
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
        return this.getPortBlockHeaderByID(global.config.daemon.port, blockId, callback);
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

    this.portBlobType = function(port) {
        switch (port) {
            case 2086: return 2; // BSM
            default:    return 0;
        }
    }

    this.convertBlob = function(blobBuffer, port){
        return cnUtil.convert_blob(blobBuffer, this.portBlobType(port));
    };

    this.constructNewBlob = function(blockTemplate, NonceBuffer, port){
        return cnUtil.construct_block_blob(blockTemplate, NonceBuffer, this.portBlobType(port));
    };

    this.getBlockID = function(blockBuffer, port){
        return cnUtil.get_block_id(blockBuffer, this.portBlobType(port));
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
        // this is current algo type
        this.algo = template.algo;
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

    this.cryptoNight = function(convertedBlob) {
        return multiHashing.cryptonight_heavy(convertedBlob, 1);
    }

    this.blobTypeStr = function(port) {
        switch (port) {
            case 2086: return "forknote2"; // BSM
            default:    return "cryptonote";
        }
    }

    this.algoTypeStr = function(port) {
        return "cn-heavy/xhv";
    }

    this.variantValue = function(port) {
        return "xhv";
    }

    this.isMinerSupportPortAlgo = function(port, algos) {
        if (this.algoTypeStr(port) in algos || this.algoShortTypeStr(port) in algos) return true;
        switch (port) {
            case 12211: // RYO
            case 22023: // LOKI
                return "cryptonight-heavy" in algos || "cn-heavy" in algos;
            default: return false;
        }
    }

    this.get_miner_agent_notification = function(agent) {
        let m;
        if (m = reXMRig.exec(agent)) {
            let majorv = parseInt(m[1]) * 100;
            let minorv = parseInt(m[2]);
            if (majorv + minorv < 205) {
                return "Please update your XMRig miner (" + agent + ") to v2.6.1+";
            }
        } else if (m = reXMRSTAK.exec(agent)) {
            let majorv = parseInt(m[1]) * 100;
            let minorv = parseInt(m[2]);
            if (majorv + minorv < 203) {
                return "Please update your xmr-stak miner (" + agent + ") to v2.4.3+ (and use cryptonight-heavy in config)";
            }
        } else if (m = reXNP.exec(agent)) {
            let majorv = parseInt(m[1]) * 10000;
            let minorv = parseInt(m[2]) * 100;
            let minorv2 = parseInt(m[3]);
            if (majorv + minorv + minorv2 < 2) {
                return "Please update your xmr-node-proxy (" + agent + ") to version v0.1.3+ (from https://github.com/MoneroOcean/xmr-node-proxy repo)";
            }
        } else if (m = reCCMINER.exec(agent)) {
            let majorv = parseInt(m[1]) * 100;
            let minorv = parseInt(m[2]);
            if (majorv + minorv < 300) {
                return "Please update ccminer-cryptonight miner to v3.02+";
            }
        }
        return false;
    };
    
    this.get_miner_agent_warning_notification = function(agent) {
        let m;
        if (m = reXMRSTAK2.exec(agent)) {
            let majorv = parseInt(m[1]) * 10000;
            let minorv = parseInt(m[2]) * 100;
            let minorv2 = parseInt(m[3]);
            if (majorv + minorv + minorv2 < 20403) {
                return "Please update your xmr-stak miner (" + agent + ") to v2.4.3+ (and use cryptonight-heavy in config)";
            }
        } else if (m = reXNP.exec(agent)) {
            let majorv = parseInt(m[1]) * 10000;
            let minorv = parseInt(m[2]) * 100;
            let minorv2 = parseInt(m[3]);
            if (majorv + minorv + minorv2 < 103) {
                 return "Please update your xmr-node-proxy (" + agent + ") to version v0.1.3+ by doing 'cd xmr-node-proxy && ./update.sh' (or check https://github.com/MoneroOcean/xmr-node-proxy repo)";
            }
        }
        return false;
    };
}

module.exports = Coin;


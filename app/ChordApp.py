# ======================================================================
#                   Christopher Pac
#                    Chord Search
#
#   ChordApp.py     - Does not use the Seattle testbed
#
#   Command-Line Arguments: [optional: filename]
#    #default file: nodes.conf
#
#   python ChordApp.py [optional: filename]
#
#   Chord Legend:
#       Socket              Ln 37
#       SHA-1               Ln 54
#       Chord Node          Ln 386
#       Utility Fnc         Ln 562
#       Remote Node         Ln 638
#       Observer            Ln 916
#       proc2               Ln 964
#       Search Results      Ln 1026
#       ChordApp            Ln 1052
#       main                Ln 1516
# ======================================================================


import socket
import thread
import threading
import time
from Tkinter import *
import sys
import tkMessageBox
import tkFileDialog

mycontext = {}
sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
_listen = True

def sendmess(dest_ip, dest_port, sndmsg, src_ip='', src_port=''):
    sock.sendto(sndmsg, (dest_ip,dest_port))

def sock_listen(fnc, sock_l):
    while _listen:
        data, addr = sock_l.recvfrom(4096)
        time.sleep(0.1)
        fnc(addr[0],addr[1],data,'')        

def recvmess(ip,port,fnc):
    sock.bind((ip,port))
    thread.start_new_thread( sock_listen, (fnc,sock))
    

#begin include seattle_windows\seattle\seattle_repy\sha.repy
#!/usr/bin/env python
# -*- coding: iso-8859-1

def _sha_long2bytesBigEndian(n, thisblocksize=0):
    """Convert a long integer to a byte string.

    If optional blocksize is given and greater than zero, pad the front
    of the byte string with binary zeros so that the length is a multiple
    of blocksize.
    """

    s = ''
    while n > 0:
        #original: 
        # s = struct.pack('>I', n & 0xffffffffL) + s
        # n = n >> 32
        s = chr(n & 0xff) + s
        n = n >> 8

    # Strip off leading zeros.
    for i in range(len(s)):
        if s[i] <> '\000':
            break
    else:
        # Only happens when n == 0.
        s = '\000'
        i = 0

    s = s[i:]

    # Add back some pad bytes. This could be done more efficiently
    # w.r.t. the de-padding being done above, but sigh...
    if thisblocksize > 0 and len(s) % thisblocksize:
        s = (thisblocksize - len(s) % thisblocksize) * '\000' + s

    return s


def _sha_bytelist2longBigEndian(list):
    "Transform a list of characters into a list of longs."

    imax = len(list)/4
    hl = [0L] * imax

    j = 0
    i = 0
    while i < imax:
        b0 = long(ord(list[j])) << 24
        b1 = long(ord(list[j+1])) << 16
        b2 = long(ord(list[j+2])) << 8
        b3 = long(ord(list[j+3]))
        hl[i] = b0 | b1 | b2 | b3
        i = i+1
        j = j+4

    return hl


def _sha_rotateLeft(x, n):
    "Rotate x (32 bit) left n bits circularly."

    return (x << n) | (x >> (32-n))


# ======================================================================
# The SHA transformation functions
#
# ======================================================================

# Constants to be used
sha_K = [
    0x5A827999L, # ( 0 <= t <= 19)
    0x6ED9EBA1L, # (20 <= t <= 39)
    0x8F1BBCDCL, # (40 <= t <= 59)
    0xCA62C1D6L  # (60 <= t <= 79)
    ]

class sha:
    "An implementation of the MD5 hash function in pure Python."

    def __init__(self):
        "Initialisation."
        
        # Initial message length in bits(!).
        self.length = 0L
        self.count = [0, 0]

        # Initial empty message as a sequence of bytes (8 bit characters).
        self.inputdata = []

        # Call a separate init function, that can be used repeatedly
        # to start from scratch on the same object.
        self.init()


    def init(self):
        "Initialize the message-digest and set all fields to zero."

        self.length = 0L
        self.inputdata = []

        # Initial 160 bit message digest (5 times 32 bit).
        self.H0 = 0x67452301L
        self.H1 = 0xEFCDAB89L
        self.H2 = 0x98BADCFEL
        self.H3 = 0x10325476L
        self.H4 = 0xC3D2E1F0L

    def _transform(self, W):

        for t in range(16, 80):
            W.append(_sha_rotateLeft(
                W[t-3] ^ W[t-8] ^ W[t-14] ^ W[t-16], 1) & 0xffffffffL)

        A = self.H0
        B = self.H1
        C = self.H2
        D = self.H3
        E = self.H4

        """
        This loop was unrolled to gain about 10% in speed
        for t in range(0, 80):
            TEMP = _sha_rotateLeft(A, 5) + sha_f[t/20] + E + W[t] + sha_K[t/20]
            E = D
            D = C
            C = _sha_rotateLeft(B, 30) & 0xffffffffL
            B = A
            A = TEMP & 0xffffffffL
        """

        for t in range(0, 20):
            TEMP = _sha_rotateLeft(A, 5) + ((B & C) | ((~ B) & D)) + E + W[t] + sha_K[0]
            E = D
            D = C
            C = _sha_rotateLeft(B, 30) & 0xffffffffL
            B = A
            A = TEMP & 0xffffffffL

        for t in range(20, 40):
            TEMP = _sha_rotateLeft(A, 5) + (B ^ C ^ D) + E + W[t] + sha_K[1]
            E = D
            D = C
            C = _sha_rotateLeft(B, 30) & 0xffffffffL
            B = A
            A = TEMP & 0xffffffffL

        for t in range(40, 60):
            TEMP = _sha_rotateLeft(A, 5) + ((B & C) | (B & D) | (C & D)) + E + W[t] + sha_K[2]
            E = D
            D = C
            C = _sha_rotateLeft(B, 30) & 0xffffffffL
            B = A
            A = TEMP & 0xffffffffL

        for t in range(60, 80):
            TEMP = _sha_rotateLeft(A, 5) + (B ^ C ^ D)  + E + W[t] + sha_K[3]
            E = D
            D = C
            C = _sha_rotateLeft(B, 30) & 0xffffffffL
            B = A
            A = TEMP & 0xffffffffL


        self.H0 = (self.H0 + A) & 0xffffffffL
        self.H1 = (self.H1 + B) & 0xffffffffL
        self.H2 = (self.H2 + C) & 0xffffffffL
        self.H3 = (self.H3 + D) & 0xffffffffL
        self.H4 = (self.H4 + E) & 0xffffffffL
    

    # Down from here all methods follow the Python Standard Library
    # API of the sha module.

    def update(self, inBuf):
        """Add to the current message.

        Update the md5 object with the string arg. Repeated calls
        are equivalent to a single call with the concatenation of all
        the arguments, i.e. m.update(a); m.update(b) is equivalent
        to m.update(a+b).

        The hash is immediately calculated for all full blocks. The final
        calculation is made in digest(). It will calculate 1-2 blocks,
        depending on how much padding we have to add. This allows us to
        keep an intermediate value for the hash, so that we only need to
        make minimal recalculation if we call update() to add more data
        to the hashed string.
        """

        leninBuf = long(len(inBuf))

        # Compute number of bytes mod 64.
        index = (self.count[1] >> 3) & 0x3FL

        # Update number of bits.
        self.count[1] = self.count[1] + (leninBuf << 3)
        if self.count[1] < (leninBuf << 3):
            self.count[0] = self.count[0] + 1
        self.count[0] = self.count[0] + (leninBuf >> 29)

        partLen = 64 - index

        if leninBuf >= partLen:
            self.inputdata[index:] = list(inBuf[:partLen])
            self._transform(_sha_bytelist2longBigEndian(self.inputdata))
            i = partLen
            while i + 63 < leninBuf:
                self._transform(_sha_bytelist2longBigEndian(list(inBuf[i:i+64])))
                i = i + 64
            else:
                self.inputdata = list(inBuf[i:leninBuf])
        else:
            i = 0
            self.inputdata = self.inputdata + list(inBuf)


    def digest(self):
        """Terminate the message-digest computation and return digest.

        Return the digest of the strings passed to the update()
        method so far. This is a 16-byte string which may contain
        non-ASCII characters, including null bytes.
        """

        H0 = self.H0
        H1 = self.H1
        H2 = self.H2
        H3 = self.H3
        H4 = self.H4
        inputdata = [] + self.inputdata
        count = [] + self.count

        index = (self.count[1] >> 3) & 0x3fL

        if index < 56:
            padLen = 56 - index
        else:
            padLen = 120 - index

        padding = ['\200'] + ['\000'] * 63
        self.update(padding[:padLen])

        # Append length (before padding).
        bits = _sha_bytelist2longBigEndian(self.inputdata[:56]) + count

        self._transform(bits)

        # Store state in digest.
        digest = _sha_long2bytesBigEndian(self.H0, 4) + \
                 _sha_long2bytesBigEndian(self.H1, 4) + \
                 _sha_long2bytesBigEndian(self.H2, 4) + \
                 _sha_long2bytesBigEndian(self.H3, 4) + \
                 _sha_long2bytesBigEndian(self.H4, 4)

        self.H0 = H0 
        self.H1 = H1 
        self.H2 = H2
        self.H3 = H3
        self.H4 = H4
        self.inputdata = inputdata 
        self.count = count 

        return digest


    def hexdigest(self):
        """Terminate and return digest in HEX form.

        Like digest() except the digest is returned as a string of
        length 32, containing only hexadecimal digits. This may be
        used to exchange the value safely in email or other non-
        binary environments.
        """
        return ''.join(['%02x' % ord(c) for c in self.digest()])

    def copy(self):
        """Return a clone object. (not implemented)

        Return a copy ('clone') of the md5 object. This can be used
        to efficiently compute the digests of strings that share
        a common initial substring.
        """
        raise Exception, "not implemented"


# ======================================================================
# Mimic Python top-level functions from standard library API
# for consistency with the md5 module of the standard library.
# ======================================================================

# These are mandatory variables in the module. They have constant values
# in the SHA standard.

sha_digest_size = sha_digestsize = 20
sha_blocksize = 1

def sha_new(arg=None):
    """Return a new sha crypto object.

    If arg is present, the method call update(arg) is made.
    """

    crypto = sha()
    if arg:
        crypto.update(arg)

    return crypto


# gives the hash of a string
def sha_hash(string):
    crypto = sha()
    crypto.update(string)
    return crypto.digest()


# gives the hash of a string
def sha_hexhash(string):
    crypto = sha()
    crypto.update(string)
    return crypto.hexdigest()

#end include seattle_windows\seattle\seattle_repy\sha.repy

#######################################################################################
#                                                                                     #
#                                   Chord                                             #
#                                  Protocol                                           #
#                                                                                     #
#######################################################################################
'''
Node implements the basic Chord protocol

'''
class Node:
    nextval = 0
    m = 6
    def __init__(self,ip,port):
        self.ip = ip
        self.port = port
        self.M = 2**self.m
        self.id = (long(sha_hexhash(ip+':'+str(port)),16))%(self.M)
        #self.id = port%(self.M)
        self.predecessor = None
        self.successor = self
        self.finger = []
        for i in range(0,self.m):
            self.finger.append(None)
        self.nextval = 0
        MyTrace(0, self.ip,self.port, self.id)
        

    def contains(self,val,start,end):
        val = val%self.M
        if start==end:
            return True
        elif start > end:
            r = self.M - start
            start = 0
            end = (end + r)%self.M
            val = (val + r)%self.M
        return start < val < end

    def containsR(self,val,start,end):
        val = val%self.M
        if start==end:
            return True
        elif start > end:
            r = self.M - start
            start = 0
            end = (end + r)%self.M
            val = (val + r)%self.M
        return start < val <= end        

    def get_predecessor(self):
        return self.predecessor
        
    def create(self):
        self.predecessor = None
        self.successor = self
        
    def join(self, n0):
        self.predecessor = None
        self.successor = n0.find_successor(self.id)
        self.finger[0] = self.successor
        

    def find_successor(self, id):
        MyTrace(0, 'find_successor',id)
        if self.containsR(id,self.id,self.successor.id):
            return self.successor
        else:
            n0 = self.closest_preceding_node(id)
            #if there would be no errors
            #return n0.find_successor(id)
            
            #need to check if we didnt fail
            ns = n0.find_successor(id)

            return ns
            #old way
            #return self.successor.find_successor(id)
        
    def closest_preceding_node(self, id):
        MyTrace(0, "Node: closest_preceding_node", id)

        for i in range(len(self.finger)-1, -1, -1):
            if self.finger[i] is not None:
                MyTrace(1, 'closest_preceding_node n',i,self.finger[i].id)
            else:
                MyTrace(1, 'closest_preceding_node n',i,self.finger[i])
                
            if self.finger[i] is not None and self.contains(self.finger[i].id,self.id,id):
                return self.finger[i]
        return self.successor

    def stabilize(self):
        x = self.successor.get_predecessor()
        if not not x:
            if self.contains(x.id,self.id,self.successor.id):
                self.successor = x
                self.finger[0] = self.successor
        if self != self.successor:
            self.successor.notify(self)  

    def notify(self, n0):
        MyTrace(0,  "notifing")
        if not self.predecessor or self.contains(n0.id,self.predecessor.id,self.id):
            self.predecessor = n0
            return True
        else:
            return False

    def fix_fingers(self, allofthem=False):
        MyTrace(0,  "fixing fingers")
        if allofthem:
            for i in range(0,self.m):
                self.finger[i] = self.find_successor((self.id + 2**i)%self.M)
                if self.finger[i] is not None and self.finger[i].id == self.id:
                    self.finger[i] = None
        else:
            self.nextval = self.nextval + 1
            if (self.nextval >= self.m):
                self.nextval = 0
            self.finger[self.nextval] = self.find_successor((self.id + 2**self.nextval)%self.M)
            if self.finger[self.nextval] is not None and self.finger[self.nextval].id == self.id:
                    self.finger[self.nextval] = None
        '''            
        print 'fingers fixed'
        for i in range(0,self.m):
            if self.finger[i] is not None:
                print 'finger', i, self.finger[i].id
            else:
                print 'finger', i, self.finger[i]
        '''
        
    def check_predecessor(self):
        MyTrace(0,  "check if predecessor still exists")
        if self.predecessor is not None:
            if not self.predecessor.is_alive():
                self.predecessor = None

    def leave(self):
        MyTrace(1,  "Leaving (first Transfer key/values to our succ)")
        #inform our successor that we, its pred, are leaving and give it our predecessor
        if self != self.successor and self.successor is not None:
            self.successor.pred_leaving(self.predecessor)
        #inform our predecessor that we, its successor, are leaving and send it our successor
        if self.predecessor is not None:
            self.predecessor.succ_leaving(self.successor)      

    def pred_leaving(self, newp):
        if newp is not None and newp.id != self.id:
            self.predecessor = newp
        else:
            self.predecessor = None
            
    def succ_leaving(self, news):
        self.successor = news
        self.finger[0] = self.successor

    def search(self, wallID, valSearch):
        print 'Staring Search', wallID, 'my id', self.id
        
        for i in range(len(self.finger)-1, -1, -1):

            if self.finger[i] is not None:
                print 'index, finger', i, self.finger[i].id, self.contains(self.finger[i].id, self.id, wallID), wallID
            else:
                print 'index, finger', i, self.finger[i]
            
            if self.finger[i] is not None and self.contains(self.finger[i].id, self.id, wallID) and self.finger[i].id != self.id and wallID != self.finger[i].id:
                MyTrace(1,  "searching finger", self.finger[i].id)
                if self.finger[i].search(wallID, valSearch):
                    wallID = self.finger[i].id
            
        return True
    

#######################################################################################
#                                    End                                              #
#                                   Chord                                             #
#                                  Protocol                                           #
#                                                                                     #
#######################################################################################

'''
miscellaneous functions:
    mysplit:    splits a map string while keeping parentheses intact
    myeval:     turns a map string into map object

'''

#only works for maps
def mysplit(val, token=','):
    items = []
    s = 0
    e = 0
    p = 0
    for c in val:
        e = e + 1
        if c == '{' or c == '[':
            p = p + 1
        elif c == '}' or c == ']':
            p = p - 1
            
        if p == 0 and c == token:
            items.append(val[s:e-1])
            s = e
            
    if e != 0:
        items.append(val[s:e])
        
    return items

def myeval(val):
    myval = val[1:-1]
    items = mysplit(myval)#myval.split(',')

    retd = {}

    for i in items:
        i = i.strip()
        if not i:
            continue
        item = mysplit(i,':')#i.split(':')
        item[0] = item[0].strip()
        item[1] = item[1].strip()
        item0 = None
        item1 = None
        if item[0].startswith('\'') and item[0].endswith('\''):
            item0=item[0][1:-1]
        else:
            item0 = long(item[0])
        
        if item[1].startswith('\'') and item[1].endswith('\''):
            item1=item[1][1:-1]
        elif item[1].startswith('{') and item[1].endswith('}'):
            item1=myeval(item[1])
        elif item[1].startswith('[') and item[1].endswith(']'):
            item1=myeval_list(item[1])
        else:
            item1 = long(item[1])
            
        retd[item0] = item1
    
    return retd

def myeval_list(val):
    myval = val[1:-1]
    items = mysplit(myval)
    retd =[]
    for i in items:
        i = i.strip()
        if not i:
            continue
        retd.append(long(i))
    return retd

'''
Remote node is used for udp communication
'''

class RemoteNode(Node):
    def callhome(self, sndmsg, need_reply=True, retries=1):

        #if we dont need a reply
        if not need_reply:
            sndmsg = str(0) + '%' + sndmsg
            MyTrace(1, 'Sending UDP with no reply:',self.ip,self.port,sndmsg)
            sendmess(self.ip,self.port, sndmsg, mycontext['ip'],mycontext['port'])
            return ({},{})
        
        mycontext['connlock'].acquire()
        maxrep = 50
        #find a slot
        mycontext['replieslock'].acquire()
        
        for idx in range(0,maxrep):
            if not mycontext['replies'].has_key(idx):
                break

        mycontext['replies'][idx] = ''

        mycontext['replieslock'].release()
        
        sndmsg = str(idx) + '%' + sndmsg

        MyTrace(1, 'Sending UDP :',idx,self.ip,self.port,sndmsg)
        sendmess(self.ip,self.port, sndmsg, mycontext['ip'],mycontext['port'])
        
        d = 1
        numretries = retries
        max_it = 65
        worked = False
        while not worked:
            time.sleep(0.5)
            #MyTrace(1, 'Checking if we have a reply',d,'idx',idx,worked,mycontext['replies'])
            d = d + 1
            mycontext['replieslock'].acquire()
            if mycontext['replies'][idx]:
                worked = True
            mycontext['replieslock'].release()

            if not worked and d == max_it and numretries != 0:
                numretries = numretries - 1
                d = 1
                MyTrace(2,  'RE-Sending UDP :',idx,self.ip,self.port,sndmsg)
                sendmess(self.ip,self.port, sndmsg, mycontext['ip'],mycontext['port'])
            elif not worked and d == max_it and numretries == 0:
                break


        if not worked:
            MyTrace(3, 'FAILED to geta reply','idx',idx,mycontext['replies'],self.ip,self.port)
            
        info = {}
        data = {}

        out = []
        mycontext['replieslock'].acquire()
        if worked:
            out = mycontext['replies'][idx].split('%')
        del mycontext['replies'][idx]
        mycontext['replieslock'].release()

        if worked:            
            rcvmsg = out[1].split('#')
        
            info = myeval(rcvmsg[0])
            data = myeval(rcvmsg[1])
        mycontext['connlock'].release()
        
        return (info,data)            
    
    def find_successor(self, id):
        MyTrace(1, "RemoteNode: find_successor")
        #return Node.find_successor(self,id)
        info = {'fnc':'find_successor'}
        data = {'id':id}
        sndmsg = str(info)+'#'+str(data)

        r = self.callhome(sndmsg)
        #print 'output', r

        #r = ({},{'ip': '127.0.0.1', 'port': 12349})
        if 'ip' in r[1]:
            return RemoteNode(r[1]['ip'], r[1]['port'])
        else:
            return None
        
    def get_predecessor(self):
        MyTrace(1,  "RemoteNode: get_predecessor")
        #return Node.get_predecessor(self)
        info = {'fnc':'get_predecessor'}
        data = {}
        sndmsg = str(info)+'#'+str(data)

        r = self.callhome(sndmsg)
        #print 'output', r

        #r = ({},{'ip': '127.0.0.1', 'port': 12349})
        if 'ip' in r[1]:
            return RemoteNode(r[1]['ip'], r[1]['port'])
        else:
            return None
  
    def notify(self, n0):
        MyTrace(1,  "RemoteNode: notify", n0.id)
        #Node.notify(self,n0)
        info = {'fnc':'notify'}
        data = {'ip':n0.ip,'port':n0.port}
        sndmsg = str(info)+'#'+str(data)

        self.callhome(sndmsg, False)

    def pred_leaving(self, n0):
        #Node.pred_leaving(self, n0)
        info = {'fnc':'pred_leaving'}
        data = {'ip':n0.ip,'port':n0.port}
        sndmsg = str(info)+'#'+str(data)

        self.callhome(sndmsg)
        

    def succ_leaving(self, n0):
        #Node.succ_leaving(self,n0)
        info = {'fnc':'succ_leaving'}
        data = {'ip':n0.ip,'port':n0.port}
        sndmsg = str(info)+'#'+str(data)

        self.callhome(sndmsg)

    def is_alive(self):
        MyTrace(1,  'check if we can get a alive reply')
        info = {'fnc':'is_alive'}
        data = {}
        sndmsg = str(info)+'#'+str(data)

        r = self.callhome(sndmsg)
        
        if r[0] and 'err' not in r[0]:
            MyTrace(1, 'Predecessor OK')
            return True
        else:
            MyTrace(3,  'Predecessor Failed to respond')
            return False

    def transfer(self, id):
        info = {'fnc':'get'}
        data = {'id':id}
        sndmsg = str(info)+'#'+str(data)

        r = self.callhome(sndmsg)

        if 'ack' in r[0] and r[0]['ack'] == 'ok':
            data1 = {}
            if r[1].has_key('data'):
                data1 = r[1]['data']
            cache = {}
            if r[1].has_key('cache'):
                cache = r[1]['cache']
                
            return data1,cache
        else:
            return None, None
        
    def get(self, key):
        #make connection to get the data
        #return Node.get(self, key)
        info = {'fnc':'get'}
        data = {'key':key}
        sndmsg = str(info)+'#'+str(data)

        r = self.callhome(sndmsg)

        if 'ack' in r[0] and r[0]['ack'] == 'ok' and r[1].has_key(key):
            return (True,r[1][key]) 
        elif r[0].has_key('err'):
            return (False, r[0]['err'])
        else:
            return (False, 'Error')

    def put(self, key, value):
        #Node.put(self, key, value)
        MyTrace(1,  "make call to upload data", key, value)
        info = {'fnc':'put'}
        data = {key:value}
        sndmsg = str(info)+'#'+str(data)

        r = self.callhome(sndmsg)
        return r

    def putall(self, data):
        #Node.put(self, key, value)
        MyTrace(1,  "make call to upload all data", data)
        info = {'fnc':'put'}
    
        sndmsg = str(info)+'#'+str(data)

        r = self.callhome(sndmsg)
        return r
    
    def dumpself(self):
        '''
        this should use pickle but repy is not that friendly
        so we'll do it the hard way...
        the key items that need to be retrieved are: successor (ip:port), predecessor (ip:port),
            data (keys/values), finger table (list of ip:port or None)
        then we create a new LocalNode, load the info and return it
        '''
        info = {'fnc':'dumpself'}
        data = {}
        sndmsg = str(info)+'#'+str(data)

        r = self.callhome(sndmsg)
        
        if r[0] and 'err' not in r[0] and r[1]:
            MyTrace(1,  'dump OK')
            n = LocalNode(r[1]['self']['ip'], r[1]['self']['port'])

            succ = None
            if r[1]['succ']:
                succ = RemoteNode(r[1]['succ']['ip'], r[1]['succ']['port'])
                
            pred = None
            if r[1]['pred']:
                pred = RemoteNode(r[1]['pred']['ip'], r[1]['pred']['port'])

            n.successor = succ
            n.predecessor = pred
            n.data = r[1]['data']

            #load fingers (we shoud not rely that the finger table will have the same len but for now)
            for k,v in r[1]['finger'].items():
                if v:
                    n.finger[k] = RemoteNode(v['ip'],v['port'])
            
            return n
        else:
            MyTrace(3,  'dump failed')
            return False
    

    def search(self, wallID, valSearch):
        info = {'fnc':'search'}
        data = {'wallID':wallID, 'valSearch':valSearch}
        sndmsg = str(info)+'#'+str(data)

        r = self.callhome(sndmsg)

        # ack here is a little different than the other function, here we only care if the connection was made not
        # if there are actual results
        if 'ack' in r[0] and r[0]['ack'] == 'ok':
            return True
        else:
            return False

    def search_results(self, data):
        info = {'fnc':'search_results'}
        
        sndmsg = str(info)+'#'+str(data)
        r = self.callhome(sndmsg)
        
        if 'ack' in r[0] and r[0]['ack'] == 'ok':
            return True
        else:
            return False
        
    #cachelvl 0=no cache, 1=both;2=only cache
    def search_start(self, strSearch, cache_lvl=1):
        info = {'fnc':'search_start'}
        data = {'search':strSearch,'cache_lvl':cache_lvl}
        sndmsg = str(info)+'#'+str(data)

        #self.callhome(sndmsg, False)
        
        r = self.callhome(sndmsg)
        
        if 'ack' in r[0] and r[0]['ack'] == 'ok':
            return r[1]
        else:
            return False
        
        
    def stop_sync(self):
        info = {'fnc':'stop_sync'}
        data = {}
        sndmsg = str(info)+'#'+str(data)

        self.callhome(sndmsg, False)
        
    def restart_sync(self):
        info = {'fnc':'restart_sync'}
        data = {}
        sndmsg = str(info)+'#'+str(data)

        self.callhome(sndmsg, False)

    def print_node(self):
        info = {'fnc':'print_node'}
        data = {}
        sndmsg = str(info)+'#'+str(data)

        self.callhome(sndmsg, False)

    def leave_ring(self):
        info = {'fnc':'leave_ring'}
        data = {}
        sndmsg = str(info)+'#'+str(data)

        self.callhome(sndmsg, False)
        
    def hello(self, tracelvl = -1):
        #this function send a 'hello' msg to see if the remote node will send it back
        info = {'fnc':'hello'}
        data = {}
        if tracelvl != -1:
            data = {'tracelvl':tracelvl}
        sndmsg = str(info)+'#'+str(data)

        self.callhome(sndmsg, False)
        
def MyTrace(lvl, *args):
    if lvl >= mycontext['traceLevel']:
        print args
        myObsr.PrintMessages(args)


def proc2(remoteIP, remoteport, message, commhandle):
    MyTrace(4, 'RECEIVED Conn',remoteIP,remoteport,message)

    out = message.split('%')
    
    rcvmsg = out[1].split('#')
    info = myeval(rcvmsg[0])
    data = myeval(rcvmsg[1])
    
    reply = True
    
    sndmsg = str({'err':'Fail'})+'#'+str({})

    try:
        if info.has_key('ack'):
            reply = False
            idx = int(out[0])
            mycontext['replieslock'].acquire()
            if mycontext['replies'].has_key(idx):
                mycontext['replies'][idx] = message
            else:
                MyTrace(3, 'ERROR got a message but no slot',idx,remoteIP,remoteport,message)
            mycontext['replieslock'].release()                         
        elif info['fnc'] == 'search_results':
            sndmsg = mysearch_results_ack(data)
    except:
        reply = False
        MyTrace(3,  'ERROR proc2 ',remoteIP,remoteport,message)
        
    if reply:
        sndmsg = out[0] + '%' + sndmsg
        MyTrace(1, 'Sending udp message', remoteIP, remoteport, sndmsg)
        sendmess(remoteIP, remoteport, sndmsg, mycontext['ip'],mycontext['port'])

    try:
        
        if info['fnc'] == 'search_results' and not info.has_key('ack'):
            mysearch_results(data)
    except:
        MyTrace(3,  'proc2 search error')
        
class Observer:
    def __init__(self, printText = None):
        self.pRes = printText
        self.pMsg = None
        
    def SetPrintRes(self, printText):
        self.pRes = printText
        
    def SetPrintMsg(self, printMsg):
        self.pMsg = printMsg

    def PrintResults(self, msg):
        if self.pRes is not None:            
            self.pRes(msg)
            
    def PrintMessages(self, msg):
        if self.pMsg is not None:            
            self.pMsg(msg)

myObsr = Observer()
        
def mysearch_results_ack(data):
    info = {'ack':'ok','fnc':'search'}
    # just say we got it
    MyTrace(1, 'Printing Search OUT', data)
    
    return str(info)+'#'+str({})

def mysearch_results(data):
    MyTrace(3, 'Printing Search OUT', data)
    
    if data.has_key('keys'):
        thread.start_new_thread( lookup_vals, (data['keys'],myObsr.PrintResults))
        
def lookup_vals(keys, fncprint):
    print 'KEYS', keys
    if keys:
        for k in keys.values():
            print 'here', k
            n0 = mycontext['remote_node'].find_successor(k)
            if n0 is not None:
                val = n0.get(k)
                
                print 'Value returned=', val
                myObsr.PrintResults('Search Results: ' + str(val[1]))


class ChordApp:
    def __init__(self, master, filename='nodes.conf'):
        # set up the UI

        #first control buttons
        controlFrame = Frame(master)
        controlFrame.pack(side = BOTTOM, fill=X)

        printbutton = Button(controlFrame, text='Print', command = self._print)
        printbutton.pack(side = LEFT)
        
        printbutton = Button(controlFrame, text='Stop', command = self._stop, fg='red')
        printbutton.pack(side = LEFT)

        printbutton = Button(controlFrame, text='Restart', command = self._restart, fg='green')
        printbutton.pack(side = LEFT)

        printbutton = Button(controlFrame, text='Leave', command = self._leave, fg='red')
        printbutton.pack(side = LEFT)

        menubutton = Menubutton(controlFrame, text='Trace Level', fg='blue', relief=RAISED)
        menubutton.pack(side = LEFT)
        menubutton.menu = Menu(menubutton, tearoff=False)
        menubutton['menu'] = menubutton.menu

        self.TraceLevel = IntVar()
        self.TraceLevel.set(-1)
        menubutton.menu.add_radiobutton(label="None", variable=self.TraceLevel, value=3)
        menubutton.menu.add_radiobutton(label="Minimal", variable=self.TraceLevel, value=2)
        menubutton.menu.add_radiobutton(label="Extended", variable=self.TraceLevel, value=1)
        menubutton.menu.add_radiobutton(label="Full", variable=self.TraceLevel, value=0)        
        

        printbutton = Button(controlFrame, text='Hello', command = self._hello, fg='blue')
        printbutton.pack(side = LEFT)

        printbutton = Button(controlFrame, text='Clear Sel', command = self._clearsel)
        printbutton.pack(side = LEFT)


        #add listbox
        listFrame = Frame(master)
        listFrame.pack(side = LEFT, fill=BOTH)

        mylable = Label(listFrame, text='Nodes')
        mylable.pack(side = TOP)

        scrollbar = Scrollbar(listFrame)
        scrollbar.pack( side = RIGHT, fill = Y)
        self.nodeListBox = Listbox(listFrame, yscrollcommand = scrollbar.set)

        self.nodes = []
        try:
            addresses = [line.strip() for line in open(filename, 'r')]
            for i in addresses:
                if i:
                    add = i.split(':')
                    n = RemoteNode(add[0], int(add[1]))
                    self.nodes.append(n)
                    self.nodeListBox.insert(END, n.ip + ' ' + str(n.port) + ' ' + str(n.id))
        except:
            print 'No File:', filename

        
        self.nodeListBox.pack( side = LEFT, fill = BOTH)
        scrollbar.config( command = self.nodeListBox.yview)


        #add functions
        fncFrame = Frame(master)
        fncFrame.pack(side = RIGHT, fill=BOTH)

        mylable = Label(fncFrame, text='Input')
        mylable.pack(side = TOP)
        
        self.mainEntry = Entry(fncFrame, bd=5)
        self.mainEntry.pack(side = TOP, fill=BOTH)

        putbutton = Button(fncFrame, text='Put', command = self._put,fg='green')
        putbutton.pack(side = TOP, fill=BOTH)

        self.AutoHash = IntVar()
        self.AutoHash.set(1)
        checkbutton = Checkbutton(fncFrame, text='Auto Gen Key', variable = self.AutoHash)
        checkbutton.pack(side = TOP, fill=BOTH)

        getbutton = Button(fncFrame, text='Get', command = self._get,fg='green')
        getbutton.pack(side = TOP, fill=BOTH)

        searchbutton = Button(fncFrame, text='Search', command = self._search,fg='blue')
        searchbutton.pack(side = TOP, fill=BOTH)

        menubutton = Menubutton(fncFrame, text='Cache', relief=RAISED,fg='blue')
        menubutton.pack(side = TOP,  fill=BOTH)
        menubutton.menu = Menu(menubutton, tearoff=False)
        menubutton['menu'] = menubutton.menu

        self.CacheLevel = IntVar()
        self.CacheLevel.set(0)
        menubutton.menu.add_radiobutton(label="Full Search", variable=self.CacheLevel, value=0)
        menubutton.menu.add_radiobutton(label="Cached Items", variable=self.CacheLevel, value=2)
        menubutton.menu.add_radiobutton(label="Both", variable=self.CacheLevel, value=1)

        
        searchbutton = Button(fncFrame, text='Add Node', command = self._addnode)
        searchbutton.pack(side = TOP, fill=BOTH)

        searchbutton = Button(fncFrame, text='Clear', command = self._clear_out,fg='red')
        searchbutton.pack(side = TOP, fill=BOTH)

        self.ShowMsg = IntVar()
        checkbutton = Checkbutton(fncFrame, text='Show Messages', variable = self.ShowMsg)
        checkbutton.pack(side = TOP, fill=BOTH)

        helpbutton = Button(fncFrame, text='Help', command = self._help,fg='blue')
        helpbutton.pack(side = BOTTOM, fill=BOTH)
        

        self.resultsText = Text(master)
        self.resultsText.pack(side = RIGHT)

        myObsr.SetPrintRes(self.PrintResults)
        myObsr.SetPrintMsg(self.PrintInMsg)

    def PostInit(self):
        self.resultsText.tag_config('err', foreground="red")
        self.resultsText.tag_config('res', foreground="green")
        self.resultsText.tag_config('info', foreground="blue")
        self.resultsText.tag_config('msg', foreground="black")

        self.nodeListBox.config(width = 30)
        print 'Init Win'

    def PrintResults(self, msg):
        self.resultsText.insert(END, str(msg) + '\n', 'res')
        self.resultsText.yview(END)
        
    def PrintInMsg(self, msg):
        if self.ShowMsg.get() != 0:
            self.resultsText.insert(END, str(msg) + '\n', 'msg')
            self.resultsText.yview(END)

    def _clearsel(self):
        self.nodeListBox.select_clear(0, END)
        

    def _print(self):
        print '_print chord'
        selectedIndex = -1

        try:
            selectedIndex = self.nodeListBox.curselection()[0]
            selectedIndex = int(selectedIndex)
        except IndexError:
            selectedIndex = -1

        if selectedIndex != -1:
            self.nodes[selectedIndex].print_node()
        else:
            for n in self.nodes:
                n.print_node()

    def _stop(self):
        print '_stop chord'
        selectedIndex = -1

        try:
            selectedIndex = self.nodeListBox.curselection()[0]
            selectedIndex = int(selectedIndex)
        except IndexError:
            selectedIndex = -1

        if selectedIndex != -1:
            self.nodes[selectedIndex].stop_sync()
        else:
            for n in self.nodes:
                n.stop_sync()

    def _restart(self):
        print '_restart chord'
        selectedIndex = -1

        try:
            selectedIndex = self.nodeListBox.curselection()[0]
            selectedIndex = int(selectedIndex)
        except IndexError:
            selectedIndex = -1

        if selectedIndex != -1:
            self.nodes[selectedIndex].restart_sync()
        else:
            for n in self.nodes:
                n.restart_sync()

    def _leave(self):
        print '_leave chord'
        selectedIndex = -1

        try:
            selectedIndex = self.nodeListBox.curselection()[0]
            selectedIndex = int(selectedIndex)
        except IndexError:
            selectedIndex = -1

        if selectedIndex != -1:
            self.nodes[selectedIndex].leave_ring()
        else:
            for n in self.nodes:
                n.leave_ring()
        
    def _hello(self):
        print '_hello chord'        
        
        selectedIndex = -1

        try:
            selectedIndex = self.nodeListBox.curselection()[0]
            selectedIndex = int(selectedIndex)
        except IndexError:
            selectedIndex = -1

        if selectedIndex != -1:
            self.nodes[selectedIndex].hello(self.TraceLevel.get())
        else:
            for n in self.nodes:
                n.hello(self.TraceLevel.get())        

    def _put(self):
        print '_put chord'
        selectedIndex = -1

        try:
            selectedIndex = self.nodeListBox.curselection()[0]
            selectedIndex = int(selectedIndex)
        except IndexError:
            selectedIndex = -1
            tkMessageBox.showinfo('Error', 'Please select a starting node.')

        if selectedIndex != -1:
            add = self.mainEntry.get().strip()
            key = -1
            if self.AutoHash.get() == 0:
                locf = add.find(':')

                if locf == -1:
                    tkMessageBox.showinfo('Error', 'Please enter a key. The format is key:value.')
                    return
                else:
                    key = add[:locf]

                try:
                    key = int(key)
                except:
                    tkMessageBox.showinfo('Error', 'Incorrect key: ' + key + ' Please enter a valid key. The format is key:value.')
                    return

                add = add[locf+1:]
            else:
                key = (long(sha_hexhash(add),16))%(self.nodes[selectedIndex].M)

            
            if not add:
                tkMessageBox.showinfo('Error', 'Please enter a valid value.')
                return
            
            n0 = self.nodes[selectedIndex].find_successor(key)
            self.AddNode(n0)
            if n0 is not None:
                ret = n0.put(key, add)  
                if 'ack' in ret[0] and ret[0]['ack'] == 'ok':
                    self.resultsText.insert(END, 'Key/Value: ' + str(key) + '/"' + add + '" was added successfully to: ' + n0.ip + ' ' + str(n0.port) + '\n', 'info')
                    self.mainEntry.delete(0, END)
                elif 'ack' in ret[0] and 'err' in ret[0]:
                    self.resultsText.insert(END, 'Unable to add Value. Error: ' + ret[0]['err'] +'\n', 'err')
                else:
                    self.resultsText.insert(END, 'Failed to add Value\n', 'err')
            else:
                self.resultsText.insert(END, 'Failed to add Value\n', 'err')                
                
                self.mainEntry.delete(0, END)
                self.resultsText.yview(END)
        
    def _get(self):
        print '_get chord'
        selectedIndex = -1

        try:
            selectedIndex = self.nodeListBox.curselection()[0]
            selectedIndex = int(selectedIndex)
        except IndexError:
            selectedIndex = -1
            tkMessageBox.showinfo('Error', 'Please select a starting node.')

        if selectedIndex != -1:
            add = self.mainEntry.get().strip()
            key = long(add)
            n0 = self.nodes[selectedIndex].find_successor(key)
            self.AddNode(n0)
            if n0 is not None:
                val = n0.get(key)
                if val[0]:
                    self.resultsText.insert(END, 'The value for the key ' + str(key) + ' is: ' + str(val[1]) + '\n', 'res')                    
                else:
                    self.resultsText.insert(END, 'Unable to find val for key. Error: ' + val[1]['err'] + str(key) + '\n', 'err')
            else:
                self.resultsText.insert(END, 'Failed to find value\n', 'err')                
                
                self.mainEntry.delete(0, END)
                self.resultsText.yview(END)

        
    def _search(self):
        print '_search chord'
        selectedIndex = -1
        cache_lvl = self.CacheLevel.get()
        
        try:
            selectedIndex = self.nodeListBox.curselection()[0]
            selectedIndex = int(selectedIndex)
        except IndexError:
            selectedIndex = -1
            tkMessageBox.showinfo('Error', 'Please select a starting node.')

        if selectedIndex != -1:
            mysearch = self.mainEntry.get().strip()
            key = (long(sha_hexhash(mysearch),16))%(self.nodes[selectedIndex].M)
            mycontext['remote_node'] = self.nodes[selectedIndex]
            n0 = self.nodes[selectedIndex].find_successor(key)
            self.AddNode(n0)
            if n0 is not None:
                cachedKeys = n0.search_start(mysearch, cache_lvl)
                if cache_lvl == 2:
                    mysearch_results(cachedKeys)


    def AddNode(self, new_n):
        if new_n is not None:
            add_ok = True
            for n in self.nodes:
                add_ok = new_n.id != n.id
                if not add_ok:
                    break
            if add_ok:
                self.nodes.append(new_n)
                self.nodeListBox.insert(END, new_n.ip + ' ' + str(new_n.port) + ' ' + str(new_n.id))
        else:
            add_ok = False
        return add_ok
        
        
    def _addnode(self):
        print '_search chord', self.mainEntry.get()

        add = self.mainEntry.get().strip()#.split(':')
        print add
        if add.find(':') != -1:
            add = add.split(':')
        else:
            add = add.split()

        print add

        if len(add) != 2:
            tkMessageBox.showinfo('Error', 'Please enter ip port or ip:port')
        else:
            new_n = RemoteNode(add[0], int(add[1]))
            if self.AddNode(new_n):
                self.mainEntry.delete(0, END)
            else:
                tkMessageBox.showinfo('Error', 'Node with this id already exists')

    def _clear_out(self):
        self.resultsText.delete(1.0,END)
        
    def encode_length(self,l):
        #Make it 4 bytes long
        l = str(l)
        while len(l) < 4:
            l = "0"+l 
        return l

    def _uploadfile(self):
        filename = tkFileDialog.askopenfilename()
        
        selectedIndex = -1
        try:
            selectedIndex = self.nodeListBox.curselection()[0]
            selectedIndex = int(selectedIndex)
        except IndexError:
            selectedIndex = -1
            tkMessageBox.showinfo('Error', 'Please select a starting node.')

        if filename and selectedIndex != -1:
            myfile = open(filename, 'r')
            key = (long(sha_hexhash(filename),16))%(self.nodes[selectedIndex].M)
            short_name = filename[filename.rfind('/')+1:]
            
            short_name = str(key) + ',' + short_name
            n0 = self.nodes[selectedIndex].find_successor(key)
            self.AddNode(n0)
            if n0 is not None:
                s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                s.connect((n0.ip, n0.port))
                s.send(self.encode_length(len(short_name)))
                s.send(short_name)
                data = myfile.read()
                s.send(self.encode_length(len(data)))
                s.send(data)
                s.close()
            
    def _help(self):
        self.resultsText.insert(END, 'Print - Send a command to node(s) which will cause the node(s) to print its status.\n', 'info')                    
        self.resultsText.insert(END, 'Stop - Send a command to node(s) to stop synchronizing.\n', 'info')                    
        self.resultsText.insert(END, 'Restart - Send a command to node(s) to resume its synchronizing.\n', 'info')                    
        self.resultsText.insert(END, 'Leave - Send a command to node(s) to leave the ring.\n', 'info')                    
        self.resultsText.insert(END, 'Trace Level - Set a trace level that will be sent by Hello to node(s).\n', 'info')                    
        self.resultsText.insert(END, 'Clear Sel - Clear selected node. Command now will apply to all displayed nodes.\n\n', 'info')                    
        self.resultsText.insert(END, 'Put - Enter a value to be saved on one of the nodes. The selected node is used to find the node that will store the value.\n', 'info')                    
        self.resultsText.insert(END, 'Auto Gen Key - Provides the ability to specify a key when unchecked. The format is key:value.\n', 'info')                    
        self.resultsText.insert(END, 'Get - Enter a key that corresponds to a value stored.\n', 'info')                    
        self.resultsText.insert(END, 'Search - Enter a search keyword.\n', 'info')                    
        self.resultsText.insert(END, 'Cache - Specify if search should use cache when retrieving data.\n', 'info')                    
        self.resultsText.insert(END, 'Add Node - Add a starting/seed node.\n', 'info')                    
        self.resultsText.insert(END, 'Clear - Clear the output screen.\n', 'info')                    
        self.resultsText.insert(END, 'Bugs - Strings containing \':{}[] will crash a node. This is due to the conversion of a string to dictionary structure. No pickling under Seattle :(\n', 'info')                    
        self.resultsText.yview(END)
        #self._uploadfile()
        
        
def main(argv):
    mycontext['traceLevel'] = 0
    filename='nodes.conf'

    if len(argv) == 1:
        filename = argv[0]
        
    print argv
    port = 12360
    ip = '127.0.0.1'
    
    #port = 12345
    #ip = socket.gethostbyname(socket.gethostname())

    mycontext['ip'] = ip
    mycontext['port'] = port
    mycontext['replies'] = {}
    mycontext['replieslock'] = threading.Lock()
    mycontext['connlock'] = threading.Lock()

    recvmess(ip, port, proc2)
    
    
    root = Tk()
    root.title("Chord Control")
    #root.minsize(800, 400)
    app = ChordApp(root,filename)
    root.after(1000, app.PostInit())
    root.mainloop()

    print 'Good Bye'
    sock.close()
    


if __name__ == '__main__':
    main(sys.argv[1:])

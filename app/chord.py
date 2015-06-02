# ======================================================================
#                   Christopher Pac
#                   Chord Search
#
#   chord.py
#
#   Command-Line Arguments: port timeout seedip seedport
#
#   python repy.py restrictions.test chord.py port timeout seedip seedport
#
#   Chord Legend:
#       SHA-1               Ln 29
#       Chord Node          Ln 362
#       Utility Fnc         Ln 538
#       Remote Node         Ln 611
#       Local Node          Ln 935
#       Communication Fnc   Ln 1092
#       Synchronization Fnc Ln 1337
#       proc2               Ln 1413
#       main                Ln 1515
#
#       Node Search         Ln 512
#       Remote Node Search  Ln 855
#       Local Node Cache    Ln 958, 1054
#       Local Node Search   Ln 1017
#       Search Comm         Ln 1214
# ======================================================================

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
        max_it = 50  
        worked = False
        while not worked:
            sleep(0.1)
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
        

class LocalNode(Node):
    '''
    format {key1:value, key2:value,...}
    '''
    data = {}

    '''
    search_cache:
    format: not used! {hashed_search1:{'strSearch1':{0:key,1:key,...}, 'strSearch2':{0:key,1:key,...}},hashed_search2:...}
    format: {hashed_search1:{'strSearch1':[key1,key2,...], 'strSearch2':[key1,key2,...]},hashed_search2:...}
    '''
    search_cache = {}
    
    def get(self, key):
        return self.data[key]

    def get_lesseq(self, id):
        ret = {}
        for n in self.data:
            if not self.containsR(n,id,self.id):
                ret[n] = self.data[n]
        return ret
    
    def get_lesseq_cache(self, id):
        ret = {}
        for n in self.search_cache:
            if not self.containsR(n,id,self.id):
                ret[n] = self.search_cache[n]
        return ret
    
    def remove_lesseq_cache(self, id):
        newdata = {}
        for n in self.search_cache:
            if self.containsR(n,id,self.id):
                #print 'deleting', self.data[n]
                newdata[n] = self.search_cache[n]
        self.search_cache = newdata
    
    def remove_lesseq(self, id):
        newdata = {}
        for n in self.data:
            if self.containsR(n,id,self.id):
                #print 'deleting', self.data[n]
                newdata[n] = self.data[n]
        self.data = newdata
        
    def put(self, d, dup_ok=False):
        if not dup_ok:
            keys = d.keys()

            for k in keys:
                if k in self.data:
                    return False
                    #raise Exception("Value Already Exists")
            
        self.data.update(d)
        return True

    def join(self, n0):
        Node.join(self,n0)
        #get all the key/values less than or equal to us if fail we can not join
        if self.successor is None:
            return False
        data,cache = self.successor.transfer(self.id)
        if data is not None:
            self.data.update(data)
        if cache is not None:
            self.search_cache.update(cache)
        return True
        
    def leave(self):
        if self != self.successor and self.successor is not None:
            data_all = {'data':self.data, 'cache':self.search_cache}
            self.successor.putall(data_all)
        Node.leave(self)
    
    def notify(self, n0):
        if Node.notify(self,n0):
            self.remove_lesseq(n0.id)
            self.remove_lesseq_cache(n0.id)

    # out: {'keys':{0:key, 1:key,...}}; search files when we have them
    def search(self, wallID, valSearch):
        print 'Calling Base Node search'
        Node.search(self, wallID, valSearch)
        #add code here to do the actual search
        data = {'keys':{}} #this will have the keys to the corresponding values
        count = 0
        strSearch = valSearch['search']
        for k in self.data:
            if isinstance(self.data[k], str) and isinstance(strSearch, str):
                if self.data[k].find(strSearch) != -1:
                    data['keys'][count] = k
                    count = count + 1
            elif not isinstance(self.data[k], str) and not isinstance(strSearch, str):
                if self.data[k] == strSearch:
                    data['keys'][count] = k
                    count = count + 1
        # also cache needs to be done here maybe
        return data

    # check if we still own this search and if not return id that does; otherwise update cache
    #in: {'keys':{0:key, 1:key,...},'valSearch':{'search':'criteria', 'ip':ip, 'port':port, 'Source':{'ip':ip, 'port':port}}}
    def search_results(self, data):
        ret_val = -1
        search_id = (long(sha_hexhash(data['valSearch']['search']),16))%(self.M)
        '''
        check if we still own this id
        #n = Node.find_successor(search_id)
        if self.predecessor is not None and !self.containsR(search_id,self.predecessor.id, self.id):
             ret_val = Node.find_successor(search_id).id
        '''

        if ret_val == -1 and data.has_key('keys') and data.has_key('valSearch') and data['valSearch'].has_key('search'):
            self.cache_put_keys(data['valSearch']['search'], data['keys'])
        
        return ret_val

    #out: {0:key, 1:key,...}
    def cache_get_keys(self, strSearch):
        hkey = (long(sha_hexhash(strSearch),16))%(self.M)
        if self.search_cache.has_key(hkey) and self.search_cache[hkey].has_key(strSearch):
            keys = {}
            for i in range(0,len(self.search_cache[hkey][strSearch])):
                keys[i] = self.search_cache[hkey][strSearch][i]
            
            return keys #self.search_cache[hkey][strSearch]
        return {}    

    #in: {0:key, 1:key,...}
    def cache_put_keys(self, strSearch, keys):
        hkey = (long(sha_hexhash(strSearch),16))%(self.M)

        if self.search_cache.has_key(hkey) and self.search_cache[hkey].has_key(strSearch):
            keys = [k for k in keys.values()]
            self.search_cache[hkey][strSearch] = list(set(self.search_cache[hkey][strSearch]) | set(keys))
        else:
            if not self.search_cache.has_key(hkey):
                self.search_cache[hkey] = {}
            self.search_cache[hkey][strSearch] = [k for k in keys.values()] #keys
        
def PNS(node):
    succ = '   '
    pred = '   '
    if node.predecessor is not None: 
        pred = node.predecessor.id
    if node.successor is not None:
        succ = node.successor.id
    MyTrace(2,  pred,"<-",node.id,"->",succ)

def print_status(msg, lvl=1):
    if 'localnode' in mycontext:
        MyTrace(lvl, mycontext['localnode'].id,mycontext['localnode'].ip,mycontext['localnode'].port,'is',msg)
    else:
        MyTrace(lvl,  msg)
        
        
def find_successor(data):
    n = mycontext['localnode'].find_successor(data['id'])
    
    info = {'ack':'ok','fnc':'find_successor'}
    data = {}
    if n is None:
        info['err'] = 'No Successor'
        info['ack'] = 'fail'
    else:
        data = {'ip':n.ip,'port':n.port}
    return str(info)+'#'+str(data)
    
def get_predecessor(data):
    n = mycontext['localnode'].get_predecessor()
    
    info = {'ack':'ok','fnc':'get_predecessor'}
    data = {}
    if n is None:
        info['err'] = 'No Predecessor'
        info['ack'] = 'fail'
    else:
        data.update({'ip':n.ip,'port':n.port})
    return str(info)+'#'+str(data)
    
def notify(data):
    MyTrace(1,data)
    n = RemoteNode(data['ip'],data['port'])
    mycontext['localnode'].notify(n)
    return str({})+'#'+str({})

def put(data):
    info = {'ack':'ok','fnc':'put'}
    data1 = data
    if data.has_key('data'):
        data1 = data['data']

    if data.has_key('cache'):
        mycontext['localnode'].search_cache.update(data['cache'])

    if not mycontext['localnode'].put(data1,len(data1)>1):
        info['err'] = 'Value Already Exists'
        info['ack'] = 'fail'

    data = {}
    return str(info)+'#'+str(data)
    
def get(data):
    info = {'ack':'ok','fnc':'get'}
    
    if 'key' in data:
        #fix if there are multiple keys
        try:
            val = mycontext['localnode'].get(data['key'])
            data = {data['key']:val}
        except:
            info['err'] = 'No data for Key'
            info['ack'] = 'fail'
            
        return str(info)+'#'+str(data)
    elif 'id' in data:
        data1 = mycontext['localnode'].get_lesseq(data['id'])
        cache = mycontext['localnode'].get_lesseq_cache(data['id'])
        data = {'cache':cache, 'data':data1}
        
    else:
        info['err'] = 'Missing Key'
        info['ack'] = 'fail'

    return str(info)+'#'+str(data)
    
def pred_leaving(data):

    info = {'ack':'ok','fnc':'pred_leaving'}
    n = RemoteNode(data['ip'],data['port'])
    data = {}
    mycontext['localnode'].pred_leaving(n)

    return str(info)+'#'+str(data)


def succ_leaving(data):
    info = {'ack':'ok','fnc':'pred_leaving'}
    n = RemoteNode(data['ip'],data['port'])
    data = {}
    
    mycontext['localnode'].succ_leaving(n)    
    return str(info)+'#'+str(data)

def is_alive(data):
    info = {'ack':'ok','fnc':'is_alive'}
    data = {}
    return str(info)+'#'+str(data)

def dumpself(data):
    info = {'ack':'ok','fnc':'dumpself'}
    data = {}
    #if we can get pickle working this will be simple
    n = {'ip':mycontext['localnode'].ip,'port':mycontext['localnode'].port}
    succ = {}
    pred = {}
    if mycontext['localnode'].successor is not None:
        succ = {'ip':mycontext['localnode'].successor.ip,'port':mycontext['localnode'].successor.port}
    if mycontext['localnode'].predecessor is not None:
        pred = {'ip':mycontext['localnode'].predecessor.ip,'port':mycontext['localnode'].predecessor.port}

    data['self'] = n
    data['succ'] = succ
    data['pred'] = pred
    data['data'] = mycontext['localnode'].data

    #load the fingers
    finger = {}
    for i in range(0, len(mycontext['localnode'].finger)):
        if mycontext['localnode'].finger[i] is not None:
            finger[i] = {'ip':mycontext['localnode'].finger[i].ip, 'port':mycontext['localnode'].finger[i].port, 'id':mycontext['localnode'].finger[i].id}
        else:
            finger[i] = {}

    data['finger'] = finger

    return str(info)+'#'+str(data)

#meat of search communication
'''
this is different cause we will be returning results to the RING node that originally started this search
    and we will be just doing 'ack' to the node that called us to let it know we got the search
the valSearch is a struc that will/has the strSearch, info about the the ip:port of the computer
    (outside the ring) that asked for results, and the ip:port of the RING node that started the search
    if the RING node doesnt respond, hash its ip:port (we will have it anyway) and do find_successor on the id


    data = {'wallID':id, 'valSearch':{'search':'criteria', 'ip':ip, 'port':port, 'Source':{'ip':ip, 'port':port}}}
    
    output:
    fnc = search_results
    data = {'keys':{0:key, 1:key,...},'valSearch':{'search':'criteria', 'ip':ip, 'port':port, 'Source':{'ip':ip, 'port':port}}}
'''
def search_ack(data):
    info = {'ack':'ok','fnc':'search'}
    # just say we got it
    data = {}
    return str(info)+'#'+str(data)
    
def search(data):
    out_data = mycontext['localnode'].search(data['wallID'], data['valSearch'])    
    #just return the results
    out_data['valSearch'] = data['valSearch']

    print 'LOCAL search results', out_data['keys']
    #check if there is anything to send; if empty dont send it
    if not out_data['keys']:
        print 'EMPTY key set check data', mycontext['localnode'].data
        return
    #check so we dont send it to ourselves
    if data['valSearch']['ip'] == mycontext['localnode'].ip and data['valSearch']['port'] == mycontext['localnode'].port:
        search_results(out_data)
    else:
        n = RemoteNode(data['valSearch']['ip'],data['valSearch']['port'])    
        did_it_work = n.search_results(out_data)

    '''
        #we were not able to send; for now we will retry once
        if not did_it_work:
            n = mycontext['localnode'].find_successor(n.id)        
            did_it_work = n.search_results(out_data)
    '''

def search_results(data):
    '''
    we got search results: 1 check if they still belong to us (i.e. pass them to localnode)
    if not forward to Node that owns them now (for caching); otherwise just farward to the guy that originally requested the search
    '''
    out_new_id = mycontext['localnode'].search_results(data)    

    if out_new_id == -1:
        # it worked so farward; the Source that requested the search is not part of the ring but will will reuse the RemoteNode func
        n = RemoteNode(data['valSearch']['Source']['ip'],data['valSearch']['Source']['port'])
        did_it_work = n.search_results(data)
        # we could retry...
    else:
        # farward to the ring node that owns it now
        n = mycontext['localnode'].find_successor(out_new_id)
        did_it_work = n.search_results(data)
        
    info = {'ack':'ok','fnc':'search_results'}
    # just say we got it
    return str(info)+'#'+str({})

#out: {'wallID':id, 'valSearch':{'search':'criteria', 'ip':ip, 'port':port, 'Source':{'ip':ip, 'port':port}}}
#data will have {'search':'criteria'}
def search_start(data, remoteIP, remoteport):
    valSearch = {}
    valSearch.update(data)
    valSearch['ip'] = mycontext['localnode'].ip
    valSearch['port'] = mycontext['localnode'].port
    valSearch['Source'] = {'ip':remoteIP, 'port':remoteport}
    out_data = {}
    out_data['valSearch'] = valSearch
    out_data['wallID'] = mycontext['localnode'].id
    
    #handle cache here; cache_lvl 0=no cache, 1=both; 2=only cache
    cached_data = {}
    clvl = 0
    if data.has_key('cache_lvl'):
        clvl = data['cache_lvl']
        if clvl == 1 or clvl == 2:
            cached_data['keys'] = mycontext['localnode'].cache_get_keys(data['search'])
        
    if clvl == 0 or clvl == 1:
        search(out_data)

    info = {'ack':'ok','fnc':'search_start'}    
    
    return str(info)+'#'+str(cached_data)
    

#print functions
def print_node(data):   
    node = mycontext['localnode']
    if not node.predecessor:
        MyTrace(4, "   <-",node.id,"->",node.successor.id)
    else:
        MyTrace(4,  node.predecessor.id,"<-",node.id,"->",node.successor.id)

    MyTrace(4, 'DATA', mycontext['localnode'].data)
    MyTrace(4, 'CACHE', mycontext['localnode'].search_cache)
    
def MyTrace(lvl, *args):
    if lvl >= mycontext['traceLevel']:
        print args

def leave_ring(data):
    if canceltimer(mycontext['stopevent']):
        stop_listening(mycontext['listenhandle'])

def hello(data):
    if data.has_key('tracelvl'):
        mycontext['traceLevel'] = data['tracelvl']
        
    info = {'ack':'ok','fnc':'hello'}
    
    data = {'hello':'hello back'}
    return str(info)+'#'+str(data)
        
#end print functions
#sync functions
def stop_sync(data):
    mycontext['finished'] = True

def restart_sync(data):
    mycontext['finished'] = False
    mycontext['syncevent'] = settimer(mycontext['synctime'], sync, ())

def sync():

    while not mycontext['finished']:
        mycontext['syncfnc'] = mycontext['syncfnc']%3
        PNS(mycontext['localnode'])
        MyTrace(0, 'DATA', mycontext['localnode'].data)
        #MyTrace(0, 'CACHE', mycontext['localnode'].search_cache)
        if not mycontext['finished'] and not mycontext['replies']:
            if mycontext['syncfnc'] == 0:
                stabilizing()
            elif mycontext['syncfnc'] == 1:
                fixing_fingers()
            elif mycontext['syncfnc'] == 2:
                checking_predecessor()
            mycontext['syncfnc'] = mycontext['syncfnc'] + 1

            #mycontext['syncevent'] = settimer(mycontext['synctime'], sync, ())
        sleep(mycontext['synctime'])
    
def stabilizing():        
    mycontext['synclock'].acquire()
    if not mycontext['finished']:
        print_status('stabilizing')
        try:
            mycontext['localnode'].stabilize()
        except:
            print_status('failed to stabilize',3)
    mycontext['synclock'].release()
    

def checking_predecessor():
    mycontext['synclock'].acquire()
    if not mycontext['finished']:
        print_status('checking predecessor')
        try:
            mycontext['localnode'].check_predecessor()
        except:
            print_status('failed to check predecessor',3)
    mycontext['synclock'].release()

def fixing_fingers():
    mycontext['synclock'].acquire()
    if not mycontext['finished']:
        print_status('fixing fingers')
        try:
            mycontext['localnode'].fix_fingers()
        except:
            print_status('failed to fix fingers',3)
    mycontext['synclock'].release()
    
def stop_listening(commhandle):
    canceltimer(mycontext['syncevent'])
    mycontext['synclock'].acquire()
    print_status('Ending',3)    

    mycontext['finished'] = True

    try:
        mycontext['localnode'].leave()
    except:
        print_status('failed to leave properly')
    
    stopcomm(commhandle)
    mycontext['synclock'].release()
    PNS(mycontext['localnode'])
    
#end sync functions

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
             
        elif info['fnc'] == 'find_successor':
            sndmsg = find_successor(data)
        elif info['fnc'] == 'get_predecessor':
            sndmsg = get_predecessor(data)
        elif info['fnc'] == 'notify':
            sndmsg = notify(data)
            reply = False
        elif info['fnc'] == 'put':
            sndmsg = put(data)
        elif info['fnc'] == 'get':
            sndmsg = get(data)
        elif info['fnc'] == 'pred_leaving':
            sndmsg = pred_leaving(data)
        elif info['fnc'] == 'succ_leaving':
            sndmsg = succ_leaving(data)
        elif info['fnc'] == 'is_alive':
            sndmsg = is_alive(data)
        elif info['fnc'] == 'dumpself':
            sndmsg = dumpself(data)
        elif info['fnc'] == 'search':
            sndmsg = search_ack(data)
        elif info['fnc'] == 'search_results':
            sndmsg = search_results(data)
        elif info['fnc'] == 'search_start':
            sndmsg = search_start(data, remoteIP, remoteport)
            #reply = False
        elif info['fnc'] == 'stop_sync':
            sndmsg = stop_sync(data)
            reply = False
        elif info['fnc'] == 'restart_sync':
            sndmsg = restart_sync(data)
            reply = False
        elif info['fnc'] == 'print_node':
            sndmsg = print_node(data)
            reply = False
        elif info['fnc'] == 'leave_ring':
            sndmsg = leave_ring(data)
            reply = False
        elif info['fnc'] == 'hello':
            sndmsg = hello(data)
            
                   
    except:
        reply = False
        MyTrace(3,  'ERROR proc2 ',remoteIP,remoteport,message)
    
    if reply:
        sndmsg = out[0] + '%' + sndmsg
        MyTrace(2, 'proc2 sendmess', remoteIP, remoteport, sndmsg, mycontext['ip'],mycontext['port'])
        sendmess(remoteIP, remoteport, sndmsg, mycontext['ip'],mycontext['port'])

    try:
        # we do the actual search after we have ack'ed to not delay the search
        if info['fnc'] == 'search' and not info.has_key('ack'):
            MyTrace(1, 'RECEIVED Conn(search)',remoteIP,remoteport,message)
            search(data)
    except:
        MyTrace(3,  'ERROR proc2 search')

def filehandling(ip, port, sockobj, thiscommhandle, listencommhandle):
    try:
        filelen =  sockobj.recv(4)
        
        filename = sockobj.recv(int(filelen))
        key_fn = filename.split(',')
        
        filelen =  sockobj.recv(4)
        data = sockobj.recv(int(filelen))

        myfile = open(key_fn[1],'w')
        myfile.write(myfile)
        myfile.close()
        print 'file saved'
    except:
        sockobj.close()
    

if callfunc == 'initialize':
    # traceLevel = 0 is everything, 1 is all info, 2 is critical info, 3 is errors
    mycontext['traceLevel'] = 3
    
    #input: port timeout seed_ip seed_port
    port = 12345
    ip = '127.0.0.1'#getmyip()#
    
    ok_run = True
    timeout = 5000
    
    mycontext['finished'] = False

    mycontext['synctime'] = 1#7+(randomfloat()*100+1)%6
    # syncfnc = 0 is stabilize, 1 is fixfingers, 2 is check predecessor
    mycontext['syncfnc'] = 3
    
    mycontext['synclock'] = getlock()
    mycontext['connlock'] = getlock()

    mycontext['replies'] = {}
    mycontext['replieslock'] = getlock()     
    
    seed_ip = ''
    seed_port = -1
    
    if len(callargs) > 0:
        port = int(callargs[0])
    else:
        MyTrace(3, 'Error: Missing Port Number')
        ok_run = False

    if len(callargs) > 1:
        timeout = int(callargs[1])

    if len(callargs) >= 4:
        seed_ip = callargs[2]
        seed_port = int(callargs[3])
        
    print 'seed', seed_ip, seed_port
    
    mycontext['ip'] = ip
    mycontext['port'] = port
    
    mynode = LocalNode(ip,port)
    mycontext['localnode'] = mynode

    listencommhandle = recvmess(ip,port,proc2)
    mycontext['listenhandle'] = listencommhandle
    #listencommhandlefile = waitforconn(ip,port,filehandling)

    join_worked = True
    if seed_port != -1:
        print 'joining:',seed_ip,seed_port
        seednode = RemoteNode(seed_ip,seed_port)
        mycontext['synclock'].acquire()
        join_worked = mycontext['localnode'].join(seednode)
        mycontext['synclock'].release()

    #if join_worked:
    mycontext['stopevent'] = settimer(timeout, stop_listening, (listencommhandle,))    
    
    mycontext['syncevent'] = settimer(mycontext['synctime'], sync, ())
    #else:
    #    print 'ERROR node not able to join the ring'

        
    ''' FIXES
    for now notify will remove all the key/values that do no belong to this node
    however, between join and stablize, a successor node could have gotten a key/values that it
    no longer handles and thus on notify it should put those new values to its predcessor
    however, that would require that we know what pred already has or we could send once again everything
    lots of fun race conditions
    '''

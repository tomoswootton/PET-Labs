#####################################################
# GA17 Privacy Enhancing Technologies -- Lab 03
#
# Basics of Privacy Friendly Computations through
#         Additive Homomorphic Encryption.
#
# Run the tests through:
# $ py.test -v test_file_name.py

#####################################################
# TASK 1 -- Setup, key derivation, log
#           Encryption and Decryption
#

###########################
# Group Members: TODO
###########################


from petlib.ec import EcGroup

def setup():
    """Generates the Cryptosystem Parameters."""
    G = EcGroup(nid=713)
    g = G.hash_to_point(b"g")
    h = G.hash_to_point(b"h")
    o = G.order()
    return (G, g, h, o)


def keyGen(params):
   """ Generate a private / public key pair """
   (G, g, h, o) = params

   priv = o.random()
   pub = priv * g

   return (priv, pub)

def encrypt(params, pub, m):
    """ Encrypt a message under the public key """
    if not -100 < m < 100:
        raise Exception("Message value to low or high.")
    (G,g,h,o) = params

    k = o.random()

    c = (k*g, k*pub + m*h)

    return c

def isCiphertext(params, ciphertext):
    """ Check a ciphertext """
    (G, g, h, o) = params
    ret = len(ciphertext) == 2
    a, b = ciphertext
    ret &= G.check_point(a)
    ret &= G.check_point(b)
    return ret

_logh = None
def logh(params, hm):
    """ Compute a discrete log, for small number only """
    global _logh
    (G, g, h, o) = params

    # Initialize the map of logh
    if _logh == None:
        _logh = {}
        for m in range (-1000, 1000):
            _logh[(m * h)] = m

    if hm not in _logh:
        raise Exception("No decryption found.")

    return _logh[hm]

def decrypt(params, priv, ciphertext):
    """ Decrypt a message using the private key """
    assert isCiphertext(params, ciphertext)

    a , b = ciphertext

    return logh(params, b - priv*a)

#####################################################
# TASK 2 -- Define homomorphic addition and
#           multiplication with a public value
# 

def add(params, pub, c1, c2):
    """ Given two ciphertexts compute the ciphertext of the 
        sum of their plaintexts.
    """
    assert isCiphertext(params, c1)
    assert isCiphertext(params, c2)

    (G,g,h,o) = params

    b = c1[1]+c2[1]
    a = c1[0]+c2[0]

    return a,b

def mul(params, pub, c1, alpha):
    """ Given a ciphertext compute the ciphertext of the 
        product of the plaintext time alpha """
    assert isCiphertext(params, c1)

    c3 = c1[0].pt_mul(alpha), c1[1].pt_mul(alpha)

    return c3

#####################################################
# TASK 3 -- Define Group key derivation & Threshold
#           decryption. Assume an honest but curious 
#           set of authorities.

def groupKey(params, pubKeys=[]):
    (G, g, h, o) = params
    """ Generate a group public key from a list of public keys """

    pub = G.infinite()
    for key in pubKeys: 
        pub = pub + key
    
    return pub

def partialDecrypt(params, priv, ciphertext, final=False):
    """ Given a ciphertext and a private key, perform partial decryption. 
        If final is True, then return the plaintext. """
    assert isCiphertext(params, ciphertext)
    
    a1,b1 = ciphertext

    b1 = b1 - priv*a1

    if final:
        return logh(params, b1)
    else:
        return a1, b1

#####################################################
# TASK 4 -- Actively corrupt final authority, derives
#           a public key with a known private key.
#

def corruptPubKey(params, priv, OtherPubKeys=[]):
    """ Simulate the operation of a corrupt decryption authority. 
        Given a set of public keys from other authorities return a
        public key for the corrupt authority that leads to a group
        public key corresponding to a private key known to the
        corrupt authority. """
    
    """
        1) Work out threshold key generated from others
        2) multiply own private key by negative of key found in 1) 
        3) add key found in 2) to threshold key
        This process will cancel out the public key values of the other participants, allowing
        the attacker's key to fully encrypt
    """

    (G, g, h, o) = params
    #1)
    pub = G.infinite()			#init point
    for key in OtherPubKeys: 
        pub = pub - key
    
    #2) 3)
    corrupt_pub = (priv*g)+pub

    return corrupt_pub

#####################################################
# TASK 5 -- Implement operations to support a simple
#           private poll.
#

def encode_vote(params, pub, vote):
    """ Given a vote 0 or 1 encode the vote as two
        ciphertexts representing the count of votes for
        zero and the votes for one."""
    assert vote in [0, 1]

    if (vote == 0):
        v0 = encrypt(params, pub, 1)
        v1 = encrypt(params, pub, 0)
    else:
        v0 = encrypt(params, pub, 0)
        v1 = encrypt(params, pub, 1)

    return (v0, v1)

def process_votes(params, pub, encrypted_votes):
    """ Given a list of encrypted votes tally them
        to sum votes for zeros and votes for ones. """
    assert isinstance(encrypted_votes, list)
    
    # init summation var with first vote
    tv0 = encrypted_votes[0][0]
    tv1 = encrypted_votes[0][1]

    # add other votes to sum
    for i in range(1,len(encrypted_votes)):
        tv0 = add(params, pub, tv0, encrypted_votes[i][0])
        tv1 = add(params, pub, tv1, encrypted_votes[i][1])
        
    return tv0, tv1

def simulate_poll(votes):
    """ Simulates the full process of encrypting votes,
        tallying them, and then decrypting the total. """

    # Generate parameters for the crypto-system
    params = setup()

    # Make keys for 3 authorities
    priv1, pub1 = keyGen(params)
    priv2, pub2 = keyGen(params)
    priv3, pub3 = keyGen(params)

    pub = groupKey(params, [pub1, pub2, pub3])

    # Simulate encrypting votes
    encrypted_votes = []
    for v in votes:
        encrypted_votes.append(encode_vote(params, pub, v))

    # Tally the votes
    total_v0, total_v1 = process_votes(params, pub, encrypted_votes)

    # Simulate threshold decryption
    privs = [priv1, priv2, priv3]
    for priv in privs[:-1]:
        total_v0 = partialDecrypt(params, priv, total_v0)
        total_v1 = partialDecrypt(params, priv, total_v1)

    total_v0 = partialDecrypt(params, privs[-1], total_v0, True)
    total_v1 = partialDecrypt(params, privs[-1], total_v1, True)

    # Return the plaintext values
    return total_v0, total_v1

###########################################################
# TASK Q1 -- Answer questions regarding your implementation
#
# Consider the following game between an adversary A and honest users H1 and H2: 
# 1) H1 picks 3 plaintext integers Pa, Pb, Pc arbitrarily, and encrypts them to the public
#    key of H2 using the scheme you defined in TASK 1.
# 2) H1 provides the ciphertexts Ca, Cb and Cc to H2 who flips a fair coin b.
#    In case b=0 then H2 homomorphically computes C as the encryption of Pa plus Pb.
#    In case b=1 then H2 homomorphically computes C as the encryption of Pb plus Pc.
# 3) H2 provides the adversary A, with Ca, Cb, Cc and C.
#
# What is the advantage of the adversary in guessing b given your implementation of 
# Homomorphic addition? What are the security implications of this?

""" Since the encryption scheme is homomorphic E(Pa+Pb) = E(Pa)+E(Pb) = Ca+Cb = C.
    This means that all the adversary needs to do is compute Ca + Cb and Cb + Cc and
    see which one matches with C. The Adversary should guess b everytime and so the game
    is not secure. 
 """

###########################################################
# TASK Q2 -- Answer questions regarding your implementation
#
# Given your implementation of the private poll in TASK 5, how
# would a malicious user implement encode_vote to (a) distrupt the
# poll so that it yields no result, or (b) manipulate the poll so 
# that it yields an arbitrary result. Can those malicious actions 
# be detected given your implementation?

""" 
    a)No.
    
    Let the values of w0,w1 be 'so far' in the threshold signature of votes counted. i.e., 
    the signature that holds the counter of results.  
  
    An attacker cant disrupt the poll so that it yields no results because it doesn't have the 
    values of w0,w1 'so far' so cant become the last to contribute and set w0,w1 = -w0,-w1 to
    cancel out the votes and set the counter to w0,w1 = 0,0.

    b)
    
    What they can do is obscure the results in some way so that results are clearly 
    incorrect and no information about the true result is revealed, for example 
    encrypting a large negative random number:

    -modify encrypt() and remove limit on m size
    -set a,b to large random negative integers
    -modify encode_vote() to return v0,v1 as encryptions of values a,b
    
    
    Yes the malicious actions can be performed undeteced given my implementation. A way to fix 	   this may be for some kind of zero-knowledge range proof to be checked by the process_votes 
    function to ensure a vote is 0 or 1.
    votes 
 """



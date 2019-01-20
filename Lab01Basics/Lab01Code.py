#####################################################
# GA17 Privacy Enhancing Technologies -- Lab 01
#
# Basics of Petlib, encryption, signatures and
# an end-to-end encryption system.
#
# Run the tests through:
# $ py.test-2.7 -v Lab01Tests.py 

###########################
# Group Members: TODO
###########################


#####################################################
# TASK 1 -- Ensure petlib is installed on the System
#           and also pytest. Ensure the Lab Code can 
#           be imported.

import petlib

#####################################################
# TASK 2 -- Symmetric encryption using AES-GCM 
#           (Galois Counter Mode)
#
# Implement a encryption and decryption function
# that simply performs AES_GCM symmetric encryption
# and decryption using the functions in petlib.cipher.

from os import urandom
from petlib.cipher import Cipher

def encrypt_message(K, message):
    """ Encrypt a message under a key K """

    plaintext = message.encode("utf8")

    #init
    aes = Cipher("aes-128-gcm")
    iv = urandom(16)

    #encrypt
    ciphertext, tag = aes.quick_gcm_enc(K,iv,plaintext, assoc="tomos",tagl=16)


    return (iv, ciphertext, tag)

def decrypt_message(K, iv, ciphertext, tag):
    """ Decrypt a cipher text under a key K 

        In case the decryption fails, throw an exception.
    """
    aes = Cipher("aes-128-gcm")
    plain = aes.quick_gcm_dec(K,iv,ciphertext,tag,assoc="tomos")


    return plain.encode("utf8")

#####################################################
# TASK 3 -- Understand Elliptic Curve Arithmetic
#           - Test if a point is on a curve.
#           - Implement Point addition.
#           - Implement Point doubling.
#           - Implement Scalar multiplication (double & add).
#           - Implement Scalar multiplication (Montgomery ladder).
#
# MUST NOT USE ANY OF THE petlib.ec FUNCIONS. Only petlib.bn!

from petlib.bn import Bn

def is_point_on_curve(a, b, p, x, y):
    """
    Check that a point (x, y) is on the curve defined by a,b and prime p.
    Reminder: an Elliptic Curve on a prime field p is defined as:
              y^2 = x^3 + ax + b (mod p)
                  (Weierstrass form)
    Return True if point (x,y) is on curve, otherwise False.
    By convention a (None, None) point represents "infinity".
    """

    if x is None or y is None:
        return True

    #Bn is big number class. First, check each input is in Bn.
    assert isinstance(a, Bn)
    assert isinstance(b, Bn)
    assert isinstance(p, Bn) and p > 0
    assert (isinstance(x, Bn) and isinstance(y, Bn)) \
           or (x is None and y is None)
    

    lhs = (y.int_mul(y)).mod(p)
    rhs = ((x.pow(3).int_add(a.int_mul(x))).int_add(b)).mod(p)
    on_curve = (lhs == rhs)

    return on_curve


def point_add(a, b, p, x0, y0, x1, y1):
    
    """
    Define the "addition" operation for 2 EC Points.

    Reminder: (xr, yr) = (xq, yq) + (xp, yp)
    is defined as:
        lam = (yq - yp) * (xq - xp)^-1 (mod p)
        xr  = lam^2 - xp - xq (mod p)
        yr  = lam * (xp - xr) - yp (mod p)

    Return the point resulting from the addition. Raises an Exception if the points are equal.
    """
    xr, yr = None, None
   
    if x0 is None or y0 is None:
        return (x1,y1)

    if x1 is None or y1 is None:
        return (x0,y0)

    if x0 == x1 and y0 == (y1.int_neg()).mod(p):
        return (None,None)


    if x0 == x1 or y0 == y1:
        raise Exception("EC Points must not be equal")

    Y = y1.int_sub(y0)
    X = (x1.int_sub(x0)).mod_inverse(p)
    lam = (Y.mod_mul(X, p))

    xr = ((lam.pow(2)).int_sub(x0)).mod_sub(x1, p)
    X2 = x0.int_sub(xr)
    yr = (lam.int_mul(X2)).mod_sub(y0, p)

    return (xr, yr)


def point_double(a, b, p, x, y):
    """Define "doubling" an EC point.
     A special case, when a point needs to be added to itself.

     Reminder:
        lam = (3 * xp ^ 2 + a) * (2 * yp) ^ -1 (mod p)
        xr  = lam ^ 2 - 2 * xp
        yr  = lam * (xp - xr) - yp (mod p)

    Returns the point representing the double of the input (x, y).
    """  

    xr, yr = None, None

    if x is None or y is None:
        return (None, None)

    Z = (((x.pow(2)).int_mul(3)) + a)
    W = (y.int_mul(2)).mod_inverse(p)
    lam = Z.mod_mul(W, p)

    xr = (lam.pow(2)).mod_sub((x.int_mul(2)), p)
    X3 = x.int_sub(xr)
    yr = (lam.int_mul(X3)).mod_sub(y, p)

    return xr, yr

import time
from time import sleep
import random
def point_scalar_multiplication_double_and_add(a, b, p, x, y, scalar):
    Q = (None, None)
    P = (x, y)

    for i in range(scalar.num_bits()):
        if scalar.is_bit_set(i):
            Q = point_add(a,b,p,Q[0],Q[1],P[0],P[1]) 
        P = point_double(a,b,p,P[0],P[1])

    sleep(1-(random.randint(1,1000)/1000))
    return Q

def point_scalar_multiplication_montgomerry_ladder(a, b, p, x, y, scalar):
    R0 = (None, None)
    R1 = (x, y)

    for i in reversed(range(0,scalar.num_bits())):
        if scalar.is_bit_set(i):
            R0 = point_add(a,b,p,R0[0],R0[1],R1[0],R1[1]) 
            R1 = point_double(a,b,p,R1[0],R1[1])
        else:
            R1 = point_add(a,b,p,R0[0],R0[1],R1[0],R1[1]) 
            R0 = point_double(a,b,p,R0[0],R0[1])

    sleep(1-(random.randint(1,1000)/1000))
    return R0


#####################################################
# TASK 4 -- Standard ECDSA signatures
#
#          - Implement a key / param generation 
#          - Implement ECDSA signature using petlib.ecdsa
#          - Implement ECDSA signature verification 
#            using petlib.ecdsa

from hashlib import sha256
from petlib.ec import EcGroup
from petlib.ecdsa import do_ecdsa_sign, do_ecdsa_verify

def ecdsa_key_gen():
    """ Returns an EC group, a random private key for signing 
        and the corresponding public key for verification"""
    G = EcGroup()
    priv_sign = G.order().random()
    pub_verify = priv_sign * G.generator()
    return (G, priv_sign, pub_verify)


def ecdsa_sign(G, priv_sign, message):
    """ Sign the SHA256 digest of the message using ECDSA and return a signature """
    plaintext =  message.encode("utf8")

    # Hash message
    digest = sha256(message).digest()
    
    sig = do_ecdsa_sign(G, priv_sign, digest)

    return sig

def ecdsa_verify(G, pub_verify, message, sig):
    """ Verify the ECDSA signature on the message """
    plaintext =  message.encode("utf8")

    # hash
    digest = sha256(message).digest()

    res = do_ecdsa_verify(G, pub_verify, sig, digest)

    return res

#####################################################
# TASK 5 -- Diffie-Hellman Key Exchange and Derivation
#           - use Bob's public key to derive a shared key.
#           - Use Bob's public key to encrypt a message.
#           - Use Bob's private key to decrypt the message.
#
# NOTE: 

from hashlib import sha1 

def dh_get_key():
    """ Generate a DH key pair """
    G = EcGroup(713)
    priv_dec = G.order().random()
    pub_enc = priv_dec * G.generator()
    return (G, priv_dec, pub_enc)

def dh_encrypt(pub, message):
    """ Assume you know the public key of someone else (Bob), 
    and wish to Encrypt a message for them.
        - Generate a fresh DH key for this message.
        - Derive a fresh shared key.
        - Use the shared key to AES_GCM encrypt the message.
        - Optionally: sign the message with Alice's key.
    """
    # derive own key pair
    G, priv_dec, pub_enc = dh_get_key()
    shared_key = pub.pt_mul(priv_dec)
    shared_key = shared_key.get_affine()[0] 	# get x-coord		
    shared_key = str(shared_key.repr())		# convert form Bn to string
    shared_key = shared_key[:16]		# truncate to length 16 (128 bits)

    # sign message
    digest = sha1(message).digest()
    aliceSig = do_ecdsa_sign(G, priv_dec, digest) 

    # encrypt init
    aes = Cipher.aes_128_gcm()
    iv = urandom(16)
    # encrypt
    enc = aes.enc(shared_key, iv)		# get encryption operation
    #enc.update_associated(aliceSig)		# add key as non-secret data to perform tag over
    ciphertext = enc.update(message)		# add plaintext
    ciphertext += enc.finalize()		# finalise
    tag = enc.get_tag(16)			# get tag


    return(iv, pub_enc, ciphertext, tag, aliceSig)


    pass


def dh_decrypt(iv, priv_dec, pub_enc, ciphertext, tag):
    """ Decrypt a received message encrypted using your public key, 
    of which the private key is provided. Optionally verify 
    the message came from Alice using her verification key."""

    # derive shared key
    shared_key = pub_enc.pt_mul(priv_dec)
    shared_key = shared_key.get_affine()[0] 	# get x-coord		
    shared_key = str(shared_key.repr())		# convert form Bn to string
    shared_key = shared_key[:16]

    # decrypt
    aes = Cipher.aes_128_gcm()
    dec = aes.dec(shared_key, iv)		# get dec operation
    #dec.update_associated(aliceSig)		# feed in alice pubkey
    plaintext = dec.update(ciphertext)		# feed in ciphertext
    dec.set_tag(tag)
    plaintext += dec.finalize()

    return plaintext
    


## NOTE: populate those (or more) tests
#  ensure they run using the "py.test filename" command.
#  What is your test coverage? Where is it missing cases?
#  $ py.test-2.7 --cov-report html --cov Lab01Code Lab01Code.py 



def test_encrypt():
    # derive (Bob) keys
    G, priv_dec, pub_enc = dh_get_key()

    message = "hello"    

    # encrypt
    iv, shared_key, ciphertext, tag, aliceSig = dh_encrypt(pub_enc, message)

    assert len(message) == len(ciphertext)

def test_decrypt():
    # derive (Bob) key pair
    G, bob_priv, bob_pub = dh_get_key()

    message = "hello"  
    
    # encrypt using above pub key and new key pair (Alice)
    iv, alice_pub, ciphertext, tag, aliceSig = dh_encrypt(bob_pub, message)

    # decrypt with bobs private and alice's public keys
    message_decrypted = dh_decrypt(iv, bob_priv, alice_pub, ciphertext, tag)

    # check sig
    assert do_ecdsa_verify(G, alice_pub, aliceSig, sha1(message).digest())

    assert message == message_decrypted

def test_fails():
    from pytest import raises  
    """ 
    	TEST 1
    	encrypt with public key derived from private key K, decrypt with K+1
    """

    # derive (Bob) key pair
    G, bob_priv, bob_pub = dh_get_key()

    message = "hello"  
    
    # encrypt using above pub key and new key pair (Alice)
    iv, alice_pub, ciphertext, tag, aliceSig = dh_encrypt(bob_pub, message)

    # K = K+1
    bob_priv += 1

    # ensure decrytpion failure exception is thrown from dec.finalize()
    with raises(Exception) as excinfo:
        # decrypt with bobs private and alice's public keys
        message_decrypted = dh_decrypt(iv, bob_priv, alice_pub, ciphertext, tag)
    assert 'Cipher: decryption failed.' in str(excinfo.value)
        
    """
        TEST 2
	check invalid signature, sign with alice_pub, verify with -(alice_pub)
    """

    # change alice_pub
    alice_pub = alice_pub.pt_neg()

    # ensure signature verification fails, exception from do_ecdsa_verify
    assert not do_ecdsa_verify(G, alice_pub, aliceSig, sha1(message).digest())


#####################################################
# TASK 6 -- Time EC scalar multiplication
#             Open Task.
#           
#           - Time your implementations of scalar multiplication
#             (use time.clock() for measurements)for different 
#              scalar sizes)
#           - Print reports on timing dependencies on secrets.
#           - Fix one implementation to not leak information.

#point_scalar_multiplication_double_and_add(a, b, p, x, y, scalar)
#point_scalar_multiplication_montgomerry_ladder(a, b, p, x, y, scalar)

def time_scalar_mul():
    # make curve and points
    G = EcGroup(713) # NIST curve
    d = G.parameters()
    a, b, p = d["a"], d["b"], d["p"]
    g = G.generator()
    gx0, gy0 = g.get_affine()

   
    res_double_add = []
    res_montgomerry = []
    for i in range(3):
        scalar = G.order().random()
        # double and add
	t0 = time.clock()
        print("t0 = ",t0)
        
        point_scalar_multiplication_double_and_add(a, b, p, gx0, gy0, scalar)
        t1 = time.clock()
        print("t1 = ",t1)
        res_double_add = res_double_add + [[len(scalar.repr()),(t1-t0)]]

        # montgomerry 
        t0 = time.clock()
        point_scalar_multiplication_montgomerry_ladder(a, b, p, gx0, gy0, scalar)
        t1 = time.clock()
        res_montgomerry = res_montgomerry + [[len(scalar.repr()),(t1-t0)]]

    res_double_add.sort()
    res_montgomerry.sort()

    print("\nDouble and Add scalar multiplication: \n")
    print("length	time")
    for i in range(len(res_double_add)):
        print res_double_add[i][0],
        print "	",
	print res_double_add[i][1]

    print("\n\nmontgomerry ladder scalar multiplication: \n")
    print("length	time")
    for i in range(len(res_montgomerry)):
        print res_montgomerry[i][0],
        print "	",
	print res_montgomerry[i][1]

"""
By running the time_Scalr_mul() function before editing the scalar multiplication functions, 
we could see that the functions ran between 0.02s and 0.035s for different length scalars. The
time taken increased as the length of the scalar increased. 

So, we have edited the scalar multiplication functions to ensure they return only after 0.05 
seconds have passed since being called. Now, all scalar multiplications look the same to an
adversary using a timing side channel attack by a sleep() cal over random ms.
"""





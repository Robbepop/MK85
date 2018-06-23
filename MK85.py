from ctypes import *
import sys

def And (*args):
    assert len(args) >= 2
    if len(args)==2:
        return args[0] & args[1]
    else:
        return args[0] & And(*args[1:])

def Or (*args):
    assert len(args) >= 2
    if len(args)==2:
        return args[0] | args[1]
    else:
        return args[0] | Or(*args[1:])

class expr:

    def __init__ (self, lib, ctx, expr):
        self.lib=lib
        self.ctx=ctx
        self.expr=expr

    def __str__ (self):
       return self.lib.expr_to_string(self.expr)

    # we need op1 to get width of it
    def make_const_if_need (self, op1, op2):
        if type(op2)==int or type(op2)==long:
            w=self.lib.get_width_of_expr(op1)
            op2=expr(self.lib, self.ctx, self.lib.create_const_expr(MK85.TY_BITVEC, op2, w))
        if type(op2)==bool:
            op2=expr(self.lib, self.ctx, self.lib.create_const_expr(MK85.TY_BOOL, op2, 1))
        return op2

    def __and__ (self, other):
        other=self.make_const_if_need(self.expr, other)

        if self.lib.get_type_of_expr(self.expr)==MK85.TY_BOOL:
            e=self.lib.create_bin_expr(MK85.OP_AND, self.expr, other.expr)
        else:
            e=self.lib.create_bin_expr(MK85.OP_BVAND, self.expr, other.expr)

        return expr(self.lib, self.ctx, e)

    def __or__ (self, other):
        other=self.make_const_if_need(self.expr, other)

        if self.lib.get_type_of_expr(self.expr)==MK85.TY_BOOL:
            e=self.lib.create_bin_expr(MK85.OP_OR, self.expr, other.expr)
        else:
            e=self.lib.create_bin_expr(MK85.OP_BVOR, self.expr, other.expr)

        return expr(self.lib, self.ctx, e)

    def __xor__ (self, other):
        other=self.make_const_if_need(self.expr, other)
        e=self.lib.create_bin_expr(MK85.OP_BVXOR, self.expr, other.expr)
        return expr(self.lib, self.ctx, e)

    def __rshift__ (self, other):
        other=self.make_const_if_need(self.expr, other)
        e=self.lib.create_bin_expr(MK85.OP_BVLSHR, self.expr, other.expr)
        return expr(self.lib, self.ctx, e)

    def __add__ (self, other):
        other=self.make_const_if_need(self.expr, other)
        e=self.lib.create_bin_expr(MK85.OP_BVADD, self.expr, other.expr)
        return expr(self.lib, self.ctx, e)

    def __mul__ (self, other):
        other=self.make_const_if_need(self.expr, other)
        e=self.lib.create_bin_expr(MK85.OP_BVMUL, self.expr, other.expr)
        return expr(self.lib, self.ctx, e)

    def __eq__ (self, other):
        other=self.make_const_if_need(self.expr, other)
        e=self.lib.create_bin_expr(MK85.OP_EQ, self.expr, other.expr)
        return expr(self.lib, self.ctx, e)

    def __ne__ (self, other):
        other=self.make_const_if_need(self.expr, other)
        e=self.lib.create_bin_expr(MK85.OP_NEQ, self.expr, other.expr)
        return expr(self.lib, self.ctx, e)

    def __ge__ (self, other):
        other=self.make_const_if_need(self.expr, other)
        e=self.lib.create_bin_expr(MK85.OP_BVUGE, self.expr, other.expr)
        return expr(self.lib, self.ctx, e)

    def __gt__ (self, other):
        other=self.make_const_if_need(self.expr, other)
        e=self.lib.create_bin_expr(MK85.OP_BVUGT, self.expr, other.expr)
        return expr(self.lib, self.ctx, e)

    def __le__ (self, other):
        other=self.make_const_if_need(self.expr, other)
        e=self.lib.create_bin_expr(MK85.OP_BVULE, self.expr, other.expr)
        return expr(self.lib, self.ctx, e)

    def __lt__ (self, other):
        other=self.make_const_if_need(self.expr, other)
        e=self.lib.create_bin_expr(MK85.OP_BVULT, self.expr, other.expr)
        return expr(self.lib, self.ctx, e)

    def Not (self):
        e=self.lib.create_unary_expr(MK85.OP_NOT, self.expr)
        return expr(self.lib, self.ctx, e)

class MK85:

    TY_BOOL=0
    TY_BITVEC=1

    OP_NOT=0
    OP_BVSHL=1
    OP_BVLSHR=2
    OP_BVASHR=3
    OP_BVSHL1=4
    OP_BVSHR1=5
    OP_EQ=6
    OP_NEQ=7
    OP_AND=8
    OP_OR=9
    OP_XOR=10
    OP_BVNOT=11
    OP_BVNEG=12
    OP_BVXOR=13
    OP_BVADD=14
    OP_BVAND=15
    OP_BVOR=16
    OP_BVMUL=17
    OP_BVMUL_NO_OVERFLOW=18
    OP_BVSUB=19
    OP_BVUGE=20
    OP_BVUGT=21
    OP_BVULE=22
    OP_BVULT=23
    OP_BVSGE=24
    OP_BVSGT=25
    OP_BVSLE=26
    OP_BVSLT=27
    OP_BVSUBGE=28
    OP_BVUDIV=29
    OP_BVUREM=30
    OP_ITE=31

    def __init__(self, verbose=0):
        for d in sys.path:
            try:
                self.lib=CDLL(d+"/MK85/libMK85.so")
            except:
                pass

        if self.lib==None:
            print "Error: Can't find libMK85.so"
            exit(0)

        self.lib.create_bin_expr.argtypes=[c_uint, c_void_p, c_void_p]
        self.lib.create_bin_expr.restype=c_void_p

        self.lib.create_distinct_expr.argtypes=[c_void_p]
        
	self.lib.create_const_expr.argtypes=[c_uint, c_ulong, c_int]

        self.lib.create_assert.argtypes=[c_uint, c_void_p]

        self.lib.set_next.argtypes=[c_void_p, c_void_p]

        self.lib.check_sat.restype=c_bool

        self.lib.get_variable_val.restype=c_uint

        self.lib.set_verbose(verbose)
        self.ctx=self.lib.MK85_init()
        self.state=None
        self.vars={}
        self.solution={}

        self.lib.expr_to_string.argtypes=[c_uint]
        self.lib.expr_to_string.restype=c_char_p

    def Bool(self, name):
        assert name not in self.vars.keys()
        self.vars[name]=MK85.TY_BOOL
        SMT_var=self.lib.declare_variable(self.ctx, name, MK85.TY_BOOL, 1, 0)
        return expr(self.lib, self.ctx, self.lib.create_id(self.ctx, name))

    def BitVec(self, name, width):
        assert name not in self.vars.keys()
        self.vars[name]=MK85.TY_BITVEC
        SMT_var=self.lib.declare_variable(self.ctx, name, MK85.TY_BITVEC, width, 0)
        return expr(self.lib, self.ctx, self.lib.create_id(self.ctx, name))

    def var_by_name (self, name):
        return expr(self.lib, self.ctx, self.lib.create_id(self.ctx, name))

    def add (self, constraint):
        self.lib.create_assert(self.ctx, constraint.expr)

    def const(self, c, w):
        return expr(self.lib, self.ctx, self.lib.create_const_expr(c, w))

    def check (self):
        self.state=self.lib.check_sat(self.ctx)
        return self.state

    def model (self):
        for v in self.vars:
            self.solution[v]=self.lib.get_variable_val(self.ctx, v);
        return self.solution

    def Distinct(self, args):
        for i in range(len(args)-1):
            self.lib.set_next(args[i].expr, args[i+1].expr)
        return expr(self.lib, self.ctx, self.lib.create_distinct_expr(args[0].expr))

    def BVMulNoOverflow (self, op1, op2):
        e=self.lib.create_bin_expr(MK85.OP_BVMUL_NO_OVERFLOW, op1.expr, op2.expr)
        return expr(self.lib, self.ctx, e)

    def If (self, op1, op2, op3):
        op3=op2.make_const_if_need(op2, op3)
        e=self.lib.create_ternary_expr(MK85.OP_ITE, op1.expr, op2.expr, op3.expr)
        return expr(self.lib, self.ctx, e)

    def BitVecConst(self, val, w):
        return expr(self.lib, self.ctx, self.lib.create_const_expr(MK85.TY_BITVEC, val, w))


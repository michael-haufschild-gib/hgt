#!/usr/bin/env python3
"""Finite period coefficients from HB positive-delay characteristic current."""

from __future__ import annotations

import cmath
import math
from functools import lru_cache

import numpy as np


def pmul(*polys):
    out=[1+0j]
    for p in polys:
        nxt=[0j]*(len(out)+len(p)-1)
        for i,a in enumerate(out):
            for j,b in enumerate(p): nxt[i+j]+=a*b
        out=nxt
    return out


def gbinom(alpha,k):
    out=1+0j
    for j in range(k): out*=alpha-j
    return out/math.factorial(k)


def H(alpha,n,P,b):
    return sum(P[k]*gbinom(alpha,n-k)*b**(n-k) for k in range(min(n,len(P)-1)+1))


def coefficients(delta: complex,h: float):
    c=math.exp(-h); b=(1-c)/(2*c)
    xm1=[-1,1]; xmD=[-c,(1+c)/2]; two=[2,-1]
    Lp=[3-delta,delta]
    Tp=[(3+delta)*c,(3+delta)*(1-c)/2-delta]
    oneD=[1-c,-(1-c)/2]
    s=(delta-3)/2; t=(-delta-3)/2
    ks=s*(s-1)/4; kt=t*(t-1)/4
    es=(2*s+1)*(2*s+2); et=(2*t+1)*(2*t+2)
    P00=pmul(xm1,xmD,two)
    P10=pmul(xm1,xm1,xmD,two,Lp)
    P01=pmul(xm1,xmD,xmD,two,Tp)
    P11=pmul(xm1,xm1,xmD,xmD,two,Lp,Tp)
    Pjet=pmul(P11,oneD)
    C00=c*c/2*H(delta,4,P00,b)
    C10=ks*c*c*H(delta,5,P10,b)
    C01=kt*c*H(delta-1,5,P01,b)
    C11=2*ks*kt*c*H(delta-1,6,P11,b)
    Cjet=ks*kt*H(delta-2,5,Pjet,b)
    CQ=es*C01-et*C10+(delta+3)*C11
    return C00,C10,C01,C11,Cjet,CQ


@lru_cache(maxsize=None)
def nodes(order):
    return np.polynomial.legendre.leggauss(order)


def integrate_gl(fn,a,b,order):
    if b<=a: return 0j
    xx,ww=nodes(order); mid=(a+b)/2; rad=(b-a)/2
    return rad*sum(w*fn(mid+rad*x) for x,w in zip(xx,ww))


def transition(x):
    if x<=0: return 0.0
    if x>=1: return 1.0
    a=math.exp(-1/x); b=math.exp(-1/(1-x))
    return a/(a+b)


def transition_first(x):
    if x<=0 or x>=1: return 0.0
    q=transition(x)
    return q*(1-q)*(1/x**2+1/(1-x)**2)


def clock_J_I10(V,h,order=40):
    U=max(0.0,V-h)
    top=min(U,1.0)
    J=integrate_gl(lambda v: math.exp(-6*v)*transition(v+h)*transition(v),0,top,order).real
    if U>1:
        J+=(math.exp(-6)-math.exp(-6*U))/6
    top10=min(U,max(0.0,1-h),1.0)
    I10=integrate_gl(lambda v: math.exp(-6*v)*transition_first(v+h)*transition(v),0,top10,order).real
    return J,I10


def period_R(delta,h,order=40):
    if h==0: return math.log(2)+0j
    eh=math.exp(h)
    return math.exp(-2*h)*integrate_gl(
        lambda y: cmath.exp((delta-2)*math.log(1+(eh-1)*y))/y,.5,1,order)


def direct_period_density(delta,h,V,order=40):
    _,_,_,C11,Cjet,CQ=coefficients(delta,h)
    R=period_R(delta,h,order)
    J,I10=clock_J_I10(V,h,order)
    return R*((CQ+Cjet)*J-C11*I10)


def direct_period_integral(delta,V,order=40,h_order=None):
    gamma=abs(delta.imag)/2
    if h_order is None: h_order=max(order,int(order+2.5*gamma*V/math.pi))
    # Split at clock transition. Global Gauss rules then see smooth integrands.
    q0=max(order,min(h_order,order+int(2.5*gamma/math.pi)))
    out=integrate_gl(lambda h: direct_period_density(delta,h,V,order),0,min(1,V),q0)
    if V>1:
        out+=integrate_gl(lambda h: direct_period_density(delta,h,V,order),1,V,h_order)
    return out


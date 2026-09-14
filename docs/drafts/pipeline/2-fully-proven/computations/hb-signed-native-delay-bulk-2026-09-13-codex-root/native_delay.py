#!/usr/bin/env python3
"""Numerical literal source for D4BMSpinTwoDelay.signed_delay_finite_transfer."""

from __future__ import annotations

import cmath
import math
from functools import lru_cache

import mpmath as mp
import numpy as np


@lru_cache(maxsize=None)
def gauss_nodes(order):
    return np.polynomial.legendre.leggauss(order)


def gl(fn, a, b, order):
    if b <= a:
        return np.asarray(fn((a+b)/2))*0
    xx, ww = gauss_nodes(order)
    mid, rad = (a+b)/2, (b-a)/2
    out = None
    for x, w in zip(xx, ww):
        value = np.asarray(fn(mid+rad*x), dtype=np.complex128)
        out = w*value if out is None else out+w*value
    return rad*out


def transition(x):
    if x <= 0:
        return 0.0
    if x >= 1:
        return 1.0
    a, b = math.exp(-1/x), math.exp(-1/(1-x))
    return a/(a+b)


def transition_first(x):
    if x <= 0 or x >= 1:
        return 0.0
    q = transition(x)
    return q*(1-q)*(1/x**2+1/(1-x)**2)


def profile(s, u, v):
    eta = (2*s+1)*(2*s+2)
    onset = s*(s-1)/2*u*(3+(2*s+3)*u)/(1+u)
    return cmath.exp(2*s*v)*(eta*transition(v)-onset*transition_first(v))


def radial_unit(x):
    return -math.tanh(x)


def clock_density(gamma, branch, x, y, V, h, order):
    u, w = radial_unit(x), radial_unit(y)
    s = complex(-3, 2*gamma if branch else -2*gamma)
    t = -s-3
    top = max(0.0, V-h)
    cuts = sorted(set([0.0, top] + [z for z in (1.0, 1.0-h) if 0 < z < top]))
    out = 0j
    for a, b in zip(cuts, cuts[1:]):
        out += gl(lambda v: profile(s,u,v+h)*profile(t,w,v), a, b, order)
    return complex(out)


@lru_cache(maxsize=None)
def completed_lambda_data(gamma, dps):
    with mp.workdps(dps):
        t = mp.mpf(gamma)
        s = 1+2j*t
        A = mp.power(mp.pi, -s/2)*mp.gamma(s/2)*mp.zeta(s)
        return float(mp.arg(A)), float(mp.log(abs(A)))


@lru_cache(maxsize=None)
def divisor_coefficient(gamma, n, dps):
    with mp.workdps(dps):
        t = mp.mpf(gamma)
        return float(mp.fsum(mp.cos(t*mp.log(mp.mpf(n)/(d*d)))
                             for d in range(1,n+1) if n % d == 0))


def fundamental_reduce(x, y):
    """Reduce by T and S; scalar differential invariants are unchanged."""
    for _ in range(20):
        x -= math.floor(x+0.5)
        r2 = x*x+y*y
        if r2 >= 1-2e-15:
            return x, y
        x, y = -x/r2, y/r2
    raise ArithmeticError("modular reduction did not terminate")


def scalar_jets(gamma, x, y, margin=40, dps=35, principal=False, reduce_point=True):
    """Normalized completed Eisenstein scalar and x/y jets through order two."""
    if reduce_point:
        x, y = fundamental_reduce(x, y)
    phase, log_abs_A = completed_lambda_data(float(gamma), int(dps))
    root = math.sqrt(y)
    angle = phase+gamma*math.log(y)
    c0 = 2*root*math.cos(angle)
    d0 = (c0/2-2*root*gamma*math.sin(angle))/y
    f, fx, fy, fxx, fxy = c0, 0.0, d0, 0.0, 0.0
    if not principal:
        N = max(1, int(math.ceil((gamma+margin)/(2*math.pi*y))))
        with mp.workdps(dps):
            nu = 1j*mp.mpf(gamma)
            yy = mp.mpf(y)
            for n in range(1, N+1):
                divisor = divisor_coefficient(float(gamma), n, int(dps))
                arg = 2*mp.pi*n*yy
                kval = mp.re(mp.besselk(nu, arg))
                kprime = -mp.re(mp.besselk(nu-1,arg)+mp.besselk(nu+1,arg))/2
                inv_abs_A = mp.exp(-log_abs_A)
                c_mp = 2*mp.sqrt(yy)*divisor*kval*inv_abs_A
                dc_mp = c_mp/(2*yy)+4*mp.pi*n*mp.sqrt(yy)*divisor*kprime*inv_abs_A
                c, dc = float(c_mp), float(dc_mp)
                a = 2*math.pi*n*x
                co, si = math.cos(a), math.sin(a)
                f += 2*c*co
                fy += 2*dc*co
                fx += -4*math.pi*n*c*si
                fxx += -8*math.pi**2*n*n*c*co
                fxy += -4*math.pi*n*dc*si
    mu = -(gamma*gamma+0.25)
    fyy = mu*f/(y*y)-fxx
    return f, fx, fy, fxx, fxy, fyy, x, y


def spin_density_from_jets(gamma, jets):
    f, fx, fy, fxx, fxy, fyy, _, y = jets
    mu = -(gamma*gamma+0.25)
    grad2 = y*y*(fx*fx+fy*fy)
    hxx = fxx-fy/y
    hxy = fxy+fx/y
    hyy = fyy+fy/y
    hess2 = y**4*(hxx*hxx+2*hxy*hxy+hyy*hyy)
    return 2*mu*(1-mu)*f*f+4*(1-mu)*grad2-2*hess2


def spin_circle_pair(gamma, z, X, k, theta_order, margin, dps):
    d = math.acosh(max(1.0, z))
    ch, sh, scale = math.cosh(d), math.sinh(d), math.exp(k)
    full = principal = 0.0
    for j in range(theta_order):
        theta = 2*math.pi*(j+0.5)/theta_order
        den = ch-sh*math.cos(theta)
        xx = X+scale*sh*math.sin(theta)/den
        yy = scale/den
        full += spin_density_from_jets(gamma, scalar_jets(gamma,xx,yy,margin,dps,False))
        principal += spin_density_from_jets(gamma, scalar_jets(gamma,xx,yy,margin,dps,True))
    return np.asarray((full/theta_order, principal/theta_order), dtype=np.complex128)


def delay_argument(image, x, y, h):
    reflected = -y if image else y
    return (math.cosh(h-x+y)+math.sinh(x)*math.sinh(reflected))/(math.cosh(x)*math.cosh(reflected))


def causal_start(image, x, y):
    return -2*y if image else 2*max(x-y, 0.0)


def sheet_action(gamma, image, x, y, X, k, V, h_order, clock_order,
                 theta_order, margin, dps):
    start = causal_start(image,x,y)
    if V <= start:
        return np.zeros((2,2), dtype=np.complex128)
    cuts = sorted(set([start,V]+[q for q in (1.0,) if start < q < V]))
    out = np.zeros((2,2), dtype=np.complex128)
    for a,b in zip(cuts,cuts[1:]):
        def integrand(h):
            spin = spin_circle_pair(gamma,delay_argument(image,x,y,h),X,k,
                                    theta_order,margin,dps)
            clocks = np.asarray((clock_density(gamma,True,x,y,V,h,clock_order),
                                 clock_density(gamma,False,x,y,V,h,clock_order)))
            return clocks[:,None]*spin[None,:]
        out += gl(integrand,a,b,h_order)
    return out


def signed_action(gamma, section, h_order=14, clock_order=14,
                  theta_order=24, margin=40, dps=35):
    x,y,X,k,V = (section[q] for q in ("x","y","X","k","V"))
    direct = sheet_action(gamma,False,x,y,X,k,V,h_order,clock_order,theta_order,margin,dps)
    image = sheet_action(gamma,True,x,y,X,k,V,h_order,clock_order,theta_order,margin,dps)
    signed = direct-image
    # rows: physicalRate branches (+gamma,-gamma); columns: full, principal-only.
    ordered = signed[0]-signed[1]
    rel = np.abs(ordered)/np.maximum(np.abs(signed[0])+np.abs(signed[1]),1e-300)
    direct_ordered = direct[0]-direct[1]
    image_ordered = image[0]-image[1]
    _, logA = completed_lambda_data(float(gamma),int(dps))
    return {"direct":direct,"image":image,"signed":signed,"ordered":ordered,
            "relative":rel,"direct_ordered":direct_ordered,
            "image_ordered":image_ordered,"log_abs_completed_lambda_sq":2*logA}

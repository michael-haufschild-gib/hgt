#!/usr/bin/env python3
"""Independent normalization, modularity, and principal-circle validation."""

from __future__ import annotations

import json
import math
import os

import mpmath as mp

from native_delay import (completed_lambda_data, scalar_jets, spin_circle_pair,
                          spin_density_from_jets)


def direct_scalar(gamma,x,y,N,dps):
    with mp.workdps(dps):
        t=mp.mpf(gamma);xx=mp.mpf(x);yy=mp.mpf(y);s=1+2j*t
        A=mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)
        value=mp.conj(A)*mp.power(yy,mp.mpf('.5')-1j*t)+A*mp.power(yy,mp.mpf('.5')+1j*t)
        plus=minus=0
        for n in range(1,N+1):
            coeff=mp.power(n,1j*t)*mp.fsum(mp.power(d,-2j*t) for d in range(1,n+1) if n%d==0)
            carrier=coeff*mp.sqrt(yy)*mp.besselk(1j*t,2*mp.pi*n*yy)
            plus+=carrier*mp.exp(2j*mp.pi*n*xx)
            minus+=carrier*mp.exp(-2j*mp.pi*n*xx)
        return (value+2*(plus+minus))/abs(A)


def legendre_power(alpha,d):
    scale=(mp.cosh(d)+1)/2
    radius=mp.sinh(d)/(mp.cosh(d)+1)
    return mp.power(scale,-alpha)*mp.hyp2f1(alpha,alpha,1,radius*radius)


def principal_spin_exact(gamma,d,k,dps):
    with mp.workdps(dps):
        phase,_=completed_lambda_data(float(gamma),int(dps));t=mp.mpf(gamma);y=mp.exp(k)
        out=0
        for alpha,coeff in ((1-2j*t,mp.exp(-2j*phase)/2),
                            (1,mp.mpf(1)),
                            (1+2j*t,mp.exp(2j*phase)/2)):
            lam=alpha*(alpha-1)
            out+=coeff*mp.power(y,alpha)*(-lam*lam+2*lam)*legendre_power(alpha,d)
        return out


def main():
    mp.mp.dps=70;gamma=float(mp.im(mp.zetazero(1)));x,y=.17,1.13;N=32
    jets=scalar_jets(gamma,x,y,80,60,False,False)
    direct=direct_scalar(gamma,x,mp.mpf(y),N,70)
    step=mp.mpf("1e-20")
    derivative=(direct_scalar(gamma,x,mp.mpf(y)+step,N,100)-
                direct_scalar(gamma,x,mp.mpf(y)-step,N,100))/(2*step)
    r2=x*x+y*y;sx,sy=-x/r2,y/r2
    jets_s=scalar_jets(gamma,sx,sy,80,60,False,False)
    d=.83;k=1.5
    circle=spin_circle_pair(gamma,math.cosh(d),.13,k,64,70,60)[1]
    exact=principal_spin_exact(gamma,mp.mpf(d),mp.mpf(k),70)
    payload={
      "gamma":gamma,"point":[x,y],"terms":N,
      "scalar_relative_error":str(abs(direct-jets[0])/max(1,abs(direct))),
      "vertical_derivative_relative_error":str(abs(derivative-jets[2])/max(1,abs(derivative))),
      "raw_modular_scalar_relative_error":float(abs(jets[0]-jets_s[0])/max(1,abs(jets[0])+abs(jets_s[0]))),
      "raw_modular_spin_relative_error":float(abs(spin_density_from_jets(gamma,jets)-spin_density_from_jets(gamma,jets_s))/
                                                max(1,abs(spin_density_from_jets(gamma,jets))+abs(spin_density_from_jets(gamma,jets_s)))),
      "principal_circle_relative_error":str(abs(exact-circle)/max(1,abs(exact))),
      "principal_circle_exact":str(exact),"principal_circle_numeric":[float(circle.real),float(circle.imag)]}
    with open("validation.json.tmp","w") as f:json.dump(payload,f,indent=2)
    os.replace("validation.json.tmp","validation.json")


if __name__=="__main__":main()

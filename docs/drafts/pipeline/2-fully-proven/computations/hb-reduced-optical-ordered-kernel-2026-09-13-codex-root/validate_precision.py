#!/usr/bin/env python3
"""Independent high-precision challenges for reported structural findings."""

from __future__ import annotations

import json
import mpmath as mp

from inverse_roots import coeff_mp


def rel(rho,L,x):
    c,a,b=coeff_mp(rho,L,x)
    return abs(c)/max(abs(a)+abs(b),mp.mpf('1e-150'))


def main():
    mp.mp.dps=140
    z95=mp.zetazero(95)
    rho95=mp.mpc('0.5',mp.im(z95))
    L95=mp.mpf('37.69760942252745'); x95=mp.mpf('0.578125')
    c95,a95,b95=coeff_mp(rho95,L95,x95)

    root_line=mp.findroot(lambda z: coeff_mp(z,mp.mpf(12),mp.mpf('.71'))[0],
                          (mp.mpc('.5','122.93'),mp.mpc('.5','122.96')),tol=mp.mpf('1e-120'))
    root_off=mp.findroot(lambda z: coeff_mp(z,mp.mpf(12),mp.mpf('.71'))[0],
                         (mp.mpc('2.28','2.90'),mp.mpc('2.31','2.95')),tol=mp.mpf('1e-120'))
    line_checks=[]
    for n,L,x in [(1,'7','.37'),(95,'37.69760942252745','.578125'),(256,'23','.89')]:
        rho=mp.mpc('.5',mp.im(mp.zetazero(n))); c,a,b=coeff_mp(rho,mp.mpf(L),mp.mpf(x))
        line_checks.append({"n":n,"real_fraction":mp.nstr(abs(mp.re(c))/abs(c),25),
                            "relative_residual":mp.nstr(abs(c)/(abs(a)+abs(b)),25)})
    complement_checks=[]
    for rho,L,x in [(mp.mpc('.37','14.2'),'7','.37'),(root_off,'12','.71'),(mp.mpc('.8','99'),'23','.49')]:
        c,_,_=coeff_mp(rho,mp.mpf(L),mp.mpf(x)); cc,_,_=coeff_mp(1-rho,mp.mpf(L),mp.mpf(x))
        complement_checks.append(mp.nstr(abs(c+cc)/max(abs(c)+abs(cc),mp.mpf('1e-150')),25))
    payload={
        "dps":mp.mp.dps,
        "exact_zeta_95_best_grid_point":{"gamma":mp.nstr(mp.im(z95),50),"relative_residual":mp.nstr(abs(c95)/(abs(a95)+abs(b95)),50),
                                          "abs_coefficient":mp.nstr(abs(c95),50)},
        "critical_root":{"rho":mp.nstr(root_line,60),"critical_distance":mp.nstr(abs(mp.re(root_line)-mp.mpf('.5')),30),
                         "local_relative_residual":mp.nstr(rel(root_line,12,mp.mpf('.71')),30)},
        "offcritical_root":{"rho":mp.nstr(root_off,60),"local_relative_residual":mp.nstr(rel(root_off,12,mp.mpf('.71')),30),
                            "complement":mp.nstr(1-root_off,60)},
        "line_checks":line_checks,
        "complement_antisymmetry_relative_errors":complement_checks,
        "self_complementary_all_point_max":mp.nstr(max(rel(mp.mpf('.5'),L,x) for L,x in [(7,'.37'),(12,'.71'),(23,'.49')]),25),
        "moving_characteristic_endpoint_abs":mp.nstr(abs(coeff_mp(rho95,7,0)[0]),25),
    }
    with open('precision_validation.json','w') as f: json.dump(payload,f,indent=2)


if __name__=='__main__': main()

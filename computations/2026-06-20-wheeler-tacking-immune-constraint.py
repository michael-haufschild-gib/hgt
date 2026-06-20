#!/usr/bin/env python3
# WILD-ANALOGY (correct protocol): rng remote nodes = SAILING-TACKING (+) IMMUNE NEGATIVE-SELECTION.
# Seed 1060414838554611887.  This experiment runs ON THE REMOTE CONSTRAINT (not on any HT object).
#
# SHARED CONSTRAINT (the collision): a target sits INSIDE a forbidden region (no-go cone into the wind /
# the self-shape band). You reach it not by a flow toward it but by oblique moves; moves that land in the
# forbidden region are NEGATIVELY SELECTED (deleted, immune-style). QUESTION (the experiment): what does
# the optimal heading do when the forbidden region is centered ON THE SYMMETRY AXIS of the constraint?
#
# Constraint model: "polar" v(theta) = boat speed at angle theta off the wind; upwind progress
# VMG(theta)=v(theta)*cos(theta). Negative-selection deletes a band |theta-theta_s|<w (self-mimicry).
# We test SYMMETRIC polar (exact reflection symmetry about the VMG optimum) vs BROKEN (epsilon).
import numpy as np

def run(polar, label):
    th=np.linspace(0.5, 89.5, 20001)*np.pi/180.0
    v=polar(th); vmg=v*np.cos(th)
    i0=int(np.argmax(vmg)); th0=th[i0]
    th_s=th0                                  # put the self-band ON the unconstrained optimum (the axis)
    print(f"\n[{label}]  unconstrained optimum theta* = {np.degrees(th0):.3f} deg, VMG*={vmg[i0]:.5f}")
    print(f"   {'w(deg)':>7} | {'#optima':>7} | {'tack headings (deg)':>26} | {'sum':>8} | {'VMG':>8} | {'symmetry pair?'}")
    for wdeg in [0.0, 1.0, 3.0, 7.0, 15.0]:
        w=wdeg*np.pi/180.0
        valid = np.abs(th-th_s) >= w           # negative selection: delete the self-band
        vv=np.where(valid, vmg, -np.inf)
        # find local maxima among valid headings
        peaks=[]
        for i in range(1,len(th)-1):
            if valid[i] and vv[i]>=vv[i-1] and vv[i]>=vv[i+1] and vv[i]>-1e9:
                peaks.append(i)
        # collapse near-equal-VMG peaks to the top tier
        if peaks:
            vmax=max(vv[i] for i in peaks)
            top=[i for i in peaks if vmax-vv[i] < 1e-6*abs(vmax)+1e-9]
            # keep at most the two extreme ones (the tack pair)
            if len(top)>=2: top=[min(top),max(top)]
        else:
            top=[int(np.argmax(vv))]
        hs=[np.degrees(th[i]) for i in top]
        ssum=sum(hs)
        vmgtop=max(vv[i] for i in top)
        paired = (len(hs)==2 and abs(ssum-2*np.degrees(th_s))<0.2)
        print(f"   {wdeg:7.1f} | {len(top):7d} | {str([round(h,2) for h in hs]):>26} | {ssum:8.3f} | {vmgtop:8.5f} | {paired}")

# SYMMETRIC polar: toy lift v=sin(theta) -> VMG=sin cos symmetric about 45 deg (exact reflection symmetry)
run(lambda th: np.sin(th), "SYMMETRIC polar v=sin(theta): exact reflection symmetry about the optimum")
# BROKEN: v=sin(theta)*(1+eps*sin(theta)) breaks the exact symmetry of the constraint
for eps in [0.15, 0.4]:
    run(lambda th,e=eps: np.sin(th)*(1+e*np.sin(th)), f"BROKEN polar eps={eps}: reflection symmetry of the constraint broken")
print("\nREAD: when the forbidden (self) band sits on the symmetry axis, the single optimum is DELETED and")
print("      forced into a REFLECTION-SYMMETRIC PAIR straddling the axis (sum = 2*axis) -> a TACK between")
print("      two equal-VMG headings. Exact polar-symmetry <=> exact pairing (sum invariant). Breaking the")
print("      polar symmetry (eps) UNBALANCES the pair (sum drifts, one tack preferred).")

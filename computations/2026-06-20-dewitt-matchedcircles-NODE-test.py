#!/usr/bin/env python3
# MACHINE STEP6: RUNNABLE test of the NON-ANTIPODAL-CIRCLE-CENTERS constraint ON THE NODE (cosmic topology).
# Constraint: matched circles = S ∩ gS for deck isometry g(x)=R x + T; the center-pair angle is fixed by g's
# ROTATIONAL part: antipodal (180 deg) iff g is a pure translation; non-antipodal iff there is a screw/rotation twist.
import numpy as np

def rot(axis, phi):
    a = np.array(axis,float); a/=np.linalg.norm(a)
    K = np.array([[0,-a[2],a[1]],[a[2],0,-a[0]],[-a[1],a[0],0]])
    return np.eye(3) + np.sin(phi)*K + (1-np.cos(phi))*(K@K)

def center_pair_angle(R, T):
    T = np.array(T,float)
    c1 = T/np.linalg.norm(T)                 # S ∩ gS  center direction ~ T-hat
    c2 = -(np.linalg.inv(R)@T); c2/=np.linalg.norm(c2)   # S ∩ g^{-1}S center ~ -R^{-1}T-hat
    cosang = np.clip(np.dot(c1,c2),-1,1)
    return np.degrees(np.arccos(cosang))

print("=== NODE test: matched-circle center-pair angle vs deck-transformation twist ===")
T = [1.0,0.3,0.0]
print("  rotation angle phi | center-pair angle (180=antipodal) | deviation from antipodal")
for phi_deg in [0,15,30,45,90,120,180]:
    R = rot([0,0,1], np.radians(phi_deg))
    ang = center_pair_angle(R,T)
    print(f"   phi={phi_deg:3d} deg     |   {ang:7.3f} deg                  |  {abs(180-ang):.3f} deg")
print("  READ: phi=0 (pure translation) -> 180 deg ANTIPODAL; phi>0 (screw twist) -> NON-antipodal.")
print("  The center-pair geometry is fixed by g's rotational part = the identification's twist (constraint).")

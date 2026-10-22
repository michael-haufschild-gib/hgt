# HB: causal onset cancellation in the Einstein horizon current

Status: analytical local source identity; its algebra is checked in Lean scratch. Admission and evaluation of the complete causal horizon pairing remain unproved. This is not a formalized extinction theorem.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The target is the complete physical `2 Ω(B(p,p)/2, B(m,m)/2)`. The calculation below attacks the SV–SV coefficient of its horizon contribution. Other source sectors, the AdS contribution, and the global cusp completion remain part of that target.

## Cancellation mechanism

**Conjecture tested:** the causal pulse supplies the opposite of the explicit squared-onset-derivative term in the switched particular field's Einstein current.

**Result:** the original forced stream equation supplies precisely that source contact correction. The cancellation is a local identity and does not require choosing the pulse's horizon value. Identifying and integrating the actual causal field still requires its horizon admission. No vanishing of the remaining pulse pairing follows from this identity.

The input is the actual radial Einstein action current in [hb-mixed-radial-action-current.md](../../../3-formalized/hb-mixed-radial-action-current.md), together with the original-source decomposition in [hb-full-source-onset-reduction.md](../../../3-formalized/hb-full-source-onset-reduction.md). The angular operator throughout is

```
D = roughLaplacian + 1
```

on the actual horizon covectors. It is not replaced by an angular spectral number. The corpus identity `D4BMHorizon.coexact_roughLaplacian` gives `D(coexact u) = coexact(Delta u)`.

## Original stream equation and the source contact term

Put `f=r²-1`. In ingoing coordinates `(v,r)`, a stream covector `Psi` reconstructs

```
h_vA = Psi_vA + f Psi_rA,
h_rA = -Psi_rA.
```

Transforming the original static master gives

```
M Psi = r² f Psi_rr + 2r² Psi_vr + 2r Psi_r
        - 2r Psi_v - 2Psi + D Psi.
```

This sign and every radial factor were checked against `D4BMVectorStream.master`. That corpus definition separates radial and angular factors: its final `H*D` is the full angular term after separation, not the unmultiplied angular coefficient.

For a stream with a C² ingoing horizon extension, let `U=Psi|_(r=1)` and `N=Psi_r|_(r=1)`. Its actual horizon source is

```
S = (M Psi)|_(r=1) = 2(N'+N)-2(U'+U)+D U.
```

Increasing-r orientation of the Einstein density gives, with the dot denoting the sum of the two covector-component products,

```
omega_h(U,V) = -2 [U' dot (N_V'+N_V) - V' dot (N_U'+N_U)]
              = U' dot (D-2)V - V' dot (D-2)U
                - U' dot S_V + V' dot S_U.                 (1)
```

The products of two time derivatives cancel in the second equality. The outward horizon orientation is the negative of this convention. Equation (1) is pointwise; it discards neither an angular boundary term nor a source term.

There is also an exterior check before taking any horizon limit. In static coordinates, the same density is

```
(f/r²) [Psi_r dot ((D-2)Phi-M Phi)
        - Phi_r dot ((D-2)Psi-M Psi)].
```

Its separated form was checked against the original master and the curl expression of the proved Einstein radial current. This is a source-dependent reduction of that current, not an identification with a source-free scalar Wronskian.

## Literal particular field and its forced pulse

Write `w=2s`, `z=2t`, with the physical source branches `t=-s-3`, so `w+z=-6`. Let `chi` be the original fixed smooth transition. For the first branch define

```
F_s(r) = a²(1+1/r)^(2s) [A_s - k_s J/r²],
k_s = s(s-1)/4,
A_s = fullAngularCovector q branch,
J = fullSquareCovector q.
```

For the other branch use its actual angular inverse and amplitude `b`. Define the horizon coefficients

```
F_s = a² 2^(2s) X_s,          X_s = A_s-k_s J,
F1_s = a² 2^(2s) Y_s,        Y_s = -s X_s+2k_s J,
D_s = F1_s-F_s,
S_s = 2(w+1)D_s+D F_s.
```

Here `F1_s` denotes the first radial derivative of the displayed radial profile at `r=1`, not a time derivative. The particular horizon value and normal jet are

```
P_s(v) = chi(v) exp(wv) F_s,
Npart_s(v) = chi(v) exp(wv) F1_s.
```

Substitution into the original horizon master equation gives exactly

```
M_h(P_s,Npart_s) = chi exp(wv) S_s + E_s,
E_s(v) = 2 chi'(v) exp(wv) D_s.                              (2)
```

Thus the causal correction `Z_s=U_s-P_s` must have stream source `-E_s`; the full original horizon source is `mathcalS_s=chi exp(wv)S_s`. This sign also follows from the already proved scalar onset remainder and `L(Psi/r)=-f M(Psi)/r³`.

The normal-jet equation for the pulse retains its unknown horizon value:

```
(d/dv+1) Npulse_s = (d/dv+1-D/2) Z_s - chi' exp(wv)D_s.
```

Its integrating-factor formula is

```
Npulse_s(v) = Z_s(v) - (1/2) exp(-v) integral_0^v exp(u)D Z_s(u) du
             - D_s exp(-v) integral_0^v chi'(u)exp((w+1)u) du
             + exp(-v)[Npulse_s(0)-Z_s(0)].
```

The last term must be fixed by the actual retarded trace. It has not been discarded. This formula alone does not determine `Z_s`: that value belongs to the global causal problem with its AdS and cusp conditions.

## Exact removal of the explicit squared-onset term

Put `A=D-2` and

```
W_A(U,V) = U' dot A V - V' dot A U.
```

Equation (1), applied to the full original source and to the particular source (2), shows that the local particular contribution after accounting for the pulse source is

```
L(v) = omega_h(P_s,P_t) + P_s' dot E_t - P_t' dot E_s
     = W_A(P_s,P_t) - P_s' dot mathcalS_t + P_t' dot mathcalS_s.  (3)
```

For one angular component, set `c=chi(v)`, `d=chi'(v)`, suppress the common `exp(-6v)`, and abbreviate `(F_s,F1_s,F_t,F1_t)` by `(F,F1,G,G1)`. Then

```
L/exp(-6v)
 = -2 c d [(z+1)F G1-(w+1)G F1+(w-z)F G]
   -2 c² [w(z+1)F G1-z(w+1)G F1].                          (4)
```

There is no `d²` term in (4). It cancels between the actual particular Einstein current and the source contact term forced by the pulse. This does **not** say the unknown causal response has no dependence on the onset; it removes the explicit `D_chi` coefficient identified in the particular-only calculation.

The fixed transition satisfies

```
C_chi = integral_0^infinity exp(-6v)chi(v)² dv,
integral_0^infinity exp(-6v)chi(v)chi'(v) dv = 3 C_chi.
```

The latter equality follows by integration by parts; `chi(0)=0`, while boundedness and exponential damping kill the other endpoint. Thus (4), summed over the two components, gives the explicit local term

```
integral_0^infinity L(v) dv
 = -2 C_chi (w+3) [(z+1) F_s dot F1_t
                   +(w+1) F_t dot F1_s+6 F_s dot F_t]
 = -(a²b²/32) C_chi (2s+3)
     [(2t+1) X_s dot Y_t+(2s+1) X_t dot Y_s+6 X_s dot X_t].    (5)
```

These are pointwise angular identities. Angular integration or finite-part transport has not been silently performed. The complex factor `2s+3=2rho-1` on the first branch is not by itself the real horizontal displacement `2 Re(rho)-1` and is not an RH conclusion.

## Exact remaining pulse test

The full horizon density is `L+R`, where

```
R = W_A(Z_s,Z_t)
    + P_s' dot A Z_t + Z_s' dot A P_t
    - P_t' dot A Z_s - Z_t' dot A P_s
    - Z_s' dot mathcalS_t + Z_t' dot mathcalS_s.               (6)
```

This formula retains the unknown causal horizon values but eliminates their normal jets. It is the next source-level cancellation test.

For a finite angular region `Omega_Y`, use the covector pairing `inner_Y`, with the actual horizon metric and volume. Let

```
b_Y(U,V) = integral_(boundary Omega_Y)
             [metricInner(U,nabla_n V)-metricInner(nabla_n U,V)] ds.
```

The actual rough-Laplacian Green identity gives
`inner_Y(U,A V)-inner_Y(A U,V)=b_Y(U,V)`; the constant curvature term cancels. Integrating (6) on a finite time interval `[0,V]` and retaining its endpoints gives

```
integral R
 = integral W_A(Z_s,Z_t)
   + integral [inner_Y(Z_s,T_t')-inner_Y(Z_t,T_s')]
   + [inner_Y(Z_s,A P_t-mathcalS_t)
      -inner_Y(Z_t,A P_s-mathcalS_s)]_(0)^V
   + integral [b_Y(P_s',Z_t)-b_Y(P_t',Z_s)],                  (7)

T_s = mathcalS_s-2 A P_s
    = chi exp(wv) [2(w+1)F1_s+(2-2w)F_s-D F_s].
```

Here each integral in (7) also includes the displayed angular pairing where appropriate. The last line is an explicit test fixed by the literal source. No fitted polarization, spectral replacement, or adjustable clock occurs. Taking `V,Y` to their physical limits requires the original causal trace and cusp finite-part admission; all terms in (7) must be transported.

**Current conjecture:** evaluating (6), or equivalently the regulated expression (7), for the actual causal pulse supplies the remaining source-specific horizon cancellation when assembled with the physical AdS and other tensor terms. The [source-only circle-kernel construction](hb-causal-horizon-circle-kernel.md) supplies an analytical formula for that horizon value and accounts for the moving AdS image endpoint in the pulse comparison. Its scalar Riemann kernel is formalized; the full angular Green identification and pairing evaluation remain open. No proof or counterexample to the full extinction conjecture is established here. Evaluate this particular source-only pairing next, rather than re-prove radial normalization, impose its vanishing, or audit the explicit `chi'^2` term again.

## Verification scope

Six identities were checked with `lake env lean` in a temporary scratch file: the original-master coordinate transformation; the exterior source contact formula; the horizon source contact identity; exact cancellation in (4); the balanced coefficient in (5); and the switched horizon source in (2). Only these new identities received axiom checks. Their dependencies are `propext`, `Classical.choice`, and `Quot.sound`.

The actual horizon-limit admission, time/cusp integral transport, and pulse evaluation are not formalized by those algebra checks. No new Lean module or umbrella import is installed for isolated algebra. No mathematical computations or builds are used for this analytical result; the scratch file is removed after verification. The frontier map remains untouched by this work.

# HB: physical lift horizon current with the original onset

Stage: 1-in-progress. RH and complete physical-current cancellation remain unproved. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target is the complete physical pairing with independent SS/SV/VV amplitudes. The original finite source-delay horizon action is now formalized. This attack evaluates the actual Einstein current of the fixed source lift, including its source-contact correction, so its onset terms can be compared with that source action.

The complete four-divergence remains a necessary comparison law. Expanding the source-contact identity exposes a more concrete current to evaluate first. Put `s=physicalRate(q,branch)`, `t=-s-3`, `lambda=(s+1)(s+2)`, `delta=2s+3`, `k_s=s(s-1)/4`, and let `J` be the actual full-square coexact covector. The original lift in compact radius and ingoing time is

```
H_s=c_s(u,v) J,
c_s=-k_s a_s^2 u^2 (1+u)^(2s) chi(v) exp(2sv).
```

This is the original scalar `timeRadialLift` divided by `u`, not a replacement response. At the horizon `u=1`, `partial_r c_s=-(s+2)c_s` and `partial_r partial_v c_s=-(s+2)partial_v c_s`.

For general ingoing coefficients `c,d`, write `f=r^2-1` and

```
O(c)=r^2 f c_rr+2r^2 c_rv+2r c_r-2r c_v.
```

The original static stream master is `O(c)J+c A J`. Substitution into the already proved actual Einstein current gives the regular ingoing components

```
omega^r=[(f d_r+d_v)O(c)-(f c_r+c_v)O(d)] (J dot J)/r^2,
omega^v=[d_r O(c)-c_r O(d)] (J dot J)/r^2,
omega^X=omega^Y=0.
```

Here `omega^v=omega^tau+omega^r/f`. Both angular components cancel because the same original covector appears in both slots; no angular eigenvalue is inserted.

At the horizon, direct expansion predicts, with `K=delta(lambda-2)(lambda-6)a_s^2 a_t^2/512`,

```
omega_h^r=K exp(-6v)[-(chi')^2+5chi chi'+4(lambda-1)chi^2](J dot J),
omega_h^v=K exp(-6v)[-chi chi'+2(2-lambda)chi^2](J dot J).
```

The complete master current instead has radial coefficient `K exp(-6v)chi^2(J dot A J)`; the source-contact current is its difference from the physical Einstein current. It cannot be silently equated to the latter.

For a finite cutoff `V>=0`, put `J2(V)=integral_0^V exp(-6v)chi^2` and `J1(V)=integral_0^V exp(-6v)(chi')^2`. The actual product derivative gives

```
integral_0^V exp(-6v)chi chi'=3J2(V)+exp(-6V)chi(V)^2/2.
```

Therefore the predicted integrated physical radial coefficient is

```
K[-J1(V)+(4lambda+11)J2(V)+(5/2)exp(-6V)chi(V)^2].
```

Verify the original lift dictionary, actual coordinate derivatives, original action-current substitution, literal horizon limit, and finite clock integral in Lean. Then compare these retained terms with the original source action; do not assign any cross-current or angular principal flux to zero.

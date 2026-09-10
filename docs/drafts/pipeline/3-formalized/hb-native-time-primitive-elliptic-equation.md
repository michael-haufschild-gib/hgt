# HB: native time-primitive elliptic equation

Status: `FORMALISED`. Four new public theorems extend `ThetaCuspHawkingBMFullNativeWave`. Physical inverse identification, energy-domain admission, complete physical-current extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target remains `2 Omega(B(p,p)/2,B(m,m)/2)=0` with independent SS/SV/VV amplitudes and every original onset, horizon, AdS, temporal and cusp current. This extension constructs the actual elliptic equation needed for the native-to-physical inverse comparison.

## Exact theorem

Let `V(p,r;X,k)=fullNullResidual q s amplitude p r X k` be the literal full theta response minus its three transported principal cutoff powers. Define

```
v(t,x;X,k)=V(t+x,t-x;X,k),
W(t,x;X,k)=integral_0^t (t-u) v(u,x;X,k) du,
Delta_H=exp(2k) partial_X^2+partial_k^2-partial_k,
A=-partial_x^2-sech(x)^2 Delta_H.
```

The new `nativeResidualStaticForcing` is the original expression

```
F(u,x;X,k)
 = squareResidual(q,[X,exp(k)]) oddSource(s,amplitude,u,x)
   + sech(x)^2 sum_i principalNullResponse(q,s,amplitude,i,u+x,u-x)
                    cutoffCommutator(principalExponent(q,i),[X,exp(k)]).
```

All three original Weyl amplitudes are retained. There is no supplied wave-equation, source-identification, trace or regularity premise.

`nativeResidualTimePrimitive_elliptic_equation` proves, for every real `t,x,X,k`,

```
A W(t)=integral_0^t (t-u) F(u) du-v(t).
```

The other public results are:

- `nativeResidualTimePrimitive_radial_equation`: the exact second radial derivative of `W`, retaining the time integral of the actual angular derivatives of `V` and all cutoff commutators.
- `nativeResidualTimePrimitive_second_time`: `partial_t^2 W=v` for every real time and radius.
- `nativeResidualTimePrimitive_boundary`: `W(t,0;X,k)=0` for every real time.

The derivatives are Lean's actual derivatives of the displayed integrals. Private `HasDerivAt` proofs establish differentiability; the statements do not rely on default derivative values of nondifferentiable functions. The formulas include the characteristic edges `t+x=0` and `t-x=0`.

## Conjecture, proof, refinement

Starting only with the already proved mixed null equation, directly expanding `partial_x^2 V(t+x,t-x)` would require pure null derivatives not supplied by that equation. The successful conjecture was to derive the spatial equation of the double time primitive instead.

Write `P=partial_p V`, `R=partial_r V` and `G=partial_r P=partial_p R`. For a continuous function `P` with continuous derivative only in its second argument, change variables before differentiating:

```
J_P(t,x)=integral_0^t (t-u) P(u+x,u-x) du
        =integral_x^(t+x) (t+x-a) P(a,a-2x) da,
partial_x J_P
 =integral_0^t P(u+x,u-x) du
  -2 integral_0^t (t-u) G(u+x,u-x) du-t P(x,-x).
```

This requires no derivative of `P` in its first argument. Apply the same identity to `R` with its arguments exchanged and `x` negated. Continuous partial derivatives give the first chain rule for `V`. Endpoint FTC then proves

```
partial_x^2 W
 =V(t+x,t-x)-V(x,-x)-t(P(x,-x)+R(x,-x))
  -4 integral_0^t (t-u) G(u+x,u-x) du.
```

The initial terms are evaluated for the actual field. The original odd source vanishes outside the forward cone; continuity includes its edges. Every angular response jet vanishes there by its literal source integral, as do the actual principal radial responses. Thus `G` vanishes there too. The residual Goursat identity extends from nonnegative endpoints to all real null coordinates. FTC yields both continuous first null derivatives globally, and their initial traces vanish.

Finally, the already constructed smooth angular response jets and cutoff-height derivatives pass through the bounded time integral. Their exact combination proves `Delta_H W=integral_0^t (t-u) Delta_H v(u) du`. Substitution of the original residual forcing gives the displayed elliptic equation. The Dirichlet condition follows by integrating the original exact boundary value.

## Search and external method intake

Broad OR searches for energy/graph, elliptic/Caccioppoli/coercivity, and extrapolation/transposition/duality were combined with deep searches describing the actual time-primitive and form-admission mechanisms. Candidate lemmas, source arguments (method search), proof ideas and ingredient sets were inspected. `ClockParametricDerivative`, mathlib's continuous-partial derivative theorem, endpoint FTC, translation of interval integrals and causal rectangle interchange supplied the applicable calculus.

`unitWaveDuhamel_wave_graph` in `UnitWaveEllipticRange` illustrated time integration into an elliptic range, but its operator is the specific Fourier Klein–Gordon operator; it was not applied to the actual joint radial/modular operator. Deep form-admission suggestions recovered the Friedrichs form representation and modular Green identities. They did not establish the native function's admission to that form. Search inventory was complete (56,004 files at the last deep request); semantic coverage was partial and compiler status predominantly pending/source-only. Retrieval proposals were verified against source and Lean rather than accepted as proofs.

Broad arXiv intake prioritized recent papers and used self-selected single-word queries `duality`, `localization`, and `memory`. Concrete method checks:

- [Hirvonen–Jüngel–Pollino, 9 September 2026](https://arxiv.org/abs/2609.09921), Section 4: a backward adjoint converts a difference equation into a squared-norm identity. This suggests a second way to prove the native/physical uniqueness step. Their bounded nonlocal operator and solution spaces have not been identified with our unbounded joint operator; no theorem is imported from the paper.
- [Ramírez-Uribe et al., 5 September 2026](https://arxiv.org/abs/2609.09202), Section II: angular symmetrization cancels individual threshold contributions while a simultaneous double residue remains. The transferable candidate is to evaluate joint boundary/contact terms together before taking the full current limit. No HB cancellation follows from that paper alone.
- [Wang–Zhu, 9 September 2026](https://arxiv.org/abs/2609.10203), Section 2.2: discounted resolvents admit a corrector into an extended generator domain before a controlled limit removes the discount. An infinite-time transfer would require native tail control not established here. The finite-time primitive above avoids that extra requirement.
- [Czaja–Kania, 7 September 2026](https://arxiv.org/abs/2609.07642), Section 5: extrapolated spaces move an evolution equation to a weaker operator domain. Their sectorial semigroup framework is not an established realization of our wave operator; it remains an alternative method candidate.

These searches supplied proof mechanisms and testable next conjectures, not external axioms or numerical evidence. No mathematical computations were run.

## Remaining construction

The actual pointwise equation is now proved. It must be integrated against admissible tests on the original radial/modular product measure, with the already proved modular germ compatibility and exact Dirichlet trace. The next positive target is the cutoff estimate admitting `W` to the closed first-derivative energy graph. For the native/constructed response difference `u`, the resulting identity should be `A W=-u`, hence `B u+(I-B)W=0` for the actual unit resolvent `B=J J*`.

Local admissible testing, cusp/radial cutoff limits and graph closure remain unproved. The present theorem is not an energy-domain membership theorem, a proof of the complete physical inverse comparison, or an evaluation of the complete physical current.

## Validation

The completed scratch file passed `lake env lean` without warnings. Final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullNativeWave` passed without warnings in 105 seconds, two jobs. The isolated audit reused 4,091 existing project module caches and 11 installed dependency packages; no dependencies were rebuilt. Only the four new public theorems were checked with `#print axioms`, and each reports exactly `[propext, Classical.choice, Quot.sound]`. The source and five build artifacts were installed byte-identically to the successful audit. The existing area-umbrella import is unique. No umbrella build, Git command, launcher or mathematical computation was run. Frontier map and route-independent STATUS are unchanged.

Formal lint passed with repository large-file warnings, including this extended module (1,692 lines). Module-filtered lexical discovery finds all four new public theorems at lines 1450, 1474, 1496 and 1679. All owned Lean/Lake, search and lint processes completed. The owned scratch and isolated audit directories were removed.

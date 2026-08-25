Mission: use exact Hawking/topological-black-hole Teukolsky dynamics to derive an RH producer or forced tilted-sector mixing.

New corpus result in formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskySingleSectorFrequencyNoGo.lean:
- Reflected real-pair clock Ω_real(q,n) is exactly a Birmingham–Mokhtari plus-branch virtual QNM at overtone 2n and spectral point z_real(q)=i(2 Re ρ(q)-7/2).
- Its continued rho is 4-2a and angular eigenvalue Q_real=(2-a)(a-1), a=Re ρ(q).
- For every Xi divisor 0<a<1, hence -2<Q_real<0: virtual, not physical self-adjoint horizon shell.
- Functional-reflection clock is the earlier fixed virtual tower rho=3, Q_FE=-3/4.
- Exact Birmingham–Mokhtari first-mass scalar/vector parity split d4BackreactionSplit(Q)=12/(Q+2) evaluates to:
  B_real=12/[a(3-a)] >0,
  B_FE=48/5 >0.
- Two-channel backreaction defect:
  Δ_B=B_real-B_FE
     =12(2a-1)(2a-5)/[5a(3-a)].
  In open strip, Δ_B=0 iff a=1/2; other algebraic root a=5/2 is excluded.
- Helicity transfer is Δ_B/2, using scalar/vector-to-helicity basis coefficient. It vanishes iff critical line and is nonzero for every tilted divisor.
- Global confluence (transfer zero for every Xi copy) is formally equivalent to RH.

Hostile audit:
- Equality of individual exchange channels is NOT forced by generic crossing/associativity; GR contact and alternate exchange terms can accommodate channel dependence.
- Therefore global confluence equivalence is a consumer, not a proof.
- Strong positive survivor: full nonlinear Einstein–Teukolsky return has exact dichotomy: if source-derived channel confluence is proved, RH follows; otherwise every tilted divisor must carry explicit nonzero helicity transfer.
- Both absolute channel coefficients are positive, so generic passivity/negative-chamber exclusion cannot select RH. Selection must be phase-sensitive channel confluence or measured helicity mixing.

Verification:
- Target Lean file compiled.
- New declarations axiom-checked: only propext, Classical.choice, Quot.sound.
- formal_tools lint reports only pre-existing unreachable umbrella modules; no forbidden declarations from this work.
- Scratch files removed.
- No git used.

Related memory: mem:research/hawking_teukolsky_two_channel_thermal_associator_2026_08_24 may not exist; previous exact clock associator was created in same file: Ω_real-Ω_FE=i(a-1/2), equal to reflected-vs-conjugated external QNM frequency defect.
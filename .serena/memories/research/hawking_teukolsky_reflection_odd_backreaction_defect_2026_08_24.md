New source-specific refinement in formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskySingleSectorFrequencyNoGo.lean.

Let a=Re rho(q), 0<a<1. The real-pair virtual BM channel has exact first-mass scalar/vector parity split B(q)=12/[a(3-a)]>0. For functional-reflection partner Rq, Re rho(Rq)=1-a and B(Rq)=12/[(1-a)(2+a)]>0.

Define reflection-odd backreaction defect D(q)=B(q)-B(Rq). Exact result:
D(q)=24(1-2a)/[a(1-a)(3-a)(2+a)].
Consequences formally proved:
- D(Rq)=-D(q).
- D(q)=0 iff a=1/2.
- D(q)>0 for a<1/2.
- D(q)<0 for a>1/2.
Denominator is strictly positive in the open strip; no extra root.

Interpretation:
- Generic passivity sees only B(q),B(Rq)>0 and is blind.
- D is an actual Birmingham–Mokhtari first-mass parity-response observable with exact theta functional-reflection orientation.
- It is a better chiral return candidate than comparing B(q) to the fixed FE mediator value 48/5 because it is involutively odd and has no spurious algebraic root.
- Still not an RH proof: one must derive from full nonlinear Einstein–Teukolsky/APS dynamics why physical reflected return identifies the two parity responses (forcing D=0), or else D is an explicit unavoidable tilted-sector chiral transfer.

Verification:
- Target module compiled and targeted olean refreshed.
- All six new theorem/lemma declarations axiom-checked; only propext, Classical.choice, Quot.sound.
- Scratch files removed. Lint was already run earlier; only pre-existing unreachable umbrella errors.
- No git used.

Related: mem:research/hawking_teukolsky_two_virtual_channel_backreaction_confluence_2026_08_24.
# TG C9.11j — does moving to the simultaneous carrier erase the current?

- **Stage:** 3-formalized
- **Type:** PROVED exact source kernel, moving-carrier annihilation and surviving boundary
- **Route:** TG, cofinal relative source admission and retention of the cubic character.

## Hard question

C9.11i excludes every nonzero eventual fixed carrier, while every finite family
of stages admits a nonzero solution. The tempting repair is to use the exact
stage-dependent simultaneous carrier E_(S,b)={f∈K_b : A_Sf∈K_b}.
Does this retain the actual prime–Gamma relative current, or erase it?

## New conjecture and paper mechanism

For b≥1, the cleared current J_S has the exact kernel on K_b:

`J_S f=0 iff R_(P_S) f=0` for f∈K_b.

The existing source formula gives R₁ A_S* f=0 on K_b, hence
`J_S f=−A_S* R₁ A_S f`.
The adjoint is injective: A_S*=V_S A_S, with V_S unitary and A_S invertible.
Therefore J_S f=0 iff R₁ A_S f=0; the sharp Fourier-gap law gives the displayed
classification. No positive or index premise is assumed.

Every f∈E_(S,b) has R₁ A_S f=0, so **J_S annihilates the whole simultaneous
carrier**, not merely its scalar trace. Congruence and adjoint injectivity then
give `δ_S A_S f=0` on that carrier as well. Its canonical orthogonal projection
P_(S,b) should satisfy `J_S P_(S,b)=0` and `δ_S A_S P_(S,b)=0`.
The projection is nonzero at every finite stage by C9.11h's positive survivor.

Thus restricting to the exact simultaneous carrier would remove the actual
relative source before any cubic character is formed. A viable TG construction
must retain the complementary boundary quotient in its graded four-leg class.
The strongest positive survivor is the exact kernel classification and the
boundary map `R₁ A_S|K_b`, whose kernel is precisely that larger Fourier gap.

## Scope and next tests

- Formalize the exact kernel and annihilation on the canonical closed carrier.
- Retain nonzero finite-stage carriers; do not turn the obstruction into a
  vacuous zero-domain argument.
- Test whether the original Sonin compression remains nonzero for P_S>b, using
  actual strict aperture loss and Fourier parity. This is a structural current
  classification, not a numerical optimization.
- The moving-domain relative class, operator-valued continuation, degree-three
  Hardy-index comparison and sub-unit law remain open.

## Corpus audit

Deep searches for anisotropic carriers, Euler-gap range/periodization and joint
operator continuation were partial. They found no applicable replacement for
this actual current calculation. `DeningerEulerDepletedKernel` has an exact Green
inverse on a different exponentially decreasing source range; it must not be
silently substituted for the physical L² carrier. `SoninPrincipalRelativeOperator`
retains the finite principal/trace-class split, not a completed joint cofinal
source. Direct inputs are the audited C9.11g/h/i leaves and exact cutoff
covariance. The new proof above is derived from those operators.

## Verified outcome — 2026-10-02

`CCMEulerMovingCarrierRadical` proves the exact kernel and both annihilation
identities on the canonical simultaneous projection, and proves that projection
nonzero. The stronger exact activation law is also formalized:
`J_S Q_b=0 iff P_S≤b` for b≥1. Its reverse obstruction uses Fourier parity:
vanishing of the larger Fourier cutoff on K_b would force the larger physical
cutoff to vanish too, equate two strictly different Sonin projections, and
contradict the actual noncompact aperture transition.

Eight public theorems, two definitions and two canonical carrier instances pass
the foreground final leaf audit at default heartbeats. All twelve public axiom
queries return only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired.
Mandatory full lint currently reports twelve unrelated unwired modules and no
failure in either new C9.11i/j leaf. No numerical experiment, added axiom,
heartbeat increase, umbrella build or subagent was used.

The failed restriction proposal and its positive survivor are recorded in
`tg-simultaneous-carrier-current-repair`. Next C9.11k constructs the surviving
boundary quotient from the actual map B_(S,b)=R₁A_S|K_b, retaining A_S* as its
return map. Its annular realization and cofinal relative class remain unproved.
This moves the source-admission frontier but does not supply the Hardy cubic
comparison, sub-unit law, or an RH proof/falsification.

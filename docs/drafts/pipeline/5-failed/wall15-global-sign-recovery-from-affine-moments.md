# Global sign recovery from all affine sieve moments fails

- **ID:** wall15-global-sign-recovery-from-affine-moments
- **Stage:** 5-failed
- **Type:** FALSIFIED; strongest positive survivor formalized
- **Wall:** 15, support versus orientation; field research only.
- **Source:** [affine sieve phase-component certificate](../3-formalized/wall15-affine-sieve-correlation-phase-components.md).
- **Statement falsified:** Complete affine quadratic observations determine a finite real divisor sieve up to one global sign, even allowing translation of the response.

## Exact killing theorem and mechanism

At every cutoff `N+5`, take weights `c(1)=-2,c(3)=3,c(5)=5` and `e(1)=0,e(3)=3,e(5)=-5`, zero elsewhere. Their Selberg coordinates are supported at 3 and 5, with values `(1,1)` and `(1,-1)`. Because these modes are incomparable under divisibility, every comparable-coordinate product agrees.

Consequently, for every natural `a,b`, their literal complete-period affine averages
`P⁻¹ ∑(0≤k<P) s(k)s(a*k+b)` agree, where `P=(N+5)!`. Yet `s_c(0)=6` and `|s_e(k)|≤5` for every `k`. No translated global sign identifies these responses. No decoder from the entire affine data function can recover absolute origin response.

The exact actual-sieve Lean theorems are `AffineSieve.exists_same_affine_data_distinct_absolute_origin` and `AffineSieve.no_absolute_origin_decoder`, in namespace `GaloisForLFunctions.BiScaleUncertainty`. The first explicitly certifies equality at all affine parameters, the value 6, and the uniform absolute bound 5; the translated-sign obstruction follows directly from those certified bounds.

## Strongest positive survivor

For arbitrary real weights and every natural cutoff, equality of all affine data is equivalent to equality of `Y(q)Y(d)` for every `1≤d∣q≤N`. It is also equivalent to a sign mask relating the two coordinate profiles, constant along every divisibility edge whose endpoints are nonzero. Thus the exact ambiguity is one independent sign per component of the nonzero divisibility graph. Zeros agree automatically; no connectedness or nonvanishing premise is assumed.

The family `1≤a≤N`, `0≤b<N!` is already complete. The coefficientwise identity exposing this classification is
`DFT_b A(a,·)(r)=N! Y(q)Y(q/gcd(q,a))`, with `q=ord(r)`. The exported real-object certificates are `AffineSieve.dft_affineMoment`, `AffineSieve.affineMoment_eq_iff_comparable`, `AffineSieve.affineMoment_finite_complete` and `AffineSieve.affineMoment_eq_iff_signComponents`.

## New insight and status

Affine dilation connects only comparable divisor modes. The obstruction is therefore an exact arithmetic component structure, not merely loss of one overall sign. This classification determines what extra observations must resolve: relative signs between distinct components. Cubic odd-mode recovery and the even-mode parity obstruction were subsequently formalized in the [follow-up certificate](../3-formalized/wall15-cubic-odd-mode-recovery-and-parity-obstruction.md).

Dependency-closed paper proof and exact Lean survivor are complete in [the formalized parent](../3-formalized/wall15-affine-sieve-correlation-phase-components.md). All 37 package exports passed signature and axiom auditing, with only `propext`, `Classical.choice`, `Quot.sound`. The actual `sieveSeq` and `selbergMultiplesCoord` definition bodies were printed and inspected. Internal corpus search was bounded; no external novelty claim, stability theorem, optimal sample bound or Wall 15 closure is asserted. Repository-wide lint limitations from concurrent work are recorded on the parent card.

## Gates

- [x] Explicit exact counterexample on the existing arithmetic objects.
- [x] Serious positive-salvage audit: full equivalence classification and finite complete measurements.
- [x] Dependency-closed paper proof and exact survivor formalized in Lean.
- [ ] Publication audit.

## Log

- 2026-10-18: C1 retired only after the exact positive survivor and actual-object counterexample passed Lean and public-axiom audits. Wall 15 remains open.

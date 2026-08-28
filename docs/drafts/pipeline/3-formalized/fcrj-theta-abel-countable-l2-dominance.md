# FCRJ theta--Abel countable `L²` dominance

- **ID:** fcrj-theta-abel-countable-l2-dominance
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/critical-multiplicative-compensated-cancellation-rh.md
- **Statement:** A norm-summable countable Hilbert-valued exponential pencil with a finite isolated dominant layer cannot decay when one phase-fiber vector is nonzero; the literal theta--Abel aperture specialization places the sharp physical wall at `Re rho=1/2`.

## Goal

Close the finite-to-infinite gap left by finite-mode observability under the strongest natural
countable-tail hypothesis: absolute summability in physical aperture `L²`.

## Gates

- [x] 0 → 1  in-progress: Hilbert-valued dominant-packet conjecture and theta--Abel specialization identified
- [x] 1 → 2  fully-proven: dependency-closed paper proof and Lean proof
- [x] 2 → 3 formalized: direct check, targeted build, and axiom audit pass; global lint blocked by unrelated unwired modules
- [ ] 3 → 4  publication-ready: standalone exposition and external novelty review

## Statement

Let `c_i` be vectors in a complex Hilbert space with `sum_i ||c_i||<infinity`, and let `b_i` be
complex modes. Suppose a finite set `D` carries common maximal radius `r>0`, every mode outside `D`
has radius strictly below `r`, and one normalized phase fiber has nonzero aggregate vector. Then

```text
tsum_i (b_i/r)^n c_i  does not tend to 0.                         (1)
```

For physical theta--Abel aperture `[0,A]`, package each mode as the literal `L²` vector

```text
v_i(u)=a_i (exp(c z_i)-1)(z_i+1)/z_i exp(-z_i u).                 (2)
```

If `sum_i ||v_i||_L2<infinity`, a finite isolated rightmost layer has real part `beta`, and one
phase fiber is nonzero, then its packet normalized by `exp(beta n)` cannot tend to zero in `L²`.
When `beta>-1/2`, physical half-density scaling by `exp((beta+1/2)n)` also cannot tend to zero.

If normalized phases are injective on the dominant packet, `A,c>0`, `-1/2<beta<0`, and one source
coefficient is nonzero with `z_j!=-1`, the nonzero-fiber premise is automatic.

## Proof

For a nonzero dominant phase-fiber vector `V`, apply the bounded functional `x ↦ <V,x>`. Absolute
summability of vector norms gives a summable scalar pencil. The chosen fiber coefficient becomes
`<V,V>=||V||²!=0`, so the corpus scalar dominant-packet theorem forbids scalar decay. Continuity of
the functional transports any hypothetical vector decay to scalar decay, contradiction.

The theta--Abel specialization uses `||exp z||=exp(Re z)`. Thus real-part dominance is exactly mode-
radius dominance. A decaying inverse geometric factor shows that physical half-density decay would
force maximally normalized decay when `beta>-1/2`. Literal aperture profiles are nonzero in `L²`
on every positive interval; under phase injectivity a selected nonzero mode is its own fiber.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelCountableL2Dominance.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- Capstones:
  - `not_tendsto_tsum_normalizedExponentialPencil_vector_zero_of_dominantFinset`
  - `xiPhysicalThetaAbelModeApertureL2_ne_zero`
  - `not_tendsto_xiPhysicalThetaAbelCountableNormalizedL2Response_zero_of_dominantFinset`
  - `not_tendsto_xiPhysicalThetaAbelCountableL2PhysicalScale_zero_of_dominantFinset`
  - `not_tendsto_xiPhysicalThetaAbelCountableL2PhysicalScale_zero_of_phaseInjective`

## No-go closure

- **Exact killing mechanism:** Any finite isolated rightmost layer survives every absolutely
  summable strictly subdominant `L²` tail. Infinite cardinality alone does not enable cancellation.
- **Strongest positive survivor:** Hilbert-valued dominant-packet theorem `(1)` and literal physical
  theta--Abel `L²` wall `(2)`.
- **New insight:** Under dominant-phase injectivity, actual escape requires either failure of
  `ell¹(L²)` summability or absence of a finite isolated rightmost real-part layer. Without phase
  injectivity, a maximal phase-fiber cancellation remains a separate finite rigidity question.
- **Status:** Survivor paper- and Lean-proved. Actual zeta zero expansion is not asserted to satisfy
  norm summability or to possess a finitely attained isolated rightmost real part.

## Novelty audit

Vector-valued Dirichlet-series reductions by bounded functionals and nonharmonic exponential
observability are classical; this abstract mechanism is not claimed new. Primary-literature audit
through 2026-08-27 found no source combining the exact theta--Abel multiplier, literal compact-
aperture `L²` vectors, isolated rightmost zero layer, and sharp physical half-density wall.
Candidate-new claim is restricted to this route-specific synthesis and its exact two-way escape
classification under phase injectivity.

## Log

- 2026-08-27 — paper proof, Lean proof, direct check, targeted build, umbrella wiring, axiom audit, corpus audit, and targeted primary-literature audit complete

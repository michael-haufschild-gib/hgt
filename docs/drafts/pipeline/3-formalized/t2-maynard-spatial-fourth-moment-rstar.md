# Maynard spatial fourth moment with exact additive energy

- **ID:** T2-MAYNARD-L4-RSTAR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · T2 ordered-prime shell defect
- **Statement:** Selected-cell Mellin packets, their fixed-ambient physical defect packets, and the actual observed Heath--Brown dyadic aggregate satisfy a spatial fourth-moment and bad-base measure law controlled by exact integer-cell additive energy `maynardRStar`.

## Goal

Close the missing equation-(112) receiver in T2's Maynard--Peck branch.  The
corpus already had equation-(111) spatial `L²`, exact prime-free occupancy,
and abstract `R*` alternatives, but no theorem converting additive energy
into fourth spatial moment and then into measure of bad physical bases.

## Gates

- [x] 0 → 1  in-progress: corpus gap isolated; exact additive-convolution attack selected
- [x] 1 → 2  fully-proven: complete proof below, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: two Lean modules, direct checks and target builds green, standard-axiom audit
- [ ] 3 → 4  publication-ready: external novelty review and integration with full Maynard prime-gap assembly

## Frozen claim

For selected natural frequency cells `S ⊆ {0,...,N-1}` and coefficients
`|a_m| ≤ A`, let

`D(y) = sum_(m in S) a_m y^(c+im)`.

Let `R*(S)` be the number of ordered integer quadruples in the cast image of
`S` satisfying `m₁+m₂=m₃+m₄`.  Prove unconditionally:

1. `D(y)^2` is exactly the Mellin packet of the pair-sum convolution
   `q_k = sum_(m+n=k) a_m a_n`.
2. The pair-sum fibre energy is exactly corpus `maynardRStar` after casting
   natural cells into integer cells.
3. `integral_[x,2x] |D(y)|^4 dy` is bounded by an explicit spatial factor
   times `A^4 R*(S)`.
4. Unit-cell averaging preserves the same fourth-moment bound.
5. The bound transports exactly to the fixed-ambient physical defect packet.
6. Fourth-moment Markov gives bad-base volume at most the same numerator
   divided by `D^4`.
7. The result specializes to the actual observed Heath--Brown eligible
   dyadic aggregate.

No actual `R*` saving, prime-free interval exclusion, consecutive-prime
second moment, critical gap energy, or RH conclusion is asserted.

## Approach

Square the finite Mellin sum and group ordered coefficient pairs by their
sum.  Complex power additivity is valid because physical base is positive.
The squared convolution coefficient is bounded by amplitude to fourth power
times square of pair-sum fibre cardinality.  Summing these fibres counts
ordered additive quadruples exactly; a coordinatewise natural-to-integer
bijection identifies this count with existing corpus `maynardRStar`.

Apply the already formalized weighted spatial `L²` theorem to the squared
packet.  This turns coefficient `L²` energy of convolution into spatial
`L⁴` energy of original packet.  Two interval Cauchy--Schwarz applications
prove unit-cell `L⁴` contraction.  Continuous parametric integration swaps
physical-base and cell-coordinate integrals.  Exact Mellin scale covariance
then transports result to physical defect packet.  Finally, fourth-moment
Markov on restricted volume gives the equation-(112) bad-base law.

## Proof

**[PROVED HERE]** The exact Cauchy product is theorem
`maynardDiscreteMellinPacket_sq_eq`.  Its convolution energy estimate is
`sum_norm_sq_maynardAdditiveSquareCoeff_le_rstar`.  The finite fibre
partition and cast bijection prove
`maynardNatRStar_eq_maynardRStar_map`, so analytic estimate lands on existing
integer-cell additive-energy interface rather than an isolated surrogate.

The weighted equation-(111) theorem is applied to squared packet at exponent
`2c` and frequency range `2N`.  Since norm of square equals square of norm,
its spatial `L²` integral is original packet's spatial `L⁴` integral.  The
result is `integral_norm_four_maynardDiscreteMellinPacket_le_rstar`.

For continuous cell coefficients, Cauchy--Schwarz first bounds square of norm
of unit-cell average by cell `L²`; applying it again to squared norm bounds
fourth power by cell `L⁴`.  Fubini for continuous compact rectangles and
discrete theorem at each cell coordinate give
`integral_norm_four_maynardUnitCellMellinPacket_le_rstar`.

Exact fixed-ambient factorization gives
`integral_norm_four_maynardFixedAmbientPhysicalDefectPacket_le_rstar`.
The restricted-volume fourth-moment Markov theorem then yields
`volume_maynardFixedAmbientPhysicalDefectPacket_large_le_rstar`.  Critical-line
kernel bounds and source substitution finish
`volume_maynardDyadicBlockObservedPhysicalDefectPacket_large_le_rstar_of_selected_bound`.

## Hostile audit

- **Circularity:** none.  No zero location, RH, prime-gap moment, large-values
  estimate, or unproved analytic premise is used.
- **Exact `R*`:** proved equal to corpus integer quadruple count by a closed
  finite bijection; not replaced by `|S|^3`.
- **Actual packet:** final theorem uses corpus observed Heath--Brown aggregate
  and physical defect packet, not only an abstract polynomial.
- **Computations:** none.  Proof is symbolic finite combinatorics and analysis.
- **What remains:** arithmetic producer bounding selected-set `R*` in each
  large-values regime, followed by occupancy-to-gap-moment assembly.  This
  card closes analytic equation-(112) receiver only.
- **Literature audit (2026-08-28):** Maynard's 2012 paper states corresponding
  fourth-moment and bad-base estimate in Lemma 4.2/equation (112), following
  Peck's method.  Therefore underlying paper theorem is not claimed as new
  mathematics.  New corpus knowledge is dependency-closed Lean realization,
  exact identification with pre-existing `maynardRStar`, fixed-ambient
  transport, and observed Heath--Brown specialization.  This advances proof
  burden but does not by itself satisfy a claim of literature-level novelty.

## Lean audit

- Core: `formal/GaloisForLFunctions/RHTower/Sieve/MaynardSpatialMellinL4.lean`
- Observed receiver: `formal/GaloisForLFunctions/RHTower/Sieve/MaynardDyadicBlockSpatialL4.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct checks: both source files pass `lake env lean`.
- Target builds: both modules pass `lake build <module>`.
- Axioms: `[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-08-28 — corpus search isolated absent equation-(112) bridge after existing spatial `L²` infrastructure.
- 2026-08-28 — exact additive convolution and pair-fibre/quadruple-count equivalence proved.
- 2026-08-28 — discrete, continuous-cell, fixed-ambient, bad-base, and observed Heath--Brown theorems formalized and audited.

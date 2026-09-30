# Exact algebraic rank of the literal Fermi dyadic defect

- **ID:** pm-dyadic-defect-rank
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route PM; multiplicity-exact witness signature and correlation-jet cancellation
- **Statement:** The extended algebraic rank of `w ↦ (t ↦ w(t/2)-w(t))`, restricted to literal Fermi witnesses on `(0,1]`, equals total right-strip zeta multiplicity.
- **Novelty:** Scoped corpus/public searches found no exact matching statement; global absence from literature or training data cannot be certified.

## Goal

Replace a Hermitian sign count by the rank of a literal source difference operator. A finite
source certificate bounding this rank would bound every off-line zero multiplicity. Rank zero
would force RH. This theorem supplies the exact receiver; it does not produce a rank bound.

## Gates

- [x] 0 → 1: literal source operator and intrinsic extended rank well defined
- [x] 1 → 2: dependency-closed paper proof below, [PROVED HERE]
- [x] 2 → 3: actual-leaf Lean audit and axiom audit
- [ ] 3 → 4: standalone publication and completed novelty review

## Exact definitions

`D(w)(t)=w(t/2)-w(t)` for `t∈(0,1]`. Let `r(D)` be the supremum of all natural `n` for which
there are literal witnesses `w_1,...,w_n` with complex-linearly independent `D(w_i)`.
Let `M` be the supremum of finite sums of analytic multiplicities over actual zeta zeros with
`1/2<Re rho<1`. Both suprema take values in `ℕ∞`.

## Dependency-closed paper proof

1. `D` is complex-linear on finite witness sums. If the correlation-jet packet `J(w)` vanishes,
   existing local pole cancellation makes `w` dyadically self-similar; hence `D(w)=0`.
2. For a negative orthonormal family `v_i`, suppose `sum c_i D(v_i)=0`. Its witness sum `v`
   is self-similar, so `q(v,v)=0`. The exact negative Gram identity gives
   `q(v,v)=-sum |c_i|²`; every coefficient therefore vanishes. Thus its differences are
   independent and `ind_-(q)≤r(D)`.
3. Conversely suppose the differences of `w_i` are independent. If `sum c_i J(w_i)=0`,
   complex linearity gives `J(sum c_i w_i)=0`, so step 1 and independence imply `c_i=0`.
   The jet-coordinate map on this coefficient space is injective.
4. If the actual right-strip zero set is finite, its jet target has dimension `M`, giving
   `n≤M` for every independent difference family. If the zero set is infinite, every zero has
   positive finite multiplicity, so `M=∞` and this upper bound is automatic. Hence `r(D)≤M`.
5. The multiplicity-exact index theorem gives `M=ind_-(q)`. Combine both inequalities:
   `r(D)=M=ind_-(q)`.

No RH, zero simplicity, finite-zero premise, source positivity, or added axiom enters this
intrinsic equality. Auxiliary family lemmas have ordinary membership inputs; the capstone does not.

## Prior-art audit

Corpus hybrid searches `dyadic witness rank Jordan spectrum` and
`dyadic selfsimilar radical witness correlation`, broadened with `--any`, expose the witness
self-similarity and exact pairing frontier but no defect-rank theorem. Source inventory complete;
compiler coverage mostly pending/stale, so source hits were inspected directly. Exhaustive searches
of the Fermi leaves and PM cards likewise found no earlier rank statement.

Scoped public searches of Nyman–Beurling with dyadic/rank/dilation/Jordan/indefinite terms found
classical dilation and zero-jet work, including Burnol's *On Fourier and Zeta(s)* and Báez-Duarte's
general strong criterion. Those general notions are not claimed novel. The proposed distinction is
the exact rank of this particular alternating Fermi witness difference, counted with all analytic
multiplicities. A publication-level prior-art audit remains open.

## Log

- 2026-09-29 — paper proof closed; Lean formalization pending. Full RH goal remains active.

## Complete Lean certificate

`formal/GaloisForLFunctions/RHTower/FermiNymanDyadicDifferenceRank.lean` defines the difference
on the actual interval `(0,1]` and its extended algebraic rank. Its finite-sum identity and
`negative_family_difference_linearIndependent` prove the lower bound from the exact negative
Gram law. `independentDifferenceFamily_card_le_multiplicity` proves the reverse bound by a
literal correlation-jet injection. The infinite-zero case is discharged internally using
`rightStripMultiplicityCount_eq_top`. The capstone
`RHTower.witnessDyadicDifferenceRank_eq_rightStripMultiplicityCount` is an equality of intrinsic
extended-natural invariants with no hypothesis parameters. The underlying exact negative-index
equality is `RHTower.witnessNegIndex_eq_rightStripMultiplicityCount`.

The targeted two-leaf PM `lake --old build` passed. Final
`lake env lean GaloisForLFunctions/RHTower/FermiNymanDyadicDifferenceRank.lean` passed exit 0.
The shared audit of all 52 declarations in the five PM leaves found only `propext`,
`Classical.choice`, and `Quot.sound`. The leaf is imported by `RHTower.lean`. Formal lint reported
only ten unrelated concurrent unreachable leaves, with no finding on this certificate.

- 2026-09-29 — full multiplicity rank, both finite/infinite cases, direct compiler and axiom audits completed; moved to Stage 3.

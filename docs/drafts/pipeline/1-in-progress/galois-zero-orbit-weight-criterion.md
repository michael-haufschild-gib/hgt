# The orbit of a zero is its conjugate pair iff its weight lies in the prime trace field

- **ID:** galois-zero-orbit-weight
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-1311/obstacles-summary.md` §2.19 question 3 (B190); programme card `gtz-galois-theory-of-zeros-programme.md`
- **Statement:** for a zero `ρ` and one prime `p`: `σρ ∈ {ρ, ρ̄}` for every `σ ∈ Gal(E/B)` ⇔ `p^{2 Re ρ} ∈ B`.

## Goal

B190 asks for the orbit of a zero with irrational real part. Known: the orbit keeps the absolute
ordinate; a rational real part gives the orbit `{ρ, ρ̄}`. The criterion replaces "rational" by its
exact content and reduces B190 to membership of one real number in `B`.

## Notation

`E = ℚ(p^ρ)`, `B` the prime trace field, `G = Gal(E/B)`, `Δ` the integer span of the zeros,
`σ ↦ σ_Δ` the action on `Δ` (`p^{σ_Δ z} = σ(p^z)`), `c ∈ G` complex conjugation.
Weight of a zero: `q_ρ = ρ + ρ̄ = 2 Re ρ ∈ Δ`.

## Paper proof

**Lemma 1 (one prime fixes the real part of the weight).** If `p^{q_ρ} ∈ B` for one prime `p`,
then `Re(τ_Δ q_ρ) = 2 Re ρ` for every `τ ∈ G`.

*Proof.* `τ` fixes `p^{q_ρ}`, so `p^{τ_Δ q_ρ} = p^{q_ρ}`; take absolute values:
`p^{Re τ_Δ q_ρ} = p^{Re q_ρ}`. ∎

**Lemma 2 (doubling).** If `Re(τ_Δ q_ρ) = 2 Re ρ` for every `τ`, then `Re(σρ) = Re ρ` for every `σ`.

*Proof.* Fix `τ`, put `ζ = τ⁻¹ρ`; `Im ζ = ± Im ρ`, so `ζ̄ = ζ ∓ (2ρ − q_ρ)` in `Δ`. Apply `τ_Δ`:
`(τcτ⁻¹)ρ = ρ ∓ (2τρ − τ_Δ q_ρ)`, and with real parts
`Re (τcτ⁻¹)ρ − Re ρ = ∓ 2 (Re τρ − Re ρ)`. So the set `S = {|Re τρ − Re ρ| : τ ∈ G}` is closed
under doubling. It is bounded by `1` (critical strip), hence `S = {0}`. ∎

**Lemma 3 (converse).** If `Re(σρ) = Re ρ` for every `σ`, then `τ_Δ q_ρ = q_ρ` for every `τ`, and
`p^{q_ρ} ∈ B` for every prime `p`.

*Proof.* `τρ` and `τρ̄ = (τc)ρ` have real part `Re ρ` and ordinate `± Im ρ`; they are distinct
(`τ` is injective on the zeros and `Im ρ ≠ 0`), so their ordinates are opposite and
`τρ + τρ̄ = 2 Re ρ`. Then `τ` fixes `p^{q_ρ}`, and `E/B` is Galois. ∎

**Theorem.** For a zero `ρ` and a prime `p` the following are equivalent:
(1) `σρ ∈ {ρ, ρ̄}` for all `σ ∈ G`; (2) `Re σρ = Re ρ` for all `σ`; (3) `p^{2 Re ρ} ∈ B`.
In particular (3) does not depend on the prime.

*Proof.* (3) ⇒ (2): Lemmas 1, 2. (2) ⇒ (1): the orbit keeps the absolute ordinate.
(1) ⇒ (2) trivial. (2) ⇒ (3): Lemma 3. ∎

**Corollaries.**
1. The orbit of `ρ` contains a zero of another real part iff `p^{2 Re ρ} ∉ B`.
2. Rational real part: `p^{2 Re ρ} ∈ B` (the known case).
3. If some `σ` reflects an off-line zero (`σρ = 1 − ρ`), then `p^{2 Re ρ} ∉ B` for every `p`.

**Remark.** The orbit is contained in the complete fibre of the two ordinates `± Im ρ`. That it
is contained in the quartet `{ρ, ρ̄, 1−ρ, 1−ρ̄}` is known only when the fibre is one quartet.

## Gates
- [x] 0 → 1
- [x] 1 → 2  paper proof above
- [ ] 2 → 3  Lean: `GaloisTheoryOfZeros/TheOrbitOfAZeroIsItsConjugatePairIffItsWeightLiesInThePrimeTraceField.lean`

## Log
- 2026-11-14 — card created with the paper proof.

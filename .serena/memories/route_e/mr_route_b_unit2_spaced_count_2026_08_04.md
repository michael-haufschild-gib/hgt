# MR route-B unit 2 built: adapted-moment well-spaced count (2026-08-04)

Card: `docs/drafts/pipeline/1-in-progress/mr-splice-wide-range-mean-square.md`.

Built `RHTower/Sieve/PrimePowerLargeValuesCount.lean` (wired, build 8803 jobs, axioms only
propext/Classical.choice/Quot.sound, zero warnings, first-pass compile):

- `card_largeValues_pow_le (N ℓ) (hℓ : ℓ ≠ 0) (hN : 2 ≤ N)` for prime-supported a, δ-spaced grid
  lam with R+1 large values ≥ V on [δ/2, T−δ/2]:
  `(R+1)·V^{2ℓ} ≤ (T + 4N^ℓ(1+logN^ℓ))·(δ⁻¹ + 2logN^ℓ)·ℓ^ℓ·(∑‖b_p‖²)^ℓ`.
  One-step composition: `card_largeValues_le` at the power polynomial `convPow N ℓ a` with
  threshold V^ℓ (via `dirPoly_convPow` + `norm_pow` + `pow_le_pow_left₀`), then the unit-1
  prime-support mass bound; `Nat.le_self_pow` derives 2 ≤ N^ℓ.

This is [4, Lemma 8] (MR note appendix) in corpus form — the spaced exceptional-set count
|𝒯| ≪ exp((logX)^{1/48+o(1)}) follows by choosing N = e^{(j+1)/H}, ℓ ≈ logT·H/j (N^ℓ ≍ T).

Route-B remaining: (3) [4,L11] duality audit (AlmostOrthogonality/CharacterSeparation/
FrequencySeparation); (4) sharp-cutoff Halász sup from MoebiusUniformFrequency; (5) numeric
re-certification with corpus constants; (6) assembly to MRBilinear.

# Attainment and the degeneracy threshold of the pole-vanishing Weil form — Lean certificate

- **ID:** `WEIL-ENTRY-001-L3`
- **Stage:** 3-formalized
- **Parent card:** `1-in-progress/weil-positivity-soft-prime-entry.md`
- **Module:** `GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarGroundState` (imports the
  pole-vanishing ground energy module and `SuzukiSmallApertureGroundEnergy`; wired after
  `CCMRestrictedWeilPolarGroundEnergy`)
- **Axioms:** `[propext, Classical.choice, Quot.sound]`; lint clean; no hypotheses.

## Statements

- `exists_polarConstrained_groundState`: at every aperture the pole-vanishing ground energy `μ₀`
  is attained by a normalized pole-vanishing form-domain vector. Proof: normalized near-minimizers
  have bounded form norm; the compact form embedding gives a physical limit of norm one; the limit
  is pole-vanishing by continuity of the pole coefficients; it lies in every closed sublevel set
  `{Q ≤ μ₀ + 1/(k+1)}`, and injectivity of the embedding identifies the sublevel witnesses across
  levels, so the witness has `Q ≤ μ₀`; the Rayleigh floor gives equality.
- `exists_small_aperture_polarGroundEnergy_pos`: `μ₀ > 0` below an explicit-existence aperture
  (from the corpus's small-aperture positivity of the full form, Suzuki 2026 Thm 1.4 side).
- `continuous_ccmRestrictedWeilPolarGroundEnergy`.
- `exists_polar_degeneracy_threshold`: if `μ₀(b) ≤ 0` for some `b`, there is `a*` with
  `μ₀(a*) = 0`, `μ₀ > 0` strictly below `a*`, and `μ₀ ≤ 0` strictly above `a*`.  The threshold
  is the infimum of the closed set `{μ₀ ≤ 0}` pulled back to the real line by a continuous
  extension constant below half the small-aperture radius.
- `polar_positivity_or_null_vector`: **the degeneracy law** — either `μ₀ > 0` at every aperture,
  or some aperture `a*` carries a normalized pole-vanishing vector `v*` with `Q(v*) = 0` while
  `Q ≥ 0` on the whole pole-vanishing subspace at `a*`.

## Reading

This is the pole-vanishing form of the Yoshida–Suzuki degeneracy corollary: the only way Weil
positivity on the pole-vanishing subspace can fail is through an attained null vector at a
threshold aperture, never discontinuously and never through a prime entering (the prime terms are
part of the exact form and `μ₀` is continuous through their thresholds). On paper the two RH links
are: RH ⇒ `μ₀ > 0` everywhere (Weil's form is a sum of `|f̂(ρ)|²`, and an entire function of
exponential type cannot vanish at all zeros by the zero-density comparison, Yoshida's Theorem 2),
and `μ₀ > 0` everywhere ⇒ RH (Weil's criterion on the pole-vanishing subspace, using the
multiplier `s(s−1)` to place any test packet in the subspace). Neither link is formalized here.

## Lean notes

- `show P at h` is not syntax; use `change P at h`.
- The threshold argument avoids the subtype topology by extending `μ₀` to the real line through
  `t ↦ ⟨max t (δ/2), _⟩` (`Continuous.subtype_mk`), which is continuous and constant below `δ/2`.
- `exists_nat_one_div_lt` and `le_of_forall_pos_le_add` pass the sublevel bounds to the limit.

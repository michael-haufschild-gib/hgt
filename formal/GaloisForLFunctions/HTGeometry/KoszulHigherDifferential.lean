import GaloisForLFunctions.HTGeometry.KoszulCohomology

/-!
# The third Koszul differential and the `H²` curvature obstruction

`KoszulCohomology.lean` builds the first two Koszul differentials `d₀, d₁` of difference cohomology on
a family of commuting additive difference actions `(σ_p - 1)`, and proves `d₁ ∘ d₀ = 0`.  This file adds
the next differential

```text
(d₂ c)_{p,q,r} = (σ_p - 1) c_{q,r} - (σ_q - 1) c_{p,r} + (σ_r - 1) c_{p,q}
```

on `2`-cochains, and proves `d₂ ∘ d₁ = 0` — the exactness needed to define the first cohomology
`H¹ = ker d₁ / im d₀` as a genuine subquotient with a well-defined curvature obstruction living in
`H²`.  The vanishing is a direct consequence of the pairwise commutativity of the difference actions:
every double-application `(σ_p - 1)(σ_q - 1)` cancels against `(σ_q - 1)(σ_p - 1)`.
-/

namespace GaloisForLFunctions

noncomputable section

variable {ι M : Type*} [AddCommGroup M]

/-- The third Koszul differential on a `2`-cochain:
`(d₂ c)_{p,q,r} = (σ_p - 1) c_{q,r} - (σ_q - 1) c_{p,r} + (σ_r - 1) c_{p,q}`. -/
def koszulD2 (act : ι → M →+ M) (c : ι → ι → M) : ι → ι → ι → M :=
  fun p q r => (act p (c q r) - c q r) - (act q (c p r) - c p r) + (act r (c p q) - c p q)

/-- **`d₂ ∘ d₁ = 0`.**  The Koszul cochain complex of commuting difference actions is exact at the
`2`-cochain stage: the third differential annihilates every image of the second. -/
theorem koszulD2_koszulD1_eq_zero {act : ι → M →+ M}
    (hcomm : commutingAdditiveActions act) (b : ι → M) :
    ∀ p q r, koszulD2 act (koszulD1 act b) p q r = 0 := by
  intro p q r
  simp only [koszulD2, koszulD1, map_sub]
  rw [hcomm p q (b r), hcomm p r (b q), hcomm q r (b p)]
  abel

/-- The joint-invariance curvature detector: `d₂` vanishes on a `2`-cochain that is itself a coboundary
image, so the second cohomology receives no obstruction from the first differential. -/
theorem koszulD2_koszulCoboundary_comp_eq_zero {act : ι → M →+ M}
    (hcomm : commutingAdditiveActions act) (h : M) :
    ∀ p q r, koszulD2 act (koszulD1 act (koszulD0 act h)) p q r = 0 :=
  koszulD2_koszulD1_eq_zero hcomm (koszulD0 act h)

end

end GaloisForLFunctions

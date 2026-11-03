import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.TheArchimedeanTateFamily

/-!
# The completed Tate family is unimodular on the critical line

The structured candidate for the archimedean side of the domination question (DZG §7.3) is the
completed Tate family: the archimedean Tate family `𝒢_k(s) = Γ_ℝ(s − k)/Γ_ℝ(s)` times the arithmetic
one `ζ(s − k)/ζ(s)`, i.e. `Λ(s − k)/Λ(s)` with `Λ = Γ_ℝζ` (`completedTate_eq_archTate_mul`). In the
centred position `s = ½ + it + k/2` it is the centred family `Λ(½ + it − k/2)/Λ(½ + it + k/2)`.

* **Conjugation symmetry of `Λ`** (`completedRiemannZeta_conj`), from the half plane `Re s > 1`
  (RHTower) by the identity theorem for the entire function `Λ₀`.
* **Reflection symmetry of the modulus** (`norm_completedRiemannZeta_reflect`):
  `‖Λ(σ + it)‖ = ‖Λ(1 − σ + it)‖`.
* **The completed centred Tate family is unimodular on the critical line**
  (`norm_completedCentredTate_critical`): `‖Λ(½ + it − k/2)/Λ(½ + it + k/2)‖ = 1` for all real `k`, `t`.
* **Exact balance of the two places** (`norm_archTate_mul_norm_zetaRatio`):
  `‖𝒢_k(½ + it + k/2)‖ · ‖ζ(½ + it − k/2)/ζ(½ + it + k/2)‖ = 1`.

So in the completed centred normalization the archimedean Tate family is, on the critical line and
in every real dimension, exactly the inverse in modulus of the arithmetic one: the domination question
for the structured completed family is the functional equation, an identity, and carries no sign. The
sign of Weil's form lives where this balance is singular — at the zeros on the line, which are the
singular part of `Re Λ′/Λ` — and off the line, where under RH `|Λ(σ + it)|` grows with `|σ − ½|`.
-/

noncomputable section

open Complex ComplexConjugate

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

/-- **`Λ₀` commutes with conjugation everywhere.** -/
theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  set g : ℂ → ℂ := conj ∘ completedRiemannZeta₀ ∘ conj with hg
  have hgd : Differentiable ℂ g := fun z => by
    have := (differentiable_completedZeta₀ (conj z)).conj_conj
    rwa [Complex.conj_conj] at this
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : completedRiemannZeta₀ =ᶠ[nhds (2 : ℂ)] g := by
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    simp only [hg, Function.comp_apply]
    rw [_root_.RHTower.completedRiemannZeta₀_conj_of_one_lt hz, Complex.conj_conj]
  have hall := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun z _ => differentiable_completedZeta₀.analyticAt z) (fun z _ => hgd.analyticAt z)
    isPreconnected_univ (Set.mem_univ 2) heq
  have h := hall (Set.mem_univ (conj s))
  simp only [hg, Function.comp_apply, Complex.conj_conj] at h
  exact h

/-- **`Λ` commutes with conjugation.** -/
theorem completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq, completedRiemannZeta₀_conj]
  simp [map_sub]

/-- **Reflection symmetry of the modulus**: `‖Λ(σ + it)‖ = ‖Λ(1 − σ + it)‖`. -/
theorem norm_completedRiemannZeta_reflect (σ t : ℝ) :
    ‖completedRiemannZeta (σ + t * I)‖ = ‖completedRiemannZeta ((1 - σ : ℝ) + t * I)‖ := by
  have h : ((1 - σ : ℝ) : ℂ) + t * I = 1 - conj ((σ : ℂ) + t * I) := by
    simp only [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I]
    push_cast; ring
  rw [h, completedRiemannZeta_one_sub, completedRiemannZeta_conj, Complex.norm_conj]

/-- **The completed centred Tate family is unimodular on the critical line.** -/
theorem norm_completedCentredTate_critical (k t : ℝ)
    (hΛ : completedRiemannZeta ((1 / 2 + k / 2 : ℝ) + t * I) ≠ 0) :
    ‖completedRiemannZeta ((1 / 2 - k / 2 : ℝ) + t * I) /
      completedRiemannZeta ((1 / 2 + k / 2 : ℝ) + t * I)‖ = 1 := by
  rw [norm_div, norm_completedRiemannZeta_reflect (1 / 2 - k / 2) t,
    show (1 - (1 / 2 - k / 2) : ℝ) = 1 / 2 + k / 2 by ring, div_self (norm_ne_zero_iff.mpr hΛ)]

/-- **The completed Tate family is the archimedean times the arithmetic Tate family**:
`Λ(s − k)/Λ(s) = 𝒢_k(s)·ζ(s − k)/ζ(s)`. -/
theorem completedTate_eq_archTate_mul {s k : ℂ} (hs0 : s ≠ 0) (hsk0 : s - k ≠ 0)
    (hΓ : Gammaℝ s ≠ 0) (hΓ' : Gammaℝ (s - k) ≠ 0) (hζ : riemannZeta s ≠ 0) :
    completedRiemannZeta (s - k) / completedRiemannZeta s =
      archTate k s * (riemannZeta (s - k) / riemannZeta s) := by
  have e1 : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    rw [riemannZeta_def_of_ne_zero hs0, div_mul_cancel₀ _ hΓ]
  have e2 : completedRiemannZeta (s - k) = riemannZeta (s - k) * Gammaℝ (s - k) := by
    rw [riemannZeta_def_of_ne_zero hsk0, div_mul_cancel₀ _ hΓ']
  rw [e1, e2, archTate]
  field_simp

/-- **Exact balance of the archimedean and arithmetic places on the critical line**: in every real
dimension `k`, `‖𝒢_k(½ + it + k/2)‖ · ‖ζ(½ + it − k/2)/ζ(½ + it + k/2)‖ = 1`. -/
theorem norm_archTate_mul_norm_zetaRatio (k t : ℝ)
    (hs0 : ((1 / 2 + k / 2 : ℝ) : ℂ) + t * I ≠ 0) (hsk0 : ((1 / 2 - k / 2 : ℝ) : ℂ) + t * I ≠ 0)
    (hΓ : Gammaℝ (((1 / 2 + k / 2 : ℝ) : ℂ) + t * I) ≠ 0)
    (hΓ' : Gammaℝ (((1 / 2 - k / 2 : ℝ) : ℂ) + t * I) ≠ 0)
    (hζ : riemannZeta (((1 / 2 + k / 2 : ℝ) : ℂ) + t * I) ≠ 0) :
    ‖archTate k (((1 / 2 + k / 2 : ℝ) : ℂ) + t * I)‖ *
      ‖riemannZeta (((1 / 2 - k / 2 : ℝ) : ℂ) + t * I) /
        riemannZeta (((1 / 2 + k / 2 : ℝ) : ℂ) + t * I)‖ = 1 := by
  have hshift : ((1 / 2 + k / 2 : ℝ) : ℂ) + t * I - k = ((1 / 2 - k / 2 : ℝ) : ℂ) + t * I := by
    push_cast; ring
  have hΛ : completedRiemannZeta (((1 / 2 + k / 2 : ℝ) : ℂ) + t * I) ≠ 0 := by
    rw [riemannZeta_def_of_ne_zero hs0] at hζ
    intro h; rw [h, zero_div] at hζ; exact hζ rfl
  have h := completedTate_eq_archTate_mul (k := k) hs0 (hshift ▸ hsk0) hΓ (hshift ▸ hΓ') hζ
  rw [hshift] at h
  rw [← norm_mul, ← h, norm_completedCentredTate_critical k t hΛ]

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

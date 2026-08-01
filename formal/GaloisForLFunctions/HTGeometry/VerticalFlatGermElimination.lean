import GaloisForLFunctions.HTGeometry.DigammaFlatElimination

/-!
# The line form of the flat elimination

Flatness *on each vertical line* to the right of `σ₀` is weaker than flatness along the half-plane
filter, but it is still invariant under the half-plane germ relation, and it still has the four
closure properties the shift elimination consumes.  So the elimination applies to it as well, and the
conclusion is correspondingly stronger:

no nonzero differential polynomial in `ψ, ψ′, …` with `ℂ(s)` coefficients decays faster than every
power of the height on even one vertical line.

In particular the evaluation of jet polynomials at the digamma jets is injective — the germ form of
Hölder's theorem — and the line form is the one the Gamma layer needs, since `Γ` decays on each
vertical line but not uniformly on a half-plane.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- What holds along the half-plane filter holds along each of its lines. -/
theorem eventually_line_of_halfPlaneUpper {σ₀ : ℝ} {p : ℂ → Prop}
    (h : ∀ᶠ s : ℂ in halfPlaneUpper σ₀, p s) {σ : ℝ} (hσ : σ₀ ≤ σ) :
    ∀ᶠ t : ℝ in atTop, p ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  rw [halfPlaneUpper, Filter.eventually_inf_principal, Filter.eventually_comap] at h
  filter_upwards [h] with t ht
  refine ht ((σ : ℂ) + (t : ℂ) * Complex.I) (by simp) ?_
  simpa using hσ

/-- Line flatness only depends on the half-plane germ. -/
theorem IsVertFlat.congr_germ {σ₀ : ℝ} {A B : ℂ → ℂ}
    (h : A =ᶠ[halfPlaneUpper σ₀] B) (hA : IsVertFlat σ₀ A) : IsVertFlat σ₀ B := by
  intro N σ hσ
  refine (hA N σ hσ).congr' ?_
  filter_upwards [eventually_line_of_halfPlaneUpper h hσ] with t ht
  rw [ht]

/-- A germ is line flat when one — equivalently every — representative is. -/
def IsVertFlatGerm (σ₀ : ℝ) (g : HalfPlaneGerm σ₀) : Prop :=
  Quotient.liftOn g (IsVertFlat σ₀) fun _A _B h =>
    propext ⟨fun hA => hA.congr_germ h, fun hB => hB.congr_germ h.symm⟩

@[simp] theorem isVertFlatGerm_coe {σ₀ : ℝ} (A : ℂ → ℂ) :
    IsVertFlatGerm σ₀ (↑A : HalfPlaneGerm σ₀) ↔ IsVertFlat σ₀ A := Iff.rfl

theorem IsVertFlatGerm.sub {σ₀ : ℝ} {g h : HalfPlaneGerm σ₀} (hg : IsVertFlatGerm σ₀ g)
    (hh : IsVertFlatGerm σ₀ h) : IsVertFlatGerm σ₀ (g - h) := by
  induction g using Filter.Germ.inductionOn with
  | h A =>
    induction h using Filter.Germ.inductionOn with
    | h B => exact IsVertFlat.sub hg hh

/-- Line flatness survives multiplication by a rational germ. -/
theorem IsVertFlatGerm.mul_ratGerm {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) (k : RatFunc ℂ)
    {g : HalfPlaneGerm σ₀} (hg : IsVertFlatGerm σ₀ g) :
    IsVertFlatGerm σ₀ (ratGerm σ₀ k * g) := by
  induction g using Filter.Germ.inductionOn with
  | h A =>
    have hA : IsVertFlat σ₀ A := hg
    rw [ratGerm_eq_div]
    have hcoe : (((fun s : ℂ => k.num.eval s / k.denom.eval s : ℂ → ℂ) : HalfPlaneGerm σ₀))
        * (↑A : HalfPlaneGerm σ₀)
        = ((fun s : ℂ => k.num.eval s * A s / k.denom.eval s : ℂ → ℂ) : HalfPlaneGerm σ₀) := by
      rw [← Filter.Germ.coe_mul]
      exact Filter.Germ.coe_eq.mpr
        (Filter.Eventually.of_forall fun s => div_mul_eq_mul_div _ _ _)
    rw [hcoe]
    exact (hA.mul_poly hσ₀ k.num).div_poly hσ₀ k.denom_ne_zero

/-- Line flatness survives the translation. -/
theorem IsVertFlatGerm.shiftGerm {σ₀ : ℝ} {g : HalfPlaneGerm σ₀} (hg : IsVertFlatGerm σ₀ g) :
    IsVertFlatGerm σ₀ (shiftGerm σ₀ g) := by
  induction g using Filter.Germ.inductionOn with
  | h A =>
    have hA : IsVertFlat σ₀ A := hg
    rw [shiftGerm_coe]
    exact hA.shift

/-- **No nonzero rational germ is line flat.** -/
theorem not_isVertFlatGerm_ratGerm {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) {k : RatFunc ℂ} (hk : k ≠ 0) :
    ¬ IsVertFlatGerm σ₀ (ratGerm σ₀ k) := by
  intro hflat
  have hnum : k.num ≠ 0 := fun h => hk (RatFunc.num_eq_zero_iff.mp h)
  have hden : k.denom ≠ 0 := k.denom_ne_zero
  rw [ratGerm_eq_div] at hflat
  have hA : IsVertFlat σ₀ (fun s : ℂ => k.num.eval s / k.denom.eval s) := hflat
  have hmul := hA.mul_poly hσ₀ k.denom
  have hcongr : IsVertFlat σ₀ (fun s : ℂ => k.num.eval s) := by
    refine hmul.congr_germ ?_
    filter_upwards [eventually_eval_ne_zero_filter σ₀ hden] with s hs
    rw [mul_comm, div_mul_cancel₀ _ hs]
  exact not_isVertFlat_polynomial hnum hcongr

/-- **No nonzero differential polynomial in the digamma jets is flat on a line.**  The line-flat
values form a shift-stable annihilator space with no nonzero constants. -/
theorem not_isVertFlatGerm_digammaJetEval {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) {m : ℕ}
    {G : MvPolynomial (Fin m) (RatFunc ℂ)} (hG : G ≠ 0) :
    ¬ IsVertFlatGerm σ₀ (digammaJetEval σ₀ m G) := by
  intro hflat
  refine RationalIncrementHolder.no_shift_stable_annihilatorWith (fun j => polePart j)
    {H | IsVertFlatGerm σ₀ (digammaJetEval σ₀ m H)} ?_ ?_ ?_ ?_ ?_ ⟨G, hflat, hG⟩
  · intro H K hH hK
    show IsVertFlatGerm σ₀ (digammaJetEval σ₀ m (H - K))
    rw [map_sub]
    exact IsVertFlatGerm.sub hH hK
  · intro k H hH
    show IsVertFlatGerm σ₀ (digammaJetEval σ₀ m (MvPolynomial.C k * H))
    rw [map_mul, digammaJetEval_C]
    exact IsVertFlatGerm.mul_ratGerm hσ₀ k hH
  · intro H hH
    show IsVertFlatGerm σ₀ (digammaJetEval σ₀ m
      (RationalIncrementHolder.jetTranslateWith (fun j => polePart j) m H))
    rw [digammaJetEval_jetTranslate]
    exact IsVertFlatGerm.shiftGerm hH
  · intro k hk
    by_contra hk0
    exact not_isVertFlatGerm_ratGerm hσ₀ hk0 (by simpa using hk)
  · intro w δ h
    exact ratShift_sub_polePart_combination h

/-- **Hölder in germ form.**  Evaluation at the digamma jets is injective: the jets are
algebraically independent over `ℂ(s)` already as germs on a half-plane. -/
theorem digammaJetEval_injective {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) (m : ℕ) :
    Function.Injective (digammaJetEval σ₀ m) := by
  intro G H hGH
  by_contra hne
  have hsub : G - H ≠ 0 := sub_ne_zero.mpr hne
  refine not_isVertFlatGerm_digammaJetEval hσ₀ hsub ?_
  have hzero : digammaJetEval σ₀ m (G - H) = 0 := by
    rw [map_sub, hGH, sub_self]
  rw [hzero]
  show IsVertFlatGerm σ₀ ((0 : ℂ → ℂ) : HalfPlaneGerm σ₀)
  intro N σ hσ
  simp

end GaloisForLFunctions

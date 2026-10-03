import GaloisForLFunctions.RHTower.DualDiagonalMellin
import GaloisForLFunctions.RHTower.Sieve.InghamPoleRegularizedDetector
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# The exponentially smoothed zero detector: rectangle residues

For a zero `ρ` of `ζ` with `ρ ≠ 1`, a mollifier length `X` and a smoothing length `Y > 0`, the
detector integrand

`F(w) = Y^w Γ(w) (1 - M_X(ρ+w) ζ(ρ+w))`,   `M_X(s) = Σ_{n ≤ X} μ(n) n^{-s}`,

has exactly two poles in `Re w > -1`: at `w = 0` with residue `1` (the factor `1 - M_X(ρ)ζ(ρ)` is
`1`), and at `w = 1 - ρ` with residue `-Y^{1-ρ} Γ(1-ρ) M_X(1)` (the pole of `ζ`).  Writing
`Γ(w) = Γ(w+1)/w` and `ζ(s) = G(s)/(s-1)` with the entire residue unit `G(s) = (s-1)ζ(s)`,

`F(w) = 1/w - Y^{1-ρ}Γ(1-ρ)M_X(1)/(w - (1-ρ)) + R(w)`,

with `R` built from divided slopes of `Ψ(w) = Y^w Γ(w+1)` and `Φ(w) = Ψ(w) M_X(ρ+w) G(ρ+w)`, hence
analytic on `Re w > -1`; here `Φ(0) = M_X(ρ) G(ρ) = 0` is where the zero is used.  The rectangle
residue theorem then evaluates the boundary integral of `F` around any rectangle in `Re w > -1`
enclosing both poles.
-/

noncomputable section

namespace RHTower

open Complex Set

/-- The detector integrand `Y^w Γ(w) (1 - M_X(ρ+w) ζ(ρ+w))`. -/
def expDetIntegrand (X : ℕ) (ρ : ℂ) (Y : ℝ) (w : ℂ) : ℂ :=
  (Y : ℂ) ^ w * Complex.Gamma w *
    (1 - Sieve.inghamMollifier X (ρ + w) * riemannZeta (ρ + w))

/-- The smooth factor `Ψ(w) = Y^w Γ(w+1)`. -/
def expDetGammaPart (Y : ℝ) (w : ℂ) : ℂ :=
  (Y : ℂ) ^ w * Complex.Gamma (w + 1)

/-- The numerator `Φ(w) = Y^w Γ(w+1) M_X(ρ+w) G(ρ+w)`. -/
def expDetNumer (X : ℕ) (ρ : ℂ) (Y : ℝ) (w : ℂ) : ℂ :=
  expDetGammaPart Y w * (Sieve.inghamMollifier X (ρ + w) * zetaResidueUnit (ρ + w))

/-- The analytic remainder of the detector integrand. -/
def expDetRemainder (X : ℕ) (ρ : ℂ) (Y : ℝ) (w : ℂ) : ℂ :=
  dslope (expDetGammaPart Y) 0 w -
    (dslope (expDetNumer X ρ Y) (1 - ρ) w - dslope (expDetNumer X ρ Y) 0 w) / (1 - ρ)

/-- The residue of the detector integrand at the pole of `ζ`. -/
def expDetZetaResidue (X : ℕ) (ρ : ℂ) (Y : ℝ) : ℂ :=
  -((Y : ℂ) ^ (1 - ρ) * Complex.Gamma (1 - ρ) * Sieve.inghamMollifier X 1)

theorem expDetGammaPart_zero (Y : ℝ) : expDetGammaPart Y 0 = 1 := by
  simp [expDetGammaPart]

theorem expDetNumer_zero {X : ℕ} {ρ : ℂ} (hρ : riemannZeta ρ = 0) (Y : ℝ) :
    expDetNumer X ρ Y 0 = 0 := by
  have hG : zetaResidueUnit ρ = 0 := by
    by_cases h1 : ρ = 1
    · subst h1
      exact absurd hρ riemannZeta_one_ne_zero
    · simp [zetaResidueUnit, Function.update_of_ne h1, hρ]
  simp [expDetNumer, hG]

/-- `-Φ(1-ρ)/(1-ρ)` is the residue `-Y^{1-ρ} Γ(1-ρ) M_X(1)`. -/
theorem neg_expDetNumer_div_eq_residue (X : ℕ) {ρ : ℂ} (hρ1 : ρ ≠ 1) (Y : ℝ) :
    -(expDetNumer X ρ Y (1 - ρ) / (1 - ρ)) = expDetZetaResidue X ρ Y := by
  have hq : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hsum : ρ + (1 - ρ) = 1 := by ring
  have hΓ : Complex.Gamma (1 - ρ + 1) = (1 - ρ) * Complex.Gamma (1 - ρ) :=
    Complex.Gamma_add_one _ hq
  simp only [expDetNumer, expDetGammaPart, expDetZetaResidue, hsum, zetaResidueUnit_one, hΓ]
  field_simp

/-- **The partial-fraction decomposition** of the detector integrand away from its two poles. -/
theorem expDetIntegrand_decomp (X : ℕ) {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) (Y : ℝ)
    {w : ℂ} (hw0 : w ≠ 0) (hwq : w ≠ 1 - ρ) :
    expDetIntegrand X ρ Y w =
      1 * (w - 0)⁻¹ + (expDetZetaResidue X ρ Y * (w - (1 - ρ))⁻¹ + expDetRemainder X ρ Y w) := by
  have hq : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hwq' : w - (1 - ρ) ≠ 0 := sub_ne_zero.mpr hwq
  have hs1 : ρ + w ≠ 1 := by
    intro h
    apply hwq
    linear_combination h
  have hs1' : ρ + w - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hΓ : Complex.Gamma w = Complex.Gamma (w + 1) / w := by
    rw [Complex.Gamma_add_one w hw0]
    field_simp
  have hζ : riemannZeta (ρ + w) = zetaResidueUnit (ρ + w) / (ρ + w - 1) := by
    simp only [zetaResidueUnit, Function.update_of_ne hs1]
    field_simp
  have hΦ0 := expDetNumer_zero (X := X) hρ Y
  have hΨ0 := expDetGammaPart_zero Y
  have hres := neg_expDetNumer_div_eq_residue X hρ1 Y
  rw [← hres]
  unfold expDetRemainder
  rw [dslope_of_ne _ hw0, dslope_of_ne _ hwq, dslope_of_ne _ hw0, slope_def_field,
    slope_def_field, slope_def_field, hΦ0, hΨ0]
  unfold expDetIntegrand expDetNumer expDetGammaPart
  rw [hΓ, hζ]
  have hden : ρ + w - 1 = w - (1 - ρ) := by ring
  rw [hden]
  field_simp
  ring

theorem differentiableOn_expDetGammaPart {Y : ℝ} (hY : 0 < Y) :
    DifferentiableOn ℂ (expDetGammaPart Y) {w : ℂ | -1 < w.re} := by
  intro w hw
  have hY0 : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (Y : ℂ) ^ w) w :=
    (differentiableAt_id).const_cpow (Or.inl hY0)
  have hΓ : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w + 1)) w := by
    have hnot : ∀ m : ℕ, w + 1 ≠ -(m : ℂ) := by
      intro m hm
      have hre := congrArg Complex.re hm
      simp only [add_re, one_re, neg_re, natCast_re] at hre
      have : (-1 : ℝ) < w.re := hw
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact (Complex.differentiableAt_Gamma _ hnot).comp w
      ((differentiableAt_id).add_const 1)
  exact (hpow.mul hΓ).differentiableWithinAt

theorem differentiableOn_expDetNumer (X : ℕ) (ρ : ℂ) {Y : ℝ} (hY : 0 < Y) :
    DifferentiableOn ℂ (expDetNumer X ρ Y) {w : ℂ | -1 < w.re} := by
  intro w hw
  have hM : DifferentiableAt ℂ (fun w : ℂ => Sieve.inghamMollifier X (ρ + w)) w :=
    ((Sieve.analyticAt_inghamMollifier X (ρ + w)).differentiableAt).comp w
      ((differentiableAt_id).const_add ρ)
  have hG : DifferentiableAt ℂ (fun w : ℂ => zetaResidueUnit (ρ + w)) w :=
    ((analyticAt_zetaResidueUnit (ρ + w)).differentiableAt).comp w
      ((differentiableAt_id).const_add ρ)
  exact ((differentiableOn_expDetGammaPart hY w hw).mul (hM.mul hG).differentiableWithinAt)

theorem isOpen_re_gt_neg_one : IsOpen {w : ℂ | -1 < w.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- The remainder is analytic on `Re w > -1` when `Re ρ < 2`. -/
theorem analyticOnNhd_expDetRemainder (X : ℕ) {ρ : ℂ} (hρ2 : ρ.re < 2) {Y : ℝ} (hY : 0 < Y) :
    AnalyticOnNhd ℂ (expDetRemainder X ρ Y) {w : ℂ | -1 < w.re} := by
  have hU := isOpen_re_gt_neg_one
  have h0 : {w : ℂ | -1 < w.re} ∈ nhds (0 : ℂ) := hU.mem_nhds (by simp)
  have hq : {w : ℂ | -1 < w.re} ∈ nhds (1 - ρ) :=
    hU.mem_nhds (by simp only [mem_setOf_eq, sub_re, one_re]; linarith)
  have hΨ := (differentiableOn_dslope h0).mpr (differentiableOn_expDetGammaPart hY)
  have hΦq := (differentiableOn_dslope hq).mpr (differentiableOn_expDetNumer X ρ hY)
  have hΦ0 := (differentiableOn_dslope h0).mpr (differentiableOn_expDetNumer X ρ hY)
  refine DifferentiableOn.analyticOnNhd ?_ hU
  exact hΨ.sub ((hΦq.sub hΦ0).div_const _)

/-- **The rectangle residue identity.**  For a rectangle in `Re w > -1` that strictly encloses `0`
and `1 - ρ`, the boundary integral of the detector integrand is `2πi (1 - Y^{1-ρ}Γ(1-ρ)M_X(1))`. -/
theorem rectIntegral_expDetIntegrand (X : ℕ) {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1)
    (hρ2 : ρ.re < 2) {Y : ℝ} (hY : 0 < Y) {z₁ z₂ : ℂ} (hz₁ : -1 < z₁.re)
    (h01 : z₁.re < 0) (h02 : 0 < z₂.re) (h03 : z₁.im < 0) (h04 : 0 < z₂.im)
    (hq1 : z₁.re < (1 - ρ).re) (hq2 : (1 - ρ).re < z₂.re)
    (hq3 : z₁.im < (1 - ρ).im) (hq4 : (1 - ρ).im < z₂.im) :
    rectIntegral (expDetIntegrand X ρ Y) z₁ z₂ =
      2 * Real.pi * I * (1 + expDetZetaResidue X ρ Y) := by
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ {w : ℂ | -1 < w.re} := by
    intro w hw
    have hwre := (Complex.mem_reProdIm.mp hw).1
    rw [uIcc_of_le (by linarith)] at hwre
    simp only [mem_setOf_eq]
    linarith [hwre.1]
  have h := rectIntegral_eq_two_pole_residues_of_analyticOnNhd (F := expDetIntegrand X ρ Y)
    (R := expDetRemainder X ρ Y) (p := 0) (q := 1 - ρ) (rp := 1) (rq := expDetZetaResidue X ρ Y)
    hsub (by simpa using h01) (by simpa using h02) (by simpa using h03) (by simpa using h04)
    hq1 hq2 hq3 hq4 (analyticOnNhd_expDetRemainder X hρ2 hY)
    (fun w hw0 hwq => expDetIntegrand_decomp X hρ hρ1 Y hw0 hwq)
  exact h

end RHTower

import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailRelativeMargin

/-! General zero-side Cauchy–Schwarz, source-level relative stability margins,
sharp involution perturbation thresholds, and binary Schur inertia classifications.

For any two sources `f, g : ℝ → ℂ` with summable multiplicity-weighted zero squares,
reflection invariance of `zetaZeroConfig.carrier` and scaled quadratic domination
prove absolute summability of `zetaZeroConfig.Wsummand f g` and the unconditional
Cauchy–Schwarz inequality `‖zetaZeroConfig.W f g‖ ≤ √(Z(f) Z(g))`. Consequently, for
any decomposition `r = h - u` where `Re W(u, u) ≥ δ Z(u)` and `Z(h) ≤ ε Z(u)`,
the difference satisfies `Re W(r, r) ≥ (δ - ε - 2 √ε) Z(u)`.

We prove that the relative stability factor `δ - ε - 2 √ε` is strictly positive if and
only if `ε < (√(1 + δ) - 1)^2`, and we construct an explicit two-mode involution
extremizer achieving equality at `ε = (√(1 + δ) - 1)^2`, establishing universal
sharpness of the relative perturbation threshold. Finally, we prove the exact
iff classification and explicit negative-direction witness for two-dimensional
Schur complements. -/

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
open _root_.Zeta23
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The reflection permutation `ρ ↦ 1 - conj ρ` on the literal zeta zero carrier. -/
def zetaZeroReflectPerm : Equiv.Perm zetaZeroConfig.carrier :=
  Function.Involutive.toPerm
    (fun ρ => ⟨reflect ρ, zetaZeroConfig.reflect_mem _ ρ.2⟩)
    (fun ρ => Subtype.ext (Tail.reflect_reflect ρ))

theorem zetaZeroSquareSummand_reflectPerm (f : ℝ → ℂ) (ρ : zetaZeroConfig.carrier) :
    zetaZeroSquareSummand f (zetaZeroReflectPerm ρ) =
      (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖ ^ 2 := by
  change (zetaZeroConfig.mult (reflect ρ) : ℝ) * ‖paperFT f (gammaOf (reflect ρ))‖ ^ 2 = _
  rw [zetaZeroConfig.mult_reflect _ ρ.2, Tail.gammaOf_reflect]

theorem zetaZeroSquareMass_nonneg (f : ℝ → ℂ) :
    0 ≤ zetaZeroSquareMass f :=
  tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- Pointwise scaled quadratic upper bound on the mixed Weil summand for any `α > 0`. -/
theorem norm_Wsummand_le_scaled_square_summands (f g : ℝ → ℂ) {α : ℝ} (hα : 0 < α)
    (ρ : zetaZeroConfig.carrier) :
    ‖zetaZeroConfig.Wsummand f g ρ‖ ≤
      (α * zetaZeroSquareSummand f ρ +
        α⁻¹ * zetaZeroSquareSummand g (zetaZeroReflectPerm ρ)) / 2 := by
  rw [zetaZeroSquareSummand_reflectPerm]
  unfold zetaZeroSquareSummand ZeroConfig.Wsummand
  simp only [norm_mul, Complex.norm_natCast, RCLike.norm_conj]
  set m : ℝ := (zetaZeroConfig.mult ρ : ℝ)
  set A : ℝ := ‖paperFT f (gammaOf ρ)‖
  set B : ℝ := ‖paperFT g ((starRingEnd ℂ) (gammaOf ρ))‖
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hsq : 0 ≤ m * (Real.sqrt α * A - (Real.sqrt α)⁻¹ * B) ^ 2 :=
    mul_nonneg hm (sq_nonneg _)
  have hα_sq : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
  have hα_inv_sq : ((Real.sqrt α)⁻¹) ^ 2 = α⁻¹ := by rw [inv_pow, hα_sq]
  have hα_mul : Real.sqrt α * (Real.sqrt α)⁻¹ = 1 :=
    mul_inv_cancel₀ (Real.sqrt_pos.mpr hα).ne'
  have hexp : m * (Real.sqrt α * A - (Real.sqrt α)⁻¹ * B) ^ 2 =
      α * (m * A ^ 2) + α⁻¹ * (m * B ^ 2) - 2 * (m * A * B) := by
    calc
      m * (Real.sqrt α * A - (Real.sqrt α)⁻¹ * B) ^ 2 =
          m * (Real.sqrt α ^ 2 * A ^ 2 + ((Real.sqrt α)⁻¹) ^ 2 * B ^ 2 -
            2 * (Real.sqrt α * (Real.sqrt α)⁻¹) * A * B) := by ring
      _ = α * (m * A ^ 2) + α⁻¹ * (m * B ^ 2) - 2 * (m * A * B) := by
        rw [hα_sq, hα_inv_sq, hα_mul]
        ring
  linarith

/-- Absolute summability of the mixed Weil series for any two square-summable sources. -/
theorem summable_norm_Wsummand (f g : ℝ → ℂ)
    (hf : Summable (zetaZeroSquareSummand f))
    (hg : Summable (zetaZeroSquareSummand g)) :
    Summable (fun ρ : zetaZeroConfig.carrier => ‖zetaZeroConfig.Wsummand f g ρ‖) := by
  have hge : Summable (fun ρ => zetaZeroSquareSummand g (zetaZeroReflectPerm ρ)) :=
    hg.comp_injective zetaZeroReflectPerm.injective
  have hb : Summable (fun ρ =>
      (1 * zetaZeroSquareSummand f ρ +
        1⁻¹ * zetaZeroSquareSummand g (zetaZeroReflectPerm ρ)) / 2) :=
    ((hf.mul_left 1).add (hge.mul_left 1⁻¹)).div_const 2
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_Wsummand_le_scaled_square_summands f g one_pos) hb

theorem summable_Wsummand (f g : ℝ → ℂ)
    (hf : Summable (zetaZeroSquareSummand f))
    (hg : Summable (zetaZeroSquareSummand g)) :
    Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f g ρ) :=
  (summable_norm_Wsummand f g hf hg).of_norm

/-- Scaled arithmetic-geometric bound for the mixed Weil pairing with any `α > 0`. -/
theorem weil_mixed_norm_le_scaled (f g : ℝ → ℂ)
    (hf : Summable (zetaZeroSquareSummand f))
    (hg : Summable (zetaZeroSquareSummand g)) {α : ℝ} (hα : 0 < α) :
    ‖zetaZeroConfig.W f g‖ ≤
      (α * zetaZeroSquareMass f + α⁻¹ * zetaZeroSquareMass g) / 2 := by
  have hge : Summable (fun ρ => zetaZeroSquareSummand g (zetaZeroReflectPerm ρ)) :=
    hg.comp_injective zetaZeroReflectPerm.injective
  let b : zetaZeroConfig.carrier → ℝ := fun ρ =>
    (α * zetaZeroSquareSummand f ρ +
      α⁻¹ * zetaZeroSquareSummand g (zetaZeroReflectPerm ρ)) / 2
  have hb : Summable b := ((hf.mul_left α).add (hge.mul_left α⁻¹)).div_const 2
  have hs := summable_norm_Wsummand f g hf hg
  calc
    ‖zetaZeroConfig.W f g‖ ≤ ∑' ρ : zetaZeroConfig.carrier, ‖zetaZeroConfig.Wsummand f g ρ‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' ρ, b ρ := hs.tsum_le_tsum (norm_Wsummand_le_scaled_square_summands f g hα) hb
    _ = (α * zetaZeroSquareMass f + α⁻¹ * zetaZeroSquareMass g) / 2 := by
      dsimp only [b]
      rw [tsum_div_const, (hf.mul_left α).tsum_add (hge.mul_left α⁻¹),
        tsum_mul_left, tsum_mul_left, zetaZeroReflectPerm.tsum_eq (zetaZeroSquareSummand g)]
      rfl

/-- **Unconditional Zero-Side Cauchy–Schwarz Inequality.** For any two sources `f, g` with
summable zero-square masses, `‖W(f, g)‖ ≤ √(Z(f) Z(g))`. -/
theorem weil_mixed_norm_le_sqrt_square_mass (f g : ℝ → ℂ)
    (hf : Summable (zetaZeroSquareSummand f))
    (hg : Summable (zetaZeroSquareSummand g)) :
    ‖zetaZeroConfig.W f g‖ ≤
      Real.sqrt (zetaZeroSquareMass f * zetaZeroSquareMass g) := by
  have hZf : 0 ≤ zetaZeroSquareMass f := zetaZeroSquareMass_nonneg f
  have hZg : 0 ≤ zetaZeroSquareMass g := zetaZeroSquareMass_nonneg g
  rcases eq_or_lt_of_le hZf with hZf0 | hZf_pos
  · rw [← hZf0, zero_mul, Real.sqrt_zero]
    apply le_of_forall_pos_le_add
    intro ε hε
    rw [zero_add]
    by_cases hZg0 : zetaZeroSquareMass g = 0
    · have h := weil_mixed_norm_le_scaled f g hf hg one_pos
      rw [← hZf0, hZg0] at h
      linarith
    · have hZg_pos : 0 < zetaZeroSquareMass g := lt_of_le_of_ne hZg (Ne.symm hZg0)
      let α : ℝ := zetaZeroSquareMass g / (2 * ε)
      have hα : 0 < α := div_pos hZg_pos (by positivity)
      have h := weil_mixed_norm_le_scaled f g hf hg hα
      rw [← hZf0, mul_zero, zero_add] at h
      have hcalc : α⁻¹ * zetaZeroSquareMass g / 2 = ε := by
        dsimp [α]
        field_simp [hZg_pos.ne', hε.ne']
      linarith
  · rcases eq_or_lt_of_le hZg with hZg0 | hZg_pos
    · rw [← hZg0, mul_zero, Real.sqrt_zero]
      apply le_of_forall_pos_le_add
      intro ε hε
      rw [zero_add]
      let α : ℝ := 2 * ε / zetaZeroSquareMass f
      have hα : 0 < α := div_pos (by positivity) hZf_pos
      have h := weil_mixed_norm_le_scaled f g hf hg hα
      rw [← hZg0, mul_zero, add_zero] at h
      have hcalc : α * zetaZeroSquareMass f / 2 = ε := by
        dsimp [α]
        field_simp [hZf_pos.ne']
      linarith
    · let α : ℝ := Real.sqrt (zetaZeroSquareMass g / zetaZeroSquareMass f)
      have hα : 0 < α := Real.sqrt_pos.mpr (div_pos hZg_pos hZf_pos)
      have h := weil_mixed_norm_le_scaled f g hf hg hα
      apply h.trans_eq
      dsimp [α]
      rw [Real.sqrt_div hZg (zetaZeroSquareMass f), inv_div]
      have hsf : Real.sqrt (zetaZeroSquareMass f) ≠ 0 := (Real.sqrt_pos.mpr hZf_pos).ne'
      have hsg : Real.sqrt (zetaZeroSquareMass g) ≠ 0 := (Real.sqrt_pos.mpr hZg_pos).ne'
      rw [Real.sqrt_mul hZf]
      have h1 : Real.sqrt (zetaZeroSquareMass g) / Real.sqrt (zetaZeroSquareMass f) *
          zetaZeroSquareMass f =
          Real.sqrt (zetaZeroSquareMass f) * Real.sqrt (zetaZeroSquareMass g) := by
        have hsq := Real.sq_sqrt hZf
        field_simp [hsf]
        nlinarith
      have h2 : Real.sqrt (zetaZeroSquareMass f) / Real.sqrt (zetaZeroSquareMass g) *
          zetaZeroSquareMass g =
          Real.sqrt (zetaZeroSquareMass f) * Real.sqrt (zetaZeroSquareMass g) := by
        have hsq := Real.sq_sqrt hZg
        field_simp [hsg]
        nlinarith
      rw [h1, h2]
      ring

theorem abs_re_weil_mixed_le_sqrt_square_mass (f g : ℝ → ℂ)
    (hf : Summable (zetaZeroSquareSummand f))
    (hg : Summable (zetaZeroSquareSummand g)) :
    |(zetaZeroConfig.W f g).re| ≤
      Real.sqrt (zetaZeroSquareMass f * zetaZeroSquareMass g) :=
  (Complex.abs_re_le_norm _).trans (weil_mixed_norm_le_sqrt_square_mass f g hf hg)

/-- **Abstract Source-Subtraction Lower Bound.** If a decomposition `r = h - u` has
diag energies `W_h, W_u` and mixed real parts `M₁, M₂` satisfying `|W_h| ≤ Z_h` and
`|M_i| ≤ √(Z_h Z_u)`, then `W_r = W_h + W_u - M₁ - M₂ ≥ W_u - Z_h - 2 √(Z_h Z_u)`. -/
theorem source_subtraction_energy_lower {W_r W_h W_u M₁ M₂ Z_h Z_u : ℝ}
    (hident : W_r = W_h + W_u - M₁ - M₂)
    (hWh : |W_h| ≤ Z_h)
    (hM1 : |M₁| ≤ Real.sqrt (Z_h * Z_u))
    (hM2 : |M₂| ≤ Real.sqrt (Z_h * Z_u)) :
    W_u - Z_h - 2 * Real.sqrt (Z_h * Z_u) ≤ W_r := by
  have h1 := (abs_le.mp hWh).1
  have h2 := (abs_le.mp hM1).2
  have h3 := (abs_le.mp hM2).2
  linarith

/-- **Relative Margin Transfer Theorem.** If `W_u ≥ δ Z_u` and `Z_h ≤ ε Z_u` (`0 ≤ ε`, `0 ≤ Z_u`),
then `W_u - Z_h - 2 √(Z_h Z_u) ≥ (δ - ε - 2 √ε) Z_u`. -/
theorem relative_margin_transfer_lower_bound {W_u Z_h Z_u δ ε : ℝ}
    (hZu : 0 ≤ Z_u) (_hZh0 : 0 ≤ Z_h) (hε0 : 0 ≤ ε)
    (hWu : δ * Z_u ≤ W_u) (hZh : Z_h ≤ ε * Z_u) :
    (δ - ε - 2 * Real.sqrt ε) * Z_u ≤ W_u - Z_h - 2 * Real.sqrt (Z_h * Z_u) := by
  have hprod : Z_h * Z_u ≤ ε * Z_u ^ 2 := by
    calc
      Z_h * Z_u ≤ (ε * Z_u) * Z_u := mul_le_mul_of_nonneg_right hZh hZu
      _ = ε * Z_u ^ 2 := by ring
  have hsqrt : Real.sqrt (Z_h * Z_u) ≤ Real.sqrt ε * Z_u := by
    calc
      Real.sqrt (Z_h * Z_u) ≤ Real.sqrt (ε * Z_u ^ 2) := Real.sqrt_le_sqrt hprod
      _ = Real.sqrt ε * Real.sqrt (Z_u ^ 2) := Real.sqrt_mul hε0 _
      _ = Real.sqrt ε * Z_u := by rw [Real.sqrt_sq hZu]
  linarith

/-- The critical relative perturbation radius `ε*(δ) = (√(1 + δ) - 1)^2`. -/
def criticalRelativePerturbationRadius (δ : ℝ) : ℝ :=
  (Real.sqrt (1 + δ) - 1) ^ 2

theorem criticalRelativePerturbationRadius_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < criticalRelativePerturbationRadius δ := by
  unfold criticalRelativePerturbationRadius
  have h1 : 1 < Real.sqrt (1 + δ) := by
    conv_lhs => rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  exact sq_pos_of_pos (sub_pos.mpr h1)

/-- **Sharp Relative Stability Radius Classification (`iff`).** For `δ > 0` and `ε ≥ 0`,
the relative margin coefficient `δ - ε - 2 √ε` is strictly positive if and only if
`ε < (√(1 + δ) - 1)^2`. -/
theorem relative_stability_factor_pos_iff {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε) :
    0 < δ - ε - 2 * Real.sqrt ε ↔ ε < criticalRelativePerturbationRadius δ := by
  unfold criticalRelativePerturbationRadius
  have hs1 : 1 < Real.sqrt (1 + δ) := by
    conv_lhs => rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hsub_pos : 0 < Real.sqrt (1 + δ) - 1 := sub_pos.mpr hs1
  have hquad : δ - ε - 2 * Real.sqrt ε =
      (1 + δ) - (Real.sqrt ε + 1) ^ 2 := by
    have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε
    linarith
  rw [hquad]
  constructor
  · intro hpos
    have hlt_sq : (Real.sqrt ε + 1) ^ 2 < Real.sqrt (1 + δ) ^ 2 := by
      rw [Real.sq_sqrt (by linarith)]
      linarith
    have hlt : Real.sqrt ε + 1 < Real.sqrt (1 + δ) := by
      nlinarith [Real.sqrt_nonneg ε, Real.sqrt_nonneg (1 + δ)]
    have hlt' : Real.sqrt ε < Real.sqrt (1 + δ) - 1 := by linarith
    have hsq_lt : Real.sqrt ε ^ 2 < (Real.sqrt (1 + δ) - 1) ^ 2 :=
      sq_lt_sq.mpr (by
        rw [abs_of_nonneg (Real.sqrt_nonneg ε), abs_of_pos hsub_pos]
        exact hlt')
    rwa [Real.sq_sqrt hε] at hsq_lt
  · intro hlt_eps
    have hlt_sqrt : Real.sqrt ε < Real.sqrt (1 + δ) - 1 := by
      have h1 := Real.sqrt_lt_sqrt hε hlt_eps
      rwa [Real.sqrt_sq hsub_pos.le] at h1
    have hlt_add : Real.sqrt ε + 1 < Real.sqrt (1 + δ) := by linarith
    have hsq_lt : (Real.sqrt ε + 1) ^ 2 < Real.sqrt (1 + δ) ^ 2 :=
      sq_lt_sq.mpr (by
        rw [abs_of_pos (by positivity), abs_of_pos (by linarith)]
        exact hlt_add)
    rw [Real.sq_sqrt (by linarith)] at hsq_lt
    linarith

/-- Two-mode reflection pairing `W₂((x₁, x₂), (y₁, y₂)) = x₁ y₂ + x₂ y₁`, the canonical
finite-dimensional model of a reflection-coupled zero pair `(ρ, 1 - conj ρ)`. -/
def twoModeInvolutionPairing (x y : ℝ × ℝ) : ℝ :=
  x.1 * y.2 + x.2 * y.1

/-- Absolute square-sampling mass `Z₂(x₁, x₂) = x₁^2 + x₂^2` on the two-mode reflection pair. -/
def twoModeSquareMass (x : ℝ × ℝ) : ℝ :=
  x.1 ^ 2 + x.2 ^ 2

/-- **Two-Mode Involution Cauchy–Schwarz Saturation (`exists_two_mode_involution_extremizer`).**
For every `δ ∈ [0, 1]` and `ε ≥ 0`, there exist explicit two-mode vectors `u, h ∈ ℝ²`
with `Z₂(u) = 1`, `W₂(u, u) = δ`, and `Z₂(h) = ε` that saturate the mixed Cauchy–Schwarz
bound `W₂(h, u) = √ε` and yield `W₂(h - u, h - u) = (1 + ε) δ - 2 √ε`. -/
theorem exists_two_mode_involution_extremizer {δ ε : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) :
    ∃ u h : ℝ × ℝ,
      twoModeSquareMass u = 1 ∧
      twoModeInvolutionPairing u u = δ ∧
      twoModeSquareMass h = ε ∧
      twoModeInvolutionPairing h u = Real.sqrt ε ∧
      twoModeInvolutionPairing (h.1 - u.1, h.2 - u.2) (h.1 - u.1, h.2 - u.2) =
        (1 + ε) * δ - 2 * Real.sqrt ε := by
  let a : ℝ := (Real.sqrt (1 + δ) + Real.sqrt (1 - δ)) / 2
  let b : ℝ := (Real.sqrt (1 + δ) - Real.sqrt (1 - δ)) / 2
  let s : ℝ := Real.sqrt ε
  refine ⟨(a, b), (s * b, s * a), ?_, ?_, ?_, ?_, ?_⟩
  · unfold twoModeSquareMass
    dsimp [a, b]
    have h1 : Real.sqrt (1 + δ) ^ 2 = 1 + δ := Real.sq_sqrt (by linarith)
    have h2 : Real.sqrt (1 - δ) ^ 2 = 1 - δ := Real.sq_sqrt (by linarith)
    nlinarith
  · unfold twoModeInvolutionPairing
    dsimp [a, b]
    have h1 : Real.sqrt (1 + δ) ^ 2 = 1 + δ := Real.sq_sqrt (by linarith)
    have h2 : Real.sqrt (1 - δ) ^ 2 = 1 - δ := Real.sq_sqrt (by linarith)
    nlinarith
  · unfold twoModeSquareMass
    dsimp [a, b, s]
    have h1 : Real.sqrt (1 + δ) ^ 2 = 1 + δ := Real.sq_sqrt (by linarith)
    have h2 : Real.sqrt (1 - δ) ^ 2 = 1 - δ := Real.sq_sqrt (by linarith)
    have hs : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε
    calc
      (Real.sqrt ε * b) ^ 2 + (Real.sqrt ε * a) ^ 2 =
          Real.sqrt ε ^ 2 * (a ^ 2 + b ^ 2) := by ring
      _ = ε * 1 := by
        rw [hs]
        congr 1
        dsimp [a, b]
        nlinarith
      _ = ε := mul_one ε
  · unfold twoModeInvolutionPairing
    dsimp [a, b, s]
    have h1 : Real.sqrt (1 + δ) ^ 2 = 1 + δ := Real.sq_sqrt (by linarith)
    have h2 : Real.sqrt (1 - δ) ^ 2 = 1 - δ := Real.sq_sqrt (by linarith)
    calc
      Real.sqrt ε * b * b + Real.sqrt ε * a * a =
          Real.sqrt ε * (a ^ 2 + b ^ 2) := by ring
      _ = Real.sqrt ε * 1 := by
        congr 1
        dsimp [a, b]
        nlinarith
      _ = Real.sqrt ε := mul_one _
  · unfold twoModeInvolutionPairing
    dsimp [a, b, s]
    have h1 : Real.sqrt (1 + δ) ^ 2 = 1 + δ := Real.sq_sqrt (by linarith)
    have h2 : Real.sqrt (1 - δ) ^ 2 = 1 - δ := Real.sq_sqrt (by linarith)
    have hs : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε
    have hab2 : a ^ 2 + b ^ 2 = 1 := by dsimp [a, b]; nlinarith
    have hab : 2 * a * b = δ := by dsimp [a, b]; nlinarith
    calc
      (Real.sqrt ε * b - a) * (Real.sqrt ε * a - b) +
          (Real.sqrt ε * a - b) * (Real.sqrt ε * b - a) =
          (1 + Real.sqrt ε ^ 2) * (2 * a * b) - 2 * Real.sqrt ε * (a ^ 2 + b ^ 2) := by ring
      _ = (1 + ε) * δ - 2 * Real.sqrt ε := by rw [hs, hab, hab2]; ring

/-- **Two-Mode Negative Diagonal Extremizer.** For every `ε ≥ 0`, the antisymmetric vector
`h = (√(ε/2), -√(ε/2))` satisfies `Z₂(h) = ε` and `W₂(h, h) = -ε`, saturating the
lower diagonal bound `W₂(h, h) ≥ -Z₂(h)`. -/
theorem exists_two_mode_negative_diagonal_extremizer {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ h : ℝ × ℝ, twoModeSquareMass h = ε ∧ twoModeInvolutionPairing h h = -ε := by
  let c : ℝ := Real.sqrt (ε / 2)
  have hc : c ^ 2 = ε / 2 := Real.sq_sqrt (by positivity)
  refine ⟨(c, -c), ?_, ?_⟩
  · unfold twoModeSquareMass
    dsimp
    linarith [hc]
  · unfold twoModeInvolutionPairing
    dsimp
    linarith [hc]

/-- **Exact Binary Schur Complement Non-Negativity Classification (`iff`).**
For any binary quadratic form `Q(c, d) = A c^2 + M c d + D d^2` with `D > 0`,
`Q(c, d) ≥ 0` for all `c, d ∈ ℝ` if and only if `M^2 ≤ 4 A D`. -/
theorem schur_binary_quadratic_nonneg_iff {A M D : ℝ} (hD : 0 < D) :
    (∀ c d : ℝ, 0 ≤ A * c ^ 2 + M * c * d + D * d ^ 2) ↔ M ^ 2 ≤ 4 * A * D := by
  constructor
  · intro h
    have hspec := h (2 * D) (-M)
    have hid : A * (2 * D) ^ 2 + M * (2 * D) * (-M) + D * (-M) ^ 2 =
        D * (4 * A * D - M ^ 2) := by ring
    rw [hid] at hspec
    have hnonneg : 0 ≤ 4 * A * D - M ^ 2 := nonneg_of_mul_nonneg_right hspec hD
    linarith
  · intro hdisc c d
    have hid : 4 * D * (A * c ^ 2 + M * c * d + D * d ^ 2) =
        (2 * D * d + M * c) ^ 2 + (4 * A * D - M ^ 2) * c ^ 2 := by ring
    have hrhs : 0 ≤ (2 * D * d + M * c) ^ 2 + (4 * A * D - M ^ 2) * c ^ 2 :=
      add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg c))
    rw [← hid] at hrhs
    exact nonneg_of_mul_nonneg_right hrhs (by positivity)

/-- **Explicit Schur Negative-Direction Extremizer.** Whenever `D > 0` and `4 A D < M^2`,
evaluating at `(c, d) = (2 D, -M)` yields strict negativity `D (4 A D - M^2) < 0`. -/
theorem schur_binary_quadratic_neg_witness {A M D : ℝ} (hD : 0 < D) (hneg : 4 * A * D < M ^ 2) :
    A * (2 * D) ^ 2 + M * (2 * D) * (-M) + D * (-M) ^ 2 < 0 := by
  have hid : A * (2 * D) ^ 2 + M * (2 * D) * (-M) + D * (-M) ^ 2 =
      D * (4 * A * D - M ^ 2) := by ring
  rw [hid]
  exact mul_neg_of_pos_of_neg hD (by linarith)

end

end GaloisForLFunctions.ArithmeticPositivityTheory

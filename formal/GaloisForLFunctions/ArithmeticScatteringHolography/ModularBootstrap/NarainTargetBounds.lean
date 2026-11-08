import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainHeatRegularity

/-!
# Uniform Gaussian bounds on target horocycles

An explicit coercivity constant controls all masses while both horizontal
target coordinates lie in the unit interval. The scalar heat sum is bounded
by one rescaled square-target heat sum and is jointly measurable.
-/

open Complex RHTower RHTower.HeckeFactorization MeasureTheory Set
set_option autoImplicit false

noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- A mass coercivity bound uniform on two target horocycles. -/
def targetHorocycleCoercivity (Y Z : Ioi (0 : ℝ)) : ℝ :=
  Y.val * Z.val * ((2 * Z.val ^ 2 + 3) / Z.val ^ 2) * (2 + 3 / Y.val ^ 2)

theorem targetHorocycleCoercivity_pos (Y Z : Ioi (0 : ℝ)) :
    0 < targetHorocycleCoercivity Y Z := by
  unfold targetHorocycleCoercivity
  have hY : 0 < Y.val := Y.property
  have hZ : 0 < Z.val := Z.property
  positivity

theorem massCoercivityConstant_le_targetHorocycle (Y Z : Ioi (0 : ℝ))
    {x w : ℝ} (hx : x ∈ Icc 0 1) (hw : w ∈ Icc 0 1) :
    massCoercivityConstant ⟨x, Y.val, Y.property⟩ ⟨w, Z.val, Z.property⟩ ≤
      targetHorocycleCoercivity Y Z := by
  have hY : 0 < Y.val := Y.property
  have hZ : 0 < Z.val := Z.property
  have hx2 : x ^ 2 ≤ 1 := by nlinarith only [hx.1, hx.2, mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hw2 : w ^ 2 ≤ 1 := by nlinarith only [hw.1, hw.2, mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  have hσ : (2 * Z.val ^ 2 + 1 + 2 * w ^ 2) / Z.val ^ 2 ≤
      (2 * Z.val ^ 2 + 3) / Z.val ^ 2 :=
    div_le_div_of_nonneg_right
      (show 2 * Z.val ^ 2 + 1 + 2 * w ^ 2 ≤ 2 * Z.val ^ 2 + 3 by linarith only [hw2])
      (sq_nonneg Z.val)
  have hρ : 2 + (2 * x ^ 2 + 1) / Y.val ^ 2 ≤ 2 + 3 / Y.val ^ 2 :=
    add_le_add le_rfl (div_le_div_of_nonneg_right
      (show 2 * x ^ 2 + 1 ≤ (3 : ℝ) by linarith only [hx2]) (sq_nonneg Y.val))
  change Y.val * Z.val * _ * _ ≤ Y.val * Z.val * _ * _
  apply mul_le_mul
    (mul_le_mul_of_nonneg_left hσ (mul_pos Y.property Z.property).le) hρ
  · positivity
  · positivity

theorem narainMassSq_uniform_lower (Y Z : Ioi (0 : ℝ))
    {x w : ℝ} (hx : x ∈ Icc 0 1) (hw : w ∈ Icc 0 1)
    (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    narainMassSq zI zI q / targetHorocycleCoercivity Y Z ≤
      narainMassSq ⟨x, Y.val, Y.property⟩ ⟨w, Z.val, Z.property⟩ q := by
  have hm : 0 ≤ narainMassSq ⟨x, Y.val, Y.property⟩ ⟨w, Z.val, Z.property⟩ q :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg _)).trans
      (two_mul_abs_spin_le_massSq _ _ q)
  apply (div_le_iff₀ (targetHorocycleCoercivity_pos Y Z)).mpr
  rw [narainMassSq_square, ← chargeEuclideanSq]
  exact (chargeEuclideanSq_le_mass _ _ q).trans
    (by simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_right (massCoercivityConstant_le_targetHorocycle Y Z hx hw) hm))

theorem narainBoltzmann_uniform_upper (Y Z : Ioi (0 : ℝ))
    {x w : ℝ} (hx : x ∈ Icc 0 1) (hw : w ∈ Icc 0 1)
    {y : ℝ} (hy : 0 < y) (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    narainBoltzmann ⟨x, Y.val, Y.property⟩ ⟨w, Z.val, Z.property⟩ y q ≤
      narainBoltzmann zI zI (y / targetHorocycleCoercivity Y Z) q := by
  unfold narainBoltzmann
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left
    (narainMassSq_uniform_lower Y Z hx hw q) (mul_pos Real.pi_pos hy).le
  calc
    _ ≤ -(Real.pi * y * (narainMassSq zI zI q / targetHorocycleCoercivity Y Z)) :=
      neg_le_neg h
    _ = _ := by ring

/-- Positivity identifies the heat norm with its real Boltzmann series. -/
theorem norm_narainScalarHeat_eq_tsum (ρ σ : D4BMUpperHalfPlaneCoordinate) (y : ℝ) :
    ‖narainScalarHeat ρ σ y‖ = ∑' q : NonzeroScalarCharge, narainBoltzmann ρ σ y q.val := by
  unfold narainScalarHeat
  rw [← Complex.ofReal_tsum, Complex.norm_real,
    Real.norm_of_nonneg (tsum_nonneg (fun q : NonzeroScalarCharge =>
      (show 0 ≤ narainBoltzmann ρ σ y q.val from (Real.exp_pos _).le)))]

/-- Positivity makes the scalar heat norm decrease on positive heights. -/
theorem antitoneOn_norm_narainScalarHeat (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    AntitoneOn (fun y => ‖narainScalarHeat ρ σ y‖) (Ioi 0) := by
  intro a ha b hb hab
  change ‖narainScalarHeat ρ σ b‖ ≤ ‖narainScalarHeat ρ σ a‖
  rw [norm_narainScalarHeat_eq_tsum, norm_narainScalarHeat_eq_tsum]
  exact ((summable_narainBoltzmann ρ σ hb).comp_injective Subtype.val_injective).tsum_le_tsum
    (fun q => narainBoltzmann_antitone ρ σ q hab)
    ((summable_narainBoltzmann ρ σ ha).comp_injective Subtype.val_injective)

/-- One rescaled square-target heat sum dominates the complete target rectangle. -/
theorem norm_narainScalarHeat_uniform_upper (Y Z : Ioi (0 : ℝ))
    {x w : ℝ} (hx : x ∈ Icc 0 1) (hw : w ∈ Icc 0 1)
    {y : ℝ} (hy : 0 < y) :
    ‖narainScalarHeat ⟨x, Y.val, Y.property⟩ ⟨w, Z.val, Z.property⟩ y‖ ≤
      ‖narainScalarHeat zI zI (y / targetHorocycleCoercivity Y Z)‖ := by
  rw [norm_narainScalarHeat_eq_tsum, norm_narainScalarHeat_eq_tsum]
  exact ((summable_narainBoltzmann _ _ hy).comp_injective Subtype.val_injective).tsum_le_tsum
    (fun q => narainBoltzmann_uniform_upper Y Z hx hw hy q.val)
    ((summable_narainBoltzmann _ _ (div_pos hy (targetHorocycleCoercivity_pos Y Z))).comp_injective
      Subtype.val_injective)

/-- The literal scalar series is jointly measurable in both target positions and height. -/
theorem measurable_narainScalarHeat_horocycles (Y Z : Ioi (0 : ℝ)) :
    Measurable (fun p : ℝ × (ℝ × ℝ) =>
      narainScalarHeat ⟨p.2.1, Y.val, Y.property⟩ ⟨p.2.2, Z.val, Z.property⟩ p.1) := by
  apply Measurable.tsum
  intro q
  unfold narainBoltzmann narainMassSq targetQuadratic
  fun_prop

#print axioms narainBoltzmann_uniform_upper
#print axioms norm_narainScalarHeat_uniform_upper
#print axioms measurable_narainScalarHeat_horocycles
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

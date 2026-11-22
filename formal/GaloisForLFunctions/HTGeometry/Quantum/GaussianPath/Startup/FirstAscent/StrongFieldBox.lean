import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.BoxMass

/-! # Gaussian boxes at increasing longitudinal field strength -/
open MeasureTheory ProbabilityTheory Set Real
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section

/-- A pair of coefficient rows with a unit tolerance at the odd longitudinal field. -/
def strongFieldBox (q : ℝ) : Set (PathPauliBlockLabel → ℝ) :=
  univ.pi fun i => Icc (isolatedFieldBlockCenter q i-1) (isolatedFieldBlockCenter q i+1)

theorem measurableSet_strongFieldBox (q : ℝ) : MeasurableSet (strongFieldBox q) :=
  MeasurableSet.pi (Set.to_countable _) fun _ _ => measurableSet_Icc

private def baseDensity : ℝ := (√(2*π))⁻¹ * exp (-1)

private theorem baseDensity_pos : 0<baseDensity := by unfold baseDensity; positivity

private theorem interval_mass (q c : ℝ) (hq : 0≤q) (hc : |c|≤q) :
    ENNReal.ofReal (2*baseDensity*exp (-q^2)) ≤ gaussianReal 0 1 (Icc (c-1) (c+1)) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,withDensity_apply _ measurableSet_Icc]
  have hf (x : ℝ) (hx : x ∈ Icc (c-1) (c+1)) :
      ENNReal.ofReal (baseDensity*exp (-q^2)) ≤ gaussianPDF 0 1 x := by
    apply ENNReal.ofReal_le_ofReal
    rw [show gaussianPDFReal 0 1 x = (√(2*π))⁻¹ * exp (-x^2/2) by
      unfold gaussianPDFReal; norm_num,baseDensity,mul_assoc,←exp_add]
    apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by positivity)
    have hxc : |x| ≤ q+1 := abs_le.mpr
      ⟨by linarith only [(abs_le.mp hc).1,hx.1],by linarith only [(abs_le.mp hc).2,hx.2]⟩
    have hsq := (sq_le_sq₀ (abs_nonneg x) (by linarith only [hq] : 0≤q+1)).mpr hxc
    rw [sq_abs] at hsq
    nlinarith only [hsq,sq_nonneg (q-1)]
  refine (setLIntegral_mono' measurableSet_Icc hf).trans_eq' ?_
  rw [setLIntegral_const,Real.volume_Icc,←ENNReal.ofReal_mul (mul_nonneg baseDensity_pos.le (exp_pos _).le)]
  congr 1
  ring

/-- At strength q the twenty-four coordinates have joint mass at least
a fixed positive constant times exp(−24q²). -/
theorem strong_field_box_mass :
    ∃ d : ℝ, 0<d ∧ ∀ q : ℝ, 0≤q →
      d*exp (-(24*q^2)) ≤ (Measure.infinitePi fun _ : PathPauliBlockLabel => gaussianReal 0 1).real
        (strongFieldBox q) := by
  refine ⟨(2*baseDensity)^24,pow_pos (mul_pos (by norm_num) baseDensity_pos) _,?_⟩
  intro q hq
  let c := isolatedFieldBlockCenter q
  have hc (i) : |c i| ≤ q := by
    dsimp only [c,isolatedFieldBlockCenter]
    split <;> simp [abs_of_nonneg hq,hq]
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp
  rw [Measure.infinitePi_eq_pi,strongFieldBox,Measure.pi_pi]
  refine le_trans ?_ (Finset.prod_le_prod' (s := Finset.univ) fun i _ => interval_mass q (c i) hq (hc i))
  rw [Finset.prod_const,Finset.card_univ,←ENNReal.ofReal_pow (mul_nonneg (mul_nonneg (by norm_num) baseDensity_pos.le) (exp_pos _).le)]
  have hcard : Fintype.card PathPauliBlockLabel=24 := by
    simp [PathPauliBlockLabel,PathPauliDirections,Fintype.card_prod,Fintype.card_sum]
  rw [hcard,mul_pow (2*baseDensity) (exp (-q^2)),←Real.exp_nat_mul,
    show ((24:ℕ):ℝ)*(-q^2)=-(24*q^2) by push_cast; ring]

end
end GaloisForLFunctions.HTGeometry.FirstAscent

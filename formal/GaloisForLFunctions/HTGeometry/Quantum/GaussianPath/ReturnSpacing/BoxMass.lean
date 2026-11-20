import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.BlockSites
import GaloisForLFunctions.HTGeometry.GaussianSmallBallLowerBound

/-! # Gaussian mass of a shrinking isolated-field box -/
open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Coefficient rows whose odd site carries a field of strength 1/(8k),
up to a relative error of 1/200 in each coordinate. -/
def isolatedFieldBox (k : ℝ) : Set (PathPauliBlockLabel → ℝ) :=
  let q := 1/(8*k)
  univ.pi fun i => Icc (isolatedFieldBlockCenter q i-q/200) (isolatedFieldBlockCenter q i+q/200)

theorem measurableSet_isolatedFieldBox (k : ℝ) : MeasurableSet (isolatedFieldBox k) :=
  MeasurableSet.pi (Set.to_countable _) fun _ _ => measurableSet_Icc

private theorem gaussian_interval_mass {l u : ℝ} (hl : -1 ≤ l) (hu : u ≤ 1) :
    ENNReal.ofReal (gaussianDensityFloor*(u-l)) ≤ gaussianReal 0 1 (Icc l u) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,withDensity_apply _ measurableSet_Icc]
  have h : ∀ x ∈ Icc l u, ENNReal.ofReal gaussianDensityFloor ≤ gaussianPDF 0 1 x := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_ge_floor (abs_le.mpr ⟨hl.trans hx.1,hx.2.trans hu⟩))
  exact (setLIntegral_mono' measurableSet_Icc h).trans_eq' (by
    rw [setLIntegral_const,Real.volume_Icc,ENNReal.ofReal_mul gaussianDensityFloor_pos.le])

/-- Twenty-four independent coordinates give a box probability at least d/k²⁴,
with a strictly positive constant independent of the field strength. -/
theorem isolated_field_box_mass :
    ∃ d : ℝ, 0 < d ∧ ∀ k : ℝ, 1 ≤ k →
      d/k^24 ≤ (Measure.infinitePi fun _ : PathPauliBlockLabel => gaussianReal 0 1).real
        (isolatedFieldBox k) := by
  let d := (gaussianDensityFloor/800)^24
  refine ⟨d,pow_pos (div_pos gaussianDensityFloor_pos (by norm_num)) _,?_⟩
  intro k hk
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  let q := 1/(8*k)
  have hq : 0 < q := by dsimp [q]; positivity
  have hqle : q ≤ 1/8 := by
    apply (div_le_iff₀ (show 0 < 8*k by positivity)).mpr
    linarith only [hk]
  let c := isolatedFieldBlockCenter q
  have hcoord (i : PathPauliBlockLabel) : ENNReal.ofReal (gaussianDensityFloor/(800*k)) ≤
      gaussianReal 0 1 (Icc (c i-q/200) (c i+q/200)) := by
    have hc : c i = q ∨ c i = 0 := by unfold c isolatedFieldBlockCenter; split <;> simp
    have h := gaussian_interval_mass (l := c i-q/200) (u := c i+q/200)
      (by rcases hc with h|h <;> linarith only [h,hq,hqle])
      (by rcases hc with h|h <;> linarith only [h,hq,hqle])
    convert h using 2
    dsimp [q]
    ring
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp
  rw [Measure.infinitePi_eq_pi,isolatedFieldBox,Measure.pi_pi]
  refine le_trans ?_ (Finset.prod_le_prod' (s := Finset.univ) fun i _ => hcoord i)
  have hbase : 0 ≤ gaussianDensityFloor/(800*k) := div_nonneg gaussianDensityFloor_pos.le (by positivity)
  rw [Finset.prod_const,Finset.card_univ,← ENNReal.ofReal_pow hbase]
  have hcard : Fintype.card PathPauliBlockLabel = 24 := by
    simp [PathPauliBlockLabel,PathPauliDirections,Fintype.card_prod,Fintype.card_sum]
  rw [hcard]
  dsimp only [d]
  rw [← div_pow,div_div]

end
end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.RHTower.ThetaCuspCurvatureProjectiveGlobal

/-! Global logarithmic convexity of the actual source curvature. The precise
first-atom velocity gap propagates from infinity through the curvature defect. -/

noncomputable section
open Set Filter Topology
namespace RHTower.ThetaCurvature

local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "a" => thetaCuspLogCurvatureJetTwo
local notation "S" => thetaCuspSingleAtomReflectionScale 1
local notation "q" => thetaCuspLikelihoodCoordinate

/-- The subleading actual-source gap retains the exact first-atom sign. -/
theorem scaledVelocityGap_limit :
    Tendsto (fun x => S x*(2*c x-v x)) atTop (𝓝 (24:ℝ)) := by
  have hi := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 1 (by norm_num)
  have ha : Tendsto (fun x : ℝ => 24*(1+(3/2:ℝ)*(1/q x))^3)
      atTop (𝓝 (24:ℝ)) := by
    have hOne : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    convert! (((hOne.add (hi.const_mul (3/2:ℝ))).pow 3).const_mul 24)
      using 1 <;> norm_num
  have hk := thetaCuspC5FarTail_scaled_likelihoodThirdCumulant_source_tendsto_zero 4
  have hv := thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero 3
  have h := (ha.sub (hk.const_mul 8)).add (hv.const_mul 16)
  have h' : Tendsto (fun x => 24*(1+(3/2:ℝ)*(1/q x))^3-
      8*(S x^4*thetaCuspLikelihoodThirdCumulant (q x))+
      16*(S x^3*thetaCuspLikelihoodVariance (q x))) atTop (𝓝 (24:ℝ)) := by
    simpa only [mul_zero, sub_zero, add_zero] using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hq := thetaCuspBornWittenWeight_pos (n := 1) (by norm_num) hx0.le
  rw [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate] at hq
  unfold thetaCuspLogCurvature thetaCuspLogCurvatureJet
  rw [iteratedDeriv_two_thetaCuspLogSource_eq_factor hx0,
    iteratedDeriv_three_thetaCuspLogSource_eq_full_jets hx0,
    thetaCuspFirstAtomLogJetThree,
    ← thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo hx0,
    ← thetaCuspLikelihoodSourceLogPartitionJetThree_eq_higherLikelihoodLogJetThree hx0]
  unfold thetaCuspBornWittenLogCurvature thetaCuspBornWittenCurvature
    thetaCuspBornWittenLogThirdDerivative thetaCuspLikelihoodSourceLogPartitionJetTwo
    thetaCuspLikelihoodSourceLogPartitionJetThree
  rw [thetaCuspC5FarTail_morseScale_one_eq_reflectionScale,
    thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate,
    thetaCuspC5FarTail_scale_eq_coordinate_add]
  field_simp [hq.ne']
  ring

private def velocityGapCurrent (x : ℝ) : ℝ := Real.exp (2*x)*(2*c x-v x)

private theorem velocityGapCurrent_hasDerivAt (x : ℝ) :
    HasDerivAt velocityGapCurrent
      (-Real.exp (2*x)*ThetaCuspDefect.curvatureDefect x) x := by
  have he := (Real.hasDerivAt_exp (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hd := ((hasDerivAt_thetaCuspLogCurvature x).const_mul 2).sub
    (hasDerivAt_thetaCuspLogCurvatureJet x)
  convert! he.mul hd using 1
  dsimp [velocityGapCurrent, ThetaCuspDefect.curvatureDefect]
  ring

private theorem velocityGapCurrent_strictAnti : StrictAntiOn velocityGapCurrent (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro x _
    exact (velocityGapCurrent_hasDerivAt x).continuousAt.continuousWithinAt
  · intro x hx
    have hxpos : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    rw [(velocityGapCurrent_hasDerivAt x).deriv]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (Real.exp_pos _))
      (ThetaCuspDefect.curvatureDefect_pos hxpos.le)

private theorem eventually_velocityGapCurrent_pos :
    ∀ᶠ x : ℝ in atTop, 0 < velocityGapCurrent x := by
  have h := (tendsto_order.1 scaledVelocityGap_limit).1 0 (by norm_num)
  filter_upwards [h] with x hx
  have hS : 0 < S x := by unfold thetaCuspSingleAtomReflectionScale; positivity
  exact mul_pos (Real.exp_pos _) ((mul_pos_iff_of_pos_left hS).mp hx)

/-- The actual curvature grows strictly more slowly than its limiting exponential rate. -/
theorem velocityGap_pos {x : ℝ} (hx : 0 ≤ x) : 0 < 2*c x-v x := by
  obtain ⟨X,hX⟩ := eventually_atTop.1 eventually_velocityGapCurrent_pos
  let y := max X (x+1)
  have hxy : x < y := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hy : 0 ≤ y := hx.trans hxy.le
  have h := velocityGapCurrent_strictAnti hx hy hxy
  have hp := lt_trans (hX y (le_max_left _ _)) h
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hp

/-- Curvature logarithmic convexity numerator for the literal source. -/
def logEnergy (x : ℝ) : ℝ := c x*a x-v x^2

/-- Global strict logarithmic convexity, with the actual tail correction retained. -/
theorem logEnergy_pos {x : ℝ} (hx : 0 ≤ x) : 0 < logEnergy x := by
  have hc := thetaCuspLogCurvature_pos x
  have hv : 0 ≤ v x := by
    rcases eq_or_lt_of_le hx with h | h
    · rw [← h]
      simp only [thetaCuspLogCurvatureJet,
        iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 3) ⟨1,rfl⟩, neg_zero, le_refl]
    · exact (thetaCuspLogCurvatureJet_pos_of_pos h).le
  have he : logEnergy x = c x*ThetaCuspDefect.curvatureDefect x+
      (2*c x-v x)*(2*c x+v x) := by
    unfold logEnergy ThetaCuspDefect.curvatureDefect
    ring
  rw [he]
  exact add_pos (mul_pos hc (ThetaCuspDefect.curvatureDefect_pos hx))
    (mul_pos (velocityGap_pos hx) (by positivity))

/-- Projective descent also gives the exact decreasing logarithmic-curvature energy. -/
theorem logEnergy_hasDerivAt (x : ℝ) :
    HasDerivAt logEnergy (-thetaCuspCompletedCurvatureProjectiveEnergy x) x := by
  convert! ((hasDerivAt_thetaCuspLogCurvature x).mul
    (hasDerivAt_thetaCuspLogCurvatureJetTwo x)).sub
      ((hasDerivAt_thetaCuspLogCurvatureJet x).pow 2) using 1
  dsimp [logEnergy, thetaCuspCompletedCurvatureProjectiveEnergy]
  ring

end RHTower.ThetaCurvature

import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossLoad
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspAllRankNativeTail

/-!
# Gaussian tail of the polynomially profiled cross-load

The profiled compensation has polynomial center factors multiplying the
source square and its first derivative. Exponential reflection-scale growth
makes these terms vanish in every entry touched by the cross-load, leaving
the same strictly positive Gaussian moment matrix.
-/

noncomputable section
open Matrix Filter Topology RHTower RHTower.ThetaCuspGaussianLimit
namespace GaloisForLFunctions.ThetaCuspSections.FifthPolynomialCross
open EvenFiveEndpoint

/-- Polynomial coefficients of the exact differentiated source correction. -/
theorem compensation_expansion (x : ℝ) : compensation x =
    (3-20*x^2+28*x^4)*thetaCuspFullSource x^2+
      (2*x-8*x^3+8*x^5)*thetaCuspFullSource x*deriv thetaCuspFullSource x := by
  unfold compensation thetaCuspCenterCompensationSource
  ring

private theorem center_power_div_scale (k n : ℕ) (hn : 0 < n) :
    Tendsto (fun x : ℝ => x^k/thetaCuspSingleAtomReflectionScale 1 x^n)
      atTop (𝓝 0) := by
  have hb : (0 : ℝ) < 2*(n : ℝ) := by positivity
  have h := (GaloisForLFunctions.HTGeometry.tendsto_pow_mul_exp_neg_mul_atTop hb k).const_mul
    ((Real.pi^n)⁻¹)
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards with x
  have he : Real.exp (2*(n : ℝ)*x)=Real.exp (2*x)^n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one,
    mul_pow,Real.exp_neg,he,div_eq_mul_inv]
  ring

private theorem square_coefficient_limit :
    Tendsto (fun x : ℝ => (3-20*x^2+28*x^4)/thetaCuspSingleAtomReflectionScale 1 x^4)
      atTop (𝓝 0) := by
  have h := (((center_power_div_scale 0 4 (by norm_num)).const_mul 3).sub
    ((center_power_div_scale 2 4 (by norm_num)).const_mul 20)).add
    ((center_power_div_scale 4 4 (by norm_num)).const_mul 28)
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards with x
  ring

private theorem slope_coefficient_limit :
    Tendsto (fun x : ℝ => (2*x-8*x^3+8*x^5)/thetaCuspSingleAtomReflectionScale 1 x^3)
      atTop (𝓝 0) := by
  have h := (((center_power_div_scale 1 3 (by norm_num)).const_mul 2).sub
    ((center_power_div_scale 3 3 (by norm_num)).const_mul 8)).add
    ((center_power_div_scale 5 3 (by norm_num)).const_mul 8)
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards with x
  ring

/-- The profiled compensation vanishes at the first affected Gaussian entry scale. -/
theorem compensation_four_limit :
    Tendsto (fun x : ℝ => compensation x/
      (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^4)) atTop (𝓝 0) := by
  have hm := thetaCuspFullSource_div_firstAtom_tendsto_one
  have hs := thetaCuspFullSource_deriv_div_firstAtom_scale_tendsto
  have h := (square_coefficient_limit.mul (hm.pow 2)).add
    ((slope_coefficient_limit.mul hm).mul hs)
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hf := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))).ne'
  rw [compensation_expansion]
  field_simp [hq,hf] <;> ring

private theorem compensation_limit (n : ℕ) (hn : 4 ≤ n) :
    Tendsto (fun x : ℝ => compensation x/
      (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^n)) atTop (𝓝 0) := by
  have h := compensation_four_limit.mul
    (thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero.pow (n-4))
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hf := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))).ne'
  conv_rhs => rw [← Nat.sub_add_cancel hn,pow_add]
  field_simp [hq,hf]

private theorem cross_load_support (i j : Fin 5) (h : i.val+j.val < 4) :
    crossLoad paidSevenSchur i j=0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [crossLoad,loadMap,Matrix.mul_apply,Fin.sum_univ_succ]

private def balanced (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
  thetaCuspNativeScaledEvenJet (i.val+j.val) x+
    crossLoad paidSevenSchur i j*(compensation x/
      (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^(i.val+j.val)))

private theorem balanced_limit (i j : Fin 5) : Tendsto (fun x => balanced x i j)
    atTop (𝓝 (gaussianMoment (i.val+j.val))) := by
  have hn := native_scaled_jet_tendsto (i.val+j.val)
  rw [profile_signed_even_jet] at hn
  have hd : Tendsto (fun x => crossLoad paidSevenSchur i j*(compensation x/
      (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^(i.val+j.val))))
      atTop (𝓝 0) := by
    by_cases hij : i.val+j.val < 4
    · simp only [cross_load_support i j hij,zero_mul]
      exact tendsto_const_nhds
    · simpa only [mul_zero] using
        (compensation_limit (i.val+j.val) (by omega)).const_mul (crossLoad paidSevenSchur i j)
  simpa only [balanced,add_zero] using hn.add hd

/-- The complete polynomially profiled cross-load preserves a positive cofinal ray. -/
theorem repair_posDef_eventually : ∀ᶠ x : ℝ in atTop, (repair x).PosDef := by
  have hB := crossCoefficient_posDef.posSemidef.conjTranspose_mul_mul_same loadMap
  have hs (i j : Fin 5) : crossLoad paidSevenSchur i j=crossLoad paidSevenSchur j i := by
    have h := congrFun (congrFun hB.isHermitian j) i
    simpa only [crossLoad,Matrix.conjTranspose_apply,star_trivial] using h
  have hh (x : ℝ) : (balanced x).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial,balanced,hs j i,add_comm]
  have hg : Matrix.PosDef (fun i j : Fin 5 => gaussianMoment (i.val+j.val)) := by
    simpa only [Nat.add_zero] using gaussian_matrix_posDef 5 0
  have hp := GaloisForLFunctions.HTGeometry.posDef_eventually_of_tendsto hg
    (Filter.Eventually.of_forall hh) balanced_limit
  filter_upwards [hp,eventually_gt_atTop (0 : ℝ)] with x hx hx0
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let D : Matrix (Fin 5) (Fin 5) ℝ := diagonal (fun i => f*q^i.val)
  have hq : q ≠ 0 := by dsimp [q,thetaCuspSingleAtomReflectionScale]; positivity
  have hf : f ≠ 0 := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx0 (by norm_num : 0 < (1 : ℕ))).ne'
  have hD : Function.Injective D.mulVec := by
    intro v w h
    funext i
    have hi := congrFun h i
    simp only [D,Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (mul_ne_zero hf (pow_ne_zero _ hq)) hi
  have he : repair x=Dᴴ*balanced x*D := by
    ext i j
    simp only [D,Matrix.diagonal_conjTranspose,star_trivial,Matrix.diagonal_mul,
      Matrix.mul_diagonal,repair,balanced,Matrix.add_apply,Matrix.smul_apply,
      smul_eq_mul,nativeShiftedMatrix,thetaCuspNativeScaledEvenJet,Nat.add_zero]
    change (-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x+
      compensation x*crossLoad paidSevenSchur i j =
      (f*q^i.val)*(((-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x)/
        (f^2*q^(i.val+j.val))+crossLoad paidSevenSchur i j*(compensation x/
        (f^2*q^(i.val+j.val))))*(f*q^j.val)
    simp only [pow_add]
    field_simp [hf,hq]
  rw [he]
  exact hx.conjTranspose_mul_mul_same hD

/-- Only a bounded center interval remains outside the proven positive regions. -/
theorem repair_compact_gap : ∃ δ R : ℝ, 0 < δ ∧ δ ≤ R ∧ ∀ x : ℝ,
    0 ≤ x → (x < δ ∨ |x-EightCrossSource.center| < δ ∨ R ≤ x) → (repair x).PosDef := by
  obtain ⟨δ,hδ,hnear⟩ := repair_neighborhoods
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.mp repair_posDef_eventually
  refine ⟨δ,max R δ,hδ,le_max_right _ _,fun x hx h => ?_⟩
  rcases h with h | h | h
  · exact hnear x (Or.inl (by simpa only [abs_of_nonneg hx] using h))
  · exact hnear x (Or.inr h)
  · exact hR x ((le_max_left _ _).trans h)

/-- The exact flux representative is positive on common origin, scale-eight, and tail regions. -/
theorem weightedRepair_compact_gap : ∃ δ R : ℝ, 0 < δ ∧ δ ≤ R ∧ ∀ a r : ℝ,
    0 < a → 0 < r → (r < δ ∨ |r-2*EightCrossSource.center| < δ ∨ R ≤ r) →
      (weightedRepair a r).PosDef := by
  obtain ⟨δ,R,hδ,hδR,hs⟩ := repair_compact_gap
  refine ⟨2*δ,2*R,by positivity,by linarith only [hδR],fun a r ha hr h => ?_⟩
  have hp : (repair (r/2)).PosDef := by
    apply hs (r/2) (by positivity)
    rcases h with h | h | h
    · exact Or.inl (by linarith only [h])
    · refine Or.inr (Or.inl ?_)
      rw [show r/2-EightCrossSource.center=(r-2*EightCrossSource.center)/2 by ring,
        abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
      linarith only [h]
    · exact Or.inr (Or.inr (by linarith only [h]))
  have hw := mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
  have hd := sub_nonneg.mpr (deriv_flux_lower ha.le hr.le)
  have hB := crossCoefficient_posDef.posSemidef.conjTranspose_mul_mul_same loadMap
  rw [weightedRepair_decomposition]
  exact (hp.smul hw).add_posSemidef (hB.smul hd)

end GaloisForLFunctions.ThetaCuspSections.FifthPolynomialCross

import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularSpectralContinuation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalAngularForcing

/-! Joint bounds over bounded spectral sets and the complete positive-height cusp. -/
open Complex Real Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMAngularSeries
noncomputable section

/-- The infinite coefficient mass has one bound on every bounded spectral set. -/
theorem scalar_heightDecayConstant_uniform (R l : ℝ) (hR : 0 < R) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖u‖ ≤ R → heightDecayConstant u u 0 l ≤ C := by
  let r := 3*R+1
  let D := Real.exp (R^(2 : ℕ)/(2*l))*Real.sqrt (2*Real.pi/l)
  let M := fun N : ℕ => ((N:ℝ)+1)^r * Real.exp (-((N:ℝ)*(l/2)))
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hM : Summable M := (summable_natSucc_rpow_exp_neg_and_tsum_le hr
    (by positivity : 0 < l/2)).1
  refine ⟨D * ∑' N, M N, mul_nonneg hD (tsum_nonneg fun N => by dsimp [M]; positivity), ?_⟩
  intro u hu
  have hcoef (N : ℕ) : ‖coefficient u 0 N‖ ≤ ((N:ℝ)+1)^r := by
    simp only [coefficient,pow_zero,mul_one]
    calc
      _ ≤ ((N+1:ℕ):ℝ)^(3*|u.re|+1) := d4BM_norm_completedEisensteinWhittakerCoefficient_le _ _
      _ ≤ _ := by
        simp only [Nat.cast_add,Nat.cast_one]
        apply Real.rpow_le_rpow_of_exponent_le (by have := Nat.cast_nonneg (α := ℝ) N; linarith : (1:ℝ) ≤ (N:ℝ)+1)
        dsimp [r]
        linarith [(Complex.abs_re_le_norm u).trans hu]
  have hBC : besselBound u l ≤ D := by
    dsimp [besselBound,D]
    gcongr
  have hterm (N : ℕ) : ‖coefficient u 0 N‖ * Real.exp (-(((N:ℝ)+1)*l/2)) ≤ M N := by
    apply mul_le_mul (hcoef N)
    · apply Real.exp_le_exp.mpr
      linarith
    · positivity
    · positivity
  have hs : Summable (fun N : ℕ => ‖coefficient u 0 N‖ * Real.exp (-(((N:ℝ)+1)*l/2))) := by
    simpa only [mul_div_assoc] using coefficient_weighted_summable u 0 (l/2) (by positivity)
  exact mul_le_mul hBC (Summable.tsum_le_tsum hterm hs hM)
    (tsum_nonneg fun N => by positivity) hD

private theorem scalar_height_factor_bounded (l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, l ≤ y → y^(1/2:ℝ)*Real.exp (-y/2) ≤ C := by
  have ht : Tendsto (fun y : ℝ => y^(1/2:ℝ)*Real.exp (-y/2)) atTop (𝓝 0) := by
    convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/2) (1/2) (by norm_num) using 1
    ext y
    congr 2
    ring
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 1 (by norm_num))
  have hc : ContinuousOn (fun y : ℝ => y^(1/2:ℝ)*Real.exp (-y/2)) (Icc l M) := by
    intro y hy
    exact ((Real.contDiffAt_rpow_const_of_ne (ne_of_gt (hl.trans_le hy.1)) (n := 0)).continuousAt.mul
      (by fun_prop)).continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 1, (by exact le_trans (by norm_num) (le_max_right C 1)), ?_⟩
  intro y hy
  by_cases h : M ≤ y
  · exact (hM y h).le.trans (le_max_right C 1)
  · exact (le_abs_self _).trans ((hC y ⟨hy,le_of_not_ge h⟩).trans (le_max_left C 1))

/-- Both full signed scalar series are bounded jointly in height and spectral parameter. -/
theorem scalar_value_uniform_cusp (R l : ℝ) (hR : 0 < R) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℂ) (negative : Bool) (z : Fin 2 → ℝ),
      ‖u‖ ≤ R → l ≤ z 1 → ‖value u u (1/2) 0 negative z‖ ≤ C := by
  obtain ⟨A,hA,ha⟩ := scalar_heightDecayConstant_uniform R l hR hl
  obtain ⟨B,hB,hb⟩ := scalar_height_factor_bounded l hl
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro u negative z hu hz
  calc
    _ ≤ heightDecayConstant u u 0 l * (z 1)^(1/2:ℝ) * Real.exp (-(z 1)/2) :=
      value_height_decay u u (1/2) 0 negative l hl z hz
    _ ≤ A * ((z 1)^(1/2:ℝ) * Real.exp (-(z 1)/2)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (ha u hu)
        (mul_nonneg (Real.rpow_nonneg (hl.trans_le hz).le _) (Real.exp_nonneg _))
    _ ≤ A*B := mul_le_mul_of_nonneg_left (hb (z 1) hz) hA

/-- The original full tail has one bound on a spectral ball and an entire cusp half-strip. -/
theorem scalar_tail_uniform_cusp (R l : ℝ) (hR : 0 < R) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℂ) (z : Fin 2 → ℝ),
      ‖u‖ ≤ R → l ≤ z 1 → ‖D4BMGlobalAngularResponse.tail u z‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := scalar_value_uniform_cusp R l hR hl
  refine ⟨4*C,by positivity,?_⟩
  intro u z hu hz
  have hy := hl.trans_le hz
  have he : D4BMGlobalAngularResponse.tail u z =
      2*(value u u (1/2) 0 false z + value u u (1/2) 0 true z) := by
    simp only [D4BMGlobalAngularResponse.tail,d4BMCompletedEisensteinCuspTailPart,
      d4BMCompletedEisensteinFullSignedZeroWord,
      signedTail_eq_value _ _ _ _ _ z hy,Nat.cast_zero,zero_add]
  rw [he,norm_mul]
  norm_num only [Complex.norm_ofNat]
  have hn := norm_add_le (value u u (1/2) 0 false z) (value u u (1/2) 0 true z)
  nlinarith [hb u false z hu hz,hb u true z hu hz]

end
end RHTower.D4BMAngularSeries

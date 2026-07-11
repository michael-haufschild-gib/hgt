import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer
import GaloisForLFunctions.RHTower.GelfondSchneider
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Group.SubmonoidClosure

open Complex Metric Set Filter Topology

namespace RHTower

noncomputable section

def depthThreeBalance (σ : ℝ) : ℝ :=
  (2 : ℝ) ^ (-σ) + (3 : ℝ) ^ (-σ)

lemma continuous_depthThreeBalance : Continuous depthThreeBalance := by
  unfold depthThreeBalance
  exact (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).comp continuous_neg |>.add
    ((Real.continuous_const_rpow (by norm_num : (3 : ℝ) ≠ 0)).comp continuous_neg)

lemma depthThreeBalance_zero : depthThreeBalance 0 = 2 := by
  norm_num [depthThreeBalance]

lemma depthThreeBalance_one : depthThreeBalance 1 = 5 / 6 := by
  norm_num [depthThreeBalance, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]

 theorem exists_depthThree_balance :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ depthThreeBalance σ = 1 := by
  have hmem : (1 : ℝ) ∈ Set.Icc (depthThreeBalance 1) (depthThreeBalance 0) := by
    rw [depthThreeBalance_zero, depthThreeBalance_one]
    norm_num
  obtain ⟨σ, hσmem, hσ⟩ :=
    (intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num)
      continuous_depthThreeBalance.continuousOn) hmem
  refine ⟨σ, ?_, ?_, hσ⟩
  · rcases hσmem with ⟨hσ0, hσ1⟩
    exact lt_of_le_of_ne hσ0 (by
      intro h
      subst σ
      rw [depthThreeBalance_zero] at hσ
      norm_num at hσ)
  · rcases hσmem with ⟨hσ0, hσ1⟩
    exact lt_of_le_of_ne hσ1 (by
      intro h
      subst σ
      rw [depthThreeBalance_one] at hσ
      norm_num at hσ)

end
end RHTower

namespace RHTower

noncomputable section

lemma exists_depthThree_rotation_subsequence :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      Tendsto (fun n => (k n) •
        ((Real.log 3 / Real.log 2 : ℝ) : AddCircle (1 : ℝ)))
        atTop (nhds
          (((1 - Real.log 3 / Real.log 2) / 2 : ℝ) : AddCircle (1 : ℝ))) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  let α : ℝ := Real.log 3 / Real.log 2
  let a : AddCircle (1 : ℝ) := (α : AddCircle (1 : ℝ))
  let b : AddCircle (1 : ℝ) := (((1 - α) / 2 : ℝ) : AddCircle (1 : ℝ))
  have hirr : Irrational α := by
    dsimp [α]
    exact GaloisForLFunctions.RHTower.irrational_log_ratio
      (by norm_num) (by norm_num) (by norm_num)
  have hdZ : DenseRange (fun m : ℤ => m • a) := by
    rw [AddCircle.denseRange_zsmul_coe_iff]
    simpa [a] using hirr
  have hbcl : b ∈ closure (Set.range (fun m : ℤ => m • a)) := hdZ b
  have hbtop : b ∈ (AddSubgroup.zmultiples a).topologicalClosure := by
    simpa only [AddSubgroup.coe_zmultiples] using hbcl
  have hcluster : MapClusterPt b atTop (fun n : ℕ => n • a) :=
    mapClusterPt_atTop_nsmul_iff_mem_topologicalClosure_zmultiples.mpr hbtop
  obtain ⟨k, hk, htend⟩ := hcluster.tendsto_subseq
  refine ⟨k, hk, ?_⟩
  simpa [Function.comp_def, a, b] using htend

end
end RHTower

namespace RHTower

noncomputable section

lemma exists_depthThree_phase_subsequence :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      Tendsto (fun n => Complex.exp
        (-(((Real.pi + 2 * Real.pi * k n) * (Real.log 3 / Real.log 2) : ℝ) : ℂ) * I))
        atTop (𝓝 (-1)) := by
  obtain ⟨k, hk, hrot⟩ := exists_depthThree_rotation_subsequence
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  let α : ℝ := Real.log 3 / Real.log 2
  let a : AddCircle (1 : ℝ) := (α : AddCircle (1 : ℝ))
  let b : AddCircle (1 : ℝ) := (((1 - α) / 2 : ℝ) : AddCircle (1 : ℝ))
  have hcircle : Tendsto (fun n => AddCircle.toCircle (k n • a)) atTop
      (𝓝 (AddCircle.toCircle b)) :=
    AddCircle.continuous_toCircle.continuousAt.tendsto.comp (by
      simpa [α, a, b] using hrot)
  let twist : Circle → Circle := fun q => Circle.exp (-Real.pi * α) * q⁻¹
  have htwist_cont : Continuous twist := by
    dsimp [twist]
    fun_prop
  have htwist := htwist_cont.continuousAt.tendsto.comp hcircle
  have hseq : (fun n => twist (AddCircle.toCircle (k n • a))) =
      (fun n => Circle.exp (-((Real.pi + 2 * Real.pi * k n) * α))) := by
    funext n
    dsimp [twist]
    rw [AddCircle.toCircle_nsmul]
    have ha : AddCircle.toCircle a = Circle.exp (2 * Real.pi * α) := by
      dsimp [a]
      rw [AddCircle.toCircle_apply_mk]
      congr 1
      ring
    rw [ha, ← Circle.exp_nsmul, ← Circle.exp_neg, ← Circle.exp_add]
    congr 1
    simp [nsmul_eq_mul]
    ring
  have hlim : twist (AddCircle.toCircle b) = Circle.exp (-Real.pi) := by
    dsimp [twist, b]
    rw [AddCircle.toCircle_apply_mk]
    rw [← Circle.exp_neg, ← Circle.exp_add]
    congr 1
    ring
  rw [hseq, hlim] at htwist
  have hcoe : Tendsto
      (fun n => ((Circle.exp (-((Real.pi + 2 * Real.pi * k n) * α) : Circle) : ℂ)))
      atTop (𝓝 ((Circle.exp (-Real.pi) : Circle) : ℂ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp htwist
  refine ⟨k, hk, ?_⟩
  have hminus : ((Circle.exp (-Real.pi) : Circle) : ℂ) = -1 := by
    rw [Circle.coe_exp]
    simpa only [ofReal_neg, ofReal_pi, neg_mul] using Complex.exp_neg_pi_mul_I
  rw [hminus] at hcoe
  simpa only [Circle.coe_exp, α, ofReal_neg, ofReal_mul, ofReal_add, ofReal_pi,
    ofReal_natCast, neg_mul] using hcoe

end
end RHTower

namespace RHTower
noncomputable section

def depthThreeHeight (k : ℕ) : ℝ :=
  (Real.pi + 2 * Real.pi * k) / Real.log 2

lemma depthThreeHeight_mul_log_two (k : ℕ) :
    depthThreeHeight k * Real.log 2 = Real.pi + 2 * Real.pi * k := by
  unfold depthThreeHeight
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

lemma depthThree_two_phase (k : ℕ) :
    (2 : ℂ) ^ (-(I * (depthThreeHeight k : ℂ))) = -1 := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num)]
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hlog]
  have hexp : (Real.log 2 : ℂ) * (-(I * (depthThreeHeight k : ℂ))) =
      -((Real.pi + 2 * Real.pi * k : ℝ) : ℂ) * I := by
    have hr : Real.log 2 * depthThreeHeight k = Real.pi + 2 * Real.pi * k := by
      rw [mul_comm, depthThreeHeight_mul_log_two]
    have hc : (Real.log 2 : ℂ) * (depthThreeHeight k : ℂ) =
        ((Real.pi + 2 * Real.pi * k : ℝ) : ℂ) := by
      exact_mod_cast hr
    rw [show (Real.log 2 : ℂ) * (-(I * (depthThreeHeight k : ℂ))) =
      -((Real.log 2 : ℂ) * (depthThreeHeight k : ℂ)) * I by ring, hc]
  rw [hexp]
  have hsplit : -((Real.pi + 2 * Real.pi * k : ℝ) : ℂ) * I =
      -(Real.pi : ℂ) * I + (-(k : ℂ)) * (2 * (Real.pi : ℂ) * I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add]
  have hperiod : Complex.exp (-(k : ℂ) * (2 * (Real.pi : ℂ) * I)) = 1 := by
    rw [show -(k : ℂ) * (2 * (Real.pi : ℂ) * I) =
      -((k : ℂ) * (2 * (Real.pi : ℂ) * I)) by ring, Complex.exp_neg,
      Complex.exp_nat_mul_two_pi_mul_I]
    simp
  rw [hperiod, mul_one]
  simpa using Complex.exp_neg_pi_mul_I

end
end RHTower

namespace RHTower
noncomputable section

lemma depthThree_three_phase_eq (k : ℕ) :
    (3 : ℂ) ^ (-(I * (depthThreeHeight k : ℂ))) =
      Complex.exp
        (-(((Real.pi + 2 * Real.pi * k) * (Real.log 3 / Real.log 2) : ℝ) : ℂ) * I) := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num)]
  have hlog : Complex.log (3 : ℂ) = (Real.log 3 : ℂ) := by
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hlog]
  congr 1
  have hr : Real.log 3 * depthThreeHeight k =
      (Real.pi + 2 * Real.pi * k) * (Real.log 3 / Real.log 2) := by
    unfold depthThreeHeight
    field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hc : (Real.log 3 : ℂ) * (depthThreeHeight k : ℂ) =
      (((Real.pi + 2 * Real.pi * k) * (Real.log 3 / Real.log 2) : ℝ) : ℂ) := by
    exact_mod_cast hr
  rw [show (Real.log 3 : ℂ) * (-(I * (depthThreeHeight k : ℂ))) =
    -((Real.log 3 : ℂ) * (depthThreeHeight k : ℂ)) * I by ring, hc]

lemma depthThreeHeight_tendsto_atTop {k : ℕ → ℕ} (hk : StrictMono k) :
    Tendsto (fun n => depthThreeHeight (k n)) atTop atTop := by
  have hkTop : Tendsto k atTop atTop := hk.tendsto_atTop
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hkTop
  rw [show (fun n => depthThreeHeight (k n)) =
      fun n => Real.pi / Real.log 2 + (2 * Real.pi / Real.log 2) * (k n : ℝ) by
    funext n
    unfold depthThreeHeight
    ring]
  have hc : 0 < 2 * Real.pi / Real.log 2 := by positivity
  exact tendsto_const_nhds.add_atTop (hkR.const_mul_atTop hc)

lemma exists_depthThree_cpow_phase_subsequence :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      Tendsto (fun n => (3 : ℂ) ^ (-(I * (depthThreeHeight (k n) : ℂ))))
        atTop (𝓝 (-1)) ∧
      Tendsto (fun n => depthThreeHeight (k n)) atTop atTop := by
  obtain ⟨k, hk, hphase⟩ := exists_depthThree_phase_subsequence
  refine ⟨k, hk, ?_, depthThreeHeight_tendsto_atTop hk⟩
  simpa only [depthThree_three_phase_eq] using hphase

end
end RHTower

namespace RHTower
noncomputable section

def depthThreeLimit (σ : ℝ) (z : ℂ) : ℂ :=
  1 - (((2 : ℝ) ^ (-σ) : ℝ) : ℂ) * (2 : ℂ) ^ (-z) -
    (((3 : ℝ) ^ (-σ) : ℝ) : ℂ) * (3 : ℂ) ^ (-z)

lemma depthThreeLimit_zero {σ : ℝ} (hσ : depthThreeBalance σ = 1) :
    depthThreeLimit σ 0 = 0 := by
  rw [depthThreeLimit]
  simp only [neg_zero, Complex.cpow_zero, mul_one]
  have hc :
      ((((2 : ℝ) ^ (-σ) : ℝ) : ℂ) + (((3 : ℝ) ^ (-σ) : ℝ) : ℂ)) = 1 := by
    exact_mod_cast hσ
  linear_combination -hc

lemma hasDerivAt_depthThreeLimit (σ : ℝ) (z : ℂ) :
    HasDerivAt (depthThreeLimit σ)
      ((((2 : ℝ) ^ (-σ) : ℝ) : ℂ) *
          ((2 : ℂ) ^ (-z) * Complex.log 2) +
       (((3 : ℝ) ^ (-σ) : ℝ) : ℂ) *
          ((3 : ℂ) ^ (-z) * Complex.log 3)) z := by
  have h2 : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ (-w))
      ((2 : ℂ) ^ (-z) * Complex.log 2 * (-1)) z :=
    (hasDerivAt_id z).neg.const_cpow (Or.inl (by norm_num))
  have h3 : HasDerivAt (fun w : ℂ => (3 : ℂ) ^ (-w))
      ((3 : ℂ) ^ (-z) * Complex.log 3 * (-1)) z :=
    (hasDerivAt_id z).neg.const_cpow (Or.inl (by norm_num))
  unfold depthThreeLimit
  convert ((hasDerivAt_const z (1 : ℂ)).sub
    (h2.const_mul (((2 : ℝ) ^ (-σ) : ℝ) : ℂ))).sub
    (h3.const_mul (((3 : ℝ) ^ (-σ) : ℝ) : ℂ)) using 1 <;> ring

lemma deriv_depthThreeLimit_zero_pos (σ : ℝ) :
    0 < (deriv (depthThreeLimit σ) 0).re := by
  rw [(hasDerivAt_depthThreeLimit σ 0).deriv]
  simp only [neg_zero, Complex.cpow_zero, one_mul]
  have hlog2 : Complex.log (2 : ℂ) = (Real.log 2 : ℝ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  have hlog3 : Complex.log (3 : ℂ) = (Real.log 3 : ℝ) := by
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hlog2, hlog3]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, add_re]
  positivity

lemma depthThreeLimit_differentiable (σ : ℝ) :
    Differentiable ℂ (depthThreeLimit σ) :=
  fun z => (hasDerivAt_depthThreeLimit σ z).differentiableAt

end
end RHTower

namespace RHTower
noncomputable section

def depthThreeTranslatedApprox (σ : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  1 + (((2 : ℝ) ^ (-σ) : ℝ) : ℂ) *
      (2 : ℂ) ^ (-(I * (depthThreeHeight k : ℂ))) * (2 : ℂ) ^ (-z) +
    (((3 : ℝ) ^ (-σ) : ℝ) : ℂ) *
      (3 : ℂ) ^ (-(I * (depthThreeHeight k : ℂ))) * (3 : ℂ) ^ (-z)

lemma depthThreeTranslatedApprox_eq (σ : ℝ) (k : ℕ) (z : ℂ) :
    depthThreeTranslatedApprox σ k z =
      1 - (((2 : ℝ) ^ (-σ) : ℝ) : ℂ) * (2 : ℂ) ^ (-z) +
        (((3 : ℝ) ^ (-σ) : ℝ) : ℂ) *
          (3 : ℂ) ^ (-(I * (depthThreeHeight k : ℂ))) * (3 : ℂ) ^ (-z) := by
  rw [depthThreeTranslatedApprox, depthThree_two_phase]
  ring

lemma depthThreeTranslatedApprox_differentiable (σ : ℝ) (k : ℕ) :
    Differentiable ℂ (depthThreeTranslatedApprox σ k) := by
  intro z
  unfold depthThreeTranslatedApprox
  fun_prop

lemma depthThreeTranslatedApprox_tendstoLocallyUniformly
    {σ : ℝ} {k : ℕ → ℕ}
    (hphase : Tendsto
      (fun n => (3 : ℂ) ^ (-(I * (depthThreeHeight (k n) : ℂ)))) atTop (𝓝 (-1))) :
    TendstoLocallyUniformly (fun n => depthThreeTranslatedApprox σ (k n))
      (depthThreeLimit σ) atTop := by
  let a2 : ℂ := (((2 : ℝ) ^ (-σ) : ℝ) : ℂ)
  let a3 : ℂ := (((3 : ℝ) ^ (-σ) : ℝ) : ℂ)
  let base2 : ℂ → ℂ := fun z => (2 : ℂ) ^ (-z)
  let base3 : ℂ → ℂ := fun z => (3 : ℂ) ^ (-z)
  have hcoeff : Tendsto
      (fun n => a3 * (3 : ℂ) ^ (-(I * (depthThreeHeight (k n) : ℂ))))
      atTop (𝓝 (-a3)) := by
    convert tendsto_const_nhds.mul hphase using 1 <;> ring
  have hcoeffLU : TendstoLocallyUniformly
      (fun n (_ : ℂ) => a3 * (3 : ℂ) ^ (-(I * (depthThreeHeight (k n) : ℂ))))
      (fun _ : ℂ => -a3) atTop :=
    hcoeff.tendstoUniformly_const.tendstoLocallyUniformly
  have hbase3LU : TendstoLocallyUniformly (fun _ : ℕ => base3) base3 atTop :=
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => base3) atTop (𝓝 base3))
      .tendstoUniformly_const).tendstoLocallyUniformly
  have hvar : TendstoLocallyUniformly
      (fun n z => (a3 * (3 : ℂ) ^ (-(I * (depthThreeHeight (k n) : ℂ)))) * base3 z)
      (fun z => (-a3) * base3 z) atTop := by
    exact hcoeffLU.mul₀ hbase3LU continuous_const (by
      dsimp [base3]
      fun_prop)
  let fixed : ℂ → ℂ := fun z => 1 - a2 * base2 z
  have hfixed : TendstoLocallyUniformly (fun _ : ℕ => fixed) fixed atTop :=
    tendsto_const_nhds.tendstoUniformly_const.tendstoLocallyUniformly
  have hadd := hfixed.add hvar
  convert hadd using 1
  · funext n z
    rw [depthThreeTranslatedApprox_eq]
    rfl
  · funext z
    rfl
  · funext z
    unfold fixed base2 base3 a2 a3 depthThreeLimit
    ring

end
end RHTower

namespace RHTower
noncomputable section

def depthThreeDirichletFactor (s : ℂ) : ℂ :=
  1 + (2 : ℂ) ^ (-s) + (3 : ℂ) ^ (-s)

lemma depthThreeTranslatedApprox_eq_factor (σ : ℝ) (k : ℕ) (z : ℂ) :
    depthThreeTranslatedApprox σ k z =
      depthThreeDirichletFactor ((σ : ℂ) + I * (depthThreeHeight k : ℂ) + z) := by
  rw [depthThreeTranslatedApprox, depthThreeDirichletFactor]
  have h2 : (((2 : ℝ) ^ (-σ) : ℝ) : ℂ) = (2 : ℂ) ^ (-(σ : ℂ)) := by
    simpa only [ofReal_neg] using Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2) (-σ)
  have h3 : (((3 : ℝ) ^ (-σ) : ℝ) : ℂ) = (3 : ℂ) ^ (-(σ : ℂ)) := by
    simpa only [ofReal_neg] using Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3) (-σ)
  rw [h2, h3]
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have h3ne : (3 : ℂ) ≠ 0 := by norm_num
  rw [← Complex.cpow_add _ _ h2ne, ← Complex.cpow_add _ _ h2ne]
  rw [← Complex.cpow_add _ _ h3ne, ← Complex.cpow_add _ _ h3ne]
  congr 1 <;> ring

lemma depthThreeDirichletFactor_differentiable :
    Differentiable ℂ depthThreeDirichletFactor := by
  intro z
  unfold depthThreeDirichletFactor
  fun_prop

end
end RHTower

namespace RHTower
noncomputable section

/-- The depth-three Dirichlet factor has zeros arbitrarily high in the open critical strip. -/
theorem exists_depthThreeDirichletFactor_zero_high (B : ℝ) :
    ∃ s : ℂ, 0 < s.re ∧ s.re < 1 ∧ B ≤ s.im ∧ depthThreeDirichletFactor s = 0 := by
  obtain ⟨σ, hσ0, hσ1, hbalance⟩ := exists_depthThree_balance
  obtain ⟨k, hk, hphase, hheight⟩ := exists_depthThree_cpow_phase_subsequence
  have hconv : TendstoLocallyUniformly
      (fun n => depthThreeTranslatedApprox σ (k n)) (depthThreeLimit σ) atTop :=
    depthThreeTranslatedApprox_tendstoLocallyUniformly hphase
  have hGdiff : Differentiable ℂ (depthThreeLimit σ) :=
    depthThreeLimit_differentiable σ
  have hGzero : depthThreeLimit σ 0 = 0 := depthThreeLimit_zero hbalance
  have hnotEventuallyZero : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), depthThreeLimit σ z = 0 := by
    intro hev
    have hevEq : (fun z => depthThreeLimit σ z) =ᶠ[𝓝 (0 : ℂ)] (fun _ => 0) := by
      simpa only [Filter.EventuallyEq, Pi.zero_apply] using hev
    have hderiv := hevEq.deriv_eq
    have hpos := deriv_depthThreeLimit_zero_pos σ
    have hzeroDeriv : deriv (depthThreeLimit σ) 0 = 0 := by
      simpa using hderiv
    rw [hzeroDeriv] at hpos
    simp at hpos
  have hpunct : ∀ᶠ z in 𝓝[≠] (0 : ℂ), depthThreeLimit σ z ≠ 0 :=
    ((hGdiff.analyticAt 0).eventually_eq_zero_or_eventually_ne_zero).resolve_left
      hnotEventuallyZero
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hpunct
  let r : ℝ := min (σ / 2) (min ((1 - σ) / 2) (δ / 2))
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (half_pos hσ0) (lt_min (half_pos (sub_pos.mpr hσ1)) (half_pos hδ))
  have hrσ : r ≤ σ / 2 := min_le_left _ _
  have hr1σ : r ≤ (1 - σ) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrδ : r < δ :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (half_lt_self hδ)
  have hsphere : ∀ z ∈ sphere (0 : ℂ) r, depthThreeLimit σ z ≠ 0 := by
    intro z hz
    apply hδsub
    refine ⟨?_, ?_⟩
    · exact Metric.mem_ball.mpr ((Metric.mem_sphere.mp hz).trans_lt hrδ)
    · exact Set.mem_compl_singleton_iff.mpr (Metric.ne_of_mem_sphere hz hr.ne')
  have hlocal : ∀ᶠ n in atTop, ∃ w ∈ closedBall (0 : ℂ) r,
      depthThreeTranslatedApprox σ (k n) w = 0 :=
    eventually_exists_zero_closedBall_of_tendstoLocallyUniformly hconv hGdiff
      (Eventually.of_forall fun n => depthThreeTranslatedApprox_differentiable σ (k n))
      hr hGzero hsphere
  have hhigh : ∀ᶠ n in atTop, B + r ≤ depthThreeHeight (k n) :=
    hheight.eventually (eventually_ge_atTop (B + r))
  obtain ⟨n, ⟨w, hwball, hwzero⟩, hnheight⟩ := (hlocal.and hhigh).exists
  let s : ℂ := (σ : ℂ) + I * (depthThreeHeight (k n) : ℂ) + w
  have hwnorm : ‖w‖ ≤ r := by
    simpa [Metric.mem_closedBall] using hwball
  have hwre : |w.re| ≤ r := (Complex.abs_re_le_norm w).trans hwnorm
  have hwim : |w.im| ≤ r := (Complex.abs_im_le_norm w).trans hwnorm
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · dsimp [s]
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, zero_mul, mul_zero,
      sub_zero, zero_add]
    linarith [abs_le.mp hwre]
  · dsimp [s]
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, zero_mul, mul_zero,
      sub_zero, zero_add]
    linarith [abs_le.mp hwre]
  · dsimp [s]
    simp only [add_im, ofReal_im, mul_im, I_re, ofReal_re, I_im, zero_mul, one_mul, zero_add]
    linarith [abs_le.mp hwim]
  · rw [← depthThreeTranslatedApprox_eq_factor σ (k n) w]
    exact hwzero

end
end RHTower

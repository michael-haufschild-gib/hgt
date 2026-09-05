import GaloisForLFunctions.RHTower.SchattenLogResidueTraceClassPerturbation
import GaloisForLFunctions.RHTower.TraceNormBound
import GaloisForLFunctions.RHTower.SoninRegularizedColumnTail
import GaloisForLFunctions.HTGeometry.HilbertSchmidtFiniteRankDensity
import GaloisForLFunctions.RHTower.SoninRegularizedPrimeCoefficientBudget

/-!
# Unconditional logarithmic singular-prefix budget for the literal regularized Sonin column

Source coefficients and prime/depth labels are not changed. No Xi or RH premise is used.
This module does not assert a determinant weld or an RH conclusion.
-/

open ContinuousLinearMap
open scoped BigOperators
namespace RHTower
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem schattenOnePrefix_le_sqrt_hilbertSchmidt
    {T : H →L[ℂ] H} (hT : T.IsHilbertSchmidt) (N : ℕ) :
    schattenPowerPartialSum 1 T N ≤ Real.sqrt ((N : ℝ) * hsNormSq T) := by
  have hsum : Summable (fun n => approxNumber T n ^ 2) := by
    have h := (memSchattenClass_two_iff_isHilbertSchmidt T).mpr hT
    simpa [MemSchattenClass, Real.rpow_two] using h
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun _ : ℕ => (1 : ℝ)) (fun n => approxNumber T n)
  have hprefix : (∑ n ∈ Finset.range N, approxNumber T n ^ 2) ≤ hsNormSq T := by
    rw [hsNormSq_eq_tsum_approxNumber_sq hT]
    exact hsum.sum_le_tsum _ (fun n _ => sq_nonneg _)
  apply Real.le_sqrt_of_sq_le
  have hform : schattenPowerPartialSum 1 T N =
      ∑ n ∈ Finset.range N, approxNumber T n := by
    simp [schattenPowerPartialSum]
  rw [hform]
  have hsq' : (∑ n ∈ Finset.range N, approxNumber T n) ^ 2 ≤
      (N : ℝ) * ∑ n ∈ Finset.range N, approxNumber T n ^ 2 := by
    simpa using hsq
  exact hsq'.trans (mul_le_mul_of_nonneg_left hprefix (Nat.cast_nonneg N))

theorem schattenOnePrefix_le_traceClassHead_add_hilbertSchmidtTail
    {T S : H →L[ℂ] H} (hT : IsCompactOperator T)
    (hS : MemSchattenClass 1 S) (hE : (T - S).IsHilbertSchmidt) (N : ℕ) :
    schattenPowerPartialSum 1 T N ≤
      traceNorm H S + Real.sqrt ((N : ℝ) * hsNormSq (T - S)) := by
  have hdiff : MemSchattenClass 1 (T - (T - S)) := by simpa using hS
  have h := schattenPowerPartialSum_one_le_add_traceNorm_of_traceClass_sub
    hT hE.isCompactOperator hdiff N
  simp only [sub_sub_cancel] at h
  have ht := schattenOnePrefix_le_sqrt_hilbertSchmidt hE N
  linarith

end
end RHTower

open ContinuousLinearMap
open scoped BigOperators
namespace RHTower
noncomputable section
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem hsNormSq_rectangularLowerBlock_le {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T) :
    hsNormSq (rectangularLowerBlock T) ≤ hsNormSq T := by
  let I : F →L[ℂ] rectangularHilbertSum E F := rectangularRightInclusion
  let P : rectangularHilbertSum E F →L[ℂ] E := WithLp.fstL 2 ℂ E F
  have hI : ‖I‖ ≤ 1 := by
    apply I.opNorm_le_bound (by norm_num)
    intro x
    simpa [I] using (norm_rectangularRightInclusion_apply (E := E) x).le
  have hP : ‖P‖ ≤ 1 := by
    apply P.opNorm_le_bound (by norm_num)
    intro x
    simpa [P] using norm_fst_le_rectangularHilbertSum x
  have hnorm : hsNorm (rectangularLowerBlock T) ≤ hsNorm T := by
    calc
      _ ≤ ‖I‖ * hsNorm (T ∘L P) := (hT.comp_right P).hsNorm_comp_left_le I
      _ ≤ 1 * (hsNorm T * 1) := by
        apply mul_le_mul hI
          ((hT.hsNorm_comp_right_le P).trans
            (mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg _)))
          (Real.sqrt_nonneg _) (by norm_num)
      _ = _ := by ring
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hnorm 2
  simpa only [hsNorm, Real.sq_sqrt (hsNormSq_nonneg _)] using hsq

theorem rectApproxPrefix_le_traceClassHead_add_hilbertSchmidtTail
    {A H : E →L[ℂ] F} (hA : IsHilbertSchmidt A)
    (hH : MemRectSchattenClass 1 H) (hE : IsHilbertSchmidt (A - H)) (N : ℕ) :
    (∑ n ∈ Finset.range N, rectApproxNumber A n) ≤
      rectTraceNorm E F H + Real.sqrt ((N : ℝ) * hsNormSq (A - H)) := by
  have hAl : IsHilbertSchmidt (rectangularLowerBlock A) :=
    (hA.comp_right _).comp_left _
  have hEl : IsHilbertSchmidt (rectangularLowerBlock A - rectangularLowerBlock H) := by
    rw [← rectangularLowerBlock_sub]
    exact (hE.comp_right _).comp_left _
  have h := schattenOnePrefix_le_traceClassHead_add_hilbertSchmidtTail
    hAl.isCompactOperator ((memRectSchattenClass_iff_lowerBlock 1 H).mp hH) hEl N
  simp only [schattenPowerPartialSum, Real.rpow_one,
    ← rectApproxNumber_eq_approxNumber_lowerBlock,
    ← rectTraceNorm_eq_traceNorm_lowerBlock, ← rectangularLowerBlock_sub] at h
  exact h.trans (add_le_add le_rfl (Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left (hsNormSq_rectangularLowerBlock_le hE) (Nat.cast_nonneg N))))

theorem rectApproxPrefix_soninAllPrimeColumn_le_sourceHeadTail
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) (N : ℕ) :
    (∑ n ∈ Finset.range N, rectApproxNumber (soninAllPrimeColumnOperator a ha) n) ≤
      4 * traceNorm SoninL2 (centralSoninProjectionCorrection a) *
        (∑ pk ∈ s, ‖soninLogPrimePowerCoefficient pk‖) +
      Real.sqrt ((N : ℝ) * ((128 * a ^ 2) * ∑' pk : Nat.Primes × ℕ,
        if pk ∈ s then 0 else ‖soninLogPrimePowerCoefficient pk‖ ^ 2)) := by
  have h := rectApproxPrefix_le_traceClassHead_add_hilbertSchmidtTail
    (soninAllPrimeColumnOperator_isHilbertSchmidt a ha)
    (soninAllPrimeColumnFiniteHead_memRectSchattenClass_one a ha s)
    (soninAllPrimeColumnTail_isHilbertSchmidt a ha s) N
  exact h.trans (add_le_add (rectTraceNorm_soninAllPrimeColumnFiniteHead_le_source a ha s)
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
      (hsNormSq_soninAllPrimeColumnTail_le_coefficientTail a ha s) (Nat.cast_nonneg N))))

end
end RHTower

open ContinuousLinearMap
open scoped BigOperators
namespace RHTower
noncomputable section

/-- The literal regularized common-source column has only logarithmic singular-prefix mass.
Every prime-power coefficient is retained; the finite prime box is only a proof decomposition. -/
theorem rectApproxPrefix_soninAllPrimeColumn_le_log
    (a : ℝ) (ha : 0 < a) (N : ℕ) :
    (∑ n ∈ Finset.range N, rectApproxNumber (soninAllPrimeColumnOperator a ha) n) ≤
      8 * traceNorm SoninL2 (centralSoninProjectionCorrection a) *
        (1 + Real.log (N + 1 : ℕ)) + Real.sqrt (512 * a ^ 2) := by
  let M := N + 1
  have hM : 0 < M := Nat.succ_pos N
  have h := rectApproxPrefix_soninAllPrimeColumn_le_sourceHeadTail a ha
    (soninPrimeDepthBox M) N
  have hhead := mul_le_mul_of_nonneg_left
    (sum_norm_soninLogPrimePowerCoefficient_box_le_log M)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (traceNorm_nonneg (centralSoninProjectionCorrection a)))
  have htail := mul_le_mul_of_nonneg_left
    (sum_sq_soninLogPrimePowerCoefficient_boxTail_le M hM)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) (sq_nonneg a))
  have hscale : (N : ℝ) * ((128 * a ^ 2) * (4 / (M : ℝ))) ≤ 512 * a ^ 2 := by
    have hpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
    have hNM : (N : ℝ) ≤ M := by exact_mod_cast Nat.le_succ N
    have hfrac : (N : ℝ) / M ≤ 1 := (div_le_one hpos).mpr hNM
    calc
      _ = (512 * a ^ 2) * ((N : ℝ) / M) := by ring
      _ ≤ (512 * a ^ 2) * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = _ := mul_one _
  have hroot := Real.sqrt_le_sqrt
    ((mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg N)).trans hscale)
  exact h.trans ((add_le_add hhead hroot).trans_eq (by dsimp [M]; ring))

end
end RHTower


open Filter Topology ContinuousLinearMap
open scoped BigOperators
namespace RHTower
noncomputable section

theorem tendsto_rectApproxPrefix_soninAllPrimeColumn_div_logSq
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, rectApproxNumber (soninAllPrimeColumnOperator a ha) n) /
        Real.log ((N : ℝ) + 1) ^ 2) atTop (nhds 0) := by
  let C := 8 * traceNorm SoninL2 (centralSoninProjectionCorrection a)
  let D := Real.sqrt (512 * a ^ 2)
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hq : Tendsto (fun N : ℕ => 1 / Real.log ((N : ℝ) + 1)) atTop (nhds 0) :=
    hlog.const_div_atTop 1
  have hzero : Tendsto (fun N : ℕ =>
      (C + D) * (1 / Real.log ((N : ℝ) + 1)) ^ 2 +
        C * (1 / Real.log ((N : ℝ) + 1))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (hq.pow 2)).add (tendsto_const_nhds.mul hq)
  apply squeeze_zero_norm' _ hzero
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hL : 0 < Real.log ((N : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast Nat.succ_lt_succ hN)
  have hsum : 0 ≤ ∑ n ∈ Finset.range N,
      rectApproxNumber (soninAllPrimeColumnOperator a ha) n :=
    Finset.sum_nonneg fun n _ => rectApproxNumber_nonneg _ n
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hsum (sq_nonneg _))]
  have hbound := rectApproxPrefix_soninAllPrimeColumn_le_log a ha N
  simp only [Nat.cast_add, Nat.cast_one] at hbound
  refine (div_le_div_of_nonneg_right hbound (sq_nonneg _)).trans_eq ?_
  dsimp [C, D]
  field_simp
  ring

end
end RHTower

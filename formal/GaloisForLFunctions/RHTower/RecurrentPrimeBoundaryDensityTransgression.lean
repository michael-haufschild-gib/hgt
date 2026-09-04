import GaloisForLFunctions.RHTower.ThetaSurvivalRelativeCurvaturePrimeLift
import GaloisForLFunctions.HTGeometry.LpInjectionCompression
import GaloisForLFunctions.RHTower.XiOrderedPrimeDeterminantNormalForm
import GaloisForLFunctions.RHTower.ZetaRealBound
import GaloisForLFunctions.HTGeometry.TraceClassQuantumCorner
import GaloisForLFunctions.RHTower.PositiveOperatorKernel
import GaloisForLFunctions.HTGeometry.FiniteDimensionalOperatorAlbertiLaw
import GaloisForLFunctions.HTGeometry.FiniteExponentialHankel

open scoped BigOperators ComplexConjugate InnerProductSpace
open ContinuousLinearMap Filter Topology

namespace RHTower

noncomputable section

def historyShiftIndex (np : PrimeHodgeHistoryIndex) : PrimeHodgeHistoryIndex :=
  (np.1 + 1, np.2)

theorem historyShiftIndex_injective : Function.Injective historyShiftIndex := by
  intro ⟨n, p⟩ ⟨m, q⟩ h
  simp only [historyShiftIndex, Prod.mk.injEq] at h ⊢
  exact ⟨Nat.succ.inj (by simpa only [Nat.succ_eq_add_one] using h.1), h.2⟩

def historyShift : PrimeHodgeHistoryHilbert →ₗᵢ[ℂ] PrimeHodgeHistoryHilbert :=
  lpScalarInjection historyShiftIndex historyShiftIndex_injective

def historyShiftCLM : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  historyShift.toContinuousLinearMap

def historyGradeIndex (n : ℕ) (p : Nat.Primes) : PrimeHodgeHistoryIndex := (n, p)

theorem historyGradeIndex_injective (n : ℕ) : Function.Injective (historyGradeIndex n) := by
  intro p q h
  exact congrArg Prod.snd h

def historyGradeEmbedding (n : ℕ) :
    lp (fun _ : Nat.Primes => ℂ) 2 →ₗᵢ[ℂ] PrimeHodgeHistoryHilbert :=
  lpScalarInjection (historyGradeIndex n) (historyGradeIndex_injective n)

def historyGradeEmbeddingCLM (n : ℕ) :
    lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] PrimeHodgeHistoryHilbert :=
  (historyGradeEmbedding n).toContinuousLinearMap

theorem historyShift_gradeEmbedding (n : ℕ) :
    historyShiftCLM ∘L historyGradeEmbeddingCLM n = historyGradeEmbeddingCLM (n + 1) := by
  apply continuousLinearMap_eq_of_eq_on_hilbertBasis (HilbertSchmidt.lpBasis Nat.Primes)
  intro p
  simp only [ContinuousLinearMap.comp_apply, historyShiftCLM, historyGradeEmbeddingCLM]
  change historyShift (historyGradeEmbedding n (HilbertSchmidt.lpBasis Nat.Primes p)) =
    historyGradeEmbedding (n + 1) (HilbertSchmidt.lpBasis Nat.Primes p)
  simp only [historyShift, historyGradeEmbedding]
  rw [HilbertSchmidt.lpBasis_apply, lpScalarInjection_single,
    lpScalarInjection_single, lpScalarInjection_single]
  rfl

theorem adjoint_historyGradeEmbeddingCLM (n : ℕ) :
    adjoint (historyGradeEmbeddingCLM n) =
      lpCoordinatePullback (E := ℂ) (historyGradeIndex n) (historyGradeIndex_injective n) := by
  exact (lpCoordinatePullback_eq_adjoint_lpScalarInjection
    (historyGradeIndex n) (historyGradeIndex_injective n)).symm

theorem historyGradeCompression_succ (T : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (n : ℕ) :
    (adjoint (historyGradeEmbeddingCLM (n + 1)) ∘L T) ∘L historyGradeEmbeddingCLM (n + 1) =
      (adjoint (historyGradeEmbeddingCLM n) ∘L
        ((adjoint historyShiftCLM ∘L T) ∘L historyShiftCLM)) ∘L
          historyGradeEmbeddingCLM n := by
  rw [← historyShift_gradeEmbedding n]
  simp only [ContinuousLinearMap.adjoint_comp]
  rfl

theorem historyShift_slice_succ (x : PrimeHodgeHistoryHilbert) (n : ℕ) :
    historyPrimeSlice (historyShiftCLM x) (n + 1) = historyPrimeSlice x n := by
  ext p
  change historyShift x (n + 1, p) = x (n, p)
  change lpScalarInjection historyShiftIndex historyShiftIndex_injective x
      (historyShiftIndex (n, p)) = x (n, p)
  exact lpScalarInjection_coordinate historyShiftIndex historyShiftIndex_injective x (n, p)

theorem adjoint_historyShiftCLM :
    adjoint historyShiftCLM =
      lpCoordinatePullback (E := ℂ) historyShiftIndex historyShiftIndex_injective := by
  exact (lpCoordinatePullback_eq_adjoint_lpScalarInjection
    historyShiftIndex historyShiftIndex_injective).symm

theorem historyShift_conjugate_historyStokesOperator
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ha2 : Summable fun n => a n ^ 2) {d : ℝ} (hd : 0 < d) :
    (adjoint historyShiftCLM ∘L historyStokesOperator a ha ha2 hd) ∘L historyShiftCLM =
      historyStokesOperator (fun n => a (n + 1)) (fun n => ha (n + 1))
        (ha2.comp_injective Nat.succ_injective) hd := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext np
  rcases np with ⟨n, p⟩
  simp only [ContinuousLinearMap.comp_apply]
  rw [adjoint_historyShiftCLM, lpCoordinatePullback_apply]
  change historyStokesOperator a ha ha2 hd (historyShiftCLM x) (n + 1, p) = _
  rw [historyStokesOperator_apply_coordinate,
    historyStokesOperator_apply_coordinate, historyShift_slice_succ]

end
end RHTower

namespace PrimeHodgeHistory

noncomputable section

theorem m_nonneg (n : ℕ) : 0 ≤ m n := (m_pos n).le

theorem m_le_shifted_square (n : ℕ) :
    m n ≤ 105 * (1 / ((n : ℝ) + 1) ^ (2 : ℕ)) := by
  rw [m]
  push_cast
  have hden : ((n : ℝ) + 1) ^ (2 : ℕ) ≤
      ((2 : ℝ) * n + 3) * ((2 : ℝ) * n + 5) * ((2 : ℝ) * n + 7) := by
    have hpair : ((n : ℝ) + 1) ^ (2 : ℕ) ≤
        ((2 : ℝ) * n + 3) * ((2 : ℝ) * n + 5) := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have hlast : (1 : ℝ) ≤ (2 : ℝ) * n + 7 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    calc
      ((n : ℝ) + 1) ^ (2 : ℕ) = ((n : ℝ) + 1) ^ (2 : ℕ) * 1 := by ring
      _ ≤ (((2 : ℝ) * n + 3) * ((2 : ℝ) * n + 5)) * ((2 : ℝ) * n + 7) :=
        mul_le_mul hpair hlast (by positivity) (by positivity)
  calc
    105 / (((2 : ℝ) * n + 3) * ((2 : ℝ) * n + 5) * ((2 : ℝ) * n + 7)) ≤
        105 / (((n : ℝ) + 1) ^ (2 : ℕ)) := by
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ = 105 * (1 / ((n : ℝ) + 1) ^ (2 : ℕ)) := by ring

theorem summable_m : Summable m := by
  have hbase : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (2 : ℝ) :=
    GaloisForLFunctions.RHTower.summable_one_div_nat_add_one_rpow (by norm_num)
  have hmajor : Summable fun n : ℕ => 105 * (1 / ((n : ℝ) + 1) ^ (2 : ℕ)) := by
    refine hbase.mul_left 105 |>.congr (fun n => ?_)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact Summable.of_nonneg_of_le m_nonneg m_le_shifted_square hmajor

theorem m_le_105 (n : ℕ) : m n ≤ 105 := by
  calc
    m n ≤ 105 * (1 / ((n : ℝ) + 1) ^ (2 : ℕ)) := m_le_shifted_square n
    _ ≤ 105 * 1 := by
      gcongr
      rw [div_le_iff₀ (by positivity)]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    _ = 105 := by ring

theorem summable_sq_m : Summable fun n => m n ^ 2 := by
  exact Summable.of_nonneg_of_le (fun n => sq_nonneg (m n))
    (fun n => by nlinarith [m_nonneg n, m_le_105 n]) (summable_m.mul_left 105)

theorem summable_sq_w : Summable fun n => w n ^ 2 := by
  exact Summable.of_nonneg_of_le (fun n => sq_nonneg (w n))
    (fun n => by nlinarith [w_pos n, w_le_two_thirds n])
    (summable_w.mul_left (2 / 3 : ℝ))

end
end PrimeHodgeHistory

namespace RHTower

open ContinuousLinearMap

noncomputable section

/-- Literal minimal first-exit completion `diag(m) ⊗ A_d`. -/
def recurrentPrimeMinimalCompletion {d : ℝ} (hd : 0 < d) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  historyStokesOperator PrimeHodgeHistory.m PrimeHodgeHistory.m_nonneg
    PrimeHodgeHistory.summable_sq_m hd

theorem recurrentPrimeMinimalCompletion_isPositive {d : ℝ} (hd : 0 < d) :
    (recurrentPrimeMinimalCompletion hd).IsPositive :=
  historyStokesOperator_isPositive PrimeHodgeHistory.m PrimeHodgeHistory.m_nonneg
    PrimeHodgeHistory.summable_sq_m hd

theorem recurrentPrimeMinimalCompletion_memSchattenClass_one {d : ℝ} (hd : 0 < d) :
    MemSchattenClass 1 (recurrentPrimeMinimalCompletion hd) :=
  historyStokesOperator_memSchattenClass_one PrimeHodgeHistory.m
    PrimeHodgeHistory.m_nonneg PrimeHodgeHistory.summable_m
    PrimeHodgeHistory.summable_sq_m hd

theorem primeHodgeHistoryDefectOperator_eq_historyStokesOperator {d : ℝ} (hd : 0 < d) :
    primeHodgeHistoryDefectOperator hd =
      historyStokesOperator PrimeHodgeHistory.w
        (fun n => (PrimeHodgeHistory.w_pos n).le)
        PrimeHodgeHistory.summable_sq_w hd := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext np
  change (HilbertSchmidt.toOperator (primeHodgeHistoryDefectKernel_isHS hd) x) np = _
  rw [HilbertSchmidt.toOperator_apply, historyStokesOperator]
  rw [HilbertSchmidt.toOperator_apply]
  apply tsum_congr
  intro mq
  rfl

theorem recurrentPrimeMinimalCompletion_displacement {d : ℝ} (hd : 0 < d) :
    recurrentPrimeMinimalCompletion hd -
      ((adjoint historyShiftCLM ∘L recurrentPrimeMinimalCompletion hd) ∘L historyShiftCLM) =
        primeHodgeHistoryDefectOperator hd := by
  simp only [recurrentPrimeMinimalCompletion]
  rw [historyShift_conjugate_historyStokesOperator]
  rw [primeHodgeHistoryDefectOperator_eq_historyStokesOperator]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext np
  rcases np with ⟨n, p⟩
  change
    historyStokesOperator PrimeHodgeHistory.m PrimeHodgeHistory.m_nonneg
        PrimeHodgeHistory.summable_sq_m hd x (n, p) -
      historyStokesOperator (fun k => PrimeHodgeHistory.m (k + 1)) _ _ hd x (n, p) =
        historyStokesOperator PrimeHodgeHistory.w _ _ hd x (n, p)
  rw [historyStokesOperator_apply_coordinate,
    historyStokesOperator_apply_coordinate, historyStokesOperator_apply_coordinate]
  rw [PrimeHodgeHistory.w]
  push_cast
  ring

def recurrentHistoryConjugate
    (T : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  (adjoint historyShiftCLM ∘L T) ∘L historyShiftCLM

theorem recurrentHistoryConjugate_sub
    (S T : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert) :
    recurrentHistoryConjugate (S - T) =
      recurrentHistoryConjugate S - recurrentHistoryConjugate T := by
  ext x
  simp [recurrentHistoryConjugate, ContinuousLinearMap.comp_apply]

theorem recurrentHistoryConjugate_isPositive
    {T : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert}
    (hT : T.IsPositive) : (recurrentHistoryConjugate T).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff] at hT
  have hnonneg : 0 ≤ T := by
    rw [ContinuousLinearMap.le_def, sub_zero,
      ContinuousLinearMap.isPositive_iff]
    exact hT
  have hs := GaloisForLFunctions.HTGeometry.traceClassSandwich_nonneg
    (adjoint historyShiftCLM) T hnonneg
  rw [ContinuousLinearMap.le_def, sub_zero,
    ContinuousLinearMap.isPositive_iff] at hs
  rw [ContinuousLinearMap.isPositive_iff]
  simpa only [recurrentHistoryConjugate, adjoint_adjoint] using hs

def recurrentPrimeTailCompletion {d : ℝ} (hd : 0 < d) (j : ℕ) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  historyStokesOperator (fun n => PrimeHodgeHistory.m (n + j))
    (fun n => PrimeHodgeHistory.m_nonneg (n + j))
    (PrimeHodgeHistory.summable_sq_m.comp_injective (fun _ _ h => Nat.add_right_cancel h)) hd

theorem recurrentPrimeTailCompletion_zero {d : ℝ} (hd : 0 < d) :
    recurrentPrimeTailCompletion hd 0 = recurrentPrimeMinimalCompletion hd := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext np
  rcases np with ⟨n, p⟩
  rw [recurrentPrimeTailCompletion, recurrentPrimeMinimalCompletion,
    historyStokesOperator_apply_coordinate, historyStokesOperator_apply_coordinate]
  simp

theorem recurrentHistoryConjugate_tail {d : ℝ} (hd : 0 < d) (j : ℕ) :
    recurrentHistoryConjugate (recurrentPrimeTailCompletion hd j) =
      recurrentPrimeTailCompletion hd (j + 1) := by
  rw [recurrentHistoryConjugate]
  simp only [recurrentPrimeTailCompletion]
  rw [historyShift_conjugate_historyStokesOperator]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext np
  rcases np with ⟨n, p⟩
  rw [historyStokesOperator_apply_coordinate, historyStokesOperator_apply_coordinate]
  congr 3
  omega

theorem recurrentHistoryConjugate_iterate_minimal {d : ℝ} (hd : 0 < d) (j : ℕ) :
    (recurrentHistoryConjugate^[j]) (recurrentPrimeMinimalCompletion hd) =
      recurrentPrimeTailCompletion hd j := by
  induction j with
  | zero =>
      simp only [Function.iterate_zero, id_eq]
      exact (recurrentPrimeTailCompletion_zero hd).symm
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, recurrentHistoryConjugate_tail]

theorem recurrentPrimeTailCompletion_norm_le {d : ℝ} (hd : 0 < d) (j : ℕ) :
    ‖recurrentPrimeTailCompletion hd j‖ ≤ PrimeHodgeHistory.m j := by
  apply norm_historyStokesOperator_le
  · exact PrimeHodgeHistory.m_nonneg j
  · intro n
    exact PrimeHodgeHistory.m_antitone (by omega)

theorem recurrentPrimeTailCompletion_tendsto_zero {d : ℝ} (hd : 0 < d) :
    Tendsto (fun j => recurrentPrimeTailCompletion hd j) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hm := (Metric.tendsto_atTop.1 PrimeHodgeHistory.m_tendsto_zero) ε hε
  obtain ⟨N, hN⟩ := hm
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  exact lt_of_le_of_lt (recurrentPrimeTailCompletion_norm_le hd n) (by
    have := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_pos (PrimeHodgeHistory.m_pos n)] at this)

theorem recurrentHistoryConjugate_iterate_sub
    (S T : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert) (j : ℕ) :
    (recurrentHistoryConjugate^[j]) (S - T) =
      (recurrentHistoryConjugate^[j]) S - (recurrentHistoryConjugate^[j]) T := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, recurrentHistoryConjugate_sub]

theorem recurrentHistoryConjugate_iterate_fixed
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (hR : recurrentHistoryConjugate R = R) (j : ℕ) :
    (recurrentHistoryConjugate^[j]) R = R := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, hR]

theorem recurrentHistoryConjugate_iterate_isPositive
    {T : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert}
    (hT : T.IsPositive) (j : ℕ) :
    ((recurrentHistoryConjugate^[j]) T).IsPositive := by
  induction j with
  | zero => exact hT
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact recurrentHistoryConjugate_isPositive ih

/-- Positive bounded completions carrying the literal prime--Hodge defect. -/
structure RecurrentPrimePositiveCompletion (a : {d : ℝ // 0 < d}) where
  operator : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert
  positive : operator.IsPositive
  displacement : operator - recurrentHistoryConjugate operator =
    primeHodgeHistoryDefectOperator a.property

def RecurrentPrimePositiveCompletion.remainder
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimePositiveCompletion a) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  X.operator - recurrentPrimeMinimalCompletion a.property

theorem RecurrentPrimePositiveCompletion.remainder_fixed
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimePositiveCompletion a) :
    recurrentHistoryConjugate X.remainder = X.remainder := by
  rw [RecurrentPrimePositiveCompletion.remainder, recurrentHistoryConjugate_sub]
  have hG := recurrentPrimeMinimalCompletion_displacement a.property
  change recurrentPrimeMinimalCompletion a.property -
      recurrentHistoryConjugate (recurrentPrimeMinimalCompletion a.property) =
        primeHodgeHistoryDefectOperator a.property at hG
  have hXconj : recurrentHistoryConjugate X.operator =
      X.operator - primeHodgeHistoryDefectOperator a.property := by
    apply eq_sub_iff_add_eq.mpr
    rw [← X.displacement]
    abel
  have hGconj : recurrentHistoryConjugate (recurrentPrimeMinimalCompletion a.property) =
      recurrentPrimeMinimalCompletion a.property -
        primeHodgeHistoryDefectOperator a.property := by
    apply eq_sub_iff_add_eq.mpr
    rw [← hG]
    abel
  rw [hXconj, hGconj]
  abel

theorem RecurrentPrimePositiveCompletion.iterate_operator_tendsto_remainder
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimePositiveCompletion a) :
    Tendsto (fun j => (recurrentHistoryConjugate^[j]) X.operator) atTop
      (nhds X.remainder) := by
  have hEq (j : ℕ) :
      (recurrentHistoryConjugate^[j]) X.operator =
        X.remainder + recurrentPrimeTailCompletion a.property j := by
    have hsub := recurrentHistoryConjugate_iterate_sub X.operator
      (recurrentPrimeMinimalCompletion a.property) j
    rw [← RecurrentPrimePositiveCompletion.remainder,
      recurrentHistoryConjugate_iterate_fixed X.remainder X.remainder_fixed j,
      recurrentHistoryConjugate_iterate_minimal] at hsub
    rw [eq_sub_iff_add_eq] at hsub
    exact hsub.symm
  have hconst : Tendsto
      (fun _ : ℕ => X.remainder) atTop (nhds X.remainder) := tendsto_const_nhds
  have hsum := hconst.add
    (recurrentPrimeTailCompletion_tendsto_zero a.property)
  have hfun : (fun j => (recurrentHistoryConjugate^[j]) X.operator) =
      fun j => X.remainder + recurrentPrimeTailCompletion a.property j := funext hEq
  rw [hfun]
  simpa using hsum

theorem RecurrentPrimePositiveCompletion.remainder_isPositive
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimePositiveCompletion a) :
    X.remainder.IsPositive := by
  constructor
  · exact X.positive.1.sub (recurrentPrimeMinimalCompletion_isPositive a.property).1
  · intro x
    have hop := X.iterate_operator_tendsto_remainder
    have happ : Tendsto
        (fun j => ((recurrentHistoryConjugate^[j]) X.operator) x) atTop
        (nhds (X.remainder x)) :=
      Filter.Tendsto.comp
        (ContinuousLinearMap.apply ℂ PrimeHodgeHistoryHilbert x).continuous.continuousAt hop
    have hinner : Tendsto
        (fun j => inner ℂ (((recurrentHistoryConjugate^[j]) X.operator) x) x) atTop
        (nhds (inner ℂ (X.remainder x) x)) :=
      Filter.Tendsto.inner happ tendsto_const_nhds
    have hre : Tendsto
        (fun j => (inner ℂ (((recurrentHistoryConjugate^[j]) X.operator) x) x).re) atTop
        (nhds (inner ℂ (X.remainder x) x).re) :=
      Filter.Tendsto.comp Complex.continuous_re.continuousAt hinner
    change 0 ≤ (inner ℂ (X.remainder x) x).re
    apply isClosed_Ici.mem_of_tendsto hre
    filter_upwards with j
    have hj := (recurrentHistoryConjugate_iterate_isPositive X.positive j).2 x
    simpa [ContinuousLinearMap.reApplyInnerSelf] using hj

theorem RecurrentPrimePositiveCompletion.minimal_plus_recurrent
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimePositiveCompletion a) :
    X.operator = recurrentPrimeMinimalCompletion a.property + X.remainder ∧
      X.remainder.IsPositive ∧ recurrentHistoryConjugate X.remainder = X.remainder := by
  refine ⟨?_, X.remainder_isPositive, X.remainder_fixed⟩
  rw [RecurrentPrimePositiveCompletion.remainder]
  abel

theorem RecurrentPrimePositiveCompletion.remainder_unique
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimePositiveCompletion a)
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (hXR : X.operator = recurrentPrimeMinimalCompletion a.property + R) :
    R = X.remainder := by
  rw [RecurrentPrimePositiveCompletion.remainder]
  rw [hXR]
  abel

def recurrentGradeCompression
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert) (n : ℕ) :
    lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] lp (fun _ : Nat.Primes => ℂ) 2 :=
  (adjoint (historyGradeEmbeddingCLM n) ∘L R) ∘L historyGradeEmbeddingCLM n

theorem recurrentGradeCompression_succ
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (hR : (adjoint historyShiftCLM ∘L R) ∘L historyShiftCLM = R) (n : ℕ) :
    recurrentGradeCompression R (n + 1) = recurrentGradeCompression R n := by
  rw [recurrentGradeCompression, recurrentGradeCompression,
    historyGradeCompression_succ, hR]

theorem recurrentGradeCompression_eq_zero
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (hR : (adjoint historyShiftCLM ∘L R) ∘L historyShiftCLM = R) (n : ℕ) :
    recurrentGradeCompression R n = recurrentGradeCompression R 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [recurrentGradeCompression_succ R hR n]
      exact ih

def recurrentFinitePrimeMass
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (F : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ F, (inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
    (recurrentGradeCompression R 0 (HilbertSchmidt.lpBasis Nat.Primes p))).re

def recurrentFiniteCompressionTrace
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (N : ℕ) (F : Finset Nat.Primes) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ p ∈ F,
    (inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
      (recurrentGradeCompression R n (HilbertSchmidt.lpBasis Nat.Primes p))).re

theorem recurrentFiniteCompressionTrace_eq
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (hR : (adjoint historyShiftCLM ∘L R) ∘L historyShiftCLM = R)
    (N : ℕ) (F : Finset Nat.Primes) :
    recurrentFiniteCompressionTrace R N F = N * recurrentFinitePrimeMass R F := by
  simp only [recurrentFiniteCompressionTrace, recurrentFinitePrimeMass,
    recurrentGradeCompression_eq_zero R hR]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem historyGradeEmbedding_basis (n : ℕ) (p : Nat.Primes) :
    historyGradeEmbeddingCLM n (HilbertSchmidt.lpBasis Nat.Primes p) =
      HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p) := by
  change historyGradeEmbedding n (HilbertSchmidt.lpBasis Nat.Primes p) = _
  simp only [historyGradeEmbedding]
  rw [HilbertSchmidt.lpBasis_apply, lpScalarInjection_single,
    HilbertSchmidt.lpBasis_apply]
  rfl

theorem inner_basis_recurrentGradeCompression
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (n : ℕ) (p : Nat.Primes) :
    inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
        (recurrentGradeCompression R n (HilbertSchmidt.lpBasis Nat.Primes p)) =
      inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
        (R (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))) := by
  rw [recurrentGradeCompression]
  simp only [ContinuousLinearMap.comp_apply]
  rw [adjoint_inner_right, historyGradeEmbedding_basis]

def recurrentPrimeClock (p : Nat.Primes) : ℝ := Real.log p.1

theorem recurrentPrimeClock_pos (p : Nat.Primes) : 0 < recurrentPrimeClock p := by
  rw [recurrentPrimeClock]
  apply Real.log_pos
  exact_mod_cast p.2.one_lt

def recurrentPrimeSourceMass (a : {d : ℝ // 0 < d}) (p : Nat.Primes) : ℝ :=
  routePPrimitiveGammaJuliaStokesTransportedPrimeWeight a.1 p /
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent a.1

def recurrentPrimeSourceCubic (a : {d : ℝ // 0 < d}) (p : Nat.Primes) : ℝ :=
  8 * recurrentPrimeClock p ^ 3 * recurrentPrimeSourceMass a p

def recurrentPrimeBoundaryCoefficient
    (X : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (p : Nat.Primes) : ℝ :=
  8 * recurrentPrimeClock p ^ 3 *
    (inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (0, p))
      (X (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (0, p)))).re

theorem inner_basis_recurrentPrimeMinimalCompletion
    (a : {d : ℝ // 0 < d}) (p : Nat.Primes) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (0, p))
      (recurrentPrimeMinimalCompletion a.property
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (0, p))) =
      (recurrentPrimeSourceMass a p : ℂ) := by
  rw [recurrentPrimeMinimalCompletion,
    inner_lpBasis_historyStokesOperator]
  simp [historyStokesDiagonalWeight, recurrentPrimeSourceMass,
    PrimeHodgeHistory.m_zero]

theorem recurrentPrimeMinimalCompletion_boundaryCoefficient
    (a : {d : ℝ // 0 < d}) (p : Nat.Primes) :
    recurrentPrimeBoundaryCoefficient (recurrentPrimeMinimalCompletion a.property) p =
      recurrentPrimeSourceCubic a p := by
  rw [recurrentPrimeBoundaryCoefficient, recurrentPrimeSourceCubic,
    inner_basis_recurrentPrimeMinimalCompletion]
  simp

def recurrentPrimeBoundaryExcessTerm
    (a : {d : ℝ // 0 < d})
    (X : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (p : Nat.Primes) : ℝ :=
  (recurrentPrimeBoundaryCoefficient X p - recurrentPrimeSourceCubic a p) /
    (8 * recurrentPrimeClock p ^ 3)

theorem RecurrentPrimePositiveCompletion.boundaryExcessTerm_eq_diagonal
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimePositiveCompletion a)
    (p : Nat.Primes) :
    recurrentPrimeBoundaryExcessTerm a X.operator p =
      (inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (0, p))
        (X.remainder (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (0, p)))).re := by
  have hdecomp := X.minimal_plus_recurrent.1
  rw [hdecomp]
  simp only [recurrentPrimeBoundaryExcessTerm, recurrentPrimeBoundaryCoefficient,
    add_apply, inner_add_right, Complex.add_re,
    recurrentPrimeSourceCubic, inner_basis_recurrentPrimeMinimalCompletion,
    Complex.ofReal_re]
  field_simp [(recurrentPrimeClock_pos p).ne']
  ring

def recurrentFiniteBoundaryExcess
    (a : {d : ℝ // 0 < d})
    (X : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (F : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ F, recurrentPrimeBoundaryExcessTerm a X p

theorem RecurrentPrimePositiveCompletion.finiteBoundaryExcess_eq_mass
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimePositiveCompletion a)
    (F : Finset Nat.Primes) :
    recurrentFiniteBoundaryExcess a X.operator F =
      recurrentFinitePrimeMass X.remainder F := by
  simp only [recurrentFiniteBoundaryExcess, recurrentFinitePrimeMass]
  apply Finset.sum_congr rfl
  intro p hp
  rw [RecurrentPrimePositiveCompletion.boundaryExcessTerm_eq_diagonal,
    inner_basis_recurrentGradeCompression]

theorem recurrentFinitePrimeMass_nonneg
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (hR : R.IsPositive) (F : Finset Nat.Primes) :
    0 ≤ recurrentFinitePrimeMass R F := by
  simp only [recurrentFinitePrimeMass]
  apply Finset.sum_nonneg
  intro p hp
  rw [inner_basis_recurrentGradeCompression]
  let e := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (0, p)
  change 0 ≤ (inner ℂ e (R e)).re
  have heq : inner ℂ e (R e) = inner ℂ (R e) e :=
    (hR.inner_left_eq_inner_right e e).symm
  rw [heq]
  exact hR.re_inner_nonneg_left e

theorem RecurrentPrimePositiveCompletion.finiteBoundaryExcess_nonneg
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimePositiveCompletion a)
    (F : Finset Nat.Primes) :
    0 ≤ recurrentFiniteBoundaryExcess a X.operator F := by
  rw [X.finiteBoundaryExcess_eq_mass]
  exact recurrentFinitePrimeMass_nonneg X.remainder X.remainder_isPositive F

theorem RecurrentPrimePositiveCompletion.finiteCompressionTrace_eq_boundaryExcess
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimePositiveCompletion a)
    (N : ℕ) (F : Finset Nat.Primes) :
    recurrentFiniteCompressionTrace X.remainder N F =
      N * recurrentFiniteBoundaryExcess a X.operator F := by
  rw [X.finiteBoundaryExcess_eq_mass]
  exact recurrentFiniteCompressionTrace_eq X.remainder X.remainder_fixed N F

theorem recurrentGradeCompression_isPositive
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (hR : R.IsPositive) (n : ℕ) : (recurrentGradeCompression R n).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff] at hR
  have hnonneg : 0 ≤ R := by
    rw [ContinuousLinearMap.le_def, sub_zero, ContinuousLinearMap.isPositive_iff]
    exact hR
  have hs := GaloisForLFunctions.HTGeometry.traceClassSandwich_nonneg
    (adjoint (historyGradeEmbeddingCLM n)) R hnonneg
  rw [ContinuousLinearMap.le_def, sub_zero,
    ContinuousLinearMap.isPositive_iff] at hs
  rw [ContinuousLinearMap.isPositive_iff]
  simpa only [recurrentGradeCompression, adjoint_adjoint] using hs

def recurrentHistoryMass
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert) : ℝ :=
  ∑' p : Nat.Primes,
    (inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
      (recurrentGradeCompression R 0 (HilbertSchmidt.lpBasis Nat.Primes p))).re

def recurrentTotalBoundaryExcess
    (a : {d : ℝ // 0 < d})
    (X : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert) : ℝ :=
  ∑' p : Nat.Primes, recurrentPrimeBoundaryExcessTerm a X p

theorem RecurrentPrimePositiveCompletion.totalBoundaryExcess_eq_historyMass
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimePositiveCompletion a) :
    recurrentTotalBoundaryExcess a X.operator = recurrentHistoryMass X.remainder := by
  apply tsum_congr
  intro p
  rw [X.boundaryExcessTerm_eq_diagonal,
    inner_basis_recurrentGradeCompression]

theorem recurrentHistoryMass_eq_re_opTrace
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (hR : R.IsPositive)
    (htrace : MemSchattenClass 1 (recurrentGradeCompression R 0)) :
    recurrentHistoryMass R =
      (ContinuousLinearMap.opTrace (recurrentGradeCompression R 0)).re := by
  let b := HilbertSchmidt.lpBasis Nat.Primes
  have hnorm := htrace.one_summable_norm_inner_diag_basis b
  have hsum : Summable fun p => inner ℂ (b p) (recurrentGradeCompression R 0 (b p)) :=
    hnorm.of_norm
  have htraceEq := opTrace_eq_tsum_basis_of_isPositive_of_summable_diagonal b
    (recurrentGradeCompression_isPositive R hR 0) hsum
  let reHom : ℂ →+ ℝ :=
    { toFun := Complex.re
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hreSum := hsum.hasSum.map reHom (by
    simpa [reHom] using Complex.continuous_re)
  rw [htraceEq]
  simpa [recurrentHistoryMass, b, reHom] using hreSum.tsum_eq

theorem RecurrentPrimePositiveCompletion.totalBoundaryExcess_eq_re_opTrace
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimePositiveCompletion a)
    (htrace : MemSchattenClass 1 (recurrentGradeCompression X.remainder 0)) :
    recurrentTotalBoundaryExcess a X.operator =
      (ContinuousLinearMap.opTrace (recurrentGradeCompression X.remainder 0)).re := by
  rw [X.totalBoundaryExcess_eq_historyMass]
  exact recurrentHistoryMass_eq_re_opTrace X.remainder X.remainder_isPositive htrace

/-- A nonnegative summable family has its total sum as the exact least upper bound of all finite
partial sums.  This packages the cofinal finite-compression statement without selecting an
enumeration of the index type. -/
theorem isLUB_finsetSums_of_summable_nonneg {ι : Type*} [DecidableEq ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hsum : Summable f) :
    IsLUB (Set.range fun F : Finset ι => ∑ i ∈ F, f i) (∑' i, f i) := by
  constructor
  · rintro _ ⟨F, rfl⟩
    exact hsum.sum_le_tsum F (fun i _ => hf i)
  · intro b hb
    by_contra hnot
    rw [not_le] at hnot
    have heventually : ∀ᶠ F : Finset ι in atTop, b < ∑ i ∈ F, f i :=
      (tendsto_order.1 hsum.hasSum).1 b hnot
    obtain ⟨F, hF⟩ := heventually.exists
    exact (not_lt_of_ge (hb ⟨F, rfl⟩)) hF

/-- Exact monotone finite-prime approximation of the trace per history cell. -/
theorem RecurrentPrimePositiveCompletion.isLUB_finiteBoundaryExcess
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimePositiveCompletion a)
    (htrace : MemSchattenClass 1 (recurrentGradeCompression X.remainder 0)) :
    IsLUB
      (Set.range fun F : Finset Nat.Primes =>
        recurrentFiniteBoundaryExcess a X.operator F)
      (recurrentTotalBoundaryExcess a X.operator) := by
  let b := HilbertSchmidt.lpBasis Nat.Primes
  have hnorm := htrace.one_summable_norm_inner_diag_basis b
  have hcomplex : Summable fun p =>
      inner ℂ (b p) (recurrentGradeCompression X.remainder 0 (b p)) :=
    hnorm.of_norm
  let reHom : ℂ →+ ℝ :=
    { toFun := Complex.re
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hreal : Summable fun p =>
      (inner ℂ (b p) (recurrentGradeCompression X.remainder 0 (b p))).re :=
    (hcomplex.hasSum.map reHom (by
      simpa [reHom] using Complex.continuous_re)).summable
  have hterm (p : Nat.Primes) :
      recurrentPrimeBoundaryExcessTerm a X.operator p =
        (inner ℂ (b p) (recurrentGradeCompression X.remainder 0 (b p))).re := by
    rw [X.boundaryExcessTerm_eq_diagonal,
      inner_basis_recurrentGradeCompression]
  have hsum : Summable fun p => recurrentPrimeBoundaryExcessTerm a X.operator p :=
    hreal.congr (fun p => (hterm p).symm)
  have hnonneg (p : Nat.Primes) :
      0 ≤ recurrentPrimeBoundaryExcessTerm a X.operator p := by
    rw [hterm]
    have hp := recurrentGradeCompression_isPositive X.remainder
      X.remainder_isPositive 0
    have heq : inner ℂ (b p) (recurrentGradeCompression X.remainder 0 (b p)) =
        inner ℂ (recurrentGradeCompression X.remainder 0 (b p)) (b p) :=
      (hp.inner_left_eq_inner_right (b p) (b p)).symm
    rw [heq]
    exact hp.re_inner_nonneg_left (b p)
  simpa only [recurrentFiniteBoundaryExcess, recurrentTotalBoundaryExcess] using
    isLUB_finsetSums_of_summable_nonneg
      (fun p => recurrentPrimeBoundaryExcessTerm a X.operator p) hnonneg hsum

/-- A completion whose literal cubic prime coefficients equal the source coefficients. -/
structure RecurrentPrimeSourceFaithfulCompletion (a : {d : ℝ // 0 < d})
    extends RecurrentPrimePositiveCompletion a where
  source_faithful : ∀ p : Nat.Primes,
    recurrentPrimeBoundaryCoefficient operator p = recurrentPrimeSourceCubic a p

theorem RecurrentPrimeSourceFaithfulCompletion.remainder_eq_zero
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimeSourceFaithfulCompletion a) :
    X.toRecurrentPrimePositiveCompletion.remainder = 0 := by
  let Y := X.toRecurrentPrimePositiveCompletion
  let R := Y.remainder
  have hR : R.IsPositive := Y.remainder_isPositive
  have hfixed : recurrentHistoryConjugate R = R := Y.remainder_fixed
  apply continuousLinearMap_eq_of_eq_on_hilbertBasis
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex) R 0
  intro np
  rcases np with ⟨n, p⟩
  let e := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p)
  apply hR.apply_eq_zero_of_inner_eq_zero
  have hre : (inner ℂ e (R e)).re = 0 := by
    change (inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
      (R (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p)))).re = 0
    rw [← inner_basis_recurrentGradeCompression]
    rw [recurrentGradeCompression_eq_zero R hfixed n]
    rw [inner_basis_recurrentGradeCompression]
    change (inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (0, p))
      (Y.remainder (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (0, p)))).re = 0
    rw [← Y.boundaryExcessTerm_eq_diagonal]
    unfold recurrentPrimeBoundaryExcessTerm
    rw [show recurrentPrimeBoundaryCoefficient Y.operator p =
      recurrentPrimeSourceCubic a p by exact X.source_faithful p]
    simp
  have hsym : inner ℂ (R e) e = inner ℂ e (R e) :=
    hR.inner_left_eq_inner_right e e
  have hstar : starRingEnd ℂ (inner ℂ e (R e)) = inner ℂ e (R e) := by
    rw [inner_conj_symm]
    exact hsym
  have him : (inner ℂ e (R e)).im = 0 := by
    apply_fun Complex.im at hstar
    simp only [Complex.conj_im] at hstar
    linarith
  exact Complex.ext hre him

theorem RecurrentPrimeSourceFaithfulCompletion.operator_eq_minimal
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimeSourceFaithfulCompletion a) :
    X.operator = recurrentPrimeMinimalCompletion a.property := by
  have hdecomp := X.toRecurrentPrimePositiveCompletion.minimal_plus_recurrent.1
  rw [X.remainder_eq_zero, add_zero] at hdecomp
  exact hdecomp

/-! ## Trace-norm reconstruction -/

/-- Trace-class bundle of the shifted minimal tail. -/
def recurrentPrimeTailSchatten (a : {d : ℝ // 0 < d}) (j : ℕ) :
    SchattenOneOperator PrimeHodgeHistoryHilbert where
  val := recurrentPrimeTailCompletion a.property j
  property := historyStokesOperator_memSchattenClass_one
    (fun n => PrimeHodgeHistory.m (n + j))
    (fun n => PrimeHodgeHistory.m_nonneg (n + j))
    ((summable_nat_add_iff j).mpr PrimeHodgeHistory.summable_m)
    (PrimeHodgeHistory.summable_sq_m.comp_injective
      (fun _ _ h => Nat.add_right_cancel h)) a.property

/-- Minimal completion bundled in genuine Schatten-one norm. -/
def recurrentPrimeMinimalSchatten (a : {d : ℝ // 0 < d}) :
    SchattenOneOperator PrimeHodgeHistoryHilbert :=
  recurrentPrimeTailSchatten a 0

@[simp] theorem recurrentPrimeMinimalSchatten_coe (a : {d : ℝ // 0 < d}) :
    ((recurrentPrimeMinimalSchatten a : SchattenOneOperator
      PrimeHodgeHistoryHilbert) : PrimeHodgeHistoryHilbert →L[ℂ]
        PrimeHodgeHistoryHilbert) = recurrentPrimeMinimalCompletion a.property :=
  recurrentPrimeTailCompletion_zero a.property

/-- The `j`th emitted defect, bundled in genuine trace norm. -/
def recurrentPrimeDefectSchatten (a : {d : ℝ // 0 < d}) (j : ℕ) :
    SchattenOneOperator PrimeHodgeHistoryHilbert :=
  recurrentPrimeTailSchatten a j - recurrentPrimeTailSchatten a (j + 1)

theorem recurrentPrimeTailSchatten_norm (a : {d : ℝ // 0 < d}) (j : ℕ) :
    ‖recurrentPrimeTailSchatten a j‖ = ∑' n, PrimeHodgeHistory.m (n + j) := by
  rw [SchattenOneOperator.norm_def]
  exact traceNorm_historyStokesOperator
    (fun n => PrimeHodgeHistory.m (n + j))
    (fun n => PrimeHodgeHistory.m_nonneg (n + j))
    ((summable_nat_add_iff j).mpr PrimeHodgeHistory.summable_m)
    (PrimeHodgeHistory.summable_sq_m.comp_injective
      (fun _ _ h => Nat.add_right_cancel h)) a.property

theorem recurrentPrimeTailSchatten_tendsto_zero (a : {d : ℝ // 0 < d}) :
    Tendsto (fun j => recurrentPrimeTailSchatten a j) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htail := tendsto_sum_nat_add PrimeHodgeHistory.m
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨N, hN⟩ := htail ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right, recurrentPrimeTailSchatten_norm]
  simpa [Real.dist_eq, abs_of_nonneg (tsum_nonneg
    (fun k => PrimeHodgeHistory.m_nonneg (k + n)))] using hN n hn

theorem recurrentPrimeDefectSchatten_coe (a : {d : ℝ // 0 < d}) (j : ℕ) :
    ((recurrentPrimeDefectSchatten a j : SchattenOneOperator
      PrimeHodgeHistoryHilbert) : PrimeHodgeHistoryHilbert →L[ℂ]
        PrimeHodgeHistoryHilbert) =
      (recurrentHistoryConjugate^[j])
        (primeHodgeHistoryDefectOperator a.property) := by
  induction j with
  | zero =>
      simp only [recurrentPrimeDefectSchatten, Function.iterate_zero, id_eq,
        SchattenOneOperator.coe_sub]
      rw [show ((recurrentPrimeTailSchatten a 0 : SchattenOneOperator
        PrimeHodgeHistoryHilbert) : PrimeHodgeHistoryHilbert →L[ℂ]
          PrimeHodgeHistoryHilbert) = recurrentPrimeMinimalCompletion a.property by
            exact recurrentPrimeTailCompletion_zero a.property]
      rw [show ((recurrentPrimeTailSchatten a 1 : SchattenOneOperator
        PrimeHodgeHistoryHilbert) : PrimeHodgeHistoryHilbert →L[ℂ]
          PrimeHodgeHistoryHilbert) =
            recurrentHistoryConjugate (recurrentPrimeMinimalCompletion a.property) by
              change recurrentPrimeTailCompletion a.property 1 =
                recurrentHistoryConjugate (recurrentPrimeMinimalCompletion a.property)
              rw [← recurrentHistoryConjugate_tail a.property 0,
                recurrentPrimeTailCompletion_zero]]
      exact recurrentPrimeMinimalCompletion_displacement a.property
  | succ j ih =>
      simp only [recurrentPrimeDefectSchatten, SchattenOneOperator.coe_sub]
      rw [Function.iterate_succ_apply', ← ih]
      change recurrentPrimeTailCompletion a.property (j + 1) -
          recurrentPrimeTailCompletion a.property (j + 1 + 1) =
        recurrentHistoryConjugate
          (recurrentPrimeTailCompletion a.property j -
            recurrentPrimeTailCompletion a.property (j + 1))
      rw [recurrentHistoryConjugate_sub]
      rw [recurrentHistoryConjugate_tail, recurrentHistoryConjugate_tail]

theorem recurrentPrimeDefectSchatten_coe_historyStokes
    (a : {d : ℝ // 0 < d}) (j : ℕ) :
    ((recurrentPrimeDefectSchatten a j : SchattenOneOperator
      PrimeHodgeHistoryHilbert) : PrimeHodgeHistoryHilbert →L[ℂ]
        PrimeHodgeHistoryHilbert) =
      historyStokesOperator (fun n => PrimeHodgeHistory.w (n + j))
        (fun n => (PrimeHodgeHistory.w_pos (n + j)).le)
        (PrimeHodgeHistory.summable_sq_w.comp_injective
          (fun _ _ h => Nat.add_right_cancel h)) a.property := by
  change recurrentPrimeTailCompletion a.property j -
      recurrentPrimeTailCompletion a.property (j + 1) = _
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext np
  rcases np with ⟨n, p⟩
  change
    recurrentPrimeTailCompletion a.property j x (n, p) -
        recurrentPrimeTailCompletion a.property (j + 1) x (n, p) =
      historyStokesOperator (fun k => PrimeHodgeHistory.w (k + j))
        (fun k => (PrimeHodgeHistory.w_pos (k + j)).le)
        (PrimeHodgeHistory.summable_sq_w.comp_injective
          (fun _ _ h => Nat.add_right_cancel h)) a.property x (n, p)
  rw [recurrentPrimeTailCompletion, recurrentPrimeTailCompletion,
    historyStokesOperator_apply_coordinate, historyStokesOperator_apply_coordinate,
    historyStokesOperator_apply_coordinate]
  rw [PrimeHodgeHistory.w]
  push_cast
  rw [show n + (j + 1) = n + j + 1 by omega]
  ring

theorem recurrentPrimeDefectSchatten_norm (a : {d : ℝ // 0 < d}) (j : ℕ) :
    ‖recurrentPrimeDefectSchatten a j‖ = PrimeHodgeHistory.m j := by
  rw [SchattenOneOperator.norm_def]
  have hoperator :
      ((recurrentPrimeDefectSchatten a j : SchattenOneOperator
        PrimeHodgeHistoryHilbert) : PrimeHodgeHistoryHilbert →L[ℂ]
          PrimeHodgeHistoryHilbert) =
        historyStokesOperator (fun n => PrimeHodgeHistory.w (n + j))
          (fun n => (PrimeHodgeHistory.w_pos (n + j)).le)
          (PrimeHodgeHistory.summable_sq_w.comp_injective
            (fun _ _ h => Nat.add_right_cancel h)) a.property := by
    exact recurrentPrimeDefectSchatten_coe_historyStokes a j
  rw [hoperator]
  rw [traceNorm_historyStokesOperator
    (fun n => PrimeHodgeHistory.w (n + j))
    (fun n => (PrimeHodgeHistory.w_pos (n + j)).le)
    ((summable_nat_add_iff j).mpr PrimeHodgeHistory.summable_w)
    (PrimeHodgeHistory.summable_sq_w.comp_injective
      (fun _ _ h => Nat.add_right_cancel h)) a.property]
  exact PrimeHodgeHistory.tail_tsum_w j

theorem summable_recurrentPrimeDefectSchatten (a : {d : ℝ // 0 < d}) :
    Summable fun j => recurrentPrimeDefectSchatten a j := by
  apply Summable.of_norm
  exact PrimeHodgeHistory.summable_m.congr
    (fun j => (recurrentPrimeDefectSchatten_norm a j).symm)

/-- Exact reconstruction of the minimal completion in genuine trace norm:
`G = ∑ j, U*^j T U^j`. -/
theorem hasSum_recurrentPrimeDefectSchatten (a : {d : ℝ // 0 < d}) :
    HasSum (fun j => recurrentPrimeDefectSchatten a j)
      (recurrentPrimeMinimalSchatten a) := by
  let hsum := summable_recurrentPrimeDefectSchatten a
  have hpartial : Tendsto
      (fun N => ∑ j ∈ Finset.range N, recurrentPrimeDefectSchatten a j)
      atTop (nhds (recurrentPrimeMinimalSchatten a)) := by
    have htel (N : ℕ) :
        (∑ j ∈ Finset.range N, recurrentPrimeDefectSchatten a j) =
          recurrentPrimeMinimalSchatten a - recurrentPrimeTailSchatten a N := by
      exact Finset.sum_range_sub' (fun j => recurrentPrimeTailSchatten a j) N
    simp only [htel]
    simpa using tendsto_const_nhds.sub (recurrentPrimeTailSchatten_tendsto_zero a)
  have heq : (∑' j, recurrentPrimeDefectSchatten a j) =
      recurrentPrimeMinimalSchatten a :=
    tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hpartial
  simpa [heq] using hsum.hasSum

/-- Operator-norm shadow of the trace-norm reconstruction. -/
theorem hasSum_recurrentPrimeDefect_iterates (a : {d : ℝ // 0 < d}) :
    HasSum (fun j => (recurrentHistoryConjugate^[j])
      (primeHodgeHistoryDefectOperator a.property))
      (recurrentPrimeMinimalCompletion a.property) := by
  have hmapped := (hasSum_recurrentPrimeDefectSchatten a).map
    (schattenOneCoeCLM (H := PrimeHodgeHistoryHilbert))
    (schattenOneCoeCLM (H := PrimeHodgeHistoryHilbert)).continuous
  rw [show (schattenOneCoeCLM (H := PrimeHodgeHistoryHilbert) ∘
      fun j => recurrentPrimeDefectSchatten a j) =
      fun j => (recurrentHistoryConjugate^[j])
        (primeHodgeHistoryDefectOperator a.property) by
    funext j
    exact recurrentPrimeDefectSchatten_coe a j] at hmapped
  simpa only [schattenOneCoeCLM_apply, recurrentPrimeMinimalSchatten_coe] using hmapped

/-! ## Normalized finite traces and finite-rank horizons -/

/-- Nonempty history cutoffs, so normalization carries no side condition. -/
abbrev RecurrentPositiveCutoff := {N : ℕ // 0 < N}

theorem RecurrentPrimePositiveCompletion.normalizedFiniteCompressionTrace_eq
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimePositiveCompletion a)
    (N : RecurrentPositiveCutoff) (F : Finset Nat.Primes) :
    (1 / (N : ℝ)) * recurrentFiniteCompressionTrace X.remainder N F =
      recurrentFiniteBoundaryExcess a X.operator F := by
  rw [X.finiteCompressionTrace_eq_boundaryExcess]
  field_simp [Nat.ne_of_gt N.property]

/-- A positive stationary operator vanishes if its grade-zero compression vanishes. -/
theorem recurrentOperator_eq_zero_of_gradeCompression_eq_zero
    (R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert)
    (hR : R.IsPositive)
    (hfixed : recurrentHistoryConjugate R = R)
    (hzero : recurrentGradeCompression R 0 = 0) : R = 0 := by
  apply continuousLinearMap_eq_of_eq_on_hilbertBasis
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex) R 0
  intro np
  rcases np with ⟨n, p⟩
  let e := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p)
  apply hR.apply_eq_zero_of_inner_eq_zero
  have hre : (inner ℂ e (R e)).re = 0 := by
    change (inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
      (R (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p)))).re = 0
    rw [← inner_basis_recurrentGradeCompression]
    rw [recurrentGradeCompression_eq_zero R hfixed n, hzero]
    simp
  have hsym : inner ℂ (R e) e = inner ℂ e (R e) :=
    hR.inner_left_eq_inner_right e e
  have hstar : starRingEnd ℂ (inner ℂ e (R e)) = inner ℂ e (R e) := by
    rw [inner_conj_symm]
    exact hsym
  have him : (inner ℂ e (R e)).im = 0 := by
    apply_fun Complex.im at hstar
    simp only [Complex.conj_im] at hstar
    linarith
  exact Complex.ext hre him

theorem euclideanIdentity_memSchattenClass_one (n : ℕ) :
    MemSchattenClass 1
      (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))) := by
  apply memSchattenClass_of_hasRankLE (n := n) one_pos
  refine ⟨⊤, inferInstance, ?_, ?_⟩
  · simp
  · intro x
    simp

/-- Finite-rank projection horizon represented by an isometric synthesis.
The `quantum` is its exact complex rank. -/
structure RecurrentPrimeProjectionHorizon (a : {d : ℝ // 0 < d})
    extends RecurrentPrimePositiveCompletion a where
  quantum : ℕ
  synthesis : EuclideanSpace ℂ (Fin quantum) →ₗᵢ[ℂ]
    lp (fun _ : Nat.Primes => ℂ) 2
  gradeZeroProjection :
    recurrentGradeCompression toRecurrentPrimePositiveCompletion.remainder 0 =
      (synthesis.toContinuousLinearMap ∘L
        adjoint synthesis.toContinuousLinearMap)

theorem RecurrentPrimeProjectionHorizon.gradeZero_memSchattenClass_one
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimeProjectionHorizon a) :
    MemSchattenClass 1
      (recurrentGradeCompression
        X.toRecurrentPrimePositiveCompletion.remainder 0) := by
  rw [X.gradeZeroProjection]
  simpa only [ContinuousLinearMap.comp_id] using
    GaloisForLFunctions.HTGeometry.memSchattenClass_one_sandwich
      X.synthesis.toContinuousLinearMap
      (euclideanIdentity_memSchattenClass_one X.quantum)

/-- The represented grade-zero horizon is literally an orthogonal projection. -/
theorem RecurrentPrimeProjectionHorizon.gradeZero_idempotent
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimeProjectionHorizon a) :
    (recurrentGradeCompression
        X.toRecurrentPrimePositiveCompletion.remainder 0) ∘L
      recurrentGradeCompression
        X.toRecurrentPrimePositiveCompletion.remainder 0 =
      recurrentGradeCompression
        X.toRecurrentPrimePositiveCompletion.remainder 0 := by
  rw [X.gradeZeroProjection]
  rw [ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc
      (adjoint X.synthesis.toContinuousLinearMap)
      X.synthesis.toContinuousLinearMap
      (adjoint X.synthesis.toContinuousLinearMap),
    X.synthesis.adjoint_comp_self]
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem RecurrentPrimeProjectionHorizon.gradeZero_isSelfAdjoint
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimeProjectionHorizon a) :
    adjoint (recurrentGradeCompression
      X.toRecurrentPrimePositiveCompletion.remainder 0) =
      recurrentGradeCompression
        X.toRecurrentPrimePositiveCompletion.remainder 0 := by
  rw [X.gradeZeroProjection, ContinuousLinearMap.adjoint_comp, adjoint_adjoint]

/-- Exact complex rank of the finite grade-zero projection. -/
theorem RecurrentPrimeProjectionHorizon.gradeZero_finrank_range_eq_quantum
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimeProjectionHorizon a) :
    Module.finrank ℂ
      (recurrentGradeCompression
        X.toRecurrentPrimePositiveCompletion.remainder 0).range = X.quantum := by
  rw [X.gradeZeroProjection]
  simpa using
    GaloisForLFunctions.HTGeometry.finrank_range_comp_adjoint_of_finiteDimensional_domain_injective
        X.synthesis.toContinuousLinearMap X.synthesis.injective

theorem opTrace_isometricFiniteProjection
    (n : ℕ) (J : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ]
      lp (fun _ : Nat.Primes => ℂ) 2) :
    ContinuousLinearMap.opTrace
      (J.toContinuousLinearMap ∘L adjoint J.toContinuousLinearMap) = (n : ℂ) := by
  let I := ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))
  calc
    ContinuousLinearMap.opTrace
        (J.toContinuousLinearMap ∘L adjoint J.toContinuousLinearMap) =
      ContinuousLinearMap.opTrace
        ((J.toContinuousLinearMap ∘L I) ∘L adjoint J.toContinuousLinearMap) := by
          congr 1
    _ = ContinuousLinearMap.opTrace
        (I ∘L (adjoint J.toContinuousLinearMap ∘L J.toContinuousLinearMap)) :=
      GaloisForLFunctions.HTGeometry.opTrace_sandwich
        J.toContinuousLinearMap I (euclideanIdentity_memSchattenClass_one n)
    _ = ContinuousLinearMap.opTrace I := by
      rw [J.adjoint_comp_self]
      rfl
    _ = (n : ℂ) := by
      rw [opTrace_eq_finiteOperatorMatrix_trace]
      rw [show finiteOperatorMatrixEquiv I = 1 by exact map_one _]
      simp

theorem RecurrentPrimeProjectionHorizon.totalBoundaryExcess_eq_quantum
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimeProjectionHorizon a) :
    recurrentTotalBoundaryExcess a X.operator = (X.quantum : ℝ) := by
  rw [X.toRecurrentPrimePositiveCompletion.totalBoundaryExcess_eq_re_opTrace
    X.gradeZero_memSchattenClass_one]
  rw [X.gradeZeroProjection, opTrace_isometricFiniteProjection]
  simp

theorem RecurrentPrimeProjectionHorizon.remainder_eq_zero_of_totalBoundaryExcess_lt_one
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimeProjectionHorizon a)
    (hsmall : recurrentTotalBoundaryExcess a X.operator < 1) :
    X.toRecurrentPrimePositiveCompletion.remainder = 0 := by
  have hq : X.quantum = 0 := by
    rw [X.totalBoundaryExcess_eq_quantum] at hsmall
    have hnat : X.quantum < 1 := by exact_mod_cast hsmall
    omega
  apply recurrentOperator_eq_zero_of_gradeCompression_eq_zero
    X.toRecurrentPrimePositiveCompletion.remainder
    X.toRecurrentPrimePositiveCompletion.remainder_isPositive
    X.toRecurrentPrimePositiveCompletion.remainder_fixed
  rw [X.gradeZeroProjection]
  ext x
  letI : Subsingleton (EuclideanSpace ℂ (Fin X.quantum)) := by
    rw [hq]
    infer_instance
  have hx : adjoint X.synthesis.toContinuousLinearMap x = 0 :=
    Subsingleton.elim _ _
  simp [hx]

theorem RecurrentPrimeProjectionHorizon.operator_eq_minimal_of_totalBoundaryExcess_lt_one
    {a : {d : ℝ // 0 < d}} (X : RecurrentPrimeProjectionHorizon a)
    (hsmall : recurrentTotalBoundaryExcess a X.operator < 1) :
    X.operator = recurrentPrimeMinimalCompletion a.property := by
  have hdecomp := X.toRecurrentPrimePositiveCompletion.minimal_plus_recurrent.1
  rw [X.remainder_eq_zero_of_totalBoundaryExcess_lt_one hsmall, add_zero] at hdecomp
  exact hdecomp

end
end RHTower

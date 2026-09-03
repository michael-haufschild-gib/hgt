import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCofinalChildTraceClass
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryDeterminant
import GaloisForLFunctions.RHTower.ArithmeticDilationTraceClass
import GaloisForLFunctions.HTGeometry.NuclearTraceLaw

/-!
# Prime--Hodge history integral--nuclear defect

This module constructs one pre-divisor operator on `ℓ²(ℕ × Primes)`.  Its history flux is
the exact telescoping Kummer sequence `w n = m n - m (n+1)`; each history fibre retains the full
normalized Stokes cofinal prime kernel.  The resulting literal matrix is positive, trace-class,
has integral trace and trace norm one, is nonzero between every two primes on every history
slice, and recovers every homotopy tail `m n`.

No zero, divisor copy, chosen ordinate, or RH hypothesis enters the construction.
-/

open Filter Topology BigOperators

namespace PrimeHodgeHistory

noncomputable section

def m (n : ℕ) : ℝ :=
  105 / (((2 * n + 3 : ℕ) : ℝ) * ((2 * n + 5 : ℕ) : ℝ) * ((2 * n + 7 : ℕ) : ℝ))

def w (n : ℕ) : ℝ := m n - m (n + 1)

theorem m_zero : m 0 = 1 := by norm_num [m]

theorem w_formula (n : ℕ) :
    w n = 630 / (((2 * n + 3 : ℕ) : ℝ) * ((2 * n + 5 : ℕ) : ℝ) *
      ((2 * n + 7 : ℕ) : ℝ) * ((2 * n + 9 : ℕ) : ℝ)) := by
  rw [w, m, m]
  push_cast
  field_simp
  ring

theorem w_pos (n : ℕ) : 0 < w n := by
  rw [w_formula]
  positivity

theorem w_zero : w 0 = 2 / 3 := by norm_num [w, m]

theorem m_tendsto_zero : Tendsto m atTop (nhds 0) := by
  have hlin : Tendsto (fun n : ℕ => (2 : ℝ) * n + 3) atTop atTop :=
    tendsto_atTop_add_const_right atTop 3
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hden : Tendsto (fun n : ℕ =>
      (((2 * n + 3 : ℕ) : ℝ) * ((2 * n + 5 : ℕ) : ℝ) * ((2 * n + 7 : ℕ) : ℝ)))
      atTop atTop := by
    have h5 : Tendsto (fun n : ℕ => (2 : ℝ) * n + 5) atTop atTop :=
      tendsto_atTop_add_const_right atTop 5
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    have h7 : Tendsto (fun n : ℕ => (2 : ℝ) * n + 7) atTop atTop :=
      tendsto_atTop_add_const_right atTop 7
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      (hlin.atTop_mul_atTop₀ h5).atTop_mul_atTop₀ h7
  exact (tendsto_const_nhds (x := (105 : ℝ))).div_atTop hden

theorem sum_range_w (N : ℕ) :
    (∑ n ∈ Finset.range N, w n) = 1 - m N := by
  induction N with
  | zero => simp [m_zero]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, w]
      ring

theorem hasSum_w : HasSum w 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => (w_pos n).le)]
  convert tendsto_const_nhds.sub m_tendsto_zero using 1
  · funext N
    exact sum_range_w N
  · ring

theorem summable_w : Summable w := hasSum_w.summable

theorem tsum_w : ∑' n, w n = 1 := hasSum_w.tsum_eq

theorem tail_hasSum_w (n : ℕ) : HasSum (fun k => w (k + n)) (m n) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => (w_pos (k + n)).le)]
  have hlim : Tendsto (fun N : ℕ => m n - m (N + n)) atTop (nhds (m n)) := by
    simpa using tendsto_const_nhds.sub (m_tendsto_zero.comp (tendsto_add_atTop_nat n))
  convert hlim using 1
  funext N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, w]
      ring

theorem tail_tsum_w (n : ℕ) : (∑' k, w (k + n)) = m n :=
  (tail_hasSum_w n).tsum_eq

theorem w_antitone : Antitone w := by
  intro a b hab
  rw [w_formula, w_formula]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  gcongr

theorem w_le_two_thirds (n : ℕ) : w n ≤ 2 / 3 := by
  rw [← w_zero]
  exact w_antitone (Nat.zero_le n)

theorem subunit_constant : (8 : ℝ) / (3 * Real.sqrt 35) < 1 := by
  have hsq : (8 / 3 : ℝ) ^ 2 < 35 := by norm_num
  have hsqrt : 8 / 3 < Real.sqrt 35 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 35), Real.sqrt_nonneg 35]
  have hpos : 0 < Real.sqrt 35 := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_one (mul_pos (by norm_num) hpos)]
  nlinarith

end
end PrimeHodgeHistory

namespace RHTower

open Filter Topology BigOperators ContinuousLinearMap
open scoped InnerProductSpace Matrix ComplexOrder

noncomputable section

def primeHodgeHistoryFluxOperator : ArithmeticDilationHilbert →L[ℂ] ArithmeticDilationHilbert :=
  absoluteMatrixOperator (HilbertSchmidt.diagMul fun n => (PrimeHodgeHistory.w n : ℂ))

theorem summable_norm_historyFlux : Summable fun n => ‖(PrimeHodgeHistory.w n : ℂ)‖ := by
  have hnorm : (fun n => ‖(PrimeHodgeHistory.w n : ℂ)‖) = PrimeHodgeHistory.w := by
    funext n
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (PrimeHodgeHistory.w_pos n)]
  rw [hnorm]
  exact PrimeHodgeHistory.summable_w

theorem primeHodgeHistoryFluxOperator_memSchattenClass_one : MemSchattenClass 1 primeHodgeHistoryFluxOperator := by
  exact absoluteMatrixOperator_memSchattenClass_one
    (summable_norm_diagMul_of_summable_norm summable_norm_historyFlux)

theorem primeHodgeHistoryFluxOperator_isPositive : primeHodgeHistoryFluxOperator.IsPositive := by
  exact absoluteMatrixOperator_diagMul_isPositive_ofReal PrimeHodgeHistory.w
    summable_norm_historyFlux (fun n => (PrimeHodgeHistory.w_pos n).le)

theorem primeHodgeHistoryFluxOperator_apply_basis (n : ℕ) :
    primeHodgeHistoryFluxOperator (HilbertSchmidt.lpBasis ℕ n) =
      (PrimeHodgeHistory.w n : ℂ) • HilbertSchmidt.lpBasis ℕ n := by
  exact absoluteMatrixOperator_diagMul_apply_basis _ summable_norm_historyFlux n

theorem inner_basis_primeHodgeHistoryFluxOperator_basis (n : ℕ) :
    inner ℂ (HilbertSchmidt.lpBasis ℕ n)
      (primeHodgeHistoryFluxOperator (HilbertSchmidt.lpBasis ℕ n)) = (PrimeHodgeHistory.w n : ℂ) := by
  rw [primeHodgeHistoryFluxOperator_apply_basis, inner_smul_right]
  rw [inner_self_eq_norm_sq_to_K,
    (HilbertSchmidt.lpBasis ℕ).orthonormal.norm_eq_one]
  simp

theorem opTrace_primeHodgeHistoryFluxOperator : ContinuousLinearMap.opTrace primeHodgeHistoryFluxOperator = 1 := by
  let b := HilbertSchmidt.lpBasis ℕ
  have hsum : Summable fun n => inner ℂ (b n) (primeHodgeHistoryFluxOperator (b n)) := by
    exact (Complex.summable_ofReal.mpr PrimeHodgeHistory.summable_w).congr
      (fun n => (inner_basis_primeHodgeHistoryFluxOperator_basis n).symm)
  rw [opTrace_eq_tsum_basis_of_isPositive_of_summable_diagonal b primeHodgeHistoryFluxOperator_isPositive hsum]
  rw [tsum_congr inner_basis_primeHodgeHistoryFluxOperator_basis, ← Complex.ofReal_tsum, PrimeHodgeHistory.tsum_w]
  norm_num

theorem primeHodgeHistoryFluxOperator_eq_diagonalOperator :
    primeHodgeHistoryFluxOperator = diagonalOperator (fun n => (PrimeHodgeHistory.w n : ℂ))
      (C := 2 / 3) (fun n => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (PrimeHodgeHistory.w_pos n)]
        exact PrimeHodgeHistory.w_le_two_thirds n) := by
  rw [primeHodgeHistoryFluxOperator, absoluteMatrixOperator_diagMul_eq_diagonalOperator _
    summable_norm_historyFlux]
  ext f n
  simp only [diagonalOperator_apply]

theorem norm_primeHodgeHistoryFluxOperator : ‖primeHodgeHistoryFluxOperator‖ = 2 / 3 := by
  rw [primeHodgeHistoryFluxOperator_eq_diagonalOperator]
  apply norm_diagonalOperator_eq (m := 0)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (PrimeHodgeHistory.w_pos 0), PrimeHodgeHistory.w_zero]

theorem traceNorm_primeHodgeHistoryFluxOperator : traceNorm ArithmeticDilationHilbert primeHodgeHistoryFluxOperator = 1 := by
  let M : ℕ × ℕ → ℂ := HilbertSchmidt.diagMul fun n => (PrimeHodgeHistory.w n : ℂ)
  have hM : Summable fun p => ‖M p‖ :=
    summable_norm_diagMul_of_summable_norm summable_norm_historyFlux
  have hsumM : (∑' p, ‖M p‖) = 1 := by
    have heq : (fun p : ℕ × ℕ => ‖M p‖) = diagMatrix PrimeHodgeHistory.w := by
      funext p
      rcases p with ⟨i, j⟩
      by_cases h : i = j
      ·
        subst j
        simp [M, HilbertSchmidt.diagMul, diagMatrix, Complex.norm_real,
          Real.norm_eq_abs, (PrimeHodgeHistory.w_pos i).le]
      · simp [M, HilbertSchmidt.diagMul, diagMatrix, h]
    rw [heq, tsum_diagMatrix, PrimeHodgeHistory.tsum_w]
  have hupper : traceNorm ArithmeticDilationHilbert primeHodgeHistoryFluxOperator ≤ 1 := by
    simpa [primeHodgeHistoryFluxOperator, M, hsumM] using traceNorm_absoluteMatrixOperator_le hM
  have hlower : (1 : ℝ) ≤ traceNorm ArithmeticDilationHilbert primeHodgeHistoryFluxOperator := by
    have h := norm_opTrace_le_traceNorm primeHodgeHistoryFluxOperator_memSchattenClass_one
    rw [opTrace_primeHodgeHistoryFluxOperator, norm_one] at h
    exact h
  exact le_antisymm hupper hlower

/-! The one-object history--prime defect. -/

abbrev PrimeHodgeHistoryIndex := ℕ × Nat.Primes

abbrev PrimeHodgeHistoryHilbert :=
  lp (fun _ : PrimeHodgeHistoryIndex => ℂ) 2

def normalizedStokesPrimeKernel (d : ℝ) (pq : Nat.Primes × Nat.Primes) : ℂ :=
  routePPrimitiveGammaJuliaStokesCofinalChildKernel d pq /
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d

def primeHodgeHistoryDefectKernel
    (d : ℝ) (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) : ℂ :=
  if ab.1.1 = ab.2.1 then
    (PrimeHodgeHistory.w ab.1.1 : ℂ) * normalizedStokesPrimeKernel d (ab.1.2, ab.2.2)
  else 0

theorem normalizedStokesPrimeKernel_hsAdjoint (d : ℝ) :
    HilbertSchmidt.hsAdjoint (normalizedStokesPrimeKernel d) =
      normalizedStokesPrimeKernel d := by
  funext pq
  rw [HilbertSchmidt.hsAdjoint]
  change star (routePPrimitiveGammaJuliaStokesCofinalChildKernel d (pq.2, pq.1) /
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ)) =
    routePPrimitiveGammaJuliaStokesCofinalChildKernel d pq /
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ)
  rw [star_div₀]
  have hsource := congrFun
    (routePPrimitiveGammaJuliaStokesCofinalChildKernel_hsAdjoint d) pq
  rw [show star (routePPrimitiveGammaJuliaStokesCofinalChildKernel d (pq.2, pq.1)) =
      routePPrimitiveGammaJuliaStokesCofinalChildKernel d pq by
    simpa [HilbertSchmidt.hsAdjoint] using hsource]
  simp

theorem primeHodgeHistoryDefectKernel_hsAdjoint (d : ℝ) :
    HilbertSchmidt.hsAdjoint (primeHodgeHistoryDefectKernel d) =
      primeHodgeHistoryDefectKernel d := by
  funext ab
  rw [HilbertSchmidt.hsAdjoint]
  change star (if ab.2.1 = ab.1.1 then
      (PrimeHodgeHistory.w ab.2.1 : ℂ) * normalizedStokesPrimeKernel d (ab.2.2, ab.1.2)
    else 0) =
    (if ab.1.1 = ab.2.1 then
      (PrimeHodgeHistory.w ab.1.1 : ℂ) * normalizedStokesPrimeKernel d (ab.1.2, ab.2.2)
    else 0)
  by_cases h : ab.1.1 = ab.2.1
  · have hr : ab.2.1 = ab.1.1 := h.symm
    rw [if_pos h, if_pos hr, star_mul]
    have hprime := congrFun (normalizedStokesPrimeKernel_hsAdjoint d) (ab.1.2, ab.2.2)
    rw [show star (normalizedStokesPrimeKernel d (ab.2.2, ab.1.2)) =
        normalizedStokesPrimeKernel d (ab.1.2, ab.2.2) by
      simpa [HilbertSchmidt.hsAdjoint] using hprime]
    rw [← h]
    simp [mul_comm]
  · have hr : ab.2.1 ≠ ab.1.1 := fun hr => h hr.symm
    rw [if_neg h, if_neg hr, star_zero]

def primeHodgeHistoryDiagonalWeight
    (d : ℝ) (np : PrimeHodgeHistoryIndex) : ℝ :=
  PrimeHodgeHistory.w np.1 * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d np.2 /
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d

theorem primeHodgeHistoryDiagonalWeight_pos
    {d : ℝ} (hd : 0 < d) (np : PrimeHodgeHistoryIndex) :
    0 < primeHodgeHistoryDiagonalWeight d np := by
  rw [primeHodgeHistoryDiagonalWeight]
  have hsource : 0 < routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d np.2 := by
    have hpR : (0 : ℝ) < (np.2 : ℝ) := by exact_mod_cast np.2.property.pos
    rw [routePPrimitiveGammaJuliaStokesTransportedPrimeWeight]
    exact mul_pos (routePPrimitiveGammaJuliaStokesApertureScaleSq_pos hd np.2) (by
      rw [routePPrimitiveGammaJuliaLogCofinalTraceWeight_prime_zero]
      exact mul_pos (by norm_num) (div_pos zero_lt_one hpR))
  exact div_pos (mul_pos (PrimeHodgeHistory.w_pos np.1) hsource)
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd)

theorem summable_primeHodgeHistoryDiagonalWeight
    {d : ℝ} (hd : 0 < d) : Summable (primeHodgeHistoryDiagonalWeight d) := by
  have hp := summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd
  have hprod : Summable (fun np : PrimeHodgeHistoryIndex =>
      PrimeHodgeHistory.w np.1 * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d np.2) :=
    summable_mul_of_summable_norm PrimeHodgeHistory.summable_w.norm hp.norm
  exact (hprod.div_const _).congr fun np => by
    rw [primeHodgeHistoryDiagonalWeight]

theorem tsum_primeHodgeHistoryDiagonalWeight
    {d : ℝ} (hd : 0 < d) :
    (∑' np, primeHodgeHistoryDiagonalWeight d np) = 1 := by
  have hp := summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd
  have hfactor := tsum_mul_tsum_of_summable_norm PrimeHodgeHistory.summable_w.norm hp.norm
  rw [show primeHodgeHistoryDiagonalWeight d = fun np : PrimeHodgeHistoryIndex =>
      (PrimeHodgeHistory.w np.1 * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d np.2) /
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d by rfl]
  rw [tsum_div_const]
  rw [show (∑' np : PrimeHodgeHistoryIndex,
      PrimeHodgeHistory.w np.1 * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d np.2) =
      (∑' n, PrimeHodgeHistory.w n) *
        ∑' p, routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p by
          exact hfactor.symm]
  rw [PrimeHodgeHistory.tsum_w, one_mul,
    tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd]
  exact div_self
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).ne'

/-- Every history-tail marginal of the joint defect recovers its exact Kummer moment. -/
theorem tsum_primeHodgeHistoryDiagonalWeight_shift
    {d : ℝ} (hd : 0 < d) (n : ℕ) :
    (∑' kp : PrimeHodgeHistoryIndex,
      primeHodgeHistoryDiagonalWeight d (kp.1 + n, kp.2)) = PrimeHodgeHistory.m n := by
  have hw : Summable (fun k : ℕ => PrimeHodgeHistory.w (k + n)) :=
    (PrimeHodgeHistory.tail_hasSum_w n).summable
  have hp := summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd
  have hfactor := tsum_mul_tsum_of_summable_norm hw.norm hp.norm
  rw [show (fun kp : PrimeHodgeHistoryIndex =>
      primeHodgeHistoryDiagonalWeight d (kp.1 + n, kp.2)) =
      fun kp => (PrimeHodgeHistory.w (kp.1 + n) *
        routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d kp.2) /
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d by rfl]
  rw [tsum_div_const]
  rw [show (∑' kp : PrimeHodgeHistoryIndex,
      PrimeHodgeHistory.w (kp.1 + n) *
        routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d kp.2) =
      (∑' k, PrimeHodgeHistory.w (k + n)) *
        ∑' p, routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p by
          exact hfactor.symm]
  rw [PrimeHodgeHistory.tail_tsum_w,
    tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd]
  field_simp [(gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).ne']

theorem primeHodgeHistoryDefectKernel_diagonal
    {d : ℝ} (hd : 0 < d) (np : PrimeHodgeHistoryIndex) :
    primeHodgeHistoryDefectKernel d (np, np) =
      (primeHodgeHistoryDiagonalWeight d np : ℂ) := by
  rw [primeHodgeHistoryDefectKernel, if_pos rfl, normalizedStokesPrimeKernel,
    routePPrimitiveGammaJuliaStokesCofinalChildKernel_diagonal hd,
    primeHodgeHistoryDiagonalWeight]
  push_cast
  ring

theorem routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    0 < routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  rw [routePPrimitiveGammaJuliaStokesTransportedPrimeWeight]
  exact mul_pos (routePPrimitiveGammaJuliaStokesApertureScaleSq_pos hd p) (by
    rw [routePPrimitiveGammaJuliaLogCofinalTraceWeight_prime_zero]
    exact mul_pos (by norm_num) (div_pos zero_lt_one hpR))

theorem routePPrimitiveGammaJuliaStokesCofinalChildKernel_ne_zero
    {d : ℝ} (hd : 0 < d) (p q : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p, q) ≠ 0 := by
  intro hzero
  have hnorm := normSq_routePPrimitiveGammaJuliaStokesCofinalChildKernel hd p q
  rw [hzero, Complex.normSq_zero] at hnorm
  have hcoh : 0 < routePBaseCauchyCubicNormalizedCoherenceSq
      (Real.log (p : ℝ)) (Real.log (q : ℝ)) 0 := by
    rw [routePBaseCauchyCubicNormalizedCoherenceSq]
    have hp : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.property.one_lt)
    have hq : 0 < Real.log (q : ℝ) :=
      Real.log_pos (by exact_mod_cast q.property.one_lt)
    positivity
  have hprod : 0 < routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p *
      routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d q *
        routePBaseCauchyCubicNormalizedCoherenceSq
          (Real.log (p : ℝ)) (Real.log (q : ℝ)) 0 := by
    exact mul_pos (mul_pos
      (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd p)
      (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd q)) hcoh
  linarith

theorem primeHodgeHistoryDefectKernel_sameHistory_ne_zero
    {d : ℝ} (hd : 0 < d) (n : ℕ) (p q : Nat.Primes) :
    primeHodgeHistoryDefectKernel d ((n, p), (n, q)) ≠ 0 := by
  rw [primeHodgeHistoryDefectKernel, if_pos rfl, normalizedStokesPrimeKernel]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (PrimeHodgeHistory.w_pos n).ne')
    (div_ne_zero (routePPrimitiveGammaJuliaStokesCofinalChildKernel_ne_zero hd p q)
      (Complex.ofReal_ne_zero.mpr
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).ne'))

theorem norm_sq_primeHodgeHistoryDefectKernel_le
    {d : ℝ} (hd : 0 < d)
    (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) :
    ‖primeHodgeHistoryDefectKernel d ab‖ ^ 2 ≤
      primeHodgeHistoryDiagonalWeight d ab.1 *
        primeHodgeHistoryDiagonalWeight d ab.2 := by
  by_cases hhist : ab.1.1 = ab.2.1
  · rw [primeHodgeHistoryDefectKernel, if_pos hhist, normalizedStokesPrimeKernel,
      norm_mul, norm_div,
      Complex.norm_real, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_pos (PrimeHodgeHistory.w_pos ab.1.1), Real.norm_eq_abs,
      abs_of_pos (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd)]
    have hbase := norm_sq_routePPrimitiveGammaJuliaStokesCofinalChildKernel_le hd
      (ab.1.2, ab.2.2)
    rw [primeHodgeHistoryDiagonalWeight, primeHodgeHistoryDiagonalWeight]
    have hwEq : PrimeHodgeHistory.w ab.2.1 = PrimeHodgeHistory.w ab.1.1 := congrArg PrimeHodgeHistory.w hhist.symm
    rw [hwEq]
    have hJ := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd
    have hw := PrimeHodgeHistory.w_pos ab.1.1
    have hp := routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd ab.1.2
    have hq := routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd ab.2.2
    calc
      (PrimeHodgeHistory.w ab.1.1 *
          (‖routePPrimitiveGammaJuliaStokesCofinalChildKernel d (ab.1.2, ab.2.2)‖ /
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)) ^ 2
          = PrimeHodgeHistory.w ab.1.1 ^ 2 *
              ‖routePPrimitiveGammaJuliaStokesCofinalChildKernel d
                (ab.1.2, ab.2.2)‖ ^ 2 /
              gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d ^ 2 := by ring
      _ ≤ PrimeHodgeHistory.w ab.1.1 ^ 2 *
              (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d ab.1.2 *
                routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d ab.2.2) /
              gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d ^ 2 := by
            gcongr
      _ = (PrimeHodgeHistory.w ab.1.1 *
              routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d ab.1.2 /
              gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d) *
            (PrimeHodgeHistory.w ab.1.1 *
              routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d ab.2.2 /
              gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d) := by ring
  · rw [primeHodgeHistoryDefectKernel, if_neg hhist, norm_zero, zero_pow (by omega)]
    exact mul_nonneg (primeHodgeHistoryDiagonalWeight_pos hd ab.1).le
      (primeHodgeHistoryDiagonalWeight_pos hd ab.2).le

theorem primeHodgeHistoryDefectKernel_isHS
    {d : ℝ} (hd : 0 < d) :
    HilbertSchmidt.IsHS (primeHodgeHistoryDefectKernel d) := by
  rw [HilbertSchmidt.IsHS]
  refine Summable.of_nonneg_of_le (fun ab => sq_nonneg _)
    (norm_sq_primeHodgeHistoryDefectKernel_le hd) ?_
  have hw := summable_primeHodgeHistoryDiagonalWeight hd
  exact summable_mul_of_summable_norm hw.norm hw.norm

def primeHodgeHistoryDefectOperator
    {d : ℝ} (hd : 0 < d) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  HilbertSchmidt.toOperator (primeHodgeHistoryDefectKernel_isHS hd)

section FinitePositivity

open Matrix

variable {N : ℕ}

theorem matrix_finset_sum_apply {I : Type} (s : Finset I)
    (f : I → Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    ((∑ x ∈ s, f x) : Matrix (Fin N) (Fin N) ℂ) i j =
      ∑ x ∈ s, f x i j := by
  let ev : Matrix (Fin N) (Fin N) ℂ →+ ℂ :=
    { toFun := fun M => M i j
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_sum ev f s

def normalizedStokesFiniteMatrix (d : ℝ) (a : Fin N → PrimeHodgeHistoryIndex) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => normalizedStokesPrimeKernel d ((a i).2, (a j).2)

def historyMaskDiagonal (a : Fin N → PrimeHodgeHistoryIndex) (r : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => if (a i).1 = r then (Real.sqrt (PrimeHodgeHistory.w r) : ℂ) else 0

def primeHodgeHistoryFiniteMatrix (d : ℝ) (a : Fin N → PrimeHodgeHistoryIndex) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => primeHodgeHistoryDefectKernel d (a i, a j)

theorem normalizedStokesFiniteMatrix_posSemidef
    {d : ℝ} (hd : 0 < d) (a : Fin N → PrimeHodgeHistoryIndex) :
    (normalizedStokesFiniteMatrix d a).PosSemidef := by
  let p : Fin N → Nat.Primes := fun i => (a i).2
  let M := routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram
    d p (fun _ => 0)
  have hM : M.PosSemidef :=
    routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram_posSemidef
      d p (fun _ => 0)
  have hscale : normalizedStokesFiniteMatrix d a =
      (((gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)⁻¹ : ℝ) : ℂ) • M := by
    ext i j
    rw [normalizedStokesFiniteMatrix, normalizedStokesPrimeKernel, Matrix.smul_apply]
    rw [show routePPrimitiveGammaJuliaStokesCofinalChildKernel d ((a i).2, (a j).2) =
        M i j by
      simpa [p, M] using
        routePPrimitiveGammaJuliaStokesCofinalChildKernel_eq_actual_apply d p i j]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hscale]
  apply hM.smul
  apply Complex.nonneg_iff.mpr
  constructor
  · simpa using (inv_pos.mpr
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd)).le
  · simp

theorem historyMask_congruence_apply
    (d : ℝ) (a : Fin N → PrimeHodgeHistoryIndex) (r : ℕ) (i j : Fin N) :
    (Matrix.conjTranspose (historyMaskDiagonal a r) * normalizedStokesFiniteMatrix d a *
      historyMaskDiagonal a r) i j =
      if (a i).1 = r ∧ (a j).1 = r then
        PrimeHodgeHistory.w r * normalizedStokesFiniteMatrix d a i j else 0 := by
  have hself : Matrix.conjTranspose (historyMaskDiagonal a r) =
      historyMaskDiagonal a r := by
    ext u v
    by_cases huv : u = v
    · subst v
      rw [Matrix.conjTranspose_apply]
      simp only [historyMaskDiagonal, Matrix.diagonal_apply_eq]
      by_cases hu : (a u).1 = r
      · rw [if_pos hu]
        simp
      · rw [if_neg hu, star_zero]
    · rw [Matrix.conjTranspose_apply]
      simp only [historyMaskDiagonal, Matrix.diagonal_apply_ne _ huv,
        Matrix.diagonal_apply_ne _ (Ne.symm huv), star_zero]
  rw [hself, Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · by_cases hi : (a i).1 = r
      · by_cases hj : (a j).1 = r
        · simp only [historyMaskDiagonal, hi, hj, if_true, Matrix.diagonal_apply_eq,
            true_and]
          let z : ℂ := normalizedStokesFiniteMatrix d a i j
          change ((Real.sqrt (PrimeHodgeHistory.w r) : ℝ) : ℂ) * z *
              ((Real.sqrt (PrimeHodgeHistory.w r) : ℝ) : ℂ) =
            ((PrimeHodgeHistory.w r : ℝ) : ℂ) * z
          rw [show ((PrimeHodgeHistory.w r : ℝ) : ℂ) =
              ((Real.sqrt (PrimeHodgeHistory.w r) : ℝ) : ℂ) *
                ((Real.sqrt (PrimeHodgeHistory.w r) : ℝ) : ℂ) by
            norm_cast
            simpa [pow_two] using (Real.sq_sqrt (PrimeHodgeHistory.w_pos r).le).symm]
          ring
        · simp [historyMaskDiagonal, hi, hj]
      · simp [historyMaskDiagonal, hi]
    · intro k _ hki
      simp [historyMaskDiagonal, Ne.symm hki]
    · simp
  · intro k _ hkj
    simp [historyMaskDiagonal, hkj]
  · simp

theorem primeHodgeHistoryFiniteMatrix_eq_sum_congruence
    (d : ℝ) (a : Fin N → PrimeHodgeHistoryIndex) :
    primeHodgeHistoryFiniteMatrix d a =
      ∑ r ∈ Finset.univ.image (fun i : Fin N => (a i).1),
        Matrix.conjTranspose (historyMaskDiagonal a r) * normalizedStokesFiniteMatrix d a *
          historyMaskDiagonal a r := by
  let S : Matrix (Fin N) (Fin N) ℂ :=
    ∑ r ∈ Finset.univ.image (fun i : Fin N => (a i).1),
      Matrix.conjTranspose (historyMaskDiagonal a r) * normalizedStokesFiniteMatrix d a *
        historyMaskDiagonal a r
  change primeHodgeHistoryFiniteMatrix d a = S
  apply Matrix.ext
  intro i j
  rw [primeHodgeHistoryFiniteMatrix]
  rw [show S i j = ∑ r ∈ Finset.univ.image (fun k : Fin N => (a k).1),
      (Matrix.conjTranspose (historyMaskDiagonal a r) * normalizedStokesFiniteMatrix d a *
        historyMaskDiagonal a r) i j by
      dsimp only [S]
      exact matrix_finset_sum_apply _ _ i j]
  simp_rw [historyMask_congruence_apply]
  by_cases hij : (a i).1 = (a j).1
  · rw [primeHodgeHistoryDefectKernel, if_pos hij]
    rw [Finset.sum_eq_single (a i).1]
    · simp [hij, normalizedStokesFiniteMatrix]
    · intro r hr hne
      simp [Ne.symm hne]
    · simp
  · rw [primeHodgeHistoryDefectKernel, if_neg hij]
    rw [eq_comm]
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hi : (a i).1 = r
    · have hj : (a j).1 ≠ r := by
        intro hj
        exact hij (hi.trans hj.symm)
      simp [hi, hj]
    · simp [hi]

theorem primeHodgeHistoryFiniteMatrix_posSemidef
    {d : ℝ} (hd : 0 < d) (a : Fin N → PrimeHodgeHistoryIndex) :
    (primeHodgeHistoryFiniteMatrix d a).PosSemidef := by
  rw [primeHodgeHistoryFiniteMatrix_eq_sum_congruence]
  exact Finset.sum_induction _ Matrix.PosSemidef
    (fun _ _ hx hy => hx.add hy) Matrix.PosSemidef.zero
    (fun r _ => (normalizedStokesFiniteMatrix_posSemidef hd a).conjTranspose_mul_mul_same
      (historyMaskDiagonal a r))

theorem primeHodgeHistoryDefectBlockMatrix_posSemidef
    {d : ℝ} (hd : 0 < d) (s : Finset PrimeHodgeHistoryIndex) :
    (HilbertSchmidt.blockMatrix (primeHodgeHistoryDefectKernel d) s).PosSemidef := by
  let a : Fin s.card → PrimeHodgeHistoryIndex := fun i => (s.equivFin.symm i).1
  have hM : (primeHodgeHistoryFiniteMatrix d a).PosSemidef :=
    primeHodgeHistoryFiniteMatrix_posSemidef hd a
  have hsub := hM.submatrix s.equivFin
  have heq : HilbertSchmidt.blockMatrix (primeHodgeHistoryDefectKernel d) s =
      (primeHodgeHistoryFiniteMatrix d a).submatrix s.equivFin s.equivFin := by
    ext i j
    rw [HilbertSchmidt.blockMatrix]
    change primeHodgeHistoryDefectKernel d (i.1, j.1) =
      primeHodgeHistoryFiniteMatrix d a (s.equivFin i) (s.equivFin j)
    rw [primeHodgeHistoryFiniteMatrix]
    simp [a]
  rwa [heq]

end FinitePositivity

theorem primeHodgeHistoryDefectOperator_isPositive
    {d : ℝ} (hd : 0 < d) :
    (primeHodgeHistoryDefectOperator hd).IsPositive :=
  toOperator_isPositive_of_blockMatrix_posSemidef
    (primeHodgeHistoryDefectKernel_isHS hd)
    (primeHodgeHistoryDefectKernel_hsAdjoint d)
    (primeHodgeHistoryDefectBlockMatrix_posSemidef hd)

theorem inner_lpBasis_primeHodgeHistoryDefectOperator
    {d : ℝ} (hd : 0 < d) (np : PrimeHodgeHistoryIndex) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np)
      (primeHodgeHistoryDefectOperator hd
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np)) =
      (primeHodgeHistoryDiagonalWeight d np : ℂ) := by
  change inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np)
      (HilbertSchmidt.toOperator (primeHodgeHistoryDefectKernel_isHS hd)
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np)) = _
  rw [HilbertSchmidt.inner_lpBasis_toOperator,
    primeHodgeHistoryDefectKernel_diagonal hd]

theorem summable_primeHodgeHistoryDefectOperator_diagonal
    {d : ℝ} (hd : 0 < d) :
    Summable (fun np => inner ℂ
      (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np)
      (primeHodgeHistoryDefectOperator hd
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np))) := by
  refine (Complex.summable_ofReal.mpr
    (summable_primeHodgeHistoryDiagonalWeight hd)).congr fun np => ?_
  exact (inner_lpBasis_primeHodgeHistoryDefectOperator hd np).symm

theorem primeHodgeHistoryDefectOperator_memSchattenClass_one
    {d : ℝ} (hd : 0 < d) :
    MemSchattenClass 1 (primeHodgeHistoryDefectOperator hd) :=
  memSchattenClass_one_of_isPositive_of_summable_diagonal
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex)
    (primeHodgeHistoryDefectOperator_isPositive hd)
    (summable_primeHodgeHistoryDefectOperator_diagonal hd)

theorem opTrace_primeHodgeHistoryDefectOperator
    {d : ℝ} (hd : 0 < d) :
    ContinuousLinearMap.opTrace (primeHodgeHistoryDefectOperator hd) = 1 := by
  rw [opTrace_eq_tsum_basis_of_isPositive_of_summable_diagonal
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex)
    (primeHodgeHistoryDefectOperator_isPositive hd)
    (summable_primeHodgeHistoryDefectOperator_diagonal hd)]
  rw [tsum_congr (fun np => inner_lpBasis_primeHodgeHistoryDefectOperator hd np),
    ← Complex.ofReal_tsum, tsum_primeHodgeHistoryDiagonalWeight hd]
  norm_num

theorem traceNorm_eq_re_opTrace_of_isPositive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T) (hpos : T.IsPositive) :
    traceNorm H T = (ContinuousLinearMap.opTrace T).re := by
  have hT0 : (0 : H →L[ℂ] H) ≤ T :=
    (ContinuousLinearMap.nonneg_iff_isPositive T).2 hpos
  have hTstar : star T = T := hpos.isSelfAdjoint.star_eq
  have habs : ContinuousLinearMap.absOp T = T := by
    unfold ContinuousLinearMap.absOp
    rw [hTstar]
    exact CFC.sqrt_mul_self T hT0
  rw [traceNorm_eq_re_opTrace_absOp hT, habs]

theorem traceNorm_primeHodgeHistoryDefectOperator
    {d : ℝ} (hd : 0 < d) :
    traceNorm PrimeHodgeHistoryHilbert (primeHodgeHistoryDefectOperator hd) = 1 := by
  rw [traceNorm_eq_re_opTrace_of_isPositive
    (primeHodgeHistoryDefectOperator_memSchattenClass_one hd)
    (primeHodgeHistoryDefectOperator_isPositive hd),
    opTrace_primeHodgeHistoryDefectOperator hd]
  norm_num

/-- One closed certificate: positivity, nuclearity, unit trace and unit trace norm coexist with
literal nonzero cross-prime entries on every history slice. -/
theorem primeHodgeHistoryIntegralNuclearDefect
    {d : ℝ} (hd : 0 < d) :
    (primeHodgeHistoryDefectOperator hd).IsPositive ∧
      MemSchattenClass 1 (primeHodgeHistoryDefectOperator hd) ∧
      ContinuousLinearMap.opTrace (primeHodgeHistoryDefectOperator hd) = 1 ∧
      traceNorm PrimeHodgeHistoryHilbert (primeHodgeHistoryDefectOperator hd) = 1 ∧
      (∀ n p q, primeHodgeHistoryDefectKernel d ((n, p), (n, q)) ≠ 0) :=
  ⟨primeHodgeHistoryDefectOperator_isPositive hd,
    primeHodgeHistoryDefectOperator_memSchattenClass_one hd,
    opTrace_primeHodgeHistoryDefectOperator hd,
    traceNorm_primeHodgeHistoryDefectOperator hd,
    fun n p q => primeHodgeHistoryDefectKernel_sameHistory_ne_zero hd n p q⟩

/-- Closed, hypothesis-free unit-aperture realization of the pre-divisor prime--history defect. -/
noncomputable def primeHodgeHistoryIntegralNuclearDefectT :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  primeHodgeHistoryDefectOperator (d := 1) zero_lt_one

/-- Unconditional capstone for the single object `T`: positive, Schatten-one, integral trace,
unit trace norm, prime-mixed on every history fibre, with exact unit history flux. -/
theorem primeHodgeHistoryIntegralNuclearDefect_closed :
    primeHodgeHistoryIntegralNuclearDefectT.IsPositive ∧
      MemSchattenClass 1 primeHodgeHistoryIntegralNuclearDefectT ∧
      ContinuousLinearMap.opTrace primeHodgeHistoryIntegralNuclearDefectT = 1 ∧
      traceNorm PrimeHodgeHistoryHilbert primeHodgeHistoryIntegralNuclearDefectT = 1 ∧
      (∀ n p q, primeHodgeHistoryDefectKernel 1 ((n, p), (n, q)) ≠ 0) ∧
      (∑' n, PrimeHodgeHistory.w n) = 1 ∧
      (∀ n, (∑' kp : PrimeHodgeHistoryIndex,
        primeHodgeHistoryDiagonalWeight 1 (kp.1 + n, kp.2)) = PrimeHodgeHistory.m n) := by
  have h := primeHodgeHistoryIntegralNuclearDefect (d := 1) zero_lt_one
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
    PrimeHodgeHistory.tsum_w,
    fun n => tsum_primeHodgeHistoryDiagonalWeight_shift zero_lt_one n⟩

end
end RHTower

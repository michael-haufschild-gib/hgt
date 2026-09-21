import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointRVMQuarticIncidence
import GaloisForLFunctions.RHTower.PrimeIndexedRVMSourceUnitaryNoGo
import GaloisForLFunctions.RHTower.TraceClassCyclicity
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import GaloisForLFunctions.HTGeometry.SchattenHolder

/-!
# Cubic trace of the quartically admitted K-RVM carrier

The finite moment head, positive reciprocal RVM tail, and cofinal triangle reserve form the
literal quartically admitted carrier.  This file computes its cubic ordinary trace without a
spectral approximation.  The trace is strictly positive: diagonal-tail and mixed terms are
nonnegative, while the retained cofinal triangle contributes a strictly positive cubic return.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

private theorem memSchattenClass_one_mul_of_hilbertSchmidt
    {S T : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert}
    (hS : S.IsHilbertSchmidt) (hT : T.IsHilbertSchmidt) :
    MemSchattenClass 1 (S * T) := by
  have hrect := memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hT hS
  exact (memRectSchattenClass_iff_memSchattenClass 1 (S ∘L T)).mp hrect

private theorem memSchattenClass_one_add'
    {S T : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert}
    (hS : MemSchattenClass 1 S) (hT : MemSchattenClass 1 T) :
    MemSchattenClass 1 (S + T) :=
  memSchattenClass_one_add (hS.isCompactOperator one_pos)
    (hT.isCompactOperator one_pos) hS hT

private theorem opTrace_eq_tsum_basis_of_memSchattenClass_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T)
    {ι : Type*} (b : HilbertBasis ι ℂ H) :
    opTrace T = ∑' i, inner ℂ (b i) (T (b i)) := by
  obtain ⟨A, B, hA, hB, hfac⟩ := hT.one_isTraceClass
  rw [hfac]
  exact ContinuousLinearMap.opTrace_comp_eq_tsum_basis hA hB b

/-- The cubic trace of a reciprocal RVM diagonal plus a zero-diagonal Hilbert--Schmidt carrier.
The three `A²B` cyclic terms vanish, and the three `AB²` cyclic terms agree. -/
private theorem opTrace_routeKRVMTail_add_cube
    (s : Finset Nat.Primes) (B : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert)
    (hBHS : B.IsHilbertSchmidt)
    (hBdiag : ∀ p : Nat.Primes,
      inner ℂ (routeKPrimeBasis p) (B (routeKPrimeBasis p)) = 0) :
    opTrace ((routeKRVMTailOperator s + B) ^ 3) =
      opTrace (routeKRVMTailOperator s ^ 3) +
        3 * opTrace (routeKRVMTailOperator s * B ^ 2) + opTrace (B ^ 3) := by
  let A := routeKRVMTailOperator s
  let T₀ := (A * A) * B + A * (B * B)
  let T₁ := (A * B) * A + (B * A) * B
  let T₂ := (B * A) * A + (B * B) * A
  have hA : A.IsHilbertSchmidt := routeKRVMTailOperator_isHilbertSchmidt s
  have hA2HS : (A * A).IsHilbertSchmidt := hA.comp_left A
  have hAA : MemSchattenClass 1 (A * A) :=
    memSchattenClass_one_mul_of_hilbertSchmidt hA hA
  have hAB : MemSchattenClass 1 (A * B) :=
    memSchattenClass_one_mul_of_hilbertSchmidt hA hBHS
  have hBA : MemSchattenClass 1 (B * A) :=
    memSchattenClass_one_mul_of_hilbertSchmidt hBHS hA
  have hBB : MemSchattenClass 1 (B * B) :=
    memSchattenClass_one_mul_of_hilbertSchmidt hBHS hBHS
  have hAAA : MemSchattenClass 1 ((A * A) * A) := by
    simpa only [ContinuousLinearMap.mul_def] using memSchattenClass_one_comp_right hAA A
  have hBBB : MemSchattenClass 1 ((B * B) * B) := by
    simpa only [ContinuousLinearMap.mul_def] using memSchattenClass_one_comp_right hBB B
  have hAAB : MemSchattenClass 1 ((A * A) * B) := by
    simpa only [ContinuousLinearMap.mul_def] using memSchattenClass_one_comp_right hAA B
  have hABA : MemSchattenClass 1 ((A * B) * A) := by
    simpa only [ContinuousLinearMap.mul_def] using memSchattenClass_one_comp_right hAB A
  have hBAA : MemSchattenClass 1 ((B * A) * A) := by
    simpa only [ContinuousLinearMap.mul_def] using memSchattenClass_one_comp_right hBA A
  have hABB : MemSchattenClass 1 (A * (B * B)) := by
    simpa only [ContinuousLinearMap.mul_def] using memSchattenClass_one_comp_left hBB A
  have hBAB : MemSchattenClass 1 ((B * A) * B) := by
    simpa only [ContinuousLinearMap.mul_def] using memSchattenClass_one_comp_right hBA B
  have hBBA : MemSchattenClass 1 ((B * B) * A) := by
    simpa only [ContinuousLinearMap.mul_def] using memSchattenClass_one_comp_right hBB A
  have hT₀ : MemSchattenClass 1 T₀ := memSchattenClass_one_add' hAAB hABB
  have hT₁ : MemSchattenClass 1 T₁ := memSchattenClass_one_add' hABA hBAB
  have hT₂ : MemSchattenClass 1 T₂ := memSchattenClass_one_add' hBAA hBBA
  have hAABzero : opTrace ((A * A) * B) = 0 := by
    have hdiag : ∀ p : Nat.Primes,
        inner ℂ (routeKPrimeBasis p) (((A * A) ∘SL B) (routeKPrimeBasis p)) = 0 := by
      intro p
      rw [ContinuousLinearMap.inner_comp_apply]
      have hAsa : ContinuousLinearMap.adjoint A = A := by
        dsimp only [A]
        exact (routeKRVMTailOperator_isSelfAdjoint s).adjoint_eq
      have hA2sa : ContinuousLinearMap.adjoint (A * A) = A * A := by
        calc
          ContinuousLinearMap.adjoint (A * A) =
              ContinuousLinearMap.adjoint A ∘SL ContinuousLinearMap.adjoint A := by
            change ContinuousLinearMap.adjoint (A ∘SL A) = _
            exact ContinuousLinearMap.adjoint_comp A A
          _ = A * A := by
            change ContinuousLinearMap.adjoint A ∘SL ContinuousLinearMap.adjoint A = A ∘SL A
            rw [hAsa]
      rw [hA2sa, show A * A = A ^ 2 by rfl,
        routeKRVMTailOperator_pow_basis, inner_smul_left]
      simp [hBdiag]
    change opTrace ((A * A) ∘SL B) = 0
    rw [ContinuousLinearMap.opTrace_comp_eq_tsum_basis hA2HS hBHS
      (HilbertSchmidt.lpBasis Nat.Primes)]
    calc
      ∑' p, inner ℂ ((HilbertSchmidt.lpBasis Nat.Primes) p)
          (((A * A) ∘SL B) ((HilbertSchmidt.lpBasis Nat.Primes) p)) = ∑' _ : Nat.Primes, 0 := by
        apply tsum_congr
        intro p
        rw [HilbertSchmidt.lpBasis_apply]
        exact hdiag p
      _ = 0 := tsum_zero
  have htraceAAB_ABA : opTrace ((A * A) * B) = opTrace ((A * B) * A) := by
    have hcyc := hAB.one_opTrace_comp_comm A
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hcyc
  have htraceAAB_BAA : opTrace ((A * A) * B) = opTrace ((B * A) * A) := by
    have hcyc := hAA.one_opTrace_comp_comm B
    calc
      opTrace ((A * A) * B) = opTrace (B * (A * A)) := by
        simpa only [ContinuousLinearMap.mul_def] using hcyc.symm
      _ = opTrace ((B * A) * A) := by rw [mul_assoc]
  have htraceABB_BAB : opTrace (A * (B * B)) = opTrace ((B * A) * B) := by
    have hcyc := hAB.one_opTrace_comp_comm B
    calc
      opTrace (A * (B * B)) = opTrace ((A * B) * B) := by rw [mul_assoc]
      _ = opTrace (B * (A * B)) := by
        simpa only [ContinuousLinearMap.mul_def] using hcyc.symm
      _ = opTrace ((B * A) * B) := by rw [mul_assoc]
  have htraceABB_BBA : opTrace (A * (B * B)) = opTrace ((B * B) * A) := by
    have hcyc := hBB.one_opTrace_comp_comm A
    simpa only [ContinuousLinearMap.mul_def] using hcyc
  have htraceT₀ : opTrace T₀ = opTrace (A * (B * B)) := by
    rw [show opTrace T₀ = opTrace ((A * A) * B) + opTrace (A * (B * B)) by
      exact opTrace_add_of_memSchattenClass_one hAAB hABB, hAABzero, zero_add]
  have htraceT₁ : opTrace T₁ = opTrace (A * (B * B)) := by
    rw [show opTrace T₁ = opTrace ((A * B) * A) + opTrace ((B * A) * B) by
      exact opTrace_add_of_memSchattenClass_one hABA hBAB,
      ← htraceAAB_ABA, hAABzero, zero_add, ← htraceABB_BAB]
  have htraceT₂ : opTrace T₂ = opTrace (A * (B * B)) := by
    rw [show opTrace T₂ = opTrace ((B * A) * A) + opTrace ((B * B) * A) by
      exact opTrace_add_of_memSchattenClass_one hBAA hBBA,
      ← htraceAAB_BAA, hAABzero, zero_add, ← htraceABB_BBA]
  have hcube : (A + B) ^ 3 = ((A * A) * A + (B * B) * B) + T₀ + T₁ + T₂ := by
    simp only [pow_succ]
    dsimp only [T₀, T₁, T₂]
    noncomm_ring
  have hbase : MemSchattenClass 1 ((A * A) * A + (B * B) * B) :=
    memSchattenClass_one_add' hAAA hBBB
  have hbaseT₀ : MemSchattenClass 1 (((A * A) * A + (B * B) * B) + T₀) :=
    memSchattenClass_one_add' hbase hT₀
  have hbaseT₀T₁ : MemSchattenClass 1 ((((A * A) * A + (B * B) * B) + T₀) + T₁) :=
    memSchattenClass_one_add' hbaseT₀ hT₁
  change opTrace ((A + B) ^ 3) = opTrace (A ^ 3) +
    3 * opTrace (A * B ^ 2) + opTrace (B ^ 3)
  rw [hcube, opTrace_add_of_memSchattenClass_one hbaseT₀T₁ hT₂, htraceT₂,
    opTrace_add_of_memSchattenClass_one hbaseT₀ hT₁, htraceT₁,
    opTrace_add_of_memSchattenClass_one hbase hT₀, htraceT₀,
    opTrace_add_of_memSchattenClass_one hAAA hBBB]
  simp only [pow_succ, pow_zero, one_mul, ContinuousLinearMap.mul_def]
  ring

private theorem re_inner_routeKRVMTailOperator_cube_nonneg
    (s : Finset Nat.Primes) (p : Nat.Primes) :
    0 ≤ (inner ℂ (routeKPrimeBasis p)
      ((routeKRVMTailOperator s ^ 3) (routeKPrimeBasis p))).re := by
  rw [routeKRVMTailOperator_pow_basis]
  rw [inner_smul_right]
  have hunit : inner ℂ (routeKPrimeBasis p) (routeKPrimeBasis p) = 1 := by
    simp [routeKPrimeBasis]
  rw [hunit, mul_one]
  change 0 ≤ ((routeKRVMTailWeight s p ^ 3 : ℂ).re)
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  exact pow_nonneg (routeKRVMTailWeight_nonneg s p) 3

private theorem re_opTrace_routeKRVMTailOperator_cube_nonneg
    (s : Finset Nat.Primes) :
    0 ≤ (opTrace (routeKRVMTailOperator s ^ 3)).re := by
  have hA := routeKRVMTailOperator_isHilbertSchmidt s
  have hA2 := hA.comp_left (routeKRVMTailOperator s)
  have hmem : MemSchattenClass 1 (routeKRVMTailOperator s ^ 3) := by
    change MemSchattenClass 1
      ((routeKRVMTailOperator s * routeKRVMTailOperator s) * routeKRVMTailOperator s)
    exact memSchattenClass_one_mul_of_hilbertSchmidt hA2 hA
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one hmem
    (HilbertSchmidt.lpBasis Nat.Primes), Complex.re_tsum]
  · apply tsum_nonneg
    intro p
    rw [HilbertSchmidt.lpBasis_apply]
    exact re_inner_routeKRVMTailOperator_cube_nonneg s p
  · exact hmem.one_summable_inner_diag_basis _

private theorem re_inner_routeKRVMTailOperator_mul_sq_nonneg
    (s : Finset Nat.Primes) (B : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert)
    (hB : IsSelfAdjoint B) (p : Nat.Primes) :
    0 ≤ (inner ℂ (routeKPrimeBasis p)
      ((routeKRVMTailOperator s * B ^ 2) (routeKPrimeBasis p))).re := by
  rw [show routeKRVMTailOperator s * B ^ 2 =
      routeKRVMTailOperator s ∘L B ^ 2 by rfl,
    ContinuousLinearMap.inner_comp_apply]
  have hA : ContinuousLinearMap.adjoint (routeKRVMTailOperator s) =
      routeKRVMTailOperator s :=
    (routeKRVMTailOperator_isSelfAdjoint s).adjoint_eq
  have hBadj : ContinuousLinearMap.adjoint B = B := hB.adjoint_eq
  rw [hA, routeKRVMTailOperator_basis, inner_smul_left]
  rw [show B ^ 2 = B ∘SL B by rfl, ContinuousLinearMap.inner_comp_apply, hBadj]
  simp
  norm_cast
  exact mul_nonneg (routeKRVMTailWeight_nonneg s p) (sq_nonneg _)

private theorem re_opTrace_routeKRVMTailOperator_mul_sq_nonneg
    (s : Finset Nat.Primes) (B : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert)
    (hB : IsSelfAdjoint B) (hBHS : B.IsHilbertSchmidt) :
    0 ≤ (opTrace (routeKRVMTailOperator s * B ^ 2)).re := by
  have hB2 : (B ^ 2).IsHilbertSchmidt := by
    change (B * B).IsHilbertSchmidt
    exact hBHS.comp_left B
  have hmem : MemSchattenClass 1 (routeKRVMTailOperator s * B ^ 2) := by
    change MemSchattenClass 1 (routeKRVMTailOperator s * (B * B))
    exact memSchattenClass_one_mul_of_hilbertSchmidt
      (routeKRVMTailOperator_isHilbertSchmidt s) hB2
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one hmem
      (HilbertSchmidt.lpBasis Nat.Primes), Complex.re_tsum]
  · apply tsum_nonneg
    intro p
    rw [HilbertSchmidt.lpBasis_apply]
    exact re_inner_routeKRVMTailOperator_mul_sq_nonneg s B hB p
  · exact hmem.one_summable_inner_diag_basis _

private theorem routeKQuarticCycleReserve_diagonal_zero (p : Nat.Primes) :
    inner ℂ (routeKPrimeBasis p)
      (routeKQuarticCycleReserve (routeKPrimeBasis p)) = 0 := by
  rw [routeKQuarticCycleReserve, smul_apply, inner_smul_right,
    routeKCofinalTriangleNuclearCarrierFrom_diagonal_zero, mul_zero]

/-- Scaling preserves the cofinal triangle's strictly positive cubic trace. -/
theorem re_opTrace_routeKQuarticCycleReserve_cube_pos :
    0 < (opTrace (routeKQuarticCycleReserve ^ 3)).re := by
  rw [routeKQuarticCycleReserve]
  have h := re_opTrace_routeKCofinalTriangleNuclearCarrierFrom_cube_pos
    routeKQuarticReserveParameters.N
  have hcube :
      routeKCofinalTriangleNuclearCarrierFrom routeKQuarticReserveParameters.N ^ 3 =
        routeKCofinalTriangleNuclearCarrierFrom routeKQuarticReserveParameters.N ∘L
          (routeKCofinalTriangleNuclearCarrierFrom routeKQuarticReserveParameters.N ∘L
            routeKCofinalTriangleNuclearCarrierFrom routeKQuarticReserveParameters.N) := by
    ext x
    rfl
  rw [smul_pow, opTrace_smul]
  change 0 < (((routeKQuarticReserveParameters.delta : ℂ) ^ 3) *
    opTrace (routeKCofinalTriangleNuclearCarrierFrom routeKQuarticReserveParameters.N ^ 3)).re
  have hcubed : 0 < routeKQuarticReserveParameters.delta ^ 3 :=
    pow_pos routeKQuarticReserveParameters.hdelta 3
  have h' : 0 < (opTrace
      (routeKCofinalTriangleNuclearCarrierFrom routeKQuarticReserveParameters.N ^ 3)).re := by
    rw [hcube]
    exact h
  rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_pos hcubed h'

/-- The actual cofinite RVM-plus-cycle reserve has strictly positive cubic trace. -/
theorem re_opTrace_routeKQuarticReserve_cube_pos :
    0 < (opTrace (routeKQuarticReserve ^ 3)).re := by
  have hformula := opTrace_routeKRVMTail_add_cube
    (routeKInitialPrimeFinset routeKQuarticReserveParameters.N)
    routeKQuarticCycleReserve routeKQuarticCycleReserve_isHilbertSchmidt
    routeKQuarticCycleReserve_diagonal_zero
  change 0 < (opTrace
    ((routeKRVMTailOperator (routeKInitialPrimeFinset routeKQuarticReserveParameters.N) +
      routeKQuarticCycleReserve) ^ 3)).re
  rw [hformula]
  have hdiag : 0 ≤ (opTrace
      (routeKRVMTailOperator (routeKInitialPrimeFinset routeKQuarticReserveParameters.N) ^ 3)).re :=
    re_opTrace_routeKRVMTailOperator_cube_nonneg
      (routeKInitialPrimeFinset routeKQuarticReserveParameters.N)
  have hcross : 0 ≤ (opTrace
      (routeKRVMTailOperator (routeKInitialPrimeFinset routeKQuarticReserveParameters.N) *
        routeKQuarticCycleReserve ^ 2)).re := by
    apply re_opTrace_routeKRVMTailOperator_mul_sq_nonneg
      (routeKInitialPrimeFinset routeKQuarticReserveParameters.N)
      routeKQuarticCycleReserve
    · rw [routeKQuarticCycleReserve]
      apply IsSelfAdjoint.smul
      · simp [IsSelfAdjoint]
      · exact routeKCofinalTriangleNuclearCarrierFrom_isSelfAdjoint _
    · exact routeKQuarticCycleReserve_isHilbertSchmidt
  have hcycle := re_opTrace_routeKQuarticCycleReserve_cube_pos
  rw [Complex.add_re, Complex.add_re, Complex.mul_re]
  norm_num
  linarith

private theorem routeKQuarticHead_pow_basis
    (n : ℕ) (p : Nat.Primes) :
    (routeKQuarticHead ^ n) (routeKPrimeBasis p) =
      (twoLevelPrimeWeight routeKQuarticResidualMass routeKQuarticResidualEnergy
        routeKQuarticReserveParameters.N p ^ n : ℂ) • routeKPrimeBasis p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply,
        routeKQuarticHead_basis, map_smul, ih, smul_smul]
      congr 1
      norm_cast
      ring

private theorem re_inner_routeKQuarticHead_cube_nonneg (p : Nat.Primes) :
    0 ≤ (inner ℂ (routeKPrimeBasis p)
      ((routeKQuarticHead ^ 3) (routeKPrimeBasis p))).re := by
  rw [routeKQuarticHead_pow_basis]
  rw [inner_smul_right]
  have hunit : inner ℂ (routeKPrimeBasis p) (routeKPrimeBasis p) = 1 := by
    simp [routeKPrimeBasis]
  rw [hunit, mul_one]
  change 0 ≤ ((twoLevelPrimeWeight routeKQuarticResidualMass routeKQuarticResidualEnergy
    routeKQuarticReserveParameters.N p ^ 3 : ℂ).re)
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  exact pow_nonneg (Real.sqrt_nonneg _) 3

/-- The finite two-level head has nonnegative cubic trace. -/
theorem re_opTrace_routeKQuarticHead_cube_nonneg :
    0 ≤ (opTrace (routeKQuarticHead ^ 3)).re := by
  have hHS := routeKQuarticHead_isHilbertSchmidt
  have hHSsq := hHS.comp_left routeKQuarticHead
  have hmem : MemSchattenClass 1 (routeKQuarticHead ^ 3) := by
    change MemSchattenClass 1
      ((routeKQuarticHead * routeKQuarticHead) * routeKQuarticHead)
    exact memSchattenClass_one_mul_of_hilbertSchmidt hHSsq hHS
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one hmem
      (HilbertSchmidt.lpBasis Nat.Primes), Complex.re_tsum]
  · apply tsum_nonneg
    intro p
    rw [HilbertSchmidt.lpBasis_apply]
    exact re_inner_routeKQuarticHead_cube_nonneg p
  · exact hmem.one_summable_inner_diag_basis _

/-- The literal quartically admitted K-RVM carrier has strictly positive cubic ordinary trace. -/
theorem re_opTrace_routeKQuarticallyAdmittedOperator_cube_pos :
    0 < (opTrace (routeKQuarticallyAdmittedOperator ^ 3)).re := by
  rw [routeKQuarticallyAdmittedOperator_cube]
  have hHmem : MemSchattenClass 1 (routeKQuarticHead ^ 3) :=
    memSchattenClass_one_mul_of_hilbertSchmidt
      (routeKQuarticHead_isHilbertSchmidt.comp_left routeKQuarticHead)
      routeKQuarticHead_isHilbertSchmidt
  have hRmem : MemSchattenClass 1 (routeKQuarticReserve ^ 3) :=
    memSchattenClass_one_mul_of_hilbertSchmidt
      (routeKQuarticReserve_isHilbertSchmidt.comp_left routeKQuarticReserve)
      routeKQuarticReserve_isHilbertSchmidt
  rw [opTrace_add_of_memSchattenClass_one hHmem hRmem, Complex.add_re]
  linarith [re_opTrace_routeKQuarticHead_cube_nonneg,
    re_opTrace_routeKQuarticReserve_cube_pos]

/-- The cubic trace of the literal quartically admitted K-RVM carrier cannot vanish. -/
theorem opTrace_routeKQuarticallyAdmittedOperator_cube_ne_zero :
    opTrace (routeKQuarticallyAdmittedOperator ^ 3) ≠ 0 := by
  intro hzero
  have hpos := re_opTrace_routeKQuarticallyAdmittedOperator_cube_pos
  rw [hzero] at hpos
  norm_num at hpos

end RHTower

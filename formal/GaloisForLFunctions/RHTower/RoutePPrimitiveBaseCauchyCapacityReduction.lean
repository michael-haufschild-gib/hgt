import GaloisForLFunctions.RHTower.RoutePPrimitiveHankelDyadicCalderonReconstruction
import GaloisForLFunctions.RHTower.RoutePPrimitiveCollisionCapacityTerminal

/-!
# Route P primitive base Cauchy capacity reduction

P-G180 reconstructs the undifferenced primitive Laplace column from the collision feature by a
dyadic Calderon telescope.  This module transports the exact trace-capacity audit to that simpler
base carrier.  Its Cauchy-cube matrix is a principal compression of the doubled Schur cube and is
therefore positive semidefinite.  Its diagonal is `1 / (4 a^3)`, so the full primitive source
budget is exactly `216 / 115` times the collision budget and remains strictly below `2`.

Every strict-right Xi zero has `0 < a <= 1/2` and therefore costs at least `2` in the base carrier.
Consequently the base trace-capacity law is again equivalent to RH.  Removing the reconstructive
dyadic defect loses no separating power: the remaining arithmetic producer may be sought directly
on one coefficient-faithful Cauchy cube, before Gamma--Euler continuation to the Xi divisor.
-/

open Complex Matrix
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Undifferenced Cauchy-cube kernel underlying the Route P collision defect. -/
def routePBaseCauchyCubicKernel (R a b kappa : ℝ) : ℂ :=
  2 * (R : ℂ) ^ 3 / routePCollisionPairFrequency R a b kappa ^ 3

/-- Finite base Cauchy-cube packet. -/
def routePBaseCauchyCubicKernelMatrix {N : ℕ}
    (R : ℝ) (a kappa : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => routePBaseCauchyCubicKernel R (a i) (a j) (kappa j - kappa i)

/-- The base packet is the left-scale principal compression of the doubled Schur cube. -/
theorem routePBaseCauchyCubicKernelMatrix_eq_submatrix {N : ℕ}
    (R : ℝ) (a kappa : Fin N → ℝ) :
    routePBaseCauchyCubicKernelMatrix R a kappa =
      (routePCollisionDoubledCubicGram R a kappa).submatrix Sum.inl Sum.inl := by
  ext i j
  simp only [Matrix.submatrix_apply]
  rw [routePBaseCauchyCubicKernelMatrix, routePBaseCauchyCubicKernel,
    routePCollisionDoubledCubicGram_apply, routePCollisionDoubledNode_pair_ll]

/-- Every finite undifferenced base packet is positive semidefinite. -/
theorem routePBaseCauchyCubicKernelMatrix_posSemidef
    {N : ℕ} {R : ℝ} {a kappa : Fin N → ℝ}
    (hR : 0 < R) (ha : ∀ i, 0 < a i) :
    (routePBaseCauchyCubicKernelMatrix R a kappa).PosSemidef := by
  rw [routePBaseCauchyCubicKernelMatrix_eq_submatrix]
  exact (routePCollisionDoubledCubicGram_posSemidef hR ha).submatrix Sum.inl

/-- Exact base diagonal, independent of boundary clock and ordinate. -/
theorem routePBaseCauchyCubicKernel_diagonal
    {R a : ℝ} (hR : 0 < R) (ha : 0 < a) :
    routePBaseCauchyCubicKernel R a a 0 =
      (((1 : ℝ) / (4 * a ^ 3) : ℝ) : ℂ) := by
  simp only [routePBaseCauchyCubicKernel, routePCollisionPairFrequency]
  push_cast
  field_simp [hR.ne', ha.ne']
  ring

/-- Exact base trace of every finite packet. -/
theorem trace_routePBaseCauchyCubicKernelMatrix
    {N : ℕ} {R : ℝ} {a kappa : Fin N → ℝ}
    (hR : 0 < R) (ha : ∀ i, 0 < a i) :
    (routePBaseCauchyCubicKernelMatrix R a kappa).trace =
      ∑ i : Fin N, ((((1 : ℝ) / (4 * (a i) ^ 3) : ℝ) : ℂ)) := by
  apply Finset.sum_congr rfl
  intro i _hi
  change routePBaseCauchyCubicKernel R (a i) (a i) (kappa i - kappa i) = _
  rw [sub_self]
  exact routePBaseCauchyCubicKernel_diagonal hR (ha i)

/-- Base Cauchy-cube kernel placed on a finite primitive Euler packet. -/
def routePPrimitiveBaseCauchyCubicKernelMatrix {N : ℕ}
    (R : ℝ) (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  routePPrimitiveCollisionScalingMatrix pe *
    routePBaseCauchyCubicKernelMatrix R
      (fun i => xiGammaEulerPrimitiveLogFrequency (pe i)) kappa *
    (routePPrimitiveCollisionScalingMatrix pe)ᴴ

theorem routePPrimitiveBaseCauchyCubicKernelMatrix_posSemidef
    {N : ℕ} {R : ℝ} {pe : Fin N → Nat.Primes × ℕ} {kappa : Fin N → ℝ}
    (hR : 0 < R) :
    (routePPrimitiveBaseCauchyCubicKernelMatrix R pe kappa).PosSemidef := by
  exact (routePBaseCauchyCubicKernelMatrix_posSemidef hR
    (fun i => xiGammaEulerPrimitiveLogFrequency_pos (pe i))).mul_mul_conjTranspose_same
      (routePPrimitiveCollisionScalingMatrix pe)

theorem routePPrimitiveBaseCauchyCubicKernelMatrix_apply
    {N : ℕ} (R : ℝ) (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (i j : Fin N) :
    routePPrimitiveBaseCauchyCubicKernelMatrix R pe kappa i j =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (pe i)) *
        routePBaseCauchyCubicKernel R
          (xiGammaEulerPrimitiveLogFrequency (pe i))
          (xiGammaEulerPrimitiveLogFrequency (pe j))
          (kappa j - kappa i) *
        star (finiteVonMangoldtDepthOneAmplitude
          (xiGammaEulerValuationNat (pe j))) := by
  simp [routePPrimitiveBaseCauchyCubicKernelMatrix,
    routePPrimitiveCollisionScalingMatrix, Matrix.diagonal_mul,
    Matrix.mul_diagonal, routePBaseCauchyCubicKernelMatrix]

/-- Literal primitive base weight.  It is `216/115` times the collision-defect weight. -/
def routePPrimitiveBaseCauchyCubicWeight (pe : Nat.Primes × ℕ) : ℝ :=
  (216 / 115 : ℝ) * xiGammaEulerPrimitiveCubicLogMomentWeight pe

theorem routePPrimitiveBaseCauchyCubicWeight_nonneg
    (pe : Nat.Primes × ℕ) : 0 ≤ routePPrimitiveBaseCauchyCubicWeight pe := by
  exact mul_nonneg (by norm_num) (xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg pe)

theorem summable_routePPrimitiveBaseCauchyCubicWeight :
    Summable routePPrimitiveBaseCauchyCubicWeight := by
  exact summable_xiGammaEulerPrimitiveCubicLogMomentWeight.mul_left (216 / 115 : ℝ)

/-- Exact primitive diagonal after removing the dyadic defect. -/
theorem routePPrimitiveBaseCauchyCubicKernelMatrix_diagonal
    {N : ℕ} {R : ℝ} (hR : 0 < R)
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) (i : Fin N) :
    routePPrimitiveBaseCauchyCubicKernelMatrix R pe kappa i i =
      (routePPrimitiveBaseCauchyCubicWeight (pe i) : ℂ) := by
  rw [routePPrimitiveBaseCauchyCubicKernelMatrix_apply]
  rw [sub_self, routePBaseCauchyCubicKernel_diagonal hR
    (xiGammaEulerPrimitiveLogFrequency_pos (pe i))]
  have hc := routePPrimitiveCollisionCubicKernelMatrix_diagonal hR pe kappa i
  rw [routePPrimitiveCollisionCubicKernelMatrix_apply, sub_self,
    routePCollisionCubicKernel_diagonal hR
      (xiGammaEulerPrimitiveLogFrequency_pos (pe i))] at hc
  rw [routePPrimitiveBaseCauchyCubicWeight]
  push_cast
  rw [← hc]
  push_cast
  have hfrequency : xiGammaEulerPrimitiveLogFrequency (pe i) ≠ 0 :=
    (xiGammaEulerPrimitiveLogFrequency_pos (pe i)).ne'
  field_simp [hfrequency]
  ring

theorem trace_routePPrimitiveBaseCauchyCubicKernelMatrix
    {N : ℕ} {R : ℝ} (hR : 0 < R)
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    (routePPrimitiveBaseCauchyCubicKernelMatrix R pe kappa).trace =
      ∑ i : Fin N, (routePPrimitiveBaseCauchyCubicWeight (pe i) : ℂ) := by
  apply Finset.sum_congr rfl
  intro i _hi
  exact routePPrimitiveBaseCauchyCubicKernelMatrix_diagonal hR pe kappa i

/-- Full primitive Euler trace budget for the undifferenced base carrier. -/
def routePPrimitiveBaseCauchyCubicTraceBudget : ℝ :=
  ∑' pe : Nat.Primes × ℕ, routePPrimitiveBaseCauchyCubicWeight pe

theorem routePPrimitiveBaseCauchyCubicTraceBudget_eq :
    routePPrimitiveBaseCauchyCubicTraceBudget =
      (216 / 115 : ℝ) * routePPrimitiveCollisionCubicTraceBudget := by
  rw [routePPrimitiveBaseCauchyCubicTraceBudget,
    routePPrimitiveCollisionCubicTraceBudget, ← tsum_mul_left]
  rfl

theorem routePPrimitiveBaseCauchyCubicTraceBudget_nonneg :
    0 ≤ routePPrimitiveBaseCauchyCubicTraceBudget := by
  exact tsum_nonneg routePPrimitiveBaseCauchyCubicWeight_nonneg

/-- The reconstructed base source remains strictly below one strict-right-zero quantum. -/
theorem routePPrimitiveBaseCauchyCubicTraceBudget_lt_quantum :
    routePPrimitiveBaseCauchyCubicTraceBudget < 2 := by
  rw [routePPrimitiveBaseCauchyCubicTraceBudget_eq]
  nlinarith [routePPrimitiveCollisionCubicTraceBudget_lt_quantum]

theorem re_trace_routePPrimitiveBaseCauchyCubicKernelMatrix_le_budget
    {N : ℕ} {R : ℝ} (hR : 0 < R)
    (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) :
    (routePPrimitiveBaseCauchyCubicKernelMatrix R pe kappa).trace.re ≤
      routePPrimitiveBaseCauchyCubicTraceBudget := by
  rw [trace_routePPrimitiveBaseCauchyCubicKernelMatrix hR pe kappa]
  have hsub :=
    (summable_routePPrimitiveBaseCauchyCubicWeight.comp_injective hpe).tsum_le_tsum_of_inj
      pe hpe
      (fun q _hq => routePPrimitiveBaseCauchyCubicWeight_nonneg q)
      (fun i => le_rfl)
      summable_routePPrimitiveBaseCauchyCubicWeight
  simpa [routePPrimitiveBaseCauchyCubicTraceBudget] using hsub

/-- Base Cauchy-cube Gram on actual strict-right Xi copies. -/
def routePStrictRightZeroBaseCauchyCubicKernelMatrix {N : ℕ}
    (q : Fin N → XiRightZeroCopy) : Matrix (Fin N) (Fin N) ℂ :=
  routePBaseCauchyCubicKernelMatrix 1
    (fun i => (xiRightCenteredZero (q i)).re)
    (fun i => (xiRightCenteredZero (q i)).im)

theorem routePStrictRightZeroBaseCauchyCubicKernelMatrix_posSemidef
    {N : ℕ} (q : Fin N → XiRightZeroCopy) :
    (routePStrictRightZeroBaseCauchyCubicKernelMatrix q).PosSemidef := by
  exact routePBaseCauchyCubicKernelMatrix_posSemidef (by norm_num)
    (fun i => xiRightCenteredZero_re_pos (q i))

theorem re_trace_routePStrictRightZeroBaseCauchyCubicKernelMatrix
    {N : ℕ} (q : Fin N → XiRightZeroCopy) :
    (routePStrictRightZeroBaseCauchyCubicKernelMatrix q).trace.re =
      ∑ i : Fin N, 1 / (4 * (xiRightCenteredZero (q i)).re ^ 3) := by
  have h := trace_routePBaseCauchyCubicKernelMatrix
    (N := N) (R := 1)
    (a := fun i => (xiRightCenteredZero (q i)).re)
    (kappa := fun i => (xiRightCenteredZero (q i)).im)
    (by norm_num) (fun i => xiRightCenteredZero_re_pos (q i))
  change (routePStrictRightZeroBaseCauchyCubicKernelMatrix q).trace = _ at h
  rw [h]
  change Complex.reCLM (∑ i : Fin N,
      (((1 / (4 * (xiRightCenteredZero (q i)).re ^ 3)) : ℝ) : ℂ)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  norm_cast

/-- One strict-right zero costs at least two units in the reconstructed base carrier. -/
theorem routePStrictRightZeroBaseCauchyCubicCharge_ge_two (q : XiRightZeroCopy) :
    2 ≤ 1 / (4 * (xiRightCenteredZero q).re ^ 3) := by
  have ha : 0 < (xiRightCenteredZero q).re := xiRightCenteredZero_re_pos q
  have hhalf : (xiRightCenteredZero q).re ≤ 1 / 2 :=
    le_of_lt (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2
  apply (le_div_iff₀ (mul_pos (by norm_num) (pow_pos ha 3))).2
  have hcube := pow_le_pow_left₀ ha.le hhalf 3
  norm_num at hcube ⊢
  nlinarith

/-- Capacity consequence on the reconstructed base carrier. -/
def RoutePPrimitiveBaseCauchyTraceCapacityLaw : Prop :=
  ∀ {N : ℕ} (q : Fin N → XiRightZeroCopy),
    (routePStrictRightZeroBaseCauchyCubicKernelMatrix q).trace.re ≤
      routePPrimitiveBaseCauchyCubicTraceBudget

/-- **P-G181.** Removing the dyadic defect preserves the exact terminal RH capacity gate. -/
theorem routePPrimitiveBaseCauchyTraceCapacityLaw_iff_riemannHypothesis :
    RoutePPrimitiveBaseCauchyTraceCapacityLaw ↔ RiemannHypothesis := by
  constructor
  · intro hcapacity
    by_contra hRH
    obtain ⟨q⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
    have hcap := hcapacity (N := 1) (fun _ => q)
    rw [re_trace_routePStrictRightZeroBaseCauchyCubicKernelMatrix] at hcap
    simp only [Fin.sum_univ_one] at hcap
    have hquant := routePStrictRightZeroBaseCauchyCubicCharge_ge_two q
    linarith [routePPrimitiveBaseCauchyCubicTraceBudget_lt_quantum]
  · intro hRH N q
    letI : IsEmpty XiRightZeroCopy := by
      constructor
      intro x
      obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH x.1
      have hpos := x.2
      rw [ht] at hpos
      simp at hpos
    letI : IsEmpty (Fin N) := ⟨fun i => isEmptyElim (q i)⟩
    rw [re_trace_routePStrictRightZeroBaseCauchyCubicKernelMatrix]
    simpa using routePPrimitiveBaseCauchyCubicTraceBudget_nonneg

end

end RHTower

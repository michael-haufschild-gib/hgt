import GaloisForLFunctions.RHTower.SelbergMaassPhaseComplexPolarization
import GaloisForLFunctions.RHTower.SelbergMaassPhaseProductLossLimit
import GaloisForLFunctions.RHTower.Sieve.LinearPhaseIntegral
import GaloisForLFunctions.RHTower.SelbergMaassModalMixedLoss

/-!
# Finite Fourier kernel for the weighted Maass phase product

The physical weighted top phase pairing has a finite Fourier expansion.  Complex
phase polarization collapses every finite arithmetic phase family to the actual
complex transfer loss.  Distinct upper-residue channels vanish exactly, leaving
a literal finite same-residue coefficient kernel.  The module proves this
identification only; no sign or spectral conclusion is introduced.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassWeightedPhaseKernel
open GaloisForLFunctions.HTGeometry SelbergMaassCongruenceTrace
open RHTower.Sieve
open SelbergMaassFourierPartial SelbergMaassPhaseProductLossLimit
  SelbergMaassPhaseComplexPolarization SelbergMaassModalMixedLoss
open SelbergMaassCongruenceTrace SelbergMaassPhaseRellich SelbergMaassDilationStress
  SelbergMaassCharacterSeamFlux SelbergMaassTraceEnergy SelbergMaassMean SelbergMaassPhaseStress
  SelbergMaassCongruenceAverage SelbergMaassUnipotentBlocks SelbergMaassCharacterProjection
  SelbergMaassCharacterFourier SelbergMaassInversionGram SelbergMaassUnipotentFourier
  SelbergMaassCharacterGradient SelbergMaassFourier SelbergMaassMixedLoss
  SelbergMaassSliceRigidity SelbergMaassKernelWronskian
noncomputable section

def unitCoordFourierKernel (i j : ℤ) : ℂ :=
  ∫ t in (0 : ℝ)..1, fourierChar (-i) t * ((t : ℂ) * fourierChar j t)

theorem l2Pair_fourierPartialSum_unitCoord_eq_double (f g : ℝ → ℂ) (M : ℕ) :
    l2Pair (fourierPartialSum f M)
      (fun t => (t : ℂ) * fourierPartialSum g M t) =
      ∑ i ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ∑ j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          (starRingEnd ℂ) (l2Pair (fourierChar i) f) *
            l2Pair (fourierChar j) g * unitCoordFourierKernel i j := by
  set S : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ) with hS
  set cf : ℤ → ℂ := fun n => l2Pair (fourierChar n) f with hcf
  set cg : ℤ → ℂ := fun n => l2Pair (fourierChar n) g with hcg
  have hexp : ∀ x : ℝ,
      (starRingEnd ℂ) (fourierPartialSum f M x) *
        ((x : ℂ) * fourierPartialSum g M x) =
      ∑ i ∈ S, ∑ j ∈ S,
        ((starRingEnd ℂ) (cf i) * cg j) *
          (fourierChar (-i) x * ((x : ℂ) * fourierChar j x)) := by
    intro x
    simp only [fourierPartialSum_eq, hS, hcf, hcg, map_sum, map_mul,
      fourierChar_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

  rw [l2Pair, intervalIntegral.integral_congr (fun x _ => hexp x),
    intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [intervalIntegral.integral_const_mul]
      rfl
    · intro j _
      exact Continuous.intervalIntegrable
        (continuous_const.mul ((continuous_fourierChar _).mul
          ((Complex.continuous_ofReal.comp continuous_id).mul (continuous_fourierChar _)))) _ _
  · intro i _
    refine Continuous.intervalIntegrable ?_ _ _
    refine continuous_finsetSum _ fun j _ => ?_
    exact continuous_const.mul ((continuous_fourierChar _).mul
      ((Complex.continuous_ofReal.comp continuous_id).mul (continuous_fourierChar _)))

theorem unitCoordFourierKernel_self (n : ℤ) :
    unitCoordFourierKernel n n = (1 / 2 : ℂ) := by
  unfold unitCoordFourierKernel
  rw [intervalIntegral.integral_congr]
  · have h : (fun t : ℝ => fourierChar (-n) t * ((t : ℂ) * fourierChar n t)) =
        fun t : ℝ => (t : ℂ) := by
      funext t
      calc
        fourierChar (-n) t * ((t : ℂ) * fourierChar n t) =
            (t : ℂ) * (fourierChar (-n) t * fourierChar n t) := by ring
        _ = (t : ℂ) * fourierChar ((-n) + n) t := by rw [fourierChar_add]
        _ = (t : ℂ) := by simp [fourierChar]
    rw [h, intervalIntegral.integral_ofReal, integral_id]
    norm_num
  · intro t _
    rfl

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
  (r s : ZMod (N + 1))

theorem phaseProductPartial_eq_kernel (M : ℕ) :
    phaseProductPartial N f r s M =
      ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          (starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
            unitCoordFourierKernel n m * coefficientMixedLoss N r s f n m 1 := by
  let c : ℝ := ((N + 1 : ℕ) : ℝ)⁻¹ ^ (3 : ℕ) / 2
  let S : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
  let H : PhaseIndex N → ℝ → ℂ := fun i =>
    unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1
  let V : PhaseIndex N → ℝ → ℂ := fun i =>
    unitRescaledVerticalReadout N f (phaseReadout N r s i) 1
  have hH (i : PhaseIndex N) (n : ℤ) :
      l2Pair (fourierChar n) (H i) =
        (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
          phaseReadout N r s i (coefficientVector N f n 1) := by
    exact l2Pair_fourierChar_unitRescaledHorizontalReadout N f
      (phaseReadout N r s i) n (by norm_num : (0 : ℝ) < 1)
  have hV (i : PhaseIndex N) (m : ℤ) :
      l2Pair (fourierChar m) (V i) =
        phaseReadout N r s i (coefficientHeightVector N f m 1) := by
    exact l2Pair_fourierChar_unitRescaledVerticalReadout N f
      (phaseReadout N r s i) m (by norm_num : (0 : ℝ) < 1)
  unfold phaseProductPartial
  change ((c : ℂ) * ∑ i : PhaseIndex N,
    l2Pair (fourierPartialSum (H i) M)
      (fun t => (t : ℂ) * fourierPartialSum (V i) M t)) = _
  simp_rw [l2Pair_fourierPartialSum_unitCoord_eq_double, hH, hV]
  change ((c : ℂ) * ∑ i : PhaseIndex N, ∑ n ∈ S, ∑ m ∈ S,
    (starRingEnd ℂ) ((((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
      phaseReadout N r s i (coefficientVector N f n 1)) *
      phaseReadout N r s i (coefficientHeightVector N f m 1) *
      unitCoordFourierKernel n m) = _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hphase := phaseAverageC_pair N r s
    (coefficientHeightVector N f m 1) (coefficientVector N f n 1)
  unfold phaseAverageC at hphase
  change ((c : ℂ) * ∑ i : PhaseIndex N,
    (starRingEnd ℂ) ((((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
      phaseReadout N r s i (coefficientVector N f n 1)) *
      phaseReadout N r s i (coefficientHeightVector N f m 1) *
      unitCoordFourierKernel n m) = _
  rw [map_mul]
  simp only [map_mul]
  calc
    ((c : ℂ) * ∑ i : PhaseIndex N,
      (starRingEnd ℂ) ((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * (starRingEnd ℂ) Complex.I *
        (starRingEnd ℂ) (phaseReadout N r s i (coefficientVector N f n 1)) *
        phaseReadout N r s i (coefficientHeightVector N f m 1) *
        unitCoordFourierKernel n m) =
      ((c : ℂ) * ∑ i : PhaseIndex N,
        ((starRingEnd ℂ) ((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * (starRingEnd ℂ) Complex.I *
          unitCoordFourierKernel n m) *
          (phaseReadout N r s i (coefficientHeightVector N f m 1) *
            (starRingEnd ℂ) (phaseReadout N r s i (coefficientVector N f n 1)))) := by
        congr 2
        funext i
        ring
    _ = (starRingEnd ℂ) ((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * (starRingEnd ℂ) Complex.I *
        unitCoordFourierKernel n m *
          ((c : ℂ) * ∑ i : PhaseIndex N,
            phaseReadout N r s i (coefficientHeightVector N f m 1) *
              (starRingEnd ℂ) (phaseReadout N r s i (coefficientVector N f n 1))) := by
        rw [← Finset.mul_sum]
        ring
    _ = _ := by
      rw [hphase]
      rfl

theorem phaseProductPartial_eq_sameResidue_kernel (M : ℕ) :
    phaseProductPartial N f r s M =
      ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          if (n : ZMod (N + 1)) = (m : ZMod (N + 1)) then
            (starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
              unitCoordFourierKernel n m * coefficientMixedLoss N r s f n m 1
          else 0 := by
  rw [phaseProductPartial_eq_kernel]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hnm : (n : ZMod (N + 1)) = (m : ZMod (N + 1))
  · simp [hnm]
  · rw [coefficientMixedLoss_eq_zero_of_residue_ne N r s f n m hnm (by norm_num)]
    simp [hnm]

theorem diagonal_weightedKernel_loss_re_eq_zero
    (e : Ioo (0 : ℝ) (1 / 4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (e : ℝ))
    (n : ℤ) :
    ((starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
      unitCoordFourierKernel n n * coefficientMixedLoss N r s g n n 1).re = 0 := by
  let a : ℂ := (starRingEnd ℂ)
    (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I)
  let c : ℂ := coefficientMixedLoss N r s g n n 1
  have h : (a * c).re = 0 := by
    simpa only [a, c] using
      (real_weighted_diagonal_mixed_eq_zero N r s e g n (by norm_num : (0 : ℝ) < 1))
  rw [unitCoordFourierKernel_self]
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hhalf]
  change (a * ((1 / 2 : ℝ) : ℂ) * c).re = 0
  calc
    (a * ((1 / 2 : ℝ) : ℂ) * c).re = ((a * c) * ((1 / 2 : ℝ) : ℂ)).re := by
      congr 1
      ring
    _ = (1 / 2 : ℝ) * (a * c).re := by
      rw [Complex.re_mul_ofReal]
      ring
    _ = 0 := by rw [h]; ring

theorem phaseProductPartial_re_eq_sameResidue_offDiagonal
    (e : Ioo (0 : ℝ) (1 / 4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (e : ℝ))
    (M : ℕ) :
    (phaseProductPartial N g r s M).re =
      (∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ∑ m ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase n,
          if (n : ZMod (N + 1)) = (m : ZMod (N + 1)) then
            (starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
              unitCoordFourierKernel n m * coefficientMixedLoss N r s g n m 1
          else 0).re := by
  let S : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
  let A : ℤ → ℤ → ℂ := fun n m =>
    if (n : ZMod (N + 1)) = (m : ZMod (N + 1)) then
      (starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
        unitCoordFourierKernel n m * coefficientMixedLoss N r s g n m 1
    else 0
  rw [phaseProductPartial_eq_sameResidue_kernel]
  change (∑ n ∈ S, ∑ m ∈ S, A n m).re =
    (∑ n ∈ S, ∑ m ∈ S.erase n, A n m).re
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_erase_add S (fun m => (A n m).re) hn]
  have hdiag : (A n n).re = 0 := by
    unfold A
    simp only [if_pos]
    exact diagonal_weightedKernel_loss_re_eq_zero N r s e g n
  rw [hdiag]
  ring

theorem tendsto_phaseProductPartial_re_sameResidue_offDiagonal
    (e : Ioo (0 : ℝ) (1 / 4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (e : ℝ)) :
    Tendsto (fun M : ℕ =>
      (∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ∑ m ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase n,
          if (n : ZMod (N + 1)) = (m : ZMod (N + 1)) then
            (starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
              unitCoordFourierKernel n m * coefficientMixedLoss N r s g n m 1
          else 0).re) atTop
      (nhds (∫ t in (0 : ℝ)..1, t * lossPair N r s
        (sourceDerivative N g 1 (ofComplex (point (t * (N + 1 : ℕ)) 1)))
        (sourceDerivative N g Complex.I (ofComplex (point (t * (N + 1 : ℕ)) 1))))) := by
  have hlim : Tendsto (fun M : ℕ => (phaseProductPartial N g r s M).re) atTop
      (nhds ((phaseProductExact N g r s).re)) :=
    Complex.continuous_re.tendsto _ |>.comp (tendsto_phaseProductPartial N g r s)
  rw [phaseProductExact_re_eq_unitLossMoment N g r s] at hlim
  refine hlim.congr' (Filter.Eventually.of_forall ?_)
  intro M
  exact phaseProductPartial_re_eq_sameResidue_offDiagonal N r s e g M

theorem unitCoordFourierKernel_offDiagonal (i j : ℤ) (hij : i ≠ j) :
    unitCoordFourierKernel i j =
      1 / (2 * (Real.pi : ℂ) * Complex.I * ((j - i : ℤ) : ℂ)) := by
  let k : ℤ := j - i
  let L : ℝ := 2 * Real.pi * (k : ℝ)
  have hk : k ≠ 0 := by
    intro h
    apply hij
    dsimp [k] at h
    omega
  have hL : L ≠ 0 := by
    dsimp [L]
    exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (by exact_mod_cast hk)
  have hpoint (t : ℝ) :
      fourierChar (-i) t * ((t : ℂ) * fourierChar j t) =
        (t : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) := by
    calc
      fourierChar (-i) t * ((t : ℂ) * fourierChar j t) =
          (t : ℂ) * (fourierChar (-i) t * fourierChar j t) := by ring
      _ = (t : ℂ) * Complex.exp
          (2 * Real.pi * Complex.I * ((-i : ℤ) : ℂ) * (t : ℂ) +
            2 * Real.pi * Complex.I * (j : ℂ) * (t : ℂ)) := by
          rw [fourierChar, fourierChar, ← Complex.exp_add]
      _ = _ := by
          unfold L k
          push_cast
          congr 1
          ring
  rw [unitCoordFourierKernel, intervalIntegral.integral_congr (fun t _ => hpoint t),
    integral_linPhase L hL]
  have hone : Complex.exp ((((1 : ℝ) * L : ℝ) : ℂ) * Complex.I) = 1 := by
    calc
      Complex.exp ((((1 : ℝ) * L : ℝ) : ℂ) * Complex.I) = fourierChar k 1 := by
        unfold fourierChar L
        push_cast
        congr 1
        ring
      _ = 1 := fourierChar_one k
  have hzero : Complex.exp ((((0 : ℝ) * L : ℝ) : ℂ) * Complex.I) = 1 := by simp
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have hden : ((L : ℂ) * Complex.I) ≠ 0 := mul_ne_zero hL' Complex.I_ne_zero
  calc
    linPhaseAnti L 1 - linPhaseAnti L 0 = 1 / ((L : ℂ) * Complex.I) := by
      unfold linPhaseAnti
      rw [hone, hzero]
      norm_num
    _ = 1 / (2 * (Real.pi : ℂ) * Complex.I * ((j - i : ℤ) : ℂ)) := by
      apply congrArg (fun z : ℂ => 1 / z) ?_
      unfold L k
      push_cast
      ring

/-- Away from the diagonal, the weighted phase kernel cancels the analytic frequency
exactly, leaving a real rational coefficient. -/
theorem weightedKernel_coefficient_offDiagonal (n m : ℤ) (hnm : n ≠ m) :
    (starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
        unitCoordFourierKernel n m =
      (-((n : ℝ) / (((N + 1 : ℕ) : ℝ) * ((m - n : ℤ) : ℝ))) : ℂ) := by
  rw [unitCoordFourierKernel_offDiagonal n m hnm]
  have hconj (x : ℝ) :
      (starRingEnd ℂ) ((x : ℂ) * Complex.I) = -(x : ℂ) * Complex.I := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hconj]
  unfold signedFrequency
  have hN : ((N + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero N
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hd : ((m - n : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (Ne.symm hnm)
  push_cast
  field_simp [hN, hpi, hd]

/-- Pairing the two orientations of the weighted Cauchy kernel removes its denominators.
The remaining terms are the symmetric coefficient-loss derivative and its antisymmetric
Wronskian current. -/
theorem weightedKernel_pair_scaled (n m : ℤ) (hnm : n ≠ m) {y : ℝ} (hy : 0 < y) :
    2 * ((N + 1 : ℕ) : ℝ) * ((m - n : ℤ) : ℝ) *
      ((starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
          unitCoordFourierKernel n m * coefficientMixedLoss N r s f n m y +
        (starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) m : ℝ) : ℂ) * Complex.I) *
          unitCoordFourierKernel m n * coefficientMixedLoss N r s f m n y).re =
      ((m - n : ℤ) : ℝ) * (deriv (coefficientLoss N r s f n m) y).re +
        ((m + n : ℤ) : ℝ) * (coefficientWronskian N r s f n m y).re := by
  have hmn : m ≠ n := Ne.symm hnm
  have hN : ((N + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero N
  have hd : ((m - n : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hmn
  have hleftRe (z : ℂ) :
      ((starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
          unitCoordFourierKernel n m * z).re =
        -((n : ℝ) / (((N + 1 : ℕ) : ℝ) * ((m - n : ℤ) : ℝ))) * z.re := by
    rw [weightedKernel_coefficient_offDiagonal N n m hnm]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_div, ← Complex.ofReal_neg]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hsub : ((n - m : ℤ) : ℝ) = -((m - n : ℤ) : ℝ) := by
    push_cast
    ring
  have hscalar :
      -((m : ℝ) / (((N + 1 : ℕ) : ℝ) * ((n - m : ℤ) : ℝ))) =
        (m : ℝ) / (((N + 1 : ℕ) : ℝ) * ((m - n : ℤ) : ℝ)) := by
    rw [hsub, mul_neg, div_neg]
    ring
  have hrightRe (z : ℂ) :
      ((starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) m : ℝ) : ℂ) * Complex.I) *
          unitCoordFourierKernel m n * z).re =
        (m : ℝ) / (((N + 1 : ℕ) : ℝ) * ((m - n : ℤ) : ℝ)) * z.re := by
    rw [weightedKernel_coefficient_offDiagonal N m n hmn]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_div, ← Complex.ofReal_neg]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hscalar]
  have hderiv := (coefficientLoss_hasDerivAt_mixed N r s f n m hy).deriv
  have hcurrent : coefficientWronskian N r s f n m y =
      (starRingEnd ℂ) (coefficientMixedLoss N r s f m n y) -
        coefficientMixedLoss N r s f n m y := by
    unfold coefficientWronskian coefficientMixedLoss
    rw [← complexLoss_conj N r s (coefficientVector N f m y)
      (coefficientHeightVector N f n y)]
  rw [Complex.add_re, hleftRe, hrightRe, hderiv, hcurrent]
  simp only [Complex.add_re, Complex.sub_re, Complex.conj_re]
  field_simp [hN, hd]
  push_cast
  ring

/-- For an exceptional cusp form, the paired Wronskian term is the literal tail Gram
current with polynomial weight.  Any sign argument must therefore control this term together
with the remaining coefficient-loss derivative. -/
theorem weightedKernel_exceptional_pair_scaled_tail
    (e : Ioo (0 : ℝ) (1 / 4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (e : ℝ))
    (n m : ℤ) (hnm : n ≠ m) {y : ℝ} (hy : 0 < y) :
    2 * ((N + 1 : ℕ) : ℝ) * ((m - n : ℤ) : ℝ) *
      ((starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
          unitCoordFourierKernel n m * coefficientMixedLoss N r s g n m y +
        (starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) m : ℝ) : ℂ) * Complex.I) *
          unitCoordFourierKernel m n * coefficientMixedLoss N r s g m n y).re =
      ((m - n : ℤ) : ℝ) * (deriv (coefficientLoss N r s g n m) y).re +
        (2 * Real.pi / ((N + 1 : ℕ) : ℝ)) ^ (2 : ℕ) * ((m - n : ℤ) : ℝ) *
          ((m + n : ℤ) : ℝ) ^ (2 : ℕ) * (tailLoss N r s g n m y).re := by
  rw [weightedKernel_pair_scaled N g r s n m hnm hy]
  rw [coefficientWronskian_eq_tail N r s e g n m hy]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  unfold signedFrequency
  push_cast
  ring

end
end GaloisForLFunctions.RHTower.SelbergMaassWeightedPhaseKernel

import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheNonRatioPrimeRowsSplitIntoDownwardAndUpward
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.OverlapGramSmoothingNeedsAQuarterDefectCorrection

/-!
# The ground-state energy of the physical prime kernel

The literal prime pairing contains its exact-ratio kernel and a nonnegative
non-ratio kernel for a nonnegative atom. Their ground-state energies add.
Consequently the full prime energy dominates the original pole defect and
has the same arithmetic ground line, at every overlap and every horizon.
-/

noncomputable section

set_option autoImplicit false

open Finset MeasureTheory
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticElectrostatics ArithmeticLorentzianGeometry
  ArithmeticEffectivityTheory CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis
open _root_.RHTower (vonMangoldtAtom primeSum)

/-- The jump energy of a kernel after transformation by `n ↦ 1/√n`. -/
def poleKernelDefect (K : ℕ → ℕ → ℝ) (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  (1 / 2) * ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
    K n j * poleVector n * poleVector j *
      (x n / poleVector n - x j / poleVector j) ^ 2

/-- The diagonal row potential paired with the square of the coefficient vector. -/
def poleKernelPotential (K : ℕ → ℕ → ℝ) (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, x n ^ 2 / poleVector n *
    ∑ j ∈ Icc 1 N, K n j * poleVector j

private theorem poleVector_pos' {n : ℕ} (hn : 0 < n) : 0 < poleVector n := by
  unfold poleVector
  exact one_div_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hn))

/-- Ground-state completion retains the full signed adjacency form. -/
theorem poleKernelDefect_add_form {K : ℕ → ℕ → ℝ}
    (hK : ∀ n j, K n j = K j n) (N : ℕ) (x : ℕ → ℝ) :
    poleKernelDefect K N x +
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, x n * x j * K n j) =
        poleKernelPotential K N x := by
  have hterm : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
      K n j * poleVector n * poleVector j *
          (x n / poleVector n - x j / poleVector j) ^ 2 =
        x n ^ 2 / poleVector n * (K n j * poleVector j) +
          x j ^ 2 / poleVector j * (K j n * poleVector n) -
            2 * (x n * x j * K n j) := by
    intro n hn j hj
    rw [hK j n]
    field_simp [(poleVector_pos' (mem_Icc.mp hn).1).ne',
      (poleVector_pos' (mem_Icc.mp hj).1).ne']
    <;> ring
  have hswap :
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        x j ^ 2 / poleVector j * (K j n * poleVector n)) =
      ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        x n ^ 2 / poleVector n * (K n j * poleVector j) := sum_comm
  have hpotential : (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      x n ^ 2 / poleVector n * (K n j * poleVector j)) =
        poleKernelPotential K N x := by
    unfold poleKernelPotential
    simp only [mul_sum]
  have htwo : (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, 2 * (x n * x j * K n j)) =
      2 * ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, x n * x j * K n j := by
    simp only [mul_sum]
  have hsplit : poleKernelDefect K N x =
      poleKernelPotential K N x -
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, x n * x j * K n j := by
    unfold poleKernelDefect
    rw [sum_congr rfl fun n hn => sum_congr rfl fun j hj => hterm n hn j hj]
    simp only [sum_sub_distrib, sum_add_distrib, hswap, hpotential, htwo]
    ring
  rw [hsplit]
  ring

/-- The exact-ratio ground-state energy is the original prime-power defect. -/
theorem poleKernelDefect_weilPrimeKernel (N : ℕ) (x : ℕ → ℝ) :
    poleKernelDefect weilPrimeKernel N x = poleDefect N x := by
  have h := poleKernelDefect_add_form weilPrimeKernel_comm N x
  have hp : poleKernelPotential weilPrimeKernel N x =
      ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) *
        x n ^ 2 := by
    unfold poleKernelPotential
    refine sum_congr rfl fun n hn => ?_
    rw [sum_weilPrimeKernel_poleVector (mem_Icc.mp hn).1 (mem_Icc.mp hn).2]
    field_simp [(poleVector_pos' (mem_Icc.mp hn).1).ne']
    <;> ring
  rw [hp] at h
  have hp' := atomicWeilForm_add_poleDefect N x
  change atomicWeilForm N x + poleDefect N x = _ at hp'
  change poleKernelDefect weilPrimeKernel N x + atomicWeilForm N x = _ at h
  linarith only [h, hp']

theorem poleKernelDefect_nonneg {K : ℕ → ℕ → ℝ} {N : ℕ}
    (hK : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, 0 ≤ K n j) (x : ℕ → ℝ) :
    0 ≤ poleKernelDefect K N x := by
  unfold poleKernelDefect
  refine mul_nonneg (by norm_num) (sum_nonneg fun n hn => sum_nonneg fun j hj => ?_)
  exact mul_nonneg (mul_nonneg (mul_nonneg (hK n hn j hj)
    (poleVector_pos' (mem_Icc.mp hn).1).le) (poleVector_pos' (mem_Icc.mp hj).1).le)
      (sq_nonneg _)

/-- The physical prime-pairing kernel, including all prime powers and both orientations. -/
def physicalPrimeKernel (g : ℝ → ℝ) (n j : ℕ) : ℝ :=
  primePair (atom g n) (atom g j)

/-- The literal prime kernel after its exact-ratio contribution has been removed. -/
def nonRatioPrimeKernel (g : ℝ → ℝ) (n j : ℕ) : ℝ :=
  physicalPrimeKernel g n j - (∫ u, g u ^ 2) * weilPrimeKernel n j

/-- Nonnegative atoms make every non-ratio edge nonnegative. -/
theorem nonRatioPrimeKernel_nonneg {g : ℝ → ℝ} {w : ℝ}
    (hg0 : ∀ u, 0 ≤ g u) (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw : 0 ≤ w) {N n j : ℕ} (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) :
    0 ≤ nonRatioPrimeKernel g n j := by
  unfold nonRatioPrimeKernel physicalPrimeKernel
  rw [primePair_atom_sub_ratio_eq_tsum hsupp hw hn hj]
  refine tsum_nonneg fun k => mul_nonneg ?_ (add_nonneg ?_ ?_)
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · split_ifs
    · exact le_rfl
    · exact integral_nonneg fun u => mul_nonneg (hg0 u) (hg0 _)
  · split_ifs
    · exact le_rfl
    · exact integral_nonneg fun u => mul_nonneg (hg0 u) (hg0 _)

/-- The physical ground-state transform is the old defect plus actual non-ratio squares. -/
theorem physicalPrimeKernel_defect_eq (g : ℝ → ℝ) (N : ℕ) (x : ℕ → ℝ) :
    poleKernelDefect (physicalPrimeKernel g) N x =
      (∫ u, g u ^ 2) * poleDefect N x +
        poleKernelDefect (nonRatioPrimeKernel g) N x := by
  rw [← poleKernelDefect_weilPrimeKernel]
  unfold poleKernelDefect nonRatioPrimeKernel
  simp only [mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun n _ => sum_congr rfl fun j _ => by ring

/-- Adding physical overlap edges never loses any of the original prime defect. -/
theorem physicalPrimeKernel_defect_ge {g : ℝ → ℝ} {w : ℝ}
    (hg0 : ∀ u, 0 ≤ g u) (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw : 0 ≤ w) (N : ℕ) (x : ℕ → ℝ) :
    (∫ u, g u ^ 2) * poleDefect N x ≤
      poleKernelDefect (physicalPrimeKernel g) N x := by
  rw [physicalPrimeKernel_defect_eq]
  exact le_add_of_nonneg_right (poleKernelDefect_nonneg
    (fun _ hn _ hj => nonRatioPrimeKernel_nonneg hg0 hsupp hw hn hj) x)

/-- The arithmetic pole line is unchanged by the physical non-ratio edges. -/
theorem physicalPrimeKernel_defect_eq_zero_iff {g : ℝ → ℝ} {w : ℝ}
    (hg0 : ∀ u, 0 ≤ g u) (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw : 0 ≤ w) (hM : 0 < ∫ u, g u ^ 2) {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    poleKernelDefect (physicalPrimeKernel g) N (primeHorizonExtension x) = 0 ↔
      ∃ a : ℝ, x = a • horizonPoleVector N := by
  constructor
  · intro hx
    have h := physicalPrimeKernel_defect_ge hg0 hsupp hw N (primeHorizonExtension x)
    rw [hx] at h
    have hD : poleDefect N (primeHorizonExtension x) = 0 := by
      have h' : (∫ u, g u ^ 2) * poleDefect N (primeHorizonExtension x) = 0 :=
        le_antisymm h (mul_nonneg hM.le (poleDefect_nonneg _ _))
      exact (mul_eq_zero.mp h').resolve_left hM.ne'
    exact (poleDefect_eq_zero_iff_horizonPoleVector hN x).mp hD
  · rintro ⟨a, rfl⟩
    have hcoord : ∀ n ∈ Icc 1 N,
        primeHorizonExtension (a • horizonPoleVector N) n / poleVector n = a := by
      intro n hn
      rw [primeHorizonExtension, dif_pos hn]
      change (a * poleVector n) / poleVector n = a
      exact mul_div_cancel_right₀ a (poleVector_pos' (mem_Icc.mp hn).1).ne'
    unfold poleKernelDefect
    have hsum : (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        physicalPrimeKernel g n j * poleVector n * poleVector j *
          (primeHorizonExtension (a • horizonPoleVector N) n / poleVector n -
            primeHorizonExtension (a • horizonPoleVector N) j / poleVector j) ^ 2) = 0 := by
      refine sum_eq_zero fun n hn => sum_eq_zero fun j hj => ?_
      rw [hcoord n hn, hcoord j hj, sub_self, zero_pow (by omega), mul_zero]
    rw [hsum, mul_zero]

/-- The literal synthesized prime sum and its ground-state energy add to the row potential. -/
theorem primeSum_add_physicalPrimeDefect {g : ℝ → ℝ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw : 0 ≤ w) (N : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    primeSum (atomicTest N (primeHorizonExtension x) g) +
      poleKernelDefect (physicalPrimeKernel g) N (primeHorizonExtension x) =
        poleKernelPotential (physicalPrimeKernel g) N (primeHorizonExtension x) := by
  have hp := horizonPrimePair_inner_eq_primeSum hg hsupp hw N x
  rw [horizonKernelMatrix_inner] at hp
  have hd := poleKernelDefect_add_form
    (K := physicalPrimeKernel g) (fun n j => primePair_comm _ _) N (primeHorizonExtension x)
  change (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
    primeHorizonExtension x n * primeHorizonExtension x j * physicalPrimeKernel g n j) = _ at hp
  rw [hp] at hd
  linarith only [hd]

/-- The full signed Weil form retains Gamma, both pole moments and the exact prime row potential. -/
theorem weilQuad_eq_physicalPrimeDefect_add_remainder {g : ℝ → ℝ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw : 0 ≤ w) (N : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    weilQuad (atomicTest N (primeHorizonExtension x) g) =
      poleKernelDefect (physicalPrimeKernel g) N (primeHorizonExtension x) +
        (2 * _root_.RHTower.gammaHardyPhaseRate 0 *
          (∫ u, atomicTest N (primeHorizonExtension x) g u ^ 2) +
          _root_.RHTower.levyEnergy (atomicTest N (primeHorizonExtension x) g) +
          (2 * _root_.RHTower.coshHalfMoment (atomicTest N (primeHorizonExtension x) g) ^ 2 -
            2 * _root_.RHTower.sinhHalfMoment (atomicTest N (primeHorizonExtension x) g) ^ 2) -
          poleKernelPotential (physicalPrimeKernel g) N (primeHorizonExtension x)) := by
  rw [weilQuad_eq (contDiff_atomicTest hg N _) (hasCompactSupport_atomicTest hsupp N _)]
  have h := primeSum_add_physicalPrimeDefect hg hsupp hw N x
  linarith only [h]

private theorem tiltedUnitSpline_nonneg' (u : ℝ) : 0 ≤ tiltedUnitSpline u := by
  change 0 ≤ Real.exp (1 * ((u - 1 / 2) / (1 / 8))) *
    RHTower.WeilDeletion.upow 1 3 ((u - 1 / 2) / (1 / 8))
  exact mul_nonneg (Real.exp_pos _).le (RHTower.WeilDeletion.upow_nonneg one_pos 3 _)

/-- Every positive overlap of the fixed tilted spline retains the full prime defect
and exactly its original arithmetic ground line. -/
theorem tiltedSpline_physicalPrimeDefect {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    let g := atomDilate tiltedUnitSpline (c / N)
    poleDefect N (primeHorizonExtension x) ≤
        poleKernelDefect (physicalPrimeKernel g) N (primeHorizonExtension x) / (∫ u, g u ^ 2) ∧
      (poleKernelDefect (physicalPrimeKernel g) N (primeHorizonExtension x) = 0 ↔
        ∃ a : ℝ, x = a • horizonPoleVector N) := by
  dsimp only
  have hw : 0 < c / (N : ℝ) := div_pos hc (by exact_mod_cast hN)
  obtain ⟨_, hsupp, _⟩ := atomDilate_facts contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hw
  have hg0 : ∀ u, 0 ≤ atomDilate tiltedUnitSpline (c / N) u :=
    fun u => tiltedUnitSpline_nonneg' _
  have hM : 0 < ∫ u, atomDilate tiltedUnitSpline (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw integral_tiltedUnitSpline_sq_pos
  refine ⟨?_, physicalPrimeKernel_defect_eq_zero_iff hg0 hsupp hw.le hM hN x⟩
  apply (le_div_iff₀ hM).mpr
  simpa only [mul_comm] using physicalPrimeKernel_defect_ge hg0 hsupp hw.le N (primeHorizonExtension x)

/-- The original prime spectral gap survives every physical overlap after atom-mass normalization. -/
theorem exists_tiltedSpline_physicalPrimeDefect_gap :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℝ, 0 < c → ∀ N : ℕ, 1 ≤ N →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        δ * ‖horizonPoleProjection x‖ ^ 2 ≤
          poleKernelDefect (physicalPrimeKernel (atomDilate tiltedUnitSpline (c / N))) N
            (primeHorizonExtension x) / (∫ u, atomDilate tiltedUnitSpline (c / N) u ^ 2) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_poleDefect_ge
  refine ⟨δ, hδ, fun c hc N hN x => ?_⟩
  have h := hgap N (primeHorizonExtension (horizonPoleProjection x))
    (harmonicSum_horizonPoleProjection hN x)
  rw [sum_primeHorizonExtension_sq, poleDefect_horizonPoleProjection hN] at h
  exact h.trans (tiltedSpline_physicalPrimeDefect hc hN x).1

#print axioms physicalPrimeKernel_defect_eq
#print axioms physicalPrimeKernel_defect_eq_zero_iff
#print axioms weilQuad_eq_physicalPrimeDefect_add_remainder
#print axioms tiltedSpline_physicalPrimeDefect
#print axioms exists_tiltedSpline_physicalPrimeDefect_gap

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

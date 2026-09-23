import GaloisForLFunctions.RHTower.XiHeatCassiniWoldLogMeshTransportCurrent
import GaloisForLFunctions.RHTower.GeneralizedDirichletSeriesInjectivity

/-!
# Lower-Hardy ray injectivity of the ordered Wold current

The source-marked Wold transport current has a scalar physical realization on the open lower
half-plane.  Along the negative imaginary ray, its edge sum becomes a generalized Dirichlet
series on the strictly increasing prime-log frequencies.  The node coefficients are the discrete
boundary of the Wold edge coefficients.

Square-root-log source damping supplies absolute convergence at one positive Laplace abscissa.
Generalized Dirichlet uniqueness then proves a rigidity statement stronger than whole-ray
faithfulness: if the scalar lower-Hardy kernel vanishes eventually along that one cofinal ray,
every centered Wold coefficient vanishes.  Thus the scalar ray and the full unit-Lipschitz
transport current have the same source kernel.

This is an interior lower-half-plane theorem.  It does not assert compact-open continuity on
escaping divisor bubbles, critical-wall absolute variation, or continuation across the forbidden
upper half-density wall.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

local notation "R" => xiHeatCassiniOrderedWoldResidualLogDiscrepancy
local notation "h" => xiMassNthPrimeLogHeight

/-- Node boundary of the ordered residual edge current. -/
def xiHeatCassiniWoldResidualLogMeshNodeCharge : ℕ → ℝ
  | 0 => R 0
  | N + 1 => R (N + 1) - R N

/-- The centered Wold residual is absolutely summable against reciprocal ordered primes. -/
theorem summable_abs_xiHeatCassiniOrderedWoldResidual_div_prime :
    Summable (fun N : ℕ => |R N| / (nthPrimeSubtype N : ℝ)) := by
  obtain ⟨B, c, hc, hB, hrate⟩ :=
    exists_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_rate
  have hc2 : 0 < c / 2 := by linarith
  have hprime0 := burnolSummable_poissonWeight_logPow (y := c / 2) hc2 0
  have hprime : Summable (fun p : Nat.Primes =>
      B * Real.exp (-c * Real.sqrt (Real.log (p : ℝ))) / (p : ℝ)) := by
    refine (hprime0.mul_left B).congr (fun p => ?_)
    rw [show 2 * (c / 2) = c by ring]
    norm_num
    ring
  have hmajor : Summable (fun N : ℕ =>
      B * Real.exp (-c * Real.sqrt (Real.log (nthPrimeSubtype N : ℝ))) /
        (nthPrimeSubtype N : ℝ)) := by
    have hs := nthPrimeEquiv.summable_iff.mpr hprime
    exact hs.congr fun N => rfl
  let clipped : ℕ → ℝ := fun N =>
    if |R N| ≤
        B * Real.exp (-c * Real.sqrt (Real.log (nthPrimeSubtype N : ℝ))) then
      |R N| / (nthPrimeSubtype N : ℝ)
    else 0
  have hclipped : Summable clipped := by
    apply hmajor.of_nonneg_of_le
    · intro N
      dsimp only [clipped]
      split_ifs
      · positivity
      · exact le_rfl
    · intro N
      dsimp only [clipped]
      split_ifs with hN
      · exact (div_le_div_iff_of_pos_right (nthPrimeSubtype_pos N)).2 hN
      · positivity
  apply hclipped.congr_atTop
  filter_upwards [hrate] with N hN
  change (if |R N| ≤
      B * Real.exp (-c * Real.sqrt (Real.log (nthPrimeSubtype N : ℝ))) then
        |R N| / (nthPrimeSubtype N : ℝ) else 0) =
      |R N| / (nthPrimeSubtype N : ℝ)
  rw [if_pos hN]

/-- The prime-log Laplace weight at abscissa one is exactly reciprocal prime weight. -/
theorem exp_neg_xiMassNthPrimeLogHeight (N : ℕ) :
    Real.exp (-h N) = 1 / (nthPrimeSubtype N : ℝ) := by
  rw [xiMassNthPrimeLogHeight, Real.exp_neg,
    Real.exp_log (nthPrimeSubtype_pos N)]
  simp [one_div]

/-- Source damping makes the centered residual absolutely summable after one prime-harmonic
Laplace weight. -/
theorem summable_norm_xiHeatCassiniOrderedWoldResidual_exp_neg_height :
    Summable (fun N : ℕ => ‖(R N : ℂ)‖ * Real.exp (-h N)) := by
  simpa [Complex.norm_real, Real.norm_eq_abs,
    exp_neg_xiMassNthPrimeLogHeight, div_eq_mul_inv] using
      summable_abs_xiHeatCassiniOrderedWoldResidual_div_prime

/-- The node boundary of the edge current is absolutely summable at the same Laplace abscissa. -/
theorem summable_norm_xiHeatCassiniWoldResidualLogMeshNodeCharge_exp_neg_height :
    Summable (fun N : ℕ =>
      ‖(xiHeatCassiniWoldResidualLogMeshNodeCharge N : ℂ)‖ *
        Real.exp (-h N)) := by
  let f : ℕ → ℝ := fun N => ‖(R N : ℂ)‖ * Real.exp (-h N)
  have hf : Summable f :=
    summable_norm_xiHeatCassiniOrderedWoldResidual_exp_neg_height
  have hfSucc : Summable (fun N : ℕ => f (N + 1)) :=
    (summable_nat_add_iff 1).2 hf
  have hmajor : Summable (fun N : ℕ => f (N + 1) + f N) := hfSucc.add hf
  have htail : Summable (fun N : ℕ =>
      ‖(xiHeatCassiniWoldResidualLogMeshNodeCharge (N + 1) : ℂ)‖ *
        Real.exp (-h (N + 1))) := by
    apply hmajor.of_nonneg_of_le
    · intro N
      positivity
    · intro N
      have hh : h N ≤ h (N + 1) :=
        nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ N)
      have hexp : Real.exp (-h (N + 1)) ≤ Real.exp (-h N) :=
        Real.exp_le_exp.mpr (by linarith)
      have htri : |R (N + 1) - R N| ≤ |R (N + 1)| + |R N| :=
        abs_sub _ _
      rw [xiHeatCassiniWoldResidualLogMeshNodeCharge]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      change |R (N + 1) - R N| * Real.exp (-h (N + 1)) ≤
        f (N + 1) + f N
      calc
        |R (N + 1) - R N| * Real.exp (-h (N + 1)) ≤
            (|R (N + 1)| + |R N|) * Real.exp (-h (N + 1)) :=
          mul_le_mul_of_nonneg_right htri (Real.exp_pos _).le
        _ = |R (N + 1)| * Real.exp (-h (N + 1)) +
            |R N| * Real.exp (-h (N + 1)) := by ring
        _ ≤ |R (N + 1)| * Real.exp (-h (N + 1)) +
            |R N| * Real.exp (-h N) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hexp (abs_nonneg _))
        _ = f (N + 1) + f N := by
          simp only [f, Complex.norm_real, Real.norm_eq_abs]
  exact (summable_nat_add_iff 1).1 htail

/-- Generalized Dirichlet series of the node boundary of the Wold edge current. -/
def xiHeatCassiniWoldResidualNodeDirichletSeries (s : ℂ) : ℂ :=
  GaloisForLFunctions.RHTower.generalizedDirichletSeries h
    (fun N => (xiHeatCassiniWoldResidualLogMeshNodeCharge N : ℂ)) s

/-- Absolute convergence at abscissa one propagates down every farther positive real ray. -/
theorem summable_mul_primeLogExp_of_summable_at_one
    {a : ℕ → ℂ}
    (ha : Summable (fun N : ℕ => ‖a N‖ * Real.exp (-h N)))
    {x : ℝ} (hx : 1 ≤ x) :
    Summable (fun N : ℕ =>
      a N * Complex.exp (-(h N : ℂ) * (x : ℂ))) := by
  apply Summable.of_norm
  apply ha.of_nonneg_of_le
  · intro N
    exact norm_nonneg _
  · intro N
    rw [norm_mul, Complex.norm_exp]
    have hh : 0 ≤ h N := (xiMassNthPrimeLogHeight_pos N).le
    have hexp : Real.exp (-h N * x) ≤ Real.exp (-h N) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hre : (-(h N : ℂ) * (x : ℂ)).re = -h N * x := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)

/-- Negative-imaginary evaluation turns a prime phase into its positive Laplace character. -/
theorem xiHeatCassiniOrderedPrimeComplexNegativePhase_neg_mul_I
    (N : ℕ) (x : ℝ) :
    xiHeatCassiniOrderedPrimeComplexNegativePhase N (-(x : ℂ) * Complex.I) =
      Complex.exp (-(h N : ℂ) * (x : ℂ)) := by
  unfold xiHeatCassiniOrderedPrimeComplexNegativePhase
  congr 1
  calc
    -(Complex.I * (h N : ℂ) * (-(x : ℂ) * Complex.I)) =
        Complex.I ^ (2 : ℕ) * (h N : ℂ) * (x : ℂ) := by ring
    _ = -(h N : ℂ) * (x : ℂ) := by rw [Complex.I_sq]; ring

/-- On the lower imaginary ray, the edge current is the generalized Dirichlet series of its
node boundary. -/
theorem xiHeatCassiniWoldResidualLowerHardyKernel_neg_mul_I_eq_nodeDirichletSeries
    {x : ℝ} (hx : 1 ≤ x) :
    xiHeatCassiniWoldResidualLowerHardyKernel (-(x : ℂ) * Complex.I) =
      xiHeatCassiniWoldResidualNodeDirichletSeries x := by
  let A : ℕ → ℂ := fun N =>
    (R N : ℂ) * Complex.exp (-(h N : ℂ) * (x : ℂ))
  let B : ℕ → ℂ := fun N =>
    (R N : ℂ) * Complex.exp (-(h (N + 1) : ℂ) * (x : ℂ))
  let C : ℕ → ℂ := fun N =>
    (xiHeatCassiniWoldResidualLogMeshNodeCharge N : ℂ) *
      Complex.exp (-(h N : ℂ) * (x : ℂ))
  have hA : Summable A :=
    summable_mul_primeLogExp_of_summable_at_one
      summable_norm_xiHeatCassiniOrderedWoldResidual_exp_neg_height hx
  have hAnorm : Summable (fun N => ‖A N‖) := hA.norm
  have hB : Summable B := by
    apply Summable.of_norm
    apply hAnorm.of_nonneg_of_le
    · intro N
      exact norm_nonneg _
    · intro N
      have hh : h N ≤ h (N + 1) :=
        nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ N)
      have hx0 : 0 ≤ x := zero_le_one.trans hx
      have hexp : Real.exp (-h (N + 1) * x) ≤ Real.exp (-h N * x) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      simp only [A, B, norm_mul, Complex.norm_exp]
      have hreA : (-(h N : ℂ) * (x : ℂ)).re = -h N * x := by simp
      have hreB : (-(h (N + 1) : ℂ) * (x : ℂ)).re = -h (N + 1) * x := by simp
      rw [hreA, hreB]
      exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
  have hC : Summable C :=
    summable_mul_primeLogExp_of_summable_at_one
      summable_norm_xiHeatCassiniWoldResidualLogMeshNodeCharge_exp_neg_height hx
  have hAsucc : Summable (fun N => A (N + 1)) :=
    (summable_nat_add_iff 1).2 hA
  have hCsucc : Summable (fun N => C (N + 1)) :=
    (summable_nat_add_iff 1).2 hC
  have hCzero : C 0 = A 0 := by
    simp [C, A, xiHeatCassiniWoldResidualLogMeshNodeCharge]
  have hCsucc_eq (N : ℕ) : C (N + 1) = A (N + 1) - B N := by
    simp [C, A, B, xiHeatCassiniWoldResidualLogMeshNodeCharge]
    ring
  have hCsum : (∑' N, C N) = (∑' N, A N) - ∑' N, B N := by
    have hCsplit := hC.sum_add_tsum_nat_add 1
    have hAsplit := hA.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at hCsplit hAsplit
    calc
      (∑' N, C N) = C 0 + ∑' N, C (N + 1) := hCsplit.symm
      _ = A 0 + ∑' N, (A (N + 1) - B N) := by
        rw [hCzero]
        congr 1
        exact tsum_congr hCsucc_eq
      _ = A 0 + ((∑' N, A (N + 1)) - ∑' N, B N) := by
        rw [hAsucc.tsum_sub hB]
      _ = (∑' N, A N) - ∑' N, B N := by rw [← hAsplit]; ring
  rw [xiHeatCassiniWoldResidualLowerHardyKernel,
    xiHeatCassiniWoldResidualNodeDirichletSeries,
    GaloisForLFunctions.RHTower.generalizedDirichletSeries]
  change (∑' N, xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
    (-(x : ℂ) * Complex.I) N) = ∑' N, C N
  calc
    (∑' N, xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (-(x : ℂ) * Complex.I) N) = ∑' N, (A N - B N) := by
      apply tsum_congr
      intro N
      rw [xiHeatCassiniWoldResidualComplexPhaseConnectionAtom,
        xiHeatCassiniOrderedPrimeComplexNegativePhase_neg_mul_I,
        xiHeatCassiniOrderedPrimeComplexNegativePhase_neg_mul_I]
      simp only [A, B]
      ring
    _ = (∑' N, A N) - ∑' N, B N := hA.tsum_sub hB
    _ = ∑' N, C N := hCsum.symm

/-- Eventual vanishing on one cofinal interior ray recovers every ordered Wold residual
coefficient. -/
theorem eventually_lowerImaginaryRay_woldResidualLowerHardyKernel_eq_zero_iff :
    ((fun x : ℝ =>
      xiHeatCassiniWoldResidualLowerHardyKernel (-(x : ℂ) * Complex.I)) =ᶠ[atTop] 0) ↔
      ∀ N : ℕ, R N = 0 := by
  constructor
  · intro hray
    have ha : Summable (fun N : ℕ =>
        ‖(xiHeatCassiniWoldResidualLogMeshNodeCharge N : ℂ)‖ *
          Real.exp (-h N * (1 : ℝ))) := by
      simpa only [mul_one] using
        summable_norm_xiHeatCassiniWoldResidualLogMeshNodeCharge_exp_neg_height
    have hseries : (fun x : ℝ =>
        GaloisForLFunctions.RHTower.generalizedDirichletSeries h
          (fun N => (xiHeatCassiniWoldResidualLogMeshNodeCharge N : ℂ)) x) =ᶠ[atTop]
        0 := by
      filter_upwards [hray, eventually_ge_atTop (1 : ℝ)] with x hrayx hx
      change xiHeatCassiniWoldResidualNodeDirichletSeries x = 0
      rw [← xiHeatCassiniWoldResidualLowerHardyKernel_neg_mul_I_eq_nodeDirichletSeries hx]
      exact hrayx
    have hchargeComplex :=
      GaloisForLFunctions.RHTower.generalizedDirichletSeries_coeff_eq_zero_of_absolutelySummable_at
        nthPrimeSubtype_log_strictMono (xiMassNthPrimeLogHeight_pos 0) ha hseries
    have hcharge : ∀ N : ℕ,
        xiHeatCassiniWoldResidualLogMeshNodeCharge N = 0 := by
      intro N
      exact_mod_cast hchargeComplex N
    intro N
    induction N with
    | zero =>
        simpa [xiHeatCassiniWoldResidualLogMeshNodeCharge] using hcharge 0
    | succ N ih =>
        have hs := hcharge (N + 1)
        simp only [xiHeatCassiniWoldResidualLogMeshNodeCharge] at hs
        linarith
  · intro hzero
    filter_upwards [] with x
    simp [xiHeatCassiniWoldResidualLowerHardyKernel,
      xiHeatCassiniWoldResidualComplexPhaseConnectionAtom, hzero]

/-- Vanishing on the lower imaginary half-ray is equivalent to coefficientwise source
vanishing. -/
theorem forall_lowerImaginaryRay_woldResidualLowerHardyKernel_eq_zero_iff :
    (∀ x : ℝ, 1 ≤ x →
      xiHeatCassiniWoldResidualLowerHardyKernel (-(x : ℂ) * Complex.I) = 0) ↔
      ∀ N : ℕ, R N = 0 := by
  constructor
  · intro hray
    rw [← eventually_lowerImaginaryRay_woldResidualLowerHardyKernel_eq_zero_iff]
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact hray x hx
  · intro hzero x hx
    simp [xiHeatCassiniWoldResidualLowerHardyKernel,
      xiHeatCassiniWoldResidualComplexPhaseConnectionAtom, hzero]

/-- The physical lower-Hardy ray and the full unit-Lipschitz transport current have exactly the
same source kernel. -/
theorem eventually_lowerImaginaryRay_woldResidualLowerHardyKernel_eq_zero_iff_current_zero :
    ((fun x : ℝ =>
      xiHeatCassiniWoldResidualLowerHardyKernel (-(x : ℂ) * Complex.I)) =ᶠ[atTop] 0) ↔
      ∀ phi : ℕ → ℂ,
        XiHeatCassiniPrimeLogMeshLipschitz 1 phi →
          xiHeatCassiniWoldResidualLogMeshCurrent phi = 0 := by
  rw [eventually_lowerImaginaryRay_woldResidualLowerHardyKernel_eq_zero_iff,
    forall_unitLipschitz_woldResidualLogMeshCurrent_eq_zero_iff]

theorem forall_lowerImaginaryRay_woldResidualLowerHardyKernel_eq_zero_iff_current_zero :
    (∀ x : ℝ, 1 ≤ x →
      xiHeatCassiniWoldResidualLowerHardyKernel (-(x : ℂ) * Complex.I) = 0) ↔
      ∀ phi : ℕ → ℂ,
        XiHeatCassiniPrimeLogMeshLipschitz 1 phi →
          xiHeatCassiniWoldResidualLogMeshCurrent phi = 0 := by
  rw [forall_lowerImaginaryRay_woldResidualLowerHardyKernel_eq_zero_iff,
    forall_unitLipschitz_woldResidualLogMeshCurrent_eq_zero_iff]

end

end RHTower

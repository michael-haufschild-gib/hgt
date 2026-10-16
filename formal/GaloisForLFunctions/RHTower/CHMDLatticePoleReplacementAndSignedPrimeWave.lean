import GaloisForLFunctions.RHTower.CHMDMobiusFoldedTransportOfKleinGordonPrimeWave

/-!
# The integer lattice replaces the pole density: the signed Klein–Gordon prime wave

The pole counterterm `∫_0^∞ K_y(s) e^{s/2} ds` of the Klein–Gordon transport differs from the
lattice sum `Σ_{n ≥ 1} n^{−1/2} K_y(log n)` by a quantity bounded uniformly in the time `y`: on
each cell `[log n, log(n+1)]` the density `e^s ds` has mass exactly `1`, and the conjugated kernel
`f_y = e^{−s/2}K_y` varies by at most `(8 log 2 + 2)/π · n^{−1/2} · log(1 + 1/n)` across the cell,
so the cell defects are summable with a `y`-independent bound.  Hence

`T(y) = Σ_{n ≥ 1} (Λ(n) − 1) n^{−1/2} K_y(log n) + O(1)` uniformly in `y`,

and the Riemann hypothesis is equivalent to a one-sided bound on the Klein–Gordon wave of the
pole-free signed measure `Σ_n (Λ(n) − 1) n^{−1/2} δ_{log n}`, whose Dirichlet series
`−ζ'/ζ − ζ` is regular at `s = 1`.  The pole of `ζ` is cancelled by the integer lattice itself,
not by a continuous density.  No one-sided bound is produced.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace RHTower.CHMDChebyshevTransport

open RHTower.CHMDLightCone RHTower.CHMDStage22 GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Section 1: the conjugated kernel is uniformly Lipschitz at the scale `e^{−s/2}` -/

/-- The constant `(8 log 2 + 2)/π` dominating `e^{s/2} f_y'(s)` for all `y, s`. -/
def conjugatedDerivBound : ℝ := 8 * Real.log 2 / π + 2 / π

theorem conjugatedDerivBound_nonneg : 0 ≤ conjugatedDerivBound := by
  unfold conjugatedDerivBound
  have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  positivity

/-- `|f_y'(s)| ≤ conjugatedDerivBound · e^{−s/2}` for all `y, s`. -/
theorem abs_conjugatedKernelDeriv_le (y s : ℝ) :
    |conjugatedKernelDeriv y s| ≤ conjugatedDerivBound * Real.exp (-(s / 2)) := by
  unfold conjugatedKernelDeriv conjugatedDerivBound
  rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have h1 := abs_kernelDeriv_le y s
  have h0 := abs_chmdPrimeKernel_le y s
  calc |kernelDeriv y s - chmdPrimeKernel y s / 2|
      ≤ |kernelDeriv y s| + |chmdPrimeKernel y s| / 2 := by
        refine (abs_sub _ _).trans ?_
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 8 * Real.log 2 / π + 4 / π / 2 := by gcongr
    _ = _ := by ring

/-- Increments of the conjugated kernel to the right of `a ≥ 0`. -/
theorem abs_conjugatedKernel_sub_le (y : ℝ) {a s : ℝ} (has : a ≤ s) :
    |conjugatedKernel y s - conjugatedKernel y a| ≤
      conjugatedDerivBound * Real.exp (-(a / 2)) * (s - a) := by
  have hint : ∫ t in a..s, conjugatedKernelDeriv y t =
      conjugatedKernel y s - conjugatedKernel y a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_conjugatedKernel y t)
      ((continuous_conjugatedKernelDeriv y).intervalIntegrable _ _)
  rw [← hint]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := s)
    (C := conjugatedDerivBound * Real.exp (-(a / 2))) (f := conjugatedKernelDeriv y) fun t ht => by
      rw [Real.norm_eq_abs]
      rw [Set.uIoc_of_le has] at ht
      refine (abs_conjugatedKernelDeriv_le y t).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [ht.1]))
        conjugatedDerivBound_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr has)] at h
  exact h

/-! ## Section 2: the lattice cells of the pole density -/

/-- The pole-density integral over the lattice cell `[log(n+1), log(n+2)]`. -/
def latticeCell (y : ℝ) (n : ℕ) : ℝ :=
  ∫ s in Real.log (n + 1)..Real.log (n + 2), chmdPrimeKernel y s * Real.exp (s / 2)

theorem log_succ_sub_log_le (n : ℕ) :
    Real.log (n + 2) - Real.log (n + 1) ≤ ((n : ℝ) + 1)⁻¹ := by
  have h1 : (0 : ℝ) < n + 1 := by positivity
  have h2 : (0 : ℝ) < n + 2 := by positivity
  rw [← Real.log_div h2.ne' h1.ne']
  refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
  field_simp
  ring

theorem exp_neg_log_succ_half (n : ℕ) :
    Real.exp (-(Real.log (n + 1) / 2)) = (Real.sqrt (n + 1))⁻¹ := by
  rw [Real.exp_neg, Real.exp_half, Real.exp_log (by positivity)]

/-- **Cell defect**: `|∫_{log(n+1)}^{log(n+2)} K_y e^{s/2} − f_y(log(n+1))| ≤ 2C (n+1)^{−3/2}`. -/
theorem abs_latticeCell_sub_le (y : ℝ) (n : ℕ) :
    |latticeCell y n - conjugatedKernel y (Real.log (n + 1))| ≤
      2 * conjugatedDerivBound * ((n + 1 : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  set a := Real.log (n + 1) with ha
  set b := Real.log (n + 2) with hb
  have hr : (0 : ℝ) < n + 1 := by positivity
  have hr1 : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hab : a ≤ b := Real.log_le_log hr (by linarith)
  have hba : b - a ≤ ((n : ℝ) + 1)⁻¹ := log_succ_sub_log_le n
  have hba0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hea : Real.exp a = n + 1 := Real.exp_log hr
  have heb : Real.exp b = n + 2 := Real.exp_log (by positivity)
  -- the cell has unit pole mass
  have hmass : ∫ s in a..b, Real.exp s = 1 := by
    rw [integral_exp, hea, heb]; ring
  have hcell : latticeCell y n = ∫ s in a..b, Real.exp s * conjugatedKernel y s := by
    unfold latticeCell
    refine intervalIntegral.integral_congr fun s _ => ?_
    exact (exp_mul_conjugatedKernel y s).symm
  have hsplit : latticeCell y n - conjugatedKernel y a =
      ∫ s in a..b, Real.exp s * (conjugatedKernel y s - conjugatedKernel y a) := by
    rw [hcell]
    have hi1 : IntervalIntegrable (fun s => Real.exp s * conjugatedKernel y s) volume a b :=
      (Real.continuous_exp.mul (continuous_conjugatedKernel y)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun s => Real.exp s * conjugatedKernel y a) volume a b :=
      (Real.continuous_exp.mul continuous_const).intervalIntegrable _ _
    have h1 : ∫ s in a..b, Real.exp s * (conjugatedKernel y s - conjugatedKernel y a) =
        (∫ s in a..b, Real.exp s * conjugatedKernel y s) -
          ∫ s in a..b, Real.exp s * conjugatedKernel y a := by
      rw [← intervalIntegral.integral_sub hi1 hi2]
      refine intervalIntegral.integral_congr fun s _ => ?_
      ring
    rw [h1, intervalIntegral.integral_mul_const, hmass, one_mul]
  rw [hsplit]
  -- pointwise bound on the cell
  have hbound : ∀ s ∈ Set.uIoc a b,
      ‖Real.exp s * (conjugatedKernel y s - conjugatedKernel y a)‖ ≤
        2 * conjugatedDerivBound * Real.sqrt (n + 1) * (b - a) := by
    intro s hs
    rw [Set.uIoc_of_le hab] at hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hs1 : Real.exp s ≤ Real.exp b := Real.exp_le_exp.mpr hs.2
    have hs2 : Real.exp b ≤ 2 * Real.exp a := by rw [hea, heb]; linarith
    have hinc := abs_conjugatedKernel_sub_le y hs.1.le
    rw [exp_neg_log_succ_half] at hinc
    have hsq : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.mpr hr
    have hsqsq : Real.sqrt (n + 1) * Real.sqrt (n + 1) = n + 1 := Real.mul_self_sqrt hr.le
    have hCq : 0 ≤ conjugatedDerivBound * (Real.sqrt (n + 1))⁻¹ :=
      mul_nonneg conjugatedDerivBound_nonneg (inv_nonneg.mpr hsq.le)
    have hq0 : Real.sqrt (n + 1) ≠ 0 := hsq.ne'
    calc Real.exp s * |conjugatedKernel y s - conjugatedKernel y a|
        ≤ (2 * Real.exp a) * (conjugatedDerivBound * (Real.sqrt (n + 1))⁻¹ * (s - a)) :=
          mul_le_mul (hs1.trans hs2) hinc (abs_nonneg _) (by positivity)
      _ ≤ (2 * Real.exp a) * (conjugatedDerivBound * (Real.sqrt (n + 1))⁻¹ * (b - a)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hCq)
            (by positivity)
      _ = 2 * (Real.sqrt (n + 1) * Real.sqrt (n + 1)) *
            (conjugatedDerivBound * (Real.sqrt (n + 1))⁻¹ * (b - a)) := by
          rw [hea, hsqsq]
      _ = 2 * conjugatedDerivBound * Real.sqrt (n + 1) * (b - a) := by
          field_simp
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, abs_of_nonneg hba0] at h
  refine h.trans ?_
  -- arithmetic of the bound: `2C√r (b−a)² ≤ 2C r^{−3/2}`
  have hsq : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.mpr hr
  have hsqsq : Real.sqrt (n + 1) * Real.sqrt (n + 1) = n + 1 := Real.mul_self_sqrt hr.le
  have hpow : ((n : ℝ) + 1) ^ (3 / 2 : ℝ) = (n + 1) * Real.sqrt (n + 1) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hr, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [hpow]
  have hC := conjugatedDerivBound_nonneg
  have hba2 : (b - a) * (b - a) ≤ ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹ :=
    mul_le_mul hba hba hba0 (by positivity)
  have hq0 : Real.sqrt (n + 1) ≠ 0 := hsq.ne'
  calc 2 * conjugatedDerivBound * Real.sqrt (n + 1) * (b - a) * (b - a)
      ≤ 2 * conjugatedDerivBound * Real.sqrt (n + 1) * (((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹) := by
        rw [mul_assoc (2 * conjugatedDerivBound * Real.sqrt (n + 1))]
        exact mul_le_mul_of_nonneg_left hba2 (by positivity)
    _ = 2 * conjugatedDerivBound * Real.sqrt (n + 1) *
          ((Real.sqrt (n + 1) * Real.sqrt (n + 1))⁻¹ * (Real.sqrt (n + 1) * Real.sqrt (n + 1))⁻¹) := by
        rw [hsqsq]
    _ = 2 * conjugatedDerivBound * ((Real.sqrt (n + 1) * Real.sqrt (n + 1)) * Real.sqrt (n + 1))⁻¹ := by
        field_simp
    _ = 2 * conjugatedDerivBound * ((n + 1) * Real.sqrt (n + 1))⁻¹ := by
        rw [hsqsq]

/-! ## Section 3: summation of the cells recovers the pole integral -/

theorem summable_conjugatedKernel_log_succ (y : ℝ) :
    Summable fun n : ℕ => conjugatedKernel y (Real.log (n + 1)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_conjugatedKernel_le y
  have hs : Summable fun n : ℕ => C * ((n + 1 : ℝ) ^ (π - 1 / 2)) ⁻¹ := by
    have := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (π - 1 / 2))⁻¹) 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by linarith [Real.pi_gt_three]))
    refine (this.mul_left C).congr fun n => ?_
    push_cast
    ring
  refine Summable.of_norm_bounded hs fun n => ?_
  rw [Real.norm_eq_abs]
  refine (hC _ (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))).trans (le_of_eq ?_)
  congr 1
  rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_neg]
  congr 1
  ring

theorem summable_latticeBudget_term :
    Summable fun n : ℕ => ((n + 1 : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  have := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) 1).mpr
    (Real.summable_nat_rpow_inv.mpr (by norm_num))
  refine this.congr fun n => ?_
  push_cast
  rfl

/-- The lattice budget `Σ_{n ≥ 1} n^{−3/2}`. -/
def latticeBudget : ℝ := ∑' n : ℕ, ((n + 1 : ℝ) ^ (3 / 2 : ℝ))⁻¹

theorem summable_latticeCell_sub (y : ℝ) :
    Summable fun n : ℕ => latticeCell y n - conjugatedKernel y (Real.log (n + 1)) :=
  Summable.of_norm_bounded (summable_latticeBudget_term.mul_left (2 * conjugatedDerivBound))
    fun n => by rw [Real.norm_eq_abs]; exact abs_latticeCell_sub_le y n

theorem summable_latticeCell (y : ℝ) : Summable (latticeCell y) := by
  have := (summable_latticeCell_sub y).add (summable_conjugatedKernel_log_succ y)
  refine this.congr fun n => ?_
  ring

/-- **The cells sum to the pole integral**: `Σ_n latticeCell y n = ∫_0^∞ K_y e^{s/2}`. -/
theorem tsum_latticeCell (y : ℝ) :
    ∑' n : ℕ, latticeCell y n = ∫ s in Ioi (0 : ℝ), chmdPrimeKernel y s * Real.exp (s / 2) := by
  refine ((summable_latticeCell y).hasSum_iff_tendsto_nat.mpr ?_).tsum_eq
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N, latticeCell y n =
      ∫ s in (0 : ℝ)..Real.log (N + 1), chmdPrimeKernel y s * Real.exp (s / 2) := by
    intro N
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun s => chmdPrimeKernel y s * Real.exp (s / 2))
      (a := fun k : ℕ => Real.log (k + 1)) (n := N) fun k _ =>
        ((continuous_chmdPrimeKernel_right y).mul (by fun_prop)).intervalIntegrable _ _
    simp only [Nat.cast_zero, zero_add, Real.log_one] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold latticeCell
    push_cast
    rw [show (k : ℝ) + 1 + 1 = k + 2 by ring]
  simp_rw [hpartial]
  refine intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    (integrable_chmdPrimeKernel_mul_exp_half y).integrableOn ?_
  exact Real.tendsto_log_atTop.comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

/-! ## Section 4: the lattice wave and the signed prime wave -/

/-- The lattice wave `Σ_{n ≥ 1} n^{−1/2} K_y(log n)`. -/
def latticeWave (y : ℝ) : ℝ := ∑' n : ℕ, conjugatedKernel y (Real.log (n + 1))

/-- **Lattice pole replacement**: the lattice wave differs from the pole integral by at most
`2 conjugatedDerivBound · Σ n^{−3/2}`, uniformly in `y`. -/
theorem abs_latticeWave_sub_integral_le (y : ℝ) :
    |latticeWave y - ∫ s in Ioi (0 : ℝ), chmdPrimeKernel y s * Real.exp (s / 2)| ≤
      2 * conjugatedDerivBound * latticeBudget := by
  rw [← tsum_latticeCell, latticeWave,
    ← (summable_conjugatedKernel_log_succ y).tsum_sub (summable_latticeCell y)]
  have hnorm : Summable fun n : ℕ =>
      ‖conjugatedKernel y (Real.log (n + 1)) - latticeCell y n‖ := by
    refine (summable_latticeCell_sub y).norm.congr fun n => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm]
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  unfold latticeBudget
  rw [← tsum_mul_left]
  refine hnorm.tsum_le_tsum (fun n => ?_)
    (summable_latticeBudget_term.mul_left (2 * conjugatedDerivBound))
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_latticeCell_sub_le y n

/-- The Klein–Gordon wave of the pole-free signed measure `Σ_n (Λ(n) − 1) n^{−1/2} δ_{log n}`. -/
def signedPrimeWave (y : ℝ) : ℝ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) - 1) *
    conjugatedKernel y (Real.log (n + 1))

theorem summable_chmdPrimeWeight_mul_kernel (y : ℝ) :
    Summable fun n : ℕ => chmdPrimeWeight n * chmdPrimeKernel y (Real.log n) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_chmdPrimeKernel_le y
  refine Summable.of_norm_bounded (summable_chmdPrimeWeight_mul_exp.mul_left C) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (chmdPrimeWeight_nonneg n)]
  have h := hC (Real.log n)
  rw [abs_of_nonneg (Real.log_natCast_nonneg n)] at h
  calc chmdPrimeWeight n * |chmdPrimeKernel y (Real.log n)|
      ≤ chmdPrimeWeight n * (C * Real.exp (-((π - 1) * Real.log n))) :=
        mul_le_mul_of_nonneg_left h (chmdPrimeWeight_nonneg n)
    _ = C * (chmdPrimeWeight n * Real.exp (-((π - 1) * Real.log n))) := by ring

theorem summable_vonMangoldt_succ_mul_conjugatedKernel (y : ℝ) :
    Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
      conjugatedKernel y (Real.log (n + 1)) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ =>
    chmdPrimeWeight n * chmdPrimeKernel y (Real.log n)) 1).mpr (summable_chmdPrimeWeight_mul_kernel y)
  refine h.congr fun n => ?_
  have := vonMangoldt_mul_conjugatedKernel_log y (n + 1)
  push_cast at this ⊢
  exact this.symm

/-- The prime sum of the transport, reindexed from `n ≥ 1`. -/
theorem tsum_chmdPrimeWeight_mul_kernel_eq_tsum_succ (y : ℝ) :
    (∑' n : ℕ, chmdPrimeWeight n * chmdPrimeKernel y (Real.log n)) =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) * conjugatedKernel y (Real.log (n + 1)) := by
  rw [(summable_chmdPrimeWeight_mul_kernel y).tsum_eq_zero_add]
  rw [chmdPrimeWeight_eq_zero_of_lt_two (by norm_num), zero_mul, zero_add]
  refine tsum_congr fun n => ?_
  have := vonMangoldt_mul_conjugatedKernel_log y (n + 1)
  push_cast at this ⊢
  exact this.symm

/-- **The transport is the signed prime wave plus the lattice defect**:
`T(y) = Σ_n (Λ(n) − 1) n^{−1/2} K_y(log n) + (latticeWave y − ∫_0^∞ K_y e^{s/2})`. -/
theorem chebyshevDiscrepancyTransport_eq_signedPrimeWave_add (y : ℝ) :
    chebyshevDiscrepancyTransport y =
      signedPrimeWave y + (latticeWave y - ∫ s in Ioi (0 : ℝ), chmdPrimeKernel y s * Real.exp (s / 2)) := by
  unfold chebyshevDiscrepancyTransport signedPrimeWave latticeWave
  rw [tsum_chmdPrimeWeight_mul_kernel_eq_tsum_succ]
  have hsub := (summable_vonMangoldt_succ_mul_conjugatedKernel y).tsum_sub
    (summable_conjugatedKernel_log_succ y)
  have hcongr : (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) - 1) *
      conjugatedKernel y (Real.log (n + 1))) =
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) * conjugatedKernel y (Real.log (n + 1)) -
        conjugatedKernel y (Real.log (n + 1))) := by
    refine tsum_congr fun n => ?_
    ring
  rw [hcongr, hsub]
  ring

/-- The signed prime wave differs from the transport by at most `2 conjugatedDerivBound · latticeBudget`,
uniformly in `y`. -/
theorem abs_chebyshevDiscrepancyTransport_sub_signedPrimeWave_le (y : ℝ) :
    |chebyshevDiscrepancyTransport y - signedPrimeWave y| ≤ 2 * conjugatedDerivBound * latticeBudget := by
  rw [chebyshevDiscrepancyTransport_eq_signedPrimeWave_add, add_sub_cancel_left]
  exact abs_latticeWave_sub_integral_le y

/-- **Riemann hypothesis through the signed prime wave (upper form)**. -/
theorem riemannHypothesis_iff_signedPrimeWave_bddAbove :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ y : ℝ, 0 ≤ y → signedPrimeWave y ≤ M := by
  rw [riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddAbove]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M + 2 * conjugatedDerivBound * latticeBudget, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_le.mp (abs_chebyshevDiscrepancyTransport_sub_signedPrimeWave_le y)
    linarith [h2.1]
  · rintro ⟨M, hM⟩
    refine ⟨M + 2 * conjugatedDerivBound * latticeBudget, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_le.mp (abs_chebyshevDiscrepancyTransport_sub_signedPrimeWave_le y)
    linarith [h2.2]

/-- **Riemann hypothesis through the signed prime wave (lower form)**. -/
theorem riemannHypothesis_iff_signedPrimeWave_bddBelow :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ y : ℝ, 0 ≤ y → -M ≤ signedPrimeWave y := by
  rw [riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddBelow]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M + 2 * conjugatedDerivBound * latticeBudget, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_le.mp (abs_chebyshevDiscrepancyTransport_sub_signedPrimeWave_le y)
    linarith [h2.2]
  · rintro ⟨M, hM⟩
    refine ⟨M + 2 * conjugatedDerivBound * latticeBudget, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_le.mp (abs_chebyshevDiscrepancyTransport_sub_signedPrimeWave_le y)
    linarith [h2.1]

end

end RHTower.CHMDChebyshevTransport

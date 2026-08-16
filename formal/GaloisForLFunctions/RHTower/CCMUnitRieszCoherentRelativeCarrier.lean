import GaloisForLFunctions.RHTower.CCMUnitRieszCoherentTailCharge


/-!
# Principal-relative carrier for the completed unit-Riesz CCM source

Literal completed response has constant right-tail charge and therefore cannot be an HG leak
profile.  Its shift codiagonal removes precisely that constant mode.  This module proves:

* exact two-exponential tail formula and decay of every shift codiagonal;
* finite and infinite telescoping reconstruction of the original completed response;
* vanishing at the zero boundary, hence exact recovery of half the arithmetic resolvent as the
  infinite discrete integral of shift-codiagonal bulk;
* a continuous closed representative whose complex lift is an admissible HG `LeakProfile`.

This is a source-faithful principal-relative replacement for the impossible direct CCM-to-HG
embedding: no arithmetic information is discarded; constant charge becomes a boundary coordinate
reconstructed from decaying bulk increments.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

def unitRieszCoherentCompletedShiftCodiagonal (N : ℕ) (h u : ℝ) : ℝ :=
  unitRieszCoherentCompletedKernelResponse N (u + h) -
    unitRieszCoherentCompletedKernelResponse N u

theorem unitRieszCoherentCompletedShiftCodiagonal_eq_rightTail
    {N : ℕ} (hN : 2 ≤ N) {h u : ℝ} (hh : 0 ≤ h) (hu : Real.log N ≤ u) :
    unitRieszCoherentCompletedShiftCodiagonal N h u =
      Real.exp (-u / 2) * (Real.exp (-h / 2) - 1) *
          (unitRieszCoherentPrimeKernelTailMode N N - Real.sqrt N) +
        (4 / 3) * Real.sqrt N * Real.exp (-u) * (Real.exp (-h) - 1) := by
  have huh : Real.log N ≤ u + h := by linarith
  rw [unitRieszCoherentCompletedShiftCodiagonal,
    unitRieszCoherentCompletedKernelResponse_eq_rightTail hN huh,
    unitRieszCoherentCompletedKernelResponse_eq_rightTail hN hu]
  have heh : Real.exp (-(u + h) / 2) =
      Real.exp (-u / 2) * Real.exp (-h / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he : Real.exp (-(u + h)) = Real.exp (-u) * Real.exp (-h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heh, he]
  ring

theorem tendsto_unitRieszCoherentCompletedShiftCodiagonal
    {N : ℕ} (hN : 2 ≤ N) (h : ℝ) :
    Tendsto (unitRieszCoherentCompletedShiftCodiagonal N h) atTop (𝓝 0) := by
  have hlim := tendsto_unitRieszCoherentCompletedKernelResponse hN
  unfold unitRieszCoherentCompletedShiftCodiagonal
  have hshift : Tendsto (fun u : ℝ => u + h) atTop atTop :=
    tendsto_atTop_add_const_right atTop h tendsto_id
  simpa using (hlim.comp hshift).sub hlim

theorem sum_unitRieszCoherentCompletedShiftCodiagonal
    (N : ℕ) (h u : ℝ) (m : ℕ) :
    (∑ j ∈ Finset.range m,
        unitRieszCoherentCompletedShiftCodiagonal N h (u + j * h)) =
      unitRieszCoherentCompletedKernelResponse N (u + m * h) -
        unitRieszCoherentCompletedKernelResponse N u := by
  let f : ℕ → ℝ := fun j =>
    unitRieszCoherentCompletedKernelResponse N (u + j * h)
  have htel := Finset.sum_range_sub f m
  dsimp only [f] at htel
  simp only [Nat.cast_zero, zero_mul, add_zero] at htel
  rw [← htel]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [unitRieszCoherentCompletedShiftCodiagonal]
  congr 2
  all_goals push_cast
  all_goals ring

theorem unitExponentialIncrementKernel_zero_right {p : ℝ} (hp : 0 ≤ p) :
    unitExponentialIncrementKernel p 0 = 0 := by
  simp only [unitExponentialIncrementKernel, zero_div, neg_zero, Real.exp_zero, sub_zero,
    abs_of_nonneg hp]
  ring

theorem unitRieszCoherentPrimeKernelResponse_zero {N : ℕ} (hN : 2 ≤ N) :
    unitRieszCoherentPrimeKernelResponse N N 0 = 0 := by
  rw [unitRieszCoherentPrimeKernelResponse]
  apply Finset.sum_eq_zero
  intro k hk
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk2)
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hlog : Real.log k ≤ Real.log N :=
    Real.strictMonoOn_log.monotoneOn hkpos hNpos (by exact_mod_cast hkN)
  rw [unitExponentialIncrementKernel_zero_right (sub_nonneg.mpr hlog), mul_zero]

theorem unitRieszCoherentCompletedKernelResponse_zero {N : ℕ} (hN : 2 ≤ N) :
    unitRieszCoherentCompletedKernelResponse N 0 = 0 := by
  rw [unitRieszCoherentCompletedKernelResponse,
    unitRieszCoherentPrimeKernelResponse_zero hN,
    unitRieszCoherentPolarKernelResponse_eq (by norm_num : (0 : ℝ) ≤ 0)]
  norm_num

/-- Source-faithful relative carrier: infinite shift-codiagonal bulk plus the arithmetic tail
charge reconstructs the literal completed coherent response exactly. -/
theorem tendsto_sum_unitRieszCoherentCompletedShiftCodiagonal
    {N : ℕ} (hN : 2 ≤ N) {h : ℝ} (hh : 0 < h) (u : ℝ) :
    Tendsto (fun m : ℕ =>
        ∑ j ∈ Finset.range m,
          unitRieszCoherentCompletedShiftCodiagonal N h (u + j * h))
      atTop
      (𝓝 (criticalMellinChebyshevResolventSource (Real.log N) / 2 -
        unitRieszCoherentCompletedKernelResponse N u)) := by
  have hargMul : Tendsto (fun m : ℕ => (m : ℝ) * h) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hh
  have harg : Tendsto (fun m : ℕ => u + (m : ℝ) * h) atTop atTop :=
    tendsto_atTop_add_const_left atTop u hargMul
  have hcomp := (tendsto_unitRieszCoherentCompletedKernelResponse hN).comp harg
  have hsub := hcomp.sub_const (unitRieszCoherentCompletedKernelResponse N u)
  refine hsub.congr' ?_
  filter_upwards with m
  exact (sum_unitRieszCoherentCompletedShiftCodiagonal N h u m).symm

/-- The CCM arithmetic resolvent charge is exactly the infinite discrete integral of the decaying
shift-codiagonal bulk. Thus codiagonalization loses no source information: it moves the forbidden
constant tail to a reconstructible boundary coordinate. -/
theorem tendsto_sum_unitRieszCoherentCompletedShiftCodiagonal_zero
    {N : ℕ} (hN : 2 ≤ N) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun m : ℕ =>
        ∑ j ∈ Finset.range m,
          unitRieszCoherentCompletedShiftCodiagonal N h (j * h))
      atTop (𝓝 (criticalMellinChebyshevResolventSource (Real.log N) / 2)) := by
  simpa [unitRieszCoherentCompletedKernelResponse_zero hN] using
    tendsto_sum_unitRieszCoherentCompletedShiftCodiagonal hN hh 0

def unitRieszCoherentCompletedKernelResponseClosed (N : ℕ) (u : ℝ) : ℝ :=
  unitRieszCoherentPrimeKernelResponse N N u -
    Real.sqrt N * (1 / 3 + Real.exp (-u / 2) - (4 / 3) * Real.exp (-u))

theorem unitRieszCoherentCompletedKernelResponseClosed_eq
    {N : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    unitRieszCoherentCompletedKernelResponseClosed N u =
      unitRieszCoherentCompletedKernelResponse N u := by
  rw [unitRieszCoherentCompletedKernelResponseClosed,
    unitRieszCoherentCompletedKernelResponse,
    unitRieszCoherentPolarKernelResponse_eq hu]

theorem continuous_unitRieszCoherentCompletedKernelResponseClosed (N : ℕ) :
    Continuous (unitRieszCoherentCompletedKernelResponseClosed N) := by
  unfold unitRieszCoherentCompletedKernelResponseClosed
  unfold unitRieszCoherentPrimeKernelResponse unitExponentialIncrementKernel
  fun_prop

def unitRieszCoherentCompletedShiftCodiagonalProfile (N : ℕ) (h u : ℝ) : ℂ :=
  ((unitRieszCoherentCompletedKernelResponseClosed N (u + h) -
    unitRieszCoherentCompletedKernelResponseClosed N u : ℝ) : ℂ)

theorem continuous_unitRieszCoherentCompletedShiftCodiagonalProfile (N : ℕ) (h : ℝ) :
    Continuous (unitRieszCoherentCompletedShiftCodiagonalProfile N h) := by
  unfold unitRieszCoherentCompletedShiftCodiagonalProfile
  exact Complex.continuous_ofReal.comp
    (((continuous_unitRieszCoherentCompletedKernelResponseClosed N).comp
      (continuous_id.add continuous_const)).sub
      (continuous_unitRieszCoherentCompletedKernelResponseClosed N))

theorem leakDensity_unitRieszCoherentCompletedShiftCodiagonalProfile (N : ℕ) (h u : ℝ) :
    leakDensity (unitRieszCoherentCompletedShiftCodiagonalProfile N h) u =
      (unitRieszCoherentCompletedKernelResponseClosed N (u + h) -
        unitRieszCoherentCompletedKernelResponseClosed N u) ^ 2 := by
  rw [leakDensity, unitRieszCoherentCompletedShiftCodiagonalProfile, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

theorem unitRieszCoherentCompletedShiftCodiagonalProfile_eq
    {N : ℕ} {h u : ℝ} (hh : 0 ≤ h) (hu : 0 ≤ u) :
    (unitRieszCoherentCompletedShiftCodiagonalProfile N h u).re =
      unitRieszCoherentCompletedShiftCodiagonal N h u := by
  rw [unitRieszCoherentCompletedShiftCodiagonalProfile, Complex.ofReal_re,
    unitRieszCoherentCompletedKernelResponseClosed_eq hu,
    unitRieszCoherentCompletedKernelResponseClosed_eq (by linarith : 0 ≤ u + h)]
  rfl

/-- Shift-codiagonal bulk is an admissible HG profile: constant arithmetic charge is removed while
all finite-lag source response remains. -/
theorem leakProfile_unitRieszCoherentCompletedShiftCodiagonalProfile
    {N : ℕ} (hN : 2 ≤ N) {h : ℝ} (hh : 0 ≤ h) :
    LeakProfile (unitRieszCoherentCompletedShiftCodiagonalProfile N h) := by
  constructor
  · exact (continuous_unitRieszCoherentCompletedShiftCodiagonalProfile N h).measurable
      |>.aestronglyMeasurable
  · let D : ℝ → ℝ := fun u =>
      unitRieszCoherentCompletedKernelResponseClosed N (u + h) -
        unitRieszCoherentCompletedKernelResponseClosed N u
    let A : ℝ := (Real.exp (-h / 2) - 1) *
      (unitRieszCoherentPrimeKernelTailMode N N - Real.sqrt N)
    let B : ℝ := (4 / 3) * Real.sqrt N * (Real.exp (-h) - 1)
    let F : ℝ → ℝ := fun u =>
      (1 + u) * leakDensity (unitRieszCoherentCompletedShiftCodiagonalProfile N h) u
    have hlog : 0 ≤ Real.log N := Real.log_nonneg (by
      have hN1 : 1 ≤ N := by omega
      exact_mod_cast hN1)
    have hcompact : IntegrableOn F (Ioc (0 : ℝ) (Real.log N)) := by
      have hcD : Continuous D := by
        dsimp only [D]
        exact ((continuous_unitRieszCoherentCompletedKernelResponseClosed N).comp
          (continuous_id.add continuous_const)).sub
            (continuous_unitRieszCoherentCompletedKernelResponseClosed N)
      have hcF : Continuous F := by
        have heq : F = fun u => (1 + u) * D u ^ 2 := by
          funext u
          dsimp only [F]
          rw [leakDensity_unitRieszCoherentCompletedShiftCodiagonalProfile]
        rw [heq]
        exact (continuous_const.add continuous_id).mul (hcD.pow 2)
      exact hcF.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have htailEq : ∀ u ∈ Ioi (Real.log N), D u =
        A * Real.exp (-u / 2) + B * Real.exp (-u) := by
      intro u hu
      have hu0 : 0 ≤ u := le_trans hlog hu.le
      dsimp only [D]
      rw [unitRieszCoherentCompletedKernelResponseClosed_eq hu0,
        unitRieszCoherentCompletedKernelResponseClosed_eq (by linarith : 0 ≤ u + h)]
      rw [show unitRieszCoherentCompletedKernelResponse N (u + h) -
          unitRieszCoherentCompletedKernelResponse N u =
        unitRieszCoherentCompletedShiftCodiagonal N h u from rfl,
        unitRieszCoherentCompletedShiftCodiagonal_eq_rightTail hN hh hu.le]
      dsimp only [A, B]
      ring
    have hbase1 : IntegrableOn (fun u : ℝ => (1 + u) * Real.exp (-1 * u))
        (Ioi (Real.log N)) :=
      (integrableOn_one_add_mul_exp_neg (b := 1) one_pos).mono_set (Ioi_subset_Ioi hlog)
    have hbase3 : IntegrableOn (fun u : ℝ => (1 + u) * Real.exp (-(3 / 2) * u))
        (Ioi (Real.log N)) :=
      (integrableOn_one_add_mul_exp_neg (b := 3 / 2) (by norm_num)).mono_set
        (Ioi_subset_Ioi hlog)
    have hbase2 : IntegrableOn (fun u : ℝ => (1 + u) * Real.exp (-2 * u))
        (Ioi (Real.log N)) :=
      (integrableOn_one_add_mul_exp_neg (b := 2) (by norm_num)).mono_set
        (Ioi_subset_Ioi hlog)
    have htailBase : IntegrableOn (fun u : ℝ =>
        A ^ 2 * ((1 + u) * Real.exp (-1 * u)) +
          (2 * A * B) * ((1 + u) * Real.exp (-(3 / 2) * u)) +
          B ^ 2 * ((1 + u) * Real.exp (-2 * u))) (Ioi (Real.log N)) :=
      ((hbase1.const_mul _).add (hbase3.const_mul _)).add (hbase2.const_mul _)
    have htail : IntegrableOn F (Ioi (Real.log N)) := by
      refine htailBase.congr_fun ?_ measurableSet_Ioi
      intro u hu
      dsimp only [F]
      rw [leakDensity_unitRieszCoherentCompletedShiftCodiagonalProfile]
      change A ^ 2 * ((1 + u) * Real.exp (-1 * u)) +
          (2 * A * B) * ((1 + u) * Real.exp (-(3 / 2) * u)) +
          B ^ 2 * ((1 + u) * Real.exp (-2 * u)) = (1 + u) * D u ^ 2
      rw [htailEq u hu]
      have e1 : Real.exp (-u / 2) ^ 2 = Real.exp (-1 * u) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      have e3 : Real.exp (-u / 2) * Real.exp (-u) =
          Real.exp (-(3 / 2) * u) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have e2 : Real.exp (-u) ^ 2 = Real.exp (-2 * u) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [← e1, ← e3, ← e2]
      ring
    have hs : Ioi (0 : ℝ) = Ioc 0 (Real.log N) ∪ Ioi (Real.log N) :=
      (Ioc_union_Ioi_eq_Ioi hlog).symm
    rw [hs]
    exact hcompact.union htail


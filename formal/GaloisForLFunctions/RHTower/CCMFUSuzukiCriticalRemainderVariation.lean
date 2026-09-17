import GaloisForLFunctions.RHTower.SuzukiCriticalOrderedJordanCancellation
import GaloisForLFunctions.RHTower.SuzukiTriangularCurvatureRHClassification
import GaloisForLFunctions.RHTower.SuzukiFirstMomentTriangularAbelTransfer
import GaloisForLFunctions.RHTower.WeilLagFunctionFrontier
import GaloisForLFunctions.HTGeometry.ShiftPartialSummation

open Set
open scoped BigOperators

namespace RHTower

open HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

/-- Critical rescaling of the literal third-grade triangular checkpoint weight. -/
def suzukiCheckpointCriticalTriangularMultiplier (H : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt ((n + 3 : ℕ) : ℝ) *
    ccmGuinandWeilThirdGradeCesaroTriangularWeight H
      (Real.log ((n + 3 : ℕ) : ℝ))

/-- Remainder after subtracting the exact Mertens--Gamma critical finite part. -/
def suzukiCheckpointCriticalOrderedRemainder (N : ℕ) : ℝ :=
  suzukiCheckpointCriticalOrderedPrefix N - suzukiCheckpointCriticalOrderedLimit

/-- Abel variation action of a checkpoint profile against the critical triangular multiplier. -/
def suzukiCheckpointCriticalVariationAction (r : ℕ → ℝ) (H : ℝ) : ℝ :=
  let n := suzukiCheckpointEventIndex H - 2
  r n *
      suzukiCheckpointCriticalTriangularMultiplier H n -
    ∑ j ∈ Finset.range n,
      r (j + 1) *
        (suzukiCheckpointCriticalTriangularMultiplier H (j + 1) -
          suzukiCheckpointCriticalTriangularMultiplier H j)

/-- Abel variation action of the actual critical-prefix remainder. -/
def suzukiCheckpointCriticalRemainderVariationAction (H : ℝ) : ℝ :=
  suzukiCheckpointCriticalVariationAction
    suzukiCheckpointCriticalOrderedRemainder H

/-- Exact Mertens deviation at the endpoint of the first `N` source-valid cells. -/
def suzukiCheckpointCriticalMertensDeviation (N : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 (N + 2),
      ArithmeticFunction.vonMangoldt k / (k : ℝ)) -
    Real.log ((N + 2 : ℕ) : ℝ) + Real.eulerMascheroniConstant

/-- Source-free remainder: Gamma-cell series tail plus the harmonic Euler remainder. -/
def suzukiCheckpointCriticalSourceFreeRemainder (N : ℕ) : ℝ :=
  ((∑ n ∈ Finset.range N, suzukiCheckpointCriticalArchCorrection n) -
      ∑' n : ℕ, suzukiCheckpointCriticalArchCorrection n) +
    ((harmonic (N + 2) : ℝ) - Real.log ((N + 2 : ℕ) : ℝ) -
      Real.eulerMascheroniConstant)

/-- Local harmonic-versus-log discrepancy at endpoint `N + 3`. -/
def suzukiCheckpointCriticalHarmonicCell (N : ℕ) : ℝ :=
  1 / ((N + 3 : ℕ) : ℝ) -
    (Real.log ((N + 3 : ℕ) : ℝ) - Real.log ((N + 2 : ℕ) : ℝ))

theorem tendsto_suzukiCheckpointCriticalOrderedRemainder_zero :
    Filter.Tendsto suzukiCheckpointCriticalOrderedRemainder Filter.atTop (nhds 0) := by
  unfold suzukiCheckpointCriticalOrderedRemainder
  simpa only [sub_self] using
    tendsto_suzukiCheckpointCriticalOrderedPrefix.sub_const
      suzukiCheckpointCriticalOrderedLimit

private theorem sum_vonMangoldt_div_Icc_one_two_local :
    (∑ k ∈ Finset.Icc 1 2,
      ArithmeticFunction.vonMangoldt k / (k : ℝ)) = Real.log 2 / 2 := by
  rw [show 2 = 1 + 1 by omega,
    Finset.sum_Icc_succ_top (a := 1) (b := 1) (by omega)
      (fun k : ℕ => ArithmeticFunction.vonMangoldt k / (k : ℝ))]
  norm_num [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

/-- Exact critical-prefix separation. Arithmetic content is one signed Mertens deviation; all
other finite-part error is source-free. -/
theorem suzukiCheckpointCriticalOrderedRemainder_eq_sourceFree_sub_mertensDeviation
    (N : ℕ) :
    suzukiCheckpointCriticalOrderedRemainder N =
      suzukiCheckpointCriticalSourceFreeRemainder N -
        suzukiCheckpointCriticalMertensDeviation N := by
  rw [suzukiCheckpointCriticalOrderedRemainder,
    suzukiCheckpointCriticalOrderedPrefix_eq_centered]
  unfold suzukiCheckpointCriticalOrderedLimit
    suzukiCheckpointCriticalSourceFreeRemainder
    suzukiCheckpointCriticalMertensDeviation
  rw [show (harmonic 2 : ℝ) = 3 / 2 by norm_num [harmonic],
    sum_vonMangoldt_div_Icc_one_two_local]
  ring

/-- Exact compensated-Chebyshev representation of the arithmetic remainder.  The endpoint error
and its full future tail remain coupled; estimating either summand separately loses the Mertens
cancellation. -/
theorem suzukiCheckpointCriticalMertensDeviation_eq_chebyshev_endpoint_sub_tail
    (N : ℕ) :
    suzukiCheckpointCriticalMertensDeviation N =
      chebyshevError (((N + 2 : ℕ) : ℝ)) / (((N + 2 : ℕ) : ℝ)) -
        ∫ t in Set.Ioi (((N + 2 : ℕ) : ℝ)), chebyshevError t / t ^ 2 := by
  have h := mertensDeviation_eq
    (x := (((N + 2 : ℕ) : ℝ)))
      (by exact_mod_cast (by omega : 1 ≤ N + 2))
  norm_num only [Nat.floor_natCast] at h
  rw [← mertensSum_eq_Icc_zero] at h
  change mertensSum (N + 2) - Real.log ((N + 2 : ℕ) : ℝ) +
      Real.eulerMascheroniConstant = _
  exact h

/-- One literal prime--polar increment of the sole arithmetic critical remainder. -/
theorem suzukiCheckpointCriticalMertensDeviation_succ_sub (N : ℕ) :
    suzukiCheckpointCriticalMertensDeviation (N + 1) -
        suzukiCheckpointCriticalMertensDeviation N =
      ArithmeticFunction.vonMangoldt (N + 3) / ((N + 3 : ℕ) : ℝ) -
        (Real.log ((N + 3 : ℕ) : ℝ) - Real.log ((N + 2 : ℕ) : ℝ)) := by
  unfold suzukiCheckpointCriticalMertensDeviation
  rw [show N + 1 + 2 = N + 2 + 1 by omega,
    Finset.sum_Icc_succ_top (a := 1) (b := N + 2) (by omega)
      (fun k : ℕ => ArithmeticFunction.vonMangoldt k / (k : ℝ))]
  ring

/-- The variation action is linear under source separation. -/
theorem suzukiCheckpointCriticalVariationAction_sub
    (r s : ℕ → ℝ) (H : ℝ) :
    suzukiCheckpointCriticalVariationAction (fun N => r N - s N) H =
      suzukiCheckpointCriticalVariationAction r H -
        suzukiCheckpointCriticalVariationAction s H := by
  simp only [suzukiCheckpointCriticalVariationAction]
  have hsum :
      (∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
        (r (j + 1) - s (j + 1)) *
          (suzukiCheckpointCriticalTriangularMultiplier H (j + 1) -
            suzukiCheckpointCriticalTriangularMultiplier H j)) =
        (∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
          r (j + 1) *
            (suzukiCheckpointCriticalTriangularMultiplier H (j + 1) -
              suzukiCheckpointCriticalTriangularMultiplier H j)) -
        ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
          s (j + 1) *
            (suzukiCheckpointCriticalTriangularMultiplier H (j + 1) -
              suzukiCheckpointCriticalTriangularMultiplier H j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hsum]
  ring

/-- Any profile action is its initial value plus the multiplier-weighted profile increments. -/
theorem suzukiCheckpointCriticalVariationAction_eq_initial_add_incrementSum
    (r : ℕ → ℝ) (H : ℝ) :
    suzukiCheckpointCriticalVariationAction r H =
      r 0 * suzukiCheckpointCriticalTriangularMultiplier H 0 +
        ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
          (r (j + 1) - r j) *
            suzukiCheckpointCriticalTriangularMultiplier H j := by
  let w := suzukiCheckpointCriticalTriangularMultiplier H
  let n := suzukiCheckpointEventIndex H - 2
  have hfinite : ∀ m : ℕ,
      r m * w m - ∑ j ∈ Finset.range m, r (j + 1) * (w (j + 1) - w j) =
        r 0 * w 0 + ∑ j ∈ Finset.range m, (r (j + 1) - r j) * w j := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        calc
          r (m + 1) * w (m + 1) -
              ((∑ j ∈ Finset.range m, r (j + 1) * (w (j + 1) - w j)) +
                r (m + 1) * (w (m + 1) - w m)) =
            (r m * w m -
              ∑ j ∈ Finset.range m, r (j + 1) * (w (j + 1) - w j)) +
                (r (m + 1) - r m) * w m := by ring
          _ = r 0 * w 0 +
              (∑ j ∈ Finset.range m, (r (j + 1) - r j) * w j) +
                (r (m + 1) - r m) * w m := by rw [ih]
          _ = r 0 * w 0 +
              ((∑ j ∈ Finset.range m, (r (j + 1) - r j) * w j) +
                (r (m + 1) - r m) * w m) := by abel
  unfold suzukiCheckpointCriticalVariationAction
  simpa only [n, w] using hfinite n

/-- Exact source form of the RH-equivalent critical variation action.  The full moving
prime--polar history is retained under its literal triangular multiplier; no unsigned or
endpoint-only substitute has been taken. -/
theorem suzukiCheckpointCriticalMertensDeviationVariationAction_eq_weightedPrimePolar
    (H : ℝ) :
    suzukiCheckpointCriticalVariationAction suzukiCheckpointCriticalMertensDeviation H =
      suzukiCheckpointCriticalMertensDeviation 0 *
          suzukiCheckpointCriticalTriangularMultiplier H 0 +
        ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
          (ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ) -
            (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ))) *
            suzukiCheckpointCriticalTriangularMultiplier H j := by
  rw [suzukiCheckpointCriticalVariationAction_eq_initial_add_incrementSum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  rw [suzukiCheckpointCriticalMertensDeviation_succ_sub]

/-- The source-free finite-part remainder has an exact local increment: one Gamma correction
plus one harmonic-versus-log cell defect. -/
theorem suzukiCheckpointCriticalSourceFreeRemainder_succ_sub
    (N : ℕ) :
    suzukiCheckpointCriticalSourceFreeRemainder (N + 1) -
        suzukiCheckpointCriticalSourceFreeRemainder N =
      suzukiCheckpointCriticalArchCorrection N +
        suzukiCheckpointCriticalHarmonicCell N := by
  unfold suzukiCheckpointCriticalSourceFreeRemainder
  unfold suzukiCheckpointCriticalHarmonicCell
  rw [Finset.sum_range_succ, harmonic_succ (N + 2),
    Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
  push_cast
  ring

/-- Sharp elementary cell bound for the harmonic finite-part correction. -/
theorem abs_suzukiCheckpointCriticalHarmonicCell_le (N : ℕ) :
    |suzukiCheckpointCriticalHarmonicCell N| ≤
      1 / (((N + 2 : ℕ) : ℝ) * ((N + 3 : ℕ) : ℝ)) := by
  let a : ℝ := ((N + 2 : ℕ) : ℝ)
  let b : ℝ := ((N + 3 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  have hba : b = a + 1 := by dsimp only [a, b]; push_cast; ring
  have hratio : 0 < b / a := div_pos hb ha
  have hlogeq : Real.log (b / a) = Real.log b - Real.log a :=
    Real.log_div hb.ne' ha.ne'
  have hlowerRaw := Real.one_sub_inv_le_log_of_pos hratio
  have hlower : 1 / b ≤ Real.log b - Real.log a := by
    rw [← hlogeq]
    calc
      1 / b = 1 - (b / a)⁻¹ := by rw [hba]; field_simp; ring
      _ ≤ Real.log (b / a) := hlowerRaw
  have hupperRaw := Real.log_le_sub_one_of_pos hratio
  have hupper : Real.log b - Real.log a ≤ 1 / a := by
    rw [← hlogeq]
    calc
      Real.log (b / a) ≤ b / a - 1 := hupperRaw
      _ = 1 / a := by rw [hba]; field_simp; ring
  have hnonpos : 1 / b - (Real.log b - Real.log a) ≤ 0 := by linarith
  unfold suzukiCheckpointCriticalHarmonicCell
  change |1 / b - (Real.log b - Real.log a)| ≤ 1 / (a * b)
  rw [abs_of_nonpos hnonpos]
  have hgap : 1 / a - 1 / b = 1 / (a * b) := by
    rw [hba]
    field_simp
    ring
  rw [← hgap]
  linarith

/-- Exact action-level separation. Prime--polar arithmetic remains coupled inside the Mertens
deviation; Gamma and harmonic finite-part errors form a disjoint source-free action. -/
theorem suzukiCheckpointCriticalRemainderVariationAction_eq_sourceFree_sub_mertensDeviation
    (H : ℝ) :
    suzukiCheckpointCriticalRemainderVariationAction H =
      suzukiCheckpointCriticalVariationAction
          suzukiCheckpointCriticalSourceFreeRemainder H -
        suzukiCheckpointCriticalVariationAction
          suzukiCheckpointCriticalMertensDeviation H := by
  have hprofile : suzukiCheckpointCriticalOrderedRemainder =
      fun N => suzukiCheckpointCriticalSourceFreeRemainder N -
        suzukiCheckpointCriticalMertensDeviation N := by
    funext N
    exact
      suzukiCheckpointCriticalOrderedRemainder_eq_sourceFree_sub_mertensDeviation N
  unfold suzukiCheckpointCriticalRemainderVariationAction
  rw [hprofile, suzukiCheckpointCriticalVariationAction_sub]

private theorem criticalTerm_mul_multiplier_eq (H : ℝ) (n : ℕ) :
    suzukiCheckpointCriticalOrderedTerm n *
        suzukiCheckpointCriticalTriangularMultiplier H n =
      suzukiCheckpointSignedCurvatureCell (n + 2) *
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H
          (Real.log ((n + 3 : ℕ) : ℝ)) := by
  have hx : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := by positivity
  have hs : Real.sqrt ((n + 3 : ℕ) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hx).ne'
  unfold suzukiCheckpointCriticalOrderedTerm
    suzukiCheckpointCurvaturePowerDamping
    suzukiCheckpointCriticalTriangularMultiplier
  rw [show n + 2 + 1 = n + 3 by omega, Real.rpow_neg hx.le,
    ← Real.sqrt_eq_rpow]
  field_simp [hs]

private theorem triangularTransform_eq_criticalWeightedSum
    {H : ℝ} (hH : 2 ≤ H) :
    suzukiCheckpointTriangularCurvatureTransform H =
      ∑ n ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
        suzukiCheckpointCriticalOrderedTerm n *
          suzukiCheckpointCriticalTriangularMultiplier H n := by
  have hlog2one : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  obtain ⟨hM2, _⟩ := suzukiCheckpointEventIndex_two_le_and_mem_cell
    (hlog2one.trans (one_le_two.trans hH))
  let M := suzukiCheckpointEventIndex H
  let m := M - 2
  have hmM : m + 2 = M := Nat.sub_add_cancel hM2
  let term : ℕ → ℝ := fun j =>
    suzukiCheckpointSignedCurvatureCell j *
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H
        (Real.log ((j + 1 : ℕ) : ℝ))
  have hshift := Finset.sum_Ico_add term 0 m 2
  have hzero : Finset.Ico 0 m = Finset.range m := by
    ext i
    simp
  rw [hzero, hmM] at hshift
  unfold suzukiCheckpointTriangularCurvatureTransform
  change (∑ j ∈ Finset.Ico 2 M, term j) = _
  rw [← hshift]
  apply Finset.sum_congr rfl
  intro n _hn
  simpa only [term, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (criticalTerm_mul_multiplier_eq H n).symm

/-- Exact source-side renormalized Abel law. The convergent critical finite part telescopes to
one base multiplier; all moving-cutoff arithmetic remains in one signed remainder-variation
pairing. -/
theorem suzukiCheckpointTriangularCurvatureTransform_eq_criticalFinitePart_add_remainderVariation
    {H : ℝ} (hH : 2 ≤ H) :
    suzukiCheckpointTriangularCurvatureTransform H =
      suzukiCheckpointCriticalOrderedLimit *
          suzukiCheckpointCriticalTriangularMultiplier H 0 +
        suzukiCheckpointCriticalRemainderVariationAction H := by
  rw [triangularTransform_eq_criticalWeightedSum hH]
  let n := suzukiCheckpointEventIndex H - 2
  let f := suzukiCheckpointCriticalOrderedTerm
  let w := suzukiCheckpointCriticalTriangularMultiplier H
  have hab := HTGeometry.sum_mul_weight_eq f w n
  rw [hab]
  unfold suzukiCheckpointCriticalRemainderVariationAction
    suzukiCheckpointCriticalVariationAction
  dsimp only [n, f, w]
  unfold suzukiCheckpointCriticalOrderedRemainder
  have htel :
      (∑ j ∈ Finset.range n,
        (suzukiCheckpointCriticalTriangularMultiplier H (j + 1) -
          suzukiCheckpointCriticalTriangularMultiplier H j)) =
        suzukiCheckpointCriticalTriangularMultiplier H n -
          suzukiCheckpointCriticalTriangularMultiplier H 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hpartial (N : ℕ) :
      HTGeometry.partialSum suzukiCheckpointCriticalOrderedTerm N =
        suzukiCheckpointCriticalOrderedPrefix N := rfl
  simp_rw [hpartial]
  have hsum :
      (∑ j ∈ Finset.range n,
        suzukiCheckpointCriticalOrderedPrefix (j + 1) *
          (suzukiCheckpointCriticalTriangularMultiplier H (j + 1) -
            suzukiCheckpointCriticalTriangularMultiplier H j)) =
        suzukiCheckpointCriticalOrderedLimit *
          (∑ j ∈ Finset.range n,
            (suzukiCheckpointCriticalTriangularMultiplier H (j + 1) -
              suzukiCheckpointCriticalTriangularMultiplier H j)) +
        ∑ j ∈ Finset.range n,
          (suzukiCheckpointCriticalOrderedPrefix (j + 1) -
            suzukiCheckpointCriticalOrderedLimit) *
              (suzukiCheckpointCriticalTriangularMultiplier H (j + 1) -
                suzukiCheckpointCriticalTriangularMultiplier H j) := by
    calc
      _ = ∑ j ∈ Finset.range n,
          (suzukiCheckpointCriticalOrderedLimit *
              (suzukiCheckpointCriticalTriangularMultiplier H (j + 1) -
                suzukiCheckpointCriticalTriangularMultiplier H j) +
            (suzukiCheckpointCriticalOrderedPrefix (j + 1) -
              suzukiCheckpointCriticalOrderedLimit) *
                (suzukiCheckpointCriticalTriangularMultiplier H (j + 1) -
                  suzukiCheckpointCriticalTriangularMultiplier H j)) := by
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = (∑ j ∈ Finset.range n,
            suzukiCheckpointCriticalOrderedLimit *
              (suzukiCheckpointCriticalTriangularMultiplier H (j + 1) -
                suzukiCheckpointCriticalTriangularMultiplier H j)) +
          ∑ j ∈ Finset.range n,
            (suzukiCheckpointCriticalOrderedPrefix (j + 1) -
              suzukiCheckpointCriticalOrderedLimit) *
                (suzukiCheckpointCriticalTriangularMultiplier H (j + 1) -
                  suzukiCheckpointCriticalTriangularMultiplier H j) :=
            Finset.sum_add_distrib
      _ = _ := by rw [← Finset.mul_sum]
  rw [hsum, htel]
  ring

/-- At every physical aperture the base critical multiplier has an absolute uniform bound. -/
theorem abs_suzukiCheckpointCriticalTriangularMultiplier_zero_le
    {H : ℝ} (hH : 2 ≤ H) :
    |suzukiCheckpointCriticalTriangularMultiplier H 0| ≤
      32 * Real.sqrt 3 := by
  let x : ℝ := Real.log 3
  have hx1 : 1 ≤ x := by
    dsimp only [x]
    have h := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
    simpa using h
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hx2 : x ≤ 2 := by
    dsimp only [x]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have hH0 : 0 < H := by linarith
  have hratio0 : 0 ≤ x / H := div_nonneg hx0.le hH0.le
  have hratio1 : x / H ≤ 1 := (div_le_one hH0).2 (hx2.trans hH)
  have hfactor0 : 0 ≤ 1 - x / H := by linarith
  have hfactor1 : 1 - x / H ≤ 1 := by linarith
  have hxpow : 1 ≤ x ^ 3 := one_le_pow₀ hx1
  have hweight0 : 0 ≤ 32 / x ^ 3 := div_nonneg (by norm_num) (pow_nonneg hx0.le 3)
  have hweight1 : 32 / x ^ 3 ≤ 32 := by
    apply (div_le_iff₀ (pow_pos hx0 3)).2
    nlinarith
  have hsqrt0 : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  unfold suzukiCheckpointCriticalTriangularMultiplier
    ccmGuinandWeilThirdGradeCesaroTriangularWeight
    ccmGuinandWeilThirdGradeWeight
  norm_num only [Nat.cast_ofNat, Nat.zero_add]
  change |Real.sqrt 3 * (32 / x ^ 3 * (1 - x / H))| ≤ _
  rw [abs_mul, abs_mul, abs_of_nonneg hsqrt0, abs_of_nonneg hweight0,
    abs_of_nonneg hfactor0]
  have hwf : 32 / x ^ 3 * (1 - x / H) ≤ 32 := by
    calc
      32 / x ^ 3 * (1 - x / H) ≤ 32 * (1 - x / H) :=
        mul_le_mul_of_nonneg_right hweight1 hfactor0
      _ ≤ 32 * 1 := mul_le_mul_of_nonneg_left hfactor1 (by norm_num)
      _ = 32 := by ring
  exact (mul_le_mul_of_nonneg_left hwf hsqrt0).trans_eq (by ring)

/-- On the active checkpoint range, the critical multiplier is bounded by its cubic-log
envelope. -/
theorem abs_suzukiCheckpointCriticalTriangularMultiplier_le
    {H : ℝ} (hH : 2 ≤ H) {j : ℕ}
    (hj : j ∈ Finset.range (suzukiCheckpointEventIndex H - 2)) :
    |suzukiCheckpointCriticalTriangularMultiplier H j| ≤
      32 * Real.sqrt ((j + 3 : ℕ) : ℝ) *
        HTGeometry.shiftedReciprocalLogPotential 3 j := by
  have hlog2one : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  obtain ⟨hM2, _⟩ := suzukiCheckpointEventIndex_two_le_and_mem_cell
    (hlog2one.trans (one_le_two.trans hH))
  have hjlt : j < suzukiCheckpointEventIndex H - 2 := Finset.mem_range.mp hj
  have hjcell : j + 2 ∈ Finset.Ico 2 (suzukiCheckpointEventIndex H) := by
    rw [Finset.mem_Ico]
    omega
  have hlog := one_lt_log_event_succ_and_log_event_succ_le hjcell
  let x : ℝ := (j : ℝ) + 3
  have hx1 : 1 ≤ Real.log x := by
    dsimp only [x]
    exact HTGeometry.one_le_log_natCast_add_three j
  have hxlog0 : 0 < Real.log x := zero_lt_one.trans_le hx1
  have hxH : Real.log x ≤ H := by
    dsimp only [x]
    convert hlog.2 using 1 <;> push_cast <;> ring
  have hH0 : 0 < H := by linarith
  have hratio0 : 0 ≤ Real.log x / H := div_nonneg hxlog0.le hH0.le
  have hratio1 : Real.log x / H ≤ 1 := (div_le_one hH0).2 hxH
  have hfactor0 : 0 ≤ 1 - Real.log x / H := by linarith
  have hfactor1 : 1 - Real.log x / H ≤ 1 := by linarith
  have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hweight0 : 0 ≤ 32 / Real.log x ^ 3 := by positivity
  unfold suzukiCheckpointCriticalTriangularMultiplier
    ccmGuinandWeilThirdGradeCesaroTriangularWeight
    ccmGuinandWeilThirdGradeWeight
    HTGeometry.shiftedReciprocalLogPotential
  simp only [Nat.cast_add, Nat.cast_ofNat]
  change |Real.sqrt x * (32 / Real.log x ^ 3 * (1 - Real.log x / H))| ≤
    32 * Real.sqrt x * (1 / Real.log x ^ 3)
  rw [abs_mul, abs_mul, abs_of_nonneg hsqrt0, abs_of_nonneg hweight0,
    abs_of_nonneg hfactor0]
  calc
    Real.sqrt x * (32 / Real.log x ^ 3 * (1 - Real.log x / H)) ≤
        Real.sqrt x * (32 / Real.log x ^ 3 * 1) := by gcongr
    _ = 32 * Real.sqrt x * (1 / Real.log x ^ 3) := by ring

private theorem rpow_neg_three_halves_mul_sqrt (x : ℝ) (hx : 0 < x) :
    x ^ (-(3 / 2 : ℝ)) * Real.sqrt x = x⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
  convert Real.rpow_neg_one x using 1 <;> ring

private theorem inv_mul_sqrt_eq_rpow_neg_three_halves (x : ℝ) (hx : 0 < x) :
    1 / (x * Real.sqrt x) = x ^ (-(3 / 2 : ℝ)) := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hr := rpow_neg_three_halves_mul_sqrt x hx
  apply (div_eq_iff (mul_ne_zero hx.ne' hs)).2
  calc
    1 = x * x⁻¹ := by field_simp
    _ = x * (x ^ (-(3 / 2 : ℝ)) * Real.sqrt x) := by rw [hr]
    _ = x ^ (-(3 / 2 : ℝ)) * (x * Real.sqrt x) := by ring

/-- Gamma-cell contribution is dominated by the summable cubic reciprocal-log weight. -/
theorem abs_criticalArchCorrection_mul_multiplier_le
    {H : ℝ} (hH : 2 ≤ H) {j : ℕ}
    (hj : j ∈ Finset.range (suzukiCheckpointEventIndex H - 2)) :
    |suzukiCheckpointCriticalArchCorrection j *
        suzukiCheckpointCriticalTriangularMultiplier H j| ≤
      (160 / 3 : ℝ) * HTGeometry.shiftedReciprocalLogWeight 3 j := by
  let x : ℝ := (j : ℝ) + 3
  have hx : 0 < x := by dsimp only [x]; positivity
  have harch := abs_suzukiCheckpointCriticalArchCorrection_le j
  have hmult := abs_suzukiCheckpointCriticalTriangularMultiplier_le hH hj
  have hright0 : 0 ≤ 32 * Real.sqrt ((j + 3 : ℕ) : ℝ) *
      HTGeometry.shiftedReciprocalLogPotential 3 j :=
    mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (HTGeometry.shiftedReciprocalLogPotential_nonneg 3 j)
  have harchMajorant0 :
      0 ≤ (5 / 3 : ℝ) * (((j + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
    positivity
  rw [abs_mul]
  calc
    |suzukiCheckpointCriticalArchCorrection j| *
        |suzukiCheckpointCriticalTriangularMultiplier H j| ≤
      ((5 / 3 : ℝ) * (((j + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) *
        (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) *
          HTGeometry.shiftedReciprocalLogPotential 3 j) :=
      mul_le_mul harch hmult (abs_nonneg _) harchMajorant0
    _ = (160 / 3 : ℝ) *
        ((((j + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) *
          Real.sqrt ((j + 3 : ℕ) : ℝ)) *
            HTGeometry.shiftedReciprocalLogPotential 3 j := by ring
    _ = (160 / 3 : ℝ) * (((j + 3 : ℕ) : ℝ)⁻¹) *
          HTGeometry.shiftedReciprocalLogPotential 3 j := by
      rw [rpow_neg_three_halves_mul_sqrt _ (by positivity)]
    _ = (160 / 3 : ℝ) * HTGeometry.shiftedReciprocalLogWeight 3 j := by
      unfold HTGeometry.shiftedReciprocalLogWeight
        HTGeometry.shiftedReciprocalLogPotential
      simp only [Nat.cast_add, Nat.cast_ofNat]
      rw [one_div, one_div, mul_inv]
      ring

/-- Harmonic finite-part cells are dominated by a shifted inverse-three-halves series. -/
theorem abs_criticalHarmonicCell_mul_multiplier_le
    {H : ℝ} (hH : 2 ≤ H) {j : ℕ}
    (hj : j ∈ Finset.range (suzukiCheckpointEventIndex H - 2)) :
    |suzukiCheckpointCriticalHarmonicCell j *
        suzukiCheckpointCriticalTriangularMultiplier H j| ≤
      64 * (((j + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  let a : ℝ := ((j + 2 : ℕ) : ℝ)
  let x : ℝ := ((j + 3 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hx : 0 < x := by dsimp only [x]; positivity
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hxa : x ≤ 2 * a := by
    dsimp only [x, a]
    exact_mod_cast (by omega : j + 3 ≤ 2 * (j + 2))
  have hlog1 : 1 ≤ Real.log x := by
    dsimp only [x]
    convert HTGeometry.one_le_log_natCast_add_three j using 1 <;> push_cast <;> ring
  have hpotential : HTGeometry.shiftedReciprocalLogPotential 3 j ≤ 1 := by
    unfold HTGeometry.shiftedReciprocalLogPotential
    have harg : (j : ℝ) + 3 = x := by
      dsimp only [x]
      push_cast
      ring
    rw [harg]
    have hp : 1 ≤ Real.log x ^ 3 := one_le_pow₀ hlog1
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp).trans_eq
      (by norm_num)
  have hpotential0 : 0 ≤ HTGeometry.shiftedReciprocalLogPotential 3 j :=
    HTGeometry.shiftedReciprocalLogPotential_nonneg 3 j
  have hmult0 := abs_suzukiCheckpointCriticalTriangularMultiplier_le hH hj
  have hmult : |suzukiCheckpointCriticalTriangularMultiplier H j| ≤
      32 * Real.sqrt x := by
    have h := mul_le_mul_of_nonneg_left hpotential
      (by positivity : 0 ≤ 32 * Real.sqrt x)
    calc
      |suzukiCheckpointCriticalTriangularMultiplier H j| ≤
          32 * Real.sqrt ((j + 3 : ℕ) : ℝ) *
            HTGeometry.shiftedReciprocalLogPotential 3 j := hmult0
      _ ≤ 32 * Real.sqrt x := by simpa [x, mul_assoc] using h
  have hcell := abs_suzukiCheckpointCriticalHarmonicCell_le j
  have hden0 : 0 ≤ 1 / (a * x) := by positivity
  have hraw :
      |suzukiCheckpointCriticalHarmonicCell j| *
          |suzukiCheckpointCriticalTriangularMultiplier H j| ≤
        (1 / (a * x)) * (32 * Real.sqrt x) := by
    apply mul_le_mul hcell hmult (abs_nonneg _)
    simpa only [a, x] using hden0
  have hcore : Real.sqrt x / (a * x) ≤ 2 / (x * Real.sqrt x) := by
    rw [div_le_div_iff₀ (mul_pos ha hx) (mul_pos hx hs)]
    nlinarith
  rw [abs_mul]
  calc
    |suzukiCheckpointCriticalHarmonicCell j| *
        |suzukiCheckpointCriticalTriangularMultiplier H j| ≤
      (1 / (a * x)) * (32 * Real.sqrt x) := hraw
    _ = 32 * (Real.sqrt x / (a * x)) := by ring
    _ ≤ 32 * (2 / (x * Real.sqrt x)) :=
      mul_le_mul_of_nonneg_left hcore (by norm_num)
    _ = 64 * x ^ (-(3 / 2 : ℝ)) := by
      calc
        32 * (2 / (x * Real.sqrt x)) =
            64 * (1 / (x * Real.sqrt x)) := by ring
        _ = 64 * x ^ (-(3 / 2 : ℝ)) := by
          rw [inv_mul_sqrt_eq_rpow_neg_three_halves x hx]
    _ = 64 * (((j + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
      rfl

/-- Summable envelope for every source-free critical finite-part increment. -/
def suzukiCheckpointCriticalSourceFreeIncrementMajorant (j : ℕ) : ℝ :=
  (160 / 3 : ℝ) * HTGeometry.shiftedReciprocalLogWeight 3 j +
    64 * (((j + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))

theorem suzukiCheckpointCriticalSourceFreeIncrementMajorant_nonneg (j : ℕ) :
    0 ≤ suzukiCheckpointCriticalSourceFreeIncrementMajorant j := by
  unfold suzukiCheckpointCriticalSourceFreeIncrementMajorant
  exact add_nonneg
    (mul_nonneg (by norm_num) (HTGeometry.shiftedReciprocalLogWeight_nonneg 3 j))
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))

theorem summable_suzukiCheckpointCriticalSourceFreeIncrementMajorant :
    Summable suzukiCheckpointCriticalSourceFreeIncrementMajorant := by
  have hlog : Summable (fun j : ℕ =>
      (160 / 3 : ℝ) * HTGeometry.shiftedReciprocalLogWeight 3 j) :=
    Summable.mul_left _ HTGeometry.summable_shiftedReciprocalLogWeight_three
  have hbase : Summable (fun j : ℕ =>
      ((j : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift : Summable (fun j : ℕ =>
      (((j + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    (summable_nat_add_iff 3).2 hbase
  have hpow : Summable (fun j : ℕ =>
      64 * (((j + 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    Summable.mul_left _ hshift
  exact hlog.add hpow

/-- Each active source-free increment obeys the common summable envelope. -/
theorem abs_sourceFreeRemainderIncrement_mul_multiplier_le
    {H : ℝ} (hH : 2 ≤ H) {j : ℕ}
    (hj : j ∈ Finset.range (suzukiCheckpointEventIndex H - 2)) :
    |(suzukiCheckpointCriticalSourceFreeRemainder (j + 1) -
        suzukiCheckpointCriticalSourceFreeRemainder j) *
      suzukiCheckpointCriticalTriangularMultiplier H j| ≤
        suzukiCheckpointCriticalSourceFreeIncrementMajorant j := by
  rw [suzukiCheckpointCriticalSourceFreeRemainder_succ_sub]
  have hsplit :
      (suzukiCheckpointCriticalArchCorrection j +
          suzukiCheckpointCriticalHarmonicCell j) *
          suzukiCheckpointCriticalTriangularMultiplier H j =
        suzukiCheckpointCriticalArchCorrection j *
            suzukiCheckpointCriticalTriangularMultiplier H j +
          suzukiCheckpointCriticalHarmonicCell j *
            suzukiCheckpointCriticalTriangularMultiplier H j := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_criticalArchCorrection_mul_multiplier_le hH hj)
    (abs_criticalHarmonicCell_mul_multiplier_le hH hj))

/-- Source-free Gamma and harmonic finite-part errors have one uniform variation budget. -/
theorem exists_uniform_bound_suzukiCheckpointCriticalSourceFreeVariationAction :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 2 ≤ H →
      |suzukiCheckpointCriticalVariationAction
        suzukiCheckpointCriticalSourceFreeRemainder H| ≤ C := by
  let q := suzukiCheckpointCriticalSourceFreeIncrementMajorant
  let B : ℝ :=
    |suzukiCheckpointCriticalSourceFreeRemainder 0| * (32 * Real.sqrt 3)
  let C : ℝ := B + ∑' j : ℕ, q j
  have hq0 : ∀ j : ℕ, 0 ≤ q j :=
    suzukiCheckpointCriticalSourceFreeIncrementMajorant_nonneg
  have hqsum : Summable q :=
    summable_suzukiCheckpointCriticalSourceFreeIncrementMajorant
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have htsum0 : 0 ≤ ∑' j : ℕ, q j := tsum_nonneg hq0
  refine ⟨C, add_nonneg hB0 htsum0, ?_⟩
  intro H hH
  rw [suzukiCheckpointCriticalVariationAction_eq_initial_add_incrementSum]
  have hbase :
      |suzukiCheckpointCriticalSourceFreeRemainder 0 *
          suzukiCheckpointCriticalTriangularMultiplier H 0| ≤ B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (abs_suzukiCheckpointCriticalTriangularMultiplier_zero_le hH)
      (abs_nonneg _)
  have hfinite :
      |∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
          (suzukiCheckpointCriticalSourceFreeRemainder (j + 1) -
            suzukiCheckpointCriticalSourceFreeRemainder j) *
              suzukiCheckpointCriticalTriangularMultiplier H j| ≤
        ∑' j : ℕ, q j := by
    calc
      |∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
          (suzukiCheckpointCriticalSourceFreeRemainder (j + 1) -
            suzukiCheckpointCriticalSourceFreeRemainder j) *
              suzukiCheckpointCriticalTriangularMultiplier H j| ≤
        ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
          |(suzukiCheckpointCriticalSourceFreeRemainder (j + 1) -
            suzukiCheckpointCriticalSourceFreeRemainder j) *
              suzukiCheckpointCriticalTriangularMultiplier H j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2), q j := by
        apply Finset.sum_le_sum
        intro j hj
        exact abs_sourceFreeRemainderIncrement_mul_multiplier_le hH hj
      _ ≤ ∑' j : ℕ, q j := hqsum.sum_le_tsum _ (fun j _hj => hq0 j)
  simpa only [C] using
    (abs_add_le _ _).trans (add_le_add hbase hfinite)

/-- Uniform boundedness of the exact prime--polar Mertens-deviation variation action. -/
def CCMFUSuzukiCriticalMertensDeviationVariationActionBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 2 ≤ H →
    |suzukiCheckpointCriticalVariationAction
      suzukiCheckpointCriticalMertensDeviation H| ≤ C

/-- Uniform boundedness of the sole rate-sensitive critical-remainder variation action. -/
def CCMFUSuzukiCriticalRemainderVariationActionBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 2 ≤ H →
    |suzukiCheckpointCriticalRemainderVariationAction H| ≤ C

/-- Critical finite-part removal is lossless for uniform boundedness. -/
theorem ccmFUSuzukiCriticalRemainderVariationActionBound_iff_triangularCurvatureTransformBound :
    CCMFUSuzukiCriticalRemainderVariationActionBound ↔
      CCMFUSuzukiTriangularCurvatureTransformBound := by
  let B : ℝ := 32 * Real.sqrt 3 * |suzukiCheckpointCriticalOrderedLimit|
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hbase : ∀ H : ℝ, 2 ≤ H →
      |suzukiCheckpointCriticalOrderedLimit *
        suzukiCheckpointCriticalTriangularMultiplier H 0| ≤ B := by
    intro H hH
    rw [abs_mul]
    have hm := abs_suzukiCheckpointCriticalTriangularMultiplier_zero_le hH
    have h := mul_le_mul_of_nonneg_left hm
      (abs_nonneg suzukiCheckpointCriticalOrderedLimit)
    dsimp only [B]
    nlinarith
  constructor
  · rintro ⟨C, hC0, hC⟩
    refine ⟨B + C, add_nonneg hB0 hC0, ?_⟩
    intro H hH
    rw [suzukiCheckpointTriangularCurvatureTransform_eq_criticalFinitePart_add_remainderVariation hH]
    exact (abs_add_le _ _).trans (add_le_add (hbase H hH) (hC H hH))
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C + B, add_nonneg hC0 hB0, ?_⟩
    intro H hH
    have hexact :=
      suzukiCheckpointTriangularCurvatureTransform_eq_criticalFinitePart_add_remainderVariation hH
    have hrearrange :
        suzukiCheckpointCriticalRemainderVariationAction H =
          suzukiCheckpointTriangularCurvatureTransform H -
            suzukiCheckpointCriticalOrderedLimit *
              suzukiCheckpointCriticalTriangularMultiplier H 0 := by
      linarith
    rw [hrearrange]
    exact (abs_sub _ _).trans (add_le_add (hC H hH) (hbase H hH))

/-- Removing the uniformly summable source-free action leaves exactly the prime--polar Mertens
deviation action, without changing the boundedness problem. -/
theorem ccmFUSuzukiCriticalMertensDeviationVariationActionBound_iff_remainderVariationActionBound :
    CCMFUSuzukiCriticalMertensDeviationVariationActionBound ↔
      CCMFUSuzukiCriticalRemainderVariationActionBound := by
  obtain ⟨B, hB0, hB⟩ :=
    exists_uniform_bound_suzukiCheckpointCriticalSourceFreeVariationAction
  constructor
  · rintro ⟨C, hC0, hC⟩
    refine ⟨B + C, add_nonneg hB0 hC0, ?_⟩
    intro H hH
    rw [suzukiCheckpointCriticalRemainderVariationAction_eq_sourceFree_sub_mertensDeviation]
    exact (abs_sub _ _).trans (add_le_add (hB H hH) (hC H hH))
  · rintro ⟨C, hC0, hC⟩
    refine ⟨B + C, add_nonneg hB0 hC0, ?_⟩
    intro H hH
    have hsep :=
      suzukiCheckpointCriticalRemainderVariationAction_eq_sourceFree_sub_mertensDeviation H
    have hrearrange :
        suzukiCheckpointCriticalVariationAction
            suzukiCheckpointCriticalMertensDeviation H =
          suzukiCheckpointCriticalVariationAction
              suzukiCheckpointCriticalSourceFreeRemainder H -
            suzukiCheckpointCriticalRemainderVariationAction H := by
      linarith
    rw [hrearrange]
    exact (abs_sub _ _).trans (add_le_add (hB H hH) (hC H hH))

/-- Closed classification: the rate-sensitive critical-prefix variation action is exactly the
RH-bearing arithmetic invariant after unconditional Mertens--Gamma finite-part removal. -/
theorem ccmFUSuzukiCriticalRemainderVariationActionBound_iff_riemannHypothesis :
    CCMFUSuzukiCriticalRemainderVariationActionBound ↔ RiemannHypothesis := by
  rw [ccmFUSuzukiCriticalRemainderVariationActionBound_iff_triangularCurvatureTransformBound,
    ccmFUSuzukiTriangularCurvatureTransformBound_iff_riemannHypothesis]

/-- Closed arithmetic frontier: RH is equivalent to uniform moving variation control of the
actual prime--polar Mertens deviation; Gamma and harmonic finite-part errors are already paid. -/
theorem ccmFUSuzukiCriticalMertensDeviationVariationActionBound_iff_riemannHypothesis :
    CCMFUSuzukiCriticalMertensDeviationVariationActionBound ↔ RiemannHypothesis := by
  rw [ccmFUSuzukiCriticalMertensDeviationVariationActionBound_iff_remainderVariationActionBound,
    ccmFUSuzukiCriticalRemainderVariationActionBound_iff_riemannHypothesis]

end

end RHTower

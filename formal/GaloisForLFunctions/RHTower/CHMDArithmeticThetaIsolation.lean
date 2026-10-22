import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKernelEnergy
import GaloisForLFunctions.RHTower.XiSliceHusimiHeatDictionary
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Quantitative isolation of signed arithmetic theta coefficients

Normalize the translate at `log (n+2)` by its cusp envelope at that point.
The resulting atoms separate superexponentially on the positive half-line.
The comparison retains the exact squared-index gap, so it applies to arbitrary
absolutely summable signed data without an order assumption on the coefficients.
-/

open Filter Topology
open scoped BigOperators
noncomputable section

namespace RHTower.CHMDArithmeticTheta
open HedenmalmThetaSource

/-- Signed arithmetic data in the natural cusp-weighted coefficient coordinates. -/
abbrev Data := lp (fun _ : ℕ => ℝ) 1

def site (n : ℕ) : ℝ := n + 2

theorem site_pos (n : ℕ) : 0 < site n := by unfold site; positivity

theorem one_lt_site (n : ℕ) : 1 < site n := by
  unfold site
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

theorem log_site_pos (n : ℕ) : 0 < Real.log (site n) :=
  Real.log_pos (one_lt_site n)

/-- The exact normalized cusp envelope of an arithmetic translate. -/
def envelopeAtom (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (9 * x / 2 - Real.pi * site n ^ 2 * (Real.exp (2 * x) - 1))

/-- The normalized actual theta translate, not an envelope surrogate. -/
def atom (n : ℕ) (x : ℝ) : ℝ :=
  riemannKernelReal (x + Real.log (site n)) / thetaEnvelope (Real.log (site n))

theorem envelopeAtom_pos (n : ℕ) (x : ℝ) : 0 < envelopeAtom n x := Real.exp_pos _

theorem atom_pos (n : ℕ) (x : ℝ) : 0 < atom n x :=
  div_pos (riemannKernelReal_pos _) (thetaEnvelope_pos _)

theorem envelope_shift (n : ℕ) (x : ℝ) :
    thetaEnvelope (x + Real.log (site n)) =
      thetaEnvelope (Real.log (site n)) * envelopeAtom n x := by
  have he : Real.exp (2 * Real.log (site n)) = site n ^ 2 := by
    rw [show 2 * Real.log (site n) = Real.log (site n) + Real.log (site n) by ring,
      Real.exp_add, Real.exp_log (site_pos n)]
    ring
  unfold thetaEnvelope envelopeAtom
  rw [show 2 * (x + Real.log (site n)) = 2 * x + 2 * Real.log (site n) by ring,
    Real.exp_add, he]
  simp only [← Real.exp_add]
  congr 1
  ring

theorem atom_envelope_bounds (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    thetaEnvelopeLower * envelopeAtom n x ≤ atom n x ∧
      atom n x ≤ thetaEnvelopeUpper * envelopeAtom n x := by
  have hpos : 0 < x + Real.log (site n) := add_pos_of_nonneg_of_pos hx (log_site_pos n)
  have hl := thetaCuspFullSource_ge_envelope hpos
  have hu := thetaCuspFullSource_le_envelope hpos.le
  rw [thetaCuspFullSource_eq_riemannKernelReal, envelope_shift] at hl hu
  constructor
  · apply (le_div_iff₀ (thetaEnvelope_pos _)).mpr
    nlinarith
  · apply (div_le_iff₀ (thetaEnvelope_pos _)).mpr
    nlinarith

theorem atom_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    atom n x ≤ thetaEnvelopeUpper * Real.exp (9 * x / 2) := by
  refine (atom_envelope_bounds n hx).2.trans ?_
  apply mul_le_mul_of_nonneg_left _ thetaEnvelopeUpper_pos.le
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ Real.exp (2 * x) - 1 := by
    have := Real.one_le_exp_iff.mpr (show 0 ≤ 2 * x by positivity)
    linarith
  exact sub_le_self _ (mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) h)

def separationConstant : ℝ := thetaEnvelopeUpper / thetaEnvelopeLower

theorem separationConstant_pos : 0 < separationConstant :=
  div_pos thetaEnvelopeUpper_pos thetaEnvelopeLower_pos

/-- An exact ratio estimate with the squared arithmetic-index gap. -/
theorem atom_ratio_le (n m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    atom n x / atom m x ≤ separationConstant *
      Real.exp (-Real.pi * (site n ^ 2 - site m ^ 2) * (Real.exp (2 * x) - 1)) := by
  have hu := (atom_envelope_bounds n hx).2
  have hl := (atom_envelope_bounds m hx).1
  calc
    atom n x / atom m x ≤
        (thetaEnvelopeUpper * envelopeAtom n x) /
          (thetaEnvelopeLower * envelopeAtom m x) :=
      div_le_div₀ (mul_pos thetaEnvelopeUpper_pos (envelopeAtom_pos n x)).le hu
        (mul_pos thetaEnvelopeLower_pos (envelopeAtom_pos m x)) hl
    _ = _ := by
      unfold envelopeAtom separationConstant
      rw [mul_div_mul_comm, ← Real.exp_sub]
      congr 2
      ring

/-- Uniform isolation rate for every index strictly beyond `m`. -/
def isolationRate (m : ℕ) (x : ℝ) : ℝ :=
  separationConstant * Real.exp (-Real.pi * (2 * (m : ℝ) + 5) * (Real.exp (2 * x) - 1))

theorem isolationRate_pos (m : ℕ) (x : ℝ) : 0 < isolationRate m x :=
  mul_pos separationConstant_pos (Real.exp_pos _)

theorem atom_ratio_le_isolationRate {n m : ℕ} (hn : m < n) {x : ℝ} (hx : 0 ≤ x) :
    atom n x / atom m x ≤ isolationRate m x := by
  refine (atom_ratio_le n m hx).trans ?_
  apply mul_le_mul_of_nonneg_left _ separationConstant_pos.le
  apply Real.exp_le_exp.mpr
  have hnm : (m : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hgap : 2 * (m : ℝ) + 5 ≤ site n ^ 2 - site m ^ 2 := by
    dsimp [site]
    nlinarith [sq_nonneg ((n : ℝ) - (m : ℝ) - 1)]
  have hd : 0 ≤ Real.exp (2 * x) - 1 := by
    have := Real.one_le_exp_iff.mpr (show 0 ≤ 2 * x by positivity)
    linarith
  have h := mul_le_mul_of_nonneg_right hgap hd
  nlinarith [Real.pi_pos]

theorem summable_abs (a : Data) : Summable fun n => |a n| := by
  simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
    (lp.memℓp a).summable (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)

theorem summable_wave (a : Data) {x : ℝ} (hx : 0 ≤ x) :
    Summable fun n => a n * atom n x := by
  apply Summable.of_norm_bounded ((summable_abs a).mul_right
    (thetaEnvelopeUpper * Real.exp (9 * x / 2)))
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (atom_pos n x)]
  exact mul_le_mul_of_nonneg_left (atom_le n hx) (abs_nonneg _)

/-- The complete signed forward theta source. -/
def wave (a : Data) (x : ℝ) : ℝ := ∑' n, a n * atom n x

/-- The tail beginning at arithmetic index `m+2`. -/
def tail (a : Data) (m : ℕ) (x : ℝ) : ℝ := ∑' j, a (j + m) * atom (j + m) x

theorem summable_tail (a : Data) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable fun j => a (j + m) * atom (j + m) x :=
  (summable_nat_add_iff m).mpr (summable_wave a hx)

theorem head_add_tail (a : Data) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∑ n ∈ Finset.range m, a n * atom n x) + tail a m x = wave a x :=
  (summable_wave a hx).sum_add_tsum_nat_add m

theorem tail_succ (a : Data) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    tail a m x = a m * atom m x + tail a (m + 1) x := by
  simpa only [tail, Nat.zero_add, Nat.add_assoc, Nat.add_comm 1 m] using
    (summable_tail a m hx).tsum_eq_zero_add

/-- The absolute coefficient mass strictly beyond `m`. -/
def tailMass (a : Data) (m : ℕ) : ℝ := ∑' j, |a (j + (m + 1))|

/-- Signed tails cannot cancel the first remaining arithmetic atom: their normalized
error has the exact next-square separation rate. -/
theorem tail_isolation (a : Data) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |tail a m x / atom m x - a m| ≤ isolationRate m x * tailMass a m := by
  have he : tail a m x / atom m x - a m = tail a (m + 1) x / atom m x := by
    rw [tail_succ a m hx]
    field_simp [(atom_pos m x).ne']
    ring
  rw [he, tail, ← tsum_div_const]
  have hs : Summable fun j : ℕ => |a (j + (m + 1))| :=
    (summable_nat_add_iff (f := fun n : ℕ => |a n|) (m + 1)).mpr (summable_abs a)
  have hb := tsum_of_norm_bounded (hs.hasSum.mul_left (isolationRate m x))
    (f := fun j => a (j + (m + 1)) * atom (j + (m + 1)) x / atom m x) (fun j => by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (atom_pos _ x),
        abs_of_pos (atom_pos _ x), mul_div_assoc]
      calc
        |a (j + (m + 1))| * (atom (j + (m + 1)) x / atom m x) ≤
            |a (j + (m + 1))| * isolationRate m x :=
          mul_le_mul_of_nonneg_left (atom_ratio_le_isolationRate (by omega) hx) (abs_nonneg _)
        _ = _ := by ring)
  simpa only [Real.norm_eq_abs, tailMass] using hb

theorem isolationRate_tendsto_zero (m : ℕ) :
    Tendsto (fun N : ℕ => isolationRate m N) atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hE : Tendsto (fun N : ℕ => Real.exp (2 * (N : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) hN)
  have hd : Tendsto (fun N : ℕ => Real.exp (2 * (N : ℝ)) - 1) atTop atTop :=
    by simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hE
  have hn : Tendsto (fun N : ℕ =>
      -Real.pi * (2 * (m : ℝ) + 5) * (Real.exp (2 * (N : ℝ)) - 1)) atTop atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg
      (mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) (by positivity)) hd
  simpa only [isolationRate, Function.comp_def, mul_zero] using
    (Real.tendsto_exp_atBot.comp hn).const_mul separationConstant

/-- Every signed coefficient is recovered from the normalized complete tail at integer times. -/
theorem recover_coefficient (a : Data) (m : ℕ) :
    Tendsto (fun N : ℕ => tail a m N / atom m N) atTop (𝓝 (a m)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb := (isolationRate_tendsto_zero m).mul_const (tailMass a m)
  simp only [zero_mul] at hb
  exact squeeze_zero (fun N => norm_nonneg _) (fun N => by
    simpa only [Real.norm_eq_abs] using tail_isolation a m (x := N) (Nat.cast_nonneg N)) hb

/-- The recovery formula uses only the observed wave and its already recovered finite head. -/
theorem recover_from_wave (a : Data) (m : ℕ) :
    Tendsto (fun N : ℕ =>
      (wave a N - ∑ n ∈ Finset.range m, a n * atom n N) / atom m N) atTop (𝓝 (a m)) := by
  convert recover_coefficient a m using 1
  funext N
  have h := head_add_tail a m (x := N) (Nat.cast_nonneg N)
  congr 1
  linarith

/-- Even discarding any finite initial segment of the observations loses no signed arithmetic data. -/
theorem eq_of_eventually_wave_eq {a b : Data}
    (hab : ∀ᶠ N : ℕ in atTop, wave a N = wave b N) : a = b := by
  apply lp.ext
  funext m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have ht : (fun N : ℕ =>
        (wave a N - ∑ n ∈ Finset.range m, a n * atom n N) / atom m N) =ᶠ[atTop]
        (fun N : ℕ =>
        (wave b N - ∑ n ∈ Finset.range m, b n * atom n N) / atom m N) := by
      filter_upwards [hab] with N hN
      rw [hN]
      congr 2
      apply Finset.sum_congr rfl
      intro n hn
      rw [ih n (Finset.mem_range.mp hn)]
    exact tendsto_nhds_unique (recover_from_wave a m)
      ((recover_from_wave b m).congr' ht.symm)

/-- Integer samples of the forward theta source determine every admissible signed arithmetic weight. -/
theorem integer_samples_injective :
    Function.Injective (fun a : Data => fun N : ℕ => wave a N) := by
  intro a b hab
  exact eq_of_eventually_wave_eq (Eventually.of_forall fun N => congrFun hab N)

end RHTower.CHMDArithmeticTheta

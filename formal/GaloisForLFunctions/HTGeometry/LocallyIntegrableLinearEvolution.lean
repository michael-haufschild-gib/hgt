import GaloisForLFunctions.HTGeometry.BanachIntervalIntegralAbsoluteContinuity
import GaloisForLFunctions.HTGeometry.ClockIteratedIntegralBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Linear Carathéodory evolution for locally integrable coefficients

This module constructs the Peano–Baker evolution in a complete real Banach algebra directly from
a locally integrable coefficient. It proves compact-uniform convergence, the global Volterra
integral equation, continuity, absolute continuity on every interval, and the differential equation
almost everywhere. No ODE existence theorem or solution premise is assumed.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory intervalIntegral Filter

open scoped Interval Topology

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

omit [NormedAlgebra ℝ B] [CompleteSpace B] in
theorem intervalIntegrable_of_locallyIntegrable {f : ℝ → B}
    (hf : LocallyIntegrable f volume) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  exact (hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc

omit [CompleteSpace B] in
theorem continuous_intervalPrimitive_of_locallyIntegrable {f : ℝ → B}
    (hf : LocallyIntegrable f volume) :
    Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, f s) := by
  rw [continuous_iff_continuousAt]
  intro t
  let T : ℝ := |t| + 1
  have hT : 0 < T := add_pos_of_nonneg_of_pos (abs_nonneg t) zero_lt_one
  have hI : IntervalIntegrable f volume (-T) T :=
    intervalIntegrable_of_locallyIntegrable hf _ _
  have hzero : (0 : ℝ) ∈ uIcc (-T) T := by
    rw [uIcc_of_le (by linarith)]
    constructor <;> linarith
  have hcont : ContinuousOn (fun x : ℝ => ∫ s in (0 : ℝ)..x, f s) (uIcc (-T) T) :=
    (GaloisForLFunctions.HTGeometry.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normed
      hI hzero).continuousOn
  have hopen : IsOpen (Ioo (-T) T) := isOpen_Ioo
  have ht : t ∈ Ioo (-T) T := by
    constructor <;> simp [T] <;> linarith [le_abs_self t, neg_le_abs t]
  have hsub : Ioo (-T) T ⊆ uIcc (-T) T := by
    rw [uIcc_of_le (by linarith)]
    exact Ioo_subset_Icc_self
  exact hcont.continuousAt (mem_of_superset (hopen.mem_nhds ht) hsub)

omit [NormedAlgebra ℝ B] [CompleteSpace B] in
theorem locallyIntegrable_mul_continuous {f g : ℝ → B}
    (hf : LocallyIntegrable f volume) (hg : Continuous g) :
    LocallyIntegrable (fun x => f x * g x) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  exact (hf.integrableOn_isCompact hk).mul_continuousOn hg.continuousOn hk

omit [NormedAlgebra ℝ B] [CompleteSpace B] in
theorem locallyIntegrable_norm {f : ℝ → B} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun x => ‖f x‖) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  exact (hf.integrableOn_isCompact hk).norm

def positiveMass (A : ℝ → B) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, ‖A s‖

theorem absolutelyContinuousOnInterval_pow {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ n : ℕ, AbsolutelyContinuousOnInterval (fun x => f x ^ n) a b
  | 0 => by
      simpa using (LipschitzOnWith.absolutelyContinuousOnInterval
        ((LipschitzWith.const (α := ℝ) (1 : ℝ)).lipschitzOnWith)
        (a := a) (b := b))
  | n + 1 => by
      convert (absolutelyContinuousOnInterval_pow hf n).mul hf using 1
      funext x
      simp [pow_succ]

omit [NormedAlgebra ℝ B] [CompleteSpace B] in
theorem integral_norm_mul_positiveMass_pow
    {A : ℝ → B} (hA : LocallyIntegrable A volume) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (∫ s in (0 : ℝ)..t, ‖A s‖ * positiveMass A s ^ n) =
      positiveMass A t ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  have hAI : IntervalIntegrable A volume 0 t :=
    intervalIntegrable_of_locallyIntegrable hA 0 t
  have hnormI := hAI.norm
  have hzero : (0 : ℝ) ∈ uIcc (0 : ℝ) t := by
    rw [uIcc_of_le ht]
    exact ⟨le_rfl, ht⟩
  have hmassAC : AbsolutelyContinuousOnInterval (positiveMass A) 0 t := by
    exact GaloisForLFunctions.HTGeometry.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normed
      hnormI hzero
  let F : ℝ → ℝ := fun x => positiveMass A x ^ (n + 1) / ((n + 1 : ℕ) : ℝ)
  have hfac : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hFAC : AbsolutelyContinuousOnInterval F 0 t := by
    have hp := absolutelyContinuousOnInterval_pow hmassAC (n + 1)
    simpa [F, div_eq_mul_inv, mul_comm] using hp.const_mul ((((n + 1 : ℕ) : ℝ))⁻¹)
  have hderivMass := hnormI.ae_hasDerivAt_integral
  have hae : ∀ᵐ x : ℝ, x ∈ uIoc (0 : ℝ) t →
      deriv F x = ‖A x‖ * positiveMass A x ^ n := by
    filter_upwards [hderivMass] with x hx hxt
    have hxu : x ∈ uIcc (0 : ℝ) t := uIoc_subset_uIcc hxt
    have hq : HasDerivAt (positiveMass A) ‖A x‖ x := hx hxu 0 hzero
    have hF : HasDerivAt F (‖A x‖ * positiveMass A x ^ n) x := by
      have hp := (hasDerivAt_pow (n + 1) (positiveMass A x)).comp x hq
      have hd := hp.div_const (((n + 1 : ℕ) : ℝ))
      change HasDerivAt F
        (((n + 1 : ℕ) : ℝ) * positiveMass A x ^ (n + 1 - 1) * ‖A x‖ /
          ((n + 1 : ℕ) : ℝ)) x at hd
      have heq : (((n + 1 : ℕ) : ℝ) * positiveMass A x ^ (n + 1 - 1) * ‖A x‖ /
          ((n + 1 : ℕ) : ℝ)) = ‖A x‖ * positiveMass A x ^ n := by
        simp only [Nat.add_sub_cancel]
        field_simp [hfac]
      rwa [heq] at hd
    exact hF.deriv
  calc
    (∫ s in (0 : ℝ)..t, ‖A s‖ * positiveMass A s ^ n) =
        ∫ s in (0 : ℝ)..t, deriv F s := by
          symm
          exact intervalIntegral.integral_congr_ae hae
    _ = F t - F 0 := hFAC.integral_deriv_eq_sub
    _ = positiveMass A t ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
      simp [F, positiveMass]

def l1Picard (A : ℝ → B) : ℕ → ℝ → B
  | 0, _ => 1
  | n + 1, t => ∫ s in (0 : ℝ)..t, A s * l1Picard A n s

omit [CompleteSpace B] in
@[simp]
theorem l1Picard_zero (A : ℝ → B) (t : ℝ) : l1Picard A 0 t = 1 := rfl

omit [CompleteSpace B] in
theorem l1Picard_succ (A : ℝ → B) (n : ℕ) (t : ℝ) :
    l1Picard A (n + 1) t = ∫ s in (0 : ℝ)..t, A s * l1Picard A n s := rfl

omit [CompleteSpace B] in
theorem continuous_l1Picard {A : ℝ → B} (hA : LocallyIntegrable A volume) :
    ∀ n : ℕ, Continuous (l1Picard A n)
  | 0 => continuous_const
  | n + 1 => by
      change Continuous (fun t => ∫ s in (0 : ℝ)..t, A s * l1Picard A n s)
      exact continuous_intervalPrimitive_of_locallyIntegrable
        (locallyIntegrable_mul_continuous hA (continuous_l1Picard hA n))

omit [NormedAlgebra ℝ B] [CompleteSpace B] in
theorem positiveMass_nonneg {A : ℝ → B} {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ positiveMass A t := by
  rw [positiveMass]
  exact intervalIntegral.integral_nonneg ht fun _ _ => norm_nonneg _

omit [NormedAlgebra ℝ B] [CompleteSpace B] in
theorem positiveMass_mono {A : ℝ → B} (hA : LocallyIntegrable A volume)
    {s t : ℝ} (hst : s ≤ t) :
    positiveMass A s ≤ positiveMass A t := by
  have hnorm := locallyIntegrable_norm hA
  have h0s := intervalIntegrable_of_locallyIntegrable hnorm 0 s
  have hstI := intervalIntegrable_of_locallyIntegrable hnorm s t
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0s hstI
  have hnonneg : 0 ≤ ∫ x in s..t, ‖A x‖ :=
    intervalIntegral.integral_nonneg hst fun _ _ => norm_nonneg _
  rw [positiveMass, positiveMass]
  linarith

omit [CompleteSpace B] in
theorem norm_l1Picard_le {A : ℝ → B} (hA : LocallyIntegrable A volume) :
    ∀ (n : ℕ) {t : ℝ}, 0 ≤ t →
      ‖l1Picard A n t‖ ≤ ‖(1 : B)‖ * positiveMass A t ^ n / (n.factorial : ℝ)
  | 0, t, _ => by
      simp only [l1Picard, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
      exact le_rfl
  | n + 1, t, ht => by
      have hAI : IntervalIntegrable A volume 0 t :=
        intervalIntegrable_of_locallyIntegrable hA 0 t
      have hprodI : IntervalIntegrable (fun s => A s * l1Picard A n s) volume 0 t :=
        hAI.mul_continuousOn (continuous_l1Picard hA n).continuousOn
      have hmassC : Continuous (positiveMass A) :=
        continuous_intervalPrimitive_of_locallyIntegrable (locallyIntegrable_norm hA)
      have hmajorI : IntervalIntegrable
          (fun s => ‖A s‖ * (‖(1 : B)‖ * positiveMass A s ^ n /
            (n.factorial : ℝ))) volume 0 t :=
        hAI.norm.mul_continuousOn
          ((continuous_const.mul (hmassC.pow n)).div_const (n.factorial : ℝ)).continuousOn
      have hbound : ∀ s ∈ Ι (0 : ℝ) t,
          ‖A s * l1Picard A n s‖ ≤
            ‖A s‖ * (‖(1 : B)‖ * positiveMass A s ^ n / (n.factorial : ℝ)) := by
        intro s hs
        have hs0 : 0 ≤ s := le_of_lt (uIoc_of_le ht ▸ hs).1
        exact le_trans (norm_mul_le _ _)
          (mul_le_mul_of_nonneg_left (norm_l1Picard_le hA n hs0) (norm_nonneg _))
      have hle := GaloisForLFunctions.HTGeometry.norm_integral_le_abs_of_norm_le
        hprodI.norm hmajorI hbound
      rw [l1Picard_succ]
      refine le_trans hle ?_
      have hval : (∫ s in (0 : ℝ)..t,
          ‖A s‖ * (‖(1 : B)‖ * positiveMass A s ^ n / (n.factorial : ℝ))) =
          ‖(1 : B)‖ * positiveMass A t ^ (n + 1) / ((n + 1).factorial : ℝ) := by
        rw [show (fun s => ‖A s‖ * (‖(1 : B)‖ * positiveMass A s ^ n /
            (n.factorial : ℝ))) =
            fun s => (‖(1 : B)‖ * (n.factorial : ℝ)⁻¹) *
              (‖A s‖ * positiveMass A s ^ n) by
          funext s
          field_simp]
        rw [intervalIntegral.integral_const_mul,
          integral_norm_mul_positiveMass_pow hA ht n, Nat.factorial_succ]
        push_cast
        field_simp
      rw [hval, abs_of_nonneg]
      exact div_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (positiveMass_nonneg ht) _))
        (by positivity)

theorem summable_l1Picard {A : ℝ → B} (hA : LocallyIntegrable A volume)
    {t : ℝ} (ht : 0 ≤ t) : Summable fun n => l1Picard A n t := by
  have hmajor : Summable fun n : ℕ =>
      ‖(1 : B)‖ * (positiveMass A t ^ n / (n.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial (positiveMass A t)).mul_left ‖(1 : B)‖
  exact Summable.of_norm_bounded hmajor fun n => by
    calc
      ‖l1Picard A n t‖ ≤
          ‖(1 : B)‖ * positiveMass A t ^ n / (n.factorial : ℝ) :=
        norm_l1Picard_le hA n ht
      _ = ‖(1 : B)‖ * (positiveMass A t ^ n / (n.factorial : ℝ)) := by ring

def positiveEvolution (A : ℝ → B) (t : ℝ) : B :=
  ∑' n : ℕ, l1Picard A n t

theorem continuousOn_positiveEvolution {A : ℝ → B} (hA : LocallyIntegrable A volume)
    {T : ℝ} : ContinuousOn (positiveEvolution A) (Icc 0 T) := by
  have hM : Summable fun n : ℕ =>
      ‖(1 : B)‖ * (positiveMass A T ^ n / (n.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial (positiveMass A T)).mul_left ‖(1 : B)‖
  refine continuousOn_tsum (fun n => (continuous_l1Picard hA n).continuousOn) hM ?_
  intro n s hs
  have hs0 : 0 ≤ s := hs.1
  have hmass : positiveMass A s ≤ positiveMass A T :=
    positiveMass_mono hA hs.2
  have hpow : positiveMass A s ^ n ≤ positiveMass A T ^ n :=
    pow_le_pow_left₀ (positiveMass_nonneg hs0) hmass n
  refine le_trans (norm_l1Picard_le hA n hs0) ?_
  have hcoef : 0 ≤ ‖(1 : B)‖ / (n.factorial : ℝ) := div_nonneg (norm_nonneg _) (by positivity)
  calc
    ‖(1 : B)‖ * positiveMass A s ^ n / (n.factorial : ℝ) =
        (‖(1 : B)‖ / (n.factorial : ℝ)) * positiveMass A s ^ n := by ring
    _ ≤ (‖(1 : B)‖ / (n.factorial : ℝ)) * positiveMass A T ^ n :=
      mul_le_mul_of_nonneg_left hpow hcoef
    _ = ‖(1 : B)‖ * (positiveMass A T ^ n / (n.factorial : ℝ)) := by ring

theorem tsum_intervalIntegral_of_summable_norm_integral
    {a b : ℝ} {f : ℕ → ℝ → B}
    (hf : ∀ n, IntervalIntegrable (f n) volume a b)
    (hnorm : Summable fun n => ∫ x in Ι a b, ‖f n x‖) :
    (∑' n, ∫ x in a..b, f n x) = ∫ x in a..b, ∑' n, f n x := by
  have hint : ∀ n, Integrable (f n) (volume.restrict (Ι a b)) :=
    fun n => intervalIntegrable_iff.mp (hf n)
  have hcore := integral_tsum_of_summable_integral_norm hint hnorm
  have hsummable : Summable fun n => ∫ x in Ι a b, f n x := by
    refine Summable.of_norm_bounded hnorm fun n => ?_
    exact norm_integral_le_integral_norm _
  have hsides : ∀ n : ℕ, (∫ x in a..b, f n x) =
      (if a ≤ b then (1 : ℝ) else -1) • ∫ x in Ι a b, f n x := fun n =>
    intervalIntegral.intervalIntegral_eq_integral_uIoc _ _ _ _
  calc
    (∑' n, ∫ x in a..b, f n x) =
        ∑' n, (if a ≤ b then (1 : ℝ) else -1) • ∫ x in Ι a b, f n x :=
      tsum_congr hsides
    _ = (if a ≤ b then (1 : ℝ) else -1) • ∑' n, ∫ x in Ι a b, f n x :=
      hsummable.tsum_const_smul _
    _ = (if a ≤ b then (1 : ℝ) else -1) • ∫ x in Ι a b, ∑' n, f n x := by
      rw [hcore]
    _ = ∫ x in a..b, ∑' n, f n x :=
      (intervalIntegral.intervalIntegral_eq_integral_uIoc _ _ _ _).symm

omit [CompleteSpace B] in
theorem summable_integral_norm_l1Picard_product
    {A : ℝ → B} (hA : LocallyIntegrable A volume) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun n => ∫ s in Ι (0 : ℝ) t, ‖A s * l1Picard A n s‖ := by
  let M : ℕ → ℝ := fun n => ‖(1 : B)‖ *
    (positiveMass A t ^ n / (n.factorial : ℝ))
  have hMs : Summable M :=
    (Real.summable_pow_div_factorial (positiveMass A t)).mul_left ‖(1 : B)‖
  have hAI : IntervalIntegrable A volume 0 t :=
    intervalIntegrable_of_locallyIntegrable hA 0 t
  have hnormAI : Integrable (fun s => ‖A s‖) (volume.restrict (Ι (0 : ℝ) t)) :=
    intervalIntegrable_iff.mp hAI.norm
  let C : ℝ := ∫ s in Ι (0 : ℝ) t, ‖A s‖
  have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hmajor : Summable fun n => M n * C := hMs.mul_right C
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
    hmajor
  have hMn : 0 ≤ M n := by
    exact mul_nonneg (norm_nonneg _)
      (div_nonneg (pow_nonneg (positiveMass_nonneg ht) _) (by positivity))
  have hprodI : Integrable (fun s => A s * l1Picard A n s)
      (volume.restrict (Ι (0 : ℝ) t)) :=
    intervalIntegrable_iff.mp
      (hAI.mul_continuousOn (continuous_l1Picard hA n).continuousOn)
  have hmajorI : Integrable (fun s => M n * ‖A s‖)
      (volume.restrict (Ι (0 : ℝ) t)) := hnormAI.const_mul _
  have hle : (∫ s in Ι (0 : ℝ) t, ‖A s * l1Picard A n s‖) ≤
      ∫ s in Ι (0 : ℝ) t, M n * ‖A s‖ := by
    refine setIntegral_mono_on hprodI.norm hmajorI measurableSet_uIoc (fun s hs => ?_)
    have hs0 : 0 ≤ s := le_of_lt (uIoc_of_le ht ▸ hs).1
    have hmass : positiveMass A s ≤ positiveMass A t :=
      positiveMass_mono hA (uIoc_of_le ht ▸ hs).2
    have hpow : positiveMass A s ^ n ≤ positiveMass A t ^ n :=
      pow_le_pow_left₀ (positiveMass_nonneg hs0) hmass n
    have hp : ‖l1Picard A n s‖ ≤ M n := by
      refine le_trans (norm_l1Picard_le hA n hs0) ?_
      dsimp [M]
      have hc : 0 ≤ ‖(1 : B)‖ / (n.factorial : ℝ) := by positivity
      calc
        ‖(1 : B)‖ * positiveMass A s ^ n / (n.factorial : ℝ) =
            (‖(1 : B)‖ / (n.factorial : ℝ)) * positiveMass A s ^ n := by ring
        _ ≤ (‖(1 : B)‖ / (n.factorial : ℝ)) * positiveMass A t ^ n :=
          mul_le_mul_of_nonneg_left hpow hc
        _ = ‖(1 : B)‖ * (positiveMass A t ^ n / (n.factorial : ℝ)) := by ring
    exact le_trans (norm_mul_le _ _)
      (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hp (norm_nonneg (A s)))
  refine le_trans hle ?_
  rw [MeasureTheory.integral_const_mul]

theorem positiveEvolution_integral_equation
    {A : ℝ → B} (hA : LocallyIntegrable A volume) {t : ℝ} (ht : 0 ≤ t) :
    positiveEvolution A t = 1 + ∫ s in (0 : ℝ)..t, A s * positiveEvolution A s := by
  have hsum := summable_l1Picard hA ht
  rw [positiveEvolution, hsum.tsum_eq_zero_add]
  change (1 : B) + ∑' n : ℕ, (∫ s in (0 : ℝ)..t, A s * l1Picard A n s) = _
  rw [tsum_intervalIntegral_of_summable_norm_integral
    (fun n => (intervalIntegrable_of_locallyIntegrable hA 0 t).mul_continuousOn
      (continuous_l1Picard hA n).continuousOn)
    (summable_integral_norm_l1Picard_product hA ht)]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  have hs0 : 0 ≤ s := hs.1
  exact (summable_l1Picard hA hs0).tsum_mul_left (A s)

omit [NormedAlgebra ℝ B] [CompleteSpace B] in
theorem locallyIntegrable_comp_neg {f : ℝ → B} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun x => f (-x)) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  have hneg := MeasureTheory.IntegrableOn.comp_neg (hf.integrableOn_isCompact hk.neg)
  simpa using hneg

def reflectedCoefficient (A : ℝ → B) (t : ℝ) : B := -A (-t)

omit [NormedAlgebra ℝ B] [CompleteSpace B] in
theorem locallyIntegrable_reflectedCoefficient {A : ℝ → B}
    (hA : LocallyIntegrable A volume) :
    LocallyIntegrable (reflectedCoefficient A) volume := by
  exact (locallyIntegrable_comp_neg hA).neg

theorem positiveEvolution_zero {A : ℝ → B} (hA : LocallyIntegrable A volume) :
    positiveEvolution A 0 = 1 := by
  simpa using positiveEvolution_integral_equation hA (t := 0) le_rfl

def caratheodoryEvolution (A : ℝ → B) (t : ℝ) : B :=
  if 0 ≤ t then positiveEvolution A t
  else positiveEvolution (reflectedCoefficient A) (-t)

omit [CompleteSpace B] in
theorem caratheodoryEvolution_of_nonneg {A : ℝ → B} {t : ℝ} (ht : 0 ≤ t) :
    caratheodoryEvolution A t = positiveEvolution A t := by
  simp [caratheodoryEvolution, ht]

omit [CompleteSpace B] in
theorem caratheodoryEvolution_of_neg {A : ℝ → B} {t : ℝ} (ht : t < 0) :
    caratheodoryEvolution A t = positiveEvolution (reflectedCoefficient A) (-t) := by
  simp [caratheodoryEvolution, not_le.mpr ht]

theorem caratheodoryEvolution_zero {A : ℝ → B} (hA : LocallyIntegrable A volume) :
    caratheodoryEvolution A 0 = 1 := by
  rw [caratheodoryEvolution_of_nonneg le_rfl, positiveEvolution_zero hA]

theorem caratheodoryEvolution_neg_eq_reflected
    {A : ℝ → B} (hA : LocallyIntegrable A volume) {s : ℝ} (hs : 0 ≤ s) :
    caratheodoryEvolution A (-s) = positiveEvolution (reflectedCoefficient A) s := by
  rcases hs.eq_or_lt with rfl | hspos
  · rw [neg_zero, caratheodoryEvolution_zero hA,
      positiveEvolution_zero (locallyIntegrable_reflectedCoefficient hA)]
  · rw [caratheodoryEvolution_of_neg (neg_lt_zero.mpr hspos)]
    simp

theorem caratheodoryEvolution_integral_equation_of_neg
    {A : ℝ → B} (hA : LocallyIntegrable A volume) {t : ℝ} (ht : t < 0) :
    caratheodoryEvolution A t =
      1 + ∫ s in (0 : ℝ)..t, A s * caratheodoryEvolution A s := by
  let R := reflectedCoefficient A
  have hR : LocallyIntegrable R volume := locallyIntegrable_reflectedCoefficient hA
  rw [caratheodoryEvolution_of_neg ht,
    positiveEvolution_integral_equation hR (neg_nonneg.mpr ht.le)]
  congr 1
  let f : ℝ → B := fun x => A x * caratheodoryEvolution A x
  calc
    (∫ s in (0 : ℝ)..-t, R s * positiveEvolution R s) =
        ∫ s in (0 : ℝ)..-t, -(f (-s)) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le (neg_nonneg.mpr ht.le)] at hs
      have hs0 : 0 ≤ s := hs.1
      dsimp only [R, reflectedCoefficient, f]
      rw [caratheodoryEvolution_neg_eq_reflected hA hs0]
      simp
    _ = -(∫ s in (0 : ℝ)..-t, f (-s)) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ x in t..(0 : ℝ), f x) := by
      rw [intervalIntegral.integral_comp_neg]
      simp
    _ = ∫ x in (0 : ℝ)..t, f x := by
      rw [intervalIntegral.integral_symm]
      simp
    _ = ∫ s in (0 : ℝ)..t, A s * caratheodoryEvolution A s := rfl

theorem caratheodoryEvolution_integral_equation
    {A : ℝ → B} (hA : LocallyIntegrable A volume) (t : ℝ) :
    caratheodoryEvolution A t =
      1 + ∫ s in (0 : ℝ)..t, A s * caratheodoryEvolution A s := by
  rcases le_or_gt 0 t with ht | ht
  · rw [caratheodoryEvolution_of_nonneg ht,
      positiveEvolution_integral_equation hA ht]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    rw [caratheodoryEvolution_of_nonneg hs.1]
  · exact caratheodoryEvolution_integral_equation_of_neg hA ht

theorem continuousOn_caratheodoryEvolution_window
    {A : ℝ → B} (hA : LocallyIntegrable A volume) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (caratheodoryEvolution A) (Icc (-T) T) := by
  let R := reflectedCoefficient A
  have hR : LocallyIntegrable R volume := locallyIntegrable_reflectedCoefficient hA
  have hpos : ContinuousOn (caratheodoryEvolution A) (Icc 0 T) :=
    (continuousOn_positiveEvolution hA).congr fun x hx =>
      caratheodoryEvolution_of_nonneg hx.1
  have href : ContinuousOn (fun x : ℝ => positiveEvolution R (-x)) (Icc (-T) 0) := by
    exact (continuousOn_positiveEvolution hR).comp continuous_neg.continuousOn fun x hx => by
      constructor <;> linarith [hx.1, hx.2]
  have hneg : ContinuousOn (caratheodoryEvolution A) (Icc (-T) 0) :=
    href.congr fun x hx => by
      have h := caratheodoryEvolution_neg_eq_reflected hA (s := -x)
        (neg_nonneg.mpr hx.2)
      simpa [R] using h
  have hunion := hneg.union_of_isClosed hpos isClosed_Icc isClosed_Icc
  convert hunion using 1
  ext x
  simp only [mem_union, mem_Icc]
  constructor
  · intro hx
    rcases le_total x 0 with hx0 | h0x
    · exact Or.inl ⟨hx.1, hx0⟩
    · exact Or.inr ⟨h0x, hx.2⟩
  · intro hx
    rcases hx with hx | hx
    · exact ⟨hx.1, le_trans hx.2 hT⟩
    · exact ⟨le_trans (by linarith : -T ≤ 0) hx.1, hx.2⟩

theorem continuous_caratheodoryEvolution
    {A : ℝ → B} (hA : LocallyIntegrable A volume) :
    Continuous (caratheodoryEvolution A) := by
  rw [continuous_iff_continuousAt]
  intro t
  let T : ℝ := |t| + 1
  have hT : 0 < T := add_pos_of_nonneg_of_pos (abs_nonneg t) zero_lt_one
  have hcont := continuousOn_caratheodoryEvolution_window hA hT.le
  have hopen : IsOpen (Ioo (-T) T) := isOpen_Ioo
  have ht : t ∈ Ioo (-T) T := by
    constructor <;> simp [T] <;> linarith [le_abs_self t, neg_le_abs t]
  exact hcont.continuousAt
    (mem_of_superset (hopen.mem_nhds ht) (by
      exact Ioo_subset_Icc_self))

theorem locallyIntegrable_caratheodoryProduct
    {A : ℝ → B} (hA : LocallyIntegrable A volume) :
    LocallyIntegrable (fun t => A t * caratheodoryEvolution A t) volume :=
  locallyIntegrable_mul_continuous hA (continuous_caratheodoryEvolution hA)

theorem caratheodoryEvolution_eq_add_intervalIntegral
    {A : ℝ → B} (hA : LocallyIntegrable A volume) (a t : ℝ) :
    caratheodoryEvolution A t = caratheodoryEvolution A a +
      ∫ s in a..t, A s * caratheodoryEvolution A s := by
  have hprod := locallyIntegrable_caratheodoryProduct hA
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_of_locallyIntegrable hprod 0 a)
    (intervalIntegrable_of_locallyIntegrable hprod a t)
  rw [caratheodoryEvolution_integral_equation hA t,
    caratheodoryEvolution_integral_equation hA a, ← hadd]
  abel

theorem absolutelyContinuousOnInterval_caratheodoryEvolution
    {A : ℝ → B} (hA : LocallyIntegrable A volume) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (caratheodoryEvolution A) a b := by
  have hprod := locallyIntegrable_caratheodoryProduct hA
  have hprim : AbsolutelyContinuousOnInterval
      (fun x => ∫ s in a..x, A s * caratheodoryEvolution A s) a b :=
    GaloisForLFunctions.HTGeometry.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normed
      (intervalIntegrable_of_locallyIntegrable hprod a b) (by simp)
  have hsum : AbsolutelyContinuousOnInterval
      (fun x => caratheodoryEvolution A a +
        ∫ s in a..x, A s * caratheodoryEvolution A s) a b := by
    exact GaloisForLFunctions.HTGeometry.LipschitzWith.comp_absolutelyContinuousOnInterval
      (show Isometry (fun y : B => caratheodoryEvolution A a + y) from
        fun x y => edist_add_left _ _ _).lipschitz hprim
  have hfun : (fun x => caratheodoryEvolution A a +
      ∫ s in a..x, A s * caratheodoryEvolution A s) =
      caratheodoryEvolution A := by
    funext x
    exact (caratheodoryEvolution_eq_add_intervalIntegral hA a x).symm
  rw [← hfun]
  exact hsum

theorem ae_hasDerivAt_caratheodoryEvolution
    {A : ℝ → B} (hA : LocallyIntegrable A volume) :
    ∀ᵐ t : ℝ, HasDerivAt (caratheodoryEvolution A)
      (A t * caratheodoryEvolution A t) t := by
  have hderiv := LocallyIntegrable.ae_hasDerivAt_integral
    (locallyIntegrable_caratheodoryProduct hA)
  filter_upwards [hderiv] with t ht
  have hp := ht 0
  have hsum := hp.const_add (1 : B)
  have hsum' : HasDerivAt
      (fun x => 1 + ∫ s in (0 : ℝ)..x, A s * caratheodoryEvolution A s)
      (A t * caratheodoryEvolution A t) t := by
    exact hsum
  have hfun : (fun x => 1 + ∫ s in (0 : ℝ)..x, A s * caratheodoryEvolution A s) =
      caratheodoryEvolution A := by
    funext x
    exact (caratheodoryEvolution_integral_equation hA x).symm
  rwa [hfun] at hsum'

omit [CompleteSpace B] in
/-- A continuous solution of the homogeneous Volterra equation vanishes on a positive compact
interval. The proof iterates the equation and uses the exact factorial simplex bound. -/
theorem eq_zero_of_continuous_volterra_on_Icc
    {A D : ℝ → B} (hA : LocallyIntegrable A volume) (hD : Continuous D)
    {T : ℝ} (hT : 0 ≤ T)
    (hvolterra : ∀ t ∈ Icc (0 : ℝ) T,
      D t = ∫ s in (0 : ℝ)..t, A s * D s) :
    ∀ t ∈ Icc (0 : ℝ) T, D t = 0 := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) T).Nonempty from ⟨0, left_mem_Icc.mpr hT⟩)
    hD.norm.continuousOn
  let C : ℝ := ‖D x‖
  have hC : 0 ≤ C := norm_nonneg _
  have hmassC : Continuous (positiveMass A) :=
    continuous_intervalPrimitive_of_locallyIntegrable (locallyIntegrable_norm hA)
  have hbound : ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      ‖D t‖ ≤ C * (positiveMass A t ^ n / (n.factorial : ℝ)) := by
    intro n
    induction n with
    | zero =>
        intro t ht
        simpa [C] using hmax ht
    | succ n ih =>
        intro t ht
        have hAI : IntervalIntegrable A volume 0 t :=
          intervalIntegrable_of_locallyIntegrable hA 0 t
        have hprodI : IntervalIntegrable (fun s => A s * D s) volume 0 t :=
          hAI.mul_continuousOn hD.continuousOn
        have hmajorI : IntervalIntegrable
            (fun s => ‖A s‖ * (C *
              (positiveMass A s ^ n / (n.factorial : ℝ)))) volume 0 t :=
          hAI.norm.mul_continuousOn
            (continuous_const.mul
              ((hmassC.pow n).div_const (n.factorial : ℝ))).continuousOn
        have hpoint : ∀ s ∈ Ι (0 : ℝ) t,
            ‖A s * D s‖ ≤ ‖A s‖ *
              (C * (positiveMass A s ^ n / (n.factorial : ℝ))) := by
          intro s hs
          have hs' := uIoc_of_le ht.1 ▸ hs
          have hsI : s ∈ Icc (0 : ℝ) T :=
            ⟨le_of_lt hs'.1, le_trans hs'.2 ht.2⟩
          exact le_trans (norm_mul_le _ _)
            (mul_le_mul_of_nonneg_left (ih s hsI) (norm_nonneg _))
        have hle := GaloisForLFunctions.HTGeometry.norm_integral_le_abs_of_norm_le
          hprodI.norm hmajorI hpoint
        rw [hvolterra t ht]
        refine le_trans hle ?_
        have hval : (∫ s in (0 : ℝ)..t,
            ‖A s‖ * (C * (positiveMass A s ^ n / (n.factorial : ℝ)))) =
            C * (positiveMass A t ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
          rw [show (fun s => ‖A s‖ *
              (C * (positiveMass A s ^ n / (n.factorial : ℝ)))) =
              fun s => (C * (n.factorial : ℝ)⁻¹) *
                (‖A s‖ * positiveMass A s ^ n) by
            funext s
            field_simp]
          rw [intervalIntegral.integral_const_mul,
            integral_norm_mul_positiveMass_pow hA ht.1 n, Nat.factorial_succ]
          push_cast
          field_simp
        rw [hval, abs_of_nonneg]
        exact mul_nonneg hC
          (div_nonneg (pow_nonneg (positiveMass_nonneg ht.1) _) (by positivity))
  intro t ht
  have hsum : Summable fun n : ℕ =>
      C * (positiveMass A t ^ n / (n.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial (positiveMass A t)).mul_left C
  have hzero : Tendsto (fun _ : ℕ => ‖D t‖) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall fun n => hbound n t ht)
      hsum.tendsto_atTop_zero
  have hconst : Tendsto (fun _ : ℕ => ‖D t‖) atTop (𝓝 ‖D t‖) := tendsto_const_nhds
  exact norm_eq_zero.mp (tendsto_nhds_unique hconst hzero)

omit [CompleteSpace B] in
/-- Backward-time form of homogeneous Volterra uniqueness, obtained by exact reflection. -/
theorem eq_zero_of_continuous_volterra_on_Icc_neg
    {A D : ℝ → B} (hA : LocallyIntegrable A volume) (hD : Continuous D)
    {T : ℝ} (hT : T ≤ 0)
    (hvolterra : ∀ t ∈ Icc T (0 : ℝ),
      D t = ∫ s in (0 : ℝ)..t, A s * D s) :
    ∀ t ∈ Icc T (0 : ℝ), D t = 0 := by
  let R : ℝ → B := reflectedCoefficient A
  let Dr : ℝ → B := fun s => D (-s)
  have hR : LocallyIntegrable R volume := locallyIntegrable_reflectedCoefficient hA
  have hDr : Continuous Dr := hD.comp continuous_neg
  have hDrVolterra : ∀ s ∈ Icc (0 : ℝ) (-T),
      Dr s = ∫ u in (0 : ℝ)..s, R u * Dr u := by
    intro s hs
    have hnegs : -s ∈ Icc T (0 : ℝ) := by
      constructor <;> linarith [hs.1, hs.2]
    rw [show Dr s = D (-s) by rfl, hvolterra (-s) hnegs]
    let f : ℝ → B := fun x => A x * D x
    calc
      (∫ x in (0 : ℝ)..-s, A x * D x) = ∫ x in (0 : ℝ)..-s, f x := rfl
      _ = -(∫ x in (-s)..(0 : ℝ), f x) := by
        rw [intervalIntegral.integral_symm]
      _ = -(∫ u in (0 : ℝ)..s, f (-u)) := by
        rw [intervalIntegral.integral_comp_neg]
        simp
      _ = ∫ u in (0 : ℝ)..s, -(f (-u)) := by
        rw [intervalIntegral.integral_neg]
      _ = ∫ u in (0 : ℝ)..s, R u * Dr u := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        simp [R, Dr, reflectedCoefficient, f]
  have hz := eq_zero_of_continuous_volterra_on_Icc hR hDr (neg_nonneg.mpr hT)
    hDrVolterra
  intro t ht
  have hnegt : -t ∈ Icc (0 : ℝ) (-T) := by
    constructor <;> linarith [ht.1, ht.2]
  simpa [Dr] using hz (-t) hnegt

/-- Uniqueness of the global Carathéodory evolution among continuous solutions of its Volterra
equation. -/
theorem caratheodoryEvolution_unique
    {A F : ℝ → B} (hA : LocallyIntegrable A volume) (hF : Continuous F)
    (hvolterra : ∀ t : ℝ,
      F t = 1 + ∫ s in (0 : ℝ)..t, A s * F s) :
    F = caratheodoryEvolution A := by
  let D : ℝ → B := fun t => F t - caratheodoryEvolution A t
  have hD : Continuous D := hF.sub (continuous_caratheodoryEvolution hA)
  have hDvolterra : ∀ t : ℝ,
      D t = ∫ s in (0 : ℝ)..t, A s * D s := by
    intro t
    have hAF : IntervalIntegrable (fun s => A s * F s) volume 0 t :=
      (intervalIntegrable_of_locallyIntegrable hA 0 t).mul_continuousOn hF.continuousOn
    have hAG : IntervalIntegrable
        (fun s => A s * caratheodoryEvolution A s) volume 0 t :=
      intervalIntegrable_of_locallyIntegrable
        (locallyIntegrable_caratheodoryProduct hA) 0 t
    dsimp only [D]
    rw [hvolterra t, caratheodoryEvolution_integral_equation hA t]
    calc
      (1 + ∫ s in (0 : ℝ)..t, A s * F s) -
          (1 + ∫ s in (0 : ℝ)..t, A s * caratheodoryEvolution A s) =
          (∫ s in (0 : ℝ)..t, A s * F s) -
            ∫ s in (0 : ℝ)..t, A s * caratheodoryEvolution A s := by abel
      _ = ∫ s in (0 : ℝ)..t,
          (A s * F s - A s * caratheodoryEvolution A s) := by
        rw [intervalIntegral.integral_sub hAF hAG]
      _ = ∫ s in (0 : ℝ)..t, A s * (F s - caratheodoryEvolution A s) := by
        refine intervalIntegral.integral_congr fun s _ => ?_
        rw [mul_sub]
  funext t
  rcases le_total 0 t with ht | ht
  · have hz := eq_zero_of_continuous_volterra_on_Icc hA hD ht
      (fun s _ => hDvolterra s) t ⟨ht, le_rfl⟩
    exact sub_eq_zero.mp hz
  · have hz := eq_zero_of_continuous_volterra_on_Icc_neg hA hD ht
      (fun s _ => hDvolterra s) t ⟨le_rfl, ht⟩
    exact sub_eq_zero.mp hz


end GaloisForLFunctions.HTGeometry

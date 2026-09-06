import GaloisForLFunctions.RHTower.ChronologicalHeatL2
import Mathlib.Algebra.BigOperators.Module

/-!
# Positive Abel transfer from the actual chronological heat errors

Averaging the exact dyadic Fermi response on the unit interval produces a
kernel K. The weights exp(-r)/K(r) are nonnegative, decreasing and at most two.
Finite Abel summation and the genuine positive-half-line L² pairing therefore
turn a tail bound δ for raw heat errors into the bound
`|sum mu(k) exp(-k*t)| ≤ 6*δ/sqrt(t) + 6 + M`.

This is a source-specific estimate, not an assumed convergence receiver. It
uses no RH assumption, numerical computation or inverse smoothing operation.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RHTower
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- The unit-interval average of the exact dyadic Fermi response. -/
def chronologicalAbelKernel (r : ℝ) : ℝ :=
  ∫ u in Ioc (0:ℝ) 1, chronologicalFermi (r*u)

private theorem fermi_unit_integrable (r : ℝ) :
    IntegrableOn (fun u => chronologicalFermi (r*u)) (Ioc (0:ℝ) 1) :=
  ((chronologicalFermi_continuous.comp (continuous_const.mul continuous_id)).integrableOn_Icc).mono_set Ioc_subset_Icc_self

private theorem fermi_scaled_mono {a b u : ℝ} (hab : a ≤ b) (_hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp a * chronologicalFermi (a*u) ≤ Real.exp b * chronologicalFermi (b*u) := by
  simp only [chronologicalFermi, mul_one_div]
  apply (div_le_div_iff₀ (by positivity : 0 < Real.exp (a*u)+1)
    (by positivity : 0 < Real.exp (b*u)+1)).mpr
  rw [mul_add, mul_one, mul_add, mul_one, ← Real.exp_add, ← Real.exp_add]
  exact add_le_add (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_le_exp.mpr hab)

theorem chronologicalAbelKernel_scaled_mono :
    Monotone (fun r => Real.exp r * chronologicalAbelKernel r) := by
  intro a b hab
  change Real.exp a * (∫ u in Ioc (0:ℝ) 1, chronologicalFermi (a*u)) ≤
    Real.exp b * (∫ u in Ioc (0:ℝ) 1, chronologicalFermi (b*u))
  rw [← integral_const_mul, ← integral_const_mul]
  apply setIntegral_mono_on ((fermi_unit_integrable a).const_mul _)
    ((fermi_unit_integrable b).const_mul _) measurableSet_Ioc
  intro u hu
  exact fermi_scaled_mono hab hu.1.le hu.2

theorem chronologicalAbelKernel_zero : chronologicalAbelKernel 0 = 1/2 := by
  simp [chronologicalAbelKernel, chronologicalFermi]
  ring

theorem chronologicalAbelKernel_scaled_lower {r : ℝ} (hr : 0 ≤ r) :
    1/2 ≤ Real.exp r * chronologicalAbelKernel r := by
  simpa [chronologicalAbelKernel_zero] using chronologicalAbelKernel_scaled_mono hr

theorem chronologicalAbelKernel_pos {r : ℝ} (hr : 0 ≤ r) :
    0 < chronologicalAbelKernel r := by
  have h := chronologicalAbelKernel_scaled_lower hr
  have he := Real.exp_pos r
  nlinarith

theorem chronologicalAbelKernel_le_half {r : ℝ} (hr : 0 ≤ r) :
    chronologicalAbelKernel r ≤ 1/2 := by
  calc
    _ ≤ ∫ _u in Ioc (0:ℝ) 1, (1/2:ℝ) := by
      apply setIntegral_mono_on (fermi_unit_integrable r) (integrableOn_const
        (C := (1/2:ℝ)) (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc
      intro u hu
      exact (chronologicalFermi_bounds _ (mul_nonneg hr hu.1.le)).2
    _ = _ := by simp

/-- The inverse averaged response produces positive Abel weights. -/
def chronologicalAbelWeight (r : ℝ) : ℝ :=
  (Real.exp r * chronologicalAbelKernel r)⁻¹

theorem chronologicalAbelWeight_bounds {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ chronologicalAbelWeight r ∧ chronologicalAbelWeight r ≤ 2 := by
  have hp : 0 < Real.exp r * chronologicalAbelKernel r :=
    mul_pos (Real.exp_pos _) (chronologicalAbelKernel_pos hr)
  constructor
  · exact (inv_pos.mpr hp).le
  · rw [chronologicalAbelWeight, ← one_div, div_le_iff₀ hp]
    nlinarith [chronologicalAbelKernel_scaled_lower hr]

theorem chronologicalAbelWeight_antitone : AntitoneOn chronologicalAbelWeight (Ici 0) := by
  intro a ha b hb hab
  exact inv_anti₀ (mul_pos (Real.exp_pos _) (chronologicalAbelKernel_pos ha))
    (chronologicalAbelKernel_scaled_mono hab)

theorem chronologicalAbelKernel_mul_weight {r : ℝ} (hr : 0 ≤ r) :
    chronologicalAbelKernel r * chronologicalAbelWeight r = Real.exp (-r) := by
  rw [chronologicalAbelWeight, mul_inv_rev, ← mul_assoc,
    mul_inv_cancel₀ (chronologicalAbelKernel_pos hr).ne', one_mul, Real.exp_neg]

/-- Finite Abel averaging cannot enlarge a uniform partial-sum bound by more
than the first nonnegative decreasing weight. -/
theorem chronological_positive_abel_bound (b w : ℕ → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hw : ∀ n, 0 ≤ w n) (hwmono : Antitone w)
    (hb : ∀ n, |∑ k ∈ Finset.range n, b k| ≤ B) (N : ℕ) :
    |∑ k ∈ Finset.range N, w k * b k| ≤ B * w 0 := by
  cases N with
  | zero => simpa using mul_nonneg hB (hw 0)
  | succ N =>
    have hi := Finset.sum_range_by_parts w b (N+1)
    simp only [Nat.add_sub_cancel, smul_eq_mul] at hi
    rw [hi]
    have hneg : (∑ i ∈ Finset.range N, (w (i+1)-w i) *
        ∑ k ∈ Finset.range (i+1), b k) =
        -(∑ i ∈ Finset.range N, (w i-w (i+1)) *
          ∑ k ∈ Finset.range (i+1), b k) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg, sub_neg_eq_add]
    calc
      _ ≤ |w N * ∑ k ∈ Finset.range (N+1), b k| +
          |∑ i ∈ Finset.range N, (w i-w (i+1)) *
            ∑ k ∈ Finset.range (i+1), b k| := abs_add_le _ _
      _ ≤ w N * B + ∑ i ∈ Finset.range N, (w i-w (i+1))*B := by
        apply add_le_add
        · rw [abs_mul, abs_of_nonneg (hw N)]
          exact mul_le_mul_of_nonneg_left (hb _) (hw _)
        · apply (Finset.abs_sum_le_sum_abs ..).trans
          apply Finset.sum_le_sum
          intro i _
          have hd : 0 ≤ w i-w (i+1) := sub_nonneg.mpr (hwmono (Nat.le_succ i))
          rw [abs_mul, abs_of_nonneg hd]
          exact mul_le_mul_of_nonneg_left (hb _) hd
      _ = B * w 0 := by rw [← Finset.sum_mul, Finset.sum_range_sub']; ring

/-- Exact norm scaling, including contractions of the positive time variable. -/
theorem chronologicalL2Norm_dilate_eq {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ioi 0)) {d : ℝ} (hd : 0 < d) :
    chronologicalL2Norm (fun t => f (d*t)) = chronologicalL2Norm f / Real.sqrt d := by
  have hcont : ContinuousOn (fun t => f (d*t)) (Ioi 0) :=
    hc.comp (continuous_const.mul continuous_id).continuousOn (fun t ht => mul_pos hd ht)
  rw [chronologicalL2Norm_eq_sqrt (hcont.aestronglyMeasurable (μ := volume) measurableSet_Ioi),
    chronologicalL2Norm_eq_sqrt (hc.aestronglyMeasurable (μ := volume) measurableSet_Ioi)]
  have he := integral_comp_mul_left_Ioi (fun t => f t^2) 0 hd
  simp only [mul_zero, smul_eq_mul] at he
  rw [he, Real.sqrt_mul (inv_nonneg.mpr hd.le), Real.sqrt_inv]
  ring

private theorem unit_memLp {f : ℝ → ℝ}
    (hf : MemLp f 2 chronologicalPositiveVolume) :
    MemLp f 2 (volume.restrict (Ioc (0:ℝ) 1)) :=
  hf.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)

private theorem unit_integral_norm_le {f : ℝ → ℝ}
    (hf : MemLp f 2 chronologicalPositiveVolume) :
    |∫ t in Ioc (0:ℝ) 1, f t| ≤ chronologicalL2Norm f := by
  have hg : MemLp (fun _t : ℝ => (1:ℝ)) 2 (volume.restrict (Ioc (0:ℝ) 1)) := memLp_const 1
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using unit_memLp hf) (by simpa using hg)
  have hc : (∫ t in Ioc (0:ℝ) 1, |f t|) ≤
      Real.sqrt (∫ t in Ioc (0:ℝ) 1, f t^2) := by
    rw [Real.sqrt_eq_rpow]
    simpa [Real.norm_eq_abs, Real.rpow_two, sq_abs] using hcs
  have hsq : (∫ t in Ioc (0:ℝ) 1, f t^2) ≤ ∫ t in Ioi (0:ℝ), f t^2 :=
    integral_mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)
      (Eventually.of_forall (fun t => sq_nonneg _)) hf.integrable_sq
  have hn : |∫ t in Ioc (0:ℝ) 1, f t| ≤ ∫ t in Ioc (0:ℝ) 1, |f t| := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (f := f) (μ := volume.restrict (Ioc (0:ℝ) 1))
  rw [chronologicalL2Norm_eq_sqrt hf.1]
  exact hn.trans (hc.trans (Real.sqrt_le_sqrt hsq))

private theorem raw_unit_integral_bound (N : ℕ) {d : ℝ} (hd : 0 < d) :
    |∫ u in Ioc (0:ℝ) 1, chronologicalRawHeatError N (d*u)| ≤
      chronologicalL2Norm (chronologicalRawHeatError N) / Real.sqrt d := by
  have h := unit_integral_norm_le (chronological_memLp_dilate
    (chronologicalRawHeatError_memLp N) (chronologicalRawHeatError_continuousOn N) hd)
  rwa [chronologicalL2Norm_dilate_eq (chronologicalRawHeatError_continuousOn N) hd] at h

private theorem exp_unit_integral_bound {d : ℝ} (hd : 0 ≤ d) :
    |∫ u in Ioc (0:ℝ) 1, Real.exp (-(d*u))| ≤ 1 := by
  rw [abs_of_nonneg (integral_nonneg (fun u => (Real.exp_pos _).le))]
  calc
    _ ≤ ∫ _u in Ioc (0:ℝ) 1, (1:ℝ) := by
      apply setIntegral_mono_on
        (((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
        (integrableOn_const (C := (1:ℝ)) (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc
      intro u hu
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hd hu.1.le))
    _ = 1 := by simp

/-- The Fermi average reads each raw residual through a bounded L² pairing. -/
theorem chronologicalAbel_partial_sum_bound (N : ℕ) {t : ℝ} (ht : 0 < t) :
    |∑ k ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) *
      chronologicalAbelKernel ((k:ℝ)*t)| ≤
      3 * chronologicalL2Norm (chronologicalRawHeatError N) / Real.sqrt t + 3 := by
  let J : (ℝ → ℝ) → ℝ := fun f => ∫ u in Ioc (0:ℝ) 1, f u
  have hraw (d : ℝ) (hd : 0 < d) :
      IntegrableOn (fun u => chronologicalRawHeatError N (d*u)) (Ioc (0:ℝ) 1) :=
    (unit_memLp (chronological_memLp_dilate (chronologicalRawHeatError_memLp N)
      (chronologicalRawHeatError_continuousOn N) hd)).integrable (by simp)
  have hex (d : ℝ) : IntegrableOn (fun u : ℝ => Real.exp (-(d*u))) (Ioc (0:ℝ) 1) :=
    ((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hsum : (∑ k ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) *
      chronologicalAbelKernel ((k:ℝ)*t)) =
      2 * J (fun u => chronologicalRawHeatError N ((2*t)*u)) -
        J (fun u => chronologicalRawHeatError N (t*u)) -
        2 * J (fun u => Real.exp (-((2*t)*u))) + J (fun u => Real.exp (-(t*u))) := by
    have hi : (∑ k ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) *
        chronologicalAbelKernel ((k:ℝ)*t)) =
        J (fun u => ∑ k ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) *
          chronologicalFermi (((k:ℝ)*t)*u)) := by
      dsimp only [J, chronologicalAbelKernel]
      rw [integral_finsetSum]
      · simp_rw [integral_const_mul]
      · intro k _
        exact (fermi_unit_integrable _).const_mul _
    rw [hi]
    have hp : J (fun u => ∑ k ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) *
          chronologicalFermi (((k:ℝ)*t)*u)) =
        J (fun u => 2 * chronologicalRawHeatError N ((2*t)*u) -
          chronologicalRawHeatError N (t*u) - 2 * Real.exp (-((2*t)*u)) +
            Real.exp (-(t*u))) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      have hh : (∑ k ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) *
          chronologicalFermi (((k:ℝ)*t)*u)) =
          2 * (∑ k ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) *
            fusionBoseDefect ((k:ℝ)*((2*t)*u))) -
          ∑ k ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) *
            fusionBoseDefect ((k:ℝ)*(t*u)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        rw [chronologicalFermi_eq_dyadic _ (mul_pos
          (mul_pos (by exact_mod_cast (Finset.mem_Ioc.mp hk).1) ht) hu.1)]
        have h1 : 2 * (((k:ℝ)*t)*u) = (k:ℝ)*((2*t)*u) := by ring
        have h2 : ((k:ℝ)*t)*u = (k:ℝ)*(t*u) := by ring
        rw [h1, h2]
        ring
      dsimp only
      rw [hh, chronologicalRawHeatError, chronologicalRawHeatError]
      ring
    rw [hp]
    dsimp only [J]
    have hA : IntegrableOn (fun u => 2 * chronologicalRawHeatError N ((2*t)*u))
        (Ioc (0:ℝ) 1) := (hraw (2*t) (by positivity)).const_mul 2
    have hAB : IntegrableOn (fun u => 2 * chronologicalRawHeatError N ((2*t)*u) -
        chronologicalRawHeatError N (t*u)) (Ioc (0:ℝ) 1) := hA.sub (hraw t ht)
    have hC : IntegrableOn (fun u => 2 * Real.exp (-((2*t)*u)))
        (Ioc (0:ℝ) 1) := (hex (2*t)).const_mul 2
    have hABC : IntegrableOn (fun u => 2 * chronologicalRawHeatError N ((2*t)*u) -
        chronologicalRawHeatError N (t*u) - 2 * Real.exp (-((2*t)*u)))
        (Ioc (0:ℝ) 1) := hAB.sub hC
    rw [integral_add hABC (hex t), integral_sub hAB hC,
      integral_sub hA (hraw t ht), integral_const_mul, integral_const_mul]
  rw [hsum]
  have ha := raw_unit_integral_bound N ht
  have hb := raw_unit_integral_bound N (by positivity : 0 < 2*t)
  have hc := exp_unit_integral_bound ht.le
  have hd := exp_unit_integral_bound (by positivity : 0 ≤ 2*t)
  have he : chronologicalL2Norm (chronologicalRawHeatError N) / Real.sqrt (2*t) ≤
      chronologicalL2Norm (chronologicalRawHeatError N) / Real.sqrt t :=
    div_le_div_of_nonneg_left (chronologicalL2Norm_nonneg _) (Real.sqrt_pos.mpr ht)
      (Real.sqrt_le_sqrt (by linarith))
  have hab := abs_sub (2 * J (fun u => chronologicalRawHeatError N ((2*t)*u)))
    (J (fun u => chronologicalRawHeatError N (t*u)))
  have habc := abs_sub
    (2 * J (fun u => chronologicalRawHeatError N ((2*t)*u)) - J (fun u => chronologicalRawHeatError N (t*u)))
    (2 * J (fun u => Real.exp (-((2*t)*u))))
  have habcd := abs_add_le
    (2 * J (fun u => chronologicalRawHeatError N ((2*t)*u)) - J (fun u => chronologicalRawHeatError N (t*u)) -
      2 * J (fun u => Real.exp (-((2*t)*u)))) (J (fun u => Real.exp (-(t*u))))
  simp only [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2)] at hab habc
  change |J _| ≤ _ at ha hb hc hd
  rw [mul_div_assoc]
  linarith

private theorem sum_range_succ_eq_sum_Ioc {f : ℕ → ℝ} (h0 : f 0 = 0) (N : ℕ) :
    (∑ k ∈ Finset.range (N+1), f k) = ∑ k ∈ Finset.Ioc 0 N, f k := by
  induction N with
  | zero => simp [h0]
  | succ N ih => rw [Finset.sum_range_succ, Finset.sum_Ioc_succ_top (Nat.zero_le N), ih]

private theorem abel_partial_sum_trivial (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |∑ k ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) *
      chronologicalAbelKernel ((k:ℝ)*t)| ≤ (N:ℝ)/2 := by
  calc
    _ ≤ ∑ k ∈ Finset.Ioc 0 N, |(ArithmeticFunction.moebius k : ℝ) *
        chronologicalAbelKernel ((k:ℝ)*t)| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _k ∈ Finset.Ioc 0 N, (1/2:ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      have hmu : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
      have hkt : 0 ≤ (k:ℝ)*t := mul_nonneg (Nat.cast_nonneg _) ht
      rw [abs_mul, abs_of_nonneg (chronologicalAbelKernel_pos hkt).le]
      exact (mul_le_mul_of_nonneg_right hmu (chronologicalAbelKernel_pos hkt).le).trans
        (by simpa using chronologicalAbelKernel_le_half hkt)
    _ = _ := by simp; ring

/-- A tail bound for raw heat errors gives a uniform bound for every finite
Möbius exponential sum. All weights and the source are the actual functions. -/
theorem chronologicalRaw_to_finite_laplace_bound (M : ℕ) {δ t : ℝ}
    (hδ : 0 ≤ δ) (ht : 0 < t)
    (hE : ∀ n, M ≤ n → chronologicalL2Norm (chronologicalRawHeatError n) ≤ δ) (N : ℕ) :
    |∑ k ∈ Finset.range N, (ArithmeticFunction.moebius k : ℝ) * Real.exp (-((k:ℝ)*t))| ≤
      6*δ / Real.sqrt t + 6 + (M:ℝ) := by
  let B := 3*δ / Real.sqrt t + 3 + (M:ℝ)/2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpart (n : ℕ) :
      |∑ k ∈ Finset.Ioc 0 n, (ArithmeticFunction.moebius k : ℝ) *
        chronologicalAbelKernel ((k:ℝ)*t)| ≤ B := by
    by_cases hmn : M ≤ n
    · apply (chronologicalAbel_partial_sum_bound n ht).trans
      have he := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hE n hmn) (by positivity : (0:ℝ) ≤ 3))
        (Real.sqrt_nonneg t)
      dsimp only [B]
      linarith [Nat.cast_nonneg (α := ℝ) M]
    · apply (abel_partial_sum_trivial n ht.le).trans
      have hnm : (n:ℝ) ≤ M := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hmn))
      dsimp only [B]
      have hx : 0 ≤ 3*δ / Real.sqrt t := by positivity
      linarith
  let b : ℕ → ℝ := fun k => (ArithmeticFunction.moebius k : ℝ) * chronologicalAbelKernel ((k:ℝ)*t)
  let w : ℕ → ℝ := fun k => chronologicalAbelWeight ((k:ℝ)*t)
  have hb : ∀ n, |∑ k ∈ Finset.range n, b k| ≤ B := by
    intro n
    cases n with
    | zero => simpa using hB
    | succ n =>
      rw [sum_range_succ_eq_sum_Ioc (by simp [b]) n]
      exact hpart n
  have hw : ∀ n, 0 ≤ w n := fun n =>
    (chronologicalAbelWeight_bounds (mul_nonneg (Nat.cast_nonneg _) ht.le)).1
  have hwm : Antitone w := by
    intro a b hab
    apply chronologicalAbelWeight_antitone
      (mul_nonneg (Nat.cast_nonneg _) ht.le) (mul_nonneg (Nat.cast_nonneg _) ht.le)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) ht.le
  have ha := chronological_positive_abel_bound b w B hB hw hwm hb N
  have hp (k : ℕ) : w k * b k =
      (ArithmeticFunction.moebius k : ℝ) * Real.exp (-((k:ℝ)*t)) := by
    dsimp only [w, b]
    calc
      _ = (ArithmeticFunction.moebius k : ℝ) *
          (chronologicalAbelKernel ((k:ℝ)*t) * chronologicalAbelWeight ((k:ℝ)*t)) := by ring
      _ = _ := by rw [chronologicalAbelKernel_mul_weight (mul_nonneg (Nat.cast_nonneg _) ht.le)]
  simp_rw [hp] at ha
  have hw0 : w 0 ≤ 2 := by
    exact (chronologicalAbelWeight_bounds (mul_nonneg (Nat.cast_nonneg _) ht.le)).2
  have hm := mul_le_mul_of_nonneg_left hw0 hB
  apply ha.trans (hm.trans_eq _)
  dsimp only [B]
  ring

end RHTower

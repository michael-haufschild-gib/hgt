import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Clamped Legendre kernels for running means

Let `𝔐 = d/dx (1 − x²) d/dx` be the Legendre operator.  For an even function `f` on `[−a, a]`
(`0 < a < 1`) write `G = (1 − x²) f'`, so that `𝔐 f = G'` and `G(0) = 0`; the running mean of
`𝔐 f` over `[0, t]` is then `G(t)/t = (1 − t²) f'(t)/t`.

For `0 < c ≤ a` put

`W(s) = s/a − min(s, c)/c`  and  `k(u) = ∫_u^a −W(s)/(1 − s²) ds`.

**Theorem** (`integral_mul_legendreKernel`).  `W ≤ 0` on `[0, a]` (`legendreMeanWeight_nonpos`), so
`k ≥ 0` (`legendreKernel_nonneg`), `k(a) = 0`, and for every even `f` with `𝔐² f = r`

`∫₀^a r · k = (1 − a²) f'(a)/a − (1 − c²) f'(c)/c`,

the difference of the running means of `𝔐 f` over `[0, a]` and `[0, c]`.

Proof.  Integrate by parts twice: `k(a) = 0` and `(1 − x²)(𝔐 f)'(0) = 0` kill the first boundary
term, `(1 − x²) k' = W` turns `∫ r k` into `−∫ W (𝔐 f)'`, and `W(0) = W(a) = 0` with
`W' = 1/a − 1_{s<c}/c` leaves `(1/a)∫₀^a 𝔐 f − (1/c)∫₀^c 𝔐 f`.

So a running-mean difference of `𝔐 f` is the pairing of `𝔐² f` with a nonnegative clamped
kernel: if `𝔐² f > 0` then the running mean of `𝔐 f` over `[0, a]` strictly exceeds every
shorter running mean (`sub_pos_of_legendre_sq_pos`).  A lower bound
`∫₀^a k ≥ (a − c) c²/(3a)` (`integral_legendreKernel_ge`) makes the gap linear in `a − c`.
-/

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

/-- The running-mean weight `W(s) = s/a − min(s, c)/c`. -/
def legendreMeanWeight (a c s : ℝ) : ℝ := s / a - min s c / c

/-- The density `−W(s)/(1 − s²)` of the clamped Legendre kernel. -/
def legendreKernelDensity (a c s : ℝ) : ℝ := -legendreMeanWeight a c s / (1 - s ^ 2)

/-- The clamped Legendre kernel `k(u) = ∫_u^a −W(s)/(1 − s²) ds`. -/
def legendreKernel (a c u : ℝ) : ℝ := ∫ s in u..a, legendreKernelDensity a c s

theorem continuous_legendreMeanWeight (a c : ℝ) : Continuous (legendreMeanWeight a c) := by
  unfold legendreMeanWeight
  fun_prop

theorem legendreMeanWeight_nonpos {a c s : ℝ} (hc : 0 < c) (hca : c ≤ a) (hs0 : 0 ≤ s)
    (hsa : s ≤ a) : legendreMeanWeight a c s ≤ 0 := by
  have ha : 0 < a := hc.trans_le hca
  unfold legendreMeanWeight
  rcases le_total s c with h | h
  · rw [min_eq_left h]
    have : s / a ≤ s / c := div_le_div_of_nonneg_left hs0 hc hca
    linarith
  · rw [min_eq_right h, div_self hc.ne']
    have : s / a ≤ 1 := (div_le_one ha).mpr hsa
    linarith

theorem legendreMeanWeight_zero (a : ℝ) {c : ℝ} (hc : 0 ≤ c) : legendreMeanWeight a c 0 = 0 := by
  unfold legendreMeanWeight
  rw [min_eq_left hc]
  simp

theorem legendreMeanWeight_self {a c : ℝ} (hc : 0 < c) (hca : c ≤ a) :
    legendreMeanWeight a c a = 0 := by
  have ha : 0 < a := hc.trans_le hca
  unfold legendreMeanWeight
  rw [min_eq_right hca, div_self ha.ne', div_self hc.ne', sub_self]

theorem legendreKernelDensity_nonneg {a c s : ℝ} (hc : 0 < c) (hca : c ≤ a) (ha1 : a < 1)
    (hs0 : 0 ≤ s) (hsa : s ≤ a) : 0 ≤ legendreKernelDensity a c s := by
  unfold legendreKernelDensity
  have h1 : 0 < 1 - s ^ 2 := by nlinarith
  exact div_nonneg (neg_nonneg.mpr (legendreMeanWeight_nonpos hc hca hs0 hsa)) h1.le

theorem continuousAt_legendreKernelDensity (a c : ℝ) {s : ℝ} (hs : s ^ 2 < 1) :
    ContinuousAt (legendreKernelDensity a c) s := by
  unfold legendreKernelDensity
  have h1 : 1 - s ^ 2 ≠ 0 := by linarith
  exact ((continuous_legendreMeanWeight a c).neg.continuousAt).div (by fun_prop) h1

theorem continuousOn_legendreKernelDensity {a c : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ContinuousOn (legendreKernelDensity a c) (uIcc 0 a) := by
  intro s hs
  rw [uIcc_of_le ha0] at hs
  have : s ^ 2 < 1 := by nlinarith [hs.1, hs.2]
  exact (continuousAt_legendreKernelDensity a c this).continuousWithinAt

theorem legendreKernel_nonneg {a c u : ℝ} (hc : 0 < c) (hca : c ≤ a) (ha1 : a < 1) (hu0 : 0 ≤ u)
    (hua : u ≤ a) : 0 ≤ legendreKernel a c u :=
  intervalIntegral.integral_nonneg hua fun _ hs =>
    legendreKernelDensity_nonneg hc hca ha1 (hu0.trans hs.1) hs.2

theorem legendreKernel_self (a c : ℝ) : legendreKernel a c a = 0 := integral_same

/-- `k' = W/(1 − x²)` inside `(−1, 1)`. -/
theorem hasDerivAt_legendreKernel {a c x : ℝ} (ha : a ^ 2 < 1) (hx : x ^ 2 < 1) :
    HasDerivAt (legendreKernel a c) (-legendreKernelDensity a c x) x := by
  have hopen : IsOpen {s : ℝ | s ^ 2 < 1} := isOpen_lt (by fun_prop) continuous_const
  have hcont : ContinuousOn (legendreKernelDensity a c) {s : ℝ | s ^ 2 < 1} := fun s hs =>
    (continuousAt_legendreKernelDensity a c hs).continuousWithinAt
  have hconv : ∀ s ∈ uIcc x a, s ^ 2 < 1 := by
    intro s hs
    have h1 : |x| < 1 := by rw [← sq_lt_one_iff_abs_lt_one]; exact hx
    have h2 : |a| < 1 := by rw [← sq_lt_one_iff_abs_lt_one]; exact ha
    rw [sq_lt_one_iff_abs_lt_one, abs_lt]
    rw [abs_lt] at h1 h2
    rcases le_total x a with h | h
    · rw [uIcc_of_le h] at hs; constructor <;> linarith [hs.1, hs.2]
    · rw [uIcc_of_ge h] at hs; constructor <;> linarith [hs.1, hs.2]
  exact intervalIntegral.integral_hasDerivAt_left
    (ContinuousOn.intervalIntegrable (hcont.mono hconv))
    (hcont.stronglyMeasurableAtFilter hopen x hx)
    (continuousAt_legendreKernelDensity a c hx)

/-- **Running means through a clamped Legendre kernel.**  Let `G = (1 − x²) f₁` have derivative `q`,
`q` have derivative `q₁`, and `(1 − x²) q₁` have derivative `r` on `[0, a]` (so `q = 𝔐 f` and
`r = 𝔐² f` for `f' = f₁`), with `f₁(0) = q₁(0) = 0` (evenness).  Then
`∫₀^a r · k = (1 − a²) f₁(a)/a − (1 − c²) f₁(c)/c`. -/
theorem integral_mul_legendreKernel {a c : ℝ} (hc : 0 < c) (hca : c ≤ a) (ha1 : a < 1)
    {f1 q q1 r : ℝ → ℝ}
    (hG : ∀ x ∈ uIcc 0 a, HasDerivAt (fun s => (1 - s ^ 2) * f1 s) (q x) x)
    (hq : ∀ x ∈ uIcc 0 a, HasDerivAt q (q1 x) x)
    (hH : ∀ x ∈ uIcc 0 a, HasDerivAt (fun s => (1 - s ^ 2) * q1 s) (r x) x)
    (hf10 : f1 0 = 0) (hq10 : q1 0 = 0)
    (hqc : ContinuousOn q (uIcc 0 a)) (hq1c : ContinuousOn q1 (uIcc 0 a))
    (hrc : ContinuousOn r (uIcc 0 a)) :
    ∫ x in (0 : ℝ)..a, r x * legendreKernel a c x =
      (1 - a ^ 2) * f1 a / a - (1 - c ^ 2) * f1 c / c := by
  have ha : 0 < a := hc.trans_le hca
  have hIa : uIcc 0 a = Icc 0 a := uIcc_of_le ha.le
  have hsubc : uIcc 0 c ⊆ uIcc 0 a := by
    rw [uIcc_of_le hc.le, hIa]; exact Icc_subset_Icc le_rfl hca
  have hsubca : uIcc c a ⊆ uIcc 0 a := by
    rw [uIcc_of_le hca, hIa]; exact Icc_subset_Icc hc.le le_rfl
  -- the running integral of `q`
  have hint_q : ∀ t ∈ Icc (0 : ℝ) a, ∫ x in (0 : ℝ)..t, q x = (1 - t ^ 2) * f1 t := by
    intro t ht
    have hsub : uIcc 0 t ⊆ uIcc 0 a := by
      rw [uIcc_of_le ht.1, hIa]; exact Icc_subset_Icc le_rfl ht.2
    rw [integral_eq_sub_of_hasDerivAt (fun x hx => hG x (hsub hx))
      ((hqc.mono hsub).intervalIntegrable)]
    simp [hf10]
  -- first integration by parts: `∫ k r = ∫ dens · (1 − x²) q₁`
  have hk : ∀ x ∈ uIcc 0 a, HasDerivAt (legendreKernel a c) (-legendreKernelDensity a c x) x := by
    intro x hx
    rw [hIa] at hx
    exact hasDerivAt_legendreKernel (by nlinarith) (by nlinarith [hx.1, hx.2])
  have hdens : IntervalIntegrable (fun x => -legendreKernelDensity a c x) volume 0 a :=
    (continuousOn_legendreKernelDensity ha.le ha1).neg.intervalIntegrable
  have step1 := integral_mul_deriv_eq_deriv_mul hk hH hdens hrc.intervalIntegrable
  rw [legendreKernel_self, hq10] at step1
  have e1 : ∫ x in (0 : ℝ)..a, r x * legendreKernel a c x =
      -∫ x in (0 : ℝ)..a, legendreMeanWeight a c x * q1 x := by
    have hcomm : ∫ x in (0 : ℝ)..a, r x * legendreKernel a c x =
        ∫ x in (0 : ℝ)..a, legendreKernel a c x * r x := by
      congr 1; funext x; ring
    rw [hcomm, step1, ← intervalIntegral.integral_neg]
    simp only [zero_mul, mul_zero, sub_zero, zero_sub]
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [hIa] at hx
    have h1 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
    simp only [legendreKernelDensity]
    field_simp
  -- second integration by parts, split at `c`
  have hq1int : IntervalIntegrable q1 volume 0 a := hq1c.intervalIntegrable
  have hqint : IntervalIntegrable q volume 0 a := hqc.intervalIntegrable
  have hlin : ∀ x ∈ uIcc (0 : ℝ) a, HasDerivAt (fun s : ℝ => s / a) (1 / a) x := fun x _ => by
    simpa using (hasDerivAt_id x).div_const a
  have hA := integral_mul_deriv_eq_deriv_mul hlin hq
    (intervalIntegrable_const (c := (1 / a))) hq1int
  have hlinc : ∀ x ∈ uIcc (0 : ℝ) c, HasDerivAt (fun s : ℝ => s) 1 x := fun x _ => hasDerivAt_id x
  have hB := integral_mul_deriv_eq_deriv_mul hlinc (fun x hx => hq x (hsubc hx))
    (intervalIntegrable_const (c := (1 : ℝ))) ((hq1c.mono hsubc).intervalIntegrable)
  have hC : ∫ x in c..a, q1 x = q a - q c :=
    integral_eq_sub_of_hasDerivAt (fun x hx => hq x (hsubca hx))
      ((hq1c.mono hsubca).intervalIntegrable)
  have hmin1 : ∫ x in (0 : ℝ)..c, min x c * q1 x = ∫ x in (0 : ℝ)..c, x * q1 x := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hc.le] at hx
    simp only [min_eq_left hx.2]
  have hmin2 : ∫ x in c..a, min x c * q1 x = c * ∫ x in c..a, q1 x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hca] at hx
    simp only [min_eq_right hx.1]
  have hminint : IntervalIntegrable (fun x => min x c * q1 x) volume 0 a :=
    ((continuous_id.min continuous_const).continuousOn.mul hq1c).intervalIntegrable
  have hsplit : ∫ x in (0 : ℝ)..a, min x c * q1 x =
      (∫ x in (0 : ℝ)..c, min x c * q1 x) + ∫ x in c..a, min x c * q1 x :=
    (integral_add_adjacent_intervals (hminint.mono_set hsubc) (hminint.mono_set hsubca)).symm
  have hW : ∫ x in (0 : ℝ)..a, legendreMeanWeight a c x * q1 x =
      (∫ x in (0 : ℝ)..a, x / a * q1 x) - (1 / c) * ∫ x in (0 : ℝ)..a, min x c * q1 x := by
    have hi1 : IntervalIntegrable (fun x => x / a * q1 x) volume 0 a :=
      ((continuous_id.div_const a).continuousOn.mul hq1c).intervalIntegrable
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hi1
      (hminint.const_mul (1 / c))]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [legendreMeanWeight]
    ring
  have hqa := hint_q a ⟨ha.le, le_rfl⟩
  have hqc' := hint_q c ⟨hc.le, hca⟩
  simp only [intervalIntegral.integral_const_mul, one_mul] at hA hB
  rw [e1, hW, hsplit, hmin1, hmin2, hB, hC, hA, hqa, hqc']
  field_simp
  ring

/-- **Lower bound.**  `∫₀^a k ≥ (a − c) c²/(3a)`: on `[u, c]` the density is at least
`s (1/c − 1/a)` and on `[c, a]` it is nonnegative. -/
theorem integral_legendreKernel_ge {a c : ℝ} (hc : 0 < c) (hca : c ≤ a) (ha1 : a < 1) :
    (a - c) * c ^ 2 / (3 * a) ≤ ∫ u in (0 : ℝ)..a, legendreKernel a c u := by
  have ha : 0 < a := hc.trans_le hca
  have hd : ∀ s ∈ Icc (0 : ℝ) c, s * (1 / c - 1 / a) ≤ legendreKernelDensity a c s := by
    intro s hs
    have hs1 : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
    have hs2 : 1 - s ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
    have hW : -legendreMeanWeight a c s = s * (1 / c - 1 / a) := by
      unfold legendreMeanWeight; rw [min_eq_left hs.2]; ring
    have hnn : 0 ≤ s * (1 / c - 1 / a) := mul_nonneg hs.1 (by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hc hca)
    unfold legendreKernelDensity
    rw [hW, le_div_iff₀ hs1]
    nlinarith
  have hcont := continuousOn_legendreKernelDensity (a := a) (c := c) ha.le ha1
  have hpt : ∀ u ∈ Icc (0 : ℝ) c, (1 / c - 1 / a) * (c ^ 2 - u ^ 2) / 2 ≤ legendreKernel a c u := by
    intro u hu
    have hsub1 : uIcc u c ⊆ uIcc 0 a := by
      rw [uIcc_of_le hu.2, uIcc_of_le ha.le]; exact Icc_subset_Icc hu.1 hca
    have hsub2 : uIcc c a ⊆ uIcc 0 a := by
      rw [uIcc_of_le hca, uIcc_of_le ha.le]; exact Icc_subset_Icc hc.le le_rfl
    have hsplit : legendreKernel a c u = (∫ s in u..c, legendreKernelDensity a c s) +
        ∫ s in c..a, legendreKernelDensity a c s :=
      (integral_add_adjacent_intervals ((hcont.mono hsub1).intervalIntegrable)
        ((hcont.mono hsub2).intervalIntegrable)).symm
    have h2 : 0 ≤ ∫ s in c..a, legendreKernelDensity a c s :=
      intervalIntegral.integral_nonneg hca fun s hs =>
        legendreKernelDensity_nonneg hc hca ha1 (hc.le.trans hs.1) hs.2
    have h1 : ∫ s in u..c, s * (1 / c - 1 / a) ≤ ∫ s in u..c, legendreKernelDensity a c s :=
      intervalIntegral.integral_mono_on hu.2 ((by fun_prop : Continuous fun s : ℝ =>
        s * (1 / c - 1 / a)).intervalIntegrable _ _) ((hcont.mono hsub1).intervalIntegrable)
        fun s hs => hd s ⟨hu.1.trans hs.1, hs.2⟩
    have hcomp : ∫ s in u..c, s * (1 / c - 1 / a) = (1 / c - 1 / a) * (c ^ 2 - u ^ 2) / 2 := by
      rw [intervalIntegral.integral_mul_const, integral_id]; ring
    rw [hsplit]
    linarith
  have hkcont : ContinuousOn (legendreKernel a c) (uIcc 0 a) := by
    intro u hu
    rw [uIcc_of_le ha.le] at hu
    exact (hasDerivAt_legendreKernel (by nlinarith) (by nlinarith [hu.1, hu.2])).continuousAt
      |>.continuousWithinAt
  have hsplit : ∫ u in (0 : ℝ)..a, legendreKernel a c u =
      (∫ u in (0 : ℝ)..c, legendreKernel a c u) +
      ∫ u in c..a, legendreKernel a c u := by
    have s1 : uIcc 0 c ⊆ uIcc 0 a := by
      rw [uIcc_of_le hc.le, uIcc_of_le ha.le]; exact Icc_subset_Icc le_rfl hca
    have s2 : uIcc c a ⊆ uIcc 0 a := by
      rw [uIcc_of_le hca, uIcc_of_le ha.le]; exact Icc_subset_Icc hc.le le_rfl
    exact (integral_add_adjacent_intervals ((hkcont.mono s1).intervalIntegrable)
      ((hkcont.mono s2).intervalIntegrable)).symm
  have hB : 0 ≤ ∫ u in c..a, legendreKernel a c u :=
    intervalIntegral.integral_nonneg hca fun u hu =>
      legendreKernel_nonneg hc hca ha1 (hc.le.trans hu.1) hu.2
  have hA : ∫ u in (0 : ℝ)..c, (1 / c - 1 / a) * (c ^ 2 - u ^ 2) / 2 ≤
      ∫ u in (0 : ℝ)..c, legendreKernel a c u := by
    have s1 : uIcc 0 c ⊆ uIcc 0 a := by
      rw [uIcc_of_le hc.le, uIcc_of_le ha.le]; exact Icc_subset_Icc le_rfl hca
    exact intervalIntegral.integral_mono_on hc.le ((by fun_prop : Continuous fun u : ℝ =>
      (1 / c - 1 / a) * (c ^ 2 - u ^ 2) / 2).intervalIntegrable _ _)
      ((hkcont.mono s1).intervalIntegrable) hpt
  have hcomp : ∫ u in (0 : ℝ)..c, (1 / c - 1 / a) * (c ^ 2 - u ^ 2) / 2 =
      (a - c) * c ^ 2 / (3 * a) := by
    have e : (fun u : ℝ => (1 / c - 1 / a) * (c ^ 2 - u ^ 2) / 2) =
        fun u => (1 / c - 1 / a) / 2 * c ^ 2 - (1 / c - 1 / a) / 2 * u ^ 2 := by
      funext u; ring
    rw [e, intervalIntegral.integral_sub ((by fun_prop : Continuous fun u : ℝ =>
      (1 / c - 1 / a) / 2 * c ^ 2).intervalIntegrable _ _) ((by fun_prop : Continuous fun u : ℝ =>
      (1 / c - 1 / a) / 2 * u ^ 2).intervalIntegrable _ _), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_pow]
    have ha0 : a ≠ 0 := ha.ne'
    have hc0 : c ≠ 0 := hc.ne'
    have hac : 1 / c - 1 / a = (a - c) / (a * c) := by field_simp
    simp only [smul_eq_mul, sub_zero]
    rw [hac]
    field_simp
    ring
  rw [hsplit]
  linarith

end

end HTGeometry
end GaloisForLFunctions

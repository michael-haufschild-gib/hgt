import GaloisForLFunctions.HTGeometry.BohrExponentialSeriesCoefficient
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The entire carrier of an exponential series

An exponential series whose amplitudes stay summable after every exponential weight converges
normally on every compact set of the plane, so it is an entire function, and on the real line it is
the almost periodic carrier of the same data.

Bohr--Fourier uniqueness on the real line therefore determines the phases of the entire carrier:
the holomorphic hull map of a frequency family with pairwise distinct frequencies and nonvanishing
amplitudes is injective.
-/

open Filter Topology Set
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type*}

/-- The entire character of a real frequency. -/
def cexpChar (omega : ℝ) (z : ℂ) : ℂ := Complex.exp (Complex.I * (omega : ℂ) * z)

theorem norm_cexpChar (omega : ℝ) (z : ℂ) :
    ‖cexpChar omega z‖ = Real.exp (-(omega * z.im)) := by
  rw [cexpChar, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem cexpChar_ofReal (omega t : ℝ) : cexpChar omega (t : ℂ) = expChar omega t := by
  rw [cexpChar, expChar]
  congr 1
  push_cast
  ring

theorem differentiable_cexpChar (omega : ℝ) : Differentiable ℂ (cexpChar omega) := by
  unfold cexpChar
  fun_prop

/-- The entire carrier of an exponential series. -/
def cexpSeriesCarrier (a : ι → ℂ) (omega : ι → ℝ) (z : ℂ) : ℂ :=
  ∑' i, a i * cexpChar (omega i) z

/-- Amplitudes which stay summable after every exponential weight. -/
def ExpSeriesNormallySummable (a : ι → ℂ) (omega : ι → ℝ) : Prop :=
  ∀ R : ℝ, Summable fun i => ‖a i‖ * Real.exp (R * |omega i|)

theorem norm_term_le_of_mem_closedBall {a : ι → ℂ} {omega : ι → ℝ} {R : ℝ} (i : ι)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖a i * cexpChar (omega i) z‖ ≤ ‖a i‖ * Real.exp (R * |omega i|) := by
  have habs : |z.im| ≤ R := by
    have h := mem_closedBall_zero_iff.mp hz
    exact le_trans (Complex.abs_im_le_norm z) h
  rw [norm_mul, norm_cexpChar]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine Real.exp_le_exp.mpr ?_
  calc -(omega i * z.im) ≤ |omega i * z.im| := neg_le_abs _
    _ = |omega i| * |z.im| := abs_mul _ _
    _ ≤ |omega i| * R := by
        refine mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    _ = R * |omega i| := by ring

theorem summable_cexpSeries {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) (z : ℂ) :
    Summable fun i => a i * cexpChar (omega i) z := by
  refine Summable.of_norm_bounded (h ‖z‖) fun i => ?_
  exact norm_term_le_of_mem_closedBall i (Metric.mem_closedBall.mpr (by simp))

/-- Normal convergence on every closed ball. -/
theorem tendstoUniformlyOn_cexpSeries {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) (R : ℝ) :
    TendstoUniformlyOn (fun (S : Finset ι) z => ∑ i ∈ S, a i * cexpChar (omega i) z)
      (cexpSeriesCarrier a omega) atTop (Metric.closedBall (0 : ℂ) R) :=
  tendstoUniformlyOn_tsum (h R) fun i _ hz => norm_term_le_of_mem_closedBall i hz

/-- Normal convergence on every compact set. -/
theorem tendstoLocallyUniformly_cexpSeries {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) :
    TendstoLocallyUniformlyOn (fun (S : Finset ι) z => ∑ i ∈ S, a i * cexpChar (omega i) z)
      (cexpSeriesCarrier a omega) atTop Set.univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  exact (tendstoUniformlyOn_cexpSeries h R).mono hR

/-- **The carrier is entire.** -/
theorem differentiable_cexpSeriesCarrier {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) :
    Differentiable ℂ (cexpSeriesCarrier a omega) := by
  rw [← differentiableOn_univ]
  refine TendstoLocallyUniformlyOn.differentiableOn (tendstoLocallyUniformly_cexpSeries h)
    ?_ isOpen_univ
  refine Filter.Eventually.of_forall fun S => Differentiable.differentiableOn ?_
  unfold cexpChar
  fun_prop

/-- On the real line the entire carrier is the almost periodic carrier. -/
theorem cexpSeriesCarrier_ofReal (a : ι → ℂ) (omega : ι → ℝ) (t : ℝ) :
    cexpSeriesCarrier a omega (t : ℂ) = expSeriesCarrier a omega t := by
  rw [cexpSeriesCarrier, expSeriesCarrier]
  exact tsum_congr fun i => by rw [cexpChar_ofReal]

/-- **The holomorphic hull is injective.**  Two phase assignments of the same nonvanishing amplitude
family whose entire carriers agree are equal. -/
theorem cexpSeriesCarrier_phase_injective {a : ι → ℂ} {omega : ι → ℝ} {lam mu : ι → ℂ}
    (halam : Summable fun i => ‖a i * lam i‖) (hamu : Summable fun i => ‖a i * mu i‖)
    (hane : ∀ i, a i ≠ 0) (hinj : Function.Injective omega)
    (h : cexpSeriesCarrier (fun i => a i * lam i) omega
      = cexpSeriesCarrier (fun i => a i * mu i) omega) :
    lam = mu := by
  refine expSeriesCarrier_phase_injective halam hamu hane hinj ?_
  funext t
  rw [← cexpSeriesCarrier_ofReal, ← cexpSeriesCarrier_ofReal, h]


/-! ## Phase families -/

/-- Damping by a bounded phase family preserves the normal summability hypothesis. -/
theorem expSeriesNormallySummable_phase {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) {lam : ι → ℂ} (hlam : ∀ i, ‖lam i‖ ≤ 1) :
    ExpSeriesNormallySummable (fun i => a i * lam i) omega := by
  intro R
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (h R)
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
  rw [norm_mul]
  calc ‖a i‖ * ‖lam i‖ ≤ ‖a i‖ * 1 := by
        refine mul_le_mul_of_nonneg_left (hlam i) (norm_nonneg _)
    _ = ‖a i‖ := mul_one _

/-- **The tail of a phase-modulated carrier is uniformly small.**  The bound does not depend on the
phase family: it is the tail of the undamped amplitudes with their exponential weight. -/
theorem norm_cexpSeriesCarrier_phase_sub_partial_le {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) {lam : ι → ℂ} (hlam : ∀ i, ‖lam i‖ ≤ 1)
    (S : Finset ι) {R : ℝ} {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖cexpSeriesCarrier (fun i => a i * lam i) omega z
        - ∑ i ∈ S, (a i * lam i) * cexpChar (omega i) z‖
      ≤ ∑' i : ((S : Set ι)ᶜ : Set ι), ‖a i‖ * Real.exp (R * |omega i|) := by
  classical
  have hphase := expSeriesNormallySummable_phase h hlam
  have hsum := summable_cexpSeries hphase z
  have hsplit := hsum.sum_add_tsum_compl (s := S)
  have hdiff : cexpSeriesCarrier (fun i => a i * lam i) omega z
        - ∑ i ∈ S, (a i * lam i) * cexpChar (omega i) z
      = ∑' i : ((S : Set ι)ᶜ : Set ι), (a i * lam i) * cexpChar (omega i) z := by
    rw [cexpSeriesCarrier, ← hsplit]
    ring
  have hbound : ∀ i : ((S : Set ι)ᶜ : Set ι),
      ‖(a i * lam i) * cexpChar (omega i) z‖ ≤ ‖a i‖ * Real.exp (R * |omega i|) := by
    intro i
    refine le_trans (norm_term_le_of_mem_closedBall (a := fun i => a i * lam i) i hz) ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
    rw [norm_mul]
    calc ‖a i.1‖ * ‖lam i.1‖ ≤ ‖a i.1‖ * 1 := by
          refine mul_le_mul_of_nonneg_left (hlam i.1) (norm_nonneg _)
      _ = ‖a i.1‖ := mul_one _
  have hnormSummable : Summable fun i : ((S : Set ι)ᶜ : Set ι) =>
      ‖(a i * lam i) * cexpChar (omega i) z‖ := by
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbound ?_
    exact ((h R).subtype _)
  rw [hdiff]
  refine le_trans (norm_tsum_le_tsum_norm hnormSummable) ?_
  exact Summable.tsum_le_tsum hbound hnormSummable ((h R).subtype _)


theorem norm_cexpChar_le_of_mem_closedBall {omega R : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖cexpChar omega z‖ ≤ Real.exp (R * |omega|) := by
  have habs : |z.im| ≤ R := by
    have h := mem_closedBall_zero_iff.mp hz
    exact le_trans (Complex.abs_im_le_norm z) h
  rw [norm_cexpChar]
  refine Real.exp_le_exp.mpr ?_
  calc -(omega * z.im) ≤ |omega * z.im| := neg_le_abs _
    _ = |omega| * |z.im| := abs_mul _ _
    _ ≤ |omega| * R := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    _ = R * |omega| := by ring

/-- **The head-tail estimate for two phase families.**  On every closed ball, two phase-modulated
carriers differ by at most the weighted head distance of a finite frequency set plus twice the tail
of the remaining weights.  This is the quantitative form of continuity of the hull map: the tail is
uniform in the phases, and the head depends on finitely many phase coordinates. -/
theorem norm_cexpSeriesCarrier_phase_sub_phase_le {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) {lam mu : ι → ℂ}
    (hlam : ∀ i, ‖lam i‖ ≤ 1) (hmu : ∀ i, ‖mu i‖ ≤ 1) (S : Finset ι) {R : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖cexpSeriesCarrier (fun i => a i * lam i) omega z
        - cexpSeriesCarrier (fun i => a i * mu i) omega z‖
      ≤ (∑ i ∈ S, ‖a i‖ * ‖lam i - mu i‖ * Real.exp (R * |omega i|))
        + 2 * ∑' i : ((S : Set ι)ᶜ : Set ι), ‖a i‖ * Real.exp (R * |omega i|) := by
  classical
  set headL : ℂ := ∑ i ∈ S, (a i * lam i) * cexpChar (omega i) z with hheadL
  set headM : ℂ := ∑ i ∈ S, (a i * mu i) * cexpChar (omega i) z with hheadM
  set tail : ℝ := ∑' i : ((S : Set ι)ᶜ : Set ι), ‖a i‖ * Real.exp (R * |omega i|) with htail
  have hL : ‖cexpSeriesCarrier (fun i => a i * lam i) omega z - headL‖ ≤ tail :=
    norm_cexpSeriesCarrier_phase_sub_partial_le h hlam S hz
  have hM : ‖cexpSeriesCarrier (fun i => a i * mu i) omega z - headM‖ ≤ tail :=
    norm_cexpSeriesCarrier_phase_sub_partial_le h hmu S hz
  have hhead : ‖headL - headM‖
      ≤ ∑ i ∈ S, ‖a i‖ * ‖lam i - mu i‖ * Real.exp (R * |omega i|) := by
    have hdiff : headL - headM
        = ∑ i ∈ S, (a i * (lam i - mu i)) * cexpChar (omega i) z := by
      rw [hheadL, hheadM, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hdiff]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, norm_mul, mul_assoc]
    have h1 : ‖lam i - mu i‖ * ‖cexpChar (omega i) z‖
        ≤ ‖lam i - mu i‖ * Real.exp (R * |omega i|) :=
      mul_le_mul_of_nonneg_left (norm_cexpChar_le_of_mem_closedBall hz)
        (norm_nonneg (lam i - mu i))
    calc ‖a i‖ * (‖lam i - mu i‖ * ‖cexpChar (omega i) z‖)
        ≤ ‖a i‖ * (‖lam i - mu i‖ * Real.exp (R * |omega i|)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg (a i))
      _ = ‖a i‖ * ‖lam i - mu i‖ * Real.exp (R * |omega i|) := by ring
  set A : ℂ := cexpSeriesCarrier (fun i => a i * lam i) omega z with hA
  set B : ℂ := cexpSeriesCarrier (fun i => a i * mu i) omega z with hB
  have htri : ‖A - B‖ ≤ ‖A - headL‖ + ‖headL - headM‖ + ‖headM - B‖ := by
    calc ‖A - B‖ = ‖(A - headL) + (headL - headM) + (headM - B)‖ := by
          congr 1
          ring
      _ ≤ ‖(A - headL) + (headL - headM)‖ + ‖headM - B‖ := norm_add_le _ _
      _ ≤ ‖A - headL‖ + ‖headL - headM‖ + ‖headM - B‖ := by
          gcongr
          exact norm_add_le _ _
  have hMB : ‖headM - B‖ ≤ tail := by
    rw [norm_sub_rev]
    exact hM
  linarith [htri, hL, hMB, hhead]


/-- Absolute convergence makes the tail sums of a real family arbitrarily small. -/
theorem exists_finset_tsum_compl_lt_real {u : ι → ℝ} (hu : Summable u) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ι, ∀ T : Finset ι, S ⊆ T → ∑' i : ((T : Set ι)ᶜ : Set ι), u i < ε := by
  classical
  obtain ⟨S, hS⟩ := Metric.tendsto_atTop.mp hu.hasSum ε hε
  refine ⟨S, fun T hT => ?_⟩
  have hsplit := hu.sum_add_tsum_compl (s := T)
  have hdist := hS T hT
  rw [Real.dist_eq, abs_lt] at hdist
  have htail : ∑' i : ((T : Set ι)ᶜ : Set ι), u i = (∑' i, u i) - ∑ i ∈ T, u i := by
    rw [← hsplit]
    ring
  rw [htail]
  linarith [hdist.1]

theorem summable_norm_of_expSeriesNormallySummable {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) : Summable fun i => ‖a i‖ := by
  have h0 := h 0
  refine h0.congr fun i => ?_
  simp

/-! ## Decay high in the upper half plane -/

theorem summable_norm_weight (a : ι → ℂ) (omega : ι → ℝ)
    (h : ExpSeriesNormallySummable a omega) (y : ℝ) :
    Summable fun i => ‖a i‖ * Real.exp (-(omega i * y)) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (h |y|)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine Real.exp_le_exp.mpr ?_
  calc -(omega i * y) ≤ |omega i * y| := neg_le_abs _
    _ = |omega i| * |y| := abs_mul _ _
    _ = |y| * |omega i| := by ring

theorem norm_cexpSeriesCarrier_le_tsum {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) (z : ℂ) :
    ‖cexpSeriesCarrier a omega z‖ ≤ ∑' i, ‖a i‖ * Real.exp (-(omega i * z.im)) := by
  have hmaj := summable_norm_weight a omega h z.im
  have hterm : ∀ i, ‖a i * cexpChar (omega i) z‖ = ‖a i‖ * Real.exp (-(omega i * z.im)) := by
    intro i
    rw [norm_mul, norm_cexpChar]
  have hnorm : Summable fun i => ‖a i * cexpChar (omega i) z‖ :=
    hmaj.congr fun i => (hterm i).symm
  refine le_trans (norm_tsum_le_tsum_norm hnorm) ?_
  exact le_of_eq (tsum_congr hterm)

/-- **Uniform decay above a height.**  With strictly positive frequencies and summable amplitudes
the carrier is uniformly small high in the upper half plane. -/
theorem exists_im_bound_norm_cexpSeriesCarrier_le {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) (hpos : ∀ i, 0 < omega i) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℝ, 0 ≤ Y ∧ ∀ z : ℂ, Y ≤ z.im → ‖cexpSeriesCarrier a omega z‖ ≤ ε := by
  classical
  have hnorm : Summable fun i => ‖a i‖ := summable_norm_of_expSeriesNormallySummable h
  obtain ⟨S, hS⟩ := exists_finset_tsum_compl_lt_real hnorm (show (0 : ℝ) < ε / 2 by linarith)
  have hhead : Filter.Tendsto
      (fun y : ℝ => ∑ i ∈ S, ‖a i‖ * Real.exp (-(omega i * y))) Filter.atTop (nhds 0) := by
    have hzero : (0 : ℝ) = ∑ i ∈ S, (0 : ℝ) := by simp
    rw [hzero]
    refine tendsto_finsetSum _ fun i _ => ?_
    have hexp : Filter.Tendsto (fun y : ℝ => Real.exp (-(omega i * y))) Filter.atTop (nhds 0) := by
      have hlin : Filter.Tendsto (fun y : ℝ => omega i * y) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (hpos i) Filter.tendsto_id
      exact Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp hlin)
    simpa using hexp.const_mul (‖a i‖)
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp
    (hhead.eventually_le_const (show (0 : ℝ) < ε / 2 by linarith))
  refine ⟨max Y₀ 0, le_max_right _ _, fun z hz => ?_⟩
  have hy0 : 0 ≤ z.im := le_trans (le_max_right Y₀ 0) hz
  have hyY : Y₀ ≤ z.im := le_trans (le_max_left Y₀ 0) hz
  have hmaj := summable_norm_weight a omega h z.im
  have hsplit := hmaj.sum_add_tsum_compl (s := S)
  have htailbound : ∑' i : ((S : Set ι)ᶜ : Set ι), ‖a i‖ * Real.exp (-(omega i * z.im))
      ≤ ∑' i : ((S : Set ι)ᶜ : Set ι), ‖a i‖ := by
    refine Summable.tsum_le_tsum (fun i => ?_) (hmaj.subtype _) (hnorm.subtype _)
    have hle : Real.exp (-(omega i * z.im)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have : 0 ≤ omega i * z.im := mul_nonneg (le_of_lt (hpos i)) hy0
      linarith
    calc ‖a i.1‖ * Real.exp (-(omega i.1 * z.im)) ≤ ‖a i.1‖ * 1 :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = ‖a i.1‖ := mul_one _
  have hheadbound : ∑ i ∈ S, ‖a i‖ * Real.exp (-(omega i * z.im)) ≤ ε / 2 := hY₀ z.im hyY
  have htail : ∑' i : ((S : Set ι)ᶜ : Set ι), ‖a i‖ < ε / 2 := hS S (le_refl S)
  refine le_trans (norm_cexpSeriesCarrier_le_tsum h z) ?_
  rw [← hsplit]
  linarith [htailbound, hheadbound, htail]

end

end GaloisForLFunctions

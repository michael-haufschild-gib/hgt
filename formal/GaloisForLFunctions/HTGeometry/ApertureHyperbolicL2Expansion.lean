import GaloisForLFunctions.HTGeometry.VectorPowerSeriesLeadingOrder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# The hyperbolic deficiency base on a bounded aperture

On a bounded aperture the hyperbolic profiles `cosh(cX)` and `sinh(cX)` are `L²` limits of their
monomial Taylor series: the tail is uniformly small on the aperture, and a finite measure turns a
uniform bound into an `L²` bound.

Combined with the leading-order theorem for vector power series, this converts the first visible
even or odd polynomial degree of a bounded linear observable into the exact rate of the
corresponding parity energy.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The aperture measure -/

/-- Lebesgue measure on the aperture `[-a, a]`. -/
def apertureMeasure (a : ℝ) : Measure ℝ := volume.restrict (Icc (-a) a)

instance instIsFiniteMeasureApertureMeasure (a : ℝ) : IsFiniteMeasure (apertureMeasure a) := by
  constructor
  rw [apertureMeasure, Measure.restrict_apply_univ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

theorem apertureMeasure_univ_toReal {a : ℝ} (ha : 0 ≤ a) :
    (apertureMeasure a Set.univ).toReal = 2 * a := by
  rw [apertureMeasure, Measure.restrict_apply_univ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]
  ring

theorem abs_le_of_mem_aperture {a x : ℝ} (hx : x ∈ Icc (-a) a) : |x| ≤ a :=
  abs_le.mpr ⟨hx.1, hx.2⟩

theorem measureUnivNNReal_apertureMeasure {a : ℝ} (ha : 0 ≤ a) :
    ((measureUnivNNReal (apertureMeasure a) : ℝ≥0) : ℝ) = 2 * a := by
  rw [← apertureMeasure_univ_toReal ha]
  rfl

theorem rpow_measureUnivNNReal_apertureMeasure {a : ℝ} (ha : 0 ≤ a) :
    ((measureUnivNNReal (apertureMeasure a) : ℝ≥0) : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹
      = Real.sqrt (2 * a) := by
  rw [measureUnivNNReal_apertureMeasure ha,
    show (((2 : ℝ≥0∞).toReal))⁻¹ = (1 : ℝ) / 2 by norm_num, ← Real.sqrt_eq_rpow]

/-! ## Elementary hyperbolic bounds -/

theorem cosh_le_exp_abs (t : ℝ) : Real.cosh t ≤ Real.exp |t| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp t ≤ Real.exp |t| := Real.exp_le_exp.mpr (le_abs_self t)
  have h2 : Real.exp (-t) ≤ Real.exp |t| := Real.exp_le_exp.mpr (neg_le_abs t)
  linarith

theorem abs_sinh_le_exp_abs (t : ℝ) : |Real.sinh t| ≤ Real.exp |t| := by
  rw [Real.sinh_eq, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have h1 : Real.exp t ≤ Real.exp |t| := Real.exp_le_exp.mpr (le_abs_self t)
  have h2 : Real.exp (-t) ≤ Real.exp |t| := Real.exp_le_exp.mpr (neg_le_abs t)
  have h1' : (0:ℝ) < Real.exp t := Real.exp_pos _
  have h2' : (0:ℝ) < Real.exp (-t) := Real.exp_pos _
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  rcases abs_cases (Real.exp t - Real.exp (-t)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith

/-! ## The `L²` classes -/

theorem memLp_pow (a : ℝ) (n : ℕ) : MemLp (fun x : ℝ => x ^ n) 2 (apertureMeasure a) := by
  refine MemLp.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) (a ^ n) ?_
  rw [apertureMeasure]
  refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg x) (abs_le_of_mem_aperture hx) n

theorem memLp_cosh (a c : ℝ) :
    MemLp (fun x : ℝ => Real.cosh (c * x)) 2 (apertureMeasure a) := by
  refine MemLp.of_bound (Continuous.aestronglyMeasurable (by fun_prop))
    (Real.exp (|c| * |a|)) ?_
  rw [apertureMeasure]
  refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
  refine le_trans (cosh_le_exp_abs _) (Real.exp_le_exp.mpr ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (le_trans (abs_le_of_mem_aperture hx) (le_abs_self a)) (abs_nonneg c)

theorem memLp_sinh (a c : ℝ) :
    MemLp (fun x : ℝ => Real.sinh (c * x)) 2 (apertureMeasure a) := by
  refine MemLp.of_bound (Continuous.aestronglyMeasurable (by fun_prop))
    (Real.exp (|c| * |a|)) ?_
  rw [apertureMeasure]
  refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs]
  refine le_trans (abs_sinh_le_exp_abs _) (Real.exp_le_exp.mpr ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (le_trans (abs_le_of_mem_aperture hx) (le_abs_self a)) (abs_nonneg c)

/-- The monomial `x ↦ xⁿ` as an element of the aperture `L²`. -/
def monomialL2 (a : ℝ) (n : ℕ) : Lp ℝ 2 (apertureMeasure a) := (memLp_pow a n).toLp _

/-- The even hyperbolic profile as an element of the aperture `L²`. -/
def coshL2 (a c : ℝ) : Lp ℝ 2 (apertureMeasure a) := (memLp_cosh a c).toLp _

/-- The odd hyperbolic profile as an element of the aperture `L²`. -/
def sinhL2 (a c : ℝ) : Lp ℝ 2 (apertureMeasure a) := (memLp_sinh a c).toLp _

theorem coeFn_monomialL2 (a : ℝ) (n : ℕ) :
    (monomialL2 a n : ℝ → ℝ) =ᵐ[apertureMeasure a] fun x => x ^ n :=
  (memLp_pow a n).coeFn_toLp

theorem coeFn_coshL2 (a c : ℝ) :
    (coshL2 a c : ℝ → ℝ) =ᵐ[apertureMeasure a] fun x => Real.cosh (c * x) :=
  (memLp_cosh a c).coeFn_toLp

theorem coeFn_sinhL2 (a c : ℝ) :
    (sinhL2 a c : ℝ → ℝ) =ᵐ[apertureMeasure a] fun x => Real.sinh (c * x) :=
  (memLp_sinh a c).coeFn_toLp

theorem norm_monomialL2_le {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    ‖monomialL2 a n‖ ≤ Real.sqrt (2 * a) * a ^ n := by
  have hbd : ∀ᵐ x ∂(apertureMeasure a), ‖(monomialL2 a n : ℝ → ℝ) x‖ ≤ a ^ n := by
    filter_upwards [coeFn_monomialL2 a n,
      (ae_restrict_iff' (μ := volume) measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun x (hx : x ∈ Icc (-a) a) => hx)] with x hx hmem
    rw [hx, Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) (abs_le_of_mem_aperture hmem) n
  have h := Lp.norm_le_of_ae_bound (p := 2) (pow_nonneg ha n) hbd
  refine h.trans (le_of_eq ?_)
  rw [rpow_measureUnivNNReal_apertureMeasure ha]

/-! ## The `L²` Taylor expansion of the hyperbolic profiles -/

set_option maxHeartbeats 1000000 in
/-- **The even hyperbolic profile is the `L²` sum of its monomial series.** -/
theorem hasSum_coshL2 {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    HasSum (fun k : ℕ => (c ^ (2 * k) / (Nat.factorial (2 * k)) : ℝ) • monomialL2 a (2 * k))
      (coshL2 a c) := by
  set w : ℕ → Lp ℝ 2 (apertureMeasure a) :=
    fun k => (c ^ (2 * k) / (Nat.factorial (2 * k)) : ℝ) • monomialL2 a (2 * k) with hwdef
  set g : ℕ → ℝ := fun k => (|c| * a) ^ (2 * k) / (Nat.factorial (2 * k)) with hgdef
  have hgsum : Summable g := (Real.hasSum_cosh (|c| * a)).summable
  have hgnn : ∀ k, 0 ≤ g k := by
    intro k
    rw [hgdef]
    positivity
  -- the pointwise tail bound
  have hpoint : ∀ (s : Finset ℕ) (x : ℝ), x ∈ Icc (-a) a →
      |(∑ k ∈ s, (c ^ (2 * k) / (Nat.factorial (2 * k)) : ℝ) * x ^ (2 * k))
        - Real.cosh (c * x)| ≤ ∑' k : ↥((s : Set ℕ)ᶜ), g k := by
    intro s x hx
    set F : ℕ → ℝ := fun m => (c ^ (2 * m) / (Nat.factorial (2 * m)) : ℝ) * x ^ (2 * m)
      with hFdef
    have hsum' : HasSum F (Real.cosh (c * x)) := by
      refine (Real.hasSum_cosh (c * x)).congr_fun fun k => ?_
      rw [hFdef]
      simp only
      rw [mul_pow]
      ring
    have hsplit := hsum'.summable.sum_add_tsum_compl (s := s)
    rw [hsum'.tsum_eq] at hsplit
    have heq : (∑ k ∈ s, F k) - Real.cosh (c * x) = -(∑' k : ↥((s : Set ℕ)ᶜ), F k) := by
      linarith [hsplit]
    rw [heq, abs_neg]
    have hxa : |x| ≤ a := abs_le_of_mem_aperture hx
    have hdom : ∀ k : ↥((s : Set ℕ)ᶜ), ‖F k‖ ≤ g k := by
      intro k
      rw [hFdef, hgdef]
      simp only
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_pow,
        abs_of_pos (show (0:ℝ) < ((Nat.factorial (2 * (k : ℕ)) : ℕ) : ℝ) by positivity),
        mul_pow, div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) hxa _) (by positivity)
    have hFsub : Summable fun k : ↥((s : Set ℕ)ᶜ) => ‖F k‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hdom (hgsum.subtype _)
    exact le_trans (norm_tsum_le_tsum_norm hFsub)
      (Summable.tsum_le_tsum hdom hFsub (hgsum.subtype _))
  -- the `L²` bound on partial sums
  have hbound : ∀ s : Finset ℕ,
      ‖(∑ k ∈ s, w k) - coshL2 a c‖ ≤ Real.sqrt (2 * a) * (∑' k : ↥((s : Set ℕ)ᶜ), g k) := by
    intro s
    have hae : ∀ᵐ x ∂(apertureMeasure a),
        ‖(((∑ k ∈ s, w k) - coshL2 a c : Lp ℝ 2 (apertureMeasure a)) : ℝ → ℝ) x‖
          ≤ ∑' k : ↥((s : Set ℕ)ᶜ), g k := by
      filter_upwards [Lp.coeFn_sub (∑ k ∈ s, w k) (coshL2 a c),
        Lp.coeFn_finsetSum s w, coeFn_coshL2 a c,
        (Filter.eventually_all_finset s).mpr
          (fun k _ => by
            filter_upwards [Lp.coeFn_smul (c ^ (2 * k) / (Nat.factorial (2 * k)) : ℝ)
              (monomialL2 a (2 * k)), coeFn_monomialL2 a (2 * k)] with x hx1 hx2
            show (w k : ℝ → ℝ) x = (c ^ (2 * k) / (Nat.factorial (2 * k)) : ℝ) * x ^ (2 * k)
            rw [hwdef]
            simp only
            rw [hx1, Pi.smul_apply, hx2, smul_eq_mul]),
        (ae_restrict_iff' (μ := volume) measurableSet_Icc).mpr
          (Filter.Eventually.of_forall fun x (hx : x ∈ Icc (-a) a) => hx)]
        with x hsub hfs hcosh hterms hmem
      rw [hsub, Pi.sub_apply, hfs, hcosh, Finset.sum_apply, Real.norm_eq_abs,
        Finset.sum_congr rfl (fun k hk => hterms k hk)]
      exact hpoint s x hmem
    have hnn : (0 : ℝ) ≤ ∑' k : ↥((s : Set ℕ)ᶜ), g k :=
      tsum_nonneg fun k => hgnn _
    have h := Lp.norm_le_of_ae_bound (p := 2) hnn hae
    refine h.trans (le_of_eq ?_)
    rw [rpow_measureUnivNNReal_apertureMeasure ha]
  -- conclude
  rw [HasSum, SummationFilter.unconditional_filter, tendsto_iff_norm_sub_tendsto_zero]
  have htail : Tendsto (fun s : Finset ℕ => Real.sqrt (2 * a) * ∑' k : ↥((s : Set ℕ)ᶜ), g k)
      atTop (𝓝 0) := by
    have h := tendsto_tsum_compl_atTop_zero g
    have h2 := h.const_mul (Real.sqrt (2 * a))
    rw [mul_zero] at h2
    exact h2
  refine squeeze_zero (fun s => norm_nonneg _) hbound htail

set_option maxHeartbeats 1000000 in
/-- **The odd hyperbolic profile is the `L²` sum of its monomial series.** -/
theorem hasSum_sinhL2 {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    HasSum
      (fun k : ℕ => (c ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)) : ℝ)
        • monomialL2 a (2 * k + 1))
      (sinhL2 a c) := by
  set w : ℕ → Lp ℝ 2 (apertureMeasure a) :=
    fun k => (c ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)) : ℝ) • monomialL2 a (2 * k + 1)
    with hwdef
  set g : ℕ → ℝ := fun k => (|c| * a) ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)) with hgdef
  have hgsum : Summable g := (Real.hasSum_sinh (|c| * a)).summable
  have hanng : 0 ≤ |c| * a := mul_nonneg (abs_nonneg c) ha
  have hgnn : ∀ k, 0 ≤ g k := by
    intro k
    rw [hgdef]
    positivity
  have hpoint : ∀ (s : Finset ℕ) (x : ℝ), x ∈ Icc (-a) a →
      |(∑ k ∈ s, (c ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)) : ℝ) * x ^ (2 * k + 1))
        - Real.sinh (c * x)| ≤ ∑' k : ↥((s : Set ℕ)ᶜ), g k := by
    intro s x hx
    set F : ℕ → ℝ :=
      fun m => (c ^ (2 * m + 1) / (Nat.factorial (2 * m + 1)) : ℝ) * x ^ (2 * m + 1) with hFdef
    have hsum' : HasSum F (Real.sinh (c * x)) := by
      refine (Real.hasSum_sinh (c * x)).congr_fun fun k => ?_
      rw [hFdef]
      simp only
      rw [mul_pow]
      ring
    have hsplit := hsum'.summable.sum_add_tsum_compl (s := s)
    rw [hsum'.tsum_eq] at hsplit
    have heq : (∑ k ∈ s, F k) - Real.sinh (c * x) = -(∑' k : ↥((s : Set ℕ)ᶜ), F k) := by
      linarith [hsplit]
    rw [heq, abs_neg]
    have hxa : |x| ≤ a := abs_le_of_mem_aperture hx
    have hdom : ∀ k : ↥((s : Set ℕ)ᶜ), ‖F k‖ ≤ g k := by
      intro k
      rw [hFdef, hgdef]
      simp only
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_pow,
        abs_of_pos (show (0:ℝ) < ((Nat.factorial (2 * (k : ℕ) + 1) : ℕ) : ℝ) by positivity),
        mul_pow, div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) hxa _) (by positivity)
    have hFsub : Summable fun k : ↥((s : Set ℕ)ᶜ) => ‖F k‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hdom (hgsum.subtype _)
    exact le_trans (norm_tsum_le_tsum_norm hFsub)
      (Summable.tsum_le_tsum hdom hFsub (hgsum.subtype _))
  have hbound : ∀ s : Finset ℕ,
      ‖(∑ k ∈ s, w k) - sinhL2 a c‖ ≤ Real.sqrt (2 * a) * (∑' k : ↥((s : Set ℕ)ᶜ), g k) := by
    intro s
    have hae : ∀ᵐ x ∂(apertureMeasure a),
        ‖(((∑ k ∈ s, w k) - sinhL2 a c : Lp ℝ 2 (apertureMeasure a)) : ℝ → ℝ) x‖
          ≤ ∑' k : ↥((s : Set ℕ)ᶜ), g k := by
      filter_upwards [Lp.coeFn_sub (∑ k ∈ s, w k) (sinhL2 a c),
        Lp.coeFn_finsetSum s w, coeFn_sinhL2 a c,
        (Filter.eventually_all_finset s).mpr
          (fun k _ => by
            filter_upwards [Lp.coeFn_smul (c ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)) : ℝ)
              (monomialL2 a (2 * k + 1)), coeFn_monomialL2 a (2 * k + 1)] with x hx1 hx2
            show (w k : ℝ → ℝ) x
              = (c ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)) : ℝ) * x ^ (2 * k + 1)
            rw [hwdef]
            simp only
            rw [hx1, Pi.smul_apply, hx2, smul_eq_mul]),
        (ae_restrict_iff' (μ := volume) measurableSet_Icc).mpr
          (Filter.Eventually.of_forall fun x (hx : x ∈ Icc (-a) a) => hx)]
        with x hsub hfs hsinh hterms hmem
      rw [hsub, Pi.sub_apply, hfs, hsinh, Finset.sum_apply, Real.norm_eq_abs,
        Finset.sum_congr rfl (fun k hk => hterms k hk)]
      exact hpoint s x hmem
    have hnn : (0 : ℝ) ≤ ∑' k : ↥((s : Set ℕ)ᶜ), g k := tsum_nonneg fun k => hgnn _
    have h := Lp.norm_le_of_ae_bound (p := 2) hnn hae
    refine h.trans (le_of_eq ?_)
    rw [rpow_measureUnivNNReal_apertureMeasure ha]
  rw [HasSum, SummationFilter.unconditional_filter, tendsto_iff_norm_sub_tendsto_zero]
  have htail : Tendsto (fun s : Finset ℕ => Real.sqrt (2 * a) * ∑' k : ↥((s : Set ℕ)ᶜ), g k)
      atTop (𝓝 0) := by
    have h := tendsto_tsum_compl_atTop_zero g
    have h2 := h.const_mul (Real.sqrt (2 * a))
    rw [mul_zero] at h2
    exact h2
  refine squeeze_zero (fun s => norm_nonneg _) hbound htail

/-! ## Parity energies of a bounded observable -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `k`-th even moment of a bounded observable on the aperture. -/
def evenMomentVector (a : ℝ) (P : Lp ℝ 2 (apertureMeasure a) →L[ℝ] E) (k : ℕ) : E :=
  ((Nat.factorial (2 * k) : ℝ))⁻¹ • P (monomialL2 a (2 * k))

/-- The `k`-th odd moment of a bounded observable on the aperture. -/
def oddMomentVector (a : ℝ) (P : Lp ℝ 2 (apertureMeasure a) →L[ℝ] E) (k : ℕ) : E :=
  ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ • P (monomialL2 a (2 * k + 1))

set_option maxHeartbeats 1000000 in
theorem summable_norm_evenMomentVector {a : ℝ} (ha : 0 ≤ a)
    (P : Lp ℝ 2 (apertureMeasure a) →L[ℝ] E) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun k : ℕ => ‖evenMomentVector a P k‖ * R ^ k := by
  set M : ℝ := ‖P‖ * Real.sqrt (2 * a) with hMdef
  have hM : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  set b : ℝ := Real.sqrt (a ^ 2 * R) with hbdef
  have hmaj : Summable fun k : ℕ => M * (b ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) :=
    ((Real.hasSum_cosh b).summable).mul_left M
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hmaj
  have hnormP : ‖P (monomialL2 a (2 * k))‖ ≤ ‖P‖ * ‖monomialL2 a (2 * k)‖ := P.le_opNorm _
  have hmon : ‖monomialL2 a (2 * k)‖ ≤ Real.sqrt (2 * a) * a ^ (2 * k) :=
    norm_monomialL2_le ha (2 * k)
  have hchain : ‖P (monomialL2 a (2 * k))‖ ≤ M * a ^ (2 * k) := by
    refine hnormP.trans ?_
    rw [hMdef, mul_assoc]
    exact mul_le_mul_of_nonneg_left hmon (norm_nonneg _)
  have hfac : (0 : ℝ) < ((Nat.factorial (2 * k) : ℕ) : ℝ) := by positivity
  have hev : ‖evenMomentVector a P k‖
      = ((Nat.factorial (2 * k) : ℝ))⁻¹ * ‖P (monomialL2 a (2 * k))‖ := by
    rw [evenMomentVector, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hbpow : b ^ (2 * k) = a ^ (2 * k) * R ^ k := by
    rw [hbdef, ← Real.sqrt_eq_rpow] at *
    rw [pow_mul, Real.sq_sqrt (by positivity), mul_pow, ← pow_mul, mul_comm 2 k, pow_mul]
  rw [hev, hbpow]
  have hstep : ((Nat.factorial (2 * k) : ℝ))⁻¹ * ‖P (monomialL2 a (2 * k))‖ * R ^ k
      ≤ ((Nat.factorial (2 * k) : ℝ))⁻¹ * (M * a ^ (2 * k)) * R ^ k := by
    have := mul_le_mul_of_nonneg_left hchain (le_of_lt (inv_pos.mpr hfac))
    exact mul_le_mul_of_nonneg_right this (by positivity)
  refine hstep.trans (le_of_eq ?_)
  field_simp
  ring

theorem summable_norm_oddMomentVector {a : ℝ} (ha : 0 ≤ a)
    (P : Lp ℝ 2 (apertureMeasure a) →L[ℝ] E) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun k : ℕ => ‖oddMomentVector a P k‖ * R ^ k := by
  set M : ℝ := ‖P‖ * Real.sqrt (2 * a) * (1 + a) with hMdef
  have hM : 0 ≤ M := by
    rw [hMdef]
    have : (0 : ℝ) ≤ ‖P‖ * Real.sqrt (2 * a) :=
      mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    positivity
  set b : ℝ := Real.sqrt (a ^ 2 * R) with hbdef
  have hmaj : Summable fun k : ℕ => M * (b ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) :=
    ((Real.hasSum_cosh b).summable).mul_left M
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hmaj
  have hnormP : ‖P (monomialL2 a (2 * k + 1))‖ ≤ ‖P‖ * ‖monomialL2 a (2 * k + 1)‖ :=
    P.le_opNorm _
  have hmon : ‖monomialL2 a (2 * k + 1)‖ ≤ Real.sqrt (2 * a) * a ^ (2 * k + 1) :=
    norm_monomialL2_le ha (2 * k + 1)
  have hchain : ‖P (monomialL2 a (2 * k + 1))‖ ≤ ‖P‖ * Real.sqrt (2 * a) * a ^ (2 * k + 1) := by
    refine hnormP.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmon (norm_nonneg _)
  have hfacpos : (0 : ℝ) < ((Nat.factorial (2 * k + 1) : ℕ) : ℝ) := by positivity
  have hfacmono : ((Nat.factorial (2 * k) : ℕ) : ℝ) ≤ ((Nat.factorial (2 * k + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ _)
  have hodd : ‖oddMomentVector a P k‖
      = ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ * ‖P (monomialL2 a (2 * k + 1))‖ := by
    rw [oddMomentVector, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hbpow : b ^ (2 * k) = a ^ (2 * k) * R ^ k := by
    rw [hbdef]
    rw [pow_mul, Real.sq_sqrt (by positivity), mul_pow, ← pow_mul, mul_comm 2 k, pow_mul]
  rw [hodd, hbpow]
  have hpowsucc : a ^ (2 * k + 1) ≤ (1 + a) * a ^ (2 * k) := by
    rw [pow_succ]
    nlinarith [pow_nonneg ha (2 * k)]
  have hstep : ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ * ‖P (monomialL2 a (2 * k + 1))‖ * R ^ k
      ≤ ((Nat.factorial (2 * k) : ℝ))⁻¹ * (M * a ^ (2 * k)) * R ^ k := by
    have h1 : ‖P (monomialL2 a (2 * k + 1))‖ ≤ M * a ^ (2 * k) := by
      refine hchain.trans ?_
      rw [hMdef]
      have hPa : (0 : ℝ) ≤ ‖P‖ * Real.sqrt (2 * a) :=
        mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
      calc ‖P‖ * Real.sqrt (2 * a) * a ^ (2 * k + 1)
          ≤ ‖P‖ * Real.sqrt (2 * a) * ((1 + a) * a ^ (2 * k)) :=
            mul_le_mul_of_nonneg_left hpowsucc hPa
        _ = ‖P‖ * Real.sqrt (2 * a) * (1 + a) * a ^ (2 * k) := by ring
    have h2 : ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ ≤ ((Nat.factorial (2 * k) : ℝ))⁻¹ := by
      have hpos : (0 : ℝ) < ((Nat.factorial (2 * k) : ℕ) : ℝ) := by positivity
      exact one_div_le_one_div_of_le hpos hfacmono |>.trans_eq (by rw [one_div])
        |>.trans_eq' (by rw [one_div])
    have hnn : (0 : ℝ) ≤ ‖P (monomialL2 a (2 * k + 1))‖ := norm_nonneg _
    have : ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ * ‖P (monomialL2 a (2 * k + 1))‖
        ≤ ((Nat.factorial (2 * k) : ℝ))⁻¹ * (M * a ^ (2 * k)) := by
      calc ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ * ‖P (monomialL2 a (2 * k + 1))‖
          ≤ ((Nat.factorial (2 * k) : ℝ))⁻¹ * ‖P (monomialL2 a (2 * k + 1))‖ :=
            mul_le_mul_of_nonneg_right h2 hnn
        _ ≤ ((Nat.factorial (2 * k) : ℝ))⁻¹ * (M * a ^ (2 * k)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  refine hstep.trans (le_of_eq ?_)
  field_simp
  ring

set_option maxHeartbeats 1000000 in
theorem hasSum_evenMomentVector {a : ℝ} (ha : 0 ≤ a)
    (P : Lp ℝ 2 (apertureMeasure a) →L[ℝ] E) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun k : ℕ => t ^ k • evenMomentVector a P k) (P (coshL2 a (Real.sqrt t))) := by
  have hbase := (hasSum_coshL2 ha (Real.sqrt t)).mapL P
  refine hbase.congr_fun fun k => ?_
  rw [ContinuousLinearMap.map_smul, evenMomentVector, smul_smul, smul_smul]
  congr 1
  rw [pow_mul, Real.sq_sqrt ht]
  field_simp

set_option maxHeartbeats 1000000 in
theorem hasSum_oddMomentVector {a : ℝ} (ha : 0 ≤ a)
    (P : Lp ℝ 2 (apertureMeasure a) →L[ℝ] E) {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => t ^ k • oddMomentVector a P k)
      ((Real.sqrt t)⁻¹ • P (sinhL2 a (Real.sqrt t))) := by
  have hbase := ((hasSum_sinhL2 ha (Real.sqrt t)).mapL P).const_smul ((Real.sqrt t)⁻¹)
  have hsq : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  refine hbase.congr_fun fun k => ?_
  rw [ContinuousLinearMap.map_smul, oddMomentVector, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [pow_succ, pow_mul, Real.sq_sqrt ht.le]
  field_simp

set_option maxHeartbeats 1000000 in
/-- **`(5)`, even half.**  The even parity energy of a bounded observable has the exact rate of its
first visible even moment. -/
theorem tendsto_evenParityEnergy_rate {a : ℝ} (ha : 0 < a)
    (P : Lp ℝ 2 (apertureMeasure a) →L[ℝ] E) {j : ℕ}
    (hzero : ∀ k, k < j → evenMomentVector a P k = 0) :
    Tendsto (fun c : ℝ => ‖P (coshL2 a c)‖ ^ 2 / c ^ (4 * j)) (𝓝[>] (0 : ℝ))
      (𝓝 (‖evenMomentVector a P j‖ ^ 2)) := by
  have hbase := tendsto_normSq_div_pow_even (E := E) (u := evenMomentVector a P) (R := 1)
    (by norm_num) (summable_norm_evenMomentVector ha.le P (by norm_num)) hzero
    (fun t htpos _ => hasSum_evenMomentVector ha.le P htpos.le)
  refine hbase.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hcpos : (0 : ℝ) < c := Set.mem_Ioi.mp hc
  rw [Real.sqrt_sq hcpos.le]

set_option maxHeartbeats 1000000 in
/-- **`(5)`, odd half.**  The odd parity energy of a bounded observable has the exact rate of its
first visible odd moment. -/
theorem tendsto_oddParityEnergy_rate {a : ℝ} (ha : 0 < a)
    (P : Lp ℝ 2 (apertureMeasure a) →L[ℝ] E) {j : ℕ}
    (hzero : ∀ k, k < j → oddMomentVector a P k = 0) :
    Tendsto (fun c : ℝ => ‖P (sinhL2 a c)‖ ^ 2 / c ^ (4 * j + 2)) (𝓝[>] (0 : ℝ))
      (𝓝 (‖oddMomentVector a P j‖ ^ 2)) := by
  have hbase := tendsto_normSq_div_pow_even (E := E) (u := oddMomentVector a P) (R := 1)
    (by norm_num) (summable_norm_oddMomentVector ha.le P (by norm_num)) hzero
    (fun t htpos _ => hasSum_oddMomentVector ha.le P htpos)
  refine hbase.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hcpos : (0 : ℝ) < c := Set.mem_Ioi.mp hc
  rw [Real.sqrt_sq hcpos.le, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hcpos), mul_pow]
  rw [show (4 * j + 2) = (4 * j) + 2 by ring, pow_add]
  field_simp
  ring

end GaloisForLFunctions.HTGeometry

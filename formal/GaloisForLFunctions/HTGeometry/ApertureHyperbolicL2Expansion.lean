import GaloisForLFunctions.HTGeometry.VectorPowerSeriesLeadingOrder
import GaloisForLFunctions.HTGeometry.ApertureFourierPairing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Function.LpSpace.Basic
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

/-! ## The aperture window constant -/

theorem apertureMeasure_univ_toReal {a : ℝ} (ha : 0 ≤ a) :
    (apertureMeasure a Set.univ).toReal = 2 * a := by
  rw [apertureMeasure, Measure.restrict_apply_univ, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith)]
  ring

theorem apertureWindow_eq_sqrt {a : ℝ} (ha : 0 ≤ a) :
    apertureWindow a = Real.sqrt (2 * a) := by
  have hcoe : ((measureUnivNNReal (apertureMeasure a) : ℝ≥0) : ℝ) = 2 * a := by
    rw [← apertureMeasure_univ_toReal ha]
    rfl
  rw [apertureWindow, hcoe, show ((2 : ℝ))⁻¹ = (1 : ℝ) / 2 by norm_num, ← Real.sqrt_eq_rpow]

theorem rpow_measureUnivNNReal_apertureMeasure {a : ℝ} (ha : 0 ≤ a) :
    ((measureUnivNNReal (apertureMeasure a) : ℝ≥0) : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹
      = Real.sqrt (2 * a) := by
  rw [← apertureWindow_eq_sqrt ha, apertureWindow]
  norm_num

/-! ## The `L²` classes -/

theorem memLp_aperturePow (a : ℝ) (n : ℕ) : MemLp (fun x : ℝ => x ^ n) 2 (apertureMeasure a) := by
  refine MemLp.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) (a ^ n) ?_
  rw [apertureMeasure]
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg x) (abs_le_of_mem_aperture hx) n

theorem memLp_apertureCosh (a c : ℝ) :
    MemLp (fun x : ℝ => Real.cosh (c * x)) 2 (apertureMeasure a) := by
  refine MemLp.of_bound (Continuous.aestronglyMeasurable (by fun_prop))
    (Real.exp (|c| * |a|)) ?_
  rw [apertureMeasure]
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
  have hcosh : Real.cosh (c * x) ≤ Real.exp |c * x| := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (c * x) ≤ Real.exp |c * x| := Real.exp_le_exp.mpr (le_abs_self _)
    have h2 : Real.exp (-(c * x)) ≤ Real.exp |c * x| := Real.exp_le_exp.mpr (neg_le_abs _)
    linarith
  refine le_trans hcosh (Real.exp_le_exp.mpr ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (le_trans (abs_le_of_mem_aperture hx) (le_abs_self a)) (abs_nonneg c)

theorem memLp_apertureSinh (a c : ℝ) :
    MemLp (fun x : ℝ => Real.sinh (c * x)) 2 (apertureMeasure a) := by
  refine MemLp.of_bound (Continuous.aestronglyMeasurable (by fun_prop))
    (Real.exp (|c| * |a|)) ?_
  rw [apertureMeasure]
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs]
  have hsinh : |Real.sinh (c * x)| ≤ Real.exp |c * x| := by
    rw [Real.sinh_eq, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2),
      div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    have h1 : Real.exp (c * x) ≤ Real.exp |c * x| := Real.exp_le_exp.mpr (le_abs_self _)
    have h2 : Real.exp (-(c * x)) ≤ Real.exp |c * x| := Real.exp_le_exp.mpr (neg_le_abs _)
    have h1' : (0:ℝ) < Real.exp (c * x) := Real.exp_pos _
    have h2' : (0:ℝ) < Real.exp (-(c * x)) := Real.exp_pos _
    rcases abs_cases (Real.exp (c * x) - Real.exp (-(c * x))) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] <;> linarith
  refine le_trans hsinh (Real.exp_le_exp.mpr ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (le_trans (abs_le_of_mem_aperture hx) (le_abs_self a)) (abs_nonneg c)

/-- The monomial `x ↦ xⁿ` as an element of the aperture `L²`. -/
def apertureMonomialL2 (a : ℝ) (n : ℕ) : Lp ℝ 2 (apertureMeasure a) := (memLp_aperturePow a n).toLp _

/-- The even hyperbolic profile as an element of the aperture `L²`. -/
def apertureCoshL2 (a c : ℝ) : Lp ℝ 2 (apertureMeasure a) := (memLp_apertureCosh a c).toLp _

/-- The odd hyperbolic profile as an element of the aperture `L²`. -/
def apertureSinhL2 (a c : ℝ) : Lp ℝ 2 (apertureMeasure a) := (memLp_apertureSinh a c).toLp _

theorem coeFn_apertureMonomialL2 (a : ℝ) (n : ℕ) :
    (apertureMonomialL2 a n : ℝ → ℝ) =ᵐ[apertureMeasure a] fun x => x ^ n :=
  (memLp_aperturePow a n).coeFn_toLp

theorem coeFn_apertureCoshL2 (a c : ℝ) :
    (apertureCoshL2 a c : ℝ → ℝ) =ᵐ[apertureMeasure a] fun x => Real.cosh (c * x) :=
  (memLp_apertureCosh a c).coeFn_toLp

theorem coeFn_apertureSinhL2 (a c : ℝ) :
    (apertureSinhL2 a c : ℝ → ℝ) =ᵐ[apertureMeasure a] fun x => Real.sinh (c * x) :=
  (memLp_apertureSinh a c).coeFn_toLp

theorem norm_apertureMonomialL2_le {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    ‖apertureMonomialL2 a n‖ ≤ Real.sqrt (2 * a) * a ^ n := by
  have hbd : ∀ᵐ x ∂(apertureMeasure a), ‖(apertureMonomialL2 a n : ℝ → ℝ) x‖ ≤ a ^ n := by
    filter_upwards [coeFn_apertureMonomialL2 a n,
      apertureMeasure_ae_mem a] with x hx hmem
    rw [hx, Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) (abs_le_of_mem_aperture hmem) n
  have h := Lp.norm_le_of_ae_bound (p := 2) (pow_nonneg ha n) hbd
  refine h.trans (le_of_eq ?_)
  rw [rpow_measureUnivNNReal_apertureMeasure ha]

/-! ## Series of `L²` classes on the aperture -/

set_option maxHeartbeats 1000000 in
/-- **A uniformly dominated pointwise series of aperture functions sums in `L²`.**  A finite measure
turns a uniform tail bound into an `L²` tail bound, so the `Finset` net of partial sums converges. -/
theorem hasSum_apertureToLp {a : ℝ} (ha : 0 ≤ a) {𝕜 : Type*} [RCLike 𝕜]
    {f : ℕ → ℝ → 𝕜} {F : ℝ → 𝕜} {g : ℕ → ℝ}
    (hgsum : Summable g) (hgnn : ∀ n, 0 ≤ g n)
    (hbd : ∀ (n : ℕ) (x : ℝ), x ∈ Set.Ioo (-a) a → ‖f n x‖ ≤ g n)
    (hpt : ∀ x : ℝ, x ∈ Set.Ioo (-a) a → HasSum (fun n => f n x) (F x))
    (hmem : ∀ n, MemLp (f n) 2 (apertureMeasure a))
    (hMem : MemLp F 2 (apertureMeasure a)) :
    HasSum (fun n => (hmem n).toLp (f n)) (hMem.toLp F) := by
  have hpoint : ∀ (s : Finset ℕ) (x : ℝ), x ∈ Set.Ioo (-a) a →
      ‖(∑ n ∈ s, f n x) - F x‖ ≤ ∑' n : ↥((s : Set ℕ)ᶜ), g n := by
    intro s x hx
    have hsplit := (hpt x hx).summable.sum_add_tsum_compl (s := s)
    rw [(hpt x hx).tsum_eq] at hsplit
    have heq : (∑ n ∈ s, f n x) - F x = -(∑' n : ↥((s : Set ℕ)ᶜ), f n x) := by
      rw [← hsplit]
      ring
    rw [heq, norm_neg]
    have hdom : ∀ n : ↥((s : Set ℕ)ᶜ), ‖f n x‖ ≤ g n := fun n => hbd n x hx
    have hFsub : Summable fun n : ↥((s : Set ℕ)ᶜ) => ‖f n x‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hdom (hgsum.subtype _)
    exact le_trans (norm_tsum_le_tsum_norm hFsub)
      (Summable.tsum_le_tsum hdom hFsub (hgsum.subtype _))
  have hbound : ∀ s : Finset ℕ,
      ‖(∑ n ∈ s, (hmem n).toLp (f n)) - hMem.toLp F‖
        ≤ Real.sqrt (2 * a) * (∑' n : ↥((s : Set ℕ)ᶜ), g n) := by
    intro s
    have hae : ∀ᵐ x ∂(apertureMeasure a),
        ‖((((∑ n ∈ s, (hmem n).toLp (f n)) - hMem.toLp F) : Lp 𝕜 2 (apertureMeasure a))
            : ℝ → 𝕜) x‖ ≤ ∑' n : ↥((s : Set ℕ)ᶜ), g n := by
      filter_upwards [Lp.coeFn_sub (∑ n ∈ s, (hmem n).toLp (f n)) (hMem.toLp F),
        Lp.coeFn_finsetSum s (fun n => (hmem n).toLp (f n)), hMem.coeFn_toLp,
        (Filter.eventually_all_finset s).mpr (fun n _ => (hmem n).coeFn_toLp),
        apertureMeasure_ae_mem a] with x hsub hfs hF hterms hx
      rw [hsub, Pi.sub_apply, hfs, hF, Finset.sum_apply,
        Finset.sum_congr rfl (fun n hn => hterms n hn)]
      exact hpoint s x hx
    have hnn : (0 : ℝ) ≤ ∑' n : ↥((s : Set ℕ)ᶜ), g n := tsum_nonneg fun n => hgnn _
    have h := Lp.norm_le_of_ae_bound (p := 2) hnn hae
    refine h.trans (le_of_eq ?_)
    rw [rpow_measureUnivNNReal_apertureMeasure ha]
  rw [HasSum, SummationFilter.unconditional_filter, tendsto_iff_norm_sub_tendsto_zero]
  have htail : Tendsto (fun s : Finset ℕ => Real.sqrt (2 * a) * ∑' n : ↥((s : Set ℕ)ᶜ), g n)
      atTop (𝓝 0) := by
    have h := tendsto_tsum_compl_atTop_zero g
    have h2 := h.const_mul (Real.sqrt (2 * a))
    rw [mul_zero] at h2
    exact h2
  exact squeeze_zero (fun s => norm_nonneg _) hbound htail

/-! ## The `L²` Taylor expansion of the hyperbolic profiles -/

set_option maxHeartbeats 1000000 in
/-- **The even hyperbolic profile is the `L²` sum of its monomial series.** -/
theorem hasSum_apertureCoshL2 {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    HasSum (fun k : ℕ => (c ^ (2 * k) / (Nat.factorial (2 * k)) : ℝ) • apertureMonomialL2 a (2 * k))
      (apertureCoshL2 a c) := by
  have hmem : ∀ k : ℕ, MemLp
      (fun x : ℝ => (c ^ (2 * k) / (Nat.factorial (2 * k)) : ℝ) * x ^ (2 * k)) 2
      (apertureMeasure a) := fun k => (memLp_aperturePow a (2 * k)).const_mul _
  have hbase := hasSum_apertureToLp (𝕜 := ℝ) ha
    (f := fun k x => (c ^ (2 * k) / (Nat.factorial (2 * k)) : ℝ) * x ^ (2 * k))
    (F := fun x => Real.cosh (c * x))
    (g := fun k => (|c| * a) ^ (2 * k) / (Nat.factorial (2 * k)))
    ((Real.hasSum_cosh (|c| * a)).summable) (fun k => by positivity)
    (fun k x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_pow,
        abs_of_pos (show (0 : ℝ) < ((Nat.factorial (2 * k) : ℕ) : ℝ) by positivity),
        mul_pow, div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg x) (abs_le_of_mem_aperture hx) _) (by positivity))
    (fun x _ => by
      refine (Real.hasSum_cosh (c * x)).congr_fun fun k => ?_
      rw [mul_pow]
      ring)
    hmem (memLp_apertureCosh a c)
  refine hbase.congr_fun fun k => ?_
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul (c ^ (2 * k) / (Nat.factorial (2 * k)) : ℝ)
    (apertureMonomialL2 a (2 * k)), coeFn_apertureMonomialL2 a (2 * k),
    (hmem k).coeFn_toLp] with x hx1 hx2 hx3
  rw [hx3, hx1, Pi.smul_apply, hx2, smul_eq_mul]

set_option maxHeartbeats 1000000 in
/-- **The odd hyperbolic profile is the `L²` sum of its monomial series.** -/
theorem hasSum_apertureSinhL2 {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    HasSum
      (fun k : ℕ => (c ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)) : ℝ)
        • apertureMonomialL2 a (2 * k + 1))
      (apertureSinhL2 a c) := by
  have hmem : ∀ k : ℕ, MemLp
      (fun x : ℝ => (c ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)) : ℝ) * x ^ (2 * k + 1)) 2
      (apertureMeasure a) := fun k => (memLp_aperturePow a (2 * k + 1)).const_mul _
  have hbase := hasSum_apertureToLp (𝕜 := ℝ) ha
    (f := fun k x => (c ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)) : ℝ) * x ^ (2 * k + 1))
    (F := fun x => Real.sinh (c * x))
    (g := fun k => (|c| * a) ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)))
    ((Real.hasSum_sinh (|c| * a)).summable) (fun k => by positivity)
    (fun k x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_pow,
        abs_of_pos (show (0 : ℝ) < ((Nat.factorial (2 * k + 1) : ℕ) : ℝ) by positivity),
        mul_pow, div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg x) (abs_le_of_mem_aperture hx) _) (by positivity))
    (fun x _ => by
      refine (Real.hasSum_sinh (c * x)).congr_fun fun k => ?_
      rw [mul_pow]
      ring)
    hmem (memLp_apertureSinh a c)
  refine hbase.congr_fun fun k => ?_
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul (c ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)) : ℝ)
    (apertureMonomialL2 a (2 * k + 1)), coeFn_apertureMonomialL2 a (2 * k + 1),
    (hmem k).coeFn_toLp] with x hx1 hx2 hx3
  rw [hx3, hx1, Pi.smul_apply, hx2, smul_eq_mul]

/-! ## Parity energies of a bounded observable -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `k`-th even moment of a bounded observable on the aperture. -/
def evenMomentVector (a : ℝ) (P : Lp ℝ 2 (apertureMeasure a) →L[ℝ] E) (k : ℕ) : E :=
  ((Nat.factorial (2 * k) : ℝ))⁻¹ • P (apertureMonomialL2 a (2 * k))

/-- The `k`-th odd moment of a bounded observable on the aperture. -/
def oddMomentVector (a : ℝ) (P : Lp ℝ 2 (apertureMeasure a) →L[ℝ] E) (k : ℕ) : E :=
  ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ • P (apertureMonomialL2 a (2 * k + 1))

set_option maxHeartbeats 1000000 in
theorem summable_norm_evenMomentVector {a : ℝ} (ha : 0 ≤ a)
    (P : Lp ℝ 2 (apertureMeasure a) →L[ℝ] E) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun k : ℕ => ‖evenMomentVector a P k‖ * R ^ k := by
  set M : ℝ := ‖P‖ * Real.sqrt (2 * a) with hMdef
  have hM : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hmaj : Summable fun k : ℕ =>
      M * (Real.sqrt (a ^ 2 * R) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) :=
    ((Real.hasSum_cosh (Real.sqrt (a ^ 2 * R))).summable).mul_left M
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hmaj
  have hnormP : ‖P (apertureMonomialL2 a (2 * k))‖ ≤ ‖P‖ * ‖apertureMonomialL2 a (2 * k)‖ := P.le_opNorm _
  have hmon : ‖apertureMonomialL2 a (2 * k)‖ ≤ Real.sqrt (2 * a) * a ^ (2 * k) :=
    norm_apertureMonomialL2_le ha (2 * k)
  have hchain : ‖P (apertureMonomialL2 a (2 * k))‖ ≤ M * a ^ (2 * k) := by
    refine hnormP.trans ?_
    rw [hMdef, mul_assoc]
    exact mul_le_mul_of_nonneg_left hmon (norm_nonneg _)
  have hfac : (0 : ℝ) < ((Nat.factorial (2 * k) : ℕ) : ℝ) := by positivity
  have hev : ‖evenMomentVector a P k‖
      = ((Nat.factorial (2 * k) : ℝ))⁻¹ * ‖P (apertureMonomialL2 a (2 * k))‖ := by
    rw [evenMomentVector, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hbpow : Real.sqrt (a ^ 2 * R) ^ (2 * k) = a ^ (2 * k) * R ^ k := by
    rw [pow_mul, Real.sq_sqrt (by positivity), mul_pow, ← pow_mul]
  rw [hev, hbpow]
  have hstep : ((Nat.factorial (2 * k) : ℝ))⁻¹ * ‖P (apertureMonomialL2 a (2 * k))‖ * R ^ k
      ≤ ((Nat.factorial (2 * k) : ℝ))⁻¹ * (M * a ^ (2 * k)) * R ^ k := by
    have := mul_le_mul_of_nonneg_left hchain (le_of_lt (inv_pos.mpr hfac))
    exact mul_le_mul_of_nonneg_right this (by positivity)
  refine hstep.trans (le_of_eq ?_)
  field_simp

theorem summable_norm_oddMomentVector {a : ℝ} (ha : 0 ≤ a)
    (P : Lp ℝ 2 (apertureMeasure a) →L[ℝ] E) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun k : ℕ => ‖oddMomentVector a P k‖ * R ^ k := by
  set M : ℝ := ‖P‖ * Real.sqrt (2 * a) * (1 + a) with hMdef
  have hM : 0 ≤ M := by
    rw [hMdef]
    have : (0 : ℝ) ≤ ‖P‖ * Real.sqrt (2 * a) :=
      mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    positivity
  have hmaj : Summable fun k : ℕ =>
      M * (Real.sqrt (a ^ 2 * R) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) :=
    ((Real.hasSum_cosh (Real.sqrt (a ^ 2 * R))).summable).mul_left M
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hmaj
  have hnormP : ‖P (apertureMonomialL2 a (2 * k + 1))‖ ≤ ‖P‖ * ‖apertureMonomialL2 a (2 * k + 1)‖ :=
    P.le_opNorm _
  have hmon : ‖apertureMonomialL2 a (2 * k + 1)‖ ≤ Real.sqrt (2 * a) * a ^ (2 * k + 1) :=
    norm_apertureMonomialL2_le ha (2 * k + 1)
  have hchain : ‖P (apertureMonomialL2 a (2 * k + 1))‖ ≤ ‖P‖ * Real.sqrt (2 * a) * a ^ (2 * k + 1) := by
    refine hnormP.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmon (norm_nonneg _)
  have hfacpos : (0 : ℝ) < ((Nat.factorial (2 * k + 1) : ℕ) : ℝ) := by positivity
  have hfacmono : ((Nat.factorial (2 * k) : ℕ) : ℝ) ≤ ((Nat.factorial (2 * k + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ _)
  have hodd : ‖oddMomentVector a P k‖
      = ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ * ‖P (apertureMonomialL2 a (2 * k + 1))‖ := by
    rw [oddMomentVector, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hbpow : Real.sqrt (a ^ 2 * R) ^ (2 * k) = a ^ (2 * k) * R ^ k := by
    rw [pow_mul, Real.sq_sqrt (by positivity), mul_pow, ← pow_mul]
  rw [hodd, hbpow]
  have hpowsucc : a ^ (2 * k + 1) ≤ (1 + a) * a ^ (2 * k) := by
    rw [pow_succ]
    nlinarith [pow_nonneg ha (2 * k)]
  have hstep : ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ * ‖P (apertureMonomialL2 a (2 * k + 1))‖ * R ^ k
      ≤ ((Nat.factorial (2 * k) : ℝ))⁻¹ * (M * a ^ (2 * k)) * R ^ k := by
    have h1 : ‖P (apertureMonomialL2 a (2 * k + 1))‖ ≤ M * a ^ (2 * k) := by
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
    have hnn : (0 : ℝ) ≤ ‖P (apertureMonomialL2 a (2 * k + 1))‖ := norm_nonneg _
    have : ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ * ‖P (apertureMonomialL2 a (2 * k + 1))‖
        ≤ ((Nat.factorial (2 * k) : ℝ))⁻¹ * (M * a ^ (2 * k)) := by
      calc ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ * ‖P (apertureMonomialL2 a (2 * k + 1))‖
          ≤ ((Nat.factorial (2 * k) : ℝ))⁻¹ * ‖P (apertureMonomialL2 a (2 * k + 1))‖ :=
            mul_le_mul_of_nonneg_right h2 hnn
        _ ≤ ((Nat.factorial (2 * k) : ℝ))⁻¹ * (M * a ^ (2 * k)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  refine hstep.trans (le_of_eq ?_)
  field_simp

set_option maxHeartbeats 1000000 in
theorem hasSum_evenMomentVector {a : ℝ} (ha : 0 ≤ a)
    (P : Lp ℝ 2 (apertureMeasure a) →L[ℝ] E) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun k : ℕ => t ^ k • evenMomentVector a P k) (P (apertureCoshL2 a (Real.sqrt t))) := by
  have hbase := (hasSum_apertureCoshL2 ha (Real.sqrt t)).mapL P
  refine hbase.congr_fun fun k => ?_
  rw [ContinuousLinearMap.map_smul, evenMomentVector, smul_smul]
  congr 1
  rw [pow_mul, Real.sq_sqrt ht, div_eq_mul_inv]

set_option maxHeartbeats 1000000 in
theorem hasSum_oddMomentVector {a : ℝ} (ha : 0 ≤ a)
    (P : Lp ℝ 2 (apertureMeasure a) →L[ℝ] E) {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => t ^ k • oddMomentVector a P k)
      ((Real.sqrt t)⁻¹ • P (apertureSinhL2 a (Real.sqrt t))) := by
  have hbase := ((hasSum_apertureSinhL2 ha (Real.sqrt t)).mapL P).const_smul ((Real.sqrt t)⁻¹)
  have hsq : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  refine hbase.congr_fun fun k => ?_
  rw [ContinuousLinearMap.map_smul, oddMomentVector, smul_smul, smul_smul]
  congr 1
  rw [pow_succ, pow_mul, Real.sq_sqrt ht.le]
  field_simp

set_option maxHeartbeats 1000000 in
/-- **`(5)`, even half.**  The even parity energy of a bounded observable has the exact rate of its
first visible even moment. -/
theorem tendsto_evenParityEnergy_rate {a : ℝ} (ha : 0 < a)
    (P : Lp ℝ 2 (apertureMeasure a) →L[ℝ] E) {j : ℕ}
    (hzero : ∀ k, k < j → evenMomentVector a P k = 0) :
    Tendsto (fun c : ℝ => ‖P (apertureCoshL2 a c)‖ ^ 2 / c ^ (4 * j)) (𝓝[>] (0 : ℝ))
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
    Tendsto (fun c : ℝ => ‖P (apertureSinhL2 a c)‖ ^ 2 / c ^ (4 * j + 2)) (𝓝[>] (0 : ℝ))
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

/-! ## The profiles at the coalescing endpoint -/

theorem evenMomentVector_id_zero (a : ℝ) :
    evenMomentVector a (ContinuousLinearMap.id ℝ (Lp ℝ 2 (apertureMeasure a))) 0
      = apertureMonomialL2 a 0 := by
  rw [evenMomentVector]
  norm_num

theorem oddMomentVector_id_zero (a : ℝ) :
    oddMomentVector a (ContinuousLinearMap.id ℝ (Lp ℝ 2 (apertureMeasure a))) 0
      = apertureMonomialL2 a 1 := by
  rw [oddMomentVector]
  norm_num

set_option maxHeartbeats 1000000 in
/-- **`(47)`, even half.**  The even profile tends to the constant source vector. -/
theorem tendsto_apertureCoshL2 {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun c : ℝ => apertureCoshL2 a c) (𝓝[>] (0 : ℝ))
      (𝓝 (apertureMonomialL2 a 0)) := by
  have hbase := tendsto_smul_inv_pow_of_hasSum
    (u := evenMomentVector a (ContinuousLinearMap.id ℝ (Lp ℝ 2 (apertureMeasure a))))
    (R := 1) (r := 0) (by norm_num)
    (summable_norm_evenMomentVector ha _ (by norm_num)) (by omega)
    (fun t htpos _ => hasSum_evenMomentVector ha _ htpos.le)
  rw [evenMomentVector_id_zero] at hbase
  have hsq : Tendsto (fun c : ℝ => c ^ 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : Tendsto (fun c : ℝ => c ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa using (continuous_pow 2).tendsto (0 : ℝ)
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact pow_pos (Set.mem_Ioi.mp hc) 2
  refine (hbase.comp hsq).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hcpos : (0 : ℝ) < c := Set.mem_Ioi.mp hc
  simp only [Function.comp_apply, pow_zero, inv_one, one_smul, ContinuousLinearMap.id_apply]
  rw [Real.sqrt_sq hcpos.le]

set_option maxHeartbeats 1000000 in
/-- **`(47)`, odd half.**  The normalized odd profile tends to the position source vector. -/
theorem tendsto_inv_smul_apertureSinhL2 {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun c : ℝ => c⁻¹ • apertureSinhL2 a c) (𝓝[>] (0 : ℝ))
      (𝓝 (apertureMonomialL2 a 1)) := by
  have hbase := tendsto_smul_inv_pow_of_hasSum
    (u := oddMomentVector a (ContinuousLinearMap.id ℝ (Lp ℝ 2 (apertureMeasure a))))
    (R := 1) (r := 0) (by norm_num)
    (summable_norm_oddMomentVector ha _ (by norm_num)) (by omega)
    (fun t htpos _ => hasSum_oddMomentVector ha _ htpos)
  rw [oddMomentVector_id_zero] at hbase
  have hsq : Tendsto (fun c : ℝ => c ^ 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : Tendsto (fun c : ℝ => c ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa using (continuous_pow 2).tendsto (0 : ℝ)
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact pow_pos (Set.mem_Ioi.mp hc) 2
  refine (hbase.comp hsq).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hcpos : (0 : ℝ) < c := Set.mem_Ioi.mp hc
  simp only [Function.comp_apply, pow_zero, inv_one, one_smul, ContinuousLinearMap.id_apply]
  rw [Real.sqrt_sq hcpos.le]

end GaloisForLFunctions.HTGeometry

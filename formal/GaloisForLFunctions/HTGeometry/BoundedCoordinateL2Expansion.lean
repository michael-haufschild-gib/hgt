import GaloisForLFunctions.HTGeometry.VectorPowerSeriesLeadingOrder
import GaloisForLFunctions.HTGeometry.DominatedSeriesToLp
import GaloisForLFunctions.HTGeometry.GroundOverlap
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Taylor expansions along a bounded coordinate

An aperture is nothing more than a finite measure space carrying a bounded real coordinate.  On such
a space the hyperbolic profiles `cosh(cX)`, `sinh(cX)` and the Fourier character `e^{-ixX}` are `L²`
sums of their monomial series, because the Taylor tail is uniformly small on the coordinate range
and a finite measure turns a uniform bound into an `L²` bound.

Combined with the leading-order theorem for vector power series this converts the first visible
degree of a bounded observable into the exact rate of the corresponding parity energy, and exhibits
the leading direction of the observed Fourier character.

The statement is model-free: it applies equally to `L²` of a restricted measure on the line and to
`L²` of the subtype carrying the interval, which is the model Suzuki's operator uses.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The `L²` window constant of a finite measure. -/
def l2Window {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : ℝ :=
  (measureUnivNNReal μ : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹

theorem l2Window_nonneg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : 0 ≤ l2Window μ :=
  Real.rpow_nonneg (by positivity) _

/-- The real-to-complex inclusion of `L²`. -/
def ofRealLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  Complex.ofRealCLM.compLpL 2 μ

/-- A bounded real coordinate on a measure space: the abstract aperture. -/
structure BoundedCoordinate (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- the coordinate -/
  coord : Ω → ℝ
  /-- the uniform bound on the coordinate -/
  bound : ℝ
  /-- the coordinate is measurable -/
  measurable_coord : Measurable coord
  /-- the bound is nonnegative -/
  bound_nonneg : 0 ≤ bound
  /-- the coordinate is bounded almost everywhere -/
  abs_coord_le : ∀ᵐ ω ∂μ, |coord ω| ≤ bound

namespace BoundedCoordinate

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  (B : BoundedCoordinate Ω μ)

/-! ## The real monomials and the hyperbolic profiles -/

theorem memLp_pow (n : ℕ) : MemLp (fun ω => (B.coord ω) ^ n) 2 μ := by
  refine MemLp.of_bound ((B.measurable_coord.pow_const n).aestronglyMeasurable)
    (B.bound ^ n) ?_
  filter_upwards [B.abs_coord_le] with ω hω
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hω n

theorem memLp_cosh (c : ℝ) : MemLp (fun ω => Real.cosh (c * B.coord ω)) 2 μ := by
  refine MemLp.of_bound
    ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).comp_aestronglyMeasurable
      B.measurable_coord.aestronglyMeasurable) (Real.exp (|c| * B.bound)) ?_
  filter_upwards [B.abs_coord_le] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
  have hcosh : Real.cosh (c * B.coord ω) ≤ Real.exp |c * B.coord ω| := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (c * B.coord ω) ≤ Real.exp |c * B.coord ω| :=
      Real.exp_le_exp.mpr (le_abs_self _)
    have h2 : Real.exp (-(c * B.coord ω)) ≤ Real.exp |c * B.coord ω| :=
      Real.exp_le_exp.mpr (neg_le_abs _)
    linarith
  refine le_trans hcosh (Real.exp_le_exp.mpr ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hω (abs_nonneg c)

theorem memLp_sinh (c : ℝ) : MemLp (fun ω => Real.sinh (c * B.coord ω)) 2 μ := by
  refine MemLp.of_bound
    ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).comp_aestronglyMeasurable
      B.measurable_coord.aestronglyMeasurable) (Real.exp (|c| * B.bound)) ?_
  filter_upwards [B.abs_coord_le] with ω hω
  rw [Real.norm_eq_abs]
  have hsinh : |Real.sinh (c * B.coord ω)| ≤ Real.exp |c * B.coord ω| := by
    rw [Real.sinh_eq, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2),
      div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    have h1 : Real.exp (c * B.coord ω) ≤ Real.exp |c * B.coord ω| :=
      Real.exp_le_exp.mpr (le_abs_self _)
    have h2 : Real.exp (-(c * B.coord ω)) ≤ Real.exp |c * B.coord ω| :=
      Real.exp_le_exp.mpr (neg_le_abs _)
    have h1' : (0:ℝ) < Real.exp (c * B.coord ω) := Real.exp_pos _
    have h2' : (0:ℝ) < Real.exp (-(c * B.coord ω)) := Real.exp_pos _
    rcases abs_cases (Real.exp (c * B.coord ω) - Real.exp (-(c * B.coord ω))) with
      ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
  refine le_trans hsinh (Real.exp_le_exp.mpr ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hω (abs_nonneg c)

/-- The monomial `X ^ n` as an `L²` class. -/
def monomial (n : ℕ) : Lp ℝ 2 μ := (B.memLp_pow n).toLp _

/-- The even hyperbolic profile as an `L²` class. -/
def coshVec (c : ℝ) : Lp ℝ 2 μ := (B.memLp_cosh c).toLp _

/-- The odd hyperbolic profile as an `L²` class. -/
def sinhVec (c : ℝ) : Lp ℝ 2 μ := (B.memLp_sinh c).toLp _

theorem coeFn_monomial (n : ℕ) :
    (B.monomial n : Ω → ℝ) =ᵐ[μ] fun ω => (B.coord ω) ^ n := (B.memLp_pow n).coeFn_toLp

theorem coeFn_coshVec (c : ℝ) :
    (B.coshVec c : Ω → ℝ) =ᵐ[μ] fun ω => Real.cosh (c * B.coord ω) := (B.memLp_cosh c).coeFn_toLp

theorem coeFn_sinhVec (c : ℝ) :
    (B.sinhVec c : Ω → ℝ) =ᵐ[μ] fun ω => Real.sinh (c * B.coord ω) := (B.memLp_sinh c).coeFn_toLp

theorem norm_monomial_le (n : ℕ) : ‖B.monomial n‖ ≤ l2Window μ * B.bound ^ n := by
  have hbd : ∀ᵐ ω ∂μ, ‖(B.monomial n : Ω → ℝ) ω‖ ≤ B.bound ^ n := by
    filter_upwards [B.coeFn_monomial n, B.abs_coord_le] with ω hω hb
    rw [hω, Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hb n
  exact Lp.norm_le_of_ae_bound (p := 2) (pow_nonneg B.bound_nonneg n) hbd

/-! ## The `L²` Taylor expansions -/

set_option maxHeartbeats 1000000 in
/-- **The even hyperbolic profile is the `L²` sum of its monomial series.** -/
theorem hasSum_coshVec (c : ℝ) :
    HasSum (fun k : ℕ => (c ^ (2 * k) / (Nat.factorial (2 * k)) : ℝ) • B.monomial (2 * k))
      (B.coshVec c) := by
  have hmem : ∀ k : ℕ, MemLp
      (fun ω => (c ^ (2 * k) / (Nat.factorial (2 * k)) : ℝ) * (B.coord ω) ^ (2 * k)) 2 μ :=
    fun k => (B.memLp_pow (2 * k)).const_mul _
  have hbase := hasSum_toLp_of_ae_dominated (𝕜 := ℝ) (μ := μ)
    (f := fun k ω => (c ^ (2 * k) / (Nat.factorial (2 * k)) : ℝ) * (B.coord ω) ^ (2 * k))
    (F := fun ω => Real.cosh (c * B.coord ω))
    (g := fun k => (|c| * B.bound) ^ (2 * k) / (Nat.factorial (2 * k)))
    ((Real.hasSum_cosh (|c| * B.bound)).summable)
    (fun k => by
      have hnn : (0 : ℝ) ≤ |c| * B.bound := mul_nonneg (abs_nonneg c) B.bound_nonneg
      positivity)
    (fun k => by
      filter_upwards [B.abs_coord_le] with ω hω
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_pow,
        abs_of_pos (show (0 : ℝ) < ((Nat.factorial (2 * k) : ℕ) : ℝ) by positivity),
        mul_pow, div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) hω _) (by positivity))
    (Filter.Eventually.of_forall fun ω => by
      refine (Real.hasSum_cosh (c * B.coord ω)).congr_fun fun k => ?_
      rw [mul_pow]
      ring)
    hmem (B.memLp_cosh c)
  refine hbase.congr_fun fun k => ?_
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul (c ^ (2 * k) / (Nat.factorial (2 * k)) : ℝ) (B.monomial (2 * k)),
    B.coeFn_monomial (2 * k), (hmem k).coeFn_toLp] with ω h1 h2 h3
  rw [h3, h1, Pi.smul_apply, h2, smul_eq_mul]

set_option maxHeartbeats 1000000 in
/-- **The odd hyperbolic profile is the `L²` sum of its monomial series.** -/
theorem hasSum_sinhVec (c : ℝ) :
    HasSum (fun k : ℕ => (c ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)) : ℝ)
        • B.monomial (2 * k + 1))
      (B.sinhVec c) := by
  have hmem : ∀ k : ℕ, MemLp
      (fun ω => (c ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)) : ℝ)
        * (B.coord ω) ^ (2 * k + 1)) 2 μ :=
    fun k => (B.memLp_pow (2 * k + 1)).const_mul _
  have hbase := hasSum_toLp_of_ae_dominated (𝕜 := ℝ) (μ := μ)
    (f := fun k ω => (c ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)) : ℝ)
      * (B.coord ω) ^ (2 * k + 1))
    (F := fun ω => Real.sinh (c * B.coord ω))
    (g := fun k => (|c| * B.bound) ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)))
    ((Real.hasSum_sinh (|c| * B.bound)).summable)
    (fun k => by
      have hnn : (0 : ℝ) ≤ |c| * B.bound := mul_nonneg (abs_nonneg c) B.bound_nonneg
      positivity)
    (fun k => by
      filter_upwards [B.abs_coord_le] with ω hω
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_pow,
        abs_of_pos (show (0 : ℝ) < ((Nat.factorial (2 * k + 1) : ℕ) : ℝ) by positivity),
        mul_pow, div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) hω _) (by positivity))
    (Filter.Eventually.of_forall fun ω => by
      refine (Real.hasSum_sinh (c * B.coord ω)).congr_fun fun k => ?_
      rw [mul_pow]
      ring)
    hmem (B.memLp_sinh c)
  refine hbase.congr_fun fun k => ?_
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul (c ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)) : ℝ)
      (B.monomial (2 * k + 1)),
    B.coeFn_monomial (2 * k + 1), (hmem k).coeFn_toLp] with ω h1 h2 h3
  rw [h3, h1, Pi.smul_apply, h2, smul_eq_mul]

/-! ## Parity energies of a bounded observable -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `k`-th even moment of a bounded observable. -/
def evenMoment (P : Lp ℝ 2 μ →L[ℝ] E) (k : ℕ) : E :=
  ((Nat.factorial (2 * k) : ℝ))⁻¹ • P (B.monomial (2 * k))

/-- The `k`-th odd moment of a bounded observable. -/
def oddMoment (P : Lp ℝ 2 μ →L[ℝ] E) (k : ℕ) : E :=
  ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ • P (B.monomial (2 * k + 1))

set_option maxHeartbeats 1000000 in
theorem summable_norm_evenMoment (P : Lp ℝ 2 μ →L[ℝ] E) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun k : ℕ => ‖B.evenMoment P k‖ * R ^ k := by
  have hmaj : Summable fun k : ℕ =>
      (‖P‖ * l2Window μ) * ((B.bound ^ 2 * R) ^ k / (Nat.factorial (2 * k) : ℝ)) := by
    have hb : Summable fun k : ℕ =>
        Real.sqrt (B.bound ^ 2 * R) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) :=
      (Real.hasSum_cosh (Real.sqrt (B.bound ^ 2 * R))).summable
    refine (hb.mul_left (‖P‖ * l2Window μ)).congr fun k => ?_
    congr 2
    rw [pow_mul, Real.sq_sqrt (by positivity)]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hmaj
  have hfac : (0 : ℝ) < ((Nat.factorial (2 * k) : ℕ) : ℝ) := by positivity
  have hnorm : ‖B.evenMoment P k‖
      = ((Nat.factorial (2 * k) : ℝ))⁻¹ * ‖P (B.monomial (2 * k))‖ := by
    rw [evenMoment, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hchain : ‖P (B.monomial (2 * k))‖ ≤ ‖P‖ * (l2Window μ * B.bound ^ (2 * k)) :=
    (P.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (B.norm_monomial_le (2 * k)) (norm_nonneg _))
  rw [hnorm]
  have hstep : ((Nat.factorial (2 * k) : ℝ))⁻¹ * ‖P (B.monomial (2 * k))‖ * R ^ k
      ≤ ((Nat.factorial (2 * k) : ℝ))⁻¹ * (‖P‖ * (l2Window μ * B.bound ^ (2 * k))) * R ^ k := by
    have h1 := mul_le_mul_of_nonneg_left hchain (le_of_lt (inv_pos.mpr hfac))
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  refine hstep.trans (le_of_eq ?_)
  rw [mul_pow, ← pow_mul, mul_comm 2 k]
  field_simp

set_option maxHeartbeats 1000000 in
theorem summable_norm_oddMoment (P : Lp ℝ 2 μ →L[ℝ] E) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun k : ℕ => ‖B.oddMoment P k‖ * R ^ k := by
  have hmaj : Summable fun k : ℕ =>
      (‖P‖ * l2Window μ * (1 + B.bound)) * ((B.bound ^ 2 * R) ^ k / (Nat.factorial (2 * k) : ℝ)) := by
    have hb : Summable fun k : ℕ =>
        Real.sqrt (B.bound ^ 2 * R) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) :=
      (Real.hasSum_cosh (Real.sqrt (B.bound ^ 2 * R))).summable
    refine (hb.mul_left (‖P‖ * l2Window μ * (1 + B.bound))).congr fun k => ?_
    congr 2
    rw [pow_mul, Real.sq_sqrt (by positivity)]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hmaj
  have hfacpos : (0 : ℝ) < ((Nat.factorial (2 * k + 1) : ℕ) : ℝ) := by positivity
  have hfac0 : (0 : ℝ) < ((Nat.factorial (2 * k) : ℕ) : ℝ) := by positivity
  have hfacmono : ((Nat.factorial (2 * k) : ℕ) : ℝ) ≤ ((Nat.factorial (2 * k + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ _)
  have hnorm : ‖B.oddMoment P k‖
      = ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ * ‖P (B.monomial (2 * k + 1))‖ := by
    rw [oddMoment, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hchain : ‖P (B.monomial (2 * k + 1))‖ ≤ ‖P‖ * (l2Window μ * B.bound ^ (2 * k + 1)) :=
    (P.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (B.norm_monomial_le (2 * k + 1)) (norm_nonneg _))
  have hpowsucc : B.bound ^ (2 * k + 1) ≤ (1 + B.bound) * B.bound ^ (2 * k) := by
    rw [pow_succ]
    nlinarith [pow_nonneg B.bound_nonneg (2 * k), B.bound_nonneg]
  have hchain' : ‖P (B.monomial (2 * k + 1))‖
      ≤ ‖P‖ * l2Window μ * (1 + B.bound) * B.bound ^ (2 * k) := by
    have hnn : (0 : ℝ) ≤ ‖P‖ * l2Window μ :=
      mul_nonneg (norm_nonneg _) (l2Window_nonneg μ)
    calc ‖P (B.monomial (2 * k + 1))‖
        ≤ ‖P‖ * (l2Window μ * B.bound ^ (2 * k + 1)) := hchain
      _ = (‖P‖ * l2Window μ) * B.bound ^ (2 * k + 1) := by ring
      _ ≤ (‖P‖ * l2Window μ) * ((1 + B.bound) * B.bound ^ (2 * k)) :=
          mul_le_mul_of_nonneg_left hpowsucc hnn
      _ = ‖P‖ * l2Window μ * (1 + B.bound) * B.bound ^ (2 * k) := by ring
  have h2 : ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ ≤ ((Nat.factorial (2 * k) : ℝ))⁻¹ := by
    have h := one_div_le_one_div_of_le hfac0 hfacmono
    rwa [one_div, one_div] at h
  rw [hnorm]
  have hstep : ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ * ‖P (B.monomial (2 * k + 1))‖ * R ^ k
      ≤ ((Nat.factorial (2 * k) : ℝ))⁻¹
        * (‖P‖ * l2Window μ * (1 + B.bound) * B.bound ^ (2 * k)) * R ^ k := by
    have hnn : (0 : ℝ) ≤ ‖P (B.monomial (2 * k + 1))‖ := norm_nonneg _
    have hinner : ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ * ‖P (B.monomial (2 * k + 1))‖
        ≤ ((Nat.factorial (2 * k) : ℝ))⁻¹
          * (‖P‖ * l2Window μ * (1 + B.bound) * B.bound ^ (2 * k)) :=
      le_trans (mul_le_mul_of_nonneg_right h2 hnn)
        (mul_le_mul_of_nonneg_left hchain' (by positivity))
    exact mul_le_mul_of_nonneg_right hinner (by positivity)
  refine hstep.trans (le_of_eq ?_)
  rw [mul_pow, ← pow_mul, mul_comm 2 k]
  field_simp

set_option maxHeartbeats 1000000 in
theorem hasSum_evenMoment (P : Lp ℝ 2 μ →L[ℝ] E) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun k : ℕ => t ^ k • B.evenMoment P k) (P (B.coshVec (Real.sqrt t))) := by
  have hbase := (B.hasSum_coshVec (Real.sqrt t)).mapL P
  refine hbase.congr_fun fun k => ?_
  rw [ContinuousLinearMap.map_smul, evenMoment, smul_smul]
  congr 1
  rw [pow_mul, Real.sq_sqrt ht, div_eq_mul_inv]

set_option maxHeartbeats 1000000 in
theorem hasSum_oddMoment (P : Lp ℝ 2 μ →L[ℝ] E) {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => t ^ k • B.oddMoment P k)
      ((Real.sqrt t)⁻¹ • P (B.sinhVec (Real.sqrt t))) := by
  have hbase := ((B.hasSum_sinhVec (Real.sqrt t)).mapL P).const_smul ((Real.sqrt t)⁻¹)
  have hsq : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  refine hbase.congr_fun fun k => ?_
  rw [ContinuousLinearMap.map_smul, oddMoment, smul_smul, smul_smul]
  congr 1
  rw [pow_succ, pow_mul, Real.sq_sqrt ht.le]
  field_simp

/-! ## The parity rates and the coalescing endpoint -/

set_option maxHeartbeats 1000000 in
/-- **`(5)`, even half.**  The even parity energy of a bounded observable has the exact rate of its
first visible even moment. -/
theorem tendsto_evenEnergy_rate (P : Lp ℝ 2 μ →L[ℝ] E) {j : ℕ}
    (hzero : ∀ k, k < j → B.evenMoment P k = 0) :
    Tendsto (fun c : ℝ => ‖P (B.coshVec c)‖ ^ 2 / c ^ (4 * j)) (𝓝[>] (0 : ℝ))
      (𝓝 (‖B.evenMoment P j‖ ^ 2)) := by
  have hbase := tendsto_normSq_div_pow_even (E := E) (u := B.evenMoment P) (R := 1)
    (by norm_num) (B.summable_norm_evenMoment P (by norm_num)) hzero
    (fun t htpos _ => B.hasSum_evenMoment P htpos.le)
  refine hbase.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [Real.sqrt_sq (Set.mem_Ioi.mp hc).le]

set_option maxHeartbeats 1000000 in
/-- **`(5)`, odd half.**  The odd parity energy of a bounded observable has the exact rate of its
first visible odd moment. -/
theorem tendsto_oddEnergy_rate (P : Lp ℝ 2 μ →L[ℝ] E) {j : ℕ}
    (hzero : ∀ k, k < j → B.oddMoment P k = 0) :
    Tendsto (fun c : ℝ => ‖P (B.sinhVec c)‖ ^ 2 / c ^ (4 * j + 2)) (𝓝[>] (0 : ℝ))
      (𝓝 (‖B.oddMoment P j‖ ^ 2)) := by
  have hbase := tendsto_normSq_div_pow_even (E := E) (u := B.oddMoment P) (R := 1)
    (by norm_num) (B.summable_norm_oddMoment P (by norm_num)) hzero
    (fun t htpos _ => B.hasSum_oddMoment P htpos)
  refine hbase.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hcpos : (0 : ℝ) < c := Set.mem_Ioi.mp hc
  rw [Real.sqrt_sq hcpos.le, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos),
    mul_pow, show (4 * j + 2) = (4 * j) + 2 by ring, pow_add]
  field_simp

theorem evenMoment_id_zero : B.evenMoment (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)) 0
    = B.monomial 0 := by
  rw [evenMoment]
  norm_num

theorem oddMoment_id_zero : B.oddMoment (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)) 0
    = B.monomial 1 := by
  rw [oddMoment]
  norm_num

private theorem tendsto_sq_nhdsWithin :
    Tendsto (fun c : ℝ => c ^ 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h0 : Tendsto (fun c : ℝ => c ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_pow 2).tendsto (0 : ℝ)
    exact h0.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact pow_pos (Set.mem_Ioi.mp hc) 2

set_option maxHeartbeats 1000000 in
/-- **`(47)`, even half.**  The even profile tends to the constant source vector. -/
theorem tendsto_coshVec : Tendsto (fun c : ℝ => B.coshVec c) (𝓝[>] (0 : ℝ))
    (𝓝 (B.monomial 0)) := by
  have hbase := tendsto_smul_inv_pow_of_hasSum
    (u := B.evenMoment (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)))
    (R := 1) (r := 0) (by norm_num)
    (B.summable_norm_evenMoment _ (by norm_num)) (by omega)
    (fun t htpos _ => B.hasSum_evenMoment _ htpos.le)
  rw [B.evenMoment_id_zero] at hbase
  refine (hbase.comp tendsto_sq_nhdsWithin).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  simp only [Function.comp_apply, pow_zero, inv_one, one_smul, ContinuousLinearMap.id_apply]
  rw [Real.sqrt_sq (Set.mem_Ioi.mp hc).le]

set_option maxHeartbeats 1000000 in
/-- **`(47)`, odd half.**  The normalized odd profile tends to the position source vector. -/
theorem tendsto_inv_smul_sinhVec :
    Tendsto (fun c : ℝ => c⁻¹ • B.sinhVec c) (𝓝[>] (0 : ℝ)) (𝓝 (B.monomial 1)) := by
  have hbase := tendsto_smul_inv_pow_of_hasSum
    (u := B.oddMoment (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)))
    (R := 1) (r := 0) (by norm_num)
    (B.summable_norm_oddMoment _ (by norm_num)) (by omega)
    (fun t htpos _ => B.hasSum_oddMoment _ htpos)
  rw [B.oddMoment_id_zero] at hbase
  refine (hbase.comp tendsto_sq_nhdsWithin).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  simp only [Function.comp_apply, pow_zero, inv_one, one_smul, ContinuousLinearMap.id_apply]
  rw [Real.sqrt_sq (Set.mem_Ioi.mp hc).le]

/-! ## The complex model -/

section Complexification

/-- The complex monomial `X ^ n`. -/
def monomialC (n : ℕ) : Lp ℂ 2 μ := ofRealLp μ (B.monomial n)

/-- The complex even hyperbolic profile. -/
def coshVecC (c : ℝ) : Lp ℂ 2 μ := ofRealLp μ (B.coshVec c)

/-- The complex odd hyperbolic profile. -/
def sinhVecC (c : ℝ) : Lp ℂ 2 μ := ofRealLp μ (B.sinhVec c)

theorem hasSum_coshVecC (c : ℝ) :
    HasSum (fun k : ℕ => (c ^ (2 * k) / (Nat.factorial (2 * k)) : ℝ) • B.monomialC (2 * k))
      (B.coshVecC c) := by
  refine ((B.hasSum_coshVec c).mapL (ofRealLp μ)).congr_fun fun k => ?_
  rw [monomialC, ContinuousLinearMap.map_smul]

theorem hasSum_sinhVecC (c : ℝ) :
    HasSum (fun k : ℕ => (c ^ (2 * k + 1) / (Nat.factorial (2 * k + 1)) : ℝ)
        • B.monomialC (2 * k + 1))
      (B.sinhVecC c) := by
  refine ((B.hasSum_sinhVec c).mapL (ofRealLp μ)).congr_fun fun k => ?_
  rw [monomialC, ContinuousLinearMap.map_smul]

theorem tendsto_coshVecC : Tendsto (fun c : ℝ => B.coshVecC c) (𝓝[>] (0 : ℝ))
    (𝓝 (B.monomialC 0)) :=
  ((ofRealLp μ).continuous.tendsto _).comp B.tendsto_coshVec

theorem tendsto_inv_smul_sinhVecC :
    Tendsto (fun c : ℝ => c⁻¹ • B.sinhVecC c) (𝓝[>] (0 : ℝ)) (𝓝 (B.monomialC 1)) := by
  have h := ((ofRealLp μ).continuous.tendsto (B.monomial 1)).comp B.tendsto_inv_smul_sinhVec
  refine h.congr' ?_
  filter_upwards with c
  simp only [Function.comp_apply, sinhVecC]
  rw [ContinuousLinearMap.map_smul]

/-! ## Complex moments of a bounded observable -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The `k`-th even complex moment of a bounded observable. -/
def evenMomentC (P : Lp ℂ 2 μ →L[ℂ] E) (k : ℕ) : E :=
  ((Nat.factorial (2 * k) : ℝ))⁻¹ • P (B.monomialC (2 * k))

/-- The `k`-th odd complex moment of a bounded observable. -/
def oddMomentC (P : Lp ℂ 2 μ →L[ℂ] E) (k : ℕ) : E :=
  ((Nat.factorial (2 * k + 1) : ℝ))⁻¹ • P (B.monomialC (2 * k + 1))

theorem evenMomentC_eq (P : Lp ℂ 2 μ →L[ℂ] E) (k : ℕ) :
    B.evenMomentC P k = B.evenMoment ((P.restrictScalars ℝ).comp (ofRealLp μ)) k := by
  rw [evenMomentC, evenMoment, monomialC]
  rfl

theorem oddMomentC_eq (P : Lp ℂ 2 μ →L[ℂ] E) (k : ℕ) :
    B.oddMomentC P k = B.oddMoment ((P.restrictScalars ℝ).comp (ofRealLp μ)) k := by
  rw [oddMomentC, oddMoment, monomialC]
  rfl

set_option maxHeartbeats 1000000 in
/-- **`(5)`, even half, complex model.** -/
theorem tendsto_evenEnergyC_rate (P : Lp ℂ 2 μ →L[ℂ] E) {j : ℕ}
    (hzero : ∀ k, k < j → B.evenMomentC P k = 0) :
    Tendsto (fun c : ℝ => ‖P (B.coshVecC c)‖ ^ 2 / c ^ (4 * j)) (𝓝[>] (0 : ℝ))
      (𝓝 (‖B.evenMomentC P j‖ ^ 2)) := by
  have hzero' : ∀ k, k < j →
      B.evenMoment ((P.restrictScalars ℝ).comp (ofRealLp μ)) k = 0 := by
    intro k hk
    rw [← B.evenMomentC_eq P k]
    exact hzero k hk
  have h := B.tendsto_evenEnergy_rate ((P.restrictScalars ℝ).comp (ofRealLp μ)) hzero'
  rw [← B.evenMomentC_eq P j] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **`(5)`, odd half, complex model.** -/
theorem tendsto_oddEnergyC_rate (P : Lp ℂ 2 μ →L[ℂ] E) {j : ℕ}
    (hzero : ∀ k, k < j → B.oddMomentC P k = 0) :
    Tendsto (fun c : ℝ => ‖P (B.sinhVecC c)‖ ^ 2 / c ^ (4 * j + 2)) (𝓝[>] (0 : ℝ))
      (𝓝 (‖B.oddMomentC P j‖ ^ 2)) := by
  have hzero' : ∀ k, k < j →
      B.oddMoment ((P.restrictScalars ℝ).comp (ofRealLp μ)) k = 0 := by
    intro k hk
    rw [← B.oddMomentC_eq P k]
    exact hzero k hk
  have h := B.tendsto_oddEnergy_rate ((P.restrictScalars ℝ).comp (ofRealLp μ)) hzero'
  rw [← B.oddMomentC_eq P j] at h
  exact h

/-! ## The Fourier character along the coordinate -/

theorem coeFn_monomialC (n : ℕ) :
    (B.monomialC n : Ω → ℂ) =ᵐ[μ] fun ω => ((B.coord ω : ℝ) : ℂ) ^ n := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM (B.monomial n),
    B.coeFn_monomial n] with ω h1 h2
  rw [monomialC, ofRealLp, h1, h2]
  simp

theorem memLp_fourier (x : ℝ) :
    MemLp (fun ω => Complex.exp (-(x : ℂ) * Complex.I * ((B.coord ω : ℝ) : ℂ))) 2 μ := by
  refine MemLp.of_bound
    ((Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).comp_aestronglyMeasurable
        B.measurable_coord.aestronglyMeasurable) 1 ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Complex.norm_exp]
  have hre : (-(x : ℂ) * Complex.I * ((B.coord ω : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-- The Fourier character `e^{-ixX}` as an `L²` class. -/
def fourierVec (x : ℝ) : Lp ℂ 2 μ := (B.memLp_fourier x).toLp _

set_option maxHeartbeats 1000000 in
/-- **The Fourier character is the `L²` sum of its monomial series.** -/
theorem hasSum_fourierVec (x : ℝ) :
    HasSum (fun n : ℕ => ((-(x : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ))
        • B.monomialC n) (B.fourierVec x) := by
  have hmemC : ∀ n : ℕ, MemLp
      (fun ω => ((-(x : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ))
        * ((B.coord ω : ℝ) : ℂ) ^ n) 2 μ := by
    intro n
    have hb : MemLp (fun ω => ((B.coord ω : ℝ) : ℂ) ^ n) 2 μ := by
      refine MemLp.of_bound
        (((Complex.continuous_ofReal.pow n)).comp_aestronglyMeasurable
          B.measurable_coord.aestronglyMeasurable) (B.bound ^ n) ?_
      filter_upwards [B.abs_coord_le] with ω hω
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hω n
    exact hb.const_mul _
  have hnormcoef : ∀ n : ℕ,
      ‖((-(x : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ))‖
        = |x| ^ n / (Nat.factorial n : ℝ) := by
    intro n
    rw [norm_div, norm_pow, norm_mul, norm_neg, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, Complex.norm_natCast]
  have hgsum : Summable fun n : ℕ => (|x| * B.bound) ^ n / (Nat.factorial n : ℝ) :=
    (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (|x| * B.bound)).summable
  have hbase := hasSum_toLp_of_ae_dominated (𝕜 := ℂ) (μ := μ)
    (f := fun n ω => ((-(x : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ))
      * ((B.coord ω : ℝ) : ℂ) ^ n)
    (F := fun ω => Complex.exp (-(x : ℂ) * Complex.I * ((B.coord ω : ℝ) : ℂ)))
    (g := fun n => (|x| * B.bound) ^ n / (Nat.factorial n : ℝ))
    hgsum
    (fun n => by
      have hnn : (0 : ℝ) ≤ |x| * B.bound := mul_nonneg (abs_nonneg x) B.bound_nonneg
      positivity)
    (fun n => by
      filter_upwards [B.abs_coord_le] with ω hω
      rw [norm_mul, hnormcoef n, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow,
        div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hω n) (by positivity))
    (Filter.Eventually.of_forall fun ω => by
      have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ)
        (-(x : ℂ) * Complex.I * ((B.coord ω : ℝ) : ℂ))
      rw [← Complex.exp_eq_exp_ℂ] at h
      refine h.congr_fun fun n => ?_
      rw [mul_pow]
      ring)
    hmemC (B.memLp_fourier x)
  refine hbase.congr_fun fun n => ?_
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul ((-(x : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ))
    (B.monomialC n), B.coeFn_monomialC n, (hmemC n).coeFn_toLp] with ω h1 h2 h3
  rw [h3, h1, Pi.smul_apply, h2, smul_eq_mul]

/-! ## The leading ground direction of the observed character -/

section GroundDirection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The observable's leading ground coefficient at degree `n`. -/
def fourierGroundVec (P : Lp ℂ 2 μ →L[ℂ] E) (n : ℕ) : E :=
  ((-Complex.I) ^ n / (Nat.factorial n : ℂ)) • P (B.monomialC n)

theorem norm_monomialC_le (n : ℕ) : ‖B.monomialC n‖ ≤ l2Window μ * B.bound ^ n := by
  have hbd : ∀ᵐ ω ∂μ, ‖(B.monomialC n : Ω → ℂ) ω‖ ≤ B.bound ^ n := by
    filter_upwards [B.coeFn_monomialC n, B.abs_coord_le] with ω hω hb
    rw [hω, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb n
  exact Lp.norm_le_of_ae_bound (p := 2) (pow_nonneg B.bound_nonneg n) hbd

set_option maxHeartbeats 1000000 in
theorem summable_norm_fourierGroundVec (P : Lp ℂ 2 μ →L[ℂ] E) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun n : ℕ => ‖B.fourierGroundVec P n‖ * R ^ n := by
  have hmaj : Summable fun n : ℕ =>
      (‖P‖ * l2Window μ) * ((B.bound * R) ^ n / (Nat.factorial n : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (B.bound * R)).summable.mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
  have hcoef : ‖((-Complex.I) ^ n / (Nat.factorial n : ℂ))‖ = (Nat.factorial n : ℝ)⁻¹ := by
    rw [norm_div, norm_pow, norm_neg, Complex.norm_I, one_pow, Complex.norm_natCast, one_div]
  have hnorm : ‖B.fourierGroundVec P n‖
      = (Nat.factorial n : ℝ)⁻¹ * ‖P (B.monomialC n)‖ := by
    rw [fourierGroundVec, norm_smul, hcoef]
  have hchain : ‖P (B.monomialC n)‖ ≤ ‖P‖ * (l2Window μ * B.bound ^ n) :=
    (P.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (B.norm_monomialC_le n) (norm_nonneg _))
  rw [hnorm]
  have hstep : (Nat.factorial n : ℝ)⁻¹ * ‖P (B.monomialC n)‖ * R ^ n
      ≤ (Nat.factorial n : ℝ)⁻¹ * (‖P‖ * (l2Window μ * B.bound ^ n)) * R ^ n := by
    have h1 := mul_le_mul_of_nonneg_left hchain
      (le_of_lt (inv_pos.mpr (show (0:ℝ) < (Nat.factorial n : ℝ) by positivity)))
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  refine hstep.trans (le_of_eq ?_)
  rw [mul_pow]
  field_simp

set_option maxHeartbeats 1000000 in
/-- **`(69)`: the observed character has an exact leading direction.** -/
theorem tendsto_smul_inv_pow_fourierVec (P : Lp ℂ 2 μ →L[ℂ] E) {k : ℕ}
    (hzero : ∀ n, n < k → P (B.monomialC n) = 0) :
    Tendsto (fun x : ℝ => (x ^ k)⁻¹ • P (B.fourierVec x)) (𝓝[≠] (0 : ℝ))
      (𝓝 (B.fourierGroundVec P k)) := by
  refine tendsto_smul_inv_pow_of_hasSum_punctured (E := E)
    (u := B.fourierGroundVec P) (R := 1) (by norm_num)
    (B.summable_norm_fourierGroundVec P (by norm_num))
    (fun n hn => by rw [fourierGroundVec, hzero n hn, smul_zero]) ?_
  intro x _ _
  have hbase := (B.hasSum_fourierVec x).mapL P
  refine hbase.congr_fun fun n => ?_
  rw [ContinuousLinearMap.map_smul, fourierGroundVec, ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  rw [mul_pow]
  ring

end GroundDirection

section GroundOverlapSection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
/-- **`(70)`: the normalized ground overlap tends to one.** -/
theorem tendsto_groundOverlap_fourierVec (P : Lp ℂ 2 μ →L[ℂ] E) {k : ℕ}
    (hzero : ∀ n, n < k → P (B.monomialC n) = 0) (hk : P (B.monomialC k) ≠ 0) :
    Tendsto (fun x : ℝ =>
        groundOverlap (((Nat.factorial k : ℂ))⁻¹ • P (B.monomialC k)) (P (B.fourierVec x)))
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  set u : E := ((Nat.factorial k : ℂ))⁻¹ • P (B.monomialC k) with hudef
  have hfacne : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hu : u ≠ 0 := by
    rw [hudef]
    exact smul_ne_zero (inv_ne_zero hfacne) hk
  have hcnorm : ‖((-Complex.I) ^ k)‖ = 1 := by
    rw [norm_pow, norm_neg, Complex.norm_I, one_pow]
  have hL : B.fourierGroundVec P k = ((-Complex.I) ^ k) • u := by
    rw [fourierGroundVec, hudef, smul_smul, div_eq_mul_inv]
  have hcne : ((-Complex.I) ^ k) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hcnorm
    norm_num at hcnorm
  have hLne : B.fourierGroundVec P k ≠ 0 := by
    rw [hL]
    exact smul_ne_zero hcne hu
  have hW := B.tendsto_smul_inv_pow_fourierVec P hzero
  have hconst : Tendsto (fun _ : ℝ => u) (𝓝[≠] (0 : ℝ)) (𝓝 u) := tendsto_const_nhds
  have hconstn : Tendsto (fun _ : ℝ => ‖u‖ ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (‖u‖ ^ 2)) :=
    tendsto_const_nhds
  have hnum : Tendsto (fun x : ℝ =>
        ‖(inner ℂ u ((x ^ k)⁻¹ • P (B.fourierVec x)) : ℂ)‖ ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (‖(inner ℂ u (B.fourierGroundVec P k) : ℂ)‖ ^ 2)) :=
    ((Filter.Tendsto.inner hconst hW).norm).pow 2
  have hden : Tendsto (fun x : ℝ => ‖u‖ ^ 2 * ‖(x ^ k)⁻¹ • P (B.fourierVec x)‖ ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (‖u‖ ^ 2 * ‖B.fourierGroundVec P k‖ ^ 2)) :=
    hconstn.mul (hW.norm.pow 2)
  have hdenne : ‖u‖ ^ 2 * ‖B.fourierGroundVec P k‖ ^ 2 ≠ 0 := by
    have h1 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have h2 : ‖B.fourierGroundVec P k‖ ≠ 0 := norm_ne_zero_iff.mpr hLne
    positivity
  have hlim := hnum.div hden hdenne
  have hvalue : ‖(inner ℂ u (B.fourierGroundVec P k) : ℂ)‖ ^ 2 /
      (‖u‖ ^ 2 * ‖B.fourierGroundVec P k‖ ^ 2) = 1 := by
    have h := groundOverlap_unimodular_smul (c := ((-Complex.I) ^ k)) hcnorm hu
    rw [← hL] at h
    exact h
  rw [hvalue] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxne : x ≠ 0 := hx
  have hpowne : (x ^ k)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero k hxne)
  simp only [Pi.div_apply]
  rw [← groundOverlap_real_smul hpowne u (P (B.fourierVec x)), groundOverlap]

end GroundOverlapSection

end Complexification

end BoundedCoordinate

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.ArithmeticCorrelationGeometry.TheMoebiusExceptionalSetIsComeagerAndNull
import GaloisForLFunctions.RHTower.MobiusMertensAbscissaLittlewood
import GaloisForLFunctions.BezoutValuationIncidence.TheVaughanEmptyLegReadsTheZeroAbscissa

/-!
# The gauge exponent of a point

For a coefficient system `a` and a gauge point `x`, the **gauge exponent** `θ_a(x)` is the least
power that bounds the twisted partial sums `Σ_{n ≤ N} a(n) χ_x(n)` (`gaugeExponent`). It plays for
the gauge torus the role the irrationality exponent plays for the real line: a Haar-almost-sure value,
a comeager null exceptional set, and special points whose exponent is the question.

* **Range** (`gaugeExponent_nonneg`, `gaugeExponent_le_one`). For `‖a(n)‖ ≤ 1` the exponent lies in
  `[0, 1]`.
* **The half-power law** (`gaugeExponent_le_half_iff`). `θ_a(x) ≤ 1/2` is exactly ACG's half-power
  law at `x`.
* **Almost-sure value** (`ae_gaugeExponent_le_half`). For sources bounded by one, `θ_a(x) ≤ 1/2` at
  Haar-almost every point.
* **The trivial point reads the zeros** (`gaugeExponent_moebius_trivial`). For the Möbius source
  the exponent at `0` is the zero abscissa `Θ = sup Re ρ` exactly: Littlewood's bound gives `≤ Θ`,
  and a power bound on the Mertens function bounds `Θ`.
* **RH is the typicality of the trivial point**
  (`riemannHypothesis_iff_gaugeExponent_moebius_trivial_le_half`). RH holds iff the exponent of `0`
  is at most the almost-sure bound `1/2`.
* **The Liouville picture** (`moebius_exponent_exceptional_null_and_residual`,
  `moebius_exponent_threeQuarters_residual`). The points of Möbius exponent above `1/2` form a Haar-null
  set that is residual; the points of exponent at least `3/4` already form a residual set. The
  trivial point lies in the closure of the exceptional set (ACG). In `ℝ` the Liouville numbers are a
  residual null set and Roth's theorem places the algebraic numbers outside it; RH places the
  special point `0` outside the Möbius exceptional set.
-/

open MeasureTheory Finset Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

variable (a : ℕ → ℂ) (x : GaugeTorus)

/-- A power bound of exponent `θ` on the twisted partial sums. -/
def GaugePowerBound (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ‖∑ n ∈ range (N + 1), a n * twist x n‖ ≤ C * ((N : ℝ) + 1) ^ θ

/-- The admissible exponents. -/
def exponentSet : Set ℝ := {θ | 0 ≤ θ ∧ GaugePowerBound a x θ}

/-- **The gauge exponent** of the source `a` at the gauge point `x`. -/
def gaugeExponent : ℝ := sInf (exponentSet a x)

variable {a x}

theorem GaugePowerBound.mono {θ θ' : ℝ} (h : GaugePowerBound a x θ) (hθ : θ ≤ θ') :
    GaugePowerBound a x θ' := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun N => (hb N).trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [N.cast_nonneg (α := ℝ)]) hθ

/-- Sources bounded by one have the trivial bound of exponent one. -/
theorem gaugePowerBound_one (ha : ∀ n, ‖a n‖ ≤ 1) : GaugePowerBound a x 1 := by
  refine ⟨1, zero_le_one, fun N => ?_⟩
  rw [one_mul, Real.rpow_one]
  calc ‖∑ n ∈ range (N + 1), a n * twist x n‖ ≤ ∑ n ∈ range (N + 1), ‖a n * twist x n‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _n ∈ range (N + 1), (1 : ℝ) :=
        sum_le_sum fun n _ => by rw [norm_mul, norm_twist, mul_one]; exact ha n
    _ = (N : ℝ) + 1 := by simp

theorem bddBelow_exponentSet : BddBelow (exponentSet a x) := ⟨0, fun _ h => h.1⟩

theorem exponentSet_nonempty (ha : ∀ n, ‖a n‖ ≤ 1) : (exponentSet a x).Nonempty :=
  ⟨1, zero_le_one, gaugePowerBound_one ha⟩

theorem gaugeExponent_le {θ : ℝ} (h0 : 0 ≤ θ) (h : GaugePowerBound a x θ) :
    gaugeExponent a x ≤ θ :=
  csInf_le bddBelow_exponentSet ⟨h0, h⟩

theorem gaugeExponent_nonneg (ha : ∀ n, ‖a n‖ ≤ 1) : 0 ≤ gaugeExponent a x :=
  le_csInf (exponentSet_nonempty ha) fun _ h => h.1

theorem gaugeExponent_le_one (ha : ∀ n, ‖a n‖ ≤ 1) : gaugeExponent a x ≤ 1 :=
  gaugeExponent_le zero_le_one (gaugePowerBound_one ha)

/-- Every exponent above the gauge exponent is admissible. -/
theorem gaugePowerBound_of_gaugeExponent_lt (ha : ∀ n, ‖a n‖ ≤ 1) {θ : ℝ}
    (h : gaugeExponent a x < θ) : GaugePowerBound a x θ := by
  obtain ⟨θ', ⟨_, hb⟩, hlt⟩ := exists_lt_of_csInf_lt (exponentSet_nonempty ha) h
  exact hb.mono hlt.le

/-- Admissibility of every exponent above `θ` bounds the gauge exponent by `θ`. -/
theorem gaugeExponent_le_of_forall {θ : ℝ} (h0 : 0 ≤ θ)
    (h : ∀ δ : ℝ, 0 < δ → GaugePowerBound a x (θ + δ)) : gaugeExponent a x ≤ θ := by
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  exact (gaugeExponent_le (by linarith) (h (δ / 2) (half_pos hδ))).trans_lt (by linarith)

/-! ### The half-power law and the almost-sure value -/

/-- **The half-power law is exponent at most one half.** -/
theorem gaugeExponent_le_half_iff (ha : ∀ n, ‖a n‖ ≤ 1) :
    gaugeExponent a x ≤ 1 / 2 ↔ GaugeHalfPowerLaw a x := by
  constructor
  · intro h δ hδ
    exact gaugePowerBound_of_gaugeExponent_lt ha (by linarith)
  · intro h
    exact gaugeExponent_le_of_forall (by norm_num) fun δ hδ => h δ hδ

/-- **Almost every gauge point has exponent at most one half.** -/
theorem ae_gaugeExponent_le_half (ha : ∀ n, ‖a n‖ ≤ 1) :
    ∀ᵐ y ∂gaugeHaar, gaugeExponent a y ≤ 1 / 2 :=
  (ae_gaugeHalfPowerLaw a ha).mono fun _ hy => (gaugeExponent_le_half_iff ha).mpr hy

/-! ### The Möbius source -/

/-- The Möbius source as complex coefficients. -/
def moebiusSource : ℕ → ℂ := fun n => ((μ n : ℤ) : ℂ)

theorem norm_moebiusSource_le (n : ℕ) : ‖moebiusSource n‖ ≤ 1 := by
  rw [moebiusSource, Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- Twisted Möbius sums over `range (N + 1)` and over `Icc 1 N` agree, since `μ(0) = 0`. -/
theorem sum_range_moebiusSource (y : GaugeTorus) (N : ℕ) :
    ∑ n ∈ range (N + 1), moebiusSource n * twist y n = moebiusGaugeSum N y := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos N), zero_add, Nat.succ_eq_add_one,
    Finset.Ico_add_one_right_eq_Icc]
  simp [moebiusSource, moebiusGaugeSum]

/-- **The trivial point reads the zero abscissa.** The gauge exponent of the Möbius source at the
trivial point is `Θ = sup Re ρ`. -/
theorem gaugeExponent_moebius_trivial :
    gaugeExponent moebiusSource 0 = RHTower.zetaZeroAbscissa := by
  have hΘ0 : (0 : ℝ) ≤ RHTower.zetaZeroAbscissa := by
    linarith [RHTower.half_le_zetaZeroAbscissa]
  apply le_antisymm
  · -- Littlewood: `M(N) = O(N^{Θ + δ})`.
    refine gaugeExponent_le_of_forall hΘ0 fun δ hδ => ?_
    obtain ⟨C, hC, hb⟩ := RHTower.mobiusMertens_subpower_zetaZeroAbscissa δ hδ
    refine ⟨C, hC, fun N => ?_⟩
    simpa [RHTower.mobiusMertensPartialSum, RHTower.mobiusComplexCoefficient, moebiusSource,
      twist_zero] using hb N
  · -- A Mertens power bound below `Θ` would bound `Θ`.
    by_contra hlt
    push Not at hlt
    obtain ⟨θ, hθ1, hθ2⟩ := exists_between hlt
    have hθ0 : 0 ≤ θ := (gaugeExponent_nonneg norm_moebiusSource_le).trans hθ1.le
    obtain ⟨C, hC, hb⟩ := gaugePowerBound_of_gaugeExponent_lt norm_moebiusSource_le hθ1
    have hM : ∀ n : ℕ, 1 ≤ n → |∑ d ∈ Icc 1 n, BezoutValuationIncidence.moebiusReal d| ≤
        (C * 2 ^ θ) * (n : ℝ) ^ θ := by
      intro n hn
      have hsum : ((∑ d ∈ Icc 1 n, BezoutValuationIncidence.moebiusReal d : ℝ) : ℂ) =
          ∑ k ∈ range (n + 1), moebiusSource k * twist 0 k := by
        rw [sum_range_moebiusSource, moebiusGaugeSum]
        push_cast
        simp [BezoutValuationIncidence.moebiusReal, twist_zero]
      have hnorm := hb n
      rw [← hsum, Complex.norm_real, Real.norm_eq_abs] at hnorm
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpow : ((n : ℝ) + 1) ^ θ ≤ 2 ^ θ * (n : ℝ) ^ θ := by
        rw [← Real.mul_rpow (by norm_num) (by linarith)]
        exact Real.rpow_le_rpow (by linarith) (by linarith) hθ0
      calc _ ≤ C * ((n : ℝ) + 1) ^ θ := hnorm
        _ ≤ C * (2 ^ θ * (n : ℝ) ^ θ) := mul_le_mul_of_nonneg_left hpow hC
        _ = (C * 2 ^ θ) * (n : ℝ) ^ θ := by ring
    have := BezoutValuationIncidence.zetaZeroAbscissa_le_of_moebius_power_bound
      (by positivity) hθ0 hM
    linarith

/-- **RH is the typicality of the trivial point**: the Möbius exponent of `0` is at most the
almost-sure bound `1/2`. -/
theorem riemannHypothesis_iff_gaugeExponent_moebius_trivial_le_half :
    RiemannHypothesis ↔ gaugeExponent moebiusSource 0 ≤ 1 / 2 := by
  rw [gaugeExponent_le_half_iff norm_moebiusSource_le]
  exact gaugeHalfPowerLaw_moebius_zero_iff.symm

/-! ### The Liouville picture -/

/-- **The exceptional set is null and residual.** -/
theorem moebius_exponent_exceptional_null_and_residual :
    {y : GaugeTorus | 1 / 2 < gaugeExponent moebiusSource y} ∈ residual GaugeTorus ∧
      gaugeHaar {y : GaugeTorus | 1 / 2 < gaugeExponent moebiusSource y} = 0 := by
  have hset : {y : GaugeTorus | 1 / 2 < gaugeExponent moebiusSource y} =
      {y : GaugeTorus | ¬ GaugeHalfPowerLaw (fun n => ((μ n : ℤ) : ℂ)) y} := by
    ext y
    simp only [Set.mem_setOf_eq]
    rw [← not_le, gaugeExponent_le_half_iff norm_moebiusSource_le]
    exact Iff.rfl
  rw [hset]
  exact moebius_exceptional_residual_and_null

/-- Points of the strong exceptional set have Möbius exponent at least `3/4`. -/
theorem threeQuarters_le_gaugeExponent_of_mem_strongExceptional {y : GaugeTorus}
    (hy : y ∈ strongExceptional) : 3 / 4 ≤ gaugeExponent moebiusSource y := by
  by_contra hlt
  push Not at hlt
  obtain ⟨C, hC, hb⟩ := gaugePowerBound_of_gaugeExponent_lt norm_moebiusSource_le hlt
  obtain ⟨N, hN⟩ := hy ⌈C⌉₊
  have hle := hb N
  rw [sum_range_moebiusSource] at hle
  have hpos : 0 ≤ ((N : ℝ) + 1) ^ (3 / 4 : ℝ) := by positivity
  have hceil : C * ((N : ℝ) + 1) ^ (3 / 4 : ℝ) ≤ (⌈C⌉₊ : ℝ) * ((N : ℝ) + 1) ^ (3 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil C) hpos
  linarith

/-- **The points of Möbius exponent at least `3/4` form a residual set.** -/
theorem moebius_exponent_threeQuarters_residual :
    {y : GaugeTorus | 3 / 4 ≤ gaugeExponent moebiusSource y} ∈ residual GaugeTorus :=
  mem_of_superset (residual_of_dense_Gδ isGδ_strongExceptional dense_strongExceptional)
    fun _ hy => threeQuarters_le_gaugeExponent_of_mem_strongExceptional hy

/-- **The Liouville point is exceptional.** -/
theorem half_lt_gaugeExponent_moebius_liouville {y : GaugeTorus}
    (hy : ∀ n, n ≠ 0 → twist y n = (-1 : ℂ) ^ ArithmeticFunction.cardFactors n) :
    1 / 2 < gaugeExponent moebiusSource y := by
  by_contra hle
  push Not at hle
  exact not_gaugeHalfPowerLaw_moebius_liouville hy
    ((gaugeExponent_le_half_iff norm_moebiusSource_le).mp hle)

end GaloisForLFunctions.ArithmeticGaugeTheory

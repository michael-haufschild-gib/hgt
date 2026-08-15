import GaloisForLFunctions.HTGeometry.InverseSqrtBinomialSeries
import GaloisForLFunctions.HTGeometry.PowerTailSquareIntegrable
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The half-power resolvent profile and its derivatives

Writing the terminal resolvent as its binomial series with the scale factored out,

`(L − T/2)^{-a} = Σ_k binom(2k,k) 4^{-k} 2^{-k} L^{-(k+a)} T^k`,

differentiating in `L` is termwise and only shifts the exponent: the `k`-th term acquires the factor
`−(k+a)` and the exponent `−(k+a+1)`.  So the whole tower of derivatives lives in one family, indexed
by the exponent `a` together with a weight `g : ℕ → ℝ`, and differentiation is the substitution

`(a, g) ↦ (a + 1, k ↦ −(k+a)·g k)`.

Starting from `(1/2, 1)` this produces `(3/2, k ↦ −(2k+1)/2)` and `(5/2, k ↦ (2k+1)(2k+3)/4)`, whose
weights are exactly the coefficients of `(1−s)^{-3/2}` and `(1−s)^{-5/2}` against the central
binomials.  No separate generalized binomial series has to be constructed: the classical coefficients
are produced by the differentiation itself.

Termwise differentiation is legitimate on any terminal ray `L > L₀` with `‖T‖ < 2L₀`, where the terms
are dominated by `|g k| L₀^{-a} (‖T‖/2L₀)^k`; the resulting profile decays like `L^{-a}`, so the
grade-one value, its first derivative and its second derivative decay at the rates `L^{-1/2}`,
`L^{-3/2}`, `L^{-5/2}`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-! ## Weighted geometric summability -/

/-- A weight of at most quadratic growth is geometrically summable. -/
theorem summable_of_le_polyGeom {g : ℕ → ℝ} {C ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hg : ∀ k, |g k| ≤ C * ((k : ℝ) + 1) ^ 2) :
    Summable fun k : ℕ => |g k| * ρ ^ k := by
  have hnorm : ‖ρ‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hρ0]
  have h2 : Summable fun k : ℕ => (k : ℝ) ^ 2 * ρ ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hnorm
  have h1 : Summable fun k : ℕ => (k : ℝ) * ρ ^ k :=
    (summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).congr fun k => by rw [pow_one]
  have h0 : Summable fun k : ℕ => ρ ^ k := summable_geometric_of_lt_one hρ0 hρ1
  have hmaj : Summable fun k : ℕ => C * ((k : ℝ) + 1) ^ 2 * ρ ^ k := by
    refine (((h2.add (h1.mul_left 2)).add h0).mul_left C).congr fun k => ?_
    ring
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hmaj
  exact mul_le_mul_of_nonneg_right (hg k) (by positivity)

/-! ## The weighted half-power family -/

/-- The scalar weight of the `k`-th term of the half-power resolvent profile of exponent `a` and
coefficient weight `g`. -/
def resolventCoeffG (a : ℝ) (g : ℕ → ℝ) (k : ℕ) (L : ℝ) : ℝ :=
  normalizedCentralBinom k * (1 / 2 : ℝ) ^ k * g k * L ^ (-((k : ℝ) + a))

/-- The half-power resolvent profile of exponent `a` and coefficient weight `g`. -/
def resolventProfileG (T : A) (a : ℝ) (g : ℕ → ℝ) (L : ℝ) : A :=
  ∑' k : ℕ, resolventCoeffG a g k L • T ^ k

/-- **Differentiation shifts the exponent and inserts the factor `−(k+a)`.** -/
theorem hasDerivAt_resolventCoeffG (a : ℝ) (g : ℕ → ℝ) (k : ℕ) {L : ℝ} (hL : L ≠ 0) :
    HasDerivAt (resolventCoeffG a g k)
      (resolventCoeffG (a + 1) (fun j => -((j : ℝ) + a) * g j) k L) L := by
  have hbase : HasDerivAt (fun x : ℝ => x ^ (-((k : ℝ) + a)))
      ((-((k : ℝ) + a)) * L ^ (-((k : ℝ) + a) - 1)) L :=
    Real.hasDerivAt_rpow_const (Or.inl hL)
  have hmul := hbase.const_mul (normalizedCentralBinom k * (1 / 2 : ℝ) ^ k * g k)
  have hexp : -((k : ℝ) + (a + 1)) = -((k : ℝ) + a) - 1 := by ring
  have heq : normalizedCentralBinom k * (1 / 2 : ℝ) ^ k * g k *
      ((-((k : ℝ) + a)) * L ^ (-((k : ℝ) + a) - 1))
      = resolventCoeffG (a + 1) (fun j => -((j : ℝ) + a) * g j) k L := by
    rw [resolventCoeffG, hexp]
    ring
  rw [← heq]
  exact hmul

theorem rpow_neg_natCast {L : ℝ} (hL : 0 < L) (k : ℕ) : L ^ (-(k : ℝ)) = (L⁻¹) ^ k := by
  rw [Real.rpow_neg hL.le, Real.rpow_natCast, ← inv_pow]

/-! ## The uniform termwise bound on a terminal ray -/

omit [CompleteSpace A] in
/-- **The termwise bound at the evaluation point itself.**  The `k`-th term is at most
`|g k| (‖T‖/2L)^k L^{-a}`. -/
theorem norm_resolventTermG_le_self {T : A} {a L : ℝ} {g : ℕ → ℝ} (hL : 0 < L) (k : ℕ) :
    ‖resolventCoeffG a g k L • T ^ k‖ ≤ (|g k| * (‖T‖ / (2 * L)) ^ k) * L ^ (-a) := by
  have hcnn : 0 ≤ normalizedCentralBinom k := normalizedCentralBinom_nonneg k
  have hcle : normalizedCentralBinom k ≤ 1 := normalizedCentralBinom_le_one k
  have hsplit : L ^ (-((k : ℝ) + a)) = L ^ (-(k : ℝ)) * L ^ (-a) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have habs : |resolventCoeffG a g k L|
      = normalizedCentralBinom k * ((1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ))) * |g k| * L ^ (-a) := by
    rw [resolventCoeffG, hsplit, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hcnn, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k),
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hL.le _))]
    ring
  have hgeom : (1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ)) * ‖T‖ ^ k = (‖T‖ / (2 * L)) ^ k := by
    rw [rpow_neg_natCast hL k, ← mul_pow, ← mul_pow]
    congr 1
    field_simp
  have hcoeff : |resolventCoeffG a g k L|
      ≤ ((1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ))) * |g k| * L ^ (-a) := by
    rw [habs]
    have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ)) := by
      have := Real.rpow_nonneg hL.le (-(k : ℝ)); positivity
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
      (Real.rpow_nonneg hL.le _)
    calc normalizedCentralBinom k * ((1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ)))
        ≤ 1 * ((1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ))) := mul_le_mul_of_nonneg_right hcle hnn
      _ = (1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ)) := one_mul _
  calc ‖resolventCoeffG a g k L • T ^ k‖
      = |resolventCoeffG a g k L| * ‖T ^ k‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ (((1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ))) * |g k| * L ^ (-a)) * ‖T‖ ^ k :=
        mul_le_mul hcoeff (norm_pow_le T k) (norm_nonneg _) (by
          have := Real.rpow_nonneg hL.le (-(k : ℝ))
          have := Real.rpow_nonneg hL.le (-a)
          positivity)
    _ = (|g k| * ((1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ)) * ‖T‖ ^ k)) * L ^ (-a) := by ring
    _ = (|g k| * (‖T‖ / (2 * L)) ^ k) * L ^ (-a) := by rw [hgeom]

omit [CompleteSpace A] in
/-- **The uniform termwise bound on a terminal ray**, with a constant independent of the point. -/
theorem norm_resolventTermG_le {T : A} {a L₀ L : ℝ} {g : ℕ → ℝ} (ha : 0 ≤ a) (hL₀ : 0 < L₀)
    (hL : L₀ < L) (k : ℕ) :
    ‖resolventCoeffG a g k L • T ^ k‖ ≤ (|g k| * L₀ ^ (-a)) * (‖T‖ / (2 * L₀)) ^ k := by
  have hLpos : (0 : ℝ) < L := lt_trans hL₀ hL
  have hratio : ‖T‖ / (2 * L) ≤ ‖T‖ / (2 * L₀) :=
    div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by linarith)
  have hpow : (‖T‖ / (2 * L)) ^ k ≤ (‖T‖ / (2 * L₀)) ^ k :=
    pow_le_pow_left₀ (by positivity) hratio k
  have hexp : L ^ (-a) ≤ L₀ ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos hL₀ hL.le (neg_nonpos.mpr ha)
  calc ‖resolventCoeffG a g k L • T ^ k‖
      ≤ (|g k| * (‖T‖ / (2 * L)) ^ k) * L ^ (-a) := norm_resolventTermG_le_self hLpos k
    _ ≤ (|g k| * (‖T‖ / (2 * L₀)) ^ k) * L₀ ^ (-a) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)) hexp
          (Real.rpow_nonneg hLpos.le _) (by positivity)
    _ = (|g k| * L₀ ^ (-a)) * (‖T‖ / (2 * L₀)) ^ k := by ring

omit [NormOneClass A] [NormedAlgebra ℝ A] [CompleteSpace A] in
theorem summable_resolventMajorantG {T : A} {a L₀ : ℝ} {g : ℕ → ℝ}
    (hg : Summable fun k : ℕ => |g k| * (‖T‖ / (2 * L₀)) ^ k) :
    Summable fun k : ℕ => (|g k| * L₀ ^ (-a)) * (‖T‖ / (2 * L₀)) ^ k := by
  refine (hg.mul_right (L₀ ^ (-a))).congr fun k => ?_
  ring

/-- **The profile converges on the whole terminal ray.** -/
theorem summable_resolventTermG {T : A} {a L₀ L : ℝ} {g : ℕ → ℝ} (ha : 0 ≤ a) (hL₀ : 0 < L₀)
    (hL : L₀ < L) (hg : Summable fun k : ℕ => |g k| * (‖T‖ / (2 * L₀)) ^ k) :
    Summable fun k : ℕ => resolventCoeffG a g k L • T ^ k :=
  Summable.of_norm_bounded (summable_resolventMajorantG (a := a) hg)
    (fun k => norm_resolventTermG_le ha hL₀ hL k)

/-- **The profile is differentiable termwise on a terminal ray**, and its derivative is the member
of the same family with exponent `a+1` and weight `k ↦ −(k+a)·g k`. -/
theorem hasDerivAt_resolventProfileG {T : A} {a L₀ L : ℝ} {g : ℕ → ℝ} (ha : 0 ≤ a) (hL₀ : 0 < L₀)
    (hL : L ∈ Ioi L₀)
    (hg : Summable fun k : ℕ => |g k| * (‖T‖ / (2 * L₀)) ^ k)
    (hg' : Summable fun k : ℕ => |(-((k : ℝ) + a) * g k)| * (‖T‖ / (2 * L₀)) ^ k) :
    HasDerivAt (resolventProfileG T a g)
      (resolventProfileG T (a + 1) (fun j => -((j : ℝ) + a) * g j) L) L := by
  have hmem : (L₀ + 1) ∈ Ioi L₀ := by
    simp only [mem_Ioi]; linarith
  have ha1 : (0 : ℝ) ≤ a + 1 := by linarith
  exact hasDerivAt_tsum_of_isPreconnected
    (summable_resolventMajorantG (a := a + 1) hg') isOpen_Ioi
    ((convex_Ioi L₀).isPreconnected)
    (fun k y hy =>
      (hasDerivAt_resolventCoeffG a g k (ne_of_gt (lt_trans hL₀ hy))).smul_const (T ^ k))
    (fun k y hy => norm_resolventTermG_le ha1 hL₀ hy k) hmem
    (summable_resolventTermG ha hL₀ (by linarith : L₀ < L₀ + 1) hg) hL

/-! ## The closed form: a scaled weighted binomial series -/

/-- The binomial series with an extra coefficient weight. -/
def binomWeightedSeries (g : ℕ → ℝ) (S : A) : A :=
  ∑' k : ℕ, (g k * normalizedCentralBinom k) • S ^ k

omit [NormOneClass A] [CompleteSpace A] in
/-- **The closed form.**  The profile is `L^{-a}` times the weighted binomial series evaluated at
`T/(2L)`. -/
theorem resolventProfileG_eq (T : A) (a : ℝ) (g : ℕ → ℝ) {L : ℝ} (hL : 0 < L) :
    resolventProfileG T a g L = (L ^ (-a)) • binomWeightedSeries g ((1 / (2 * L)) • T) := by
  rw [resolventProfileG, binomWeightedSeries, ← tsum_const_smul'']
  refine tsum_congr fun k => ?_
  rw [smul_pow, smul_smul, smul_smul]
  congr 1
  have hsplit : L ^ (-((k : ℝ) + a)) = L ^ (-(k : ℝ)) * L ^ (-a) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hpow : (1 / (2 * L) : ℝ) ^ k = (1 / 2 : ℝ) ^ k * (L⁻¹) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [resolventCoeffG, hsplit, rpow_neg_natCast hL k, hpow]
  ring

/-! ## The three grades -/

/-- The weight of the value grade. -/
def gradeZeroWeight : ℕ → ℝ := fun _ => 1

/-- The weight of the first-derivative grade: `−(2k+1)/2`. -/
def gradeOneWeight : ℕ → ℝ := fun k => -((k : ℝ) + 1 / 2)

/-- The weight of the second-derivative grade: `(2k+1)(2k+3)/4`. -/
def gradeTwoWeight : ℕ → ℝ := fun k => ((k : ℝ) + 3 / 2) * ((k : ℝ) + 1 / 2)

theorem gradeOneWeight_eq (k : ℕ) : gradeOneWeight k = -((2 * (k : ℝ) + 1) / 2) := by
  rw [gradeOneWeight]; ring

theorem gradeTwoWeight_eq (k : ℕ) :
    gradeTwoWeight k = (2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 3) / 4 := by
  rw [gradeTwoWeight]; ring

theorem gradeZeroWeight_bound (k : ℕ) : |gradeZeroWeight k| ≤ 1 * ((k : ℝ) + 1) ^ 2 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [gradeZeroWeight, abs_one]
  nlinarith

theorem gradeOneWeight_bound (k : ℕ) : |gradeOneWeight k| ≤ 1 * ((k : ℝ) + 1) ^ 2 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [gradeOneWeight, abs_neg, abs_of_nonneg (by linarith)]
  nlinarith

theorem gradeTwoWeight_bound (k : ℕ) : |gradeTwoWeight k| ≤ 2 * ((k : ℝ) + 1) ^ 2 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [gradeTwoWeight, abs_of_nonneg (by nlinarith)]
  nlinarith

theorem gradeOneWeight_eq_deriv (k : ℕ) :
    -((k : ℝ) + 1 / 2) * gradeZeroWeight k = gradeOneWeight k := by
  rw [gradeZeroWeight, gradeOneWeight]; ring

theorem gradeTwoWeight_eq_deriv (k : ℕ) :
    -((k : ℝ) + 3 / 2) * gradeOneWeight k = gradeTwoWeight k := by
  rw [gradeOneWeight, gradeTwoWeight]; ring

/-! ## The first and second derivatives of the grade-one profile -/

variable {T : A} {L₀ L : ℝ}

/-- **The value profile has a first derivative given by the `−3/2` series.**  Its weight
`−(2k+1)/2` against the central binomials is exactly the coefficient sequence of `(1−s)^{-3/2}`. -/
theorem hasDerivAt_resolventProfile_gradeZero (hL₀ : 0 < L₀) (hT : ‖T‖ < 2 * L₀)
    (hL : L ∈ Ioi L₀) :
    HasDerivAt (resolventProfileG T (1 / 2) gradeZeroWeight)
      (resolventProfileG T (3 / 2) gradeOneWeight L) L := by
  have hρ0 : (0 : ℝ) ≤ ‖T‖ / (2 * L₀) := by positivity
  have hρ1 : ‖T‖ / (2 * L₀) < 1 := by
    rw [div_lt_one (by positivity)]; exact hT
  have h0 : Summable fun k : ℕ => |gradeZeroWeight k| * (‖T‖ / (2 * L₀)) ^ k :=
    summable_of_le_polyGeom hρ0 hρ1 gradeZeroWeight_bound
  have h1 : Summable fun k : ℕ =>
      |(-((k : ℝ) + 1 / 2) * gradeZeroWeight k)| * (‖T‖ / (2 * L₀)) ^ k := by
    refine (summable_of_le_polyGeom hρ0 hρ1 gradeOneWeight_bound).congr fun k => ?_
    rw [gradeOneWeight_eq_deriv]
  have hstep := hasDerivAt_resolventProfileG (T := T) (a := 1 / 2) (g := gradeZeroWeight)
    (by norm_num) hL₀ hL h0 h1
  have hfun : (fun j : ℕ => -((j : ℝ) + 1 / 2) * gradeZeroWeight j) = gradeOneWeight := by
    funext j; exact gradeOneWeight_eq_deriv j
  rw [hfun] at hstep
  have hexp : (1 : ℝ) / 2 + 1 = 3 / 2 := by norm_num
  rwa [hexp] at hstep

/-- **The first derivative has a second derivative given by the `−5/2` series.**  Its weight
`(2k+1)(2k+3)/4` against the central binomials is the coefficient sequence of `(1−s)^{-5/2}`. -/
theorem hasDerivAt_resolventProfile_gradeOne (hL₀ : 0 < L₀) (hT : ‖T‖ < 2 * L₀)
    (hL : L ∈ Ioi L₀) :
    HasDerivAt (resolventProfileG T (3 / 2) gradeOneWeight)
      (resolventProfileG T (5 / 2) gradeTwoWeight L) L := by
  have hρ0 : (0 : ℝ) ≤ ‖T‖ / (2 * L₀) := by positivity
  have hρ1 : ‖T‖ / (2 * L₀) < 1 := by
    rw [div_lt_one (by positivity)]; exact hT
  have h1 : Summable fun k : ℕ => |gradeOneWeight k| * (‖T‖ / (2 * L₀)) ^ k :=
    summable_of_le_polyGeom hρ0 hρ1 gradeOneWeight_bound
  have h2 : Summable fun k : ℕ =>
      |(-((k : ℝ) + 3 / 2) * gradeOneWeight k)| * (‖T‖ / (2 * L₀)) ^ k := by
    refine (summable_of_le_polyGeom hρ0 hρ1 gradeTwoWeight_bound).congr fun k => ?_
    rw [gradeTwoWeight_eq_deriv]
  have hstep := hasDerivAt_resolventProfileG (T := T) (a := 3 / 2) (g := gradeOneWeight)
    (by norm_num) hL₀ hL h1 h2
  have hfun : (fun j : ℕ => -((j : ℝ) + 3 / 2) * gradeOneWeight j) = gradeTwoWeight := by
    funext j; exact gradeTwoWeight_eq_deriv j
  rw [hfun] at hstep
  have hexp : (3 : ℝ) / 2 + 1 = 5 / 2 := by norm_num
  rwa [hexp] at hstep

/-! ## The decay rates -/

omit [CompleteSpace A] in
/-- **The decay rate.**  The profile of exponent `a` decays like `L^{-a}` on the terminal ray, with
the constant given by the weighted geometric series at the endpoint. -/
theorem norm_resolventProfileG_le {a : ℝ} {g : ℕ → ℝ} (hL₀ : 0 < L₀)
    (hL : L₀ < L) (hg : Summable fun k : ℕ => |g k| * (‖T‖ / (2 * L₀)) ^ k) :
    ‖resolventProfileG T a g L‖
      ≤ (∑' k : ℕ, |g k| * (‖T‖ / (2 * L₀)) ^ k) * L ^ (-a) := by
  have hLpos : (0 : ℝ) < L := lt_trans hL₀ hL
  have hratio : ‖T‖ / (2 * L) ≤ ‖T‖ / (2 * L₀) :=
    div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by linarith)
  have hterm : ∀ k : ℕ, ‖resolventCoeffG a g k L • T ^ k‖
      ≤ (|g k| * (‖T‖ / (2 * L₀)) ^ k) * L ^ (-a) := by
    intro k
    refine (norm_resolventTermG_le_self (a := a) (g := g) hLpos k).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
      (Real.rpow_nonneg hLpos.le _)
    exact pow_le_pow_left₀ (by positivity) hratio k
  have hmaj : Summable fun k : ℕ => (|g k| * (‖T‖ / (2 * L₀)) ^ k) * L ^ (-a) := hg.mul_right _
  have hnormsum : Summable fun k : ℕ => ‖resolventCoeffG a g k L • T ^ k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm hmaj
  calc ‖resolventProfileG T a g L‖
      ≤ ∑' k : ℕ, ‖resolventCoeffG a g k L • T ^ k‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' k : ℕ, (|g k| * (‖T‖ / (2 * L₀)) ^ k) * L ^ (-a) :=
        Summable.tsum_mono hnormsum hmaj hterm
    _ = (∑' k : ℕ, |g k| * (‖T‖ / (2 * L₀)) ^ k) * L ^ (-a) := tsum_mul_right

/-! ## The classical closed forms -/

/-- The `(1−s)^{-3/2}` binomial series: coefficients `(2k+1)·binom(2k,k)4^{-k}`. -/
def invPow32Series (S : A) : A :=
  ∑' k : ℕ, ((2 * (k : ℝ) + 1) * normalizedCentralBinom k) • S ^ k

/-- The `(1−s)^{-5/2}` binomial series: coefficients `(2k+1)(2k+3)/3·binom(2k,k)4^{-k}`. -/
def invPow52Series (S : A) : A :=
  ∑' k : ℕ, ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 3) / 3 * normalizedCentralBinom k) • S ^ k

omit [NormOneClass A] [CompleteSpace A] in
theorem binomWeightedSeries_const_smul (c : ℝ) (g : ℕ → ℝ) (S : A) :
    binomWeightedSeries (fun k => c * g k) S = c • binomWeightedSeries g S := by
  rw [binomWeightedSeries, binomWeightedSeries, ← tsum_const_smul'']
  refine tsum_congr fun k => ?_
  rw [smul_smul]
  congr 1
  ring

omit [NormOneClass A] [CompleteSpace A] in
theorem binomWeightedSeries_gradeOne (S : A) :
    binomWeightedSeries gradeOneWeight S = (-(1 / 2 : ℝ)) • invPow32Series S := by
  have hfun : gradeOneWeight = fun k : ℕ => (-(1 / 2 : ℝ)) * (2 * (k : ℝ) + 1) := by
    funext k
    rw [gradeOneWeight]
    ring
  rw [hfun, binomWeightedSeries_const_smul, invPow32Series, binomWeightedSeries]

omit [NormOneClass A] [CompleteSpace A] in
theorem binomWeightedSeries_gradeTwo (S : A) :
    binomWeightedSeries gradeTwoWeight S = (3 / 4 : ℝ) • invPow52Series S := by
  have hfun : gradeTwoWeight =
      fun k : ℕ => (3 / 4 : ℝ) * ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 3) / 3) := by
    funext k
    rw [gradeTwoWeight]
    ring
  rw [hfun, binomWeightedSeries_const_smul, invPow52Series, binomWeightedSeries]

variable {T : A} {L₀ L : ℝ}

omit [NormOneClass A] [CompleteSpace A] in
/-- **The first derivative in closed form.**  It is `−½ L^{-3/2}` times the `(1−s)^{-3/2}` series
at `s = T/(2L)`. -/
theorem resolventProfileG_gradeOne_eq (hL : 0 < L) :
    resolventProfileG T (3 / 2) gradeOneWeight L
      = (-(1 / 2 : ℝ) * L ^ (-(3 / 2 : ℝ))) • invPow32Series ((1 / (2 * L)) • T) := by
  rw [resolventProfileG_eq T (3 / 2) gradeOneWeight hL, binomWeightedSeries_gradeOne, smul_smul]
  congr 1
  ring

omit [NormOneClass A] [CompleteSpace A] in
/-- **The second derivative in closed form.**  It is `¾ L^{-5/2}` times the `(1−s)^{-5/2}` series
at `s = T/(2L)`. -/
theorem resolventProfileG_gradeTwo_eq (hL : 0 < L) :
    resolventProfileG T (5 / 2) gradeTwoWeight L
      = ((3 / 4 : ℝ) * L ^ (-(5 / 2 : ℝ))) • invPow52Series ((1 / (2 * L)) • T) := by
  rw [resolventProfileG_eq T (5 / 2) gradeTwoWeight hL, binomWeightedSeries_gradeTwo, smul_smul]
  congr 1
  ring

/-- **The value profile differentiates to the classical `−3/2` resolvent power.** -/
theorem hasDerivAt_resolventProfile_gradeZero_closedForm (hL₀ : 0 < L₀) (hT : ‖T‖ < 2 * L₀)
    (hL : L ∈ Ioi L₀) :
    HasDerivAt (resolventProfileG T (1 / 2) gradeZeroWeight)
      ((-(1 / 2 : ℝ) * L ^ (-(3 / 2 : ℝ))) • invPow32Series ((1 / (2 * L)) • T)) L := by
  have hLpos : (0 : ℝ) < L := lt_trans hL₀ hL
  rw [← resolventProfileG_gradeOne_eq (T := T) hLpos]
  exact hasDerivAt_resolventProfile_gradeZero hL₀ hT hL

/-- **The first derivative differentiates to the classical `−5/2` resolvent power.** -/
theorem hasDerivAt_resolventProfile_gradeOne_closedForm (hL₀ : 0 < L₀) (hT : ‖T‖ < 2 * L₀)
    (hL : L ∈ Ioi L₀) :
    HasDerivAt (resolventProfileG T (3 / 2) gradeOneWeight)
      (((3 / 4 : ℝ) * L ^ (-(5 / 2 : ℝ))) • invPow52Series ((1 / (2 * L)) • T)) L := by
  have hLpos : (0 : ℝ) < L := lt_trans hL₀ hL
  rw [← resolventProfileG_gradeTwo_eq (T := T) hLpos]
  exact hasDerivAt_resolventProfile_gradeOne hL₀ hT hL

/-! ## Square integrability on a terminal ray -/

omit [CompleteSpace A] in
/-- **A profile of exponent past the square-root threshold is square integrable on the terminal
ray.**  With exponents `3/2` and `5/2` this places the first and second derivatives of the
grade-one profile in `L²(L₀,∞)`, hence the profile in `H¹` there. -/
theorem lintegral_sq_resolventProfileG_ne_top {a : ℝ} {g : ℕ → ℝ} (ha : 1 / 2 < a) (hL₀ : 0 < L₀)
    (hg : Summable fun k : ℕ => |g k| * (‖T‖ / (2 * L₀)) ^ k) :
    (∫⁻ L in Ioi L₀, ‖resolventProfileG T a g L‖ₑ ^ 2) ≠ ⊤ :=
  lintegral_sq_powerTail_ne_top hL₀ ha
    (fun _ hL => norm_resolventProfileG_le hL₀ hL hg)

end GaloisForLFunctions.HTGeometry

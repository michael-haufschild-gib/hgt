import GaloisForLFunctions.HTGeometry.AlgebraicRootGrowth
import GaloisForLFunctions.HTGeometry.MvPolynomialGrowthBound
import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic
import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Proximity of an algebraic element

An element satisfying a polynomial relation with a nonvanishing top coefficient is bounded, on every
circle, by the normalised lower coefficients.  Averaging turns that pointwise estimate into a bound
on its Nevanlinna proximity function: an algebraic element cannot approach infinity faster than the
coefficients of its equation.

This is the value-distribution form of the algebraic root estimate, and it is the comparison a
composition-growth argument needs in the direction "algebraic over a field cannot outgrow it".
-/

open Real ValueDistribution

namespace GaloisForLFunctions.HTGeometry

/-- **The root estimate in additive form.**  A root of a monic-after-normalisation polynomial is
logarithmically bounded by the sum of the normalised lower coefficients. -/
theorem posLog_norm_le_of_root_sum {n : ℕ} (hn : 1 ≤ n) {g : ℂ} {c : ℕ → ℂ} (hcn : c n ≠ 0)
    (hrel : ∑ i ∈ Finset.range (n + 1), c i * g ^ i = 0) :
    Real.posLog ‖g‖ ≤ Real.log n + ∑ i ∈ Finset.range n, Real.posLog ‖c i / c n‖ := by
  refine le_trans (posLog_norm_le_of_root hn hcn hrel) ?_
  have hsum := Real.posLog_sum (Finset.range n) (fun i => ‖c i / c n‖)
  simpa using hsum

/-- **The proximity bound for an algebraic element.**  On a circle where the top coefficient does not
vanish, the proximity of a root is at most that of the normalised lower coefficients. -/
theorem proximity_le_of_root {n : ℕ} (hn : 1 ≤ n) {g : ℂ → ℂ} {a : ℕ → ℂ → ℂ} {r : ℝ}
    (hg : Meromorphic g) (ha : ∀ i, Meromorphic (a i))
    (hcirc : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, a n z ≠ 0)
    (hrel : ∀ z : ℂ, ∑ i ∈ Finset.range (n + 1), a i z * (g z) ^ i = 0) :
    proximity g ⊤ r
      ≤ Real.log n + ∑ i ∈ Finset.range n, proximity (fun z => a i z / a n z) ⊤ r := by
  classical
  have hquot : ∀ i, Meromorphic (fun z => a i z / a n z) := fun i => (ha i).div (ha n)
  have hgint : CircleIntegrable (Real.posLog ‖g ·‖) 0 r :=
    MeromorphicOn.circleIntegrable_posLog_norm (fun x _ => hg x)
  have hqint : ∀ i ∈ Finset.range n,
      CircleIntegrable (Real.posLog ‖(fun z => a i z / a n z) ·‖) 0 r :=
    fun i _ => MeromorphicOn.circleIntegrable_posLog_norm (fun x _ => hquot i x)
  have hbound : circleAverage (Real.posLog ‖g ·‖) 0 r
      ≤ circleAverage
          ((∑ i ∈ Finset.range n, Real.posLog ‖(fun z => a i z / a n z) ·‖)
            + fun _ => Real.log n) 0 r := by
    refine circleAverage_mono hgint
      ((CircleIntegrable.fun_sum (Finset.range n) hqint).add
        (circleIntegrable_const _ _ _)) ?_
    intro x hx
    simp only [Pi.add_apply]
    rw [add_comm]
    exact posLog_norm_le_of_root_sum hn (hcirc x hx) (hrel x)
  have hpi : (fun x : ℂ => ∑ i ∈ Finset.range n, Real.posLog ‖(fun z => a i z / a n z) x‖)
      = ∑ i ∈ Finset.range n, (fun x : ℂ => Real.posLog ‖(fun z => a i z / a n z) x‖) := by
    funext x
    rw [Finset.sum_apply]
  rw [hpi, circleAverage_add (CircleIntegrable.sum (Finset.range n) hqint)
    (circleIntegrable_const (Real.log n) 0 r), circleAverage_sum hqint,
    circleAverage_const] at hbound
  have hgoal : proximity g ⊤ r = circleAverage (Real.posLog ‖g ·‖) 0 r := by
    rw [proximity_top]
  have hgoal2 : ∀ i : ℕ, proximity (fun z => a i z / a n z) ⊤ r
      = circleAverage (Real.posLog ‖(fun z => a i z / a n z) ·‖) 0 r := by
    intro i
    rw [proximity_top]
  rw [hgoal, Finset.sum_congr rfl (fun i _ => hgoal2 i)]
  linarith [hbound]

/-- **The proximity bound in terms of the coefficients themselves.**  Splitting each normalised
coefficient into the coefficient and the reciprocal of the top one. -/
theorem proximity_le_of_root_coeff {n : ℕ} (hn : 1 ≤ n) {g : ℂ → ℂ} {a : ℕ → ℂ → ℂ} {r : ℝ}
    (hg : Meromorphic g) (ha : ∀ i, Meromorphic (a i))
    (hcirc : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, a n z ≠ 0)
    (hrel : ∀ z : ℂ, ∑ i ∈ Finset.range (n + 1), a i z * (g z) ^ i = 0) :
    proximity g ⊤ r
      ≤ Real.log n + ∑ i ∈ Finset.range n,
          (proximity (a i) ⊤ r + proximity (a n) 0 r) := by
  have hstep : ∑ i ∈ Finset.range n, proximity (fun z => a i z / a n z) ⊤ r
      ≤ ∑ i ∈ Finset.range n, (proximity (a i) ⊤ r + proximity (a n) 0 r) := by
    refine Finset.sum_le_sum ?_
    intro i _
    have hfun : (fun z => a i z / a n z) = (a i) * (a n)⁻¹ := by
      funext z
      rw [Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
    rw [hfun]
    have hmul := proximity_mul_top_le (ha i) (ha n).inv r
    rw [Pi.add_apply, proximity_inv] at hmul
    exact hmul
  linarith [proximity_le_of_root hn hg ha hcirc hrel, hstep]

/-! ## Proximity of a polynomial in a meromorphic function -/

/-- A two-variable polynomial in the coordinate and a meromorphic function is meromorphic. -/
theorem meromorphic_eval_mvPolynomial {f : ℂ → ℂ} (hf : Meromorphic f)
    (A : MvPolynomial (Fin 2) ℂ) :
    Meromorphic (fun z => MvPolynomial.eval ![z, f z] A) := by
  induction A using MvPolynomial.induction_on with
  | C a =>
      have hfun : (fun z : ℂ => MvPolynomial.eval ![z, f z] (MvPolynomial.C a))
          = fun _ : ℂ => a := by
        funext z
        simp
      rw [hfun]
      exact Meromorphic.const a
  | add p q hp hq =>
      have hfun : (fun z : ℂ => MvPolynomial.eval ![z, f z] (p + q))
          = fun z : ℂ => MvPolynomial.eval ![z, f z] p + MvPolynomial.eval ![z, f z] q := by
        funext z
        rw [map_add]
      rw [hfun]
      exact hp.fun_add hq
  | mul_X p i hp =>
      have hfun : (fun z : ℂ => MvPolynomial.eval ![z, f z] (p * MvPolynomial.X i))
          = fun z : ℂ => MvPolynomial.eval ![z, f z] p * (![z, f z] : Fin 2 → ℂ) i := by
        funext z
        rw [map_mul, MvPolynomial.eval_X]
      rw [hfun]
      refine hp.fun_mul ?_
      fin_cases i
      · exact fun x => (analyticAt_id (𝕜 := ℂ) (z := x)).meromorphicAt
      · exact hf

/-- **The proximity of a polynomial in a meromorphic function.**  Only the total degree and the
coefficient size enter. -/
theorem proximity_eval_mvPolynomial_le (A : MvPolynomial (Fin 2) ℂ) {f : ℂ → ℂ}
    (hf : Meromorphic f) (r : ℝ) :
    proximity (fun z => MvPolynomial.eval ![z, f z] A) ⊤ r
      ≤ (Real.posLog (mvCoeffNormSum A)
          + A.totalDegree * (Real.log 2 + Real.posLog |r|)
          + A.totalDegree * Real.log 2)
        + A.totalDegree * proximity f ⊤ r := by
  classical
  set d : ℕ := A.totalDegree with hd
  set K : ℝ := Real.posLog (mvCoeffNormSum A) + d * (Real.log 2 + Real.posLog |r|)
    + d * Real.log 2 with hK
  have hAf : Meromorphic (fun z => MvPolynomial.eval ![z, f z] A) :=
    meromorphic_eval_mvPolynomial hf A
  have hfint : CircleIntegrable (Real.posLog ‖f ·‖) 0 r :=
    MeromorphicOn.circleIntegrable_posLog_norm (fun x _ => hf x)
  have hAint : CircleIntegrable (Real.posLog ‖(fun z => MvPolynomial.eval ![z, f z] A) ·‖) 0 r :=
    MeromorphicOn.circleIntegrable_posLog_norm (fun x _ => hAf x)
  have hsumint : ∀ j ∈ Finset.range d, CircleIntegrable (Real.posLog ‖f ·‖) 0 r :=
    fun _ _ => hfint
  have hbound : circleAverage (Real.posLog ‖(fun z => MvPolynomial.eval ![z, f z] A) ·‖) 0 r
      ≤ circleAverage ((fun _ : ℂ => K) + ∑ _j ∈ Finset.range d, (Real.posLog ‖f ·‖)) 0 r := by
    refine circleAverage_mono hAint
      ((circleIntegrable_const _ _ _).add (CircleIntegrable.sum (Finset.range d) hsumint)) ?_
    intro x hx
    have hxn : ‖x‖ = |r| := mem_sphere_zero_iff_norm.mp hx
    have hpt := posLog_norm_eval_le A x (f x)
    rw [hxn] at hpt
    have hrw : ((fun _ : ℂ => K) + ∑ _j ∈ Finset.range d, (Real.posLog ‖f ·‖)) x
        = K + (d : ℝ) * Real.posLog ‖f x‖ := by
      simp [Finset.card_range, nsmul_eq_mul]
    rw [hrw, hK]
    rw [mul_add (a := (A.totalDegree : ℝ)) (b := Real.log 2)
      (c := Real.posLog ‖f x‖)] at hpt
    rw [hd]
    linarith [hpt]
  rw [circleAverage_add (circleIntegrable_const K 0 r)
    (CircleIntegrable.sum (Finset.range d) hsumint), circleAverage_const,
    circleAverage_sum hsumint, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hbound
  rw [proximity_top, proximity_top]
  exact hbound

/-! ## Entire functions have no poles to count -/

/-- **An entire function has vanishing pole-counting function.** -/
theorem logCounting_top_eq_zero_of_analyticOnNhd {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) :
    logCounting f ⊤ = 0 := by
  rw [logCounting_top, negPart_eq_zero.mpr (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf)]
  simp

/-- **For an entire function the characteristic is the proximity.** -/
theorem characteristic_top_eq_proximity_of_analyticOnNhd {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) :
    characteristic f ⊤ = proximity f ⊤ := by
  rw [characteristic, logCounting_top_eq_zero_of_analyticOnNhd hf, add_zero]

/-- **The coefficient bound with characteristics on both sides.**  For an entire `F`, the
characteristic of a polynomial in `(z, F)` is bounded by the total degree times that of `F`. -/
theorem characteristic_eval_mvPolynomial_le (A : MvPolynomial (Fin 2) ℂ) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (Set.univ : Set ℂ)) (r : ℝ) :
    characteristic (fun z => MvPolynomial.eval ![z, F z] A) ⊤ r
      ≤ (Real.posLog (mvCoeffNormSum A)
          + A.totalDegree * (Real.log 2 + Real.posLog |r|)
          + A.totalDegree * Real.log 2)
        + A.totalDegree * characteristic F ⊤ r := by
  have hAF : AnalyticOnNhd ℂ (fun z => MvPolynomial.eval ![z, F z] A) (Set.univ : Set ℂ) :=
    analyticOnNhd_eval_two hF A
  have hFm : Meromorphic F := fun x => (hF x (Set.mem_univ x)).meromorphicAt
  have hbase := proximity_eval_mvPolynomial_le A hFm r
  have hlhs : characteristic (fun z => MvPolynomial.eval ![z, F z] A) ⊤ r
      = proximity (fun z => MvPolynomial.eval ![z, F z] A) ⊤ r := by
    rw [characteristic_top_eq_proximity_of_analyticOnNhd hAF]
  have hrhs : characteristic F ⊤ r = proximity F ⊤ r := by
    rw [characteristic_top_eq_proximity_of_analyticOnNhd hF]
  rw [hlhs, hrhs]
  exact hbase

/-! ## In terms of the characteristic function -/

/-- The proximity function is at most the characteristic function on `[1, ∞)`. -/
theorem proximity_le_characteristic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {a : WithTop E} {r : ℝ} (hr : 1 ≤ r) :
    proximity f a r ≤ characteristic f a r := by
  have hdef : characteristic f a r = proximity f a r + logCounting f a r := rfl
  have hnn : 0 ≤ logCounting f a r := logCounting_nonneg hr
  rw [hdef]
  linarith

/-- **An algebraic element is bounded by the characteristics of its coefficients.** -/
theorem proximity_le_of_root_characteristic {n : ℕ} (hn : 1 ≤ n) {g : ℂ → ℂ} {a : ℕ → ℂ → ℂ}
    {r : ℝ} (hr : 1 ≤ r)
    (hg : Meromorphic g) (ha : ∀ i, Meromorphic (a i))
    (hcirc : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, a n z ≠ 0)
    (hrel : ∀ z : ℂ, ∑ i ∈ Finset.range (n + 1), a i z * (g z) ^ i = 0) :
    proximity g ⊤ r
      ≤ Real.log n + ∑ i ∈ Finset.range n,
          (characteristic (a i) ⊤ r + characteristic (a n) 0 r) := by
  have hstep : ∑ i ∈ Finset.range n, (proximity (a i) ⊤ r + proximity (a n) 0 r)
      ≤ ∑ i ∈ Finset.range n, (characteristic (a i) ⊤ r + characteristic (a n) 0 r) := by
    refine Finset.sum_le_sum ?_
    intro i _
    exact add_le_add (proximity_le_characteristic hr) (proximity_le_characteristic hr)
  linarith [proximity_le_of_root_coeff hn hg ha hcirc hrel, hstep]

/-- **The algebraic bound with every characteristic taken at infinity.**  The first main theorem
replaces the reciprocal's characteristic by that of the top coefficient itself, at the cost of the
explicit constant it supplies. -/
theorem proximity_le_of_root_characteristic_top {n : ℕ} (hn : 1 ≤ n) {g : ℂ → ℂ}
    {a : ℕ → ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r)
    (hg : Meromorphic g) (ha : ∀ i, Meromorphic (a i))
    (hcirc : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, a n z ≠ 0)
    (hrel : ∀ z : ℂ, ∑ i ∈ Finset.range (n + 1), a i z * (g z) ^ i = 0) :
    proximity g ⊤ r
      ≤ Real.log n + ∑ i ∈ Finset.range n,
          (characteristic (a i) ⊤ r + characteristic (a n) ⊤ r
            + max |Real.log ‖a n 0‖|
                |Real.log ‖meromorphicTrailingCoeffAt (a n) 0‖|) := by
  set C : ℝ := max |Real.log ‖a n 0‖|
    |Real.log ‖meromorphicTrailingCoeffAt (a n) 0‖| with hC
  have hFMT : characteristic (a n)⁻¹ ⊤ r ≤ characteristic (a n) ⊤ r + C := by
    have h := characteristic_sub_characteristic_inv_le (f := a n) (R := r) (ha n)
    rw [← hC] at h
    have h2 := abs_le.mp h
    linarith [h2.1]
  have hstep : ∑ i ∈ Finset.range n, (proximity (a i) ⊤ r + proximity (a n) 0 r)
      ≤ ∑ i ∈ Finset.range n,
          (characteristic (a i) ⊤ r + characteristic (a n) ⊤ r + C) := by
    refine Finset.sum_le_sum ?_
    intro i _
    have h1 : proximity (a i) ⊤ r ≤ characteristic (a i) ⊤ r :=
      proximity_le_characteristic hr
    have h2 : proximity (a n) 0 r ≤ characteristic (a n)⁻¹ ⊤ r := by
      rw [← proximity_inv]
      exact proximity_le_characteristic hr
    linarith [hFMT]
  linarith [proximity_le_of_root_coeff hn hg ha hcirc hrel, hstep]

/-! ## The composite: algebraic over `ℂ(z, F)` cannot outgrow `F` -/

/-- **An element algebraic over the field generated by an entire function grows no faster.**  The
constant depends only on the coefficient polynomials, not on the radius. -/
theorem exists_bound_proximity_of_two_var_relation {n : ℕ} (hn : 1 ≤ n)
    {g F : ℂ → ℂ} {A : ℕ → MvPolynomial (Fin 2) ℂ}
    (hg : Meromorphic g) (hF : AnalyticOnNhd ℂ F (Set.univ : Set ℂ)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ r : ℝ, 1 ≤ r →
      (∀ z ∈ Metric.sphere (0 : ℂ) |r|, MvPolynomial.eval ![z, F z] (A n) ≠ 0) →
      (∀ z : ℂ, ∑ i ∈ Finset.range (n + 1),
        MvPolynomial.eval ![z, F z] (A i) * (g z) ^ i = 0) →
      proximity g ⊤ r ≤ c * (1 + Real.posLog |r| + characteristic F ⊤ r) := by
  classical
  set a : ℕ → ℂ → ℂ := fun i z => MvPolynomial.eval ![z, F z] (A i) with hadef
  have haA : ∀ i, AnalyticOnNhd ℂ (a i) (Set.univ : Set ℂ) :=
    fun i => analyticOnNhd_eval_two hF (A i)
  have ham : ∀ i, Meromorphic (a i) := fun i x => (haA i x (Set.mem_univ x)).meromorphicAt
  set K : ℝ := ∑ i ∈ Finset.range (n + 1),
    (Real.posLog (mvCoeffNormSum (A i)) + 2 * (((A i).totalDegree : ℝ) * Real.log 2)) with hK
  set D : ℝ := ∑ i ∈ Finset.range (n + 1), ((A i).totalDegree : ℝ) with hD
  set Cn : ℝ := max |Real.log ‖a n 0‖|
    |Real.log ‖meromorphicTrailingCoeffAt (a n) 0‖| with hCn
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  refine ⟨max (Real.log n + 2 * n * K + n * Cn) (2 * n * D), ?_, ?_⟩
  · refine le_max_of_le_right ?_
    positivity
  · intro r hr hcirc hrel
    have hTF : 0 ≤ characteristic F ⊤ r := characteristic_nonneg hr
    have hposr : (0 : ℝ) ≤ Real.posLog |r| := Real.posLog_nonneg
    have hcoef : ∀ i, i ≤ n → characteristic (a i) ⊤ r
        ≤ K + D * Real.posLog |r| + D * characteristic F ⊤ r := by
      intro i hi
      have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      have hbase := characteristic_eval_mvPolynomial_le (A i) hF r
      rw [mul_add] at hbase
      have h1 : Real.posLog (mvCoeffNormSum (A i))
          + 2 * (((A i).totalDegree : ℝ) * Real.log 2) ≤ K := by
        rw [hK]
        refine Finset.single_le_sum
          (f := fun j => Real.posLog (mvCoeffNormSum (A j))
            + 2 * (((A j).totalDegree : ℝ) * Real.log 2)) (fun j _ => ?_) hmem
        have hp : (0 : ℝ) ≤ Real.posLog (mvCoeffNormSum (A j)) := Real.posLog_nonneg
        positivity
      have h2 : ((A i).totalDegree : ℝ) ≤ D := by
        rw [hD]
        exact Finset.single_le_sum (f := fun j => ((A j).totalDegree : ℝ))
          (fun j _ => Nat.cast_nonneg _) hmem
      have h3 : ((A i).totalDegree : ℝ) * Real.posLog |r| ≤ D * Real.posLog |r| :=
        mul_le_mul_of_nonneg_right h2 hposr
      have h4 : ((A i).totalDegree : ℝ) * characteristic F ⊤ r
          ≤ D * characteristic F ⊤ r := mul_le_mul_of_nonneg_right h2 hTF
      linarith [hbase, h1, h3, h4]
    have hmain := proximity_le_of_root_characteristic_top hn hr hg ham hcirc hrel
    rw [← hCn] at hmain
    have hsum : ∑ i ∈ Finset.range n,
        (characteristic (a i) ⊤ r + characteristic (a n) ⊤ r + Cn)
        ≤ ∑ _i ∈ Finset.range n,
            (2 * (K + D * Real.posLog |r| + D * characteristic F ⊤ r) + Cn) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hi' : i ≤ n := by
        have := Finset.mem_range.mp hi
        omega
      linarith [hcoef i hi', hcoef n (le_refl n)]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hexp2 : (n : ℝ) * (2 * (K + D * Real.posLog |r| + D * characteristic F ⊤ r) + Cn)
        = 2 * n * K + 2 * n * D * Real.posLog |r|
          + 2 * n * D * characteristic F ⊤ r + n * Cn := by ring
    have hc1 : Real.log n + 2 * n * K + n * Cn
        ≤ max (Real.log n + 2 * n * K + n * Cn) (2 * n * D) := le_max_left _ _
    have hc2 : 2 * n * D ≤ max (Real.log n + 2 * n * K + n * Cn) (2 * n * D) := le_max_right _ _
    have hP : 2 * n * D * Real.posLog |r|
        ≤ max (Real.log n + 2 * n * K + n * Cn) (2 * n * D) * Real.posLog |r| :=
      mul_le_mul_of_nonneg_right hc2 hposr
    have hT : 2 * n * D * characteristic F ⊤ r
        ≤ max (Real.log n + 2 * n * K + n * Cn) (2 * n * D) * characteristic F ⊤ r :=
      mul_le_mul_of_nonneg_right hc2 hTF
    have hexp : max (Real.log n + 2 * n * K + n * Cn) (2 * n * D)
        * (1 + Real.posLog |r| + characteristic F ⊤ r)
        = max (Real.log n + 2 * n * K + n * Cn) (2 * n * D)
          + max (Real.log n + 2 * n * K + n * Cn) (2 * n * D) * Real.posLog |r|
          + max (Real.log n + 2 * n * K + n * Cn) (2 * n * D) * characteristic F ⊤ r := by
      ring
    rw [hexp2] at hsum
    rw [hexp]
    linarith [hmain, hsum, hc1, hP, hT]

/-! ## Comparison with the maximum modulus -/

/-- **The characteristic is at most the logarithm of the maximum modulus.**  For an entire function
the characteristic is a circle average of `log⁺‖f‖`, hence bounded by any bound on the circle. -/
theorem characteristic_le_posLog_of_forall_sphere {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) {r M : ℝ}
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, ‖f z‖ ≤ M) :
    characteristic f ⊤ r ≤ Real.posLog M := by
  have hfm : Meromorphic f := fun x => (hf x (Set.mem_univ x)).meromorphicAt
  have hint : CircleIntegrable (Real.posLog ‖f ·‖) 0 r :=
    MeromorphicOn.circleIntegrable_posLog_norm (fun x _ => hfm x)
  have hbound : circleAverage (Real.posLog ‖f ·‖) 0 r
      ≤ circleAverage (fun _ : ℂ => Real.posLog M) 0 r := by
    refine circleAverage_mono hint (circleIntegrable_const _ _ _) ?_
    intro x hx
    exact Real.monotoneOn_posLog (Set.mem_Ici.mpr (norm_nonneg _))
      (Set.mem_Ici.mpr (le_trans (norm_nonneg _) (hM x hx))) (hM x hx)
  rw [circleAverage_const] at hbound
  rw [characteristic_top_eq_proximity_of_analyticOnNhd hf, proximity_top]
  exact hbound

/-! ## The pointwise form with an explicit floor

The composition-growth results of the corpus are pointwise: they produce a single point at which the
composition outgrows a prescribed multiple of the inner function.  The algebraic estimate has to be
available at that same point, which means the top coefficient must be bounded below there — a floor,
not a nonvanishing hypothesis. -/

/-- **The root estimate under a floor on the top coefficient.** -/
theorem posLog_norm_le_of_root_floor {n : ℕ} (hn : 1 ≤ n) {g : ℂ} {c : ℕ → ℂ} {ε : ℝ}
    (hε : 0 < ε) (hfloor : ε ≤ ‖c n‖)
    (hrel : ∑ i ∈ Finset.range (n + 1), c i * g ^ i = 0) :
    Real.posLog ‖g‖
      ≤ Real.log n + ∑ i ∈ Finset.range n,
          (Real.posLog ‖c i‖ + Real.posLog ε⁻¹) := by
  have hcn : c n ≠ 0 := by
    intro h
    rw [h, norm_zero] at hfloor
    linarith
  have hcn0 : 0 < ‖c n‖ := lt_of_lt_of_le hε hfloor
  have hstep : ∑ i ∈ Finset.range n, Real.posLog ‖c i / c n‖
      ≤ ∑ i ∈ Finset.range n, (Real.posLog ‖c i‖ + Real.posLog ε⁻¹) := by
    refine Finset.sum_le_sum ?_
    intro i _
    have hnorm : ‖c i / c n‖ = ‖c i‖ * ‖c n‖⁻¹ := by
      rw [norm_div, div_eq_mul_inv]
    have hinv : ‖c n‖⁻¹ ≤ ε⁻¹ := by
      exact inv_anti₀ hε hfloor
    have hinvpos : (0 : ℝ) ≤ ‖c n‖⁻¹ := by positivity
    have hmono : Real.posLog ‖c n‖⁻¹ ≤ Real.posLog ε⁻¹ :=
      Real.monotoneOn_posLog (Set.mem_Ici.mpr hinvpos)
        (Set.mem_Ici.mpr (by positivity)) hinv
    rw [hnorm]
    exact le_trans Real.posLog_mul (by linarith [hmono])
  linarith [posLog_norm_le_of_root_sum hn hcn hrel, hstep]

/-- **The pointwise algebraic bound, in the shape the separation contradicts.**  An element
satisfying a two-variable relation over `(z, G)` with a floor `ε` on the top coefficient is bounded
by a fixed multiple of `1 + log⁺‖z‖ + log⁺‖G z‖ + log⁺ε⁻¹`.  The constant depends only on the
coefficient polynomials. -/
theorem exists_bound_posLog_of_two_var_relation {D : ℕ} (hD : 1 ≤ D)
    {G : ℂ → ℂ} {A : ℕ → MvPolynomial (Fin 2) ℂ} :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (g : ℂ → ℂ) (z : ℂ) (ε : ℝ), 0 < ε →
      ε ≤ ‖MvPolynomial.eval ![z, G z] (A D)‖ →
      (∑ i ∈ Finset.range (D + 1),
        MvPolynomial.eval ![z, G z] (A i) * (g z) ^ i = 0) →
      Real.posLog ‖g z‖
        ≤ c * (1 + Real.posLog ‖z‖ + Real.posLog ‖G z‖ + Real.posLog ε⁻¹) := by
  classical
  set K : ℝ := ∑ i ∈ Finset.range D, Real.posLog (mvCoeffNormSum (A i)) with hK
  set Dg : ℝ := ∑ i ∈ Finset.range D, ((A i).totalDegree : ℝ) with hDg
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Real.posLog_nonneg
  have hDg0 : 0 ≤ Dg := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hDpos : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  refine ⟨max (max (Real.log D + D * K + 2 * D * Dg * Real.log 2) (D * Dg)) D, ?_, ?_⟩
  · exact le_trans hDpos (le_max_right _ _)
  · intro g z ε hε hfloor hrel
    have hz0 : (0 : ℝ) ≤ Real.posLog ‖z‖ := Real.posLog_nonneg
    have hGz0 : (0 : ℝ) ≤ Real.posLog ‖G z‖ := Real.posLog_nonneg
    have hε0 : (0 : ℝ) ≤ Real.posLog ε⁻¹ := Real.posLog_nonneg
    have hbase := posLog_norm_le_of_root_floor hD hε hfloor hrel
    have hterm : ∀ i ∈ Finset.range D,
        Real.posLog ‖MvPolynomial.eval ![z, G z] (A i)‖ + Real.posLog ε⁻¹
        ≤ (K + Dg * (Real.log 2 + Real.posLog ‖z‖)
            + Dg * (Real.log 2 + Real.posLog ‖G z‖)) + Real.posLog ε⁻¹ := by
      intro i hi
      have h0 := posLog_norm_eval_le (A i) z (G z)
      have h1 : Real.posLog (mvCoeffNormSum (A i)) ≤ K := by
        rw [hK]
        exact Finset.single_le_sum
          (f := fun j => Real.posLog (mvCoeffNormSum (A j)))
          (fun _ _ => Real.posLog_nonneg) hi
      have h2 : ((A i).totalDegree : ℝ) ≤ Dg := by
        rw [hDg]
        exact Finset.single_le_sum (f := fun j => ((A j).totalDegree : ℝ))
          (fun _ _ => Nat.cast_nonneg _) hi
      have h3 : ((A i).totalDegree : ℝ) * (Real.log 2 + Real.posLog ‖z‖)
          ≤ Dg * (Real.log 2 + Real.posLog ‖z‖) :=
        mul_le_mul_of_nonneg_right h2 (by linarith)
      have h4 : ((A i).totalDegree : ℝ) * (Real.log 2 + Real.posLog ‖G z‖)
          ≤ Dg * (Real.log 2 + Real.posLog ‖G z‖) :=
        mul_le_mul_of_nonneg_right h2 (by linarith)
      linarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hexp : (D : ℝ) * ((K + Dg * (Real.log 2 + Real.posLog ‖z‖)
          + Dg * (Real.log 2 + Real.posLog ‖G z‖)) + Real.posLog ε⁻¹)
        = (D * K + 2 * D * Dg * Real.log 2) + D * Dg * Real.posLog ‖z‖
          + D * Dg * Real.posLog ‖G z‖ + D * Real.posLog ε⁻¹ := by ring
    rw [hexp] at hsum
    set c : ℝ := max (max (Real.log D + D * K + 2 * D * Dg * Real.log 2) (D * Dg)) D with hc
    have hc1 : Real.log D + D * K + 2 * D * Dg * Real.log 2 ≤ c :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    have hc2 : D * Dg ≤ c := le_trans (le_max_right _ _) (le_max_left _ _)
    have hc3 : (D : ℝ) ≤ c := le_max_right _ _
    have hp1 : D * Dg * Real.posLog ‖z‖ ≤ c * Real.posLog ‖z‖ :=
      mul_le_mul_of_nonneg_right hc2 hz0
    have hp2 : D * Dg * Real.posLog ‖G z‖ ≤ c * Real.posLog ‖G z‖ :=
      mul_le_mul_of_nonneg_right hc2 hGz0
    have hp3 : (D : ℝ) * Real.posLog ε⁻¹ ≤ c * Real.posLog ε⁻¹ :=
      mul_le_mul_of_nonneg_right hc3 hε0
    have hgoal : c * (1 + Real.posLog ‖z‖ + Real.posLog ‖G z‖ + Real.posLog ε⁻¹)
        = c + c * Real.posLog ‖z‖ + c * Real.posLog ‖G z‖ + c * Real.posLog ε⁻¹ := by ring
    rw [hgoal]
    linarith [hbase, hsum, hc1, hp1, hp2, hp3]

/-- **The separation forbids an algebraic relation.**  If for every level `c` there is a point at
which the top coefficient is bounded below and `g` outgrows `c` times the joint scale of the point
and of `G`, then `g` satisfies no two-variable polynomial relation over `(z, G)` of degree `D`. -/
theorem not_two_var_relation_of_separation {D : ℕ} (hD : 1 ≤ D)
    {G g : ℂ → ℂ} {A : ℕ → MvPolynomial (Fin 2) ℂ}
    (hsel : ∀ c : ℝ, 0 ≤ c → ∃ (z : ℂ) (ε : ℝ), 0 < ε ∧
      ε ≤ ‖MvPolynomial.eval ![z, G z] (A D)‖ ∧
      c * (1 + Real.posLog ‖z‖ + Real.posLog ‖G z‖ + Real.posLog ε⁻¹)
        < Real.posLog ‖g z‖) :
    ¬ (∀ z : ℂ, ∑ i ∈ Finset.range (D + 1),
        MvPolynomial.eval ![z, G z] (A i) * (g z) ^ i = 0) := by
  intro hrel
  obtain ⟨c, hc0, hbound⟩ :=
    exists_bound_posLog_of_two_var_relation (D := D) (G := G) (A := A) hD
  obtain ⟨z, ε, hε, hfloor, hsep⟩ := hsel c hc0
  exact absurd (hbound g z ε hε hfloor (hrel z)) (not_le.mpr hsep)

end GaloisForLFunctions.HTGeometry

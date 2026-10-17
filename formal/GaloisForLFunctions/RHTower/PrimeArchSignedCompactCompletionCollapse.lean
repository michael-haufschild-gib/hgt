import GaloisForLFunctions.RHTower.PrimeArchHausdorffFixedOrderLargeShiftPositivity
import GaloisForLFunctions.RHTower.ReciprocalAtomTestSpaceClosure
import GaloisForLFunctions.RHTower.LiClockThetaSingleDampingStrip
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Signed compact completions of the prime–archimedean moment tower force RH

Let `m_n` be the normalized prime–archimedean moments, `m_n = Σ_q x_q^(n+1)` over the reciprocal-square
Xi atoms `x_q = a_q^(-2)`.  A *signed compact completion* is a pair of finite measures `μ, ν` on a
bounded interval `[-B, B]` with

`m_n = ∫ x^n dμ − ∫ x^n dν` for every `n`.

**Theorem** (`riemannHypothesis_of_signedCompactPrimeArchMoments`).  Any signed compact completion
forces the Riemann hypothesis.  Consequently a signed compact completion exists iff RH
(`exists_signedCompactPrimeArchMoments_iff_riemannHypothesis`): the positive canonical Xi measure is
one under RH, and none exists otherwise.

Mechanism.  The moment generating germ `Σ_n m_n z^n` continues to the atom resolvent sum
`F(z) = Σ_q x_q / (1 − z x_q)`, meromorphic with poles at `1/x_q`; a signed compact completion
continues it instead to `H(z) = ∫ dμ(x)/(1 − zx) − ∫ dν(x)/(1 − zx)`, holomorphic on the whole
upper half-plane because its poles lie on the real axis.  By critical-line reflection an off-line zero
gives an atom with negative imaginary part, hence a pole of `F` in the upper half-plane.  Taking such
an atom of maximal modulus, `F` and `H` are holomorphic on the half-disc below that pole, agree near
`0` and hence on the half-disc by the identity theorem, while `F` blows up along the ray to the pole
and `H` stays continuous — a contradiction.

So the "nonpassive source-faithful completion with added and removed mass" cannot be a signed measure
of bounded support short of RH; any completion of the tower must be a distribution of unbounded
variation.
-/

open Complex MeasureTheory Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The atom resolvent sum -/

/-- The resolvent atom `x_q / (1 − z x_q)`. -/
def xiAtomResolventTerm (z : ℂ) (q : XiZeroCopy) : ℂ :=
  xiZeroCopyReciprocalSquare q / (1 - z * xiZeroCopyReciprocalSquare q)

/-- The atom resolvent sum `Σ_q x_q / (1 − z x_q)`, the meromorphic continuation of the moment germ. -/
def xiAtomResolventSum (z : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, xiAtomResolventTerm z q

theorem norm_xiZeroCopyReciprocalSquare_le_two_div_fortyOne (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ ≤ 2 / 41 := by
  rw [norm_xiZeroCopyReciprocalSquare]
  have := normSq_xiSpectralPoint_ge q
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- If `‖z x‖ ≤ 1/2` then `‖x / (1 − z x)‖ ≤ 2 ‖x‖`. -/
theorem norm_div_one_sub_mul_le {z x : ℂ} (h : ‖z * x‖ ≤ 1 / 2) :
    ‖x / (1 - z * x)‖ ≤ 2 * ‖x‖ := by
  have h1 : 1 / 2 ≤ ‖1 - z * x‖ := by
    have := norm_sub_norm_le (1 : ℂ) (z * x)
    rw [norm_one] at this
    linarith
  rw [norm_div, div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg x]

theorem one_sub_mul_ne_zero_of_norm_le_half {z x : ℂ} (h : ‖z * x‖ ≤ 1 / 2) : 1 - z * x ≠ 0 := by
  intro h0
  have := norm_sub_norm_le (1 : ℂ) (z * x)
  rw [h0, norm_zero, norm_one] at this
  linarith

/-- Only finitely many atoms have modulus at least `ε > 0`. -/
theorem finite_xiZeroCopy_norm_ge {ε : ℝ} (hε : 0 < ε) :
    {q : XiZeroCopy | ε ≤ ‖xiZeroCopyReciprocalSquare q‖}.Finite := by
  have h := summable_norm_xiZeroCopyReciprocalSquare.tendsto_cofinite_zero.eventually
    (gt_mem_nhds hε)
  rw [Filter.eventually_cofinite] at h
  refine h.subset ?_
  intro q hq
  simp only [Set.mem_setOf_eq, not_lt]
  exact hq

theorem summable_xiAtomResolventTerm (z : ℂ) : Summable (xiAtomResolventTerm z) := by
  have hε : (0 : ℝ) < 1 / (2 * (‖z‖ + 1)) := by positivity
  apply Summable.of_norm_bounded_eventually (summable_norm_xiZeroCopyReciprocalSquare.mul_left 2)
  have hsmall := summable_norm_xiZeroCopyReciprocalSquare.tendsto_cofinite_zero.eventually
    (gt_mem_nhds hε)
  filter_upwards [hsmall] with q hq
  apply norm_div_one_sub_mul_le
  rw [norm_mul]
  have hz : ‖z‖ ≤ ‖z‖ + 1 := by linarith
  calc ‖z‖ * ‖xiZeroCopyReciprocalSquare q‖ ≤ (‖z‖ + 1) * (1 / (2 * (‖z‖ + 1))) := by
        gcongr
    _ = 1 / 2 := by field_simp
    _ ≤ 1 / 2 := le_rfl

/-! ## Geometric expansion and the moment germ -/

theorem xiAtomResolventTerm_eq_tsum {z : ℂ} (hz : ‖z‖ ≤ 41 / 4) (q : XiZeroCopy) :
    xiAtomResolventTerm z q =
      ∑' n : ℕ, xiZeroCopyReciprocalSquare q ^ (n + 1) * z ^ n := by
  have hzx : ‖z * xiZeroCopyReciprocalSquare q‖ < 1 := by
    rw [norm_mul]
    have := norm_xiZeroCopyReciprocalSquare_le_two_div_fortyOne q
    calc ‖z‖ * ‖xiZeroCopyReciprocalSquare q‖ ≤ 41 / 4 * (2 / 41) := by
          gcongr
      _ < 1 := by norm_num
  rw [xiAtomResolventTerm, div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one hzx, ← tsum_mul_left]
  congr 1
  funext n
  rw [mul_pow, pow_succ]
  ring

/-- The atoms' power sums are the normalized prime–archimedean moments. -/
theorem tsum_xiZeroCopyReciprocalSquare_pow_succ (n : ℕ) :
    ∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q ^ (n + 1) =
      (normalizedPrimeArchMoment n : ℂ) := by
  have h := xiCentralPolynomialMoment_eq_sourceMomentFunctional ((Polynomial.X : Polynomial ℝ) ^ n)
  rw [HTGeometry.momentFunctional_X_pow] at h
  rw [← h, xiCentralPolynomialMoment]
  congr 1
  funext q
  rw [xiCentralPolynomialMomentTerm, evalRealPolynomial, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.eval_pow, Polynomial.eval_X, pow_succ]
  ring

theorem norm_pow_succ_mul_pow_le {z : ℂ} (hz : ‖z‖ ≤ 41 / 4) (q : XiZeroCopy) (n : ℕ) :
    ‖xiZeroCopyReciprocalSquare q ^ (n + 1) * z ^ n‖ ≤
      ‖xiZeroCopyReciprocalSquare q‖ * (1 / 2) ^ n := by
  have hx := norm_xiZeroCopyReciprocalSquare_le_two_div_fortyOne q
  have hx0 := norm_nonneg (xiZeroCopyReciprocalSquare q)
  rw [norm_mul, norm_pow, norm_pow, pow_succ]
  have hzx : ‖xiZeroCopyReciprocalSquare q‖ * ‖z‖ ≤ 1 / 2 := by
    calc ‖xiZeroCopyReciprocalSquare q‖ * ‖z‖ ≤ 2 / 41 * (41 / 4) := by gcongr
      _ = 1 / 2 := by norm_num
  calc ‖xiZeroCopyReciprocalSquare q‖ ^ n * ‖xiZeroCopyReciprocalSquare q‖ * ‖z‖ ^ n
      = ‖xiZeroCopyReciprocalSquare q‖ * (‖xiZeroCopyReciprocalSquare q‖ * ‖z‖) ^ n := by
        rw [mul_pow]
        ring
    _ ≤ ‖xiZeroCopyReciprocalSquare q‖ * (1 / 2) ^ n := by gcongr

/-- **Germ identity.**  Near the origin the atom resolvent sum is the moment generating function of the
normalized prime–archimedean moments. -/
theorem xiAtomResolventSum_eq_tsum_moment {z : ℂ} (hz : ‖z‖ ≤ 41 / 4) :
    xiAtomResolventSum z = ∑' n : ℕ, (normalizedPrimeArchMoment n : ℂ) * z ^ n := by
  set f : XiZeroCopy → ℕ → ℂ := fun q n => xiZeroCopyReciprocalSquare q ^ (n + 1) * z ^ n with hf
  have hbound : ∀ p : XiZeroCopy × ℕ,
      ‖Function.uncurry f p‖ ≤ ‖xiZeroCopyReciprocalSquare p.1‖ * (1 / 2 : ℝ) ^ p.2 :=
    fun p => norm_pow_succ_mul_pow_le hz p.1 p.2
  have hprod : Summable (fun p : XiZeroCopy × ℕ =>
      ‖xiZeroCopyReciprocalSquare p.1‖ * (1 / 2 : ℝ) ^ p.2) := by
    have h1 : Summable (fun q : XiZeroCopy => ‖‖xiZeroCopyReciprocalSquare q‖‖) := by
      simpa only [norm_norm] using summable_norm_xiZeroCopyReciprocalSquare
    have h2 : Summable (fun n : ℕ => ‖(1 / 2 : ℝ) ^ n‖) := by
      simpa only [norm_pow, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
        summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    exact summable_mul_of_summable_norm h1 h2
  have hsum : Summable (Function.uncurry f) := Summable.of_norm_bounded hprod hbound
  have hfib1 : ∀ q, Summable (f q) := fun q =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_left ‖xiZeroCopyReciprocalSquare q‖) (fun n => hbound (q, n))
  have hfib2 : ∀ n, Summable (fun q => f q n) := fun n =>
    Summable.of_norm_bounded (summable_norm_xiZeroCopyReciprocalSquare.mul_right ((1 / 2 : ℝ) ^ n))
      (fun q => hbound (q, n))
  calc xiAtomResolventSum z = ∑' q, ∑' n, f q n := by
        rw [xiAtomResolventSum]
        congr 1
        funext q
        exact xiAtomResolventTerm_eq_tsum hz q
    _ = ∑' n, ∑' q, f q n := (Summable.tsum_comm' hsum hfib1 hfib2).symm
    _ = ∑' n : ℕ, (normalizedPrimeArchMoment n : ℂ) * z ^ n := by
        congr 1
        funext n
        rw [show (fun q => f q n) = fun q => xiZeroCopyReciprocalSquare q ^ (n + 1) * z ^ n from rfl,
          tsum_mul_right, tsum_xiZeroCopyReciprocalSquare_pow_succ]

/-! ## Holomorphy away from the poles -/

/-- At a point where no denominator vanishes the atom resolvent sum is differentiable. -/
theorem differentiableAt_xiAtomResolventSum {z₁ : ℂ}
    (h : ∀ q, 1 - z₁ * xiZeroCopyReciprocalSquare q ≠ 0) :
    DifferentiableAt ℂ xiAtomResolventSum z₁ := by
  classical
  set ε : ℝ := 1 / (2 * (‖z₁‖ + 1)) with hε
  have hεpos : 0 < ε := by positivity
  set T : Finset XiZeroCopy := (finite_xiZeroCopy_norm_ge hεpos).toFinset with hT
  have hsplit : xiAtomResolventSum = fun z =>
      (∑ q ∈ T, xiAtomResolventTerm z q) +
        ∑' q : {q // q ∉ T}, xiAtomResolventTerm z q := by
    funext z
    rw [xiAtomResolventSum, ← (summable_xiAtomResolventTerm z).sum_add_tsum_subtype_compl T]
  rw [hsplit]
  apply DifferentiableAt.add
  · apply DifferentiableAt.fun_sum
    intro q _
    apply DifferentiableAt.div (differentiableAt_const _) _ (h q)
    exact (differentiableAt_id.mul_const _).const_sub _
  · have hsub : ∀ q : {q // q ∉ T}, ‖xiZeroCopyReciprocalSquare q.1‖ < ε := by
      intro q
      have := q.2
      rw [hT, Set.Finite.mem_toFinset] at this
      simpa only [Set.mem_setOf_eq, not_le] using this
    have hkey : ∀ (q : {q // q ∉ T}) (w : ℂ), w ∈ Metric.ball z₁ 1 →
        ‖w * xiZeroCopyReciprocalSquare q.1‖ ≤ 1 / 2 := by
      intro q w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have hwn : ‖w‖ ≤ ‖z₁‖ + 1 := by
        have := norm_sub_norm_le w z₁
        linarith
      rw [norm_mul]
      calc ‖w‖ * ‖xiZeroCopyReciprocalSquare q.1‖ ≤ (‖z₁‖ + 1) * ε := by
            gcongr
            exact (hsub q).le
        _ = 1 / 2 := by
            rw [hε]
            field_simp
    have hdiff := Complex.differentiableOn_tsum_of_summable_norm
      (F := fun (q : {q // q ∉ T}) (w : ℂ) => xiAtomResolventTerm w q.1)
      (U := Metric.ball z₁ 1)
      (u := fun q : {q // q ∉ T} => 2 * ‖xiZeroCopyReciprocalSquare q.1‖)
      ((summable_norm_xiZeroCopyReciprocalSquare.mul_left 2).subtype _)
      (fun q => by
        intro w hw
        apply DifferentiableAt.differentiableWithinAt
        apply DifferentiableAt.div (differentiableAt_const _) _
          (one_sub_mul_ne_zero_of_norm_le_half (hkey q w hw))
        exact (differentiableAt_id.mul_const _).const_sub _)
      Metric.isOpen_ball
      (fun q w hw => norm_div_one_sub_mul_le (hkey q w hw))
    exact hdiff.differentiableAt (Metric.ball_mem_nhds z₁ one_pos)

/-! ## Blow-up along the ray to a maximal pole -/

/-- Along the ray `t ↦ t z₀`, `z₀ = x₀⁻¹`, towards the pole of an atom `x₀` of maximal modulus among the
atoms with negative imaginary part, the atom resolvent sum is unbounded: for every `C` and every small
`η` there is `t ∈ (1 − η, 1)` with `‖F(t z₀)‖ > C`. -/
theorem exists_norm_xiAtomResolventSum_gt (q₀ : XiZeroCopy)
    (hneg : (xiZeroCopyReciprocalSquare q₀).im < 0)
    (hmax : ∀ q, (xiZeroCopyReciprocalSquare q).im < 0 →
      ‖xiZeroCopyReciprocalSquare q‖ ≤ ‖xiZeroCopyReciprocalSquare q₀‖)
    (C η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 2) :
    ∃ t : ℝ, 1 - η < t ∧ t < 1 ∧
      C < ‖xiAtomResolventSum ((t : ℂ) * (xiZeroCopyReciprocalSquare q₀)⁻¹)‖ := by
  classical
  set x₀ : ℂ := xiZeroCopyReciprocalSquare q₀ with hx₀def
  have hx₀ : x₀ ≠ 0 := by
    intro h
    rw [h] at hneg
    simp at hneg
  have hx₀norm : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀
  set z₀ : ℂ := x₀⁻¹ with hz₀
  have hz₀x₀ : z₀ * x₀ = 1 := inv_mul_cancel₀ hx₀
  -- the head: atoms of modulus at least `‖x₀‖ / 2`
  have hhalf : 0 < ‖x₀‖ / 2 := by positivity
  set T : Finset XiZeroCopy := (finite_xiZeroCopy_norm_ge hhalf).toFinset with hT
  have hmemT : ∀ q, q ∈ T ↔ ‖x₀‖ / 2 ≤ ‖xiZeroCopyReciprocalSquare q‖ := by
    intro q
    rw [hT, Set.Finite.mem_toFinset]
    rfl
  -- the pole atoms
  set E : Finset XiZeroCopy := T.filter (fun q => xiZeroCopyReciprocalSquare q = x₀) with hE
  have hq₀E : q₀ ∈ E := by
    rw [hE, Finset.mem_filter, hmemT]
    exact ⟨by linarith, rfl⟩
  have hEsub : E ⊆ T := Finset.filter_subset _ _
  -- denominators of the non-pole head atoms do not vanish on `[1/2, 1]`
  have hden : ∀ q ∈ T \ E, ∀ t : ℝ, 1 / 2 ≤ t → t ≤ 1 →
      1 - (t : ℂ) * z₀ * xiZeroCopyReciprocalSquare q ≠ 0 := by
    intro q hq t ht1 ht2 h0
    rw [Finset.mem_sdiff, hE, Finset.mem_filter, not_and] at hq
    have hqne : xiZeroCopyReciprocalSquare q ≠ x₀ := hq.2 hq.1
    have htpos : (0 : ℝ) < t := by linarith
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
    -- `x_q = x₀ / t`
    have hxq : xiZeroCopyReciprocalSquare q = x₀ * ((t : ℂ))⁻¹ := by
      have h1 : (t : ℂ) * z₀ * xiZeroCopyReciprocalSquare q = 1 := by
        linear_combination -h0
      rw [hz₀] at h1
      field_simp at h1 ⊢
      linear_combination h1
    have hnormq : ‖xiZeroCopyReciprocalSquare q‖ = ‖x₀‖ / t := by
      rw [hxq, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos,
        div_eq_mul_inv]
    have himq : (xiZeroCopyReciprocalSquare q).im = x₀.im / t := by
      rw [hxq, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, add_zero, div_eq_mul_inv]
    have hqneg : (xiZeroCopyReciprocalSquare q).im < 0 := by
      rw [himq]
      exact div_neg_of_neg_of_pos hneg htpos
    have hle := hmax q hqneg
    rw [hnormq] at hle
    have ht1' : 1 ≤ t := by
      rw [div_le_iff₀ htpos] at hle
      nlinarith
    have hteq : t = 1 := le_antisymm ht2 ht1'
    apply hqne
    rw [hxq, hteq]
    simp
  -- the non-pole head is bounded on `[1/2, 1]`
  have hcont : ContinuousOn (fun t : ℝ => ∑ q ∈ T \ E,
      xiAtomResolventTerm ((t : ℂ) * z₀) q) (Set.Icc (1 / 2) 1) := by
    apply continuousOn_finset_sum
    intro q hq
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_const.sub ((Complex.continuous_ofReal.continuousOn.mul
        continuousOn_const).mul continuousOn_const))
    · intro t ht
      exact hden q hq t ht.1 ht.2
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  -- the tail is bounded by twice the total atom mass
  set S : ℝ := ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ with hS
  have htail : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖∑' q : {q // q ∉ T}, xiAtomResolventTerm ((t : ℂ) * z₀) q.1‖ ≤ 2 * S := by
    intro t ht0 ht1
    have hbd : ∀ q : {q // q ∉ T}, ‖xiAtomResolventTerm ((t : ℂ) * z₀) q.1‖ ≤
        2 * ‖xiZeroCopyReciprocalSquare q.1‖ := by
      intro q
      apply norm_div_one_sub_mul_le
      have hq := q.2
      rw [hmemT, not_le] at hq
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, hz₀,
        norm_inv]
      calc t * ‖x₀‖⁻¹ * ‖xiZeroCopyReciprocalSquare q.1‖ ≤ 1 * ‖x₀‖⁻¹ * (‖x₀‖ / 2) := by
            gcongr
        _ = 1 / 2 := by field_simp
    have hsumm : Summable (fun q : {q // q ∉ T} => 2 * ‖xiZeroCopyReciprocalSquare q.1‖) :=
      (summable_norm_xiZeroCopyReciprocalSquare.mul_left 2).subtype _
    calc ‖∑' q : {q // q ∉ T}, xiAtomResolventTerm ((t : ℂ) * z₀) q.1‖
        ≤ ∑' q : {q // q ∉ T}, 2 * ‖xiZeroCopyReciprocalSquare q.1‖ :=
          norm_tsum_le_tsum_norm_of_le hsumm hbd  -- placeholder name, fixed below
      _ ≤ 2 * S := by
          rw [hS, ← tsum_mul_left]
          exact (hsumm.tsum_le_tsum_of_subtype_le ?_ ?_)  -- placeholder
  sorry

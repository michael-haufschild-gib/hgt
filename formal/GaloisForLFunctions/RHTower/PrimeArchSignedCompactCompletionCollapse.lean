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
  have hmemT : ∀ q, q ∈ T ↔ ε ≤ ‖xiZeroCopyReciprocalSquare q‖ := by
    intro q
    rw [hT, Set.Finite.mem_toFinset]
    rfl
  have hsplit : xiAtomResolventSum = fun z =>
      (∑ q ∈ T, xiAtomResolventTerm z q) +
        ∑' q : {q // q ∉ T}, xiAtomResolventTerm z q := by
    funext z
    rw [xiAtomResolventSum, ← (summable_xiAtomResolventTerm z).sum_add_tsum_subtype_compl T]
  rw [hsplit]
  apply DifferentiableAt.add
  · apply DifferentiableAt.fun_sum
    intro q _
    have hfun : (fun y : ℂ => xiAtomResolventTerm y q) =
        fun y : ℂ => xiZeroCopyReciprocalSquare q / (1 - y * xiZeroCopyReciprocalSquare q) := rfl
    rw [hfun]
    exact (differentiableAt_const _).div ((differentiableAt_id.mul_const _).const_sub _) (h q)
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
        have hfun : (fun y : ℂ => xiAtomResolventTerm y q.1) =
            fun y : ℂ => xiZeroCopyReciprocalSquare q.1 /
              (1 - y * xiZeroCopyReciprocalSquare q.1) := rfl
        rw [hfun]
        exact (differentiableAt_const _).div ((differentiableAt_id.mul_const _).const_sub _)
          (one_sub_mul_ne_zero_of_norm_le_half (hkey q w hw)))
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
      rw [hxq, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
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
    apply continuousOn_finsetSum
    intro q hq
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_const.sub ((Complex.continuous_ofReal.continuousOn.mul
        continuousOn_const).mul continuousOn_const))
    · intro t ht
      exact hden q hq t ht.1 ht.2
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  -- the tail is bounded by twice the total atom mass
  set S : ℝ := ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun q => norm_nonneg _
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
    have hfull : Summable (fun q : XiZeroCopy => 2 * ‖xiZeroCopyReciprocalSquare q‖) :=
      summable_norm_xiZeroCopyReciprocalSquare.mul_left 2
    have hsplit := hfull.sum_add_tsum_subtype_compl T
    have hhead : 0 ≤ ∑ q ∈ T, 2 * ‖xiZeroCopyReciprocalSquare q‖ :=
      Finset.sum_nonneg fun q _ => by positivity
    calc ‖∑' q : {q // q ∉ T}, xiAtomResolventTerm ((t : ℂ) * z₀) q.1‖
        ≤ ∑' q : {q // q ∉ T}, 2 * ‖xiZeroCopyReciprocalSquare q.1‖ :=
          tsum_of_norm_bounded hsumm.hasSum hbd
      _ ≤ ∑' q : XiZeroCopy, 2 * ‖xiZeroCopyReciprocalSquare q‖ := by linarith
      _ = 2 * S := by rw [hS, tsum_mul_left]
  -- the pole atoms
  set M : ℕ := E.card with hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Finset.card_pos.mpr ⟨q₀, hq₀E⟩
  set K : ℝ := |C| + |C₁| + 2 * S + 1 with hK
  have hKpos : 0 < K := by positivity
  set δ : ℝ := min η (M * ‖x₀‖ / K) with hδ
  have hδpos : 0 < δ := lt_min hη (by positivity)
  have hδη : δ ≤ η := min_le_left _ _
  have hδK : δ ≤ M * ‖x₀‖ / K := min_le_right _ _
  refine ⟨1 - δ / 2, by linarith, by linarith, ?_⟩
  set t : ℝ := 1 - δ / 2 with ht
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ 1 := by linarith
  have ht2 : 1 / 2 ≤ t := by linarith
  have htlt : t < 1 := by linarith
  -- the pole contribution
  have hpole : ∀ q ∈ E, xiAtomResolventTerm ((t : ℂ) * z₀) q = x₀ / ((1 - t : ℝ) : ℂ) := by
    intro q hq
    rw [hE, Finset.mem_filter] at hq
    rw [xiAtomResolventTerm, hq.2, mul_assoc, hz₀x₀, mul_one]
    push_cast
    ring_nf
  have hEsum : ∑ q ∈ E, xiAtomResolventTerm ((t : ℂ) * z₀) q = (M : ℂ) * (x₀ / ((1 - t : ℝ) : ℂ)) := by
    rw [Finset.sum_congr rfl hpole, Finset.sum_const, nsmul_eq_mul]
  have hEnorm : ‖∑ q ∈ E, xiAtomResolventTerm ((t : ℂ) * z₀) q‖ = M * ‖x₀‖ / (1 - t) := by
    rw [hEsum, norm_mul, Complex.norm_natCast, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    ring
  -- the full decomposition
  have hdecomp : xiAtomResolventSum ((t : ℂ) * z₀) =
      (∑ q ∈ E, xiAtomResolventTerm ((t : ℂ) * z₀) q) +
        ((∑ q ∈ T \ E, xiAtomResolventTerm ((t : ℂ) * z₀) q) +
          ∑' q : {q // q ∉ T}, xiAtomResolventTerm ((t : ℂ) * z₀) q.1) := by
    rw [xiAtomResolventSum, ← (summable_xiAtomResolventTerm _).sum_add_tsum_subtype_compl T,
      ← Finset.sum_sdiff hEsub]
    ring
  have hC₁t := hC₁ t ⟨ht2, ht1⟩
  have htailt := htail t ht0 ht1
  have hbig : K ≤ M * ‖x₀‖ / (1 - t) := by
    have h1t : 1 - t = δ / 2 := by rw [ht]; ring
    rw [h1t, le_div_iff₀ (by positivity)]
    calc K * (δ / 2) ≤ K * (M * ‖x₀‖ / K / 2) := by gcongr
      _ = M * ‖x₀‖ / 2 := by field_simp
      _ ≤ M * ‖x₀‖ := by linarith [mul_nonneg hMpos.le hx₀norm.le]
  rw [hdecomp]
  have hlow := norm_sub_norm_le (∑ q ∈ E, xiAtomResolventTerm ((t : ℂ) * z₀) q)
    (-((∑ q ∈ T \ E, xiAtomResolventTerm ((t : ℂ) * z₀) q) +
      ∑' q : {q // q ∉ T}, xiAtomResolventTerm ((t : ℂ) * z₀) q.1))
  rw [sub_neg_eq_add, norm_neg, hEnorm] at hlow
  have hrest := norm_add_le (∑ q ∈ T \ E, xiAtomResolventTerm ((t : ℂ) * z₀) q)
    (∑' q : {q // q ∉ T}, xiAtomResolventTerm ((t : ℂ) * z₀) q.1)
  have hC : C ≤ |C| := le_abs_self C
  have hC₁' : C₁ ≤ |C₁| := le_abs_self C₁
  linarith

/-! ## The transform of a measure of bounded support -/

/-- The Markov-type transform `∫ dμ(x) / (1 − z x)` of a measure on the line. -/
def markovIntegral (μ : Measure ℝ) (z : ℂ) : ℂ := ∫ x, (1 - z * (x : ℂ))⁻¹ ∂μ

/-- For real `x`, `‖1 − z x‖ ≥ |Im z| / ‖z‖`: the distance from `1` to the real line through `z`. -/
theorem abs_im_div_norm_le_norm_one_sub_mul_real (z : ℂ) (hz : z ≠ 0) (x : ℝ) :
    |z.im| / ‖z‖ ≤ ‖1 - z * (x : ℂ)‖ := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [div_le_iff₀ hzpos]
  have hsq : |z.im| ^ 2 ≤ (‖1 - z * (x : ℂ)‖ * ‖z‖) ^ 2 := by
    rw [sq_abs, mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_sub,
      add_zero]
    nlinarith [sq_nonneg (z.re - x * (z.re * z.re + z.im * z.im))]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- The transform of a finite measure of bounded support is holomorphic on the upper half-plane. -/
theorem differentiableOn_markovIntegral (μ : Measure ℝ) [IsFiniteMeasure μ] {B : ℝ}
    (hμ : ∀ᵐ x ∂μ, |x| ≤ B) :
    DifferentiableOn ℂ (markovIntegral μ) {z : ℂ | 0 < z.im} := by
  intro z₀ hz₀
  have hz₀im : 0 < z₀.im := hz₀
  apply DifferentiableAt.differentiableWithinAt
  set r : ℝ := z₀.im / 2 with hr
  have hrpos : 0 < r := by positivity
  set c : ℝ := r / (‖z₀‖ + r) with hc
  have hcpos : 0 < c := by positivity
  have hlow : ∀ z ∈ Metric.ball z₀ r, ∀ x : ℝ, c ≤ ‖1 - z * (x : ℂ)‖ := by
    intro z hz x
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have him : |(z - z₀).im| ≤ ‖z - z₀‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im] at him
    have hzim : r ≤ z.im := by
      have := (abs_le.mp him).1
      linarith
    have hznorm : ‖z‖ ≤ ‖z₀‖ + r := by
      have := norm_sub_norm_le z z₀
      linarith
    have hzne : z ≠ 0 := by
      intro h
      rw [h] at hzim
      simp at hzim
      linarith
    calc c = r / (‖z₀‖ + r) := rfl
      _ ≤ |z.im| / ‖z‖ := by
          rw [abs_of_pos (by linarith)]
          exact div_le_div₀ (by linarith) hzim (norm_pos_iff.mpr hzne) hznorm
      _ ≤ ‖1 - z * (x : ℂ)‖ := abs_im_div_norm_le_norm_one_sub_mul_real z hzne x
  have hne : ∀ z ∈ Metric.ball z₀ r, ∀ x : ℝ, 1 - z * (x : ℂ) ≠ 0 := by
    intro z hz x h0
    have := hlow z hz x
    rw [h0, norm_zero] at this
    linarith
  have hz₀ball : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hrpos
  have hmeas : ∀ z ∈ Metric.ball z₀ r,
      AEStronglyMeasurable (fun x : ℝ => (1 - z * (x : ℂ))⁻¹) μ := by
    intro z hz
    apply Continuous.aestronglyMeasurable
    exact Continuous.inv₀ (by fun_prop) (fun x => hne z hz x)
  have hmeas' : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) / (1 - z₀ * (x : ℂ)) ^ 2) μ := by
    apply Continuous.aestronglyMeasurable
    exact Continuous.div (by fun_prop) (by fun_prop) (fun x => pow_ne_zero 2 (hne z₀ hz₀ball x))
  have hint : Integrable (fun x : ℝ => (1 - z₀ * (x : ℂ))⁻¹) μ := by
    refine Integrable.of_bound (hmeas z₀ hz₀ball) (1 / c) (ae_of_all _ fun x => ?_)
    rw [norm_inv, one_div]
    exact inv_anti₀ hcpos (hlow z₀ hz₀ball x)
  have hbound : ∀ᵐ (x : ℝ) ∂μ, ∀ z : ℂ, z ∈ Metric.ball z₀ r →
      ‖(x : ℂ) / (1 - z * (x : ℂ)) ^ 2‖ ≤ B / c ^ 2 := by
    filter_upwards [hμ] with x hx z hz
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div₀ ((abs_nonneg x).trans hx) hx (by positivity)
      (pow_le_pow_left₀ hcpos.le (hlow z hz x) 2)
  have hderiv : ∀ᵐ (x : ℝ) ∂μ, ∀ z : ℂ, z ∈ Metric.ball z₀ r →
      HasDerivAt (fun z : ℂ => (1 - z * (x : ℂ))⁻¹) ((x : ℂ) / (1 - z * (x : ℂ)) ^ 2) z := by
    refine ae_of_all _ fun x z hz => ?_
    have h1 : HasDerivAt (fun z : ℂ => 1 - z * (x : ℂ)) (-(1 * (x : ℂ))) z :=
      ((hasDerivAt_id z).mul_const (x : ℂ)).const_sub 1
    have h2 := h1.inv (hne z hz x)
    convert h2 using 1
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun z x => (1 - z * (x : ℂ))⁻¹) (F' := fun z x => (x : ℂ) / (1 - z * (x : ℂ)) ^ 2)
    (x₀ := z₀) (bound := fun _ => B / c ^ 2)
    (Metric.ball_mem_nhds z₀ hrpos)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds z₀ hrpos) hmeas) hint hmeas' hbound
    (integrable_const _) hderiv
  exact key.2.differentiableAt

/-- Near the origin the transform of a measure of bounded support is the moment generating function
of its moments. -/
theorem markovIntegral_eq_tsum (μ : Measure ℝ) [IsFiniteMeasure μ] {B : ℝ} (hB : 0 ≤ B)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ B) {z : ℂ} (hz : ‖z‖ * B < 1) :
    markovIntegral μ z = ∑' n : ℕ, ((∫ x, x ^ n ∂μ : ℝ) : ℂ) * z ^ n := by
  set ρ : ℝ := ‖z‖ * B with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hterm : ∀ x : ℝ, |x| ≤ B → ∀ n : ℕ, ‖(z * (x : ℂ)) ^ n‖ ≤ ρ ^ n := by
    intro x hx n
    rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (by positivity) (by rw [hρ]; gcongr) n
  have hpt : ∀ x : ℝ, |x| ≤ B → (1 - z * (x : ℂ))⁻¹ = ∑' n : ℕ, (z * (x : ℂ)) ^ n := by
    intro x hx
    have : ‖z * (x : ℂ)‖ < 1 := by
      have := hterm x hx 1
      rw [pow_one, pow_one] at this
      linarith
    exact (tsum_geometric_of_norm_lt_one this).symm
  have hint : ∀ n : ℕ, Integrable (fun x : ℝ => (z * (x : ℂ)) ^ n) μ := fun n =>
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) (ρ ^ n)
      (hμ.mono fun x hx => hterm x hx n)
  have hsum : Summable (fun n : ℕ => ∫ x, ‖(z * (x : ℂ)) ^ n‖ ∂μ) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => ?_) ((summable_geometric_of_lt_one hρ0 hz).mul_right (μ.real Set.univ))
    calc ∫ x, ‖(z * (x : ℂ)) ^ n‖ ∂μ ≤ ∫ _x, ρ ^ n ∂μ :=
          integral_mono_ae (hint n).norm (integrable_const _) (hμ.mono fun x hx => hterm x hx n)
      _ = ρ ^ n * μ.real Set.univ := by
          rw [integral_const, smul_eq_mul, mul_comm]
  calc markovIntegral μ z = ∫ x, ∑' n : ℕ, (z * (x : ℂ)) ^ n ∂μ := by
        rw [markovIntegral]
        apply integral_congr_ae
        filter_upwards [hμ] with x hx
        exact hpt x hx
    _ = ∑' n : ℕ, ∫ x, (z * (x : ℂ)) ^ n ∂μ :=
        (integral_tsum_of_summable_integral_norm hint hsum).symm
    _ = ∑' n : ℕ, ((∫ x, x ^ n ∂μ : ℝ) : ℂ) * z ^ n := by
        congr 1
        funext n
        simp_rw [mul_pow]
        rw [integral_const_mul]
        have : ∫ x, (x : ℂ) ^ n ∂μ = ((∫ x, x ^ n ∂μ : ℝ) : ℂ) := by
          rw [← integral_complex_ofReal]
          congr 1
          funext x
          rw [Complex.ofReal_pow]
        rw [this]
        ring

/-- The moment series of a finite measure of bounded support converges inside the disc
`‖z‖ B < 1`. -/
theorem summable_moment_series (μ : Measure ℝ) [IsFiniteMeasure μ] {B : ℝ} (hB : 0 ≤ B)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ B) {z : ℂ} (hz : ‖z‖ * B < 1) :
    Summable (fun n : ℕ => ((∫ x, x ^ n ∂μ : ℝ) : ℂ) * z ^ n) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by positivity) hz).mul_left (μ.real Set.univ)) (fun n => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hle : ∀ᵐ x ∂μ, |x ^ n| ≤ B ^ n := by
    filter_upwards [hμ] with x hx
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) hx n
  have hint : Integrable (fun x : ℝ => x ^ n) μ :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) (B ^ n)
      (hle.mono fun x hx => by rwa [Real.norm_eq_abs])
  have habs : |∫ x, x ^ n ∂μ| ≤ B ^ n * μ.real Set.univ := by
    calc |∫ x, x ^ n ∂μ| ≤ ∫ x, |x ^ n| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _x, B ^ n ∂μ := integral_mono_ae hint.abs (integrable_const _) hle
      _ = B ^ n * μ.real Set.univ := by rw [integral_const, smul_eq_mul, mul_comm]
  calc |∫ x, x ^ n ∂μ| * ‖z‖ ^ n ≤ (B ^ n * μ.real Set.univ) * ‖z‖ ^ n := by gcongr
    _ = μ.real Set.univ * (‖z‖ * B) ^ n := by
        rw [mul_pow]
        ring

/-! ## The collapse -/

/-- Imaginary part of an atom in terms of the spectral point. -/
theorem xiZeroCopyReciprocalSquare_im_eq_zero_iff (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im = 0 ↔ (xiSpectralPoint q).im = 0 := by
  rw [xiZeroCopyReciprocalSquare_im]
  have hγ : (xiSpectralPoint q).re ≠ 0 := by
    intro h
    have := xiSpectralPoint_re_sq_ge q
    rw [h] at this
    norm_num at this
  have hN : Complex.normSq (xiSpectralPoint q) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (normSq_xiSpectralPoint_pos q).ne'
  constructor
  · intro h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · have : (2 : ℝ) * (xiSpectralPoint q).re * (xiSpectralPoint q).im = 0 := by linarith
      rcases mul_eq_zero.mp this with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · norm_num at h3
        · exact absurd h3 hγ
      · exact h2
    · exact absurd h hN
  · intro h
    rw [h]
    simp

/-- **Signed compact completions collapse.**  If two finite measures of bounded support on the line
represent the normalized prime–archimedean moment tower as a difference, then RH holds. -/
theorem riemannHypothesis_of_signedCompactPrimeArchMoments {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {B : ℝ} (hB : 0 ≤ B)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ B) (hν : ∀ᵐ x ∂ν, |x| ≤ B)
    (hmom : ∀ n : ℕ, normalizedPrimeArchMoment n = ∫ x, x ^ n ∂μ - ∫ x, x ^ n ∂ν) :
    RiemannHypothesis := by
  classical
  rw [riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero]
  by_contra hnot
  obtain ⟨q₁, hq₁⟩ : ∃ q : XiZeroCopy, (xiZeroCopyReciprocalSquare q).im ≠ 0 := by
    by_contra hall
    apply hnot
    intro q
    rw [← xiZeroCopyReciprocalSquare_im_eq_zero_iff]
    by_contra h
    exact hall ⟨q, h⟩
  -- an atom with negative imaginary part
  obtain ⟨q₂, hq₂⟩ : ∃ q : XiZeroCopy, (xiZeroCopyReciprocalSquare q).im < 0 := by
    rcases lt_or_gt_of_ne hq₁ with h | h
    · exact ⟨q₁, h⟩
    · refine ⟨xiZeroCopyLineConjEquiv q₁, ?_⟩
      have hconj : xiZeroCopyReciprocalSquare (xiZeroCopyLineConjEquiv q₁) =
          (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q₁) := by
        simp [xiZeroCopyReciprocalSquare, xiSpectralPoint_lineConj, map_inv₀]
      rw [hconj, Complex.conj_im]
      linarith
  -- an atom of maximal modulus among those with negative imaginary part
  have hpos₂ : 0 < ‖xiZeroCopyReciprocalSquare q₂‖ := by
    rw [norm_pos_iff]
    intro h
    rw [h] at hq₂
    simp at hq₂
  set T₂ : Finset XiZeroCopy := ((finite_xiZeroCopy_norm_ge hpos₂).toFinset).filter
    (fun q => (xiZeroCopyReciprocalSquare q).im < 0) with hT₂
  have hmemT₂ : ∀ q, q ∈ T₂ ↔
      ‖xiZeroCopyReciprocalSquare q₂‖ ≤ ‖xiZeroCopyReciprocalSquare q‖ ∧
        (xiZeroCopyReciprocalSquare q).im < 0 := by
    intro q
    rw [hT₂, Finset.mem_filter, Set.Finite.mem_toFinset]
    rfl
  have hq₂T : q₂ ∈ T₂ := (hmemT₂ q₂).mpr ⟨le_rfl, hq₂⟩
  obtain ⟨q₀, hq₀T, hq₀max⟩ := T₂.exists_max_image (fun q => ‖xiZeroCopyReciprocalSquare q‖)
    ⟨q₂, hq₂T⟩
  have hneg : (xiZeroCopyReciprocalSquare q₀).im < 0 := (Finset.mem_filter.mp hq₀T).2
  have hmax : ∀ q, (xiZeroCopyReciprocalSquare q).im < 0 →
      ‖xiZeroCopyReciprocalSquare q‖ ≤ ‖xiZeroCopyReciprocalSquare q₀‖ := by
    intro q hq
    by_cases hle : ‖xiZeroCopyReciprocalSquare q₂‖ ≤ ‖xiZeroCopyReciprocalSquare q‖
    · exact hq₀max q ((hmemT₂ q).mpr ⟨hle, hq⟩)
    · have := hq₀max q₂ hq₂T
      linarith [not_le.mp hle]
  set x₀ : ℂ := xiZeroCopyReciprocalSquare q₀ with hx₀def
  have hx₀ : x₀ ≠ 0 := by
    intro h
    have hneg' : x₀.im < 0 := hneg
    rw [h] at hneg'
    simp at hneg'
  set z₀ : ℂ := x₀⁻¹ with hz₀def
  have hz₀im : 0 < z₀.im := by
    rw [hz₀def, Complex.inv_im, neg_div, neg_pos]
    exact div_neg_of_neg_of_pos hneg (Complex.normSq_pos.mpr hx₀)
  have hz₀norm : ‖z₀‖ = ‖x₀‖⁻¹ := by rw [hz₀def, norm_inv]
  have hx₀le : ‖x₀‖ ≤ 2 / 41 := norm_xiZeroCopyReciprocalSquare_le_two_div_fortyOne q₀
  have hx₀pos : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀
  have hz₀big : 41 / 2 ≤ ‖z₀‖ := by
    rw [hz₀norm, le_inv_comm₀ (by norm_num) hx₀pos]
    linarith
  -- the common disc of convergence
  set ρ : ℝ := min (41 / 4) (1 / (2 * (B + 1))) with hρ
  have hρpos : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 41 / 4 := min_le_left _ _
  have hρ2 : ρ ≤ 1 / (2 * (B + 1)) := min_le_right _ _
  have hρB : ∀ z : ℂ, ‖z‖ < ρ → ‖z‖ * B < 1 := by
    intro z hz
    have h1 : ‖z‖ * B ≤ ‖z‖ * (B + 1) := by nlinarith [norm_nonneg z]
    have h2 : ‖z‖ * (B + 1) < 1 / (2 * (B + 1)) * (B + 1) := by
      apply mul_lt_mul_of_pos_right _ (by linarith)
      linarith
    have h3 : 1 / (2 * (B + 1)) * (B + 1) = 1 / 2 := by field_simp
    linarith
  -- the two continuations
  set H : ℂ → ℂ := fun z => markovIntegral μ z - markovIntegral ν z with hH
  have hFH : ∀ z : ℂ, ‖z‖ < ρ → xiAtomResolventSum z = H z := by
    intro z hz
    have hzB := hρB z hz
    have hz41 : ‖z‖ ≤ 41 / 4 := by linarith
    rw [xiAtomResolventSum_eq_tsum_moment hz41, hH]
    simp only
    rw [markovIntegral_eq_tsum μ hB hμ hzB, markovIntegral_eq_tsum ν hB hν hzB,
      ← (summable_moment_series μ hB hμ hzB).tsum_sub (summable_moment_series ν hB hν hzB)]
    congr 1
    funext n
    rw [hmom n]
    push_cast
    ring
  -- the half-disc below the first pole in the upper half-plane
  set D : Set ℂ := {z : ℂ | 0 < z.im} ∩ Metric.ball 0 ‖z₀‖ with hD
  have hUopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hDopen : IsOpen D := hUopen.inter Metric.isOpen_ball
  have hDconn : IsPreconnected D :=
    ((convex_halfSpace_im_gt 0).inter (convex_ball 0 _)).isPreconnected
  have hFdiff : DifferentiableOn ℂ xiAtomResolventSum D := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_xiAtomResolventSum
    intro q h0
    have hxq : xiZeroCopyReciprocalSquare q ≠ 0 := by
      intro hx
      rw [hx, mul_zero, sub_zero] at h0
      exact one_ne_zero h0
    have hzq : z = (xiZeroCopyReciprocalSquare q)⁻¹ := by
      have h1 : z * xiZeroCopyReciprocalSquare q = 1 := by linear_combination -h0
      exact eq_inv_of_mul_eq_one_left h1
    have hzim : 0 < z.im := hz.1
    have hqneg : (xiZeroCopyReciprocalSquare q).im < 0 := by
      rw [hzq, Complex.inv_im] at hzim
      have hN := Complex.normSq_pos.mpr hxq
      have := mul_pos hzim hN
      rw [div_mul_cancel₀ _ hN.ne'] at this
      linarith
    have hle := hmax q hqneg
    have hz' : ‖z‖ < ‖z₀‖ := by
      have := hz.2
      rwa [Metric.mem_ball, dist_zero_right] at this
    rw [hzq, norm_inv, hz₀norm] at hz'
    have := (inv_lt_inv₀ (norm_pos_iff.mpr hxq) hx₀pos).mp hz'
    linarith
  have hHdiffU : DifferentiableOn ℂ H {z : ℂ | 0 < z.im} :=
    (differentiableOn_markovIntegral μ hμ).sub (differentiableOn_markovIntegral ν hν)
  have hHdiff : DifferentiableOn ℂ H D := hHdiffU.mono Set.inter_subset_left
  -- the base point of the identity theorem
  set w₀ : ℂ := ((ρ / 2 : ℝ) : ℂ) * I with hw₀
  have hw₀im : w₀.im = ρ / 2 := by simp [hw₀]
  have hw₀norm : ‖w₀‖ = ρ / 2 := by
    rw [hw₀, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hw₀D : w₀ ∈ D := by
    refine ⟨?_, ?_⟩
    · show 0 < w₀.im
      rw [hw₀im]
      positivity
    · rw [Metric.mem_ball, dist_zero_right, hw₀norm]
      linarith
  have hev : xiAtomResolventSum =ᶠ[nhds w₀] H := by
    filter_upwards [Metric.ball_mem_nhds w₀ (half_pos hρpos)] with z hz
    apply hFH
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have := norm_sub_norm_le z w₀
    linarith
  have hEq : Set.EqOn xiAtomResolventSum H D :=
    (hFdiff.analyticOnNhd hDopen).eqOn_of_preconnected_of_eventuallyEq
      (hHdiff.analyticOnNhd hDopen) hDconn hw₀D hev
  -- continuity of the measure transform at the pole
  have hHcont : ContinuousAt H z₀ :=
    (hHdiffU.differentiableAt (hUopen.mem_nhds hz₀im)).continuousAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hHcont 1 one_pos
  -- blow-up of the atom sum along the ray to the pole
  have hz₀pos : 0 < ‖z₀‖ := by linarith
  set η : ℝ := min (1 / 2) (δ / ‖z₀‖) with hη
  have hηpos : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hη2 : η ≤ δ / ‖z₀‖ := min_le_right _ _
  obtain ⟨t, ht1, ht2, hbig⟩ :=
    exists_norm_xiAtomResolventSum_gt q₀ hneg hmax (‖H z₀‖ + 1) η hηpos hη1
  have ht0 : 0 < t := by linarith
  have htD : (t : ℂ) * z₀ ∈ D := by
    refine ⟨?_, ?_⟩
    · show 0 < ((t : ℂ) * z₀).im
      rw [Complex.im_ofReal_mul]
      positivity
    · rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0]
      nlinarith
  have hdist : dist ((t : ℂ) * z₀) z₀ < δ := by
    rw [dist_eq_norm]
    have hrw : (t : ℂ) * z₀ - z₀ = ((t - 1 : ℝ) : ℂ) * z₀ := by
      push_cast
      ring
    rw [hrw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    have h1 : -(t - 1) * ‖z₀‖ < η * ‖z₀‖ :=
      mul_lt_mul_of_pos_right (by linarith) hz₀pos
    have h2 : η * ‖z₀‖ ≤ δ := by
      rw [← le_div_iff₀ hz₀pos]
      exact hη2
    linarith
  have hHt := hδ hdist
  rw [dist_eq_norm] at hHt
  have hHnorm : ‖H ((t : ℂ) * z₀)‖ ≤ ‖H z₀‖ + 1 := by
    have := norm_sub_norm_le (H ((t : ℂ) * z₀)) (H z₀)
    linarith
  have hbig' : ‖H z₀‖ + 1 < ‖xiAtomResolventSum ((t : ℂ) * z₀)‖ := hbig
  rw [hEq htD] at hbig'
  linarith

/-- **The collapse as an equivalence.**  A signed compact completion of the normalized
prime–archimedean moment tower exists exactly under RH, where the canonical compact Xi measure is
one. -/
theorem exists_signedCompactPrimeArchMoments_iff_riemannHypothesis :
    (∃ (μ ν : Measure ℝ) (B : ℝ), IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧ 0 ≤ B ∧
      (∀ᵐ x ∂μ, |x| ≤ B) ∧ (∀ᵐ x ∂ν, |x| ≤ B) ∧
      ∀ n : ℕ, normalizedPrimeArchMoment n = ∫ x, x ^ n ∂μ - ∫ x, x ^ n ∂ν) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨μ, ν, B, hμf, hνf, hB, hμ, hν, hmom⟩
    exact riemannHypothesis_of_signedCompactPrimeArchMoments hB hμ hν hmom
  · intro hRH
    refine ⟨primeArchXiCompactMomentMeasure, 0, 1, primeArchXiCompactMomentMeasure_finite,
      inferInstance, zero_le_one, ?_, ?_, ?_⟩
    · filter_upwards [ae_primeArchXiCompactMomentMeasure_mem_zero_one] with x hx using hx.2
    · rw [ae_zero]
      exact Filter.eventually_bot
    · intro n
      rw [integral_primeArchXiCompactMomentMeasure_eq_of_riemannHypothesis hRH n,
        integral_zero_measure, sub_zero]

end

end RHTower

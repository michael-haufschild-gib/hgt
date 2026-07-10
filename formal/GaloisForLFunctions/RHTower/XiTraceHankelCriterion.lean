import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.TraceHankelConverse

open Complex Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The multiplicity-weighted trace-Hankel summand of a real polynomial test on the actual
centered xi-divisor spectrum. -/
def xiCentralTraceHankelTerm (p : Polynomial ℝ)
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) : ℂ :=
  (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) *
    xiCentralReciprocalSquare (ρ : ℂ) *
      evalRealPolynomial p (xiCentralReciprocalSquare (ρ : ℂ)) ^ 2

/-- The target-free trace-Hankel quadratic value of the actual centered xi divisor. -/
def xiCentralTraceHankel (p : Polynomial ℝ) : ℂ :=
  ∑' ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
    xiCentralTraceHankelTerm p ρ

/-- Every polynomial trace-Hankel test is absolutely summable; this is a finite linear
combination of the already proved all-order centered reciprocal moments. -/
theorem xi_central_traceHankel_summable (p : Polynomial ℝ) :
    Summable (xiCentralTraceHankelTerm p) := by
  classical
  let D := MeromorphicOn.divisor xi Set.univ
  let lam : ↥D.support → ℂ := fun ρ => xiCentralReciprocalSquare (ρ : ℂ)
  let q : Polynomial ℂ := (p.map (algebraMap ℝ ℂ)) ^ 2
  let moment : ℕ → ↥D.support → ℂ := fun k ρ =>
    ((D (ρ : ℂ) : ℝ) : ℂ) * lam ρ ^ (k + 1)
  have hmoment (k : ℕ) : Summable (moment k) := by
    simpa only [D, lam, moment] using xi_central_reciprocal_moment_summable k
  have hcoeff (k : ℕ) :
      Summable (fun ρ => q.coeff k * moment k ρ) :=
    (hmoment k).mul_left (q.coeff k)
  have hfin : ∀ s : Finset ℕ,
      Summable (fun ρ => ∑ k ∈ s, q.coeff k * moment k ρ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hks ih =>
        simpa only [Finset.sum_insert hks] using (hcoeff k).add ih
  have hsum := hfin (Finset.range (q.natDegree + 1))
  apply hsum.congr
  intro ρ
  symm
  rw [xiCentralTraceHankelTerm]
  change ((D (ρ : ℂ) : ℝ) : ℂ) * lam ρ * evalRealPolynomial p (lam ρ) ^ 2 = _
  calc
    ((D (ρ : ℂ) : ℝ) : ℂ) * lam ρ * evalRealPolynomial p (lam ρ) ^ 2 =
        ((D (ρ : ℂ) : ℝ) : ℂ) * lam ρ * q.eval (lam ρ) := by
          simp [q, evalRealPolynomial]
    _ = ((D (ρ : ℂ) : ℝ) : ℂ) * lam ρ *
        (∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k * lam ρ ^ k) := by
          rw [Polynomial.eval_eq_sum_range]
    _ = ∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k * moment k ρ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          simp only [moment]
          ring

/-- Conjugation of the xi divisor conjugates each real-polynomial trace-Hankel summand. -/
theorem xiCentralTraceHankelTerm_conj (p : Polynomial ℝ)
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) :
    xiCentralTraceHankelTerm p (xiZeroConjEquiv ρ) =
      (starRingEnd ℂ) (xiCentralTraceHankelTerm p ρ) := by
  rw [xiCentralTraceHankelTerm, xiCentralTraceHankelTerm]
  change (((MeromorphicOn.divisor xi Set.univ)
      ((starRingEnd ℂ) (ρ : ℂ)) : ℝ) : ℂ) *
        xiCentralReciprocalSquare ((starRingEnd ℂ) (ρ : ℂ)) *
          evalRealPolynomial p
            (xiCentralReciprocalSquare ((starRingEnd ℂ) (ρ : ℂ))) ^ 2 = _
  rw [xi_divisor_conj, xiCentralReciprocalSquare_conj,
    evalRealPolynomial_conj]
  simp only [map_mul, map_pow, Complex.conj_ofReal]

/-- Every actual centered trace-Hankel value is real, unconditionally. -/
theorem xiCentralTraceHankel_conj (p : Polynomial ℝ) :
    (starRingEnd ℂ) (xiCentralTraceHankel p) = xiCentralTraceHankel p := by
  let term := xiCentralTraceHankelTerm p
  rw [xiCentralTraceHankel]
  calc
    (starRingEnd ℂ) (∑' ρ, term ρ) =
        ∑' ρ, (starRingEnd ℂ) (term ρ) :=
      Complex.conj_tsum term
    _ = ∑' ρ, term (xiZeroConjEquiv ρ) := by
      apply tsum_congr
      intro ρ
      exact (xiCentralTraceHankelTerm_conj p ρ).symm
    _ = ∑' ρ, term ρ := xiZeroConjEquiv.tsum_eq term

theorem xiCentralTraceHankel_im_eq_zero (p : Polynomial ℝ) :
    (xiCentralTraceHankel p).im = 0 :=
  Complex.conj_eq_iff_im.mp (xiCentralTraceHankel_conj p)

/-- The actual centered reciprocal-square spectrum is uniformly bounded. -/
theorem exists_xi_central_reciprocal_square_norm_bound :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
        ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ≤ M := by
  classical
  let S : Finset ↥(MeromorphicOn.divisor xi Set.univ).support :=
    (xi_central_reciprocal_square_finite_norm_ge (r := 1) (by norm_num)).toFinset
  let M : ℝ := ∑ ρ ∈ S, ‖xiCentralReciprocalSquare (ρ : ℂ)‖ + 1
  refine ⟨M, ?_, ?_⟩
  · dsimp [M]
    have hsum : 0 ≤ ∑ ρ ∈ S, ‖xiCentralReciprocalSquare (ρ : ℂ)‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  · intro ρ
    by_cases hlarge : 1 ≤ ‖xiCentralReciprocalSquare (ρ : ℂ)‖
    · have hmem : ρ ∈ S := by
        simp only [S, Set.Finite.mem_toFinset]
        exact hlarge
      have hle : ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ≤
          ∑ z ∈ S, ‖xiCentralReciprocalSquare (z : ℂ)‖ := by
        exact Finset.single_le_sum
          (s := S) (f := fun (z : ↥(MeromorphicOn.divisor xi Set.univ).support) =>
            ‖xiCentralReciprocalSquare (z : ℂ)‖)
          (fun z _ => norm_nonneg (xiCentralReciprocalSquare (z : ℂ))) hmem
      dsimp [M]
      linarith
    · have hlt : ‖xiCentralReciprocalSquare (ρ : ℂ)‖ < 1 := lt_of_not_ge hlarge
      have hsum : 0 ≤ ∑ z ∈ S, ‖xiCentralReciprocalSquare (z : ℂ)‖ :=
        Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      dsimp [M]
      linarith

/-- The source-side positivity statement for the actual centered trace spectrum. -/
def XiCentralTraceHankelNonnegative : Prop :=
  ∀ p : Polynomial ℝ, 0 ≤ (xiCentralTraceHankel p).re

/-- Global real-polynomial trace-Hankel positivity excludes every nonreal coordinate of the
actual trace-class xi spectrum. -/
theorem xi_central_spectrum_real_of_traceHankel_nonnegative
    (hpos : XiCentralTraceHankelNonnegative) :
    ∀ ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
      (xiCentralReciprocalSquare (ρ : ℂ)).im = 0 := by
  classical
  intro ρ₀
  let I := ↥(MeromorphicOn.divisor xi Set.univ).support
  let lam : I → ℂ := fun ρ => xiCentralReciprocalSquare (ρ : ℂ)
  let weight : I → ℝ := fun ρ =>
    ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ)
  let α := lam ρ₀
  by_contra him
  have hα0 : α ≠ 0 := by
    dsimp [α, lam]
    exact xiCentralReciprocalSquare_ne_zero ρ₀
  have hrpos : 0 < ‖α‖ := norm_pos_iff.mpr hα0
  let S : Finset I :=
    (xi_central_reciprocal_square_finite_norm_ge hrpos).toFinset
  have hρ₀S : ρ₀ ∈ S := by
    simpa only [S, Set.Finite.mem_toFinset, α, lam] using
      (le_rfl : ‖xiCentralReciprocalSquare (ρ₀ : ℂ)‖ ≤
        ‖xiCentralReciprocalSquare (ρ₀ : ℂ)‖)
  let F : Finset ℂ := S.image lam
  have hαF : α ∈ F := Finset.mem_image.mpr ⟨ρ₀, hρ₀S, rfl⟩
  obtain ⟨c, hc⟩ := exists_phase_sq_re_neg him
  let p : ℕ → Polynomial ℝ := fun n =>
    phaseCorrectedSeparatorPolynomial F α c n
  let f : ℕ → I → ℂ := fun n ρ => xiCentralTraceHankelTerm (p n) ρ
  let g : I → ℂ := fun ρ =>
    if lam ρ = α then ((weight ρ : ℝ) : ℂ) * α * c ^ 2
    else if lam ρ = (starRingEnd ℂ) α then
      ((weight ρ : ℝ) : ℂ) * (starRingEnd ℂ) α * ((starRingEnd ℂ) c) ^ 2
    else 0
  have hpointwise (ρ : I) : Tendsto (fun n => f n ρ) atTop (nhds (g ρ)) := by
    by_cases hρα : lam ρ = α
    · have heval (n : ℕ) : evalRealPolynomial (p n) (lam ρ) = c := by
        rw [hρα]
        exact eval_phaseCorrectedSeparatorPolynomial_target hα0 him n
      have hfconst : (fun n => f n ρ) =
          fun _ => ((weight ρ : ℝ) : ℂ) * α * c ^ 2 := by
        funext n
        change (((weight ρ : ℝ) : ℂ) * lam ρ *
          evalRealPolynomial (p n) (lam ρ) ^ 2) = _
        rw [hρα, eval_phaseCorrectedSeparatorPolynomial_target hα0 him n]
      have hgconst : g ρ = ((weight ρ : ℝ) : ℂ) * α * c ^ 2 := by
        simp only [g, hρα, if_pos]
      rw [hfconst, hgconst]
      exact tendsto_const_nhds
    · by_cases hρc : lam ρ = (starRingEnd ℂ) α
      · have heval (n : ℕ) :
          evalRealPolynomial (p n) (lam ρ) = (starRingEnd ℂ) c := by
          rw [hρc]
          exact eval_phaseCorrectedSeparatorPolynomial_conj_target hα0 him n
        have hfconst : (fun n => f n ρ) = fun _ =>
            ((weight ρ : ℝ) : ℂ) * (starRingEnd ℂ) α *
              ((starRingEnd ℂ) c) ^ 2 := by
          funext n
          change (((weight ρ : ℝ) : ℂ) * lam ρ *
            evalRealPolynomial (p n) (lam ρ) ^ 2) = _
          rw [hρc, eval_phaseCorrectedSeparatorPolynomial_conj_target hα0 him n]
        have hgconst : g ρ = ((weight ρ : ℝ) : ℂ) * (starRingEnd ℂ) α *
            ((starRingEnd ℂ) c) ^ 2 := by
          have hconjne : (starRingEnd ℂ) α ≠ α :=
            Complex.conj_eq_iff_im.not.mpr him
          simp only [g, hρc, hconjne, if_false, if_pos]
        rw [hfconst, hgconst]
        exact tendsto_const_nhds
      · by_cases houter : ‖α‖ ≤ ‖lam ρ‖
        · have hρS : ρ ∈ S := by
            simp only [S, Set.Finite.mem_toFinset]
            exact houter
          have hρF : lam ρ ∈ F := Finset.mem_image.mpr ⟨ρ, hρS, rfl⟩
          have heval (n : ℕ) : evalRealPolynomial (p n) (lam ρ) = 0 :=
            eval_phaseCorrectedSeparatorPolynomial_outer_zero hρF hρα hρc n
          have hfzero : (fun n => f n ρ) = fun _ => (0 : ℂ) := by
            funext n
            change (((weight ρ : ℝ) : ℂ) * lam ρ *
              evalRealPolynomial (p n) (lam ρ) ^ 2) = 0
            rw [heval n]
            ring
          have hgzero : g ρ = 0 := by
            simp only [g, hρα, hρc, if_false]
          rw [hfzero, hgzero]
          exact tendsto_const_nhds
        · have hinner : ‖lam ρ‖ < ‖α‖ := lt_of_not_ge houter
          have heval := tendsto_eval_phaseCorrectedSeparatorPolynomial_zero
            (F := F) (c := c) hα0 him hinner
          have hsq := heval.pow 2
          have hmul := hsq.const_mul
            ((((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) * lam ρ)
          simpa only [f, g, xiCentralTraceHankelTerm, lam, weight, p, hρα, hρc,
            if_false, pow_two, zero_mul, mul_zero] using hmul
  let C := phaseCorrectedSeparatorNormBound F α c
  have hC : 0 ≤ C := phaseCorrectedSeparatorNormBound_nonneg F him
  let base : I → ℂ := fun ρ => ((weight ρ : ℝ) : ℂ) * lam ρ
  have hbase : Summable base := by
    simpa only [base, weight, lam] using xi_central_reciprocal_square_summable
  let bound : I → ℝ := fun ρ => C ^ 2 * ‖base ρ‖
  have hboundSum : Summable bound := by
    exact hbase.norm.mul_left (C ^ 2)
  have hevalBound (n : ℕ) (ρ : I) :
      ‖evalRealPolynomial (p n) (lam ρ)‖ ≤ C := by
    by_cases hle : ‖lam ρ‖ ≤ ‖α‖
    · exact norm_eval_phaseCorrectedSeparatorPolynomial_le hα0 him hle n
    · have houter : ‖α‖ ≤ ‖lam ρ‖ := le_of_not_ge hle
      have hρS : ρ ∈ S := by
        simp only [S, Set.Finite.mem_toFinset]
        exact houter
      have hρF : lam ρ ∈ F := Finset.mem_image.mpr ⟨ρ, hρS, rfl⟩
      have hρα : lam ρ ≠ α := by
        intro h
        apply hle
        rw [h]
      have hρc : lam ρ ≠ (starRingEnd ℂ) α := by
        intro h
        apply hle
        rw [h, norm_conj]
      rw [eval_phaseCorrectedSeparatorPolynomial_outer_zero hρF hρα hρc n,
        norm_zero]
      exact hC
  have hdom : ∀ n ρ, ‖f n ρ‖ ≤ bound ρ := by
    intro n ρ
    have hev := hevalBound n ρ
    have hevSq : ‖evalRealPolynomial (p n) (lam ρ)‖ ^ 2 ≤ C ^ 2 := by
      nlinarith [norm_nonneg (evalRealPolynomial (p n) (lam ρ))]
    change ‖base ρ * evalRealPolynomial (p n) (lam ρ) ^ 2‖ ≤
      C ^ 2 * ‖base ρ‖
    rw [norm_mul, norm_pow]
    nlinarith [norm_nonneg (base ρ)]
  have htsum : Tendsto (fun n => ∑' ρ, f n ρ) atTop (nhds (∑' ρ, g ρ)) :=
    tendsto_tsum_of_dominated_convergence hboundSum hpointwise
      (Eventually.of_forall hdom)
  have hnonneg_n (n : ℕ) : 0 ≤ (∑' ρ, f n ρ).re := by
    have hp := hpos (p n)
    simpa only [XiCentralTraceHankelNonnegative, xiCentralTraceHankel, f] using hp
  have hreTend : Tendsto (fun n => (∑' ρ, f n ρ).re) atTop
      (nhds ((∑' ρ, g ρ).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp htsum
  have hlimit_nonneg : 0 ≤ (∑' ρ, g ρ).re :=
    ge_of_tendsto hreTend (Eventually.of_forall hnonneg_n)
  let T : Finset I := S.filter (fun ρ => lam ρ = α ∨ lam ρ = (starRingEnd ℂ) α)
  have hρ₀T : ρ₀ ∈ T := Finset.mem_filter.mpr ⟨hρ₀S, Or.inl rfl⟩
  have hTnonempty : T.Nonempty := ⟨ρ₀, hρ₀T⟩
  have hgoutside : ∀ ρ ∉ T, g ρ = 0 := by
    intro ρ hρT
    by_cases hρS : ρ ∈ S
    · have hnot : ¬(lam ρ = α ∨ lam ρ = (starRingEnd ℂ) α) := by
        intro hor
        exact hρT (Finset.mem_filter.mpr ⟨hρS, hor⟩)
      simp only [not_or] at hnot
      simp only [g, hnot.1, hnot.2, if_false]
    · have hneα : lam ρ ≠ α := by
        intro h
        apply hρS
        have hnorm : ‖α‖ ≤ ‖lam ρ‖ := by rw [h]
        simpa only [S, Set.Finite.mem_toFinset, lam] using hnorm
      have hnec : lam ρ ≠ (starRingEnd ℂ) α := by
        intro h
        apply hρS
        have hnorm : ‖α‖ ≤ ‖lam ρ‖ := by rw [h, norm_conj]
        simpa only [S, Set.Finite.mem_toFinset, lam] using hnorm
      simp only [g, hneα, hnec, if_false]
  have hgsum : (∑' ρ, g ρ) = ∑ ρ ∈ T, g ρ := tsum_eq_sum hgoutside
  have hgneg : ∀ ρ ∈ T, (g ρ).re < 0 := by
    intro ρ hρT
    have hor := (Finset.mem_filter.mp hρT).2
    have hwZ : 0 < (MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) :=
      xi_divisor_pos_on_support ρ
    have hw : 0 < weight ρ := by
      dsimp [weight]
      exact_mod_cast hwZ
    rcases hor with hρα | hρc
    · simp only [g, hρα, if_pos]
      rw [real_weight_phase_re]
      nlinarith
    · have hρα : lam ρ ≠ α := by
        intro h
        have hcfix : (starRingEnd ℂ) α = α := by rw [← hρc, h]
        exact him (Complex.conj_eq_iff_im.mp hcfix)
      have hgval : g ρ = ((weight ρ : ℝ) : ℂ) * (starRingEnd ℂ) α *
          ((starRingEnd ℂ) c) ^ 2 := by
        have hconjne : (starRingEnd ℂ) α ≠ α :=
          Complex.conj_eq_iff_im.not.mpr him
        simp only [g, hρc, hconjne, if_false, if_pos]
      rw [hgval]
      rw [real_weight_conj_phase_re]
      nlinarith
  have hlimit_neg : (∑' ρ, g ρ).re < 0 := by
    rw [hgsum, Complex.re_sum]
    exact Finset.sum_neg hgneg hTnonempty
  linarith

/-- The remaining positivity interface is strong enough to force RH; the proof uses the
trace-class outer-spectrum detector rather than assuming a moment-problem converse. -/
theorem riemannHypothesis_of_xiCentralTraceHankelNonnegative
    (hpos : XiCentralTraceHankelNonnegative) : RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hright hzero
  let z : ↥(MeromorphicOn.divisor xi Set.univ).support :=
    ⟨ρ, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hreal := xi_central_spectrum_real_of_traceHankel_nonnegative hpos z
  have hre := (xiCentralReciprocalSquare_im_eq_zero_iff z).mp hreal
  have hgt := mem_rightHalf.mp hright
  dsimp [z] at hre
  linarith

theorem xiCentralTraceHankelNonnegative_of_riemannHypothesis
    (hRH : RiemannHypothesis) : XiCentralTraceHankelNonnegative := by
  intro p
  rw [xiCentralTraceHankel,
    Complex.re_tsum (xi_central_traceHankel_summable p)]
  apply tsum_nonneg
  intro ρ
  obtain ⟨x, hx, hcoord⟩ := xiCentralReciprocalSquare_pos_real_of_rh hRH ρ
  rw [xiCentralTraceHankelTerm, hcoord, evalRealPolynomial_ofReal]
  have hw : 0 ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    exact_mod_cast xi_divisor_nonneg Set.univ (ρ : ℂ)
  rw [show ((((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) *
      (x : ℂ) * (((Polynomial.eval x p : ℝ) : ℂ)) ^ 2) =
      ((((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * x *
        (Polynomial.eval x p) ^ 2 : ℝ) : ℂ) by push_cast; ring]
  simp only [Complex.ofReal_re]
  positivity

/-- The trace-Hankel positivity source law is exactly RH. The forward direction is the
trace-class polynomial detector; the reverse direction is the positive atomic Gram sum on the
critical line. -/
theorem xiCentralTraceHankelNonnegative_iff_riemannHypothesis :
    XiCentralTraceHankelNonnegative ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiCentralTraceHankelNonnegative,
    xiCentralTraceHankelNonnegative_of_riemannHypothesis⟩

end

end RHTower

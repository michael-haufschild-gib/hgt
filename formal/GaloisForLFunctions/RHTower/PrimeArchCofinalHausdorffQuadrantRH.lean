import GaloisForLFunctions.RHTower.PrimeArchScaledHausdorffDivisorValueRelation
import GaloisForLFunctions.HTGeometry.ReflectionPositiveHankel

/-!
# Cofinal Hausdorff quadrants already force RH

The full calibrated Hausdorff criterion appears to require every pair of indices `(k,r)`.
In fact only one cofinal quadrant matters.  Shifting both indices past a common cutoff is
equivalent to multiplying every trace--Hankel test by the fixed polynomial

`X^M (R-X)^M`.

That multiplier cannot vanish at a nonreal reciprocal-square Xi atom.  The trace-class
phase separator therefore still detects every off-line atom through the resulting principal
ideal.  Consequently positivity for all sufficiently large `k` and `r` is already equivalent
to RH; neither infinite coordinate arm is part of the remaining obligation.
-/

open scoped BigOperators Polynomial
open Complex Polynomial Filter Topology

namespace RHTower
noncomputable section
open HTGeometry

/-- Moment sequence obtained by multiplying the tested polynomial by a fixed factor. -/
def momentPolynomialTransform (m : ℕ → ℝ) (b : Polynomial ℝ) (n : ℕ) : ℝ :=
  momentFunctional m (Polynomial.X ^ n * b)

/-- Multiplication on polynomials is exactly the induced transformation on moments. -/
theorem momentFunctional_momentPolynomialTransform
    (m : ℕ → ℝ) (b p : Polynomial ℝ) :
    momentFunctional (momentPolynomialTransform m b) p =
      momentFunctional m (p * b) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [momentFunctional_add, hp, hq, add_mul, momentFunctional_add]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      rw [← Polynomial.smul_eq_C_mul, momentFunctional_smul,
        HTGeometry.momentFunctional_X_pow]
      unfold momentPolynomialTransform
      rw [← momentFunctional_smul]
      congr 1
      exact (smul_mul_assoc a (X ^ n) b).symm

/-- Shifting a sequence by a calibrated Hausdorff difference shifts both difference indices. -/
theorem scaledHausdorffMomentDifference_shift
    (R : ℝ) (m : ℕ → ℝ) (K L k r : ℕ) :
    scaledHausdorffMomentDifference R
        (fun n => scaledHausdorffMomentDifference R m (K + n) L) k r =
      scaledHausdorffMomentDifference R m (K + k) (L + r) := by
  induction r generalizing k with
  | zero => simp [scaledHausdorffMomentDifference]
  | succ r ih =>
      rw [scaledHausdorffMomentDifference, ih k, ih (k + 1)]
      rw [show L + (r + 1) = (L + r) + 1 by omega,
        scaledHausdorffMomentDifference]
      congr 2

/-- Positivity on one common cofinal quadrant of calibrated Hausdorff indices. -/
def CofinalScaledHausdorffQuadrantNonnegative
    (R : ℝ) (m : ℕ → ℝ) : Prop :=
  ∃ M : ℕ, ∀ k r : ℕ, M ≤ k → M ≤ r →
    0 ≤ scaledHausdorffMomentDifference R m k r

/-- The fixed polynomial whose square shifts both Hausdorff indices by an even cutoff. -/
def cofinalHausdorffMultiplier (R : ℝ) (M : ℕ) : Polynomial ℝ :=
  Polynomial.X ^ M * (Polynomial.C R - Polynomial.X) ^ M

/-- The square of the cofinal multiplier is the simultaneous even Hausdorff shift. -/
theorem momentPolynomialTransform_cofinalHausdorffMultiplier_sq
    (R : ℝ) (m : ℕ → ℝ) (M n : ℕ) :
    momentPolynomialTransform m (cofinalHausdorffMultiplier R M ^ 2) n =
      scaledHausdorffMomentDifference R m (2 * M + n) (2 * M) := by
  unfold momentPolynomialTransform cofinalHausdorffMultiplier
  rw [scaledHausdorffMomentDifference_eq_momentFunctional]
  congr 1
  ring

/-- A cofinal Hausdorff quadrant gives complete trace--Hankel positivity after multiplication
by one fixed squared polynomial. -/
theorem sequenceTraceHankelNonnegative_transform_of_cofinalScaledHausdorffQuadrant
    {R : ℝ} (hR : 0 < R) {m : ℕ → ℝ}
    (h : CofinalScaledHausdorffQuadrantNonnegative R m) :
    ∃ M : ℕ, SequenceTraceHankelNonnegative
      (momentPolynomialTransform m (cofinalHausdorffMultiplier R M ^ 2)) := by
  obtain ⟨M, hM⟩ := h
  let t := momentPolynomialTransform m (cofinalHausdorffMultiplier R M ^ 2)
  have ht : t = fun n =>
      scaledHausdorffMomentDifference R m (2 * M + n) (2 * M) := by
    funext n
    exact momentPolynomialTransform_cofinalHausdorffMultiplier_sq R m M n
  have hscaled : ScaledHausdorffMomentDifferencesNonnegative R t := by
    intro k r
    rw [ht, scaledHausdorffMomentDifference_shift]
    apply hM
    · omega
    · omega
  have hclosure : FinitePositiveAtomicLocalMomentClosure t :=
    finitePositiveAtomicLocalMomentClosure_of_scaledHausdorffMomentDifferencesNonnegative
      hR hscaled
  refine ⟨M, ?_⟩
  exact sequenceTraceHankelNonnegative_of_finiteKMSWightmanLocalMomentClosure
    (finiteKMSWightmanLocalMomentClosure_of_finitePositiveAtomicLocalMomentClosure hclosure)

/-- A cofinal source quadrant supplies trace--Hankel positivity on the principal ideal generated
by its fixed Hausdorff multiplier. -/
theorem primeArchTraceHankel_nonnegative_on_cofinalHausdorffIdeal
    {R : ℝ} (hR : 0 < R)
    (h : CofinalScaledHausdorffQuadrantNonnegative R normalizedPrimeArchMoment) :
    ∃ M : ℕ, ∀ p : Polynomial ℝ,
      0 ≤ (primeArchSourceTraceHankel
        (cofinalHausdorffMultiplier R M * p)).re := by
  obtain ⟨M, hseq⟩ :=
    sequenceTraceHankelNonnegative_transform_of_cofinalScaledHausdorffQuadrant hR h
  refine ⟨M, fun p => ?_⟩
  have hp := hseq p
  rw [sequenceTraceHankel_eq_momentFunctional,
    momentFunctional_momentPolynomialTransform] at hp
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  convert hp using 1
  ring

end
end RHTower

namespace RHTower
noncomputable section

/-- Positivity restricted to a principal polynomial ideal still excludes every nonreal Xi atom,
provided the generator is nonzero at nonreal atoms. -/
theorem xi_central_spectrum_real_of_traceHankel_nonnegative_on_principalIdeal
    (a : Polynomial ℝ)
    (ha : ∀ ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
      (xiCentralReciprocalSquare (ρ : ℂ)).im ≠ 0 →
        evalRealPolynomial a (xiCentralReciprocalSquare (ρ : ℂ)) ≠ 0)
    (hpos : ∀ p : Polynomial ℝ,
      0 ≤ (xiCentralTraceHankel (a * p)).re) :
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
  have haα : evalRealPolynomial a α ≠ 0 := by
    exact ha ρ₀ him
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
  let d : ℂ := c / evalRealPolynomial a α
  have had : evalRealPolynomial a α * d = c := by
    dsimp only [d]
    exact mul_div_cancel₀ c haα
  let p : ℕ → Polynomial ℝ := fun n =>
    phaseCorrectedSeparatorPolynomial F α d n
  let q : ℕ → Polynomial ℝ := fun n => a * p n
  have hevalTarget (n : ℕ) : evalRealPolynomial (q n) α = c := by
    simp only [q, evalRealPolynomial_mul]
    rw [eval_phaseCorrectedSeparatorPolynomial_target hα0 him n, had]
  have hevalConjTarget (n : ℕ) :
      evalRealPolynomial (q n) ((starRingEnd ℂ) α) = (starRingEnd ℂ) c := by
    simp only [q, evalRealPolynomial_mul]
    rw [evalRealPolynomial_conj,
      eval_phaseCorrectedSeparatorPolynomial_conj_target hα0 him n]
    rw [← map_mul, had]
  let f : ℕ → I → ℂ := fun n ρ => xiCentralTraceHankelTerm (q n) ρ
  let g : I → ℂ := fun ρ =>
    if lam ρ = α then ((weight ρ : ℝ) : ℂ) * α * c ^ 2
    else if lam ρ = (starRingEnd ℂ) α then
      ((weight ρ : ℝ) : ℂ) * (starRingEnd ℂ) α * ((starRingEnd ℂ) c) ^ 2
    else 0
  have hpointwise (ρ : I) : Tendsto (fun n => f n ρ) atTop (nhds (g ρ)) := by
    by_cases hρα : lam ρ = α
    · have hfconst : (fun n => f n ρ) =
          fun _ => ((weight ρ : ℝ) : ℂ) * α * c ^ 2 := by
        funext n
        change (((weight ρ : ℝ) : ℂ) * lam ρ *
          evalRealPolynomial (q n) (lam ρ) ^ 2) = _
        rw [hρα, hevalTarget]
      have hgconst : g ρ = ((weight ρ : ℝ) : ℂ) * α * c ^ 2 := by
        simp only [g, hρα, if_pos]
      rw [hfconst, hgconst]
      exact tendsto_const_nhds
    · by_cases hρc : lam ρ = (starRingEnd ℂ) α
      · have hfconst : (fun n => f n ρ) = fun _ =>
            ((weight ρ : ℝ) : ℂ) * (starRingEnd ℂ) α *
              ((starRingEnd ℂ) c) ^ 2 := by
          funext n
          change (((weight ρ : ℝ) : ℂ) * lam ρ *
            evalRealPolynomial (q n) (lam ρ) ^ 2) = _
          rw [hρc, hevalConjTarget]
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
          have hevalP (n : ℕ) : evalRealPolynomial (p n) (lam ρ) = 0 :=
            eval_phaseCorrectedSeparatorPolynomial_outer_zero hρF hρα hρc n
          have hfzero : (fun n => f n ρ) = fun _ => (0 : ℂ) := by
            funext n
            change (((weight ρ : ℝ) : ℂ) * lam ρ *
              evalRealPolynomial (q n) (lam ρ) ^ 2) = 0
            simp only [q, evalRealPolynomial_mul, hevalP, mul_zero]
            ring
          have hgzero : g ρ = 0 := by
            simp only [g, hρα, hρc, if_false]
          rw [hfzero, hgzero]
          exact tendsto_const_nhds
        · have hinner : ‖lam ρ‖ < ‖α‖ := lt_of_not_ge houter
          have heval := tendsto_eval_phaseCorrectedSeparatorPolynomial_zero
            (F := F) (c := d) hα0 him hinner
          have hevalq := heval.const_mul (evalRealPolynomial a (lam ρ))
          have hsq := hevalq.pow 2
          have hmul := hsq.const_mul
            ((((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) * lam ρ)
          simpa only [f, g, xiCentralTraceHankelTerm, q, evalRealPolynomial_mul,
            lam, weight, p, hρα, hρc, if_false, pow_two, zero_mul, mul_zero] using hmul
  obtain ⟨M, hMone, hM⟩ := exists_xi_central_reciprocal_square_norm_bound
  let A := evalRealPolynomialNormBound a M
  have hA : 0 ≤ A := evalRealPolynomialNormBound_nonneg a (le_trans zero_le_one hMone)
  let C := phaseCorrectedSeparatorNormBound F α d
  have hC : 0 ≤ C := phaseCorrectedSeparatorNormBound_nonneg F him
  let E := A * C
  have hE : 0 ≤ E := mul_nonneg hA hC
  let base : I → ℂ := fun ρ => ((weight ρ : ℝ) : ℂ) * lam ρ
  have hbase : Summable base := by
    simpa only [base, weight, lam] using xi_central_reciprocal_square_summable
  let bound : I → ℝ := fun ρ => E ^ 2 * ‖base ρ‖
  have hboundSum : Summable bound := by
    exact hbase.norm.mul_left (E ^ 2)
  have hevalPBound (n : ℕ) (ρ : I) :
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
  have hevalBound (n : ℕ) (ρ : I) :
      ‖evalRealPolynomial (q n) (lam ρ)‖ ≤ E := by
    simp only [q, evalRealPolynomial_mul, norm_mul]
    exact mul_le_mul (norm_evalRealPolynomial_le a (hM ρ)) (hevalPBound n ρ)
      (norm_nonneg _) hA
  have hdom : ∀ n ρ, ‖f n ρ‖ ≤ bound ρ := by
    intro n ρ
    have hev := hevalBound n ρ
    have hevSq : ‖evalRealPolynomial (q n) (lam ρ)‖ ^ 2 ≤ E ^ 2 := by
      nlinarith [norm_nonneg (evalRealPolynomial (q n) (lam ρ))]
    change ‖base ρ * evalRealPolynomial (q n) (lam ρ) ^ 2‖ ≤
      E ^ 2 * ‖base ρ‖
    rw [norm_mul, norm_pow]
    nlinarith [norm_nonneg (base ρ)]
  have htsum : Tendsto (fun n => ∑' ρ, f n ρ) atTop (nhds (∑' ρ, g ρ)) :=
    tendsto_tsum_of_dominated_convergence hboundSum hpointwise
      (Eventually.of_forall hdom)
  have hnonneg_n (n : ℕ) : 0 ≤ (∑' ρ, f n ρ).re := by
    have hp := hpos (p n)
    simpa only [xiCentralTraceHankel, f, q] using hp
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

end
end RHTower

namespace RHTower
noncomputable section

/-- A cofinal Hausdorff multiplier has only the real roots `0` and `R`, so it is nonzero at every
nonreal spectral coordinate. -/
theorem evalRealPolynomial_cofinalHausdorffMultiplier_ne_zero_of_im_ne_zero
    (R : ℝ) (M : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    evalRealPolynomial (cofinalHausdorffMultiplier R M) z ≠ 0 := by
  have hz0 : z ≠ 0 := by
    intro h
    apply hz
    rw [h]
    simp
  have hRz : (R : ℂ) - z ≠ 0 := by
    intro h
    have heq : (R : ℂ) = z := sub_eq_zero.mp h
    apply hz
    rw [← heq]
    simp
  have heval :
      evalRealPolynomial (cofinalHausdorffMultiplier R M) z =
        z ^ M * ((R : ℂ) - z) ^ M := by
    simp [cofinalHausdorffMultiplier, evalRealPolynomial]
  rw [heval]
  exact mul_ne_zero (pow_ne_zero M hz0) (pow_ne_zero M hRz)

/-- Principal-ideal trace positivity is an RH criterion whenever its generator does not vanish at
nonreal reciprocal-square atoms. -/
theorem riemannHypothesis_of_xiCentralTraceHankel_nonnegative_on_principalIdeal
    (a : Polynomial ℝ)
    (ha : ∀ ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
      (xiCentralReciprocalSquare (ρ : ℂ)).im ≠ 0 →
        evalRealPolynomial a (xiCentralReciprocalSquare (ρ : ℂ)) ≠ 0)
    (hpos : ∀ p : Polynomial ℝ,
      0 ≤ (xiCentralTraceHankel (a * p)).re) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hright hzero
  let z : ↥(MeromorphicOn.divisor xi Set.univ).support :=
    ⟨ρ, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hreal :=
    xi_central_spectrum_real_of_traceHankel_nonnegative_on_principalIdeal a ha hpos z
  have hre := (xiCentralReciprocalSquare_im_eq_zero_iff z).mp hreal
  have hgt := mem_rightHalf.mp hright
  dsimp [z] at hre
  linarith

/-- **Cofinal-quadrant RH capstone.**  At any positive radius, positivity of the calibrated
prime--Gamma Hausdorff differences once both indices are sufficiently large already proves RH. -/
theorem riemannHypothesis_of_cofinalScaledPrimeArchHausdorffQuadrantNonnegative
    {R : ℝ} (hR : 0 < R)
    (h : CofinalScaledHausdorffQuadrantNonnegative R normalizedPrimeArchMoment) :
    RiemannHypothesis := by
  obtain ⟨M, hideal⟩ :=
    primeArchTraceHankel_nonnegative_on_cofinalHausdorffIdeal hR h
  apply riemannHypothesis_of_xiCentralTraceHankel_nonnegative_on_principalIdeal
    (cofinalHausdorffMultiplier R M)
  · intro ρ him
    exact evalRealPolynomial_cofinalHausdorffMultiplier_ne_zero_of_im_ne_zero
      R M (xiCentralReciprocalSquare (ρ : ℂ)) him
  · intro p
    rw [xiCentralTraceHankel_eq_primeArchSourceTraceHankel]
    exact hideal p

/-- Complete calibrated positivity trivially supplies a cofinal quadrant. -/
theorem cofinalScaledHausdorffQuadrantNonnegative_of_scaledHausdorffMomentDifferencesNonnegative
    {R : ℝ} {m : ℕ → ℝ}
    (h : ScaledHausdorffMomentDifferencesNonnegative R m) :
    CofinalScaledHausdorffQuadrantNonnegative R m := by
  exact ⟨0, fun k r _ _ => h k r⟩

/-- At a positive radius containing all thermal nodes, positivity in one cofinal quadrant is
already exactly RH. -/
theorem cofinalScaledPrimeArchHausdorffQuadrantNonnegative_iff_riemannHypothesis_of_node_le
    {R : ℝ} (hR : 0 < R) (hnode : ∀ q : XiZeroCopy, xiThermalNode q ≤ R) :
    CofinalScaledHausdorffQuadrantNonnegative R normalizedPrimeArchMoment ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_cofinalScaledPrimeArchHausdorffQuadrantNonnegative hR
  · intro hRH
    exact cofinalScaledHausdorffQuadrantNonnegative_of_scaledHausdorffMomentDifferencesNonnegative
      (scaledPrimeArchHausdorffMomentDifferencesNonnegative_of_riemannHypothesis_of_node_le
        R hnode hRH)

/-- **Endpoint cofinal-quadrant value law.**  The endpoint abscissa/RH criterion needs calibrated
Hausdorff positivity only after both indices cross one unspecified finite cutoff. -/
theorem cofinalScaledPrimeArchHausdorffQuadrantNonnegative_iff_riemannHypothesis :
    CofinalScaledHausdorffQuadrantNonnegative primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment ↔
      RiemannHypothesis :=
  cofinalScaledPrimeArchHausdorffQuadrantNonnegative_iff_riemannHypothesis_of_node_le
    primeArchEndpointHausdorffRadius_pos
    xiThermalNode_le_primeArchEndpointHausdorffRadius

/-- **Cofinal-quadrant prime--polar endpoint law.**  The target absolute-abscissa bound is
equivalent to positivity only in some deep two-index quadrant. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_cofinalHausdorffQuadrant
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) ↔
      CofinalScaledHausdorffQuadrantNonnegative primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment := by
  exact
    (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_scaledPrimeArchHausdorffMomentDifferencesNonnegative
      hL hN).trans
      ((scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis).trans
        cofinalScaledPrimeArchHausdorffQuadrantNonnegative_iff_riemannHypothesis.symm)

end
end RHTower

namespace RHTower
noncomputable section
open HTGeometry

/-- For any principal-ideal generator nonzero at nonreal Xi atoms, positivity of the transformed
moment sequence is exactly RH. -/
theorem sequenceTraceHankelNonnegative_momentPolynomialTransform_iff_riemannHypothesis
    (a : Polynomial ℝ)
    (ha : ∀ ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
      (xiCentralReciprocalSquare (ρ : ℂ)).im ≠ 0 →
        evalRealPolynomial a (xiCentralReciprocalSquare (ρ : ℂ)) ≠ 0) :
    SequenceTraceHankelNonnegative
        (momentPolynomialTransform normalizedPrimeArchMoment (a ^ 2)) ↔
      RiemannHypothesis := by
  constructor
  · intro hseq
    apply riemannHypothesis_of_xiCentralTraceHankel_nonnegative_on_principalIdeal a ha
    intro p
    rw [xiCentralTraceHankel_eq_primeArchSourceTraceHankel,
      re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
    have hp := hseq p
    rw [sequenceTraceHankel_eq_momentFunctional,
      momentFunctional_momentPolynomialTransform] at hp
    convert hp using 1
    ring
  · intro hRH p
    have hp := xiCentralTraceHankelNonnegative_of_riemannHypothesis hRH (a * p)
    rw [xiCentralTraceHankel_eq_primeArchSourceTraceHankel,
      re_primeArchSourceTraceHankel_eq_momentFunctional_sq] at hp
    rw [sequenceTraceHankel_eq_momentFunctional,
      momentFunctional_momentPolynomialTransform]
    convert hp using 1
    ring

/-- The even-shifted prime--Gamma tail beginning at moment `2M`. -/
def shiftedPrimeArchMomentTail (M : ℕ) (n : ℕ) : ℝ :=
  normalizedPrimeArchMoment (2 * M + n)

/-- Multiplication by `X^M` on Hankel tests is exactly deletion of the first `2M` source moments. -/
theorem momentPolynomialTransform_X_pow_sq_eq_shiftedPrimeArchMomentTail
    (M : ℕ) :
    momentPolynomialTransform normalizedPrimeArchMoment
        (((Polynomial.X : Polynomial ℝ) ^ M) ^ 2) =
      shiftedPrimeArchMomentTail M := by
  funext n
  unfold momentPolynomialTransform shiftedPrimeArchMomentTail
  have hpoly :
      (Polynomial.X : Polynomial ℝ) ^ n *
          ((Polynomial.X : Polynomial ℝ) ^ M) ^ 2 =
        Polynomial.X ^ (2 * M + n) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hpoly, momentFunctional_X_pow]

/-- **Shifted Hankel-tail RH law.**  For every cutoff `M`, positivity of the Hankel form after
removing the first `2M` prime--Gamma moments is already equivalent to RH. -/
theorem sequenceTraceHankelNonnegative_shiftedPrimeArchMomentTail_iff_riemannHypothesis
    (M : ℕ) :
    SequenceTraceHankelNonnegative (shiftedPrimeArchMomentTail M) ↔
      RiemannHypothesis := by
  rw [← momentPolynomialTransform_X_pow_sq_eq_shiftedPrimeArchMomentTail M]
  apply sequenceTraceHankelNonnegative_momentPolynomialTransform_iff_riemannHypothesis
    ((Polynomial.X : Polynomial ℝ) ^ M)
  intro ρ him
  have hne := xiCentralReciprocalSquare_ne_zero ρ
  simpa [evalRealPolynomial] using
    (pow_ne_zero M hne)

/-- Shifting a finite positive-atomic Stieltjes moment sequence preserves that structure. -/
theorem finitePositiveAtomicMomentSequence_shift
    {m : ℕ → ℝ} (hm : FinitePositiveAtomicMomentSequence m) (K : ℕ) :
    FinitePositiveAtomicMomentSequence (fun n => m (K + n)) := by
  obtain ⟨d, mass, node, hmass, hnode, rfl⟩ := hm
  refine ⟨d, fun i => mass i * node i ^ K, node,
    fun i => mul_nonneg (hmass i) (pow_nonneg (hnode i) K), hnode, ?_⟩
  funext n
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add]
  ring

/-- Local finite positive-atomic moment closure is stable under deleting a finite prefix. -/
theorem finitePositiveAtomicLocalMomentClosure_shift
    {m : ℕ → ℝ} (hm : FinitePositiveAtomicLocalMomentClosure m) (K : ℕ) :
    FinitePositiveAtomicLocalMomentClosure (fun n => m (K + n)) := by
  intro N epsilon hepsilon
  obtain ⟨a, ha, happrox⟩ := hm (K + N) epsilon hepsilon
  refine ⟨fun n => a (K + n), finitePositiveAtomicMomentSequence_shift ha K, ?_⟩
  intro n hn
  exact happrox (K + n) (by omega)

/-- **Shifted finite-system closure RH law.**  For every cutoff, approximating only the even-shifted
prime--Gamma tail by finite positive atomic systems is exactly RH. -/
theorem finitePositiveAtomicLocalMomentClosure_shiftedPrimeArchMomentTail_iff_riemannHypothesis
    (M : ℕ) :
    FinitePositiveAtomicLocalMomentClosure (shiftedPrimeArchMomentTail M) ↔
      RiemannHypothesis := by
  constructor
  · intro hclosure
    apply (sequenceTraceHankelNonnegative_shiftedPrimeArchMomentTail_iff_riemannHypothesis M).mp
    exact sequenceTraceHankelNonnegative_of_finiteKMSWightmanLocalMomentClosure
      (finiteKMSWightmanLocalMomentClosure_of_finitePositiveAtomicLocalMomentClosure hclosure)
  · intro hRH
    have hsource := primeArchFinitePositiveAtomicLocalMomentClosure_of_riemannHypothesis hRH
    simpa only [shiftedPrimeArchMomentTail] using
      finitePositiveAtomicLocalMomentClosure_shift hsource (2 * M)

/-- A complex static self-adjoint observable representing only one even-shifted prime--Gamma tail
already proves RH.  No Hamiltonian flow and no low source moments are required. -/
theorem riemannHypothesis_of_complexSelfAdjointObservable_shiftedPrimeArchMomentTail
    (M : ℕ)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : F →L[ℂ] F) (omega : F) (hA : IsSelfAdjoint A)
    (hmom : ∀ n,
      inner ℂ omega ((A ^ n) omega) = (shiftedPrimeArchMomentTail M n : ℂ)) :
    RiemannHypothesis := by
  apply (sequenceTraceHankelNonnegative_shiftedPrimeArchMomentTail_iff_riemannHypothesis M).mp
  intro p
  rw [sequenceTraceHankel_eq_momentFunctional]
  exact momentFunctional_pow_two_nonneg_of_complexSelfAdjointObservable
    (shiftedPrimeArchMomentTail M) A omega hA hmom p

end
end RHTower

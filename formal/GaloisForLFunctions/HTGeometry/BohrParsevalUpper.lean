import GaloisForLFunctions.HTGeometry.BohrTrigMeans
import GaloisForLFunctions.HTGeometry.BohrApproximation

/-!
# Parseval's identity for almost-periodic functions

Completing the square in the expansion of the approximation error turns the approximation theorem
into the upper bound

`M(|f|²) ≤ δ² + ∑_λ |c_λ(f)|²`

over the frequencies of a `δ`-approximating trigonometric polynomial.  With Bessel's inequality in
the corpus this is Parseval: the mean square is the supremum of the partial sums of squared Bohr
coefficients.
-/

open MeasureTheory ComplexConjugate

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

theorem bohrExp_eq_exp (mu t : ℝ) : bohrExp mu t = Complex.exp ((mu * t : ℝ) * Complex.I) := by
  unfold bohrExp bohrChar
  congr 1
  push_cast
  ring

/-- The completed square, in real form. -/
theorem re_pairing_eq (z w : ℂ) :
    (conj z * w + z * conj w - z * conj z).re
      = Complex.normSq w - Complex.normSq (z - w) := by
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply, Complex.sub_im]
  ring

/-- The approximation theorem in the form indexed by a finite set of distinct frequencies. -/
theorem exists_trigPoly_approx {f : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : Finset ℝ) (a : ℝ → ℂ), ∀ t : ℝ, ‖f t - trigPoly S a t‖ ≤ ε := by
  classical
  obtain ⟨n, c, lam, hclose⟩ := exists_trig_approx hf htb hε
  refine ⟨Finset.image lam Finset.univ,
    fun mu => ∑ j ∈ Finset.univ.filter (fun j => lam j = mu), c j, fun t => ?_⟩
  have hregroup : trigPoly (Finset.image lam Finset.univ)
      (fun mu => ∑ j ∈ Finset.univ.filter (fun j => lam j = mu), c j) t
      = ∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I) := by
    rw [trigPoly]
    have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin n)), lam j ∈ Finset.image lam Finset.univ :=
      fun j _ => Finset.mem_image_of_mem lam (Finset.mem_univ j)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun j => c j * Complex.exp ((lam j * t : ℝ) * Complex.I))]
    refine Finset.sum_congr rfl fun mu _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hlam : lam j = mu := (Finset.mem_filter.mp hj).2
    rw [hlam, bohrExp_eq_exp]
  rw [hregroup]
  exact hclose t

/-- **Parseval's upper bound.**  The mean square is approximated from above by finite partial sums
of squared Bohr coefficients. -/
theorem exists_finset_bohrMean_normSq_le {f : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x)) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℝ, (bohrMean (fun t => f t * conj (f t))).re
      ≤ (∑ lam ∈ S, Complex.normSq (bohrCoefficient (fun x => f x) lam)) + ε := by
  classical
  have hap : HTGeometry.IsBohrAlmostPeriodic (fun x => f x) :=
    isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit htb
  have hcont : Continuous (fun x => f x) := f.continuous
  set δ : ℝ := min 1 ε with hδ
  have hδpos : 0 < δ := lt_min one_pos hε
  have hδsq : δ * δ ≤ ε := by
    calc δ * δ ≤ 1 * δ := by
          exact mul_le_mul_of_nonneg_right (min_le_left _ _) hδpos.le
      _ = δ := one_mul δ
      _ ≤ ε := min_le_right _ _
  obtain ⟨S, a, hclose⟩ := exists_trigPoly_approx hf htb hδpos
  refine ⟨S, ?_⟩
  -- the expansion of the error
  have hexp := bohrMean_sub_trigPoly_mul_conj hcont hap S a
  -- the error mean is small
  have herr : ‖bohrMean (fun t => ((fun x => f x) t - trigPoly S a t) *
      conj ((fun x => f x) t - trigPoly S a t))‖ ≤ δ * δ := by
    have hc : Continuous fun t : ℝ => ((fun x => f x) t - trigPoly S a t) *
        conj ((fun x => f x) t - trigPoly S a t) := by
      refine (hcont.sub (continuous_trigPoly S a)).mul ?_
      exact Complex.continuous_conj.comp (hcont.sub (continuous_trigPoly S a))
    have ha : HTGeometry.IsBohrAlmostPeriodic fun t : ℝ =>
        ((fun x => f x) t - trigPoly S a t) * conj ((fun x => f x) t - trigPoly S a t) := by
      refine isBohrAlmostPeriodic_mul (hcont.sub (continuous_trigPoly S a))
        (isBohrAlmostPeriodic_sub hcont hap (continuous_trigPoly S a)
          (isBohrAlmostPeriodic_trigPoly S a)) ?_ ?_
      · exact Complex.continuous_conj.comp (hcont.sub (continuous_trigPoly S a))
      · exact isBohrAlmostPeriodic_conj (isBohrAlmostPeriodic_sub hcont hap
          (continuous_trigPoly S a) (isBohrAlmostPeriodic_trigPoly S a))
    refine norm_bohrMean_le hc ha fun t => ?_
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul (hclose t) (hclose t) (norm_nonneg _) hδpos.le
  -- assemble
  have hre : (bohrMean (fun t => f t * conj (f t))).re
      = (bohrMean (fun t => ((fun x => f x) t - trigPoly S a t) *
          conj ((fun x => f x) t - trigPoly S a t))).re
        + ∑ lam ∈ S, (Complex.normSq (bohrCoefficient (fun x => f x) lam)
            - Complex.normSq (a lam - bohrCoefficient (fun x => f x) lam)) := by
    rw [hexp, Complex.sub_re, Complex.re_sum]
    have : ∀ lam ∈ S, (conj (a lam) * bohrCoefficient (fun x => f x) lam
        + a lam * conj (bohrCoefficient (fun x => f x) lam) - a lam * conj (a lam)).re
        = Complex.normSq (bohrCoefficient (fun x => f x) lam)
          - Complex.normSq (a lam - bohrCoefficient (fun x => f x) lam) :=
      fun lam _ => re_pairing_eq _ _
    rw [Finset.sum_congr rfl this]
    ring
  rw [hre]
  have hterm : ∑ lam ∈ S, (Complex.normSq (bohrCoefficient (fun x => f x) lam)
      - Complex.normSq (a lam - bohrCoefficient (fun x => f x) lam))
      ≤ ∑ lam ∈ S, Complex.normSq (bohrCoefficient (fun x => f x) lam) := by
    refine Finset.sum_le_sum fun lam _ => ?_
    have := Complex.normSq_nonneg (a lam - bohrCoefficient (fun x => f x) lam)
    linarith
  have hle : (bohrMean (fun t => ((fun x => f x) t - trigPoly S a t) *
      conj ((fun x => f x) t - trigPoly S a t))).re ≤ ε :=
    le_trans (le_trans (Complex.re_le_norm _) herr) hδsq
  linarith

end

end GaloisForLFunctions

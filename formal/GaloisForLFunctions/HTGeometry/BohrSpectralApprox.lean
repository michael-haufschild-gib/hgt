import GaloisForLFunctions.HTGeometry.BohrParsevalUpper

/-!
# Mean-square approximation by spectrum-supported polynomials

Replacing the coefficients of a uniform approximant by the true Bohr coefficients can only decrease
the mean-square error, by the completed square.  The resulting polynomial is supported on the Bohr
spectrum, since coefficients off the spectrum vanish by definition.

This is the form of the approximation theorem the spectral product rule needs: the approximating
frequencies must be known to lie in the spectrum.
-/

open MeasureTheory ComplexConjugate

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

/-- **Mean-square approximation by a polynomial supported on the spectrum.** -/
theorem exists_spectral_mean_square_approx {f : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset ℝ,
      (bohrMean (fun t => (f t - trigPoly S (bohrCoefficient (fun x => f x)) t) *
        conj (f t - trigPoly S (bohrCoefficient (fun x => f x)) t))).re ≤ δ := by
  classical
  have hap : HTGeometry.IsBohrAlmostPeriodic (fun x => f x) :=
    isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit htb
  have hcont : Continuous (fun x => f x) := f.continuous
  set η : ℝ := min 1 δ with hη
  have hηpos : 0 < η := lt_min one_pos hδ
  have hηsq : η * η ≤ δ := by
    calc η * η ≤ 1 * η := mul_le_mul_of_nonneg_right (min_le_left _ _) hηpos.le
      _ = η := one_mul η
      _ ≤ δ := min_le_right _ _
  obtain ⟨S, a, hclose⟩ := exists_trigPoly_approx hf htb hηpos
  refine ⟨S, ?_⟩
  set c : ℝ → ℂ := bohrCoefficient (fun x => f x) with hc
  -- the two expansions
  have h1 := bohrMean_sub_trigPoly_mul_conj hcont hap S a
  have h2 := bohrMean_sub_trigPoly_mul_conj hcont hap S c
  have hre1 : (bohrMean (fun t => ((fun x => f x) t - trigPoly S a t) *
      conj ((fun x => f x) t - trigPoly S a t))).re
      = (bohrMean (fun t => f t * conj (f t))).re
        - ∑ lam ∈ S, (Complex.normSq (c lam) - Complex.normSq (a lam - c lam)) := by
    rw [h1, Complex.sub_re, Complex.re_sum]
    have hterm : ∀ lam ∈ S, (conj (a lam) * c lam + a lam * conj (c lam)
        - a lam * conj (a lam)).re
        = Complex.normSq (c lam) - Complex.normSq (a lam - c lam) :=
      fun lam _ => re_pairing_eq _ _
    rw [Finset.sum_congr rfl hterm]
  have hre2 : (bohrMean (fun t => ((fun x => f x) t - trigPoly S c t) *
      conj ((fun x => f x) t - trigPoly S c t))).re
      = (bohrMean (fun t => f t * conj (f t))).re
        - ∑ lam ∈ S, Complex.normSq (c lam) := by
    rw [h2, Complex.sub_re, Complex.re_sum]
    have hterm : ∀ lam ∈ S, (conj (c lam) * c lam + c lam * conj (c lam)
        - c lam * conj (c lam)).re = Complex.normSq (c lam) := by
      intro lam _
      rw [re_pairing_eq, sub_self]
      simp
    rw [Finset.sum_congr rfl hterm]
  -- the uniform approximant has small mean square
  have herr : (bohrMean (fun t => ((fun x => f x) t - trigPoly S a t) *
      conj ((fun x => f x) t - trigPoly S a t))).re ≤ η * η := by
    have hc' : Continuous fun t : ℝ => ((fun x => f x) t - trigPoly S a t) *
        conj ((fun x => f x) t - trigPoly S a t) :=
      (hcont.sub (continuous_trigPoly S a)).mul
        (Complex.continuous_conj.comp (hcont.sub (continuous_trigPoly S a)))
    have ha' : HTGeometry.IsBohrAlmostPeriodic fun t : ℝ =>
        ((fun x => f x) t - trigPoly S a t) * conj ((fun x => f x) t - trigPoly S a t) := by
      refine isBohrAlmostPeriodic_mul (hcont.sub (continuous_trigPoly S a))
        (isBohrAlmostPeriodic_sub hcont hap (continuous_trigPoly S a)
          (isBohrAlmostPeriodic_trigPoly S a))
        (Complex.continuous_conj.comp (hcont.sub (continuous_trigPoly S a)))
        (isBohrAlmostPeriodic_conj (isBohrAlmostPeriodic_sub hcont hap
          (continuous_trigPoly S a) (isBohrAlmostPeriodic_trigPoly S a)))
    refine le_trans (Complex.re_le_norm _) ?_
    refine norm_bohrMean_le hc' ha' fun t => ?_
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul (hclose t) (hclose t) (norm_nonneg _) hηpos.le
  -- replacing the coefficients only helps
  have hmono : ∑ lam ∈ S, Complex.normSq (c lam)
      ≥ ∑ lam ∈ S, (Complex.normSq (c lam) - Complex.normSq (a lam - c lam)) := by
    refine Finset.sum_le_sum fun lam _ => ?_
    have := Complex.normSq_nonneg (a lam - c lam)
    linarith
  rw [hre2]
  rw [hre1] at herr
  linarith [hηsq]

end

end GaloisForLFunctions

import GaloisForLFunctions.RHTower.QuietPathRigidity
import GaloisForLFunctions.RHTower.CocycleKernelTrivial

/-!
# Path-quiet multiplicative carriers are globally trivial

Arbitrary high `C¹` crossings with a vanishing length-weighted quiet budget annihilate every
nonconstant Dirichlet coefficient.  Multiplicative normalization fixes the remaining coefficient
at one, and analytic continuation makes the entire carrier identically one.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open ArithmeticFunction

/--
**Path-quiet multiplicative-carrier rigidity universality law.**  An entire,
reflection-symmetric multiplicative Dirichlet carrier admitting arbitrary top and bottom `C¹`
crossings with `(qₖ Lₖ + 1) / Tₖ² → 0` is identically one.
-/
theorem pathQuiet_symmetricMultiplicativeCarrier_eq_one
    {F : ℂ → ℂ} {a : ArithmeticFunction ℂ} {c : ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) (hc0 : 0 < c)
    (hmul : a.IsMultiplicative)
    (hF : Differentiable ℂ F)
    (hsum : LSeriesSummable (fun n => a n) c)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries (fun n => a n) s)
    (hsym : ∀ s : ℂ, F s = F (1 - s))
    (hquiet : ∃ (T q L : ℕ → ℝ) (gammaTop gammaBottom : ℕ → ℝ → ℂ),
      Filter.Tendsto T Filter.atTop Filter.atTop ∧
      (∀ k, 1 ≤ T k) ∧
      (∀ k, 0 ≤ q k) ∧
      Filter.Tendsto
        (fun k => (q k * L k + 1) / (T k) ^ 2)
        Filter.atTop (nhds 0) ∧
      ∀ k,
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          1 - c ≤ (gammaTop k t).re ∧
          (gammaTop k t).re ≤ c ∧
          T k ≤ (gammaTop k t).im ∧
          (gammaTop k t).im ≤ 2 * T k ∧
          ‖F (gammaTop k t)‖ ≤ q k) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          1 - c ≤ (gammaBottom k t).re ∧
          (gammaBottom k t).re ≤ c ∧
          -(2 * T k) ≤ (gammaBottom k t).im ∧
          (gammaBottom k t).im ≤ -(T k) ∧
          ‖F (gammaBottom k t)‖ ≤ q k) ∧
        (gammaTop k 0).re = c ∧
        (gammaTop k 1).re = 1 - c ∧
        (gammaBottom k 0).re = 1 - c ∧
        (gammaBottom k 1).re = c ∧
        (∀ t, HasDerivAt (gammaTop k)
          (deriv (gammaTop k) t) t) ∧
        (∀ t, HasDerivAt (gammaBottom k)
          (deriv (gammaBottom k) t) t) ∧
        Continuous (deriv (gammaTop k)) ∧
        Continuous (deriv (gammaBottom k)) ∧
        (∫ t in (0 : ℝ)..1, ‖deriv (gammaTop k) t‖) ≤ L k ∧
        (∫ t in (0 : ℝ)..1, ‖deriv (gammaBottom k) t‖) ≤ L k) :
    ∀ s : ℂ, F s = 1 := by
  have hsupp : ∀ n : ℕ, 2 ≤ n → a n = 0 :=
    quiet_path_rigidity hc hc0 hF hsum hFeq hsym hquiet
  have hLone : ∀ s : ℂ, c ≤ s.re → LSeries (fun n => a n) s = 1 := by
    intro s _
    have hterms :
        ∀ m : ℕ, m ≠ 1 →
          LSeries.term (fun n => a n) s m = 0 := by
      intro m hm
      rcases eq_or_ne m 0 with rfl | hm0
      · exact LSeries.term_zero (fun n => a n) s
      · rw [LSeries.term_of_ne_zero hm0, hsupp m (by omega), zero_div]
    rw [LSeries, tsum_eq_single 1 hterms,
      LSeries.term_of_ne_zero one_ne_zero,
      hmul.map_one, Nat.cast_one, Complex.one_cpow,
      one_div, inv_one]
  have hFanalytic : AnalyticOnNhd ℂ F Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
  have honeAnalytic :
      AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) Set.univ :=
    analyticOnNhd_const
  have hopen : IsOpen {s : ℂ | c < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heventual :
      F =ᶠ[nhds ((c + 1 : ℝ) : ℂ)] fun _ => 1 := by
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds ?_) fun s hs => ?_
    · simp only [Set.mem_setOf_eq, Complex.ofReal_re]
      linarith
    · exact
        (hFeq s (le_of_lt hs)).trans
          (hLone s (le_of_lt hs))
  have heq :=
    hFanalytic.eqOn_of_preconnected_of_eventuallyEq
      honeAnalytic isPreconnected_univ
      (Set.mem_univ ((c + 1 : ℝ) : ℂ)) heventual
  exact fun s => heq (Set.mem_univ s)

end

end RHTower

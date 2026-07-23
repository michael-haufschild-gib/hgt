import GaloisForLFunctions.RHTower.QuietCrossingEscalation
import GaloisForLFunctions.RHTower.CocycleKernelTrivial

/-!
# Gaussian-quiet multiplicative carriers are globally trivial

Escalated Gaussian quietness annihilates every nonconstant Dirichlet coefficient.  Multiplicative
normalization fixes the sole survivor at one, and the identity principle transports this
half-plane classification to the entire carrier.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open ArithmeticFunction

/-- **Gaussian-quiet multiplicative carrier rigidity universality law.**  An entire,
reflection-symmetric multiplicative Dirichlet carrier under the all-scale Gaussian quiet budget is
identically one.  Unlike integral cocycle rigidity, only right-half-plane representation is
required and coefficients need not be integer-valued. -/
theorem gaussianQuiet_symmetricMultiplicativeCarrier_eq_one
    {F : ℂ → ℂ} {a : ArithmeticFunction ℂ} {c : ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) (hc0 : 0 < c)
    (hmul : a.IsMultiplicative)
    (hF : Differentiable ℂ F)
    (hsum : LSeriesSummable (fun n => a n) c)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries (fun n => a n) s)
    (hsym : ∀ s : ℂ, F s = F (1 - s))
    (hquiet : ∃ (T : ℕ → ℝ) (q : ℕ → ℝ),
      Filter.Tendsto T Filter.atTop Filter.atTop ∧ (∀ k, 0 < T k) ∧
      (∀ lam : ℝ, 0 < lam →
        Filter.Tendsto (fun k => q k * Real.exp (-(T k) ^ 2 / lam))
          Filter.atTop (nhds 0)) ∧
      ∀ k, ∀ sigma : ℝ, 1 - c ≤ sigma → sigma ≤ c →
        ‖F (sigma + (T k) * Complex.I)‖ ≤ q k ∧
          ‖F (sigma - (T k) * Complex.I)‖ ≤ q k) :
    ∀ s : ℂ, F s = 1 := by
  have hsupp : ∀ n : ℕ, 2 ≤ n → a n = 0 :=
    quiet_crossing_rigidity_gaussian hc hc0 hF hsum hFeq hsym hquiet
  have hLone : ∀ s : ℂ, c ≤ s.re → LSeries (fun n => a n) s = 1 := by
    intro s _
    have hterms : ∀ m : ℕ, m ≠ 1 → LSeries.term (fun n => a n) s m = 0 := by
      intro m hm
      rcases eq_or_ne m 0 with rfl | hm0
      · exact LSeries.term_zero (fun n => a n) s
      · rw [LSeries.term_of_ne_zero hm0, hsupp m (by omega), zero_div]
    rw [LSeries, tsum_eq_single 1 hterms, LSeries.term_of_ne_zero one_ne_zero,
      hmul.map_one, Nat.cast_one, Complex.one_cpow, one_div, inv_one]
  have h1 : AnalyticOnNhd ℂ F Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
  have h2 : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) (Set.univ : Set ℂ) :=
    analyticOnNhd_const
  have hopen : IsOpen {s : ℂ | c < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hev : F =ᶠ[nhds ((c + 1 : ℝ) : ℂ)] fun _ => 1 := by
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds ?_) fun s hs => ?_
    · simp only [Set.mem_setOf_eq, Complex.ofReal_re]
      linarith
    · exact (hFeq s (le_of_lt hs)).trans (hLone s (le_of_lt hs))
  have heq := h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_univ
    (Set.mem_univ ((c + 1 : ℝ) : ℂ)) hev
  exact fun s => heq (Set.mem_univ s)

end

end RHTower

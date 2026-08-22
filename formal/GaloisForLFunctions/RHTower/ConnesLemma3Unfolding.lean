import GaloisForLFunctions.RHTower.ConnesOrbitEnergy

/-!
# Appendix I Lemma 3: the unfolding identity

Appendix I Lemma 3 of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `∫_{C_k} E(f)(x) Χ_0(x) |x|^{s-1/2} d^*x = c L(Χ_0,s) Δ'_s(f)`,   `f ∈ 𝒮(A)_0`.

Connes proves it by *"for `σ > 1` the equality follows from Lemma 1, but since both sides are
analytic in `s` it holds in general"*.  The continuation half is `ConnesMellinContinuation`; this
file supplies the other half, the passage from Lemma 1 to the statement about the periodization.

With `E(f)(x) = |x|^{1/2} ∑_{q ∈ k^*} f(qx)` the integrand on the left is
`(∑_q f(qx)) · Χ_0(x)|x|^s`, and `Χ_0(x)|x|^s` is invariant under `k^*` (a character of the idele
class group; `|q| = 1` by the product formula).  So Lemma 3's left side is the fundamental-domain
integral of the periodization against a *invariant* weight, and unfolding turns it into the
ambient integral `∫_{A^*} f(x)Χ_0(x)|x|^s d^*x` — which is Lemma 1's `Δ_s(f)`.  That unfolding is
what is proved here, in the same generality as the quadratic version of `ConnesOrbitEnergy`.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {G X : Type*} [Group G] [MulAction G X]

/-- **Appendix I Lemma 3, the unfolding step.**  Against a weight invariant under the group, the
ambient integral of `f` is the fundamental-domain integral of the periodization of `f`. -/
theorem connes_periodization_pairing_unfold
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasurableSpace G] [MeasurableSMul G X] [MeasureTheory.SMulInvariantMeasure G X μ]
    [Countable G] {F : Set X} (hF : MeasureTheory.IsFundamentalDomain G F μ)
    (f : X → ℂ) (φ : X → ℂ)
    (hinv : ∀ (q : G) (x : X), φ (q • x) = φ x)
    (hint : MeasureTheory.Integrable (fun x => f x * φ x) μ)
    (hqint : ∀ q : G, MeasureTheory.IntegrableOn (fun x => f (q • x) * φ x) F μ)
    (hsum : Summable fun q : G => ∫ x in F, ‖f (q • x) * φ x‖ ∂μ) :
    (∫ x, f x * φ x ∂μ) = ∫ x in F, (∑' q : G, f (q • x)) * φ x ∂μ := by
  have hstep1 : (∫ x, f x * φ x ∂μ)
      = ∑' g : G, ∫ x in F, f (g • x) * φ x ∂μ := by
    rw [hF.integral_eq_tsum' _ hint]
    have hre := (Equiv.inv G).tsum_eq
      (fun g : G => ∫ x in F, f (g • x) * φ x ∂μ)
    rw [← hre]
    refine tsum_congr fun g => ?_
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show f (g⁻¹ • x) * φ (g⁻¹ • x) = f (g⁻¹ • x) * φ x
    rw [hinv g⁻¹ x]
  rw [hstep1, MeasureTheory.integral_tsum_of_summable_integral_norm hqint hsum]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact tsum_mul_right

end

end GaloisForLFunctions.RHTower

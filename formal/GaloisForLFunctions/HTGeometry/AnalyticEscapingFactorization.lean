import GaloisForLFunctions.HTGeometry.AnalyticPolynomialDivisionGerm
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Exact analytic separation of a packet escaping to infinity

Analytic scaled root branches give an escaping divisor whose leading
coefficient vanishes at the contact, but whose constant coefficient is a
unit. Triangular division then produces the analytic monic finite factor.
-/

open Filter Topology Polynomial

namespace GaloisForLFunctions.HTGeometry
noncomputable section

variable {ι : Type*} [Fintype ι]

def escapingRootFactor (r : ι → ℝ → ℂ) (a t : ℝ) : ℂ[X] :=
  ∏ i, (X - C (r i t / ((t - a : ℝ) : ℂ)))

def scaledEscapingRootFactor (r : ι → ℝ → ℂ) (a t : ℝ) : ℂ[X] :=
  ∏ i, (C ((t - a : ℝ) : ℂ) * X - C (r i t))

theorem escapingRootFactor_monic (r : ι → ℝ → ℂ) (a t : ℝ) :
    (escapingRootFactor r a t).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem escapingRootFactor_natDegree (r : ι → ℝ → ℂ) (a t : ℝ) :
    (escapingRootFactor r a t).natDegree = Fintype.card ι := by
  unfold escapingRootFactor
  rw [natDegree_prod_of_monic Finset.univ _ (fun _ _ => monic_X_sub_C _)]
  simp

theorem scaledEscapingRootFactor_at (r : ι → ℝ → ℂ) (a : ℝ) :
    scaledEscapingRootFactor r a a = C (∏ i, -r i a) := by
  simp [scaledEscapingRootFactor, map_prod]

theorem scaledEscapingRootFactor_eq (r : ι → ℝ → ℂ) (a t : ℝ) (hta : t ≠ a) :
    scaledEscapingRootFactor r a t =
      C (((t - a : ℝ) : ℂ) ^ Fintype.card ι) * escapingRootFactor r a t := by
  have hε : ((t - a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hta)
  have he (i : ι) : C ((t - a : ℝ) : ℂ) * X - C (r i t) =
      C ((t - a : ℝ) : ℂ) * (X - C (r i t / ((t - a : ℝ) : ℂ))) := by
    rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hε]
  simp only [scaledEscapingRootFactor, he, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ← map_pow, escapingRootFactor]

theorem analyticAt_scaledEscapingRootFactor_coeff {r : ι → ℝ → ℂ} {a : ℝ}
    (hr : ∀ i, AnalyticAt ℝ (r i) a) (j : ℕ) :
    AnalyticAt ℝ (fun t => (scaledEscapingRootFactor r a t).coeff j) a := by
  have hε : AnalyticAt ℝ (fun t : ℝ => ((t - a : ℝ) : ℂ)) a :=
    (Complex.ofRealCLM.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  apply analyticAt_polynomial_prod_coeff
  intro i _ l
  by_cases hl : l = 0
  · subst l
    simpa only [coeff_sub, coeff_C_mul, coeff_X_zero, coeff_C_zero, mul_zero,
      zero_sub, Pi.neg_apply] using! (hr i).neg
  · simpa only [coeff_sub, coeff_C_mul, coeff_C, if_neg hl, sub_zero, Pi.mul_apply] using!
      hε.mul (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (X : ℂ[X]).coeff l) a)

/-- The finite quotient is analytic and monic, and the scaled factorization
holds across the contact. No condition is imposed on the finite roots. -/
theorem analytic_finite_factor_of_escaping_roots
    {p S : ℝ → ℂ[X]} {r : ι → ℝ → ℂ} {a : ℝ} {n k : ℕ}
    (hcard : Fintype.card ι = k)
    (hp : ∀ t, (p t).Monic ∧ (p t).natDegree = n + k)
    (hS : ∀ i, AnalyticAt ℝ (fun t => (S t).coeff i) a)
    (hscale : ∀ᶠ t in 𝓝[≠] a, S t = C (((t - a : ℝ) : ℂ) ^ k) * p t)
    (hr : ∀ i, AnalyticAt ℝ (r i) a) (hr0 : ∀ i, r i a ≠ 0)
    (hroots : ∀ᶠ t in 𝓝[≠] a,
      (∀ i, (p t).eval (r i t / ((t - a : ℝ) : ℂ)) = 0) ∧
      Function.Injective (fun i => r i t / ((t - a : ℝ) : ℂ))) :
    ∃ F : ℝ → ℂ[X], (∀ t, (F t).Monic ∧ (F t).natDegree = n) ∧
      (∀ i, AnalyticAt ℝ (fun t => (F t).coeff i) a) ∧
      (∀ᶠ t in 𝓝[≠] a, p t = escapingRootFactor r a t * F t) ∧
      (∀ᶠ t in 𝓝 a, S t = scaledEscapingRootFactor r a t * F t) ∧
      S a = C (∏ i, -r i a) * F a := by
  classical
  let E := scaledEscapingRootFactor r a
  let B := escapingRootFactor r a
  let D : ℝ → ℂ[X] := fun t => p t /ₘ B t
  have hBm (t : ℝ) : (B t).Monic := escapingRootFactor_monic _ _ _
  have hBD : ∀ᶠ t in 𝓝[≠] a, p t = B t * D t := by
    filter_upwards [hroots] with t ht
    have hd : B t ∣ p t := Fintype.prod_dvd_of_coprime
      (pairwise_coprime_X_sub_C ht.2) (fun i => dvd_iff_isRoot.mpr (ht.1 i))
    have he := modByMonic_add_div (p t) (B t)
    rw [(modByMonic_eq_zero_iff_dvd (hBm t)).mpr hd, zero_add] at he
    exact he.symm
  have hD : ∀ᶠ t in 𝓝[≠] a, (D t).Monic ∧ (D t).natDegree = n := by
    filter_upwards [hBD] with t ht
    refine ⟨(hBm t).of_mul_monic_left (by rw [← ht]; exact (hp t).1), ?_⟩
    change (p t /ₘ escapingRootFactor r a t).natDegree = n
    rw [natDegree_divByMonic _ (hBm t), (hp t).2,
      escapingRootFactor_natDegree, hcard, Nat.add_sub_cancel]
  have hSE : ∀ᶠ t in 𝓝[≠] a, S t = E t * D t := by
    filter_upwards [hscale, hBD, self_mem_nhdsWithin] with t ht hbt hta
    rw [ht, hbt]
    change _ = scaledEscapingRootFactor r a t * D t
    rw [scaledEscapingRootFactor_eq _ _ _ hta, hcard, mul_assoc]
  have hE0 : (E a).coeff 0 ≠ 0 := by
    change (scaledEscapingRootFactor r a a).coeff 0 ≠ 0
    rw [scaledEscapingRootFactor_at, coeff_C_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => neg_ne_zero.mpr (hr0 i))
  obtain ⟨F, hFm, hFa, hFD, hcontact⟩ := analytic_monic_factor_extension
    hS (analyticAt_scaledEscapingRootFactor_coeff hr) hE0 hSE hD
  have hSF : ∀ᶠ t in 𝓝[≠] a, S t = E t * F t := by
    filter_upwards [hSE, hFD] with t ht hft
    rw [hft, ht]
  refine ⟨F, hFm, hFa, ?_, ?_, ?_⟩
  · filter_upwards [hBD, hFD] with t ht hft
    rw [hft]
    exact ht
  · rw [eventually_nhdsWithin_iff] at hSF
    filter_upwards [hSF] with t ht
    by_cases hta : t = a
    · subst t
      exact hcontact
    · exact ht hta
  · simpa only [E, scaledEscapingRootFactor_at] using hcontact

end
end GaloisForLFunctions.HTGeometry

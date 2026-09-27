import GaloisForLFunctions.HTGeometry.EntireAlgebraicRatioRational
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval

/-!
# `ℂ(z)` is relatively algebraically closed in the global meromorphic field

A meromorphic function on `ℂ` that is algebraic over `ℂ(z)` is rational.  Writing it as a ratio
`g/h` of entire germs and clearing denominators in an algebraic relation over `ℂ[z]` gives a
homogeneous identity `∑ qᵢ(z) g(z)ⁱ h(z)^(d-i) = 0` of entire functions; the analytic-order argument
of `EntireAlgebraicRatioRational` then produces `ℓ g = r h` with polynomials `ℓ ≠ 0, r`.

Consequently every subfield of the global meromorphic field is a regular extension of `ℂ(z)` —
in particular the function field `ℂ(z, f, f')` of a first-order differential-algebraic entire
function.
-/

open Filter Set Polynomial

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-- **Regularity of meromorphic function fields over `ℂ(z)`.**  An element of the global
meromorphic field that is algebraic over `ℂ(z)` lies in `ℂ(z)`. -/
theorem exists_ratfuncToMero_eq_of_isAlgebraic (x : meroField (Set.univ : Set ℂ))
    (hx : letI := (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
        Set.infinite_univ).toAlgebra
      IsAlgebraic (RatFunc ℂ) x) :
    ∃ r : RatFunc ℂ, ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ r = x := by
  classical
  letI algK : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
    (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ).toAlgebra
  letI algA : Algebra (Polynomial ℂ) (meroField (Set.univ : Set ℂ)) :=
    (polyToMero Set.univ).toAlgebra
  haveI hst : IsScalarTower (Polynomial ℂ) (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) := by
    apply IsScalarTower.of_algebraMap_eq
    intro p
    show polyToMero Set.univ p = ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
    rw [ratfuncToMero_algebraMap_polynomial]
  haveI hdom := isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ
    Set.univ_nonempty
  rw [← IsFractionRing.isAlgebraic_iff (Polynomial ℂ) (RatFunc ℂ)
    (meroField (Set.univ : Set ℂ))] at hx
  obtain ⟨q, hq0, hqe⟩ := hx
  obtain ⟨⟨a, b⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (nonZeroDivisors (analyticSubring (Set.univ : Set ℂ))) x
  dsimp only at hqe ⊢
  obtain ⟨g, hg, hga⟩ := a.2
  obtain ⟨h, hh, hhb⟩ := (b : analyticSubring (Set.univ : Set ℂ)).2
  set d := q.natDegree
  let ι := algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
  have hb0 : (b : analyticSubring (Set.univ : Set ℂ)) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hB : ι b ≠ 0 := by
    rw [ne_eq, meroField_algebraMap_eq_zero_iff _ isOpen_univ isPreconnected_univ
      Set.univ_nonempty]
    exact hb0
  -- the germ relation
  let S : analyticSubring (Set.univ : Set ℂ) := ∑ i ∈ Finset.range (d + 1),
    polyToAnalytic Set.univ (q.coeff i) * a ^ i * (b : analyticSubring Set.univ) ^ (d - i)
  have hS : ι S = 0 := by
    have hmk : IsLocalization.mk' (meroField (Set.univ : Set ℂ)) a b = ι a / ι b := by
      rw [IsFractionRing.mk'_eq_div]
    rw [Polynomial.aeval_eq_sum_range, hmk] at hqe
    have hmul := congrArg (fun y => ι b ^ d * y) hqe
    simp only [mul_zero] at hmul
    rw [← hmul, Finset.mul_sum]
    simp only [S, map_sum, map_mul, map_pow]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Algebra.smul_def, div_pow]
    have halg : algebraMap (Polynomial ℂ) (meroField (Set.univ : Set ℂ)) (q.coeff i) =
        ι (polyToAnalytic Set.univ (q.coeff i)) := rfl
    rw [halg]
    have hpow : ι b ^ d = ι b ^ (d - i) * ι b ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hi']
    rw [hpow]
    field_simp
  have hS0 : S = 0 := by
    rwa [meroField_algebraMap_eq_zero_iff _ isOpen_univ isPreconnected_univ
      Set.univ_nonempty] at hS
  -- read the germ relation pointwise
  have hrel : ∀ z, ∑ i ∈ Finset.range (d + 1),
      (q.coeff i).eval z * g z ^ i * h z ^ (d - i) = 0 := by
    have hgerm : ((S : Germ (Filter.principal (Set.univ : Set ℂ)) ℂ)) =
        ((fun z => ∑ i ∈ Finset.range (d + 1),
          (q.coeff i).eval z * g z ^ i * h z ^ (d - i) : ℂ → ℂ) :
            Germ (Filter.principal (Set.univ : Set ℂ)) ℂ) := by
      change (analyticSubring (Set.univ : Set ℂ)).subtype S = Germ.coeRingHom _ _
      simp only [S, map_sum, map_mul, map_pow]
      rw [show (fun z => ∑ i ∈ Finset.range (d + 1),
          (q.coeff i).eval z * g z ^ i * h z ^ (d - i)) =
          ∑ i ∈ Finset.range (d + 1), (fun z => (q.coeff i).eval z) * g ^ i * h ^ (d - i) by
        funext z; simp, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, map_mul, map_pow, map_pow]
      have ha' : (analyticSubring (Set.univ : Set ℂ)).subtype a = Germ.coeRingHom _ g := hga.symm
      have hb' : (analyticSubring (Set.univ : Set ℂ)).subtype (b : analyticSubring Set.univ) =
          Germ.coeRingHom _ h := hhb.symm
      rw [ha', hb']
      rfl
    rw [hS0, ZeroMemClass.coe_zero] at hgerm
    have hev := (Germ.coe_eq.mp (hgerm.symm.trans (Germ.coe_zero).symm))
    intro z
    exact eventually_principal.mp hev z (Set.mem_univ z)
  have hgd : Differentiable ℂ g := fun z => (hg z (Set.mem_univ z)).differentiableAt
  have hhd : Differentiable ℂ h := fun z => (hh z (Set.mem_univ z)).differentiableAt
  have hh0 : ∃ z, h z ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hb0
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero, ← hhb]
    change (↑h : Germ (Filter.principal (Set.univ : Set ℂ)) ℂ) = ↑(0 : ℂ → ℂ)
    exact Germ.coe_eq.mpr (Eventually.of_forall hall)
  obtain ⟨r, hr⟩ := exists_polynomial_mul_eq_of_algebraic_ratio hgd hhd hh0 q hq0 hrel
  have hℓ : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
  refine ⟨algebraMap (Polynomial ℂ) (RatFunc ℂ) r /
    algebraMap (Polynomial ℂ) (RatFunc ℂ) q.leadingCoeff, ?_⟩
  rw [map_div₀, ratfuncToMero_algebraMap_polynomial, ratfuncToMero_algebraMap_polynomial,
    IsFractionRing.mk'_eq_div]
  change _ = ι a / ι b
  have hℓM : polyToMero Set.univ q.leadingCoeff ≠ 0 := by
    intro h0
    exact hℓ (polyToMero_injective _ isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ (by rw [h0, map_zero]))
  rw [div_eq_div_iff hℓM hB]
  change ι (polyToAnalytic Set.univ r) * ι b = ι a * ι (polyToAnalytic Set.univ q.leadingCoeff)
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subring.coe_mul]
  rw [← hga, ← hhb]
  change Germ.coeRingHom _ (fun z => r.eval z) * Germ.coeRingHom _ h =
    Germ.coeRingHom _ g * Germ.coeRingHom _ (fun z => q.leadingCoeff.eval z)
  rw [← map_mul, ← map_mul]
  congr 1
  funext z
  simp only [Pi.mul_apply]
  rw [mul_comm (g z), hr z]

end

end GaloisForLFunctions.HTGeometry

import Mathlib

/-!
# A Serre-type normality criterion

Let `A` be a Noetherian domain such that

* every associated prime of `A / aA` (`a ≠ 0`) has height one, and
* the localization at every height-one prime is integrally closed.

Then `A` is integrally closed.  For `x = b/a` integral over `A`, the conductor
`J = {c : cb ∈ aA}` embeds `A/J` into `A/aA` by `c ↦ cb`, so any associated prime `Q` of `A/J` is an
associated prime of `A/aA`, of height one, and contains `J`.  But `x` lies in the integrally closed
`A_Q`, so `sx ∈ A` for some `s ∉ Q`, i.e. `s ∈ J ⊆ Q` — unless `J = A`, which is `x ∈ A`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [CommRing A]

/-- Multiplication by `b` into `A/aA`. -/
noncomputable def mulIntoQuot (a b : A) : A →ₗ[A] A ⧸ Ideal.span {a} :=
  LinearMap.toSpanSingleton A _ (Ideal.Quotient.mk _ b)

theorem mem_ker_mulIntoQuot {a b c : A} : c ∈ LinearMap.ker (mulIntoQuot a b) ↔ c * b ∈ Ideal.span {a} := by
  rw [LinearMap.mem_ker, mulIntoQuot, LinearMap.toSpanSingleton_apply, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]

/-- The conductor's quotient embeds in `A/aA`. -/
theorem associatedPrimes_quot_ker_subset (a b : A) :
    associatedPrimes A (A ⧸ LinearMap.ker (mulIntoQuot a b)) ⊆
      associatedPrimes A (A ⧸ Ideal.span {a}) := by
  let e := (mulIntoQuot a b).quotKerEquivRange
  have hinj : Function.Injective ((LinearMap.range (mulIntoQuot a b)).subtype ∘ₗ e.toLinearMap) :=
    (Submodule.injective_subtype _).comp e.injective
  exact associatedPrimes.subset_of_injective hinj

theorem le_of_mem_associatedPrimes_quot {J Q : Ideal A} (hQ : Q ∈ associatedPrimes A (A ⧸ J)) :
    J ≤ Q := by
  obtain ⟨_, v, hv⟩ := hQ
  intro c hc
  rw [hv]
  refine Ideal.le_radical ?_
  rw [Submodule.mem_colon]
  intro p hp
  rw [Set.mem_singleton_iff.mp hp]
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective J v
  rw [← Submodule.Quotient.mk_smul, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
  exact J.mul_mem_right w hc

variable [IsDomain A] [IsNoetherianRing A]

/-- **The Serre-type normality criterion.** -/
theorem isIntegrallyClosed_of_height_one
    (hS2 : ∀ a : A, a ≠ 0 → ∀ Q ∈ associatedPrimes A (A ⧸ Ideal.span {a}), Q.height = 1)
    (hR1 : ∀ (P : Ideal A) [P.IsPrime], P.height = 1 →
      IsIntegrallyClosed (Localization.AtPrime P)) :
    IsIntegrallyClosed A := by
  classical
  set K := FractionRing A
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨b, a, ha, rfl⟩ := IsFractionRing.div_surjective A x
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  set J := LinearMap.ker (mulIntoQuot a b) with hJ
  by_cases htop : J = ⊤
  · have h1 : (1 : A) ∈ J := by rw [htop]; exact Submodule.mem_top
    rw [mem_ker_mulIntoQuot, one_mul, Ideal.mem_span_singleton] at h1
    obtain ⟨y, rfl⟩ := h1
    refine ⟨y, ?_⟩
    have hak : algebraMap A K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
    rw [map_mul, mul_div_cancel_left₀ _ hak]
  exfalso
  haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr htop
  obtain ⟨Q, hQ⟩ := associatedPrimes.nonempty A (A ⧸ J)
  have hQprime : Q.IsPrime := hQ.1
  have hJQ : J ≤ Q := le_of_mem_associatedPrimes_quot hQ
  have hQa := associatedPrimes_quot_ker_subset a b hQ
  have hht : Q.height = 1 := hS2 a ha0 Q hQa
  haveI := hR1 Q hht
  haveI : IsFractionRing (Localization.AtPrime Q) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl
      (Localization.AtPrime Q) K
  have hxloc : IsIntegral (Localization.AtPrime Q) (algebraMap A K b / algebraMap A K a) :=
    hx.tower_top
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).mp ‹IsIntegrallyClosed (Localization.AtPrime Q)› hxloc
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl y
  have hspec := IsLocalization.mk'_spec (Localization.AtPrime Q) c s
  have hspecK := congrArg (algebraMap (Localization.AtPrime Q) K) hspec
  simp only [map_mul, ← IsScalarTower.algebraMap_apply] at hspecK
  simp only at hy
  rw [hy] at hspecK
  have hs : (s : A) ∉ Q := s.2
  have hsK : algebraMap A K s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero fun h => hs (h ▸ Q.zero_mem))
  have hak : algebraMap A K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
  -- `s b = c a`
  have hsb : (s : A) * b = c * a := by
    apply IsFractionRing.injective A K
    rw [map_mul, map_mul, ← hspecK, div_mul_eq_mul_div, div_mul_cancel₀ _ hak]
    ring
  have hsJ : (s : A) ∈ J := by
    rw [mem_ker_mulIntoQuot, hsb, Ideal.mem_span_singleton]
    exact dvd_mul_left a c
  exact hs (hJQ hsJ)

end GaloisForLFunctions.HTGeometry

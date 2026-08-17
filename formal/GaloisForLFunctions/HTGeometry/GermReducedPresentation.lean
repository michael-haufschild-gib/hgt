import GaloisForLFunctions.HTGeometry.GermReducedTransition
import GaloisForLFunctions.HTGeometry.SiegelClearedCombination

/-!
# Reduced local presentations and the unit that relates them

Every fraction of germs reduces, so a meromorphic germ has a presentation whose numerator and
denominator are relatively prime.  Two such presentations of the same fraction differ by a single
unit factor, the *same* one for numerator and denominator: associated denominators give the unit,
and cancelling the nonzero denominator in the cross identity transports it to the numerators.

For a denominator-cleared Siegel combination the consequence is exact and division-free: passing
from one reduced presentation to another multiplies the combination by the `m`-th power of the
product of the unit factors, with no hypothesis on where the denominators vanish.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric

variable {n : ℕ}

/-- **Every germ fraction has a reduced presentation at an arbitrary point.** -/
theorem exists_reduced_presentation_at {c : Fin n → ℂ} {A B : (Fin n → ℂ) → ℂ}
    (hA : AnalyticAt ℂ A c) (hB : AnalyticAt ℂ B c) (hB0 : ¬ B =ᶠ[𝓝 c] 0) :
    ∃ (A' B' : (Fin n → ℂ) → ℂ) (hA' : AnalyticAt ℂ A' c) (hB' : AnalyticAt ℂ B' c),
      ¬ B' =ᶠ[𝓝 c] 0 ∧ IsRelPrime (analyticGermOf hA') (analyticGermOf hB') ∧
        (fun w => A w * B' w) =ᶠ[𝓝 c] fun w => A' w * B w := by
  classical
  letI := uniqueFactorizationMonoid_analyticGerm c
  letI := UniqueFactorizationMonoid.toGCDMonoid (AnalyticGerm c)
  have hBne : analyticGermOf hB ≠ 0 := by
    intro h
    refine hB0 ?_
    have := congrArg (fun x : AnalyticGerm c => (x : Germ (𝓝 c) ℂ)) h
    rw [analyticGermOf_val, ZeroMemClass.coe_zero] at this
    exact Germ.coe_eq.mp this
  obtain ⟨a', b', hb'0, hrel, hcross⟩ :=
    exists_reduced_fraction (analyticGermOf hA) (analyticGermOf hB) hBne
  obtain ⟨A', hA'A, hA'eq⟩ := a'.2
  obtain ⟨B', hB'A, hB'eq⟩ := b'.2
  have ha'eq : a' = analyticGermOf hA'A := Subtype.ext hA'eq.symm
  have hb'eq : b' = analyticGermOf hB'A := Subtype.ext hB'eq.symm
  refine ⟨A', B', hA'A, hB'A, ?_, ?_, ?_⟩
  · intro h
    refine hb'0 ?_
    rw [hb'eq]
    exact analyticGermOf_eq_zero hB'A h
  · rw [← ha'eq, ← hb'eq]
    exact hrel
  · refine (analyticGermOf_eq_iff (hA.mul hB'A) (hA'A.mul hB)).mp ?_
    rw [analyticGermOf_mul hA hB'A, analyticGermOf_mul hA'A hB, ← ha'eq, ← hb'eq]
    exact hcross

/-- **Two reduced presentations of the same fraction differ by one unit factor.** -/
theorem exists_unit_factor_of_reduced_at {w : Fin n → ℂ} {A₁ B₁ A₂ B₂ : (Fin n → ℂ) → ℂ}
    (hA₁ : AnalyticAt ℂ A₁ w) (hB₁ : AnalyticAt ℂ B₁ w)
    (hA₂ : AnalyticAt ℂ A₂ w) (hB₂ : AnalyticAt ℂ B₂ w)
    (hred₁ : IsRelPrime (analyticGermOf hA₁) (analyticGermOf hB₁))
    (hred₂ : IsRelPrime (analyticGermOf hA₂) (analyticGermOf hB₂))
    (hB₂0 : ¬ B₂ =ᶠ[𝓝 w] 0)
    (hcross : (fun v => A₁ v * B₂ v) =ᶠ[𝓝 w] fun v => A₂ v * B₁ v) :
    ∃ (v : (Fin n → ℂ) → ℂ), AnalyticAt ℂ v w ∧ v w ≠ 0 ∧
      A₁ =ᶠ[𝓝 w] (fun z => v z * A₂ z) ∧ B₁ =ᶠ[𝓝 w] fun z => v z * B₂ z := by
  classical
  have hassoc : Associated (analyticGermOf hB₁) (analyticGermOf hB₂) :=
    associated_den_of_reduced_at hA₁ hB₁ hA₂ hB₂ hred₁ hred₂ hcross
  obtain ⟨U, hU⟩ := hassoc
  -- the inverse unit is the factor turning the second presentation into the first
  obtain ⟨v, hvA, hveq⟩ := ((U⁻¹ : (AnalyticGerm w)ˣ) : AnalyticGerm w).2
  have hvgerm : ((U⁻¹ : (AnalyticGerm w)ˣ) : AnalyticGerm w) = analyticGermOf hvA :=
    Subtype.ext hveq.symm
  have hvunit : IsUnit (analyticGermOf hvA) := by
    rw [← hvgerm]
    exact (U⁻¹).isUnit
  have hvne : v w ≠ 0 := by
    have := (isUnit_analyticGerm_iff (analyticGermOf hvA)).mp hvunit
    rwa [analyticGermValue_of hvA] at this
  have hBgerm : analyticGermOf hB₁ = analyticGermOf hvA * analyticGermOf hB₂ := by
    rw [← hvgerm, ← hU]
    rw [show (analyticGermOf hB₁ * (U : AnalyticGerm w)) = (U : AnalyticGerm w) * analyticGermOf hB₁
      from mul_comm _ _, ← mul_assoc]
    rw [show ((U⁻¹ : (AnalyticGerm w)ˣ) : AnalyticGerm w) * (U : AnalyticGerm w) = 1 from
      U.inv_mul, one_mul]
  have hB₂ne : analyticGermOf hB₂ ≠ 0 := by
    intro h
    exact hB₂0 ((analyticGermOf_eq_iff hB₂ analyticAt_const).mp (by rw [h]; rfl))
  have hAgerm : analyticGermOf hA₁ = analyticGermOf hvA * analyticGermOf hA₂ := by
    have hc : analyticGermOf hA₁ * analyticGermOf hB₂ = analyticGermOf hA₂ * analyticGermOf hB₁ := by
      rw [← analyticGermOf_mul hA₁ hB₂, ← analyticGermOf_mul hA₂ hB₁]
      exact analyticGermOf_congr _ _ hcross
    refine mul_right_cancel₀ hB₂ne ?_
    rw [hc, hBgerm]
    ring
  refine ⟨v, hvA, hvne, ?_, ?_⟩
  · refine (analyticGermOf_eq_iff hA₁ (hvA.mul hA₂)).mp ?_
    rw [analyticGermOf_mul hvA hA₂]
    exact hAgerm
  · refine (analyticGermOf_eq_iff hB₁ (hvA.mul hB₂)).mp ?_
    rw [analyticGermOf_mul hvA hB₂]
    exact hBgerm

/-- **The cleared combination transforms by the product of the unit factors.** -/
theorem siegelHomCombination_of_unit_factors {N m : ℕ} {E : Type*}
    (A₁ B₁ A₂ B₂ : Fin (N + 1) → E → ℂ) (v : Fin (N + 1) → E → ℂ)
    (hA : ∀ k z, A₁ k z = v k z * A₂ k z) (hB : ∀ k z, B₁ k z = v k z * B₂ k z)
    (a : (Fin (N + 1) → Fin (m + 1)) → ℂ) (z : E) :
    siegelHomCombination A₁ B₁ m a z
      = (∏ k, (v k z) ^ m) * siegelHomCombination A₂ B₂ m a z := by
  rw [siegelHomCombination, siegelHomCombination, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hstep : ∀ k : Fin (N + 1),
      (A₁ k z) ^ (β k : ℕ) * (B₁ k z) ^ (m - (β k : ℕ))
        = (v k z) ^ m * ((A₂ k z) ^ (β k : ℕ) * (B₂ k z) ^ (m - (β k : ℕ))) := by
    intro k
    have hk : (β k : ℕ) ≤ m := Nat.lt_succ_iff.mp (β k).2
    rw [hA k z, hB k z, mul_pow, mul_pow]
    rw [show (v k z) ^ (β k : ℕ) * (A₂ k z) ^ (β k : ℕ)
        * ((v k z) ^ (m - (β k : ℕ)) * (B₂ k z) ^ (m - (β k : ℕ)))
      = ((v k z) ^ (β k : ℕ) * (v k z) ^ (m - (β k : ℕ)))
        * ((A₂ k z) ^ (β k : ℕ) * (B₂ k z) ^ (m - (β k : ℕ))) from by ring]
    rw [← pow_add, show (β k : ℕ) + (m - (β k : ℕ)) = m from by omega]
  calc a β * ∏ k, (A₁ k z) ^ (β k : ℕ) * (B₁ k z) ^ (m - (β k : ℕ))
      = a β * ∏ k, (v k z) ^ m * ((A₂ k z) ^ (β k : ℕ) * (B₂ k z) ^ (m - (β k : ℕ))) := by
        rw [Finset.prod_congr rfl fun k _ => hstep k]
    _ = (∏ k, (v k z) ^ m) * (a β * ∏ k, (A₂ k z) ^ (β k : ℕ) * (B₂ k z) ^ (m - (β k : ℕ))) := by
        rw [Finset.prod_mul_distrib]
        ring

end GaloisForLFunctions.HTGeometry

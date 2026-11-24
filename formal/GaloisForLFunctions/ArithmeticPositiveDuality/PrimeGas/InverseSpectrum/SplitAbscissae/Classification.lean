import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.SplitAbscissae.Domains
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.SplitAbscissae.Profiles

/-! # All individual split domains, already on each single prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

private theorem critical_finite (v : MissingWave) : finiteSplit v ((1/2:ℝ):ℂ) :=
  (forall_finiteSplit_iff _).mpr le_rfl v

private theorem zero_infinite (v : MissingWave) : ¬ finiteSplit v 0 :=
  fun h => (lt_irrefl (0:ℝ)) ((exists_finiteSplit_iff 0).mp ⟨v,h⟩)

/-- Every allowed open half-plane, including the one starting at zero, occurs on any chosen elementary prime. -/
theorem open_prime_domain_iff (p : Nat.Primes) (θ : ℝ) :
    (∃ v : MissingWave, onPrimeRay p v.val ∧ ∀ s : ℂ, finiteSplit v s ↔ θ < s.re) ↔
      0 ≤ θ ∧ θ < 1/2 := by
  constructor
  · rintro ⟨v,_,h⟩
    exact ⟨le_of_not_gt (fun h0 => zero_infinite v ((h 0).mpr h0)),(h _).mp (critical_finite v)⟩
  · rintro ⟨h0,hc⟩
    have he (x : ℝ) : momentAdmitted θ 0 x 0 ↔ θ < x := by simp [momentAdmitted]
    obtain ⟨v,hp,hv⟩ := (prime_moment_profile_iff p θ 0).mpr ⟨(he _).mpr hc,fun h => h0.not_gt ((he _).mp h)⟩
    exact ⟨v,hp,fun s => (zeroth_energyMoment_iff v s).symm.trans ((hv s 0).trans (he _))⟩

/-- Closed half-planes include the critical endpoint and exclude zero as an endpoint. -/
theorem closed_prime_domain_iff (p : Nat.Primes) (θ : ℝ) :
    (∃ v : MissingWave, onPrimeRay p v.val ∧ ∀ s : ℂ, finiteSplit v s ↔ θ ≤ s.re) ↔
      0 < θ ∧ θ ≤ 1/2 := by
  constructor
  · rintro ⟨v,_,h⟩
    exact ⟨lt_of_not_ge (fun h0 => zero_infinite v ((h 0).mpr h0)),(h _).mp (critical_finite v)⟩
  · rintro ⟨h0,hc⟩
    have he (x : ℝ) : momentAdmitted θ 2 x 0 ↔ θ ≤ x := by
      change (θ < x ∨ θ = x ∧ (0:ℕ)+1 < 2) ↔ θ ≤ x
      exact ⟨fun h => h.elim le_of_lt (fun he => he.1.le),
        fun h => h.lt_or_eq.imp_right (fun he => ⟨he,by norm_num⟩)⟩
    obtain ⟨v,hp,hv⟩ := (prime_moment_profile_iff p θ 2).mpr ⟨(he _).mpr hc,fun h => h0.not_ge ((he _).mp h)⟩
    exact ⟨v,hp,fun s => (zeroth_energyMoment_iff v s).symm.trans ((hv s 0).trans (he _))⟩

/-- All exterior split domains can be reproduced using only the powers of each specified prime. -/
theorem one_prime_reproduces_split_domain (p : Nat.Primes) (v : MissingWave) :
    ∃ w : MissingWave, onPrimeRay p w.val ∧ ∀ s : ℂ, finiteSplit w s ↔ finiteSplit v s := by
  let a := splitAbscissa v
  have hl := splitAbscissa_bounds v
  by_cases hb : finiteSplit v ((a:ℝ):ℂ)
  · obtain ⟨w,hp,hw⟩ := (closed_prime_domain_iff p a).mpr ⟨(splitBoundary_constraints v).1 hb,hl.2⟩
    refine ⟨w,hp,fun s => (hw s).trans ?_⟩
    rw [finiteSplit_iff_abscissa]
    exact ⟨fun h => h.lt_or_eq.imp_right (fun he => ⟨he,hb⟩),fun h => h.elim le_of_lt (fun he => he.1.le)⟩
  · obtain ⟨w,hp,hw⟩ := (open_prime_domain_iff p a).mpr ⟨hl.1,(splitBoundary_constraints v).2 hb⟩
    refine ⟨w,hp,fun s => (hw s).trans ?_⟩
    rw [finiteSplit_iff_abscissa]
    exact ⟨Or.inl,fun h => h.resolve_right (fun he => hb he.2)⟩

#print axioms open_prime_domain_iff
#print axioms closed_prime_domain_iff
#print axioms one_prime_reproduces_split_domain

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

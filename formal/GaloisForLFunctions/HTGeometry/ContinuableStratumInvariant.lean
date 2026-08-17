import GaloisForLFunctions.HTGeometry.HelsonZetaEulerProduct

/-!
# The continuable stratum is a tail event

Changing the phase at finitely many primes multiplies the Helson zeta function by a finite product
of ratios of entire functions,

```text
∏_{p ∈ S} (1 - χ_p p^{-s}) / (1 - ψ_p p^{-s}) ,
```

each of which is meromorphic on the whole plane.  So meromorphic continuability of a Helson zeta is
unchanged by a finite modification of its phase: the continuable stratum is invariant under
modification of finitely many coordinates of the phase torus.

This is the tail-event property of the continuation stratum.  It is what makes the stratum a
candidate for a zero–one law, and it is the reason the stratum cannot be distinguished by any
finitely many prime phases.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The ratio of two Euler factors at the same prime. -/
def eulerRatio (a b b' : ℂ) : ℂ → ℂ :=
  fun s => (1 - b * a ^ (-s)) / (1 - b' * a ^ (-s))

/-- The ratio of two Euler factors is meromorphic at every point. -/
theorem meromorphicAt_eulerRatio {a b b' : ℂ} (ha : a ≠ 0) (s : ℂ) :
    MeromorphicAt (eulerRatio a b b') s := by
  have hnum : AnalyticAt ℂ (fun z : ℂ => 1 - b * a ^ (-z)) s :=
    analyticAt_const.sub (analyticAt_const.mul (analyticAt_const_cpow_neg ha s))
  have hden : AnalyticAt ℂ (fun z : ℂ => 1 - b' * a ^ (-z)) s :=
    analyticAt_const.sub (analyticAt_const.mul (analyticAt_const_cpow_neg ha s))
  exact hnum.meromorphicAt.div hden.meromorphicAt

/-- A meromorphic function times a finite product of Euler ratios stays meromorphic. -/
theorem meromorphicOn_mul_eulerRatio {ι : Type*} {F : ℂ → ℂ}
    (hF : MeromorphicOn F Set.univ) (P : Finset ι) (a b b' : ι → ℂ)
    (ha : ∀ i ∈ P, a i ≠ 0) :
    MeromorphicOn (fun s : ℂ => F s * ∏ i ∈ P, eulerRatio (a i) (b i) (b' i) s) Set.univ := by
  intro s hs
  refine (hF s hs).mul ?_
  exact meromorphicAt_finsetProd P (fun i => eulerRatio (a i) (b i) (b' i)) s
    fun i hi => meromorphicAt_eulerRatio (ha i hi) s

/-- **The continuable stratum is invariant under finite modification of the phase.** -/
theorem continuableStratum_invariant {χ ψ : PhaseTorus}
    (hfin : {p : Nat.Primes | χ p ≠ ψ p}.Finite) (hχ : χ ∈ continuableStratum) :
    ψ ∈ continuableStratum := by
  classical
  obtain ⟨F, hF, hprod⟩ := hχ
  refine ⟨fun s => F s * ∏ p ∈ hfin.toFinset,
      eulerRatio ((p : ℕ) : ℂ) ((χ p : ℂ)) ((ψ p : ℂ)) s, ?_, ?_⟩
  · refine meromorphicOn_mul_eulerRatio hF hfin.toFinset (fun p => ((p : ℕ) : ℂ))
      (fun p => ((χ p : ℂ))) (fun p => ((ψ p : ℂ))) ?_
    intro p _
    exact_mod_cast Nat.cast_ne_zero.mpr p.2.ne_zero
  · intro s hs
    have hunitχ : ∀ p : Nat.Primes, ‖(χ p : ℂ)‖ ≤ 1 := fun p => le_of_eq (χ p).2
    have hunitψ : ∀ p : Nat.Primes, ‖(ψ p : ℂ)‖ ≤ 1 := fun p => le_of_eq (ψ p).2
    have hne : ∀ p : Nat.Primes, (1 : ℂ) - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s) ≠ 0 :=
      fun p => one_sub_phase_prime_cpow_ne_zero hunitχ hs
    have hne' : ∀ p : Nat.Primes, (1 : ℂ) - (ψ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s) ≠ 0 :=
      fun p => one_sub_phase_prime_cpow_ne_zero hunitψ hs
    have hh : HasProd (fun p : Nat.Primes => eulerRatio ((p : ℕ) : ℂ) ((χ p : ℂ))
          ((ψ p : ℂ)) s)
        (∏ p ∈ hfin.toFinset, eulerRatio ((p : ℕ) : ℂ) ((χ p : ℂ)) ((ψ p : ℂ)) s) := by
      refine hasProd_prod_of_ne_finset_one ?_
      intro p hp
      have heq : χ p = ψ p := by
        by_contra hcon
        exact hp (hfin.mem_toFinset.mpr hcon)
      rw [eulerRatio, heq]
      exact div_self (hne' p)
    have hmul := (hprod s hs).mul hh
    have hfun : (fun p : Nat.Primes =>
        ((1 : ℂ) - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹
          * eulerRatio ((p : ℕ) : ℂ) ((χ p : ℂ)) ((ψ p : ℂ)) s)
        = fun p : Nat.Primes => ((1 : ℂ) - (ψ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
      funext p
      rw [eulerRatio, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (hne p), one_mul]
    rw [hfun] at hmul
    exact hmul

end GaloisForLFunctions.HTGeometry

end

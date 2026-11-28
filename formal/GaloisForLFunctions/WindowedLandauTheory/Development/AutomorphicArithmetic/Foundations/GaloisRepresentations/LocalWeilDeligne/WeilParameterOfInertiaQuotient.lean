import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.InducedPeriodicWeilParameter

/-! A Frobenius-equivariant inertia quotient and a character with a full
Frobenius orbit give an irreducible Weil parameter with prescribed
Frobenius determinant. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TameKummer

namespace GlobalTheory.WeilDeligne

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}

theorem exists_wdRep_of_inertia_quotient {U : Type} [Group U]
    (r : Ine (F := K) A →* U) (hr : Function.Surjective r) (hop : IsOpen (r.ker : Set (Ine (F := K) A)))
    (φ : Weil h) (hφ : deg φ = 1) (f : MulAut U)
    (hF : ∀ t t' : Ine (F := K) A, ineIncl h t' = φ * ineIncl h t * φ⁻¹ → r t' = f (r t))
    (χ : U →* ℂˣ) (n : ℕ) (hn : 0 < n)
    (hperiod : ∀ j j' : ℤ, χ.comp ((f ^ j).toMonoidHom) = χ.comp ((f ^ j').toMonoidHom) ↔
      (n : ℤ) ∣ j - j')
    (c : ℂ) (hc : c ≠ 0) :
    ∃ a : WDRep h (Fin n → ℂ), a.ρ.IsIrreducible ∧ a.N = 0 ∧
      LinearMap.det (a.ρ φ) = c ∧
      (∀ t : Ine (F := K) A, (a.ρ (ineIncl h t)).charpoly =
        ∏ j ∈ Finset.range n, (X - C ((χ ((f ^ j) (r t)) : ℂˣ) : ℂ))) ∧
      ((∀ t : Ine (F := K) A, t.val ∈ wildInertia A → r t = 1) → a.Tame) := by
  let η (i : ℤ) : Ine (F := K) A →* ℂˣ := (χ.comp (f ^ i).toMonoidHom).comp r
  have hop' : IsOpen ((η 0).ker : Set (Ine (F := K) A)) := by
    apply (η 0).ker.isOpen_of_mem_nhds (g := 1)
    apply Filter.mem_of_superset (hop.mem_nhds r.ker.one_mem)
    intro t ht
    have ht' := MonoidHom.mem_ker.mp ht
    change χ ((f ^ (0 : ℤ)) (r t)) = 1
    rw [ht', map_one, map_one]
  have hF' (j : ℤ) (t t' : Ine (F := K) A) (ht : ineIncl h t' = φ * ineIncl h t * φ⁻¹) :
      η j t' = η (j + 1) t := by
    change χ ((f ^ j) (r t')) = χ ((f ^ (j + 1)) (r t))
    rw [hF t t' ht, zpow_add_one]
    rfl
  have hη (i j : ℤ) : η i = η j ↔ (n : ℤ) ∣ i - j := by
    rw [← hperiod]
    exact ⟨fun h => MonoidHom.ext fun x => by
      obtain ⟨t, rfl⟩ := hr x
      exact DFunLike.congr_fun h t, fun h => congrArg (fun g : U →* ℂˣ => g.comp r) h⟩
  obtain ⟨a, hA, hN, hdet, hchar, hT⟩ :=
    exists_wdRep_of_periodic_inertia_orbit φ hφ n hn η hop' hF' hη c hc
  refine ⟨a, hA, hN, hdet, fun t => ?_, fun hw => ?_⟩
  · simpa only [η, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, zpow_natCast] using hchar t
  · apply hT
    intro i t ht
    change χ ((f ^ i) (r t)) = 1
    rw [hw t ht, map_one, map_one]

end GlobalTheory.WeilDeligne

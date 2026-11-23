import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechDifferentialComplex

/-! A linear map on coefficients acts on Čech cochains intersection by
intersection. -/

noncomputable section

namespace GlobalTheory.CechDR

variable {k M N ι : Type} [Field k] [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N] [LinearOrder ι]

def mapCochain (g : M →ₗ[k] N) : (Finset ι → M) →ₗ[k] (Finset ι → N) :=
  LinearMap.pi fun I => g.comp (LinearMap.proj I)

@[simp]
theorem mapCochain_apply (g : M →ₗ[k] N) (c : Finset ι → M) (I : Finset ι) :
    mapCochain g c I = g (c I) := rfl

theorem mapCochain_delta (g : M →ₗ[k] N) (c : Finset ι → M) :
    mapCochain g (deltaL k ι M c) = deltaL k ι N (mapCochain g c) := by
  funext I
  simp only [mapCochain_apply, deltaL_apply, map_sum, map_zsmul]

/-- Acting on coefficients gives a map of complexes when the regular
sections on each nonempty intersection map to regular sections. -/
theorem isMap_mapCochain (A : Finset ι → Submodule k M) (B : Finset ι → Submodule k N)
    (g : M →ₗ[k] N) (h : ∀ I, I.Nonempty → A I ≤ (B I).comap g) :
    IsMap (cech A) (cech B) (mapCochain g) := by
  intro n a ha
  refine ⟨Submodule.mem_pi.mpr fun I _ => ?_, mapCochain_delta g a⟩
  have hm := (Submodule.mem_pi.mp ha) I (Set.mem_univ _)
  change g (a I) ∈ if I.Nonempty ∧ (I.card : ℤ) = n + 1 then B I else ⊥
  split_ifs at hm ⊢ with hi
  · exact h I hi.1 hm
  · simpa only [Submodule.mem_bot.mp hm, map_zero] using (zero_mem (⊥ : Submodule k N))

end GlobalTheory.CechDR

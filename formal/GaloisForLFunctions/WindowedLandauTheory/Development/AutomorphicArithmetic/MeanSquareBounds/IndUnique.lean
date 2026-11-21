import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic

/-! The primitive character is determined by values on the units of a common modulus. -/

open WindowedLandauTheory.HC

theorem QH.ind_unique (N N' M : ℕ) [NeZero N] [NeZero N'] (ψ : DirichletCharacter ℂ N)
    (ψ' : DirichletCharacter ℂ N') (hM : M ≠ 0) (hψ : ψ.IsPrimitive) (hψ' : ψ'.IsPrimitive)
    (h : ∀ n : ℕ, n.Coprime M → ψ (n : ZMod N) = ψ' (n : ZMod N')) :
    (⟨N, ψ⟩ : Σ n : ℕ, DirichletCharacter ℂ n) = ⟨N', ψ'⟩ := by
  have he := An.Induces.unique (ψ := PChar.mk N ψ hψ) (ψ' := PChar.mk N' ψ' hψ')
    (f := fun n => ψ' n) hM ⟨hψ, h⟩ ⟨hψ', fun _ _ => rfl⟩
  exact congrArg (fun p : PChar => (⟨p.N, p.χ⟩ : Σ n : ℕ, DirichletCharacter ℂ n)) he

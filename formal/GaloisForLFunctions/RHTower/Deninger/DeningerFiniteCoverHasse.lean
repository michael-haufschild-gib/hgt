import GaloisForLFunctions.RHTower.Deninger.DeningerDivisibleFiberFiniteCoverInvariance

/-!
# Hasse descent for finite quotients

A surjection whose kernel has no finite quotient is invisible to every finite group.  Consequently
every finite quotient homomorphism descends uniquely.  This is the homomorphism-level local--global
classification behind invariance of finite covers and profinite completion.
-/

namespace RHTower

universe u

/-- Every homomorphism to a finite group descends uniquely across a surjection whose kernel has no
finite quotient. -/
theorem deningerFiniteHom_existsUnique_descend
    {G H Q : Type u} [Group G] [Group H] [Group Q] [Finite Q]
    {f : G →* H} (hsurj : Function.Surjective f)
    (hker : DeningerNoFiniteQuotient (f.ker : Subgroup G))
    (φ : G →* Q) : ∃! ψ : H →* Q, ψ.comp f = φ := by
  have hkill : ∀ k ∈ f.ker, φ k = 1 := by
    intro k hk
    exact MonoidHom.mem_ker.mp (deningerKer_le_ker hker φ hk)
  refine ⟨deningerDescendHom hsurj φ hkill, ?_, ?_⟩
  · ext g
    exact deningerDescendHom_apply hsurj φ hkill g
  · intro ψ hψ
    ext h
    obtain ⟨g, rfl⟩ := hsurj h
    rw [deningerDescendHom_apply]
    exact DFunLike.congr_fun hψ g

/-- Power-divisibility of the kernel is a concrete sufficient hypothesis for unique finite
descent. -/
theorem deningerFiniteHom_existsUnique_descend_of_powerDivisible
    {G H Q : Type u} [Group G] [Group H] [Group Q] [Finite Q]
    {f : G →* H} (hsurj : Function.Surjective f)
    (hker : DeningerPowerDivisible (f.ker : Subgroup G))
    (φ : G →* Q) : ∃! ψ : H →* Q, ψ.comp f = φ :=
  deningerFiniteHom_existsUnique_descend hsurj
    (deningerNoFiniteQuotient_of_powerDivisible hker) φ

end RHTower

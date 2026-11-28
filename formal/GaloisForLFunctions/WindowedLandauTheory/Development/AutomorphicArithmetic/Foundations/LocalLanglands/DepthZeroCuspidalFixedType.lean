import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.CuspidalTorusCoinvariants
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicCartan
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PrincipalFixedReduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.CompactSmoothInvariants
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.FixedTypeSpan

/-! An inflated cuspidal type fills the first principal-congruence
fixed space of an irreducible smooth p-adic representation. The
Cartan decomposition reduces type translates to diagonal ones. -/

noncomputable section

open Matrix Representation GlobalTheory.GLq

namespace GlobalTheory.GLp

variable {p m : ℕ} [Fact p.Prime] {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

private theorem integral_apply_mem_principalCoinvariantKer
    (ρ : Representation ℂ (GL (Fin m) ℚ_[p]) V) (k : GL (Fin m) ℤ_[p])
    {v : V} (hv : v ∈ Coinvariants.ker (ρ.comp (principalCongruenceOne p (Fin m)).subtype)) :
    ρ (integralInclusion p (Fin m) k) v ∈ Coinvariants.ker
      (ρ.comp (principalCongruenceOne p (Fin m)).subtype) := by
  let K := principalCongruenceOne p (Fin m)
  let r : Representation ℂ K V := ρ.comp K.subtype
  let g := integralInclusion p (Fin m) k
  change ρ g v ∈ Coinvariants.ker r
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨u, w⟩, rfl⟩ := hy
    have hu : g * u.val * g⁻¹ ∈ K := by
      simpa only [g, map_inv, inv_inv] using integral_conj_mem_principal k⁻¹ u.2
    have h := Coinvariants.sub_mem_ker (ρ := r) (⟨g * u.val * g⁻¹, hu⟩ : K) (ρ g w)
    change ρ (g * u.val * g⁻¹) (ρ g w) - ρ g w ∈ _ at h
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply] at h
    change ρ g (ρ u.val w - w) ∈ Coinvariants.ker r
    rw [map_sub]
    exact h
  | zero => rw [map_zero]; exact (Coinvariants.ker r).zero_mem
  | add a b _ _ ha hb => rw [map_add]; exact (Coinvariants.ker r).add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact (Coinvariants.ker r).smul_mem c ha

theorem orbit_cuspidal_mem_range_sup_principalCoinvariantKer
    (ρ : Representation ℂ (GL (Fin m) ℚ_[p]) V) (ω : ℚ_[p]ˣ →* ℂˣ)
    (hω : ∀ z v, ρ (GeneralLinearGroup.scalar (Fin m) z) v = (ω z : ℂ) • v)
    (τ : Representation ℂ (Gn p m) W) (hτ : IsCusp τ.character) (j : W →ₗ[ℂ] V)
    (hj : ∀ (k : GL (Fin m) ℤ_[p]) (w : W),
      j (τ (integralReduction p (Fin m) k) w) = ρ (integralInclusion p (Fin m) k) (j w))
    (x : GL (Fin m) ℚ_[p]) (w : W) :
    ρ x (j w) ∈ LinearMap.range j ⊔ Coinvariants.ker
      (ρ.comp (principalCongruenceOne p (Fin m)).subtype) := by
  obtain ⟨a, k, l, -, hx⟩ := exists_integral_cartan x
  rw [hx, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← hj l w]
  let w' := τ (integralReduction p (Fin m) l) w
  let r := Coinvariants.ker (ρ.comp (principalCongruenceOne p (Fin m)).subtype)
  have hmid : ρ (uniformizerTorus (p := p) a) (j w') ∈ LinearMap.range j ⊔ r := by
    by_cases ha : ∃ i l, a i ≠ a l
    · exact Submodule.mem_sup_right (torus_cuspidal_mem_principal_coinvariantKer ρ τ hτ j hj a ha w')
    · push Not at ha
      let c := a ⟨0, hτ.1⟩
      have hc : a = fun _ => c := funext fun i => ha i ⟨0, hτ.1⟩
      let u : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p])
        (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
      have ht : uniformizerTorus (p := p) a = GeneralLinearGroup.scalar (Fin m) (u ^ c) := by
        apply Units.ext
        rw [hc]
        change Matrix.diagonal (fun _ : Fin m => (p : ℚ_[p]) ^ c) =
          Matrix.scalar (Fin m) ((u ^ c : ℚ_[p]ˣ) : ℚ_[p])
        rw [Units.val_zpow_eq_zpow_val]
        rfl
      rw [ht, hω]
      exact Submodule.mem_sup_left ((LinearMap.range j).smul_mem _ ⟨w', rfl⟩)
  obtain ⟨v, ⟨v', rfl⟩, z, hz, e⟩ := Submodule.mem_sup.mp hmid
  change ρ (integralInclusion p (Fin m) k) (ρ (uniformizerTorus (p := p) a) (j w')) ∈ _
  rw [← e, map_add, ← hj]
  exact add_mem (Submodule.mem_sup_left ⟨_, rfl⟩)
    (Submodule.mem_sup_right (integral_apply_mem_principalCoinvariantKer ρ k hz))

theorem principalFixed_eq_range_of_cuspidal_type
    (ρ : Representation ℂ (GL (Fin m) ℚ_[p]) V) [ρ.IsIrreducible]
    (hρ : ∀ v : V, IsOpen {g : GL (Fin m) ℚ_[p] | ρ g v = v})
    (ω : ℚ_[p]ˣ →* ℂˣ)
    (hω : ∀ z v, ρ (GeneralLinearGroup.scalar (Fin m) z) v = (ω z : ℂ) • v)
    (τ : Representation ℂ (Gn p m) W) (hτ : IsCusp τ.character) (j : W →ₗ[ℂ] V) (hj0 : j ≠ 0)
    (hj : ∀ (k : GL (Fin m) ℤ_[p]) (w : W),
      j (τ (integralReduction p (Fin m) k) w) = ρ (integralInclusion p (Fin m) k) (j w)) :
    principalFixed ρ = LinearMap.range j := by
  let K := principalCongruenceOne p (Fin m)
  let r : Representation ℂ K V := ρ.comp K.subtype
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_principalCongruenceOne p (Fin m))
  have hr (v : V) : IsOpen {g : K | r g v = v} := (hρ v).preimage continuous_subtype_val
  have hcomp := (invariants_isCompl_coinvariantKer_of_compact r hr).disjoint
  refine invariants_eq_range_of_orbit_mod_coinvariants ρ K hcomp j hj0 ?_
    (orbit_cuspidal_mem_range_sup_principalCoinvariantKer ρ ω hω τ hτ j hj)
  rintro _ ⟨w, rfl⟩
  apply (mem_principalFixed_iff ρ _).mpr
  rintro _ ⟨k, hk, rfl⟩
  rw [← hj k w, show integralReduction p (Fin m) k = 1 from hk, map_one, Module.End.one_apply]

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.principalFixed_eq_range_of_cuspidal_type

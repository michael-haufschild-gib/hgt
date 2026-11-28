import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.DepthZeroCuspidalFixedType
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.IrreducibleTypePair

/-! Two smooth irreducible p-adic representations with the same
central character and inflated cuspidal type are equivalent. The
diagonal type fills the fixed space of the subrepresentation it
generates in the product. -/

noncomputable section

open Matrix Representation GlobalTheory.GLq

namespace GlobalTheory.GLp

variable {p n : ℕ} [Fact p.Prime] {V V' W : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]

theorem nonempty_equiv_of_cuspidal_type
    (ρ : Representation ℂ (GL (Fin n) ℚ_[p]) V)
    (ρ' : Representation ℂ (GL (Fin n) ℚ_[p]) V') [ρ.IsIrreducible] [ρ'.IsIrreducible]
    (hρ : ∀ v : V, IsOpen {g : GL (Fin n) ℚ_[p] | ρ g v = v})
    (hρ' : ∀ v : V', IsOpen {g : GL (Fin n) ℚ_[p] | ρ' g v = v})
    (ω : ℚ_[p]ˣ →* ℂˣ)
    (hω : ∀ z v, ρ (GeneralLinearGroup.scalar (Fin n) z) v = (ω z : ℂ) • v)
    (hω' : ∀ z v, ρ' (GeneralLinearGroup.scalar (Fin n) z) v = (ω z : ℂ) • v)
    (τ : Representation ℂ (Gn p n) W) (hτ : IsCusp τ.character)
    (j : W →ₗ[ℂ] V) (j' : W →ₗ[ℂ] V') (hji : Function.Injective j) (hji' : Function.Injective j')
    (hj : ∀ (k : GL (Fin n) ℤ_[p]) (w : W),
      j (τ (integralReduction p (Fin n) k) w) = ρ (integralInclusion p (Fin n) k) (j w))
    (hj' : ∀ (k : GL (Fin n) ℤ_[p]) (w : W),
      j' (τ (integralReduction p (Fin n) k) w) = ρ' (integralInclusion p (Fin n) k) (j' w)) :
    Nonempty (ρ.Equiv ρ') := by
  let K := principalCongruenceOne p (Fin n)
  let π := ρ.prod ρ'
  let f := j.prod j'
  let orbit : Set (V × V') := {v | ∃ g w, π g (f w) = v}
  let S := Submodule.span ℂ orbit
  have hstable (g : GL (Fin n) ℚ_[p]) : S.map (π g) ≤ S := by
    change (Submodule.span ℂ orbit).map (π g) ≤ Submodule.span ℂ orbit
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨k, w, rfl⟩, rfl⟩
    exact ⟨g * k, w, by rw [map_mul, Module.End.mul_apply]⟩
  let U : Subrepresentation π := ⟨S, fun g {v} hv => hstable g ⟨v, hv, rfl⟩⟩
  have hcent (z : ℚ_[p]ˣ) (v : V × V') :
      π (GeneralLinearGroup.scalar (Fin n) z) v = (ω z : ℂ) • v := by
    rw [prod_apply_apply, hω, hω']
    rfl
  have hJ (k : GL (Fin n) ℤ_[p]) (w : W) :
      f (τ (integralReduction p (Fin n) k) w) = π (integralInclusion p (Fin n) k) (f w) := by
    change (j (τ (integralReduction p (Fin n) k) w), j' (τ (integralReduction p (Fin n) k) w)) =
      (ρ (integralInclusion p (Fin n) k) (j w), ρ' (integralInclusion p (Fin n) k) (j' w))
    rw [hj, hj']
  have hJfixed : LinearMap.range f ≤ principalFixed π := by
    rintro _ ⟨w, rfl⟩
    apply (mem_principalFixed_iff π _).mpr
    rintro _ ⟨k, hk, rfl⟩
    rw [← hJ, show integralReduction p (Fin n) k = 1 from hk, map_one, Module.End.one_apply]
  have hj'fix (k : GL (Fin n) ℚ_[p]) (hk : k ∈ K) (w : W) : ρ' k (j' w) = j' w :=
    congrArg Prod.snd ((mem_principalFixed_iff π _).mp (hJfixed ⟨w, rfl⟩) k hk)
  have hU (w : W) : (j w, j' w) ∈ U :=
    Submodule.subset_span ⟨1, w, by rw [map_one, Module.End.one_apply]; rfl⟩
  refine nonempty_equiv_of_fixed_diagonal_type ρ ρ' K j j' hji hji' hj'fix U hU ?_
  let r : Representation ℂ K (V × V') := π.comp K.subtype
  have hle : S ≤ LinearMap.range f ⊔ Coinvariants.ker r :=
    Submodule.span_le.mpr (by
      rintro _ ⟨g, w, rfl⟩
      exact orbit_cuspidal_mem_range_sup_principalCoinvariantKer π ω hcent τ hτ f hJ g w)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_principalCongruenceOne p (Fin n))
  have hr (v : V × V') : IsOpen {g : K | r g v = v} := by
    have hopen := (hρ v.1).inter (hρ' v.2)
    change IsOpen (Subtype.val ⁻¹' {g : GL (Fin n) ℚ_[p] | π g v = v})
    have hset : {g : GL (Fin n) ℚ_[p] | π g v = v} =
        {g | ρ g v.1 = v.1} ∩ {g | ρ' g v.2 = v.2} := by
      ext g
      exact Prod.ext_iff
    rw [hset]
    exact hopen.preimage continuous_subtype_val
  have hc := (invariants_isCompl_coinvariantKer_of_compact r hr).disjoint
  intro x hx hfix
  have hxF := (mem_principalFixed_iff π x).mpr hfix
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hle hx)
  have hbF : b ∈ principalFixed π := by simpa using (principalFixed π).sub_mem hxF (hJfixed ha)
  have hb₀ := Submodule.disjoint_def.mp hc b hbF hb
  rw [hb₀, add_zero]
  exact ha

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.nonempty_equiv_of_cuspidal_type

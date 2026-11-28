import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.BlockRadicalNormalizer
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.BlockRadicalConjugation
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicIntegralGroupTransport
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicRadicalContraction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.HarishChandraCuspidalRestriction

/-! Inflating a cuspidal residue type forces the Jacquet modules of
the generated irreducible representation to vanish. The finite
radical averages kill the type, and Iwasawa decomposition extends
this to all translates. -/

noncomputable section

open NumberField IsDedekindDomain Matrix Representation GlobalTheory.GLq
open WindowedLandauTheory.UG WindowedLandauTheory.UG.P

namespace GlobalTheory.GLp

variable {F : Type} [Field F] [NumberField F] {p n : ℕ} [Fact p.Prime]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [FiniteDimensional ℂ W]

theorem isSmoothCuspidal_of_inflated_cuspidal_type
    (v : HeightOneSpectrum (𝓞 F)) (i : ℚ_[p] ≃+* v.adicCompletion F) (hi : Continuous i)
    (ρ : Representation ℂ (GL (Fin n) (v.adicCompletion F)) V) [ρ.IsIrreducible]
    (hρ : ∀ x : V, IsOpen {g : GL (Fin n) (v.adicCompletion F) | ρ g x = x})
    (τ : Representation ℂ (Gn p n) W) (hτ : IsCusp τ.character)
    (j : W →ₗ[ℂ] V) (hj₀ : j ≠ 0)
    (hj : ∀ (k : GL (Fin n) ℤ_[p]) (x : W),
      j (τ (integralReduction p (Fin n) k) x) =
        ρ (GeneralLinearGroup.map i.toRingHom (integralInclusion p (Fin n) k)) (j x)) :
    IsSmoothCuspidal ρ := by
  have hstd (a b : ℕ) (hab : a + b = n) (ha : 0 < a) (hb : 0 < b) :
      Coinvariants.ker (ρ.comp (blockUnipotentRadical (v.adicCompletion F)
        (standardTwoBlockLabels n a)).subtype) = ⊤ := by
    subst n
    let H := blockUnipotentRadical (v.adicCompletion F) (standardTwoBlockLabels (a + b) a)
    let r : Representation ℂ H V := ρ.comp H.subtype
    let N := (twoBlockLevi (g := p) (a := a) (b := b)).ker
    letI : Fintype N := Fintype.ofFinite _
    let f := i.toRingHom.comp (algebraMap ℤ_[p] ℚ_[p])
    have hres : res a b τ.character 1 1 = 0 := by
      let D (c : ℕ) : Prop := res a c τ.character 1 1 = 0
      exact (congrArg D (show a + b - a = b by omega)).mp (hτ.2.2 a ha (by omega))
    have hs : ∑ u : N, τ u.val.val = 0 := sum_leviKernel_eq_zero_of_degree_zero τ hres
    have hjH (w : W) : j w ∈ Coinvariants.ker r := by
      have hU (u : N) : j w - j (τ u.val.val w) ∈ Coinvariants.ker r := by
        have hu (i j : Fin (a + b)) (h : ¬ (i.val < a ∧ ¬ j.val < a)) :
            (u.val.val.val - 1) i j = 0 := by
          rw [Matrix.sub_apply, radical_apply_eq_one_of_not_cross u i j (by simpa only [not_lt] using h), sub_self]
        obtain ⟨k, hk, hK⟩ := exists_integral_radical_lift_of_block_support (fun z => z.val < a) u.val.val hu
        let g := GeneralLinearGroup.map f k
        have hg : g ∈ H := (mem_standardTwoBlockRadical_iff g).mpr fun c d hcd => by
          change (f.mapMatrix k.val - 1) c d = 0
          rw [← map_one f.mapMatrix, ← map_sub]
          change f ((k.val - 1) c d) = 0
          rw [hK c d (by simpa only [not_lt] using hcd), map_zero]
        rw [← hk, hj, ← neg_sub]
        exact (Coinvariants.ker r).neg_mem (Coinvariants.sub_mem_ker (⟨g, hg⟩ : H) (j w))
      have hsum := (Coinvariants.ker r).sum_mem fun u (_ : u ∈ Finset.univ) => hU u
      have hzero : ∑ u : N, j (τ u.val.val w) = 0 := by
        rw [← map_sum, ← LinearMap.sum_apply, hs, LinearMap.zero_apply, map_zero]
      rw [Finset.sum_sub_distrib, hzero, sub_zero, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ] at hsum
      exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card N : ℂ) ≠ 0)).mp hsum
    have hgen (x : GL (Fin (a + b)) (v.adicCompletion F)) (w : W) : ρ x (j w) ∈ Coinvariants.ker r := by
      obtain ⟨t, k, ht, hk, rfl⟩ := spherical_iwasawa F v x
      obtain ⟨κ, rfl⟩ := exists_integralGL_preimage_of_completion v i hi k hk
      rw [map_mul, Module.End.mul_apply, ← hj]
      refine blockTriangular_apply_mem_blockCoinvariantKer ρ ?_ (hjH _)
      intro i j hij
      exact ht (lt_of_not_ge fun h => (not_lt_of_ge (monotone_standardTwoBlockLabels _ _ h)) hij)
    let S : Subrepresentation ρ :=
      ⟨Submodule.span ℂ {x | ∃ g w, ρ g (j w) = x}, fun g {x} hx =>
        (Submodule.span_le.mpr (fun _ hx => by
          obtain ⟨k, w, rfl⟩ := hx
          refine Submodule.subset_span ⟨g * k, w, ?_⟩
          rw [map_mul, Module.End.mul_apply]) : _ ≤ (Submodule.span ℂ _).comap (ρ g)) hx⟩
    have hS : S = ⊤ := (eq_bot_or_eq_top S).resolve_left fun h => hj₀ (LinearMap.ext fun w => by
      have hm : j w ∈ S := Submodule.subset_span ⟨1, w, by rw [map_one, Module.End.one_apply]⟩
      rw [h] at hm
      exact hm)
    have hle : S.toSubmodule ≤ Coinvariants.ker r :=
      Submodule.span_le.mpr (by rintro _ ⟨g, w, rfl⟩; exact hgen g w)
    rw [hS] at hle
    exact eq_top_iff.mpr hle
  refine ⟨hρ, fun b hb => ?_⟩
  obtain ⟨q, a, ha, han, hq⟩ := exists_standardTwoBlockRadical_conjugate_le (k := v.adicCompletion F) b hb
  have ht := hstd a (n - a) (Nat.add_sub_of_le han.le) ha (by omega)
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : ρ q⁻¹ x ∈ Coinvariants.ker
      (ρ.comp (blockUnipotentRadical (v.adicCompletion F) (standardTwoBlockLabels n a)).subtype) :=
    ht ▸ Submodule.mem_top
  have h := apply_mem_coinvariantKer_of_conjugation ρ hq hx
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  exact h

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.isSmoothCuspidal_of_inflated_cuspidal_type

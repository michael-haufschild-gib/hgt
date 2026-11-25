import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.HomogeneousLocalizationLift
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedDehomogenization
import Mathlib.RingTheory.QuotSMulTop

/-! On a coordinate chart, a homogeneous fraction is identified with its numerator
after setting the coordinate equal to one. -/

open DirectSum MvPolynomial
open scoped Pointwise

namespace GlobalTheory

theorem nonempty_singletonHomLocEquiv_quotSMulTop {ι R M : Type} [CommRing R] [AddCommGroup M]
    [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
    (D : ℤ → Submodule R M) [PolyGradedSMul ι D] [Decomposition D] (i : ι) (n : ℤ) :
    Nonempty (homLoc D {i} n ≃ₗ[R] QuotSMulTop (X i - 1 : MvPolynomial ι R) M) := by
  let u : MvPolynomial ι R := X i - 1
  let K : Submodule (MvPolynomial ι R) M := u • ⊤
  let f (k : ℕ) : D (n + k * (({i} : Finset ι).card : ℤ)) →ₗ[R] QuotSMulTop u M :=
    (K.mkQ.restrictScalars R) ∘ₗ (D _).subtype
  have hf (k : ℕ) (a : D (n + k * (({i} : Finset ι).card : ℤ)))
      (b : D (n + (k + 1 : ℕ) * (({i} : Finset ι).card : ℤ)))
      (h : (b : M) = xProd R {i} • (a : M)) : f (k + 1) b = f k a := by
    change Submodule.Quotient.mk (b : M) = Submodule.Quotient.mk (a : M)
    apply (Submodule.Quotient.eq K).2
    have he : xProd R {i} • (a : M) - (a : M) = u • (a : M) := by
      change xProd R {i} • (a : M) - (a : M) = (X i - 1 : MvPolynomial ι R) • (a : M)
      rw [xProd, Finset.prod_singleton, sub_smul, one_smul]
    rw [h, he]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  refine ⟨LinearEquiv.ofBijective (homLocLift f hf) ⟨?_, ?_⟩⟩
  · rw [homLocLift_injective_iff]
    intro k a ha
    have hm := (Submodule.Quotient.mk_eq_zero K).1 ha
    obtain ⟨w, _, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
    obtain ⟨l, hl⟩ := exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul D i a.2 hw.symm
    exact ⟨l, by simpa only [xProd, Finset.prod_singleton] using hl⟩
  · rw [homLocLift_surjective_iff]
    intro z
    obtain ⟨y, rfl⟩ := K.mkQ_surjective z
    obtain ⟨b, hb⟩ := exists_homogeneous_add_X_sub_one_smul D i y
    let k := (b - n).toNat
    have hkn : b ≤ n + k * (({i} : Finset ι).card : ℤ) := by
      simp only [Finset.card_singleton, Nat.cast_one, mul_one, k]
      omega
    obtain ⟨a, ha, w, hw⟩ := hb _ hkn
    refine ⟨k, ⟨a, ha⟩, ?_⟩
    change K.mkQ a = K.mkQ y
    have hz : K.mkQ (u • w) = 0 := (Submodule.Quotient.mk_eq_zero K).2
      (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
    conv_rhs => rw [hw, map_add, hz, add_zero]

end GlobalTheory

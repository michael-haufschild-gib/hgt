import GaloisForLFunctions.RHTower.DeningerMonicKaehlerLine
import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# The cotangent complex of a monic hypersurface is multiplication by the derivative

The polynomial algebra presents the quotient by a monic polynomial, and the cotangent complex of
that presentation is the two-term complex

`(P)/(P²) --dP--> Ω¹_{A[X]⁄A} ⊗ B`.

Both terms are free of rank one — the first on the class of `P`, the second on the class of `dX` —
and under those trivializations the differential is multiplication by the derivative of `P`, since
`d(qP) = q·dP + P·dq` and the second term dies in the quotient.

* `deningerMonicExtension` : the polynomial presentation of the monic quotient.
* `deningerMonicExtension_ker` : its kernel is the principal ideal.
* `deningerMonicCotangentComplex_mk` : **the cotangent complex is multiplication by `P'`.**
-/

namespace RHTower

open Polynomial TensorProduct KaehlerDifferential

variable {A : Type*} [CommRing A]

/-- The polynomial presentation of the quotient by a principal ideal, as an extension. -/
noncomputable def deningerMonicExtension (P : Polynomial A) :
    Algebra.Extension A (DeningerMonicQuotient P) where
  Ring := Polynomial A
  σ := Function.surjInv
    (Ideal.Quotient.mk_surjective (I := Ideal.span ({P} : Set (Polynomial A))))
  algebraMap_σ x := Function.surjInv_eq _ x

/-- **The kernel of the presentation is the principal ideal.** -/
theorem deningerMonicExtension_ker (P : Polynomial A) :
    (deningerMonicExtension P).ker = Ideal.span ({P} : Set (Polynomial A)) := by
  ext x
  show (Ideal.Quotient.mk (Ideal.span ({P} : Set (Polynomial A))) x = 0) ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

theorem deningerMonic_mul_mem_ker (P : Polynomial A) (q : Polynomial A) :
    q * P ∈ (deningerMonicExtension P).ker := by
  rw [deningerMonicExtension_ker]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/-- **The cotangent complex of a monic hypersurface is multiplication by the derivative.**
The class of `qP` in the conormal module goes to `q·dP` in the base-changed differential module,
because the Leibniz term `P·dq` dies in the quotient, and `dP` is `P'·dX`. -/
theorem deningerMonicCotangentComplex_mk (P : Polynomial A) (q : Polynomial A) :
    deningerKaehlerBaseChangeEquiv P
        ((TensorProduct.comm (Polynomial A) (DeningerMonicQuotient P) Ω[Polynomial A⁄A])
          ((deningerMonicExtension P).cotangentComplex
            (Algebra.Extension.Cotangent.mk ⟨q * P, deningerMonic_mul_mem_ker P q⟩)))
      = derivative P • (Ideal.Quotient.mk (Ideal.span ({P} : Set (Polynomial A))) q) := by
  rw [Algebra.Extension.cotangentComplex_mk]
  show deningerKaehlerBaseChangeEquiv P
      ((TensorProduct.comm (Polynomial A) (DeningerMonicQuotient P) Ω[Polynomial A⁄A])
        ((1 : DeningerMonicQuotient P) ⊗ₜ[Polynomial A]
          (KaehlerDifferential.D A (Polynomial A)) (q * P))) = _
  have hP0 : (P : Polynomial A) • (1 : DeningerMonicQuotient P) = 0 := by
    show (Ideal.Quotient.mk (Ideal.span ({P} : Set (Polynomial A))) (P * 1)) = 0
    rw [mul_one, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hleib : (KaehlerDifferential.D A (Polynomial A)) (q * P)
      = q • (KaehlerDifferential.D A (Polynomial A)) P
        + P • (KaehlerDifferential.D A (Polynomial A)) q := by
    rw [Derivation.leibniz, add_comm]
  have hzero : ((1 : DeningerMonicQuotient P) ⊗ₜ[Polynomial A]
      (P • (KaehlerDifferential.D A (Polynomial A)) q)) = 0 := by
    rw [← TensorProduct.smul_tmul, hP0, TensorProduct.zero_tmul]
  rw [hleib, TensorProduct.tmul_add, hzero, add_zero, ← TensorProduct.smul_tmul,
    TensorProduct.comm_tmul, deningerKaehlerBaseChangeEquiv_D]
  congr 1
  show Ideal.Quotient.mk (Ideal.span ({P} : Set (Polynomial A))) (q * 1) = _
  rw [mul_one]

/-- **The cotangent complex of a monic hypersurface is injective exactly when the derivative is a
non-zero-divisor**, so the first homology of the naive cotangent complex vanishes there.  This is
the unramifiedness of the monic hypersurface along its own equation. -/
theorem deningerMonicH1Cotangent_subsingleton (P : Polynomial A)
    (hreg : ∀ b : DeningerMonicQuotient P, derivative P • b = 0 → b = 0) :
    Subsingleton (deningerMonicExtension P).H1Cotangent := by
  rw [Algebra.Extension.subsingleton_h1Cotangent]
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  have hy' : y ∈ Ideal.span ({P} : Set (Polynomial A)) := by
    rwa [deningerMonicExtension_ker] at hy
  obtain ⟨q, hq⟩ : ∃ q : Polynomial A, q * P = y := Ideal.mem_span_singleton'.1 hy'
  have hximg : (deningerMonicExtension P).cotangentComplex
      (Algebra.Extension.Cotangent.mk ⟨q * P, deningerMonic_mul_mem_ker P q⟩) = 0 := by
    rw [show (⟨q * P, deningerMonic_mul_mem_ker P q⟩ : (deningerMonicExtension P).ker)
        = ⟨y, hy⟩ from Subtype.ext hq]
    exact hx
  have hzero : derivative P • (Ideal.Quotient.mk (Ideal.span ({P} : Set (Polynomial A))) q)
      = 0 := by
    rw [← deningerMonicCotangentComplex_mk P q, hximg]
    simp
    rfl
  have hq0 : (Ideal.Quotient.mk (Ideal.span ({P} : Set (Polynomial A))) q) = 0 :=
    hreg _ hzero
  obtain ⟨c, hc⟩ : ∃ c : Polynomial A, c * P = q :=
    Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hq0)
  rw [Algebra.Extension.Cotangent.mk_eq_zero_iff]
  have hmem : (q * P : Polynomial A) ∈ Ideal.span ({P} : Set (Polynomial A)) ^ (2 : ℕ) := by
    rw [Ideal.span_singleton_pow]
    refine Ideal.mem_span_singleton'.2 ⟨c, ?_⟩
    rw [← hc]
    ring
  show y ∈ (deningerMonicExtension P).ker ^ (2 : ℕ)
  rw [deningerMonicExtension_ker, ← hq]
  exact hmem

end RHTower

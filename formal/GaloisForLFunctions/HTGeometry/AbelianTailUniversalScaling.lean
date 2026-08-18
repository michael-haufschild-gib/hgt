import GaloisForLFunctions.HTGeometry.DifferentialIndependentFieldUniversality

/-!
# The universal abstract multiplication tail and its scaling dynamics

Let `F` be a differential field and let `v : ι → K` be a family which is differentially
independent over `F` inside a differential field extension `K`.  The differential field
`F⟨v⟩ = differentialAdjoin F (Set.range v)` is then the free differential rational field on `ι`,
and for every integer `m` invertible in `F` it carries a canonical differential `F`-automorphism

`sigma_m (v i) = m • v i`.

This file constructs that automorphism, proves that it commutes with the derivation, and proves
the **no-hair theorem**: for two differentially independent palettes with the same index type, the
canonical labelled equivalence intertwines their scaling automorphisms.  Hence the abstract
differential field with its multiplication dynamics depends only on the index type and on `m` —
no further data of the source of the palette survives.

This is the abstract half of the Manin-horizon theorem: once the multiplication tail of an
Abelian variety is identified with the invariants of the Manin kernel, that quotient is a free
differential group of rank `dim A` on which multiplication acts by the scalar `m`, so the
dynamical field is universal.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ### Integer scaling of jets -/

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]

/-- Every jet of an integer multiple is the same multiple of the jet. -/
theorem differentialJet_zsmul (m : ℤ) (n : ℕ) (x : K) :
    differentialJet n (m • x) = m • differentialJet n x := by
  induction n with
  | zero => simp only [differentialJet_zero]
  | succ n ih =>
      rw [differentialJet_succ, ih, differentialJet_succ]
      exact map_zsmul (Differential.deriv : Derivation ℤ K K) m _

/-- Rescaling a family by one nonzero base scalar preserves algebraic independence. -/
theorem algebraicIndependent_const_smul {ι : Type*} {c : F} (hc : c ≠ 0)
    {y : ι → K} (hy : AlgebraicIndependent F y) :
    AlgebraicIndependent F (fun i => c • y i) := by
  classical
  set sigma : MvPolynomial ι F →ₐ[F] MvPolynomial ι F :=
    MvPolynomial.aeval (fun i => c • (MvPolynomial.X i : MvPolynomial ι F)) with hsigma
  set tau : MvPolynomial ι F →ₐ[F] MvPolynomial ι F :=
    MvPolynomial.aeval (fun i => c⁻¹ • (MvPolynomial.X i : MvPolynomial ι F)) with htau
  have hround : tau.comp sigma = AlgHom.id F (MvPolynomial ι F) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, hsigma, htau, MvPolynomial.aeval_X, AlgHom.id_apply,
      map_smul, smul_smul]
    rw [inv_mul_cancel₀ hc, one_smul]
  have hsigmaInj : Function.Injective sigma := by
    intro p q hpq
    have := congrArg tau hpq
    simpa only [← AlgHom.comp_apply, hround, AlgHom.id_apply] using this
  have hcomp : (MvPolynomial.aeval (fun i => c • y i) : MvPolynomial ι F →ₐ[F] K)
      = (MvPolynomial.aeval y).comp sigma := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [hsigma]
  show Function.Injective (MvPolynomial.aeval (fun i => c • y i) : MvPolynomial ι F →ₐ[F] K)
  rw [hcomp]
  exact hy.comp hsigmaInj

/-- Rescaling a palette by a nonzero integer preserves differential independence. -/
theorem DifferentialIndependent.zsmul {ι : Type*} {x : ι → K}
    (hx : DifferentialIndependent F x) (m : ℤ) (hm : (m : F) ≠ 0) :
    DifferentialIndependent F (fun i => m • x i) := by
  have hrw : (fun p : ι × ℕ => differentialJet p.2 ((fun i => m • x i) p.1))
      = fun p : ι × ℕ => (m : F) • differentialJet p.2 (x p.1) := by
    funext p
    rw [differentialJet_zsmul]
    exact (Int.cast_smul_eq_zsmul F m (differentialJet p.2 (x p.1))).symm
  show AlgebraicIndependent F _
  rw [hrw]
  exact algebraicIndependent_const_smul hm hx

variable [Differential F] [DifferentialAlgebra F K]

/-- Rescaling a palette by a nonzero integer does not change the differential field it
generates. -/
theorem differentialAdjoin_range_zsmul {ι : Type*} (x : ι → K) (m : ℤ) (hm : (m : F) ≠ 0) :
    differentialAdjoin F (Set.range fun i => m • x i) = differentialAdjoin F (Set.range x) := by
  have hmK : (algebraMap F K) (m : F) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (algebraMap F K).injective).mpr hm
  apply le_antisymm
  · refine differentialAdjoin_le F ?_ (derivationClosed_differentialAdjoin F _)
    rintro y ⟨i, rfl⟩
    exact zsmul_mem (subset_differentialAdjoin F (Set.range x) (Set.mem_range_self i)) m
  · refine differentialAdjoin_le F ?_ (derivationClosed_differentialAdjoin F _)
    rintro y ⟨i, rfl⟩
    have hmem : m • x i ∈ differentialAdjoin F (Set.range fun i => m • x i) :=
      subset_differentialAdjoin F _ (Set.mem_range_self i)
    have hinv : (algebraMap F K) ((m : F)⁻¹) ∈
        differentialAdjoin F (Set.range fun i => m • x i) :=
      IntermediateField.algebraMap_mem _ _
    have hprod := IntermediateField.mul_mem _ hinv hmem
    have hval : (algebraMap F K) ((m : F)⁻¹) * (m • x i) = x i := by
      rw [← Int.cast_smul_eq_zsmul F m (x i), smul_smul, inv_mul_cancel₀ hm, one_smul]
    rwa [hval] at hprod

/-! ### The scaling automorphism of a free differential palette field -/

/-- **The multiplication-tail scaling automorphism.**  On the free differential field generated by
a differentially independent palette, the assignment `v i ↦ m • v i` extends to a differential
`F`-automorphism. -/
def multiplicationTailScaling {ι : Type*} (x : ι → K)
    (hx : DifferentialIndependent F x) (m : ℤ) (hm : (m : F) ≠ 0) :
    differentialAdjoin F (Set.range x) ≃ₐ[F] differentialAdjoin F (Set.range x) :=
  (differentialIndependentAdjoinAlgEquiv x (fun i => m • x i) hx (hx.zsmul m hm)).trans
    (IntermediateField.equivOfEq (differentialAdjoin_range_zsmul x m hm))

/-- The scaling automorphism multiplies every jet of the palette by `m`. -/
@[simp]
theorem multiplicationTailScaling_jet {ι : Type*} (x : ι → K)
    (hx : DifferentialIndependent F x) (m : ℤ) (hm : (m : F) ≠ 0) (i : ι) (n : ℕ) :
    ((multiplicationTailScaling x hx m hm
        ⟨differentialJet n (x i),
          differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ :
      differentialAdjoin F (Set.range x)) : K) = m • differentialJet n (x i) := by
  have hstep := differentialIndependentAdjoinAlgEquiv_jet x (fun i => m • x i) hx
    (hx.zsmul m hm) i n
  have hval := congrArg Subtype.val hstep
  simp only [multiplicationTailScaling, AlgEquiv.trans_apply]
  rw [show ((IntermediateField.equivOfEq (differentialAdjoin_range_zsmul x m hm))
      (differentialIndependentAdjoinAlgEquiv x (fun i => m • x i) hx (hx.zsmul m hm)
        ⟨differentialJet n (x i),
          differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩) : K)
    = ((differentialIndependentAdjoinAlgEquiv x (fun i => m • x i) hx (hx.zsmul m hm)
        ⟨differentialJet n (x i),
          differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ :
      differentialAdjoin F (Set.range fun i => m • x i)) : K) from rfl]
  rw [hval]
  exact differentialJet_zsmul m n (x i)

/-- **Equation (8) of the Manin-horizon theorem.**  The scaling automorphism acts on the palette
itself by multiplication by `m`. -/
theorem multiplicationTailScaling_source {ι : Type*} (x : ι → K)
    (hx : DifferentialIndependent F x) (m : ℤ) (hm : (m : F) ≠ 0) (i : ι) :
    ((multiplicationTailScaling x hx m hm
        ⟨x i, subset_differentialAdjoin F (Set.range x) (Set.mem_range_self i)⟩ :
      differentialAdjoin F (Set.range x)) : K) = m • x i := by
  have h := multiplicationTailScaling_jet x hx m hm i 0
  simpa only [differentialJet_zero] using h

/-- The scaling automorphism commutes with the derivation. -/
theorem multiplicationTailScaling_deriv {ι : Type*} (x : ι → K)
    (hx : DifferentialIndependent F x) (m : ℤ) (hm : (m : F) ≠ 0)
    (z : differentialAdjoin F (Set.range x)) :
    multiplicationTailScaling x hx m hm z′ = (multiplicationTailScaling x hx m hm z)′ := by
  apply Subtype.ext
  have hbase := differentialIndependentAdjoinAlgEquiv_deriv x (fun i => m • x i) hx
    (hx.zsmul m hm) z
  have hval := congrArg Subtype.val hbase
  simpa only [multiplicationTailScaling, AlgEquiv.trans_apply] using hval

/-! ### The no-hair theorem -/

/-- **Corollary C: the abstract multiplication tail is universal.**  For two differentially
independent palettes with the same index type, the canonical labelled differential equivalence
intertwines their scaling automorphisms.  Consequently the abstract differential field together
with its multiplication dynamics depends only on the index type and on `m`. -/
theorem multiplicationTailScaling_naturality {ι : Type*} {L : Type*} [Field L] [Algebra F L]
    [Differential L] [DifferentialAlgebra F L]
    (x : ι → K) (y : ι → L)
    (hx : DifferentialIndependent F x) (hy : DifferentialIndependent F y)
    (m : ℤ) (hm : (m : F) ≠ 0)
    (z : differentialAdjoin F (Set.range x)) :
    differentialIndependentAdjoinAlgEquiv x y hx hy (multiplicationTailScaling x hx m hm z) =
      multiplicationTailScaling y hy m hm
        (differentialIndependentAdjoinAlgEquiv x y hx hy z) := by
  classical
  set e := differentialIndependentAdjoinAlgEquiv x y hx hy with he
  set sx := multiplicationTailScaling x hx m hm with hsx
  set sy := multiplicationTailScaling y hy m hm with hsy
  have hhom : (e.toAlgHom.comp sx.toAlgHom) = (sy.toAlgHom.comp e.toAlgHom) := by
    unfold differentialAdjoin
    apply IntermediateField.adjoin_algHom_ext
    rintro u ⟨w, ⟨i, rfl⟩, n, rfl⟩
    apply Subtype.ext
    have hsxval : ((sx ⟨differentialJet n (x i),
        differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ : _) : K)
        = m • differentialJet n (x i) := multiplicationTailScaling_jet x hx m hm i n
    have hsxeq : sx ⟨differentialJet n (x i),
        differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩
        = m • (⟨differentialJet n (x i),
            differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ :
          differentialAdjoin F (Set.range x)) := by
      apply Subtype.ext
      rw [hsxval]
      rfl
    have heval := differentialIndependentAdjoinAlgEquiv_jet x y hx hy i n
    have hsyval : ((sy ⟨differentialJet n (y i),
        differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ : _) : L)
        = m • differentialJet n (y i) := multiplicationTailScaling_jet y hy m hm i n
    calc ((e.toAlgHom.comp sx.toAlgHom) ⟨differentialJet n (x i), _⟩ : _)
        = e (sx ⟨differentialJet n (x i), _⟩) := rfl
      _ = e (m • (⟨differentialJet n (x i), _⟩ : differentialAdjoin F (Set.range x))) := by
            rw [hsxeq]
      _ = m • e ⟨differentialJet n (x i), _⟩ := by rw [map_zsmul]
      _ = m • (⟨differentialJet n (y i),
            differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ :
          differentialAdjoin F (Set.range y)) := by rw [heval]
      _ = sy ⟨differentialJet n (y i), _⟩ := by
            apply Subtype.ext
            rw [hsyval]
            rfl
      _ = sy (e ⟨differentialJet n (x i), _⟩) := by rw [heval]
      _ = ((sy.toAlgHom.comp e.toAlgHom) ⟨differentialJet n (x i), _⟩ : _) := rfl
  exact AlgHom.congr_fun hhom z

end

end GaloisForLFunctions.HTGeometry

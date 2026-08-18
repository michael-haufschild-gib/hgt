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
differential field together with its multiplication dynamics depends only on the index type and
on `m`; no further data of the palette's source survives.

This is the abstract half of the Manin-horizon theorem: once the multiplication tail of an
Abelian variety is identified with the invariants of the Manin kernel, that quotient is a free
differential group of rank `dim A` on which multiplication acts by the scalar `m`, so the
dynamical field is universal.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ### Transport lemmas -/

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The equivalence induced by an equality of intermediate fields does not move elements. -/
theorem coe_intermediateFieldEquivOfEq
    {S T : IntermediateField F K} (h : S = T) (z : S) :
    ((IntermediateField.equivOfEq h z : T) : K) = (z : K) := rfl

variable [Differential K]

/-- The derivation of a differential adjunction is the ambient derivation. -/
theorem coe_deriv_differentialAdjoin [Differential F] [DifferentialAlgebra F K] (s : Set K)
    (z : differentialAdjoin F s) : ((z′ : differentialAdjoin F s) : K) = (z : K)′ := rfl

/-! ### Integer scaling of jets -/

/-- Every jet of an integer multiple is the same multiple of the jet. -/
theorem differentialJet_zsmul (m : ℤ) (n : ℕ) (x : K) :
    differentialJet n (m • x) = m • differentialJet n x := by
  induction n with
  | zero => simp only [differentialJet_zero]
  | succ n ih =>
      rw [differentialJet_succ, ih, differentialJet_succ]
      exact map_zsmul (Differential.deriv : Derivation ℤ K K) m _

omit [Differential K] in
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
    rw [mul_inv_cancel₀ hc, one_smul]
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
  rw [hcomp, AlgHom.coe_comp]
  exact Function.Injective.comp hy hsigmaInj

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
      rw [← Algebra.smul_def, ← Int.cast_smul_eq_zsmul F m (x i), smul_smul,
        inv_mul_cancel₀ hm, one_smul]
    rwa [hval] at hprod

/-! ### The scaling automorphism of a free differential palette field -/

/-- **The multiplication-tail scaling automorphism.**  On the free differential field generated by
a differentially independent palette, the assignment `v i ↦ m • v i` extends to an
`F`-automorphism. -/
def multiplicationTailScaling {ι : Type*} (x : ι → K)
    (hx : DifferentialIndependent F x) (m : ℤ) (hm : (m : F) ≠ 0) :
    differentialAdjoin F (Set.range x) ≃ₐ[F] differentialAdjoin F (Set.range x) :=
  (differentialIndependentAdjoinAlgEquiv x (fun i => m • x i) hx
      (DifferentialIndependent.zsmul hx m hm)).trans
    (IntermediateField.equivOfEq (differentialAdjoin_range_zsmul x m hm))

/-- The scaling automorphism multiplies every jet of the palette by `m`. -/
theorem multiplicationTailScaling_jet {ι : Type*} (x : ι → K)
    (hx : DifferentialIndependent F x) (m : ℤ) (hm : (m : F) ≠ 0) (i : ι) (n : ℕ) :
    ((multiplicationTailScaling x hx m hm
        ⟨differentialJet n (x i),
          differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ :
      differentialAdjoin F (Set.range x)) : K) = m • differentialJet n (x i) := by
  have hval := congrArg Subtype.val
    (differentialIndependentAdjoinAlgEquiv_jet x (fun i => m • x i) hx
      (DifferentialIndependent.zsmul hx m hm) i n)
  simp only [multiplicationTailScaling, AlgEquiv.trans_apply]
  rw [coe_intermediateFieldEquivOfEq, hval]
  exact differentialJet_zsmul m n (x i)

/-- The scaling automorphism multiplies every jet of the palette by `m`, as an equation in the
generated differential field. -/
theorem multiplicationTailScaling_jet_eq {ι : Type*} (x : ι → K)
    (hx : DifferentialIndependent F x) (m : ℤ) (hm : (m : F) ≠ 0) (i : ι) (n : ℕ) :
    multiplicationTailScaling x hx m hm
        ⟨differentialJet n (x i),
          differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ =
      m • (⟨differentialJet n (x i),
          differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ :
        differentialAdjoin F (Set.range x)) := by
  apply Subtype.ext
  rw [multiplicationTailScaling_jet]
  rfl

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
  have hval := congrArg Subtype.val
    (differentialIndependentAdjoinAlgEquiv_deriv x (fun i => m • x i) hx
      (DifferentialIndependent.zsmul hx m hm) z)
  simp only [multiplicationTailScaling, AlgEquiv.trans_apply]
  rw [coe_deriv_differentialAdjoin, coe_intermediateFieldEquivOfEq,
    coe_intermediateFieldEquivOfEq]
  exact hval

/-! ### The no-hair theorem -/

/-- **Corollary C: the abstract multiplication tail is universal.**  For two differentially
independent palettes with the same index type, the canonical labelled equivalence intertwines
their scaling automorphisms.  Consequently the abstract differential field together with its
multiplication dynamics depends only on the index type and on `m`. -/
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
    have hxjet := multiplicationTailScaling_jet_eq x hx m hm i n
    have hyjet := multiplicationTailScaling_jet_eq y hy m hm i n
    have heval := differentialIndependentAdjoinAlgEquiv_jet x y hx hy i n
    rw [← hsx] at hxjet
    rw [← hsy] at hyjet
    rw [← he] at heval
    calc (e.toAlgHom.comp sx.toAlgHom)
            ⟨differentialJet n (x i),
              differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩
        = e (sx ⟨differentialJet n (x i),
              differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩) := rfl
      _ = e (m • (⟨differentialJet n (x i),
              differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ :
            differentialAdjoin F (Set.range x))) := by rw [hxjet]
      _ = m • e ⟨differentialJet n (x i),
              differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ := by
            rw [map_zsmul]
      _ = m • (⟨differentialJet n (y i),
              differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ :
            differentialAdjoin F (Set.range y)) := by rw [heval]
      _ = sy ⟨differentialJet n (y i),
              differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ := by
            rw [hyjet]
      _ = sy (e ⟨differentialJet n (x i),
              differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩) := by
            rw [heval]
      _ = (sy.toAlgHom.comp e.toAlgHom)
            ⟨differentialJet n (x i),
              differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ := rfl
  exact AlgHom.congr_fun hhom z

/-- **Corollary C, packaged form: the full Abelian no-hair theorem.**  Two differentially
independent palettes of the same rank generate differential fields which are isomorphic over the
base by a single map that preserves the derivation, matches the palettes, and intertwines the two
multiplication-by-`m` dynamics.  Nothing beyond the rank and the integer `m` is visible in the
abstract tail. -/
theorem multiplicationTail_noHair {ι : Type*} {L : Type*} [Field L] [Algebra F L]
    [Differential L] [DifferentialAlgebra F L]
    (x : ι → K) (y : ι → L)
    (hx : DifferentialIndependent F x) (hy : DifferentialIndependent F y)
    (m : ℤ) (hm : (m : F) ≠ 0) :
    ∃ Φ : differentialAdjoin F (Set.range x) ≃ₐ[F] differentialAdjoin F (Set.range y),
      (∀ z, Φ z′ = (Φ z)′) ∧
      (∀ i, Φ ⟨x i, subset_differentialAdjoin F (Set.range x) (Set.mem_range_self i)⟩ =
        ⟨y i, subset_differentialAdjoin F (Set.range y) (Set.mem_range_self i)⟩) ∧
      (∀ z, Φ (multiplicationTailScaling x hx m hm z) =
        multiplicationTailScaling y hy m hm (Φ z)) := by
  refine ⟨differentialIndependentAdjoinAlgEquiv x y hx hy, ?_, ?_, ?_⟩
  · exact differentialIndependentAdjoinAlgEquiv_deriv x y hx hy
  · intro i
    have h := differentialIndependentAdjoinAlgEquiv_jet x y hx hy i 0
    simpa only [differentialJet_zero] using h
  · exact multiplicationTailScaling_naturality x y hx hy m hm

end

end GaloisForLFunctions.HTGeometry

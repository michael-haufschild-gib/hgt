import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GenericChartForms
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveFiniteCover
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler

/-! Logarithmic volume forms in a finite separable extension of the
projective coordinate field. -/

noncomputable section

open GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F]
  [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- The differentials of the origin coordinates form a basis in the
separable extension. -/
theorem IsFinCover.exists_coordinateDifferentialBasis (h : IsFinCover k E x) :
    ∃ b : Module.Basis (Fin d) E Ω[E⁄k], ∀ j,
      b j = D k E (algebraMap F E (x j.succ / x 0)) := by
  letI := h.fin
  letI := h.sep
  let t (j : Fin d) := x j.succ / x 0
  let A := MvPolynomial (Fin d) k
  let p : A →ₐ[k] F := MvPolynomial.aeval t
  letI : Algebra A F := p.toRingHom.toAlgebra
  letI : IsScalarTower k A F := .of_algebraMap_eq fun r => (p.commutes r).symm
  letI : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective A F).mpr h.pd.indep
  letI : IsFractionRing A F := IsFractionRing.of_field A F fun z => by
    have hz : z ∈ IntermediateField.adjoin k (Set.range t) := h.pd.gen.symm ▸ IntermediateField.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := (IntermediateField.mem_adjoin_iff_div (F := k) (S := Set.range t)).mp hz
    rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range] at ha hb
    obtain ⟨q, rfl⟩ := ha
    obtain ⟨r, rfl⟩ := hb
    exact ⟨q, r, rfl⟩
  letI : Algebra.FormallyEtale A F := .of_isLocalization (nonZeroDivisors A)
  letI : Algebra.FormallyEtale F E := .of_isSeparable F E
  letI : Algebra A E := ((algebraMap F E).comp (algebraMap A F)).toAlgebra
  letI : IsScalarTower A F E := .of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower k A E := .of_algebraMap_eq fun r => by
    change _ = algebraMap F E (algebraMap A F (algebraMap k A r))
    rw [← IsScalarTower.algebraMap_apply k A F, ← IsScalarTower.algebraMap_apply k F E]
  letI : Algebra.FormallyEtale A E := Algebra.FormallyEtale.comp A F E
  let b := KaehlerDifferential.mvPolynomialBasis k (Fin d)
  let g := tensorKaehlerEquivOfFormallyEtale k A E
  refine ⟨(b.baseChange E).map g, fun j => ?_⟩
  have hb : b j = D k A (MvPolynomial.X j) := b.repr.injective (by
    rw [Module.Basis.repr_self]
    exact (KaehlerDifferential.mvPolynomialBasis_repr_D_X k (Fin d) j).symm)
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb]
  apply g.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  have hX : algebraMap A E (MvPolynomial.X j) = algebraMap F E (t j) :=
    congrArg (algebraMap F E) (MvPolynomial.aeval_X t j)
  rw [← hX, tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

variable (k E) in
/-- The wedge of the logarithmic differentials of the origin coordinates. -/
def vol0 (x : Fin (d + 1) → F) : DR k E :=
  ExteriorAlgebra.ιMulti E d fun j =>
    (algebraMap F E (x j.succ / x 0))⁻¹ • D k E (algebraMap F E (x j.succ / x 0))

/-- Extract the top coefficient relative to the logarithmic volume form,
and vanish in all other degrees. -/
def IsTop (τ : DR k E →ₗ[E] E) : Prop :=
  τ (vol0 k E x) = 1 ∧ ∀ q, q ≠ d → ∀ y ∈ ⋀[E]^q Ω[E⁄k], τ y = 0

/-- The normalized coefficient determines every top-degree form.
Exterior powers above the dimension vanish. -/
theorem IsFinCover.topDegreeForms (h : IsFinCover k E x) :
    (∃ τ : DR k E →ₗ[E] E, IsTop (x := x) τ) ∧
      (∀ τ : DR k E →ₗ[E] E, IsTop (x := x) τ → ∀ y ∈ ⋀[E]^d Ω[E⁄k], y = τ y • vol0 k E x) ∧
      ∀ q, d < q → ∀ y ∈ ⋀[E]^q Ω[E⁄k], y = 0 := by
  obtain ⟨b, hb⟩ := h.exists_coordinateDifferentialBasis
  let u (j : Fin d) := (algebraMap F E (x j.succ / x 0))⁻¹
  have hu (j : Fin d) : u j ≠ 0 :=
    inv_ne_zero ((map_ne_zero _).mpr (div_ne_zero (h.pd.ne _) (h.pd.ne _)))
  let a := b.unitsSMul (fun j => Units.mk0 (u j) (hu j))
  have ha (j : Fin d) : a j = u j • D k E (algebraMap F E (x j.succ / x 0)) := by
    rw [Module.Basis.unitsSMul_apply, hb]
    rfl
  have hvol : vol0 k E x = ExteriorAlgebra.ιMulti E d a :=
    congrArg (ExteriorAlgebra.ιMulti E d) (funext fun j => (ha j).symm)
  let φ : ⋀[E]^d Ω[E⁄k] →ₗ[E] E := exteriorPower.alternatingMapLinearEquiv a.det
  let A (i : ℕ) := ⋀[E]^i Ω[E⁄k]
  let τ : DR k E →ₗ[E] E :=
    φ ∘ₗ DirectSum.component E ℕ (fun q => ↥(A q)) d ∘ₗ
      (DirectSum.decomposeLinearEquiv A).toLinearMap
  have ht (v : DR k E) : τ v = φ (DirectSum.decompose A v d) := rfl
  refine ⟨⟨τ, ?_, ?_⟩, ?_, ?_⟩
  · rw [ht, hvol, ← exteriorPower.ιMulti_apply_coe, DirectSum.decompose_coe,
      DirectSum.of_eq_same, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Module.Basis.det_self]
  · intro q hq v hv
    have hz : DirectSum.decompose A v d = 0 :=
      Subtype.ext (DirectSum.decompose_of_mem_ne _ hv hq)
    rw [ht, hz, map_zero]
  · intro ψ hψ v hv
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hv
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      have e : ExteriorAlgebra.ιMulti E d w = a.det w • vol0 k E x := by
        rw [hvol, ← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff E]
        intro f
        have hh := congrArg (fun g => g w)
          (AlternatingMap.eq_smul_basis_det a (f.compAlternatingMap (ExteriorAlgebra.ιMulti E d)))
        simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at hh
        rw [map_sub, map_smul, hh, smul_eq_mul, mul_comm, sub_self]
      rw [e, map_smul, hψ.1, smul_eq_mul, mul_one]
    | zero => rw [map_zero, zero_smul]
    | add v w _ _ hv hw => rw [map_add, add_smul, ← hv, ← hw]
    | smul r v _ hv => rw [map_smul, smul_eq_mul, mul_smul, ← hv]
  · intro q hq v hv
    letI : Module.Finite E Ω[E⁄k] := Module.Finite.of_basis b
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hv
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      apply AlternatingMap.map_linearDependent
      intro hli
      have hcard := hli.fintype_card_le_finrank
      rw [Module.finrank_eq_card_basis b, Fintype.card_fin, Fintype.card_fin] at hcard
      exact (Nat.not_le_of_lt hq) hcard
    | zero => rfl
    | add v w _ _ hv hw => rw [hv, hw, add_zero]
    | smul r v _ hv => rw [hv, smul_zero]

end GlobalTheory.PD

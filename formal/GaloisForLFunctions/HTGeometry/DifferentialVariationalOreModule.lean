import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreTorsion
import GaloisForLFunctions.HTGeometry.KaehlerSemilinearAction
import GaloisForLFunctions.HTGeometry.DifferentialVariationalSemilinearMatrixAction
import GaloisForLFunctions.HTGeometry.OperatorBalanceLaw

/-!
# Canonical variational Ore module and its differential-automorphism action

This leaf forms the literal quotient `M_K = Ω[K⁄C] / Tor_R(Ω[K⁄C])`, proves its freeness under
finite differential generation, and descends every differential base automorphism to an invertible
semilinear action on that quotient.  Full semilinearity is over the induced automorphism of the
noncommutative operator ring `K[∂;δ]`, not merely over the coefficient field.

In any finite operator basis, the action and its inverse yield an invertible operator matrix.  Its
canonical image in the completed pseudodifferential skew field is therefore a genuine matrix unit
acting on the projective lattice carrier.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

omit [Differential K] [IsConstantBase C K] in
/-- The identity coefficient automorphism acts identically on Kähler differentials. -/
theorem kaehlerSemilinear_refl
    (ω : Ω[K⁄C]) :
    kaehlerSemilinear (σ := RingEquiv.refl K) (fun _ => rfl) ω = ω := by
  have hmem : ω ∈ (⊤ : Submodule K (Ω[K⁄C])) := Submodule.mem_top
  rw [← KaehlerDifferential.span_range_derivation C K] at hmem
  induction hmem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [kaehlerSemilinear_D]
      rfl
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => rw [kaehlerSemilinear_smul, hx]; rfl

omit [Differential K] [IsConstantBase C K] in
/-- Kähler semilinear actions compose in coefficient-automorphism order. -/
theorem kaehlerSemilinear_trans
    (σ τ : K ≃+* K)
    (hσfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hτfix : ∀ c : C, τ (algebraMap C K c) = algebraMap C K c)
    (ω : Ω[K⁄C]) :
    kaehlerSemilinear hτfix (kaehlerSemilinear hσfix ω) =
      kaehlerSemilinear (σ := σ.trans τ)
        (fun c => by rw [RingEquiv.trans_apply, hσfix c, hτfix c]) ω := by
  have hmem : ω ∈ (⊤ : Submodule K (Ω[K⁄C])) := Submodule.mem_top
  rw [← KaehlerDifferential.span_range_derivation C K] at hmem
  induction hmem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [kaehlerSemilinear_D, kaehlerSemilinear_D, kaehlerSemilinear_D]
      rfl
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      rw [kaehlerSemilinear_smul, kaehlerSemilinear_smul, hx,
        kaehlerSemilinear_smul]
      rfl

/-- Kähler semilinearity commutes with every iterate of the canonical connection. -/
theorem kaehlerSemilinear_connection_iterate {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    (n : ℕ) (ω : Ω[K⁄C]) :
    kaehlerSemilinear hfix
        ((kaehlerConnection (IsConstantBase.deriv_algebraMap (C := C) (K := K)) :
          Ω[K⁄C] → Ω[K⁄C])^[n] ω) =
      (kaehlerConnection (IsConstantBase.deriv_algebraMap (C := C) (K := K)) :
        Ω[K⁄C] → Ω[K⁄C])^[n] (kaehlerSemilinear hfix ω) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        kaehlerSemilinear_kaehlerConnection hfix
          (IsConstantBase.deriv_algebraMap (C := C) (K := K)) hδ, ih]

/-- Kähler semilinearity upgrades from coefficient scalars to the full differential-operator
ring. -/
theorem kaehlerSemilinear_diffOp_smul {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    (p : DiffOp K) (ω : Ω[K⁄C]) :
    kaehlerSemilinear hfix (p • ω) =
      DiffOp.mapRingEquiv σ hδ p • kaehlerSemilinear hfix ω := by
  rw [diffOp_smul_def, diffOp_smul_def]
  refine DiffOp.induction_linear
    (motive := fun p =>
      kaehlerSemilinear hfix (diffOpSMul IsConstantBase.deriv_algebraMap p ω) =
        diffOpSMul IsConstantBase.deriv_algebraMap (DiffOp.mapRingEquiv σ hδ p)
          (kaehlerSemilinear hfix ω)) p ?_ ?_ ?_
  · simp [DiffOp.mapRingEquiv_apply, DiffOp.map_zero']
  · intro p q hp hq
    rw [diffOpSMul_add_op, map_add, hp, hq, map_add, diffOpSMul_add_op]
  · intro n a
    rw [diffOpSMul_mono, kaehlerSemilinear_smul, DiffOp.mapRingEquiv_apply,
      DiffOp.map_mono, diffOpSMul_mono, kaehlerSemilinear_connection_iterate hfix hδ]
    rw [← one_smul (DiffOp K)
      ((kaehlerConnection IsConstantBase.deriv_algebraMap : Ω[K⁄C] → Ω[K⁄C])^[n]
        (kaehlerSemilinear hfix ω)), ← smul_assoc]
    simp

/-- The canonical differential-operator module modulo all Ore torsion. -/
abbrev VariationalOreModule (C K : Type*) [Field C] [Field K] [Algebra C K]
    [Differential K] [IsConstantBase C K] :=
  Ω[K⁄C] ⧸ DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])

/-- Differential automorphisms of `K` fixing `C`, bundled as the intrinsic automorphism group used
by the variational construction.  Multiplication is chronological composition: `σ * τ` applies
`σ` first and then `τ`. -/
structure DifferentialFieldAut (C K : Type*) [Field C] [Field K]
    [Algebra C K] [Differential K] where
  toRingEquiv : K ≃+* K
  fixes : ∀ c : C, toRingEquiv (algebraMap C K c) = algebraMap C K c
  deriv_comm : ∀ x : K,
    toRingEquiv (Differential.deriv x) = Differential.deriv (toRingEquiv x)

namespace DifferentialFieldAut

omit [IsConstantBase C K] in
@[ext] theorem ext {σ τ : DifferentialFieldAut C K}
    (h : σ.toRingEquiv = τ.toRingEquiv) : σ = τ := by
  cases σ
  cases τ
  cases h
  rfl

instance : One (DifferentialFieldAut C K) :=
  ⟨⟨RingEquiv.refl K, fun _ => rfl, fun _ => rfl⟩⟩

instance : Mul (DifferentialFieldAut C K) :=
  ⟨fun σ τ =>
    ⟨σ.toRingEquiv.trans τ.toRingEquiv,
      fun c => by rw [RingEquiv.trans_apply, σ.fixes c, τ.fixes c],
      DiffOp.trans_deriv_comm σ.toRingEquiv τ.toRingEquiv σ.deriv_comm τ.deriv_comm⟩⟩

instance : Inv (DifferentialFieldAut C K) :=
  ⟨fun σ =>
    ⟨σ.toRingEquiv.symm, symm_fixes σ.fixes,
      DiffOp.symm_deriv_comm σ.deriv_comm⟩⟩

instance : Group (DifferentialFieldAut C K) where
  mul_assoc σ τ υ := by ext x; rfl
  one_mul σ := by ext x; rfl
  mul_one σ := by ext x; rfl
  inv_mul_cancel σ := by
    ext x
    exact σ.toRingEquiv.apply_symm_apply x

end DifferentialFieldAut

/-- Kähler semilinearity as a semilinear map over the full operator-ring automorphism. -/
def kaehlerDiffOpSemilinearMap {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x)) :
    Ω[K⁄C] →ₛₗ[(DiffOp.mapRingEquiv σ hδ).toRingHom] Ω[K⁄C] where
  toFun := kaehlerSemilinear hfix
  map_add' := map_add _
  map_smul' := kaehlerSemilinear_diffOp_smul hfix hδ

/-- Kähler semilinearity preserves the canonical Ore-torsion submodule. -/
theorem kaehlerSemilinear_mem_oreTorsion {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    {ω : Ω[K⁄C]}
    (hω : ω ∈ DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])) :
    kaehlerSemilinear hfix ω ∈
      DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C]) := by
  obtain ⟨r, hr, hrω⟩ := hω
  refine ⟨DiffOp.mapRingEquiv σ hδ r, ?_, ?_⟩
  · intro hzero
    apply hr
    apply (DiffOp.mapRingEquiv σ hδ).injective
    simpa only [map_zero] using hzero
  · rw [← kaehlerSemilinear_diffOp_smul hfix hδ, hrω, map_zero]

/-- The induced semilinear endomorphism of the variational Ore module. -/
def variationalOreSemilinearMap {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x)) :
    VariationalOreModule C K →ₛₗ[(DiffOp.mapRingEquiv σ hδ).toRingHom]
      VariationalOreModule C K :=
  Submodule.mapQ
    (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C]))
    (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C]))
    (kaehlerDiffOpSemilinearMap hfix hδ)
    (fun _ hω => kaehlerSemilinear_mem_oreTorsion hfix hδ hω)

/-- The quotient semilinear map sends the class of `ω` to the class of `σ₊ω`. -/
@[simp] theorem variationalOreSemilinearMap_mk {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    (ω : Ω[K⁄C]) :
    variationalOreSemilinearMap hfix hδ
        ((DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ ω) =
      (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ
        (kaehlerSemilinear hfix ω) := rfl

/-- Underlying equivalence of the differential-automorphism action on the variational Ore module.
Its full operator-semilinearity is recorded separately below. -/
def variationalOreModuleEquiv {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x)) :
    VariationalOreModule C K ≃ VariationalOreModule C K where
  toFun := variationalOreSemilinearMap hfix hδ
  invFun := variationalOreSemilinearMap (σ := σ.symm) (symm_fixes hfix)
    (DiffOp.symm_deriv_comm hδ)
  left_inv := by
    intro x
    obtain ⟨ω, rfl⟩ :=
      (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ_surjective x
    simp only [variationalOreSemilinearMap_mk]
    exact congrArg
      (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ
      (kaehlerSemilinear_symm_kaehlerSemilinear hfix ω)
  right_inv := by
    intro x
    obtain ⟨ω, rfl⟩ :=
      (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ_surjective x
    have h := kaehlerSemilinear_symm_kaehlerSemilinear (C := C)
      (σ := σ.symm) (symm_fixes hfix) ω
    simp only [variationalOreSemilinearMap_mk]
    exact congrArg
      (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ h

/-- The underlying equivalence agrees pointwise with the quotient semilinear map. -/
@[simp] theorem variationalOreModuleEquiv_apply {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    (x : VariationalOreModule C K) :
    variationalOreModuleEquiv hfix hδ x = variationalOreSemilinearMap hfix hδ x := rfl

/-- The quotient action is additive. -/
theorem variationalOreModuleEquiv_add {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    (x y : VariationalOreModule C K) :
    variationalOreModuleEquiv hfix hδ (x + y) =
      variationalOreModuleEquiv hfix hδ x + variationalOreModuleEquiv hfix hδ y :=
  (variationalOreSemilinearMap hfix hδ).map_add x y

/-- The quotient equivalence is semilinear for the full operator-ring automorphism. -/
theorem variationalOreModuleEquiv_smul {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    (r : DiffOp K) (x : VariationalOreModule C K) :
    variationalOreModuleEquiv hfix hδ (r • x) =
      DiffOp.mapRingEquiv σ hδ r • variationalOreModuleEquiv hfix hδ x :=
  (variationalOreSemilinearMap hfix hδ).map_smulₛₗ r x

/-- Identity automorphism acts identically on the canonical variational Ore module. -/
theorem variationalOreModuleEquiv_refl (x : VariationalOreModule C K) :
    variationalOreModuleEquiv (σ := RingEquiv.refl K) (fun _ => rfl)
      (fun _ => rfl) x = x := by
  obtain ⟨ω, rfl⟩ :=
    (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ_surjective x
  rw [variationalOreModuleEquiv_apply, variationalOreSemilinearMap_mk,
    kaehlerSemilinear_refl]

/-- Differential-automorphism actions compose functorially on the canonical variational Ore
module. -/
theorem variationalOreModuleEquiv_trans
    (σ τ : K ≃+* K)
    (hσfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hτfix : ∀ c : C, τ (algebraMap C K c) = algebraMap C K c)
    (hσδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    (hτδ : ∀ x : K, τ (Differential.deriv x) = Differential.deriv (τ x))
    (x : VariationalOreModule C K) :
    variationalOreModuleEquiv hτfix hτδ (variationalOreModuleEquiv hσfix hσδ x) =
      variationalOreModuleEquiv (σ := σ.trans τ)
        (fun c => by rw [RingEquiv.trans_apply, hσfix c, hτfix c])
        (DiffOp.trans_deriv_comm σ τ hσδ hτδ) x := by
  obtain ⟨ω, rfl⟩ :=
    (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ_surjective x
  simp only [variationalOreModuleEquiv_apply, variationalOreSemilinearMap_mk]
  exact congrArg
    (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ
    (kaehlerSemilinear_trans σ τ hσfix hτfix ω)

/-- Finite differential generation makes the canonical variational Ore module free. -/
theorem variationalOreModule_free {n : ℕ} {y : Fin n → K}
    (hy : differentialAdjoin C (Set.range y) = ⊤) :
    Module.Free (DiffOp K) (VariationalOreModule C K) :=
  free_quotient_kaehler_of_torsionFree hy
    (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C]))
    DiffOp.oreTorsionQuotient_torsionFree

/-- Finite differential generation also makes the canonical variational Ore module finitely
generated over the differential-operator ring. -/
theorem variationalOreModule_finite {n : ℕ} {y : Fin n → K}
    (hy : differentialAdjoin C (Set.range y) = ⊤) :
    Module.Finite (DiffOp K) (VariationalOreModule C K) := by
  let N : Submodule (DiffOp K) (Ω[K⁄C]) :=
    DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])
  have hspan : Submodule.span (DiffOp K)
      (Set.range fun i => N.mkQ (KaehlerDifferential.D C K (y i))) = ⊤ := by
    have himg : Submodule.map N.mkQ
        (Submodule.span (DiffOp K) (KaehlerDifferential.D C K '' Set.range y)) = ⊤ := by
      rw [span_diffOp_D_eq_top hy, Submodule.map_top, N.range_mkQ]
    rw [Submodule.map_span] at himg
    have hset : (N.mkQ : Ω[K⁄C] → (Ω[K⁄C]) ⧸ N) ''
        (KaehlerDifferential.D C K '' Set.range y) =
          Set.range fun i => N.mkQ (KaehlerDifferential.D C K (y i)) := by
      rw [← Set.image_comp, ← Set.range_comp]
      rfl
    rwa [hset] at himg
  apply Module.Finite.of_fg_top
  rw [← hspan]
  exact Submodule.fg_span (Set.finite_range _)

/-- A finite differential generating family produces an actual finite operator basis of the
canonical variational Ore module.  The rank is obtained from its free-basis index; no basis or rank
is assumed. -/
theorem exists_fin_basis_variationalOreModule {n : ℕ} {y : Fin n → K}
    (hy : differentialAdjoin C (Set.range y) = ⊤) :
    ∃ r : ℕ,
      Nonempty (Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) := by
  letI : Module.Free (DiffOp K) (VariationalOreModule C K) :=
    variationalOreModule_free hy
  letI : Module.Finite (DiffOp K) (VariationalOreModule C K) :=
    variationalOreModule_finite hy
  let ι := Module.Free.ChooseBasisIndex (DiffOp K) (VariationalOreModule C K)
  letI : Fintype ι := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  exact ⟨Fintype.card ι, ⟨(Module.Free.chooseBasis (DiffOp K)
    (VariationalOreModule C K)).reindex e⟩⟩

/-- In a finite basis, the action on the variational Ore module yields a genuine unit matrix over
the completed pseudodifferential skew field. -/
theorem exists_variationalOre_completedPseudoDiffOpMatrixUnit {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    ∃ A A' : Matrix (Fin r) (Fin r) (DiffOp K),
      ∃ Ahat : (Matrix (Fin r) (Fin r) (DiffOp.CompletedPseudoDiffOp K))ˣ,
        (∀ i, variationalOreModuleEquiv hfix hδ (b i) = ∑ j, A i j • b j) ∧
        (∀ i, variationalOreModuleEquiv (σ := σ.symm) (symm_fixes hfix)
            (DiffOp.symm_deriv_comm hδ) (b i) = ∑ j, A' i j • b j) ∧
        (Ahat : Matrix (Fin r) (Fin r) (DiffOp.CompletedPseudoDiffOp K)) =
          A.map DiffOp.diffOpToCompletedPseudoRingHom := by
  apply DiffOp.exists_completedPseudoDiffOpMatrixUnit_of_semilinear_equiv σ hδ b
    (variationalOreModuleEquiv hfix hδ)
    (variationalOreModuleEquiv (σ := σ.symm) (symm_fixes hfix)
      (DiffOp.symm_deriv_comm hδ))
  · exact variationalOreModuleEquiv_add hfix hδ
  · exact variationalOreModuleEquiv_smul hfix hδ
  · exact variationalOreModuleEquiv_add (σ := σ.symm) (symm_fixes hfix)
      (DiffOp.symm_deriv_comm hδ)
  · intro a x
    exact variationalOreModuleEquiv_smul (σ := σ.symm) (symm_fixes hfix)
      (DiffOp.symm_deriv_comm hδ) a x
  · exact (variationalOreModuleEquiv hfix hδ).right_inv
  · exact (variationalOreModuleEquiv hfix hδ).left_inv

/-- Canonical operator-matrix unit of the variational Ore action in a fixed finite basis. -/
noncomputable def variationalOreOperatorMatrixUnit {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    (Matrix (Fin r) (Fin r) (DiffOp K))ˣ :=
  basisMapMatrixUnitOfSemilinearEquiv b
    (variationalOreModuleEquiv hfix hδ)
    (variationalOreModuleEquiv (σ := σ.symm) (symm_fixes hfix)
      (DiffOp.symm_deriv_comm hδ))
    (variationalOreModuleEquiv_add hfix hδ)
    (variationalOreModuleEquiv_smul hfix hδ)
    (variationalOreModuleEquiv_add (σ := σ.symm) (symm_fixes hfix)
      (DiffOp.symm_deriv_comm hδ))
    (variationalOreModuleEquiv_smul (σ := σ.symm) (symm_fixes hfix)
      (DiffOp.symm_deriv_comm hδ))
    (variationalOreModuleEquiv hfix hδ).right_inv
    (variationalOreModuleEquiv hfix hδ).left_inv

/-- Canonical completed matrix unit of the variational Ore action in a fixed finite basis. -/
noncomputable def variationalOreCompletedMatrixUnit {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    (Matrix (Fin r) (Fin r) (DiffOp.CompletedPseudoDiffOp K))ˣ :=
  DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit
    (variationalOreOperatorMatrixUnit hfix hδ b)

/-- The completed matrix unit is the completed embedding of the canonical operator matrix. -/
@[simp] theorem variationalOreCompletedMatrixUnit_val {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    (variationalOreCompletedMatrixUnit hfix hδ b :
        Matrix (Fin r) (Fin r) (DiffOp.CompletedPseudoDiffOp K)) =
      (basisMapMatrix b (variationalOreModuleEquiv hfix hδ)).map
        DiffOp.diffOpToCompletedPseudoRingHom := rfl

/-- Literal projective completed-lattice action attached to a differential automorphism in a fixed
finite operator basis. -/
noncomputable def variationalOreProjectiveBuildingAction {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r) →
      DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r) :=
  DiffOp.differentialVariationalProjectiveSemilinearAction σ hδ
    (variationalOreCompletedMatrixUnit hfix hδ b)

/-- The actual differential-automorphism matrices in two finite operator bases obey the exact
twisted change-of-basis identity.  With row coordinates `c = B b`, this is
`A_c B = σ(B) A_b`; invertibility of the basis transition converts it to the usual twisted
conjugacy formula. -/
theorem variationalOre_actionMatrix_changeBasis {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    {r : ℕ}
    (b c : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (B A Ac : Matrix (Fin r) (Fin r) (DiffOp K))
    (hB : ∀ i, c i = ∑ j, B i j • b j)
    (hA : ∀ i, variationalOreModuleEquiv hfix hδ (b i) = ∑ j, A i j • b j)
    (hAc : ∀ i, variationalOreModuleEquiv hfix hδ (c i) = ∑ j, Ac i j • c j) :
    Ac * B = B.map (DiffOp.mapRingEquiv σ hδ : DiffOp K →+* DiffOp K) * A :=
  matrix_changeBasis_semilinear b c (variationalOreModuleEquiv hfix hδ)
    (variationalOreModuleEquiv_add hfix hδ)
    (variationalOreModuleEquiv_smul hfix hδ) B A Ac hB hA hAc

/-- Canonically extracted matrices of the variational Ore action satisfy literal twisted
conjugacy under every finite operator-basis change. -/
theorem variationalOre_basisMapMatrix_changeBasis {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    {r : ℕ}
    (b c : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    basisMapMatrix c (variationalOreModuleEquiv hfix hδ) =
      (basisTransitionMatrix b c).map
          (DiffOp.mapRingEquiv σ hδ : DiffOp K →+* DiffOp K) *
        basisMapMatrix b (variationalOreModuleEquiv hfix hδ) *
          (basisTransitionMatrixUnit b c).inv :=
  basisMapMatrix_changeBasis_semilinear b c (variationalOreModuleEquiv hfix hδ)
    (variationalOreModuleEquiv_add hfix hδ)
    (variationalOreModuleEquiv_smul hfix hδ)

/-- Canonical operator-matrix units obey the denominator-free twisted basis-change identity. -/
theorem variationalOreOperatorMatrixUnit_changeBasis {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    {r : ℕ}
    (b c : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    variationalOreOperatorMatrixUnit hfix hδ c * basisTransitionMatrixUnit b c =
      DiffOp.mapDiffOpMatrixUnit σ hδ (basisTransitionMatrixUnit b c) *
        variationalOreOperatorMatrixUnit hfix hδ b := by
  apply Units.ext
  exact matrix_changeBasis_semilinear b c (variationalOreModuleEquiv hfix hδ)
    (variationalOreModuleEquiv_add hfix hδ)
    (variationalOreModuleEquiv_smul hfix hδ)
    (basisTransitionMatrix b c)
    (basisMapMatrix b (variationalOreModuleEquiv hfix hδ))
    (basisMapMatrix c (variationalOreModuleEquiv hfix hδ))
    (basisTransitionMatrix_apply b c)
    (basisMapMatrix_apply b (variationalOreModuleEquiv hfix hδ))
    (basisMapMatrix_apply c (variationalOreModuleEquiv hfix hδ))

/-- Completed transition matrix between two finite operator bases. -/
noncomputable def variationalOreCompletedBasisTransition
    {r : ℕ}
    (b c : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    (Matrix (Fin r) (Fin r) (DiffOp.CompletedPseudoDiffOp K))ˣ :=
  DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit
    (basisTransitionMatrixUnit b c)

/-- Completed action and transition units obey the exact twisted basis-change identity. -/
theorem variationalOreCompletedMatrixUnit_changeBasis {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    {r : ℕ}
    (b c : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    variationalOreCompletedMatrixUnit hfix hδ c *
        variationalOreCompletedBasisTransition b c =
      DiffOp.mapCompletedPseudoDiffOpMatrixUnit σ hδ
          (variationalOreCompletedBasisTransition b c) *
        variationalOreCompletedMatrixUnit hfix hδ b := by
  unfold variationalOreCompletedMatrixUnit variationalOreCompletedBasisTransition
  rw [DiffOp.mapCompletedPseudoDiffOpMatrixUnit_completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit,
    ← DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_mul,
    ← DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_mul]
  congr 1
  exact variationalOreOperatorMatrixUnit_changeBasis hfix hδ b c

/-- The projective completed-lattice actions constructed from two finite operator bases are
conjugate by their completed transition matrix.  Thus changing basis cannot change intrinsic
translation data once the metric/Cartan layer is supplied. -/
theorem variationalOreProjectiveBuildingAction_changeBasis {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    {r : ℕ}
    (b c : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
        (variationalOreCompletedBasisTransition b c)
        (variationalOreProjectiveBuildingAction hfix hδ c x) =
      variationalOreProjectiveBuildingAction hfix hδ b
        (DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
          (variationalOreCompletedBasisTransition b c) x) := by
  unfold variationalOreProjectiveBuildingAction
  unfold DiffOp.differentialVariationalProjectiveSemilinearAction
  rw [DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix_mul,
    DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierCoefficients_matrix,
    DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix_mul,
    variationalOreCompletedMatrixUnit_changeBasis]

/-- Canonical operator matrices of the variational action satisfy the exact semilinear cocycle
law in every fixed finite basis. -/
theorem variationalOre_basisMapMatrix_trans
    (σ τ : K ≃+* K)
    (hσfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hτfix : ∀ c : C, τ (algebraMap C K c) = algebraMap C K c)
    (hσδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    (hτδ : ∀ x : K, τ (Differential.deriv x) = Differential.deriv (τ x))
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    basisMapMatrix b
        (variationalOreModuleEquiv (σ := σ.trans τ)
          (fun c => by rw [RingEquiv.trans_apply, hσfix c, hτfix c])
          (DiffOp.trans_deriv_comm σ τ hσδ hτδ)) =
      (basisMapMatrix b (variationalOreModuleEquiv hσfix hσδ)).map
          (DiffOp.mapRingEquiv τ hτδ : DiffOp K →+* DiffOp K) *
        basisMapMatrix b (variationalOreModuleEquiv hτfix hτδ) := by
  have hcomp := basisMapMatrix_semilinear_comp
    (τ := DiffOp.mapRingEquiv τ hτδ) b
    (variationalOreModuleEquiv hσfix hσδ)
    (variationalOreModuleEquiv hτfix hτδ)
    (variationalOreModuleEquiv_add hτfix hτδ)
    (variationalOreModuleEquiv_smul hτfix hτδ)
  have heq : (fun x => variationalOreModuleEquiv hτfix hτδ
      (variationalOreModuleEquiv hσfix hσδ x)) =
      variationalOreModuleEquiv (σ := σ.trans τ)
        (fun c => by rw [RingEquiv.trans_apply, hσfix c, hτfix c])
        (DiffOp.trans_deriv_comm σ τ hσδ hτδ) := by
    funext x
    exact variationalOreModuleEquiv_trans σ τ hσfix hτfix hσδ hτδ x
  rw [heq] at hcomp
  exact hcomp

/-- Canonical operator-matrix units satisfy the semilinear cocycle law. -/
theorem variationalOreOperatorMatrixUnit_trans
    (σ τ : K ≃+* K)
    (hσfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hτfix : ∀ c : C, τ (algebraMap C K c) = algebraMap C K c)
    (hσδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    (hτδ : ∀ x : K, τ (Differential.deriv x) = Differential.deriv (τ x))
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    variationalOreOperatorMatrixUnit
        (σ := σ.trans τ)
        (fun c => by rw [RingEquiv.trans_apply, hσfix c, hτfix c])
        (DiffOp.trans_deriv_comm σ τ hσδ hτδ) b =
      DiffOp.mapDiffOpMatrixUnit τ hτδ
          (variationalOreOperatorMatrixUnit hσfix hσδ b) *
        variationalOreOperatorMatrixUnit hτfix hτδ b := by
  apply Units.ext
  exact variationalOre_basisMapMatrix_trans σ τ hσfix hτfix hσδ hτδ b

/-- Canonical completed matrix units satisfy the same semilinear cocycle law. -/
theorem variationalOreCompletedMatrixUnit_trans
    (σ τ : K ≃+* K)
    (hσfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hτfix : ∀ c : C, τ (algebraMap C K c) = algebraMap C K c)
    (hσδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    (hτδ : ∀ x : K, τ (Differential.deriv x) = Differential.deriv (τ x))
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    variationalOreCompletedMatrixUnit
        (σ := σ.trans τ)
        (fun c => by rw [RingEquiv.trans_apply, hσfix c, hτfix c])
        (DiffOp.trans_deriv_comm σ τ hσδ hτδ) b =
      DiffOp.mapCompletedPseudoDiffOpMatrixUnit τ hτδ
          (variationalOreCompletedMatrixUnit hσfix hσδ b) *
        variationalOreCompletedMatrixUnit hτfix hτδ b := by
  rw [variationalOreCompletedMatrixUnit,
    variationalOreCompletedMatrixUnit,
    variationalOreCompletedMatrixUnit,
    DiffOp.mapCompletedPseudoDiffOpMatrixUnit_completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit,
    ← DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_mul]
  congr 1
  exact variationalOreOperatorMatrixUnit_trans σ τ hσfix hτfix hσδ hτδ b

/-- Identity differential automorphism has the identity canonical operator matrix unit. -/
theorem variationalOreOperatorMatrixUnit_refl
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    variationalOreOperatorMatrixUnit
        (σ := RingEquiv.refl K) (fun _ => rfl) (fun _ => rfl) b = 1 := by
  apply Units.ext
  exact basisMapMatrix_eq_one b
    (variationalOreModuleEquiv (σ := RingEquiv.refl K) (fun _ => rfl) (fun _ => rfl))
    variationalOreModuleEquiv_refl

/-- Identity differential automorphism has the identity canonical completed matrix unit. -/
theorem variationalOreCompletedMatrixUnit_refl
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    variationalOreCompletedMatrixUnit
        (σ := RingEquiv.refl K) (fun _ => rfl) (fun _ => rfl) b = 1 := by
  rw [variationalOreCompletedMatrixUnit, variationalOreOperatorMatrixUnit_refl]
  exact map_one _

/-- The canonical projective completed-lattice action is functorial in a fixed finite operator
basis. -/
theorem variationalOreProjectiveBuildingAction_trans
    (σ τ : K ≃+* K)
    (hσfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hτfix : ∀ c : C, τ (algebraMap C K c) = algebraMap C K c)
    (hσδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    (hτδ : ∀ x : K, τ (Differential.deriv x) = Differential.deriv (τ x))
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    variationalOreProjectiveBuildingAction hτfix hτδ b
        (variationalOreProjectiveBuildingAction hσfix hσδ b x) =
      variationalOreProjectiveBuildingAction
        (σ := σ.trans τ)
        (fun c => by rw [RingEquiv.trans_apply, hσfix c, hτfix c])
        (DiffOp.trans_deriv_comm σ τ hσδ hτδ) b x := by
  unfold variationalOreProjectiveBuildingAction
  rw [DiffOp.differentialVariationalProjectiveSemilinearAction_trans,
    ← variationalOreCompletedMatrixUnit_trans σ τ hσfix hτfix hσδ hτδ b]

/-- Identity differential automorphism acts identically on the projective completed-lattice
carrier. -/
theorem variationalOreProjectiveBuildingAction_refl
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    variationalOreProjectiveBuildingAction
        (σ := RingEquiv.refl K) (fun _ => rfl) (fun _ => rfl) b x = x := by
  unfold variationalOreProjectiveBuildingAction
  rw [variationalOreCompletedMatrixUnit_refl]
  exact DiffOp.differentialVariationalProjectiveSemilinearAction_refl_one x

namespace DifferentialFieldAut

/-- Projective completed-lattice action of a bundled differential-field automorphism in a fixed
finite operator basis. -/
noncomputable def projectiveBuildingAction
    (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r) →
      DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r) :=
  variationalOreProjectiveBuildingAction σ.fixes σ.deriv_comm b

/-- Chronological multiplication of bundled differential automorphisms is composition of their
projective actions. -/
theorem projectiveBuildingAction_mul
    (σ τ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    projectiveBuildingAction (σ * τ) b x =
      projectiveBuildingAction τ b (projectiveBuildingAction σ b x) := by
  exact (variationalOreProjectiveBuildingAction_trans
    σ.toRingEquiv τ.toRingEquiv σ.fixes τ.fixes σ.deriv_comm τ.deriv_comm b x).symm

/-- Identity bundled differential automorphism acts identically. -/
theorem projectiveBuildingAction_one
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    projectiveBuildingAction (1 : DifferentialFieldAut C K) b x = x :=
  variationalOreProjectiveBuildingAction_refl b x

/-- Every bundled differential automorphism acts by a genuine equivalence of the projective
completed-lattice carrier; its inverse is the action of the inverse automorphism. -/
noncomputable def projectiveBuildingEquiv
    (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r) ≃
      DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r) where
  toFun := projectiveBuildingAction σ b
  invFun := projectiveBuildingAction σ⁻¹ b
  left_inv x := by
    rw [← projectiveBuildingAction_mul σ σ⁻¹ b x, mul_inv_cancel,
      projectiveBuildingAction_one]
  right_inv x := by
    rw [← projectiveBuildingAction_mul σ⁻¹ σ b x, inv_mul_cancel,
      projectiveBuildingAction_one]

/-- The carrier equivalences respect chronological multiplication exactly. -/
theorem projectiveBuildingEquiv_mul
    (σ τ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    projectiveBuildingEquiv (σ * τ) b =
      (projectiveBuildingEquiv σ b).trans (projectiveBuildingEquiv τ b) := by
  ext x
  exact projectiveBuildingAction_mul σ τ b x

/-- Identity automorphism gives the identity carrier equivalence. -/
theorem projectiveBuildingEquiv_one
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    projectiveBuildingEquiv (1 : DifferentialFieldAut C K) b = Equiv.refl _ := by
  ext x
  exact projectiveBuildingAction_one b x

end DifferentialFieldAut

/-- The matrix of the differential-automorphism action has a trivial operator-row-lattice
conductor: its operator elementary divisors all have degree zero.  Identifying this certificate
with completed-building Cartan position is a separate comparison theorem. -/
theorem exists_variationalOre_operatorMatrix_degree_balance {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x))
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    ∃ A A' : Matrix (Fin r) (Fin r) (DiffOp K),
      (∀ i, variationalOreModuleEquiv hfix hδ (b i) = ∑ j, A i j • b j) ∧
      (∀ i, variationalOreModuleEquiv (σ := σ.symm) (symm_fixes hfix)
          (DiffOp.symm_deriv_comm hδ) (b i) = ∑ j, A' i j • b j) ∧
      ∃ d : Fin r → DiffOp K, (∀ i, d i ≠ 0) ∧
        ∑ i, DiffOp.degree (d i) = 0 ∧ ∀ i, DiffOp.degree (d i) = 0 := by
  classical
  obtain ⟨A, A', hA, hA', hAA', hA'A⟩ :=
    isUnit_matrix_of_semilinear_equiv (DiffOp.mapRingEquiv σ hδ) b
      (variationalOreModuleEquiv hfix hδ)
      (variationalOreModuleEquiv (σ := σ.symm) (symm_fixes hfix)
        (DiffOp.symm_deriv_comm hδ))
      (variationalOreModuleEquiv_add hfix hδ)
      (variationalOreModuleEquiv_smul hfix hδ)
      (variationalOreModuleEquiv_add (σ := σ.symm) (symm_fixes hfix)
        (DiffOp.symm_deriv_comm hδ))
      (variationalOreModuleEquiv_smul (σ := σ.symm) (symm_fixes hfix)
        (DiffOp.symm_deriv_comm hδ))
      (variationalOreModuleEquiv hfix hδ).right_inv
      (variationalOreModuleEquiv hfix hδ).left_inv
  let Q := A'.map (DiffOp.mapRingEquiv σ hδ : DiffOp K →+* DiffOp K)
  have hAQ : A * Q = 1 := hAA'
  have hQA : Q * A = 1 := hA'A
  have hright : ∀ v : Fin r → DiffOp K,
      Matrix.vecMul (Matrix.vecMul v A) Q = v := by
    intro v
    rw [Matrix.vecMul_vecMul, hAQ, Matrix.vecMul_one]
  have hleft : ∀ v : Fin r → DiffOp K,
      Matrix.vecMul (Matrix.vecMul v Q) A = v := by
    intro v
    rw [Matrix.vecMul_vecMul, hQA, Matrix.vecMul_one]
  obtain ⟨d, hd, hsum, hzero⟩ :=
    DiffOp.exists_degree_sum_eq_zero_of_vecMul_inverse A Q hright hleft
  exact ⟨A, A', hA, hA', d, hd, hsum, hzero⟩

/-- Finite differential generation alone supplies a finite basis and the genuine completed matrix
unit of every differential automorphism; no basis or rank is additional input. -/
theorem exists_variationalOre_finiteBasis_completedPseudoDiffOpMatrixUnit
    {n : ℕ} {y : Fin n → K}
    (hy : differentialAdjoin C (Set.range y) = ⊤)
    {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x)) :
    ∃ r : ℕ,
      ∃ b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K),
        ∃ A A' : Matrix (Fin r) (Fin r) (DiffOp K),
          ∃ Ahat : (Matrix (Fin r) (Fin r) (DiffOp.CompletedPseudoDiffOp K))ˣ,
            (∀ i, variationalOreModuleEquiv hfix hδ (b i) = ∑ j, A i j • b j) ∧
            (∀ i, variationalOreModuleEquiv (σ := σ.symm) (symm_fixes hfix)
                (DiffOp.symm_deriv_comm hδ) (b i) = ∑ j, A' i j • b j) ∧
            (Ahat : Matrix (Fin r) (Fin r) (DiffOp.CompletedPseudoDiffOp K)) =
              A.map DiffOp.diffOpToCompletedPseudoRingHom := by
  obtain ⟨r, ⟨b⟩⟩ := exists_fin_basis_variationalOreModule hy
  obtain ⟨A, A', Ahat, hA, hA', hAhat⟩ :=
    exists_variationalOre_completedPseudoDiffOpMatrixUnit hfix hδ b
  exact ⟨r, b, A, A', Ahat, hA, hA', hAhat⟩

/-- Finite differential generation alone also supplies the operator-row-lattice degree-balance
certificate for the automorphism matrix. -/
theorem exists_variationalOre_finiteBasis_operatorMatrix_degree_balance
    {n : ℕ} {y : Fin n → K}
    (hy : differentialAdjoin C (Set.range y) = ⊤)
    {σ : K ≃+* K}
    (hfix : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x)) :
    ∃ r : ℕ,
      ∃ b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K),
        ∃ A A' : Matrix (Fin r) (Fin r) (DiffOp K),
          (∀ i, variationalOreModuleEquiv hfix hδ (b i) = ∑ j, A i j • b j) ∧
          (∀ i, variationalOreModuleEquiv (σ := σ.symm) (symm_fixes hfix)
              (DiffOp.symm_deriv_comm hδ) (b i) = ∑ j, A' i j • b j) ∧
          ∃ d : Fin r → DiffOp K, (∀ i, d i ≠ 0) ∧
            ∑ i, DiffOp.degree (d i) = 0 ∧ ∀ i, DiffOp.degree (d i) = 0 := by
  obtain ⟨r, ⟨b⟩⟩ := exists_fin_basis_variationalOreModule hy
  obtain ⟨A, A', hA, hA', d, hd, hsum, hzero⟩ :=
    exists_variationalOre_operatorMatrix_degree_balance hfix hδ b
  exact ⟨r, b, A, A', hA, hA', d, hd, hsum, hzero⟩

end
end GaloisForLFunctions.HTGeometry

import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.CongruenceOrderSoldering

/-!
# Source-linear comparisons from the cotangent module to the trace-law defect

The trace-law defect of the diagonal congruence order is annihilated by `a²`, so the submodule
`a·L` is a module over the residue field.  Every source-linear map from the cotangent module to
the defect therefore factors through the closed fibre, and the space of such maps is the matrix
algebra on the observer directions.
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace HTGeometry.ConstraintRelativity

open MvPolynomial

section Annihilation

variable {R : Type*} [CommRing R] {a : R} {m : ℕ} [IsDomain R] [Invertible ((m : R) + 1)]

omit [IsDomain R] in
/-- The trace-law defect is annihilated by `a²`. -/
theorem sq_smul_traceDefect (ℓ : traceDefect a m) : (a ^ 2) • ℓ = 0 := by
  refine (traceDefectModelEquiv a m).injective ?_
  rw [map_smul, map_zero]
  funext j
  rw [Pi.smul_apply, Pi.zero_apply]
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective (Ideal.span ({a ^ 2} : Set R))
    (traceDefectModelEquiv a m ℓ j)
  rw [← hr, ← Submodule.Quotient.mk_smul, smul_eq_mul, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mem_span_singleton.2 ⟨r, rfl⟩

omit [IsDomain R] in
theorem smul_smul_aMul (w : traceDefect a m) : a • (a • w) = 0 := by
  rw [smul_smul, ← pow_two]
  exact sq_smul_traceDefect w

variable [Invertible ((m : R) - 1)]

omit [IsDomain R] [Invertible ((m : R) - 1)] in
/-- **Card `(26f)`, first step.**  The maximal ideal annihilates `a·L`. -/
theorem maximalIdealA_smul_aMulA :
    (maximalIdealA a m) • (aMulA a m) = ⊥ := by
  refine le_antisymm (Submodule.smul_le.2 fun c hc x hx => ?_) bot_le
  obtain ⟨w, rfl⟩ := mem_aMul.1 hx
  rw [Submodule.mem_bot]
  rw [maximalIdealA] at hc
  induction hc using Submodule.span_induction with
  | mem y hy =>
    rcases hy with hy | ⟨i, rfl⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [IsScalarTower.algebraMap_smul]
      exact smul_smul_aMul w
    · obtain ⟨u, hu⟩ := mem_aMul.1 (congruenceX_smul_mem_aMul i w)
      rw [smul_comm, ← hu]
      exact smul_smul_aMul u
  | zero => exact zero_smul (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (a • w)
  | add x y _ _ hx hy => rw [add_smul, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_mul, mul_smul, hx, smul_zero]

/-- **Card `(26f)`, second step.**  Every source-linear comparison annihilates `𝔪_A·Ω`, hence
factors through the closed cotangent fibre. -/
theorem soldering_annihilates_maximalIdeal (ha : a ≠ 0)
    (φ : Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]
      →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] traceDefect a m)
    {ω : Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]}
    (hω : ω ∈ (maximalIdealA a m) • (⊤ : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R])) :
    φ ω = 0 := by
  refine Submodule.smul_induction_on hω ?_ ?_
  · intro c hc x _
    rw [map_smul]
    have hmem : c • φ x ∈ (maximalIdealA a m) • (aMulA a m) :=
      Submodule.smul_mem_smul hc (soldering_range_le ha φ x)
    rwa [maximalIdealA_smul_aMulA, Submodule.mem_bot] at hmem
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

omit [IsDomain R] [Invertible ((m : R) - 1)] in
theorem maximalIdealA_smul_eq_zero {c : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m}
    (hc : c ∈ maximalIdealA a m) {x : traceDefect a m}
    (hx : x ∈ aMul a (traceDefect a m)) : c • x = 0 := by
  have hmem : c • x ∈ (maximalIdealA a m) • (aMulA a m) := Submodule.smul_mem_smul hc hx
  rwa [maximalIdealA_smul_aMulA, Submodule.mem_bot] at hmem

end Annihilation

/-! ## The residue-field structure of `a·L` -/

section ResidueModel

variable {R : Type*} [CommRing R]

theorem congruenceX_mem_maximalIdealA {a : R} {m : ℕ} (i : Fin m) :
    congruenceX a m i ∈ maximalIdealA a m := Ideal.subset_span (Or.inr ⟨i, rfl⟩)

theorem algebraMap_mem_maximalIdealA (a : R) (m : ℕ) :
    algebraMap R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) a ∈ maximalIdealA a m :=
  Ideal.subset_span (Or.inl rfl)

/-- A product of submodules is the submodule of products. -/
def submodulePiEquiv {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (p : ∀ i, Submodule R (M i)) :
    ↥(Submodule.pi Set.univ p) ≃ₗ[R] ∀ i, ↥(p i) where
  toFun v i := ⟨(v : ∀ i, M i) i, v.2 i (Set.mem_univ i)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨fun i => (w i : M i), fun i _ => (w i).2⟩
  left_inv _ := rfl
  right_inv _ := funext fun _ => Subtype.ext rfl

variable {a : R}

/-- The `a`-multiples in `R/a²`, as the image of `R`. -/
noncomputable def aMulSqMap (a : R) :
    R →ₗ[R] ↥(aMul a (R ⧸ Ideal.span ({a ^ 2} : Set R))) where
  toFun r := ⟨a • Submodule.Quotient.mk r, ⟨Submodule.Quotient.mk r, rfl⟩⟩
  map_add' r r' := by
    refine Subtype.ext ?_
    show a • Submodule.Quotient.mk (r + r') = a • Submodule.Quotient.mk r
      + a • Submodule.Quotient.mk r'
    rw [Submodule.Quotient.mk_add, smul_add]
  map_smul' c r := by
    refine Subtype.ext ?_
    show a • Submodule.Quotient.mk (c * r) = c • (a • Submodule.Quotient.mk r)
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      ← Submodule.Quotient.mk_smul]
    simp only [smul_eq_mul]
    congr 1
    ring

theorem aMulSqMap_surjective (a : R) : Function.Surjective (aMulSqMap a) := by
  rintro ⟨x, hx⟩
  obtain ⟨u, rfl⟩ := mem_aMul.1 hx
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span ({a ^ 2} : Set R)) u
  exact ⟨r, rfl⟩

variable [IsDomain R]

theorem ker_aMulSqMap (ha : a ≠ 0) :
    LinearMap.ker (aMulSqMap a) = Ideal.span ({a} : Set R) := by
  ext r
  rw [LinearMap.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro h
    have h' : a • (Submodule.Quotient.mk r : R ⧸ Ideal.span ({a ^ 2} : Set R)) = 0 :=
      congrArg Subtype.val h
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, Submodule.Quotient.mk_eq_zero,
      Ideal.mem_span_singleton] at h'
    obtain ⟨c, hc⟩ := h'
    exact ⟨c, mul_left_cancel₀ ha (by linear_combination hc)⟩
  · rintro ⟨c, rfl⟩
    refine Subtype.ext ?_
    show a • (Submodule.Quotient.mk (a * c) : R ⧸ Ideal.span ({a ^ 2} : Set R)) = 0
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, Submodule.Quotient.mk_eq_zero,
      Ideal.mem_span_singleton]
    exact ⟨c, by ring⟩

/-- The `a`-multiples in `R/a²` form a copy of the residue ring. -/
noncomputable def aMulSqEquiv (ha : a ≠ 0) :
    ↥(aMul a (R ⧸ Ideal.span ({a ^ 2} : Set R))) ≃ₗ[R] (R ⧸ Ideal.span ({a} : Set R)) :=
  (LinearMap.quotKerEquivOfSurjective _ (aMulSqMap_surjective a)).symm.trans
    (Submodule.quotEquivOfEq _ _ (ker_aMulSqMap ha))

end ResidueModel

/-! ## The space of source-linear comparisons -/

section HomSpace

variable {R : Type*} [CommRing R] {a : R} {m : ℕ} [IsDomain R] [Invertible ((m : R) + 1)]

/-- `a·L` is free on the observer directions over the residue ring. -/
noncomputable def aMulTraceDefectEquiv (ha : a ≠ 0) :
    ↥(aMulA a m) ≃ₗ[R] (Fin m → R ⧸ Ideal.span ({a} : Set R)) :=
  (Submodule.equivMapOfInjective (traceDefectModelEquiv a m).toLinearMap
      (traceDefectModelEquiv a m).injective (aMul a (traceDefect a m))).trans
    ((LinearEquiv.ofEq _ _ (map_aMul (traceDefectModelEquiv a m))).trans
      ((LinearEquiv.ofEq _ _
          (aMul_pi a fun _ : Fin m => R ⧸ Ideal.span ({a ^ 2} : Set R))).trans
        ((submodulePiEquiv _).trans (LinearEquiv.piCongrRight fun _ => aMulSqEquiv ha))))

/-- The evaluation of a coefficient vector against a family of defect classes. -/
noncomputable def solderingRaw (ℓ : Fin m → traceDefect a m) :
    (Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
      →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] traceDefect a m :=
  ∑ i, (LinearMap.toSpanSingleton _ _ (ℓ i)).comp (LinearMap.proj i)

omit [IsDomain R] [Invertible ((m : R) + 1)] in
theorem solderingRaw_single (ℓ : Fin m → traceDefect a m) (i : Fin m)
    (c : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) :
    solderingRaw ℓ (Pi.single i c) = c • ℓ i := by
  classical
  simp only [solderingRaw, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.proj_apply, LinearMap.toSpanSingleton_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    exact zero_smul (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (ℓ j)
  · intro h
    exact absurd (Finset.mem_univ i) h

variable [Invertible ((m : R) - 1)]

omit [IsDomain R] [Invertible ((m : R) - 1)] in
theorem kaehlerRelations_le_ker_solderingRaw (ℓ : Fin m → ↥(aMulA a m)) :
    kaehlerRelations a m
      ≤ LinearMap.ker (solderingRaw fun i => ((ℓ i : traceDefect a m))) := by
  rw [kaehlerRelations, Submodule.span_le]
  rintro v (⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩)
  · rw [SetLike.mem_coe, LinearMap.mem_ker, solderingRaw_single]
    refine maximalIdealA_smul_eq_zero ?_ (ℓ i).2
    exact sub_mem (add_mem (congruenceX_mem_maximalIdealA i) (congruenceX_mem_maximalIdealA i))
      (algebraMap_mem_maximalIdealA a m)
  · rw [SetLike.mem_coe, LinearMap.mem_ker, map_add, solderingRaw_single, solderingRaw_single,
      maximalIdealA_smul_eq_zero (congruenceX_mem_maximalIdealA j) (ℓ i).2,
      maximalIdealA_smul_eq_zero (congruenceX_mem_maximalIdealA i) (ℓ j).2, add_zero]

/-- The source-linear comparison determined by a family of defect classes. -/
noncomputable def solderingOfPi (ℓ : Fin m → ↥(aMulA a m)) :
    Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]
      →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] traceDefect a m :=
  (Submodule.liftQ _ _ (kaehlerRelations_le_ker_solderingRaw ℓ)).comp
    (kaehlerModelEquiv (a := a) (m := m)).toLinearMap

omit [IsDomain R] [Invertible ((m : R) - 1)] in
theorem solderingOfPi_D (ℓ : Fin m → ↥(aMulA a m)) (i : Fin m) :
    solderingOfPi ℓ (KaehlerDifferential.D R
        (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (congruenceX a m i))
      = (ℓ i : traceDefect a m) := by
  rw [solderingOfPi, LinearMap.comp_apply, LinearEquiv.coe_coe,
    show (kaehlerModelEquiv (a := a) (m := m))
        (KaehlerDifferential.D R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
          (congruenceX a m i))
      = Submodule.Quotient.mk
          (Pi.single i (1 : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
            : Fin m → MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) from kaehlerToModel_D i,
    Submodule.liftQ_apply, solderingRaw_single, one_smul]

/-- The coefficient vector of a source-linear comparison. -/
noncomputable def solderingCoeff (ha : a ≠ 0) :
    (Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]
        →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] traceDefect a m)
      →ₗ[R] (Fin m → ↥(aMulA a m)) where
  toFun φ i := ⟨φ (KaehlerDifferential.D R
    (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (congruenceX a m i)),
    soldering_range_le ha φ _⟩
  map_add' _ _ := funext fun _ => Subtype.ext rfl
  map_smul' _ _ := funext fun _ => Subtype.ext rfl

theorem solderingCoeff_bijective (ha : a ≠ 0) :
    Function.Bijective (solderingCoeff (a := a) (m := m) ha) := by
  constructor
  · intro φ ψ hφψ
    refine LinearMap.ext_on (span_D_congruenceX a m) ?_
    rintro _ ⟨i, rfl⟩
    exact congrArg Subtype.val (congrFun hφψ i)
  · intro ℓ
    refine ⟨solderingOfPi ℓ, funext fun i => Subtype.ext ?_⟩
    exact solderingOfPi_D ℓ i

/-- **Card `(26f)`.**  The space of source-linear comparisons from the cotangent module to the
trace-law defect is the matrix algebra on the observer directions over the residue ring. -/
noncomputable def solderingHomMatrixEquiv (ha : a ≠ 0) :
    (Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R]
        →ₗ[MvPolynomial (Fin m) R ⧸ congruenceIdeal a m] traceDefect a m)
      ≃ₗ[R] Matrix (Fin m) (Fin m) (R ⧸ Ideal.span ({a} : Set R)) :=
  (LinearEquiv.ofBijective _ (solderingCoeff_bijective ha)).trans
    (LinearEquiv.piCongrRight fun _ => aMulTraceDefectEquiv ha)

end HomSpace

end HTGeometry.ConstraintRelativity

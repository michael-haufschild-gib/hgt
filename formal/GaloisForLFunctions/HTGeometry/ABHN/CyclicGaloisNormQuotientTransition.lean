import Mathlib.RingTheory.Norm.Transitivity
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2NormQuotient
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsionDirectedSystem

/-!
# Tower transitions for cyclic norm quotients

For a tower `K ⊆ L ⊆ M`, the transition from the relative norm quotient for `L/K` to
the relative norm quotient for `M/K` sends a base unit `a` to `a ^ [M : L]`.  Norm
transitivity makes this well-defined.  Under split valuation coordinates it is exactly the
canonical inclusion `ZMod [L : K] → ZMod [M : K]` induced by the common embedding in `ℚ/ℤ`.

Transport through the cyclic `H²` norm-quotient equivalence supplies a directed system on
finite cyclic unit cohomology.  These maps satisfy identity and composition, commute with the
finite local invariant isomorphisms, and are injective whenever the split valuation
classification holds.  Comparison with group-cohomological inflation remains a separate
naturality theorem.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Norm of an intermediate-field unit embedded into the top field. -/
theorem cyclicGaloisNormUnits_algebraMap_tower
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    (x : Lˣ) :
    cyclicGaloisNormUnits K M (Units.map (algebraMap L M) x) =
      (cyclicGaloisNormUnits K L x) ^ Module.finrank L M := by
  apply Units.ext
  change Algebra.norm K (algebraMap L M (x : L)) =
    Algebra.norm K (x : L) ^ Module.finrank L M
  rw [← Algebra.norm_norm (R := K) (S := L), Algebra.norm_algebraMap, map_pow]

/-- Multiplication by the relative degree carries lower norm classes into upper norm classes. -/
theorem cyclicGaloisH2BaseNormImage_finrank_nsmul_mem
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    (a : Additive Kˣ) (ha : a ∈ cyclicGaloisH2BaseNormImage K L) :
    Module.finrank L M • a ∈ cyclicGaloisH2BaseNormImage K M := by
  rcases ha with ⟨x, rfl⟩
  refine ⟨Additive.ofMul (Units.map (algebraMap L M) (Additive.toMul x)), ?_⟩
  apply Additive.toMul.injective
  change cyclicGaloisNormUnits K M
      (Units.map (algebraMap L M) (Additive.toMul x)) =
    Additive.toMul (Module.finrank L M • cyclicGaloisAdditiveNormUnits K L x)
  rw [cyclicGaloisNormUnits_algebraMap_tower]
  simp [cyclicGaloisAdditiveNormUnits]

/-- Transition between base-unit norm quotients along a scalar tower. -/
noncomputable def cyclicGaloisH2BaseNormQuotientTransition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M] :
    Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L →+
      Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M :=
  QuotientAddGroup.lift (cyclicGaloisH2BaseNormImage K L)
    ((QuotientAddGroup.mk' (cyclicGaloisH2BaseNormImage K M)).comp
      (Module.finrank L M • AddMonoidHom.id (Additive Kˣ))) (by
        intro a ha
        rw [AddMonoidHom.mem_ker]
        apply (QuotientAddGroup.eq_zero_iff _).mpr
        exact cyclicGaloisH2BaseNormImage_finrank_nsmul_mem K L M a ha)

/-- A representative is raised to the relative degree by the norm-quotient transition. -/
@[simp] theorem cyclicGaloisH2BaseNormQuotientTransition_mk
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    (a : Additive Kˣ) :
    cyclicGaloisH2BaseNormQuotientTransition K L M (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (Module.finrank L M • a) := rfl

/-- Explicit integer formula for canonical refinement between finite torsion layers. -/
theorem zmodRatModIntTransition_intCast {m n r : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hmr : m * r = n) (z : ℤ) :
    zmodRatModIntTransition hm hn ⟨r, hmr.symm⟩ (z : ZMod m) =
      (((r : ℤ) * z : ℤ) : ZMod n) := by
  apply zmodRatModIntAddHom_injective n hn
  rw [zmodRatModIntAddHom_transition]
  simp only [zmodRatModIntAddHom, ZMod.lift_coe]
  have hr : r ≠ 0 := by
    rintro rfl
    simp at hmr
    exact hn hmr.symm
  change QuotientAddGroup.mk ((z : ℚ) / (m : ℚ)) =
    QuotientAddGroup.mk ((((r : ℤ) * z : ℤ) : ℚ) / (n : ℚ))
  congr 1
  rw [← hmr]
  push_cast
  field_simp [hr]

/-- Valuation coordinates carry norm-quotient transition to canonical torsion inclusion. -/
theorem cyclicGaloisH2BaseNormQuotientTransition_tameValModNat
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ)))
    (hm : Module.finrank K L ≠ 0) (hn : Module.finrank K M ≠ 0)
    (hvalKL : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vL x) ^ Module.finrank K L)
    (hvalKM : ∀ x : Mˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vM x) ^ Module.finrank K M) :
    (cyclicGaloisH2BaseNormQuotient_tameValModNat K M vK vM
        (Module.finrank K M) hvalKM).comp
        (cyclicGaloisH2BaseNormQuotientTransition K L M) =
      (zmodRatModIntTransition hm hn
        ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩).comp
        (cyclicGaloisH2BaseNormQuotient_tameValModNat K L vK vL
          (Module.finrank K L) hvalKL) := by
  apply AddMonoidHom.ext
  intro q
  refine QuotientAddGroup.induction_on q fun a => ?_
  change tameValModNat vK (Module.finrank K M) (Module.finrank L M • a) =
    zmodRatModIntTransition hm hn
      ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩
      (tameValModNat vK (Module.finrank K L) a)
  rw [map_nsmul]
  change Module.finrank L M •
      (((Multiplicative.toAdd (tameValHom vK (Additive.toMul a)) : ℤ)) :
        ZMod (Module.finrank K M)) =
    zmodRatModIntTransition hm hn
      ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩
      (((Multiplicative.toAdd (tameValHom vK (Additive.toMul a)) : ℤ)) :
        ZMod (Module.finrank K L))
  rw [zmodRatModIntTransition_intCast hm hn (Module.finrank_mul_finrank K L M)]
  simp [nsmul_eq_mul]

/-- Identity law for norm-quotient transition. -/
theorem cyclicGaloisH2BaseNormQuotientTransition_self
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    cyclicGaloisH2BaseNormQuotientTransition K L L = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro q
  refine QuotientAddGroup.induction_on q fun a => ?_
  simp

/-- Composition law for norm-quotient transition. -/
theorem cyclicGaloisH2BaseNormQuotientTransition_comp
    (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [Algebra M N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [IsScalarTower K M N] [IsScalarTower L M N]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K N]
    [FiniteDimensional L M] [FiniteDimensional L N] [FiniteDimensional M N] :
    (cyclicGaloisH2BaseNormQuotientTransition K M N).comp
        (cyclicGaloisH2BaseNormQuotientTransition K L M) =
      cyclicGaloisH2BaseNormQuotientTransition K L N := by
  apply AddMonoidHom.ext
  intro q
  refine QuotientAddGroup.induction_on q fun a => ?_
  change QuotientAddGroup.mk (Module.finrank M N • Module.finrank L M • a) =
    QuotientAddGroup.mk (Module.finrank L N • a)
  rw [← Module.finrank_mul_finrank L M N, ← mul_nsmul]

/-- Norm-defined transition on cyclic degree-two unit cohomology. -/
noncomputable def cyclicGaloisH2NormQuotientTransition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] :
    cyclicGaloisH2 K L →+ cyclicGaloisH2 K M :=
  (cyclicGaloisH2BaseNormQuotientEquiv K M).toAddMonoidHom.comp
    ((cyclicGaloisH2BaseNormQuotientTransition K L M).comp
      (cyclicGaloisH2BaseNormQuotientEquiv K L).symm.toAddMonoidHom)

/-- On a base unit, cyclic `H²` transition multiplies by the relative degree. -/
theorem cyclicGaloisH2NormQuotientTransition_baseProjection
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] (a : Additive Kˣ) :
    cyclicGaloisH2NormQuotientTransition K L M (cyclicGaloisH2BaseProjection K L a) =
      cyclicGaloisH2BaseProjection K M (Module.finrank L M • a) := by
  have hsource :
      (cyclicGaloisH2BaseNormQuotientEquiv K L).symm
          (cyclicGaloisH2BaseProjection K L a) = QuotientAddGroup.mk a := by
    apply (cyclicGaloisH2BaseNormQuotientEquiv K L).injective
    rw [(cyclicGaloisH2BaseNormQuotientEquiv K L).apply_symm_apply]
    rfl
  change cyclicGaloisH2BaseNormQuotientEquiv K M
      (cyclicGaloisH2BaseNormQuotientTransition K L M
        ((cyclicGaloisH2BaseNormQuotientEquiv K L).symm
          (cyclicGaloisH2BaseProjection K L a))) = _
  rw [hsource]
  rfl

/-- Identity law for norm-defined cyclic `H²` transition. -/
theorem cyclicGaloisH2NormQuotientTransition_self
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    cyclicGaloisH2NormQuotientTransition K L L = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a, rfl⟩ := cyclicGaloisH2BaseProjection_surjective K L z
  rw [cyclicGaloisH2NormQuotientTransition_baseProjection]
  simp

/-- Composition law for norm-defined cyclic `H²` transition. -/
theorem cyclicGaloisH2NormQuotientTransition_comp
    (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [Algebra M N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [IsScalarTower K M N] [IsScalarTower L M N]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K N]
    [FiniteDimensional L M] [FiniteDimensional L N] [FiniteDimensional M N]
    [IsGalois K L] [IsGalois K M] [IsGalois K N]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] [IsCyclic Gal(N/K)] :
    (cyclicGaloisH2NormQuotientTransition K M N).comp
        (cyclicGaloisH2NormQuotientTransition K L M) =
      cyclicGaloisH2NormQuotientTransition K L N := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a, rfl⟩ := cyclicGaloisH2BaseProjection_surjective K L z
  rw [AddMonoidHom.comp_apply, cyclicGaloisH2NormQuotientTransition_baseProjection,
    cyclicGaloisH2NormQuotientTransition_baseProjection,
    cyclicGaloisH2NormQuotientTransition_baseProjection]
  rw [← Module.finrank_mul_finrank L M N, ← mul_nsmul]

/-- Valuation invariant on cyclic `H²`, before imposing conditions making it an equivalence. -/
noncomputable def cyclicGaloisH2TameInvariant
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ))) (n : ℕ)
    (hval : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) = (tameValHom vL x) ^ n) :
    cyclicGaloisH2 K L →+ ZMod n :=
  (cyclicGaloisH2BaseNormQuotient_tameValModNat K L vK vL n hval).comp
    (cyclicGaloisH2BaseNormQuotientEquiv K L).symm.toAddMonoidHom

/-- The cyclic `H²` tame invariant evaluates by reducing base-unit valuation. -/
theorem cyclicGaloisH2TameInvariant_baseProjection
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ))) (n : ℕ)
    (hval : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) = (tameValHom vL x) ^ n)
    (a : Additive Kˣ) :
    cyclicGaloisH2TameInvariant K L vK vL n hval (cyclicGaloisH2BaseProjection K L a) =
      tameValModNat vK n a := by
  have hsource :
      (cyclicGaloisH2BaseNormQuotientEquiv K L).symm
          (cyclicGaloisH2BaseProjection K L a) = QuotientAddGroup.mk a := by
    apply (cyclicGaloisH2BaseNormQuotientEquiv K L).injective
    rw [(cyclicGaloisH2BaseNormQuotientEquiv K L).apply_symm_apply]
    rfl
  change cyclicGaloisH2BaseNormQuotient_tameValModNat K L vK vL n hval
      ((cyclicGaloisH2BaseNormQuotientEquiv K L).symm
        (cyclicGaloisH2BaseProjection K L a)) = _
  rw [hsource]
  rfl

/-- Norm-defined cyclic `H²` transition preserves the represented `ℚ/ℤ` invariant. -/
theorem cyclicGaloisH2NormQuotientTransition_tameInvariant
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ)))
    (hm : Module.finrank K L ≠ 0) (hn : Module.finrank K M ≠ 0)
    (hvalKL : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vL x) ^ Module.finrank K L)
    (hvalKM : ∀ x : Mˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vM x) ^ Module.finrank K M) :
    (cyclicGaloisH2TameInvariant K M vK vM (Module.finrank K M) hvalKM).comp
        (cyclicGaloisH2NormQuotientTransition K L M) =
      (zmodRatModIntTransition hm hn
        ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩).comp
        (cyclicGaloisH2TameInvariant K L vK vL (Module.finrank K L) hvalKL) := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a, rfl⟩ := cyclicGaloisH2BaseProjection_surjective K L z
  rw [AddMonoidHom.comp_apply, cyclicGaloisH2NormQuotientTransition_baseProjection,
    cyclicGaloisH2TameInvariant_baseProjection]
  rw [AddMonoidHom.comp_apply, cyclicGaloisH2TameInvariant_baseProjection]
  rw [map_nsmul]
  change Module.finrank L M •
      (((Multiplicative.toAdd (tameValHom vK (Additive.toMul a)) : ℤ)) :
        ZMod (Module.finrank K M)) =
    zmodRatModIntTransition hm hn
      ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩
      (((Multiplicative.toAdd (tameValHom vK (Additive.toMul a)) : ℤ)) :
        ZMod (Module.finrank K L))
  rw [zmodRatModIntTransition_intCast hm hn (Module.finrank_mul_finrank K L M)]
  simp [nsmul_eq_mul]

/-- The tame invariant is the underlying map of the split valuation `H²` equivalence. -/
theorem cyclicGaloisH2TameInvariant_eq_splitValuationEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ))) (n : ℕ) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hfinrank : Module.finrank K L = n)
    (hval : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) = (tameValHom vL x) ^ n)
    (hzero : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a) :
    cyclicGaloisH2TameInvariant K L vK vL n hval =
      (cyclicGaloisH2SplitValuationEquiv K L vK vL n u hu hfinrank hval hzero).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a, rfl⟩ := cyclicGaloisH2BaseProjection_surjective K L z
  rw [cyclicGaloisH2TameInvariant_baseProjection]
  have hsource :
      (cyclicGaloisH2BaseNormQuotientEquiv K L).symm
          (cyclicGaloisH2BaseProjection K L a) = QuotientAddGroup.mk a := by
    apply (cyclicGaloisH2BaseNormQuotientEquiv K L).injective
    rw [(cyclicGaloisH2BaseNormQuotientEquiv K L).apply_symm_apply]
    rfl
  change tameValModNat vK n a =
    cyclicGaloisH2BaseNormQuotientSplitValuationEquiv K L vK vL n u hu hfinrank hval hzero
      ((cyclicGaloisH2BaseNormQuotientEquiv K L).symm
        (cyclicGaloisH2BaseProjection K L a))
  rw [hsource]
  rfl

/-- Split valuation `H²` isomorphisms are natural under norm-defined tower transition. -/
theorem cyclicGaloisH2SplitValuationEquiv_transition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ))) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hvalKL : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vL x) ^ Module.finrank K L)
    (hzeroKL : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a)
    (hvalKM : ∀ x : Mˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vM x) ^ Module.finrank K M)
    (hzeroKM : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Mˣ, Units.map (Algebra.norm K) b = a) :
    (cyclicGaloisH2SplitValuationEquiv K M vK vM (Module.finrank K M) u hu rfl
      hvalKM hzeroKM).toAddMonoidHom.comp (cyclicGaloisH2NormQuotientTransition K L M) =
      (zmodRatModIntTransition Module.finrank_pos.ne' Module.finrank_pos.ne'
        ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩).comp
        (cyclicGaloisH2SplitValuationEquiv K L vK vL (Module.finrank K L) u hu rfl
          hvalKL hzeroKL).toAddMonoidHom := by
  rw [← cyclicGaloisH2TameInvariant_eq_splitValuationEquiv K M vK vM
      (Module.finrank K M) u hu rfl hvalKM hzeroKM,
    ← cyclicGaloisH2TameInvariant_eq_splitValuationEquiv K L vK vL
      (Module.finrank K L) u hu rfl hvalKL hzeroKL]
  exact cyclicGaloisH2NormQuotientTransition_tameInvariant K L M vK vL vM
    Module.finrank_pos.ne' Module.finrank_pos.ne' hvalKL hvalKM

/-- Under split valuation classification, norm-defined cyclic `H²` transition is injective. -/
theorem cyclicGaloisH2NormQuotientTransition_injective_of_splitValuation
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ))) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hvalKL : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vL x) ^ Module.finrank K L)
    (hzeroKL : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a)
    (hvalKM : ∀ x : Mˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vM x) ^ Module.finrank K M)
    (hzeroKM : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Mˣ, Units.map (Algebra.norm K) b = a) :
    Function.Injective (cyclicGaloisH2NormQuotientTransition K L M) := by
  let eL := cyclicGaloisH2SplitValuationEquiv K L vK vL
    (Module.finrank K L) u hu rfl hvalKL hzeroKL
  let eM := cyclicGaloisH2SplitValuationEquiv K M vK vM
    (Module.finrank K M) u hu rfl hvalKM hzeroKM
  let t := zmodRatModIntTransition Module.finrank_pos.ne' Module.finrank_pos.ne'
    ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩
  have hnat := cyclicGaloisH2SplitValuationEquiv_transition K L M vK vL vM u hu
    hvalKL hzeroKL hvalKM hzeroKM
  intro x y hxy
  apply eL.injective
  apply zmodRatModIntTransition_injective Module.finrank_pos.ne' Module.finrank_pos.ne'
    ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩
  have hx := congrArg (fun f : cyclicGaloisH2 K L →+ ZMod (Module.finrank K M) => f x) hnat
  have hy := congrArg (fun f : cyclicGaloisH2 K L →+ ZMod (Module.finrank K M) => f y) hnat
  change eM (cyclicGaloisH2NormQuotientTransition K L M x) = t (eL x) at hx
  change eM (cyclicGaloisH2NormQuotientTransition K L M y) = t (eL y) at hy
  exact hx.symm.trans ((congrArg eM hxy).trans hy)

end

end GaloisForLFunctions.HTGeometry.ABHN

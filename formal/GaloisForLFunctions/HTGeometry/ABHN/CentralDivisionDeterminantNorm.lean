import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionSeparableSubfield
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Determinant norms on finite division algebras

The determinant norm of left multiplication on a finite division algebra restricts to a power of
the ordinary field norm on every commutative subfield.  On a finite extension of a complete
nonarchimedean field, the absolute value of the field norm is the spectral norm raised to the
extension degree.  These are the two determinant identities used in the valuation-theoretic proof
of local Brauer exhaustion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open Module IntermediateField
open scoped IsMulCommutative

universe u

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [Module.Finite K D]

/-- Restricting left multiplication to any commutative subfield inside a finite division
algebra expresses its determinant norm as a power of the subfield norm. -/
theorem divisionAlgebra_norm_eq_subalgebra_norm_pow
    (S : Subalgebra K D) (hS : IsField S) (s : S) :
    Algebra.norm K (s : D) =
      Algebra.norm K s ^ Module.finrank S D := by
  letI : Field S := hS.toField
  letI : Module S D := Module.compHom D S.subtype
  haveI towerKSD : IsScalarTower K S D := by
    constructor
    intro k a d
    simp only [Algebra.smul_def]
    change (((algebraMap K S k : S) : D) * (a : D)) * d =
      algebraMap K D k * ((a : D) * d)
    rw [show ((algebraMap K S k : S) : D) = algebraMap K D k from rfl, mul_assoc]
  haveI finiteSD : Module.Finite S D :=
    @Module.Finite.of_restrictScalars_finite K S D inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance towerKSD inferInstance
  haveI compatKSD : LinearMap.CompatibleSMul D D K S :=
    { map_smul := fun f k d ↦ by
        simp only [Algebra.smul_def]
        rw [← show ((algebraMap K S k : S) : D) = algebraMap K D k from rfl]
        change f ((algebraMap K S k) • d) = (algebraMap K S k) • f d
        exact f.map_smul _ _ }
  haveI commSD : SMulCommClass S S D :=
    { smul_comm := fun a b d ↦ by
        change (a : D) * ((b : D) * d) = (b : D) * ((a : D) * d)
        rw [← mul_assoc, ← mul_assoc]
        congr 1
        exact congrArg Subtype.val (mul_comm a b) }
  let f : D →ₗ[S] D := (LinearMap.lsmul S D) s
  have hf : f.restrictScalars K = Algebra.lmul K D (s : D) := by
    ext y
    rfl
  calc
    Algebra.norm K (s : D) = LinearMap.det (Algebra.lmul K D (s : D)) := rfl
    _ = LinearMap.det (f.restrictScalars K) := by rw [hf]
    _ = Algebra.norm K (LinearMap.det f) :=
      @LinearMap.det_restrictScalars K S D
        (inferInstance : CommRing K) (inferInstance : CommRing S)
        (inferInstance : Algebra K S) (inferInstance : Module.Free K S)
        (inferInstance : AddCommGroup D) (inferInstance : Module K D)
        (show Module S D from inferInstance) towerKSD
        (inferInstance : Module.Free S D) f
    _ = Algebra.norm K (s ^ Module.finrank S D) := by
      congr 1
      let g : D →ₗ[S] D := @DistribSMul.toLinearMap S S D
        (inferInstance : Semiring S) (inferInstance : AddCommMonoid D)
        (show Module S D from inferInstance) (inferInstance : DistribSMul S D) commSD s
      have hfg : f = g := by
        ext y
        change (s : D) * y = (s : D) * y
        rfl
      rw [hfg]
      let b := Module.Free.chooseBasis S D
      rw [← LinearMap.det_toMatrix b]
      have hmatrix : LinearMap.toMatrix b b g = Matrix.diagonal fun _ ↦ s := by
        exact toMatrix_distrib_mul_action_toLinearMap b s
      rw [hmatrix, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        ← Module.finrank_eq_card_basis b]
    _ = Algebra.norm K s ^ Module.finrank S D :=
      map_pow (Algebra.norm K) s (Module.finrank S D)

/-- The determinant norm of an element of a finite division algebra is the field norm from its
generated commutative subfield, raised to the relative module rank. -/
theorem divisionAlgebra_norm_eq_adjoin_norm_pow (x : D) :
    Algebra.norm K x =
      Algebra.norm K
        (⟨x, Algebra.self_mem_adjoin_singleton K x⟩ : Algebra.adjoin K ({x} : Set D)) ^
          Module.finrank (Algebra.adjoin K ({x} : Set D)) D := by
  exact divisionAlgebra_norm_eq_subalgebra_norm_pow
    (Algebra.adjoin K ({x} : Set D))
    (algebraAdjoinSingleton_isField_of_finiteDivisionRing K D x)
    ⟨x, Algebra.self_mem_adjoin_singleton K x⟩

variable {F L : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [Field L] [Algebra F L] [FiniteDimensional F L]

/-- Absolute value of a finite field norm equals spectral norm raised to extension degree. -/
theorem norm_algebraNorm_eq_spectralNorm_pow_finrank (x : L) :
    ‖Algebra.norm F x‖ = spectralNorm F L x ^ Module.finrank F L := by
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hnormgen :
      ‖Algebra.norm F (IntermediateField.AdjoinSimple.gen F x)‖ =
        ‖(minpoly F x).coeff 0‖ := by
    rw [← IntermediateField.adjoin.powerBasis_gen hx,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    congr 1
    exact congrArg (fun p : Polynomial F ↦ p.coeff 0) <|
      (minpoly.algebraMap_eq (algebraMap F⟮x⟯ L).injective
        (IntermediateField.AdjoinSimple.gen F x)).symm.trans <| by
          rw [IntermediateField.AdjoinSimple.algebraMap_gen]
  rw [Algebra.norm_eq_norm_adjoin F x, norm_pow, hnormgen,
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow]
  rw [← Real.rpow_natCast, ← Real.rpow_mul_natCast (norm_nonneg _)]
  congr 1
  rw [← Module.finrank_mul_finrank F F⟮x⟯ L,
    IntermediateField.adjoin.finrank hx, Nat.cast_mul]
  have hn : ((minpoly F x).natDegree : ℝ) ≠ 0 := by
    exact_mod_cast (minpoly.natDegree_pos hx).ne'
  field_simp

variable {A : Type u} [DivisionRing A] [Algebra F A] [Module.Finite F A]

/-- Unit-ball form of the ultrametric inequality for the determinant norm on a finite division
algebra.  Its proof takes place in the commutative field generated by `x`. -/
theorem divisionAlgebra_norm_one_add_le_one_of_norm_le_one (x : A)
    (hx : ‖Algebra.norm F x‖ ≤ 1) :
    ‖Algebra.norm F (1 + x)‖ ≤ 1 := by
  let S := Algebra.adjoin F ({x} : Set A)
  have hS : IsField S := algebraAdjoinSingleton_isField_of_finiteDivisionRing F A x
  letI : Field S := hS.toField
  haveI towerFSA : IsScalarTower F S A := by
    constructor
    intro k s a
    simp only [Algebra.smul_def]
    change (((algebraMap F S k : S) : A) * (s : A)) * a =
      algebraMap F A k * ((s : A) * a)
    rw [show ((algebraMap F S k : S) : A) = algebraMap F A k from rfl, mul_assoc]
  haveI finiteSA : Module.Finite S A :=
    @Module.Finite.of_restrictScalars_finite F S A inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance towerFSA inferInstance
  let sx : S := ⟨x, Algebra.self_mem_adjoin_singleton F x⟩
  have hdet (s : S) :
      ‖Algebra.norm F (s : A)‖ =
        spectralNorm F S s ^ Module.finrank F A := by
    have hfinrank : Module.finrank F S * Module.finrank S A = Module.finrank F A :=
      @Module.finrank_mul_finrank F S A
        (inferInstance : Semiring F) (inferInstance : Semiring S)
        (inferInstance : AddCommMonoid A) (inferInstance : Module F S)
        (show Module S A from inferInstance) (inferInstance : Module F A) towerFSA
        (inferInstance : StrongRankCondition F) (inferInstance : StrongRankCondition S)
        (inferInstance : Module.Free F S) (inferInstance : Module.Free S A)
    rw [divisionAlgebra_norm_eq_subalgebra_norm_pow S hS s, norm_pow,
      norm_algebraNorm_eq_spectralNorm_pow_finrank, ← pow_mul,
      hfinrank]
  have hsx : spectralNorm F S sx ≤ 1 := by
    rw [hdet sx] at hx
    apply (pow_le_pow_iff_left₀ (spectralNorm_nonneg sx) zero_le_one
      (Module.finrank_pos (R := F) (M := A)).ne').mp
    simpa only [one_pow] using hx
  have honeadd : spectralNorm F S (1 + sx) ≤ 1 := by
    calc
      spectralNorm F S (1 + sx) ≤
          spectralNorm F S 1 ⊔ spectralNorm F S sx :=
        isNonarchimedean_spectralNorm 1 sx
      _ ≤ 1 := sup_le (by rw [spectralNorm_one]) hsx
  rw [← show (((1 + sx : S) : A)) = 1 + x from rfl, hdet]
  exact pow_le_one₀ (spectralNorm_nonneg (1 + sx)) honeadd

/-- The absolute value of the determinant norm on a finite division algebra over a complete
nonarchimedean field satisfies the ultrametric inequality. -/
theorem divisionAlgebra_norm_isNonarchimedean :
    IsNonarchimedean (fun x : A ↦ ‖Algebra.norm F x‖) := by
  let f : A → ℝ := fun x ↦ ‖Algebra.norm F x‖
  have hle (a b : A) (hab : f a ≤ f b) : f (a + b) ≤ f b := by
    by_cases hb : b = 0
    · simpa [f, hb] using hab
    have hnormb : Algebra.norm F b ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb
    have hfb : f b ≠ 0 := by
      exact norm_ne_zero_iff.mpr hnormb
    have hquotient : f (b⁻¹ * a) ≤ 1 := by
      change ‖Algebra.norm F (b⁻¹ * a)‖ ≤ 1
      rw [map_mul, Algebra.norm_inv, norm_mul, norm_inv]
      calc
        ‖Algebra.norm F b‖⁻¹ * ‖Algebra.norm F a‖ ≤
            ‖Algebra.norm F b‖⁻¹ * ‖Algebra.norm F b‖ :=
          mul_le_mul_of_nonneg_left hab (inv_nonneg.mpr (norm_nonneg _))
        _ = 1 := inv_mul_cancel₀ hfb
    have honeadd : f (1 + b⁻¹ * a) ≤ 1 :=
      divisionAlgebra_norm_one_add_le_one_of_norm_le_one (b⁻¹ * a) hquotient
    have hfactor : a + b = b * (1 + b⁻¹ * a) := by
      rw [mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hb, one_mul, add_comm]
    rw [hfactor]
    change ‖Algebra.norm F (b * (1 + b⁻¹ * a))‖ ≤ ‖Algebra.norm F b‖
    rw [map_mul, norm_mul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left honeadd (norm_nonneg (Algebra.norm F b))
  intro a b
  rcases le_total (f a) (f b) with hab | hba
  · rw [sup_eq_right.mpr hab]
    exact hle a b hab
  · rw [sup_eq_left.mpr hba, add_comm]
    exact hle b a hba

omit [CompleteSpace F] [IsUltrametricDist F] [Module.Finite F A] in
/-- Negation preserves determinant size. -/
theorem divisionAlgebra_norm_norm_neg (x : A) :
    ‖Algebra.norm F (-x)‖ = ‖Algebra.norm F x‖ := by
  have hnegone : ‖Algebra.norm F (-1 : A)‖ = 1 := by
    rw [show (-1 : A) = algebraMap F A (-1) by simp, Algebra.norm_algebraMap]
    simp
  rw [show -x = (-1 : A) * x by simp, map_mul, norm_mul, hnegone, one_mul]

/-- Valuation order of a finite division algebra, defined by its determinant unit ball.  This is
the noncommutative analogue of the valuation subring attached to an absolute value. -/
noncomputable def divisionAlgebraDeterminantValuationSubring : Subring A where
  carrier := {x | ‖Algebra.norm F x‖ ≤ 1}
  zero_mem' := by simp [Algebra.norm_zero]
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact (divisionAlgebra_norm_isNonarchimedean (F := F) (A := A) x y).trans
      (sup_le hx hy)
  mul_mem' := by
    intro x y hx hy
    rw [Set.mem_setOf_eq, map_mul, norm_mul]
    simpa only [one_mul] using mul_le_mul hx hy (norm_nonneg _) zero_le_one
  neg_mem' := by
    intro x hx
    rw [Set.mem_setOf_eq, divisionAlgebra_norm_norm_neg]
    exact hx

@[simp]
theorem mem_divisionAlgebraDeterminantValuationSubring_iff (x : A) :
    x ∈ divisionAlgebraDeterminantValuationSubring (F := F) (A := A) ↔
      ‖Algebra.norm F x‖ ≤ 1 :=
  Iff.rfl

/-- Every element or its inverse belongs to the determinant valuation order. -/
theorem divisionAlgebraDeterminantValuationSubring_mem_or_inv_mem (x : A) :
    x ∈ divisionAlgebraDeterminantValuationSubring (F := F) (A := A) ∨
      x⁻¹ ∈ divisionAlgebraDeterminantValuationSubring (F := F) (A := A) := by
  by_cases hx : ‖Algebra.norm F x‖ ≤ 1
  · exact Or.inl hx
  · right
    have hxzero : x ≠ 0 := by
      intro h
      subst x
      simp [Algebra.norm_zero] at hx
    have hnormzero : Algebra.norm F x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hxzero
    rw [mem_divisionAlgebraDeterminantValuationSubring_iff, Algebra.norm_inv, norm_inv,
      inv_le_one₀ (norm_pos_iff.mpr hnormzero)]
    exact (le_of_not_ge hx)

/-- On central scalars, the determinant valuation order cuts out exactly the base unit ball. -/
theorem algebraMap_mem_divisionAlgebraDeterminantValuationSubring_iff (x : F) :
    algebraMap F A x ∈ divisionAlgebraDeterminantValuationSubring (F := F) (A := A) ↔
      ‖x‖ ≤ 1 := by
  rw [mem_divisionAlgebraDeterminantValuationSubring_iff, Algebra.norm_algebraMap, norm_pow]
  simpa only [one_pow] using
    pow_le_pow_iff_left₀ (norm_nonneg x) zero_le_one
      (Module.finrank_pos (R := F) (M := A)).ne'

/-- Strict determinant unit ball inside the determinant valuation order. -/
noncomputable def divisionAlgebraDeterminantMaximalIdeal :
    Ideal (divisionAlgebraDeterminantValuationSubring (F := F) (A := A)) where
  carrier := {x | ‖Algebra.norm F (x : A)‖ < 1}
  zero_mem' := by simp [Algebra.norm_zero]
  add_mem' := by
    intro x y hx hy
    change ‖Algebra.norm F ((x : A) + (y : A))‖ < 1
    exact (divisionAlgebra_norm_isNonarchimedean (F := F) (A := A) (x : A) (y : A)).trans_lt
      (max_lt hx hy)
  smul_mem' := by
    intro r x hx
    change ‖Algebra.norm F ((r : A) * (x : A))‖ < 1
    rw [map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right r.property (norm_nonneg _) hx

@[simp]
theorem mem_divisionAlgebraDeterminantMaximalIdeal_iff
    (x : divisionAlgebraDeterminantValuationSubring (F := F) (A := A)) :
    x ∈ divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A) ↔
      ‖Algebra.norm F (x : A)‖ < 1 :=
  Iff.rfl

/-- The strict determinant unit ball is a two-sided ideal. -/
noncomputable instance divisionAlgebraDeterminantMaximalIdeal_isTwoSided :
    (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)).IsTwoSided where
  mul_mem_of_left b ha := by
    change ‖Algebra.norm F (((↑_ : A) * (↑b : A)))‖ < 1
    rw [map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) ha b.property

/-- Units of the determinant valuation order are exactly its determinant-norm-one elements. -/
theorem divisionAlgebraDeterminantValuationSubring_isUnit_iff
    (x : divisionAlgebraDeterminantValuationSubring (F := F) (A := A)) :
    IsUnit x ↔ ‖Algebra.norm F (x : A)‖ = 1 := by
  constructor
  · intro hx
    obtain ⟨y, hxy, _⟩ := isUnit_iff_exists.mp hx
    have hprod :
        ‖Algebra.norm F (x : A)‖ * ‖Algebra.norm F (y : A)‖ = 1 := by
      have h := congrArg (fun z :
        divisionAlgebraDeterminantValuationSubring (F := F) (A := A) ↦
          ‖Algebra.norm F (z : A)‖) hxy
      change ‖Algebra.norm F ((x : A) * (y : A))‖ =
        ‖Algebra.norm F (1 : A)‖ at h
      simpa only [map_mul, norm_mul, map_one, norm_one] using h
    apply le_antisymm x.property
    apply le_of_not_gt
    intro hxlt
    have hlt :
        ‖Algebra.norm F (x : A)‖ * ‖Algebra.norm F (y : A)‖ < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hxlt y.property
    rw [hprod] at hlt
    exact lt_irrefl 1 hlt
  · intro hx
    have hxzero : (x : A) ≠ 0 := by
      intro hzero
      have : ‖Algebra.norm F (x : A)‖ = 0 := by
        rw [hzero, Algebra.norm_zero, norm_zero]
      linarith
    let y : divisionAlgebraDeterminantValuationSubring (F := F) (A := A) :=
      ⟨(x : A)⁻¹, by
        rw [mem_divisionAlgebraDeterminantValuationSubring_iff, Algebra.norm_inv,
          norm_inv, hx, inv_one]⟩
    apply isUnit_iff_exists.mpr
    exact ⟨y, Subtype.ext (mul_inv_cancel₀ hxzero),
      Subtype.ext (inv_mul_cancel₀ hxzero)⟩

/-- Determinant valuation order is a local ring. -/
noncomputable instance divisionAlgebraDeterminantValuationSubring_isLocalRing :
    IsLocalRing (divisionAlgebraDeterminantValuationSubring (F := F) (A := A)) := by
  apply IsLocalRing.of_nonunits_add
  intro x y hx hy
  rw [mem_nonunits_iff]
  rw [divisionAlgebraDeterminantValuationSubring_isUnit_iff]
  have hxlt : ‖Algebra.norm F (x : A)‖ < 1 :=
    lt_of_le_of_ne x.property fun h ↦ hx <|
      divisionAlgebraDeterminantValuationSubring_isUnit_iff x |>.mpr h
  have hylt : ‖Algebra.norm F (y : A)‖ < 1 :=
    lt_of_le_of_ne y.property fun h ↦ hy <|
      divisionAlgebraDeterminantValuationSubring_isUnit_iff y |>.mpr h
  exact ne_of_lt <|
    (divisionAlgebra_norm_isNonarchimedean (F := F) (A := A) (x : A) (y : A)).trans_lt
      (max_lt hxlt hylt)

/-- The strict determinant unit ball is a maximal left ideal of the local valuation order. -/
theorem divisionAlgebraDeterminantMaximalIdeal_isMaximal :
    (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · rw [mem_divisionAlgebraDeterminantMaximalIdeal_iff]
    simp
  · intro J x _ hx hxJ
    have hxnotlt : ¬ ‖Algebra.norm F (x : A)‖ < 1 := by
      simpa only [mem_divisionAlgebraDeterminantMaximalIdeal_iff] using hx
    have hxnorm : ‖Algebra.norm F (x : A)‖ = 1 :=
      le_antisymm x.property (le_of_not_gt hxnotlt)
    have hxunit : IsUnit x :=
      divisionAlgebraDeterminantValuationSubring_isUnit_iff x |>.mpr hxnorm
    rw [J.eq_top_of_isUnit_mem hxJ hxunit]
    exact Submodule.mem_top

noncomputable instance divisionAlgebraDeterminantMaximalIdeal_instIsMaximal :
    (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)).IsMaximal :=
  divisionAlgebraDeterminantMaximalIdeal_isMaximal (F := F) (A := A)

/-- Residue skew field of the determinant valuation order. -/
abbrev DivisionAlgebraDeterminantResidue : Type u :=
  divisionAlgebraDeterminantValuationSubring (F := F) (A := A) ⧸
    divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)

/-- Maximality and two-sidedness make the determinant residue a division ring. -/
noncomputable instance divisionAlgebraDeterminantResidue_divisionRing :
    DivisionRing (DivisionAlgebraDeterminantResidue (F := F) (A := A)) :=
  Ideal.Quotient.divisionRing
    (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A))

/-- Base valuation ring defined by the nonarchimedean norm. -/
abbrev NormValuationSubring : Type u :=
  (NormedField.valuation (K := F)).valuationSubring

/-- Central embedding of the norm valuation ring into the determinant valuation order. -/
noncomputable def normValuationSubringToDivisionAlgebraDeterminantValuationSubring :
    NormValuationSubring (F := F) →+*
      divisionAlgebraDeterminantValuationSubring (F := F) (A := A) where
  toFun x := ⟨algebraMap F A (x : F),
    algebraMap_mem_divisionAlgebraDeterminantValuationSubring_iff (F := F) (A := A) (x : F) |>.mpr
      (by exact_mod_cast x.property)⟩
  map_one' := Subtype.ext (map_one (algebraMap F A))
  map_mul' x y := Subtype.ext (map_mul (algebraMap F A) (x : F) (y : F))
  map_zero' := Subtype.ext (map_zero (algebraMap F A))
  map_add' x y := Subtype.ext (map_add (algebraMap F A) (x : F) (y : F))

@[simp]
theorem normValuationSubringToDivisionAlgebraDeterminantValuationSubring_apply
    (x : NormValuationSubring (F := F)) :
    (normValuationSubringToDivisionAlgebraDeterminantValuationSubring
      (F := F) (A := A) x : A) = algebraMap F A (x : F) :=
  rfl

omit [CompleteSpace F] [IsUltrametricDist F] in
/-- Strict scalar determinant size detects the strict base norm ball. -/
theorem divisionAlgebra_norm_algebraMap_lt_one_iff (x : F) :
    ‖Algebra.norm F (algebraMap F A x)‖ < 1 ↔ ‖x‖ < 1 := by
  rw [Algebra.norm_algebraMap, norm_pow]
  simpa only [one_pow] using
    pow_lt_pow_iff_left₀ (norm_nonneg x) zero_le_one
      (Module.finrank_pos (R := F) (M := A)).ne'

/-- Pullback of the determinant maximal ideal is exactly the base valuation maximal ideal. -/
theorem divisionAlgebraDeterminantMaximalIdeal_comap_normValuationSubring :
    Ideal.comap
        (normValuationSubringToDivisionAlgebraDeterminantValuationSubring
          (F := F) (A := A))
        (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) =
      IsLocalRing.maximalIdeal (NormValuationSubring (F := F)) := by
  ext x
  rw [Ideal.mem_comap, mem_divisionAlgebraDeterminantMaximalIdeal_iff]
  change ‖Algebra.norm F (algebraMap F A (x : F))‖ < 1 ↔
    x ∈ IsLocalRing.maximalIdeal (NormValuationSubring (F := F))
  rw [divisionAlgebra_norm_algebraMap_lt_one_iff,
    Valuation.mem_maximalIdeal_iff F (NormedField.valuation (K := F)),
    NormedField.valuation_apply]
  simpa only [coe_nnnorm] using (NNReal.coe_lt_one (r := ‖(x : F)‖₊))

/-- Residue field of the base norm valuation ring. -/
abbrev NormValuationResidue : Type u :=
  NormValuationSubring (F := F) ⧸
    IsLocalRing.maximalIdeal (NormValuationSubring (F := F))

noncomputable instance normValuationResidue_field :
    Field (NormValuationResidue (F := F)) :=
  Ideal.Quotient.field
    (IsLocalRing.maximalIdeal (NormValuationSubring (F := F)))

/-- Injective residue map from the base residue field to the determinant residue skew field. -/
noncomputable def normValuationResidueToDivisionAlgebraDeterminantResidue :
    NormValuationResidue (F := F) →+*
      DivisionAlgebraDeterminantResidue (F := F) (A := A) :=
  Ideal.quotientMap
    (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A))
    (normValuationSubringToDivisionAlgebraDeterminantValuationSubring
      (F := F) (A := A))
    (by rw [divisionAlgebraDeterminantMaximalIdeal_comap_normValuationSubring])

theorem normValuationResidueToDivisionAlgebraDeterminantResidue_injective :
    Function.Injective
      (normValuationResidueToDivisionAlgebraDeterminantResidue (F := F) (A := A)) := by
  unfold normValuationResidueToDivisionAlgebraDeterminantResidue
  apply Ideal.quotientMap_injective'
  rw [divisionAlgebraDeterminantMaximalIdeal_comap_normValuationSubring]

theorem normValuationResidueToDivisionAlgebraDeterminantResidue_commutes
    (c : NormValuationResidue (F := F))
    (x : DivisionAlgebraDeterminantResidue (F := F) (A := A)) :
    normValuationResidueToDivisionAlgebraDeterminantResidue (F := F) (A := A) c * x =
      x * normValuationResidueToDivisionAlgebraDeterminantResidue (F := F) (A := A) c := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk
      (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A))
        (normValuationSubringToDivisionAlgebraDeterminantValuationSubring
          (F := F) (A := A) c * x) =
    Ideal.Quotient.mk
      (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A))
        (x * normValuationSubringToDivisionAlgebraDeterminantValuationSubring
          (F := F) (A := A) c)
  apply congrArg (Ideal.Quotient.mk
    (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)))
  apply Subtype.ext
  exact Algebra.commutes (c : F) (x : A)

/-- The base residue field acts centrally on the determinant residue division ring. -/
noncomputable instance normValuationResidue_algebra_divisionAlgebraDeterminantResidue :
    Algebra (NormValuationResidue (F := F))
      (DivisionAlgebraDeterminantResidue (F := F) (A := A)) :=
  RingHom.toAlgebra'
    (normValuationResidueToDivisionAlgebraDeterminantResidue (F := F) (A := A))
    (normValuationResidueToDivisionAlgebraDeterminantResidue_commutes
      (F := F) (A := A))

instance normValuationResidue_faithfulSMul_divisionAlgebraDeterminantResidue :
    FaithfulSMul (NormValuationResidue (F := F))
      (DivisionAlgebraDeterminantResidue (F := F) (A := A)) := by
  apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
  exact normValuationResidueToDivisionAlgebraDeterminantResidue_injective
    (F := F) (A := A)

end

end GaloisForLFunctions.HTGeometry.ABHN

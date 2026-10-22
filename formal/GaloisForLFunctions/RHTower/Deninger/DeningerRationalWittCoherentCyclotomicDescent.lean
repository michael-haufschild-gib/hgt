import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittFiniteEvaluationBridge
import Mathlib.Algebra.Algebra.Subalgebra.Directed

/-!
# Coherent cyclotomic descent inside the rational-Witt presentation

The finite rational-Witt embeddings choose a primitive root independently at
each modulus.  This file proves that their images in the common rational-Witt
presentation nevertheless induce a strict directed system.  The induced
transition maps are injective, compose strictly, commute with the ambient
rational-Witt inclusions, and intertwine arithmetic Frobenius.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

instance deningerFiniteFrobeniusStageNonempty (p : ℕ) :
    Nonempty (DeningerFiniteFrobeniusStage p) :=
  ⟨⟨1, one_ne_zero, Nat.coprime_one_right p⟩⟩

@[simp]
theorem deningerPrimeFiniteWittRootEmbedding_nat
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (i : ℕ) :
    deningerPrimeFiniteWittRootEmbedding p s
        (Multiplicative.ofAdd (i : ZMod s.modulus)) =
      deningerPrimeFiniteWittPrimitiveRootUnit p s ^ i := by
  change
    ((((deningerPrimeFiniteWittPrimitiveRootUnit_spec p s).zmodEquivZPowers
        (i : ZMod s.modulus)).toMul :
      Subgroup.zpowers (deningerPrimeFiniteWittPrimitiveRootUnit p s)) :
        (DeningerPrimeArithmeticClosure p)ˣ) =
      deningerPrimeFiniteWittPrimitiveRootUnit p s ^ i
  rw [IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat]
  rfl

/-- Divisibility of stages induces inclusion of their root images in the
common arithmetic closure. -/
theorem deningerPrimeFiniteWittRootEmbedding_range_mono
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    (deningerPrimeFiniteWittRootEmbedding p s).range ≤
      (deningerPrimeFiniteWittRootEmbedding p t).range := by
  rintro x ⟨j, rfl⟩
  have hjpow :
      j ^ s.modulus = (1 : Multiplicative (ZMod s.modulus)) := by
    rw [← ofAdd_toAdd j,
      ← ofAdd_nsmul,
      ZModModule.char_nsmul_eq_zero]
    rfl
  have hxpow_s :
      (deningerPrimeFiniteWittRootEmbedding p s j) ^ s.modulus = 1 := by
    rw [← map_pow, hjpow, map_one]
  obtain ⟨k, hk⟩ := hst
  have hxpow_t :
      (deningerPrimeFiniteWittRootEmbedding p s j) ^ t.modulus = 1 := by
    calc
      (deningerPrimeFiniteWittRootEmbedding p s j) ^ t.modulus =
          (deningerPrimeFiniteWittRootEmbedding p s j) ^
            (s.modulus * k) :=
        congrArg
          (fun n : ℕ =>
            (deningerPrimeFiniteWittRootEmbedding p s j) ^ n) hk
      _ = ((deningerPrimeFiniteWittRootEmbedding p s j) ^
          s.modulus) ^ k := pow_mul _ _ _
      _ = 1 := by rw [hxpow_s, one_pow]
  have hxpow_t_val :
      (((deningerPrimeFiniteWittRootEmbedding p s j :
          (DeningerPrimeArithmeticClosure p)ˣ) :
        DeningerPrimeArithmeticClosure p) ^ t.modulus) = 1 := by
    exact congrArg Units.val hxpow_t
  obtain ⟨i, _hi, heq⟩ :=
    (deningerPrimeFiniteWittPrimitiveRoot_spec p t).eq_pow_of_pow_eq_one
      hxpow_t_val
  refine ⟨Multiplicative.ofAdd (i : ZMod t.modulus), ?_⟩
  apply Units.ext
  rw [deningerPrimeFiniteWittRootEmbedding_nat, ← heq]
  rfl

/-- A chosen root embedding is a multiplicative equivalence onto its range. -/
noncomputable def deningerPrimeFiniteWittRootEmbeddingRangeEquiv
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Multiplicative (ZMod s.modulus) ≃*
      (deningerPrimeFiniteWittRootEmbedding p s).range :=
  MulEquiv.ofBijective
    (deningerPrimeFiniteWittRootEmbedding p s).rangeRestrict
    ⟨(MonoidHom.rangeRestrict_injective_iff.mpr
        (deningerPrimeFiniteWittRootEmbedding_injective p s)),
      MonoidHom.rangeRestrict_surjective _⟩

/-- Unique transition induced by two finite root embeddings in the common
rational-Witt presentation. -/
noncomputable def deningerPrimeFiniteWittRootTransition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    Multiplicative (ZMod s.modulus) →*
      Multiplicative (ZMod t.modulus) :=
  (deningerPrimeFiniteWittRootEmbeddingRangeEquiv p t).symm.toMonoidHom.comp
    ((Subgroup.inclusion
      (deningerPrimeFiniteWittRootEmbedding_range_mono p hst)).comp
      (deningerPrimeFiniteWittRootEmbeddingRangeEquiv p s).toMonoidHom)

theorem deningerPrimeFiniteWittRootTransition_spec
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (j : Multiplicative (ZMod s.modulus)) :
    deningerPrimeFiniteWittRootEmbedding p t
        (deningerPrimeFiniteWittRootTransition p hst j) =
      deningerPrimeFiniteWittRootEmbedding p s j := by
  change
    (((deningerPrimeFiniteWittRootEmbeddingRangeEquiv p t)
      ((deningerPrimeFiniteWittRootEmbeddingRangeEquiv p t).symm
        ((Subgroup.inclusion
            (deningerPrimeFiniteWittRootEmbedding_range_mono p hst))
          (deningerPrimeFiniteWittRootEmbeddingRangeEquiv p s j))) :
        (deningerPrimeFiniteWittRootEmbedding p t).range) :
      (DeningerPrimeArithmeticClosure p)ˣ) =
    deningerPrimeFiniteWittRootEmbedding p s j
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem deningerPrimeFiniteWittRootTransition_injective
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    Function.Injective (deningerPrimeFiniteWittRootTransition p hst) := by
  intro i j hij
  apply deningerPrimeFiniteWittRootEmbedding_injective p s
  rw [← deningerPrimeFiniteWittRootTransition_spec p hst i,
    ← deningerPrimeFiniteWittRootTransition_spec p hst j, hij]

/-- The transition is uniquely forced by its triangle in the common
rational-Witt root presentation. -/
theorem deningerPrimeFiniteWittRootTransition_unique
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (f : Multiplicative (ZMod s.modulus) →*
      Multiplicative (ZMod t.modulus))
    (hf : ∀ j,
      deningerPrimeFiniteWittRootEmbedding p t (f j) =
        deningerPrimeFiniteWittRootEmbedding p s j) :
    f = deningerPrimeFiniteWittRootTransition p hst := by
  apply MonoidHom.ext
  intro j
  apply deningerPrimeFiniteWittRootEmbedding_injective p t
  rw [hf, deningerPrimeFiniteWittRootTransition_spec]

theorem deningerPrimeFiniteWittRootTransition_refl
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    deningerPrimeFiniteWittRootTransition p (le_refl s) =
      MonoidHom.id _ := by
  apply MonoidHom.ext
  intro j
  apply deningerPrimeFiniteWittRootEmbedding_injective p s
  rw [deningerPrimeFiniteWittRootTransition_spec]
  rfl

theorem deningerPrimeFiniteWittRootTransition_comp
    (p : Nat.Primes)
    {r s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hrs : r ≤ s)
    (hst : s ≤ t) :
    (deningerPrimeFiniteWittRootTransition p hst).comp
        (deningerPrimeFiniteWittRootTransition p hrs) =
      deningerPrimeFiniteWittRootTransition p (hrs.trans hst) := by
  apply MonoidHom.ext
  intro j
  apply deningerPrimeFiniteWittRootEmbedding_injective p t
  rw [MonoidHom.comp_apply,
    deningerPrimeFiniteWittRootTransition_spec p hst,
    deningerPrimeFiniteWittRootTransition_spec p hrs,
    deningerPrimeFiniteWittRootTransition_spec p (hrs.trans hst)]

/-- Additive index form of the coherent root transition. -/
noncomputable def deningerPrimeFiniteWittIndexTransition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    ZMod s.modulus →+ ZMod t.modulus where
  toFun j :=
    (deningerPrimeFiniteWittRootTransition p hst
      (Multiplicative.ofAdd j)).toAdd
  map_zero' := by
    have h := map_one (deningerPrimeFiniteWittRootTransition p hst)
    exact congrArg Multiplicative.toAdd h
  map_add' a b := by
    have h :=
      map_mul (deningerPrimeFiniteWittRootTransition p hst)
        (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
    exact congrArg Multiplicative.toAdd h

@[simp]
theorem deningerPrimeFiniteWittIndexTransition_apply
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (j : ZMod s.modulus) :
    Multiplicative.ofAdd (deningerPrimeFiniteWittIndexTransition p hst j) =
      deningerPrimeFiniteWittRootTransition p hst
        (Multiplicative.ofAdd j) := by
  exact ofAdd_toAdd _

theorem deningerPrimeFiniteWittIndexTransition_injective
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    Function.Injective (deningerPrimeFiniteWittIndexTransition p hst) := by
  intro i j hij
  have hmul :
      deningerPrimeFiniteWittRootTransition p hst
          (Multiplicative.ofAdd i) =
        deningerPrimeFiniteWittRootTransition p hst
          (Multiplicative.ofAdd j) := by
    rw [← deningerPrimeFiniteWittIndexTransition_apply,
      ← deningerPrimeFiniteWittIndexTransition_apply, hij]
  have hpre :=
    deningerPrimeFiniteWittRootTransition_injective p hst hmul
  simpa using congrArg Multiplicative.toAdd hpre

theorem deningerPrimeFiniteWittIndexTransition_refl
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    deningerPrimeFiniteWittIndexTransition p (le_refl s) =
      AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro j
  have h := DFunLike.congr_fun
    (deningerPrimeFiniteWittRootTransition_refl p s)
    (Multiplicative.ofAdd j)
  simpa [deningerPrimeFiniteWittIndexTransition] using
    congrArg Multiplicative.toAdd h

theorem deningerPrimeFiniteWittIndexTransition_comp
    (p : Nat.Primes)
    {r s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hrs : r ≤ s)
    (hst : s ≤ t) :
    (deningerPrimeFiniteWittIndexTransition p hst).comp
        (deningerPrimeFiniteWittIndexTransition p hrs) =
      deningerPrimeFiniteWittIndexTransition p (hrs.trans hst) := by
  apply AddMonoidHom.ext
  intro j
  have h := DFunLike.congr_fun
    (deningerPrimeFiniteWittRootTransition_comp p hrs hst)
    (Multiplicative.ofAdd j)
  simpa [deningerPrimeFiniteWittIndexTransition,
    AddMonoidHom.comp_apply] using
    congrArg Multiplicative.toAdd h

/-- Arithmetic Frobenius on finite indices is natural under the coherent
transition. -/
theorem deningerPrimeFiniteWittIndexTransition_frobenius
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (j : ZMod s.modulus) :
    deningerPrimeFiniteWittIndexTransition p hst
        (j * (ZMod.unitOfCoprime
          (p : ℕ) s.coprime : ZMod s.modulus)) =
      deningerPrimeFiniteWittIndexTransition p hst j *
        (ZMod.unitOfCoprime
          (p : ℕ) t.coprime : ZMod t.modulus) := by
  simp only [ZMod.unitOfCoprime]
  rw [mul_comm j, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, mul_comm]

/-- Coherent transition between finite cyclotomic rational-Witt algebras. -/
noncomputable def deningerPrimeFiniteCyclotomicWittTransition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    DeningerFiniteCyclotomicWittAlgebra s.modulus →ₐ[ℂ]
      DeningerFiniteCyclotomicWittAlgebra t.modulus :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ
    (deningerPrimeFiniteWittIndexTransition p hst)

@[simp]
theorem deningerPrimeFiniteCyclotomicWittTransition_single
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (j : ZMod s.modulus)
    (c : ℂ) :
    deningerPrimeFiniteCyclotomicWittTransition p hst
        (AddMonoidAlgebra.single j c) =
      AddMonoidAlgebra.single
        (deningerPrimeFiniteWittIndexTransition p hst j) c := by
  simp [deningerPrimeFiniteCyclotomicWittTransition]

theorem deningerPrimeFiniteCyclotomicWittTransition_injective
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    Function.Injective
      (deningerPrimeFiniteCyclotomicWittTransition p hst) := by
  change Function.Injective
    (AddMonoidAlgebra.mapDomain
      (deningerPrimeFiniteWittIndexTransition p hst))
  exact AddMonoidAlgebra.mapDomain_injective
    (deningerPrimeFiniteWittIndexTransition_injective p hst)

theorem deningerPrimeFiniteCyclotomicWittTransition_refl
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    deningerPrimeFiniteCyclotomicWittTransition p (le_refl s) =
      AlgHom.id ℂ _ := by
  simp [deningerPrimeFiniteCyclotomicWittTransition,
    deningerPrimeFiniteWittIndexTransition_refl]

theorem deningerPrimeFiniteCyclotomicWittTransition_comp
    (p : Nat.Primes)
    {r s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hrs : r ≤ s)
    (hst : s ≤ t) :
    (deningerPrimeFiniteCyclotomicWittTransition p hst).comp
        (deningerPrimeFiniteCyclotomicWittTransition p hrs) =
      deningerPrimeFiniteCyclotomicWittTransition p
        (hrs.trans hst) := by
  rw [deningerPrimeFiniteCyclotomicWittTransition,
    deningerPrimeFiniteCyclotomicWittTransition,
    deningerPrimeFiniteCyclotomicWittTransition,
    ← AddMonoidAlgebra.mapDomainAlgHom_comp,
    deningerPrimeFiniteWittIndexTransition_comp]

/-- Stage transition intertwines finite arithmetic Frobenius. -/
theorem deningerPrimeFiniteCyclotomicWittTransition_frobenius
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (w : DeningerFiniteCyclotomicWittAlgebra s.modulus) :
    deningerPrimeFiniteCyclotomicWittTransition p hst
        (deningerFiniteCyclotomicWittFrobenius
          (p : ℕ) s.modulus s.coprime w) =
      deningerFiniteCyclotomicWittFrobenius
          (p : ℕ) t.modulus t.coprime
        (deningerPrimeFiniteCyclotomicWittTransition p hst w) := by
  have h :
      ((deningerPrimeFiniteCyclotomicWittTransition p hst).comp
        (deningerFiniteCyclotomicWittFrobenius
          (p : ℕ) s.modulus s.coprime).toAlgHom).toLinearMap.toAddMonoidHom =
      ((deningerFiniteCyclotomicWittFrobenius
          (p : ℕ) t.modulus t.coprime).toAlgHom.comp
        (deningerPrimeFiniteCyclotomicWittTransition p hst)).toLinearMap.toAddMonoidHom := by
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro j c
    change
      deningerPrimeFiniteCyclotomicWittTransition p hst
          (deningerFiniteCyclotomicWittFrobenius
            (p : ℕ) s.modulus s.coprime
            (AddMonoidAlgebra.single j c)) =
        deningerFiniteCyclotomicWittFrobenius
            (p : ℕ) t.modulus t.coprime
          (deningerPrimeFiniteCyclotomicWittTransition p hst
            (AddMonoidAlgebra.single j c))
    rw [deningerFiniteCyclotomicWittFrobenius_single,
      deningerPrimeFiniteCyclotomicWittTransition_single,
      deningerPrimeFiniteCyclotomicWittTransition_single,
      deningerFiniteCyclotomicWittFrobenius_single,
      deningerPrimeFiniteWittIndexTransition_frobenius]
  exact DFunLike.congr_fun h w

theorem deningerPrimeFiniteCyclotomicWittTransition_preserves_frobenius_fixed
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (w : DeningerFiniteCyclotomicWittAlgebra s.modulus)
    (hw :
      deningerFiniteCyclotomicWittFrobenius
        (p : ℕ) s.modulus s.coprime w = w) :
    deningerFiniteCyclotomicWittFrobenius
        (p : ℕ) t.modulus t.coprime
        (deningerPrimeFiniteCyclotomicWittTransition p hst w) =
      deningerPrimeFiniteCyclotomicWittTransition p hst w := by
  rw [← deningerPrimeFiniteCyclotomicWittTransition_frobenius, hw]

/-- The coherent transition commutes with the inclusions in the common
rational-Witt presentation. -/
theorem deningerPrimeFiniteCyclotomicWittInclusion_transition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    (deningerPrimeFiniteCyclotomicWittInclusion p t).comp
        (deningerPrimeFiniteCyclotomicWittTransition p hst) =
      deningerPrimeFiniteCyclotomicWittInclusion p s := by
  apply DFunLike.ext _ _
  intro w
  have h :
      ((deningerPrimeFiniteCyclotomicWittInclusion p t).comp
        (deningerPrimeFiniteCyclotomicWittTransition p hst)).toLinearMap.toAddMonoidHom =
      (deningerPrimeFiniteCyclotomicWittInclusion p s).toLinearMap.toAddMonoidHom := by
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro j c
    change
      deningerPrimeFiniteCyclotomicWittInclusion p t
          (deningerPrimeFiniteCyclotomicWittTransition p hst
            (AddMonoidAlgebra.single j c)) =
        deningerPrimeFiniteCyclotomicWittInclusion p s
          (AddMonoidAlgebra.single j c)
    rw [deningerPrimeFiniteCyclotomicWittTransition_single,
      deningerPrimeFiniteCyclotomicWittInclusion_single,
      deningerPrimeFiniteCyclotomicWittInclusion_single]
    congr 1
    exact deningerPrimeFiniteWittRootTransition_spec p hst
      (Multiplicative.ofAdd j)
  exact DFunLike.congr_fun h w

/-- The algebra transition is uniquely forced by its inclusion triangle. -/
theorem deningerPrimeFiniteCyclotomicWittTransition_unique
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t)
    (T : DeningerFiniteCyclotomicWittAlgebra s.modulus →ₐ[ℂ]
      DeningerFiniteCyclotomicWittAlgebra t.modulus)
    (hT :
      (deningerPrimeFiniteCyclotomicWittInclusion p t).comp T =
        deningerPrimeFiniteCyclotomicWittInclusion p s) :
    T = deningerPrimeFiniteCyclotomicWittTransition p hst := by
  apply DFunLike.ext _ _
  intro w
  apply deningerPrimeFiniteCyclotomicWittInclusion_injective p t
  calc
    deningerPrimeFiniteCyclotomicWittInclusion p t (T w) =
        deningerPrimeFiniteCyclotomicWittInclusion p s w :=
      DFunLike.congr_fun hT w
    _ = deningerPrimeFiniteCyclotomicWittInclusion p t
          (deningerPrimeFiniteCyclotomicWittTransition p hst w) :=
      (DFunLike.congr_fun
        (deningerPrimeFiniteCyclotomicWittInclusion_transition p hst)
        w).symm

/-- Image of one finite cyclotomic stage in the common rational-Witt
presentation. -/
noncomputable def deningerPrimeFiniteCyclotomicWittStageImage
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Subalgebra ℂ (DeningerPrimeComplexifiedRationalWittPresentation p) :=
  (deningerPrimeFiniteCyclotomicWittInclusion p s).range

theorem deningerPrimeFiniteCyclotomicWittStageImage_mono
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t) :
    deningerPrimeFiniteCyclotomicWittStageImage p s ≤
      deningerPrimeFiniteCyclotomicWittStageImage p t := by
  rintro x ⟨w, rfl⟩
  refine ⟨deningerPrimeFiniteCyclotomicWittTransition p hst w, ?_⟩
  exact DFunLike.congr_fun
    (deningerPrimeFiniteCyclotomicWittInclusion_transition p hst) w

theorem deningerPrimeFiniteCyclotomicWittStageImage_directed
    (p : Nat.Primes) :
    Directed (· ≤ ·)
      (deningerPrimeFiniteCyclotomicWittStageImage p) := by
  intro s t
  obtain ⟨u, hsu, htu⟩ := exists_ge_ge s t
  exact
    ⟨u,
      deningerPrimeFiniteCyclotomicWittStageImage_mono p hsu,
      deningerPrimeFiniteCyclotomicWittStageImage_mono p htu⟩

/-- Actual finite-cyclotomic source subalgebra inside Deninger's common
complexified rational-Witt presentation. -/
noncomputable def deningerPrimeFiniteCyclotomicWittSource
    (p : Nat.Primes) :
    Subalgebra ℂ (DeningerPrimeComplexifiedRationalWittPresentation p) :=
  ⨆ s, deningerPrimeFiniteCyclotomicWittStageImage p s

/-- The finite source is literally the filtered union of stage images; its
supremum introduces no additional algebraic elements. -/
theorem deningerPrimeFiniteCyclotomicWittSource_mem_iff
    (p : Nat.Primes)
    (x : DeningerPrimeComplexifiedRationalWittPresentation p) :
    x ∈ deningerPrimeFiniteCyclotomicWittSource p ↔
      ∃ s, x ∈ deningerPrimeFiniteCyclotomicWittStageImage p s := by
  change
    x ∈ (⨆ s, deningerPrimeFiniteCyclotomicWittStageImage p s) ↔ _
  rw [← SetLike.mem_coe,
    Subalgebra.coe_iSup_of_directed
      (deningerPrimeFiniteCyclotomicWittStageImage_directed p)]
  simp

end
end RHTower

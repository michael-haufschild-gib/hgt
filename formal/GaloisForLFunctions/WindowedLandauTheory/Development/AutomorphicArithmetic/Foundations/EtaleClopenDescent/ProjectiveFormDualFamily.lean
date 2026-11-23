import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LocalizedFormDualFamily
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteNormalizationProjective
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedIntersectionLocalization

/-! Regular forms on a normalized projective intersection have finite
dual families over the field of projective coordinates. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology nonZeroDivisors

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

omit [CharZero k] [IsScalarTower k F E] in
private theorem exists_formDualFamily_subalgebra
    (A : Subalgebra k F) (B : Subalgebra k E)
    [Algebra A B] [IsScalarTower A B E] [IsFractionRing A F]
    [Module.Finite A B] [Module.Projective A B] [Algebra.Smooth k B]
    [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) E] (p : ℕ) :
    ∃ (n : ℕ) (v : Fin n → ExteriorDifferentials k E p)
      (φ : Fin n → ExteriorDifferentials k E p →ₗ[F] F),
      (∀ j, (v j : DR k E) ∈ omB k E B p) ∧
      (∀ j (w : ExteriorDifferentials k E p), (w : DR k E) ∈ omB k E B p → φ j w ∈ A) ∧
      (∀ w, w = ∑ j, φ j w • v j) := by
  obtain ⟨n, v, φ, hφ, hsum⟩ :=
    exists_localized_form_dual_family (k := k) (A := A) (B := B) (F := F) (E := E) p
  let u := algebraFormPullback k B E p
  refine ⟨n, fun j => u (v j), φ, ?_, ?_, hsum⟩
  · intro j
    exact (mem_omB_iff_pullback_range B (u (v j))).mpr ⟨v j, rfl⟩
  · intro j w hw
    obtain ⟨z, hz⟩ := (mem_omB_iff_pullback_range B w).mp hw
    have hmem := hφ j z
    change φ j (u z) ∈ (algebraMap A F).range at hmem
    rw [hz] at hmem
    obtain ⟨a, ha⟩ := hmem
    exact ha ▸ a.property

omit [CharZero k] in
/-- Projective regular forms on a chart have a finite dual family whose
coordinate functionals take chart values on regular forms. -/
theorem IsFinCover.exists_formDualFamily_chart (h : IsFinCover k E x) (i : Fin (d + 1)) (p : ℕ) :
    ∃ (n : ℕ) (v : Fin n → ExteriorDifferentials k E p)
      (φ : Fin n → ExteriorDifferentials k E p →ₗ[F] F),
      (∀ j, (v j : DR k E) ∈ omB k E (rB k E x {i}) p) ∧
      (∀ j (w : ExteriorDifferentials k E p),
        (w : DR k E) ∈ omB k E (rB k E x {i}) p → φ j w ∈ rA k x {i}) ∧
      (∀ w, w = ∑ j, φ j w • v j) := by
  let A := rA k x (Singleton.singleton i)
  let B := rB k E x (Singleton.singleton i)
  letI : IsFractionRing A F := h.pd.isFractionRing_rA i
  letI := h.fin
  letI : Algebra A B := (integralClosure A E).algebra
  letI : IsScalarTower A B E := .of_algebraMap_eq fun _ => rfl
  letI : IsIntegralClosure B A E := inferInstanceAs (IsIntegralClosure (integralClosure A E) A E)
  letI : Module.Finite A B := (h.finiteProjective_chart i).1
  letI : Module.Projective A B := (h.finiteProjective_chart i).2
  letI : Algebra.Smooth k B := h.smooth i
  letI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) E :=
    IsIntegralClosure.isLocalization A F E B
  exact exists_formDualFamily_subalgebra A B p

omit [CharZero k] [IsScalarTower k F E] in
private theorem coordinates_mem_after_inverting {A C : Subalgebra k F}
    (hAC : A ≤ C) {P Q : Submodule k (DR k E)} {p : ℕ}
    (u : F) {v : F} (hv : v ∈ C) (huv : u * v = 1)
    (hQ : ∀ w : ExteriorDifferentials k E p, (w : DR k E) ∈ Q →
      ∃ N : ℕ, ((u ^ N • w : ExteriorDifferentials k E p) : DR k E) ∈ P)
    (φ : ExteriorDifferentials k E p →ₗ[F] F)
    (hφ : ∀ w : ExteriorDifferentials k E p, (w : DR k E) ∈ P → φ w ∈ A)
    (w : ExteriorDifferentials k E p) (hw : (w : DR k E) ∈ Q) : φ w ∈ C := by
  obtain ⟨N, hN⟩ := hQ w hw
  have hm := hφ (u ^ N • w) hN
  rw [map_smul, smul_eq_mul] at hm
  have he : v ^ N * (u ^ N * φ w) = φ w := by
    rw [← mul_assoc, ← mul_pow, mul_comm v, huv, one_pow, one_mul]
  exact he ▸ C.mul_mem (C.pow_mem hv N) (hAC hm)

omit [CharZero k] in
private theorem exists_chartDenominator_inverse (h : IsPd k x)
    (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) :
    ∃ v : F, v ∈ rA k x I ∧ (chartDenominator k x I i : F) * v = 1 := by
  refine ⟨∏ l ∈ I, x i / x l, Subalgebra.prod_mem _ fun l hl =>
    Algebra.subset_adjoin ⟨l, hl, i, rfl⟩, ?_⟩
  change (∏ l ∈ I, x l / x i) * (∏ l ∈ I, x i / x l) = 1
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun l _ => by
    rw [div_mul_div_cancel₀ (h.ne i), div_self (h.ne l)]

omit [CharZero k] in
private theorem exists_chartForm_denominator (h : IsPd k x)
    {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) {p : ℕ}
    (w : ExteriorDifferentials k E p) (hw : (w : DR k E) ∈ omB k E (rB k E x I) p) :
    ∃ N : ℕ, ((((chartDenominator k x I i : F) ^ N • w) :
      ExteriorDifferentials k E p) : DR k E) ∈ omB k E (rB k E x {i}) p := by
  obtain ⟨N, hN⟩ := (mem_omB_chartIntersection_iff (E := E) h hi w).mp hw
  refine ⟨N, ?_⟩
  change algebraMap F E ((chartDenominator k x I i : F) ^ N) •
    (w : DR k E) ∈ omB k E (rB k E x {i}) p
  simpa only [map_pow] using hN

/-- The dual family on any chart in the intersection remains integral
on the intersection after inverting its coordinate denominator. -/
theorem IsFinCover.exists_formDualFamily_intersection (h : IsFinCover k E x)
    {I : Finset (Fin (d + 1))} (hI : I.Nonempty) (p : ℕ) :
    ∃ (n : ℕ) (v : Fin n → ExteriorDifferentials k E p)
      (φ : Fin n → ExteriorDifferentials k E p →ₗ[F] F),
      (∀ j, (v j : DR k E) ∈ omB k E (rB k E x I) p) ∧
      (∀ j (w : ExteriorDifferentials k E p),
        (w : DR k E) ∈ omB k E (rB k E x I) p → φ j w ∈ rA k x I) ∧
      (∀ w, w = ∑ j, φ j w • v j) := by
  obtain ⟨i, hi⟩ := hI
  obtain ⟨n, v, φ, hv, hφ, hsum⟩ := h.exists_formDualFamily_chart i p
  have hle : (Singleton.singleton i : Finset (Fin (d + 1))) ⊆ I :=
    Finset.singleton_subset_iff.mpr hi
  have hv' (j : Fin n) : (v j : DR k E) ∈ omB k E (rB k E x I) p :=
    (mem_omB_chartIntersection_iff (E := E) h.pd hi (v j)).mpr
      ⟨0, by simpa only [pow_zero, one_smul] using hv j⟩
  obtain ⟨t, ht, hut⟩ := exists_chartDenominator_inverse h.pd I i
  have hden := exists_chartForm_denominator (E := E) h.pd hi (p := p)
  exact ⟨n, v, φ, hv', fun j =>
    coordinates_mem_after_inverting (rA_mono hle) _ ht hut hden (φ j) (hφ j), hsum⟩

end GlobalTheory.PD

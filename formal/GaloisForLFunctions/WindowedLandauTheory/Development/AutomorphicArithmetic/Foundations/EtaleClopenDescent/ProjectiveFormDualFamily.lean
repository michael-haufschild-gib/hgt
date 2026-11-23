import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LocalizedFormDualFamily
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveCupResidue
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

/-- Projective regular forms on a chart have a finite dual family whose
coordinate functionals take chart values on regular forms. -/
theorem IsFinCover.exists_formDualFamily_chart (h : IsFinCover k E x) (i : Fin (d + 1)) (p : ℕ) :
    ∃ (n : ℕ) (v : Fin n → ExteriorDifferentials k E p)
      (φ : Fin n → ExteriorDifferentials k E p →ₗ[F] F),
      (∀ j, (v j : DR k E) ∈ omB k E (rB k E x {i}) p) ∧
      (∀ j w, (w : DR k E) ∈ omB k E (rB k E x {i}) p → φ j w ∈ rA k x {i}) ∧
      (∀ w, w = ∑ j, φ j w • v j) := by
  let A := rA k x (Singleton.singleton i)
  let B := rB k E x (Singleton.singleton i)
  letI : IsFractionRing A F := h.pd.isFractionRing_rA i
  letI := h.fin
  letI : Module.Finite A B := (h.finiteProjective_chart i).1
  letI : Module.Projective A B := (h.finiteProjective_chart i).2
  letI : Algebra.Smooth k B := h.smooth i
  letI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) E :=
    IsIntegralClosure.isLocalization A F E B
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
    exact (mem_algebraMap_range_subalgebra A _).mp hmem

/-- The dual family on any chart in the intersection remains integral
on the intersection after inverting its coordinate denominator. -/
theorem IsFinCover.exists_formDualFamily_intersection (h : IsFinCover k E x)
    {I : Finset (Fin (d + 1))} (hI : I.Nonempty) (p : ℕ) :
    ∃ (n : ℕ) (v : Fin n → ExteriorDifferentials k E p)
      (φ : Fin n → ExteriorDifferentials k E p →ₗ[F] F),
      (∀ j, (v j : DR k E) ∈ omB k E (rB k E x I) p) ∧
      (∀ j w, (w : DR k E) ∈ omB k E (rB k E x I) p → φ j w ∈ rA k x I) ∧
      (∀ w, w = ∑ j, φ j w • v j) := by
  obtain ⟨i, hi⟩ := hI
  obtain ⟨n, v, φ, hv, hφ, hsum⟩ := h.exists_formDualFamily_chart i p
  have hle : (Singleton.singleton i : Finset (Fin (d + 1))) ⊆ I :=
    Finset.singleton_subset_iff.mpr hi
  refine ⟨n, v, φ, fun j => omB_mono (rB_mono hle) p (hv j), ?_, hsum⟩
  intro j w hw
  let A := rA k x (Singleton.singleton i)
  let C := rA k x I
  let u := chartDenominator k x I i
  letI : Algebra A C := chartIntersectionAlgebra (k := k) (x := x) hi
  letI : IsLocalization.Away u C := chartIntersection_isLocalization h.pd hi
  obtain ⟨N, hN⟩ := (mem_omB_chartIntersection_iff (E := E) h.pd hi w).mp hw
  have h₀ : (((u : F) ^ N • w : ExteriorDifferentials k E p) : DR k E) ∈
      omB k E (rB k E x {i}) p := by
    change (algebraMap F E ((u : F) ^ N) • (w : DR k E)) ∈ _
    simpa only [map_pow] using hN
  have h₁ := hφ j ((u : F) ^ N • w) h₀
  rw [map_smul, smul_eq_mul] at h₁
  have hu : IsUnit (algebraMap A C u) :=
    IsLocalization.map_units C (⟨u, ⟨1, pow_one _⟩⟩ : Submonoid.powers u)
  obtain ⟨v₀, hv₀⟩ := isUnit_iff_exists_inv.mp hu
  have he : (u : F) * (v₀ : F) = 1 := congrArg Subtype.val hv₀
  have hmul : φ j w = (v₀ : F) ^ N * ((u : F) ^ N * φ j w) := by
    rw [← mul_assoc, ← mul_pow, mul_comm (v₀ : F), he, one_pow, one_mul]
  rw [hmul]
  exact C.mul_mem (C.pow_mem v₀.property N) (rA_mono hle h₁)

end GlobalTheory.PD

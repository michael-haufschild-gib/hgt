import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedDehomogenization
import Mathlib.RingTheory.QuotSMulTop

/-! Finite sets of generators after dehomogenization give a single homogeneous family
whose span agrees with the module after inverting any of the variables. -/

open DirectSum MvPolynomial
open scoped Pointwise

namespace GlobalTheory

/-- If a graded submodule surjects after setting a coordinate equal to one, it
contains a multiple by a power of that coordinate of every element. -/
theorem powers_mem_of_surjective_specialization {ι R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    (D : ℤ → Submodule R M) [PolyGradedSMul ι D] [Decomposition D]
    {N : Submodule (MvPolynomial ι R) M} (hN : N.IsHomogeneous D) (i : ι)
    (hfull : let J : Submodule (MvPolynomial ι R) M := (X i - 1 : MvPolynomial ι R) • ⊤
      N.map J.mkQ = ⊤) :
    ∀ y : M, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ N := by
  let S := MvPolynomial ι R
  let J : Submodule S M := (X i - 1 : S) • ⊤
  change N.map J.mkQ = ⊤ at hfull
  letI := grQuotDecomposition hN
  have hmultiple (y : M) : ∃ w : M, N.mkQ y = (X i - 1 : S) • N.mkQ w := by
    have hy : J.mkQ y ∈ N.map J.mkQ := by
      rw [hfull]
      exact Submodule.mem_top
    obtain ⟨v, hv, hvy⟩ := Submodule.mem_map.1 hy
    have hyv : y - v ∈ J := (Submodule.Quotient.eq J).1 hvy.symm
    obtain ⟨w, _, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hyv
    have h : y = v + (X i - 1 : S) • w := by rw [hw]; abel
    have hv₀ : N.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero N).2 hv
    refine ⟨w, ?_⟩
    conv_lhs => rw [h, map_add, map_smul, hv₀, zero_add]
  intro y
  induction y using Decomposition.inductionOn D with
  | zero => exact ⟨0, by rw [smul_zero]; exact N.zero_mem⟩
  | @homogeneous n y =>
    obtain ⟨w, hw⟩ := hmultiple y
    have hy : N.mkQ y ∈ grQuot D N n := mem_grQuot.2 ⟨y, y.2, rfl⟩
    obtain ⟨k, hk⟩ := exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul (grQuot D N) i hy hw
    exact ⟨k, (Submodule.Quotient.mk_eq_zero N).1 ((map_smul N.mkQ _ _).trans hk)⟩
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    refine ⟨a + b, ?_⟩
    rw [smul_add]
    apply N.add_mem
    · rw [add_comm a b, pow_add, mul_smul]
      exact N.smul_mem _ ha
    · rw [pow_add, mul_smul]
      exact N.smul_mem _ hb

theorem exists_homogeneous_family_saturating {ι R M : Type*} [Finite ι] [CommRing R]
    [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    (D : ℤ → Submodule R M) [PolyGradedSMul ι D] [Decomposition D]
    (hfin : ∀ i : ι, Module.Finite (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) M)) :
    ∃ (r : ℕ) (d : Fin r → ℤ) (g : Fin r → M), (∀ l, g l ∈ D (d l)) ∧
      ∀ (i : ι) (y : M), ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈
        Submodule.span (MvPolynomial ι R) (Set.range g) := by
  classical
  let S := MvPolynomial ι R
  let J (i : ι) : Submodule S M := (X i - 1 : S) • ⊤
  choose T hT using fun i => (hfin i).fg_top
  have exists_lift (i : ι) (q : M ⧸ J i) : ∃ (d : ℤ) (y : M), y ∈ D d ∧ (J i).mkQ y = q := by
    obtain ⟨z, rfl⟩ := (J i).mkQ_surjective q
    obtain ⟨n, hn⟩ := exists_homogeneous_add_X_sub_one_smul D i z
    obtain ⟨y, hy, w, hw⟩ := hn n le_rfl
    refine ⟨n, y, hy, ?_⟩
    have e : (J i).mkQ ((X i - 1 : S) • w) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
    conv_rhs => rw [hw, map_add, e, add_zero]
  choose d₀ g₀ hg₀ hq₀ using exists_lift
  letI := Fintype.ofFinite ι
  let I := Σ i : ι, T i
  let e := (Fintype.equivFin I).symm
  let g : Fin (Fintype.card I) → M := fun j => g₀ (e j).1 (e j).2
  let N := Submodule.span S (Set.range g)
  refine ⟨_, fun j => d₀ (e j).1 (e j).2, g, fun j => hg₀ _ _, ?_⟩
  have hN : N.IsHomogeneous D := by
    apply isHomogeneous_span_gr
    intro y hy
    change y ∈ Set.range g at hy
    obtain ⟨j, rfl⟩ := hy
    exact ⟨_, hg₀ (e j).1 (e j).2⟩
  intro i
  have hspan : (T i : Set (M ⧸ J i)) ⊆ (J i).mkQ '' Set.range g := by
    intro q hq
    let j := e.symm ⟨i, ⟨q, hq⟩⟩
    have he : e j = ⟨i, ⟨q, hq⟩⟩ := e.apply_symm_apply _
    have hg : g j = g₀ i q := by dsimp only [g]; rw [he]
    exact ⟨g j, ⟨j, rfl⟩, by rw [hg, hq₀]⟩
  apply powers_mem_of_surjective_specialization D hN i
  change N.map (J i).mkQ = ⊤
  rw [Submodule.map_span]
  apply top_unique
  rw [← hT i]
  exact Submodule.span_mono hspan

end GlobalTheory

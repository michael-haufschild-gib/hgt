import GaloisForLFunctions.HTGeometry.HermitianInertia
import GaloisForLFunctions.HTGeometry.KernelCorrelationOrder

/-!
# Nested finite-section inertia of a scalar kernel

This file supplies the exact finite-matrix layer used by dense Pick sampling.  Leading principal
extension preserves every negative subspace by zero-padding its coordinate vectors.  Consequently
the negative inertia of the nested kernel matrices is monotone, and for Hermitian kernels it is
literally the number of strictly negative eigenvalues, counted with multiplicity.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Complex
open scoped ComplexOrder

noncomputable section

/-- Extend a finite coordinate vector by a final zero coordinate. -/
def finZeroExtend {N : ℕ} : (Fin N → ℂ) →ₗ[ℂ] (Fin (N + 1) → ℂ) where
  toFun x := Fin.snoc x 0
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp]
theorem finZeroExtend_apply_castSucc {N : ℕ} (x : Fin N → ℂ) (i : Fin N) :
    finZeroExtend x i.castSucc = x i := by
  simp [finZeroExtend]

@[simp]
theorem finZeroExtend_apply_last {N : ℕ} (x : Fin N → ℂ) :
    finZeroExtend x (Fin.last N) = 0 := by
  simp [finZeroExtend]

theorem finZeroExtend_injective {N : ℕ} : Function.Injective (finZeroExtend (N := N)) := by
  intro x y h
  funext i
  have hi := congrFun h i.castSucc
  simpa using hi

/-- The Hermitian quadratic form of a leading principal block is the ambient quadratic form after
zero extension. -/
theorem hermQuad_leadingPrincipalSubmatrix {N : ℕ}
    (H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (x : Fin N → ℂ) :
    hermQuad (H.submatrix Fin.castSucc Fin.castSucc) x =
      hermQuad H (finZeroExtend x) := by
  change
    (∑ i : Fin N, (starRingEnd ℂ) (x i) *
      ∑ j : Fin N, H i.castSucc j.castSucc * x j).re =
    (∑ i : Fin (N + 1), (starRingEnd ℂ) (finZeroExtend x i) *
      ∑ j : Fin (N + 1), H i j * finZeroExtend x j).re
  rw [Fin.sum_univ_castSucc]
  rw [finZeroExtend_apply_last, map_zero, zero_mul, add_zero]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_castSucc]
  simp only [finZeroExtend_apply_castSucc, finZeroExtend_apply_last, mul_zero, add_zero]

/-- Negative inertia is monotone under leading principal extension. -/
theorem hermNegIndex_le_of_leadingPrincipalSubmatrix {N : ℕ}
    (H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    hermNegIndex (H.submatrix Fin.castSucc Fin.castSucc) ≤ hermNegIndex H := by
  obtain ⟨W, hWrank, hW⟩ :=
    exists_isPosDefOn_finrank_eq_posIndex (-(H.submatrix Fin.castSucc Fin.castSucc))
  let L : (Fin N → ℂ) →ₗ[ℂ] (Fin (N + 1) → ℂ) := finZeroExtend
  have hLinj : Function.Injective L := finZeroExtend_injective
  have hpos : IsPosDefOn (-H) (W.map L) := by
    rintro _ ⟨x, hx, rfl⟩ hx0
    have hxne : x ≠ 0 := fun hzero => hx0 (by simp [hzero])
    have hneg := hW x hx hxne
    have heq := hermQuad_leadingPrincipalSubmatrix (-H) x
    have hsubneg : (-H).submatrix Fin.castSucc Fin.castSucc =
        -(H.submatrix Fin.castSucc Fin.castSucc) := by
      rfl
    rw [hsubneg] at heq
    rw [heq] at hneg
    simpa [L] using hneg
  have hrank : Module.finrank ℂ (W.map L) = Module.finrank ℂ W :=
    ((Submodule.equivMapOfInjective L hLinj W).symm).finrank_eq
  rw [hermNegIndex, hermNegIndex, ← hWrank, ← hrank]
  exact finrank_le_posIndex hpos

variable {X : Type*}

/-- Transposed Gram orientation matching `kernelForm`: row `i`, column `j` contains
`K (z j) (z i)`. -/
def kernelFiniteSectionMatrix (K : X → X → ℂ) (z : ℕ → X) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => K (z j) (z i)

/-- Negative inertia of the first `N` nodes of a fixed kernel sampling sequence. -/
def kernelFiniteSectionNegIndex (K : X → X → ℂ) (z : ℕ → X) (N : ℕ) : ℕ :=
  hermNegIndex (kernelFiniteSectionMatrix K z N)

/-- Supremum of all nested finite-section inertias, with `⊤` representing an unbounded sequence. -/
def kernelFiniteSectionNegIndexSup (K : X → X → ℂ) (z : ℕ → X) : WithTop ℕ :=
  ⨆ N : ℕ, (kernelFiniteSectionNegIndex K z N : WithTop ℕ)

theorem kernelFiniteSectionMatrix_succ_submatrix
    (K : X → X → ℂ) (z : ℕ → X) (N : ℕ) :
    (kernelFiniteSectionMatrix K z (N + 1)).submatrix Fin.castSucc Fin.castSucc =
      kernelFiniteSectionMatrix K z N := by
  rfl

/-- Nested kernel finite-section inertia is nondecreasing. -/
theorem kernelFiniteSectionNegIndex_le_succ
    (K : X → X → ℂ) (z : ℕ → X) (N : ℕ) :
    kernelFiniteSectionNegIndex K z N ≤ kernelFiniteSectionNegIndex K z (N + 1) := by
  unfold kernelFiniteSectionNegIndex
  rw [← kernelFiniteSectionMatrix_succ_submatrix K z N]
  exact hermNegIndex_le_of_leadingPrincipalSubmatrix _

/-- The complete nested finite-section inertia sequence is monotone. -/
theorem kernelFiniteSectionNegIndex_monotone
    (K : X → X → ℂ) (z : ℕ → X) :
    Monotone (kernelFiniteSectionNegIndex K z) := by
  intro n m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact ih.trans (kernelFiniteSectionNegIndex_le_succ K z m)

/-- Hermitian symmetry of the scalar kernel makes every sampled matrix Hermitian. -/
theorem kernelFiniteSectionMatrix_isHermitian
    {K : X → X → ℂ} (hK : ∀ x y, (starRingEnd ℂ) (K x y) = K y x)
    (z : ℕ → X) (N : ℕ) :
    (kernelFiniteSectionMatrix K z N).IsHermitian := by
  ext i j
  simp [kernelFiniteSectionMatrix, hK]

/-- For a Hermitian kernel, finite-section negative inertia is exactly negative-eigenvalue count. -/
theorem kernelFiniteSectionNegIndex_eq_card_neg_eigenvalues
    {K : X → X → ℂ} (hK : ∀ x y, (starRingEnd ℂ) (K x y) = K y x)
    (z : ℕ → X) (N : ℕ) :
    kernelFiniteSectionNegIndex K z N =
      ({i | (kernelFiniteSectionMatrix_isHermitian hK z N).eigenvalues i < 0} :
        Finset (Fin N)).card := by
  exact negIndex_eq_card_neg_eigenvalues (kernelFiniteSectionMatrix_isHermitian hK z N)

/-- A Hermitian complex matrix has zero negative inertia exactly when it is positive semidefinite. -/
theorem hermNegIndex_eq_zero_iff_posSemidef {N : ℕ}
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    hermNegIndex H = 0 ↔ H.PosSemidef := by
  rw [negIndex_eq_card_neg_eigenvalues hH]
  constructor
  · intro hzero
    rw [hH.posSemidef_iff_eigenvalues_nonneg]
    intro i
    by_contra hi
    have himem : i ∈ ({j | hH.eigenvalues j < 0} : Finset (Fin N)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_not_ge hi
    have hempty : ({j | hH.eigenvalues j < 0} : Finset (Fin N)) = ∅ :=
      Finset.card_eq_zero.mp hzero
    rw [hempty] at himem
    simp at himem
  · intro hpsd
    apply Finset.card_eq_zero.mpr
    ext i
    simp [not_lt_of_ge (hpsd.eigenvalues_nonneg i)]

/-- On a finite node type, `kernelForm` is exactly the real Hermitian quadratic form of the
transposed kernel matrix. -/
theorem finiteKernelForm_eq_hermQuad {N : ℕ}
    (K : Fin N → Fin N → ℂ) (v : Fin N → ℂ) :
    (kernelForm K
      ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin N)).symm v)
      ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin N)).symm v)).re =
      hermQuad (Matrix.of fun i j => K j i) v := by
  let vf : Fin N →₀ ℂ := (Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin N)).symm v
  have hvf : ∀ i, vf i = v i := by
    intro i
    have h := congrFun
      ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin N)).apply_symm_apply v) i
    exact h
  change (kernelForm K vf vf).re = _
  rw [kernelForm]
  rw [Finsupp.sum_fintype]
  · have hinner : ∀ i : Fin N,
        vf.sum (fun x b => (starRingEnd ℂ) (vf i) * b * K x i) =
          ∑ j : Fin N, (starRingEnd ℂ) (vf i) * vf j * K j i := by
      intro i
      rw [Finsupp.sum_fintype]
      intro j
      simp only [mul_zero, zero_mul]
    simp_rw [hinner]
    simp_rw [hvf]
    simp only [hermQuad, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
      RCLike.star_def]
    apply congrArg Complex.re
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro i
    simp only [map_zero, zero_mul, Finsupp.sum_fun_zero]

/-- The negative inertia of a finite sample gives a literal kernel-negative packet of exactly the
same dimension. -/
theorem hasFiniteKernelNegativeDimension_of_sample_negIndex {N : ℕ}
    (K : X → X → ℂ) (w : Fin N → X) :
    HasFiniteKernelNegativeDimension K
      (hermNegIndex (Matrix.of fun i j => K (w j) (w i))) := by
  let M : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun i j => K (w j) (w i)
  let r : ℕ := hermNegIndex M
  obtain ⟨W, hWrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-M)
  have hrank : Module.finrank ℂ W = r := by
    simpa [r, hermNegIndex] using hWrank
  let b : Module.Basis (Fin r) ℂ W :=
    (Module.finBasis ℂ W).reindex (Fintype.equivFinOfCardEq (by simpa using hrank))
  let f : Fin r → (Fin N →₀ ℂ) := fun i =>
    (Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin N)).symm ((b i : W) : Fin N → ℂ)
  let d : Fin r → (X →₀ ℂ) := fun i => Finsupp.mapDomain w (f i)
  refine ⟨d, ?_⟩
  intro c hc
  let vW : W := ∑ i, c i • b i
  have hvW : vW ≠ 0 := by
    intro hv
    have hall : ∀ i, c i = 0 :=
      (Fintype.linearIndependent_iff.mp b.linearIndependent c) (by simpa [vW] using hv)
    exact hc (funext hall)
  have hvWval : ((vW : W) : Fin N → ℂ) ≠ 0 := by
    intro hzero
    exact hvW (Subtype.ext hzero)
  have hnegative : 0 < hermQuad (-M) (vW : Fin N → ℂ) :=
    hW (vW : Fin N → ℂ) vW.property hvWval
  have hsumf : ∑ i, c i • f i =
      (Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin N)).symm ((vW : W) : Fin N → ℂ) := by
    apply (Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin N)).injective
    simp [f, vW]
  have hsumd : ∑ i, c i • d i =
      Finsupp.mapDomain w
        ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin N)).symm ((vW : W) : Fin N → ℂ)) := by
    simp only [d, ← Finsupp.mapDomain_smul]
    calc
      ∑ i, Finsupp.mapDomain w (c i • f i) =
          Finsupp.mapDomain w (∑ i, c i • f i) := by
        exact (map_sum (Finsupp.mapDomain.addMonoidHom w)
          (fun i => c i • f i) Finset.univ).symm
      _ = _ := by rw [hsumf]
  rw [hsumd, kernelForm_mapDomain]
  rw [finiteKernelForm_eq_hermQuad]
  simpa [hermQuad_neg] using hnegative

/-- Conversely, every literal negative packet on a finite node type fits inside the negative
spectral subspace of its transposed kernel matrix. -/
theorem le_hermNegIndex_of_hasFiniteKernelNegativeDimension {N r : ℕ}
    (K : Fin N → Fin N → ℂ) (hneg : HasFiniteKernelNegativeDimension K r) :
    r ≤ hermNegIndex (Matrix.of fun i j => K j i) := by
  obtain ⟨d, hd⟩ := hneg
  let E := Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin N)
  let T : (Fin r → ℂ) →ₗ[ℂ] (Fin N → ℂ) :=
    { toFun := fun c => E (∑ i, c i • d i)
      map_add' := by
        intro c e
        apply E.symm.injective
        simp [E, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        apply E.symm.injective
        simp [E, Finset.smul_sum, smul_smul] }
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hcT
    by_contra hc
    have hform := hd c hc
    have hsum : ∑ i, c i • d i = 0 := by
      apply E.injective
      simpa [T] using hcT
    have : (kernelForm K 0 0).re < 0 := by simpa [hsum] using hform
    simp [kernelForm] at this
  have hpos : IsPosDefOn (-(Matrix.of fun i j => K j i)) (LinearMap.range T) := by
    rintro _ ⟨c, rfl⟩ hcT
    have hc : c ≠ 0 := fun hzero => hcT (by simp [hzero])
    have hform := hd c hc
    have heq := finiteKernelForm_eq_hermQuad K (T c)
    have hsymm : E.symm (T c) = ∑ i, c i • d i := by
      simp [T, E]
    rw [hsymm] at heq
    rw [hermQuad_neg]
    rw [← heq]
    linarith
  have hrank : Module.finrank ℂ (LinearMap.range T) = r := by
    rw [← Submodule.map_top]
    rw [((Submodule.equivMapOfInjective T hT ⊤).symm).finrank_eq]
    simp
  rw [← hrank, hermNegIndex]
  exact finrank_le_posIndex hpos

/-- Every nested finite-section inertia is a genuine finite negative dimension of the ambient
kernel. -/
theorem hasFiniteKernelNegativeDimension_kernelFiniteSectionNegIndex
    (K : X → X → ℂ) (z : ℕ → X) (N : ℕ) :
    HasFiniteKernelNegativeDimension K (kernelFiniteSectionNegIndex K z N) := by
  exact hasFiniteKernelNegativeDimension_of_sample_negIndex K (fun i : Fin N => z i)

/-- A global upper bound on finite negative dimensions bounds every nested finite section. -/
theorem kernelFiniteSectionNegIndex_le_of_global_bound
    {K : X → X → ℂ} {k : ℕ}
    (hbound : ∀ r, HasFiniteKernelNegativeDimension K r → r ≤ k)
    (z : ℕ → X) (N : ℕ) :
    kernelFiniteSectionNegIndex K z N ≤ k :=
  hbound _ (hasFiniteKernelNegativeDimension_kernelFiniteSectionNegIndex K z N)

/-- Every literal kernel-negative packet is supported on one finite subset of the node type. -/
theorem exists_finite_support_restriction_negativeDimension
    (K : X → X → ℂ) {r : ℕ}
    (hneg : HasFiniteKernelNegativeDimension K r) :
    ∃ S : Finset X, HasFiniteKernelNegativeDimension
      (fun x y : S => K x.1 y.1) r := by
  classical
  obtain ⟨d, hd⟩ := hneg
  let S : Finset X := Finset.univ.biUnion fun i : Fin r => (d i).support
  let dS : Fin r → (S →₀ ℂ) := fun i =>
    Finsupp.subtypeDomain (fun x => x ∈ S) (d i)
  have hsupp (i : Fin r) : (d i).support ⊆ S := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
  have hmap (i : Fin r) :
      Finsupp.mapDomain (Subtype.val : S → X) (dS i) = d i := by
    ext x
    by_cases hx : x ∈ (d i).support
    · have hxS : x ∈ S := hsupp i hx
      have hval : (Subtype.val : S → X) ⟨x, hxS⟩ = x := rfl
      rw [← hval, Finsupp.mapDomain_apply Subtype.val_injective]
      rfl
    · have hnr : x ∉ Set.range (Subtype.val : S → X) ∨ x ∈ S := by
        by_cases hxS : x ∈ S
        · exact Or.inr hxS
        · left
          rintro ⟨y, rfl⟩
          exact hxS y.property
      rcases hnr with hnr | hxS
      · rw [Finsupp.mapDomain_notin_range _ _ hnr]
        exact (Finsupp.notMem_support_iff.mp hx).symm
      · have hval : (Subtype.val : S → X) ⟨x, hxS⟩ = x := rfl
        rw [← hval, Finsupp.mapDomain_apply Subtype.val_injective]
        rfl
  refine ⟨S, dS, ?_⟩
  intro c hc
  have hsum : Finsupp.mapDomain (Subtype.val : S → X) (∑ i, c i • dS i) =
      ∑ i, c i • d i := by
    calc
      Finsupp.mapDomain (Subtype.val : S → X) (∑ i, c i • dS i) =
          ∑ i, Finsupp.mapDomain (Subtype.val : S → X) (c i • dS i) := by
        exact map_sum (Finsupp.mapDomain.addMonoidHom Subtype.val)
          (fun i => c i • dS i) Finset.univ
      _ = ∑ i, c i • d i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finsupp.mapDomain_smul, hmap]
  have h := hd c hc
  rw [← hsum, kernelForm_mapDomain] at h
  exact h

/-- Every literal finite negative dimension is visible as a lower bound for the inertia of one
finite sampled kernel matrix. -/
theorem exists_finite_sample_negIndex_ge
    (K : X → X → ℂ) {r : ℕ}
    (hneg : HasFiniteKernelNegativeDimension K r) :
    ∃ (N : ℕ) (w : Fin N → X),
      r ≤ hermNegIndex (Matrix.of fun i j => K (w j) (w i)) := by
  classical
  obtain ⟨S, hnegS⟩ :=
    exists_finite_support_restriction_negativeDimension K hneg
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let w : Fin (Fintype.card S) → X := fun i => (e.symm i).1
  have hnegFin : HasFiniteKernelNegativeDimension
      (fun i j : Fin (Fintype.card S) => K (w i) (w j)) r := by
    exact (hasFiniteKernelNegativeDimension_diagonal_equiv_iff
      (fun x y : S => K x.1 y.1)
      (fun i j : Fin (Fintype.card S) => K (w i) (w j))
      e (fun _ => 1) (fun _ => one_ne_zero)
      (fun _ _ => by simp [w, e]) r).mp hnegS
  exact ⟨Fintype.card S, w,
    le_hermNegIndex_of_hasFiniteKernelNegativeDimension _ hnegFin⟩

/-- Bounding all arbitrary finite sample inertias is equivalent to bounding every literal finite
negative dimension of the kernel. -/
theorem finite_sample_negIndex_le_iff_global_bound
    (K : X → X → ℂ) (m : ℕ) :
    (∀ (N : ℕ) (w : Fin N → X),
      hermNegIndex (Matrix.of fun i j => K (w j) (w i)) ≤ m) ↔
      ∀ r, HasFiniteKernelNegativeDimension K r → r ≤ m := by
  constructor
  · intro hsamples r hr
    obtain ⟨N, w, hrle⟩ := exists_finite_sample_negIndex_ge K hr
    exact hrle.trans (hsamples N w)
  · intro hglobal N w
    exact hglobal _ (hasFiniteKernelNegativeDimension_of_sample_negIndex K w)

/-- A surjective enumeration of a node type captures every literal finite negative packet in one
initial segment. -/
theorem exists_prefix_hasFiniteKernelNegativeDimension_of_surjective
    (K : X → X → ℂ) (z : ℕ → X) (hz : Function.Surjective z)
    {r : ℕ} (hneg : HasFiniteKernelNegativeDimension K r) :
    ∃ N : ℕ, HasFiniteKernelNegativeDimension
      (fun i j : Fin N => K (z i) (z j)) r := by
  classical
  obtain ⟨S, hnegS⟩ :=
    exists_finite_support_restriction_negativeDimension K hneg
  let idx : S → ℕ := fun x => Classical.choose (hz x.1)
  have hidx (x : S) : z (idx x) = x.1 := Classical.choose_spec (hz x.1)
  let N : ℕ := (Finset.univ : Finset S).sup idx + 1
  have hidxlt (x : S) : idx x < N := by
    exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ x))
  let e : S → Fin N := fun x => ⟨idx x, hidxlt x⟩
  have he : Function.Injective e := by
    intro x y hxy
    have hindex : idx x = idx y := congrArg Fin.val hxy
    apply Subtype.ext
    rw [← hidx x, ← hidx y, hindex]
  refine ⟨N, ?_⟩
  apply hasFiniteKernelNegativeDimension_of_diagonal_pullback
    (fun x y : S => K x.1 y.1)
    (fun i j : Fin N => K (z i) (z j)) e (fun _ => 1)
      (fun _ => one_ne_zero)
  · intro x y
    simp only [one_mul, map_one, mul_one, e]
    rw [hidx x, hidx y]
  · exact hnegS

/-- Every ambient finite negative dimension appears as a lower bound for one prefix inertia of a
surjective enumeration. -/
theorem exists_le_kernelFiniteSectionNegIndex_of_surjective
    (K : X → X → ℂ) (z : ℕ → X) (hz : Function.Surjective z)
    {r : ℕ} (hneg : HasFiniteKernelNegativeDimension K r) :
    ∃ N : ℕ, r ≤ kernelFiniteSectionNegIndex K z N := by
  obtain ⟨N, hN⟩ :=
    exists_prefix_hasFiniteKernelNegativeDimension_of_surjective K z hz hneg
  refine ⟨N, ?_⟩
  exact le_hermNegIndex_of_hasFiniteKernelNegativeDimension _ hN

/-- If the ambient kernel has exact finite negative dimension `k`, one prefix of every surjective
enumeration already has inertia exactly `k`. -/
theorem exists_kernelFiniteSectionNegIndex_eq_of_surjective
    (K : X → X → ℂ) (z : ℕ → X) (hz : Function.Surjective z) {k : ℕ}
    (hk : HasFiniteKernelNegativeDimension K k)
    (hbound : ∀ r, HasFiniteKernelNegativeDimension K r → r ≤ k) :
    ∃ N : ℕ, kernelFiniteSectionNegIndex K z N = k := by
  obtain ⟨N, hlower⟩ :=
    exists_le_kernelFiniteSectionNegIndex_of_surjective K z hz hk
  exact ⟨N, le_antisymm
    (kernelFiniteSectionNegIndex_le_of_global_bound hbound z N) hlower⟩

/-- In the exact finite-index case, the monotone prefix-inertia sequence stabilizes at the ambient
negative dimension. -/
theorem eventually_kernelFiniteSectionNegIndex_eq_of_surjective
    (K : X → X → ℂ) (z : ℕ → X) (hz : Function.Surjective z) {k : ℕ}
    (hk : HasFiniteKernelNegativeDimension K k)
    (hbound : ∀ r, HasFiniteKernelNegativeDimension K r → r ≤ k) :
    ∀ᶠ N in Filter.atTop, kernelFiniteSectionNegIndex K z N = k := by
  obtain ⟨N, hN⟩ :=
    exists_kernelFiniteSectionNegIndex_eq_of_surjective K z hz hk hbound
  filter_upwards [Filter.eventually_ge_atTop N] with m hm
  apply le_antisymm
  · exact kernelFiniteSectionNegIndex_le_of_global_bound hbound z m
  · rw [← hN]
    exact kernelFiniteSectionNegIndex_monotone K z hm

/-- The ordinary limit of the finite-index prefix inertias is the exact ambient index. -/
theorem tendsto_kernelFiniteSectionNegIndex_of_surjective
    (K : X → X → ℂ) (z : ℕ → X) (hz : Function.Surjective z) {k : ℕ}
    (hk : HasFiniteKernelNegativeDimension K k)
    (hbound : ∀ r, HasFiniteKernelNegativeDimension K r → r ≤ k) :
    Filter.Tendsto (kernelFiniteSectionNegIndex K z) Filter.atTop (nhds k) := by
  have hev : (fun _ : ℕ => k) =ᶠ[Filter.atTop] kernelFiniteSectionNegIndex K z := by
    filter_upwards
      [eventually_kernelFiniteSectionNegIndex_eq_of_surjective K z hz hk hbound] with N hN
    exact hN.symm
  exact Filter.Tendsto.congr' hev tendsto_const_nhds

/-- In the exact finite-index case, the supremum of prefix inertias is the ambient index. -/
theorem kernelFiniteSectionNegIndexSup_eq_of_surjective
    (K : X → X → ℂ) (z : ℕ → X) (hz : Function.Surjective z) {k : ℕ}
    (hk : HasFiniteKernelNegativeDimension K k)
    (hbound : ∀ r, HasFiniteKernelNegativeDimension K r → r ≤ k) :
    kernelFiniteSectionNegIndexSup K z = (k : WithTop ℕ) := by
  apply le_antisymm
  · apply iSup_le
    intro N
    exact WithTop.coe_le_coe.mpr
      (kernelFiniteSectionNegIndex_le_of_global_bound hbound z N)
  · obtain ⟨N, hN⟩ :=
      exists_kernelFiniteSectionNegIndex_eq_of_surjective K z hz hk hbound
    rw [← hN]
    exact le_iSup (fun N : ℕ => (kernelFiniteSectionNegIndex K z N : WithTop ℕ)) N

/-- If every finite negative dimension occurs globally, prefix inertias of a surjective enumeration
are unbounded. -/
theorem kernelFiniteSectionNegIndex_unbounded_of_surjective
    (K : X → X → ℂ) (z : ℕ → X) (hz : Function.Surjective z)
    (hunbounded : ∀ r, HasFiniteKernelNegativeDimension K r) :
    ∀ r, ∃ N : ℕ, r ≤ kernelFiniteSectionNegIndex K z N := by
  intro r
  exact exists_le_kernelFiniteSectionNegIndex_of_surjective K z hz (hunbounded r)

/-- In the infinite-index case, the monotone prefix inertias tend to infinity. -/
theorem tendsto_kernelFiniteSectionNegIndex_atTop_of_surjective
    (K : X → X → ℂ) (z : ℕ → X) (hz : Function.Surjective z)
    (hunbounded : ∀ r, HasFiniteKernelNegativeDimension K r) :
    Filter.Tendsto (kernelFiniteSectionNegIndex K z) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro r
  obtain ⟨N, hN⟩ :=
    kernelFiniteSectionNegIndex_unbounded_of_surjective K z hz hunbounded r
  filter_upwards [Filter.eventually_ge_atTop N] with m hm
  exact hN.trans (kernelFiniteSectionNegIndex_monotone K z hm)

/-- In the infinite-index case, the supremum of prefix inertias is `⊤`. -/
theorem kernelFiniteSectionNegIndexSup_eq_top_of_surjective
    (K : X → X → ℂ) (z : ℕ → X) (hz : Function.Surjective z)
    (hunbounded : ∀ r, HasFiniteKernelNegativeDimension K r) :
    kernelFiniteSectionNegIndexSup K z = ⊤ := by
  unfold kernelFiniteSectionNegIndexSup
  apply (WithTop.iSup_coe_eq_top
    (f := fun N : ℕ => kernelFiniteSectionNegIndex K z N)).2
  intro hb
  obtain ⟨a, ha⟩ := hb
  obtain ⟨N, hN⟩ :=
    kernelFiniteSectionNegIndex_unbounded_of_surjective K z hz hunbounded (a + 1)
  have hupper : kernelFiniteSectionNegIndex K z N ≤ a := ha ⟨N, rfl⟩
  omega

/-- A dense sequence in a nonempty open complex region has an ambient accumulation point whose
punctured neighborhoods meet the sequence range. -/
theorem denseRange_subtype_range_accumulates
    {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty)
    (z : ℕ → U) (hz : DenseRange z) :
    ∃ p : ℂ, p ∈ U ∧
      ∃ᶠ w in nhdsWithin p ({p}ᶜ), w ∈ Set.range (fun n => (z n).1) := by
  obtain ⟨p, hp⟩ := hne
  let ps : U := ⟨p, hp⟩
  have hpclosePunct : ps ∈ closure ({ps}ᶜ : Set U) := by
    rw [mem_closure_iff]
    intro O hO hpO
    have hOimg : IsOpen (Subtype.val '' O : Set ℂ) :=
      (hU.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen).mp hO
    have hOimgne : (Subtype.val '' O : Set ℂ).Nonempty :=
      ⟨p, ps, hpO, rfl⟩
    obtain ⟨q, ⟨hqO, hqne⟩⟩ :=
      (dense_compl_singleton p).inter_open_nonempty _ hOimg hOimgne
    obtain ⟨x, hxO, hxq⟩ := hqO
    refine ⟨x, hxO, ?_⟩
    intro hxp
    apply hqne
    rw [← hxq]
    exact congrArg Subtype.val hxp
  have hnebot : (nhdsWithin ps ({ps}ᶜ : Set U)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hpclosePunct
  letI : (nhdsWithin ps ({ps}ᶜ : Set U)).NeBot := hnebot
  have hpunct : Dense ({ps}ᶜ : Set U) := dense_compl_singleton ps
  have hdense : Dense (Set.range z ∩ ({ps}ᶜ : Set U)) :=
    hz.inter_of_isOpen_right hpunct isOpen_compl_singleton
  have hpclose : ps ∈ closure (Set.range z ∩ ({ps}ᶜ : Set U)) := hdense ps
  let A : Set U := Set.range z ∩ ({ps}ᶜ : Set U)
  have hpimage : p ∈ closure (Subtype.val '' A) := by
    apply map_mem_closure continuous_subtype_val hpclose
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hfreq : ∃ᶠ w in nhds p, w ∈ Subtype.val '' A :=
    mem_closure_iff_frequently.mp hpimage
  refine ⟨p, hp, frequently_nhdsWithin_iff.mpr ?_⟩
  exact hfreq.mono fun w hw => by
    obtain ⟨x, ⟨⟨n, hn⟩, hnep⟩, hxw⟩ := hw
    subst w
    refine ⟨⟨n, congrArg Subtype.val hn⟩, ?_⟩
    intro h
    apply hnep
    apply Subtype.ext
    exact h

end

end GaloisForLFunctions.HTGeometry

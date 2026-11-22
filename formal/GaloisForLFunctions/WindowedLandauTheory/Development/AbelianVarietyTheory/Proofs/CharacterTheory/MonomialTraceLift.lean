import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Eigenvalue multiplicities of a finite-order monomial matrix are preserved by lifting. -/

open Polynomial

namespace GlobalTheory.CuspGL

private def orbProd {K : Type} [CommMonoid K] {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → K)
    (m : ℕ) (j : Fin n) : K :=
  ∏ i ∈ Finset.range m, a ((σ ^ i) j)

private def compatibleCycle {K : Type} [CommMonoid K] {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → K)
    (j : Fin n) : Prop :=
  (∀ m : ℕ, j ≤ (σ ^ m) j) ∧ ∀ m : ℕ, (σ ^ m) j = j → orbProd σ a m j = 1

section
variable {K : Type} [Field K] {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → K)

private lemma orbProd_succ (m : ℕ) (j : Fin n) :
    orbProd σ a (m + 1) j = orbProd σ a m j * a ((σ ^ m) j) := by
  simp [orbProd, Finset.prod_range_succ]

private lemma orbProd_add (d m : ℕ) (j : Fin n) :
    orbProd σ a (d + m) j = orbProd σ a d j * orbProd σ a m ((σ ^ d) j) := by
  unfold orbProd
  rw [Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [add_comm, pow_add, Equiv.Perm.mul_apply]

private lemma orbProd_eq {j : Fin n} (hj : ∀ m : ℕ, (σ ^ m) j = j → orbProd σ a m j = 1)
    (m m' : ℕ) (h : (σ ^ m) j = (σ ^ m') j) : orbProd σ a m j = orbProd σ a m' j := by
  wlog hle : m ≤ m' generalizing m m'
  · exact (this m' m h.symm (le_of_not_ge hle)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hle
  have hd : (σ ^ d) j = j := by
    rw [add_comm, pow_add, Equiv.Perm.mul_apply] at h
    exact ((σ ^ m).injective h).symm
  rw [orbProd_add, hj d hd, hd, one_mul]

private lemma apply_pow {v : Fin n → K} (hv : ∀ j, v (σ j) = a j * v j) (m : ℕ) (j : Fin n) :
    v ((σ ^ m) j) = orbProd σ a m j * v j := by
  induction m with
  | zero => simp [orbProd]
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, hv, ih, orbProd_succ]; ring

private lemma exists_back (m : ℕ) (j : Fin n) : ∃ m' : ℕ, (σ ^ m') ((σ ^ m) j) = j := by
  have h : σ.SameCycle ((σ ^ m) j) j := by
    rw [Equiv.Perm.sameCycle_pow_left]
  exact h.exists_nat_pow_eq

private lemma exists_rep (i : Fin n) : ∃ j : Fin n, (∀ m : ℕ, j ≤ (σ ^ m) j) ∧ ∃ m : ℕ, (σ ^ m) j = i := by
  classical
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun j => ∃ m : ℕ, (σ ^ m) i = j) id ⟨i, by simpa using ⟨0, by simp⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, id] at hj hmin
  obtain ⟨m, rfl⟩ := hj
  refine ⟨_, fun k => hmin _ ⟨k + m, by rw [pow_add, Equiv.Perm.mul_apply]⟩, exists_back σ m i⟩

private lemma exists_vec {s : Fin n} (hs : compatibleCycle σ a s) :
    ∃ v : Fin n → K, (∀ j, v (σ j) = a j * v j) ∧ v s = 1 ∧
      ∀ t, compatibleCycle σ a t → t ≠ s → v t = 0 := by
  classical
  let v : Fin n → K := fun i => if h : ∃ m : ℕ, (σ ^ m) s = i then orbProd σ a h.choose s else 0
  have hv : ∀ m : ℕ, v ((σ ^ m) s) = orbProd σ a m s := by
    intro m
    have h : ∃ m' : ℕ, (σ ^ m') s = (σ ^ m) s := ⟨m, rfl⟩
    simp only [v, dif_pos h]
    exact orbProd_eq σ a hs.2 _ _ h.choose_spec
  refine ⟨v, fun j => ?_, by simpa [orbProd] using hv 0, fun t ht hts => ?_⟩
  · by_cases h : ∃ m : ℕ, (σ ^ m) s = j
    · obtain ⟨m, rfl⟩ := h
      rw [← Equiv.Perm.mul_apply, ← pow_succ', hv, hv, orbProd_succ, mul_comm]
    · have h' : ¬ ∃ m : ℕ, (σ ^ m) s = σ j := by
        rintro ⟨m, hm⟩
        obtain ⟨m', hm'⟩ := exists_back σ 1 j
        refine h ⟨m' + m, ?_⟩
        rw [pow_add, Equiv.Perm.mul_apply, hm]
        simpa using hm'
      simp only [v, dif_neg h, dif_neg h', mul_zero]
  · have h' : ¬ ∃ m : ℕ, (σ ^ m) s = t := by
      rintro ⟨m, rfl⟩
      obtain ⟨m', hm'⟩ := exists_back σ m s
      have h1 := ht.1 m'
      rw [hm'] at h1
      exact hts (le_antisymm h1 (hs.1 m))
    simp only [v, dif_neg h']

private theorem finrank_eq_card (E : Submodule K (Fin n → K))
    (hE : ∀ v, v ∈ E ↔ ∀ j, v (σ j) = a j * v j) :
    Module.finrank K E = Nat.card {j // compatibleCycle σ a j} := by
  classical
  let f : E →ₗ[K] ({j // compatibleCycle σ a j} → K) :=
    (LinearMap.funLeft K K Subtype.val).comp E.subtype
  have hf : ∀ (v : E) s, f v s = v.1 s.1 := fun _ _ => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro v h0
    have hv := (hE _).1 v.2
    ext i
    obtain ⟨j, hj, m, rfl⟩ := exists_rep σ i
    have : v.1 j = 0 := by
      by_cases hg : compatibleCycle σ a j
      · have := congrFun h0 ⟨j, hg⟩
        simpa [hf] using this
      · have : ¬ ∀ m : ℕ, (σ ^ m) j = j → orbProd σ a m j = 1 := fun h => hg ⟨hj, h⟩
        push_neg at this
        obtain ⟨r, hr, hne⟩ := this
        have h2 := apply_pow σ a hv r j
        rw [hr] at h2
        by_contra h3
        exact hne (mul_right_cancel₀ h3 (by rw [← h2, one_mul]))
    simp [apply_pow σ a hv, this]
  have hsurj : Function.Surjective f := by
    intro w
    choose u hu h1 h0 using fun s : {j // compatibleCycle σ a j} => exists_vec σ a s.2
    refine ⟨∑ s, w s • ⟨u s, (hE _).2 (hu s)⟩, ?_⟩
    ext t
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single t]
    · simp [hf, h1]
    · intro s _ hst
      simp [hf, h0 s t.1 t.2 (fun h => hst (Subtype.ext h).symm)]
    · simp
  rw [(LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

private lemma mem_eigenspace_iff (c : Fin n → K) (μ : K) (hμ : μ ≠ 0) (v : Fin n → K) :
    v ∈ Module.End.eigenspace
      (Matrix.toLin' (Matrix.of fun i j => if i = σ j then c j else 0)) μ ↔
      ∀ j, v (σ j) = (c j * μ⁻¹) * v j := by
  rw [Module.End.mem_eigenspace_iff, funext_iff, ← σ.forall_congr_right]
  refine forall_congr' fun j => ?_
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
    EmbeddingLike.apply_eq_iff_eq, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    field_simp
    linear_combination -h
  · intro h
    rw [h]; field_simp

end

-- A cycle contributes one coordinate exactly when its normalized weight product is one.
private theorem finrank_eigenspace_monomial_lift {k : Type} [Field k] (θ : k →* ℂ)
    (hθ : ∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y)
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (c : Fin n → k) (hc : ∀ j, c j ≠ 0)
    (μ : k) (hμ : μ ≠ 0) :
    Module.finrank k
        (Module.End.eigenspace (Matrix.toLin' (Matrix.of fun i j => if i = σ j then c j else 0)) μ) =
      Module.finrank ℂ (Module.End.eigenspace
        (Matrix.toLin' (Matrix.of fun i j => if i = σ j then θ (c j) else 0)) (θ μ)) := by
  have hmul : θ μ * θ μ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hμ, map_one]
  have hθμ : θ μ ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hinv : (θ μ)⁻¹ = θ μ⁻¹ := inv_eq_of_mul_eq_one_right hmul
  rw [finrank_eq_card σ (fun j => c j * μ⁻¹) _ (mem_eigenspace_iff σ c μ hμ),
    finrank_eq_card σ (fun j => θ (c j) * (θ μ)⁻¹) _
      (mem_eigenspace_iff σ (fun j => θ (c j)) (θ μ) hθμ)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun j => ?_)
  refine and_congr_right fun _ => forall_congr' fun m => imp_congr_right fun _ => ?_
  have h1 : orbProd σ (fun j => θ (c j) * (θ μ)⁻¹) m j
      = θ (orbProd σ (fun j => c j * μ⁻¹) m j) := by
    simp only [orbProd, map_prod, map_mul, hinv]
  have h2 : orbProd σ (fun j => c j * μ⁻¹) m j ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hc _) (inv_ne_zero hμ)
  rw [h1]
  constructor
  · intro h; rw [h, map_one]
  · intro h
    exact hθ _ _ h2 one_ne_zero (by rw [h, map_one])

private theorem sum_roots_charpoly_eq_finsum_eigenspace (k : Type) [Field k] [IsAlgClosed k] (V : Type)
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (g : Module.End k V) (N : ℕ)
    (hN : (N : k) ≠ 0) (hg : g ^ N = 1) (h : k → ℂ) :
    ((LinearMap.charpoly g).roots.map h).sum =
      ∑ᶠ μ ∈ {μ : k | μ ^ N = 1}, (Module.finrank k (Module.End.eigenspace g μ) : ℂ) * h μ := by
  classical
  have hsep : (X ^ N - C (1 : k) : k[X]).Separable := separable_X_pow_sub_C 1 hN one_ne_zero
  have hss : g.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hg])
  have hdim : ∀ μ, Module.finrank k (Module.End.eigenspace g μ) =
      (LinearMap.charpoly g).roots.count μ := by
    intro μ
    rw [← hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ,
      LinearMap.finrank_maxGenEigenspace_eq, count_roots]
  rw [Finset.sum_multiset_map_count]
  rw [finsum_mem_eq_sum_of_inter_support_eq _ (t := (LinearMap.charpoly g).roots.toFinset)]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hdim, nsmul_eq_mul]
  · ext μ
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support, Finset.mem_coe,
      Multiset.mem_toFinset]
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨?_, h2⟩
      by_contra hc
      apply h2
      rw [hdim, Multiset.count_eq_zero_of_notMem hc]
      simp
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have hev : g.HasEigenvalue μ := by
        rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
        exact isRoot_of_mem_roots h1
      have h3 := hev.pow N
      rw [hg] at h3
      obtain ⟨v, hv⟩ := h3.exists_hasEigenvector
      have h4 := hv.apply_eq_smul
      have h5 : (μ ^ N - 1) • v = 0 := by
        rw [sub_smul, ← h4]; simp
      exact sub_eq_zero.mp ((smul_eq_zero.mp h5).resolve_right hv.2)

private theorem ncard_pow_eq_one (k : Type) [Field k] [IsAlgClosed k] (N : ℕ) (hN : (N : k) ≠ 0) :
    {μ : k | μ ^ N = 1}.Finite ∧ {μ : k | μ ^ N = 1}.ncard = N := by
  haveI : NeZero (N : k) := ⟨hN⟩
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k N
  have hs : {μ : k | μ ^ N = 1} = (nthRootsFinset N (1 : k) : Set k) := by
    ext x
    simp [mem_nthRootsFinset (Nat.pos_of_ne_zero hN0)]
  rw [hs]
  exact ⟨Finset.finite_toSet _, by rw [Set.ncard_coe_finset, hζ.card_nthRootsFinset]⟩

private theorem bijOn_pow_eq_one (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ)
    (hθ : ∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (N : ℕ) (hN : (N : k) ≠ 0) :
    Set.BijOn θ {μ : k | μ ^ N = 1} {μ : ℂ | μ ^ N = 1} := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hne : ∀ μ : k, μ ^ N = 1 → μ ≠ 0 := by
    rintro μ h rfl
    simp [hN0] at h
  have hmaps : Set.MapsTo θ {μ : k | μ ^ N = 1} {μ : ℂ | μ ^ N = 1} := by
    intro μ h
    simp only [Set.mem_setOf_eq] at h ⊢
    rw [← map_pow, h, map_one]
  have hinj : Set.InjOn θ {μ : k | μ ^ N = 1} :=
    fun x hx y hy h => hθ x y (hne x hx) (hne y hy) h
  obtain ⟨_, h1⟩ := ncard_pow_eq_one k N hN
  obtain ⟨f2, h2⟩ := ncard_pow_eq_one ℂ N (by exact_mod_cast hN0)
  have himg : θ '' {μ : k | μ ^ N = 1} = {μ : ℂ | μ ^ N = 1} := by
    apply Set.eq_of_subset_of_ncard_le hmaps.image_subset _ f2
    rw [hinj.ncard_image, h1, h2]
  exact ⟨hmaps, hinj, himg.ge⟩

/-- The complex trace of a monomial lift equals the sum of the lifted characteristic roots. -/
theorem trace_lift_monomial (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ)
    (hθ : ∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y)
    {n N : ℕ} (σ : Equiv.Perm (Fin n)) (c : Fin n → k) (hc : ∀ j, c j ≠ 0)
    (hN : (N : k) ≠ 0)
    (hA : (Matrix.of fun i j => if i = σ j then c j else 0 : Matrix (Fin n) (Fin n) k) ^ N = 1)
    (hB : (Matrix.of fun i j => if i = σ j then θ (c j) else 0 : Matrix (Fin n) (Fin n) ℂ) ^ N = 1) :
    Matrix.trace (Matrix.of fun i j => if i = σ j then θ (c j) else 0 : Matrix (Fin n) (Fin n) ℂ) =
      ((Matrix.charpoly (Matrix.of fun i j => if i = σ j then c j else 0 :
        Matrix (Fin n) (Fin n) k)).roots.map θ).sum := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hE := finrank_eigenspace_monomial_lift θ hθ σ c hc
  set A : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => if i = σ j then c j else 0 with hAdef
  set B : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if i = σ j then θ (c j) else 0 with hBdef
  have h1 := sum_roots_charpoly_eq_finsum_eigenspace k (Fin n → k) (Matrix.toLin' A) N hN
    (by rw [← Matrix.toLin'_pow, hA, Matrix.toLin'_one]; rfl) θ
  have h2 := sum_roots_charpoly_eq_finsum_eigenspace ℂ (Fin n → ℂ) (Matrix.toLin' B) N (by exact_mod_cast hN0)
    (by rw [← Matrix.toLin'_pow, hB, Matrix.toLin'_one]; rfl) id
  rw [Matrix.charpoly_toLin'] at h1 h2
  rw [Matrix.trace_eq_sum_roots_charpoly, h1]
  rw [Multiset.map_id] at h2
  rw [h2]
  symm
  apply finsum_mem_eq_of_bijOn θ (bijOn_pow_eq_one k θ hθ N hN)
  intro μ hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp [hN0] at hμ
  rw [hE μ hμ0]
  rfl

end GlobalTheory.CuspGL

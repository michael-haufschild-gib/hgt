import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Fin

/-! An eigenvalue orbit with a full cyclic basis determines a pair of
inertia and Frobenius operators up to equivalence. The determinant
fixes the multiplier on the last basis vector. -/

noncomputable section

open Module Matrix

namespace GlobalTheory.WeilDeligne

private theorem pow_apply_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V] (M : Module.End ℂ V) {v : V} {c : ℂ}
    (hv : M v = c • v) (k : ℕ) : (M ^ k) v = c ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' M k, Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ c k]

private theorem eigenvector_after_shift {V : Type*} [AddCommGroup V] [Module ℂ V] {q : ℕ} (M G : Module.End ℂ V)
    (hMG : M * G = G * M ^ q) {v : V} {c : ℂ} (hv : M v = c • v) (k : ℕ) :
    M ((G ^ k) v) = c ^ q ^ k • (G ^ k) v := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    have h1 : M (G ((G ^ k) v)) = G ((M ^ q) ((G ^ k) v)) := by
      rw [← Module.End.mul_apply M G, hMG, Module.End.mul_apply]
    rw [pow_succ' G k, Module.End.mul_apply, h1, pow_apply_eigenvector M ih q, map_smul, ← pow_mul,
      ← pow_succ]

private theorem exists_eigenbasis_of_cyclic_shift {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {q m : ℕ} (M G : Module.End ℂ V) (hG : IsUnit G) (hMG : M * G = G * M ^ q) {z : ℂ}
    (hperiod : z ^ q ^ (m + 1) = z)
    (hsep : Function.Injective (fun j : Fin (m + 1) => z ^ q ^ (j : ℕ)))
    (hr : Module.finrank ℂ V = m + 1) {v : V} (hv0 : v ≠ 0)
    (hv : M v = z • v) :
    ∃ b : Module.Basis (Fin (m + 1)) ℂ V, (∀ j : Fin (m + 1), M (b j) = z ^ q ^ (j : ℕ) • b j) ∧
      (∀ k : Fin m, G (b k.castSucc) = b k.succ) ∧
      ∃ μ : ℂ, μ ≠ 0 ∧ G (b (Fin.last m)) = μ • b 0 := by
  have hGinj : ∀ k : ℕ, Function.Injective (G ^ k) := fun k =>
    ((Module.End.isUnit_iff _).mp (hG.pow k)).injective
  obtain ⟨f, hf⟩ : ∃ f : Fin (m + 1) → V, ∀ j, f j = (G ^ (j : ℕ)) v := ⟨_, fun _ => rfl⟩
  have hMf : ∀ j : Fin (m + 1), M (f j) = z ^ q ^ (j : ℕ) • f j := fun j => by
    rw [hf]; exact eigenvector_after_shift M G hMG hv j
  have hfne : ∀ j, f j ≠ 0 := fun j h =>
    hv0 (hGinj (j : ℕ) (by rw [map_zero, ← hf]; exact h))
  have hli : LinearIndependent ℂ f :=
    Module.End.eigenvectors_linearIndependent' M _ hsep f
      (fun j => ⟨Module.End.mem_eigenspace_iff.mpr (hMf j), hfne j⟩)
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin (m + 1)) ℂ V, ∀ j, b j = f j :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hr]),
      fun j => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli _) j⟩
  refine ⟨b, fun j => by rw [hb]; exact hMf j, fun k => ?_, ?_⟩
  · rw [hb, hb, hf, hf, Fin.val_succ, Fin.val_castSucc, pow_succ', Module.End.mul_apply]
  · obtain ⟨x, hxdef⟩ : ∃ x, x = G (b (Fin.last m)) := ⟨_, rfl⟩
    have hxG : x = (G ^ (m + 1)) v := by
      rw [hxdef, hb, hf, Fin.val_last, pow_succ', Module.End.mul_apply]
    have hx : M x = z • x := by
      rw [hxG, eigenvector_after_shift M G hMG hv, hperiod]
    obtain ⟨c, hcdef⟩ : ∃ c, c = b.repr x := ⟨_, rfl⟩
    have hsum : x = ∑ j, c j • b j := by rw [hcdef]; exact (b.sum_repr x).symm
    have hcoef : ∀ j, c j * z ^ q ^ (j : ℕ) = z * c j := by
      intro j
      have e1 : M x = ∑ j, (c j * z ^ q ^ (j : ℕ)) • b j := by
        conv_lhs => rw [hsum]
        rw [map_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [map_smul, hb j, hMf j, smul_smul]
      have e2 : z • x = ∑ j, (z * c j) • b j := by
        conv_lhs => rw [hsum]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [smul_smul]
      have e3 : (∑ j, (c j * z ^ q ^ (j : ℕ)) • b j) = ∑ j, (z * c j) • b j :=
        e1.symm.trans (hx.trans e2)
      have e4 := congrArg (fun y => b.repr y j) e3
      simp only [Module.Basis.repr_sum_self] at e4
      exact e4
    have hc0 : ∀ j : Fin (m + 1), j ≠ 0 → c j = 0 := by
      intro j hj
      have hne : z ^ q ^ (j : ℕ) ≠ z := fun hz => hj (hsep (by simpa using hz))
      have h2 : c j * (z ^ q ^ (j : ℕ) - z) = 0 := by
        rw [mul_sub, hcoef j]
        ring
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h) hne
    have hx0 : x = c 0 • b 0 := by
      conv_lhs => rw [hsum]
      rw [Finset.sum_eq_single 0 (fun j _ hj => by rw [hc0 j hj, zero_smul]) (by simp)]
    refine ⟨c 0, fun h => ?_, ?_⟩
    · have hx00 : G (b (Fin.last m)) = 0 := by rw [← hxdef, hx0, h, zero_smul]
      exact b.ne_zero (Fin.last m)
        (((Module.End.isUnit_iff _).mp hG).injective (by rw [map_zero]; exact hx00))
    · rw [← hxdef]
      exact hx0

private theorem det_cyclic_basis_shift {V : Type*} [AddCommGroup V] [Module ℂ V]
    {m : ℕ} (b : Basis (Fin (m + 1)) ℂ V) (S : End ℂ V) (μ : ℂ)
    (hS : ∀ i : Fin m, S (b i.castSucc) = b i.succ)
    (hLast : S (b (Fin.last m)) = μ • b 0) :
    LinearMap.det S = (-1) ^ m * μ := by
  let wt (i : Fin (m + 1)) := if i = 0 then μ else 1
  let P := (Matrix.diagonal wt).submatrix (finRotate (m + 1)) id
  have hP : (LinearMap.toMatrix b b S)ᵀ = P := by
    ext i j
    rw [Matrix.transpose_apply, LinearMap.toMatrix_apply]
    change b.repr (S (b i)) j = Matrix.diagonal wt (finRotate (m + 1) i) j
    cases i using Fin.lastCases with
    | last =>
      rw [hLast, finRotate_last]
      simp only [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply,
        Matrix.diagonal_apply, wt, if_true, smul_eq_mul]
      split_ifs <;> simp_all [eq_comm]
    | cast j' =>
      have hrot : finRotate (m + 1) j'.castSucc = j'.succ := by
        exact finRotate_of_lt j'.isLt
      rw [hS, hrot, Basis.repr_self, Finsupp.single_apply, Matrix.diagonal_apply]
      simp [wt, Fin.succ_ne_zero, eq_comm]
  rw [← LinearMap.det_toMatrix b, ← Matrix.det_transpose, hP, Matrix.det_permute,
    Matrix.det_diagonal, sign_finRotate]
  simp [wt, Finset.prod_ite_eq']

theorem exists_equiv_of_cyclic_eigenvalue_pairs {V V' : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    (M S : End ℂ V) (M' S' : End ℂ V') (hS : IsUnit S) (hS' : IsUnit S')
    {q n : ℕ} (hn : 0 < n) (hd : Module.finrank ℂ V = n) (hd' : Module.finrank ℂ V' = n)
    (hMS : M * S = S * M ^ q) (hMS' : M' * S' = S' * M' ^ q)
    (z : ℂ) (hZ : M.HasEigenvalue z) (hZ' : M'.HasEigenvalue z)
    (hperiod : z ^ q ^ n = z)
    (hsep : Function.Injective (fun i : Fin n => z ^ q ^ (i : ℕ)))
    (hdet : LinearMap.det S = LinearMap.det S') :
    ∃ e : V ≃ₗ[ℂ] V', (∀ x, e (M x) = M' (e x)) ∧ (∀ x, e (S x) = S' (e x)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨x, hx⟩ := hZ.exists_hasEigenvector
  obtain ⟨y, hy⟩ := hZ'.exists_hasEigenvector
  obtain ⟨b, hm, hs, μ, -, hl⟩ := exists_eigenbasis_of_cyclic_shift M S hS hMS hperiod hsep hd hx.2
    (Module.End.mem_eigenspace_iff.mp hx.1)
  obtain ⟨b', hm', hs', μ', -, hl'⟩ := exists_eigenbasis_of_cyclic_shift M' S' hS' hMS' hperiod hsep hd' hy.2
    (Module.End.mem_eigenspace_iff.mp hy.1)
  have hμ : μ = μ' := by
    rw [det_cyclic_basis_shift b S μ hs hl, det_cyclic_basis_shift b' S' μ' hs' hl'] at hdet
    exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hdet
  let e := b.equiv b' (Equiv.refl _)
  have he (i : Fin (m + 1)) : e (b i) = b' i := by simp [e]
  have hM : e.toLinearMap.comp M = M'.comp e.toLinearMap := by
    apply b.ext
    intro i
    change e (M (b i)) = M' (e (b i))
    rw [hm, map_smul, he, hm']
  have hShift : e.toLinearMap.comp S = S'.comp e.toLinearMap := by
    apply b.ext
    intro i
    change e (S (b i)) = S' (e (b i))
    cases i using Fin.lastCases with
    | last => rw [hl, map_smul, he, he, hl', hμ]
    | cast i => rw [hs, he, he, hs']
  exact ⟨e, LinearMap.congr_fun hM, LinearMap.congr_fun hShift⟩

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.exists_equiv_of_cyclic_eigenvalue_pairs

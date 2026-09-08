import GaloisForLFunctions.HTGeometry.CavitySpinHierarchy
/-!
# Collective-spin powers and repeated-site interactions

The expansion of `S_z^k` in arXiv:2608.14343, Section II, is an ordered sum over
all site tuples. The proof here works for arbitrary matrix observables without
commutativity assumptions. No distinct-site term exists above the number of
sites, and repeated longitudinal Pauli factors reduce by parity.
-/

open scoped BigOperators Matrix
namespace GaloisForLFunctions.HTGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
/-- Every power of a collective observable is an ordered sum over all site tuples, including repeated indices. -/
theorem finiteCollectiveObservable_pow_ordered_words
    {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (A : ι → Matrix n n ℂ) (k : ℕ) :
    finiteCollectiveObservable A ^ k =
      ∑ f : Fin k → ι, (List.ofFn (fun j => A (f j))).prod := by
  classical
  induction k with
  | zero => simp [List.ofFn_zero]
  | succ k ih =>
      let e : (ι × (Fin k → ι)) ≃ (Fin (k + 1) → ι) :=
        { toFun := fun p => Fin.cons p.1 p.2
          invFun := fun f => (f 0, fun i => f i.succ)
          left_inv := fun _ => rfl
          right_inv := fun f => by funext i; exact Fin.cases rfl (fun _ => rfl) i }
      have he := Fintype.sum_equiv e
        (fun p => A p.1 * (List.ofFn (fun j => A (p.2 j))).prod)
        (fun f => (List.ofFn (fun j => A (f j))).prod)
        (fun p => by simp [e, List.ofFn_succ])
      rw [← he, Fintype.sum_prod_type, pow_succ', ih, finiteCollectiveObservable, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.mul_sum]
/-- Half-normalized spin powers retain the same complete ordered tuple expansion. -/
theorem finiteHalfCollectiveObservable_pow_ordered_words
    {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (A : ι → Matrix n n ℂ) (k : ℕ) :
    finiteHalfCollectiveObservable A ^ k =
      (((1 / 2 : ℝ) : ℂ) ^ k) •
        ∑ f : Fin k → ι, (List.ofFn (fun j => A (f j))).prod := by
  rw [finiteHalfCollectiveObservable, smul_pow, finiteCollectiveObservable_pow_ordered_words]
/-- At orders exceeding the number of sites, the distinct-site contribution vanishes exactly. -/
theorem collective_distinct_site_words_above_card_eq_zero
    {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (A : ι → Matrix n n ℂ) (k : ℕ) :
    (∑ f ∈ (Finset.univ : Finset (Fin (Fintype.card ι + k + 1) → ι)).filter
      (fun f => Function.Injective f), (List.ofFn (fun j => A (f j))).prod) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro f hf
  have hinj := (Finset.mem_filter.mp hf).2
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  omega
/-- Every even power of one longitudinal Pauli collapses to the identity. -/
theorem localZPauliObservable_even_power
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) (k : ℕ) :
    localZPauliObservable i ^ (2 * k) = 1 := by
  have h : localZPauliObservable i ^ 2 = 1 := by
    rw [pow_two]
    exact finitePauliMatrix_mul_self _
  rw [pow_mul, h, one_pow]
/-- Every odd power of one longitudinal Pauli collapses to that same single-site observable. -/
theorem localZPauliObservable_odd_power
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) (k : ℕ) :
    localZPauliObservable i ^ (2 * k + 1) = localZPauliObservable i := by
  rw [pow_succ, localZPauliObservable_even_power, one_mul]

end
end GaloisForLFunctions.HTGeometry

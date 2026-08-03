import Mathlib

/-!
# Integer values of `{-1,0,1}`-combinations of primitive `p`-th roots of unity

For a prime `p` and a primitive `p`-th root of unity `ω`, the only `ℚ`-linear relation among
`1, ω, …, ω^{p-1}` is the vanishing of their sum.  Consequently a combination
`∑_{m=1}^{p-1} d_m ω^m` is rational exactly when all the `d_m` agree, and then it equals `-d_1`.

Applied to differences of subset sums `σ_S = ∑_{k ∈ S} ω^{-k}`, this says that
`σ_S - σ_{S'} ∈ ℤ` forces `S = S'` or `{S, S'} = {∅, {1,…,p-1}}`: the `ℤ`-shift orbits of the subset
sums are the singletons together with one exceptional pair.
-/

namespace HTGeometry

open Polynomial

/-- A polynomial of degree below `p` vanishing at a primitive `p`-th root of unity is a constant
multiple of the `p`-th cyclotomic polynomial. -/
theorem eq_const_mul_cyclotomic_of_aeval_eq_zero {p : ℕ} [hp : Fact p.Prime] {ω : ℂ}
    (hω : IsPrimitiveRoot ω p) {Q : Polynomial ℚ} (hdeg : Q.natDegree < p)
    (hQ : Polynomial.aeval ω Q = 0) :
    ∃ lam : ℚ, Q = Polynomial.C lam * Polynomial.cyclotomic p ℚ := by
  classical
  have hppos : 0 < p := hp.out.pos
  haveI : NeZero (p : ℕ) := ⟨hppos.ne'⟩
  have hmin : Polynomial.cyclotomic p ℚ = minpoly ℚ ω :=
    hω.minpoly_eq_cyclotomic_of_irreducible (Polynomial.cyclotomic.irreducible_rat hppos)
  have hdvd : Polynomial.cyclotomic p ℚ ∣ Q := by
    rw [hmin]
    exact minpoly.dvd ℚ ω hQ
  obtain ⟨R, hR⟩ := hdvd
  rcases eq_or_ne Q 0 with hQ0 | hQ0
  · exact ⟨0, by simp [hQ0]⟩
  have hcycne : (Polynomial.cyclotomic p ℚ) ≠ 0 := Polynomial.cyclotomic_ne_zero p ℚ
  have hRne : R ≠ 0 := by
    intro h
    rw [h, mul_zero] at hR
    exact hQ0 hR
  have hdegcyc : (Polynomial.cyclotomic p ℚ).natDegree = p - 1 := by
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hp.out]
  have hsum : Q.natDegree = (p - 1) + R.natDegree := by
    rw [hR, Polynomial.natDegree_mul hcycne hRne, hdegcyc]
  have hR0 : R.natDegree = 0 := by omega
  obtain ⟨lam, hlam⟩ := Polynomial.natDegree_eq_zero.mp hR0
  exact ⟨lam, by rw [hR, ← hlam, mul_comm]⟩

/-- **Rationality forces equal coefficients.**  If `∑_{m=1}^{p-1} d_m ω^m` is the rational number
`c`, then all `d_m` are equal and `c = -d_m`. -/
theorem coeffs_eq_of_sum_pow_eq_ratCast {p : ℕ} [hp : Fact p.Prime] {ω : ℂ}
    (hω : IsPrimitiveRoot ω p) (d : ℕ → ℚ) (c : ℚ)
    (h : ∑ m ∈ Finset.Ico 1 p, ((d m : ℚ) : ℂ) * ω ^ m = ((c : ℚ) : ℂ)) :
    ∀ m ∈ Finset.Ico 1 p, ∀ n ∈ Finset.Ico 1 p, d m = d n := by
  classical
  have hppos : 0 < p := hp.out.pos
  set Q : Polynomial ℚ :=
    Polynomial.C (-c) + ∑ m ∈ Finset.Ico 1 p, Polynomial.C (d m) * Polynomial.X ^ m with hQdef
  have hdeg : Q.natDegree < p := by
    have h1 : (Polynomial.C (-c) : Polynomial ℚ).natDegree ≤ p - 1 := by
      simp [Polynomial.natDegree_C]
    have h2 : (∑ m ∈ Finset.Ico 1 p, Polynomial.C (d m) * Polynomial.X ^ m).natDegree
        ≤ p - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
      have hmlt : m < p := (Finset.mem_Ico.mp hm).2
      calc (Polynomial.C (d m) * Polynomial.X ^ m).natDegree
          ≤ (Polynomial.C (d m)).natDegree + (Polynomial.X ^ m : Polynomial ℚ).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ p - 1 := by
            rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
            omega
    have hle := Polynomial.natDegree_add_le (Polynomial.C (-c) : Polynomial ℚ)
      (∑ m ∈ Finset.Ico 1 p, Polynomial.C (d m) * Polynomial.X ^ m)
    have hfin : Q.natDegree ≤ p - 1 := le_trans hle (max_le h1 h2)
    omega
  have haeval : Polynomial.aeval ω Q = 0 := by
    rw [hQdef, map_add, map_sum]
    simp only [Polynomial.aeval_C, Polynomial.aeval_mul, Polynomial.aeval_X_pow, eq_ratCast]
    rw [h]
    push_cast
    ring
  obtain ⟨lam, hlam⟩ := eq_const_mul_cyclotomic_of_aeval_eq_zero hω hdeg haeval
  have hcoeff : ∀ m ∈ Finset.Ico 1 p, Q.coeff m = d m := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
    rw [hQdef, Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega),
      Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single m]
    · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    · intro n _ hnm
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hnm]
    · intro hnm
      exact absurd hm hnm
  have hlamcoeff : ∀ m ∈ Finset.Ico 1 p, Q.coeff m = lam := by
    intro m hm
    have hmlt : m < p := (Finset.mem_Ico.mp hm).2
    rw [hlam, Polynomial.coeff_C_mul, Polynomial.cyclotomic_prime ℚ p,
      Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single m]
    · simp [Polynomial.coeff_X_pow]
    · intro n _ hnm
      simp [Polynomial.coeff_X_pow, Ne.symm hnm]
    · intro hnm
      exact absurd (Finset.mem_range.mpr hmlt) hnm
  intro m hm n hn
  rw [← hcoeff m hm, ← hcoeff n hn, hlamcoeff m hm, hlamcoeff n hn]

private theorem ite_sub_ite_cases {α β : Prop} [Decidable α] [Decidable β] :
    ((if α then (1 : ℚ) else 0) - (if β then (1 : ℚ) else 0) = -1 ↔ (¬ α ∧ β))
      ∧ ((if α then (1 : ℚ) else 0) - (if β then (1 : ℚ) else 0) = 0 ↔ (α ↔ β))
      ∧ ((if α then (1 : ℚ) else 0) - (if β then (1 : ℚ) else 0) = 1 ↔ (α ∧ ¬ β)) := by
  by_cases hα : α <;> by_cases hβ : β <;> norm_num [hα, hβ]

/-- **The `ℤ`-shift orbits of subset sums.**  For a prime `p` and a primitive `p`-th root `ω`, two
subset sums `∑_{m ∈ M} ω^m` over `M ⊆ {1,…,p-1}` differ by an integer only in the trivial case
`M = M'` and in the single exceptional pair `{∅, {1,…,p-1}}`. -/
theorem subsetSum_sub_eq_intCast_cases {p : ℕ} [hp : Fact p.Prime] {ω : ℂ}
    (hω : IsPrimitiveRoot ω p) {M M' : Finset ℕ} (hM : M ⊆ Finset.Ico 1 p)
    (hM' : M' ⊆ Finset.Ico 1 p) {n : ℤ}
    (h : (∑ m ∈ M, ω ^ m) - (∑ m ∈ M', ω ^ m) = (n : ℂ)) :
    M = M' ∨ (M = ∅ ∧ M' = Finset.Ico 1 p) ∨ (M = Finset.Ico 1 p ∧ M' = ∅) := by
  classical
  have hppos : 0 < p := hp.out.pos
  have hp2 : 2 ≤ p := hp.out.two_le
  set d : ℕ → ℚ := fun m => (if m ∈ M then (1 : ℚ) else 0) - (if m ∈ M' then (1 : ℚ) else 0)
    with hddef
  have hexpand : ∀ (T : Finset ℕ), T ⊆ Finset.Ico 1 p →
      ∑ m ∈ Finset.Ico 1 p, ((if m ∈ T then (1 : ℚ) else 0) : ℂ) * ω ^ m = ∑ m ∈ T, ω ^ m := by
    intro T hT
    rw [← Finset.sum_subset hT (fun x _ hx => by rw [if_neg hx]; simp)]
    exact Finset.sum_congr rfl fun m hm => by rw [if_pos hm]; simp
  have hsum : ∑ m ∈ Finset.Ico 1 p, ((d m : ℚ) : ℂ) * ω ^ m = ((n : ℚ) : ℂ) := by
    have hterm : ∀ m : ℕ, ((d m : ℚ) : ℂ) * ω ^ m
        = ((if m ∈ M then (1 : ℚ) else 0) : ℂ) * ω ^ m
          - ((if m ∈ M' then (1 : ℚ) else 0) : ℂ) * ω ^ m := by
      intro m
      simp only [hddef]
      by_cases hmM : m ∈ M <;> by_cases hmM' : m ∈ M' <;> simp [hmM, hmM']
    rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_sub_distrib,
      hexpand M hM, hexpand M' hM', h]
    push_cast
    ring
  have hall := coeffs_eq_of_sum_pow_eq_ratCast hω d ((n : ℚ)) hsum
  have h1mem : (1 : ℕ) ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩
  have hconst : ∀ m ∈ Finset.Ico 1 p, d m = d 1 := fun m hm => hall m hm 1 h1mem
  have hd : d 1 = -1 ∨ d 1 = 0 ∨ d 1 = 1 := by
    simp only [hddef]
    by_cases h1M : (1 : ℕ) ∈ M <;> by_cases h1M' : (1 : ℕ) ∈ M' <;> simp [h1M, h1M']
  rcases hd with hd | hd | hd
  · right; left
    have hforall : ∀ m ∈ Finset.Ico 1 p, m ∉ M ∧ m ∈ M' := by
      intro m hm
      have hcm := hconst m hm
      rw [hd] at hcm
      simp only [hddef] at hcm
      exact ite_sub_ite_cases.1.mp hcm
    exact ⟨Finset.eq_empty_of_forall_notMem fun m hmM => (hforall m (hM hmM)).1 hmM,
      Finset.Subset.antisymm hM' fun m hm => (hforall m hm).2⟩
  · left
    refine Finset.ext fun m => ?_
    constructor
    · intro hmM
      have hcm := hconst m (hM hmM)
      rw [hd] at hcm
      simp only [hddef] at hcm
      exact (ite_sub_ite_cases.2.1.mp hcm).mp hmM
    · intro hmM'
      have hcm := hconst m (hM' hmM')
      rw [hd] at hcm
      simp only [hddef] at hcm
      exact (ite_sub_ite_cases.2.1.mp hcm).mpr hmM'
  · right; right
    have hforall : ∀ m ∈ Finset.Ico 1 p, m ∈ M ∧ m ∉ M' := by
      intro m hm
      have hcm := hconst m hm
      rw [hd] at hcm
      simp only [hddef] at hcm
      exact ite_sub_ite_cases.2.2.mp hcm
    exact ⟨Finset.Subset.antisymm hM fun m hm => (hforall m hm).1,
      Finset.eq_empty_of_forall_notMem fun m hmM' => (hforall m (hM' hmM')).2 hmM'⟩

end HTGeometry



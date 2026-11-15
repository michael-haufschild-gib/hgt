import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheCubicStepanovPolynomialIsIndependent
import GaloisForLFunctions.RHTower.StepanovCount

/-!
# Stepanov's count for a character of order three

Let `|E| = Q = p^n = 3N + 1` and `h` squarefree of degree `D ≥ 1`. The auxiliary polynomial
`R = Σ_{j<J} (r_j + s_j h^N + t_j h^{2N}) X^{Qj}` (`auxPoly3`) with coefficient data in the kernel of
`ℓ` linear conditions (`exists_nonzero_solution_of_finrank`, `3JK` unknowns) vanishes to order `ℓ`
at every `x` with `h(x)^N = ε`: there `h(x)^k (D^{(k)}R)(x) = Φ_k(x)` (`eval_hasseDeriv_auxPoly3`,
through `eval_hasseDeriv_mul_pow` for one level). `R ≠ 0` by `cubic_stepanov_independence`, so

  `ℓ · #{x : h(x) ≠ 0, h(x)^N = ε} ≤ (K − 1) + 2N·D + Q(J − 1)`  (`cubic_stepanov_count`).
-/

open Polynomial Finset

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open RHTower.Stepanov

variable {E : Type*} [Field E]

/-- An underdetermined homogeneous system of polynomial conditions has a nonzero solution. -/
theorem exists_nonzero_solution_of_finrank {V : Type*} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] {ℓ : ℕ} (M : Fin ℓ → ℕ) (Φ : Fin ℓ → V → E[X])
    (hΦlin : ∀ k u v (t : E), Φ k (u + t • v) = Φ k u + C t * Φ k v)
    (hΦdeg : ∀ k u, (Φ k u).natDegree < M k ∨ Φ k u = 0)
    (hdim : ∑ k, M k < Module.finrank E V) :
    ∃ u ≠ 0, ∀ k, Φ k u = 0 := by
  let L : V →ₗ[E] ((k : Fin ℓ) → Fin (M k) → E) :=
    { toFun := fun u k m => (Φ k u).coeff m
      map_add' := by
        intro u v; funext k m
        have := hΦlin k u v 1
        simp only [one_smul, C_1, one_mul] at this
        simp [this]
      map_smul' := by
        intro t u; funext k m
        have := hΦlin k 0 u t
        have h0 : Φ k 0 = 0 := by
          have := hΦlin k 0 0 1
          simp at this
          linear_combination this
        simp only [zero_add, h0] at this
        simp [this, coeff_C_mul] }
  have hfin : Module.finrank E ((k : Fin ℓ) → Fin (M k) → E) < Module.finrank E V := by
    rw [Module.finrank_pi_fintype]
    simpa only [Module.finrank_fin_fun] using hdim
  obtain ⟨u, hu, hu0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hfin)
  refine ⟨u, hu0, fun k => ?_⟩
  have hc : ∀ m : Fin (M k), (Φ k u).coeff m = 0 := fun m => by
    have := congrFun (congrFun (LinearMap.mem_ker.mp hu) k) m
    simpa [L] using this
  rcases hΦdeg k u with hd | hz
  · ext m
    simp only [coeff_zero]
    by_cases hm : m < M k
    · exact hc ⟨m, hm⟩
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  · exact hz

/-- Coefficient data for three levels. -/
abbrev Data3 (E : Type*) (J K : ℕ) := (Fin J → Fin K → E) × (Fin J → Fin K → E) × (Fin J → Fin K → E)

theorem finrank_data3 (J K : ℕ) : Module.finrank E (Data3 E J K) = 3 * (J * K) := by
  simp only [Data3, Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_fin_fun,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- **One level of the Hasse derivative.** For `k ≤ M`,
`h^k D^{(k)}(r h^M) = h^M Σ_{i ≤ k} h^{k−i} P_{M,i} D^{(k−i)} r` at every point, `D^{(i)} h^M = h^{M−i} P_{M,i}`. -/
theorem eval_hasseDeriv_mul_pow (h r : E[X]) {M k : ℕ} (hh : h ≠ 0) (hkM : k ≤ M) (x : E) :
    (h.eval x) ^ k * (hasseDeriv k (r * h ^ M)).eval x =
      (h.eval x) ^ M * ∑ i ∈ range (k + 1),
        (h ^ (k - i) * derivFactor h M i * hasseDeriv (k - i) r).eval x := by
  rw [hasseDeriv_mul, eval_finsetSum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Finset.sum_range_reflect, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have e1 : k + 1 - 1 - i = k - i := by omega
  have e2 : k - (k - i) = i := by omega
  rw [e1, e2, (derivFactor_spec h M hh (i := i) (by omega)).1]
  simp only [eval_mul, eval_pow]
  have e3 : (h.eval x) ^ k * (h.eval x) ^ (M - i) = (h.eval x) ^ M * (h.eval x) ^ (k - i) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  linear_combination (hasseDeriv (k - i) r).eval x * (derivFactor h M i).eval x * e3

section setup

variable (h : E[X]) (N : ℕ) (ε : E)

/-- The level sum `Σ_{i ≤ k} h^{k−i} P_{M,i} D^{(k−i)} r`. -/
noncomputable def levelSum (M k : ℕ) (r : E[X]) : E[X] :=
  ∑ i ∈ range (k + 1), h ^ (k - i) * derivFactor h M i * hasseDeriv (k - i) r

theorem levelSum_linear (M k : ℕ) (r s : E[X]) (t : E) :
    levelSum h M k (r + C t * s) = levelSum h M k r + C t * levelSum h M k s := by
  unfold levelSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, ← smul_eq_C_mul, map_smul, smul_eq_C_mul]
  ring

/-- Stepanov's polynomials `Φ_k` for three levels. -/
noncomputable def phi3 {J K : ℕ} (k : ℕ) (u : Data3 E J K) : E[X] :=
  ∑ j : Fin J, (h ^ k * hasseDeriv k (ofCoeffs (u.1 j)) + C ε * levelSum h N k (ofCoeffs (u.2.1 j)) +
    C (ε ^ 2) * levelSum h (2 * N) k (ofCoeffs (u.2.2 j))) * X ^ (j : ℕ)

theorem phi3_linear {J K : ℕ} (k : ℕ) (u v : Data3 E J K) (t : E) :
    phi3 h N ε k (u + t • v) = phi3 h N ε k u + C t * phi3 h N ε k v := by
  unfold phi3
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
    ofCoeffs_linear, levelSum_linear]
  rw [map_add, ← smul_eq_C_mul, map_smul, smul_eq_C_mul]
  ring

theorem levelSum_natDegree_le (hh : h ≠ 0) {M k K : ℕ} (hK : 0 < K) (hkM : k ≤ M) {r : E[X]}
    (hr : r.natDegree < K) : (levelSum h M k r).natDegree ≤ k * h.natDegree + (K - 1) := by
  unfold levelSum
  apply natDegree_sum_le_of_forall_le
  intro i hi
  rw [Finset.mem_range] at hi
  have hP := (derivFactor_spec h M hh (i := i) (by omega)).2
  have hs : (hasseDeriv (k - i) r).natDegree ≤ K - 1 :=
    (natDegree_hasseDeriv_le _ _).trans (by omega)
  refine natDegree_mul_le.trans ?_
  refine (Nat.add_le_add (natDegree_mul_le.trans (Nat.add_le_add (le_of_eq (natDegree_pow _ _))
    hP)) hs).trans ?_
  have : (k - i) * h.natDegree + i * h.natDegree = k * h.natDegree := by
    rw [← add_mul, Nat.sub_add_cancel (by omega)]
  omega

theorem phi3_natDegree_le (hh : h ≠ 0) {J K k : ℕ} (hK : 0 < K) (hkN : k ≤ N) (u : Data3 E J K) :
    (phi3 h N ε k u).natDegree ≤ k * h.natDegree + (K - 1) + (J - 1) := by
  unfold phi3
  apply natDegree_sum_le_of_forall_le
  intro j _
  refine natDegree_mul_le.trans ?_
  have hX : (X ^ (j : ℕ) : E[X]).natDegree ≤ J - 1 := by
    rw [natDegree_X_pow]; have := j.isLt; omega
  have hr : (hasseDeriv k (ofCoeffs (u.1 j))).natDegree ≤ K - 1 :=
    (natDegree_hasseDeriv_le _ _).trans (by have := ofCoeffs_natDegree_lt hK (u.1 j); omega)
  have h1 : (h ^ k * hasseDeriv k (ofCoeffs (u.1 j))).natDegree ≤ k * h.natDegree + (K - 1) := by
    refine natDegree_mul_le.trans (Nat.add_le_add ?_ hr)
    rw [natDegree_pow]
  have h2 : (C ε * levelSum h N k (ofCoeffs (u.2.1 j))).natDegree ≤ k * h.natDegree + (K - 1) :=
    (natDegree_C_mul_le _ _).trans
      (levelSum_natDegree_le h hh hK hkN (ofCoeffs_natDegree_lt hK _))
  have h3 : (C (ε ^ 2) * levelSum h (2 * N) k (ofCoeffs (u.2.2 j))).natDegree ≤
      k * h.natDegree + (K - 1) :=
    (natDegree_C_mul_le _ _).trans
      (levelSum_natDegree_le h hh hK (by omega) (ofCoeffs_natDegree_lt hK _))
  have h12 := natDegree_add_le_of_degree_le h1 h2
  exact (Nat.add_le_add (natDegree_add_le_of_degree_le h12 h3) hX).trans (by omega)

/-- Stepanov's auxiliary polynomial with three levels. -/
noncomputable def auxPoly3 {J K : ℕ} (Q : ℕ) (u : Data3 E J K) : E[X] :=
  ∑ j : Fin J, (ofCoeffs (u.1 j) + ofCoeffs (u.2.1 j) * h ^ N + ofCoeffs (u.2.2 j) * h ^ (2 * N)) *
    (X ^ Q) ^ (j : ℕ)

theorem eval_hasseDeriv_auxPoly3 {p n : ℕ} [Fact p.Prime] [CharP E p] (hh : h ≠ 0)
    {J K k : ℕ} (hkQ : k < p ^ n) (hkN : k ≤ N) (u : Data3 E J K) {x : E} (hx : x ^ (p ^ n) = x)
    (hxε : (h.eval x) ^ N = ε) :
    (h.eval x) ^ k * (hasseDeriv k (auxPoly3 h N (p ^ n) u)).eval x = (phi3 h N ε k u).eval x := by
  unfold auxPoly3 phi3
  rw [map_sum, eval_finsetSum, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hasseDeriv_mul_X_pow (p := p) hkQ, eval_mul, eval_mul, eval_pow, eval_pow, eval_X, hx,
    map_add, map_add, eval_add, eval_add, eval_add, eval_add, eval_mul, eval_mul, eval_mul, eval_pow,
    eval_C, eval_C]
  have l1 := eval_hasseDeriv_mul_pow h (ofCoeffs (u.2.1 j)) hh hkN x
  have l2 := eval_hasseDeriv_mul_pow h (ofCoeffs (u.2.2 j)) hh (M := 2 * N) (by omega) x
  have hε2 : (h.eval x) ^ (2 * N) = ε ^ 2 := by rw [mul_comm, pow_mul, hxε]
  rw [hxε] at l1
  rw [hε2] at l2
  simp only [levelSum, eval_finsetSum]
  linear_combination x ^ (j : ℕ) * l1 + x ^ (j : ℕ) * l2

end setup

/-- **Stepanov's counting theorem for a character of order three.** Let `|E| = p^n = 3N + 1`, `h`
squarefree of degree `D ≥ 1` and `ε ∈ E`. If `ℓ ≤ N`, `3(K − 1) + 2D < p^n` and
`Σ_{k<ℓ} (K + kD + J) < 3JK`, then `ℓ · #{x : h(x) ≠ 0, h(x)^N = ε} ≤ (K − 1) + 2N·D + p^n(J − 1)`. -/
theorem cubic_stepanov_count [Fintype E] [DecidableEq E] {p n : ℕ} [Fact p.Prime] [CharP E p]
    (hcard : Fintype.card E = p ^ n) {h : E[X]} (hsq : Squarefree h) (hdeg : 1 ≤ h.natDegree)
    {N ℓ J K : ℕ} (hQ : p ^ n = 3 * N + 1) (hℓN : ℓ ≤ N) (hK0 : 0 < K)
    (hK : 3 * (K - 1) + 2 * h.natDegree < p ^ n)
    (hdim : ∑ k : Fin ℓ, (K + (k : ℕ) * h.natDegree + J) < 3 * (J * K)) (ε : E) :
    ℓ * (univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = ε)).card ≤
      (K - 1) + 2 * N * h.natDegree + p ^ n * (J - 1) := by
  have hh : h ≠ 0 := by rintro rfl; simp at hdeg
  set T := univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = ε)
  obtain ⟨u, hu0, hu⟩ := exists_nonzero_solution_of_finrank (E := E) (V := Data3 E J K)
    (M := fun k : Fin ℓ => K + (k : ℕ) * h.natDegree + J)
    (fun k v => phi3 h N ε (k : ℕ) v) (fun k v w t => phi3_linear h N ε k v w t)
    (fun k v => Or.inl (lt_of_le_of_lt (phi3_natDegree_le h N ε hh hK0 (by omega) v) (by omega)))
    (by rw [finrank_data3]; exact hdim)
  set R := auxPoly3 h N (p ^ n) u
  have hR : R ≠ 0 := by
    intro hR0
    have hind := cubic_stepanov_independence hsq hdeg (N := N) (K := K) (J := J)
      (by rw [hcard, hQ]) (by rw [hcard]; exact hK) (fun j => ofCoeffs (u.1 j))
      (fun j => ofCoeffs (u.2.1 j)) (fun j => ofCoeffs (u.2.2 j))
      (fun j => ofCoeffs_natDegree_lt hK0 _) (fun j => ofCoeffs_natDegree_lt hK0 _)
      (fun j => ofCoeffs_natDegree_lt hK0 _) (by rw [hcard]; exact hR0)
    apply hu0
    ext j a
    · exact congrFun (ofCoeffs_eq_zero (hind j).1) a
    · exact congrFun (ofCoeffs_eq_zero (hind j).2.1) a
    · exact congrFun (ofCoeffs_eq_zero (hind j).2.2) a
  have hroot : ∀ x ∈ T, (X - C x) ^ ℓ ∣ R := by
    intro x hx
    rw [Finset.mem_filter] at hx
    apply pow_dvd_of_hasseDeriv_eval_eq_zero
    intro k hk
    have hxq : x ^ (p ^ n) = x := by rw [← hcard]; exact FiniteField.pow_card x
    have hid := eval_hasseDeriv_auxPoly3 h N ε hh (p := p) (n := n) (J := J) (K := K) (k := k)
      (by omega) (by omega) u hxq hx.2.2
    rw [hu ⟨k, hk⟩] at hid
    simp only [eval_zero] at hid
    exact (mul_eq_zero.mp hid).resolve_left (pow_ne_zero _ hx.2.1)
  have hprod : (∏ x ∈ T, (X - C x) ^ ℓ) ∣ R := by
    apply Finset.prod_dvd_of_coprime
    · intro x _ y _ hxy
      exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hxy).isUnit).pow
    · exact hroot
  have hdegprod : (∏ x ∈ T, (X - C x) ^ ℓ : E[X]).natDegree = ℓ * T.card := by
    rw [natDegree_prod _ _ (fun x _ => pow_ne_zero _ (X_sub_C_ne_zero x))]
    simp [natDegree_pow, mul_comm]
  have hle := natDegree_le_of_dvd hprod hR
  rw [hdegprod] at hle
  refine hle.trans ?_
  unfold R auxPoly3
  apply natDegree_sum_le_of_forall_le
  intro j _
  refine natDegree_mul_le.trans ?_
  have hj := j.isLt
  have h1 : (ofCoeffs (u.1 j) + ofCoeffs (u.2.1 j) * h ^ N +
      ofCoeffs (u.2.2 j) * h ^ (2 * N)).natDegree ≤ (K - 1) + 2 * N * h.natDegree := by
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
    · have := ofCoeffs_natDegree_lt hK0 (u.1 j); omega
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_pow]
      have := ofCoeffs_natDegree_lt hK0 (u.2.1 j)
      nlinarith
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_pow]
      have := ofCoeffs_natDegree_lt hK0 (u.2.2 j)
      nlinarith
  have h2 : ((X ^ (p ^ n)) ^ (j : ℕ) : E[X]).natDegree ≤ p ^ n * (J - 1) := by
    rw [← pow_mul, natDegree_X_pow]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

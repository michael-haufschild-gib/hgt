import GaloisForLFunctions.RHTower.StepanovHyperelliptic

/-!
# Stepanov's counting theorem for hyperelliptic curves

The auxiliary polynomial `R = Σ_{j<J} (r_j + s_j h^N) X^{Qj}` (`auxPoly`) with coefficient data solving an
underdetermined homogeneous linear system (`exists_nonzero_solution`) is chosen so that the polynomials
`Φ_k` (`phi`) vanish for `k < ℓ`. At each `x` with `h(x) ≠ 0`, `h(x)^N = ε`,
`h(x)^k (D^{(k)}R)(x) = Φ_k(x)` (`eval_hasseDeriv_auxPoly`), so `x` is a root of multiplicity `ℓ`;
`R ≠ 0` by `stepanov_independence`. Counting degrees gives
`ℓ · #{x : h(x) ≠ 0, h(x)^N = ε} ≤ (K-1) + N·deg h + Q(J-1)` (`stepanov_count`).
-/

open Polynomial Finset

namespace GaloisForLFunctions.RHTower.Stepanov

variable {E : Type*} [Field E]

/-- Polynomial with prescribed coefficients below `K`. -/
noncomputable def ofCoeffs {K : ℕ} (c : Fin K → E) : E[X] := ∑ a : Fin K, C (c a) * X ^ (a : ℕ)

theorem ofCoeffs_natDegree_lt {K : ℕ} (hK : 0 < K) (c : Fin K → E) : (ofCoeffs c).natDegree < K := by
  unfold ofCoeffs
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := K - 1) ?_) (by omega)
  intro a _
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem ofCoeffs_coeff {K : ℕ} (c : Fin K → E) (a : Fin K) : (ofCoeffs c).coeff a = c a := by
  unfold ofCoeffs
  rw [finsetSum_coeff, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [coeff_C_mul_X_pow, if_neg]
    intro h; exact hb (Fin.ext h.symm)
  · simp

theorem ofCoeffs_linear {K : ℕ} (c d : Fin K → E) (t : E) :
    ofCoeffs (c + t • d) = ofCoeffs c + C t * ofCoeffs d := by
  unfold ofCoeffs
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, C_add, C_mul]
  ring

theorem ofCoeffs_eq_zero {K : ℕ} {c : Fin K → E} (h : ofCoeffs c = 0) : c = 0 := by
  funext a
  have := ofCoeffs_coeff c a
  rw [h, coeff_zero] at this
  exact this.symm

/-- The linear map sending coefficient data to the coefficients of a linear polynomial expression. -/
theorem exists_nonzero_solution {J K ℓ : ℕ} (M : Fin ℓ → ℕ)
    (Φ : Fin ℓ → (Fin J → Fin K → E) × (Fin J → Fin K → E) → E[X])
    (hΦlin : ∀ k u v (t : E), Φ k (u + t • v) = Φ k u + C t * Φ k v)
    (hΦdeg : ∀ k u, (Φ k u).natDegree < M k ∨ Φ k u = 0)
    (hdim : ∑ k, M k < 2 * (J * K)) :
    ∃ u ≠ 0, ∀ k, Φ k u = 0 := by
  let L : ((Fin J → Fin K → E) × (Fin J → Fin K → E)) →ₗ[E] ((k : Fin ℓ) → Fin (M k) → E) :=
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
  have hfin : Module.finrank E ((k : Fin ℓ) → Fin (M k) → E) <
      Module.finrank E ((Fin J → Fin K → E) × (Fin J → Fin K → E)) := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    simp only [Module.finrank_fin_fun, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    linarith [hdim]
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hfin)
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

section setup

variable (h : E[X]) (N : ℕ) (ε : E)

open Classical in
/-- The polynomials `P_i` with `D^{(i)}(h^N) = h^{N-i} P_i`. -/
noncomputable def derivFactor (i : ℕ) : E[X] :=
  if hi : i ≤ N ∧ h ≠ 0 then Classical.choose (hasseDeriv_pow_eq hi.2 N i hi.1) else 0

theorem derivFactor_spec (hh : h ≠ 0) {i : ℕ} (hi : i ≤ N) :
    hasseDeriv i (h ^ N) = h ^ (N - i) * derivFactor h N i ∧
      (derivFactor h N i).natDegree ≤ i * h.natDegree := by
  unfold derivFactor
  rw [dif_pos ⟨hi, hh⟩]
  exact Classical.choose_spec (hasseDeriv_pow_eq hh N i hi)

/-- Stepanov's polynomials `Φ_k`. -/
noncomputable def phi {J K : ℕ} (k : ℕ) (u : (Fin J → Fin K → E) × (Fin J → Fin K → E)) : E[X] :=
  ∑ j : Fin J, (h ^ k * hasseDeriv k (ofCoeffs (u.1 j)) +
    C ε * ∑ i ∈ range (k + 1), h ^ (k - i) * derivFactor h N i *
      hasseDeriv (k - i) (ofCoeffs (u.2 j))) * X ^ (j : ℕ)

theorem phi_linear {J K : ℕ} (k : ℕ) (u v : (Fin J → Fin K → E) × (Fin J → Fin K → E)) (t : E) :
    phi h N ε k (u + t • v) = phi h N ε k u + C t * phi h N ε k v := by
  unfold phi
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
    Pi.smul_apply]
  have e1 : ofCoeffs (u.1 j + t • v.1 j) = ofCoeffs (u.1 j) + C t * ofCoeffs (v.1 j) :=
    ofCoeffs_linear _ _ _
  have e2 : ofCoeffs (u.2 j + t • v.2 j) = ofCoeffs (u.2 j) + C t * ofCoeffs (v.2 j) :=
    ofCoeffs_linear _ _ _
  rw [e1, e2]
  have hd : ∀ m (f g : E[X]), hasseDeriv m (f + C t * g) = hasseDeriv m f + C t * hasseDeriv m g := by
    intro m f g
    rw [map_add, ← smul_eq_C_mul, map_smul, smul_eq_C_mul]
  simp_rw [hd]
  have hs : (∑ i ∈ range (k + 1), h ^ (k - i) * derivFactor h N i *
      (hasseDeriv (k - i) (ofCoeffs (u.2 j)) + C t * hasseDeriv (k - i) (ofCoeffs (v.2 j)))) =
      (∑ i ∈ range (k + 1), h ^ (k - i) * derivFactor h N i * hasseDeriv (k - i) (ofCoeffs (u.2 j))) +
        C t * ∑ i ∈ range (k + 1), h ^ (k - i) * derivFactor h N i *
          hasseDeriv (k - i) (ofCoeffs (v.2 j)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hs]
  ring

theorem phi_natDegree_le (hh : h ≠ 0) {J K k : ℕ} (hK : 0 < K) (hkN : k ≤ N)
    (u : (Fin J → Fin K → E) × (Fin J → Fin K → E)) :
    (phi h N ε k u).natDegree ≤ k * h.natDegree + (K - 1) + (J - 1) := by
  unfold phi
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
  have h2 : (C ε * ∑ i ∈ range (k + 1), h ^ (k - i) * derivFactor h N i *
      hasseDeriv (k - i) (ofCoeffs (u.2 j))).natDegree ≤ k * h.natDegree + (K - 1) := by
    refine natDegree_C_mul_le _ _ |>.trans ?_
    apply natDegree_sum_le_of_forall_le
    intro i hi
    rw [Finset.mem_range] at hi
    have hP := (derivFactor_spec h N hh (i := i) (by omega)).2
    have hs : (hasseDeriv (k - i) (ofCoeffs (u.2 j))).natDegree ≤ K - 1 :=
      (natDegree_hasseDeriv_le _ _).trans (by have := ofCoeffs_natDegree_lt hK (u.2 j); omega)
    refine natDegree_mul_le.trans ?_
    refine (Nat.add_le_add (natDegree_mul_le.trans (Nat.add_le_add (le_of_eq (natDegree_pow _ _))
      hP)) hs).trans ?_
    have : (k - i) * h.natDegree + i * h.natDegree = k * h.natDegree := by
      rw [← add_mul, Nat.sub_add_cancel (by omega)]
    omega
  exact (Nat.add_le_add (natDegree_add_le_of_degree_le h1 h2) hX).trans (by omega)

/-- Stepanov's auxiliary polynomial. -/
noncomputable def auxPoly {J K : ℕ} (Q : ℕ) (u : (Fin J → Fin K → E) × (Fin J → Fin K → E)) : E[X] :=
  ∑ j : Fin J, (ofCoeffs (u.1 j) + ofCoeffs (u.2 j) * h ^ N) * (X ^ Q) ^ (j : ℕ)

theorem eval_hasseDeriv_auxPoly {p n : ℕ} [Fact p.Prime] [CharP E p] (hh : h ≠ 0)
    {J K k : ℕ} (hkQ : k < p ^ n) (hkN : k ≤ N)
    (u : (Fin J → Fin K → E) × (Fin J → Fin K → E)) {x : E} (hx : x ^ (p ^ n) = x)
    (hxε : (h.eval x) ^ N = ε) :
    (h.eval x) ^ k * (hasseDeriv k (auxPoly h N (p ^ n) u)).eval x = (phi h N ε k u).eval x := by
  unfold auxPoly phi
  rw [map_sum, eval_finsetSum, eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hasseDeriv_mul_X_pow (p := p) hkQ, eval_mul, eval_mul, eval_pow, eval_pow, eval_X, hx]
  rw [map_add, hasseDeriv_mul, eval_add, eval_add, eval_mul, eval_mul, eval_pow, eval_C,
    eval_finsetSum, eval_finsetSum]
  -- reindex the Leibniz sum and substitute `D^{(i)} h^N = h^{N-i} P_i`
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Finset.sum_range_reflect]
  have hterm : ∀ i ∈ range (k + 1),
      (h.eval x) ^ k * ((hasseDeriv (k + 1 - 1 - i) (ofCoeffs (u.2 j)) *
        hasseDeriv (k - (k + 1 - 1 - i)) (h ^ N)).eval x) =
      ε * (h ^ (k - i) * derivFactor h N i * hasseDeriv (k - i) (ofCoeffs (u.2 j))).eval x := by
    intro i hi
    rw [Finset.mem_range] at hi
    have e1 : k + 1 - 1 - i = k - i := by omega
    have e2 : k - (k - i) = i := by omega
    rw [e1, e2, (derivFactor_spec h N hh (i := i) (by omega)).1]
    simp only [eval_mul, eval_pow]
    rw [← hxε]
    have : (h.eval x) ^ k * (h.eval x) ^ (N - i) = (h.eval x) ^ N * (h.eval x) ^ (k - i) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    linear_combination (hasseDeriv (k - i) (ofCoeffs (u.2 j))).eval x *
      (derivFactor h N i).eval x * this
  simp only [Nat.succ_eq_add_one] at *
  rw [eval_pow, eval_X]
  have hsum : (h.eval x) ^ k * (∑ i ∈ range (k + 1), ((hasseDeriv (k + 1 - 1 - i) (ofCoeffs (u.2 j)) *
      hasseDeriv (k - (k + 1 - 1 - i)) (h ^ N)).eval x)) =
      ε * ∑ i ∈ range (k + 1), (h ^ (k - i) * derivFactor h N i *
        hasseDeriv (k - i) (ofCoeffs (u.2 j))).eval x := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  linear_combination (x ^ (j : ℕ)) * hsum

end setup

/-- **Stepanov's counting theorem (hyperelliptic).** Let `E` be a finite field with `|E| = p^n = 2N+1`,
`h` squarefree of degree `D ≥ 1`, `ε ∈ E`. If `ℓ ≤ N`, `2(K-1) + D < p^n` and
`Σ_{k<ℓ} (K + kD + J) < 2JK`, then `ℓ · #{x : h(x) ≠ 0, h(x)^N = ε} ≤ (K-1) + N·D + p^n (J-1)`. -/
theorem stepanov_count [Fintype E] [DecidableEq E] {p n : ℕ} [Fact p.Prime] [CharP E p]
    (hcard : Fintype.card E = p ^ n) {h : E[X]} (hsq : Squarefree h) (hdeg : 1 ≤ h.natDegree)
    {N ℓ J K : ℕ} (hQ : p ^ n = 2 * N + 1) (hℓN : ℓ ≤ N) (hK0 : 0 < K)
    (hK : 2 * (K - 1) + h.natDegree < p ^ n)
    (hdim : ∑ k : Fin ℓ, (K + (k : ℕ) * h.natDegree + J) < 2 * (J * K)) (ε : E) :
    ℓ * (univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = ε)).card ≤
      (K - 1) + N * h.natDegree + p ^ n * (J - 1) := by
  have hh : h ≠ 0 := by rintro rfl; simp at hdeg
  set T := univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = ε)
  -- 1. a nonzero solution of the linear system
  obtain ⟨u, hu0, hu⟩ := exists_nonzero_solution (E := E) (J := J) (K := K)
    (M := fun k : Fin ℓ => K + (k : ℕ) * h.natDegree + J)
    (fun k v => phi h N ε (k : ℕ) v) (fun k v w t => phi_linear h N ε k v w t)
    (fun k v => Or.inl (lt_of_le_of_lt (phi_natDegree_le h N ε hh hK0 (by omega) v) (by omega)))
    hdim
  set R := auxPoly h N (p ^ n) u
  -- 2. the auxiliary polynomial is nonzero
  have hR : R ≠ 0 := by
    intro hR0
    have hind := stepanov_independence hsq hdeg (N := N) (K := K) (J := J)
      (by rw [hcard, hQ]) (by rw [hcard]; exact hK) (fun j => ofCoeffs (u.1 j))
      (fun j => ofCoeffs (u.2 j)) (fun j => ofCoeffs_natDegree_lt hK0 _)
      (fun j => ofCoeffs_natDegree_lt hK0 _) (by rw [hcard]; exact hR0)
    apply hu0
    ext j a
    · exact congrFun (ofCoeffs_eq_zero (hind j).1) a
    · exact congrFun (ofCoeffs_eq_zero (hind j).2) a
  -- 3. every point of `T` is a root of multiplicity `ℓ`
  have hroot : ∀ x ∈ T, (X - C x) ^ ℓ ∣ R := by
    intro x hx
    rw [Finset.mem_filter] at hx
    apply pow_dvd_of_hasseDeriv_eval_eq_zero
    intro k hk
    have hxq : x ^ (p ^ n) = x := by rw [← hcard]; exact FiniteField.pow_card x
    have hid := eval_hasseDeriv_auxPoly h N ε hh (p := p) (n := n) (J := J) (K := K) (k := k)
      (by omega) (by omega) u hxq hx.2.2
    rw [hu ⟨k, hk⟩] at hid
    simp only [eval_zero] at hid
    exact (mul_eq_zero.mp hid).resolve_left (pow_ne_zero _ hx.2.1)
  -- 4. product of the root factors divides `R`
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
  -- 5. degree of the auxiliary polynomial
  refine hle.trans ?_
  unfold R auxPoly
  apply natDegree_sum_le_of_forall_le
  intro j _
  refine natDegree_mul_le.trans ?_
  have hj := j.isLt
  have h1 : (ofCoeffs (u.1 j) + ofCoeffs (u.2 j) * h ^ N).natDegree ≤ (K - 1) + N * h.natDegree := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · have := ofCoeffs_natDegree_lt hK0 (u.1 j); omega
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_pow]
      have := ofCoeffs_natDegree_lt hK0 (u.2 j); omega
  have h2 : ((X ^ (p ^ n)) ^ (j : ℕ) : E[X]).natDegree ≤ p ^ n * (J - 1) := by
    rw [← pow_mul, natDegree_X_pow]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

end GaloisForLFunctions.RHTower.Stepanov

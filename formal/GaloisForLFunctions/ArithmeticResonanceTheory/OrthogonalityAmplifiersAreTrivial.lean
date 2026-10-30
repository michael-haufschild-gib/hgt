import Mathlib

/-!
# Orthogonality amplifiers are trivial: the rank law

A family `X` of unimodular twists `w x : Fin r → ℂ` acts on a weighted sum
`A_x = Σ_i a_i w_x(i)` with `a_i ≥ 0`; for `ℤ` at scale `y` the index runs over the `r = π(y)`
primes and the twists are characters `p^{iτ}` or `χ(p)`. The family is **Brauer at level `k`**
(`IsBrauer`) when its degree-`k` monomials `w_x^m = Π_{i ∈ m} w_x(i)`, one for each multiset `m`
of size `k`, are orthogonal over the family. This is the only mechanism by which orthogonality
evaluates a `2k`-th moment: the diagonal survives, nothing else does.

* **Counting** (`card_sym_le_card_of_isBrauer`): the monomial vectors are nonzero and orthogonal in
  `ℂ^X`, so `|X| ≥ #{multisets of size k} = C(r + k − 1, k)`.
* **The gain is paid** (`pow_sum_le_moment_of_isBrauer`): the moment is the diagonal,
  `Σ_x |A_x|^{2k} = |X| Σ_m (N_m a^m)²` with `N_m` the multinomial count; Cauchy–Schwarz with the
  multinomial theorem gives `(Σ_i a_i)^{2k} ≤ C(r+k−1, k) Σ_m (N_m a^m)² ≤ Σ_x |A_x|^{2k}`. The
  bound `max_x |A_x| ≤ (Σ_x |A_x|^{2k})^{1/2k}` that positivity gives is never below the trivial
  bound `Σ_i a_i`.
* **Rank** (`tendsto_choose_rpow_inv_of_fixed_rank`, `rank_div_le_choose_rpow_inv`): the cost
  `C(r + k − 1, k)^{1/k}` tends to `1` as `k → ∞` at fixed rank `r` — the finite genus of a curve,
  where a family loss per iteration can be fixed in `k` — and is at least `r / k`, unbounded in the
  rank: at scale `y` over `ℤ` it is the whole gain.

A non-envelope amplifier over `ℤ` must therefore evaluate its moments by an identity, not by
orthogonality.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticResonanceTheory

variable {X : Type*} [Fintype X] {r k : ℕ}

/-- The degree-`k` monomial `Π_{i ∈ m} w_x(i)` of the family member `x`. -/
noncomputable def monomial (w : X → Fin r → ℂ) (x : X) (m : Sym (Fin r) k) : ℂ :=
  ((m : Multiset (Fin r)).map (w x)).prod

/-- **Brauer at level `k`**: distinct degree-`k` monomials are orthogonal over the family. -/
def IsBrauer (w : X → Fin r → ℂ) (k : ℕ) : Prop :=
  ∀ m m' : Sym (Fin r) k, m ≠ m' →
    ∑ x, monomial w x m' * starRingEnd ℂ (monomial w x m) = 0

omit [Fintype X] in
theorem norm_monomial {w : X → Fin r → ℂ} (hw : ∀ x i, ‖w x i‖ = 1) (x : X) (m : Sym (Fin r) k) :
    ‖monomial w x m‖ = 1 := by
  have h := map_multiset_prod (normHom : ℂ →*₀ ℝ) ((m : Multiset (Fin r)).map (w x))
  rw [Multiset.map_map] at h
  have hc : (m : Multiset (Fin r)).map ((normHom : ℂ →*₀ ℝ) ∘ w x) =
      (m : Multiset (Fin r)).map fun _ => (1 : ℝ) :=
    Multiset.map_congr rfl fun i _ => by simp [hw x i]
  rw [hc, Multiset.map_const', Multiset.prod_replicate, one_pow] at h
  simpa [monomial] using h

/-- **Counting.** A Brauer family at level `k` has at least as many members as there are
multisets of size `k` in `r` phases. -/
theorem card_sym_le_card_of_isBrauer [Nonempty X] {w : X → Fin r → ℂ} (hw : ∀ x i, ‖w x i‖ = 1)
    (hB : IsBrauer w k) : Fintype.card (Sym (Fin r) k) ≤ Fintype.card X := by
  classical
  let v : Sym (Fin r) k → EuclideanSpace ℂ X := fun m => WithLp.toLp 2 fun x => monomial w x m
  have hli : LinearIndependent ℂ v := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun m hm => ?_) (fun m m' hmm' => ?_)
    · obtain ⟨x⟩ := ‹Nonempty X›
      have h := congrArg (fun f : EuclideanSpace ℂ X => f x) hm
      simp only [v, PiLp.zero_apply] at h
      have h1 := norm_monomial hw x m
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    · show inner ℂ (v m) (v m') = 0
      rw [PiLp.inner_apply]
      simp only [v, PiLp.toLp_apply, RCLike.inner_apply]
      exact hB m m' hmm'
  have := hli.fintype_card_le_finrank
  rwa [finrank_euclideanSpace] at this

/-- The number of multisets of size `k` in `r` phases is `C(r + k − 1, k)`. -/
theorem card_sym_fin (r k : ℕ) : Fintype.card (Sym (Fin r) k) = (r + k - 1).choose k := by
  rw [Sym.card_sym_eq_choose, Fintype.card_fin]

/-- **Orthogonality amplifiers are trivial.** For a Brauer family at level `k`, the `2k`-th moment
of `A_x = Σ_i a_i w_x(i)` is at least the `2k`-th power of the trivial bound `Σ_i a_i`. -/
theorem pow_sum_le_moment_of_isBrauer [Nonempty X] {w : X → Fin r → ℂ}
    (hw : ∀ x i, ‖w x i‖ = 1) {a : Fin r → ℝ} (hB : IsBrauer w k) :
    (∑ i, a i) ^ (2 * k) ≤ ∑ x, ‖∑ i, (a i : ℂ) * w x i‖ ^ (2 * k) := by
  classical
  set S : Finset (Sym (Fin r) k) := (univ : Finset (Fin r)).sym k with hS
  set b : Sym (Fin r) k → ℝ := fun m =>
    ((m : Multiset (Fin r)).countPerms : ℝ) * ((m : Multiset (Fin r)).map a).prod with hb
  -- the multinomial expansions of the trivial bound and of `A_xᵏ`
  have htriv : (∑ i, a i) ^ k = ∑ m ∈ S, b m := Finset.sum_pow a k
  have hA : ∀ x, (∑ i, (a i : ℂ) * w x i) ^ k = ∑ m ∈ S, (b m : ℂ) * monomial w x m := by
    intro x
    rw [Finset.sum_pow]
    refine sum_congr rfl fun m _ => ?_
    simp only [hb, monomial, Multiset.prod_map_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
    have hcast : ((m : Multiset (Fin r)).map fun i => ((a i : ℝ) : ℂ)).prod =
        ((((m : Multiset (Fin r)).map a).prod : ℝ) : ℂ) := by
      rw [Complex.ofReal_multiset_prod, Multiset.map_map]; rfl
    rw [hcast]
    ring
  -- the Gram matrix of the monomials is `|X|` times the identity
  have hG : ∀ m m' : Sym (Fin r) k,
      ∑ x, monomial w x m * starRingEnd ℂ (monomial w x m') =
        if m = m' then (Fintype.card X : ℂ) else 0 := by
    intro m m'
    split_ifs with h
    · subst h
      simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_monomial hw]
      simp
    · exact hB m' m (Ne.symm h)
  -- the moment is the diagonal
  have hmomC : ((∑ x, ‖∑ i, (a i : ℂ) * w x i‖ ^ (2 * k) : ℝ) : ℂ) =
      ((Fintype.card X * ∑ m ∈ S, b m ^ 2 : ℝ) : ℂ) := by
    push_cast
    calc ∑ x, ((‖∑ i, (a i : ℂ) * w x i‖ : ℂ)) ^ (2 * k)
        = ∑ x, (∑ m ∈ S, (b m : ℂ) * monomial w x m) *
            starRingEnd ℂ (∑ m' ∈ S, (b m' : ℂ) * monomial w x m') := by
          refine sum_congr rfl fun x _ => ?_
          rw [← hA x, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow]
          push_cast; ring
      _ = ∑ m ∈ S, ∑ m' ∈ S, (b m : ℂ) * b m' *
            ∑ x, monomial w x m * starRingEnd ℂ (monomial w x m') := by
          simp_rw [map_sum, map_mul, Complex.conj_ofReal, sum_mul_sum, mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun m _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun m' _ => sum_congr rfl fun x _ => ?_
          ring
      _ = ∑ m ∈ S, (Fintype.card X : ℂ) * (b m : ℂ) ^ 2 := by
          refine sum_congr rfl fun m hm => ?_
          simp_rw [hG, mul_ite, mul_zero]
          rw [sum_ite_eq S m, if_pos hm]
          ring
      _ = (Fintype.card X : ℂ) * ∑ m ∈ S, (b m : ℂ) ^ 2 := by rw [mul_sum]
  have hmom : ∑ x, ‖∑ i, (a i : ℂ) * w x i‖ ^ (2 * k) = Fintype.card X * ∑ m ∈ S, b m ^ 2 :=
    Complex.ofReal_injective hmomC
  -- Cauchy–Schwarz over the multisets and the counting bound
  have hcard : (S.card : ℝ) ≤ Fintype.card X := by
    have h := card_sym_le_card_of_isBrauer hw hB
    rw [hS, Finset.sym_univ, Finset.card_univ]
    exact_mod_cast h
  calc (∑ i, a i) ^ (2 * k) = (∑ m ∈ S, b m) ^ 2 := by rw [mul_comm, pow_mul, htriv]
    _ ≤ S.card * ∑ m ∈ S, b m ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ Fintype.card X * ∑ m ∈ S, b m ^ 2 :=
        mul_le_mul_of_nonneg_right hcard (sum_nonneg fun _ _ => sq_nonneg _)
    _ = ∑ x, ‖∑ i, (a i : ℂ) * w x i‖ ^ (2 * k) := hmom.symm

/-! ## Finite and infinite rank -/

/-- **Finite rank.** At fixed rank `r ≥ 1`, the per-power cost `C(r + k − 1, k)^{1/k}` of a Brauer
family tends to `1`. -/
theorem tendsto_choose_rpow_inv_of_fixed_rank {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (fun k : ℕ => (((r + k - 1).choose k : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)) atTop (𝓝 1) := by
  -- `1 ≤ C(r + k − 1, k) ≤ (k + r)^r`
  have hlow : ∀ k : ℕ, (1 : ℝ) ≤ (((r + k - 1).choose k : ℕ) : ℝ) := fun k => by
    exact_mod_cast Nat.choose_pos (by omega)
  have hup : ∀ k : ℕ, (((r + k - 1).choose k : ℕ) : ℝ) ≤ ((k + r : ℕ) : ℝ) ^ r := fun k => by
    have hsymm : (r + k - 1).choose k = (r + k - 1).choose (r - 1) := by
      rw [show r + k - 1 = k + (r - 1) by omega, Nat.choose_symm_add]
    rw [hsymm]
    have h1 := Nat.choose_le_pow_div (α := ℝ) (r - 1) (r + k - 1)
    have h2 : ((r + k - 1 : ℕ) : ℝ) ^ (r - 1) / ((r - 1).factorial : ℝ) ≤
        ((r + k - 1 : ℕ) : ℝ) ^ (r - 1) :=
      div_le_self (by positivity) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
    have h3 : ((r + k - 1 : ℕ) : ℝ) ^ (r - 1) ≤ ((k + r : ℕ) : ℝ) ^ r := by
      calc ((r + k - 1 : ℕ) : ℝ) ^ (r - 1) ≤ ((k + r : ℕ) : ℝ) ^ (r - 1) :=
            pow_le_pow_left₀ (by positivity) (by exact_mod_cast (by omega : r + k - 1 ≤ k + r)) _
        _ ≤ ((k + r : ℕ) : ℝ) ^ r :=
            pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ k + r)) (by omega)
    exact h1.trans (h2.trans h3)
  -- the logarithms are squeezed between `0` and `r log(k + r)/k → 0`
  have hlog : Tendsto (fun k : ℕ => (r : ℝ) * (Real.log ((k + r : ℕ) : ℝ) / k)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-(r : ℝ)) 1 one_ne_zero).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (r : ℝ))))
    have h' := h.const_mul (r : ℝ)
    rw [mul_zero] at h'
    refine h'.congr' ((eventually_ge_atTop 1).mono fun k _ => ?_)
    simp only [Function.comp, pow_one, one_mul]
    push_cast
    ring_nf
  have hexp : Tendsto (fun k : ℕ => Real.exp (Real.log ((((r + k - 1).choose k : ℕ) : ℝ)) / k))
      atTop (𝓝 1) := by
    rw [← Real.exp_zero]
    refine Real.continuous_exp.continuousAt.tendsto.comp ?_
    refine squeeze_zero' (Eventually.of_forall fun k => div_nonneg (Real.log_nonneg (hlow k))
      (Nat.cast_nonneg k)) ((eventually_ge_atTop 1).mono fun k hk => ?_) hlog
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hk']
    calc Real.log ((((r + k - 1).choose k : ℕ) : ℝ)) ≤ Real.log (((k + r : ℕ) : ℝ) ^ r) :=
          Real.log_le_log (by linarith [hlow k]) (hup k)
      _ = r * Real.log ((k + r : ℕ) : ℝ) := by rw [Real.log_pow]
  refine hexp.congr fun k => ?_
  rw [Real.rpow_def_of_pos (by linarith [hlow k]), div_eq_mul_inv]

/-- **Infinite rank.** The per-power cost of a Brauer family at level `k ≥ 1` on `r` phases is at
least `r / k`. -/
theorem rank_div_le_choose_rpow_inv (r : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (r : ℝ) / k ≤ (((r + k - 1).choose k : ℕ) : ℝ) ^ ((k : ℝ)⁻¹) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  -- `(r/k)^k ≤ r^k / k! ≤ C(r + k − 1, k)`
  have h1 := Nat.pow_le_choose (α := ℝ) k (r + k - 1)
  rw [show r + k - 1 + 1 - k = r by omega] at h1
  have h2 : ((r : ℝ) / k) ^ k ≤ (r : ℝ) ^ k / (k.factorial : ℝ) := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast Nat.factorial_pos k)
      (by exact_mod_cast Nat.factorial_le_pow k)
  have h3 := h2.trans (by exact_mod_cast h1)
  have hroot := Real.rpow_le_rpow (by positivity) h3 (inv_nonneg.mpr hk'.le)
  rwa [Real.pow_rpow_inv_natCast (by positivity) (by omega)] at hroot

end GaloisForLFunctions.ArithmeticResonanceTheory

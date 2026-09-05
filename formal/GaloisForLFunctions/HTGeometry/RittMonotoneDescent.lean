import GaloisForLFunctions.HTGeometry.RittAffineTowerDichotomy

/-!
# The jet-tower descent with monotone exponents

Iterating the five-way dichotomy.  Along the surviving line the scalar of the relation is divided at
each level by `(q/ρ^m)^s` with `s` the degree of a numerator — so `s ≥ 0` always.  Writing the scalar
as `q^i·ρ^k`, one step at level `m` sends `(i,k)` to `(i − s, k + m·s)`, so for any weight `M ≥ m`
the quantity

`k + M·i`

is non-increasing: it changes by `−s·(M − m) ≤ 0`.  Since a relation seeded at jet order `n` uses
only the levels `m < n`, the weight `M = n − 1` works throughout, and the seed `c = q/ρ^n` has
`k + M·i = −n + (n−1) = −1`.

So the base relation reached by the descent has `k + M·i ≤ −1 < 0`, and in particular its exponent
pair is not `(0,0)`: the multiplier that arrives at the base is never trivial.  The two exits are a
jet with no shift defect and the affine connection of a coordinate, both of which carry their own
nontrivial data.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [CharZero L] [Algebra K L]

/-- Dividing a monomial in the multiplier and the chain-rule factor by a power of the level
multiplier shifts the exponent pair by `(−D, m·D)`. -/
theorem div_level_multiplier_pow {q ρ c : K} (hq : q ≠ 0) (hρ : ρ ≠ 0) {i k : ℤ}
    (hc : c = q ^ i * ρ ^ k) (m D : ℕ) :
    c / (q / ρ ^ m) ^ D = q ^ (i - (D : ℤ)) * ρ ^ (k + (m : ℤ) * (D : ℤ)) := by
  have hpow : (q / ρ ^ m) ^ D = q ^ (D : ℤ) * ρ ^ (-((m : ℤ) * (D : ℤ))) := by
    rw [div_pow, ← pow_mul, ← zpow_natCast q D, ← zpow_natCast ρ (m * D), zpow_neg,
      div_eq_mul_inv]
    push_cast
    rfl
  rw [hc, hpow, zpow_sub₀ hq, zpow_add₀ hρ, zpow_neg]
  have h1 : q ^ (D : ℤ) ≠ 0 := zpow_ne_zero _ hq
  have h2 : ρ ^ ((m : ℤ) * (D : ℤ)) ≠ 0 := zpow_ne_zero _ hρ
  field_simp

/-- **The monotone tower descent, stopped at a floor.**  An eigen-inhomogeneous relation over the
jet prefix field either exits through a jet with no shift defect above the floor or through the
affine connection of a coordinate, or reaches the floor with an exponent pair whose weighted sum has
not increased. -/
theorem exists_floor_relation_or_exit_of_tower (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0) (M : ℤ)
    (F : ℕ) :
    ∀ (n : ℕ), (n : ℤ) ≤ M + 1 →
      (∀ j, j < n → Transcendental ↥(Fr.jetPrefixField τ j) (Fr.d^[j] τ)) →
      ∀ (W : L) (c g : K) (A : ℕ → K) (i k : ℤ),
        W ≠ 0 → W ∈ Fr.jetPrefixField τ n → c ≠ 0 → c = q ^ i * Fr.ρ ^ k →
        Fr.σ W = algebraMap K L c * W + algebraMap K L g
          + ∑ j ∈ Finset.range n, algebraMap K L (A j) * Fr.d^[j] τ →
        (∃ m : ℕ, F ≤ m ∧ m < n ∧
            Fr.σ (Fr.d^[m] τ) = algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ) ∨
        (∃ (m : ℕ) (w : L) (N : ℕ) (A' : ℕ → K), F ≤ m ∧ m < n ∧ w ≠ 0 ∧
            w ∈ Fr.jetPrefixField τ m ∧ 1 ≤ N ∧
            (Fr.σ (Fr.d^[m] τ) = algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ
              + ∑ j ∈ Finset.range m, algebraMap K L (A' j) * Fr.d^[j] τ) ∧
            Fr.σ w = algebraMap K L (q / Fr.ρ ^ m) * w
              + ∑ j ∈ Finset.range m, algebraMap K L (-(N : K) * A' j) * Fr.d^[j] τ) ∨
        (∃ (n' : ℕ) (V : L) (c' g' : K) (A' : ℕ → K) (i' k' : ℤ),
            n' ≤ F ∧ n' ≤ n ∧ V ≠ 0 ∧ V ∈ Fr.jetPrefixField τ n' ∧ c' ≠ 0 ∧
            c' = q ^ i' * Fr.ρ ^ k' ∧ k' + M * i' ≤ k + M * i ∧
            (g' = 0 ∨ g' = g ∨ ∃ m : ℕ, m < n ∧ g' = A m / (q / Fr.ρ ^ m)) ∧
            Fr.σ V = algebraMap K L c' * V + algebraMap K L g'
              + ∑ j ∈ Finset.range n', algebraMap K L (A' j) * Fr.d^[j] τ) := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  intro n
  induction n with
  | zero =>
      intro _ _ W c g A i k hW0 hWmem hc hcik hrel
      exact Or.inr (Or.inr ⟨0, W, c, g, A, i, k, Nat.zero_le _, le_rfl, hW0, hWmem, hc, hcik,
        le_rfl, Or.inr (Or.inl rfl), hrel⟩)
  | succ m ih =>
      intro hM htr W c g A i k hW0 hWmem hc hcik hrel
      by_cases hFloor : m + 1 ≤ F
      · exact Or.inr (Or.inr ⟨m + 1, W, c, g, A, i, k, hFloor, le_rfl, hW0, hWmem, hc, hcik,
          le_rfl, Or.inr (Or.inl rfl), hrel⟩)
      have hFm : F ≤ m := by omega
      have hmM : (m : ℤ) ≤ M := by
        have : ((m : ℤ) + 1) ≤ M + 1 := by exact_mod_cast hM
        omega
      have haK0 : q / Fr.ρ ^ m ≠ 0 := div_ne_zero hq (pow_ne_zero _ hρ0)
      rcases affine_descent_dichotomy Fr hqconst hshift hq (htr m (by omega)) hW0 hWmem hc
          hrel with h1 | h2 | h3 | h4 | h5
      · obtain ⟨hAm, hWm⟩ := h1
        have hrel' : Fr.σ W = algebraMap K L c * W + algebraMap K L g
            + ∑ j ∈ Finset.range m, algebraMap K L (A j) * Fr.d^[j] τ := by
          rw [hrel, Finset.sum_range_succ, hAm, map_zero, zero_mul, add_zero]
        rcases ih (by omega) (fun j hj => htr j (by omega)) W c g A i k hW0 hWm hc hcik hrel'
          with ⟨m', hFm', hm', hd⟩ | ⟨m', w, N, A', hFm', hm', hw0, hwmem, hN, hAsh, hconn⟩ |
            ⟨n', V, c', g', A', i', k', hn'F, hn'm, hV0, hVmem, hc'0, hc'ik, hmono, hgshape, hVrel⟩
        · exact Or.inl ⟨m', hFm', by omega, hd⟩
        · exact Or.inr (Or.inl ⟨m', w, N, A', hFm', by omega, hw0, hwmem, hN, hAsh, hconn⟩)
        · refine Or.inr (Or.inr ⟨n', V, c', g', A', i', k', hn'F, by omega, hV0, hVmem, hc'0,
            hc'ik, hmono, ?_, hVrel⟩)
          rcases hgshape with h | h | ⟨m'', hm'', h⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨m'', by omega, h⟩)
      · exact Or.inl ⟨m, hFm, by omega, h2⟩
      · obtain ⟨w, N, A', hw0, hwmem, hN, hAsh, hconn⟩ := h3
        exact Or.inr (Or.inl ⟨m, w, N, A', hFm, by omega, hw0, hwmem, hN, hAsh, hconn⟩)
      · obtain ⟨v, -, -, hv0, hvmem, -, -, -, hveq, -, -⟩ := h4
        have hc'val : c / (q / Fr.ρ ^ m) ^ 2
            = q ^ (i - ((2 : ℕ) : ℤ)) * Fr.ρ ^ (k + (m : ℤ) * ((2 : ℕ) : ℤ)) :=
          div_level_multiplier_pow hq hρ0 hcik m 2
        have hc'0 : c / (q / Fr.ρ ^ m) ^ 2 ≠ 0 := div_ne_zero hc (pow_ne_zero _ haK0)
        have hrel' : Fr.σ v = algebraMap K L (c / (q / Fr.ρ ^ m) ^ 2) * v
            + algebraMap K L 0
            + ∑ j ∈ Finset.range m, algebraMap K L ((0 : ℕ → K) j) * Fr.d^[j] τ := by
          rw [hveq, map_zero, add_zero]
          simp
        rcases ih (by omega) (fun j hj => htr j (by omega)) v _ 0 (0 : ℕ → K)
            (i - ((2 : ℕ) : ℤ)) (k + (m : ℤ) * ((2 : ℕ) : ℤ)) hv0 hvmem hc'0 hc'val hrel'
          with ⟨m', hFm', hm', hd⟩ | ⟨m', w, N, A', hFm', hm', hw0, hwmem, hN, hAsh, hconn⟩ |
            ⟨n', V, c', g', A', i', k', hn'F, hn'm, hV0, hVmem, hc''0, hc'ik, hmono, hgshape, hVrel⟩
        · exact Or.inl ⟨m', hFm', by omega, hd⟩
        · exact Or.inr (Or.inl ⟨m', w, N, A', hFm', by omega, hw0, hwmem, hN, hAsh, hconn⟩)
        · refine Or.inr (Or.inr ⟨n', V, c', g', A', i', k', hn'F, by omega, hV0, hVmem, hc''0,
            hc'ik, ?_, ?_, hVrel⟩)
          · have hstep : k + (m : ℤ) * ((2 : ℕ) : ℤ) + M * (i - ((2 : ℕ) : ℤ)) ≤ k + M * i := by
              have hnn : (0 : ℤ) ≤ ((2 : ℕ) : ℤ) * (M - (m : ℤ)) :=
                mul_nonneg (by norm_num) (by omega)
              linarith [hnn]
            exact le_trans hmono hstep
          · left
            rcases hgshape with h | h | ⟨m'', -, h⟩
            · exact h
            · exact h
            · rw [h]
              simp
      · obtain ⟨v, hv0, hvmem, hveq, -⟩ := h5
        have hc'val : c / (q / Fr.ρ ^ m) ^ 1
            = q ^ (i - (1 : ℤ)) * Fr.ρ ^ (k + (m : ℤ) * (1 : ℤ)) :=
          div_level_multiplier_pow hq hρ0 hcik m 1
        rw [pow_one] at hc'val
        have hc'0 : c / (q / Fr.ρ ^ m) ≠ 0 := div_ne_zero hc haK0
        have hrel' : Fr.σ v = algebraMap K L (c / (q / Fr.ρ ^ m)) * v
            + algebraMap K L (A m / (q / Fr.ρ ^ m))
            + ∑ j ∈ Finset.range m, algebraMap K L ((0 : ℕ → K) j) * Fr.d^[j] τ := by
          rw [hveq]
          simp
        rcases ih (by omega) (fun j hj => htr j (by omega)) v _ (A m / (q / Fr.ρ ^ m))
            (0 : ℕ → K) (i - 1) (k + (m : ℤ)) hv0 hvmem hc'0 (by rw [hc'val]; ring_nf) hrel'
          with ⟨m', hFm', hm', hd⟩ | ⟨m', w, N, A', hFm', hm', hw0, hwmem, hN, hAsh, hconn⟩ |
            ⟨n', V, c', g', A', i', k', hn'F, hn'm, hV0, hVmem, hc''0, hc'ik, hmono, hgshape, hVrel⟩
        · exact Or.inl ⟨m', hFm', by omega, hd⟩
        · exact Or.inr (Or.inl ⟨m', w, N, A', hFm', by omega, hw0, hwmem, hN, hAsh, hconn⟩)
        · refine Or.inr (Or.inr ⟨n', V, c', g', A', i', k', hn'F, by omega, hV0, hVmem, hc''0,
            hc'ik, ?_, ?_, hVrel⟩)
          · have hstep : k + (m : ℤ) + M * (i - 1) ≤ k + M * i := by
              have hexp : M * (i - 1) = M * i - M := by ring
              rw [hexp]
              omega
            exact le_trans hmono hstep
          · rcases hgshape with h | h | ⟨m'', -, h⟩
            · exact Or.inl h
            · exact Or.inr (Or.inr ⟨m, by omega, h⟩)
            · left
              rw [h]
              simp

end GaloisForLFunctions.HTGeometry

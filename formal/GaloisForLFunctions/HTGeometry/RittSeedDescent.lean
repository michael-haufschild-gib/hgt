import GaloisForLFunctions.HTGeometry.RittMonotoneDescent

/-!
# The seed of the tower collapse descends to a nontrivial base multiplier

The relation the collapse of the jet tower produces has a very particular scalar: the shift of the
`n`-th jet is `q/ρ^n`, that is `q^1·ρ^{−n}`, whose weighted exponent at weight `M = n − 1` is

`(−n) + (n − 1)·1 = −1`.

The monotone descent never increases that quantity, so whatever multiplier reaches the base has
weighted exponent at most `−1`; in particular its exponent pair is not `(0,0)` and the multiplier is
not trivial.

The descent's affine-connection exit is itself a relation with the same seed shape one level down —
its scalar is `q/ρ^m` and its inhomogeneity is a multiple of the shift defect at level `m` — so a
strong induction on the level absorbs it.  What survives is a single alternative: either some jet
below the top has no shift defect at all, or the base carries a relation whose multiplier is a
genuinely nontrivial monomial in `q` and `ρ`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [CharZero L] [Algebra K L]

/-- **The seeded tower descent.**  A relation whose scalar is the shift multiplier of the top jet
descends to the floor with a nontrivial exponent pair, unless some jet at or above the floor has no
shift defect. -/
theorem exists_nontrivial_floor_relation_of_jet_seed (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0) (F : ℕ) :
    ∀ n : ℕ, (∀ j, j < n → Transcendental ↥(Fr.jetPrefixField τ j) (Fr.d^[j] τ)) →
      ∀ (W : L) (A : ℕ → K), W ≠ 0 → W ∈ Fr.jetPrefixField τ n →
        Fr.σ W = algebraMap K L (q / Fr.ρ ^ n) * W
          + ∑ j ∈ Finset.range n, algebraMap K L (A j) * Fr.d^[j] τ →
        (∃ m : ℕ, F ≤ m ∧ m < n ∧
            Fr.σ (Fr.d^[m] τ) = algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ) ∨
        (∃ (n' : ℕ) (V : L) (c' g' : K) (A' : ℕ → K) (i' k' : ℤ),
            n' ≤ F ∧ V ≠ 0 ∧ V ∈ Fr.jetPrefixField τ n' ∧ c' ≠ 0 ∧
            c' = q ^ i' * Fr.ρ ^ k' ∧ ¬(i' = 0 ∧ k' = 0) ∧
            Fr.σ V = algebraMap K L c' * V + algebraMap K L g'
              + ∑ j ∈ Finset.range n', algebraMap K L (A' j) * Fr.d^[j] τ) := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro htr W A hW0 hWmem hrel
    have hseed : q / Fr.ρ ^ n = q ^ (1 : ℤ) * Fr.ρ ^ (-(n : ℤ)) := by
      rw [zpow_one, zpow_neg, zpow_natCast, div_eq_mul_inv]
    have hseed0 : q / Fr.ρ ^ n ≠ 0 := div_ne_zero hq (pow_ne_zero _ hρ0)
    have hrel' : Fr.σ W = algebraMap K L (q / Fr.ρ ^ n) * W + algebraMap K L 0
        + ∑ j ∈ Finset.range n, algebraMap K L (A j) * Fr.d^[j] τ := by
      rw [map_zero, add_zero]
      exact hrel
    rcases exists_floor_relation_or_exit_of_tower Fr hqconst hshift hq ((n : ℤ) - 1) F n
        (by omega) htr W _ 0 A 1 (-(n : ℤ)) hW0 hWmem hseed0 hseed hrel'
      with ⟨m, hFm, hm, hd⟩ |
        ⟨m, w, N, A', hFm, hm, hw0, hwmem, hN, hAsh, hconn⟩ |
        ⟨n', V, c', g', A', i', k', hn'F, -, hV0, hVmem, hc'0, hc'ik, hmono, -, hVrel⟩
    · exact Or.inl ⟨m, hFm, hm, hd⟩
    · rcases ih m hm (fun j hj => htr j (by omega)) w (fun j => -(N : K) * A' j) hw0 hwmem hconn
        with ⟨m', hFm', hm', hd⟩ | hfloor
      · exact Or.inl ⟨m', hFm', by omega, hd⟩
      · exact Or.inr hfloor
    · refine Or.inr ⟨n', V, c', g', A', i', k', hn'F, hV0, hVmem, hc'0, hc'ik, ?_, hVrel⟩
      rintro ⟨rfl, rfl⟩
      simp only [mul_zero, add_zero] at hmono
      have hone : ((n : ℤ) - 1) * 1 = (n : ℤ) - 1 := mul_one _
      omega

end GaloisForLFunctions.HTGeometry

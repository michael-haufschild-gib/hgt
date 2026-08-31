import GaloisForLFunctions.HTGeometry.RittLevelTwoClassification
import GaloisForLFunctions.HTGeometry.RittAffineTowerDichotomy
import GaloisForLFunctions.HTGeometry.RittJetIndependence
import GaloisForLFunctions.HTGeometry.RittGeneralInhomogeneity

/-!
# The seed of a tower collapse, by strong induction on its order

The relation a collapse produces at jet order `n` has scalar `q/ρ^n` and an inhomogeneity whose top
coefficient is the leading coefficient of the shift defect, `−C(n,2)·q·(dρ)/ρ^{n+1}`, nonzero for
`n ≥ 2`.  Applying the five-way dichotomy at the top level:

* the "top jet absent" branch needs that coefficient to vanish — impossible;
* the "no shift defect" branch is impossible above jet order one;
* the affine-connection branch produces a relation of exactly the same shape one order down, with
  inhomogeneity `−N` times the defect at that order, whose top coefficient is again nonzero — so
  strong induction applies;
* the two remaining branches are the exceptional ones, with scalars `q^{−1}ρ^{m−1}` (homogeneous)
  and `ρ^{−1}` (affine with a nonzero constant inhomogeneity).

At order two the classification applies directly, and its monomial alternative needs the linear part
of the inhomogeneity to vanish, which the nonzero top coefficient forbids.  So a collapse forces
Ritt's order-one form, an affine transport equation, or one of the two exceptional relations.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] [Algebra K L]

/-- **The seeded collapse, by strong induction on the jet order.** -/
theorem ritt_affine_or_exceptional_of_seed (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (hdρ : Fr.dK Fr.ρ ≠ 0) (htr0 : Transcendental K τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ)) :
    ∀ n : ℕ, 2 ≤ n → (∀ j, j < n → Transcendental ↥(Fr.jetPrefixField τ j) (Fr.d^[j] τ)) →
      ∀ (W : L) (A : ℕ → K), W ≠ 0 → W ∈ Fr.jetPrefixField τ n → A (n - 1) ≠ 0 →
        Fr.σ W = algebraMap K L (q / Fr.ρ ^ n) * W
          + ∑ j ∈ Finset.range n, algebraMap K L (A j) * Fr.d^[j] τ →
        (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
        (∃ (u h : K) (I J : ℤ), u ≠ 0 ∧ h ≠ 0 ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u + h) ∨
        (∃ (m : ℕ) (v z : L) (κ : K), 2 ≤ m ∧ m < n ∧ v ≠ 0 ∧ κ ≠ 0 ∧
          v ∈ Fr.jetPrefixField τ m ∧ z ∈ Fr.jetPrefixField τ m ∧
          Fr.σ v = algebraMap K L (q⁻¹ * Fr.ρ ^ (m - 1)) * v ∧
          Fr.σ z = algebraMap K L (q / Fr.ρ ^ m) * z + algebraMap K L κ / v
            - (2 : L) * (Fr.σ (Fr.d^[m] τ)
                - algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ)) ∨
        (∃ (m : ℕ) (v : L) (h : K), 2 ≤ m ∧ m < n ∧ v ≠ 0 ∧ v ∈ Fr.jetPrefixField τ m ∧ h ≠ 0 ∧
          Fr.σ v = algebraMap K L (q / Fr.ρ ^ (m + 1) / (q / Fr.ρ ^ m)) * v
            + algebraMap K L h) := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn2 htr W A hW0 hWmem hAtop hrel
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · -- the base case: jet order two
      have hn : n = 2 := by omega
      subst hn
      have hcq : q / Fr.ρ ^ 2 ≠ 0 := div_ne_zero hq (pow_ne_zero _ hρ0)
      have hcik : q / Fr.ρ ^ 2 = q ^ (1 : ℤ) * Fr.ρ ^ (-(2 : ℤ)) := by
        have hinv : (Fr.ρ : K) ^ (-(2 : ℤ)) = (Fr.ρ ^ (2 : ℕ))⁻¹ := by
          rw [zpow_neg]
          norm_cast
        rw [zpow_one, hinv, div_eq_mul_inv]
      have hG1 : (fun j : ℕ => if j = 1 then C (A 1) else C (A 0) * X) 1 ≠ 0 := by
        simp only [if_true]
        exact fun hz => hAtop (C_eq_zero.mp hz)
      have hrel' : Fr.σ W = algebraMap K L (q / Fr.ρ ^ 2) * W
          + ∑ j ∈ Finset.range 2,
            aeval τ ((fun j : ℕ => if j = 1 then C (A 1) else C (A 0) * X) j)
              * (Fr.d τ) ^ j := by
        rw [hrel, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_succ,
          Finset.sum_range_one]
        simp only [Function.iterate_zero_apply, Function.iterate_one, if_neg
          (by omega : ¬ (0 : ℕ) = 1), map_mul, aeval_C, aeval_X, pow_zero,
          pow_one, mul_one, if_true]
      rcases level_two_nonzero_inhom Fr hqconst hshift hq htr0 htr1 hW0 hWmem hcq hcik
          ⟨1, by omega, hG1⟩ hrel' with hritt | ⟨u, h, I, J, -, -, hu0, hh0, -, hbase⟩
      · exact Or.inl hritt
      · exact Or.inr (Or.inl ⟨u, h, I, J, hu0, hh0, hbase⟩)
    · -- the inductive step
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hm2 : 2 ≤ m := by omega
      have hnsub : m + 1 - 1 = m := by omega
      rw [hnsub] at hAtop
      have hcq : q / Fr.ρ ^ (m + 1) ≠ 0 := div_ne_zero hq (pow_ne_zero _ hρ0)
      rcases affine_descent_dichotomy Fr hqconst hshift hq (htr m (by omega)) hW0 hWmem hcq
          (g := 0) (A := A) (by rw [hrel, map_zero, add_zero]) with
          ⟨hA0, -⟩ | hdiag | ⟨w, N, A', hw0, hwmem, hN, hAsh, hconn⟩ | h4 | h5
      · exact absurd hA0 hAtop
      · exfalso
        obtain ⟨p, hp⟩ : ∃ p, m = p + 2 := ⟨m - 2, by omega⟩
        have hjet : Fr.d^[p + 1] τ ∉ Fr.jetPrefixField τ (p + 1) := by
          intro hmem
          exact htr (p + 1) (by omega)
            (isAlgebraic_algebraMap
              (⟨Fr.d^[p + 1] τ, hmem⟩ : ↥(Fr.jetPrefixField τ (p + 1))))
        refine jetDefect_ne_zero Fr hqconst hshift hq hdρ p hjet ?_
        rw [RittFrame.jetDefect, ← hp, hdiag, sub_self]
      · -- the affine connection: the same seed one order down
        have hAtop' : A' (m - 1) = -(((m.choose 2 : ℕ) : K) * q * Fr.dK Fr.ρ / Fr.ρ ^ (m + 1)) :=
          jetDefect_top_coeff Fr hqconst hshift hm2 (fun j hj => htr j (by omega)) hAsh
        have hlam0 : A' (m - 1) ≠ 0 := by
          rw [hAtop']
          refine neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (mul_ne_zero ?_ hq) hdρ)
            (pow_ne_zero _ hρ0))
          exact Nat.cast_ne_zero.mpr (by have := Nat.choose_pos (show 2 ≤ m from hm2); omega)
        have hNtop : (-(N : K) * A' (m - 1)) ≠ 0 := by
          refine mul_ne_zero (neg_ne_zero.mpr ?_) hlam0
          exact Nat.cast_ne_zero.mpr (by omega)
        rcases ih m (by omega) hm2 (fun j hj => htr j (by omega)) w
            (fun j => -(N : K) * A' j) hw0 hwmem hNtop hconn with
            h | h | ⟨m', v', z', κ', hm'2, hm'lt, hv'0, hκ'0, hv'mem, hz'mem, hv'eq, hz'eq⟩ |
            ⟨m', v', h', hm'2, hm'lt, hv'0, hv'mem, hh'0, hv'eq⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl ⟨m', v', z', κ', hm'2, by omega, hv'0, hκ'0, hv'mem,
            hz'mem, hv'eq, hz'eq⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨m', v', h', hm'2, by omega, hv'0, hv'mem, hh'0,
            hv'eq⟩))
      · obtain ⟨v, z, -, hv0, hvmem, hzmem, -, hAm, hveq, hzeq, -⟩ := h4
        have haK0 : q / Fr.ρ ^ m ≠ 0 := div_ne_zero hq (pow_ne_zero _ hρ0)
        have hsc : q / Fr.ρ ^ (m + 1) / (q / Fr.ρ ^ m) ^ 2 = q⁻¹ * Fr.ρ ^ (m - 1) := by
          obtain ⟨r, hr⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
          subst hr
          rw [show r + 1 - 1 = r by omega]
          field_simp
          ring
        exact Or.inr (Or.inr (Or.inl ⟨m, v, z, (q / Fr.ρ ^ m) * A m / (q / Fr.ρ ^ (m + 1)),
          hm2, by omega, hv0, div_ne_zero (mul_ne_zero haK0 hAm) hcq, hvmem, hzmem,
          by rw [← hsc]; exact hveq, hzeq⟩))
      · obtain ⟨v, hv0, hvmem, hveq, -⟩ := h5
        have haK0 : q / Fr.ρ ^ m ≠ 0 := div_ne_zero hq (pow_ne_zero _ hρ0)
        exact Or.inr (Or.inr (Or.inr ⟨m, v, A m / (q / Fr.ρ ^ m), hm2, by omega, hv0, hvmem,
          div_ne_zero hAtop haK0, hveq⟩))

end GaloisForLFunctions.HTGeometry

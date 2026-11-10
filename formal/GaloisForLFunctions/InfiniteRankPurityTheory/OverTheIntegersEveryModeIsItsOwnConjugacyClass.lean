import GaloisForLFunctions.InfiniteRankPurityTheory.TwoFrobeniiDetermineATraceClassModule

/-!
# Over the integers every mode is its own conjugacy class

In finite rank the conjugates of a Frobenius eigenvalue share its absolute value because a Galois
group permutes them. This module determines the conjugacy classes of the Frobenius module
`M = ⊕_i ℂ(−ρ_i)` of any rank, on which the Frobenius at `n` multiplies the `i`-th line by `n^{ρ_i}`
(`frobAct`).

* `cpow_eq_of_commute`, `re_eq_of_commute`: a linear map commuting with the Frobenius at one prime
  `p` sends the line of `ρ_i` into the lines of the modes `ρ_j` with `p^{ρ_j} = p^{ρ_i}`. These
  share the weight `Re ρ_i`: over one Frobenius the conjugacy class of a mode is its vertical
  progression `ρ_i + (2πi/log p) ℤ`, and conjugates share their depth.
* `eq_of_commute_two_three`: with distinct modes, a linear map commuting with the Frobenii at `2`
  and `3` is diagonal. Over `ℤ` every mode is alone in its class.
* `eq_conj_of_semilinear_commute`: a conjugate-linear map commuting with the Frobenii at `2` and `3`
  sends the line of `ρ_i` into the line of `ρ̄_i`. The only conjugation of modes over `ℤ` is the
  archimedean involution.
* `single_mem_of_stable`: a subspace stable under the Frobenii at `2` and `3` contains every line on
  which one of its vectors has a nonzero component. The module is semisimple without multiplicity;
  its Frobenius-stable subspaces are the sums of lines, and its simple constituents are the single
  modes.

So no Frobenius-equivariant structure relates the depths of two different zeros: what finite rank
gets from conjugation must come from elsewhere.
-/

open Finsupp

namespace GaloisForLFunctions.InfiniteRankPurityTheory

variable {ι : Type*}

/-- The Frobenius at `n` on `⊕_i ℂ(−ρ_i)`: multiplication by `n^{ρ_i}` on the `i`-th line. -/
noncomputable def frobAct (ρ : ι → ℂ) (n : ℕ) : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ) :=
  Finsupp.lsum ℂ fun i => ((n : ℂ) ^ ρ i) • Finsupp.lsingle i

theorem frobAct_single (ρ : ι → ℂ) (n : ℕ) (i : ι) (a : ℂ) :
    frobAct ρ n (Finsupp.single i a) = Finsupp.single i ((n : ℂ) ^ ρ i * a) := by
  rw [frobAct, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.smul_single, smul_eq_mul]

theorem frobAct_apply (ρ : ι → ℂ) (n : ℕ) (v : ι →₀ ℂ) (j : ι) :
    frobAct ρ n v j = (n : ℂ) ^ ρ j * v j := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply, mul_add]
  | single i a =>
    rw [frobAct_single, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : i = j
    · rw [if_pos h, if_pos h, h]
    · rw [if_neg h, if_neg h, mul_zero]

/-- Equal Frobenius eigenvalues at one prime have equal weights. -/
theorem re_eq_of_natCast_cpow_eq {p : ℕ} (hp : 2 ≤ p) {s t : ℂ}
    (h : (p : ℂ) ^ s = (p : ℂ) ^ t) : s.re = t.re := by
  have hn := congrArg norm h
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.norm_natCast_cpow_of_pos (by omega)]
    at hn
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  refine le_antisymm (le_of_not_gt fun hlt => ?_) (le_of_not_gt fun hlt => ?_)
  · exact absurd hn (ne_of_gt (Real.rpow_lt_rpow_of_exponent_lt hp1 hlt))
  · exact absurd hn (ne_of_lt (Real.rpow_lt_rpow_of_exponent_lt hp1 hlt))

/-- **An equivariant map preserves the Frobenius eigenvalue.** If `T` commutes with the Frobenius at
`p`, the image of the `i`-th line has components only at modes `j` with `p^{ρ_j} = p^{ρ_i}`. -/
theorem cpow_eq_of_commute {ρ : ι → ℂ} {p : ℕ} {T : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ)}
    (hT : ∀ v, T (frobAct ρ p v) = frobAct ρ p (T v)) {i j : ι}
    (h : T (Finsupp.single i 1) j ≠ 0) : (p : ℂ) ^ ρ j = (p : ℂ) ^ ρ i := by
  have h1 := congrArg (fun w : ι →₀ ℂ => w j) (hT (Finsupp.single i 1))
  have h2 : T (Finsupp.single i ((p : ℂ) ^ ρ i * 1)) =
      ((p : ℂ) ^ ρ i) • T (Finsupp.single i 1) := by
    rw [← map_smul, Finsupp.smul_single, smul_eq_mul]
  simp only [frobAct_single, frobAct_apply] at h1
  rw [h2, Finsupp.smul_apply, smul_eq_mul] at h1
  exact (mul_right_cancel₀ h h1).symm

/-- **Conjugates over one Frobenius share their weight.** -/
theorem re_eq_of_commute {ρ : ι → ℂ} {p : ℕ} (hp : 2 ≤ p) {T : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ)}
    (hT : ∀ v, T (frobAct ρ p v) = frobAct ρ p (T v)) {i j : ι}
    (h : T (Finsupp.single i 1) j ≠ 0) : (ρ j).re = (ρ i).re :=
  re_eq_of_natCast_cpow_eq hp (cpow_eq_of_commute hT h)

/-- **Over `ℤ` an equivariant map is diagonal.** With distinct modes, a linear map commuting with
the Frobenii at `2` and `3` sends each line into itself. -/
theorem eq_of_commute_two_three {ρ : ι → ℂ} (hρ : Function.Injective ρ)
    {T : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ)} (h2 : ∀ v, T (frobAct ρ 2 v) = frobAct ρ 2 (T v))
    (h3 : ∀ v, T (frobAct ρ 3 v) = frobAct ρ 3 (T v)) {i j : ι}
    (h : T (Finsupp.single i 1) j ≠ 0) : j = i :=
  hρ (cpow_two_three_injective (by simpa using cpow_eq_of_commute h2 h)
    (by simpa using cpow_eq_of_commute h3 h))

theorem conj_natCast_cpow {p : ℕ} (s : ℂ) :
    (starRingEnd ℂ) ((p : ℂ) ^ s) = (p : ℂ) ^ (starRingEnd ℂ) s := by
  have harg : ((p : ℂ)).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_pos.ne
  rw [Complex.cpow_conj _ _ harg, Complex.conj_natCast]

/-- **The only conjugation over `ℤ` is the archimedean one.** A conjugate-linear map commuting with
the Frobenii at `2` and `3` sends the line of `ρ_i` into lines of modes equal to `ρ̄_i`. -/
theorem eq_conj_of_semilinear_commute {ρ : ι → ℂ}
    {T : (ι →₀ ℂ) →ₛₗ[starRingEnd ℂ] (ι →₀ ℂ)}
    (h2 : ∀ v, T (frobAct ρ 2 v) = frobAct ρ 2 (T v))
    (h3 : ∀ v, T (frobAct ρ 3 v) = frobAct ρ 3 (T v)) {i j : ι}
    (h : T (Finsupp.single i 1) j ≠ 0) : ρ j = (starRingEnd ℂ) (ρ i) := by
  have key : ∀ p : ℕ, (∀ v, T (frobAct ρ p v) = frobAct ρ p (T v)) →
      (p : ℂ) ^ ρ j = (p : ℂ) ^ (starRingEnd ℂ) (ρ i) := by
    intro p hp
    have h1 := congrArg (fun w : ι →₀ ℂ => w j) (hp (Finsupp.single i 1))
    have hs : T (Finsupp.single i ((p : ℂ) ^ ρ i * 1)) =
        ((starRingEnd ℂ) ((p : ℂ) ^ ρ i)) • T (Finsupp.single i 1) := by
      rw [← map_smulₛₗ, Finsupp.smul_single, smul_eq_mul]
    simp only [frobAct_single, frobAct_apply] at h1
    rw [hs, Finsupp.smul_apply, smul_eq_mul, conj_natCast_cpow] at h1
    exact (mul_right_cancel₀ h h1).symm
  exact cpow_two_three_injective (by simpa using key 2 h2) (by simpa using key 3 h3)

/-- **The Frobenius module over `ℤ` is semisimple without multiplicity.** A subspace stable under
the Frobenii at `2` and `3` contains every line on which one of its vectors has a nonzero
component: for each other mode in the support one of the two primes separates it, and
`Frob_p − p^{ρ_j}` removes it. -/
theorem single_mem_of_stable {ρ : ι → ℂ} (hρ : Function.Injective ρ)
    {W : Submodule ℂ (ι →₀ ℂ)} (h2 : ∀ v ∈ W, frobAct ρ 2 v ∈ W)
    (h3 : ∀ v ∈ W, frobAct ρ 3 v ∈ W) {v : ι →₀ ℂ} (hv : v ∈ W) {i : ι} (hi : v i ≠ 0) :
    Finsupp.single i (1 : ℂ) ∈ W := by
  classical
  suffices H : ∀ (s : Finset ι) (v : ι →₀ ℂ), v ∈ W → v i ≠ 0 →
      (∀ j, v j ≠ 0 → j = i ∨ j ∈ s) → Finsupp.single i (1 : ℂ) ∈ W from
    H v.support v hv hi fun j hj => Or.inr (Finsupp.mem_support_iff.mpr hj)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro v hv hi hs
    have hv' : v = Finsupp.single i (v i) := by
      ext j
      rw [Finsupp.single_apply]
      by_cases hj : i = j
      · rw [if_pos hj, hj]
      · rw [if_neg hj]
        by_contra h
        rcases hs j h with h' | h'
        · exact hj h'.symm
        · exact absurd h' (Finset.notMem_empty j)
    have hone : Finsupp.single i (1 : ℂ) = (v i)⁻¹ • Finsupp.single i (v i) := by
      rw [Finsupp.smul_single, smul_eq_mul, inv_mul_cancel₀ hi]
    rw [hone, ← hv']
    exact W.smul_mem _ hv
  | insert j₀ s hj₀ ih =>
    intro v hv hi hs
    by_cases hji : j₀ = i
    · exact ih v hv hi fun j hj => (hs j hj).elim Or.inl fun h =>
        (Finset.mem_insert.mp h).elim (fun h' => Or.inl (h'.trans hji)) Or.inr
    · -- one of the two primes separates `j₀` from `i`
      have hsep : (2 : ℂ) ^ ρ j₀ ≠ (2 : ℂ) ^ ρ i ∨ (3 : ℂ) ^ ρ j₀ ≠ (3 : ℂ) ^ ρ i := by
        by_contra hcon
        rw [not_or, not_not, not_not] at hcon
        exact hji (hρ (cpow_two_three_injective hcon.1 hcon.2))
      have step : ∀ p : ℕ, (∀ v ∈ W, frobAct ρ p v ∈ W) → (p : ℂ) ^ ρ j₀ ≠ (p : ℂ) ^ ρ i →
          Finsupp.single i (1 : ℂ) ∈ W := by
        intro p hp hne
        have hw : frobAct ρ p v - ((p : ℂ) ^ ρ j₀) • v ∈ W :=
          W.sub_mem (hp v hv) (W.smul_mem _ hv)
        have hwj : ∀ j, (frobAct ρ p v - ((p : ℂ) ^ ρ j₀) • v) j =
            ((p : ℂ) ^ ρ j - (p : ℂ) ^ ρ j₀) * v j := by
          intro j
          rw [Finsupp.sub_apply, frobAct_apply, Finsupp.smul_apply, smul_eq_mul]
          ring
        refine ih _ hw ?_ ?_
        · rw [hwj]
          exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hne)) hi
        · intro j hj
          rw [hwj] at hj
          have hvj : v j ≠ 0 := right_ne_zero_of_mul hj
          have hjj : j ≠ j₀ := fun h => by
            rw [h, sub_self, zero_mul] at hj
            exact hj rfl
          exact (hs j hvj).elim Or.inl fun h =>
            (Finset.mem_insert.mp h).elim (fun h' => absurd h' hjj) Or.inr
      rcases hsep with h | h
      · exact step 2 h2 (by simpa using h)
      · exact step 3 h3 (by simpa using h)

end GaloisForLFunctions.InfiniteRankPurityTheory

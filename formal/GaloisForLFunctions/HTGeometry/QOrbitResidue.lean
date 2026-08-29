import GaloisForLFunctions.HTGeometry.RationalPolePart

/-!
# The `q`-discrete residue of a rational function along a multiplicative orbit

For a fixed pole order `d ≥ 1` and a multiplicative orbit `a q^ℤ` of nonzero points, the weighted
sum of the order-`d` principal parts along the orbit,

`∑_n (q^{-d})^n · polePart C (a q^n) d`,

is a finite sum and is invariant under the dilation `x ↦ q x`.  It therefore annihilates every
dilation coboundary `σ k − k`, so a rational function with a nonzero residue is not `q`-summable.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

/-- The `q`-discrete residue at pole order `d` along the multiplicative orbit of `a`. -/
def qOrbitResidue (q a : K) (d : ℕ) (C : RatFunc K) : K :=
  ∑ᶠ n : ℤ, (q ^ (-(d : ℤ))) ^ n * polePart C (multOrbit q a n) d

theorem qOrbitResidue_eq_sum {q a : K} {d : ℕ} (C : RatFunc K) (s : Finset ℤ)
    (hs : ∀ n : ℤ, polePart C (multOrbit q a n) d ≠ 0 → n ∈ s) :
    qOrbitResidue q a d C
      = ∑ n ∈ s, (q ^ (-(d : ℤ))) ^ n * polePart C (multOrbit q a n) d := by
  refine finsum_eq_sum_of_support_subset _ ?_
  intro n hn
  rw [Function.mem_support] at hn
  refine hs n ?_
  intro h0
  exact hn (by rw [h0, mul_zero])

/-- **The `q`-discrete residue annihilates dilation coboundaries.** -/
theorem qOrbitResidue_ratFuncScale_sub {q a : K} (hq : q ≠ 0) (ha : a ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) {d : ℕ} (hd : 0 < d) (k : RatFunc K) :
    qOrbitResidue q a d (ratFuncScale q hq k - k) = 0 := by
  classical
  set lam : K := q ^ (-(d : ℤ)) with hlam
  have hlam0 : lam ≠ 0 := zpow_ne_zero _ hq
  set P : ℤ → K := fun n => polePart k (multOrbit q a n) d with hP
  have hrel : ∀ n : ℤ,
      polePart (ratFuncScale q hq k - k) (multOrbit q a n) d = lam * P (n + 1) - P n := by
    intro n
    rw [sub_eq_add_neg, polePart_add, polePart_neg, polePart_ratFuncScale,
      ← multOrbit_succ q a hq n, sub_eq_add_neg, hlam, hP]
  have hfin := finite_support_polePart_multOrbit (g := k) hq ha hqtor hd
  set S : Finset ℤ := hfin.toFinset with hS
  set N : ℕ := S.sup (fun n => n.natAbs) with hN
  have hzero : ∀ n : ℤ, (N : ℤ) < |n| → P n = 0 := by
    intro n hn
    by_contra hcon
    have hmem : n ∈ S := by
      rw [hS, Set.Finite.mem_toFinset]
      exact hcon
    have hle : n.natAbs ≤ N := Finset.le_sup (f := fun n : ℤ => n.natAbs) hmem
    have habs : |n| ≤ (N : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hle
    omega
  set n₀ : ℤ := -(N : ℤ) - 1 with hn₀
  set M : ℕ := 2 * N + 2 with hM
  have hsupp : ∀ n : ℤ, polePart (ratFuncScale q hq k - k) (multOrbit q a n) d ≠ 0 →
      n ∈ (Finset.range M).image (fun j : ℕ => n₀ + (j : ℤ)) := by
    intro n hn
    have hne : P (n + 1) ≠ 0 ∨ P n ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hn (by rw [hrel n, hcon.1, hcon.2, mul_zero, sub_zero])
    have hbound : n₀ ≤ n ∧ n ≤ n₀ + (M : ℤ) - 1 := by
      rcases hne with h | h
      · have : |n + 1| ≤ (N : ℤ) := by
          by_contra hcon
          exact h (hzero _ (lt_of_not_ge hcon))
        rw [abs_le] at this
        constructor <;> [skip; skip] <;> push_cast [hn₀, hM] <;> omega
      · have : |n| ≤ (N : ℤ) := by
          by_contra hcon
          exact h (hzero _ (lt_of_not_ge hcon))
        rw [abs_le] at this
        constructor <;> push_cast [hn₀, hM] <;> omega
    refine Finset.mem_image.2 ⟨(n - n₀).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  rw [qOrbitResidue_eq_sum _ _ hsupp]
  rw [Finset.sum_image (by
    intro x _ y _ h
    have h' : n₀ + (x : ℤ) = n₀ + (y : ℤ) := h
    omega)]
  have hsum : ∑ j ∈ Finset.range M, lam ^ (n₀ + (j : ℤ)) *
      polePart (ratFuncScale q hq k - k) (multOrbit q a (n₀ + (j : ℤ))) d
      = lam ^ (n₀ + (M : ℤ)) * P (n₀ + (M : ℤ)) - lam ^ n₀ * P n₀ := by
    refine telescoping_sum_zero hlam0 (fun n => hrel n) n₀ M
  rw [hsum, hzero (n₀ + (M : ℤ)) (by rw [hn₀, hM]; push_cast; rw [abs_of_nonneg] <;> omega),
    hzero n₀ (by rw [hn₀]; rw [abs_of_nonpos] <;> omega)]
  ring

/-- **A nonzero `q`-discrete residue obstructs `q`-summability.** -/
theorem not_dilationTelescoped_of_qOrbitResidue_ne_zero {q a : K} (hq : q ≠ 0) (ha : a ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) {d : ℕ} (hd : 0 < d) (C : RatFunc K)
    (hres : qOrbitResidue q a d C ≠ 0) :
    ¬ ∃ k : RatFunc K, C = ratFuncScale q hq k - k := by
  rintro ⟨k, rfl⟩
  exact hres (qOrbitResidue_ratFuncScale_sub hq ha hqtor hd k)

end

end GaloisForLFunctions.HTGeometry

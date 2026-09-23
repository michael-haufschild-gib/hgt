import GaloisForLFunctions.RHTower.MobiusDivisorDilationMeanUniformRenewal

/-!
# No core-uniform one-step renewal bound

The fixed core `{2}` has arbitrarily deep one-prime extensions whose physical signed dilation
mean is negative on the square-root scale.  Thus a proof that bounds the source uniformly after
each individual prime insertion cannot close the Möbius--divisor route.  Any viable estimate must
retain cancellation between multiple inserted primes before a uniform bound is taken.
-/

open Filter Topology Finset

namespace RHTower

noncomputable section

/-- A core-uniform bound cannot control the physical dilation mean after even one new prime is
inserted.  The fixed core `{2}` has arbitrarily deep inserted-prime bands whose signed mean is
negative on the square-root scale. -/
theorem not_exists_uniform_coreTwo_insert_dilationMean_bound :
    ¬ ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ Y : ℝ, (p : ℝ) ≤ Y →
      |mobiusDivisorDilationMean (insert p ({2} : Finset ℕ)) Y| ≤ B := by
  intro hbound
  rcases hbound with ⟨B, hB, hBbound⟩
  have hcore : ({2} : Finset ℕ).Nonempty := ⟨2, by simp⟩
  have hcorePrime : ∀ q ∈ ({2} : Finset ℕ), q.Prime := by
    intro q hq
    simp only [mem_singleton] at hq
    subst q
    norm_num
  obtain ⟨η, c, T, hη, hc, hband⟩ :=
    exists_mobiusDivisorDilationMean_insert_negative_band ({2} : Finset ℕ)
      hcore hcorePrime
  let r : ℝ := B / c + 1
  have hr : 0 < r := by
    dsimp [r]
    have : 0 ≤ B / c := div_nonneg hB hc.le
    linarith
  let X : ℝ := max 2 (max T (r ^ (2 : ℕ)))
  have hX : 0 < X := by
    dsimp [X]
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let N : ℕ := ⌈X⌉₊
  have hN0 : N ≠ 0 := (Nat.ceil_pos.mpr hX).ne'
  obtain ⟨p, hp, hNp, _⟩ := Nat.exists_prime_lt_and_le_two_mul N hN0
  have hXN : X ≤ (N : ℝ) := Nat.le_ceil _
  have hNpR : (N : ℝ) < (p : ℝ) := by exact_mod_cast hNp
  have hpX : X < (p : ℝ) := lt_of_le_of_lt hXN hNpR
  have hpne : p ≠ 2 := by
    have : (2 : ℝ) < (p : ℝ) := lt_of_le_of_lt
      (show (2 : ℝ) ≤ X by dsimp [X]; exact le_max_left _ _) hpX
    exact_mod_cast this.ne.symm
  have hpT : T ≤ (p : ℝ) :=
    (le_max_left T (r ^ (2 : ℕ))).trans
      ((le_max_right 2 (max T (r ^ (2 : ℕ)))).trans hpX.le)
  have hprsq : r ^ (2 : ℕ) < (p : ℝ) :=
    lt_of_le_of_lt
      ((le_max_right T (r ^ (2 : ℕ))).trans (le_max_right 2 (max T (r ^ (2 : ℕ))))) hpX
  have hroot : r < Real.sqrt (p : ℝ) := by
    have h := Real.sqrt_lt_sqrt (sq_nonneg r) hprsq
    simpa [Real.sqrt_sq hr.le] using h
  have hscale : B < c * Real.sqrt (p : ℝ) := by
    calc
      B < c * r := by
        dsimp [r]
        field_simp [hc.ne']
        nlinarith
      _ < c * Real.sqrt (p : ℝ) := mul_lt_mul_of_pos_left hroot hc
  have hneg := hband p hp (by simp [hpne]) hpT (p : ℝ) le_rfl
    (by nlinarith [hη, show (0 : ℝ) < p by exact_mod_cast hp.pos])
  have habs := hBbound p hp hpne (p : ℝ) le_rfl
  have hlower : -B ≤ mobiusDivisorDilationMean (insert p ({2} : Finset ℕ)) (p : ℝ) := by
    have hnegabs : -mobiusDivisorDilationMean (insert p ({2} : Finset ℕ)) (p : ℝ) ≤
        |mobiusDivisorDilationMean (insert p ({2} : Finset ℕ)) (p : ℝ)| := neg_le_abs _
    linarith
  nlinarith

end

end RHTower

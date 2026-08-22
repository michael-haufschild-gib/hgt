import GaloisForLFunctions.RHTower.PrimeEulerCauchyPhaseChamber
import GaloisForLFunctions.HTGeometry.PrimeTorusKroneckerDensity

/-!
# Simultaneous phase chambers of a finite Euler packet

Each prime has an exact one-Cauchy phase chamber: the local finite-Euler diagonal is positive
exactly when `cos(x log p)` exceeds the radial Poisson threshold.  Summing over a finite prime
packet, the positive chamber is reached at `x = 0` by every summand at once.  The negative chamber
is also reached simultaneously, because unique factorization makes the prime log-frequencies
rationally independent, so the prime diagonal flow is dense in the aperture torus and can steer
every clock phase near `π` at the same time.

Consequently a finite Euler connection has **no fixed sign**, and any completed source that is
nonnegative must supply a strictly positive remainder on the simultaneous negative chamber.
-/

namespace GaloisForLFunctions.RHTower

open HTGeometry

noncomputable section

open scoped BigOperators

/-- The one-sided Cauchy diagonal of a finite Euler packet. -/
def finiteEulerOneSidedCauchyDiagonal (F : Finset ℕ) (x y : ℝ) : ℝ :=
  ∑ p ∈ F, primeEulerOneSidedCauchyDiagonal p x y

/-- The centered functional-equation-paired diagonal of a finite Euler packet. -/
def finiteEulerFEPairedCauchyDiagonal (F : Finset ℕ) (x y : ℝ) : ℝ :=
  ∑ p ∈ F, primeEulerFEPairedCauchyDiagonal p x y

theorem finiteEulerFEPairedCauchyDiagonal_eq (F : Finset ℕ) (x y : ℝ) :
    finiteEulerFEPairedCauchyDiagonal F x y = 2 * finiteEulerOneSidedCauchyDiagonal F x y := by
  rw [finiteEulerFEPairedCauchyDiagonal, finiteEulerOneSidedCauchyDiagonal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => rfl

/-! ## The simultaneous negative clock phase -/

theorem cos_lt_of_norm_exp_add_one_lt_one {theta : ℝ}
    (h : ‖Complex.exp ((theta : ℝ) * Complex.I) + 1‖ < 1) :
    Real.cos theta < -(1 / 2) := by
  have hre : (Complex.exp ((theta : ℝ) * Complex.I)).re = Real.cos theta := by
    rw [Complex.exp_ofReal_mul_I_re]
  have hnorm : ‖Complex.exp ((theta : ℝ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp_ofReal_mul_I]
  have hnsq : Complex.normSq (Complex.exp ((theta : ℝ) * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have hsq : ‖Complex.exp ((theta : ℝ) * Complex.I) + 1‖ ^ 2 = 2 + 2 * Real.cos theta := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_one, hnsq,
      map_one, mul_one, hre]
    ring
  have hlt : ‖Complex.exp ((theta : ℝ) * Complex.I) + 1‖ ^ 2 < 1 := by
    have h0 : (0 : ℝ) ≤ ‖Complex.exp ((theta : ℝ) * Complex.I) + 1‖ := norm_nonneg _
    nlinarith
  rw [hsq] at hlt
  linarith

/-- **Simultaneous negative clock phase for a finite prime packet.**  Kronecker density of the
prime diagonal flow steers every `cos(x log p)`, `p ∈ F`, below `-1/2` at one real time. -/
theorem exists_simultaneous_negative_cosine (F : Finset ℕ) (hF : ∀ p ∈ F, Nat.Prime p) :
    ∃ x : ℝ, ∀ p ∈ F, Real.cos (primeEulerClockPhase p x) < -(1 / 2) := by
  set N : ℕ := F.sup id with hN
  obtain ⟨t, ht⟩ :=
    GaloisForLFunctions.primeTorus_kronecker_dense N (fun _ => Real.pi) (by norm_num : (0:ℝ) < 1)
  refine ⟨t, fun p hp => ?_⟩
  have hple : p ≤ N := Finset.le_sup (f := id) hp
  have hpmem : (⟨p, hF p hp⟩ : Nat.Primes) ∈ primesLE N :=
    (GaloisForLFunctions.mem_primesLE N ⟨p, hF p hp⟩).mpr hple
  have hkey := ht ⟨⟨p, hF p hp⟩, hpmem⟩
  have hpi : Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I) = -1 := by
    simp
  have hnorm : ‖GaloisForLFunctions.expChar (Real.log p) t + 1‖ < 1 := by
    rw [show GaloisForLFunctions.expChar (Real.log p) t + 1
        = GaloisForLFunctions.expChar (Real.log p) t - (-1) by ring, ← hpi]
    exact hkey
  have hchar : GaloisForLFunctions.expChar (Real.log p) t
      = Complex.exp ((primeEulerClockPhase p t : ℝ) * Complex.I) := by
    rw [GaloisForLFunctions.expChar, primeEulerClockPhase]
    congr 2
    push_cast
    ring
  rw [hchar] at hnorm
  exact cos_lt_of_norm_exp_add_one_lt_one hnorm

/-! ## The finite-packet sign theorem -/

/-- `(14)`, positive half: at clock phase zero every summand is strictly positive. -/
theorem finiteEulerOneSidedCauchyDiagonal_pos_at_zero {F : Finset ℕ} (hFne : F.Nonempty)
    (hF : ∀ p ∈ F, Nat.Prime p) {y : ℝ} (hy0 : 0 < y) (hyHalf : y < 1 / 2) :
    0 < finiteEulerOneSidedCauchyDiagonal F 0 y :=
  Finset.sum_pos
    (fun p hp => primeEulerOneSidedCauchyDiagonal_pos_at_zero (hF p hp).one_lt hy0 hyHalf) hFne

/-- `(14)`, negative half: some clock phase puts every summand strictly in its negative chamber. -/
theorem exists_finiteEulerOneSidedCauchyDiagonal_neg {F : Finset ℕ} (hFne : F.Nonempty)
    (hF : ∀ p ∈ F, Nat.Prime p) {y : ℝ} (hy0 : 0 < y) (hyHalf : y < 1 / 2) :
    ∃ x : ℝ, finiteEulerOneSidedCauchyDiagonal F x y < 0 ∧
      ∀ p ∈ F, primeEulerOneSidedCauchyDiagonal p x y < 0 := by
  obtain ⟨x, hx⟩ := exists_simultaneous_negative_cosine F hF
  have hterm : ∀ p ∈ F, primeEulerOneSidedCauchyDiagonal p x y < 0 := by
    intro p hp
    rw [primeEulerOneSidedCauchyDiagonal_neg_iff (hF p hp).one_lt hy0 hyHalf]
    exact lt_trans (hx p hp)
      (by linarith [(primeEulerCauchyThreshold_mem_Ioo (hF p hp).one_lt hy0 hyHalf).1])
  exact ⟨x, Finset.sum_neg hterm hFne, hterm⟩

/-- **`(14)`: every finite nonempty prime packet visits both chambers.** -/
theorem finiteEuler_simultaneous_sign_theorem {F : Finset ℕ} (hFne : F.Nonempty)
    (hF : ∀ p ∈ F, Nat.Prime p) {y : ℝ} (hy0 : 0 < y) (hyHalf : y < 1 / 2) :
    (0 < finiteEulerOneSidedCauchyDiagonal F 0 y ∧
        0 < finiteEulerFEPairedCauchyDiagonal F 0 y) ∧
      ∃ x : ℝ, finiteEulerOneSidedCauchyDiagonal F x y < 0 ∧
        finiteEulerFEPairedCauchyDiagonal F x y < 0 := by
  obtain ⟨x, hxneg, _⟩ := exists_finiteEulerOneSidedCauchyDiagonal_neg hFne hF hy0 hyHalf
  have hpos := finiteEulerOneSidedCauchyDiagonal_pos_at_zero hFne hF hy0 hyHalf
  refine ⟨⟨hpos, ?_⟩, x, hxneg, ?_⟩
  · rw [finiteEulerFEPairedCauchyDiagonal_eq]; linarith
  · rw [finiteEulerFEPairedCauchyDiagonal_eq]; linarith

/-- `(18)`: the exact compensation obligation.  On the simultaneous negative chamber, any remainder
restoring a nonnegative completed diagonal is strictly positive. -/
theorem finiteEuler_remainder_pos_on_negative_chamber {F : Finset ℕ} (hFne : F.Nonempty)
    (hF : ∀ p ∈ F, Nat.Prime p) {y : ℝ} (hy0 : 0 < y) (hyHalf : y < 1 / 2) :
    ∃ x : ℝ, ∀ remainder : ℝ,
      0 ≤ finiteEulerOneSidedCauchyDiagonal F x y + remainder → 0 < remainder := by
  obtain ⟨x, hxneg, _⟩ := exists_finiteEulerOneSidedCauchyDiagonal_neg hFne hF hy0 hyHalf
  exact ⟨x, fun remainder hcompleted => by linarith⟩

end

end GaloisForLFunctions.RHTower

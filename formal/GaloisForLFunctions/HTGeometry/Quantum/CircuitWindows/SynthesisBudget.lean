import GaloisForLFunctions.HTGeometry.Quantum.TranslatedCircuitExcursion

/-! # Comparing the synthesis cap with the excursion budget -/
namespace GaloisForLFunctions.HTGeometry

/-- The synthesis bound is at most a polynomial in register size times the
fourth power of the first excluded budget. Its fifth power suffices alone. -/
theorem cap_le_excursion_powers {n : ℕ} (hn : 256 ≤ n) :
    160*(2*n+1)*16^n ≤ (excursionGateBudget n + 1)^5 ∧
      160*(2*n+1)*16^n ≤ 160*(2*n+1)*(128*(n+1)*(excursionGateBudget n + 1))^4 := by
  let F := 128*(n+1)
  let r := excursionGateBudget n
  have hF : 0 < F := by dsimp [F]; positivity
  have hr : r = 2^n/F := by
    change (2^n/(64*(n+1)))/2 = _
    rw [Nat.div_div_eq_div_mul,show 64*(n+1)*2 = F by dsimp [F]; ring]
  have hD := Nat.lt_mul_div_succ (2^n) hF
  rw [← hr] at hD
  have poly (k : ℕ) (hk : 256 ≤ k) : 320*128^5*(k+1)^6 ≤ 2^k := by
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      calc
        _ ≤ 2*(320*128^5*(k+1)^6) := by
          obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
          ring_nf
          omega
        _ ≤ _ := by rw [pow_succ]; omega
  have hc : 160*(2*n+1)*F^5 ≤ 2^n := by
    apply le_trans _ (poly n hn)
    dsimp [F]
    calc
      _ ≤ 160*(2*(n+1))*(128*(n+1))^5 := by
        gcongr
        omega
      _ = _ := by ring
  have h16 : (16:ℕ)^n = (2^n)^4 := by rw [← pow_mul, mul_comm n 4,pow_mul]; norm_num
  constructor
  · refine Nat.le_of_mul_le_mul_right ?_ (show 0 < F^5 by positivity)
    calc
      160*(2*n+1)*16^n*F^5 = (160*(2*n+1)*F^5)*(2^n)^4 := by rw [h16]; ring
      _ ≤ (2^n)*(2^n)^4 := Nat.mul_le_mul_right _ hc
      _ = (2^n)^5 := by ring
      _ ≤ (F*(r+1))^5 := Nat.pow_le_pow_left hD.le _
      _ = _ := by rw [mul_pow,mul_comm]
  · rw [h16]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD.le 4)

/-- A budget below either indicated power of the physical maximum fits
inside the half-budget used for separated circuit windows. -/
theorem budget_le_excursion_of_below_maximum {n m s : ℕ} (hn : 256 ≤ n)
    (hupper : m ≤ 160*(2*n+1)*16^n)
    (hs : s^5 < m ∨ 160*(2*n+1)*(128*(n+1)*s)^4 < m) :
    s ≤ excursionGateBudget n := by
  have hc := cap_le_excursion_powers hn
  by_contra! h
  rcases hs with hs | hs
  · exact (not_lt_of_ge ((hupper.trans hc.1).trans (Nat.pow_le_pow_left h 5))) hs
  · have hp := Nat.pow_le_pow_left (Nat.mul_le_mul_left (128*(n+1)) h) 4
    exact (not_lt_of_ge ((hupper.trans hc.2).trans (Nat.mul_le_mul_left _ hp))) hs

#print axioms budget_le_excursion_of_below_maximum
end GaloisForLFunctions.HTGeometry

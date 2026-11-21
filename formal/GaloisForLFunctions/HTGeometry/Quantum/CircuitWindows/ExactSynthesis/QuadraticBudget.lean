import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SynthesisBudget

/-! # The exact synthesis bound relative to the excursion budget -/
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis

/-- The quadratic synthesis bound fits in the cube of the first budget above
the excursion cutoff. Its more precise comparison loses only a polynomial
factor in the number of qubits against the square of that budget. -/
theorem budget_of_quadratic_cap {n m s : ℕ} (hn : 256 ≤ n)
    (hcap : m ≤ (4*n+1)*(2*n+2)*(2^n)^2)
    (hs : s^3 < m ∨ (4*n+1)*(2*n+2)*(128*(n+1)*s)^2 < m) :
    s ≤ excursionGateBudget n := by
  let F := 128*(n+1)
  let Q := (4*n+1)*(2*n+2)
  let r := excursionGateBudget n
  have hF : 0<F := by dsimp [F]; positivity
  have hr : r=2^n/F := by
    change (2^n/(64*(n+1)))/2=_
    rw [Nat.div_div_eq_div_mul,show 64*(n+1)*2=F by dsimp [F]; ring]
  have hD := Nat.lt_mul_div_succ (2^n) hF
  rw [← hr] at hD
  have poly (k : ℕ) (hk : 256 ≤ k) : 8*128^3*(k+1)^5 ≤ 2^k := by
    induction k,hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      calc
        _ ≤ 2*(8*128^3*(k+1)^5) := by
          obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
          ring_nf
          omega
        _ ≤ _ := by rw [pow_succ]; omega
  have hsmall : Q*F^3 ≤ 2^n := by
    apply le_trans _ (poly n hn)
    dsimp [Q,F]; ring_nf; omega
  have hQr : Q*F^2 ≤ r+1 := by
    apply Nat.le_of_mul_le_mul_right _ hF
    calc
      Q*F^2*F = Q*F^3 := by ring
      _ ≤ _ := (hsmall.trans hD.le).trans_eq (Nat.mul_comm ..)
  have hcap' : m ≤ Q*(F*(r+1))^2 := hcap.trans (Nat.mul_le_mul_left Q (Nat.pow_le_pow_left hD.le _))
  by_contra! h
  have hr' : r+1 ≤ s := h
  rcases hs with hh|hh
  · have hb : Q*(F*(r+1))^2 ≤ (r+1)^3 := by
      calc
        _ = (Q*F^2)*(r+1)^2 := by ring
        _ ≤ (r+1)*(r+1)^2 := Nat.mul_le_mul_right _ hQr
        _ = _ := by ring
    exact (not_lt_of_ge ((hcap'.trans hb).trans (Nat.pow_le_pow_left hr' 3))) hh
  · exact (not_lt_of_ge (hcap'.trans (Nat.mul_le_mul_left Q
      (Nat.pow_le_pow_left (Nat.mul_le_mul_left F hr') 2)))) hh

#print axioms budget_of_quadratic_cap
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis

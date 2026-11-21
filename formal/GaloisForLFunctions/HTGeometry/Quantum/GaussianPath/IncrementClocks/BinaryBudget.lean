import GaloisForLFunctions.HTGeometry.NearHilbertContinuousCircuitEntropyLaw
import GaloisForLFunctions.HTGeometry.PathShellEdgeTail

/-! # Binary step allocation below the exponential circuit budget -/
namespace GaloisForLFunctions.HTGeometry.IncrementClocks
noncomputable section

/-- Binary base for the number of repetitions at order floor(sqrt N)+1. -/
def stepBase (N : ℕ) := 2^(N.sqrt-16)

/-- Physical duration protected on each side of the crossing. -/
def crossingWidth (N : ℕ) : ℝ := 2^(N-26*N.sqrt)

private theorem sqrt_exponents (N : ℕ) (hs : 32 ≤ N.sqrt) :
    (N.sqrt-16)*(N.sqrt+2)+6*N.sqrt ≤ N ∧
    N-26*N.sqrt+6*N.sqrt ≤ (N.sqrt-16)*(N.sqrt+1) := by
  let s := N.sqrt
  have hlo : s^2 ≤ N := Nat.sqrt_le' N
  have hhi : N < (s+1)*(s+1) := Nat.lt_succ_sqrt N
  have hc : s-16+16=s := by dsimp [s]; omega
  have hl : 26*s ≤ s^2 := by nlinarith only [Nat.mul_le_mul_right s (show 26 ≤ s by dsimp [s]; omega)]
  have hd := Nat.sub_add_cancel (hl.trans hlo)
  change (s-16)*(s+2)+6*s ≤ N ∧ N-26*s+6*s ≤ (s-16)*(s+1)
  constructor
  · nlinarith only [hlo,congrArg (fun n => n*(s+2)) hc]
  · nlinarith only [hhi,hd,congrArg (fun n => n*(s+1)) hc,show 32 ≤ s from hs]

private theorem sqrt_overhead (N : ℕ) (hs : 32 ≤ N.sqrt) : 64*(N+1) ≤ 2^(2*N.sqrt) := by
  have hexp (s : ℕ) (h : 8 ≤ s) : 8*(s+1) ≤ 2^s := by
    induction s,h using Nat.le_induction with
    | base => norm_num
    | succ n hn ih => rw [pow_succ]; omega
  have hN := Nat.lt_succ_sqrt N
  have hs' := hexp N.sqrt (by omega)
  calc
    _ ≤ (8*(N.sqrt+1))^2 := by nlinarith only [hN]
    _ ≤ (2^N.sqrt)^2 := Nat.pow_le_pow_left hs' _
    _ = _ := by rw [← pow_mul,Nat.mul_comm N.sqrt]

/-- Every gate in all repeated, rescaled Pauli words fits in half the
exponential circuit budget. -/
theorem high_order_budget (n : ℕ) (h : 32 ≤ (n+2).sqrt) :
    let N := n+2
    let s := N.sqrt
    2*(stepBase N^(s+2)*(3^s*Fintype.card (PathLabel n))) ≤ nearHilbertContinuousCircuitBudget N := by
  intro N s
  let F := 64*(N+1)
  let m := Fintype.card (PathLabel n)
  have hm : 2*m ≤ F := by
    dsimp [m,F,N,PathLabel]; simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]; omega
  have hF : F ≤ 2^(2*s) := sqrt_overhead N h
  have h3 : (3:ℕ)^s ≤ 2^(2*s) := by rw [pow_mul]; exact Nat.pow_le_pow_left (by decide) _
  change 2*(stepBase N^(s+2)*(3^s*m)) ≤ 2^N/F
  apply (Nat.le_div_iff_mul_le (by dsimp [F]; positivity)).mpr
  calc
    _ = stepBase N^(s+2)*(3^s*((2*m)*F)) := by ring
    _ ≤ stepBase N^(s+2)*(2^(2*s)*(2^(2*s)*2^(2*s))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul h3 (Nat.mul_le_mul (hm.trans hF) hF))
    _ = 2^((s-16)*(s+2)+6*s) := by
      dsimp only [stepBase]; rw [← pow_mul,← pow_add,← pow_add,← pow_add]; congr 1; ring
    _ ≤ 2^N := Nat.pow_le_pow_right (by decide) (sqrt_exponents N h).1

/-- The binary time radius pays the order-dependent norm growth, the linear
mass of a Gaussian prefix, and the fixed error tolerance. -/
theorem high_order_time (N : ℕ) (L : ℝ) (hL : 0 ≤ L) (hs : 32 ≤ N.sqrt)
    (hscale : 100*(1+L) ≤ (2:ℝ)^N.sqrt) {m t : ℝ} (hm : m ≤ L*N)
    (ht : |t| ≤ crossingWidth N) :
    7^N.sqrt*(1+m)*|t| ≤ (stepBase N:ℝ)^(N.sqrt+1)/100 := by
  let s := N.sqrt
  have hN : (N:ℝ)+1 ≤ 2^(2*s) := by
    exact_mod_cast (show N+1 ≤ 2^(2*s) by dsimp [s]; have := sqrt_overhead N hs; omega)
  have h7 : (7:ℝ)^s ≤ 2^(3*s) := by rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hmass : 100*(1+m) ≤ 2^s*2^(2*s) := by
    apply le_trans _ (mul_le_mul hscale hN (by positivity) (by positivity))
    nlinarith only [hm,hL,show (0:ℝ) ≤ N by positivity]
  have hmass' : 100*(1+m)*|t| ≤ (2^s*2^(2*s))*crossingWidth N :=
    mul_le_mul hmass ht (abs_nonneg _) (by positivity)
  apply (le_div_iff₀ (by norm_num)).mpr
  calc
    _ = 7^s*(100*(1+m)*|t|) := by ring
    _ ≤ (2^(3*s))*((2^s*2^(2*s))*crossingWidth N) :=
      (mul_le_mul_of_nonneg_left hmass' (by positivity)).trans
        (mul_le_mul_of_nonneg_right h7 (by dsimp [crossingWidth]; positivity))
    _ = 2^(N-26*s+6*s) := by
      dsimp only [crossingWidth]; rw [← pow_add,← pow_add,← pow_add]; congr 1; ring
    _ ≤ (2:ℝ)^((s-16)*(s+1)) := pow_le_pow_right₀ (by norm_num) (sqrt_exponents N hs).2
    _ = _ := by simp only [s,stepBase,Nat.cast_pow,Nat.cast_ofNat,pow_mul]

#print axioms high_order_budget
#print axioms high_order_time
end
end GaloisForLFunctions.HTGeometry.IncrementClocks

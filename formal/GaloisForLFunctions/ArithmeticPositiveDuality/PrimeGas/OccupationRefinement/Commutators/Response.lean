import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators.Coefficients
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.Vacuum

/-! # A measured commutator forces the Born law without a power-law assumption -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators

open ModeCapacities CoherentRay UniversalResponse SquareTest

private def probabilityAt (u v : ℕ → ℝ) (p : Nat.Primes) (j k : ℕ) :=
  branch u v (rayState p j).val (rayState p k).val

private theorem branches {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) (j k : ℕ) :
    probabilityAt u v p j k = ((j+k).choose j : ℝ) * ((share u v p)^j * (share v u p)^k) := by
  change branch u v (p.val^j) (p.val^k) = _
  rw [branch_on_ray,prime_ray (hu p) (hv p),binomial, share, share, add_comm (v p.val) (u p.val)]

private theorem power_share {A : ℝ → ℂ} (seq : sequential A) (one : A 1 = 1)
    {x : ℝ} (hx : x ∈ Shares) (k : ℕ) : A (x^k) = (A x)^k := by
  induction k with
  | zero => simpa only [pow_zero] using one
  | succ k ih =>
    rw [pow_succ, seq _ ⟨pow_pos hx.1 _, pow_le_one₀ hx.1.le hx.2⟩ _ hx, ih, pow_succ]

private theorem calibration {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) (k : ℕ) :
    (1 / ((k+1:ℕ):ℝ)) * probabilityAt u v p 1 k =
      probabilityAt u v p 1 0 * (probabilityAt u v p 0 1)^k := by
  simp only [branches hu hv, Nat.choose_one_right, Nat.choose_zero_right, Nat.add_zero, Nat.zero_add,
    pow_one, pow_zero, one_mul, mul_one, Nat.cast_one, Nat.add_comm 1 k]
  field_simp [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)]

private theorem inverse_mem (k : ℕ) : (1 / ((k+1:ℕ):ℝ)) ∈ Shares :=
  ⟨one_div_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos k)), (div_le_one (Nat.cast_pos.mpr
    (Nat.succ_pos k))).mpr (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))⟩

theorem response_ladder (A : Response) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v)
    (p : Nat.Primes) (k : ℕ) : ladder (routing A.val u v) p (k+1) = (A.val (1/((k+1:ℕ):ℝ)))⁻¹ := by
  let B := probabilityAt u v p
  have mem (j k : ℕ) : B j k ∈ Shares := branch_mem hu hv _ _
  have nz (j k : ℕ) : A.val (B j k) ≠ 0 := by
    intro h
    have H := A.property.2 _ (mem j k)
    rw [h, norm_zero, zero_pow two_ne_zero] at H
    exact (mem j k).1.ne H
  have H := congrArg A.val (calibration hu hv p k)
  change A.val (1/((k+1:ℕ):ℝ) * B 1 k) = A.val (B 1 0 * B 0 1 ^ k) at H
  rw [A.property.1 _ (inverse_mem k) _ (mem 1 k), A.property.1 _ (mem 1 0) _
    ⟨pow_pos (mem 0 1).1 k, pow_le_one₀ (mem 0 1).1.le (mem 0 1).2⟩,
    power_share A.property.1 (response_at_one A) (mem 0 1)] at H
  change A.val (B 1 k) / (A.val (B 1 0) * A.val (B 0 1) ^ k) = _
  rw [← H, div_eq_mul_inv, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (nz 1 k), one_mul]

/-- A nonzero square-shell commutator calibrates an unknown bounded
multiplicative response even if some branch amplitudes initially might vanish. -/
theorem square_response_iff (A : ℝ → ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v)
    (p : Nat.Primes) :
    sequential A ∧ bounded A ∧ ‖ladder (routing A u v) p 2‖ ^ 2 = 2 ↔
      sequential A ∧ conserving A := by
  rw [← response_iff]
  constructor
  · rintro ⟨seq,bound,test⟩
    let B := probabilityAt u v p
    have mem (j k : ℕ) : B j k ∈ Shares := branch_mem hu hv _ _
    have cal := calibration hu hv p 1
    norm_num at cal
    have inv : (1/2:ℝ) ∈ Shares := ⟨by norm_num,by norm_num⟩
    have H := congrArg A cal
    change A (1/2 * B 1 1) = A (B 1 0 * B 0 1) at H
    rw [seq _ inv _ (mem 1 1), seq _ (mem 1 0) _ (mem 0 1)] at H
    change ‖A (B 1 1) / (A (B 1 0) * A (B 0 1) ^ 1)‖ ^ 2 = 2 at test
    rw [pow_one, ← H, norm_div, div_pow, norm_mul, mul_pow] at test
    have nz : ‖A (1/2)‖ ^ 2 * ‖A (B 1 1)‖ ^ 2 ≠ 0 := by
      intro h
      rw [h, div_zero] at test
      norm_num at test
    have h := (div_eq_iff nz).mp test
    have nonzero := (mul_ne_zero_iff.mp nz).2
    apply (born_iff A).mp
    refine ⟨seq,bound,?_⟩
    change 2*‖A (1/2)‖ ^ 2 = 1
    apply mul_right_cancel₀ nonzero
    rw [one_mul, mul_assoc, ← h]
  · intro H
    let R : Response := ⟨A,H⟩
    have half : (1/2:ℝ) ∈ Shares := ⟨by norm_num,by norm_num⟩
    refine ⟨H.1,((born_iff A).mpr H).2.1,?_⟩
    have step := response_ladder R hu hv p 1
    change ‖ladder (routing R.val u v) p 2‖ ^ 2 = 2
    norm_num at step
    rw [step, norm_inv, inv_pow, R.property.2 _ half]
    norm_num

#print axioms response_ladder
#print axioms square_response_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators

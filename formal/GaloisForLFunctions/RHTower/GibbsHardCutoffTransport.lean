import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Exact cutoff-scale transport and integer-birth incidence

The joint transfer `T_p F(N,x)=F(N/p,p*x)` retains literal natural division and
still forms a commutative multiplicative action. Same-sign seams commute with
unnormalized signed insertion. Integer births instead intertwine through the
exact divisibility event `p ∣ N+1`.

Zero-boundary same-sign seam data determine the full history by finite alternating
reconstruction. This injectivity has no uniform sup bound: an explicit alternating
logarithmic ramp has seam magnitude at most one and amplitude `K+1` at `p^K`.

These statements concern generic real-valued cutoff histories. They do not bound
the Möbius Gamma--Hankel energy or rule out additional source-derived dynamics.
-/

open scoped BigOperators

namespace RHTower.GibbsGas

/-- Joint integer-cutoff and real-scale transfer. -/
def hardCutoffTransfer (p : ℕ) (F : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun N x => F (N / p) ((p : ℝ) * x)

/-- Same-sign seam of a cutoff history. -/
def hardCutoffSameSign (p : ℕ) (F : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun N x => F N x + hardCutoffTransfer p F N x

/-- Unnormalized signed insertion on a cutoff history. -/
def hardCutoffSignedInsertion (p : ℕ) (F : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun N x => F N x - hardCutoffTransfer p F N x

/-- The increment admitted at the next literal integer. -/
def hardCutoffBirth (F : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun N x => F (N + 1) x - F N x

/-- The exact floors preserve the multiplicative transfer law. -/
theorem hardCutoffTransfer_mul (p q : ℕ) (F : ℕ → ℝ → ℝ) :
    hardCutoffTransfer p (hardCutoffTransfer q F) =
      hardCutoffTransfer (p * q) F := by
  funext N x
  simp only [hardCutoffTransfer, Nat.div_div_eq_div_mul, Nat.cast_mul]
  congr 1
  ring

/-- Joint cutoff-scale transfers commute, not merely their untruncated limits. -/
theorem hardCutoffTransfer_comm (p q : ℕ) (F : ℕ → ℝ → ℝ) :
    hardCutoffTransfer p (hardCutoffTransfer q F) =
      hardCutoffTransfer q (hardCutoffTransfer p F) := by
  rw [hardCutoffTransfer_mul, hardCutoffTransfer_mul, Nat.mul_comm p q]

/-- Signed insertion commutes with every same-sign seam operator. -/
theorem hardCutoffSameSign_signedInsertion (p q : ℕ) (F : ℕ → ℝ → ℝ) :
    hardCutoffSameSign p (hardCutoffSignedInsertion q F) =
      hardCutoffSignedInsertion q (hardCutoffSameSign p F) := by
  funext N x
  have h := congrFun (congrFun (hardCutoffTransfer_comm p q F) N) x
  simp only [hardCutoffSameSign, hardCutoffSignedInsertion, hardCutoffTransfer] at h ⊢
  linarith

/-- Exact antiscale histories remain antiscale under signed insertion. -/
theorem hardCutoffSignedInsertion_preserves_sameSign_kernel
    (p q : ℕ) (F : ℕ → ℝ → ℝ)
    (hF : hardCutoffSameSign p F = 0) :
    hardCutoffSameSign p (hardCutoffSignedInsertion q F) = 0 := by
  rw [hardCutoffSameSign_signedInsertion, hF]
  funext N x
  simp [hardCutoffSignedInsertion, hardCutoffTransfer]

/-- Integer births see a transferred history exactly at divisibility events. -/
theorem hardCutoffBirth_transfer (p : ℕ) (F : ℕ → ℝ → ℝ) (N : ℕ) (x : ℝ) :
    hardCutoffBirth (hardCutoffTransfer p F) N x =
      if p ∣ N + 1 then hardCutoffTransfer p (hardCutoffBirth F) N x else 0 := by
  by_cases h : p ∣ N + 1
  · simp only [hardCutoffBirth, hardCutoffTransfer, if_pos h,
      Nat.succ_div_of_dvd h]
  · simp only [hardCutoffBirth, hardCutoffTransfer, if_neg h,
      Nat.succ_div_of_not_dvd h, sub_self]

/-- The integer-birth/scale-transfer commutator is the complementary incidence channel. -/
theorem hardCutoffBirth_transfer_commutator
    (p : ℕ) (F : ℕ → ℝ → ℝ) (N : ℕ) (x : ℝ) :
    hardCutoffBirth (hardCutoffTransfer p F) N x -
        hardCutoffTransfer p (hardCutoffBirth F) N x =
      if p ∣ N + 1 then 0 else -hardCutoffTransfer p (hardCutoffBirth F) N x := by
  rw [hardCutoffBirth_transfer]
  split_ifs <;> ring

/-- At zero boundary, exact same-sign seam data determine the entire cutoff history. -/
theorem hardCutoffSameSign_zero_boundary_injective
    (p : ℕ) (hp : 2 ≤ p) (F : ℕ → ℝ → ℝ)
    (hzero : ∀ x, F 0 x = 0) (hseam : hardCutoffSameSign p F = 0) :
    F = 0 := by
  funext N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    funext x
    by_cases hN : N = 0
    · simpa [hN] using hzero x
    · have hlt : N / p < N := Nat.div_lt_self (Nat.pos_of_ne_zero hN) (by omega)
      have hsmall := congrFun (ih (N / p) hlt) ((p : ℝ) * x)
      have h := congrFun (congrFun hseam N) x
      simpa [hardCutoffSameSign, hardCutoffTransfer, hsmall] using h

/-- Exact finite reconstruction from same-sign seams, retaining the terminal boundary. -/
theorem hardCutoffSameSign_reconstruction
    (p K : ℕ) (F : ℕ → ℝ → ℝ) (N : ℕ) (x : ℝ) :
    F N x =
      (∑ j ∈ Finset.range K, (-1 : ℝ) ^ j *
        hardCutoffSameSign p F (N / p ^ j) ((p : ℝ) ^ j * x)) +
      (-1 : ℝ) ^ K * F (N / p ^ K) ((p : ℝ) ^ K * x) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    simp only [hardCutoffSameSign, hardCutoffTransfer, Nat.div_div_eq_div_mul,
      pow_succ, mul_left_comm, mul_assoc]
    simp only [hardCutoffSameSign, hardCutoffTransfer, Nat.div_div_eq_div_mul] at ih
    linear_combination ih

/-- Beyond the floor horizon, the finite reconstruction has no unrecorded boundary term. -/
theorem hardCutoffSameSign_reconstruction_of_lt
    (p K : ℕ) (F : ℕ → ℝ → ℝ) (N : ℕ) (x : ℝ)
    (hzero : ∀ y, F 0 y = 0) (hN : N < p ^ K) :
    F N x = ∑ j ∈ Finset.range K, (-1 : ℝ) ^ j *
      hardCutoffSameSign p F (N / p ^ j) ((p : ℝ) ^ j * x) := by
  have h := hardCutoffSameSign_reconstruction p K F N x
  simpa [Nat.div_eq_of_lt hN, hzero] using h

/-- An alternating logarithmic ramp, with physical zero cutoff boundary. -/
def hardCutoffAntiscaleRamp (p : ℕ) : ℕ → ℝ → ℝ :=
  fun N _ => if N = 0 then 0 else (-1 : ℝ) ^ Nat.log p N * (Nat.log p N + 1)

/-- The ramp's same-sign seam has unit magnitude at every positive cutoff. -/
theorem hardCutoffAntiscaleRamp_seam (p : ℕ) (hp : 2 ≤ p) (N : ℕ) (x : ℝ) :
    hardCutoffSameSign p (hardCutoffAntiscaleRamp p) N x =
      if N = 0 then 0 else (-1 : ℝ) ^ Nat.log p N := by
  by_cases hN : N = 0
  · simp [hN, hardCutoffSameSign, hardCutoffTransfer, hardCutoffAntiscaleRamp]
  · by_cases hNp : N < p
    · have hlog : Nat.log p N = 0 := Nat.log_eq_zero_iff.mpr (Or.inl hNp)
      simp [hardCutoffSameSign, hardCutoffTransfer, hardCutoffAntiscaleRamp,
        hN, Nat.div_eq_of_lt hNp, hlog]
    · have hle : p ≤ N := Nat.le_of_not_gt hNp
      have hdiv : N / p ≠ 0 := Nat.ne_of_gt (Nat.div_pos hle (by omega))
      have hlog := Nat.log_of_one_lt_of_le (show 1 < p by omega) hle
      simp only [hardCutoffSameSign, hardCutoffTransfer, hardCutoffAntiscaleRamp,
        if_neg hN, if_neg hdiv]
      rw [hlog]
      simp only [pow_succ, Nat.cast_add, Nat.cast_one]
      ring

/-- The ramp amplitude grows by one along each prime-power horizon. -/
theorem hardCutoffAntiscaleRamp_pow (p : ℕ) (hp : 2 ≤ p) (K : ℕ) (x : ℝ) :
    |hardCutoffAntiscaleRamp p (p ^ K) x| = (K : ℝ) + 1 := by
  have hp0 : p ≠ 0 := by omega
  rw [hardCutoffAntiscaleRamp, if_neg (pow_ne_zero K hp0),
    Nat.log_pow (show 1 < p by omega)]
  rw [abs_mul, abs_pow]
  simp only [abs_neg, abs_one, one_pow, one_mul]
  exact abs_of_nonneg (by positivity)

/-- Bounded same-sign seams and a zero initial boundary do not uniformly bound histories.
The same explicit history works at every depth, not a separately chosen finite witness. -/
theorem exists_hardCutoff_unit_seam_logarithmic_escape (p : ℕ) (hp : 2 ≤ p) :
    ∃ F : ℕ → ℝ → ℝ,
      (∀ x, F 0 x = 0) ∧
      (∀ N x, |hardCutoffSameSign p F N x| ≤ 1) ∧
      (∀ (K : ℕ) (x : ℝ), |F (p ^ K) x| = (K : ℝ) + 1) := by
  refine ⟨hardCutoffAntiscaleRamp p, ?_, ?_, hardCutoffAntiscaleRamp_pow p hp⟩
  · intro x
    simp [hardCutoffAntiscaleRamp]
  · intro N x
    rw [hardCutoffAntiscaleRamp_seam p hp]
    split_ifs <;> simp [abs_pow]

/-- There is no cutoff-uniform sup bound for all zero-boundary, unit-seam histories. -/
theorem not_hardCutoff_unit_seam_uniform_bound (p : ℕ) (hp : 2 ≤ p) :
    ¬ ∃ C : ℝ, ∀ F : ℕ → ℝ → ℝ,
      (∀ x, F 0 x = 0) →
      (∀ N x, |hardCutoffSameSign p F N x| ≤ 1) →
      ∀ N x, |F N x| ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨F, hzero, hseam, hpow⟩ := exists_hardCutoff_unit_seam_logarithmic_escape p hp
  obtain ⟨K, hK⟩ := exists_nat_gt C
  have h := hC F hzero hseam (p ^ K) 0
  rw [hpow] at h
  linarith

end RHTower.GibbsGas

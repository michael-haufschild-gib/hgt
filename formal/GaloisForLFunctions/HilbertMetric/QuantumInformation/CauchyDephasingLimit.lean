import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchyDephasing

/-!
# Exact asymptotics of repeated Cauchy dephasing

Repeated normalized Jordan inversion suppresses every coefficient between
unequal rates. The limit is the projection onto equal-rate blocks. The
finite iterates retain positivity, identity, and trace throughout.
-/

noncomputable section
open Matrix Filter
open scoped Topology ComplexOrder
namespace GaloisForLFunctions.HilbertMetric.CauchyDephasing

/-- The exact coefficient formula for repeated Cauchy dephasing. -/
def channelPower {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (coherence (r i) (r j) : ℂ) ^ k * A i j

/-- Projection onto the blocks with equal logarithmic rates. -/
def pinching {n : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := by
  classical
  exact fun i j => if r i = r j then A i j else 0

theorem channelPower_zero {n : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : channelPower 0 r A = A := by
  ext i j
  exact one_mul _

theorem channelPower_succ {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    channelPower (k + 1) r A = channel r (channelPower k r A) := by
  ext i j
  simp only [channelPower, channel, pow_succ]
  ring

/-- Composition of finite dephasing iterates adds their exponents. -/
theorem channelPower_add {n : ℕ} (k l : ℕ) (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    channelPower (k + l) r A = channelPower k r (channelPower l r A) := by
  ext i j
  simp only [channelPower, pow_add, mul_assoc]

/-- Every finite iterate preserves all Gram matrices. -/
theorem channelPower_gram_posSemidef {n m : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (B : Matrix (Fin m) (Fin n) ℂ) : (channelPower k r (Bᴴ * B)).PosSemidef := by
  induction k with
  | zero => simpa only [channelPower_zero] using posSemidef_conjTranspose_mul_self B
  | succ k ih =>
    rw [channelPower_succ, channel_eq_hadamard]
    exact ih.hadamard (symbol_posSemidef r)

theorem trace_channelPower {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : trace (channelPower k r A) = trace A := by
  simp only [Matrix.trace, Matrix.diag_apply, channelPower, coherence_self,
    Complex.ofReal_one, one_pow, one_mul]

theorem channelPower_one {n : ℕ} (k : ℕ) (r : Fin n → ℝ) : channelPower k r 1 = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp only [channelPower, coherence_self, Complex.ofReal_one, one_pow, one_mul]
  · simp only [channelPower, Matrix.one_apply_ne h, mul_zero]

/-- Unequal-rate coherences vanish; every equal-rate block survives unchanged. -/
theorem channelPower_tendsto_pinching {n : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun k => channelPower k r A) atTop (𝓝 (pinching r A)) := by
  classical
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  by_cases h : r i = r j
  · simpa only [channelPower, pinching, h, if_true, coherence_self,
      Complex.ofReal_one, one_pow, one_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => A i j) atTop (𝓝 (A i j)))
  · have hlt : coherence (r i) (r j) < 1 := by
      by_contra hn
      have heq := le_antisymm (coherence_le_one (r i) (r j)) (le_of_not_gt hn)
      exact h ((coherence_eq_one_iff _ _).mp heq)
    have hlim : Tendsto (fun k : ℕ => ((coherence (r i) (r j) ^ k : ℝ) : ℂ))
        atTop (𝓝 (0 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_pow_atTop_nhds_zero_of_lt_one (coherence_pos _ _).le hlt)
    simpa only [channelPower, pinching, if_neg h, Complex.ofReal_pow,
      Complex.ofReal_zero, zero_mul] using hlim.mul_const (A i j)

/-- The limiting block projection is already fixed by one dephasing step. -/
theorem channel_pinching {n : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : channel r (pinching r A) = pinching r A := by
  classical
  apply (channel_fixed_iff r _).mpr
  intro i j h
  exact if_neg h

/-- Applying the limiting projection twice makes no further change. -/
theorem pinching_idempotent {n : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : pinching r (pinching r A) = pinching r A := by
  classical
  ext i j
  by_cases h : r i = r j <;> simp only [pinching, h, if_true, if_false]

/-- Dephasing changes none of the coefficients retained by its limiting projection. -/
theorem pinching_channelPower {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : pinching r (channelPower k r A) = pinching r A := by
  classical
  ext i j
  by_cases h : r i = r j
  · simp only [pinching, channelPower, h, if_true, coherence_self,
      Complex.ofReal_one, one_pow, one_mul]
  · simp only [pinching, if_neg h]

#print axioms channelPower_add
#print axioms channelPower_gram_posSemidef
#print axioms trace_channelPower
#print axioms channelPower_tendsto_pinching
#print axioms channel_pinching
#print axioms pinching_idempotent
#print axioms pinching_channelPower

end GaloisForLFunctions.HilbertMetric.CauchyDephasing

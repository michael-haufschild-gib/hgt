import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeMasks

/-!
# Exact prime-power valuation masks

An exact valuation mask commutes with convolution by a sequence supported away
from the prime. No multiplicativity of the sequence being masked is assumed.
-/

open Complex
noncomputable section
namespace RHTower.WeilSingularArithmetic

def valuationMask (p k n : ℕ) : ℝ :=
  if p ^ k ∣ n ∧ ¬p ^ (k + 1) ∣ n then 1 else 0

def valuationPart (p k : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  (valuationMask p k n : ℂ) * f n

theorem valuationPart_zero (p k : ℕ) (f : ℕ → ℂ) :
    valuationPart p k f 0 = 0 := by
  simp [valuationPart, valuationMask]

theorem norm_valuationPart_le (p k : ℕ) (f : ℕ → ℂ) (n : ℕ) :
    ‖valuationPart p k f n‖ ≤ ‖f n‖ := by
  by_cases hn : p ^ k ∣ n ∧ ¬p ^ (k + 1) ∣ n
  · simp [valuationPart, valuationMask, hn]
  · simp [valuationPart, valuationMask, hn]

theorem summable_valuationPart (p k : ℕ) {f : ℕ → ℂ} {s : ℂ}
    (hf : LSeriesSummable f s) : LSeriesSummable (valuationPart p k f) s :=
  hf.norm.of_norm_bounded fun n => LSeries.norm_term_le s (norm_valuationPart_le p k f n)

theorem valuationMask_mul_of_coprime (p k a b : ℕ) (hb : b.Coprime p) :
    valuationMask p k (a * b) = valuationMask p k a := by
  have hk : p ^ k ∣ a * b ↔ p ^ k ∣ a := (hb.symm.pow_left k).dvd_mul_right
  have hk1 : p ^ (k + 1) ∣ a * b ↔ p ^ (k + 1) ∣ a :=
    (hb.symm.pow_left (k + 1)).dvd_mul_right
  simp only [valuationMask, hk, hk1]

theorem valuationPart_convolution_coprimePart (p k : ℕ) (f g : ℕ → ℂ) :
    valuationPart p k (LSeries.convolution f (coprimePart p g)) =
      LSeries.convolution (valuationPart p k f) (coprimePart p g) := by
  funext n
  simp only [valuationPart, LSeries.convolution_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  have hn := (Nat.mem_divisorsAntidiagonal.mp hab).1
  by_cases hb : ab.2.Coprime p
  · have hm : valuationMask p k n = valuationMask p k ab.1 :=
      hn ▸ valuationMask_mul_of_coprime p k ab.1 ab.2 hb
    rw [hm]
    ring
  · simp [coprimePart, coprimeMask, hb]

theorem valuationPart_zero_eq_coprimePart {p : ℕ} (hp : p.Prime) (f : ℕ → ℂ) :
    valuationPart p 0 f = coprimePart p f := by
  funext n
  have hn : n.Coprime p ↔ ¬p ∣ n := Nat.coprime_comm.trans hp.coprime_iff_not_dvd
  simp [valuationPart, valuationMask, coprimePart, coprimeMask, hn]

theorem valuationPart_sub (p k : ℕ) (f g : ℕ → ℂ) :
    valuationPart p k (f - g) = valuationPart p k f - valuationPart p k g := by
  funext n
  simp [valuationPart, mul_sub]

theorem valuationPart_smul (p k : ℕ) (c : ℂ) (f : ℕ → ℂ) :
    valuationPart p k (c • f) = c • valuationPart p k f := by
  funext n
  simp only [valuationPart, Pi.smul_apply, smul_eq_mul]
  ring

end RHTower.WeilSingularArithmetic

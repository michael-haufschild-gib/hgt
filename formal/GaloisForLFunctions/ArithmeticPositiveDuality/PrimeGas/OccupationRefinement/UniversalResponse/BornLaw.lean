import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SurvivalClock.Existence

/-! # Born normalization forced by bounded sequential composition and one binary test -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse

open Set SurvivalClock ModeCapacities
open scoped NNReal

abbrev Shares := Ioc (0:ℝ) 1

def sequential (A : ℝ → ℂ) := ∀ x ∈ Shares, ∀ y ∈ Shares, A (x*y)=A x*A y
def bounded (A : ℝ → ℂ) := ∃ C : ℝ, ∀ x ∈ Shares, ‖A x‖≤C
def balanced (A : ℝ → ℂ) := 2*‖A (1/2)‖^2=1
def born (A : ℝ → ℂ) := ∀ x ∈ Shares, ‖A x‖^2=x

private theorem contractive {A : ℝ → ℂ} (seq : sequential A) (bound : bounded A) (test : balanced A)
    {x : ℝ} (hx : x∈Shares) : ‖A x‖≤1 := by
  have half : (1/2:ℝ)∈Shares := ⟨by norm_num,by norm_num⟩
  have nz : A (1/2)≠0 := by
    intro h
    norm_num [balanced,h] at test
  have origin : A 1=1 := by
    have H := seq 1 ⟨zero_lt_one,le_rfl⟩ _ half
    rw [one_mul] at H
    exact mul_right_cancel₀ nz (H.symm.trans (one_mul _).symm)
  have inside (n : ℕ) : x^n∈Shares := ⟨pow_pos hx.1 n,pow_le_one₀ hx.1.le hx.2⟩
  have iterate (n : ℕ) : A (x^n)=(A x)^n := by
    induction n with
    | zero => simpa only [pow_zero] using origin
    | succ n ih => rw [pow_succ,seq _ (inside n) x hx,ih,pow_succ]
  obtain ⟨C,hC⟩ := bound
  by_contra! above
  obtain ⟨n,large⟩ := pow_unbounded_of_one_lt C above
  have H := hC (x^n) (inside n)
  rw [iterate,norm_pow] at H
  exact large.not_ge H

private theorem realize (p : Nat.Primes) {x : ℝ} (hx : x∈Shares) :
    ∃ t : ℝ≥0, survive t p.val=x := by
  have pos := Real.log_pos (Nat.one_lt_cast.mpr p.property.one_lt : (1:ℝ)<p.val)
  let t : ℝ≥0 := ⟨-Real.log x/Real.log p.val,div_nonneg (neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2)) pos.le⟩
  refine ⟨t,?_⟩
  change Real.exp (-(-Real.log x/Real.log p.val)*Real.log p.val)=x
  rw [neg_div,neg_neg,div_mul_cancel₀ _ pos.ne',Real.exp_log hx.1]

private theorem born_of_balanced {A : ℝ → ℂ} (seq : sequential A) (bound : bounded A) (test : balanced A) :
    born A := by
  let p : Nat.Primes := ⟨2,Nat.prime_two⟩
  let X (t : ℝ≥0) := (residueClock p t).val
  have inside (t : ℝ≥0) : X t∈Shares := ⟨survive_pos t p,(residueClock p t).property.2⟩
  let q : Curve := fun t => ⟨‖A (X t)‖^2,sq_nonneg _,
    (sq_le_one_iff₀ (norm_nonneg _)).mpr (contractive seq bound test (inside t))⟩
  have calibratedQ : calibrated p q := by
    constructor
    · intro a b
      change ‖A (X (a+b))‖^2=‖A (X a)‖^2*‖A (X b)‖^2
      have mulX : X (a+b)=X a*X b := (residueClock_calibrated p).1 a b
      rw [mulX,seq _ (inside a) _ (inside b),norm_mul,mul_pow]
    · have unit : X 1=1/2 := (residueClock_calibrated p).2
      change ‖A (X 1)‖^2=1/2
      rw [unit]
      change 2*‖A (1/2)‖^2=1 at test
      linarith only [test]
  intro x hx
  obtain ⟨t,ht⟩ := realize p hx
  have H := (calibrated_iff p q).mp calibratedQ t
  change ‖A (survive t p.val)‖^2=survive t p.val at H
  rwa [ht] at H

/-- One equal split fixes the modulus for all positive branch probabilities,
without selecting a power law or imposing continuity. -/
theorem born_iff (A : ℝ → ℂ) :
    sequential A ∧ bounded A ∧ balanced A ↔ sequential A ∧ born A := by
  constructor
  · exact fun ⟨seq,b,h⟩ => ⟨seq,born_of_balanced seq b h⟩
  · rintro ⟨seq,h⟩
    refine ⟨seq,⟨1,fun x hx => (sq_le_one_iff₀ (norm_nonneg _)).mp ((h x hx).le.trans hx.2)⟩,?_⟩
    change 2*‖A (1/2)‖^2=1
    rw [h (1/2) ⟨by norm_num,by norm_num⟩]
    norm_num

#print axioms born_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse

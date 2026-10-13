import GaloisForLFunctions.RHTower.JointAncestryTypicalCapArith

/-!
# Exceptional phase vectors of the coherent model

For a prime set `P` inside the window `(X, CX]` and a zero copy `q` with `|Re ρ − ½| ≤ Θ`, the
error `Δ_q(k)` of the coherent exponential model (`capDelta`) is small off few phase vectors.
Its four random parts have second moments `N^{|P|}` times
`4V‖ρ − ½‖²(log C)²` (coherence, two slots) and `¼ X^{2(Θ−σ)} C^{2Θ} V` (second order, two
slots), with `V = ¼ X^{2Θ} Σ_p p^{−2σ}`.  The deterministic part is at most
`X^{−2Θ}V + (8/3) X^{Θ−σ} C^{2Θ} V` (`capDelta_le_random_add_det`).  Markov in `L²` then counts the
exceptional vectors (`card_capDelta_gt_le`).
-/

open Complex Finset
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- The coherent coefficients `a_p = ½ p^{−σ}`. -/
def capCoef (σ : ℝ) {P : Finset Nat.Primes} (p : ↥P) : ℝ :=
  1 / 2 * Real.exp (-σ * Real.log ((p : Nat.Primes) : ℕ))

/-- `X^{ρ−½}`. -/
def capXc (X : ℝ) (q : XiZeroCopy) : ℂ := Complex.exp (((q.1 : ℂ) - 1 / 2) * Real.log X)

/-- `X^{½−ρ}`. -/
def capYc (X : ℝ) (q : XiZeroCopy) : ℂ := Complex.exp ((1 / 2 - (q.1 : ℂ)) * Real.log X)

/-- The model error `Δ_q(k)`. -/
def capDelta (σ X : ℝ) {N : ℕ} (P : Finset Nat.Primes) (q : XiZeroCopy) (k : ↥P → Fin N) : ℝ :=
  ‖∑ p : ↥P, 1 / 2 * typCapB σ q p * conj (unitRoot N ^ ((k p : Fin N) : ℕ)) -
      capXc X q * ∑ p : ↥P, (capCoef σ p : ℂ) * conj (unitRoot N ^ ((k p : Fin N) : ℕ))‖ +
    ‖∑ p : ↥P, 1 / 2 * typCapA σ q p * unitRoot N ^ ((k p : Fin N) : ℕ) -
      capYc X q * conj (∑ p : ↥P, (capCoef σ p : ℂ) * conj (unitRoot N ^ ((k p : Fin N) : ℕ)))‖ +
    1 / 2 * ‖∑ p : ↥P, (1 / 2 * typCapB σ q p) ^ 2 * conj (unitRoot N ^ ((k p : Fin N) : ℕ)) ^ 2‖ +
    1 / 2 * ‖∑ p : ↥P, (1 / 2 * typCapA σ q p) ^ 2 * (unitRoot N ^ ((k p : Fin N) : ℕ)) ^ 2‖ +
    1 / 4 * ‖∑ p : ↥P, typCapA σ q p * typCapB σ q p‖ +
    2 / 3 * ∑ p : ↥P, (1 / 2 * (‖typCapA σ q p‖ + ‖typCapB σ q p‖)) ^ 3

/-- The window variance `V = ¼ X^{2Θ} Σ_p p^{−2σ}`. -/
def capVar (Θ σ X : ℝ) (P : Finset Nat.Primes) : ℝ :=
  1 / 4 * Real.exp (2 * Θ * Real.log X) *
    ∑ p : ↥P, Real.exp (-(2 * σ) * Real.log ((p : Nat.Primes) : ℕ))

/-! ## Phase functions with mean zero -/

theorem sum_conj_unitRoot_pow {N : ℕ} (hN : 3 ≤ N) :
    ∑ x : Fin N, conj (unitRoot N ^ (x : ℕ)) = 0 := by
  rw [← map_sum]
  have := sum_unitRoot_pow_mul_eq_zero (N := N) (m := 1) one_ne_zero (by omega)
  simp only [one_mul] at this; rw [this, map_zero]

theorem sum_unitRoot_pow' {N : ℕ} (hN : 3 ≤ N) : ∑ x : Fin N, unitRoot N ^ (x : ℕ) = 0 := by
  have := sum_unitRoot_pow_mul_eq_zero (N := N) (m := 1) one_ne_zero (by omega)
  simpa using this

theorem sum_unitRoot_pow_sq {N : ℕ} (hN : 3 ≤ N) :
    ∑ x : Fin N, (unitRoot N ^ (x : ℕ)) ^ 2 = 0 := by
  have := sum_unitRoot_pow_mul_eq_zero (N := N) (m := 2) two_ne_zero (by omega)
  simp_rw [← pow_mul, mul_comm (2 : ℕ)] at this ⊢; exact this

theorem sum_conj_unitRoot_pow_sq {N : ℕ} (hN : 3 ≤ N) :
    ∑ x : Fin N, conj (unitRoot N ^ (x : ℕ)) ^ 2 = 0 := by
  simp_rw [← map_pow]; rw [← map_sum, sum_unitRoot_pow_sq hN, map_zero]

theorem norm_conj_unitRoot_pow_sq (N : ℕ) (x : Fin N) : ‖conj (unitRoot N ^ (x : ℕ)) ^ 2‖ = 1 := by
  rw [norm_pow, Complex.norm_conj, norm_unitRoot_pow, one_pow]

theorem norm_unitRoot_pow_sq (N : ℕ) (x : Fin N) : ‖(unitRoot N ^ (x : ℕ)) ^ 2‖ = 1 := by
  rw [norm_pow, norm_unitRoot_pow, one_pow]

/-! ## The four random parts -/

theorem capDelta_eq (σ X : ℝ) {N : ℕ} (P : Finset Nat.Primes) (q : XiZeroCopy)
    (k : ↥P → Fin N) : capDelta σ X P q k =
      ‖∑ p : ↥P, (1 / 2 * typCapB σ q p - capXc X q * capCoef σ p) *
        conj (unitRoot N ^ ((k p : Fin N) : ℕ))‖ +
      ‖∑ p : ↥P, (1 / 2 * typCapA σ q p - capYc X q * capCoef σ p) *
        unitRoot N ^ ((k p : Fin N) : ℕ)‖ +
      1 / 2 * ‖∑ p : ↥P, (1 / 2 * typCapB σ q p) ^ 2 * conj (unitRoot N ^ ((k p : Fin N) : ℕ)) ^ 2‖ +
      1 / 2 * ‖∑ p : ↥P, (1 / 2 * typCapA σ q p) ^ 2 * (unitRoot N ^ ((k p : Fin N) : ℕ)) ^ 2‖ +
      (1 / 4 * ‖∑ p : ↥P, typCapA σ q p * typCapB σ q p‖ +
        2 / 3 * ∑ p : ↥P, (1 / 2 * (‖typCapA σ q p‖ + ‖typCapB σ q p‖)) ^ 3) := by
  unfold capDelta
  have h1 : ∑ p : ↥P, 1 / 2 * typCapB σ q p * conj (unitRoot N ^ ((k p : Fin N) : ℕ)) -
      capXc X q * ∑ p : ↥P, (capCoef σ p : ℂ) * conj (unitRoot N ^ ((k p : Fin N) : ℕ)) =
      ∑ p : ↥P, (1 / 2 * typCapB σ q p - capXc X q * capCoef σ p) *
        conj (unitRoot N ^ ((k p : Fin N) : ℕ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => by ring
  have h2 : ∑ p : ↥P, 1 / 2 * typCapA σ q p * unitRoot N ^ ((k p : Fin N) : ℕ) -
      capYc X q * conj (∑ p : ↥P, (capCoef σ p : ℂ) * conj (unitRoot N ^ ((k p : Fin N) : ℕ))) =
      ∑ p : ↥P, (1 / 2 * typCapA σ q p - capYc X q * capCoef σ p) *
        unitRoot N ^ ((k p : Fin N) : ℕ) := by
    rw [map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, Complex.conj_ofReal, Complex.conj_conj]; ring
  rw [h1, h2]; ring

/-! ## Coefficient bounds in a window -/

section Window

variable {σ Θ X C : ℝ} {P : Finset Nat.Primes}

theorem log_prime_mem_window (hX : 1 ≤ X) (hP : ∀ p ∈ P, X < (((p : Nat.Primes) : ℕ) : ℝ) ∧
    (((p : Nat.Primes) : ℕ) : ℝ) ≤ C * X) (p : ↥P) :
    Real.log X < Real.log (((p : Nat.Primes) : ℕ) : ℝ) ∧
      Real.log (((p : Nat.Primes) : ℕ) : ℝ) ≤ Real.log C + Real.log X := by
  obtain ⟨h1, h2⟩ := hP p p.2
  have hX0 : 0 < X := by linarith
  have hC : 0 < C := by
    by_contra h; push Not at h; nlinarith
  refine ⟨Real.log_lt_log hX0 h1, ?_⟩
  rw [← Real.log_mul hC.ne' hX0.ne']
  exact Real.log_le_log (by linarith) h2

theorem norm_coh_capB_le (hX : 1 ≤ X) (hP : ∀ p ∈ P, X < (((p : Nat.Primes) : ℕ) : ℝ) ∧
    (((p : Nat.Primes) : ℕ) : ℝ) ≤ C * X) {q : XiZeroCopy} (hq : |(q.1 : ℂ).re - 1 / 2| ≤ Θ)
    (hz : ‖(q.1 : ℂ) - 1 / 2‖ * Real.log C ≤ 1) (p : ↥P) :
    ‖1 / 2 * typCapB σ q p - capXc X q * capCoef σ p‖ ≤
      Real.exp (-σ * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) * Real.exp (Θ * Real.log X) *
        (‖(q.1 : ℂ) - 1 / 2‖ * Real.log C) := by
  obtain ⟨h1, h2⟩ := hP p p.2
  have hX0 : 0 < X := by linarith
  have hLX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hcoh := norm_cexp_log_sub_le (z := (q.1 : ℂ) - 1 / 2) hX0 h1 h2 hz
  have hlogC : 0 ≤ Real.log C := by have := log_prime_mem_window hX hP p; linarith
  rw [capB_eq, capXc, capCoef]
  generalize hLp : Real.log (((p : Nat.Primes) : ℕ) : ℝ) = Lp at hcoh ⊢
  generalize hLX' : Real.log X = LX at hcoh hLX ⊢
  set z : ℂ := (q.1 : ℂ) - 1 / 2 with hzdef
  have heq : 1 / 2 * (Complex.exp (-σ * (Lp : ℂ)) * Complex.exp (z * (Lp : ℂ))) -
      Complex.exp (z * (LX : ℂ)) * ((1 / 2 * Real.exp (-σ * Lp) : ℝ) : ℂ) =
      1 / 2 * Complex.exp (-σ * (Lp : ℂ)) *
        (Complex.exp (z * (Lp : ℂ)) - Complex.exp (z * (LX : ℂ))) := by
    rw [Complex.ofReal_mul, Complex.ofReal_exp]; push_cast; ring
  rw [heq, norm_mul, norm_mul]
  have hn : ‖Complex.exp (-σ * (Lp : ℂ))‖ = Real.exp (-σ * Lp) := by
    rw [Complex.norm_exp]; congr 1; simp
  rw [hn]
  have hre : z.re ≤ Θ := by
    simp only [hzdef, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re]
    have := (abs_le.mp hq).2; norm_num at this ⊢; linarith
  have hexp : Real.exp (z.re * LX) ≤ Real.exp (Θ * LX) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre hLX)
  have hE := Real.exp_pos (-σ * Lp)
  have hz0 : 0 ≤ ‖z‖ * Real.log C := by positivity
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h12]
  have step : ‖Complex.exp (z * (Lp : ℂ)) - Complex.exp (z * (LX : ℂ))‖ ≤
      2 * Real.exp (Θ * LX) * (‖z‖ * Real.log C) :=
    hcoh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num)) hz0)
  calc 1 / 2 * Real.exp (-σ * Lp) * ‖Complex.exp (z * (Lp : ℂ)) - Complex.exp (z * (LX : ℂ))‖
      ≤ 1 / 2 * Real.exp (-σ * Lp) * (2 * Real.exp (Θ * LX) * (‖z‖ * Real.log C)) :=
        mul_le_mul_of_nonneg_left step (by positivity)
    _ = Real.exp (-σ * Lp) * Real.exp (Θ * LX) * (‖z‖ * Real.log C) := by ring

theorem norm_coh_capA_le (hX : 1 ≤ X) (hP : ∀ p ∈ P, X < (((p : Nat.Primes) : ℕ) : ℝ) ∧
    (((p : Nat.Primes) : ℕ) : ℝ) ≤ C * X) {q : XiZeroCopy} (hq : |(q.1 : ℂ).re - 1 / 2| ≤ Θ)
    (hz : ‖1 / 2 - (q.1 : ℂ)‖ * Real.log C ≤ 1) (p : ↥P) :
    ‖1 / 2 * typCapA σ q p - capYc X q * capCoef σ p‖ ≤
      Real.exp (-σ * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) * Real.exp (Θ * Real.log X) *
        (‖1 / 2 - (q.1 : ℂ)‖ * Real.log C) := by
  obtain ⟨h1, h2⟩ := hP p p.2
  have hX0 : 0 < X := by linarith
  have hLX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hcoh := norm_cexp_log_sub_le (z := 1 / 2 - (q.1 : ℂ)) hX0 h1 h2 hz
  have hlogC : 0 ≤ Real.log C := by have := log_prime_mem_window hX hP p; linarith
  rw [capA_eq, capYc, capCoef]
  generalize hLp : Real.log (((p : Nat.Primes) : ℕ) : ℝ) = Lp at hcoh ⊢
  generalize hLX' : Real.log X = LX at hcoh hLX ⊢
  set z : ℂ := 1 / 2 - (q.1 : ℂ) with hzdef
  have heq : 1 / 2 * (Complex.exp (-σ * (Lp : ℂ)) * Complex.exp (z * (Lp : ℂ))) -
      Complex.exp (z * (LX : ℂ)) * ((1 / 2 * Real.exp (-σ * Lp) : ℝ) : ℂ) =
      1 / 2 * Complex.exp (-σ * (Lp : ℂ)) *
        (Complex.exp (z * (Lp : ℂ)) - Complex.exp (z * (LX : ℂ))) := by
    rw [Complex.ofReal_mul, Complex.ofReal_exp]; push_cast; ring
  rw [heq, norm_mul, norm_mul]
  have hn : ‖Complex.exp (-σ * (Lp : ℂ))‖ = Real.exp (-σ * Lp) := by
    rw [Complex.norm_exp]; congr 1; simp
  rw [hn]
  have hre : z.re ≤ Θ := by
    simp only [hzdef, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re]
    have := (abs_le.mp hq).1; norm_num at this ⊢; linarith
  have hexp : Real.exp (z.re * LX) ≤ Real.exp (Θ * LX) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre hLX)
  have hE := Real.exp_pos (-σ * Lp)
  have hz0 : 0 ≤ ‖z‖ * Real.log C := by positivity
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h12]
  have step : ‖Complex.exp (z * (Lp : ℂ)) - Complex.exp (z * (LX : ℂ))‖ ≤
      2 * Real.exp (Θ * LX) * (‖z‖ * Real.log C) :=
    hcoh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num)) hz0)
  calc 1 / 2 * Real.exp (-σ * Lp) * ‖Complex.exp (z * (Lp : ℂ)) - Complex.exp (z * (LX : ℂ))‖
      ≤ 1 / 2 * Real.exp (-σ * Lp) * (2 * Real.exp (Θ * LX) * (‖z‖ * Real.log C)) :=
        mul_le_mul_of_nonneg_left step (by positivity)
    _ = Real.exp (-σ * Lp) * Real.exp (Θ * LX) * (‖z‖ * Real.log C) := by ring

/-- `Σ_p p^{−2σ} p^{2Θ} ≤ C^{2Θ} · 4V`. -/
theorem sum_exp_two_mul_le (hX : 1 ≤ X) (hΘ : 0 ≤ Θ)
    (hP : ∀ p ∈ P, X < (((p : Nat.Primes) : ℕ) : ℝ) ∧ (((p : Nat.Primes) : ℕ) : ℝ) ≤ C * X) :
    ∑ p : ↥P, Real.exp (2 * (Θ - σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) ≤
      Real.exp (2 * Θ * Real.log C) * (4 * capVar Θ σ X P) := by
  unfold capVar
  rw [show Real.exp (2 * Θ * Real.log C) * (4 * (1 / 4 * Real.exp (2 * Θ * Real.log X) *
      ∑ p : ↥P, Real.exp (-(2 * σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)))) =
      ∑ p : ↥P, Real.exp (2 * Θ * (Real.log C + Real.log X)) *
        Real.exp (-(2 * σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) by
    rw [← Finset.mul_sum, mul_add, Real.exp_add]; ring]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have := (log_prime_mem_window hX hP p).2
  nlinarith

/-- `max_p p^{Θ−σ} ≤ X^{Θ−σ}` for `Θ ≤ σ`. -/
theorem exp_le_of_window (hX : 1 ≤ X) {c : ℝ} (hc : c ≤ 0)
    (hP : ∀ p ∈ P, X < (((p : Nat.Primes) : ℕ) : ℝ) ∧ (((p : Nat.Primes) : ℕ) : ℝ) ≤ C * X)
    (p : ↥P) : Real.exp (c * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) ≤ Real.exp (c * Real.log X) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (log_prime_mem_window hX hP p).1.le hc)

end Window

/-! ## Counting the exceptional vectors -/

section Count

variable {σ Θ X C : ℝ} {P : Finset Nat.Primes}

theorem sum_sq_coh_capB_le (hX : 1 ≤ X) (hP : ∀ p ∈ P, X < (((p : Nat.Primes) : ℕ) : ℝ) ∧
    (((p : Nat.Primes) : ℕ) : ℝ) ≤ C * X) {q : XiZeroCopy} (hq : |(q.1 : ℂ).re - 1 / 2| ≤ Θ)
    (hz : ‖(q.1 : ℂ) - 1 / 2‖ * Real.log C ≤ 1) :
    ∑ p : ↥P, ‖1 / 2 * typCapB σ q p - capXc X q * capCoef σ p‖ ^ 2 ≤
      4 * capVar Θ σ X P * (‖(q.1 : ℂ) - 1 / 2‖ * Real.log C) ^ 2 := by
  have h := fun p => pow_le_pow_left₀ (norm_nonneg _) (norm_coh_capB_le (σ := σ) hX hP hq hz p) 2
  refine (Finset.sum_le_sum fun p _ => h p).trans (le_of_eq ?_)
  unfold capVar
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  have : ((2 : ℕ) : ℝ) * (-σ * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) =
      -(2 * σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ) := by push_cast; ring
  rw [this, show ((2 : ℕ) : ℝ) * (Θ * Real.log X) = 2 * Θ * Real.log X by push_cast; ring]
  ring

theorem sum_sq_coh_capA_le (hX : 1 ≤ X) (hP : ∀ p ∈ P, X < (((p : Nat.Primes) : ℕ) : ℝ) ∧
    (((p : Nat.Primes) : ℕ) : ℝ) ≤ C * X) {q : XiZeroCopy} (hq : |(q.1 : ℂ).re - 1 / 2| ≤ Θ)
    (hz : ‖(q.1 : ℂ) - 1 / 2‖ * Real.log C ≤ 1) :
    ∑ p : ↥P, ‖1 / 2 * typCapA σ q p - capYc X q * capCoef σ p‖ ^ 2 ≤
      4 * capVar Θ σ X P * (‖(q.1 : ℂ) - 1 / 2‖ * Real.log C) ^ 2 := by
  have hz' : ‖1 / 2 - (q.1 : ℂ)‖ * Real.log C ≤ 1 := by rw [norm_sub_rev]; exact hz
  have h := fun p => pow_le_pow_left₀ (norm_nonneg _) (norm_coh_capA_le (σ := σ) hX hP hq hz' p) 2
  refine (Finset.sum_le_sum fun p _ => h p).trans (le_of_eq ?_)
  unfold capVar
  rw [norm_sub_rev, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  have : ((2 : ℕ) : ℝ) * (-σ * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) =
      -(2 * σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ) := by push_cast; ring
  rw [this, show ((2 : ℕ) : ℝ) * (Θ * Real.log X) = 2 * Θ * Real.log X by push_cast; ring]
  ring

/-- The square of a coefficient is at most `p^{2(Θ−σ)}`. -/
theorem sq_norm_le_of_le {x c L : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.exp (c * L)) :
    x ^ 2 ≤ Real.exp (2 * c * L) := by
  calc x ^ 2 ≤ Real.exp (c * L) ^ 2 := pow_le_pow_left₀ hx0 hx 2
    _ = Real.exp (2 * c * L) := by rw [sq, ← Real.exp_add]; congr 1; ring

theorem sum_sq_sq_capB_le (hX : 1 ≤ X) (hΘ : 0 ≤ Θ) (hΘσ : Θ ≤ σ)
    (hP : ∀ p ∈ P, X < (((p : Nat.Primes) : ℕ) : ℝ) ∧ (((p : Nat.Primes) : ℕ) : ℝ) ≤ C * X)
    {q : XiZeroCopy} (hq : |(q.1 : ℂ).re - 1 / 2| ≤ Θ) :
    ∑ p : ↥P, ‖(1 / 2 * typCapB σ q p) ^ 2‖ ^ 2 ≤
      1 / 16 * Real.exp (2 * (Θ - σ) * Real.log X) *
        (Real.exp (2 * Θ * Real.log C) * (4 * capVar Θ σ X P)) := by
  have hsum := sum_exp_two_mul_le (σ := σ) hX hΘ hP
  have hterm : ∀ p : ↥P, ‖(1 / 2 * typCapB σ q p) ^ 2‖ ^ 2 ≤
      1 / 16 * Real.exp (2 * (Θ - σ) * Real.log X) *
        Real.exp (2 * (Θ - σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) := by
    intro p
    have hB := norm_capB_le (σ := σ) hq p
    have hB2 := sq_norm_le_of_le (norm_nonneg _) hB
    have hle := exp_le_of_window hX (c := 2 * (Θ - σ)) (by linarith) hP p
    rw [norm_pow, norm_mul]
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h12]
    have hB0 := norm_nonneg (typCapB σ q p)
    have hE1 := Real.exp_pos (2 * (Θ - σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ))
    calc ((1 / 2 * ‖typCapB σ q p‖) ^ 2) ^ 2 = 1 / 16 * (‖typCapB σ q p‖ ^ 2 * ‖typCapB σ q p‖ ^ 2) := by
          ring
      _ ≤ 1 / 16 * (Real.exp (2 * (Θ - σ) * Real.log X) *
          Real.exp (2 * (Θ - σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ))) := by
          gcongr
          · exact hB2.trans hle
      _ = _ := by ring
  refine (Finset.sum_le_sum fun p _ => hterm p).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

theorem sum_sq_sq_capA_le (hX : 1 ≤ X) (hΘ : 0 ≤ Θ) (hΘσ : Θ ≤ σ)
    (hP : ∀ p ∈ P, X < (((p : Nat.Primes) : ℕ) : ℝ) ∧ (((p : Nat.Primes) : ℕ) : ℝ) ≤ C * X)
    {q : XiZeroCopy} (hq : |(q.1 : ℂ).re - 1 / 2| ≤ Θ) :
    ∑ p : ↥P, ‖(1 / 2 * typCapA σ q p) ^ 2‖ ^ 2 ≤
      1 / 16 * Real.exp (2 * (Θ - σ) * Real.log X) *
        (Real.exp (2 * Θ * Real.log C) * (4 * capVar Θ σ X P)) := by
  have hsum := sum_exp_two_mul_le (σ := σ) hX hΘ hP
  have hterm : ∀ p : ↥P, ‖(1 / 2 * typCapA σ q p) ^ 2‖ ^ 2 ≤
      1 / 16 * Real.exp (2 * (Θ - σ) * Real.log X) *
        Real.exp (2 * (Θ - σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) := by
    intro p
    have hB := norm_capA_le (σ := σ) hq p
    have hB2 := sq_norm_le_of_le (norm_nonneg _) hB
    have hle := exp_le_of_window hX (c := 2 * (Θ - σ)) (by linarith) hP p
    rw [norm_pow, norm_mul]
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h12]
    have hB0 := norm_nonneg (typCapA σ q p)
    calc ((1 / 2 * ‖typCapA σ q p‖) ^ 2) ^ 2 = 1 / 16 * (‖typCapA σ q p‖ ^ 2 * ‖typCapA σ q p‖ ^ 2) := by
          ring
      _ ≤ 1 / 16 * (Real.exp (2 * (Θ - σ) * Real.log X) *
          Real.exp (2 * (Θ - σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ))) := by
          gcongr
          · exact hB2.trans hle
      _ = _ := by ring
  refine (Finset.sum_le_sum fun p _ => hterm p).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- The deterministic part of `Δ`. -/
theorem capDelta_det_le (hX : 1 ≤ X) (hΘ : 0 ≤ Θ) (hΘσ : Θ ≤ σ)
    (hP : ∀ p ∈ P, X < (((p : Nat.Primes) : ℕ) : ℝ) ∧ (((p : Nat.Primes) : ℕ) : ℝ) ≤ C * X)
    {q : XiZeroCopy} (hq : |(q.1 : ℂ).re - 1 / 2| ≤ Θ) :
    1 / 4 * ‖∑ p : ↥P, typCapA σ q p * typCapB σ q p‖ +
        2 / 3 * ∑ p : ↥P, (1 / 2 * (‖typCapA σ q p‖ + ‖typCapB σ q p‖)) ^ 3 ≤
      Real.exp (-(2 * Θ) * Real.log X) * capVar Θ σ X P +
        2 / 3 * Real.exp ((Θ - σ) * Real.log X) *
          (Real.exp (2 * Θ * Real.log C) * (4 * capVar Θ σ X P)) := by
  have hsum := sum_exp_two_mul_le (σ := σ) hX hΘ hP
  have h1 : 1 / 4 * ‖∑ p : ↥P, typCapA σ q p * typCapB σ q p‖ ≤
      Real.exp (-(2 * Θ) * Real.log X) * capVar Θ σ X P := by
    have : ‖∑ p : ↥P, typCapA σ q p * typCapB σ q p‖ ≤
        ∑ p : ↥P, Real.exp (-(2 * σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) := by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
      rw [capA_mul_capB, Complex.norm_exp]
      generalize Real.log (((p : Nat.Primes) : ℕ) : ℝ) = L
      congr 1; simp
    unfold capVar
    have hE : Real.exp (-(2 * Θ) * Real.log X) * Real.exp (2 * Θ * Real.log X) = 1 := by
      rw [← Real.exp_add]; simp
    rw [show Real.exp (-(2 * Θ) * Real.log X) * (1 / 4 * Real.exp (2 * Θ * Real.log X) *
        ∑ p : ↥P, Real.exp (-(2 * σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ))) =
        1 / 4 * (∑ p : ↥P, Real.exp (-(2 * σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ))) *
          (Real.exp (-(2 * Θ) * Real.log X) * Real.exp (2 * Θ * Real.log X)) by ring, hE,
      mul_one]
    linarith
  have h2 : 2 / 3 * ∑ p : ↥P, (1 / 2 * (‖typCapA σ q p‖ + ‖typCapB σ q p‖)) ^ 3 ≤
      2 / 3 * Real.exp ((Θ - σ) * Real.log X) *
        (Real.exp (2 * Θ * Real.log C) * (4 * capVar Θ σ X P)) := by
    have hterm : ∀ p : ↥P, (1 / 2 * (‖typCapA σ q p‖ + ‖typCapB σ q p‖)) ^ 3 ≤
        Real.exp ((Θ - σ) * Real.log X) *
          Real.exp (2 * (Θ - σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) := by
      intro p
      have hA := norm_capA_le (σ := σ) hq p
      have hB := norm_capB_le (σ := σ) hq p
      set e := Real.exp ((Θ - σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ))
      have hm : 1 / 2 * (‖typCapA σ q p‖ + ‖typCapB σ q p‖) ≤ e := by linarith
      have hm0 : 0 ≤ 1 / 2 * (‖typCapA σ q p‖ + ‖typCapB σ q p‖) := by positivity
      have h3 := pow_le_pow_left₀ hm0 hm 3
      have he3 : e ^ 3 = e * Real.exp (2 * (Θ - σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) := by
        rw [show e ^ 3 = e * e ^ 2 by ring, ← Real.exp_nat_mul]; congr 2; push_cast; ring
      have hle := exp_le_of_window hX (c := Θ - σ) (by linarith) hP p
      have hE2 := Real.exp_pos (2 * (Θ - σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ))
      calc _ ≤ e ^ 3 := h3
        _ = _ := he3
        _ ≤ _ := mul_le_mul_of_nonneg_right hle hE2.le
    have := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => hterm p
    rw [← Finset.mul_sum] at this
    have h0 : 0 ≤ Real.exp ((Θ - σ) * Real.log X) := (Real.exp_pos _).le
    calc 2 / 3 * ∑ p : ↥P, (1 / 2 * (‖typCapA σ q p‖ + ‖typCapB σ q p‖)) ^ 3 ≤
        2 / 3 * (Real.exp ((Θ - σ) * Real.log X) *
          ∑ p : ↥P, Real.exp (2 * (Θ - σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ))) := by
          gcongr
      _ ≤ 2 / 3 * (Real.exp ((Θ - σ) * Real.log X) *
          (Real.exp (2 * Θ * Real.log C) * (4 * capVar Θ σ X P))) := by
          gcongr
      _ = _ := by ring
  linarith

/-- **Counting exceptional vectors.** -/
theorem card_capDelta_gt_le {N : ℕ} (hN : 3 ≤ N) (hX : 1 ≤ X) (hΘ : 0 ≤ Θ) (hΘσ : Θ ≤ σ)
    (hP : ∀ p ∈ P, X < (((p : Nat.Primes) : ℕ) : ℝ) ∧ (((p : Nat.Primes) : ℕ) : ℝ) ≤ C * X)
    {q : XiZeroCopy} (hq : |(q.1 : ℂ).re - 1 / 2| ≤ Θ)
    (hz : ‖(q.1 : ℂ) - 1 / 2‖ * Real.log C ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hdet : Real.exp (-(2 * Θ) * Real.log X) * capVar Θ σ X P +
        2 / 3 * Real.exp ((Θ - σ) * Real.log X) *
          (Real.exp (2 * Θ * Real.log C) * (4 * capVar Θ σ X P)) ≤ δ / 2) :
    ((Finset.univ.filter fun k : ↥P → Fin N => δ < capDelta σ X P q k).card : ℝ) ≤
      (N : ℝ) ^ Fintype.card ↥P * (2 * (64 / δ ^ 2) *
        (4 * capVar Θ σ X P * (‖(q.1 : ℂ) - 1 / 2‖ * Real.log C) ^ 2) +
        2 * (16 / δ ^ 2) * (1 / 16 * Real.exp (2 * (Θ - σ) * Real.log X) *
          (Real.exp (2 * Θ * Real.log C) * (4 * capVar Θ σ X P)))) := by
  set n : ℝ := (N : ℝ) ^ Fintype.card ↥P
  set Y1 : (↥P → Fin N) → ℂ := fun k => ∑ p : ↥P, (1 / 2 * typCapB σ q p - capXc X q * capCoef σ p) *
    conj (unitRoot N ^ ((k p : Fin N) : ℕ))
  set Y2 : (↥P → Fin N) → ℂ := fun k => ∑ p : ↥P, (1 / 2 * typCapA σ q p - capYc X q * capCoef σ p) *
    unitRoot N ^ ((k p : Fin N) : ℕ)
  set Y3 : (↥P → Fin N) → ℂ := fun k => ∑ p : ↥P, (1 / 2 * typCapB σ q p) ^ 2 *
    conj (unitRoot N ^ ((k p : Fin N) : ℕ)) ^ 2
  set Y4 : (↥P → Fin N) → ℂ := fun k => ∑ p : ↥P, (1 / 2 * typCapA σ q p) ^ 2 *
    (unitRoot N ^ ((k p : Fin N) : ℕ)) ^ 2
  have hdet' := (capDelta_det_le (σ := σ) hX hΘ hΘσ hP hq).trans hdet
  have hsub : (Finset.univ.filter fun k : ↥P → Fin N => δ < capDelta σ X P q k) ⊆
      ((Finset.univ.filter fun k => δ / 8 < ‖Y1 k‖) ∪ (Finset.univ.filter fun k => δ / 8 < ‖Y2 k‖))
        ∪ ((Finset.univ.filter fun k => δ / 4 < ‖Y3 k‖) ∪
          (Finset.univ.filter fun k => δ / 4 < ‖Y4 k‖)) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hk ⊢
    by_contra hno
    push Not at hno
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hno
    rw [capDelta_eq] at hk
    simp only [Y1, Y2, Y3, Y4] at h1 h2 h3 h4
    linarith
  have hc1 := card_lt_norm_le Y1 (by positivity : 0 < δ / 8)
  have hc2 := card_lt_norm_le Y2 (by positivity : 0 < δ / 8)
  have hc3 := card_lt_norm_le Y3 (by positivity : 0 < δ / 4)
  have hc4 := card_lt_norm_le Y4 (by positivity : 0 < δ / 4)
  have hs1 : ∑ k, ‖Y1 k‖ ^ 2 ≤ n * (4 * capVar Θ σ X P * (‖(q.1 : ℂ) - 1 / 2‖ * Real.log C) ^ 2) := by
    rw [sum_normSq_sum_mul_phase (fun x : Fin N => conj (unitRoot N ^ (x : ℕ)))
      (sum_conj_unitRoot_pow hN) (fun x => by rw [Complex.norm_conj, norm_unitRoot_pow])]
    exact mul_le_mul_of_nonneg_left (sum_sq_coh_capB_le hX hP hq hz) (by positivity)
  have hs2 : ∑ k, ‖Y2 k‖ ^ 2 ≤ n * (4 * capVar Θ σ X P * (‖(q.1 : ℂ) - 1 / 2‖ * Real.log C) ^ 2) := by
    rw [sum_normSq_sum_mul_phase (fun x : Fin N => unitRoot N ^ (x : ℕ))
      (sum_unitRoot_pow' hN) (fun x => norm_unitRoot_pow N _)]
    exact mul_le_mul_of_nonneg_left (sum_sq_coh_capA_le hX hP hq hz) (by positivity)
  have hs3 : ∑ k, ‖Y3 k‖ ^ 2 ≤ n * (1 / 16 * Real.exp (2 * (Θ - σ) * Real.log X) *
      (Real.exp (2 * Θ * Real.log C) * (4 * capVar Θ σ X P))) := by
    rw [sum_normSq_sum_mul_phase (fun x : Fin N => conj (unitRoot N ^ (x : ℕ)) ^ 2)
      (sum_conj_unitRoot_pow_sq hN) (fun x => norm_conj_unitRoot_pow_sq N x)]
    exact mul_le_mul_of_nonneg_left (sum_sq_sq_capB_le hX hΘ hΘσ hP hq) (by positivity)
  have hs4 : ∑ k, ‖Y4 k‖ ^ 2 ≤ n * (1 / 16 * Real.exp (2 * (Θ - σ) * Real.log X) *
      (Real.exp (2 * Θ * Real.log C) * (4 * capVar Θ σ X P))) := by
    rw [sum_normSq_sum_mul_phase (fun x : Fin N => (unitRoot N ^ (x : ℕ)) ^ 2)
      (sum_unitRoot_pow_sq hN) (fun x => norm_unitRoot_pow_sq N x)]
    exact mul_le_mul_of_nonneg_left (sum_sq_sq_capA_le hX hΘ hΘσ hP hq) (by positivity)
  have hcard := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le ((Finset.univ.filter fun k => δ / 8 < ‖Y1 k‖) ∪
    (Finset.univ.filter fun k => δ / 8 < ‖Y2 k‖)) ((Finset.univ.filter fun k => δ / 4 < ‖Y3 k‖) ∪
      (Finset.univ.filter fun k => δ / 4 < ‖Y4 k‖))
  have hu2 := Finset.card_union_le (Finset.univ.filter fun k => δ / 8 < ‖Y1 k‖)
    (Finset.univ.filter fun k => δ / 8 < ‖Y2 k‖)
  have hu3 := Finset.card_union_le (Finset.univ.filter fun k => δ / 4 < ‖Y3 k‖)
    (Finset.univ.filter fun k => δ / 4 < ‖Y4 k‖)
  have hd8 : (δ / 8) ^ 2 = δ ^ 2 / 64 := by ring
  have hd4 : (δ / 4) ^ 2 = δ ^ 2 / 16 := by ring
  rw [hd8] at hc1 hc2; rw [hd4] at hc3 hc4
  have hδ2 : 0 < δ ^ 2 := by positivity
  have e1 : (∑ k, ‖Y1 k‖ ^ 2) / (δ ^ 2 / 64) = 64 / δ ^ 2 * ∑ k, ‖Y1 k‖ ^ 2 := by field_simp
  have e2 : (∑ k, ‖Y2 k‖ ^ 2) / (δ ^ 2 / 64) = 64 / δ ^ 2 * ∑ k, ‖Y2 k‖ ^ 2 := by field_simp
  have e3 : (∑ k, ‖Y3 k‖ ^ 2) / (δ ^ 2 / 16) = 16 / δ ^ 2 * ∑ k, ‖Y3 k‖ ^ 2 := by field_simp
  have e4 : (∑ k, ‖Y4 k‖ ^ 2) / (δ ^ 2 / 16) = 16 / δ ^ 2 * ∑ k, ‖Y4 k‖ ^ 2 := by field_simp
  rw [e1] at hc1; rw [e2] at hc2; rw [e3] at hc3; rw [e4] at hc4
  have h64 : (0 : ℝ) ≤ 64 / δ ^ 2 := by positivity
  have h16 : (0 : ℝ) ≤ 16 / δ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hs1 h64
  have := mul_le_mul_of_nonneg_left hs2 h64
  have := mul_le_mul_of_nonneg_left hs3 h16
  have := mul_le_mul_of_nonneg_left hs4 h16
  have hcR : ((Finset.univ.filter fun k : ↥P → Fin N => δ < capDelta σ X P q k).card : ℝ) ≤
      ((Finset.univ.filter fun k => δ / 8 < ‖Y1 k‖).card : ℝ) +
      ((Finset.univ.filter fun k => δ / 8 < ‖Y2 k‖).card : ℝ) +
      ((Finset.univ.filter fun k => δ / 4 < ‖Y3 k‖).card : ℝ) +
      ((Finset.univ.filter fun k => δ / 4 < ‖Y4 k‖).card : ℝ) := by
    have : (Finset.univ.filter fun k : ↥P → Fin N => δ < capDelta σ X P q k).card ≤
        (Finset.univ.filter fun k => δ / 8 < ‖Y1 k‖).card +
        (Finset.univ.filter fun k => δ / 8 < ‖Y2 k‖).card +
        ((Finset.univ.filter fun k => δ / 4 < ‖Y3 k‖).card +
        (Finset.univ.filter fun k => δ / 4 < ‖Y4 k‖).card) := by omega
    have := (Nat.cast_le (α := ℝ)).mpr this
    push_cast at this; linarith
  nlinarith

end Count

end

end RHTower

import GaloisForLFunctions.RHTower.Sieve.TwistedSelbergForms

/-!
# The gcd-logarithmic twisted Selberg coefficient

`c_{a,b}(m,n) log(ma, nb)` is the `u`-derivative at `u = 0` of `μ(m)μ(n)(ma, nb)^{1+u}/(mn)`, so it is a
Leibniz derivation of `c_{a,b}` (`bivariateDerivation_twistedGcdLogCoeff`). Differentiating the
Euler factorization `c_{a,b} = (F ⋆ G) ⋆ P` factor by factor gives
(`twistedGcdLogCoeff_eq_convolution`)

`c_{a,b} log(ma, nb) = (F' ⋆ G + F ⋆ G') ⋆ P + (F ⋆ G) ⋆ P^{log}`,

with `F' = Δ' ⋆ μ_{b,a} + Δ ⋆ μ'_{b,a}` (`Δ'(m,m) = Δ(m,m) log m`, `μ'_{b,a} = μ_{b,a} log(mn)`),
`G' = E'_{ab} ⋆ R_{b,a}` (`E'` the corpus differentiated correction, restricted to pairs coprime to
`ab`), and `P^{log}` the gcd-logarithmic principal coefficient.

**Local check at `p | a`.** With `δ = 1 − XY/p`, `D = 1/δ`, `P = D(1 − X/p)(1 − Y/p)`,
`P^{log} = D^{log}(1 − X/p)(1 − Y/p)` where `D^{log} δ = (log p/p)XY·D`, and `R = 1/(1 − Y/p)`:
`(−(log p/p)XY(1 − Y) − δ log p·Y) R P + δ(1 − Y) R P^{log} = −log p·Y(1 − X/p)`, the local factor of
`c_{a,b} log(ma, nb)`. At `p ∤ ab` it is the corpus identity `c log(m,n) = E ⋆ P^{log} + E' ⋆ P`.
-/

open ArithmeticFunction Finset Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- `c_{a,b}(m,n) log(ma, nb)`. -/
def twistedGcdLogCoeff (a b m n : ℕ) : ℝ :=
  twistedOriginalCoeff a b m n * Real.log (Nat.gcd (m * a) (n * b) : ℝ)

/-- `Δ'_q(m,n) = Δ_q(m,n) log m`. -/
def diagMoebiusLog (q m n : ℕ) : ℝ := diagMoebius q m n * Real.log m

/-- `μ'_{b,a}(m,n) = μ_{b,a}(m,n) log(mn)`. -/
def moebiusDvdPairLog (a b m n : ℕ) : ℝ := moebiusDvdPair a b m n * Real.log ((m * n : ℕ) : ℝ)

/-- The differentiated correction restricted to pairs coprime to `q`. -/
def corrLogCoprime (q m n : ℕ) : ℝ :=
  if Nat.Coprime (m * n) q then selbergEulerCorrectionLogCoeff m n else 0

/-- `F' = Δ' ⋆ μ_{b,a} + Δ ⋆ μ'_{b,a}`. -/
def twistFiniteLog (a b m n : ℕ) : ℝ :=
  bivariateDirichletConvolution (diagMoebiusLog (a * b)) (moebiusDvdPair a b) m n +
    bivariateDirichletConvolution (diagMoebius (a * b)) (moebiusDvdPairLog a b) m n

/-- `G' = E'_{ab} ⋆ R_{b,a}`. -/
def twistSummableLog (a b : ℕ) : ℕ → ℕ → ℝ :=
  bivariateDirichletConvolution (corrLogCoprime (a * b)) (smoothRecipPair a b)

/-- The right-hand side `(F' ⋆ G + F ⋆ G') ⋆ P + (F ⋆ G) ⋆ P^{log}`. -/
def twistGcdLogSide (a b : ℕ) : ℕ → ℕ → ℝ := fun m n =>
  bivariateDirichletConvolution
      (fun m n => bivariateDirichletConvolution (twistFiniteLog a b) (twistSummable a b) m n +
        bivariateDirichletConvolution (twistFinite a b) (twistSummableLog a b) m n)
      selbergPrincipalCoeff m n +
    bivariateDirichletConvolution
      (bivariateDirichletConvolution (twistFinite a b) (twistSummable a b))
      selbergGcdLogPrincipalCoeff m n

/-! ## Derivations -/

/-- Derivations need to be checked only on positive pairs. -/
theorem BivariateDerivation.of_pos {f D : ℕ → ℕ → ℝ} (hf1 : f 1 1 = 1) (hD1 : D 1 1 = 0)
    (hpos : ∀ {a b c d : ℕ}, 0 < a → 0 < b → 0 < c → 0 < d → Nat.Coprime (a * b) (c * d) →
      D (a * c) (b * d) = D a b * f c d + f a b * D c d) : BivariateDerivation f D := by
  refine ⟨hD1, fun {a b c d} h => ?_⟩
  by_cases hab0 : a * b = 0
  · have hcd1 : c * d = 1 := by rw [Nat.Coprime, hab0] at h; simpa using h
    have hc1 : c = 1 := Nat.dvd_one.mp ⟨d, hcd1.symm⟩
    have hd1 : d = 1 := Nat.dvd_one.mp ⟨c, by simpa [Nat.mul_comm] using hcd1.symm⟩
    subst c; subst d; simp [hf1, hD1]
  by_cases hcd0 : c * d = 0
  · have hab1 : a * b = 1 := by rw [Nat.Coprime, hcd0] at h; simpa using h
    have ha1 : a = 1 := Nat.dvd_one.mp ⟨b, hab1.symm⟩
    have hb1 : b = 1 := Nat.dvd_one.mp ⟨a, by simpa [Nat.mul_comm] using hab1.symm⟩
    subst a; subst b; simp [hf1, hD1]
  exact hpos (Nat.pos_of_ne_zero (left_ne_zero_of_mul hab0))
    (Nat.pos_of_ne_zero (right_ne_zero_of_mul hab0)) (Nat.pos_of_ne_zero (left_ne_zero_of_mul hcd0))
    (Nat.pos_of_ne_zero (right_ne_zero_of_mul hcd0)) h

theorem bivariateDerivation_twistedGcdLogCoeff {a b : ℕ} (hab : Nat.Coprime a b) (ha : a ≠ 0)
    (hb : b ≠ 0) :
    BivariateDerivation (twistedOriginalCoeff a b) (twistedGcdLogCoeff a b) := by
  have hf := bivariateMultiplicative_twistedOriginalCoeff hab ha hb
  refine BivariateDerivation.of_pos hf.one (by simp [twistedGcdLogCoeff, hab.gcd_eq_one])
    fun {m₁ n₁ m₂ n₂} hm₁ hn₁ hm₂ hn₂ h => ?_
  unfold twistedGcdLogCoeff
  rw [hf.map_mul_of_pair_coprime h,
    gcd_mul_twist hab ha hb hm₁.ne' hn₁.ne' hm₂.ne' hn₂.ne' h]
  have hg₁ : (0 : ℝ) < Nat.gcd (m₁ * a) (n₁ * b) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left _ (by positivity)
  have hg₂ : (0 : ℝ) < Nat.gcd (m₂ * a) (n₂ * b) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left _ (by positivity)
  push_cast
  rw [Real.log_mul hg₁.ne' hg₂.ne']
  ring

theorem bivariateDerivation_diagMoebiusLog (q : ℕ) :
    BivariateDerivation (diagMoebius q) (diagMoebiusLog q) := by
  have hf := bivariateMultiplicative_diagMoebius q
  refine BivariateDerivation.of_pos hf.one (by simp [diagMoebiusLog])
    fun {m₁ n₁ m₂ n₂} hm₁ hn₁ hm₂ hn₂ h => ?_
  unfold diagMoebiusLog
  rw [hf.map_mul_of_pair_coprime h]
  push_cast
  rw [Real.log_mul (by positivity) (by positivity)]
  ring

theorem bivariateDerivation_moebiusDvdPairLog (a b : ℕ) :
    BivariateDerivation (moebiusDvdPair a b) (moebiusDvdPairLog a b) := by
  have hf := bivariateMultiplicative_moebiusDvdPair a b
  refine BivariateDerivation.of_pos hf.one (by simp [moebiusDvdPairLog])
    fun {m₁ n₁ m₂ n₂} hm₁ hn₁ hm₂ hn₂ h => ?_
  unfold moebiusDvdPairLog
  rw [hf.map_mul_of_pair_coprime h]
  push_cast
  rw [show (m₁ : ℝ) * m₂ * (n₁ * n₂) = (m₁ * n₁) * (m₂ * n₂) by ring,
    Real.log_mul (by positivity) (by positivity)]
  ring

theorem bivariateDerivation_corrLogCoprime (q : ℕ) :
    BivariateDerivation (corrCoprime q) (corrLogCoprime q) := by
  have hE := bivariateDerivation_selbergEulerCorrectionLogCoeff
  refine ⟨?_, fun {a b c d} h => ?_⟩
  · unfold corrLogCoprime; rw [if_pos (by simp)]; exact hE.one
  · unfold corrLogCoprime corrCoprime
    rw [show a * c * (b * d) = (a * b) * (c * d) by ring]
    by_cases h1 : Nat.Coprime (a * b) q <;> by_cases h2 : Nat.Coprime (c * d) q
    · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨h1, h2⟩), if_pos h1, if_pos h1, if_pos h2,
        if_pos h2]
      exact hE.leibniz h
    all_goals
      rw [if_neg (fun h' => by
        have := Nat.coprime_mul_iff_left.mp h'
        tauto)]
      split_ifs; ring

theorem bivariateDerivation_twistFiniteLog (a b : ℕ) :
    BivariateDerivation (twistFinite a b) (twistFiniteLog a b) :=
  BivariateDerivation.convolution (bivariateMultiplicative_diagMoebius _)
    (bivariateMultiplicative_moebiusDvdPair a b) (bivariateDerivation_diagMoebiusLog _)
    (bivariateDerivation_moebiusDvdPairLog a b)

theorem bivariateDirichletConvolution_zero_right (f : ℕ → ℕ → ℝ) (m n : ℕ) :
    bivariateDirichletConvolution f (fun _ _ => 0) m n = 0 := by
  unfold bivariateDirichletConvolution
  split_ifs <;> simp

theorem bivariateDerivation_twistSummableLog (a b : ℕ) :
    BivariateDerivation (twistSummable a b) (twistSummableLog a b) := by
  have h := BivariateDerivation.convolution (bivariateMultiplicative_corrCoprime (a * b))
    (bivariateMultiplicative_smoothRecipPair a b) (bivariateDerivation_corrLogCoprime (a * b))
    (bivariateDerivation_zero _)
  simp only [bivariateDirichletConvolution_zero_right, add_zero] at h
  exact h

/-! ## Local factors -/

/-- `μ(p^j) log p^j` on the divisors of `q` at `p | q`: `−log p` at `j = 1`, zero otherwise. -/
def localMoebiusDvdLog (p j : ℕ) : ℝ := if j = 1 then -Real.log p else 0

theorem diagMoebiusLog_prime_pow_of_dvd {q p : ℕ} (hq : Squarefree q) (hp : p.Prime) (hpq : p ∣ q)
    (i j : ℕ) : diagMoebiusLog q (p ^ i) (p ^ j) =
      -additiveBivariateDiagonalMonomial (Real.log p / p) i j := by
  unfold diagMoebiusLog
  rw [diagMoebius_prime_pow_of_dvd hq hp hpq]
  unfold selbergLocalEulerDenominator additiveBivariateOne additiveBivariateDiagonalMonomial
  push_cast
  rw [Real.log_pow]
  by_cases h11 : i = 1 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := h11
    rw [if_neg (by omega), if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
    push_cast
    ring
  · rw [if_neg h11, if_neg h11]
    by_cases h00 : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h00
      simp
    · rw [if_neg h00]
      simp

theorem diagMoebiusLog_prime_pow_of_not_dvd {q p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) (i j : ℕ) :
    diagMoebiusLog q (p ^ i) (p ^ j) = 0 := by
  unfold diagMoebiusLog
  rw [diagMoebius_prime_pow_of_not_dvd hp hpq]
  unfold additiveBivariateOne
  by_cases h : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, zero_mul]

theorem moebiusDvdPair_prime_pow_of_dvd_left {a b p : ℕ} (ha : Squarefree a) (hp : p.Prime)
    (hpa : p ∣ a) (hpb : ¬ p ∣ b) (i j : ℕ) :
    moebiusDvdPair a b (p ^ i) (p ^ j) = if i = 0 then localMoebiusDvd j else 0 := by
  unfold moebiusDvdPair
  rw [moebiusDvd_prime_pow_of_not_dvd hpb, moebiusDvd_prime_pow_of_dvd ha hp hpa]
  split_ifs <;> simp

theorem moebiusDvdPair_prime_pow_of_dvd_right {a b p : ℕ} (hb : Squarefree b) (hp : p.Prime)
    (hpb : p ∣ b) (hpa : ¬ p ∣ a) (i j : ℕ) :
    moebiusDvdPair a b (p ^ i) (p ^ j) = if j = 0 then localMoebiusDvd i else 0 := by
  unfold moebiusDvdPair
  rw [moebiusDvd_prime_pow_of_dvd hb hp hpb, moebiusDvd_prime_pow_of_not_dvd hpa]
  split_ifs <;> simp

theorem moebiusDvdPair_prime_pow_of_not_dvd {a b p : ℕ} (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (i j : ℕ) :
    moebiusDvdPair a b (p ^ i) (p ^ j) = additiveBivariateOne i j := by
  unfold moebiusDvdPair additiveBivariateOne
  rw [moebiusDvd_prime_pow_of_not_dvd hpb, moebiusDvd_prime_pow_of_not_dvd hpa]
  split_ifs <;> simp_all

theorem moebiusDvdPairLog_prime_pow_of_dvd_left {a b p : ℕ} (ha : Squarefree a) (hp : p.Prime)
    (hpa : p ∣ a) (hpb : ¬ p ∣ b) (i j : ℕ) :
    moebiusDvdPairLog a b (p ^ i) (p ^ j) = if i = 0 then localMoebiusDvdLog p j else 0 := by
  unfold moebiusDvdPairLog
  rw [moebiusDvdPair_prime_pow_of_dvd_left ha hp hpa hpb, ← pow_add]
  push_cast
  rw [Real.log_pow]
  unfold localMoebiusDvd localMoebiusDvdLog
  by_cases hi : i = 0
  · subst hi
    rcases Nat.lt_or_ge j 2 with hj | hj
    · interval_cases j <;> simp
    · simp [show j ≠ 0 by omega, show j ≠ 1 by omega]
  · simp [hi]

theorem moebiusDvdPairLog_prime_pow_of_dvd_right {a b p : ℕ} (hb : Squarefree b) (hp : p.Prime)
    (hpb : p ∣ b) (hpa : ¬ p ∣ a) (i j : ℕ) :
    moebiusDvdPairLog a b (p ^ i) (p ^ j) = if j = 0 then localMoebiusDvdLog p i else 0 := by
  unfold moebiusDvdPairLog
  rw [moebiusDvdPair_prime_pow_of_dvd_right hb hp hpb hpa, ← pow_add]
  push_cast
  rw [Real.log_pow]
  unfold localMoebiusDvd localMoebiusDvdLog
  by_cases hj : j = 0
  · subst hj
    rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i <;> simp
    · simp [show i ≠ 0 by omega, show i ≠ 1 by omega]
  · simp [hj]

theorem moebiusDvdPairLog_prime_pow_of_not_dvd {a b p : ℕ} (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (i j : ℕ) : moebiusDvdPairLog a b (p ^ i) (p ^ j) = 0 := by
  unfold moebiusDvdPairLog
  rw [moebiusDvdPair_prime_pow_of_not_dvd hpa hpb]
  unfold additiveBivariateOne
  by_cases h : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, zero_mul]

theorem corrLogCoprime_prime_pow_of_dvd {q p : ℕ} (hp : p.Prime) (hpq : p ∣ q) (i j : ℕ) :
    corrLogCoprime q (p ^ i) (p ^ j) = 0 := by
  unfold corrLogCoprime
  by_cases h : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [← pow_add, if_neg]
    intro hc
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hc (dvd_pow_self p (by omega)) hpq)

theorem corrLogCoprime_prime_pow_of_not_dvd {q p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) (i j : ℕ) :
    corrLogCoprime q (p ^ i) (p ^ j) = selbergCorrectionLogLocal p i j := by
  unfold corrLogCoprime
  rw [if_pos (by rw [← pow_add]; exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq).pow_left _),
    selbergEulerCorrectionLogCoeff_prime_pow hp]

theorem smoothRecipPair_prime_pow_of_dvd_left {a b p : ℕ} (ha : a ≠ 0) (hp : p.Prime)
    (hpa : p ∣ a) (hpb : ¬ p ∣ b) (i j : ℕ) :
    smoothRecipPair a b (p ^ i) (p ^ j) = if i = 0 then (1 / (p : ℝ)) ^ j else 0 := by
  unfold smoothRecipPair
  rw [smoothRecip_prime_pow_of_not_dvd hp hpb, smoothRecip_prime_pow_of_dvd ha hp hpa]
  split_ifs <;> simp

theorem smoothRecipPair_prime_pow_of_dvd_right {a b p : ℕ} (hb : b ≠ 0) (hp : p.Prime)
    (hpb : p ∣ b) (hpa : ¬ p ∣ a) (i j : ℕ) :
    smoothRecipPair a b (p ^ i) (p ^ j) = if j = 0 then (1 / (p : ℝ)) ^ i else 0 := by
  unfold smoothRecipPair
  rw [smoothRecip_prime_pow_of_dvd hb hp hpb, smoothRecip_prime_pow_of_not_dvd hp hpa]
  split_ifs <;> simp

theorem smoothRecipPair_prime_pow_of_not_dvd {a b p : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a)
    (hpb : ¬ p ∣ b) (i j : ℕ) : smoothRecipPair a b (p ^ i) (p ^ j) = additiveBivariateOne i j := by
  unfold smoothRecipPair additiveBivariateOne
  rw [smoothRecip_prime_pow_of_not_dvd hp hpb, smoothRecip_prime_pow_of_not_dvd hp hpa]
  split_ifs <;> simp_all

/-- The local factor `−log p · Y(1 − X/p)` of `c_{a,b} log(ma, nb)` at `p | a`. -/
theorem twistedGcdLogCoeff_prime_pow_of_dvd_left {a b p : ℕ} (hab : Nat.Coprime a b)
    (ha : Squarefree a) (hp : p.Prime) (hpa : p ∣ a) (i j : ℕ) :
    twistedGcdLogCoeff a b (p ^ i) (p ^ j) = localMoebiusFactor p i * localMoebiusDvdLog p j := by
  unfold twistedGcdLogCoeff
  rw [twistedOriginalCoeff_prime_pow_of_dvd_left hab ha hp hpa]
  obtain ⟨a', rfl⟩ := hpa
  have hpb : ¬ p ∣ b := fun h => hp.ne_one (Nat.eq_one_of_dvd_coprimes hab (dvd_mul_right p a') h)
  have ha'b : Nat.Coprime a' b := Nat.Coprime.coprime_dvd_left (dvd_mul_left a' p) hab
  have hpbC : Nat.Coprime p b := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpb
  unfold twistLocal localMoebiusFactor localMoebiusDvdLog
  rcases Nat.lt_or_ge i 2 with hi | hi
  · rcases Nat.lt_or_ge j 2 with hj | hj
    · have g01 : Nat.gcd (p ^ 0 * (p * a')) (p ^ 1 * b) = p := by
        rw [pow_zero, one_mul, pow_one, Nat.gcd_mul_left, ha'b.gcd_eq_one, mul_one]
      have g10 : Nat.gcd (p ^ 1 * (p * a')) (p ^ 0 * b) = 1 := by
        rw [pow_zero, one_mul, pow_one]
        exact (Nat.Coprime.mul_left hpbC hab).gcd_eq_one
      have g11 : Nat.gcd (p ^ 1 * (p * a')) (p ^ 1 * b) = p := by
        rw [pow_one, Nat.gcd_mul_left, hab.gcd_eq_one, mul_one]
      have g00 : Nat.gcd (p ^ 0 * (p * a')) (p ^ 0 * b) = 1 := by
        rw [pow_zero, one_mul, one_mul]; exact hab.gcd_eq_one
      interval_cases i <;> interval_cases j
      · rw [g00]; simp
      · rw [g01]; simp
      · rw [g10]; simp
      · rw [g11]; simp
    · simp [show j ≠ 0 by omega, show j ≠ 1 by omega]
  · simp [show i ≠ 0 by omega, show i ≠ 1 by omega]

/-- The local factor `−log p · X(1 − Y/p)` of `c_{a,b} log(ma, nb)` at `p | b`. -/
theorem twistedGcdLogCoeff_prime_pow_of_dvd_right {a b p : ℕ} (hab : Nat.Coprime a b)
    (hb : Squarefree b) (hp : p.Prime) (hpb : p ∣ b) (i j : ℕ) :
    twistedGcdLogCoeff a b (p ^ i) (p ^ j) = localMoebiusDvdLog p i * localMoebiusFactor p j := by
  have hswap : twistedGcdLogCoeff a b (p ^ i) (p ^ j) = twistedGcdLogCoeff b a (p ^ j) (p ^ i) := by
    unfold twistedGcdLogCoeff twistedOriginalCoeff
    rw [Nat.gcd_comm]
    ring
  rw [hswap, twistedGcdLogCoeff_prime_pow_of_dvd_left hab.symm hb hp hpb j i, mul_comm]

/-- At `p ∤ ab` the local factor of `c_{a,b} log(ma, nb)` is that of `c log(m, n)`. -/
theorem twistedGcdLogCoeff_prime_pow_of_not_dvd {a b p : ℕ} (hab : Nat.Coprime a b)
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (i j : ℕ) :
    twistedGcdLogCoeff a b (p ^ i) (p ^ j) = selbergLocalOriginalGcdLog p i j := by
  unfold twistedGcdLogCoeff selbergLocalOriginalGcdLog selbergOriginalGcdLogCoeff
  rw [twistedOriginalCoeff_prime_pow_of_not_dvd hab hp hpa hpb,
    gcd_prime_pow_mul_of_not_dvd hab hp hpa hpb]

/-! ## Local series -/

/-- The power series `Σ F(p^i, p^j) X^i Y^j` of the prime-power restriction of `F`. -/
def localSeries (p : ℕ) (F : ℕ → ℕ → ℝ) : PowerSeries (PowerSeries ℝ) :=
  bivariateCoefficientSeries fun i j => F (p ^ i) (p ^ j)

theorem localSeries_eq {p : ℕ} {F f : ℕ → ℕ → ℝ} (h : ∀ i j, F (p ^ i) (p ^ j) = f i j) :
    localSeries p F = bivariateCoefficientSeries f := by
  unfold localSeries
  congr 1
  funext i j
  exact h i j

theorem localSeries_convolution (F G : ℕ → ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    localSeries p (bivariateDirichletConvolution F G) = localSeries p F * localSeries p G := by
  unfold localSeries
  rw [local_convolution F G hp, bivariateCoefficientSeries_convolution]

theorem localSeries_add (F G : ℕ → ℕ → ℝ) (p : ℕ) :
    localSeries p (fun m n => F m n + G m n) = localSeries p F + localSeries p G :=
  bivariateCoefficientSeries_add _ _

theorem bivariateCoefficientSeries_neg (f : ℕ → ℕ → ℝ) :
    bivariateCoefficientSeries (fun i j => -f i j) = -bivariateCoefficientSeries f := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp

/-- A product `u(i) v(j)` is the product of an `X`-series and a `Y`-series. -/
theorem bivariateCoefficientSeries_tensor (u v : ℕ → ℝ) :
    bivariateCoefficientSeries (fun i j => u i * v j) =
      bivariateCoefficientSeries (fun i j => if j = 0 then u i else 0) *
        bivariateCoefficientSeries (fun i j => if i = 0 then v j else 0) := by
  rw [← bivariateCoefficientSeries_convolution, additiveBivariateConvolution_X_Y]

theorem twistFinite_def (a b : ℕ) :
    twistFinite a b = bivariateDirichletConvolution (diagMoebius (a * b)) (moebiusDvdPair a b) :=
  rfl

theorem twistSummable_def (a b : ℕ) :
    twistSummable a b = bivariateDirichletConvolution (corrCoprime (a * b)) (smoothRecipPair a b) :=
  rfl

theorem twistFiniteLog_def (a b : ℕ) : twistFiniteLog a b = fun m n =>
    bivariateDirichletConvolution (diagMoebiusLog (a * b)) (moebiusDvdPair a b) m n +
      bivariateDirichletConvolution (diagMoebius (a * b)) (moebiusDvdPairLog a b) m n :=
  rfl

theorem twistSummableLog_def (a b : ℕ) : twistSummableLog a b =
    bivariateDirichletConvolution (corrLogCoprime (a * b)) (smoothRecipPair a b) :=
  rfl

theorem twistGcdLogSide_def (a b : ℕ) : twistGcdLogSide a b = fun m n =>
    bivariateDirichletConvolution
        (fun m n => bivariateDirichletConvolution (twistFiniteLog a b) (twistSummable a b) m n +
          bivariateDirichletConvolution (twistFinite a b) (twistSummableLog a b) m n)
        selbergPrincipalCoeff m n +
      bivariateDirichletConvolution
        (bivariateDirichletConvolution (twistFinite a b) (twistSummable a b))
        selbergGcdLogPrincipalCoeff m n :=
  rfl

/-- The local series of the right-hand side, factor by factor. -/
theorem localSeries_twistGcdLogSide (a b : ℕ) {p : ℕ} (hp : p.Prime) :
    localSeries p (twistGcdLogSide a b) =
      ((localSeries p (diagMoebiusLog (a * b)) * localSeries p (moebiusDvdPair a b) +
            localSeries p (diagMoebius (a * b)) * localSeries p (moebiusDvdPairLog a b)) *
          (localSeries p (corrCoprime (a * b)) * localSeries p (smoothRecipPair a b)) +
        localSeries p (diagMoebius (a * b)) * localSeries p (moebiusDvdPair a b) *
          (localSeries p (corrLogCoprime (a * b)) * localSeries p (smoothRecipPair a b))) *
        localSeries p selbergPrincipalCoeff +
      localSeries p (diagMoebius (a * b)) * localSeries p (moebiusDvdPair a b) *
          (localSeries p (corrCoprime (a * b)) * localSeries p (smoothRecipPair a b)) *
        localSeries p selbergGcdLogPrincipalCoeff := by
  simp only [twistGcdLogSide_def, twistFiniteLog_def, twistSummableLog_def, twistFinite_def,
    twistSummable_def, localSeries_add, localSeries_convolution _ _ hp]

/-- `S(1 − X/p) S(1 − Y/p)` is the local series of the Möbius pair. -/
theorem bivariateCoefficientSeries_localMoebiusPair {p : ℕ} (hp : p.Prime) :
    bivariateCoefficientSeries (selbergLocalMoebiusReciprocalPair p) =
      bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusFactor p i else 0) *
        bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusFactor p j else 0) := by
  rw [← localMoebiusPairFactor_eq hp, ← bivariateCoefficientSeries_tensor]
  rfl

/-- **The local identity.** At every prime, both sides have the same local series. -/
theorem localSeries_twistedGcdLogCoeff {a b : ℕ} (hab : Nat.Coprime a b) (ha : Squarefree a)
    (hb : Squarefree b) {p : ℕ} (hp : p.Prime) :
    localSeries p (twistedGcdLogCoeff a b) = localSeries p (twistGcdLogSide a b) := by
  have hq : Squarefree (a * b) := Nat.squarefree_mul_iff.mpr ⟨hab, ha, hb⟩
  have hP : localSeries p selbergPrincipalCoeff =
      bivariateCoefficientSeries (selbergLocalDiagonalReciprocal p) *
        (bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusFactor p i else 0) *
          bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusFactor p j else 0)) := by
    change bivariateCoefficientSeries (selbergLocalPrincipal p) = _
    rw [selbergLocalPrincipal_eq_convolution hp, bivariateCoefficientSeries_convolution,
      bivariateCoefficientSeries_localMoebiusPair hp]
  have hPlog : localSeries p selbergGcdLogPrincipalCoeff =
      bivariateCoefficientSeries (selbergLocalDiagonalLogReciprocal p) *
        (bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusFactor p i else 0) *
          bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusFactor p j else 0)) := by
    change bivariateCoefficientSeries (selbergLocalGcdLogPrincipal p) = _
    rw [selbergLocalGcdLogPrincipal_eq_convolution hp, bivariateCoefficientSeries_convolution,
      bivariateCoefficientSeries_localMoebiusPair hp]
  have h1 := congrArg bivariateCoefficientSeries
    (additiveBivariateConvolution_localDiagonal_eulerDenominator hp)
  have h3 := congrArg bivariateCoefficientSeries
    (additiveBivariateConvolution_diagonalLog_eulerDenominator hp)
  simp only [bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_one] at h1 h3
  rw [localSeries_twistGcdLogSide a b hp, hP, hPlog]
  by_cases hpa : p ∣ a
  · have hpb : ¬ p ∣ b := fun h => hp.ne_one (Nat.eq_one_of_dvd_coprimes hab hpa h)
    have hpq : p ∣ a * b := dvd_mul_of_dvd_left hpa b
    have h2 := congrArg bivariateCoefficientSeries (additiveBivariateConvolution_recipY hp)
    simp only [bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_one] at h2
    rw [localSeries_eq (twistedGcdLogCoeff_prime_pow_of_dvd_left hab ha hp hpa),
      bivariateCoefficientSeries_tensor,
      localSeries_eq (diagMoebiusLog_prime_pow_of_dvd hq hp hpq), bivariateCoefficientSeries_neg,
      localSeries_eq (moebiusDvdPair_prime_pow_of_dvd_left ha hp hpa hpb),
      localSeries_eq (diagMoebius_prime_pow_of_dvd hq hp hpq),
      localSeries_eq (moebiusDvdPairLog_prime_pow_of_dvd_left ha hp hpa hpb),
      localSeries_eq (corrCoprime_prime_pow_of_dvd hp hpq), bivariateCoefficientSeries_one,
      localSeries_eq (smoothRecipPair_prime_pow_of_dvd_left ha.ne_zero hp hpa hpb),
      localSeries_eq (corrLogCoprime_prime_pow_of_dvd hp hpq), bivariateCoefficientSeries_zero]
    linear_combination
      (-(bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusDvdLog p j else 0) *
        bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusFactor p i else 0) *
        bivariateCoefficientSeries (fun i j => if i = 0 then (1 / (p : ℝ)) ^ j else 0) *
        bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusFactor p j else 0))) * h1 -
      (bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusDvdLog p j else 0) *
        bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusFactor p i else 0)) * h2 -
      (bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusDvd j else 0) *
        bivariateCoefficientSeries (fun i j => if i = 0 then (1 / (p : ℝ)) ^ j else 0) *
        bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusFactor p i else 0) *
        bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusFactor p j else 0)) * h3
  by_cases hpb : p ∣ b
  · have hpq : p ∣ a * b := dvd_mul_of_dvd_right hpb a
    have h2 := congrArg bivariateCoefficientSeries (additiveBivariateConvolution_recipX hp)
    simp only [bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_one] at h2
    rw [localSeries_eq (twistedGcdLogCoeff_prime_pow_of_dvd_right hab hb hp hpb),
      bivariateCoefficientSeries_tensor,
      localSeries_eq (diagMoebiusLog_prime_pow_of_dvd hq hp hpq), bivariateCoefficientSeries_neg,
      localSeries_eq (moebiusDvdPair_prime_pow_of_dvd_right hb hp hpb hpa),
      localSeries_eq (diagMoebius_prime_pow_of_dvd hq hp hpq),
      localSeries_eq (moebiusDvdPairLog_prime_pow_of_dvd_right hb hp hpb hpa),
      localSeries_eq (corrCoprime_prime_pow_of_dvd hp hpq), bivariateCoefficientSeries_one,
      localSeries_eq (smoothRecipPair_prime_pow_of_dvd_right hb.ne_zero hp hpb hpa),
      localSeries_eq (corrLogCoprime_prime_pow_of_dvd hp hpq), bivariateCoefficientSeries_zero]
    linear_combination
      (-(bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusDvdLog p i else 0) *
        bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusFactor p j else 0) *
        bivariateCoefficientSeries (fun i j => if j = 0 then (1 / (p : ℝ)) ^ i else 0) *
        bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusFactor p i else 0))) * h1 -
      (bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusDvdLog p i else 0) *
        bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusFactor p j else 0)) * h2 -
      (bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusDvd i else 0) *
        bivariateCoefficientSeries (fun i j => if j = 0 then (1 / (p : ℝ)) ^ i else 0) *
        bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusFactor p i else 0) *
        bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusFactor p j else 0)) * h3
  · have hpq : ¬ p ∣ a * b := fun h => ((Nat.Prime.dvd_mul hp).mp h).elim hpa hpb
    have hL : localSeries p (twistedGcdLogCoeff a b) =
        bivariateCoefficientSeries (selbergLocalCorrection p) *
            bivariateCoefficientSeries (selbergLocalGcdLogPrincipal p) +
          bivariateCoefficientSeries (selbergCorrectionLogLocal p) *
            bivariateCoefficientSeries (selbergLocalPrincipal p) := by
      rw [localSeries_eq (twistedGcdLogCoeff_prime_pow_of_not_dvd hab hp hpa hpb),
        ← additiveBivariateConvolution_localGcdLog_identity hp, bivariateCoefficientSeries_add,
        bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_convolution]
    rw [← hP, ← hPlog, hL,
      localSeries_eq (diagMoebiusLog_prime_pow_of_not_dvd hp hpq), bivariateCoefficientSeries_zero,
      localSeries_eq (moebiusDvdPair_prime_pow_of_not_dvd hpa hpb),
      localSeries_eq (diagMoebius_prime_pow_of_not_dvd hp hpq),
      localSeries_eq (moebiusDvdPairLog_prime_pow_of_not_dvd hpa hpb),
      localSeries_eq (f := selbergLocalCorrection p) (corrCoprime_prime_pow_of_not_dvd hp hpq),
      localSeries_eq (smoothRecipPair_prime_pow_of_not_dvd hp hpa hpb),
      localSeries_eq (corrLogCoprime_prime_pow_of_not_dvd hp hpq), bivariateCoefficientSeries_one,
      bivariateCoefficientSeries_zero,
      show localSeries p selbergPrincipalCoeff =
        bivariateCoefficientSeries (selbergLocalPrincipal p) from rfl,
      show localSeries p selbergGcdLogPrincipalCoeff =
        bivariateCoefficientSeries (selbergLocalGcdLogPrincipal p) from rfl]
    ring

/-! ## The global identity -/

/-- **`c_{a,b} log(ma, nb) = (F' ⋆ G + F ⋆ G') ⋆ P + (F ⋆ G) ⋆ P^{log}`** for coprime squarefree
`a, b` and positive `m, n`. -/
theorem twistedGcdLogCoeff_eq_convolution {a b : ℕ} (hab : Nat.Coprime a b) (ha : Squarefree a)
    (hb : Squarefree b) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    twistedGcdLogCoeff a b m n = twistGcdLogSide a b m n := by
  have hFG := (bivariateMultiplicative_twistFinite a b).convolution
    (bivariateMultiplicative_twistSummable a b)
  have hR : BivariateDerivation
      (bivariateDirichletConvolution
        (bivariateDirichletConvolution (twistFinite a b) (twistSummable a b)) selbergPrincipalCoeff)
      (twistGcdLogSide a b) :=
    BivariateDerivation.convolution hFG bivariateMultiplicative_selbergPrincipalCoeff
      (BivariateDerivation.convolution (bivariateMultiplicative_twistFinite a b)
        (bivariateMultiplicative_twistSummable a b) (bivariateDerivation_twistFiniteLog a b)
        (bivariateDerivation_twistSummableLog a b))
      bivariateDerivation_selbergGcdLogPrincipalCoeff
  have hbase : bivariateDirichletConvolution
      (bivariateDirichletConvolution (twistFinite a b) (twistSummable a b)) selbergPrincipalCoeff =
        twistedOriginalCoeff a b := by
    funext m n
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [bivariateDirichletConvolution, twistedOriginalCoeff]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [bivariateDirichletConvolution, twistedOriginalCoeff]
    exact (twistedOriginalCoeff_eq_convolution hab ha hb hm hn).symm
  rw [hbase] at hR
  refine BivariateDerivation.eq_of_prime_pow_eq
    (bivariateDerivation_twistedGcdLogCoeff hab ha.ne_zero hb.ne_zero) hR
    (fun {p} hp i j => ?_) hm hn
  exact congrFun (congrFun (bivariateCoefficientSeries_injective
    (localSeries_twistedGcdLogCoeff hab ha hb hp)) i) j

end

end RHTower.Sieve

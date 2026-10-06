import GaloisForLFunctions.RHTower.Sieve.TwistedSelbergCoefficient

/-!
# Euler factorization of the twisted Selberg coefficient

For coprime squarefree `a, b` (`q = ab`),

`c_{a,b} = ((Δ_q ⋆ μ_{b,a}) ⋆ (E_q ⋆ R_{b,a})) ⋆ P`  (`twistedOriginalCoeff_eq_convolution`),

where `P` is the principal Selberg coefficient, `E_q` the Euler correction restricted to pairs
coprime to `q`, `Δ_q(m, m) = μ(m)/m` for `m | q`, `μ_{b,a}(m, n) = μ(m)[m | b] μ(n)[n | a]`, and
`R_{b,a}(m, n) = R_b(m) R_a(n)` with `R_q(n) = 1/n` on `q`-smooth `n`.

**Proof.** All factors are bivariate multiplicative, so it suffices to compare local factors. At
`p ∤ q` the identity is `E ⋆ P = c`. At `p | a` the local factors are `1 − XY/p`, `1 − Y`, `1`,
`1/(1 − Y/p)` and `P = (1 − X/p)(1 − Y/p)/(1 − XY/p)`, whose product is `(1 − X/p)(1 − Y)`, the local
factor of `c_{a,b}`; `p | b` is the mirror image.

The finitely supported factor `Δ_q ⋆ μ_{b,a}` has total mass `Σ_{m|q} μ(m)/m · Σ_{m|b} μ(m) Σ_{n|a} μ(n)`,
which vanishes as soon as `q > 1`: this is the cancellation that makes resonant twisted forms small.
-/

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-! ## Multiplicativity tools -/

/-- Multiplicativity needs to be checked only on positive pairs. -/
theorem BivariateMultiplicative.of_pos {f : ℕ → ℕ → ℝ} (h1 : f 1 1 = 1)
    (hpos : ∀ {a b c d : ℕ}, 0 < a → 0 < b → 0 < c → 0 < d → Nat.Coprime (a * b) (c * d) →
      f (a * c) (b * d) = f a b * f c d) : BivariateMultiplicative f := by
  refine ⟨h1, fun {a b c d} h => ?_⟩
  by_cases hab0 : a * b = 0
  · have hcd1 : c * d = 1 := by rw [Nat.Coprime, hab0] at h; simpa using h
    have hc1 : c = 1 := Nat.dvd_one.mp ⟨d, hcd1.symm⟩
    have hd1 : d = 1 := Nat.dvd_one.mp ⟨c, by simpa [Nat.mul_comm] using hcd1.symm⟩
    subst c; subst d; simp [h1]
  by_cases hcd0 : c * d = 0
  · have hab1 : a * b = 1 := by rw [Nat.Coprime, hcd0] at h; simpa using h
    have ha1 : a = 1 := Nat.dvd_one.mp ⟨b, hab1.symm⟩
    have hb1 : b = 1 := Nat.dvd_one.mp ⟨a, by simpa [Nat.mul_comm] using hab1.symm⟩
    subst a; subst b; simp [h1]
  exact hpos (Nat.pos_of_ne_zero (left_ne_zero_of_mul hab0))
    (Nat.pos_of_ne_zero (right_ne_zero_of_mul hab0)) (Nat.pos_of_ne_zero (left_ne_zero_of_mul hcd0))
    (Nat.pos_of_ne_zero (right_ne_zero_of_mul hcd0)) h

/-- The pointwise product of bivariate multiplicative functions is bivariate multiplicative. -/
theorem BivariateMultiplicative.mul {f g : ℕ → ℕ → ℝ} (hf : BivariateMultiplicative f)
    (hg : BivariateMultiplicative g) : BivariateMultiplicative (fun m n => f m n * g m n) := by
  refine ⟨by simp [hf.one, hg.one], fun {a b c d} h => ?_⟩
  simp only
  rw [hf.map_mul_of_pair_coprime h, hg.map_mul_of_pair_coprime h]
  ring

/-- Coprimality of the left and right halves of a pair-coprime splitting. -/
theorem coprime_left_of_pair {a b c d : ℕ} (h : Nat.Coprime (a * b) (c * d)) : Nat.Coprime a c :=
  Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) (Nat.Coprime.coprime_dvd_right (dvd_mul_right c d) h)

theorem coprime_right_of_pair {a b c d : ℕ} (h : Nat.Coprime (a * b) (c * d)) : Nat.Coprime b d :=
  Nat.Coprime.coprime_dvd_left (dvd_mul_left b a) (Nat.Coprime.coprime_dvd_right (dvd_mul_left d c) h)

/-- A tensor product of two multiplicative functions of one variable. -/
theorem bivariateMultiplicative_tensor {u v : ℕ → ℝ} (hu1 : u 1 = 1) (hv1 : v 1 = 1)
    (hu : ∀ {m n : ℕ}, Nat.Coprime m n → u (m * n) = u m * u n)
    (hv : ∀ {m n : ℕ}, Nat.Coprime m n → v (m * n) = v m * v n) :
    BivariateMultiplicative (fun m n => u m * v n) := by
  refine ⟨by simp [hu1, hv1], fun {a b c d} h => ?_⟩
  simp only
  rw [hu (coprime_left_of_pair h), hv (coprime_right_of_pair h)]
  ring

/-! ## The factors -/

/-- The Euler correction restricted to pairs coprime to `q`. -/
def corrCoprime (q m n : ℕ) : ℝ :=
  if Nat.Coprime (m * n) q then selbergEulerCorrectionCoeff m n else 0

/-- `Δ_q(m, n) = [m = n, m | q] μ(m)/m`. -/
def diagMoebius (q m n : ℕ) : ℝ :=
  if m = n ∧ m ∣ q then ((μ m : ℤ) : ℝ) / (m : ℝ) else 0

/-- `μ restricted to divisors of q`. -/
def moebiusDvd (q n : ℕ) : ℝ := if n ∣ q then ((μ n : ℤ) : ℝ) else 0

/-- `μ_{b,a}(m, n) = μ(m)[m | b] μ(n)[n | a]`. -/
def moebiusDvdPair (a b m n : ℕ) : ℝ := moebiusDvd b m * moebiusDvd a n

/-- `R_q(n) = 1/n` on `q`-smooth `n ≥ 1`. -/
def smoothRecip (q n : ℕ) : ℝ := if n ≠ 0 ∧ n.primeFactors ⊆ q.primeFactors then 1 / (n : ℝ) else 0

/-- `R_{b,a}(m, n) = R_b(m) R_a(n)`. -/
def smoothRecipPair (a b m n : ℕ) : ℝ := smoothRecip b m * smoothRecip a n

theorem bivariateMultiplicative_corrCoprime (q : ℕ) : BivariateMultiplicative (corrCoprime q) := by
  have hind : BivariateMultiplicative (fun m n : ℕ => if Nat.Coprime (m * n) q then (1 : ℝ) else 0) := by
    refine ⟨by simp, fun {a b c d} h => ?_⟩
    simp only
    rw [show a * c * (b * d) = (a * b) * (c * d) by ring]
    by_cases h1 : Nat.Coprime (a * b) q <;> by_cases h2 : Nat.Coprime (c * d) q
    · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨h1, h2⟩), if_pos h1, if_pos h2]; ring
    · rw [if_neg (show ¬ Nat.Coprime (a * b * (c * d)) q from
        fun h => h2 (Nat.coprime_mul_iff_left.mp h).2), if_neg h2]; ring
    · rw [if_neg (show ¬ Nat.Coprime (a * b * (c * d)) q from
        fun h => h1 (Nat.coprime_mul_iff_left.mp h).1), if_neg h1]; ring
    · rw [if_neg (show ¬ Nat.Coprime (a * b * (c * d)) q from
        fun h => h1 (Nat.coprime_mul_iff_left.mp h).1), if_neg h1]; ring
  have := bivariateMultiplicative_selbergEulerCorrectionCoeff.mul hind
  refine ⟨?_, fun {a b c d} h => ?_⟩
  · have := this.one; simp [corrCoprime]
  · have h' := this.map_mul_of_pair_coprime h
    simp only [corrCoprime] at h' ⊢
    split_ifs at h' ⊢ <;> simp_all

theorem moebiusDvd_mul {q m n : ℕ} (h : Nat.Coprime m n) :
    moebiusDvd q (m * n) = moebiusDvd q m * moebiusDvd q n := by
  unfold moebiusDvd
  by_cases hm : m ∣ q <;> by_cases hn : n ∣ q
  · rw [if_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd h hm hn), if_pos hm, if_pos hn,
      isMultiplicative_moebius.map_mul_of_coprime h]
    push_cast; ring
  · rw [if_neg (fun hd => hn (dvd_trans (dvd_mul_left n m) hd)), if_neg hn, mul_zero]
  · rw [if_neg (fun hd => hm (dvd_trans (dvd_mul_right m n) hd)), if_neg hm, zero_mul]
  · rw [if_neg (fun hd => hm (dvd_trans (dvd_mul_right m n) hd)), if_neg hm, zero_mul]

theorem bivariateMultiplicative_moebiusDvdPair (a b : ℕ) :
    BivariateMultiplicative (moebiusDvdPair a b) :=
  bivariateMultiplicative_tensor (by simp [moebiusDvd]) (by simp [moebiusDvd])
    (fun h => moebiusDvd_mul h) (fun h => moebiusDvd_mul h)

theorem smoothRecip_mul {q m n : ℕ} (h : Nat.Coprime m n) :
    smoothRecip q (m * n) = smoothRecip q m * smoothRecip q n := by
  unfold smoothRecip
  by_cases hm : m = 0
  · subst hm; simp
  by_cases hn : n = 0
  · subst hn; simp
  rw [Nat.primeFactors_mul hm hn]
  by_cases hsm : m.primeFactors ⊆ q.primeFactors <;> by_cases hsn : n.primeFactors ⊆ q.primeFactors
  · rw [if_pos ⟨mul_ne_zero hm hn, Finset.union_subset hsm hsn⟩, if_pos ⟨hm, hsm⟩, if_pos ⟨hn, hsn⟩]
    push_cast; field_simp
  · rw [if_neg (fun h => hsn ((Finset.union_subset_iff.mp h.2).2)),
      if_neg (show ¬ (n ≠ 0 ∧ n.primeFactors ⊆ q.primeFactors) from fun h => hsn h.2), mul_zero]
  · rw [if_neg (fun h => hsm ((Finset.union_subset_iff.mp h.2).1)),
      if_neg (show ¬ (m ≠ 0 ∧ m.primeFactors ⊆ q.primeFactors) from fun h => hsm h.2), zero_mul]
  · rw [if_neg (fun h => hsm ((Finset.union_subset_iff.mp h.2).1)),
      if_neg (show ¬ (m ≠ 0 ∧ m.primeFactors ⊆ q.primeFactors) from fun h => hsm h.2), zero_mul]

theorem bivariateMultiplicative_smoothRecipPair (a b : ℕ) :
    BivariateMultiplicative (smoothRecipPair a b) :=
  bivariateMultiplicative_tensor (by simp [smoothRecip]) (by simp [smoothRecip])
    (fun h => smoothRecip_mul h) (fun h => smoothRecip_mul h)

theorem bivariateMultiplicative_diagMoebius (q : ℕ) :
    BivariateMultiplicative (diagMoebius q) := by
  refine BivariateMultiplicative.of_pos (by simp [diagMoebius]) fun {a b c d} ha hb hc hd h => ?_
  have hac := coprime_left_of_pair h
  have hbd := coprime_right_of_pair h
  have had : Nat.Coprime a d :=
    Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) (Nat.Coprime.coprime_dvd_right (dvd_mul_left d c) h)
  have hbc : Nat.Coprime b c :=
    Nat.Coprime.coprime_dvd_left (dvd_mul_left b a) (Nat.Coprime.coprime_dvd_right (dvd_mul_right c d) h)
  -- `ac = bd` iff `a = b` and `c = d`
  have heq : a * c = b * d ↔ a = b ∧ c = d := by
    constructor
    · intro he
      have hab : a = b := by
        apply Nat.dvd_antisymm
        · exact (Nat.Coprime.dvd_of_dvd_mul_right had (he ▸ dvd_mul_right a c))
        · exact (Nat.Coprime.dvd_of_dvd_mul_right hbc (he ▸ dvd_mul_right b d))
      subst hab
      exact ⟨rfl, Nat.eq_of_mul_eq_mul_left ha he⟩
    · rintro ⟨rfl, rfl⟩; rfl
  unfold diagMoebius
  by_cases hab : a = b
  · subst hab
    by_cases hcd : c = d
    · subst hcd
      by_cases haq : a ∣ q <;> by_cases hcq : c ∣ q
      · rw [if_pos ⟨rfl, Nat.Coprime.mul_dvd_of_dvd_of_dvd hac haq hcq⟩, if_pos ⟨rfl, haq⟩,
          if_pos ⟨rfl, hcq⟩, isMultiplicative_moebius.map_mul_of_coprime hac]
        push_cast; field_simp
      · rw [if_neg (fun h => hcq (dvd_trans (dvd_mul_left c a) h.2)),
          if_neg (show ¬ (c = c ∧ c ∣ q) from fun h => hcq h.2), mul_zero]
      · rw [if_neg (fun h => haq (dvd_trans (dvd_mul_right a c) h.2)),
          if_neg (show ¬ (a = a ∧ a ∣ q) from fun h => haq h.2), zero_mul]
      · rw [if_neg (fun h => haq (dvd_trans (dvd_mul_right a c) h.2)),
          if_neg (show ¬ (a = a ∧ a ∣ q) from fun h => haq h.2), zero_mul]
    · rw [if_neg (fun h => hcd (heq.mp h.1).2),
        if_neg (show ¬ (c = d ∧ c ∣ q) from fun h => hcd h.1), mul_zero]
  · rw [if_neg (fun h => hab (heq.mp h.1).1),
      if_neg (show ¬ (a = b ∧ a ∣ q) from fun h => hab h.1), zero_mul]

/-! ## Local factors -/

theorem corrCoprime_prime_pow_of_not_dvd {q p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) (i j : ℕ) :
    corrCoprime q (p ^ i) (p ^ j) = selbergEulerCorrectionCoeff (p ^ i) (p ^ j) := by
  unfold corrCoprime
  rw [if_pos (by rw [← pow_add]; exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq).pow_left _)]

theorem corrCoprime_prime_pow_of_dvd {q p : ℕ} (hp : p.Prime) (hpq : p ∣ q) (i j : ℕ) :
    corrCoprime q (p ^ i) (p ^ j) = additiveBivariateOne i j := by
  unfold corrCoprime additiveBivariateOne
  rw [← pow_add]
  by_cases h : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have hij : i + j ≠ 0 := by omega
    rw [if_neg h, if_neg]
    intro hc
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hc (dvd_pow_self p hij) hpq)

theorem diagMoebius_prime_pow_of_dvd {q p : ℕ} (hq : Squarefree q) (hp : p.Prime) (hpq : p ∣ q)
    (i j : ℕ) : diagMoebius q (p ^ i) (p ^ j) = selbergLocalEulerDenominator p i j := by
  have hpow : p ^ i = p ^ j ↔ i = j := (Nat.pow_right_injective hp.two_le).eq_iff
  unfold diagMoebius selbergLocalEulerDenominator additiveBivariateOne
    additiveBivariateDiagonalMonomial
  by_cases hij : i = j
  · subst hij
    rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i
      · simp
      · rw [if_pos ⟨rfl, by simpa using hpq⟩, pow_one, ArithmeticFunction.moebius_apply_prime hp]
        simp
        ring
    · have hndvd : ¬ p ^ i ∣ q := by
        intro h
        have h2 : p * p ∣ q := dvd_trans (by rw [← pow_two]; exact pow_dvd_pow p hi) h
        exact (Nat.squarefree_iff_prime_squarefree.mp hq) p hp h2
      rw [if_neg (fun h => hndvd h.2), if_neg (by omega), if_neg (by omega)]
      ring
  · rw [if_neg (fun h => hij (hpow.mp h.1)), if_neg (by omega), if_neg (by omega)]
    ring

theorem diagMoebius_prime_pow_of_not_dvd {q p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) (i j : ℕ) :
    diagMoebius q (p ^ i) (p ^ j) = additiveBivariateOne i j := by
  have hpow : p ^ i = p ^ j ↔ i = j := (Nat.pow_right_injective hp.two_le).eq_iff
  unfold diagMoebius additiveBivariateOne
  by_cases h : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg h, if_neg]
    rintro ⟨h1, h2⟩
    have hij := hpow.mp h1
    subst hij
    have hi : i ≠ 0 := by omega
    exact hpq (dvd_trans (dvd_pow_self p hi) h2)

/-- `μ` on the divisors of a squarefree `q`, at a prime power. -/
def localMoebiusDvd (i : ℕ) : ℝ := if i = 0 then 1 else if i = 1 then -1 else 0

theorem moebiusDvd_prime_pow_of_dvd {q p : ℕ} (hq : Squarefree q) (hp : p.Prime) (hpq : p ∣ q)
    (i : ℕ) : moebiusDvd q (p ^ i) = localMoebiusDvd i := by
  unfold moebiusDvd localMoebiusDvd
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i
    · simp
    · rw [pow_one, if_pos hpq, ArithmeticFunction.moebius_apply_prime hp]; simp
  · have hndvd : ¬ p ^ i ∣ q := by
      intro h
      have h2 : p * p ∣ q := dvd_trans (by rw [← pow_two]; exact pow_dvd_pow p hi) h
      exact (Nat.squarefree_iff_prime_squarefree.mp hq) p hp h2
    rw [if_neg hndvd, if_neg (by omega), if_neg (by omega)]

theorem moebiusDvd_prime_pow_of_not_dvd {q p : ℕ} (hpq : ¬ p ∣ q) (i : ℕ) :
    moebiusDvd q (p ^ i) = if i = 0 then 1 else 0 := by
  unfold moebiusDvd
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [if_neg (fun h => hpq (dvd_trans (dvd_pow_self p hi.ne') h)), if_neg hi.ne']

theorem smoothRecip_prime_pow_of_dvd {q p : ℕ} (hq : q ≠ 0) (hp : p.Prime) (hpq : p ∣ q) (i : ℕ) :
    smoothRecip q (p ^ i) = (1 / (p : ℝ)) ^ i := by
  have hsub : (p ^ i).primeFactors ⊆ q.primeFactors := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · rw [Nat.primeFactors_prime_pow hi.ne' hp, Finset.singleton_subset_iff]
      exact Nat.mem_primeFactors.mpr ⟨hp, hpq, hq⟩
  unfold smoothRecip
  rw [if_pos ⟨pow_ne_zero _ hp.ne_zero, hsub⟩]
  push_cast
  ring

theorem smoothRecip_prime_pow_of_not_dvd {q p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) (i : ℕ) :
    smoothRecip q (p ^ i) = if i = 0 then 1 else 0 := by
  unfold smoothRecip
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [if_neg, if_neg hi.ne']
    rintro ⟨_, h⟩
    rw [Nat.primeFactors_prime_pow hi.ne' hp, Finset.singleton_subset_iff] at h
    exact hpq (Nat.dvd_of_mem_primeFactors h)

/-! ## Local series -/

/-- Convolving an `X`-only sequence with a `Y`-only one gives their tensor product. -/
theorem additiveBivariateConvolution_X_Y (u v : ℕ → ℝ) :
    additiveBivariateConvolution (fun i j => if j = 0 then u i else 0)
      (fun i j => if i = 0 then v j else 0) = fun i j => u i * v j := by
  funext i j
  unfold additiveBivariateConvolution
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; simp at h
  · intro a ha hai
    refine Finset.sum_eq_zero fun b _ => ?_
    have : i - a ≠ 0 := by have := Finset.mem_range.mp ha; omega
    simp [this]
  · intro h; simp at h

/-- `1/(1 − Y/p) ⋆ (1 − Y/p) = 1`. -/
theorem additiveBivariateConvolution_recipY {p : ℕ} (hp : p.Prime) :
    additiveBivariateConvolution (fun i j => if i = 0 then (1 / (p : ℝ)) ^ j else 0)
      (fun i j => if i = 0 then localMoebiusFactor p j else 0) = additiveBivariateOne := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  funext i j
  unfold additiveBivariateConvolution additiveBivariateOne
  rw [Finset.sum_eq_single 0]
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [if_true, Nat.sub_zero]
      rcases j with _ | k
      · simp [localMoebiusFactor]
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have hrest : ∑ b ∈ Finset.range k, (1 / (p : ℝ)) ^ b * localMoebiusFactor p (k + 1 - b) = 0 :=
          Finset.sum_eq_zero fun b hb => by
            have := Finset.mem_range.mp hb
            simp [localMoebiusFactor, show k + 1 - b ≠ 0 by omega, show k + 1 - b ≠ 1 by omega]
        rw [hrest, show k + 1 - k = 1 by omega, Nat.sub_self]
        simp [localMoebiusFactor, pow_succ]
    · simp [show i ≠ 0 by omega]
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [ha]
  · intro h; simp at h

/-- Additive convolution commutes with transposition. -/
theorem additiveBivariateConvolution_transpose (f g : ℕ → ℕ → ℝ) :
    additiveBivariateConvolution (fun i j => f j i) (fun i j => g j i) =
      fun i j => additiveBivariateConvolution f g j i := by
  funext i j
  unfold additiveBivariateConvolution
  exact Finset.sum_comm

theorem additiveBivariateOne_transpose : (fun i j => additiveBivariateOne j i) = additiveBivariateOne := by
  funext i j; unfold additiveBivariateOne; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]

/-- `1/(1 − X/p) ⋆ (1 − X/p) = 1`. -/
theorem additiveBivariateConvolution_recipX {p : ℕ} (hp : p.Prime) :
    additiveBivariateConvolution (fun i j => if j = 0 then (1 / (p : ℝ)) ^ i else 0)
      (fun i j => if j = 0 then localMoebiusFactor p i else 0) = additiveBivariateOne := by
  have h := additiveBivariateConvolution_transpose
    (fun i j => if i = 0 then (1 / (p : ℝ)) ^ j else 0)
    (fun i j => if i = 0 then localMoebiusFactor p j else 0)
  rw [additiveBivariateConvolution_recipY hp, additiveBivariateOne_transpose] at h
  exact h

theorem twistLocal_eq (p i j : ℕ) : twistLocal p i j = localMoebiusFactor p i * localMoebiusDvd j := by
  unfold twistLocal localMoebiusFactor localMoebiusDvd
  rcases Nat.lt_or_ge i 2 with hi | hi
  · rcases Nat.lt_or_ge j 2 with hj | hj
    · interval_cases i <;> interval_cases j <;> simp
    · simp [show j ≠ 0 by omega, show j ≠ 1 by omega]
  · simp [show i ≠ 0 by omega, show i ≠ 1 by omega]

/-! ## The factorization -/

/-- The finitely supported factor `Δ_{ab} ⋆ μ_{b,a}`. -/
def twistFinite (a b : ℕ) : ℕ → ℕ → ℝ :=
  bivariateDirichletConvolution (diagMoebius (a * b)) (moebiusDvdPair a b)

/-- The absolutely summable factor `E_{ab} ⋆ R_{b,a}`. -/
def twistSummable (a b : ℕ) : ℕ → ℕ → ℝ :=
  bivariateDirichletConvolution (corrCoprime (a * b)) (smoothRecipPair a b)

theorem bivariateMultiplicative_twistFinite (a b : ℕ) : BivariateMultiplicative (twistFinite a b) :=
  (bivariateMultiplicative_diagMoebius _).convolution (bivariateMultiplicative_moebiusDvdPair a b)

theorem bivariateMultiplicative_twistSummable (a b : ℕ) :
    BivariateMultiplicative (twistSummable a b) :=
  (bivariateMultiplicative_corrCoprime _).convolution (bivariateMultiplicative_smoothRecipPair a b)

theorem local_convolution (F G : ℕ → ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    (fun x y => bivariateDirichletConvolution F G (p ^ x) (p ^ y)) =
      additiveBivariateConvolution (fun x y => F (p ^ x) (p ^ y)) (fun x y => G (p ^ x) (p ^ y)) := by
  funext x y
  exact bivariateDirichletConvolution_prime_pow F G hp

/-- **Euler factorization of the twisted Selberg coefficient.** -/
theorem twistedOriginalCoeff_eq_convolution {a b : ℕ} (hab : Nat.Coprime a b) (ha : Squarefree a)
    (hb : Squarefree b) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    twistedOriginalCoeff a b m n =
      bivariateDirichletConvolution
        (bivariateDirichletConvolution (twistFinite a b) (twistSummable a b))
        selbergPrincipalCoeff m n := by
  have hq : Squarefree (a * b) := Nat.squarefree_mul_iff.mpr ⟨hab, ha, hb⟩
  have ha0 : a ≠ 0 := ha.ne_zero
  have hb0 : b ≠ 0 := hb.ne_zero
  refine BivariateMultiplicative.eq_of_prime_pow_eq
    (bivariateMultiplicative_twistedOriginalCoeff hab ha0 hb0)
    (((bivariateMultiplicative_twistFinite a b).convolution
      (bivariateMultiplicative_twistSummable a b)).convolution
      bivariateMultiplicative_selbergPrincipalCoeff) (fun {p} hp i j => ?_) hm hn
  rw [bivariateDirichletConvolution_prime_pow _ _ hp, local_convolution _ _ hp]
  unfold twistFinite twistSummable
  rw [local_convolution _ _ hp, local_convolution _ _ hp]
  -- local factors of `P`
  have hP : (fun x y => selbergPrincipalCoeff (p ^ x) (p ^ y)) =
      additiveBivariateConvolution (selbergLocalDiagonalReciprocal p)
        (selbergLocalMoebiusReciprocalPair p) := selbergLocalPrincipal_eq_convolution hp
  have hM : selbergLocalMoebiusReciprocalPair p =
      additiveBivariateConvolution (fun i j => if j = 0 then localMoebiusFactor p i else 0)
        (fun i j => if i = 0 then localMoebiusFactor p j else 0) := by
    rw [← localMoebiusPairFactor_eq hp, additiveBivariateConvolution_X_Y]
    rfl
  have hDE := additiveBivariateConvolution_localDiagonal_eulerDenominator hp
  by_cases hpa : p ∣ a
  · have hpb : ¬ p ∣ b := fun h => hp.ne_one (Nat.eq_one_of_dvd_coprimes hab hpa h)
    have hpq : p ∣ a * b := dvd_mul_of_dvd_left hpa b
    have hdiag : (fun x y => diagMoebius (a * b) (p ^ x) (p ^ y)) = selbergLocalEulerDenominator p := by
      funext x y; exact diagMoebius_prime_pow_of_dvd hq hp hpq x y
    have hpair : (fun x y => moebiusDvdPair a b (p ^ x) (p ^ y)) =
        fun i j => if i = 0 then localMoebiusDvd j else 0 := by
      funext x y
      unfold moebiusDvdPair
      rw [moebiusDvd_prime_pow_of_not_dvd hpb, moebiusDvd_prime_pow_of_dvd ha hp hpa]
      split_ifs <;> simp
    have hcorr : (fun x y => corrCoprime (a * b) (p ^ x) (p ^ y)) = additiveBivariateOne := by
      funext x y; exact corrCoprime_prime_pow_of_dvd hp hpq x y
    have hrec : (fun x y => smoothRecipPair a b (p ^ x) (p ^ y)) =
        fun i j => if i = 0 then (1 / (p : ℝ)) ^ j else 0 := by
      funext x y
      unfold smoothRecipPair
      rw [smoothRecip_prime_pow_of_not_dvd hp hpb, smoothRecip_prime_pow_of_dvd ha0 hp hpa]
      split_ifs <;> simp
    rw [hdiag, hpair, hcorr, hrec, hP, twistedOriginalCoeff_prime_pow_of_dvd_left hab ha hp hpa]
    have htw : twistLocal p = additiveBivariateConvolution
        (fun i j => if j = 0 then localMoebiusFactor p i else 0)
        (fun i j => if i = 0 then localMoebiusDvd j else 0) := by
      rw [additiveBivariateConvolution_X_Y]
      funext i j; exact twistLocal_eq p i j
    rw [htw]
    refine congrFun (congrFun ?_ i) j
    apply bivariateCoefficientSeries_injective
    simp only [bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_one, hM]
    have h1 := congrArg bivariateCoefficientSeries hDE
    have h2 := congrArg bivariateCoefficientSeries (additiveBivariateConvolution_recipY hp)
    simp only [bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_one] at h1 h2
    linear_combination
      (-1 : PowerSeries (PowerSeries ℝ)) *
      (bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusDvd j else 0) *
        bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusFactor p i else 0) *
        (bivariateCoefficientSeries (fun i j => if i = 0 then (1 / (p : ℝ)) ^ j else 0) *
          bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusFactor p j else 0))) * h1 -
      (bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusDvd j else 0) *
        bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusFactor p i else 0)) * h2
  by_cases hpb : p ∣ b
  · have hpq : p ∣ a * b := dvd_mul_of_dvd_right hpb a
    have hdiag : (fun x y => diagMoebius (a * b) (p ^ x) (p ^ y)) = selbergLocalEulerDenominator p := by
      funext x y; exact diagMoebius_prime_pow_of_dvd hq hp hpq x y
    have hpair : (fun x y => moebiusDvdPair a b (p ^ x) (p ^ y)) =
        fun i j => if j = 0 then localMoebiusDvd i else 0 := by
      funext x y
      unfold moebiusDvdPair
      rw [moebiusDvd_prime_pow_of_dvd hb hp hpb, moebiusDvd_prime_pow_of_not_dvd hpa]
      split_ifs <;> simp
    have hcorr : (fun x y => corrCoprime (a * b) (p ^ x) (p ^ y)) = additiveBivariateOne := by
      funext x y; exact corrCoprime_prime_pow_of_dvd hp hpq x y
    have hrec : (fun x y => smoothRecipPair a b (p ^ x) (p ^ y)) =
        fun i j => if j = 0 then (1 / (p : ℝ)) ^ i else 0 := by
      funext x y
      unfold smoothRecipPair
      rw [smoothRecip_prime_pow_of_dvd hb0 hp hpb, smoothRecip_prime_pow_of_not_dvd hp hpa]
      split_ifs <;> simp
    rw [hdiag, hpair, hcorr, hrec, hP, twistedOriginalCoeff_prime_pow_of_dvd_right hab hb hp hpb]
    have htw : (fun i j => twistLocal p j i) = additiveBivariateConvolution
        (fun i j => if j = 0 then localMoebiusDvd i else 0)
        (fun i j => if i = 0 then localMoebiusFactor p j else 0) := by
      rw [additiveBivariateConvolution_X_Y]
      funext i j; rw [twistLocal_eq]; ring
    change (fun i j => twistLocal p j i) i j = _
    rw [htw]
    refine congrFun (congrFun ?_ i) j
    apply bivariateCoefficientSeries_injective
    simp only [bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_one, hM]
    have h1 := congrArg bivariateCoefficientSeries hDE
    have h2 := congrArg bivariateCoefficientSeries (additiveBivariateConvolution_recipX hp)
    simp only [bivariateCoefficientSeries_convolution, bivariateCoefficientSeries_one] at h1 h2
    linear_combination
      (-1 : PowerSeries (PowerSeries ℝ)) *
      (bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusDvd i else 0) *
        bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusFactor p j else 0) *
        (bivariateCoefficientSeries (fun i j => if j = 0 then (1 / (p : ℝ)) ^ i else 0) *
          bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusFactor p i else 0))) * h1 -
      (bivariateCoefficientSeries (fun i j => if j = 0 then localMoebiusDvd i else 0) *
        bivariateCoefficientSeries (fun i j => if i = 0 then localMoebiusFactor p j else 0)) * h2
  · have hpq : ¬ p ∣ a * b := fun h => ((Nat.Prime.dvd_mul hp).mp h).elim hpa hpb
    have hdiag : (fun x y => diagMoebius (a * b) (p ^ x) (p ^ y)) = additiveBivariateOne := by
      funext x y; exact diagMoebius_prime_pow_of_not_dvd hp hpq x y
    have hpair : (fun x y => moebiusDvdPair a b (p ^ x) (p ^ y)) = additiveBivariateOne := by
      funext x y
      unfold moebiusDvdPair additiveBivariateOne
      rw [moebiusDvd_prime_pow_of_not_dvd hpb, moebiusDvd_prime_pow_of_not_dvd hpa]
      split_ifs <;> simp_all
    have hcorr : (fun x y => corrCoprime (a * b) (p ^ x) (p ^ y)) = selbergLocalCorrection p := by
      funext x y; exact corrCoprime_prime_pow_of_not_dvd hp hpq x y
    have hrec : (fun x y => smoothRecipPair a b (p ^ x) (p ^ y)) = additiveBivariateOne := by
      funext x y
      unfold smoothRecipPair additiveBivariateOne
      rw [smoothRecip_prime_pow_of_not_dvd hp hpb, smoothRecip_prime_pow_of_not_dvd hp hpa]
      split_ifs <;> simp_all
    rw [hdiag, hpair, hcorr, hrec, additiveBivariateConvolution_one_left,
      additiveBivariateConvolution_one_right, additiveBivariateConvolution_one_left,
      twistedOriginalCoeff_prime_pow_of_not_dvd hab hp hpa hpb]
    change selbergLocalOriginal p i j = _
    rw [← additiveBivariateConvolution_localCorrection_principal hp]
    rfl

end

end RHTower.Sieve

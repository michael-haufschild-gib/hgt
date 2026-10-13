import GaloisForLFunctions.RHTower.JointAncestryRealSignTypical

/-!
# Almost every vertical translate of a prime cosine test is positive

For a finite set `P` of primes and a level `σ` let
`K_P(s) = ∏_{p ∈ P} (1 + p^{−σ} cosh((s − ½) log p))` (`jasCosineKernel`) and
`F_P(τ) = Re Σ_ρ K_P(ρ − iτ)/(ρ(1−ρ))`.  Positivity of `F_P(τ)` for **all** `τ` and all finite `P`
of large primes is product positivity (`R:JointAncestryPrimeCosineKernel`), which together with a
half-plane bound below `½` is RH.

**Theorem** (`exists_volume_cosineTranslate_re_neg_le`).  For every level `σ ≥ 1` and every `ε > 0`
there is `X` such that for every finite set `P` of primes `p > X` there is `T₀` with
`|{τ ∈ [0, T] : F_P(τ) < 0}| ≤ ε T` for all `T ≥ T₀`.  No hypothesis on the zeros is used.

Proof.
* Expanding the product, `K_P(s − iτ) = Σ_k X_k(s) e^{−iτλ_k}` over `k ∈ {−1,0,1}^P`, with
  frequencies `λ_k = Σ_p k_p log p`.  These are pairwise distinct by the linear independence of the
  `log p` (`cosineTranslateFreq_injective`).
* Summing over the zeros, `F_P(τ) = Φ(0) + Re Z(τ)`, where `Z(τ) = Σ_{k ≠ 0} C_k e^{−iτλ_k}` is a
  finite exponential sum and `C_k = Σ_ρ X_k(ρ)/(ρ(1−ρ))`.
* Cauchy–Schwarz and the local second moments `Σ_j |X_{p,j}(ρ)|² ≤ 1 + p^{−s_ρ}`,
  `s_ρ = 2 − 2|Re ρ − ½|`, give `Σ_{k≠0} |C_k|² ≤ W V_P`, the variance functional of
  `R:JointAncestryRealSignTypical`, which tends to `0` uniformly in `P`.
* The mean square of a finite exponential sum over `[0, T]` is `T Σ|C_k|² + O(1)`
  (`integral_norm_sq_expSum_le`), and Chebyshev's inequality counts the `τ` with `|Z(τ)| ≥ Φ(0)`.

So the exceptional translates of the corpus cosine family have small upper density for every
finite large-prime set at once.  Since `F_P` is almost periodic, its negative set is either empty or
of positive density, and RH is the statement that it is always empty
(`riemannHypothesis_iff_exists_jasCosinePositiveAbove_one`, no side condition).
-/

open Complex MeasureTheory Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The exponential expansion of a translate -/

/-- The exponent `j − 1 ∈ {−1, 0, 1}` of a letter `j : Fin 3`. -/
def cosLetter (j : Fin 3) : ℤ := (j : ℤ) - 1

/-- The local coefficient: `1` at exponent `0`, `(p^{−σ}/2) p^{±(s − ½)}` at exponents `±1`. -/
def cosLocalCoeff (σ : ℝ) (s : ℂ) (p : Nat.Primes) (j : Fin 3) : ℂ :=
  if cosLetter j = 0 then 1 else
    ((Real.exp (-σ * Real.log p) / 2 : ℝ) : ℂ) *
      cexp ((cosLetter j : ℂ) * ((s - 1 / 2) * (Real.log p : ℂ)))

/-- The frequency `λ_k = Σ_p k_p log p`. -/
def cosineTranslateFreq (P : Finset Nat.Primes) (k : ↥P → Fin 3) : ℝ :=
  ∑ p : ↥P, (cosLetter (k p) : ℝ) * Real.log (p : Nat.Primes)

/-- The coefficient `X_k(s) = ∏_p X_{p, k_p}(s)`. -/
def cosineTranslateCoeff (P : Finset Nat.Primes) (σ : ℝ) (s : ℂ) (k : ↥P → Fin 3) : ℂ :=
  ∏ p : ↥P, cosLocalCoeff σ s p (k p)

/-- The zero letter vector `k ≡ 0` (letter `1`). -/
def cosZeroLetters (P : Finset Nat.Primes) : ↥P → Fin 3 := fun _ => 1

theorem cosLocal_expansion (σ : ℝ) (s : ℂ) (τ : ℝ) (p : Nat.Primes) :
    1 + (Real.exp (-σ * Real.log p) : ℂ) * Complex.cosh ((s - (τ : ℂ) * I - 1 / 2) *
      (Real.log p : ℂ)) =
      ∑ j : Fin 3, cosLocalCoeff σ s p j *
        cexp (-((τ : ℂ) * ((cosLetter j : ℝ) * Real.log p : ℝ)) * I) := by
  rw [Fin.sum_univ_three]
  have h0 : cosLetter 0 = -1 := by decide
  have h1 : cosLetter 1 = 0 := by decide
  have h2 : cosLetter 2 = 1 := by decide
  simp only [cosLocalCoeff, h0, h1, h2]
  simp only [show (-1 : ℤ) ≠ 0 by decide, show (1 : ℤ) ≠ 0 by decide, if_false, if_true]
  obtain ⟨L, hL⟩ : ∃ L : ℂ, L = (Real.log p : ℂ) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℂ, E = ((Real.exp (-σ * Real.log p) / 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hE2 : (Real.exp (-σ * Real.log p) : ℂ) = 2 * E := by
    rw [hE]; push_cast; ring
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_intCast,
    Complex.ofReal_intCast, Complex.ofReal_intCast, ← hL, hE2, ← hE, Complex.cosh]
  simp only [Int.cast_neg, Int.cast_one, Int.cast_zero]
  have e1 : cexp ((s - (τ : ℂ) * I - 1 / 2) * L) =
      cexp ((1 : ℂ) * ((s - 1 / 2) * L)) * cexp (-((τ : ℂ) * ((1 : ℂ) * L)) * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : cexp (-((s - (τ : ℂ) * I - 1 / 2) * L)) =
      cexp ((-1 : ℂ) * ((s - 1 / 2) * L)) * cexp (-((τ : ℂ) * ((-1 : ℂ) * L)) * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e3 : cexp (-((τ : ℂ) * ((0 : ℂ) * L)) * I) = 1 := by
    rw [zero_mul, mul_zero, neg_zero, zero_mul, Complex.exp_zero]
  rw [e1, e2, e3]
  ring

/-- **The exponential expansion.**  `K_P(s − iτ) = Σ_k X_k(s) e^{−iτλ_k}`. -/
theorem jasCosineKernel_translate_eq_sum (P : Finset Nat.Primes) (σ : ℝ) (s : ℂ) (τ : ℝ) :
    jasCosineKernel P σ (s - (τ : ℂ) * I) = ∑ k : ↥P → Fin 3,
      cosineTranslateCoeff P σ s k * cexp (-((τ : ℂ) * cosineTranslateFreq P k) * I) := by
  classical
  rw [jasCosineKernel, ← Finset.prod_coe_sort P (fun p : Nat.Primes =>
    1 + (Real.exp (-σ * Real.log p) : ℂ) * Complex.cosh ((s - (τ : ℂ) * I - 1 / 2) *
      (Real.log p : ℂ)))]
  rw [Finset.prod_congr rfl fun p _ => cosLocal_expansion σ s τ p.1]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.prod_mul_distrib, cosineTranslateCoeff, ← Complex.exp_sum]
  congr 1
  rw [cosineTranslateFreq, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
    Finset.sum_mul]

theorem cosineTranslateCoeff_zero (P : Finset Nat.Primes) (σ : ℝ) (s : ℂ) :
    cosineTranslateCoeff P σ s (cosZeroLetters P) = 1 := by
  refine Finset.prod_eq_one fun p _ => ?_
  simp [cosLocalCoeff, cosZeroLetters, cosLetter]

theorem cosineTranslateFreq_zero (P : Finset Nat.Primes) :
    cosineTranslateFreq P (cosZeroLetters P) = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  simp [cosZeroLetters, cosLetter]

theorem cosLetter_injective : Function.Injective cosLetter := by
  intro a b h
  unfold cosLetter at h
  exact Fin.ext (by omega)

/-- **Distinct letter vectors have distinct frequencies** (linear independence of `log p`). -/
theorem cosineTranslateFreq_injective (P : Finset Nat.Primes) :
    Function.Injective (cosineTranslateFreq P) := by
  intro k k' h
  have hli : LinearIndependent ℤ (fun p : ↥P => Real.log ((p : Nat.Primes) : ℕ)) :=
    GaloisForLFunctions.logPrime_linearIndependent_int.comp _ Subtype.val_injective
  have hsum : ∑ p : ↥P, (cosLetter (k p) - cosLetter (k' p)) •
      Real.log ((p : Nat.Primes) : ℕ) = 0 := by
    have := sub_eq_zero.mpr h
    rw [cosineTranslateFreq, cosineTranslateFreq, ← Finset.sum_sub_distrib] at this
    rw [← this]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [zsmul_eq_mul]
    push_cast
    ring
  funext p
  have := Fintype.linearIndependent_iff.mp hli _ hsum p
  exact cosLetter_injective (sub_eq_zero.mp this)

/-! ## Coefficient bounds at a zero -/

theorem norm_cexp_letter (s : ℂ) (p : Nat.Primes) (j : Fin 3) :
    ‖cexp ((cosLetter j : ℂ) * ((s - 1 / 2) * (Real.log p : ℂ)))‖ ≤
      Real.exp (|s.re - 1 / 2| * Real.log p) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hL := (log_two_le_log_prime p).trans' (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hre : ((cosLetter j : ℂ) * ((s - 1 / 2) * (Real.log p : ℂ))).re =
      (cosLetter j : ℝ) * ((s.re - 1 / 2) * Real.log p) := by
    rw [← Complex.ofReal_intCast, Complex.re_ofReal_mul, Complex.re_mul_ofReal, Complex.sub_re,
      Complex.div_ofNat_re, Complex.one_re]
  rw [hre]
  have hj : |(cosLetter j : ℝ)| ≤ 1 := by
    fin_cases j <;> simp [cosLetter]
  calc (cosLetter j : ℝ) * ((s.re - 1 / 2) * Real.log p)
      = ((cosLetter j : ℝ) * (s.re - 1 / 2)) * Real.log p := by ring
    _ ≤ |(cosLetter j : ℝ) * (s.re - 1 / 2)| * Real.log p :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hL
    _ = |(cosLetter j : ℝ)| * (|s.re - 1 / 2| * Real.log p) := by rw [abs_mul]; ring
    _ ≤ 1 * (|s.re - 1 / 2| * Real.log p) :=
        mul_le_mul_of_nonneg_right hj (mul_nonneg (abs_nonneg _) hL)
    _ = |s.re - 1 / 2| * Real.log p := one_mul _

/-- At a zero and a level `σ ≥ 1`, each local coefficient has modulus at most `1`. -/
theorem norm_cosLocalCoeff_le_one {σ : ℝ} (hσ : 1 ≤ σ) (q : XiZeroCopy) (p : Nat.Primes)
    (j : Fin 3) : ‖cosLocalCoeff σ (q.1 : ℂ) p j‖ ≤ 1 := by
  unfold cosLocalCoeff
  split_ifs
  · simp
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hL := (log_two_le_log_prime p).trans' (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hq : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
    have h1 := norm_cexp_letter (q.1 : ℂ) p j
    have h2 : Real.exp (-σ * Real.log p) * Real.exp (|(q.1 : ℂ).re - 1 / 2| * Real.log p) ≤ 1 := by
      rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by nlinarith)
    calc Real.exp (-σ * Real.log p) / 2 *
          ‖cexp ((cosLetter j : ℂ) * (((q.1 : ℂ) - 1 / 2) * (Real.log p : ℂ)))‖
        ≤ Real.exp (-σ * Real.log p) / 2 * Real.exp (|(q.1 : ℂ).re - 1 / 2| * Real.log p) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 := by nlinarith [Real.exp_pos (-σ * Real.log p)]

/-- At a zero and a level `σ ≥ 1`, `Σ_j |X_{p,j}|² ≤ 1 + p^{−s_ρ}`. -/
theorem sum_norm_sq_cosLocalCoeff_le {σ : ℝ} (hσ : 1 ≤ σ) (q : XiZeroCopy) (p : Nat.Primes) :
    ∑ j : Fin 3, ‖cosLocalCoeff σ (q.1 : ℂ) p j‖ ^ 2 ≤
      1 + Real.exp (-jasSignExponent q * Real.log p) := by
  rw [Fin.sum_univ_three]
  have h0 : cosLetter 0 = -1 := by decide
  have h1 : cosLetter 1 = 0 := by decide
  have h2 : cosLetter 2 = 1 := by decide
  have hL := (log_two_le_log_prime p).trans' (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hbd : ∀ j : Fin 3, cosLetter j ≠ 0 → ‖cosLocalCoeff σ (q.1 : ℂ) p j‖ ^ 2 ≤
      Real.exp (-jasSignExponent q * Real.log p) / 2 := by
    intro j hj
    unfold cosLocalCoeff
    rw [if_neg hj, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
    have hc := pow_le_pow_left₀ (norm_nonneg _) (norm_cexp_letter (q.1 : ℂ) p j) 2
    have e1 : (Real.exp (-σ * Real.log p) / 2) ^ 2 = Real.exp (-(2 * σ) * Real.log p) / 4 := by
      rw [div_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    have e2 : Real.exp (|(q.1 : ℂ).re - 1 / 2| * Real.log p) ^ 2 =
        Real.exp (2 * |(q.1 : ℂ).re - 1 / 2| * Real.log p) := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e1]
    calc Real.exp (-(2 * σ) * Real.log p) / 4 *
          ‖cexp ((cosLetter j : ℂ) * (((q.1 : ℂ) - 1 / 2) * (Real.log p : ℂ)))‖ ^ 2
        ≤ Real.exp (-(2 * σ) * Real.log p) / 4 *
            Real.exp (2 * |(q.1 : ℂ).re - 1 / 2| * Real.log p) := by
          rw [← e2]; exact mul_le_mul_of_nonneg_left hc (by positivity)
      _ = Real.exp ((-(2 * σ) + 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log p) / 4 := by
          rw [div_mul_eq_mul_div, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-jasSignExponent q * Real.log p) / 2 := by
          have : Real.exp ((-(2 * σ) + 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log p) ≤
              Real.exp (-jasSignExponent q * Real.log p) :=
            Real.exp_le_exp.mpr (by unfold jasSignExponent; nlinarith)
          have := Real.exp_pos (-jasSignExponent q * Real.log p)
          linarith
  have hz : ‖cosLocalCoeff σ (q.1 : ℂ) p 1‖ ^ 2 = 1 := by simp [cosLocalCoeff, h1]
  have ha := hbd 0 (by rw [h0]; decide)
  have hb := hbd 2 (by rw [h2]; decide)
  rw [hz]
  linarith

/-- `Σ_k |X_k(ρ)|² = ∏_p Σ_j |X_{p,j}(ρ)|²`. -/
theorem sum_norm_sq_cosineTranslateCoeff (P : Finset Nat.Primes) (σ : ℝ) (s : ℂ) :
    ∑ k : ↥P → Fin 3, ‖cosineTranslateCoeff P σ s k‖ ^ 2 =
      ∏ p : ↥P, ∑ j : Fin 3, ‖cosLocalCoeff σ s p j‖ ^ 2 := by
  classical
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cosineTranslateCoeff, norm_prod, Finset.prod_pow]

/-- At a zero and a level `σ ≥ 1`, `Σ_{k ≠ 0} |X_k(ρ)|² ≤ ∏_P (1 + p^{−s_ρ}) − 1`. -/
theorem sum_norm_sq_cosineTranslateCoeff_sub_le {σ : ℝ} (hσ : 1 ≤ σ) (P : Finset Nat.Primes)
    (q : XiZeroCopy) :
    ∑ k ∈ Finset.univ.erase (cosZeroLetters P), ‖cosineTranslateCoeff P σ (q.1 : ℂ) k‖ ^ 2 ≤
      (∏ p ∈ P, (1 + Real.exp (-jasSignExponent q * Real.log p))) - 1 := by
  classical
  have hall := sum_norm_sq_cosineTranslateCoeff P σ (q.1 : ℂ)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (cosZeroLetters P)),
    cosineTranslateCoeff_zero, norm_one, one_pow] at hall
  have hle : ∏ p : ↥P, ∑ j : Fin 3, ‖cosLocalCoeff σ (q.1 : ℂ) p j‖ ^ 2 ≤
      ∏ p ∈ P, (1 + Real.exp (-jasSignExponent q * Real.log p)) := by
    rw [← Finset.prod_coe_sort P (fun p => 1 + Real.exp (-jasSignExponent q * Real.log p))]
    exact Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
      fun p _ => sum_norm_sq_cosLocalCoeff_le hσ q p
  linarith

/-! ## Mean square of a finite exponential sum -/

/-- The exponential `e^{−iτλ}`. -/
def expPhase (τ lam : ℝ) : ℂ := cexp (-((τ : ℂ) * lam) * I)

theorem continuous_expPhase (lam : ℝ) : Continuous fun τ : ℝ => expPhase τ lam := by
  unfold expPhase; fun_prop

theorem expPhase_mul_conj (τ a b : ℝ) :
    expPhase τ a * (starRingEnd ℂ) (expPhase τ b) = expPhase τ (a - b) := by
  unfold expPhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `|∫_0^T e^{−iτΔ} dτ| ≤ 2/|Δ|` for `Δ ≠ 0`. -/
theorem norm_integral_expPhase_le {Δ : ℝ} (hΔ : Δ ≠ 0) (T : ℝ) :
    ‖∫ τ in (0 : ℝ)..T, expPhase τ Δ‖ ≤ 2 / |Δ| := by
  have hc : (-(Δ : ℂ) * I) ≠ 0 := by
    have : (Δ : ℂ) ≠ 0 := by exact_mod_cast hΔ
    exact mul_ne_zero (neg_ne_zero.mpr this) Complex.I_ne_zero
  have e : (fun τ : ℝ => expPhase τ Δ) = fun τ : ℝ => cexp (-(Δ : ℂ) * I * (τ : ℂ)) := by
    funext τ; unfold expPhase; congr 1; ring
  rw [e, integral_exp_mul_complex hc]
  have hn : ‖-(Δ : ℂ) * I‖ = |Δ| := by
    rw [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_div, hn]
  gcongr
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖cexp (-(Δ : ℂ) * I * (T : ℂ))‖ = 1 := by
    rw [show -(Δ : ℂ) * I * (T : ℂ) = ((-(Δ * T) : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have h0 : ‖cexp (-(Δ : ℂ) * I * ((0 : ℝ) : ℂ))‖ = 1 := by simp
  rw [h1, h0]; norm_num

/-- **Mean square of a finite exponential sum.**  For pairwise distinct frequencies,
`∫_0^T |Σ_k C_k e^{−iτλ_k}|² ≤ T Σ_k |C_k|² + Σ_{k ≠ k'} |C_k||C_{k'}| · 2/|λ_k − λ_{k'}|`. -/
theorem integral_norm_sq_expSum_le {ι : Type*} [DecidableEq ι] (S : Finset ι) (C : ι → ℂ)
    (lam : ι → ℝ) (hlam : Set.InjOn lam S) {T : ℝ} (hT : 0 ≤ T) :
    ∫ τ in (0 : ℝ)..T, ‖∑ k ∈ S, C k * expPhase τ (lam k)‖ ^ 2 ≤
      T * ∑ k ∈ S, ‖C k‖ ^ 2 +
        ∑ k ∈ S, ∑ k' ∈ S.erase k, ‖C k‖ * ‖C k'‖ * (2 / |lam k - lam k'|) := by
  -- the square as a double sum
  have hpt : ∀ τ : ℝ, (((‖∑ k ∈ S, C k * expPhase τ (lam k)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ k ∈ S, ∑ k' ∈ S, C k * (starRingEnd ℂ) (C k') * expPhase τ (lam k - lam k') := by
    intro τ
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
    rw [map_mul, ← expPhase_mul_conj]
    ring
  have hint : ∀ k ∈ S, ∀ k' ∈ S, IntervalIntegrable
      (fun τ : ℝ => C k * (starRingEnd ℂ) (C k') * expPhase τ (lam k - lam k')) volume 0 T :=
    fun k _ k' _ => (continuous_const.mul (continuous_expPhase (lam k - lam k'))).intervalIntegrable 0 T
  have hcomplex : (((∫ τ in (0 : ℝ)..T, ‖∑ k ∈ S, C k * expPhase τ (lam k)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ k ∈ S, ∑ k' ∈ S, C k * (starRingEnd ℂ) (C k') *
        ∫ τ in (0 : ℝ)..T, expPhase τ (lam k - lam k') := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum (f := fun k τ => ∑ k' ∈ S,
      C k * (starRingEnd ℂ) (C k') * expPhase τ (lam k - lam k')) fun k _ =>
      (continuous_finsetSum _ fun k' _ =>
        continuous_const.mul (continuous_expPhase _)).intervalIntegrable 0 T]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [intervalIntegral.integral_finsetSum fun k' hk' => hint k hk k' hk']
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [intervalIntegral.integral_const_mul]
  have hre : (∫ τ in (0 : ℝ)..T, ‖∑ k ∈ S, C k * expPhase τ (lam k)‖ ^ 2) =
      (∑ k ∈ S, ∑ k' ∈ S, C k * (starRingEnd ℂ) (C k') *
        ∫ τ in (0 : ℝ)..T, expPhase τ (lam k - lam k')).re := by
    rw [← hcomplex, Complex.ofReal_re]
  rw [hre]
  refine (Complex.re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k hk => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [← Finset.add_sum_erase S _ hk]
  have hdiag : ‖C k * (starRingEnd ℂ) (C k) * ∫ τ in (0 : ℝ)..T, expPhase τ (lam k - lam k)‖ =
      T * ‖C k‖ ^ 2 := by
    have : ∫ τ in (0 : ℝ)..T, expPhase τ (lam k - lam k) = (T : ℂ) := by
      simp [expPhase]
    rw [this, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hT]
    ring
  rw [hdiag]
  refine add_le_add_right ?_ (T * ‖C k‖ ^ 2)
  refine Finset.sum_le_sum fun k' hk' => ?_
  have hne : lam k - lam k' ≠ 0 := by
    intro h
    exact (Finset.mem_erase.mp hk').1 (hlam (Finset.mem_erase.mp hk').2 hk (sub_eq_zero.mp h).symm)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (norm_integral_expPhase_le hne T)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-! ## The deviation of a translate -/

theorem norm_cosineTranslateCoeff_le_one {σ : ℝ} (hσ : 1 ≤ σ) (P : Finset Nat.Primes)
    (q : XiZeroCopy) (k : ↥P → Fin 3) : ‖cosineTranslateCoeff P σ (q.1 : ℂ) k‖ ≤ 1 := by
  rw [cosineTranslateCoeff, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
    (fun p _ => norm_cosLocalCoeff_le_one hσ q p (k p))

theorem summable_lagWeight_mul_cosineTranslateCoeff {σ : ℝ} (hσ : 1 ≤ σ) (P : Finset Nat.Primes)
    (k : ↥P → Fin 3) :
    Summable fun q : XiZeroCopy => lagWeight q * cosineTranslateCoeff P σ (q.1 : ℂ) k :=
  Summable.of_norm_bounded summable_norm_lagWeight fun q => by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_cosineTranslateCoeff_le_one hσ P q k)

/-- `C_k = Σ_ρ X_k(ρ)/(ρ(1−ρ))`. -/
def cosineTranslateWeight (P : Finset Nat.Primes) (σ : ℝ) (k : ↥P → Fin 3) : ℂ :=
  ∑' q : XiZeroCopy, lagWeight q * cosineTranslateCoeff P σ (q.1 : ℂ) k

/-- The deviation `Z(τ) = Σ_{k ≠ 0} C_k e^{−iτλ_k}`. -/
def cosineTranslateDeviation (P : Finset Nat.Primes) (σ τ : ℝ) : ℂ :=
  ∑ k ∈ Finset.univ.erase (cosZeroLetters P),
    cosineTranslateWeight P σ k * expPhase τ (cosineTranslateFreq P k)

theorem continuous_cosineTranslateDeviation (P : Finset Nat.Primes) (σ : ℝ) :
    Continuous fun τ : ℝ => cosineTranslateDeviation P σ τ := by
  unfold cosineTranslateDeviation
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_expPhase _)

/-- **The translate aggregate is `Φ(0)` plus a finite exponential sum.** -/
theorem tsum_jasCosineKernel_translate_eq {σ : ℝ} (hσ : 1 ≤ σ) (P : Finset Nat.Primes) (τ : ℝ) :
    ∑' q : XiZeroCopy, jasCosineKernel P σ ((q.1 : ℂ) - (τ : ℂ) * I) /
      ((q.1 : ℂ) * (1 - (q.1 : ℂ))) = poleSharpConstant + cosineTranslateDeviation P σ τ := by
  classical
  have e : ∀ q : XiZeroCopy, jasCosineKernel P σ ((q.1 : ℂ) - (τ : ℂ) * I) /
      ((q.1 : ℂ) * (1 - (q.1 : ℂ))) = ∑ k : ↥P → Fin 3,
        lagWeight q * cosineTranslateCoeff P σ (q.1 : ℂ) k * expPhase τ (cosineTranslateFreq P k) := by
    intro q
    rw [jasCosineKernel_translate_eq_sum, div_eq_mul_one_div, mul_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [lagWeight, expPhase]
    ring
  simp_rw [e]
  rw [Summable.tsum_finsetSum fun k _ =>
    (summable_lagWeight_mul_cosineTranslateCoeff hσ P k).mul_right _]
  simp_rw [tsum_mul_right]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (cosZeroLetters P))]
  congr 1
  · have h1 : ∀ q : XiZeroCopy, lagWeight q * cosineTranslateCoeff P σ (q.1 : ℂ)
        (cosZeroLetters P) = 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := fun q => by
      rw [cosineTranslateCoeff_zero, mul_one, lagWeight]
    simp_rw [h1]
    rw [tsum_inv_zero_mul_one_sub_zero, cosineTranslateFreq_zero]
    simp [expPhase]

/-- **The coefficient variance.**  `Σ_{k ≠ 0} |C_k|² ≤ W V_P`. -/
theorem sum_norm_sq_cosineTranslateWeight_le {σ : ℝ} (hσ : 1 ≤ σ) (P : Finset Nat.Primes) :
    ∑ k ∈ Finset.univ.erase (cosZeroLetters P), ‖cosineTranslateWeight P σ k‖ ^ 2 ≤
      lagWeightTotal * jasSignVariance P := by
  classical
  have hW : ∑' q : XiZeroCopy, ‖lagWeight q‖ = lagWeightTotal := rfl
  have hs1 : ∀ k, Summable fun q : XiZeroCopy =>
      ‖lagWeight q‖ * ‖cosineTranslateCoeff P σ (q.1 : ℂ) k‖ := fun k =>
    Summable.of_nonneg_of_le (fun q => by positivity)
      (fun q => mul_le_of_le_one_right (norm_nonneg _) (norm_cosineTranslateCoeff_le_one hσ P q k))
      summable_norm_lagWeight
  have hs2 : ∀ k, Summable fun q : XiZeroCopy =>
      ‖lagWeight q‖ * ‖cosineTranslateCoeff P σ (q.1 : ℂ) k‖ ^ 2 := fun k =>
    Summable.of_nonneg_of_le (fun q => by positivity)
      (fun q => mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _)
        (norm_cosineTranslateCoeff_le_one hσ P q k)))
      summable_norm_lagWeight
  have hk : ∀ k, ‖cosineTranslateWeight P σ k‖ ^ 2 ≤
      lagWeightTotal * ∑' q : XiZeroCopy, ‖lagWeight q‖ * ‖cosineTranslateCoeff P σ (q.1 : ℂ) k‖ ^ 2 := by
    intro k
    have h1 : ‖cosineTranslateWeight P σ k‖ ≤
        ∑' q : XiZeroCopy, ‖lagWeight q‖ * ‖cosineTranslateCoeff P σ (q.1 : ℂ) k‖ := by
      refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun q => norm_mul _ _))
      refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => le_of_eq (norm_mul _ _))
        (hs1 k)
    have hCS := sq_tsum_mul_le (c := fun q : XiZeroCopy => ‖lagWeight q‖)
      (x := fun q => ‖cosineTranslateCoeff P σ (q.1 : ℂ) k‖) (fun q => norm_nonneg _)
      summable_norm_lagWeight (hs1 k) (hs2 k)
    rw [hW] at hCS
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans hCS
  calc ∑ k ∈ Finset.univ.erase (cosZeroLetters P), ‖cosineTranslateWeight P σ k‖ ^ 2
      ≤ ∑ k ∈ Finset.univ.erase (cosZeroLetters P), lagWeightTotal *
          ∑' q : XiZeroCopy, ‖lagWeight q‖ * ‖cosineTranslateCoeff P σ (q.1 : ℂ) k‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => hk k
    _ = lagWeightTotal * ∑' q : XiZeroCopy, ‖lagWeight q‖ *
          ∑ k ∈ Finset.univ.erase (cosZeroLetters P), ‖cosineTranslateCoeff P σ (q.1 : ℂ) k‖ ^ 2 := by
        rw [← Finset.mul_sum, ← Summable.tsum_finsetSum fun k _ => hs2 k]
        congr 1
        exact tsum_congr fun q => (Finset.mul_sum _ _ _).symm
    _ ≤ lagWeightTotal * jasSignVariance P := by
        refine mul_le_mul_of_nonneg_left ?_ lagWeightTotal_nonneg
        refine Summable.tsum_le_tsum (fun q => mul_le_mul_of_nonneg_left
          (sum_norm_sq_cosineTranslateCoeff_sub_le hσ P q) (norm_nonneg _)) ?_
          (summable_jasSignVariance_term P)
        refine Summable.of_nonneg_of_le (fun q => mul_nonneg (norm_nonneg _)
          (Finset.sum_nonneg fun k _ => sq_nonneg _)) (fun q => mul_le_mul_of_nonneg_left
          (sum_norm_sq_cosineTranslateCoeff_sub_le hσ P q) (norm_nonneg _))
          (summable_jasSignVariance_term P)

/-! ## Counting the negative translates -/

/-- **Chebyshev in the translate.**  `|{τ ∈ (0, T] : F_P(τ) < 0}| · Φ(0)² ≤ ∫_0^T |Z|²`. -/
theorem volume_cosineTranslate_re_neg_mul_le {σ : ℝ} (hσ : 1 ≤ σ) (P : Finset Nat.Primes) {T : ℝ}
    (hT : 0 ≤ T) :
    volume.real {τ ∈ Set.Ioc (0 : ℝ) T | (∑' q : XiZeroCopy,
        jasCosineKernel P σ ((q.1 : ℂ) - (τ : ℂ) * I) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re < 0} *
      poleSharpConstant ^ 2 ≤ ∫ τ in (0 : ℝ)..T, ‖cosineTranslateDeviation P σ τ‖ ^ 2 := by
  have hΦ := poleSharpConstant_pos
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun τ => ‖cosineTranslateDeviation P σ τ‖ ^ 2 := ⟨_, rfl⟩
  have hfc : Continuous f := by
    rw [hf]; exact (continuous_cosineTranslateDeviation P σ).norm.pow 2
  have hsub : {τ ∈ Set.Ioc (0 : ℝ) T | (∑' q : XiZeroCopy,
      jasCosineKernel P σ ((q.1 : ℂ) - (τ : ℂ) * I) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re < 0} ⊆
      {τ | poleSharpConstant ^ 2 ≤ f τ} ∩ Set.Ioc (0 : ℝ) T := by
    rintro τ ⟨hτ, hneg⟩
    refine ⟨?_, hτ⟩
    rw [tsum_jasCosineKernel_translate_eq hσ, Complex.add_re, Complex.ofReal_re] at hneg
    have h1 : poleSharpConstant ≤ ‖cosineTranslateDeviation P σ τ‖ := by
      have := (neg_le_abs _).trans (Complex.abs_re_le_norm (cosineTranslateDeviation P σ τ))
      linarith
    show poleSharpConstant ^ 2 ≤ f τ
    rw [hf]
    exact pow_le_pow_left₀ hΦ.le h1 2
  have hmeas : MeasurableSet {τ | poleSharpConstant ^ 2 ≤ f τ} :=
    measurableSet_le measurable_const hfc.measurable
  have hint : Integrable f (volume.restrict (Set.Ioc (0 : ℝ) T)) :=
    hfc.integrableOn_Ioc
  have hcheb := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Set.Ioc (0 : ℝ) T))
    (Eventually.of_forall fun τ => by rw [hf]; positivity) hint (poleSharpConstant ^ 2)
  rw [measureReal_restrict_apply hmeas] at hcheb
  have hfin : volume ({τ | poleSharpConstant ^ 2 ≤ f τ} ∩ Set.Ioc (0 : ℝ) T) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_Ioc_lt_top.ne (measure_mono Set.inter_subset_right)
  have hmono := measureReal_mono hsub hfin
  rw [intervalIntegral.integral_of_le hT, ← hf]
  calc _ ≤ volume.real ({τ | poleSharpConstant ^ 2 ≤ f τ} ∩ Set.Ioc (0 : ℝ) T) *
        poleSharpConstant ^ 2 := mul_le_mul_of_nonneg_right hmono (by positivity)
    _ ≤ _ := by rw [mul_comm]; exact hcheb

/-- **Almost every vertical translate is positive, uniformly in the prime set.**  For every level
`σ ≥ 1` and every `ε > 0` there is `X` such that for every finite set `P` of primes `p > X` there is
`T₀` with `|{τ ∈ (0, T] : Re Σ_ρ K_P(ρ − iτ)/(ρ(1−ρ)) < 0}| ≤ ε T` for every `T ≥ T₀`. -/
theorem exists_volume_cosineTranslate_re_neg_le {σ : ℝ} (hσ : 1 ≤ σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℕ, ∀ P : Finset Nat.Primes, (∀ p ∈ P, X < (p : ℕ)) → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      volume.real {τ ∈ Set.Ioc (0 : ℝ) T | (∑' q : XiZeroCopy,
        jasCosineKernel P σ ((q.1 : ℂ) - (τ : ℂ) * I) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re < 0} ≤
        ε * T := by
  classical
  have hΦ := poleSharpConstant_pos
  have hW0 := lagWeightTotal_nonneg
  have hΦ2 : 0 < poleSharpConstant ^ 2 := by positivity
  obtain ⟨X, hX⟩ := exists_jasSignVariance_le
    (show 0 < ε * poleSharpConstant ^ 2 / (2 * (lagWeightTotal + 1)) by positivity)
  refine ⟨X, fun P hP => ?_⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ k ∈ Finset.univ.erase (cosZeroLetters P),
      ∑ k' ∈ (Finset.univ.erase (cosZeroLetters P)).erase k,
        ‖cosineTranslateWeight P σ k‖ * ‖cosineTranslateWeight P σ k'‖ *
          (2 / |cosineTranslateFreq P k - cosineTranslateFreq P k'|) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB]; exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun k' _ => by positivity
  refine ⟨2 * B / (ε * poleSharpConstant ^ 2) + 1, fun T hT => ?_⟩
  have hT0 : 0 ≤ T := le_trans (by positivity) hT
  have hvol := volume_cosineTranslate_re_neg_mul_le hσ P hT0
  have hms := integral_norm_sq_expSum_le (Finset.univ.erase (cosZeroLetters P))
    (cosineTranslateWeight P σ) (cosineTranslateFreq P)
    ((cosineTranslateFreq_injective P).injOn) hT0
  have hdev : (fun τ : ℝ => ‖cosineTranslateDeviation P σ τ‖ ^ 2) = fun τ : ℝ =>
      ‖∑ k ∈ Finset.univ.erase (cosZeroLetters P),
        cosineTranslateWeight P σ k * expPhase τ (cosineTranslateFreq P k)‖ ^ 2 := rfl
  rw [← hB] at hms
  have hC := sum_norm_sq_cosineTranslateWeight_le hσ P
  have hV := hX P hP
  have hCV : ∑ k ∈ Finset.univ.erase (cosZeroLetters P), ‖cosineTranslateWeight P σ k‖ ^ 2 ≤
      ε * poleSharpConstant ^ 2 / 2 := by
    calc _ ≤ lagWeightTotal * jasSignVariance P := hC
      _ ≤ lagWeightTotal * (ε * poleSharpConstant ^ 2 / (2 * (lagWeightTotal + 1))) :=
          mul_le_mul_of_nonneg_left hV hW0
      _ ≤ (lagWeightTotal + 1) * (ε * poleSharpConstant ^ 2 / (2 * (lagWeightTotal + 1))) := by
          gcongr; linarith
      _ = ε * poleSharpConstant ^ 2 / 2 := by field_simp
  have hBT : B ≤ T * (ε * poleSharpConstant ^ 2 / 2) := by
    have h1 : 2 * B / (ε * poleSharpConstant ^ 2) ≤ T := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    nlinarith
  have htotal : ∫ τ in (0 : ℝ)..T, ‖cosineTranslateDeviation P σ τ‖ ^ 2 ≤
      ε * T * poleSharpConstant ^ 2 := by
    calc ∫ τ in (0 : ℝ)..T, ‖cosineTranslateDeviation P σ τ‖ ^ 2
        ≤ T * ∑ k ∈ Finset.univ.erase (cosZeroLetters P), ‖cosineTranslateWeight P σ k‖ ^ 2 + B :=
          hms
      _ ≤ T * (ε * poleSharpConstant ^ 2 / 2) + T * (ε * poleSharpConstant ^ 2 / 2) := by
          gcongr
      _ = ε * T * poleSharpConstant ^ 2 := by ring
  exact le_of_mul_le_mul_right (hvol.trans htotal) hΦ2

end

end RHTower

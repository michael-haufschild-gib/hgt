import GaloisForLFunctions.HTGeometry.PrimeGammaFrameInjective
import GaloisForLFunctions.RHTower.PrimeHodgeCubicOrbitBirth
import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearHomotopyDefect
import GaloisForLFunctions.RHTower.ThetaSurvivalRelativeCurvaturePrimeLift

/-!
# The operator form of the prime–Hodge cubic Sylvester law

Let `λ_p = log p`, `μ_d` the normalized transported Stokes prime law, `A_d` the normalized cofinal
Stokes child operator on `ℓ²(Primes)`, and `b_d(p) = √μ_d(p) λ_p^{3/2}` the cubic birth vector.

* **(PCOB.2)** `b_d ∈ ℓ²(Primes)` with `‖b_d‖² = ∑_p μ_d(p) λ_p³`.
* **(PCOB.13)–(PCOB.14)** Every monomial `L^m A_d L^{3-m}` (`L e_p = λ_p e_p`), defined on finite
  prime support, extends to a Hilbert–Schmidt operator (entries bounded by `8|b_d(p) b_d(q)|`), and
  `L³A_d + 3L²A_dL + 3LA_dL² + A_dL³ = 8|b_d⟩⟨b_d|`.
* The law is rigid: a bounded operator satisfying it on finite support is `A_d`.
* **(PCOB.15)** With `Λ = I ⊗ L` on history–prime space, `S_Λ³(𝖳(t)) = 8 sgn(t) Φ ⊗ |b_{|t|}⟩⟨b_{|t|}|`.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate
open InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

variable {d : ℝ}

/-! ## The birth vector -/

/-- **(PCOB.1)** `|b_d(p)|² = μ_d(p) λ_p³`. -/
theorem norm_sq_primeHodgeCubicBirthVector (hd : 0 < d) (p : Nat.Primes) :
    ‖primeHodgeCubicBirthVector d p‖ ^ 2 = primeFormationLaw d p * Real.log (p : ℝ) ^ 3 := by
  have h := primeHodgeCubicBirthVector_diagonal hd p
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

theorem summable_norm_sq_primeHodgeCubicBirthVector (hd : 0 < d) :
    Summable fun p : Nat.Primes => ‖primeHodgeCubicBirthVector d p‖ ^ 2 := by
  simp_rw [norm_sq_primeHodgeCubicBirthVector hd]
  exact summable_primeFormationLaw_mul_log_pow hd 3

/-- **(PCOB.2)** The birth vector `b_d ∈ ℓ²(Primes)`. -/
def primeCubicBirthLp (hd : 0 < d) : ℓ²P :=
  ⟨fun p => primeHodgeCubicBirthVector d p,
    HilbertSchmidt.memℓp_of_sq (summable_norm_sq_primeHodgeCubicBirthVector hd)⟩

theorem primeCubicBirthLp_apply (hd : 0 < d) (p : Nat.Primes) :
    primeCubicBirthLp hd p = primeHodgeCubicBirthVector d p := rfl

theorem norm_sq_primeCubicBirthLp (hd : 0 < d) :
    ‖primeCubicBirthLp hd‖ ^ 2 = ∑' p : Nat.Primes, primeFormationLaw d p * Real.log (p : ℝ) ^ 3 := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  exact tsum_congr fun p => norm_sq_primeHodgeCubicBirthVector hd p

/-! ## Sylvester monomials -/

/-- The kernel of `L^m A_d L^{3-m}`: `λ_p^m A_d(p,q) λ_q^{3-m}`. -/
def cubicSylvesterKernel (d : ℝ) (m : ℕ) (pq : Nat.Primes × Nat.Primes) : ℂ :=
  ((Real.log (pq.1 : ℝ) : ℂ) ^ m) * normalizedStokesPrimeKernel d pq *
    ((Real.log (pq.2 : ℝ) : ℂ) ^ (3 - m))

theorem norm_normalizedStokesPrimeKernel_mul_cube (hd : 0 < d) (p q : Nat.Primes) :
    (Real.log (p : ℝ) + Real.log (q : ℝ)) ^ 3 * ‖normalizedStokesPrimeKernel d (p, q)‖ =
      8 * ‖primeHodgeCubicBirthVector d p‖ * ‖primeHodgeCubicBirthVector d q‖ := by
  have h := congrArg norm (primeHodgeCubicClock_normalizedStokesKernel hd p q)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg
    (add_pos (primeClock_pos p) (primeClock_pos q)).le, norm_mul, norm_mul, norm_star] at h
  rw [h]
  norm_num

/-- **Monomial entry bound.**  `|λ_p^m A_d(p,q) λ_q^{3-m}| ≤ 8|b_d(p)||b_d(q)|` for `m ≤ 3`. -/
theorem norm_cubicSylvesterKernel_le (hd : 0 < d) {m : ℕ} (hm : m ≤ 3) (p q : Nat.Primes) :
    ‖cubicSylvesterKernel d m (p, q)‖ ≤
      8 * ‖primeHodgeCubicBirthVector d p‖ * ‖primeHodgeCubicBirthVector d q‖ := by
  have hp := (primeClock_pos p).le
  have hq := (primeClock_pos q).le
  have hpq : 0 < Real.log (p : ℝ) + Real.log (q : ℝ) := add_pos (primeClock_pos p) (primeClock_pos q)
  rw [← norm_normalizedStokesPrimeKernel_mul_cube hd, cubicSylvesterKernel, norm_mul, norm_mul,
    norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hp,
    Real.norm_of_nonneg hq]
  have hmono : Real.log (p : ℝ) ^ m * Real.log (q : ℝ) ^ (3 - m) ≤
      (Real.log (p : ℝ) + Real.log (q : ℝ)) ^ 3 := by
    calc Real.log (p : ℝ) ^ m * Real.log (q : ℝ) ^ (3 - m)
        ≤ (Real.log (p : ℝ) + Real.log (q : ℝ)) ^ m *
            (Real.log (p : ℝ) + Real.log (q : ℝ)) ^ (3 - m) := by
          gcongr
          · linarith
          · linarith
      _ = (Real.log (p : ℝ) + Real.log (q : ℝ)) ^ 3 := by
          rw [← pow_add, Nat.add_sub_cancel' hm]
  calc Real.log (p : ℝ) ^ m * ‖normalizedStokesPrimeKernel d (p, q)‖ * Real.log (q : ℝ) ^ (3 - m)
      = (Real.log (p : ℝ) ^ m * Real.log (q : ℝ) ^ (3 - m)) *
          ‖normalizedStokesPrimeKernel d (p, q)‖ := by ring
    _ ≤ (Real.log (p : ℝ) + Real.log (q : ℝ)) ^ 3 * ‖normalizedStokesPrimeKernel d (p, q)‖ :=
        mul_le_mul_of_nonneg_right hmono (norm_nonneg _)

theorem isHS_cubicSylvesterKernel (hd : 0 < d) {m : ℕ} (hm : m ≤ 3) :
    HilbertSchmidt.IsHS (cubicSylvesterKernel d m) := by
  have hb := summable_norm_sq_primeHodgeCubicBirthVector hd
  have hprod := (hb.mul_of_nonneg hb (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)).mul_left 64
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun pq => ?_) hprod
  have h := norm_cubicSylvesterKernel_le hd hm pq.1 pq.2
  calc ‖cubicSylvesterKernel d m pq‖ ^ 2
      ≤ (8 * ‖primeHodgeCubicBirthVector d pq.1‖ * ‖primeHodgeCubicBirthVector d pq.2‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 64 * (‖primeHodgeCubicBirthVector d pq.1‖ ^ 2 * ‖primeHodgeCubicBirthVector d pq.2‖ ^ 2) := by
        ring

/-- The Hilbert–Schmidt extension of `L^m A_d L^{3-m}`. -/
def cubicSylvesterTerm (hd : 0 < d) {m : ℕ} (hm : m ≤ 3) : ℓ²P →L[ℂ] ℓ²P :=
  HilbertSchmidt.toOperator (isHS_cubicSylvesterKernel hd hm)

/-- On the prime basis `⟨e_p, (L^m A_d L^{3-m}) e_q⟩ = ⟨L^m e_p, A_d L^{3-m} e_q⟩`. -/
theorem inner_single_cubicSylvesterTerm (hd : 0 < d) {m : ℕ} (hm : m ≤ 3) (p q : Nat.Primes) :
    ⟪(lp.single 2 p (1 : ℂ) : ℓ²P), cubicSylvesterTerm hd hm (lp.single 2 q 1)⟫_ℂ =
      ((Real.log (p : ℝ) : ℂ) ^ m) * normalizedStokesPrimeKernel d (p, q) *
        ((Real.log (q : ℝ) : ℂ) ^ (3 - m)) := by
  rw [lp.inner_single_left, cubicSylvesterTerm, HilbertSchmidt.toOperator_single]
  simp [cubicSylvesterKernel]

theorem inner_single_rankOne (b : ℓ²P) (p q : Nat.Primes) :
    ⟪(lp.single 2 p (1 : ℂ) : ℓ²P), (rankOne ℂ b b) (lp.single 2 q 1)⟫_ℂ = b p * star (b q) := by
  rw [rankOne_apply, inner_smul_right, lp.inner_single_left, lp.inner_single_right]
  simp only [RCLike.inner_apply, map_one, one_mul, mul_one, Complex.star_def]
  ring

/-- **(PCOB.13)–(PCOB.14), the cubic Sylvester law.**
`L³A_d + 3L²A_dL + 3LA_dL² + A_dL³ = 8|b_d⟩⟨b_d|`. -/
theorem cubicSylvester_law (hd : 0 < d) :
    cubicSylvesterTerm hd (m := 3) le_rfl + (3 : ℂ) • cubicSylvesterTerm hd (m := 2) (by norm_num) +
        (3 : ℂ) • cubicSylvesterTerm hd (m := 1) (by norm_num) +
        cubicSylvesterTerm hd (m := 0) (by norm_num) =
      (8 : ℂ) • rankOne ℂ (primeCubicBirthLp hd) (primeCubicBirthLp hd) := by
  refine ext_of_inner_single fun p q => ?_
  simp only [add_apply, smul_apply, inner_add_right,
    inner_smul_right, inner_single_cubicSylvesterTerm, inner_single_rankOne, primeCubicBirthLp_apply]
  have h := primeHodgeCubicClock_normalizedStokesKernel hd p q
  rw [show (8 : ℂ) * (primeHodgeCubicBirthVector d p * star (primeHodgeCubicBirthVector d q)) =
    8 * primeHodgeCubicBirthVector d p * star (primeHodgeCubicBirthVector d q) by ring, ← h]
  simp only [Nat.sub_self, Nat.reduceSub, pow_zero, pow_one, mul_one, one_mul]
  push_cast
  ring

/-- **Rigidity.**  A bounded operator satisfying the cubic law on finite prime support is `A_d`. -/
theorem eq_normalizedStokesPrimeOperator_of_cubicLaw (hd : 0 < d) (X : ℓ²P →L[ℂ] ℓ²P)
    (hX : ∀ p q : Nat.Primes,
      ((Real.log (p : ℝ) + Real.log (q : ℝ) : ℝ) : ℂ) ^ 3 *
          ⟪(lp.single 2 p (1 : ℂ) : ℓ²P), X (lp.single 2 q 1)⟫_ℂ =
        8 * primeHodgeCubicBirthVector d p * star (primeHodgeCubicBirthVector d q)) :
    X = normalizedStokesPrimeOperator hd := by
  refine ext_of_inner_single fun p q => ?_
  have hne : ((Real.log (p : ℝ) + Real.log (q : ℝ) : ℝ) : ℂ) ^ 3 ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.2 (add_pos (primeClock_pos p) (primeClock_pos q)).ne')
  refine mul_left_cancel₀ hne ?_
  rw [hX, normalizedStokesPrimeOperator, lp.inner_single_left, HilbertSchmidt.toOperator_single,
    ← primeHodgeCubicClock_normalizedStokesKernel hd p q]
  simp

/-! ## The joint history–prime law -/

/-- The kernel of `Λ^m 𝖳_d Λ^{3-m}` with `Λ = I ⊗ L`. -/
def jointCubicSylvesterKernel (d : ℝ) (m : ℕ)
    (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) : ℂ :=
  ((Real.log (ab.1.2 : ℝ) : ℂ) ^ m) * primeHodgeHistoryDefectKernel d ab *
    ((Real.log (ab.2.2 : ℝ) : ℂ) ^ (3 - m))

/-- The history-weighted birth mass `8 w_n |b_d(p)|²`. -/
def historyBirthMass (d : ℝ) (np : PrimeHodgeHistoryIndex) : ℝ :=
  8 * PrimeHodgeHistory.w np.1 * ‖primeHodgeCubicBirthVector d np.2‖ ^ 2

theorem summable_historyBirthMass (hd : 0 < d) : Summable (historyBirthMass d) := by
  have hw : Summable fun n => ‖(PrimeHodgeHistory.w n : ℝ)‖ := by
    simpa [Real.norm_of_nonneg (PrimeHodgeHistory.w_pos _).le] using PrimeHodgeHistory.summable_w
  have hb : Summable fun p => ‖‖primeHodgeCubicBirthVector d p‖ ^ 2‖ := by
    simpa using summable_norm_sq_primeHodgeCubicBirthVector hd
  have h := (summable_mul_of_summable_norm hw hb).mul_left 8
  exact h.congr fun np => by simp only [historyBirthMass]; ring

theorem norm_sq_jointCubicSylvesterKernel_le (hd : 0 < d) {m : ℕ} (hm : m ≤ 3)
    (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) :
    ‖jointCubicSylvesterKernel d m ab‖ ^ 2 ≤ historyBirthMass d ab.1 * historyBirthMass d ab.2 := by
  obtain ⟨⟨n, p⟩, ⟨k, q⟩⟩ := ab
  by_cases hnk : n = k
  · subst hnk
    have hS := norm_cubicSylvesterKernel_le hd hm p q
    have hw := (PrimeHodgeHistory.w_pos n).le
    have hkey : ‖jointCubicSylvesterKernel d m ((n, p), (n, q))‖ =
        PrimeHodgeHistory.w n * ‖cubicSylvesterKernel d m (p, q)‖ := by
      rw [jointCubicSylvesterKernel, primeHodgeHistoryDefectKernel, if_pos rfl, cubicSylvesterKernel]
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hw]
      ring
    rw [hkey, mul_pow, historyBirthMass, historyBirthMass]
    have h1 : PrimeHodgeHistory.w n ^ 2 * ‖cubicSylvesterKernel d m (p, q)‖ ^ 2 ≤
        PrimeHodgeHistory.w n ^ 2 * (8 * ‖primeHodgeCubicBirthVector d p‖ *
          ‖primeHodgeCubicBirthVector d q‖) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hS 2) (sq_nonneg _)
    refine h1.trans (le_of_eq ?_)
    ring
  · rw [jointCubicSylvesterKernel, primeHodgeHistoryDefectKernel, if_neg hnk]
    simp only [mul_zero, zero_mul, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (PrimeHodgeHistory.w_pos n).le)
      (sq_nonneg _)) (mul_nonneg (mul_nonneg (by norm_num) (PrimeHodgeHistory.w_pos k).le)
      (sq_nonneg _))

theorem isHS_jointCubicSylvesterKernel (hd : 0 < d) {m : ℕ} (hm : m ≤ 3) :
    HilbertSchmidt.IsHS (jointCubicSylvesterKernel d m) := by
  have hB := summable_historyBirthMass hd
  have hnn : ∀ np, 0 ≤ historyBirthMass d np := fun np =>
    mul_nonneg (mul_nonneg (by norm_num) (PrimeHodgeHistory.w_pos _).le) (sq_nonneg _)
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (norm_sq_jointCubicSylvesterKernel_le hd hm) (hB.mul_of_nonneg hB hnn hnn)

/-- The Hilbert–Schmidt extension of `Λ^m 𝖳_d Λ^{3-m}`. -/
def jointCubicSylvesterTerm (hd : 0 < d) {m : ℕ} (hm : m ≤ 3) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  HilbertSchmidt.toOperator (isHS_jointCubicSylvesterKernel hd hm)

theorem isHS_primeHodgeHistoryCubicBirthKernel (hd : 0 < d) :
    HilbertSchmidt.IsHS (primeHodgeHistoryCubicBirthKernel d) := by
  have hB := summable_historyBirthMass hd
  have hnn : ∀ np, 0 ≤ historyBirthMass d np := fun np =>
    mul_nonneg (mul_nonneg (by norm_num) (PrimeHodgeHistory.w_pos _).le) (sq_nonneg _)
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun ab => ?_) (hB.mul_of_nonneg hB hnn hnn)
  obtain ⟨⟨n, p⟩, ⟨k, q⟩⟩ := ab
  by_cases hnk : n = k
  · subst hnk
    have hw := (PrimeHodgeHistory.w_pos n).le
    rw [primeHodgeHistoryCubicBirthKernel, dif_pos rfl, historyBirthMass, historyBirthMass]
    simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg hw]
    nlinarith [norm_nonneg (primeHodgeCubicBirthVector d p), norm_nonneg (primeHodgeCubicBirthVector d q),
      sq_nonneg (PrimeHodgeHistory.w n * ‖primeHodgeCubicBirthVector d p‖ *
        ‖primeHodgeCubicBirthVector d q‖), mul_nonneg hw (sq_nonneg (‖primeHodgeCubicBirthVector d p‖ *
          ‖primeHodgeCubicBirthVector d q‖))]
  · rw [primeHodgeHistoryCubicBirthKernel, dif_neg hnk, norm_zero, zero_pow two_ne_zero]
    exact mul_nonneg (hnn _) (hnn _)

/-- The joint source `Φ ⊗ |b_d⟩⟨b_d|`. -/
def historyCubicBirthOperator (hd : 0 < d) : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  HilbertSchmidt.toOperator (isHS_primeHodgeHistoryCubicBirthKernel hd)

theorem inner_single_historyCubicBirthOperator (hd : 0 < d) (a b : PrimeHodgeHistoryIndex) :
    ⟪(lp.single 2 a (1 : ℂ) : PrimeHodgeHistoryHilbert), historyCubicBirthOperator hd
        (lp.single 2 b 1)⟫_ℂ =
      if a.1 = b.1 then (PrimeHodgeHistory.w a.1 : ℂ) * primeHodgeCubicBirthVector d a.2 *
        star (primeHodgeCubicBirthVector d b.2) else 0 := by
  rw [lp.inner_single_left, historyCubicBirthOperator, HilbertSchmidt.toOperator_single]
  rw [primeHodgeHistoryCubicBirthKernel]
  split_ifs <;> simp

theorem inner_single_jointCubicSylvesterTerm (hd : 0 < d) {m : ℕ} (hm : m ≤ 3)
    (a b : PrimeHodgeHistoryIndex) :
    ⟪(lp.single 2 a (1 : ℂ) : PrimeHodgeHistoryHilbert), jointCubicSylvesterTerm hd hm
        (lp.single 2 b 1)⟫_ℂ = jointCubicSylvesterKernel d m (a, b) := by
  rw [lp.inner_single_left, jointCubicSylvesterTerm, HilbertSchmidt.toOperator_single]
  simp

/-- **(PCOB.15) for `t = d > 0`.**  `S_Λ³(𝖳_d) = 8 Φ ⊗ |b_d⟩⟨b_d|`. -/
theorem jointCubicSylvester_law (hd : 0 < d) :
    jointCubicSylvesterTerm hd (m := 3) le_rfl +
        (3 : ℂ) • jointCubicSylvesterTerm hd (m := 2) (by norm_num) +
        (3 : ℂ) • jointCubicSylvesterTerm hd (m := 1) (by norm_num) +
        jointCubicSylvesterTerm hd (m := 0) (by norm_num) =
      (8 : ℂ) • historyCubicBirthOperator hd := by
  refine ext_of_inner_single fun a b => ?_
  simp only [add_apply, smul_apply, inner_add_right,
    inner_smul_right, inner_single_jointCubicSylvesterTerm, inner_single_historyCubicBirthOperator]
  have h := primeHodgeHistoryCubicClockCore_eq_birth hd (a, b)
  simp only [primeHodgeHistoryCubicClockCore, primeHodgeHistoryCubicClock,
    primeHodgeHistoryCubicBirthKernel] at h
  simp only [jointCubicSylvesterKernel]
  split_ifs at h ⊢ with hab
  · rw [← h]
    push_cast
    ring
  · rw [primeHodgeHistoryDefectKernel, if_neg hab]
    ring

/-- **(PCOB.15), signed family.**  For `t ≠ 0`,
`S_Λ³(𝖳(t)) = 8 sgn(t) Φ ⊗ |b_{|t|}⟩⟨b_{|t|}|`, where `𝖳(t) = sgn(t) 𝖳_{|t|}`. -/
theorem jointCubicSylvester_law_signed {t : ℝ} (ht : t ≠ 0) :
    (Real.sign t : ℂ) • (jointCubicSylvesterTerm (abs_pos.2 ht) (m := 3) le_rfl +
        (3 : ℂ) • jointCubicSylvesterTerm (abs_pos.2 ht) (m := 2) (by norm_num) +
        (3 : ℂ) • jointCubicSylvesterTerm (abs_pos.2 ht) (m := 1) (by norm_num) +
        jointCubicSylvesterTerm (abs_pos.2 ht) (m := 0) (by norm_num)) =
      (8 * Real.sign t : ℂ) • historyCubicBirthOperator (abs_pos.2 ht) ∧
    primeHodgeHistoryIntegralNuclearHomotopyDefect t =
      (Real.sign t : ℂ) • primeHodgeHistoryDefectOperator (abs_pos.2 ht) := by
  refine ⟨?_, ?_⟩
  · rw [jointCubicSylvester_law, smul_smul, mul_comm]
  · simp [primeHodgeHistoryIntegralNuclearHomotopyDefect, ht]

/-- The joint monomials are the extensions of `Λ^m 𝖳_d Λ^{3-m}` from finite support: their entries
are `λ_p^m 𝖳_d((n,p),(k,q)) λ_q^{3-m}`. -/
theorem jointCubicSylvesterTerm_entry (hd : 0 < d) {m : ℕ} (hm : m ≤ 3)
    (a b : PrimeHodgeHistoryIndex) :
    ⟪(lp.single 2 a (1 : ℂ) : PrimeHodgeHistoryHilbert), jointCubicSylvesterTerm hd hm
        (lp.single 2 b 1)⟫_ℂ =
      ((Real.log (a.2 : ℝ) : ℂ) ^ m) *
        ⟪(lp.single 2 a (1 : ℂ) : PrimeHodgeHistoryHilbert), primeHodgeHistoryDefectOperator hd
          (lp.single 2 b 1)⟫_ℂ * ((Real.log (b.2 : ℝ) : ℂ) ^ (3 - m)) := by
  rw [inner_single_jointCubicSylvesterTerm, primeHodgeHistoryDefectOperator, lp.inner_single_left,
    HilbertSchmidt.toOperator_single]
  simp [jointCubicSylvesterKernel]

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.ArithmeticKreinLangerTheory.MultivariateParityAuxiliariesReachTheMainTerm
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheForcedJumpsOfAProducer

/-!
# Quantitative cost of parity-selective factorial producers

The Möbius–Farkas producer has an explicit alphabet radius depending on the slope excess.
Its Stirling error is polynomial in that radius. Clearing denominators introduces no extra
normalized cost: both the slope and the required prime multiplicity scale by that denominator.
-/

open Finset
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics

noncomputable section
namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-- Explicit alphabet radius for slope excess `ε` and absolute scale constant `K`. -/
def producerRadius (K ε : ℝ) : ℕ :=
  producerPeriod (ε / 2) (Nat.ceil (K / ε) + 10)

/-- The normalized Stirling cost at the explicit alphabet radius. -/
def producerCost (K ε : ℝ) : ℝ :=
  8 * (producerRadius K ε : ℝ) ^ 3 * (5 + Real.log (producerRadius K ε))

theorem producerPeriod_pos (ε : ℝ) (ℓ : ℕ) : 0 < producerPeriod ε ℓ := by
  unfold producerPeriod
  exact Nat.mul_pos (pow_pos zero_lt_two _) (Nat.factorial_pos _)

theorem producerCost_pos (K ε : ℝ) : 0 < producerCost K ε := by
  have hP : 0 < producerRadius K ε := producerPeriod_pos _ _
  have hPR : (0 : ℝ) < producerRadius K ε := by exact_mod_cast hP
  have hlog : 0 ≤ Real.log (producerRadius K ε) := Real.log_natCast_nonneg _
  unfold producerCost
  positivity

private theorem log_factorial_le_sq {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hfac0 : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have hlog := Real.log_le_log hfac0 hfac
  rw [Real.log_pow] at hlog
  have hnlog : Real.log (n : ℝ) ≤ n := by linarith [Real.log_le_sub_one_of_pos hn0]
  exact hlog.trans (by nlinarith [mul_le_mul_of_nonneg_left hnlog hn0.le])

/-- The factorial period is at most doubly exponential in the cutoff exponent and inverse
slope excess. The estimate uses only `log(n!) ≤ n²` and the explicit period formula. -/
theorem producerPeriod_le_double_exp {ε : ℝ} (hε : 0 < ε) (_hε1 : ε ≤ 1) (ℓ : ℕ) :
    (producerPeriod ε ℓ : ℝ) ≤
      Real.exp (Real.exp (100 * ((ℓ : ℝ) + 1 + 1 / ε))) := by
  let t : ℝ := (ℓ : ℝ) + 1 + 1 / ε
  let B : ℕ := 2 ^ ℓ + 1
  let F : ℕ := B.factorial
  let u : ℝ := 24 * (2 + Real.log (F : ℝ)) / ε
  let M : ℕ := max (4 * ℓ + 2) (Nat.ceil u + 6)
  have hinv0 : 0 ≤ 1 / ε := (one_div_pos.mpr hε).le
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have ht1 : 1 ≤ t := by dsimp [t]; linarith only [hℓ0, hinv0]
  have ht0 : 0 ≤ t := by linarith
  have hℓt : (ℓ : ℝ) ≤ t := by dsimp [t]; linarith
  have hinvt : 1 / ε ≤ t := by dsimp [t]; linarith only [hℓ0]
  have htexp : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hexp1 : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht0
  have hexp12 : Real.exp t ≤ Real.exp (2 * t) := Real.exp_le_exp.mpr (by linarith)
  have hexp23 : Real.exp (2 * t) ≤ Real.exp (3 * t) := Real.exp_le_exp.mpr (by linarith)
  have hB1 : 1 ≤ B := Nat.succ_le_succ (Nat.zero_le _)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hB : (B : ℝ) ≤ Real.exp t := by
    have hp1 : 1 ≤ 2 ^ ℓ := Nat.one_le_pow ℓ 2 zero_lt_two
    have hp : B ≤ 2 ^ (ℓ + 1) := by dsimp [B]; rw [pow_succ]; omega
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hlog : Real.log (B : ℝ) ≤ t := by
      calc Real.log (B : ℝ) ≤ Real.log (2 ^ (ℓ + 1) : ℕ) :=
          Real.log_le_log hB0 (by exact_mod_cast hp)
        _ = ((ℓ : ℝ) + 1) * Real.log 2 := by
          rw [Nat.cast_pow, Real.log_pow]; push_cast; rfl
        _ ≤ ((ℓ : ℝ) + 1) * 1 :=
          mul_le_mul_of_nonneg_left hlog2 (by positivity)
        _ ≤ t := by dsimp [t]; linarith
    calc (B : ℝ) = Real.exp (Real.log B) := (Real.exp_log hB0).symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr hlog
  have hF0 : (0 : ℝ) < F := by dsimp [F]; exact_mod_cast Nat.factorial_pos B
  have hlogF0 : 0 ≤ Real.log (F : ℝ) := Real.log_natCast_nonneg F
  have hlogF : Real.log (F : ℝ) ≤ Real.exp (2 * t) := by
    calc Real.log (F : ℝ) ≤ (B : ℝ) ^ 2 := log_factorial_le_sq hB1
      _ ≤ (Real.exp t) ^ 2 := pow_le_pow_left₀ hB0.le hB 2
      _ = Real.exp (2 * t) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu : u ≤ 72 * Real.exp (3 * t) := by
    have htwo : 2 + Real.log (F : ℝ) ≤ 3 * Real.exp (2 * t) := by
      linarith [hexp1.trans hexp12]
    have hi : 1 / ε ≤ Real.exp t := hinvt.trans htexp
    calc u = 24 * (2 + Real.log (F : ℝ)) * (1 / ε) := by dsimp [u]; ring
      _ ≤ 24 * (3 * Real.exp (2 * t)) * Real.exp t := by gcongr
      _ = 72 * Real.exp (3 * t) := by
        rw [show 24 * (3 * Real.exp (2 * t)) * Real.exp t =
          72 * (Real.exp (2 * t) * Real.exp t) by ring, ← Real.exp_add]
        congr 2
        ring
  have hceil : (Nat.ceil u : ℝ) ≤ u + 1 := (Nat.ceil_lt_add_one hu0).le
  have hM : (M : ℝ) ≤ 85 * Real.exp (3 * t) := by
    have hmax : (M : ℝ) ≤ 4 * (ℓ : ℝ) + 2 + ((Nat.ceil u : ℝ) + 6) := by
      dsimp only [M]
      rw [Nat.cast_max]
      push_cast
      exact max_le (le_add_of_nonneg_right (by positivity))
        (le_add_of_nonneg_left (by positivity))
    have hlarge : (ℓ : ℝ) ≤ Real.exp (3 * t) := hℓt.trans (htexp.trans (hexp12.trans hexp23))
    have hlarge1 : 1 ≤ Real.exp (3 * t) := hexp1.trans (hexp12.trans hexp23)
    linarith
  have hP0 : (0 : ℝ) < producerPeriod ε ℓ := by exact_mod_cast producerPeriod_pos ε ℓ
  have hperiod : (producerPeriod ε ℓ : ℝ) = (2 : ℝ) ^ M * F := by
    simp only [producerPeriod, M, u, F, B, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hlogP : Real.log (producerPeriod ε ℓ : ℝ) ≤ 86 * Real.exp (3 * t) := by
    rw [hperiod, Real.log_mul (pow_ne_zero _ two_ne_zero) hF0.ne', Real.log_pow]
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hm := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
    linarith [hlogF.trans hexp23]
  have h86 : (86 : ℝ) ≤ Real.exp 86 := by linarith [Real.add_one_le_exp (86 : ℝ)]
  have htop : 86 * Real.exp (3 * t) ≤ Real.exp (100 * t) := by
    calc 86 * Real.exp (3 * t) ≤ Real.exp 86 * Real.exp (3 * t) := by gcongr
      _ = Real.exp (86 + 3 * t) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (100 * t) := Real.exp_le_exp.mpr (by linarith)
  calc (producerPeriod ε ℓ : ℝ) = Real.exp (Real.log (producerPeriod ε ℓ : ℝ)) :=
      (Real.exp_log hP0).symm
    _ ≤ Real.exp (Real.exp (100 * t)) := Real.exp_le_exp.mpr (hlogP.trans htop)

/-- The alphabet radius grows at most as `exp(exp(C/ε))`, with an explicit affine dependence
of `C` on the absolute scale constant. -/
theorem producerRadius_le_double_exp {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (producerRadius K ε : ℝ) ≤ Real.exp (Real.exp ((100 * (K + 14)) / ε)) := by
  have hbase := producerPeriod_le_double_exp (by linarith : 0 < ε / 2)
    (by linarith : ε / 2 ≤ 1) (Nat.ceil (K / ε) + 10)
  have hceil : (Nat.ceil (K / ε) : ℝ) ≤ K / ε + 1 :=
    (Nat.ceil_lt_add_one (div_pos hK hε).le).le
  have h12 : (12 : ℝ) ≤ 12 / ε := by rw [le_div_iff₀ hε]; linarith
  refine hbase.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr ?_))
  push_cast
  have hid : 1 / (ε / 2) = 2 / ε := by field_simp
  rw [hid]
  calc
    100 * ((Nat.ceil (K / ε) : ℝ) + 10 + 1 + 2 / ε)
        ≤ 100 * (K / ε + 12 + 2 / ε) := by linarith only [hceil]
    _ ≤ 100 * (K / ε + 12 / ε + 2 / ε) := by linarith only [h12]
    _ = 100 * (K + 14) / ε := by ring

/-- The normalized error has the same doubly exponential rate as the alphabet radius. -/
theorem producerCost_le_double_exp {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    producerCost K ε ≤ Real.exp (Real.exp ((100 * (K + 14) + 52) / ε)) := by
  let A : ℝ := 100 * (K + 14)
  let U : ℝ := Real.exp (A / ε)
  have hU0 : 0 < U := Real.exp_pos _
  have hU1 : 1 ≤ U := Real.one_le_exp_iff.mpr (by dsimp [A]; positivity)
  have hUexp : U ≤ Real.exp U := by linarith [Real.add_one_le_exp U]
  have hexp1 : 1 ≤ Real.exp U := hU1.trans hUexp
  have hR0 : (0 : ℝ) < producerRadius K ε := by exact_mod_cast producerPeriod_pos (ε / 2) _
  have hR : (producerRadius K ε : ℝ) ≤ Real.exp U := producerRadius_le_double_exp hK hε hε1
  have hlog : Real.log (producerRadius K ε) ≤ U := by
    simpa only [Real.log_exp] using Real.log_le_log hR0 hR
  have hlog0 : 0 ≤ Real.log (producerRadius K ε) := Real.log_natCast_nonneg _
  have hcost : producerCost K ε ≤ 48 * Real.exp (4 * U) := by
    have hfac : 5 + Real.log (producerRadius K ε) ≤ 6 * Real.exp U := by linarith
    calc
      producerCost K ε ≤ 8 * (Real.exp U) ^ 3 * (6 * Real.exp U) := by
        unfold producerCost
        gcongr
      _ = 48 * Real.exp (4 * U) := by
        rw [show 4 * U = U + U + U + U by ring]
        simp only [Real.exp_add]
        ring
  have h48 : (48 : ℝ) ≤ Real.exp (48 * U) := by
    have h := Real.add_one_le_exp (48 : ℝ)
    exact (by linarith : (48 : ℝ) ≤ Real.exp 48).trans
      (Real.exp_le_exp.mpr (by linarith))
  have hcost' : producerCost K ε ≤ Real.exp (52 * U) := by
    calc producerCost K ε ≤ 48 * Real.exp (4 * U) := hcost
      _ ≤ Real.exp (48 * U) * Real.exp (4 * U) := by gcongr
      _ = Real.exp (52 * U) := by rw [← Real.exp_add]; congr 1; ring
  have h52 : (52 : ℝ) ≤ Real.exp (52 / ε) := by
    have h := Real.add_one_le_exp (52 : ℝ)
    refine (by linarith : (52 : ℝ) ≤ Real.exp 52).trans (Real.exp_le_exp.mpr ?_)
    rw [le_div_iff₀ hε]
    linarith
  refine hcost'.trans (Real.exp_le_exp.mpr ?_)
  change 52 * U ≤ Real.exp ((A + 52) / ε)
  rw [add_div, Real.exp_add]
  change 52 * U ≤ U * Real.exp (52 / ε)
  nlinarith [mul_le_mul_of_nonneg_left h52 hU0.le]

/-- Uniform quantitative dependence on the slope excess for an actual integer producer. -/
theorem exists_producer_with_quantitative_cost :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B ∧
        normSlope c m B < 1 + ε ∧ AlphabetLE c (producerRadius K ε) ∧
        stencilErrorConst c / m ≤ producerCost K ε := by
  obtain ⟨K, hK, hprod⟩ := exists_producer_with_quantitative_support
  refine ⟨K, hK, fun ε hε hε1 => ?_⟩
  obtain ⟨c, m, B, hc0, hbal, hm, hB, hn, hw, hs, _, hdvd⟩ := hprod ε hε hε1
  have hP : IsProducer c m B := ⟨hc0, hbal, hn, hm, hB, hw⟩
  have hA : normSlope c m B < 1 + ε := hs
  have halphabet : AlphabetLE c (producerRadius K ε) := fun k hk =>
    Nat.le_of_dvd (producerPeriod_pos _ _) (hdvd k hk)
  have hS : stencilSlope c ≤ 2 * m := by
    have heq : stencilSlope c = normSlope c m B * ((m : ℝ) * (1 - 1 / (B : ℝ))) := by
      rw [normSlope, div_mul_cancel₀ _ (mul_pos hP.m_pos hP.one_sub_pos).ne']
    have hbound : (m : ℝ) * (1 - 1 / (B : ℝ)) ≤ m := by
      have hfactor : 1 - 1 / (B : ℝ) ≤ 1 := sub_le_self _ (by positivity)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor hP.m_pos.le
    rw [heq]
    calc normSlope c m B * ((m : ℝ) * (1 - 1 / (B : ℝ)))
        ≤ 2 * ((m : ℝ) * (1 - 1 / (B : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_pos hP.m_pos hP.one_sub_pos).le
      _ ≤ 2 * m := mul_le_mul_of_nonneg_left hbound (by norm_num)
  refine ⟨c, m, B, hP, hA, halphabet, ?_⟩
  rw [div_le_iff₀ hP.m_pos]
  have hE := hP.stencilErrorConst_le halphabet
  have hlog : 0 ≤ Real.log (producerRadius K ε) := Real.log_natCast_nonneg _
  have hfac : 0 ≤ (producerRadius K ε : ℝ) ^ 3 *
      (5 + Real.log (producerRadius K ε)) := by positivity
  unfold producerCost
  nlinarith only [hE, mul_le_mul_of_nonneg_right hS hfac]

/-- One absolute constant bounds both the alphabet and the normalized error of actual
integer producers, uniformly in their slope excess. -/
theorem exists_producer_with_double_exp_cost :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B ∧
        normSlope c m B < 1 + ε ∧
        (∀ k ∈ c.support, (k : ℝ) ≤ Real.exp (Real.exp (C / ε))) ∧
        stencilErrorConst c / m ≤ Real.exp (Real.exp (C / ε)) := by
  obtain ⟨K, hK, hprod⟩ := exists_producer_with_quantitative_cost
  refine ⟨100 * (K + 14) + 52, by positivity, fun ε hε hε1 => ?_⟩
  obtain ⟨c, m, B, hP, hA, halphabet, hE⟩ := hprod ε hε hε1
  refine ⟨c, m, B, hP, hA, ?_, hE.trans (producerCost_le_double_exp hK hε hε1)⟩
  intro k hk
  have hkR : (k : ℝ) ≤ producerRadius K ε := by exact_mod_cast halphabet k hk
  refine hkR.trans ((producerRadius_le_double_exp hK hε hε1).trans ?_)
  apply Real.exp_le_exp.mpr
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (by linarith) hε.le

/-- The factorial construction yields a prime-count bound with one explicit cost function
for every `ε`; only its absolute scale constant is unspecified. -/
theorem exists_psi_le_quantitative_producer_cost :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : ℝ, 1 ≤ x →
      Chebyshev.psi x ≤ (1 + ε) * x +
        producerCost K ε * (1 + Real.log x) * (1 + Real.log x / Real.log 2) := by
  obtain ⟨K, hK, hprod⟩ := exists_producer_with_quantitative_cost
  refine ⟨K, hK, fun ε hε hε1 x hx => ?_⟩
  obtain ⟨c, m, B, hP, hA, halphabet, _⟩ := hprod ε hε hε1
  have h := hP.psi_le_of_alphabet halphabet (by linarith : normSlope c m B ≤ 2) hx
  have hmain := mul_le_mul_of_nonneg_right hA.le (by linarith : 0 ≤ x)
  exact h.trans (add_le_add hmain le_rfl)

/-- The main-term factorial producers have a uniform doubly exponential cost in `1/ε`. -/
theorem exists_psi_le_double_exp_producer_cost :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : ℝ, 2 ≤ x →
      Chebyshev.psi x ≤ (1 + ε) * x +
        12 * Real.exp (Real.exp (C / ε)) * (Real.log x) ^ 2 := by
  obtain ⟨K, hK, hpsi⟩ := exists_psi_le_quantitative_producer_cost
  refine ⟨100 * (K + 14) + 52, by positivity, fun ε hε hε1 x hx => ?_⟩
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlx : (1 / 2 : ℝ) ≤ Real.log x :=
    hl2.trans (Real.log_le_log (by norm_num) hx)
  have hlx0 : 0 ≤ Real.log x := by linarith only [hlx]
  have hl20 : 0 < Real.log 2 := by linarith
  have hquot : Real.log x / Real.log 2 ≤ 2 * Real.log x := by
    rw [div_le_iff₀ hl20]
    nlinarith only [mul_le_mul_of_nonneg_right hl2 hlx0]
  have hfirst : 1 + Real.log x ≤ 3 * Real.log x := by linarith
  have hsecond : 1 + Real.log x / Real.log 2 ≤ 4 * Real.log x := by linarith
  have hcost := producerCost_le_double_exp hK hε hε1
  refine (hpsi ε hε hε1 x (by linarith)).trans (add_le_add le_rfl ?_)
  calc producerCost K ε * (1 + Real.log x) * (1 + Real.log x / Real.log 2)
      ≤ Real.exp (Real.exp ((100 * (K + 14) + 52) / ε)) *
          (3 * Real.log x) * (4 * Real.log x) := by gcongr
    _ = _ := by ring

/-- The same producer cost controls the first Chebyshev function. -/
theorem exists_theta_le_double_exp_producer_cost :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : ℝ, 2 ≤ x →
      Chebyshev.theta x ≤ (1 + ε) * x +
        12 * Real.exp (Real.exp (C / ε)) * (Real.log x) ^ 2 := by
  obtain ⟨C, hC, hpsi⟩ := exists_psi_le_double_exp_producer_cost
  exact ⟨C, hC, fun ε hε hε1 x hx => (Chebyshev.theta_le_psi x).trans (hpsi ε hε hε1 x hx)⟩

/-- Below the parity-blind floor the bounded-cost producers necessarily have both signs
among their nontrivial letters. -/
theorem exists_parity_producer_with_quantitative_cost :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 30 →
      ∃ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B ∧
        (∃ k₁ : ℕ, 2 ≤ k₁ ∧ 0 < c k₁) ∧
        (∃ k₂ : ℕ, 2 ≤ k₂ ∧ c k₂ < 0) ∧
        normSlope c m B < 1 + ε ∧ AlphabetLE c (producerRadius K ε) ∧
        stencilErrorConst c / m ≤ producerCost K ε := by
  obtain ⟨K, hK, hprod⟩ := exists_producer_with_quantitative_cost
  refine ⟨K, hK, fun ε hε hε1 => ?_⟩
  obtain ⟨c, m, B, hP, hA, halphabet, hE⟩ := hprod ε hε (by linarith)
  have hsign := exists_sign_alternation_of_slope_le hP.zero hP.balanced
    hP.one_le_m hP.two_le_B hP.window (by
      change normSlope c m B ≤ 31 / 30
      linarith)
  exact ⟨c, m, B, hP, hsign.1, hsign.2, hA, halphabet, hE⟩

end GaloisForLFunctions.ArithmeticKreinLangerTheory

import GaloisForLFunctions.HTGeometry.ConstitutiveLocalRenewalActionThreshold

/-!
# Sharp local renewal schedules

This module realizes the superquadratic side of ULF-CRG-1 on exact two-point spaces: exponential
baseline mass, polynomial renewed mass, constant admitted current, finite KL action, and entrance
into a compact finite-action sublevel.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real InformationTheory Set ProbabilityTheory Filter Topology
open scoped ENNReal Topology

noncomputable section

/-- When renewed aperture mass dominates baseline mass, binary KL has its sharp one-sided bound. -/
theorem binaryRenewalCost_le_mul_log_inv
    (epsilon alpha : unitInterval)
    (hepsilon0 : 0 < (epsilon : ℝ)) (hepsilon1 : (epsilon : ℝ) < 1)
    (halpha0 : 0 < (alpha : ℝ)) (halpha1 : (alpha : ℝ) < 1)
    (hle : (epsilon : ℝ) ≤ (alpha : ℝ)) :
    binaryRenewalCost epsilon alpha ≤
      (alpha : ℝ) * Real.log (1 / (epsilon : ℝ)) := by
  rw [binaryRenewalCost_eq_klDiv epsilon alpha hepsilon0 hepsilon1 halpha0 halpha1,
    toReal_klDiv_bernoulli alpha epsilon halpha0 halpha1 hepsilon0 hepsilon1]
  have hratioPos : 0 < (alpha : ℝ) / (epsilon : ℝ) := div_pos halpha0 hepsilon0
  have hratioLe : (alpha : ℝ) / (epsilon : ℝ) ≤ 1 / (epsilon : ℝ) := by
    exact (div_le_div_iff_of_pos_right hepsilon0).2 alpha.property.2
  have hlogMain : Real.log ((alpha : ℝ) / (epsilon : ℝ)) ≤
      Real.log (1 / (epsilon : ℝ)) := Real.log_le_log hratioPos hratioLe
  have hcompNonneg : 0 ≤ (1 - (alpha : ℝ)) / (1 - (epsilon : ℝ)) :=
    div_nonneg (sub_nonneg.mpr alpha.property.2) (sub_nonneg.mpr epsilon.property.2)
  have hcompLe : (1 - (alpha : ℝ)) / (1 - (epsilon : ℝ)) ≤ 1 := by
    rw [div_le_one (sub_pos.mpr hepsilon1)]
    linarith
  have hlogComp : Real.log ((1 - (alpha : ℝ)) / (1 - (epsilon : ℝ))) ≤ 0 :=
    Real.log_nonpos hcompNonneg hcompLe
  have hmain := mul_le_mul_of_nonneg_left hlogMain alpha.property.1
  have hcompCoeff : 0 ≤ 1 - (alpha : ℝ) := sub_nonneg.mpr alpha.property.2
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hcompCoeff hlogComp]

/-- Exact exponentially evacuated binary aperture at shifted scale `n + 1`. -/
def exponentialBinaryBaseline (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) : unitInterval :=
  ⟨Real.exp (-beta * ((n + 1 : ℕ) : ℝ)),
    (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hbeta.le) (by positivity))⟩

@[simp] theorem exponentialBinaryBaseline_coe
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    (exponentialBinaryBaseline beta hbeta n : ℝ) =
      Real.exp (-beta * ((n + 1 : ℕ) : ℝ)) := rfl

/-- Exact degree-`d` polynomial binary renewal at shifted scale `n + 1`. -/
def polynomialBinaryRenewal
    (a d : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 ≤ d) (n : ℕ) : unitInterval :=
  ⟨a * ((n + 1 : ℕ) : ℝ) ^ (-d),
    mul_nonneg ha0.le (Real.rpow_nonneg (by positivity) _),
    calc
      a * ((n + 1 : ℕ) : ℝ) ^ (-d) ≤ a * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos
            (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) (neg_nonpos.mpr hd0)) ha0.le
      _ ≤ 1 := by linarith⟩

@[simp] theorem polynomialBinaryRenewal_coe
    (a d : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 ≤ d) (n : ℕ) :
    (polynomialBinaryRenewal a d ha0 ha1 hd0 n : ℝ) =
      a * ((n + 1 : ℕ) : ℝ) ^ (-d) := rfl

theorem polynomialBinaryRenewal_pos
    (a d : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 ≤ d) (n : ℕ) :
    0 < (polynomialBinaryRenewal a d ha0 ha1 hd0 n : ℝ) := by
  simp only [polynomialBinaryRenewal_coe]
  exact mul_pos ha0 (Real.rpow_pos_of_pos (by positivity) _)

theorem polynomialBinaryRenewal_lt_one
    (a d : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 ≤ d) (n : ℕ) :
    (polynomialBinaryRenewal a d ha0 ha1 hd0 n : ℝ) < 1 := by
  simp only [polynomialBinaryRenewal_coe]
  calc
    a * ((n + 1 : ℕ) : ℝ) ^ (-d) ≤ a * 1 :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) (neg_nonpos.mpr hd0)) ha0.le
    _ < 1 := by simpa using ha1

theorem exponentialBinaryBaseline_pos
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    0 < (exponentialBinaryBaseline beta hbeta n : ℝ) := Real.exp_pos _

theorem exponentialBinaryBaseline_lt_one
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    (exponentialBinaryBaseline beta hbeta n : ℝ) < 1 := by
  simp only [exponentialBinaryBaseline_coe]
  exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hbeta) (by positivity))

/-- Every positive polynomial tail eventually dominates a strictly decaying exponential. -/
theorem eventually_exponentialBinaryBaseline_le_polynomialBinaryRenewal
    (a beta d : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hbeta : 0 < beta) (hd0 : 0 ≤ d) :
    ∀ᶠ n : ℕ in atTop,
      (exponentialBinaryBaseline beta hbeta n : ℝ) ≤
        (polynomialBinaryRenewal a d ha0 ha1 hd0 n : ℝ) := by
  have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hdecay : Tendsto
      ((fun x : ℝ => x ^ d * Real.exp (-beta * x)) ∘
        fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero d beta hbeta).comp hcast
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ((n + 1 : ℕ) : ℝ) ^ d * Real.exp (-beta * ((n + 1 : ℕ) : ℝ)) < a :=
    hdecay.eventually_lt_const ha0
  filter_upwards [hsmall] with n hn
  simp only [exponentialBinaryBaseline_coe, polynomialBinaryRenewal_coe]
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN : 0 < N := by positivity
  have hcancel : N ^ d * N ^ (-d) = 1 := by
    rw [← Real.rpow_add hN]
    simp
  calc
    Real.exp (-beta * N) = Real.exp (-beta * N) * 1 := by ring
    _ = Real.exp (-beta * N) * (N ^ d * N ^ (-d)) := by rw [hcancel]
    _ = (N ^ d * Real.exp (-beta * N)) * N ^ (-d) := by ring
    _ ≤ a * N ^ (-d) :=
      mul_le_mul_of_nonneg_right hn.le (Real.rpow_nonneg hN.le _)

/-- Above the quadratic wall, exact exponential/polynomial binary KL coordinates are summable. -/
theorem summable_binaryRenewalCost_exponential_polynomial
    (a beta d : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hbeta : 0 < beta) (hd : 2 < d) :
    Summable (fun n : ℕ =>
      binaryRenewalCost (exponentialBinaryBaseline beta hbeta n)
        (polynomialBinaryRenewal a d ha0 ha1 (by linarith) n)) := by
  have hd0 : 0 ≤ d := by linarith
  have hdom := eventually_exponentialBinaryBaseline_le_polynomialBinaryRenewal
    a beta d ha0 ha1 hbeta hd0
  have hupper : ∀ᶠ n : ℕ in atTop,
      binaryRenewalCost (exponentialBinaryBaseline beta hbeta n)
          (polynomialBinaryRenewal a d ha0 ha1 hd0 n) ≤
        a * beta * ((n + 1 : ℕ) : ℝ) ^ (1 - d) := by
    filter_upwards [hdom] with n hn
    have hbound := binaryRenewalCost_le_mul_log_inv
      (exponentialBinaryBaseline beta hbeta n)
      (polynomialBinaryRenewal a d ha0 ha1 hd0 n)
      (exponentialBinaryBaseline_pos beta hbeta n)
      (exponentialBinaryBaseline_lt_one beta hbeta n)
      (polynomialBinaryRenewal_pos a d ha0 ha1 hd0 n)
      (polynomialBinaryRenewal_lt_one a d ha0 ha1 hd0 n) hn
    apply hbound.trans_eq
    simp only [polynomialBinaryRenewal_coe, exponentialBinaryBaseline_coe]
    let N : ℝ := ((n + 1 : ℕ) : ℝ)
    have hN : 0 < N := by positivity
    have hpow : N ^ (-d) * N = N ^ (1 - d) := by
      calc
        N ^ (-d) * N = N ^ (-d) * N ^ (1 : ℝ) := by
          exact congrArg (N ^ (-d) * ·) (Real.rpow_one N).symm
        _ = N ^ (-d + 1) := (Real.rpow_add hN _ _).symm
        _ = N ^ (1 - d) := by ring_nf
    rw [one_div, Real.log_inv, Real.log_exp]
    rw [show -(-beta * N) = beta * N by ring]
    rw [show (a * N ^ (-d)) * (beta * N) = a * beta * (N ^ (-d) * N) by ring,
      hpow]
  have hsumBase : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (1 - d)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))
  have hsumMajor : Summable (fun n : ℕ =>
      a * beta * ((n + 1 : ℕ) : ℝ) ^ (1 - d)) :=
    hsumBase.mul_left (a * beta)
  apply hsumMajor.of_norm_bounded_eventually_nat
  filter_upwards [hupper] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact hn
  · exact binaryRenewalCost_nonneg
      (exponentialBinaryBaseline beta hbeta n)
      (polynomialBinaryRenewal a d ha0 ha1 hd0 n)
      (exponentialBinaryBaseline_pos beta hbeta n)
      (exponentialBinaryBaseline_lt_one beta hbeta n)

/-- Exact persistent current of the polynomial two-point renewal. -/
theorem polynomialBinaryRenewal_constantCurrent
    (K c d : ℝ) (hK : 0 < K) (hc : 0 < c) (hck : c < K) (hd : 2 < d) (n : ℕ) :
    (polynomialBinaryRenewal (c / K) d (div_pos hc hK)
        ((div_lt_one hK).mpr hck) (by linarith) n : ℝ) *
      (K * ((n + 1 : ℕ) : ℝ) ^ d) = c := by
  simp only [polynomialBinaryRenewal_coe]
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN : 0 < N := by positivity
  have hcancel : N ^ (-d) * N ^ d = 1 := by
    rw [← Real.rpow_add hN]
    simp
  calc
    (c / K * N ^ (-d)) * (K * N ^ d) = c * (N ^ (-d) * N ^ d) := by
      field_simp [hK.ne']
    _ = c := by rw [hcancel, mul_one]

/-- CRG sharpness model: exact two-point exponential baseline, polynomial renewal, constant current,
and finite total action for every real degree strictly above two. -/
theorem exponentialPolynomialBinaryRenewal_sharp
    (beta K c d : ℝ) (hbeta : 0 < beta) (hK : 0 < K) (hc : 0 < c)
    (hck : c < K) (hd : 2 < d) :
    let epsilon := exponentialBinaryBaseline beta hbeta
    let alpha := polynomialBinaryRenewal (c / K) d (div_pos hc hK)
      ((div_lt_one hK).mpr hck) (by linarith)
    (∀ n, (epsilon n : ℝ) = Real.exp (-beta * ((n + 1 : ℕ) : ℝ))) ∧
      (∀ n, (alpha n : ℝ) =
        (c / K) * ((n + 1 : ℕ) : ℝ) ^ (-d)) ∧
      (∀ n, (alpha n : ℝ) * (K * ((n + 1 : ℕ) : ℝ) ^ d) = c) ∧
      (∀ n, Ber(true, false, alpha n) ≪ Ber(true, false, epsilon n)) ∧
      (∀ n, binaryRenewalCost (epsilon n) (alpha n) =
        (klDiv Ber(true, false, alpha n) Ber(true, false, epsilon n)).toReal) ∧
      binaryRenewalAction epsilon alpha ≠ ⊤ := by
  dsimp only
  have ha0 : 0 < c / K := div_pos hc hK
  have ha1 : c / K < 1 := (div_lt_one hK).mpr hck
  have hd0 : 0 ≤ d := by linarith
  refine ⟨fun n => rfl, fun n => rfl, ?_, ?_, ?_, ?_⟩
  · intro n
    exact polynomialBinaryRenewal_constantCurrent K c d hK hc hck hd n
  · intro n
    exact bernoulli_ac _ _
      (polynomialBinaryRenewal_pos (c / K) d ha0 ha1 hd0 n)
      (polynomialBinaryRenewal_lt_one (c / K) d ha0 ha1 hd0 n)
      (exponentialBinaryBaseline_pos beta hbeta n)
      (exponentialBinaryBaseline_lt_one beta hbeta n)
  · intro n
    exact binaryRenewalCost_eq_klDiv _ _
      (exponentialBinaryBaseline_pos beta hbeta n)
      (exponentialBinaryBaseline_lt_one beta hbeta n)
      (polynomialBinaryRenewal_pos (c / K) d ha0 ha1 hd0 n)
      (polynomialBinaryRenewal_lt_one (c / K) d ha0 ha1 hd0 n)
  · rw [binaryRenewalAction]
    exact (summable_binaryRenewalCost_exponential_polynomial
      (c / K) beta d ha0 ha1 hbeta hd).tsum_ofReal_lt_top.ne

/-- The sharp two-point schedule enters a compact finite-action sublevel above degree two. -/
theorem exponentialPolynomialBinaryRenewal_enters_finiteActionSublevel
    (beta K c d : ℝ) (hbeta : 0 < beta) (hK : 0 < K) (hc : 0 < c)
    (hck : c < K) (hd : 2 < d) :
    let epsilon := exponentialBinaryBaseline beta hbeta
    let alpha := polynomialBinaryRenewal (c / K) d (div_pos hc hK)
      ((div_lt_one hK).mpr hck) (by linarith)
    let W := fun n : ℕ => K * ((n + 1 : ℕ) : ℝ) ^ d
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
      alpha ∈ binaryRenewalActionSublevel epsilon M ∩ persistentCurrentLocus W c := by
  dsimp only
  let epsilon := exponentialBinaryBaseline beta hbeta
  let alpha := polynomialBinaryRenewal (c / K) d (div_pos hc hK)
    ((div_lt_one hK).mpr hck) (by linarith)
  let M := binaryRenewalAction epsilon alpha
  refine ⟨M, ?_, ?_, ?_⟩
  · exact (exponentialPolynomialBinaryRenewal_sharp beta K c d hbeta hK hc hck hd).2.2.2.2.2
  · change binaryRenewalAction epsilon alpha ≤ M
    exact le_rfl
  · intro n
    exact (polynomialBinaryRenewal_constantCurrent K c d hK hc hck hd n).ge

end

end GaloisForLFunctions.HTGeometry

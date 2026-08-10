import GaloisForLFunctions.RHTower.SquarefreeCoronaPrimeCurrentField
import GaloisForLFunctions.RHTower.SquarefreeFixedCurrentLocalization
import GaloisForLFunctions.RHTower.XiMassPrimeSquareBoundaryResidue
import GaloisForLFunctions.RHTower.MFreeLadder

/-!
# The corona codiagonal of the squarefree Euler clock

Summing the prime coordinates of the modular current is an algebraic operation with no bounded
extension to `ℓ²(Primes)`.  On `Re s > 1` the finite-support sum evaluates to the squarefree fixed
current

```text
∑_p (log p) p^{-s}/(1 + p^{-s}) = A(s) - 2 A(2s),   A = -ζ'/ζ,
```

because the alternating geometric expansion of each Euler factor reproduces the von Mangoldt
prime-power Laplace channel with the even prime powers counted with the opposite sign.  On the
normalized indicator of `N` prime coordinates the same sum has value `√N`, so no continuous linear
functional restricts to it: the scalarization, not any prime coordinate, is the singular operation.
-/

open Complex Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-! ## The prime-power Laplace family -/

/-- The prime-power Laplace family of the von Mangoldt current. -/
def primePowerFluxTerm (s : ℂ) (pk : Nat.Primes × ℕ) : ℂ :=
  (Real.log ((pk.1 : ℕ) : ℝ) : ℂ) * (((pk.1 : ℕ) : ℂ) ^ (-s)) ^ (pk.2 + 1)

theorem term_vonMangoldt_primePow_eq (s : ℂ) (pk : Nat.Primes × ℕ) :
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s
        ((pk.1 : ℕ) ^ (pk.2 + 1)) = primePowerFluxTerm s pk := by
  rw [LSeries.term_of_ne_zero (pow_ne_zero _ pk.1.prop.ne_zero),
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
    ArithmeticFunction.vonMangoldt_apply_prime pk.1.prop, natCast_pow_cpow,
    primePowerFluxTerm, Complex.cpow_neg, inv_pow, div_eq_mul_inv]

theorem summable_primePowerFluxTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (primePowerFluxTerm s) := by
  have hf : Summable (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have h := hf.comp_injective eulerPrimePowerNat_injective
  exact h.congr fun pk => term_vonMangoldt_primePow_eq s pk

theorem summable_norm_primePowerFluxTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun pk : Nat.Primes × ℕ => ‖primePowerFluxTerm s pk‖) :=
  summable_norm_iff.mpr (summable_primePowerFluxTerm hs)

/-- **The prime-power Laplace channel.**  On `Re s > 1` the double prime-power family sums to the
von Mangoldt current `A(s) = -ζ'(s)/ζ(s)`. -/
theorem tsum_primePowerFluxTerm {s : ℂ} (hs : 1 < s.re) :
    ∑' pk : Nat.Primes × ℕ, primePowerFluxTerm s pk = infinitePrimeFlux s := by
  have hf : Summable (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  calc
    (∑' pk : Nat.Primes × ℕ, primePowerFluxTerm s pk) =
        ∑' p : Nat.Primes, ∑' k : ℕ, primePowerFluxTerm s (p, k) :=
      (summable_primePowerFluxTerm hs).tsum_prod
    _ = ∑' p : Nat.Primes, ∑' k : ℕ,
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s
          ((p : ℕ) ^ (k + 1)) := by
      exact tsum_congr fun p => tsum_congr fun k => (term_vonMangoldt_primePow_eq s (p, k)).symm
    _ = ∑' n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n :=
      (tsum_eq_tsum_primes_of_support_subset_prime_powers hf
        (vonMangoldtLSeriesTerm_support_primePower s)).symm
    _ = infinitePrimeFlux s := (infinitePrimeFlux_eq_vonMangoldtLSeries hs).symm

/-! ## Alternating expansion of the modular current -/

/-- The alternating prime-power family of the modular current. -/
def coronaCurrentPowerTerm (s : ℂ) (pk : Nat.Primes × ℕ) : ℂ :=
  (-1 : ℂ) ^ pk.2 * primePowerFluxTerm s pk

theorem norm_coronaCurrentPowerTerm (s : ℂ) (pk : Nat.Primes × ℕ) :
    ‖coronaCurrentPowerTerm s pk‖ = ‖primePowerFluxTerm s pk‖ := by
  rw [coronaCurrentPowerTerm, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

theorem summable_coronaCurrentPowerTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (coronaCurrentPowerTerm s) := by
  refine Summable.of_norm ?_
  exact (summable_norm_primePowerFluxTerm hs).congr fun pk =>
    (norm_coronaCurrentPowerTerm s pk).symm

/-- Each Euler coordinate of the modular current is the alternating sum of its prime powers. -/
theorem hasSum_coronaPrimeCurrentCoeff {s : ℂ} (hs : 1 / 2 ≤ s.re) (p : Nat.Primes) :
    HasSum (fun k : ℕ => coronaCurrentPowerTerm s (p, k)) (coronaPrimeCurrentCoeff s p) := by
  have hnorm : ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 3 / 4 := norm_primeCpowNeg_le hs p
  have hgeo : HasSum (fun k : ℕ => (-(((p : ℕ) : ℂ) ^ (-s))) ^ k)
      (1 - (-(((p : ℕ) : ℂ) ^ (-s))))⁻¹ := by
    apply hasSum_geometric_of_norm_lt_one
    rw [norm_neg]
    linarith
  have hmul := hgeo.mul_left ((Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s))
  have hval : (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s) *
      (1 - (-(((p : ℕ) : ℂ) ^ (-s))))⁻¹ = coronaPrimeCurrentCoeff s p := by
    rw [coronaPrimeCurrentCoeff, div_eq_mul_inv]
    congr 2
    ring
  rw [hval] at hmul
  refine hmul.congr_fun fun k => ?_
  rw [coronaCurrentPowerTerm, primePowerFluxTerm, neg_pow, pow_succ]
  ring

theorem tsum_coronaPrimeCurrentCoeff_eq {s : ℂ} (hs : 1 < s.re) :
    ∑' p : Nat.Primes, coronaPrimeCurrentCoeff s p =
      ∑' pk : Nat.Primes × ℕ, coronaCurrentPowerTerm s pk := by
  rw [(summable_coronaCurrentPowerTerm hs).tsum_prod]
  exact tsum_congr fun p =>
    ((hasSum_coronaPrimeCurrentCoeff (by linarith) p).tsum_eq).symm

/-! ## The even prime-power correction -/

/-- The even-exponent part of the prime-power Laplace family. -/
def primePowerFluxEvenPart (s : ℂ) (pk : Nat.Primes × ℕ) : ℂ :=
  if Odd pk.2 then primePowerFluxTerm s pk else 0

theorem coronaCurrentPowerTerm_eq_sub (s : ℂ) (pk : Nat.Primes × ℕ) :
    coronaCurrentPowerTerm s pk =
      primePowerFluxTerm s pk - 2 * primePowerFluxEvenPart s pk := by
  rw [coronaCurrentPowerTerm, primePowerFluxEvenPart]
  by_cases h : Odd pk.2
  · rw [if_pos h, h.neg_one_pow]
    ring
  · rw [if_neg h, (Nat.not_odd_iff_even.mp h).neg_one_pow]
    ring

theorem summable_primePowerFluxEvenPart {s : ℂ} (hs : 1 < s.re) :
    Summable (primePowerFluxEvenPart s) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun pk => norm_nonneg _)
    (fun pk => ?_) (summable_norm_primePowerFluxTerm hs))
  rw [primePowerFluxEvenPart]
  by_cases h : Odd pk.2
  · rw [if_pos h]
  · rw [if_neg h, norm_zero]
    exact norm_nonneg _

private theorem primePowerFluxTerm_odd_eq (s : ℂ) (p : Nat.Primes) (j : ℕ) :
    primePowerFluxTerm s (p, 2 * j + 1) = primePowerFluxTerm (2 * s) (p, j) := by
  have hp : ((p : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr p.prop.ne_zero
  have hsq : ((p : ℕ) : ℂ) ^ (-(2 * s)) = (((p : ℕ) : ℂ) ^ (-s)) ^ 2 := by
    rw [show (-(2 * s)) = (-s) + (-s) by ring, Complex.cpow_add _ _ hp, sq]
  rw [primePowerFluxTerm, primePowerFluxTerm, hsq, ← pow_mul]
  congr 2

/-- **The even prime-power correction is the doubled current.**  Summing the odd-index part of the
alternating family recovers `A(2s)`. -/
theorem tsum_primePowerFluxEvenPart {s : ℂ} (hs : 1 < s.re) :
    ∑' pk : Nat.Primes × ℕ, primePowerFluxEvenPart s pk = infinitePrimeFlux (2 * s) := by
  have hs2 : 1 < (2 * s).re := by
    rw [Complex.mul_re]
    simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hinj : Function.Injective (fun pj : Nat.Primes × ℕ => (pj.1, 2 * pj.2 + 1)) := by
    rintro ⟨p, j⟩ ⟨q, k⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hpq, hjk⟩ := h
    have : j = k := by omega
    rw [hpq, this]
  have hsupport : Function.support (primePowerFluxEvenPart s) ⊆
      Set.range (fun pj : Nat.Primes × ℕ => (pj.1, 2 * pj.2 + 1)) := by
    intro pk hpk
    rw [Function.mem_support, primePowerFluxEvenPart] at hpk
    by_cases h : Odd pk.2
    · obtain ⟨j, hj⟩ := h
      exact ⟨(pk.1, j), by simp [hj, two_mul, Prod.ext_iff]⟩
    · exact absurd (by rw [if_neg h]) hpk
  calc
    (∑' pk : Nat.Primes × ℕ, primePowerFluxEvenPart s pk) =
        ∑' pj : Nat.Primes × ℕ, primePowerFluxEvenPart s (pj.1, 2 * pj.2 + 1) :=
      (hinj.tsum_eq hsupport).symm
    _ = ∑' pj : Nat.Primes × ℕ, primePowerFluxTerm (2 * s) pj := by
      refine tsum_congr fun pj => ?_
      rw [primePowerFluxEvenPart, if_pos ⟨pj.2, by ring⟩]
      exact primePowerFluxTerm_odd_eq s pj.1 pj.2
    _ = infinitePrimeFlux (2 * s) := tsum_primePowerFluxTerm hs2

/-- **The corona codiagonal identity.**  On `Re s > 1` the algebraic sum of the prime current
coordinates is the squarefree fixed current `A(s) - 2 A(2s)`. -/
theorem tsum_coronaPrimeCurrentCoeff_eq_squarefreeFixedCurrent {s : ℂ} (hs : 1 < s.re) :
    ∑' p : Nat.Primes, coronaPrimeCurrentCoeff s p =
      GaloisForLFunctions.squarefreeFixedCurrent s := by
  rw [tsum_coronaPrimeCurrentCoeff_eq hs]
  rw [show coronaCurrentPowerTerm s =
      fun pk => primePowerFluxTerm s pk - 2 * primePowerFluxEvenPart s pk from
    funext (coronaCurrentPowerTerm_eq_sub s)]
  rw [Summable.tsum_sub (summable_primePowerFluxTerm hs)
    ((summable_primePowerFluxEvenPart hs).mul_left 2), tsum_mul_left,
    tsum_primePowerFluxTerm hs, tsum_primePowerFluxEvenPart hs]
  rw [GaloisForLFunctions.squarefreeFixedCurrent]

/-! ## Unboundedness of the codiagonal -/

/-- The normalized indicator of a finite set of prime coordinates. -/
def coronaIndicatorLp (T : Finset Nat.Primes) : lp (fun _ : Nat.Primes => ℂ) 2 :=
  ∑ p ∈ T, lp.single 2 p (((Real.sqrt (T.card : ℝ) : ℝ) : ℂ)⁻¹)

theorem coronaIndicatorLp_apply (T : Finset Nat.Primes) (q : Nat.Primes) :
    (coronaIndicatorLp T : Nat.Primes → ℂ) q =
      if q ∈ T then ((Real.sqrt (T.card : ℝ) : ℝ) : ℂ)⁻¹ else 0 :=
  lp_sum_single_apply T (fun _ => ((Real.sqrt (T.card : ℝ) : ℝ) : ℂ)⁻¹) q

theorem norm_coronaIndicatorLp {T : Finset Nat.Primes} (hT : T.Nonempty) :
    ‖coronaIndicatorLp T‖ = 1 := by
  have hcard : (0 : ℝ) < (T.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hT
  have hsqrt : 0 < Real.sqrt (T.card : ℝ) := Real.sqrt_pos.mpr hcard
  have hsq : ‖coronaIndicatorLp T‖ ^ 2 = 1 := by
    rw [HilbertSchmidt.lp_norm_sq_eq]
    rw [show (fun q : Nat.Primes => ‖(coronaIndicatorLp T : Nat.Primes → ℂ) q‖ ^ 2) =
        fun q : Nat.Primes => if q ∈ T then (Real.sqrt (T.card : ℝ))⁻¹ ^ 2 else 0 by
      funext q
      rw [coronaIndicatorLp_apply]
      by_cases hq : q ∈ T <;>
        simp [hq, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hsqrt]]
    rw [tsum_eq_sum (s := T) (fun q hq => by simp [hq])]
    rw [Finset.sum_ite_mem]
    rw [Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    rw [inv_pow, Real.sq_sqrt hcard.le]
    field_simp
  nlinarith [norm_nonneg (coronaIndicatorLp T), hsq]

theorem codiagonal_coronaIndicatorLp {T : Finset Nat.Primes} (hT : T.Nonempty) :
    ∑ _p ∈ T, ((Real.sqrt (T.card : ℝ) : ℝ) : ℂ)⁻¹ = ((Real.sqrt (T.card : ℝ) : ℝ) : ℂ) := by
  have hcard : (0 : ℝ) < (T.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hT
  have hsqrt : 0 < Real.sqrt (T.card : ℝ) := Real.sqrt_pos.mpr hcard
  have hne : ((Real.sqrt (T.card : ℝ) : ℝ) : ℂ) ≠ 0 := by
    simpa using hsqrt.ne'
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [show ((T.card : ℕ) : ℂ) = ((Real.sqrt (T.card : ℝ) : ℝ) : ℂ) ^ 2 by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hcard.le]
    norm_cast]
  field_simp

/-- **No-go: the corona codiagonal is unbounded.**  No continuous linear functional on
`ℓ²(Primes)` restricts to the algebraic sum of finitely many prime coordinates: on the normalized
indicator of `N` coordinates that sum has value `√N`. -/
theorem not_exists_bounded_coronaCodiagonal :
    ¬ ∃ ℓ : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] ℂ,
        ∀ (T : Finset Nat.Primes) (c : Nat.Primes → ℂ),
          ℓ (∑ p ∈ T, lp.single 2 p (c p)) = ∑ p ∈ T, c p := by
  rintro ⟨ℓ, hℓ⟩
  obtain ⟨T, hTcard⟩ := Infinite.exists_subset_card_eq Nat.Primes (⌊‖ℓ‖ ^ 2⌋₊ + 1)
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos, hTcard]
    omega
  have hlarge : ‖ℓ‖ ^ 2 < (T.card : ℝ) := by
    rw [hTcard]
    push_cast
    exact Nat.lt_floor_add_one (‖ℓ‖ ^ 2)
  have hvalue : ℓ (coronaIndicatorLp T) = ((Real.sqrt (T.card : ℝ) : ℝ) : ℂ) := by
    rw [coronaIndicatorLp, hℓ T (fun _ => ((Real.sqrt (T.card : ℝ) : ℝ) : ℂ)⁻¹)]
    exact codiagonal_coronaIndicatorLp hTne
  have hbound : ‖ℓ (coronaIndicatorLp T)‖ ≤ ‖ℓ‖ := by
    have := ℓ.le_opNorm (coronaIndicatorLp T)
    rwa [norm_coronaIndicatorLp hTne, mul_one] at this
  rw [hvalue, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at hbound
  have hsq : Real.sqrt (T.card : ℝ) ^ 2 = (T.card : ℝ) :=
    Real.sq_sqrt (by positivity)
  nlinarith [norm_nonneg ℓ, Real.sqrt_nonneg (T.card : ℝ)]

/-- **Corona localization of the squarefree divisor.**  Every prime coordinate of the modular
current is holomorphic on `Re s > 1/2`; the codiagonal that reassembles the squarefree fixed
current from those coordinates has no bounded extension to `ℓ²(Primes)`. -/
theorem coronaScalarizationLocalizesDivisor :
    (∀ p : Nat.Primes,
        DifferentiableOn ℂ (fun s : ℂ => coronaPrimeCurrentCoeff s p) {s : ℂ | 1 / 2 < s.re}) ∧
      (∀ s : ℂ, 1 < s.re →
        ∑' p : Nat.Primes, coronaPrimeCurrentCoeff s p =
          GaloisForLFunctions.squarefreeFixedCurrent s) ∧
      ¬ ∃ ℓ : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] ℂ,
          ∀ (T : Finset Nat.Primes) (c : Nat.Primes → ℂ),
            ℓ (∑ p ∈ T, lp.single 2 p (c p)) = ∑ p ∈ T, c p :=
  ⟨differentiableOn_coronaPrimeCurrentCoeff_halfPlane,
    fun _ hs => tsum_coronaPrimeCurrentCoeff_eq_squarefreeFixedCurrent hs,
    not_exists_bounded_coronaCodiagonal⟩

end RHTower

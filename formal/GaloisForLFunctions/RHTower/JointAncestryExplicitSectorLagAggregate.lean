import GaloisForLFunctions.RHTower.JointAncestryExplicitSectorTotalVariation
import GaloisForLFunctions.RHTower.WeilLagFunction

/-!
# The lag-weighted aggregate of explicit-formula sectors

A rational character of the prime torus is a finitely supported exponent vector
`n : Nat.Primes →₀ ℤ`; write `log u = Σ_p n_p⁺ log p` and `log v = Σ_p n_p⁻ log p` for the
logarithms of its numerator and denominator.  The explicit-formula sector of a strip point `s` has
coefficient `u^{-s} v^{-(1-s)}` at `n`.

Summing the sectors of all Xi zeros with the lag weights `1/(ρ(1-ρ))` gives the aggregate

`N(n) = Σ_ρ u^{-ρ} v^{-(1-ρ)} / (ρ(1-ρ)) = (uv)^{-1/2} · Φ(log v - log u)`,

where `Φ(L) = Σ_ρ e^{L(ρ-1/2)}/(ρ(1-ρ))` is the Weil lag function.  The factor `(uv)^{-1/2}` is the
character Gram coefficient of the critical prime-Poisson sector, so the aggregate kernel is the
critical-sector Gram multiplied entrywise by the lag kernel `Φ(log(v/u))`, and `Φ` has an exact
prime side for `L > 0`.

Under RH every zero's explicit-formula sector is its prime-Poisson sector and every lag weight is
the positive number `1/(1/4 + γ²)`; the aggregate quadratic form is then a positive combination of
squared `L²`-norms of trigonometric polynomials over prime-Poisson sectors, hence positive
semidefinite.  The converse — positivity of the aggregate excludes off-line zeros — is the JAS
receiver problem: by the depth and total-variation theorems an off-line sector is non-positive only
at unbounded prime depth and has infinite total variation, so the converse must use multi-prime
test vectors and the superselection of distinct zero heights.
-/

open Complex MeasureTheory
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Logarithm of the numerator of a rational character. -/
def jasLogPos (n : Nat.Primes →₀ ℤ) : ℝ := n.sum fun p k => (k.toNat : ℝ) * Real.log p

/-- Logarithm of the denominator of a rational character. -/
def jasLogNeg (n : Nat.Primes →₀ ℤ) : ℝ := n.sum fun p k => ((-k).toNat : ℝ) * Real.log p

/-- Local explicit-formula coefficient at exponent `k`. -/
def jasHoloLocalCoeff (s : ℂ) (p : Nat.Primes) (k : ℤ) : ℂ :=
  if 0 ≤ k then jasHoloA s p ^ k.toNat else jasHoloB s p ^ (-k).toNat

/-- Coefficient of the explicit-formula sector of `s` at the rational character `n`. -/
def jasHoloCoeff (s : ℂ) (n : Nat.Primes →₀ ℤ) : ℂ := n.prod fun p k => jasHoloLocalCoeff s p k

theorem jasHoloLocalCoeff_eq_exp (s : ℂ) (p : Nat.Primes) (k : ℤ) :
    jasHoloLocalCoeff s p k =
      cexp (-s * ((k.toNat : ℝ) * Real.log p : ℝ) - (1 - s) * (((-k).toNat : ℝ) * Real.log p : ℝ)) := by
  unfold jasHoloLocalCoeff jasHoloA jasHoloB
  split
  · rename_i hk
    have : (-k).toNat = 0 := by omega
    rw [this, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  · rename_i hk
    have : k.toNat = 0 := by omega
    rw [this, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

/-- The explicit-formula coefficient is `u^{-s} v^{-(1-s)}` in exponential form. -/
theorem jasHoloCoeff_eq_exp (s : ℂ) (n : Nat.Primes →₀ ℤ) :
    jasHoloCoeff s n = cexp (-s * (jasLogPos n : ℂ) - (1 - s) * (jasLogNeg n : ℂ)) := by
  unfold jasHoloCoeff jasLogPos jasLogNeg Finsupp.prod Finsupp.sum
  simp_rw [jasHoloLocalCoeff_eq_exp]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- **Lag factorization of a single coefficient**: `u^{-s} v^{-(1-s)} = (uv)^{-1/2} (v/u)^{s-1/2}`. -/
theorem jasHoloCoeff_eq_gram_mul_lag (s : ℂ) (n : Nat.Primes →₀ ℤ) :
    jasHoloCoeff s n = (Real.exp (-(jasLogPos n + jasLogNeg n) / 2) : ℂ) *
      cexp (((jasLogNeg n - jasLogPos n : ℝ) : ℂ) * (s - 1 / 2)) := by
  rw [jasHoloCoeff_eq_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The lag-weighted aggregate of the explicit-formula sectors of all Xi zeros. -/
def jasLagAggregate (n : Nat.Primes →₀ ℤ) : ℂ :=
  ∑' q : XiZeroCopy, jasHoloCoeff (q.1 : ℂ) n / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))

theorem jasLagAggregate_term_eq (n : Nat.Primes →₀ ℤ) (q : XiZeroCopy) :
    jasHoloCoeff (q.1 : ℂ) n / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
      (Real.exp (-(jasLogPos n + jasLogNeg n) / 2) : ℂ) *
        (cexp (((jasLogNeg n - jasLogPos n : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2)) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
  rw [jasHoloCoeff_eq_gram_mul_lag, mul_div_assoc]

theorem summable_jasLagAggregate_term (n : Nat.Primes →₀ ℤ) :
    Summable (fun q : XiZeroCopy =>
      jasHoloCoeff (q.1 : ℂ) n / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
  simp_rw [jasLagAggregate_term_eq]
  exact (summable_weilLagTerm _).mul_left _

/-- **JAS–lag bridge.**  The aggregate coefficient at a rational character is the critical
Gram coefficient `(uv)^{-1/2}` times the Weil lag function at `log(v/u)`. -/
theorem jasLagAggregate_eq (n : Nat.Primes →₀ ℤ) :
    jasLagAggregate n = (Real.exp (-(jasLogPos n + jasLogNeg n) / 2) : ℂ) *
      weilLagFunction (jasLogNeg n - jasLogPos n) := by
  unfold jasLagAggregate weilLagFunction
  simp_rw [jasLagAggregate_term_eq]
  rw [tsum_mul_left]

/-- At the trivial character the aggregate is `Φ(0) = 2 + γ - log 4π`. -/
theorem jasLagAggregate_zero : jasLagAggregate 0 = poleSharpConstant := by
  rw [jasLagAggregate_eq]
  simp [jasLogPos, jasLogNeg, weilLagFunction_zero]

/-! ## Positivity under RH -/

theorem primePoissonParameterValue_eq_jasHoloA (s : ℂ) (p : Nat.Primes) :
    primePoissonParameterValue s.re (-s.im) p = jasHoloA s p := by
  unfold primePoissonParameterValue jasHoloA
  congr 1
  conv_rhs => rw [← Complex.re_add_im s]
  push_cast
  ring

/-- On the critical line the explicit-formula coefficients are the character moments of a
prime-Poisson sector. -/
theorem jasHoloCoeff_eq_integral_of_critical {s : ℂ} (hs : s.re = 1 / 2) (n : Nat.Primes →₀ ℤ) :
    jasHoloCoeff s n = ∫ x, infiniteTorusFourier n x
      ∂(primePoissonMeasure s.re (-s.im) (by rw [hs]; norm_num)) := by
  rw [integral_infiniteTorusFourier_primePoissonMeasure]
  unfold jasHoloCoeff
  refine Finsupp.prod_congr fun p _ => ?_
  rcases (n p) with m | m
  · simp [jasHoloLocalCoeff, circlePoissonFourierMoment, primePoissonParameterValue_eq_jasHoloA]
  · simp only [jasHoloLocalCoeff, circlePoissonFourierMoment, coe_primePoissonParameter,
      primePoissonParameterValue_eq_jasHoloA, jasHoloB_eq_conj_jasHoloA hs]
    rw [if_neg (by omega)]
    congr 1

/-- Gram positivity of character moments: `Σ c_i c̄_j ∫ χ_{n_i - n_j} dμ = ∫ |Σ c_i χ_{n_i}|²`. -/
theorem gram_infiniteTorusFourier_nonneg {I : Type*} [Countable I]
    (μ : Measure (I → UnitAddCircle)) [IsFiniteMeasure μ] {ι : Type*} (t : Finset ι)
    (c : ι → ℂ) (n : ι → I →₀ ℤ) :
    (∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * ∫ x, infiniteTorusFourier (n i - n j) x ∂μ).im = 0 ∧
      0 ≤ (∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) *
        ∫ x, infiniteTorusFourier (n i - n j) x ∂μ).re := by
  have hint : ∀ m : I →₀ ℤ, Integrable (fun x => infiniteTorusFourier m x) μ :=
    integrable_infiniteTorusFourier μ
  have hpt : ∀ x, ∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * infiniteTorusFourier (n i - n j) x =
      ((‖∑ i ∈ t, c i * infiniteTorusFourier (n i) x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sub_eq_add_neg, infiniteTorusFourier_add, infiniteTorusFourier_neg, map_mul]
    ring
  have hsum : ∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * ∫ x, infiniteTorusFourier (n i - n j) x ∂μ =
      ∫ x, ((‖∑ i ∈ t, c i * infiniteTorusFourier (n i) x‖ ^ 2 : ℝ) : ℂ) ∂μ := by
    simp_rw [← hpt]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]
      · intro j _; exact (hint _).const_mul _
    · intro i _
      exact integrable_finsetSum _ fun j _ => (hint _).const_mul _
  rw [hsum, integral_complex_ofReal]
  exact ⟨Complex.ofReal_im _, by
    rw [Complex.ofReal_re]; exact integral_nonneg fun x => by positivity⟩

theorem inv_mul_one_sub_eq_of_critical {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    1 / (ρ * (1 - ρ)) = ((1 / (1 / 4 + ρ.im ^ 2) : ℝ) : ℂ) := by
  have h : ρ * (1 - ρ) = ((1 / 4 + ρ.im ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [← Complex.re_add_im ρ, hρ]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [h]
  push_cast
  ring

/-- **RH ⟹ the aggregate kernel is positive semidefinite** on every finite family of rational
characters. -/
theorem jasLagAggregate_posSemidef_of_riemannHypothesis (hRH : RiemannHypothesis) {ι : Type*}
    (t : Finset ι) (c : ι → ℂ) (n : ι → Nat.Primes →₀ ℤ) :
    (∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * jasLagAggregate (n i - n j)).im = 0 ∧
      0 ≤ (∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * jasLagAggregate (n i - n j)).re := by
  set term : XiZeroCopy → ℂ := fun q => ∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) *
    (jasHoloCoeff (q.1 : ℂ) (n i - n j) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) with hterm
  have hswap : ∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * jasLagAggregate (n i - n j) =
      ∑' q, term q := by
    rw [hterm, Summable.tsum_finsetSum (fun i _ => summable_sum fun j _ =>
      (summable_jasLagAggregate_term _).mul_left _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum (fun j _ => (summable_jasLagAggregate_term _).mul_left _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [jasLagAggregate, tsum_mul_left]
  have hsummable : Summable term := by
    rw [hterm]
    exact summable_sum fun i _ =>
      summable_sum fun j _ => (summable_jasLagAggregate_term _).mul_left _
  have hq : ∀ q : XiZeroCopy, (term q).im = 0 ∧ 0 ≤ (term q).re := by
    intro q
    have hcrit : ((q.1 : ℂ)).re = 1 / 2 := xi_divisor_support_re_eq_half_of_rh hRH q.1
    have hpos : 0 < ((q.1 : ℂ)).re := by rw [hcrit]; norm_num
    set w : ℝ := 1 / (1 / 4 + ((q.1 : ℂ)).im ^ 2) with hw
    have hw0 : 0 ≤ w := by rw [hw]; positivity
    have hsplit : term q = (w : ℂ) * ∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) *
        ∫ x, infiniteTorusFourier (n i - n j) x
          ∂(primePoissonMeasure ((q.1 : ℂ)).re (-((q.1 : ℂ)).im) hpos) := by
      rw [hterm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← jasHoloCoeff_eq_integral_of_critical hcrit, div_eq_mul_one_div _ ((q.1 : ℂ) * _),
        inv_mul_one_sub_eq_of_critical hcrit, ← hw]
      ring
    have hgram := gram_infiniteTorusFourier_nonneg
      (primePoissonMeasure ((q.1 : ℂ)).re (-((q.1 : ℂ)).im) hpos) t c n
    rw [hsplit, Complex.re_ofReal_mul, Complex.im_ofReal_mul, hgram.1, mul_zero]
    exact ⟨rfl, mul_nonneg hw0 hgram.2⟩
  rw [hswap]
  refine ⟨?_, ?_⟩
  · rw [Complex.im_tsum hsummable]
    simp [fun q => (hq q).1]
  · rw [Complex.re_tsum hsummable]
    exact tsum_nonneg fun q => (hq q).2

end

end RHTower

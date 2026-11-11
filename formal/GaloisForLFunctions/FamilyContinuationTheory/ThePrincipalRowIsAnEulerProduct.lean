import GaloisForLFunctions.FamilyContinuationTheory.TheLocalFactorOfThePoissonSeriesIsExplicit
import GaloisForLFunctions.FamilyContinuationTheory.TheSeriesOfAMultiplicativeFunctionIsItsEulerProduct
import GaloisForLFunctions.FamilyContinuationTheory.TheCorrectionOfThePrincipalRowIsAConvergentEulerProduct

/-!
# The principal row is an Euler product

The row `u = 1` of the Poisson series of the cubic-theta probe has, at a primary prime `π ∤ 6` with
`N(π) = Q`, `κ = ᾱ η_π`, `X = Q^{−x}`, `Y = Q^{−w}`, `V = Q^{−6z}`, `R = κ⁶ Q⁴ X⁶ V`, the local sum

`P = (1 − V)⁻¹ + Y (1 − Y)⁻¹ + (1 − R)⁻¹ (R (1 − Q⁻¹)(1 − V)⁻¹ + Y R − η_π X
      − η_π (Q − 1) X Y V (1 − V)⁻¹)`   (`principalSum`, `hasSum_localTerm_one`),

the specialization `j = 0`, `ρ = 1` of the complete local identity. Its correction
`H = P (1 − V)(1 − Y)/(1 − η_π X)` (`principalH`) is, at the double residue `w = 1`, `z = 1/6`,
the local factor `h(s) = (1 − q²)(1 − q (R − D)/(1 − D))/(1 − R)` of the correction of the target
(`principalH_residue`), with the phase `A = κ⁶ = ᾱ⁶ η_π⁶`.

On `Re x ≥ 3`, `Re w ≥ 3`, `Re z ≥ 2` the excess mass of the local series is at most `8 N(π)^{−2}`
(`tsum_norm_localTerm_one_sub_one_le`); the general Euler product then makes the principal row
the product of the local sums over the good primes.
-/

noncomputable section

open scoped BigOperators Classical ComplexConjugate

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-- The local sum of the principal row. -/
def principalSum (Q κ ηp X Y V : ℂ) : ℂ :=
  (1 - V)⁻¹ + Y * (1 - Y)⁻¹ + (1 - κ ^ 6 * Q ^ 4 * X ^ 6 * V)⁻¹ *
    (κ ^ 6 * Q ^ 4 * X ^ 6 * V * (1 - Q⁻¹) * (1 - V)⁻¹ + Y * (κ ^ 6 * Q ^ 4 * X ^ 6 * V) -
      ηp * X - ηp * (Q - 1) * X * Y * V * (1 - V)⁻¹)

/-- The local correction of the principal row: the local sum with the Euler factors of
`ζ(6z) ζ(w)/L(x, η)` removed. -/
def principalH (Q κ ηp X Y V : ℂ) : ℂ :=
  principalSum Q κ ηp X Y V * (1 - V) * (1 - Y) / (1 - ηp * X)

/-- **At the double residue the correction is the local factor of the target.** For `Q > 0`,
`H(Q^{−s}, Q⁻¹, Q⁻¹) = h(s)` with the phase `κ⁶`. -/
theorem principalH_residue {Q : ℝ} (hQ : 0 < Q) (κ ηp s : ℂ)
    (hD : 1 - ηp * (Q : ℂ) ^ (-s) ≠ 0) (hR : 1 - κ ^ 6 * (Q : ℂ) ^ (3 - 6 * s) ≠ 0)
    (hq : 1 - (Q : ℂ)⁻¹ ≠ 0) :
    principalH Q κ ηp ((Q : ℂ) ^ (-s)) (Q : ℂ)⁻¹ (Q : ℂ)⁻¹ =
      principalLocalFactor Q (κ ^ 6) ηp s := by
  have hQ0 : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  have hX6 : ((Q : ℂ) ^ (-s)) ^ 6 = (Q : ℂ) ^ (-(6 * s)) := by
    rw [← Complex.cpow_nat_mul]
    ring_nf
  have h36 : (Q : ℂ) ^ (3 - 6 * s) = (Q : ℂ) ^ 3 * (Q : ℂ) ^ (-(6 * s)) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hQ0, show ((3 : ℂ)) = ((3 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast]
  have hQ1 : (Q : ℂ) - 1 ≠ 0 := by
    intro h
    apply hq
    rw [show (Q : ℂ) = 1 by linear_combination h, inv_one, sub_self]
  unfold principalH principalSum principalLocalFactor
  rw [hX6]
  rw [h36] at hR ⊢
  have hRR : κ ^ 6 * (Q : ℂ) ^ 4 * (Q : ℂ) ^ (-(6 * s)) * (Q : ℂ)⁻¹ =
      κ ^ 6 * ((Q : ℂ) ^ 3 * (Q : ℂ) ^ (-(6 * s))) := by
    field_simp
  rw [hRR]
  generalize κ ^ 6 * ((Q : ℂ) ^ 3 * (Q : ℂ) ^ (-(6 * s))) = R at hR ⊢
  generalize (Q : ℂ) ^ (-s) = X at hD ⊢
  field_simp
  ring

section Prime

variable (π : O) [NeZero π] [hP : (Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
  (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)

theorem one_not_mem_span_prime : (1 : O) ∉ Ideal.span {π} := fun h =>
  (prime_of_isMaximal_span π).not_unit (isUnit_of_dvd_one (Ideal.mem_span_singleton.mp h))

omit [NeZero π] in
theorem sexticChar_mk_one :
    complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ 1) = 1 := by
  rw [map_one, MulChar.map_one]

include hlam h2 hprim in
/-- **The local sum of the principal row.** -/
theorem hasSum_localTerm_one (ηp X Y V : ℂ) (hV : ‖V‖ < 1) (hY : ‖Y‖ < 1)
    (hR : ‖primeR π ηp X V‖ < 1) :
    HasSum (localTerm π ηp X Y V 1 0) (principalSum (primeQ π) (primeKappa π ηp) ηp X Y V) := by
  have hρ := sexticChar_mk_one π hlam
  have h := hasSum_localTerm π hlam h2 hprim ηp X Y V (one_not_mem_span_prime π) (j := 0)
    (by norm_num) hV (by rwa [hρ, one_mul]) hR
  convert h using 1
  simp [Fin.sum_univ_two, baseSum]
  unfold principalSum primeR
  ring

include hlam h2 hprim in
/-- **The excess mass of the principal local series.** If `‖V‖, ‖Y‖, ‖X‖, ‖R‖` and
`‖Q − 1‖ ‖X‖ ‖Y‖` are at most `δ ≤ 1/4`, the norm series exceeds `1` by at most `8δ`. -/
theorem tsum_norm_localTerm_one_sub_one_le (ηp X Y V : ℂ) {δ : ℝ} (hδ : δ ≤ 1 / 4)
    (hV : ‖V‖ ≤ δ) (hY : ‖Y‖ ≤ δ) (hX : ‖X‖ ≤ δ) (hR : ‖primeR π ηp X V‖ ≤ δ)
    (hQXY : ‖primeQ π - 1‖ * ‖X‖ * ‖Y‖ ≤ δ) (hη : ‖ηp‖ ≤ 1)
    (hq : ‖1 - (primeQ π)⁻¹‖ ≤ 1) :
    ∑' d, ‖localTerm π ηp X Y V 1 0 d‖ - 1 ≤ 8 * δ := by
  have hρ := sexticChar_mk_one π hlam
  have hV1 : ‖V‖ < 1 := by linarith
  have hY1 : ‖Y‖ < 1 := by linarith
  have hR1 : ‖primeR π ηp X V‖ < 1 := by linarith
  rw [(hasSum_norm_localTerm π hlam h2 hprim ηp X Y V (one_not_mem_span_prime π) (j := 0)
    (by norm_num) hV1 (by rwa [hρ, one_mul]) hR1).tsum_eq,
    sum_tsum_norm_base_zero π hlam h2 hprim ηp X Y V (one_not_mem_span_prime π) hV1]
  simp only [hρ, one_mul, inv_one, mul_one, ↓reduceIte]
  set a := ‖V‖
  set b := ‖Y‖
  set r := ‖primeR π ηp X V‖
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hr0 : 0 ≤ r := norm_nonneg _
  have hδ0 : 0 ≤ δ := ha0.trans hV
  -- the four norm masses
  have m1 : ‖primeR π ηp X V * (1 - (primeQ π)⁻¹)‖ ≤ δ := by
    rw [norm_mul]
    calc r * ‖1 - (primeQ π)⁻¹‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hq hr0
      _ ≤ δ := by linarith
  have m2 : ‖Y * primeR π ηp X V‖ ≤ δ / 4 := by
    rw [norm_mul]
    calc b * r ≤ (1 / 4) * δ := mul_le_mul (by linarith) hR hr0 (by norm_num)
      _ = δ / 4 := by ring
  have m3 : ‖ηp * X‖ ≤ δ := by
    rw [norm_mul]
    calc ‖ηp‖ * ‖X‖ ≤ 1 * δ := mul_le_mul hη hX (norm_nonneg _) zero_le_one
      _ = δ := one_mul δ
  have m4 : ‖ηp * (primeQ π - 1) * X * Y‖ ≤ δ := by
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖ηp‖ * ‖primeQ π - 1‖ * ‖X‖ * ‖Y‖ = ‖ηp‖ * (‖primeQ π - 1‖ * ‖X‖ * ‖Y‖) := by ring
      _ ≤ 1 * δ := mul_le_mul hη hQXY (by positivity) zero_le_one
      _ = δ := one_mul δ
  -- the three geometric denominators
  have ia : (1 - a)⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have ib : (1 - b)⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have ir : (1 - r)⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have ia0 : 0 ≤ (1 - a)⁻¹ := inv_nonneg.mpr (by linarith)
  have ib0 : 0 ≤ (1 - b)⁻¹ := inv_nonneg.mpr (by linarith)
  have ir0 : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr (by linarith)
  have ha1 : (1 - a)⁻¹ - 1 = a * (1 - a)⁻¹ := by
    have h1a : 1 - a ≠ 0 := (show (0 : ℝ) < 1 - a by linarith).ne'
    field_simp
    ring
  have hinner : ‖primeR π ηp X V * (1 - (primeQ π)⁻¹)‖ * (1 - a)⁻¹ + ‖Y * primeR π ηp X V‖ +
      ‖ηp * X‖ + ‖ηp * (primeQ π - 1) * X * Y‖ * a * (1 - a)⁻¹ ≤ 3 * δ := by
    have t1 : ‖primeR π ηp X V * (1 - (primeQ π)⁻¹)‖ * (1 - a)⁻¹ ≤ δ * (4 / 3) :=
      mul_le_mul m1 ia ia0 hδ0
    have t4 : ‖ηp * (primeQ π - 1) * X * Y‖ * a * (1 - a)⁻¹ ≤ δ * (1 / 4) * (4 / 3) :=
      mul_le_mul (mul_le_mul m4 (by linarith) ha0 hδ0) ia ia0 (by positivity)
    linarith
  have hfirst : (1 - a)⁻¹ - 1 ≤ δ * (4 / 3) := by
    rw [ha1]
    exact mul_le_mul hV ia ia0 hδ0
  have hsecond : b * (1 - b)⁻¹ ≤ δ * (4 / 3) := mul_le_mul hY ib ib0 hδ0
  have hthird : (1 - r)⁻¹ * (‖primeR π ηp X V * (1 - (primeQ π)⁻¹)‖ * (1 - a)⁻¹ +
      ‖Y * primeR π ηp X V‖ + ‖ηp * X‖ + ‖ηp * (primeQ π - 1) * X * Y‖ * a * (1 - a)⁻¹) ≤
        4 / 3 * (3 * δ) :=
    mul_le_mul ir hinner (by positivity) (by norm_num)
  linarith

end Prime

/-! ### The good primes and their primary generators -/

open IsDedekindDomain HeckeLFunctions

/-- The primary generator of a prime not above `3` (and `1` above `3`). -/
def primeGen (v : HeightOneSpectrum O) : O :=
  if h : lambda ∉ v.asIdeal then primaryGenerator v.asIdeal h else 1

theorem primeGen_spec (v : HeightOneSpectrum O) (h : lambda ∉ v.asIdeal) :
    v.asIdeal = Ideal.span {primeGen v} ∧ lambda ^ 2 ∣ primeGen v - 1 := by
  unfold primeGen
  rw [dif_pos h]
  exact primaryGenerator_spec v.asIdeal h

instance (v : HeightOneSpectrum O) : NeZero (primeGen v) := by
  refine ⟨fun h0 => ?_⟩
  unfold primeGen at h0
  by_cases h : lambda ∉ v.asIdeal
  · rw [dif_pos h] at h0
    have hs := (primaryGenerator_spec v.asIdeal h).1
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hs
    exact v.ne_bot hs
  · rw [dif_neg h] at h0
    exact one_ne_zero h0

theorem isMaximal_span_primeGen (v : HeightOneSpectrum O) (h : lambda ∉ v.asIdeal) :
    (Ideal.span {primeGen v}).IsMaximal := by
  rw [← (primeGen_spec v h).1]
  exact v.isMaximal

/-- `‖(n : ℂ)^{−x}‖ ≤ n^{−a}` for `n ≥ 1` and `Re x ≥ a`. -/
theorem norm_natCast_cpow_neg_le {n : ℕ} (hn : 1 ≤ n) {x : ℂ} {a : ℝ} (hx : a ≤ x.re) :
    ‖(n : ℂ) ^ (-x)‖ ≤ (n : ℝ) ^ (-a) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

section Global

variable (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)

/-- The term of the principal row at a prime `v` and local exponents `d`. -/
def principalRowTerm (x w z : ℂ) (v : HeightOneSpectrum O) (d : Fin 2 × ℕ × ℕ × ℕ) : ℂ :=
  localTerm (primeGen v) (heckeValue 𝔪 η v.asIdeal) ((v.asIdeal.absNorm : ℂ) ^ (-x))
    ((v.asIdeal.absNorm : ℂ) ^ (-w)) ((v.asIdeal.absNorm : ℂ) ^ (-(6 * z))) 1 0 d

/-- The local terms of the principal row on the good primes. -/
def principalRowFun (S : Finset (HeightOneSpectrum O)) (x w z : ℂ)
    (v : {v : HeightOneSpectrum O // v ∉ S}) (d : Fin 2 × ℕ × ℕ × ℕ) : ℂ :=
  principalRowTerm 𝔪 η x w z v.1 d

/-- **The principal row of the Poisson series**: the multiplicative series over the exponent
vectors supported on the good primes. -/
def principalRow (S : Finset (HeightOneSpectrum O)) (x w z : ℂ) : ℂ :=
  ∑' g : {v : HeightOneSpectrum O // v ∉ S} →₀ (Fin 2 × ℕ × ℕ × ℕ),
    eulerTerm (principalRowFun 𝔪 η S x w z) g

/-- The local sum of the principal row at a good prime. -/
def principalRowLocal (x w z : ℂ) (v : HeightOneSpectrum O) : ℂ :=
  principalSum (primeQ (primeGen v)) (primeKappa (primeGen v) (heckeValue 𝔪 η v.asIdeal))
    (heckeValue 𝔪 η v.asIdeal) ((v.asIdeal.absNorm : ℂ) ^ (-x)) ((v.asIdeal.absNorm : ℂ) ^ (-w))
    ((v.asIdeal.absNorm : ℂ) ^ (-(6 * z)))

theorem primeQ_primeGen (v : HeightOneSpectrum O) (h : lambda ∉ v.asIdeal) :
    primeQ (primeGen v) = (v.asIdeal.absNorm : ℂ) := by
  rw [primeQ, ← (primeGen_spec v h).1]

theorem norm_primeKappa_le (π : O) [NeZero π] {ηp : ℂ} (hη : ‖ηp‖ ≤ 1) :
    ‖primeKappa π ηp‖ ≤ 1 := by
  have hN : (‖ringComplex π‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr (ringComplex_ne_zero π)
  rw [primeKappa, norm_mul, Complex.norm_conj, norm_div, primeAbs, Complex.norm_real, norm_norm,
    div_self hN, one_mul]
  exact hη

/-- **The local facts at a good prime** in the region `Re x ≥ 3`, `Re w ≥ 3`, `Re z ≥ 2`: the local
series of the principal row has sum `principalRowLocal`, and its excess mass is at most
`8 N(v)^{−2}`. -/
theorem principalRowTerm_facts {v : HeightOneSpectrum O} (hlam : lambda ∉ v.asIdeal)
    (h2 : (2 : O) ∉ v.asIdeal) {x w z : ℂ} (hx : 3 ≤ x.re) (hw : 3 ≤ w.re) (hz : 2 ≤ z.re) :
    HasSum (principalRowTerm 𝔪 η x w z v) (principalRowLocal 𝔪 η x w z v) ∧
      Summable (fun d => ‖principalRowTerm 𝔪 η x w z v d‖) ∧
        ∑' d, ‖principalRowTerm 𝔪 η x w z v d‖ - 1 ≤ 8 * (v.asIdeal.absNorm : ℝ) ^ (-(2 : ℝ)) := by
  obtain ⟨hspan, hprim⟩ := primeGen_spec v hlam
  haveI := isMaximal_span_primeGen v hlam
  have hlam' : lambda ∉ Ideal.span {primeGen v} := hspan ▸ hlam
  have h2' : (2 : O) ∉ Ideal.span {primeGen v} := hspan ▸ h2
  set n := v.asIdeal.absNorm
  have hn2 : 2 ≤ n := ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hpos : (0 : ℝ) < n := by linarith
  have hδ : (n : ℝ) ^ (-(2 : ℝ)) ≤ 1 / 4 := by
    have : (n : ℝ) ^ (-(2 : ℝ)) = ((n : ℝ) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hpos.le]
      norm_cast
    rw [this, inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  set δ : ℝ := (n : ℝ) ^ (-(2 : ℝ))
  have hpow : ∀ a : ℝ, 2 ≤ a → (n : ℝ) ^ (-a) ≤ δ := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  set ηp := heckeValue 𝔪 η v.asIdeal
  have hη : ‖ηp‖ ≤ 1 := norm_heckeValue_le_one 𝔪 η _
  set X := (n : ℂ) ^ (-x)
  set Y := (n : ℂ) ^ (-w)
  set V := (n : ℂ) ^ (-(6 * z))
  have hX3 : ‖X‖ ≤ (n : ℝ) ^ (-(3 : ℝ)) := norm_natCast_cpow_neg_le hn1 hx
  have hY3 : ‖Y‖ ≤ (n : ℝ) ^ (-(3 : ℝ)) := norm_natCast_cpow_neg_le hn1 hw
  have hV12 : ‖V‖ ≤ (n : ℝ) ^ (-(12 : ℝ)) :=
    norm_natCast_cpow_neg_le hn1 (by simp [Complex.mul_re]; linarith)
  have hX : ‖X‖ ≤ δ := hX3.trans (hpow 3 (by norm_num))
  have hY : ‖Y‖ ≤ δ := hY3.trans (hpow 3 (by norm_num))
  have hV : ‖V‖ ≤ δ := hV12.trans (hpow 12 (by norm_num))
  have hQ : primeQ (primeGen v) = (n : ℂ) := primeQ_primeGen v hlam
  have hκ : ‖primeKappa (primeGen v) ηp‖ ≤ 1 := norm_primeKappa_le _ hη
  have hR : ‖primeR (primeGen v) ηp X V‖ ≤ δ := by
    unfold primeR
    rw [hQ, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, Complex.norm_natCast]
    calc ‖primeKappa (primeGen v) ηp‖ ^ 6 * (n : ℝ) ^ 4 * ‖X‖ ^ 6 * ‖V‖ ≤
        1 * (n : ℝ) ^ 4 * ((n : ℝ) ^ (-(3 : ℝ))) ^ 6 * (n : ℝ) ^ (-(12 : ℝ)) := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hκ
      _ = (n : ℝ) ^ ((4 : ℝ) + (-(3 : ℝ)) * 6 + (-(12 : ℝ))) := by
          rw [Real.rpow_add hpos, Real.rpow_add hpos, Real.rpow_mul hpos.le, one_mul]
          norm_cast
      _ = (n : ℝ) ^ (-(26 : ℝ)) := by norm_num
      _ ≤ δ := hpow 26 (by norm_num)
  have hQXY : ‖primeQ (primeGen v) - 1‖ * ‖X‖ * ‖Y‖ ≤ δ := by
    rw [hQ]
    have hn1' : ‖(n : ℂ) - 1‖ ≤ (n : ℝ) := by
      rw [show (n : ℂ) - 1 = ((n - 1 : ℕ) : ℂ) by push_cast [Nat.cast_sub hn1]; ring,
        Complex.norm_natCast]
      exact_mod_cast Nat.sub_le n 1
    calc ‖(n : ℂ) - 1‖ * ‖X‖ * ‖Y‖ ≤ (n : ℝ) * (n : ℝ) ^ (-(3 : ℝ)) * (n : ℝ) ^ (-(3 : ℝ)) := by
          gcongr
      _ = (n : ℝ) ^ ((1 : ℝ) + (-(3 : ℝ)) + (-(3 : ℝ))) := by
          rw [Real.rpow_add hpos, Real.rpow_add hpos, Real.rpow_one]
      _ = (n : ℝ) ^ (-(5 : ℝ)) := by norm_num
      _ ≤ δ := hpow 5 (by norm_num)
  have hq : ‖1 - (primeQ (primeGen v))⁻¹‖ ≤ 1 := by
    rw [hQ, show (1 : ℂ) - (n : ℂ)⁻¹ = ((1 - (n : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    have : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (by linarith)
    have : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    constructor <;> linarith
  have hV1 : ‖V‖ < 1 := by linarith
  have hY1 : ‖Y‖ < 1 := by linarith
  have hR1 : ‖primeR (primeGen v) ηp X V‖ < 1 := by linarith
  refine ⟨hasSum_localTerm_one (primeGen v) hlam' h2' hprim ηp X Y V hV1 hY1 hR1, ?_, ?_⟩
  · exact (hasSum_norm_localTerm (primeGen v) hlam' h2' hprim ηp X Y V
      (one_not_mem_span_prime _) (j := 0) (by norm_num) hV1
      (by rwa [sexticChar_mk_one _ hlam', one_mul]) hR1).summable
  · exact tsum_norm_localTerm_one_sub_one_le (primeGen v) hlam' h2' hprim ηp X Y V hδ hV hY hX hR
      hQXY hη hq

/-- **The principal row is the product of its local sums** over the good primes, on
`Re x ≥ 3`, `Re w ≥ 3`, `Re z ≥ 2`. -/
theorem hasProd_principalRow (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, (lambda ∈ v.asIdeal ∨ (2 : O) ∈ v.asIdeal) → v ∈ S)
    {x w z : ℂ} (hx : 3 ≤ x.re) (hw : 3 ≤ w.re) (hz : 2 ≤ z.re) :
    HasProd (fun v : {v : HeightOneSpectrum O // v ∉ S} => principalRowLocal 𝔪 η x w z v.1)
      (principalRow 𝔪 η S x w z) := by
  have good : ∀ v : {v : HeightOneSpectrum O // v ∉ S},
      lambda ∉ v.1.asIdeal ∧ (2 : O) ∉ v.1.asIdeal :=
    fun v => ⟨fun h => v.2 (hS _ (Or.inl h)), fun h => v.2 (hS _ (Or.inr h))⟩
  have facts := fun v : {v : HeightOneSpectrum O // v ∉ S} =>
    principalRowTerm_facts 𝔪 η (good v).1 (good v).2 hx hw hz
  have hf0 : ∀ v : {v : HeightOneSpectrum O // v ∉ S}, principalRowFun 𝔪 η S x w z v 0 = 1 := by
    intro v
    obtain ⟨hspan, hprim⟩ := primeGen_spec v.1 (good v).1
    haveI := isMaximal_span_primeGen v.1 (good v).1
    have hlam' : lambda ∉ Ideal.span {primeGen v.1} := hspan ▸ (good v).1
    have h2' : (2 : O) ∉ Ideal.span {primeGen v.1} := hspan ▸ (good v).2
    show localTerm _ _ _ _ _ 1 0 (0, 0, 0, 0) = 1
    rw [localTerm_T0 (primeGen v.1) hlam' h2' hprim _ _ _ _ (one_not_mem_span_prime _) 0 0 0,
      if_pos rfl, pow_zero]
  have hs : ∀ v : {v : HeightOneSpectrum O // v ∉ S},
      Summable fun d => ‖principalRowFun 𝔪 η S x w z v d‖ := fun v => (facts v).2.1
  have hle : ∀ v : {v : HeightOneSpectrum O // v ∉ S},
      ∑' d, ‖principalRowFun 𝔪 η S x w z v d‖ - 1 ≤ 8 * (v.1.asIdeal.absNorm : ℝ) ^ (-(2 : ℝ)) :=
    fun v => (facts v).2.2
  have hmaj : Summable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
      8 * (v.1.asIdeal.absNorm : ℝ) ^ (-(2 : ℝ)) :=
    ((numberField_summable_finitePlace_absNorm_rpow (K := K) (σ := 2) (by norm_num)).subtype
      _).mul_left 8
  have hb : Summable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
      ∑' d, ‖principalRowFun 𝔪 η S x w z v d‖ - 1 :=
    Summable.of_nonneg_of_le
      (fun v => sub_nonneg.mpr (one_le_tsum_norm (principalRowFun 𝔪 η S x w z) hf0 hs v)) hle hmaj
  have h := hasProd_tsum_eulerTerm (principalRowFun 𝔪 η S x w z) hf0 hs hb
  have hloc : (fun v : {v : HeightOneSpectrum O // v ∉ S} =>
      ∑' d, principalRowFun 𝔪 η S x w z v d) =
        fun v => principalRowLocal 𝔪 η x w z v.1 := funext fun v => (facts v).1.tsum_eq
  rw [hloc] at h
  exact h

/-! ### The factorization of the principal row -/

/-- The partial Dedekind zeta function `ζ^S(s) = ∏_{v ∉ S} (1 − N(v)^{−s})⁻¹`. -/
def zetaS (S : Finset (HeightOneSpectrum O)) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum O // v ∉ S}, (1 - (v.1.asIdeal.absNorm : ℂ) ^ (-s))⁻¹

/-- The reciprocal of the partial Hecke `L`-function, `∏_{v ∉ S} (1 − η(v) N(v)^{−s})`. -/
def heckeInvS (S : Finset (HeightOneSpectrum O)) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum O // v ∉ S},
    (1 - heckeValue 𝔪 η v.1.asIdeal * (v.1.asIdeal.absNorm : ℂ) ^ (-s))

/-- The correction of the principal row, `∏_{v ∉ S} H_v(x, w, z)`. -/
def principalRowCorrection (S : Finset (HeightOneSpectrum O)) (x w z : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum O // v ∉ S},
    principalH (primeQ (primeGen v.1)) (primeKappa (primeGen v.1) (heckeValue 𝔪 η v.1.asIdeal))
      (heckeValue 𝔪 η v.1.asIdeal) ((v.1.asIdeal.absNorm : ℂ) ^ (-x))
      ((v.1.asIdeal.absNorm : ℂ) ^ (-w)) ((v.1.asIdeal.absNorm : ℂ) ^ (-(6 * z)))

/-- The local sum is the product of the three scalar Euler factors and the correction. -/
theorem principalSum_eq_mul (Q κ ηp X Y V : ℂ) (hV : 1 - V ≠ 0) (hY : 1 - Y ≠ 0)
    (hD : 1 - ηp * X ≠ 0) :
    principalSum Q κ ηp X Y V =
      (1 - V)⁻¹ * (1 - Y)⁻¹ * (1 - ηp * X) * principalH Q κ ηp X Y V := by
  unfold principalH
  field_simp

/-- A family `1 − a_v` with `Σ ‖a_v‖ < ∞` is multipliable, and so is its inverse when
`‖a_v‖ ≤ 1/2`. -/
theorem multipliable_one_sub {ι : Type*} {a : ι → ℂ} (ha : Summable fun i => ‖a i‖) :
    Multipliable fun i => 1 - a i := by
  simpa [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable
    (f := fun i => -a i) (by simpa using ha.of_norm.neg)

theorem multipliable_one_sub_inv {ι : Type*} {a : ι → ℂ} (ha : Summable fun i => ‖a i‖)
    (hhalf : ∀ i, ‖a i‖ ≤ 1 / 2) : Multipliable fun i => (1 - a i)⁻¹ := by
  have hne : ∀ i, 1 - a i ≠ 0 := fun i h => by
    have := hhalf i
    rw [show a i = 1 by linear_combination -h, norm_one] at this
    norm_num at this
  have hval : ∀ i, (1 - a i)⁻¹ = 1 + a i * (1 - a i)⁻¹ := fun i => by
    field_simp [hne i]
    ring
  have hbd : ∀ i, ‖a i * (1 - a i)⁻¹‖ ≤ 2 * ‖a i‖ := fun i => by
    rw [norm_mul, norm_inv]
    have hlow : 1 / 2 ≤ ‖1 - a i‖ := by
      have := norm_sub_norm_le (1 : ℂ) (a i)
      rw [norm_one] at this
      linarith [hhalf i]
    calc ‖a i‖ * ‖1 - a i‖⁻¹ ≤ ‖a i‖ * 2 := by
          gcongr
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
      _ = 2 * ‖a i‖ := by ring
  simp_rw [hval]
  exact Complex.multipliable_one_add_of_summable
    ((ha.mul_left 2).of_nonneg_of_le (fun i => norm_nonneg _) hbd).of_norm

/-- **The principal row factors** on `Re x ≥ 3`, `Re w ≥ 3`, `Re z ≥ 2`:
`F₁ = ζ^S(6z) ζ^S(w) L^S(x, η)⁻¹ ∏_{v ∉ S} H_v`. -/
theorem principalRow_eq (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, (lambda ∈ v.asIdeal ∨ (2 : O) ∈ v.asIdeal) → v ∈ S)
    {x w z : ℂ} (hx : 3 ≤ x.re) (hw : 3 ≤ w.re) (hz : 2 ≤ z.re) :
    principalRow 𝔪 η S x w z =
      zetaS S (6 * z) * zetaS S w * heckeInvS 𝔪 η S x * principalRowCorrection 𝔪 η S x w z := by
  -- the three scalar families and their summable majorants
  set n : {v : HeightOneSpectrum O // v ∉ S} → ℕ := fun v => v.1.asIdeal.absNorm
  have hn2 : ∀ v, 2 ≤ n v := fun v => ArtinMertens.two_le_absNorm_of_isPrime v.1.isPrime v.1.ne_bot
  have hmaj : ∀ {a : ℝ}, 1 < a → Summable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
      (n v : ℝ) ^ (-a) := fun ha =>
    (numberField_summable_finitePlace_absNorm_rpow (K := K) ha).subtype _
  have hsmall : ∀ (v : {v : HeightOneSpectrum O // v ∉ S}) {a : ℝ}, 1 ≤ a →
      (n v : ℝ) ^ (-a) ≤ 1 / 2 := fun v a ha => by
    have h2 : (2 : ℝ) ≤ n v := by exact_mod_cast hn2 v
    calc (n v : ℝ) ^ (-a) ≤ (n v : ℝ) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (n v : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hV : ∀ v, ‖(n v : ℂ) ^ (-(6 * z))‖ ≤ (n v : ℝ) ^ (-(12 : ℝ)) := fun v =>
    norm_natCast_cpow_neg_le (by linarith [hn2 v]) (by simp [Complex.mul_re]; linarith)
  have hY : ∀ v, ‖(n v : ℂ) ^ (-w)‖ ≤ (n v : ℝ) ^ (-(3 : ℝ)) := fun v =>
    norm_natCast_cpow_neg_le (by linarith [hn2 v]) hw
  have hD : ∀ v : {v : HeightOneSpectrum O // v ∉ S},
      ‖heckeValue 𝔪 η v.1.asIdeal * (n v : ℂ) ^ (-x)‖ ≤ (n v : ℝ) ^ (-(3 : ℝ)) := fun v => by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_heckeValue_le_one 𝔪 η _)).trans
      (norm_natCast_cpow_neg_le (by linarith [hn2 v]) hx)
  have sV : Summable fun v => ‖(n v : ℂ) ^ (-(6 * z))‖ :=
    (hmaj (by norm_num)).of_nonneg_of_le (fun _ => norm_nonneg _) hV
  have sY : Summable fun v => ‖(n v : ℂ) ^ (-w)‖ :=
    (hmaj (by norm_num)).of_nonneg_of_le (fun _ => norm_nonneg _) hY
  have sD : Summable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
      ‖heckeValue 𝔪 η v.1.asIdeal * (n v : ℂ) ^ (-x)‖ :=
    (hmaj (by norm_num)).of_nonneg_of_le (fun _ => norm_nonneg _) hD
  have mV := multipliable_one_sub_inv sV fun v => (hV v).trans (hsmall v (by norm_num))
  have mY := multipliable_one_sub_inv sY fun v => (hY v).trans (hsmall v (by norm_num))
  have mD := multipliable_one_sub sD
  have mVi := multipliable_one_sub sV
  have mYi := multipliable_one_sub sY
  have mDi := multipliable_one_sub_inv sD fun v => (hD v).trans (hsmall v (by norm_num))
  have hP := hasProd_principalRow 𝔪 η S hS hx hw hz
  -- pointwise factorization
  have hne : ∀ (v : {v : HeightOneSpectrum O // v ∉ S}) (a : ℂ), ‖a‖ ≤ 1 / 2 → 1 - a ≠ 0 :=
    fun v a ha h => by
      rw [show a = 1 by linear_combination -h, norm_one] at ha
      norm_num at ha
  have hpt : ∀ v : {v : HeightOneSpectrum O // v ∉ S}, principalRowLocal 𝔪 η x w z v.1 =
      (1 - (n v : ℂ) ^ (-(6 * z)))⁻¹ * (1 - (n v : ℂ) ^ (-w))⁻¹ *
        (1 - heckeValue 𝔪 η v.1.asIdeal * (n v : ℂ) ^ (-x)) *
          principalH (primeQ (primeGen v.1)) (primeKappa (primeGen v.1)
            (heckeValue 𝔪 η v.1.asIdeal)) (heckeValue 𝔪 η v.1.asIdeal) ((n v : ℂ) ^ (-x))
            ((n v : ℂ) ^ (-w)) ((n v : ℂ) ^ (-(6 * z))) := fun v =>
    principalSum_eq_mul _ _ _ _ _ _ (hne v _ ((hV v).trans (hsmall v (by norm_num))))
      (hne v _ ((hY v).trans (hsmall v (by norm_num))))
      (hne v _ ((hD v).trans (hsmall v (by norm_num))))
  -- the correction is multipliable: it is the local sum times three multipliable families
  have mH : Multipliable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
      principalH (primeQ (primeGen v.1)) (primeKappa (primeGen v.1)
        (heckeValue 𝔪 η v.1.asIdeal)) (heckeValue 𝔪 η v.1.asIdeal) ((n v : ℂ) ^ (-x))
        ((n v : ℂ) ^ (-w)) ((n v : ℂ) ^ (-(6 * z))) := by
    have hm := ((hP.multipliable.mul mVi).mul mYi).mul mDi
    refine hm.congr fun v => ?_
    rw [hpt v]
    have h1 := hne v _ ((hV v).trans (hsmall v (by norm_num)))
    have h2 := hne v _ ((hY v).trans (hsmall v (by norm_num)))
    have h3 := hne v _ ((hD v).trans (hsmall v (by norm_num)))
    field_simp
  rw [← hP.tprod_eq, tprod_congr hpt, Multipliable.tprod_mul ((mV.mul mY).mul mD) mH,
    Multipliable.tprod_mul (mV.mul mY) mD, Multipliable.tprod_mul mV mY]
  rfl

end Global

end GaloisForLFunctions.FamilyContinuationTheory

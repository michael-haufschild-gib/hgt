import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanQuadratic
import GaloisForLFunctions.RHTower.RegularizedDivisorHarmonicLimit
import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion

/-!
# Weighted first moment of Ramanujan primitives and von Mangoldt centering of the Gram

For `q > 1` the harmonic sums of Ramanujan sums satisfy
`∑_{n≤N} Re c_q(n)/n = ∑_{dm=q} μ(m) H(⌊N/d⌋) → −Λ(q)` (von Mangoldt function `Λ`), using
`H(⌊N/d⌋) − log N → γ − log d` and `∑_{dm=q} μ(m) log d = Λ(q)`. Summation by parts converts
this into the weighted first moment `∑_N Re C_q(N)/(N(N+1)) = −Λ(q)` of the primitive
`C_q(N) = ∑_{n≤N} c_q(n)`. Since `∑_{N≥1} 1/(N(N+1)) = 1`, recentering the primitives by their
Cesàro mean `−φ(q)/2` or by the weighted mean `−Λ(q)` gives exact rank-one corrections of the
Gram entries `G(p,q)`; in particular `G(p,q) = Λ(p)Λ(q) + Ĝ(p,q)`, where `Ĝ` is the Gram of
the `Λ`-centered primitives `Re C_q + Λ(q)`.

## Main results

- `pm_ramanujan_harmonic_eq_divisor`: `∑_{n≤N} Re c_q(n)/n = ∑_{dm=q} μ(m) H(⌊N/d⌋)`.
- `tendsto_pm_ramanujan_harmonic`: `∑_{n≤N} Re c_q(n)/n → −Λ(q)` for `q > 1`.
- `hasSum_pmRamanujanPrimitive_reciprocal`: `∑_N Re C_q(N)/(N(N+1)) = −Λ(q)` for `q > 1`.
- `pmRamanujanPrimitiveGram_eq_meanCentered`: `G(p,q) = G̃(p,q) + φ(p)Λ(q)/2 + φ(q)Λ(p)/2 − φ(p)φ(q)/4` with `G̃` the Gram of `Re C_q + φ(q)/2`.
- `hasSum_pmRamanujanEnergyCenteredPrimitive`: the `Λ`-centered primitive has weighted mean zero.
- `pmRamanujanPrimitiveGram_eq_energyCentered`: `G(p,q) = Λ(p)Λ(q) + Ĝ(p,q)`.

## Hypotheses

All results are unconditional; the limit and Gram statements assume `1 < p` and `1 < q`.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

/-- `∑_{n≤N} Re c_q(n)/n = ∑_{dm=q} μ(m) H(⌊N/d⌋)`, with `H` the harmonic numbers. -/
theorem pm_ramanujan_harmonic_eq_divisor (q N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (d4BMRamanujanNaturalCoefficient n q).re/(n : ℝ)) =
      ∑ x ∈ q.divisorsAntidiagonal, (moebius x.2 : ℝ)*(harmonic (N/x.1) : ℝ) := by
  have h := congrArg Complex.re (pm_ramanujan_weighted_sum
    (fun n => (((n : ℝ)⁻¹ : ℝ) : ℂ)) N q)
  have hr : (∑ n ∈ Finset.Icc 1 N, (d4BMRamanujanNaturalCoefficient n q).re/(n : ℝ)) =
      ∑ x ∈ q.divisorsAntidiagonal, (x.1 : ℝ)*(moebius x.2 : ℝ)*
        ∑ n ∈ Finset.Icc 1 N, if x.1 ∣ n then (n : ℝ)⁻¹ else 0 := by
    simpa only [Complex.re_sum, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      Complex.intCast_re, Complex.intCast_im, zero_mul, mul_zero, add_zero, sub_zero,
      apply_ite, Complex.zero_re, div_eq_mul_inv, mul_comm] using h
  rw [hr]
  apply Finset.sum_congr rfl
  intro x hx
  have hd := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
  rw [← Finset.sum_filter, RegularizedDivisorHarmonic.sum_inv_multiples_eq_harmonic N x.1 hd]
  have hdR : (x.1 : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

/-- `∑_{dm=q} μ(m) log d = Λ(q)`. -/
theorem pm_log_mobius_antidiagonal (q : ℕ) :
    (∑ x ∈ q.divisorsAntidiagonal, (moebius x.2 : ℝ)*Real.log x.1) = vonMangoldt q := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f q)
    ArithmeticFunction.log_mul_moebius_eq_vonMangoldt
  simpa only [ArithmeticFunction.mul_apply, ArithmeticFunction.log_apply,
    ArithmeticFunction.intCoe_apply, mul_comm] using h

/-- For `q > 1`, `∑_{n≤N} Re c_q(n)/n → −Λ(q)` as `N → ∞`. -/
theorem tendsto_pm_ramanujan_harmonic {q : ℕ} (hq : 1 < q) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      (d4BMRamanujanNaturalCoefficient n q).re/(n : ℝ)) atTop (𝓝 (-vonMangoldt q)) := by
  have hz : (∑ x ∈ q.divisorsAntidiagonal, (moebius x.2 : ℝ)) = 0 := by
    have h := congrArg Complex.re (pm_mobius_antidiagonal_sum q)
    simpa [ne_of_gt hq] using h
  have he (N : ℕ) :
      (∑ n ∈ Finset.Icc 1 N, (d4BMRamanujanNaturalCoefficient n q).re/(n : ℝ)) =
        ∑ x ∈ q.divisorsAntidiagonal,
          (moebius x.2 : ℝ)*((harmonic (N/x.1) : ℝ)-Real.log N) := by
    rw [pm_ramanujan_harmonic_eq_divisor]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hz, zero_mul, sub_zero]
  simp_rw [he]
  have hlim := tendsto_finsetSum q.divisorsAntidiagonal (fun x hx =>
    (GaloisForLFunctions.HTGeometry.tendsto_harmonic_natDiv_sub_log
      (Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx))).const_mul
        (moebius x.2 : ℝ))
  have hv : (∑ x ∈ q.divisorsAntidiagonal,
      (moebius x.2 : ℝ)*(Real.eulerMascheroniConstant-Real.log x.1)) = -vonMangoldt q := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hz, zero_mul,
      pm_log_mobius_antidiagonal, zero_sub]
  simpa only [hv] using hlim

/-- Summation by parts: `∑_{n≤N} Re C_q(n)/(n(n+1)) = ∑_{n≤N} Re c_q(n)/n − Re C_q(N)/(N+1)`. -/
theorem pmRamanujanPrimitive_reciprocal_partial (q N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (pmRamanujanPrimitive q n).re/((n : ℝ)*((n : ℝ)+1))) =
      (∑ n ∈ Finset.Icc 1 N, (d4BMRamanujanNaturalCoefficient n q).re/(n : ℝ))-
        (pmRamanujanPrimitive q N).re/((N : ℝ)+1) := by
  induction N with
  | zero => simp [pmRamanujanPrimitive]
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih,
      pmRamanujanPrimitive_succ]
    simp only [Complex.add_re, Nat.cast_add, Nat.cast_one]
    have hN1 : (N : ℝ)+1 ≠ 0 := by positivity
    have hN2 : (N : ℝ)+1+1 ≠ 0 := by positivity
    field_simp
    ring

/-- For `q > 1`, `Re C_q(N)/(N+1) → 0`. -/
theorem tendsto_pmRamanujanPrimitive_div_succ {q : ℕ} (hq : 1 < q) :
    Tendsto (fun N : ℕ => (pmRamanujanPrimitive q N).re/((N : ℝ)+1)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N => ?_)
    (show Tendsto (fun N : ℕ => pmRamanujanPrimitiveBound q/((N : ℝ)+1)) atTop (𝓝 0) from
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ)<(N : ℝ)+1)]
  exact div_le_div_of_nonneg_right
    ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hq N)) (by positivity)

/-- For `q > 1`, `∑_N Re C_q(N)/(N(N+1))` converges absolutely. -/
theorem summable_pmRamanujanPrimitive_reciprocal {q : ℕ} (hq : 1 < q) :
    Summable (fun N : ℕ => (pmRamanujanPrimitive q N).re/((N : ℝ)*((N : ℝ)+1))) := by
  apply (summable_nat_add_iff 1).mp
  have hs := (GaloisForLFunctions.hasSum_one_div_shift_mul_succ (by norm_num : (0 : ℝ)<1)).summable
  apply Summable.of_norm_bounded (hs.mul_left (pmRamanujanPrimitiveBound q))
  intro n
  have hB := (Complex.abs_re_le_norm (pmRamanujanPrimitive q (n+1))).trans
    (norm_pmRamanujanPrimitive_le hq (n+1))
  simp only [Real.norm_eq_abs, abs_div, Nat.cast_add, Nat.cast_one]
  rw [abs_of_nonneg (by positivity : 0 ≤ ((n : ℝ)+1)*((n : ℝ)+1+1))]
  calc
    _ ≤ pmRamanujanPrimitiveBound q/(((n : ℝ)+1)*((n : ℝ)+1+1)) := by gcongr
    _ = _ := by ring

/-- For `q > 1`, the weighted first moment is `∑_N Re C_q(N)/(N(N+1)) = −Λ(q)`. -/
theorem hasSum_pmRamanujanPrimitive_reciprocal {q : ℕ} (hq : 1 < q) :
    HasSum (fun N : ℕ => (pmRamanujanPrimitive q N).re/((N : ℝ)*((N : ℝ)+1)))
      (-vonMangoldt q) := by
  have hlim : Tendsto (fun T : ℕ => ∑ n ∈ Finset.Icc 1 T,
      (pmRamanujanPrimitive q n).re/((n : ℝ)*((n : ℝ)+1))) atTop (𝓝 (-vonMangoldt q)) := by
    simp_rw [pmRamanujanPrimitive_reciprocal_partial]
    simpa only [sub_zero] using (tendsto_pm_ramanujan_harmonic hq).sub
      (tendsto_pmRamanujanPrimitive_div_succ hq)
  have hs := (summable_pmRamanujanPrimitive_reciprocal hq).hasSum
  have ht := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, div_zero, sub_zero] at ht
  have he : (∑' N : ℕ, (pmRamanujanPrimitive q N).re/((N : ℝ)*((N : ℝ)+1))) =
      -vonMangoldt q := tendsto_nhds_unique ht.tendsto_sum_nat
        (by simpa only [sum_Icc_eq_sum_range_succ] using hlim)
  simpa only [he] using hs

/-- Telescoping: `∑_{N≥1} 1/(N(N+1)) = 1` (the `N = 0` term is `0`). -/
theorem hasSum_pm_reciprocal_weight :
    HasSum (fun N : ℕ => 1/((N : ℝ)*((N : ℝ)+1))) 1 := by
  have h := GaloisForLFunctions.hasSum_one_div_shift_mul_succ (by norm_num : (0 : ℝ)<1)
  have ht : HasSum (fun N : ℕ => 1/(((N+1 : ℕ) : ℝ)*(((N+1 : ℕ) : ℝ)+1))) 1 := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div_one, add_comm] using h
  simpa only [Finset.sum_range_one, Nat.cast_zero, zero_mul, div_zero, add_zero] using
    (hasSum_nat_add_iff (f := fun N : ℕ => 1/((N : ℝ)*((N : ℝ)+1))) 1).mp ht

/-- The Cesàro-centered primitive `Re C_q(N) + φ(q)/2`. -/
def pmRamanujanMeanCenteredPrimitive (q N : ℕ) : ℝ :=
  (pmRamanujanPrimitive q N).re+(q.totient : ℝ)/2

/-- The Gram entry of the Cesàro-centered primitives with weight `1/(N(N+1))`. -/
def pmRamanujanMeanCenteredGram (p q : ℕ) : ℝ :=
  ∑' N : ℕ, pmRamanujanMeanCenteredPrimitive p N*pmRamanujanMeanCenteredPrimitive q N/
    ((N : ℝ)*((N : ℝ)+1))

/-- For `p, q > 1`, the Cesàro-centered Gram series sums to
`G(p,q) − φ(p)Λ(q)/2 − φ(q)Λ(p)/2 + φ(p)φ(q)/4`. -/
theorem hasSum_pmRamanujanMeanCenteredGram {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    HasSum (fun N : ℕ =>
      pmRamanujanMeanCenteredPrimitive p N*pmRamanujanMeanCenteredPrimitive q N/
        ((N : ℝ)*((N : ℝ)+1)))
      (pmRamanujanPrimitiveGram p q+(p.totient : ℝ)/2*(-vonMangoldt q)+
        (q.totient : ℝ)/2*(-vonMangoldt p)+(p.totient : ℝ)/2*((q.totient : ℝ)/2)) := by
  have h := (((summable_pmRamanujanPrimitiveGramTerm hp hq).hasSum.add
    ((hasSum_pmRamanujanPrimitive_reciprocal hq).mul_left ((p.totient : ℝ)/2))).add
      ((hasSum_pmRamanujanPrimitive_reciprocal hp).mul_left ((q.totient : ℝ)/2))).add
        (hasSum_pm_reciprocal_weight.mul_left ((p.totient : ℝ)/2*((q.totient : ℝ)/2)))
  simp only [mul_one] at h
  apply h.congr_fun
  intro N
  dsimp only [pmRamanujanMeanCenteredPrimitive, pmRamanujanPrimitiveGramTerm]
  ring

/-- For `p, q > 1`, `G(p,q) = G̃(p,q) + φ(p)Λ(q)/2 + φ(q)Λ(p)/2 − φ(p)φ(q)/4`. -/
theorem pmRamanujanPrimitiveGram_eq_meanCentered {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    pmRamanujanPrimitiveGram p q = pmRamanujanMeanCenteredGram p q+
      (p.totient : ℝ)*vonMangoldt q/2+(q.totient : ℝ)*vonMangoldt p/2-
        (p.totient : ℝ)*(q.totient : ℝ)/4 := by
  have h := (hasSum_pmRamanujanMeanCenteredGram hp hq).tsum_eq
  change pmRamanujanMeanCenteredGram p q = _ at h
  linear_combination -h

/-- The `Λ`-centered primitive `Re C_q(N) + Λ(q)`. -/
def pmRamanujanEnergyCenteredPrimitive (q N : ℕ) : ℝ :=
  (pmRamanujanPrimitive q N).re+vonMangoldt q

/-- The Gram entry `Ĝ(p,q)` of the `Λ`-centered primitives with weight `1/(N(N+1))`. -/
def pmRamanujanEnergyCenteredGram (p q : ℕ) : ℝ :=
  ∑' N : ℕ, pmRamanujanEnergyCenteredPrimitive p N*pmRamanujanEnergyCenteredPrimitive q N/
    ((N : ℝ)*((N : ℝ)+1))

/-- For `q > 1`, the `Λ`-centered primitive has weighted mean zero:
`∑_N (Re C_q(N) + Λ(q))/(N(N+1)) = 0`. -/
theorem hasSum_pmRamanujanEnergyCenteredPrimitive {q : ℕ} (hq : 1 < q) :
    HasSum (fun N : ℕ => pmRamanujanEnergyCenteredPrimitive q N/
      ((N : ℝ)*((N : ℝ)+1))) 0 := by
  have h := (hasSum_pmRamanujanPrimitive_reciprocal hq).add
    (hasSum_pm_reciprocal_weight.mul_left (vonMangoldt q))
  simp only [mul_one, neg_add_cancel] at h
  apply h.congr_fun
  intro N
  unfold pmRamanujanEnergyCenteredPrimitive
  ring

/-- For `p, q > 1`, the `Λ`-centered Gram series sums to `G(p,q) − Λ(p)Λ(q)`. -/
theorem hasSum_pmRamanujanEnergyCenteredGram {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    HasSum (fun N : ℕ =>
      pmRamanujanEnergyCenteredPrimitive p N*pmRamanujanEnergyCenteredPrimitive q N/
        ((N : ℝ)*((N : ℝ)+1)))
      (pmRamanujanPrimitiveGram p q-vonMangoldt p*vonMangoldt q) := by
  have h := (((summable_pmRamanujanPrimitiveGramTerm hp hq).hasSum.add
    ((hasSum_pmRamanujanPrimitive_reciprocal hq).mul_left (vonMangoldt p))).add
      ((hasSum_pmRamanujanPrimitive_reciprocal hp).mul_left (vonMangoldt q))).add
        (hasSum_pm_reciprocal_weight.mul_left (vonMangoldt p*vonMangoldt q))
  have he : pmRamanujanPrimitiveGram p q+vonMangoldt p*(-vonMangoldt q)+
      vonMangoldt q*(-vonMangoldt p)+(vonMangoldt p*vonMangoldt q)*1 =
        pmRamanujanPrimitiveGram p q-vonMangoldt p*vonMangoldt q := by ring
  change HasSum _ (pmRamanujanPrimitiveGram p q+vonMangoldt p*(-vonMangoldt q)+
    vonMangoldt q*(-vonMangoldt p)+(vonMangoldt p*vonMangoldt q)*1) at h
  rw [he] at h
  apply h.congr_fun
  intro N
  dsimp only [pmRamanujanEnergyCenteredPrimitive, pmRamanujanPrimitiveGramTerm]
  ring

/-- For `p, q > 1`, `G(p,q) = Λ(p)Λ(q) + Ĝ(p,q)`. -/
theorem pmRamanujanPrimitiveGram_eq_energyCentered {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    pmRamanujanPrimitiveGram p q =
      vonMangoldt p*vonMangoldt q+pmRamanujanEnergyCenteredGram p q := by
  have h := (hasSum_pmRamanujanEnergyCenteredGram hp hq).tsum_eq
  change pmRamanujanEnergyCenteredGram p q = _ at h
  linarith

end RHTower

import GaloisForLFunctions.HTGeometry.PerronRationalKernels
import GaloisForLFunctions.HTGeometry.DigammaMittagLeffler
import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv
import GaloisForLFunctions.RHTower.ArchimedeanGenusZeroSum
import GaloisForLFunctions.RHTower.XiThreeHalvesSummability
import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# The explicit formula with the genus kernel `1/(s(1−s))`

For every real `X > 1`, with the sum over the nontrivial zeros of `ξ` counted with multiplicity,

`Σ_ρ X^ρ/(ρ(1−ρ)) = X − ψ(X) + X·(Σ_{n≤X} Λ(n)/n − log X + γ) − log 2π + Σ_{k≥1} X^{−2k}/(2k(2k+1))`.

The left side converges absolutely.  Mechanism: the Perron integral
`(1/2πi)∫_{(2)} (−ζ'/ζ)(s) X^s/(s(s−1)) ds` is evaluated twice.  On the Dirichlet side it is
`Σ_n Λ(n)(X/n − 1)_+ = X·Σ_{n≤X}Λ(n)/n − ψ(X)`, by the kernel formula `(1/2πi)∫ y^s/(s(s−1)) = (y−1)_+`.
On the Mittag-Leffler side, `−ζ'/ζ = 1/(s−1) + 1/s + (log-derivative of Γ_ℝ) − Σ_ρ [1/(s−ρ) + 1/(ρ−½)]`
with the digamma series `ψ(s/2) = −γ + Σ_k (1/(k+1) − 2/(s+2k))`, and every rational term is
integrated by residues (the two-, double- and three-pole Perron evaluations); the interchange of
sum and integral is dominated by `(1+t²)^{−3/4}`.  The constants are `Σ_ρ 1/(ρ(1−ρ)) = 2+γ−log 4π`,
`Σ_ρ [1/(ρ−½) − 1/ρ] = −(2+γ−log 4π)/2`, `ψ(½) = −γ − 2 log 2` and `ψ(2) = 1 − γ`.
-/

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-! ## Digamma constants -/

/-- `Σ_{k≥0} (1/(k+1) − 1/(k+2)) = 1`, read off the digamma series at `s = 2`. -/
theorem hasSum_digammaTelescoping :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 2)) 1 := by
  have h := hasSum_digammaSeries (s := 2) (by norm_num)
  have h2 : Complex.digamma 2 = 1 - Real.eulerMascheroniConstant := by
    have := Complex.digamma_apply_add_one 1 (fun m => by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    rw [show (1 : ℂ) + 1 = 2 by norm_num, Complex.digamma_one] at this
    rw [this]; ring
  rw [h2, sub_add_cancel] at h
  have hf : (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 2)) =
      fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((2 : ℂ) + k) := by
    funext k; rw [add_comm (2 : ℂ)]
  rw [hf]; exact h

/-- `Σ_{k≥0} (1/(k+2) − 2/(2k+3)) = 1 − 2 log 2`, from the digamma series at `s = 1/2`. -/
theorem hasSum_digammaHalfShift :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 2) - 2 / (2 * (k : ℂ) + 3)) (1 - 2 * Complex.log 2) := by
  have h := hasSum_digammaSeries (s := 1 / 2) (by norm_num)
  rw [Complex.digamma_one_half] at h
  have h' := (hasSum_nat_add_iff' 1).mpr h
  have hf : (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ) + 1) - 1 / (1 / 2 + ((n + 1 : ℕ) : ℂ))) =
      fun k : ℕ => 1 / ((k : ℂ) + 2) - 2 / (2 * (k : ℂ) + 3) := by
    funext k
    have h2 : ((k : ℂ) + 2) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (k + 1))
    have h3 : (2 * (k : ℂ) + 3) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re] at this
      norm_num at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    push_cast
    rw [show ((k : ℂ) + 1 + 1) = (k : ℂ) + 2 by ring,
      show (1 / 2 : ℂ) + ((k : ℂ) + 1) = (2 * (k : ℂ) + 3) / 2 by ring]
    field_simp
  have hv : (-2 * Complex.log 2 - (Real.eulerMascheroniConstant : ℂ) + Real.eulerMascheroniConstant
      - ∑ i ∈ Finset.range 1, (1 / ((i : ℂ) + 1) - 1 / (1 / 2 + (i : ℂ)))) = 1 - 2 * Complex.log 2 := by
    rw [Finset.sum_range_one]
    push_cast
    ring
  rw [hf, hv] at h'
  exact h'

/-- `Σ_{k≥0} 1/((k+1)(2k+3)) = 2 − 2 log 2`. -/
theorem hasSum_inv_succ_mul_two_add_three :
    HasSum (fun k : ℕ => 1 / (((k : ℂ) + 1) * (2 * (k : ℂ) + 3))) (2 - 2 * Complex.log 2) := by
  have h := hasSum_digammaTelescoping.add hasSum_digammaHalfShift
  have hf : (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 2) +
      (1 / ((k : ℂ) + 2) - 2 / (2 * (k : ℂ) + 3))) =
      fun k : ℕ => 1 / (((k : ℂ) + 1) * (2 * (k : ℂ) + 3)) := by
    funext k
    have h1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have h2 : ((k : ℂ) + 2) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (k + 1))
    have h3 : (2 * (k : ℂ) + 3) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re] at this
      norm_num at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [sub_add_sub_cancel, div_sub_div _ _ h1 h3]
    congr 1
    ring
  rw [hf, show (1 : ℂ) + (1 - 2 * Complex.log 2) = 2 - 2 * Complex.log 2 by ring] at h
  exact h

/-! ## The trivial-zero series -/

/-- `S(X) = Σ_{k≥0} X^{−2(k+1)}/(2(k+1)(2k+3))`, the trivial-zero contribution. -/
def trivialZeroSeriesTerm (X : ℝ) (k : ℕ) : ℂ :=
  ((X : ℂ) ^ (2 * (k + 1)))⁻¹ / (2 * ((k : ℂ) + 1) * (2 * (k : ℂ) + 3))

def trivialZeroSeries (X : ℝ) : ℂ := ∑' k : ℕ, trivialZeroSeriesTerm X k

theorem norm_trivialZeroSeriesTerm_le {X : ℝ} (hX : 1 ≤ X) (k : ℕ) :
    ‖trivialZeroSeriesTerm X k‖ ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
  unfold trivialZeroSeriesTerm
  have hXk : (1 : ℝ) ≤ X ^ (2 * (k + 1)) := one_le_pow₀ hX
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hden : ‖(2 : ℂ) * ((k : ℂ) + 1) * (2 * (k : ℂ) + 3)‖ = 2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3) := by
    rw [show (2 : ℂ) * ((k : ℂ) + 1) * (2 * (k : ℂ) + 3)
        = ((2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [norm_div, hden, norm_inv, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (X ^ (2 * (k + 1)))⁻¹ * ((k : ℝ) + 1) ^ 2 ≤ 1 * ((k : ℝ) + 1) ^ 2 := by
        gcongr
        exact inv_le_one_of_one_le₀ hXk
    _ ≤ 1 * (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) := by nlinarith

theorem summable_trivialZeroSeriesTerm {X : ℝ} (hX : 1 ≤ X) :
    Summable (trivialZeroSeriesTerm X) := by
  refine Summable.of_norm_bounded (g := fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) ?_
    (norm_trivialZeroSeriesTerm_le hX)
  have := (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
  exact_mod_cast (summable_nat_add_iff 1).mpr this

/-! ## Zero-side constants -/

/-- Every copy is a zero of `ξ`. -/
theorem xi_xiZeroCopy_eq_zero (q : XiZeroCopy) : xi (q.1 : ℂ) = 0 := by
  have h := XiC_xiSpectralPoint_eq_zero q
  rw [XiC, ← xiZeroCopy_eq_half_add] at h
  exact h

theorem xiZeroCopy_re_pos (q : XiZeroCopy) : 0 < ((q.1 : ℂ)).re :=
  (xi_zero_re_mem_open_unit (xi_xiZeroCopy_eq_zero q)).1

theorem xiZeroCopy_re_lt_one (q : XiZeroCopy) : ((q.1 : ℂ)).re < 1 :=
  (xi_zero_re_mem_open_unit (xi_xiZeroCopy_eq_zero q)).2

theorem xiZeroCopy_ne_zero (q : XiZeroCopy) : (q.1 : ℂ) ≠ 0 := by
  intro h; have := xiZeroCopy_re_pos q; rw [h] at this; simp at this

theorem xiZeroCopy_ne_one (q : XiZeroCopy) : (q.1 : ℂ) ≠ 1 := by
  intro h; have := xiZeroCopy_re_lt_one q; rw [h] at this; simp at this

theorem xiZeroCopy_sub_half_ne_zero (q : XiZeroCopy) : (q.1 : ℂ) - 1 / 2 ≠ 0 := by
  have := xiSpectralPoint_ne_zero q
  rw [xiSpectralPoint] at this
  exact (mul_ne_zero_iff.mp this).1

theorem xiZeroCopy_one_sub_ne_zero (q : XiZeroCopy) : 1 - (q.1 : ℂ) ≠ 0 :=
  sub_ne_zero.mpr (xiZeroCopy_ne_one q).symm

/-- The reflected copy has value `1 − ρ`. -/
theorem xiZeroCopy_reflect_val (q : XiZeroCopy) :
    ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := by
  have h1 := xiZeroCopy_eq_half_add (xiZeroCopyReflectEquiv q)
  have h2 := xiZeroCopy_eq_half_add q
  rw [xiSpectralPoint_reflect] at h1
  rw [h1]
  linear_combination h2

/-- The half-shifted reflection term: `Σ_ρ [1/(ρ−½) + 1/(1−ρ)] = (2+γ−log 4π)/2`. -/
theorem summable_halfShift_reflect :
    Summable (fun q : XiZeroCopy => 1 / ((q.1 : ℂ) - 1 / 2) + 1 / (1 - (q.1 : ℂ))) := by
  have h := summable_canonicalProductE1LogDerivTerm (a := xiSpectralPoint) xiSpectralPoint_ne_zero
    xiSpectralPoint_inv_sq_summable (z := -I / 2) (fun q => neg_I_half_ne_xiSpectralPoint q)
  have h' := (h.neg).mul_left (-I)
  refine h'.congr fun q => ?_
  have ht : xiSpectralPoint q = ((q.1 : ℂ) - 1 / 2) * (-I) := rfl
  have e3 : ((q.1 : ℂ) - 1 / 2) * -I - -I / 2 = I * (1 - (q.1 : ℂ)) := by ring
  rw [ht, e3, mul_inv, Complex.inv_I, mul_inv, inv_neg, Complex.inv_I, one_div, one_div]
  linear_combination (-((1 - (q.1 : ℂ))⁻¹ + ((q.1 : ℂ) - 1 / 2)⁻¹)) * Complex.I_mul_I

theorem tsum_halfShift_reflect :
    ∑' q : XiZeroCopy, (1 / ((q.1 : ℂ) - 1 / 2) + 1 / (1 - (q.1 : ℂ))) =
      (poleSharpConstant : ℂ) / 2 := by
  have hA := tsum_logDerivTerm_eq
  have hB := tsum_inv_zero_mul_one_sub_zero
  -- termwise: (−I/2 − t_q)⁻¹ + t_q⁻¹ = I·(1/(ρ−½) + 1/(1−ρ)) and 1/(¼ + t_q²) = 1/(ρ(1−ρ))
  have hterm : ∀ q : XiZeroCopy, (-I / 2 - xiSpectralPoint q)⁻¹ + (xiSpectralPoint q)⁻¹ =
      I * (1 / ((q.1 : ℂ) - 1 / 2) + 1 / (1 - (q.1 : ℂ))) := by
    intro q
    have ht : xiSpectralPoint q = ((q.1 : ℂ) - 1 / 2) * (-I) := rfl
    have e1 : -I / 2 - ((q.1 : ℂ) - 1 / 2) * -I = I * ((q.1 : ℂ) - 1) := by ring
    have e2 : (1 - (q.1 : ℂ))⁻¹ = -((q.1 : ℂ) - 1)⁻¹ := by
      rw [← inv_neg]; congr 1; ring
    rw [ht, e1, mul_inv, Complex.inv_I, mul_inv, inv_neg, Complex.inv_I]
    simp only [one_div]
    rw [e2]
    ring
  have hterm2 : ∀ q : XiZeroCopy, (1 : ℂ) / (1 / 4 + xiSpectralPoint q ^ 2) =
      1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
    intro q
    have ht : xiSpectralPoint q = ((q.1 : ℂ) - 1 / 2) * (-I) := rfl
    rw [ht]
    congr 1
    linear_combination ((q.1 : ℂ) - 1 / 2) ^ 2 * Complex.I_mul_I
  simp_rw [hterm, hterm2] at hA
  rw [tsum_mul_left, hB] at hA
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have := mul_left_cancel₀ hI (hA.trans (by ring : I / 2 * (poleSharpConstant : ℂ) = I * ((poleSharpConstant : ℂ) / 2)))
  exact this

/-- The reflected constant: `Σ_ρ [1/(ρ−½) − 1/ρ] = −(2+γ−log 4π)/2`. -/
theorem summable_halfShift_pole :
    Summable (fun q : XiZeroCopy => 1 / ((q.1 : ℂ) - 1 / 2) - 1 / (q.1 : ℂ)) := by
  have h := (xiZeroCopyReflectEquiv.summable_iff.mpr summable_halfShift_reflect).neg
  refine h.congr fun q => ?_
  simp only [Function.comp, xiZeroCopy_reflect_val]
  rw [show (1 : ℂ) - (q.1 : ℂ) - 1 / 2 = -((q.1 : ℂ) - 1 / 2) by ring,
    show (1 : ℂ) - (1 - (q.1 : ℂ)) = (q.1 : ℂ) by ring, div_neg]
  ring

theorem tsum_halfShift_pole :
    ∑' q : XiZeroCopy, (1 / ((q.1 : ℂ) - 1 / 2) - 1 / (q.1 : ℂ)) =
      -((poleSharpConstant : ℂ) / 2) := by
  calc ∑' q : XiZeroCopy, (1 / ((q.1 : ℂ) - 1 / 2) - 1 / (q.1 : ℂ))
      = ∑' q : XiZeroCopy, -(1 / (((xiZeroCopyReflectEquiv q).1 : ℂ) - 1 / 2) +
          1 / (1 - ((xiZeroCopyReflectEquiv q).1 : ℂ))) := by
        refine tsum_congr fun q => ?_
        rw [xiZeroCopy_reflect_val, show (1 : ℂ) - (q.1 : ℂ) - 1 / 2 = -((q.1 : ℂ) - 1 / 2) by ring,
          show (1 : ℂ) - (1 - (q.1 : ℂ)) = (q.1 : ℂ) by ring, div_neg]
        ring
    _ = -∑' q : XiZeroCopy, (1 / (((xiZeroCopyReflectEquiv q).1 : ℂ) - 1 / 2) +
          1 / (1 - ((xiZeroCopyReflectEquiv q).1 : ℂ))) := by rw [tsum_neg]
    _ = -∑' q : XiZeroCopy, (1 / ((q.1 : ℂ) - 1 / 2) + 1 / (1 - (q.1 : ℂ))) := by
        rw [xiZeroCopyReflectEquiv.tsum_eq
          (fun q : XiZeroCopy => 1 / ((q.1 : ℂ) - 1 / 2) + 1 / (1 - (q.1 : ℂ)))]
    _ = -((poleSharpConstant : ℂ) / 2) := by rw [tsum_halfShift_reflect]

theorem summable_inv_mul_one_sub :
    Summable (fun q : XiZeroCopy => 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
  have h := summable_halfShift_reflect.sub summable_halfShift_pole
  refine h.congr fun q => ?_
  have hq := xiZeroCopy_sub_half_ne_zero q
  have hq0 := xiZeroCopy_ne_zero q
  have hq1 := xiZeroCopy_one_sub_ne_zero q
  field_simp
  ring

/-! ## The von Mangoldt series on the line `Re s = 2` in partial fractions -/

theorem logDeriv_Gammaℝ_digamma {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2 := by
  rw [logDeriv_apply, (hasDerivAt_Gammaℝ_of_re_pos hs).deriv,
    mul_div_cancel_left₀ _ (Complex.Gammaℝ_ne_zero_of_re_pos hs)]

/-- `Σ_n Λ(n) n^{-s} = 1/(s−1) + (½ − ½ log π − γ/2) + ½ Σ_{k≥0} (1/(k+2) − 2/(s+2k+2))
  − Σ_ρ [1/(ρ−½) + 1/(s−ρ)]` on `Re s = 2`. -/
theorem lseries_vonMangoldt_lineTwo (t : ℝ) :
    LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo t) =
      (lineTwo t - 1)⁻¹ +
        ((1 : ℂ) / 2 - (Real.log Real.pi : ℂ) / 2 - (Real.eulerMascheroniConstant : ℂ) / 2) +
        (1 / 2 : ℂ) * ∑' k : ℕ, (1 / ((k : ℂ) + 2) - 2 / (lineTwo t + 2 * ((k : ℂ) + 1))) -
        ∑' q : XiZeroCopy, (((q.1 : ℂ) - 1 / 2)⁻¹ + (lineTwo t - (q.1 : ℂ))⁻¹) := by
  have hre : 1 < (lineTwo t).re := by rw [lineTwo_re]; norm_num
  have h := xi_explicitFormula_logDeriv hre
  have hs2 : 0 < (lineTwo t / 2).re := by
    rw [Complex.div_re]; simp [lineTwo]
  have hΓ := logDeriv_Gammaℝ_digamma (show 0 < (lineTwo t).re by rw [lineTwo_re]; norm_num)
  have hdig := digamma_eq_tsum hs2
  have hsumm := summable_digammaSeriesTerm hs2
  rw [hsumm.tsum_eq_zero_add] at hdig
  have hshift : (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℂ) + 1) - 1 / (lineTwo t / 2 + ((k + 1 : ℕ) : ℂ)))
      = fun k : ℕ => 1 / ((k : ℂ) + 2) - 2 / (lineTwo t + 2 * ((k : ℂ) + 1)) := by
    funext k
    push_cast
    rw [show (k : ℂ) + 1 + 1 = (k : ℂ) + 2 by ring,
      show lineTwo t / 2 + ((k : ℂ) + 1) = (lineTwo t + 2 * ((k : ℂ) + 1)) / 2 by ring, one_div_div]
  rw [hshift] at hdig
  have hs0 := lineTwo_ne_zero t
  have h0 : (1 : ℂ) / (((0 : ℕ) : ℂ) + 1) - 1 / (lineTwo t / 2 + ((0 : ℕ) : ℂ)) = 1 - 2 / lineTwo t := by
    push_cast
    rw [add_zero, zero_add, div_one, one_div_div]
  rw [h0] at hdig
  have hL : LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo t) =
      (lineTwo t)⁻¹ + (lineTwo t - 1)⁻¹ + logDeriv Complex.Gammaℝ (lineTwo t) -
        ∑' q : XiZeroCopy, (((q.1 : ℂ) - 1 / 2)⁻¹ + (lineTwo t - (q.1 : ℂ))⁻¹) := by
    rw [h]; ring
  rw [hL, hΓ, hdig]
  field_simp
  ring

/-! ## The Dirichlet side -/

/-- The Perron kernel `X^s/(s(s−1))` on the line `Re s = 2`. -/
def lagKernel (X : ℝ) (t : ℝ) : ℂ := (X : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1))

theorem integrable_lagKernel {X : ℝ} (hX : 0 < X) : Integrable (lagKernel X) :=
  integrable_lineTwo_basic hX

theorem continuous_lagKernel {X : ℝ} (hX : 0 < X) : Continuous (lagKernel X) := by
  unfold lagKernel
  have hcp : Continuous (fun t : ℝ => (X : ℂ) ^ lineTwo t) :=
    (by unfold lineTwo; fun_prop : Continuous lineTwo).const_cpow
      (Or.inl (by exact_mod_cast hX.ne'))
  refine hcp.div ?_ fun t => mul_ne_zero (lineTwo_ne_zero t) (lineTwo_sub_one_ne_zero t)
  unfold lineTwo; fun_prop

/-- `‖X^s/(s(s−1))‖ ≤ X²/(1+t²)` on the line. -/
theorem norm_lagKernel_le {X : ℝ} (hX : 0 < X) (t : ℝ) :
    ‖lagKernel X t‖ ≤ X ^ 2 / (1 + t ^ 2) := by
  unfold lagKernel
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, lineTwo_re,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h1 : ‖lineTwo t‖ = Real.sqrt (2 ^ 2 + t ^ 2) := by
    unfold lineTwo; exact Complex.norm_add_mul_I 2 t
  have h2 : ‖lineTwo t - 1‖ = Real.sqrt (1 ^ 2 + t ^ 2) := by
    rw [show lineTwo t - 1 = ((1 : ℝ) : ℂ) + t * I by unfold lineTwo; push_cast; ring]
    exact Complex.norm_add_mul_I 1 t
  rw [h1, h2]
  have h3 : Real.sqrt (1 ^ 2 + t ^ 2) * Real.sqrt (1 ^ 2 + t ^ 2) = 1 + t ^ 2 := by
    rw [Real.mul_self_sqrt (by positivity)]; ring
  have h4 : Real.sqrt (1 ^ 2 + t ^ 2) ≤ Real.sqrt (2 ^ 2 + t ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h5 : 1 + t ^ 2 ≤ Real.sqrt (2 ^ 2 + t ^ 2) * Real.sqrt (1 ^ 2 + t ^ 2) := by
    rw [← h3]; gcongr
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) h5

/-- The `n`-th Dirichlet term of the Perron integrand. -/
def dirichletTerm (X : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) (lineTwo t) n * lagKernel X t

theorem dirichletTerm_eq {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    dirichletTerm X n t =
      ((vonMangoldt n : ℝ) : ℂ) * (((X / n : ℝ) : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1))) := by
  unfold dirichletTerm lagKernel
  rw [LSeries.term_of_ne_zero hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hcp : (((X / n : ℝ) : ℂ) ^ lineTwo t) = (X : ℂ) ^ lineTwo t / (n : ℂ) ^ lineTwo t := by
    rw [show (X / n : ℝ) = X * (n : ℝ)⁻¹ by ring, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hX.le (by positivity), Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.inv_cpow _ _ (by rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg hn0.le]; exact Real.pi_pos.ne'.symm)]
    exact (div_eq_mul_inv _ _).symm
  rw [hcp]
  ring

theorem dirichletTerm_zero (X : ℝ) (t : ℝ) : dirichletTerm X 0 t = 0 := by
  unfold dirichletTerm; rw [LSeries.term_zero, zero_mul]

theorem integrable_dirichletTerm {X : ℝ} (hX : 0 < X) (n : ℕ) : Integrable (dirichletTerm X n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : dirichletTerm X 0 = fun _ => 0 := funext (dirichletTerm_zero X)
    rw [h0]; exact integrable_zero _ _ _
  · have hn0 : n ≠ 0 := hn.ne'
    have hXn : (0 : ℝ) < X / n := by positivity
    have := (integrable_lineTwo_basic hXn).const_mul ((vonMangoldt n : ℝ) : ℂ)
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    rw [dirichletTerm_eq hX hn0]

/-- `∫ ‖dirichletTerm n‖ = Λ(n) (X/n)² ∫ ‖1/(s(s−1))‖`. -/
theorem integral_norm_dirichletTerm {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : n ≠ 0) :
    ∫ t : ℝ, ‖dirichletTerm X n t‖ =
      vonMangoldt n * (X / n) ^ 2 * ∫ t : ℝ, ‖(1 : ℂ) / (lineTwo t * (lineTwo t - 1))‖ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hXn : (0 : ℝ) < X / n := by positivity
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  beta_reduce
  rw [dirichletTerm_eq hX hn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, div_eq_mul_one_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hXn, lineTwo_re,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

theorem summable_vonMangoldt_div_sq :
    Summable (fun n : ℕ => vonMangoldt n / (n : ℝ) ^ 2) := by
  have hbase : Summable (fun n : ℕ => 2 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    ((Real.summable_nat_rpow_inv (p := 3 / 2)).mpr (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
      Real.log_le_rpow_div hn0.le (by norm_num)
    have hΛ := ArithmeticFunction.vonMangoldt_le_log (n := n)
    have hpow : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) ^ 2 / (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [eq_div_iff (by positivity), ← Real.rpow_natCast, ← Real.rpow_add hn0]
      norm_num
    rw [hpow, inv_div, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have : vonMangoldt n ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by linarith
    calc vonMangoldt n * (n : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ 2 := by gcongr
      _ = 2 * (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ 2 := rfl

theorem summable_integral_norm_dirichletTerm {X : ℝ} (hX : 0 < X) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖dirichletTerm X n t‖) := by
  set C : ℝ := ∫ t : ℝ, ‖(1 : ℂ) / (lineTwo t * (lineTwo t - 1))‖
  have hbase : Summable (fun n : ℕ => (X ^ 2 * C) * (vonMangoldt n / (n : ℝ) ^ 2)) :=
    summable_vonMangoldt_div_sq.mul_left _
  refine hbase.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [dirichletTerm_zero]
  · rw [integral_norm_dirichletTerm hX hn.ne']
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring

/-- **The Dirichlet side.**  `(1/2π)∫ (Σ_n Λ(n) n^{-s}) X^s/(s(s−1)) dt = Σ_{n≤X} Λ(n)(X/n − 1)`. -/
theorem dirichlet_side {X : ℝ} (hX : 1 < X) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo t) *
        lagKernel X t
      = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ((vonMangoldt n : ℝ) : ℂ) * ((X : ℂ) / n - 1) := by
  have hX0 : 0 < X := by linarith
  have hint : (fun t : ℝ => LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo t) * lagKernel X t)
      = fun t : ℝ => ∑' n : ℕ, dirichletTerm X n t := by
    funext t
    unfold LSeries dirichletTerm
    rw [tsum_mul_right]
  rw [hint, ← integral_tsum_of_summable_integral_norm (integrable_dirichletTerm hX0)
    (summable_integral_norm_dirichletTerm hX0)]
  -- termwise evaluation
  have hterm : ∀ n : ℕ, (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, dirichletTerm X n t =
      ((vonMangoldt n : ℝ) : ℂ) * (if 1 < X / n then ((X / n : ℝ) : ℂ) - 1 else 0) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [dirichletTerm_zero]
    · have hn0 : n ≠ 0 := hn.ne'
      have hXn : (0 : ℝ) < X / n := by positivity
      have h := perron_lineTwo_basic hXn
      have hI : ∫ t : ℝ, dirichletTerm X n t = ((vonMangoldt n : ℝ) : ℂ) *
          ∫ t : ℝ, ((X / n : ℝ) : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1)) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun t => dirichletTerm_eq hX0 hn0 t)
      rw [hI, ← h, Complex.real_smul, Complex.real_smul]
      ring
  have hsmul : (1 / (2 * Real.pi) : ℝ) • ∑' n : ℕ, ∫ t : ℝ, dirichletTerm X n t
      = ∑' n : ℕ, (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, dirichletTerm X n t := by
    rw [Complex.real_smul, ← tsum_mul_left]
    exact tsum_congr fun n => Complex.real_smul.symm
  rw [hsmul]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊X⌋₊)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hnX : (n : ℝ) ≤ X := (Nat.cast_le.mpr hn.2).trans (Nat.floor_le hX0.le)
    by_cases h : 1 < X / n
    · rw [if_pos h]; push_cast; ring
    · rw [if_neg h]
      have hle : X / n ≤ 1 := not_lt.mp h
      have heq : X / n = 1 := le_antisymm hle (by rw [le_div_iff₀ hn0]; linarith)
      have hXn : (X : ℂ) / n = 1 := by
        have := congrArg (fun r : ℝ => (r : ℂ)) heq
        push_cast at this; exact this
      rw [hXn]; ring
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp
    · have hgt : ¬ (1 < X / n) := by
        intro h1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
        rw [one_lt_div hn0] at h1
        exact hn ⟨hnpos, Nat.le_floor h1.le⟩
      rw [if_neg hgt, mul_zero]

/-! ## The Mittag-Leffler side: termwise bounds -/

/-- The `k`-th digamma term times the kernel. -/
def kTerm (X : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  (1 / ((k : ℂ) + 2) - 2 / (lineTwo t + 2 * ((k : ℂ) + 1))) * lagKernel X t

/-- The zero term times the kernel. -/
def zTerm (X : ℝ) (q : XiZeroCopy) (t : ℝ) : ℂ :=
  (((q.1 : ℂ) - 1 / 2)⁻¹ + (lineTwo t - (q.1 : ℂ))⁻¹) * lagKernel X t

theorem lineTwo_add_ne_zero (k : ℕ) (t : ℝ) : lineTwo t + 2 * ((k : ℂ) + 1) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [lineTwo] at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- `|1/(k+2) − 2/(s+2k+2)| ≤ √|t| / (2(k+2)√(k+2))` on the line `Re s = 2`. -/
theorem norm_kFactor_le (k : ℕ) (t : ℝ) :
    ‖1 / ((k : ℂ) + 2) - 2 / (lineTwo t + 2 * ((k : ℂ) + 1))‖ ≤
      Real.sqrt |t| / (2 * ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) := by
  have hk2 : ((k : ℂ) + 2) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (k + 1))
  have hs := lineTwo_add_ne_zero k t
  have hid : 1 / ((k : ℂ) + 2) - 2 / (lineTwo t + 2 * ((k : ℂ) + 1)) =
      (lineTwo t - 2) / (((k : ℂ) + 2) * (lineTwo t + 2 * ((k : ℂ) + 1))) := by
    field_simp
    ring
  rw [hid, norm_div, norm_mul]
  have h1 : ‖lineTwo t - 2‖ = |t| := by
    rw [show lineTwo t - 2 = (t : ℂ) * I by unfold lineTwo; push_cast; ring, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖(k : ℂ) + 2‖ = (k : ℝ) + 2 := by
    rw [show (k : ℂ) + 2 = (((k : ℝ) + 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h3 : ‖lineTwo t + 2 * ((k : ℂ) + 1)‖ =
      Real.sqrt ((2 * ((k : ℝ) + 1) + 2) ^ 2 + t ^ 2) := by
    rw [show lineTwo t + 2 * ((k : ℂ) + 1) = ((2 * ((k : ℝ) + 1) + 2 : ℝ) : ℂ) + t * I by
      unfold lineTwo; push_cast; ring]
    exact Complex.norm_add_mul_I _ _
  rw [h1, h2, h3]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hamgm : 4 * ((k : ℝ) + 2) * |t| ≤ (2 * ((k : ℝ) + 1) + 2) ^ 2 + t ^ 2 := by
    nlinarith [sq_nonneg (2 * ((k : ℝ) + 1) + 2 - |t|), sq_abs t, abs_nonneg t]
  have hsq : Real.sqrt (4 * ((k : ℝ) + 2) * |t|) ≤
      Real.sqrt ((2 * ((k : ℝ) + 1) + 2) ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hamgm
  have hsq' : Real.sqrt (4 * ((k : ℝ) + 2) * |t|) =
      2 * Real.sqrt ((k : ℝ) + 2) * Real.sqrt |t| := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · have hpos : 0 < Real.sqrt |t| := Real.sqrt_pos.mpr (abs_pos.mpr ht)
    have hk2pos : 0 < Real.sqrt ((k : ℝ) + 2) := Real.sqrt_pos.mpr (by positivity)
    have hden : 0 < Real.sqrt ((2 * ((k : ℝ) + 1) + 2) ^ 2 + t ^ 2) :=
      Real.sqrt_pos.mpr (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have habs : |t| = Real.sqrt |t| * Real.sqrt |t| := (Real.mul_self_sqrt (abs_nonneg t)).symm
    calc |t| * (2 * ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))
        = Real.sqrt |t| * (((k : ℝ) + 2) * (2 * Real.sqrt ((k : ℝ) + 2) * Real.sqrt |t|)) := by
          linear_combination (2 * ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) * habs
      _ ≤ Real.sqrt |t| * (((k : ℝ) + 2) * Real.sqrt ((2 * ((k : ℝ) + 1) + 2) ^ 2 + t ^ 2)) := by
          gcongr
          rw [← hsq']
          exact hsq

/-- `√|t| ≤ (1+t²)^{1/4}`. -/
theorem sqrt_abs_le_rpow_quarter (t : ℝ) : Real.sqrt |t| ≤ (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, show (1 / 4 : ℝ) = (1 / 2) * (1 / 2) by norm_num,
    Real.rpow_mul (by positivity)]
  apply Real.rpow_le_rpow (abs_nonneg t) _ (by norm_num)
  rw [← Real.sqrt_eq_rpow, Real.le_sqrt (abs_nonneg t) (by positivity), sq_abs]
  linarith

theorem rpow_quarter_div_eq (t : ℝ) :
    (1 + t ^ 2) ^ (1 / 4 : ℝ) / (1 + t ^ 2) = (1 + t ^ 2) ^ (-(3 / 4 : ℝ)) := by
  rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add (by positivity)]
  norm_num

theorem norm_kTerm_le {X : ℝ} (hX : 0 < X) (k : ℕ) (t : ℝ) :
    ‖kTerm X k t‖ ≤ (X ^ 2 / 2) * (1 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) *
      (1 + t ^ 2) ^ (-(3 / 4 : ℝ)) := by
  unfold kTerm
  rw [norm_mul]
  have h1 := norm_kFactor_le k t
  have h2 := norm_lagKernel_le hX t
  have h3 := sqrt_abs_le_rpow_quarter t
  calc ‖1 / ((k : ℂ) + 2) - 2 / (lineTwo t + 2 * ((k : ℂ) + 1))‖ * ‖lagKernel X t‖
      ≤ (Real.sqrt |t| / (2 * ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) * (X ^ 2 / (1 + t ^ 2)) := by
        gcongr
    _ ≤ ((1 + t ^ 2) ^ (1 / 4 : ℝ) / (2 * ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) *
          (X ^ 2 / (1 + t ^ 2)) := by gcongr
    _ = (X ^ 2 / 2) * (1 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) *
          ((1 + t ^ 2) ^ (1 / 4 : ℝ) / (1 + t ^ 2)) := by
        have hk2pos : 0 < Real.sqrt ((k : ℝ) + 2) := Real.sqrt_pos.mpr (by positivity)
        have h1t : 0 < 1 + t ^ 2 := by positivity
        field_simp
        try ring
    _ = _ := by rw [rpow_quarter_div_eq]

theorem continuous_kTerm {X : ℝ} (hX : 0 < X) (k : ℕ) : Continuous (kTerm X k) := by
  unfold kTerm
  refine Continuous.mul (Continuous.sub continuous_const ?_) (continuous_lagKernel hX)
  exact continuous_const.div (by unfold lineTwo; fun_prop) (lineTwo_add_ne_zero k)

theorem integrable_kTerm {X : ℝ} (hX : 0 < X) (k : ℕ) : Integrable (kTerm X k) :=
  (integrable_one_add_sq_rpow_neg_three_quarters.const_mul
    ((X ^ 2 / 2) * (1 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))))).mono'
    (continuous_kTerm hX k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => norm_kTerm_le hX k t)

/-- The majorant constant `∫ (1+t²)^{−3/4} dt`. -/
def majorantMass : ℝ := ∫ t : ℝ, (1 + t ^ 2) ^ (-(3 / 4 : ℝ))

theorem integral_norm_kTerm_le {X : ℝ} (hX : 0 < X) (k : ℕ) :
    ∫ t : ℝ, ‖kTerm X k t‖ ≤
      (X ^ 2 / 2) * (1 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) * majorantMass := by
  unfold majorantMass
  rw [← integral_const_mul]
  exact integral_mono (integrable_kTerm hX k).norm
    (integrable_one_add_sq_rpow_neg_three_quarters.const_mul _) (norm_kTerm_le hX k)

theorem summable_inv_mul_sqrt_shift :
    Summable (fun k : ℕ => 1 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) := by
  have h := (Real.summable_nat_rpow_inv (p := 3 / 2)).mpr (by norm_num)
  have h2 := (summable_nat_add_iff 2).mpr h
  refine h2.congr fun k => ?_
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  push_cast
  rw [one_div, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hk, Real.rpow_one,
    Real.sqrt_eq_rpow]

theorem summable_integral_norm_kTerm {X : ℝ} (hX : 0 < X) :
    Summable (fun k : ℕ => ∫ t : ℝ, ‖kTerm X k t‖) := by
  have hb : Summable (fun k : ℕ =>
      (X ^ 2 / 2) * (1 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) * majorantMass) :=
    (summable_inv_mul_sqrt_shift.mul_left (X ^ 2 / 2)).mul_right majorantMass
  exact Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _)
    (fun k => integral_norm_kTerm_le hX k) hb

/-- Zero terms: `|1/(ρ−½) + 1/(s−ρ)| ≤ 4(1+|t|)/(‖ρ−½‖ (1+|t−γ|))` on the line. -/
theorem norm_zFactor_le (q : XiZeroCopy) (t : ℝ) :
    ‖((q.1 : ℂ) - 1 / 2)⁻¹ + (lineTwo t - (q.1 : ℂ))⁻¹‖ ≤
      4 * (1 + |t|) / (‖(q.1 : ℂ) - 1 / 2‖ * (1 + |t - ((q.1 : ℂ)).im|)) := by
  have hq := xiZeroCopy_sub_half_ne_zero q
  have hre := xiZeroCopy_re_lt_one q
  have hs : lineTwo t - (q.1 : ℂ) ≠ 0 := lineTwo_sub_ne_zero (by linarith) t
  have hid : ((q.1 : ℂ) - 1 / 2)⁻¹ + (lineTwo t - (q.1 : ℂ))⁻¹ =
      (lineTwo t - 1 / 2) / (((q.1 : ℂ) - 1 / 2) * (lineTwo t - (q.1 : ℂ))) := by
    rw [inv_add_inv hq hs]
    congr 1
    ring
  rw [hid, norm_div, norm_mul]
  have h1 : ‖lineTwo t - 1 / 2‖ ≤ 2 * (1 + |t|) := by
    rw [show lineTwo t - 1 / 2 = ((3 / 2 : ℝ) : ℂ) + t * I by unfold lineTwo; push_cast; ring,
      Complex.norm_add_mul_I, Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg t, sq_abs t]
  have h2 : (1 + |t - ((q.1 : ℂ)).im|) / 2 ≤ ‖lineTwo t - (q.1 : ℂ)‖ := by
    have hw : lineTwo t - (q.1 : ℂ) = ((2 - ((q.1 : ℂ)).re : ℝ) : ℂ) + ((t - ((q.1 : ℂ)).im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [lineTwo]
    rw [hw, Complex.norm_add_mul_I]
    apply Real.le_sqrt_of_sq_le
    have hre1 : 1 ≤ 2 - ((q.1 : ℂ)).re := by linarith
    nlinarith [abs_nonneg (t - ((q.1 : ℂ)).im), sq_abs (t - ((q.1 : ℂ)).im),
      sq_nonneg (1 - |t - ((q.1 : ℂ)).im|)]
  have hqn : 0 < ‖(q.1 : ℂ) - 1 / 2‖ := norm_pos_iff.mpr hq
  have hsn : 0 < ‖lineTwo t - (q.1 : ℂ)‖ := norm_pos_iff.mpr hs
  calc ‖lineTwo t - 1 / 2‖ / (‖(q.1 : ℂ) - 1 / 2‖ * ‖lineTwo t - (q.1 : ℂ)‖)
      ≤ (2 * (1 + |t|)) / (‖(q.1 : ℂ) - 1 / 2‖ * ((1 + |t - ((q.1 : ℂ)).im|) / 2)) := by
        gcongr
    _ = 4 * (1 + |t|) / (‖(q.1 : ℂ) - 1 / 2‖ * (1 + |t - ((q.1 : ℂ)).im|)) := by
        field_simp
        ring

theorem norm_zTerm_le {X : ℝ} (hX : 0 < X) (q : XiZeroCopy) (t : ℝ) :
    ‖zTerm X q t‖ ≤ (8 * X ^ 2 / ‖(q.1 : ℂ) - 1 / 2‖) *
      (1 / ((1 + |t - ((q.1 : ℂ)).im|) * (1 + |t|))) := by
  unfold zTerm
  rw [norm_mul]
  have h1 := norm_zFactor_le q t
  have h2 := norm_lagKernel_le hX t
  have hqn : 0 < ‖(q.1 : ℂ) - 1 / 2‖ := norm_pos_iff.mpr (xiZeroCopy_sub_half_ne_zero q)
  have h3 : X ^ 2 / (1 + t ^ 2) ≤ 2 * X ^ 2 / (1 + |t|) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (1 - |t|), sq_nonneg X]
  calc ‖((q.1 : ℂ) - 1 / 2)⁻¹ + (lineTwo t - (q.1 : ℂ))⁻¹‖ * ‖lagKernel X t‖
      ≤ (4 * (1 + |t|) / (‖(q.1 : ℂ) - 1 / 2‖ * (1 + |t - ((q.1 : ℂ)).im|))) *
          (2 * X ^ 2 / (1 + |t|) ^ 2) :=
        mul_le_mul h1 (h2.trans h3) (norm_nonneg _) (by positivity)
    _ = (8 * X ^ 2 / ‖(q.1 : ℂ) - 1 / 2‖) * (1 / ((1 + |t - ((q.1 : ℂ)).im|) * (1 + |t|))) := by
        have : (0 : ℝ) < 1 + |t| := by positivity
        field_simp
        try ring

/-- The two-centre majorant, specialised: the integrable dominating function of `zTerm`. -/
theorem norm_zTerm_le_majorant {X : ℝ} (hX : 0 < X) (q : XiZeroCopy) (t : ℝ) :
    ‖zTerm X q t‖ ≤ (8 * X ^ 2 * Real.sqrt 2 / (‖(q.1 : ℂ) - 1 / 2‖ * Real.sqrt ‖(q.1 : ℂ) - 1 / 2‖)) *
      ((1 + t ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (t - ((q.1 : ℂ)).im) ^ 2) ^ (-(3 / 4 : ℝ))) := by
  have h1 := norm_zTerm_le hX q t
  have h2 := two_centre_majorant ((q.1 : ℂ)).im t
  have hqn : 0 < ‖(q.1 : ℂ) - 1 / 2‖ := norm_pos_iff.mpr (xiZeroCopy_sub_half_ne_zero q)
  -- `‖ρ − ½‖ ≤ 1 + |γ|`, hence `(1+|γ|)^{−1/2} ≤ ‖ρ−½‖^{−1/2}`
  have hle : ‖(q.1 : ℂ) - 1 / 2‖ ≤ 1 + |((q.1 : ℂ)).im| := by
    have := Complex.norm_le_abs_re_add_abs_im ((q.1 : ℂ) - 1 / 2)
    have hre0 := xiZeroCopy_re_pos q
    have hre1 := xiZeroCopy_re_lt_one q
    have habs : |((q.1 : ℂ) - 1 / 2).re| ≤ 1 := by
      rw [Complex.sub_re]; simp only [Complex.div_ofNat_re, Complex.one_re]
      rw [abs_le]; constructor <;> linarith
    have him : ((q.1 : ℂ) - 1 / 2).im = ((q.1 : ℂ)).im := by simp
    rw [him] at this
    linarith
  have hrp : (1 + |((q.1 : ℂ)).im|) ^ (-(1 / 2 : ℝ)) ≤ 1 / Real.sqrt ‖(q.1 : ℂ) - 1 / 2‖ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
    exact inv_anti₀ (Real.sqrt_pos.mpr hqn) (Real.sqrt_le_sqrt hle)
  calc ‖zTerm X q t‖ ≤ (8 * X ^ 2 / ‖(q.1 : ℂ) - 1 / 2‖) *
        (1 / ((1 + |t - ((q.1 : ℂ)).im|) * (1 + |t|))) := h1
    _ ≤ (8 * X ^ 2 / ‖(q.1 : ℂ) - 1 / 2‖) * (Real.sqrt 2 * (1 + |((q.1 : ℂ)).im|) ^ (-(1 / 2 : ℝ)) *
          ((1 + t ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (t - ((q.1 : ℂ)).im) ^ 2) ^ (-(3 / 4 : ℝ)))) := by
        gcongr
    _ ≤ (8 * X ^ 2 / ‖(q.1 : ℂ) - 1 / 2‖) * (Real.sqrt 2 * (1 / Real.sqrt ‖(q.1 : ℂ) - 1 / 2‖) *
          ((1 + t ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (t - ((q.1 : ℂ)).im) ^ 2) ^ (-(3 / 4 : ℝ)))) := by
        gcongr
    _ = _ := by
        have := Real.sqrt_pos.mpr hqn
        field_simp
        try ring

theorem continuous_zTerm {X : ℝ} (hX : 0 < X) (q : XiZeroCopy) : Continuous (zTerm X q) := by
  unfold zTerm
  have hre := xiZeroCopy_re_lt_one q
  refine Continuous.mul (Continuous.add continuous_const ?_) (continuous_lagKernel hX)
  exact Continuous.inv₀ (by unfold lineTwo; fun_prop) (fun t => lineTwo_sub_ne_zero (by linarith) t)

theorem integrable_majorant_shift (γ : ℝ) :
    Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (t - γ) ^ 2) ^ (-(3 / 4 : ℝ))) :=
  integrable_one_add_sq_rpow_neg_three_quarters.add
    (integrable_one_add_sq_rpow_neg_three_quarters.comp_sub_right γ)

theorem integral_majorant_shift (γ : ℝ) :
    ∫ t : ℝ, ((1 + t ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (t - γ) ^ 2) ^ (-(3 / 4 : ℝ))) = 2 * majorantMass := by
  rw [integral_add integrable_one_add_sq_rpow_neg_three_quarters
    (integrable_one_add_sq_rpow_neg_three_quarters.comp_sub_right γ),
    integral_sub_right_eq_self (fun t : ℝ => (1 + t ^ 2) ^ (-(3 / 4 : ℝ))) γ]
  unfold majorantMass
  ring

theorem integrable_zTerm {X : ℝ} (hX : 0 < X) (q : XiZeroCopy) : Integrable (zTerm X q) :=
  ((integrable_majorant_shift ((q.1 : ℂ)).im).const_mul _).mono'
    (continuous_zTerm hX q).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => norm_zTerm_le_majorant hX q t)

theorem integral_norm_zTerm_le {X : ℝ} (hX : 0 < X) (q : XiZeroCopy) :
    ∫ t : ℝ, ‖zTerm X q t‖ ≤ (16 * X ^ 2 * Real.sqrt 2 * majorantMass) *
      (1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)) := by
  have hnorm : ‖xiSpectralPoint q‖ = ‖(q.1 : ℂ) - 1 / 2‖ := by
    rw [xiSpectralPoint, norm_mul, norm_neg, Complex.norm_I, mul_one]
  rw [hnorm]
  calc ∫ t : ℝ, ‖zTerm X q t‖
      ≤ ∫ t : ℝ, (8 * X ^ 2 * Real.sqrt 2 / (‖(q.1 : ℂ) - 1 / 2‖ * Real.sqrt ‖(q.1 : ℂ) - 1 / 2‖)) *
          ((1 + t ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (t - ((q.1 : ℂ)).im) ^ 2) ^ (-(3 / 4 : ℝ))) :=
        integral_mono (integrable_zTerm hX q).norm
          ((integrable_majorant_shift _).const_mul _) (norm_zTerm_le_majorant hX q)
    _ = _ := by
        rw [integral_const_mul, integral_majorant_shift]
        ring

theorem summable_integral_norm_zTerm {X : ℝ} (hX : 0 < X) :
    Summable (fun q : XiZeroCopy => ∫ t : ℝ, ‖zTerm X q t‖) :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun q => integral_norm_zTerm_le hX q)
    (xiSpectralPoint_inv_three_halves_summable.mul_left _)

/-! ## Termwise integrals -/

theorem integral_kTerm {X : ℝ} (hX : 1 < X) (k : ℕ) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, kTerm X k t =
      (1 / ((k : ℂ) + 2)) * ((X : ℂ) - 1) -
        2 * ((1 / (-(2 * ((k : ℂ) + 1)))) *
          (((X : ℂ) ^ (-(2 * ((k : ℂ) + 1))) - X) / (-(2 * ((k : ℂ) + 1)) - 1) - (X - 1))) := by
  have hX0 : 0 < X := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set a : ℂ := -(2 * ((k : ℂ) + 1)) with ha
  have hare : a.re < 2 := by
    rw [ha]; simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.natCast_re,
      Complex.one_re]; norm_num; linarith
  have ha0 : a ≠ 0 := by
    rw [ha]; intro h; have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.natCast_re, Complex.one_re,
      Complex.zero_re] at this; norm_num at this; linarith
  have ha1 : a ≠ 1 := by
    rw [ha]; intro h; have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.natCast_re, Complex.one_re] at this
    norm_num at this; linarith
  have hsa : ∀ t : ℝ, lineTwo t - a = lineTwo t + 2 * ((k : ℂ) + 1) := by intro t; rw [ha]; ring
  have hsplit : ∀ t : ℝ, kTerm X k t = (1 / ((k : ℂ) + 2)) * lagKernel X t -
      2 * ((X : ℂ) ^ lineTwo t / ((lineTwo t - a) * lineTwo t * (lineTwo t - 1))) := by
    intro t
    unfold kTerm lagKernel
    have h0 := lineTwo_ne_zero t
    have h1 := lineTwo_sub_one_ne_zero t
    have h2 := lineTwo_add_ne_zero k t
    have hk2 : ((k : ℂ) + 2) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (k + 1))
    rw [hsa]
    field_simp
    try ring
  simp_rw [hsplit]
  have hI1 := (integrable_lagKernel hX0).const_mul (1 / ((k : ℂ) + 2))
  have hI2 : Integrable (fun t : ℝ =>
      (X : ℂ) ^ lineTwo t / ((lineTwo t - a) * lineTwo t * (lineTwo t - 1))) := by
    have := ((integrable_lineTwo_shift hare hX0).sub (integrable_lineTwo_basic hX0)).const_mul (1 / a)
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    have h0 := lineTwo_ne_zero t
    have h1 := lineTwo_sub_one_ne_zero t
    have h2 := lineTwo_sub_ne_zero hare t
    simp only [Pi.sub_apply]
    field_simp
    try ring
  rw [integral_sub hI1 (hI2.const_mul 2), integral_const_mul, integral_const_mul, smul_sub,
    ← mul_smul_comm, ← mul_smul_comm, perron_lineTwo_threePole hare ha0 ha1 hX]
  have hb := perron_lineTwo_basic hX0
  rw [if_pos hX] at hb
  unfold lagKernel
  rw [hb]

theorem integral_zTerm {X : ℝ} (hX : 1 < X) (q : XiZeroCopy) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, zTerm X q t =
      ((q.1 : ℂ) - 1 / 2)⁻¹ * ((X : ℂ) - 1) +
        (1 / (q.1 : ℂ)) * (((X : ℂ) ^ (q.1 : ℂ) - X) / ((q.1 : ℂ) - 1) - (X - 1)) := by
  have hX0 : 0 < X := by linarith
  have hre := xiZeroCopy_re_lt_one q
  have hare : ((q.1 : ℂ)).re < 2 := by linarith
  have ha0 := xiZeroCopy_ne_zero q
  have ha1 := xiZeroCopy_ne_one q
  have hsplit : ∀ t : ℝ, zTerm X q t = ((q.1 : ℂ) - 1 / 2)⁻¹ * lagKernel X t +
      (X : ℂ) ^ lineTwo t / ((lineTwo t - (q.1 : ℂ)) * lineTwo t * (lineTwo t - 1)) := by
    intro t
    unfold zTerm lagKernel
    have h0 := lineTwo_ne_zero t
    have h1 := lineTwo_sub_one_ne_zero t
    have h2 := lineTwo_sub_ne_zero hare t
    have hq := xiZeroCopy_sub_half_ne_zero q
    field_simp
    try ring
  simp_rw [hsplit]
  have hI1 := (integrable_lagKernel hX0).const_mul ((q.1 : ℂ) - 1 / 2)⁻¹
  have hI2 : Integrable (fun t : ℝ =>
      (X : ℂ) ^ lineTwo t / ((lineTwo t - (q.1 : ℂ)) * lineTwo t * (lineTwo t - 1))) := by
    have := ((integrable_lineTwo_shift hare hX0).sub (integrable_lineTwo_basic hX0)).const_mul
      (1 / (q.1 : ℂ))
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    have h0 := lineTwo_ne_zero t
    have h1 := lineTwo_sub_one_ne_zero t
    have h2 := lineTwo_sub_ne_zero hare t
    simp only [Pi.sub_apply]
    field_simp
    try ring
  rw [integral_add hI1 hI2, integral_const_mul, smul_add, ← mul_smul_comm,
    perron_lineTwo_threePole hare ha0 ha1 hX]
  have hb := perron_lineTwo_basic hX0
  rw [if_pos hX] at hb
  unfold lagKernel
  rw [hb]

/-! ## The two series of termwise values -/

theorem tsum_integral_kTerm {X : ℝ} (hX : 1 < X) :
    ∑' k : ℕ, (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, kTerm X k t =
      -((X : ℂ) - 1) + X * (2 - 2 * Complex.log 2) - 2 * trivialZeroSeries X := by
  have hval : ∀ k : ℕ, (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, kTerm X k t =
      ((X : ℂ) - 1) * (1 / ((k : ℂ) + 2) - 1 / ((k : ℂ) + 1)) +
        (X : ℂ) * (1 / (((k : ℂ) + 1) * (2 * (k : ℂ) + 3))) - 2 * trivialZeroSeriesTerm X k := by
    intro k
    rw [integral_kTerm hX k]
    unfold trivialZeroSeriesTerm
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hk2 : ((k : ℂ) + 2) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (k + 1))
    have hk3 : (2 * (k : ℂ) + 3) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re] at this
      norm_num at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hpow : (X : ℂ) ^ (-(2 * ((k : ℂ) + 1))) = ((X : ℂ) ^ (2 * (k + 1)))⁻¹ := by
      rw [Complex.cpow_neg, show (2 * ((k : ℂ) + 1)) = ((2 * (k + 1) : ℕ) : ℂ) by push_cast; ring,
        Complex.cpow_natCast]
    have hne1 : -(2 * ((k : ℂ) + 1)) ≠ 0 := by
      intro h; apply hk1; linear_combination -(1 / 2 : ℂ) * h
    have hne2 : -(2 * ((k : ℂ) + 1)) - 1 ≠ 0 := by
      intro h; apply hk3; linear_combination -h
    have hk3' : (3 : ℂ) + (k : ℂ) * 2 ≠ 0 := by intro h; apply hk3; linear_combination h
    have hk3'' : (3 : ℂ) + 2 * (k : ℂ) ≠ 0 := by intro h; apply hk3; linear_combination h
    have hne2' : (-3 : ℂ) - (k : ℂ) * 2 ≠ 0 := by intro h; apply hk3; linear_combination -h
    have hne2'' : (-3 : ℂ) - 2 * (k : ℂ) ≠ 0 := by intro h; apply hk3; linear_combination -h
    have hk2' : (2 : ℂ) + (k : ℂ) ≠ 0 := by intro h; apply hk2; linear_combination h
    have hk1' : (1 : ℂ) + (k : ℂ) ≠ 0 := by intro h; apply hk1; linear_combination h
    rw [hpow]
    generalize ((X : ℂ) ^ (2 * (k + 1)))⁻¹ = P
    rw [show -(2 * ((k : ℂ) + 1)) - 1 = -(2 * (k : ℂ) + 3) by ring]
    simp only [div_eq_mul_inv, mul_inv, inv_neg, neg_mul, mul_neg]
    ring
  simp_rw [hval]
  have h1 : HasSum (fun k : ℕ => ((X : ℂ) - 1) * (1 / ((k : ℂ) + 2) - 1 / ((k : ℂ) + 1)))
      (((X : ℂ) - 1) * -1) := by
    have h := (hasSum_digammaTelescoping.neg).mul_left ((X : ℂ) - 1)
    have hf : (fun k : ℕ => ((X : ℂ) - 1) * -(1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 2)))
        = fun k : ℕ => ((X : ℂ) - 1) * (1 / ((k : ℂ) + 2) - 1 / ((k : ℂ) + 1)) := by
      funext k; ring
    rwa [hf] at h
  have h2 := hasSum_inv_succ_mul_two_add_three.mul_left (X : ℂ)
  have h3 := (summable_trivialZeroSeriesTerm hX.le).hasSum.mul_left (2 : ℂ)
  have := ((h1.add h2).sub h3).tsum_eq
  rw [this]
  unfold trivialZeroSeries
  ring

theorem summable_cpow_div_zero {X : ℝ} (hX : 1 < X) :
    Summable (fun q : XiZeroCopy => (X : ℂ) ^ (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
  refine Summable.of_norm_bounded
    (g := fun q : XiZeroCopy => X * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)
    (summable_inv_mul_one_sub.norm.mul_left X) fun q => ?_
  rw [div_eq_mul_one_div, norm_mul]
  gcongr
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  calc X ^ ((q.1 : ℂ)).re ≤ X ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hX.le (xiZeroCopy_re_lt_one q).le
    _ = X := Real.rpow_one X

theorem tsum_integral_zTerm {X : ℝ} (hX : 1 < X) :
    ∑' q : XiZeroCopy, (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, zTerm X q t =
      ((X : ℂ) - 1) * (-((poleSharpConstant : ℂ) / 2)) -
        ∑' q : XiZeroCopy, (X : ℂ) ^ (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) +
        X * poleSharpConstant := by
  have hval : ∀ q : XiZeroCopy, (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, zTerm X q t =
      ((X : ℂ) - 1) * (1 / ((q.1 : ℂ) - 1 / 2) - 1 / (q.1 : ℂ)) -
        (X : ℂ) ^ (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) +
        X * (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
    intro q
    rw [integral_zTerm hX q]
    have hq := xiZeroCopy_sub_half_ne_zero q
    have h0 := xiZeroCopy_ne_zero q
    have h1 := xiZeroCopy_one_sub_ne_zero q
    have h1' : (q.1 : ℂ) - 1 ≠ 0 := by intro h; apply h1; linear_combination -h
    have h1'' : (-1 : ℂ) + (q.1 : ℂ) ≠ 0 := by intro h; apply h1; linear_combination -h
    have hq2 : (2 : ℂ) * (q.1 : ℂ) - 1 ≠ 0 := by intro h; apply hq; linear_combination h / 2
    have hq2' : (-1 : ℂ) + (q.1 : ℂ) * 2 ≠ 0 := by intro h; apply hq; linear_combination h / 2
    generalize (X : ℂ) ^ (q.1 : ℂ) = Q
    field_simp
    ring
  simp_rw [hval]
  have hA := summable_halfShift_pole.mul_left ((X : ℂ) - 1)
  have hB := summable_cpow_div_zero hX
  have hC := summable_inv_mul_one_sub.mul_left (X : ℂ)
  rw [Summable.tsum_add (hA.sub hB) hC, Summable.tsum_sub hA hB, tsum_mul_left, tsum_mul_left,
    tsum_halfShift_pole, tsum_inv_zero_mul_one_sub_zero]

/-! ## Assembly -/

/-- A countable family with summable norm-integrals has an integrable pointwise sum. -/
theorem integrable_tsum_of_summable_integral_norm' {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ}
    (hmeas : ∀ i, Measurable (F i)) (hint : ∀ i, Integrable (F i))
    (hsum : Summable fun i => ∫ t : ℝ, ‖F i t‖) : Integrable (fun t => ∑' i, F i t) := by
  refine ⟨(Measurable.tsum hmeas).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ t, ‖∑' i, F i t‖ₑ ≤ ∫⁻ t, ∑' i, ‖F i t‖ₑ :=
        lintegral_mono fun t => enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ t, ‖F i t‖ₑ := lintegral_tsum fun i => (hmeas i).enorm.aemeasurable
    _ = ∑' i, ENNReal.ofReal (∫ t, ‖F i t‖) := by
        simp_rw [ofReal_integral_norm_eq_lintegral_enorm (hint _)]
    _ = ENNReal.ofReal (∑' i, ∫ t, ‖F i t‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun _ => integral_nonneg fun _ => norm_nonneg _) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem smul_tsum_eq {ι : Type*} (c : ℝ) (f : ι → ℂ) :
    c • ∑' i, f i = ∑' i, c • f i := by
  rw [Complex.real_smul, ← tsum_mul_left]
  exact tsum_congr fun i => Complex.real_smul.symm

/-- **The Mittag-Leffler side.** -/
theorem mittagLeffler_side {X : ℝ} (hX : 1 < X) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo t) *
        lagKernel X t
      = ((X : ℂ) * Complex.log X - X + 1) +
        ((1 : ℂ) / 2 - (Real.log Real.pi : ℂ) / 2 - (Real.eulerMascheroniConstant : ℂ) / 2) *
          (X - 1) +
        (1 / 2 : ℂ) * (∑' k : ℕ, (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, kTerm X k t) -
        ∑' q : XiZeroCopy, (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, zTerm X q t := by
  have hX0 : 0 < X := by linarith
  set c₁ : ℂ := (1 : ℂ) / 2 - (Real.log Real.pi : ℂ) / 2 - (Real.eulerMascheroniConstant : ℂ) / 2
    with hc₁
  have hpt : ∀ t : ℝ, LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo t) * lagKernel X t =
      ((X : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1) ^ 2) + c₁ * lagKernel X t) +
        (1 / 2 : ℂ) * (∑' k : ℕ, kTerm X k t) - ∑' q : XiZeroCopy, zTerm X q t := by
    intro t
    rw [lseries_vonMangoldt_lineTwo t]
    unfold kTerm zTerm
    rw [tsum_mul_right, tsum_mul_right]
    unfold lagKernel
    have h0 := lineTwo_ne_zero t
    have h1 := lineTwo_sub_one_ne_zero t
    field_simp
    try ring
  simp_rw [hpt]
  have hA1 : Integrable (fun t : ℝ => (X : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1) ^ 2)) := by
    have := (integrable_lineTwo_sub_one_sq hX0).sub (integrable_lineTwo_basic hX0)
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    have h0 := lineTwo_ne_zero t
    have h1 := lineTwo_sub_one_ne_zero t
    simp only [Pi.sub_apply]
    field_simp
    try ring
  have hA2 := (integrable_lagKernel hX0).const_mul c₁
  have hTk : Integrable (fun t : ℝ => ∑' k : ℕ, kTerm X k t) :=
    integrable_tsum_of_summable_integral_norm' (fun k => (continuous_kTerm hX0 k).measurable)
      (integrable_kTerm hX0) (summable_integral_norm_kTerm hX0)
  have hTq : Integrable (fun t : ℝ => ∑' q : XiZeroCopy, zTerm X q t) :=
    integrable_tsum_of_summable_integral_norm' (fun q => (continuous_zTerm hX0 q).measurable)
      (integrable_zTerm hX0) (summable_integral_norm_zTerm hX0)
  have hS1 : Integrable (fun t : ℝ => (X : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1) ^ 2) +
      c₁ * lagKernel X t) := hA1.add hA2
  have hS2 : Integrable (fun t : ℝ => (X : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1) ^ 2) +
      c₁ * lagKernel X t + (1 / 2 : ℂ) * ∑' k : ℕ, kTerm X k t) := hS1.add (hTk.const_mul _)
  rw [integral_sub hS2 hTq, integral_add hS1 (hTk.const_mul _), integral_add hA1 hA2,
    integral_const_mul, integral_const_mul,
    ← integral_tsum_of_summable_integral_norm (integrable_kTerm hX0) (summable_integral_norm_kTerm hX0),
    ← integral_tsum_of_summable_integral_norm (integrable_zTerm hX0) (summable_integral_norm_zTerm hX0)]
  rw [smul_sub, smul_add, smul_add, ← mul_smul_comm, ← mul_smul_comm, perron_lineTwo_sub_one_sq hX]
  have hb := perron_lineTwo_basic hX0
  rw [if_pos hX] at hb
  unfold lagKernel
  rw [hb, smul_tsum_eq, smul_tsum_eq]

/-- **The explicit formula with the genus kernel `1/(s(1−s))`.**  For real `X > 1`,

`Σ_ρ X^ρ/(ρ(1−ρ)) = (X − ψ(X)) + X (Σ_{n≤X} Λ(n)/n − log X + γ) − log 2π + Σ_{k≥1} X^{−2k}/(2k(2k+1))`,

the sum on the left running over the nontrivial zeros of `ξ` with multiplicity (absolutely
convergent). -/
theorem lag_explicit_formula {X : ℝ} (hX : 1 < X) :
    ∑' q : XiZeroCopy, (X : ℂ) ^ (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
      ((X - Chebyshev.psi X : ℝ) : ℂ) +
        X * (((∑ n ∈ Finset.Icc 1 ⌊X⌋₊, vonMangoldt n / (n : ℝ) : ℝ) : ℂ) - Real.log X +
          Real.eulerMascheroniConstant) -
        Real.log (2 * Real.pi) + trivialZeroSeries X := by
  have hX0 : 0 < X := by linarith
  have hD := dirichlet_side hX
  have hM := mittagLeffler_side hX
  rw [tsum_integral_kTerm hX, tsum_integral_zTerm hX] at hM
  have hpsi : ((Chebyshev.psi X : ℝ) : ℂ) = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ((vonMangoldt n : ℝ) : ℂ) := by
    rw [Chebyshev.psi_eq_sum_Icc]
    push_cast
    symm
    apply Finset.sum_subset
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      exact ⟨by omega, hn.2⟩
    · intro n hn hn2
      rw [Finset.mem_Icc] at hn hn2
      have : n = 0 := by omega
      subst this
      simp
  have hfin : ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ((vonMangoldt n : ℝ) : ℂ) * ((X : ℂ) / n - 1) =
      X * ((∑ n ∈ Finset.Icc 1 ⌊X⌋₊, vonMangoldt n / (n : ℝ) : ℝ) : ℂ) -
        ((Chebyshev.psi X : ℝ) : ℂ) := by
    rw [hpsi]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hfin] at hD
  have hkey := hD.symm.trans hM
  have hlog2 : Complex.log 2 = (Real.log 2 : ℂ) := by
    have := Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)
    push_cast at this
    exact this.symm
  have hlogX : Complex.log X = (Real.log X : ℂ) := (Complex.ofReal_log hX0.le).symm
  have hlog2π : (Real.log (2 * Real.pi) : ℂ) = Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne']
    push_cast
    ring
  have hc₀ : (poleSharpConstant : ℂ) =
      2 + Real.eulerMascheroniConstant - (2 * Real.log 2 + Real.log Real.pi) := by
    unfold poleSharpConstant
    rw [show (4 * Real.pi : ℝ) = 2 ^ 2 * Real.pi by ring, Real.log_mul (by norm_num) Real.pi_pos.ne',
      Real.log_pow]
    push_cast
    ring
  rw [hlog2, hlogX, hc₀] at hkey
  rw [hlog2π, Complex.ofReal_sub]
  linear_combination -hkey

end

end RHTower

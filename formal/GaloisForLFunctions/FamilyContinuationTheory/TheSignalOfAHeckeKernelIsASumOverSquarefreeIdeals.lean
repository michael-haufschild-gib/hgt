import GaloisForLFunctions.FamilyContinuationTheory.TheSignalOfTheZetaKernelIsAMoebiusSum
import GaloisForLFunctions.FamilyContinuationTheory.TheContinuationFrameHoldsForHeckeLFunctions
import GaloisForLFunctions.RHTower.Deninger.DeningerPlaceCountable

/-!
# The signal of a Hecke kernel is a sum over squarefree ideals

* **A kernel times a Dirichlet series** (`signal_eq_tsum_of_hasSum`). If on the line `Re s = 2`
  the function `G` is the sum of the terms `a_i r_i^{−s} E(s)`, with `Σ |a_i| r_i^{−2} < ∞` and
  `E` decaying like `C/(1 + y²)` on the line, then
  `signal G 2 Z = Σ_i a_i · signal E 2 (Z / r_i)`: the signal of `E` is dilated by the scales.
* **The reciprocal of a Hecke `L`-series** (`hasSum_squarefree_inv_heckeL`). For `Re s > 1`,
  `1/L(s, ψ) = Σ_S (−1)^{|S|} ψ(∏ S) N(∏ S)^{−s}` over the finite sets `S` of primes: the Möbius
  series over the squarefree ideals, from the Euler product.
* **The signal** (`signal_heckeKernel_eq_tsum`). The signal of `exp((s − c)²)/L(s, ψ)` is
  `Σ_S (−1)^{|S|} ψ(∏ S) · w(Z / N(∏ S))`, `w` the signal of the Gaussian kernel: the smoothed
  Möbius sum of the character.
* **Zeros** (`heckeLFunction_ne_zero_of_squarefreeSum_le`). A bound `O(Z^b)`, `b < 1`, for that
  sum excludes the zeros of `L(s, ψ)` in `Re s > b`, for a nontrivial ray class character `ψ`.
-/

noncomputable section

open Complex MeasureTheory NumberField IsDedekindDomain
open scoped Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open HeckeLFunctions

/-! ### A kernel times a Dirichlet series -/

/-- A power of a quotient of positive reals. -/
theorem ofReal_div_cpow {Z r : ℝ} (hZ : 0 ≤ Z) (hr : 0 < r) (s : ℂ) :
    ((Z / r : ℝ) : ℂ) ^ s = (Z : ℂ) ^ s * (r : ℂ) ^ (-s) := by
  have hmul := mul_cpow_ofReal_nonneg (div_nonneg hZ hr.le) hr.le s
  have hZr : ((Z / r : ℝ) : ℂ) * ((r : ℝ) : ℂ) = (Z : ℂ) := by
    rw [← ofReal_mul, div_mul_cancel₀ _ hr.ne']
  rw [hZr] at hmul
  have hne : (r : ℂ) ^ s ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h => (ofReal_ne_zero.mpr hr.ne') h.1
  rw [cpow_neg, hmul]
  field_simp

/-- The term of a Dirichlet series in the signal: `a (Z/r)^s E(s)` on the line `Re s = 2`. -/
def dilatedTerm (E : ℂ → ℂ) (a : ℂ) (x : ℝ) (y : ℝ) : ℂ :=
  a * ((x : ℂ) ^ linePoint y • E (linePoint y))

theorem norm_dilatedTerm_le {E : ℂ → ℂ} {C : ℝ}
    (hE : ∀ y : ℝ, ‖E (linePoint y)‖ ≤ C * (1 + y ^ 2)⁻¹) (a : ℂ) {x : ℝ} (hx : 0 < x)
    (y : ℝ) : ‖dilatedTerm E a x y‖ ≤ ‖a‖ * x ^ 2 * C * (1 + y ^ 2)⁻¹ := by
  have hpow : ‖(x : ℂ) ^ linePoint y‖ = x ^ 2 := by
    rw [norm_cpow_eq_rpow_re_of_pos hx, linePoint_re]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  unfold dilatedTerm
  rw [norm_mul, norm_smul, hpow]
  calc ‖a‖ * (x ^ 2 * ‖E (linePoint y)‖) ≤ ‖a‖ * (x ^ 2 * (C * (1 + y ^ 2)⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hE y) (by positivity))
          (norm_nonneg _)
    _ = ‖a‖ * x ^ 2 * C * (1 + y ^ 2)⁻¹ := by ring

theorem continuous_dilatedTerm {E : ℂ → ℂ} (hEc : Continuous fun y : ℝ => E (linePoint y))
    (a : ℂ) {x : ℝ} (hx : 0 < x) : Continuous (dilatedTerm E a x) := by
  have hbase : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  unfold dilatedTerm
  refine continuous_const.mul (Continuous.smul (f := fun y : ℝ => (x : ℂ) ^ linePoint y)
    (g := fun y : ℝ => E (linePoint y)) ?_ hEc)
  exact continuous_linePoint.const_cpow (Or.inl hbase)

/-- **The signal of a kernel times a Dirichlet series.** -/
theorem signal_eq_tsum_of_hasSum {ι : Type*} [Countable ι] {E G : ℂ → ℂ} {a : ι → ℂ}
    {r : ι → ℝ} {C : ℝ} (hr : ∀ i, 0 < r i)
    (hEc : Continuous fun y : ℝ => E (linePoint y))
    (hE : ∀ y : ℝ, ‖E (linePoint y)‖ ≤ C * (1 + y ^ 2)⁻¹)
    (ha : Summable fun i => ‖a i‖ * (1 / r i ^ 2))
    (hG : ∀ y : ℝ, HasSum (fun i => a i * (r i : ℂ) ^ (-linePoint y) * E (linePoint y))
      (G (linePoint y)))
    {Z : ℝ} (hZ : 0 < Z) :
    signal G 2 Z = ∑' i, a i * signal E 2 (Z / r i) := by
  have hpos : ∀ i, 0 < Z / r i := fun i => div_pos hZ (hr i)
  have hbound : ∀ i y, ‖dilatedTerm E (a i) (Z / r i) y‖ ≤
      ‖a i‖ * (1 / r i ^ 2) * (Z ^ 2 * C) * (1 + y ^ 2)⁻¹ := by
    intro i y
    refine (norm_dilatedTerm_le hE (a i) (hpos i) y).trans (le_of_eq ?_)
    rw [div_pow]
    ring
  have hdom : ∀ i, Integrable fun y : ℝ =>
      ‖a i‖ * (1 / r i ^ 2) * (Z ^ 2 * C) * (1 + y ^ 2)⁻¹ :=
    fun i => integrable_inv_one_add_sq.const_mul _
  have hint : ∀ i, Integrable (dilatedTerm E (a i) (Z / r i)) := fun i =>
    (hdom i).mono' (continuous_dilatedTerm hEc (a i) (hpos i)).aestronglyMeasurable
      (Filter.Eventually.of_forall (hbound i))
  have hsumm : Summable fun i => ∫ y : ℝ, ‖dilatedTerm E (a i) (Z / r i) y‖ := by
    have hle : ∀ i, ∫ y : ℝ, ‖dilatedTerm E (a i) (Z / r i) y‖ ≤
        ‖a i‖ * (1 / r i ^ 2) * (Z ^ 2 * C * Real.pi) := by
      intro i
      have h := integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
        (hdom i) (Filter.Eventually.of_forall (hbound i))
      rw [integral_const_mul, integral_univ_inv_one_add_sq] at h
      calc ∫ y : ℝ, ‖dilatedTerm E (a i) (Z / r i) y‖
          ≤ ‖a i‖ * (1 / r i ^ 2) * (Z ^ 2 * C) * Real.pi := h
        _ = ‖a i‖ * (1 / r i ^ 2) * (Z ^ 2 * C * Real.pi) := by ring
    exact Summable.of_nonneg_of_le (fun i => integral_nonneg fun y => norm_nonneg _) hle
      (ha.mul_right _)
  have hswap := integral_tsum_of_summable_integral_norm hint hsumm
  have hpoint : (fun y : ℝ => ∑' i, dilatedTerm E (a i) (Z / r i) y) =
      fun y : ℝ => (Z : ℂ) ^ linePoint y • G (linePoint y) := by
    funext y
    have h := (hG y).mul_left ((Z : ℂ) ^ linePoint y)
    have hfun : (fun i => (Z : ℂ) ^ linePoint y *
        (a i * (r i : ℂ) ^ (-linePoint y) * E (linePoint y))) =
        fun i => dilatedTerm E (a i) (Z / r i) y := by
      funext i
      unfold dilatedTerm
      rw [smul_eq_mul, ofReal_div_cpow hZ.le (hr i)]
      ring
    rw [hfun] at h
    rw [smul_eq_mul]
    exact h.tsum_eq
  rw [hpoint] at hswap
  rw [signal_two_eq_integral, ← hswap, ← tsum_const_smul'']
  refine tsum_congr fun i => ?_
  rw [signal_two_eq_integral]
  unfold dilatedTerm
  rw [integral_const_mul, mul_smul_comm]

/-! ### The Gaussian kernel -/

/-- The Gaussian kernel with centre `c`: `exp((s − c)²)`. -/
def gaussKernel (c : ℝ) (s : ℂ) : ℂ := cexp ((s - c) ^ 2)

theorem continuous_gaussKernel_linePoint (c : ℝ) :
    Continuous fun y : ℝ => gaussKernel c (linePoint y) := by
  unfold gaussKernel
  exact ((continuous_linePoint.sub continuous_const).pow 2).cexp

theorem norm_gaussKernel_linePoint_le (c : ℝ) (y : ℝ) :
    ‖gaussKernel c (linePoint y)‖ ≤ Real.exp ((2 - c) ^ 2) * (1 + y ^ 2)⁻¹ := by
  unfold gaussKernel
  rw [norm_cexp_sub_sq, linePoint_re, linePoint_im, neg_sq, sub_eq_add_neg, Real.exp_add]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [Real.exp_neg]
  refine inv_anti₀ (by positivity) ?_
  linarith [Real.add_one_le_exp (y ^ 2)]

/-! ### The reciprocal of a Hecke `L`-series -/

variable {K : Type*} [Field K] [NumberField K]
variable (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)

/-- The coefficient of a finite set of primes: `(−1)^{|S|} ψ(∏ S)`. -/
def squarefreeCoeff (S : Finset (HeightOneSpectrum (𝓞 K))) : ℂ :=
  ∏ v ∈ S, -heckeValue 𝔪 ψ v.asIdeal

/-- The norm of the product of a finite set of primes. -/
def squarefreeNorm (S : Finset (HeightOneSpectrum (𝓞 K))) : ℕ :=
  ∏ v ∈ S, Ideal.absNorm v.asIdeal

theorem squarefreeNorm_pos (S : Finset (HeightOneSpectrum (𝓞 K))) : 0 < squarefreeNorm S :=
  Finset.prod_pos fun v _ => Nat.pos_of_ne_zero fun h =>
    v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)

theorem norm_squarefreeCoeff_le (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ‖squarefreeCoeff 𝔪 ψ S‖ ≤ 1 := by
  unfold squarefreeCoeff
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun v _ => by
    rw [norm_neg]
    exact norm_heckeValue_le_one 𝔪 ψ _

/-- The product of the prime terms over a finite set of primes. -/
theorem prod_neg_heckePrimeTerm (s : ℂ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∏ v ∈ S, -heckePrimeTerm 𝔪 ψ s v =
      squarefreeCoeff 𝔪 ψ S * ((squarefreeNorm S : ℝ) : ℂ) ^ (-s) := by
  have key : ∏ v ∈ S, -heckePrimeTerm 𝔪 ψ s v =
      (∏ v ∈ S, -heckeValue 𝔪 ψ v.asIdeal) *
        ((∏ v ∈ S, Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert v S hv ih =>
      rw [Finset.prod_insert hv, Finset.prod_insert hv, Finset.prod_insert hv, ih,
        Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      unfold heckePrimeTerm
      ring
  unfold squarefreeCoeff squarefreeNorm
  rw [key, Complex.ofReal_natCast]

/-- **The Möbius series of a Hecke character.** For `Re s > 1` the reciprocal of the `L`-series
is the sum over the finite sets of primes of `(−1)^{|S|} ψ(∏ S) N(∏ S)^{−s}`. -/
theorem hasSum_squarefree_inv_heckeL {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      squarefreeCoeff 𝔪 ψ S * ((squarefreeNorm S : ℝ) : ℂ) ^ (-s)) (heckeL 𝔪 ψ s)⁻¹ := by
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 K) => ‖-heckePrimeTerm 𝔪 ψ s v‖ := by
    simpa only [norm_neg] using summable_norm_heckePrimeTerm 𝔪 ψ hs
  have hS : Summable fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      ∏ v ∈ S, -heckePrimeTerm 𝔪 ψ s v := summable_finsetProd_of_summable_norm hsum
  have hprod : ∏' v : HeightOneSpectrum (𝓞 K), (1 + -heckePrimeTerm 𝔪 ψ s v) =
      ∑' S : Finset (HeightOneSpectrum (𝓞 K)), ∏ v ∈ S, -heckePrimeTerm 𝔪 ψ s v :=
    tprod_one_add hS
  have hinv : (heckeL 𝔪 ψ s)⁻¹ =
      ∏' v : HeightOneSpectrum (𝓞 K), (1 + -heckePrimeTerm 𝔪 ψ s v) := by
    have h := heckeEulerDenominatorProduct_mul_heckeL 𝔪 ψ hs
    simp only [sub_eq_add_neg] at h
    exact (eq_inv_of_mul_eq_one_left h).symm
  have h := hS.hasSum
  rw [← hprod, ← hinv] at h
  simpa only [prod_neg_heckePrimeTerm] using h

/-! ### The signal -/

/-- **The signal of a Hecke kernel is a sum over the squarefree ideals.** -/
theorem signal_heckeKernel_eq_tsum (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    signal (heckeKernel 𝔪 ψ c) 2 Z =
      ∑' S : Finset (HeightOneSpectrum (𝓞 K)),
        squarefreeCoeff 𝔪 ψ S * signal (gaussKernel c) 2 (Z / squarefreeNorm S) := by
  haveI : Countable (HeightOneSpectrum (𝓞 K)) := _root_.RHTower.deningerHeightOneSpectrum_countable K
  have hr : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), (0 : ℝ) < (squarefreeNorm S : ℝ) :=
    fun S => Nat.cast_pos.mpr (squarefreeNorm_pos S)
  -- summability of the coefficients against `N^{−2}`
  have hN : Summable fun v : HeightOneSpectrum (𝓞 K) => ((v.asIdeal.absNorm : ℝ) ^ 2)⁻¹ := by
    have h := numberField_summable_finitePlace_norm_cpow (K := K) (s := 2) (by norm_num)
    simpa only [norm_absNorm_cpow_neg_two] using h
  have hprodN : Summable fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      ∏ v ∈ S, ((v.asIdeal.absNorm : ℝ) ^ 2)⁻¹ :=
    summable_finsetProd_of_summable_nonneg (fun _ => by positivity) hN
  have ha : Summable fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      ‖squarefreeCoeff 𝔪 ψ S‖ * (1 / (squarefreeNorm S : ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun S => by positivity) (fun S => ?_) hprodN
    have heq : 1 / (squarefreeNorm S : ℝ) ^ 2 = ∏ v ∈ S, ((v.asIdeal.absNorm : ℝ) ^ 2)⁻¹ := by
      unfold squarefreeNorm
      rw [one_div, Nat.cast_prod, ← Finset.prod_pow, Finset.prod_inv_distrib]
    rw [heq]
    exact mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => by positivity)
      (norm_squarefreeCoeff_le 𝔪 ψ S)
  refine signal_eq_tsum_of_hasSum (E := gaussKernel c) hr (continuous_gaussKernel_linePoint c)
    (norm_gaussKernel_linePoint_le c) ha (fun y => ?_) hZ
  have hre : 1 < (linePoint y).re := by rw [linePoint_re]; norm_num
  have h := (hasSum_squarefree_inv_heckeL 𝔪 ψ hre).mul_right (gaussKernel c (linePoint y))
  have hval : (heckeL 𝔪 ψ (linePoint y))⁻¹ * gaussKernel c (linePoint y) =
      heckeKernel 𝔪 ψ c (linePoint y) := by
    unfold heckeKernel gaussKernel
    rw [heckeLFunction_eq_heckeL 𝔪 ψ hre, div_eq_mul_inv, mul_comm]
  rwa [hval] at h

/-- **Zeros.** For a nontrivial ray class character, a bound `O(Z^b)`, `b < 1`, for the smoothed
Möbius sum over the squarefree ideals excludes the zeros of `L(s, ψ)` in `Re s > b`. -/
theorem heckeLFunction_ne_zero_of_squarefreeSum_le {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1)
    {c b C Z₀ : ℝ} (hb : b < 1) (hZ₀ : 0 < Z₀)
    (hC : ∀ Z : ℝ, Z₀ ≤ Z → ‖∑' S : Finset (HeightOneSpectrum (𝓞 K)),
      squarefreeCoeff 𝔪 ψ S * signal (gaussKernel c) 2 (Z / squarefreeNorm S)‖ ≤ C * Z ^ b)
    (ρ : ℂ) (hρ : b < ρ.re) : heckeLFunction 𝔪 ψ ρ ≠ 0 :=
  heckeLFunction_ne_zero_of_signal_le hψ hb hZ₀
    (fun Z hZ => by
      rw [signal_heckeKernel_eq_tsum 𝔪 ψ c (lt_of_lt_of_le hZ₀ hZ)]
      exact hC Z hZ) ρ hρ

end GaloisForLFunctions.FamilyContinuationTheory

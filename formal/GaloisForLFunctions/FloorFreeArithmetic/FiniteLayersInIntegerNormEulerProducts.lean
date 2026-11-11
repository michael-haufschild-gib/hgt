import GaloisForLFunctions.FloorFreeArithmetic.FiniteLayersInDiscreteEulerProducts
import GaloisForLFunctions.ArithmeticPositiveDuality.AnIntegerNormOneOffCrossesTheCriticalLine

/-!
# Finite layers in integer-norm Euler products

Round each discrete prime `p_k = e^{t_k}` of a prime density upward to a natural number
`q_k = ⌈p_k⌉ ≥ 2`. The logarithm changes by at most `1/p_k`, so the difference of the prime sums
is holomorphic on `Re s > 0`, and the prime-power remainder of the rounded primes is holomorphic
on `Re s > ½`. The Euler product over the natural norms `q_k` is therefore the zeta function of
the density times a factor that is holomorphic and without zeros on `Re s > ½`.

For the density of a layer this gives, for every `½ < Θ < 1`, all ordinates `γ_j` and all
multiplicities `m_j`:

* natural norms `q_k ≥ 2` and a function `G` holomorphic on `Re s > ½`;
* `∏_k (1 − q_k^{−s})^{−1} = Σ_n a_n n^{−s} = G(s)/(s − 1)` on `Re s > 1`, with natural
  coefficients `a_n`;
* `G` vanishes on `Re s > ½` exactly at the points `Θ ± iγ_j` with `m_j ≠ 0`;
* linear counting `Σ_{n<N} a_n ∼ A N` with `A > 0`.

So an Euler product with natural norms, natural coefficients, a simple pole and linear counting
can have any prescribed finite set of zeros right of the critical line, at every depth below
`½`, and no others there. Multiplicativity, positivity and integrality of the coefficients put
no condition on a finite top layer.

* `PrimeDensity.genEulerLog_primeNorm_eq`: the Euler logarithm of the rounded primes.
* `exists_integer_norm_euler_product_with_layer`: the realization theorem.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff
open GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

namespace PrimeDensity

variable (P : PrimeDensity)

/-! ### Rounding the discrete primes to natural norms -/

/-- The natural norm of the `k`-th discrete prime, rounded upward. -/
def primeNorm (k : ℕ) : ℕ := ⌈Real.exp (P.atom k)⌉₊

/-- The logarithm of the rounded norm. -/
def roundedAtom (k : ℕ) : ℝ := roundedLog (P.atom k)

theorem two_le_primeNorm (k : ℕ) : 2 ≤ P.primeNorm k := by
  have h : (1 : ℝ) < Real.exp (P.atom k) := Real.one_lt_exp_iff.mpr (P.atom_pos k)
  have h1 : 1 < P.primeNorm k := Nat.lt_ceil.mpr (by exact_mod_cast h)
  exact h1

theorem atom_le_roundedAtom (k : ℕ) : P.atom k ≤ P.roundedAtom k := (roundedLog_bounds _).1

theorem roundedAtom_le (k : ℕ) : P.roundedAtom k ≤ P.atom k + Real.exp (-(P.atom k)) :=
  (roundedLog_bounds _).2

theorem roundedAtom_pos (k : ℕ) : 0 < P.roundedAtom k :=
  (P.atom_pos k).trans_le (P.atom_le_roundedAtom k)

theorem roundedAtom_zero_le (k : ℕ) : P.roundedAtom 0 ≤ P.roundedAtom k :=
  roundedLog_mono (P.atom_zero_le k)

theorem summable_exp_roundedAtom {a : ℝ} (ha : 1 < a) :
    Summable fun k => Real.exp (-(a * P.roundedAtom k)) := by
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun k => ?_)
    (P.summable_exp_atom ha)
  have h := mul_le_mul_of_nonneg_left (P.atom_le_roundedAtom k) (by linarith only [ha] : 0 ≤ a)
  exact Real.exp_le_exp.mpr (by linarith only [h])

/-- The correction between the Euler logarithm of the rounded primes and the Laplace transform
of the density: the Laplace transform of `N − W`, the change of the prime sum under rounding,
and the prime-power remainder of the rounded primes. -/
def roundedCorrection (s : ℂ) : ℂ :=
  s * boundedLaplace P.discrepancy s + primeCorrection P.atom P.roundedAtom s +
    primePowerRemainder P.roundedAtom s

/-- **The correction is holomorphic on `Re s > ½`.** -/
theorem differentiableOn_roundedCorrection :
    DifferentiableOn ℂ P.roundedCorrection {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  have hs' : 1 / 2 < s.re := hs
  have hopen0 : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hpos : s ∈ {s : ℂ | 0 < s.re} := by
    show 0 < s.re
    linarith only [hs']
  have hΛ : DifferentiableAt ℂ (boundedLaplace P.discrepancy) s :=
    (differentiableOn_boundedLaplace P.measurable_discrepancy
      P.abs_discrepancy_le).differentiableAt (hopen0.mem_nhds hpos)
  have hC : DifferentiableAt ℂ (primeCorrection P.atom P.roundedAtom) s :=
    (differentiableOn_primeCorrection P.atom_pos P.atom_le_roundedAtom P.roundedAtom_le
      (fun a ha => P.summable_exp_atom ha)).differentiableAt (hopen0.mem_nhds hpos)
  have hR : DifferentiableAt ℂ (primePowerRemainder P.roundedAtom) s :=
    (differentiableOn_primePowerRemainder P.roundedAtom_pos P.roundedAtom_zero_le
      (fun a ha => P.summable_exp_roundedAtom ha)).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs')
  exact (((differentiableAt_id.mul hΛ).add hC).add hR).differentiableWithinAt

/-- The prime sum of the discrete primes is the Laplace transform of the density plus the
Laplace transform of the discrepancy. -/
theorem tsum_cexp_atom {s : ℂ} (hs : 1 < s.re) :
    ∑' k, cexp (-(s * P.atom k)) = (∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * (P.w u : ℂ)) +
      s * boundedLaplace P.discrepancy s := by
  have h1 := P.eulerLog_eq hs
  have h2 := tsum_neg_log_eq P.atom_pos P.atom_zero_le (fun a ha => P.summable_exp_atom ha) hs
  rw [eulerLog, h2, correction] at h1
  linear_combination h1

/-- **The Euler logarithm of the rounded primes** is the Laplace transform of the density plus
the correction, on `Re s > 1`. -/
theorem genEulerLog_primeNorm_eq {s : ℂ} (hs : 1 < s.re) :
    genEulerLog P.primeNorm s =
      (∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * (P.w u : ℂ)) + P.roundedCorrection s := by
  have hu := tsum_neg_log_eq P.roundedAtom_pos P.roundedAtom_zero_le
    (fun a ha => P.summable_exp_roundedAtom ha) hs
  obtain ⟨hsu, -⟩ := summable_neg_log P.roundedAtom_pos P.roundedAtom_zero_le
    (fun a ha => P.summable_exp_roundedAtom ha) hs
  obtain ⟨hst, -⟩ := summable_neg_log P.atom_pos P.atom_zero_le
    (fun a ha => P.summable_exp_atom ha) hs
  have hcorr : primeCorrection P.atom P.roundedAtom s =
      (∑' k, cexp (-(s * P.roundedAtom k))) - ∑' k, cexp (-(s * P.atom k)) := by
    rw [primeCorrection, hsu.tsum_sub hst]
  have hgen : genEulerLog P.primeNorm s =
      ∑' k, -Complex.log (1 - cexp (-(s * P.roundedAtom k))) := rfl
  rw [hgen, hu, roundedCorrection, hcorr, P.tsum_cexp_atom hs]
  ring

end PrimeDensity

/-! ### The realization theorem -/

variable {ι : Type*} [Fintype ι]

/-- **Integer-norm Euler products admit every finite layer.** For `½ < Θ < 1`, ordinates `γ_j`
and multiplicities `m_j` there are natural norms `q_k ≥ 2` and a function `G` holomorphic on
`Re s > ½` such that, on `Re s > 1`, the Euler product `∏_k (1 − q_k^{−s})^{−1}` converges to
`G(s)/(s − 1)` and is the Dirichlet series `Σ_n a_n n^{−s}` with the natural coefficients
`a_n = genCoeff q n`; `G` vanishes on `Re s > ½` exactly at the points `Θ ± iγ_j` with
`m_j ≠ 0`; and `Σ_{n<N} a_n / N` tends to a positive limit. -/
theorem exists_integer_norm_euler_product_with_layer {Θ : ℝ} (h0 : 1 / 2 < Θ) (h1 : Θ < 1)
    (γ : ι → ℝ) (m : ι → ℕ) :
    ∃ (q : ℕ → ℕ) (G : ℂ → ℂ), (∀ k, 2 ≤ q k) ∧
      DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (G s / (s - 1)) ∧
        LSeriesHasSum (fun n => (genCoeff q n : ℂ)) s (G s / (s - 1))) ∧
      (∀ s : ℂ, 1 / 2 < s.re →
        (G s = 0 ↔ ∃ j, m j ≠ 0 ∧ (s = (Θ : ℂ) + γ j * I ∨ s = (Θ : ℂ) - γ j * I))) ∧
      ∃ A : ℝ, 0 < A ∧
        Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (genCoeff q n : ℝ)) / N) atTop (𝓝 A) := by
  have hΘ0 : 0 < Θ := by linarith only [h0]
  obtain ⟨P, hP⟩ : ∃ P : PrimeDensity, P = layerPrimeDensity hΘ0 h1 γ m := ⟨_, rfl⟩
  have hw : P.w = layerLogDensity Θ γ m := by rw [hP]; rfl
  have hmono : ∀ k, Real.log (P.primeNorm 0) ≤ Real.log (P.primeNorm k) :=
    P.roundedAtom_zero_le
  have hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * Real.log (P.primeNorm k))) :=
    fun a ha => P.summable_exp_roundedAtom ha
  -- the Euler product is the regular factor over `s − 1`
  have hF : ∀ s : ℂ, 1 < s.re → cexp (genEulerLog P.primeNorm s) =
      layerRegular Θ γ m s * cexp (P.roundedCorrection s) / (s - 1) := by
    intro s hs
    rw [P.genEulerLog_primeNorm_eq hs, Complex.exp_add, hw, cexp_layer_eq h1 γ m hs]
    ring
  have hG : DifferentiableOn ℂ (fun s => layerRegular Θ γ m s * cexp (P.roundedCorrection s))
      {s : ℂ | 1 / 2 < s.re} :=
    (differentiable_layerRegular h1 γ m).differentiableOn.mul
      P.differentiableOn_roundedCorrection.cexp
  have hzero : ∀ s : ℂ, (layerRegular Θ γ m s * cexp (P.roundedCorrection s) = 0 ↔
      ∃ j, m j ≠ 0 ∧ (s = (Θ : ℂ) + γ j * I ∨ s = (Θ : ℂ) - γ j * I)) := fun s => by
    rw [mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), layerRegular_eq_zero_iff]
  -- the regular factor does not vanish at the pole
  have hG1 : layerRegular Θ γ m 1 * cexp (P.roundedCorrection 1) ≠ 0 := by
    rw [Ne, hzero]
    rintro ⟨j, -, h | h⟩
    · have hr := congrArg Complex.re h
      simp only [Complex.one_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero] at hr
      linarith only [hr, h1]
    · have hr := congrArg Complex.re h
      simp only [Complex.one_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero] at hr
      linarith only [hr, h1]
  obtain ⟨A, hA, -, hcount⟩ := tendsto_genCoeff_count P.two_le_primeNorm hmono hsum
    (by norm_num : (1 / 2 : ℝ) < 1) hG hG1 hF
  refine ⟨P.primeNorm, fun s => layerRegular Θ γ m s * cexp (P.roundedCorrection s),
    P.two_le_primeNorm, hG, fun s hs => ⟨?_, ?_⟩, fun s _ => hzero s, A, hA, hcount⟩
  · have hprod := hasProd_euler P.roundedAtom_pos P.roundedAtom_zero_le
      (fun a ha => P.summable_exp_roundedAtom ha) hs
    have hval : cexp (∑' k, -Complex.log (1 - cexp (-(s * P.roundedAtom k)))) =
        layerRegular Θ γ m s * cexp (P.roundedCorrection s) / (s - 1) := hF s hs
    rw [hval] at hprod
    exact hprod
  · have hser := hasSum_genCoeff P.two_le_primeNorm hmono hsum hs
    rw [hF s hs] at hser
    exact hser

end GaloisForLFunctions.FloorFreeArithmetic

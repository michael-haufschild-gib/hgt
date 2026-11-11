import GaloisForLFunctions.FloorFreeArithmetic.FiniteLayersInIntegerNormEulerProducts
import GaloisForLFunctions.ArithmeticPositiveDuality.ARationalPrimeBeurlingOneOff

/-!
# Finite layers in Euler products over the rational primes

Round each discrete prime `p_k = e^{t_k}` of a prime density to the next rational prime `q_k`.
A prime lies in `(x, x + x^α]` for every `α > 17/30` and all large `x`, so the logarithm moves
by at most `p_k^{−(1−α)}`, and the change of the prime sums is holomorphic on `Re s > 17/30`.
The Euler product `∏_k (1 − q_k^{−s})^{−1}`, in which a rational prime may occur several times,
is the zeta function of the density times a factor holomorphic and without zeros on
`Re s > 17/30`.

For the density of a layer with `17/30 < Θ < 1` this gives an Euler product over the rational
primes with natural exponents — the Dirichlet series of a nonnegative multiplicative function
on the integers — equal to `G(s)/(s − 1)` on `Re s > 1`, with `G` holomorphic on `Re s > 17/30`
and vanishing there exactly at the points `Θ ± iγ_j` with `m_j ≠ 0`.

* `PrimeDensity.tsum_neg_log_primeAtom_eq`: the Euler logarithm of the rounded primes.
* `exists_rational_prime_euler_product_with_layer`: the realization theorem.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff
open GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff
open GaloisForLFunctions.ArithmeticPositiveDuality.RationalPrimeOneOff

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

namespace PrimeDensity

variable (P : PrimeDensity)

/-! ### Rounding the discrete primes to rational primes -/

/-- The rational prime following the `k`-th discrete prime. -/
def rationalPrime (k : ℕ) : ℕ := nextPrime (Real.exp (P.atom k))

/-- Its logarithm. -/
def primeAtom (k : ℕ) : ℝ := Real.log (P.rationalPrime k)

theorem rationalPrime_prime (k : ℕ) : (P.rationalPrime k).Prime := nextPrime_prime _

theorem atom_le_primeAtom (k : ℕ) : P.atom k ≤ P.primeAtom k := by
  apply (Real.le_log_iff_exp_le (by exact_mod_cast (P.rationalPrime_prime k).pos)).2
  exact le_nextPrime _

theorem primeAtom_pos (k : ℕ) : 0 < P.primeAtom k :=
  (P.atom_pos k).trans_le (P.atom_le_primeAtom k)

theorem primeAtom_zero_le (k : ℕ) : P.primeAtom 0 ≤ P.primeAtom k := by
  apply Real.log_le_log (by exact_mod_cast (P.rationalPrime_prime 0).pos)
  exact_mod_cast nextPrime_mono (Real.exp_le_exp.mpr (P.atom_zero_le k))

theorem summable_exp_primeAtom {a : ℝ} (ha : 1 < a) :
    Summable fun k => Real.exp (-(a * P.primeAtom k)) := by
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_)
    (P.summable_exp_atom ha)
  exact Real.exp_le_exp.mpr (by nlinarith only [ha, P.atom_le_primeAtom k])

/-- The discrete primes escape every bound. -/
theorem tendsto_atom : Tendsto P.atom atTop atTop := by
  apply tendsto_atTop.2
  intro b
  refine eventually_atTop.2 ⟨⌈P.W (max b 0)⌉₊ + 1, ?_⟩
  intro k hk
  have hk' : P.W (max b 0) < (k : ℝ) + 1 := by
    have hc := Nat.le_ceil (P.W (max b 0))
    have hn : (⌈P.W (max b 0)⌉₊ : ℝ) + 1 ≤ k := by exact_mod_cast hk
    linarith only [hc, hn]
  have ha : max b 0 < P.atom k := by
    by_contra h
    have := (P.atom_le_iff k (max b 0)).1 (le_of_not_gt h)
    linarith only [this, hk']
  exact (le_max_left b 0).trans ha.le

/-- Prime gaps give an exponentially small displacement of the logarithmic norms. -/
theorem eventually_primeAtom_sub_le {α : ℝ} (hα : 17 / 30 < α) (hα1 : α < 1) :
    ∀ᶠ k : ℕ in atTop, P.primeAtom k - P.atom k ≤ Real.exp (-((1 - α) * P.atom k)) := by
  have he := (Real.tendsto_exp_atTop.comp P.tendsto_atom).eventually
    (_root_.RHTower.eventually_exists_prime_short_interval_seventeenThirtieths hα hα1)
  filter_upwards [he] with k hk
  obtain ⟨p, hp, hlow, hhigh⟩ := hk
  have hq : (P.rationalPrime k : ℝ) ≤ Real.exp (P.atom k) + Real.exp (P.atom k) ^ α := by
    have hqp : (P.rationalPrime k : ℝ) ≤ p := by exact_mod_cast nextPrime_le hp hlow.le
    exact hqp.trans hhigh
  have hp0 : (0 : ℝ) < P.rationalPrime k := by exact_mod_cast (P.rationalPrime_prime k).pos
  have ht0 := Real.exp_pos (P.atom k)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hp0 ht0)
  rw [Real.log_div hp0.ne' ht0.ne', Real.log_exp] at hlog
  have hratio : (P.rationalPrime k : ℝ) / Real.exp (P.atom k) - 1 ≤
      Real.exp (P.atom k) ^ α / Real.exp (P.atom k) := by
    apply (sub_le_iff_le_add).2
    apply (div_le_iff₀ ht0).2
    simpa only [add_mul, one_mul, div_mul_cancel₀ _ ht0.ne', add_comm] using hq
  have hexp : Real.exp (P.atom k) ^ α / Real.exp (P.atom k) =
      Real.exp (-((1 - α) * P.atom k)) := by
    rw [Real.rpow_def_of_pos ht0, Real.log_exp, ← Real.exp_sub]
    congr 1
    ring
  exact hlog.trans (hexp ▸ hratio)

theorem summable_displacement {a : ℝ} (ha : 17 / 30 < a) :
    Summable fun k => Real.exp (-(a * P.atom k)) * (P.primeAtom k - P.atom k) := by
  set α : ℝ := (17 / 30 + min a 1) / 2
  have hmin : 17 / 30 < min a 1 := lt_min ha (by norm_num)
  have hα : 17 / 30 < α ∧ α < min a 1 := by
    dsimp only [α]
    constructor <;> linarith only [hmin]
  have hαa : α < a := hα.2.trans_le (min_le_left _ _)
  have hα1 : α < 1 := hα.2.trans_le (min_le_right _ _)
  apply (P.summable_exp_atom (a := a + 1 - α)
    (by linarith only [hαa])).of_norm_bounded_eventually_nat
  filter_upwards [P.eventually_primeAtom_sub_le hα.1 hα1] with k hk
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le
    (sub_nonneg.mpr (P.atom_le_primeAtom k)))]
  calc
    _ ≤ Real.exp (-(a * P.atom k)) * Real.exp (-((1 - α) * P.atom k)) :=
      mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le
    _ = Real.exp (-((a + 1 - α) * P.atom k)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The change of the prime sum under rounding to rational primes is holomorphic on
`Re s > 17/30`. -/
theorem differentiableOn_primeCorrection_primeAtom :
    DifferentiableOn ℂ (primeCorrection P.atom P.primeAtom) {s : ℂ | 17 / 30 < s.re} := by
  intro s hs
  change 17 / 30 < s.re at hs
  set σ₀ : ℝ := (s.re + 17 / 30) / 2
  set M : ℝ := ‖s‖ + 1
  have hσ₀ : 17 / 30 < σ₀ := by dsimp only [σ₀]; linarith only [hs]
  have hM : 0 < M := by dsimp only [M]; positivity
  set U : Set ℂ := {z : ℂ | σ₀ < z.re ∧ ‖z‖ < M}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hsU : s ∈ U := by
    constructor
    · dsimp only [σ₀]; linarith only [hs]
    · dsimp only [M]; linarith
  have hdiff : ∀ k, DifferentiableOn ℂ
      (fun z : ℂ => cexp (-(z * P.primeAtom k)) - cexp (-(z * P.atom k))) U := by
    intro k
    exact (by fun_prop : Differentiable ℂ
      (fun z : ℂ => cexp (-(z * P.primeAtom k)) - cexp (-(z * P.atom k)))).differentiableOn
  have hbound : ∀ k (z : ℂ), z ∈ U →
      ‖cexp (-(z * P.primeAtom k)) - cexp (-(z * P.atom k))‖ ≤
        M * (Real.exp (-(σ₀ * P.atom k)) * (P.primeAtom k - P.atom k)) := by
    intro k z hz
    have hz0 : 0 ≤ z.re := by linarith only [hσ₀, hz.1]
    refine (norm_primeTerm_sub_le_displacement (P.atom_le_primeAtom k) hz0).trans ?_
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr (P.atom_le_primeAtom k))
    exact mul_le_mul hz.2.le (Real.exp_le_exp.mpr (by
      nlinarith only [hz.1, P.atom_pos k])) (Real.exp_pos _).le hM.le
  have hD := differentiableOn_tsum_of_summable_norm
    ((P.summable_displacement hσ₀).mul_left M) hdiff hU hbound
  exact (hD.differentiableAt (hU.mem_nhds hsU)).differentiableWithinAt

/-- The correction between the Euler logarithm over the rational primes and the Laplace
transform of the density. -/
def primeRoundedCorrection (s : ℂ) : ℂ :=
  s * boundedLaplace P.discrepancy s + primeCorrection P.atom P.primeAtom s +
    primePowerRemainder P.primeAtom s

/-- **The correction is holomorphic on `Re s > 17/30`.** -/
theorem differentiableOn_primeRoundedCorrection :
    DifferentiableOn ℂ P.primeRoundedCorrection {s : ℂ | 17 / 30 < s.re} := by
  intro s hs
  have hs' : 17 / 30 < s.re := hs
  have hopen0 : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hpos : s ∈ {s : ℂ | 0 < s.re} := by
    show 0 < s.re
    linarith only [hs']
  have hhalf : s ∈ {s : ℂ | 1 / 2 < s.re} := by
    show 1 / 2 < s.re
    linarith only [hs']
  have hΛ : DifferentiableAt ℂ (boundedLaplace P.discrepancy) s :=
    (differentiableOn_boundedLaplace P.measurable_discrepancy
      P.abs_discrepancy_le).differentiableAt (hopen0.mem_nhds hpos)
  have hC : DifferentiableAt ℂ (primeCorrection P.atom P.primeAtom) s :=
    P.differentiableOn_primeCorrection_primeAtom.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs')
  have hR : DifferentiableAt ℂ (primePowerRemainder P.primeAtom) s :=
    (differentiableOn_primePowerRemainder P.primeAtom_pos P.primeAtom_zero_le
      (fun a ha => P.summable_exp_primeAtom ha)).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hhalf)
  exact (((differentiableAt_id.mul hΛ).add hC).add hR).differentiableWithinAt

/-- **The Euler logarithm over the rational primes** is the Laplace transform of the density
plus the correction, on `Re s > 1`. -/
theorem tsum_neg_log_primeAtom_eq {s : ℂ} (hs : 1 < s.re) :
    ∑' k, -Complex.log (1 - cexp (-(s * P.primeAtom k))) =
      (∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * (P.w u : ℂ)) + P.primeRoundedCorrection s := by
  have hu := tsum_neg_log_eq P.primeAtom_pos P.primeAtom_zero_le
    (fun a ha => P.summable_exp_primeAtom ha) hs
  obtain ⟨hsu, -⟩ := summable_neg_log P.primeAtom_pos P.primeAtom_zero_le
    (fun a ha => P.summable_exp_primeAtom ha) hs
  obtain ⟨hst, -⟩ := summable_neg_log P.atom_pos P.atom_zero_le
    (fun a ha => P.summable_exp_atom ha) hs
  have hcorr : primeCorrection P.atom P.primeAtom s =
      (∑' k, cexp (-(s * P.primeAtom k))) - ∑' k, cexp (-(s * P.atom k)) := by
    rw [primeCorrection, hsu.tsum_sub hst]
  rw [hu, primeRoundedCorrection, hcorr, P.tsum_cexp_atom hs]
  ring

end PrimeDensity

/-! ### The realization theorem -/

variable {ι : Type*} [Fintype ι]

/-- **Euler products over the rational primes admit every finite layer right of `17/30`.** For
`17/30 < Θ < 1`, ordinates `γ_j` and multiplicities `m_j` there are rational primes `q_k`,
possibly repeated, and a function `G` holomorphic on `Re s > 17/30` such that the Euler product
`∏_k (1 − q_k^{−s})^{−1}` converges to `G(s)/(s − 1)` on `Re s > 1`, and `G` vanishes on
`Re s > 17/30` exactly at the points `Θ ± iγ_j` with `m_j ≠ 0`. -/
theorem exists_rational_prime_euler_product_with_layer {Θ : ℝ} (h0 : 17 / 30 < Θ) (h1 : Θ < 1)
    (γ : ι → ℝ) (m : ι → ℕ) :
    ∃ (q : ℕ → ℕ) (G : ℂ → ℂ), (∀ k, (q k).Prime) ∧
      DifferentiableOn ℂ G {s : ℂ | 17 / 30 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (G s / (s - 1))) ∧
      ∀ s : ℂ, 17 / 30 < s.re →
        (G s = 0 ↔ ∃ j, m j ≠ 0 ∧ (s = (Θ : ℂ) + γ j * I ∨ s = (Θ : ℂ) - γ j * I)) := by
  have hΘ0 : 0 < Θ := by linarith only [h0]
  obtain ⟨P, hP⟩ : ∃ P : PrimeDensity, P = layerPrimeDensity hΘ0 h1 γ m := ⟨_, rfl⟩
  have hw : P.w = layerLogDensity Θ γ m := by rw [hP]; rfl
  refine ⟨P.rationalPrime, fun s => layerRegular Θ γ m s * cexp (P.primeRoundedCorrection s),
    P.rationalPrime_prime, ?_, fun s hs => ?_, fun s _ => ?_⟩
  · exact (differentiable_layerRegular h1 γ m).differentiableOn.mul
      P.differentiableOn_primeRoundedCorrection.cexp
  · have hprod := hasProd_euler P.primeAtom_pos P.primeAtom_zero_le
      (fun a ha => P.summable_exp_primeAtom ha) hs
    have hval : cexp (∑' k, -Complex.log (1 - cexp (-(s * P.primeAtom k)))) =
        layerRegular Θ γ m s * cexp (P.primeRoundedCorrection s) / (s - 1) := by
      rw [P.tsum_neg_log_primeAtom_eq hs, Complex.exp_add, hw, cexp_layer_eq h1 γ m hs]
      ring
    rw [hval] at hprod
    exact hprod
  · rw [mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), layerRegular_eq_zero_iff]

end GaloisForLFunctions.FloorFreeArithmetic

import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# The Blaschke factor bounds the Cauchy form

For `λ_k` in the right half plane and coefficients `C_k`, the exponential sum `F(y) = Σ_k C_k e^{λ_k y}` has energy on
`(−∞, Y]` equal to the Cauchy form `Σ_{k,l} C_k C̄_l e^{(λ_k + λ̄_l)Y}/(λ_k + λ̄_l)`.

Multiplying coefficients by the Blaschke factor `β_j(k) = (λ_k − λ_j)/(λ_k + λ̄_j)` kills `λ_j` and does not raise the form:

`G(β_j C) = G(C) − 2 Re λ_j |Σ_k C_k/(λ_k + λ̄_j)|²` (`gramForm_blaschke`).

The identity is one line of algebra: `(a − μ)(c̄ − μ̄) − (a + μ̄)(c̄ + μ) = −(a + c̄)(μ + μ̄)`. Killing every node except `i`
gives, with no separation and no condition on the coefficients,

`G(C) ≥ |C_i|² Π_{j≠i} |β_j(i)|² / (2 Re λ_i)` (`re_gramForm_ge_blaschke`).

This replaces the combinatorial loss of a power-sum theorem by a factor that only sees the pseudo-hyperbolic geometry of
the nodes. Far nodes, much deeper nodes and much shallower nodes all have `|β_j(i)|` close to one.

On a finite interval the energy is a difference of two forms (`integral_normSq_expField`), and the lower form has
the trivial bound `(Σ_k |C_k|)²/(2 b₀)` (`re_gramForm_le`). The result is `energy_ge_blaschke`.
-/

noncomputable section

open Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

variable {ι : Type*}

/-- The Cauchy form of the nodes `lam` and coefficients `C`. -/
def gramForm (D : Finset ι) (lam C : ι → ℂ) : ℂ :=
  ∑ k ∈ D, ∑ l ∈ D, C k * conj (C l) / (lam k + conj (lam l))

/-- The Blaschke factor of the node `lam j` at the node `lam k`. -/
def blaschke (lam : ι → ℂ) (j k : ι) : ℂ := (lam k - lam j) / (lam k + conj (lam j))

theorem blaschke_self (lam : ι → ℂ) (j : ι) : blaschke lam j j = 0 := by
  simp [blaschke]

theorem add_conj_ne_zero {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) : a + conj b ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [add_re, conj_re, zero_re] at this
  linarith

/-- **One Blaschke factor.** It lowers the Cauchy form by an explicit square. -/
theorem gramForm_blaschke (D : Finset ι) {lam : ι → ℂ} (hlam : ∀ k ∈ D, 0 < (lam k).re) {j : ι}
    (hj : 0 < (lam j).re) (C : ι → ℂ) :
    gramForm D lam (fun k => blaschke lam j k * C k) = gramForm D lam C -
      ((2 * (lam j).re : ℝ) : ℂ) * ((∑ k ∈ D, C k / (lam k + conj (lam j))) *
        conj (∑ k ∈ D, C k / (lam k + conj (lam j)))) := by
  unfold gramForm
  rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l hl => ?_
  have h1 : lam k + conj (lam l) ≠ 0 := add_conj_ne_zero (hlam k hk) (hlam l hl)
  have h2 : lam k + conj (lam j) ≠ 0 := add_conj_ne_zero (hlam k hk) hj
  have h3 : conj (lam l) + lam j ≠ 0 := by
    rw [add_comm]
    exact add_conj_ne_zero hj (hlam l hl)
  have h3' : conj (lam l + conj (lam j)) = conj (lam l) + lam j := by
    rw [map_add, Complex.conj_conj]
  have hre : ((2 * (lam j).re : ℝ) : ℂ) = lam j + conj (lam j) := (Complex.add_conj _).symm
  simp only [blaschke, map_mul, map_div₀, map_sub, map_add, Complex.conj_conj]
  rw [hre]
  field_simp
  ring

theorem re_gramForm_blaschke_le (D : Finset ι) {lam : ι → ℂ} (hlam : ∀ k ∈ D, 0 < (lam k).re) {j : ι}
    (hj : 0 < (lam j).re) (C : ι → ℂ) :
    (gramForm D lam (fun k => blaschke lam j k * C k)).re ≤ (gramForm D lam C).re := by
  rw [gramForm_blaschke D hlam hj C, Complex.sub_re, Complex.mul_conj, Complex.re_ofReal_mul]
  have h0 : 0 ≤ (((Complex.normSq (∑ k ∈ D, C k / (lam k + conj (lam j))) : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  have h1 : 0 ≤ 2 * (lam j).re := by linarith
  have := mul_nonneg h1 h0
  linarith

/-- Killing a family of nodes does not raise the Cauchy form. -/
theorem re_gramForm_prod_blaschke_le [DecidableEq ι] (D : Finset ι) {lam : ι → ℂ} (hlam : ∀ k ∈ D, 0 < (lam k).re)
    (J : Finset ι) (hJ : J ⊆ D) (C : ι → ℂ) :
    (gramForm D lam (fun k => (∏ j ∈ J, blaschke lam j k) * C k)).re ≤ (gramForm D lam C).re := by
  induction J using Finset.induction_on with
  | empty => simp
  | insert j J hjJ ih =>
    have hJ' : J ⊆ D := fun x hx => hJ (Finset.mem_insert_of_mem hx)
    have hjD : j ∈ D := hJ (Finset.mem_insert_self j J)
    have h1 := re_gramForm_blaschke_le D hlam (hlam j hjD)
      (fun k => (∏ j ∈ J, blaschke lam j k) * C k)
    have e : (fun k => (∏ j' ∈ insert j J, blaschke lam j' k) * C k) =
        fun k => blaschke lam j k * ((∏ j ∈ J, blaschke lam j k) * C k) := by
      funext k
      rw [Finset.prod_insert hjJ]
      ring
    rw [e]
    exact h1.trans (ih hJ')

/-- **The Blaschke lower bound.** With no separation of the nodes and no condition on the coefficients,
`Re G(C) ≥ |C_i|² Π_{j≠i} |β_j(i)|² / (2 Re λ_i)`. -/
theorem re_gramForm_ge_blaschke [DecidableEq ι] (D : Finset ι) {lam : ι → ℂ} (hlam : ∀ k ∈ D, 0 < (lam k).re) {i : ι}
    (hi : i ∈ D) (C : ι → ℂ) :
    ‖C i‖ ^ 2 * (∏ j ∈ D.erase i, ‖blaschke lam j i‖) ^ 2 / (2 * (lam i).re) ≤
      (gramForm D lam C).re := by
  refine le_trans (le_of_eq ?_) (re_gramForm_prod_blaschke_le D hlam (D.erase i) (Finset.erase_subset _ _) C)
  set C' : ι → ℂ := fun k => (∏ j ∈ D.erase i, blaschke lam j k) * C k with hC'
  have hzero : ∀ k ∈ D, k ≠ i → C' k = 0 := by
    intro k hk hne
    simp only [hC']
    rw [Finset.prod_eq_zero (f := fun j => blaschke lam j k) (Finset.mem_erase.mpr ⟨hne, hk⟩)
      (blaschke_self lam k), zero_mul]
  have hsum : gramForm D lam C' = C' i * conj (C' i) / (lam i + conj (lam i)) := by
    unfold gramForm
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · intro l hl hne
      rw [hzero l hl hne]
      simp
    · intro h
      exact (h hi).elim
    · intro k hk hne
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hzero k hk hne]
      simp
    · intro h
      exact (h hi).elim
  rw [hsum, Complex.mul_conj, Complex.add_conj]
  have hb : 0 < (lam i).re := hlam i hi
  rw [← Complex.ofReal_div, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp only [hC']
  rw [norm_mul, norm_prod, mul_pow]
  ring

/-- The Cauchy form is at most the square of the coefficient mass over `2 b₀`. -/
theorem re_gramForm_le (D : Finset ι) {lam : ι → ℂ} {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hlam : ∀ k ∈ D, b₀ ≤ (lam k).re) (C : ι → ℂ) :
    (gramForm D lam C).re ≤ (∑ k ∈ D, ‖C k‖) ^ 2 / (2 * b₀) := by
  refine (Complex.re_le_norm _).trans ?_
  unfold gramForm
  refine (norm_sum_le _ _).trans ?_
  rw [sq, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
  rw [norm_div, norm_mul, Complex.norm_conj]
  have hden : 2 * b₀ ≤ ‖lam k + conj (lam l)‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp only [add_re, conj_re]
    linarith [hlam k hk, hlam l hl]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden

/-! ### The energy of an exponential sum -/

/-- The exponential sum `F(y) = Σ_k C_k e^{λ_k y}`. -/
def expField (D : Finset ι) (lam C : ι → ℂ) (y : ℝ) : ℂ := ∑ k ∈ D, C k * cexp (lam k * y)

theorem continuous_expField (D : Finset ι) (lam C : ι → ℂ) : Continuous (expField D lam C) := by
  unfold expField
  fun_prop

/-- The coefficients of the field translated to `y`. -/
def shiftCoeff (lam C : ι → ℂ) (y : ℝ) : ι → ℂ := fun k => C k * cexp (lam k * y)

theorem norm_shiftCoeff (lam C : ι → ℂ) (y : ℝ) (k : ι) :
    ‖shiftCoeff lam C y k‖ = ‖C k‖ * Real.exp ((lam k).re * y) := by
  simp only [shiftCoeff]
  rw [norm_mul, Complex.norm_exp]
  simp

/-- **The energy on an interval is a difference of two Cauchy forms.** -/
theorem integral_normSq_expField (D : Finset ι) {lam : ι → ℂ} (hlam : ∀ k ∈ D, 0 < (lam k).re)
    (C : ι → ℂ) (y₀ Y : ℝ) :
    ∫ y in y₀..Y, ‖expField D lam C y‖ ^ 2 =
      (gramForm D lam (shiftCoeff lam C Y)).re - (gramForm D lam (shiftCoeff lam C y₀)).re := by
  have hpt : ∀ y : ℝ, ((‖expField D lam C y‖ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ D, ∑ l ∈ D, C k * conj (C l) * cexp ((lam k + conj (lam l)) * y) := by
    intro y
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    unfold expField
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, add_mul, Complex.exp_add]
    ring
  have hcont : ∀ k l : ι, Continuous fun y : ℝ =>
      C k * conj (C l) * cexp ((lam k + conj (lam l)) * y) := fun k l => by fun_prop
  have hint : ((∫ y in y₀..Y, ‖expField D lam C y‖ ^ 2 : ℝ) : ℂ) =
      gramForm D lam (shiftCoeff lam C Y) - gramForm D lam (shiftCoeff lam C y₀) := by
    rw [← intervalIntegral.integral_ofReal]
    simp only [hpt]
    rw [intervalIntegral.integral_finsetSum (f := fun k y => ∑ l ∈ D,
      C k * conj (C l) * cexp ((lam k + conj (lam l)) * y))
      fun k _ => (continuous_finsetSum _ fun l _ => hcont k l).intervalIntegrable _ _]
    unfold gramForm
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [intervalIntegral.integral_finsetSum (f := fun l y =>
      C k * conj (C l) * cexp ((lam k + conj (lam l)) * y))
      fun l _ => (hcont k l).intervalIntegrable _ _, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hne : lam k + conj (lam l) ≠ 0 := add_conj_ne_zero (hlam k hk) (hlam l hl)
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hne]
    simp only [shiftCoeff, map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
    have e : ∀ y : ℝ, cexp ((lam k + conj (lam l)) * y) =
        cexp (lam k * y) * cexp (conj (lam l) * y) := fun y => by
      rw [add_mul, Complex.exp_add]
    rw [e, e]
    ring
  have h := congrArg Complex.re hint
  rwa [Complex.ofReal_re, Complex.sub_re] at h

/-- **The energy lower bound.** On `[y₀, Y]`, `F` has energy at least the Blaschke bound at `Y`, up to the coefficient mass
at `y₀`. -/
theorem energy_ge_blaschke [DecidableEq ι] (D : Finset ι) {lam : ι → ℂ} {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hlam : ∀ k ∈ D, b₀ ≤ (lam k).re) {i : ι} (hi : i ∈ D) (C : ι → ℂ) (y₀ Y : ℝ) :
    ‖C i‖ ^ 2 * Real.exp (2 * (lam i).re * Y) * (∏ j ∈ D.erase i, ‖blaschke lam j i‖) ^ 2 /
        (2 * (lam i).re) -
      (∑ k ∈ D, ‖C k‖ * Real.exp ((lam k).re * y₀)) ^ 2 / (2 * b₀) ≤
    ∫ y in y₀..Y, ‖expField D lam C y‖ ^ 2 := by
  have hpos : ∀ k ∈ D, 0 < (lam k).re := fun k hk => lt_of_lt_of_le hb₀ (hlam k hk)
  rw [integral_normSq_expField D hpos]
  have h1 := re_gramForm_ge_blaschke D hpos hi (shiftCoeff lam C Y)
  have h2 := re_gramForm_le D hb₀ hlam (shiftCoeff lam C y₀)
  rw [norm_shiftCoeff] at h1
  simp only [norm_shiftCoeff] at h2
  have e : ‖C i‖ ^ 2 * Real.exp (2 * (lam i).re * Y) *
      (∏ j ∈ D.erase i, ‖blaschke lam j i‖) ^ 2 / (2 * (lam i).re) =
      (‖C i‖ * Real.exp ((lam i).re * Y)) ^ 2 *
        (∏ j ∈ D.erase i, ‖blaschke lam j i‖) ^ 2 / (2 * (lam i).re) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 3
    push_cast
    ring_nf
  rw [e]
  exact sub_le_sub h1 h2

end GaloisForLFunctions.MultiscaleMollifiedZetaField

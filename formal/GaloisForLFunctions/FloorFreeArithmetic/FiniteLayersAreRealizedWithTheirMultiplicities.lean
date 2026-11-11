import GaloisForLFunctions.FloorFreeArithmetic.FiniteLayersInIntegerNormEulerProducts

/-!
# Finite layers are realized with their multiplicities

The regular factor of a layer is
`∏_j (F_A(s − ρ_j) F_A(s − ρ̄_j))^{m_j} / U_A(s − 1)`, with `F_A(z) = z U_A(z)` and `U_A`
without zeros. When the ordinates are distinct and no two of them add up to zero — for
instance when they are positive — the point `ρ_k = Θ + iγ_k` is a zero of exactly one linear
factor, to the power `m_k`: the regular factor is `(s − ρ_k)^{m_k}` times a cofactor that does
not vanish at `ρ_k`. So its order at `ρ_k`, and by symmetry at `ρ̄_k`, is `m_k`.

The integer-norm Euler product of a layer therefore realizes the whole datum: its regular
factor has on `Re s > ½` the divisor `Σ_j m_j ([ρ_j] + [ρ̄_j])`.

* `analyticOrderAt_layerRegular`, `analyticOrderAt_layerRegular_conj`: the orders of the
  regular factor.
* `exists_integer_norm_euler_product_with_divisor`: natural norms, natural coefficients, a
  simple pole, linear counting, and the prescribed zeros with the prescribed orders.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff
open GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff
open GaloisForLFunctions.ArithmeticPositiveDuality.TwoScaleIntegerNormOneOff

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The order of the regular factor -/

/-- The cofactor of the regular factor at the point `Θ + iγ_k`. -/
def layerCofactor (Θ : ℝ) (γ : ι → ℝ) (m : ι → ℕ) (k : ι) (s : ℂ) : ℂ :=
  frullaniUnit (layerCut Θ m) (s - ((Θ : ℂ) + γ k * I)) ^ m k *
    frullaniCutoffFactor (layerCut Θ m) (s - ((Θ : ℂ) - γ k * I)) ^ m k *
    (∏ j ∈ Finset.univ.erase k,
      (frullaniCutoffFactor (layerCut Θ m) (s - ((Θ : ℂ) + γ j * I)) *
        frullaniCutoffFactor (layerCut Θ m) (s - ((Θ : ℂ) - γ j * I))) ^ m j) *
    (frullaniUnit (layerCut Θ m) (s - 1))⁻¹

/-- The regular factor is `(s − ρ_k)^{m_k}` times the cofactor. -/
theorem layerRegular_eq_pow_mul_cofactor (Θ : ℝ) (γ : ι → ℝ) (m : ι → ℕ) (k : ι) (s : ℂ) :
    layerRegular Θ γ m s = (s - ((Θ : ℂ) + γ k * I)) ^ m k * layerCofactor Θ γ m k s := by
  rw [layerRegular, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
    frullaniCutoffFactor_eq_mul_unit (layerCut Θ m) (s - ((Θ : ℂ) + γ k * I)), layerCofactor,
    mul_pow, mul_pow]
  simp only [mul_assoc]

theorem differentiable_layerCofactor {Θ : ℝ} (h1 : Θ < 1) (γ : ι → ℝ) (m : ι → ℕ) (k : ι) :
    Differentiable ℂ (layerCofactor Θ γ m k) := by
  have hA := layerCut_pos h1 m
  have hF := differentiable_frullaniCutoffFactor hA
  have hU := differentiable_frullaniUnit hA
  have hprod : Differentiable ℂ (∏ j ∈ Finset.univ.erase k, fun s : ℂ =>
      (frullaniCutoffFactor (layerCut Θ m) (s - ((Θ : ℂ) + γ j * I)) *
        frullaniCutoffFactor (layerCut Θ m) (s - ((Θ : ℂ) - γ j * I))) ^ m j) :=
    Differentiable.finsetProd fun j _ => ((hF.comp (differentiable_id.sub_const _)).mul
      (hF.comp (differentiable_id.sub_const _))).pow _
  rw [Finset.prod_fn] at hprod
  unfold layerCofactor
  exact ((((hU.comp (differentiable_id.sub_const _)).pow _).mul
    ((hF.comp (differentiable_id.sub_const _)).pow _)).mul hprod).mul
    ((hU.comp (differentiable_id.sub_const _)).inv fun s => frullaniUnit_ne_zero _ _)

/-- The cofactor does not vanish at `Θ + iγ_k`, when the ordinates are distinct and no two of
them add up to zero. -/
theorem layerCofactor_ne_zero (Θ : ℝ) {γ : ι → ℝ} (m : ι → ℕ) (hinj : Function.Injective γ)
    (hsum : ∀ j k, γ j + γ k ≠ 0) (k : ι) :
    layerCofactor Θ γ m k ((Θ : ℂ) + γ k * I) ≠ 0 := by
  have hI : ∀ x : ℝ, x ≠ 0 → (x : ℂ) * I ≠ 0 := fun x hx =>
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hx) Complex.I_ne_zero
  have hF : ∀ z : ℂ, z ≠ 0 → frullaniCutoffFactor (layerCut Θ m) z ≠ 0 := fun z hz h =>
    hz ((frullaniCutoffFactor_eq_zero_iff _ _).mp h)
  unfold layerCofactor
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (frullaniUnit_ne_zero _ _))
    (pow_ne_zero _ (hF _ ?_))) (Finset.prod_ne_zero_iff.mpr fun j hj =>
      pow_ne_zero _ (mul_ne_zero (hF _ ?_) (hF _ ?_)))) (inv_ne_zero (frullaniUnit_ne_zero _ _))
  · rw [show (Θ : ℂ) + γ k * I - ((Θ : ℂ) - γ k * I) = ((γ k + γ k : ℝ) : ℂ) * I by
      push_cast; ring]
    exact hI _ (hsum k k)
  · rw [show (Θ : ℂ) + γ k * I - ((Θ : ℂ) + γ j * I) = ((γ k - γ j : ℝ) : ℂ) * I by
      push_cast; ring]
    exact hI _ (sub_ne_zero.mpr fun h => Finset.ne_of_mem_erase hj (hinj h).symm)
  · rw [show (Θ : ℂ) + γ k * I - ((Θ : ℂ) - γ j * I) = ((γ k + γ j : ℝ) : ℂ) * I by
      push_cast; ring]
    exact hI _ (hsum k j)

/-- **The order of the regular factor at `Θ + iγ_k` is `m_k`.** -/
theorem analyticOrderAt_layerRegular {Θ : ℝ} (h1 : Θ < 1) {γ : ι → ℝ} (m : ι → ℕ)
    (hinj : Function.Injective γ) (hsum : ∀ j k, γ j + γ k ≠ 0) (k : ι) :
    analyticOrderAt (layerRegular Θ γ m) ((Θ : ℂ) + γ k * I) = m k := by
  rw [((differentiable_layerRegular h1 γ m).analyticAt _).analyticOrderAt_eq_natCast]
  exact ⟨layerCofactor Θ γ m k, (differentiable_layerCofactor h1 γ m k).analyticAt _,
    layerCofactor_ne_zero Θ m hinj hsum k, Eventually.of_forall fun s => by
      rw [smul_eq_mul]
      exact layerRegular_eq_pow_mul_cofactor Θ γ m k s⟩

omit [DecidableEq ι] in
/-- The regular factor does not change when all ordinates change sign. -/
theorem layerRegular_neg (Θ : ℝ) (γ : ι → ℝ) (m : ι → ℕ) :
    layerRegular Θ (fun j => -γ j) m = layerRegular Θ γ m := by
  funext s
  unfold layerRegular
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [show (Θ : ℂ) + ((-γ j : ℝ) : ℂ) * I = (Θ : ℂ) - γ j * I by push_cast; ring,
    show (Θ : ℂ) - ((-γ j : ℝ) : ℂ) * I = (Θ : ℂ) + γ j * I by push_cast; ring, mul_comm]

/-- **The order of the regular factor at `Θ − iγ_k` is `m_k`.** -/
theorem analyticOrderAt_layerRegular_conj {Θ : ℝ} (h1 : Θ < 1) {γ : ι → ℝ} (m : ι → ℕ)
    (hinj : Function.Injective γ) (hsum : ∀ j k, γ j + γ k ≠ 0) (k : ι) :
    analyticOrderAt (layerRegular Θ γ m) ((Θ : ℂ) - γ k * I) = m k := by
  have h := analyticOrderAt_layerRegular h1 (γ := fun j => -γ j) m
    (fun a b hab => hinj (neg_injective hab))
    (fun j k h => hsum j k (by linarith only [h])) k
  rw [layerRegular_neg] at h
  rwa [show (Θ : ℂ) + ((-γ k : ℝ) : ℂ) * I = (Θ : ℂ) - γ k * I by push_cast; ring] at h

/-! ### The realization theorem with multiplicities -/

/-- **Integer-norm Euler products realize every finite divisor right of the critical line.**
For `½ < Θ < 1`, distinct positive ordinates `γ_j` and multiplicities `m_j` there are natural
norms `q_k ≥ 2` and a function `G` holomorphic on `Re s > ½` such that, on `Re s > 1`, the Euler
product `∏_k (1 − q_k^{−s})^{−1}` converges to `G(s)/(s − 1)` and is the Dirichlet series with
the natural coefficients `genCoeff q n`; `G` vanishes on `Re s > ½` exactly at the points
`Θ ± iγ_j` with `m_j ≠ 0`, to the order `m_j`; and `Σ_{n<N} a_n / N` tends to a positive
limit. -/
theorem exists_integer_norm_euler_product_with_divisor {Θ : ℝ} (h0 : 1 / 2 < Θ) (h1 : Θ < 1)
    {γ : ι → ℝ} (hinj : Function.Injective γ) (hpos : ∀ j, 0 < γ j) (m : ι → ℕ) :
    ∃ (q : ℕ → ℕ) (G : ℂ → ℂ), (∀ k, 2 ≤ q k) ∧
      DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (G s / (s - 1)) ∧
        LSeriesHasSum (fun n => (genCoeff q n : ℂ)) s (G s / (s - 1))) ∧
      (∀ s : ℂ, 1 / 2 < s.re →
        (G s = 0 ↔ ∃ j, m j ≠ 0 ∧ (s = (Θ : ℂ) + γ j * I ∨ s = (Θ : ℂ) - γ j * I))) ∧
      (∀ j, analyticOrderAt G ((Θ : ℂ) + γ j * I) = m j ∧
        analyticOrderAt G ((Θ : ℂ) - γ j * I) = m j) ∧
      ∃ A : ℝ, 0 < A ∧
        Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (genCoeff q n : ℝ)) / N) atTop (𝓝 A) := by
  have hΘ0 : 0 < Θ := by linarith only [h0]
  have hsum0 : ∀ j k, γ j + γ k ≠ 0 := fun j k => ne_of_gt (add_pos (hpos j) (hpos k))
  obtain ⟨P, hP⟩ : ∃ P : PrimeDensity, P = layerPrimeDensity hΘ0 h1 γ m := ⟨_, rfl⟩
  have hw : P.w = layerLogDensity Θ γ m := by rw [hP]; rfl
  have hmono : ∀ k, Real.log (P.primeNorm 0) ≤ Real.log (P.primeNorm k) :=
    P.roundedAtom_zero_le
  have hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * Real.log (P.primeNorm k))) :=
    fun a ha => P.summable_exp_roundedAtom ha
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
  -- the order of `G` at a point right of the line is that of the regular factor
  have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have horder : ∀ ρ : ℂ, 1 / 2 < ρ.re →
      analyticOrderAt (fun s => layerRegular Θ γ m s * cexp (P.roundedCorrection s)) ρ =
        analyticOrderAt (layerRegular Θ γ m) ρ := by
    intro ρ hρ
    have hfa : AnalyticAt ℂ (layerRegular Θ γ m) ρ :=
      (differentiable_layerRegular h1 γ m).analyticAt ρ
    have hga : AnalyticAt ℂ (fun s => cexp (P.roundedCorrection s)) ρ :=
      P.differentiableOn_roundedCorrection.cexp.analyticAt (hopen.mem_nhds hρ)
    have hg0 : analyticOrderAt (fun s => cexp (P.roundedCorrection s)) ρ = 0 :=
      hga.analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _)
    have hmul := analyticOrderAt_mul hfa hga
    rw [hg0, add_zero] at hmul
    exact hmul
  have hre : ∀ j, 1 / 2 < ((Θ : ℂ) + γ j * I).re ∧ 1 / 2 < ((Θ : ℂ) - γ j * I).re := by
    intro j
    constructor
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
      exact h0
    · simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero]
      exact h0
  obtain ⟨A, hA, -, hcount⟩ := tendsto_genCoeff_count P.two_le_primeNorm hmono hsum
    (by norm_num : (1 / 2 : ℝ) < 1) hG hG1 hF
  refine ⟨P.primeNorm, fun s => layerRegular Θ γ m s * cexp (P.roundedCorrection s),
    P.two_le_primeNorm, hG, fun s hs => ⟨?_, ?_⟩, fun s _ => hzero s, fun j => ⟨?_, ?_⟩,
    A, hA, hcount⟩
  · have hprod := hasProd_euler P.roundedAtom_pos P.roundedAtom_zero_le
      (fun a ha => P.summable_exp_roundedAtom ha) hs
    have hval : cexp (∑' k, -Complex.log (1 - cexp (-(s * P.roundedAtom k)))) =
        layerRegular Θ γ m s * cexp (P.roundedCorrection s) / (s - 1) := hF s hs
    rw [hval] at hprod
    exact hprod
  · have hser := hasSum_genCoeff P.two_le_primeNorm hmono hsum hs
    rw [hF s hs] at hser
    exact hser
  · rw [horder _ (hre j).1]
    exact analyticOrderAt_layerRegular h1 m hinj hsum0 j
  · rw [horder _ (hre j).2]
    exact analyticOrderAt_layerRegular_conj h1 m hinj hsum0 j

end GaloisForLFunctions.FloorFreeArithmetic

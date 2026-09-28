import GaloisForLFunctions.RHTower.WeilPositivityMertensConstantObstruction
import GaloisForLFunctions.RHTower.ThetaPowerChiEightLFunction
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicPrimitive
import Zeta23.ThmE.MainChi
import GaloisForLFunctions.RHTower.ClusterInterpolationContour

/-!
# Weil positivity fails when the primes `p ≡ ±3 (mod 8)` are weighted down

Let `χ₈` be the even primitive quadratic character modulo `8`.  For `t ∈ ℝ` consider the prime
weights `Λ(n)(1 - t + tχ₈(n))` in the finite-atom Weil symbol of `ζ`.  The archimedean part stays
that of `ζ`.

* **Exact energy** (`integral_weilAtomSymbol_chiEightMix`).  For a polar-constrained `C²` test
  `f` supported in `[-a, a]`,
  `∫ |h_f|² S_{Λ(1-t+tχ₈)} = 2π(1-t) Re W_ζ(f) + t (2π Re W_{χ₈}(f) - log 8 ∫ |h_f|²)`.
  Here `W_ζ` and `W_{χ₈}` are the zero sides of `ζ` and `L(s, χ₈)`, and the twisted part comes
  from the explicit formula of `L(s, χ₈)` (`integral_weilAtomSymbol_chiEight`).  For an even
  character the archimedean mismatch with `ζ` is the constant `log q`.
* **Double radical tests.**
  - `chiEightKernel`, the axis source of the theta series of `χ₈`, has transform
    `(√2/4) 8^{s/2} Λ(s, χ₈)` with `s = ½ + iz`, so it lies in the radical of `L(s, χ₈)`
    (`paperFT_chiEightKernel_gammaOf_eq_zero`).
  - The test `g_R = f_R ⋆ K_{≤4R}` is built from the truncated radical test `f_R` of `ζ`.
  - Both zero sides of `g_R` are `O(R e^{-R/2})`: `exists_norm_W_zeta_conductorTest_le` and
    `exists_norm_W_chiEight_conductorTest_le`.
  - `∫ |h_{g_R}|²` stays bounded below (`exists_integral_normSq_conductorTest_ge`). The limit
    transform `Φ̂ κ̂₂ K̂` is analytic on `|Im z| < 1` and nonzero at `z = -3i/4`, so it does not
    vanish identically on `ℝ`.
* **Theorem** (`chiEightMix_weilAtomSymbol_not_nonneg`).  For every `t > 0` some polar-constrained
  test has negative symbol energy.
  - At `t = 1/2` the weights are `Λ` on `n ≡ ±1 (mod 8)`, with half weight on the powers of `2`.
    This deletes the primes `p ≡ ±3 (mod 8)` together with their odd powers.
  - At `t = 1` they are the twisted weights `Λχ₈`.
  - The defect is `t log 8 ∫ |h|²`, the logarithm of the conductor.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

local notation "Φ" => riemannPhiKernel

/-! ### The theta kernel of `L(s, χ₈)` -/

/-- The axis source `K(x) = e^{x/2} F_{1/2}(i e^{2x}) / 2` of the theta series of `χ₈`. -/
def chiEightKernel (x : ℝ) : ℂ := modTail (thetaPowerForm (1 / 2)) 0 x

theorem continuous_chiEightKernel : Continuous chiEightKernel :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_modTail 0 (differentiableOn_thetaPowerForm (1 / 2)) x).continuousAt

theorem exists_norm_chiEightKernel_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖chiEightKernel x‖ ≤ C * Real.exp (-|x|) := by
  obtain ⟨C, hC0, hC⟩ := thetaPowerTail_decay (a := 1 / 2) (by norm_num) 0 le_rfl
    (by positivity)
  refine ⟨C, hC0, fun x => ?_⟩
  have h := hC (x : ℂ) (by simp)
  rw [chargeTailC_ofReal] at h
  simpa [chiEightKernel] using h

/-- The kernel is integrable against `e^{|u|/2}` and its transform on `|Im z| ≤ 1/2` is bounded
by that integral. -/
theorem integrable_norm_chiEightKernel_mul_exp :
    Integrable (fun u : ℝ => ‖chiEightKernel u‖ * Real.exp (1 / 2 * |u|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_chiEightKernel_le
  refine Integrable.mono' ((integrable_exp_neg_mul_abs_modSource (a := 1 / 2)
    (by norm_num)).const_mul C) ?_ (Eventually.of_forall fun u => ?_)
  · exact (continuous_chiEightKernel.norm.mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖chiEightKernel u‖ * Real.exp (1 / 2 * |u|)
        ≤ C * Real.exp (-|u|) * Real.exp (1 / 2 * |u|) :=
          mul_le_mul_of_nonneg_right (hC u) (Real.exp_pos _).le
      _ = C * Real.exp (-(1 / 2) * |u|) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem paperFT_chiEightKernel (z : ℂ) :
    paperFT chiEightKernel z = thetaPowerXiC (1 / 2) (-z) := by
  unfold paperFT thetaPowerXiC chiEightKernel
  congr 1; funext x
  rw [mul_comm]; congr 2; ring

/-- The transform of the kernel is the completed `L`-function of `χ₈` at `1/2 + iz`. -/
theorem paperFT_chiEightKernel_eq {z : ℂ} (hz : |z.im| < 1) :
    paperFT chiEightKernel z = ((Real.sqrt 2 / 4 : ℝ) : ℂ) * (8 : ℂ) ^ ((1 / 2 + I * z) / 2) *
      DirichletCharacter.completedLFunction dirichletChiEight (1 / 2 + I * z) := by
  rw [paperFT_chiEightKernel, thetaPowerXiC_half_eq_completedLFunction (by simpa using hz)]
  rw [show (1 / 2 : ℂ) - I * -z = 1 / 2 + I * z by ring]

theorem half_add_I_mul_gammaOf (ρ : ℂ) : 1 / 2 + I * gammaOf ρ = ρ := by
  unfold gammaOf
  field_simp
  ring

/-- **The kernel lies in the radical of `L(s, χ₈)`**: its transform vanishes at every nontrivial
zero. -/
theorem paperFT_chiEightKernel_gammaOf_eq_zero {ρ : ℂ}
    (hρ : Zeta23.ThmE.IsNontrivialZeroL dirichletChiEight ρ) :
    paperFT chiEightKernel (gammaOf ρ) = 0 := by
  have hstrip : 0 < ρ.re ∧ ρ.re < 1 := ⟨hρ.2.1, hρ.2.2⟩
  have hIm : |(gammaOf ρ).im| < 1 := lt_trans (WeilEF.abs_gammaOf_im_lt hstrip) (by norm_num)
  rw [paperFT_chiEightKernel_eq hIm, half_add_I_mul_gammaOf]
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor dirichletChiEight ρ
    (Or.inr (by norm_num))
  rw [hρ.1, dirichletChiEight_even.gammaFactor_def] at hL
  have hΓ : ρ.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hstrip.1
  have : DirichletCharacter.completedLFunction dirichletChiEight ρ = 0 := by
    rcases (div_eq_zero_iff.mp hL.symm) with h | h
    · exact h
    · exact absurd h hΓ
  rw [this, mul_zero]

/-! ### Truncations of the kernel -/

/-- The kernel on `[-L, L]`. -/
def chiEightCore (L : ℝ) : ℝ → ℂ := (Icc (-L) L).indicator chiEightKernel

/-- The kernel beyond `|u| > L`. -/
def chiEightTail (L : ℝ) : ℝ → ℂ := {u : ℝ | L < |u|}.indicator chiEightKernel

theorem chiEightCore_add_tail (L u : ℝ) : chiEightCore L u + chiEightTail L u = chiEightKernel u := by
  unfold chiEightCore chiEightTail indicator
  by_cases h : L < |u|
  · have : u ∉ Icc (-L) L := fun hm => by have := abs_le.mpr ⟨hm.1, hm.2⟩; linarith
    simp [h, this]
  · push Not at h
    have : u ∈ Icc (-L) L := ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩
    simp [this, not_lt.mpr h]

theorem norm_chiEightCore_le (L u : ℝ) : ‖chiEightCore L u‖ ≤ ‖chiEightKernel u‖ := by
  unfold chiEightCore indicator; split_ifs <;> simp

theorem norm_chiEightTail_le (L u : ℝ) : ‖chiEightTail L u‖ ≤ ‖chiEightKernel u‖ := by
  unfold chiEightTail indicator; split_ifs <;> simp

theorem integrable_chiEightCore_mul_exp (L : ℝ) (z : ℂ) :
    Integrable (fun u : ℝ => chiEightCore L u * Complex.exp (I * z * u)) := by
  have : (fun u : ℝ => chiEightCore L u * Complex.exp (I * z * u)) =
      (Icc (-L) L).indicator (fun u : ℝ => chiEightKernel u * Complex.exp (I * z * u)) := by
    funext u; unfold chiEightCore indicator; split_ifs <;> simp
  rw [this]
  exact ((continuous_chiEightKernel.mul (by fun_prop)).integrableOn_Icc).integrable_indicator
    measurableSet_Icc

theorem integrable_chiEightCore (L : ℝ) : Integrable (chiEightCore L) := by
  have h := integrable_chiEightCore_mul_exp L 0
  simpa using h

theorem integrable_chiEightKernel_mul_exp {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    Integrable (fun u : ℝ => chiEightKernel u * Complex.exp (I * z * u)) := by
  refine Integrable.mono' integrable_norm_chiEightKernel_mul_exp
    ((continuous_chiEightKernel.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_exp hz u) (norm_nonneg _)

theorem integrable_chiEightTail_mul_exp (L : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    Integrable (fun u : ℝ => chiEightTail L u * Complex.exp (I * z * u)) := by
  have h := (integrable_chiEightKernel_mul_exp hz).sub (integrable_chiEightCore_mul_exp L z)
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.sub_apply]
  rw [← chiEightCore_add_tail L u]; ring

theorem paperFT_chiEightCore_eq (L : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    paperFT (chiEightCore L) z = paperFT chiEightKernel z - paperFT (chiEightTail L) z := by
  unfold paperFT
  rw [← integral_sub (integrable_chiEightKernel_mul_exp hz) (integrable_chiEightTail_mul_exp L hz)]
  congr 1; funext u
  rw [← chiEightCore_add_tail L u]; ring

theorem measurableSet_chiEightTailSet (L : ℝ) : MeasurableSet {u : ℝ | L < |u|} :=
  (isOpen_lt continuous_const continuous_abs).measurableSet

theorem aestronglyMeasurable_chiEightTail (L : ℝ) : AEStronglyMeasurable (chiEightTail L) volume :=
  continuous_chiEightKernel.aestronglyMeasurable.indicator (measurableSet_chiEightTailSet L)

theorem aestronglyMeasurable_chiEightCore (L : ℝ) : AEStronglyMeasurable (chiEightCore L) volume :=
  continuous_chiEightKernel.aestronglyMeasurable.indicator measurableSet_Icc

/-- Transform bound in the strip `|Im z| ≤ 1/2` for a measurable function dominated by the
kernel. -/
theorem norm_paperFT_le_of_norm_le_chiEightKernel {g : ℝ → ℂ}
    (hgm : AEStronglyMeasurable g volume) (hg : ∀ u, ‖g u‖ ≤ ‖chiEightKernel u‖) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT g z‖ ≤ ∫ u : ℝ, ‖g u‖ * Real.exp (1 / 2 * |u|) := by
  unfold paperFT
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _) ?_ (Eventually.of_forall fun u => ?_))
  · refine Integrable.mono' integrable_norm_chiEightKernel_mul_exp
      (hgm.norm.mul (by fun_prop : Continuous fun u : ℝ => Real.exp (1 / 2 * |u|)).aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (hg u) (Real.exp_pos _).le
  · simp only
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_exp hz u) (norm_nonneg _)

theorem norm_paperFT_chiEightCore_le (L : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (chiEightCore L) z‖ ≤ ∫ u : ℝ, ‖chiEightKernel u‖ * Real.exp (1 / 2 * |u|) := by
  refine (norm_paperFT_le_of_norm_le_chiEightKernel (aestronglyMeasurable_chiEightCore L)
    (norm_chiEightCore_le L) hz).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun u => by positivity) integrable_norm_chiEightKernel_mul_exp
      (Eventually.of_forall fun u => ?_))
  exact mul_le_mul_of_nonneg_right (norm_chiEightCore_le L u) (Real.exp_pos _).le

/-- **Tail bound.**  `∫_{|u| > L} |K(u)| e^{|u|/2} du ≤ C₈ e^{-L/4}` with `C₈` independent of `L`. -/
theorem exists_integral_chiEightTail_le : ∃ C₈ : ℝ, 0 ≤ C₈ ∧ ∀ L : ℝ, 0 ≤ L →
    ∫ u : ℝ, ‖chiEightTail L u‖ * Real.exp (1 / 2 * |u|) ≤ C₈ * Real.exp (-(L / 4)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_chiEightKernel_le
  have hint := integrable_exp_neg_mul_abs_modSource (a := 1 / 4) (by norm_num)
  refine ⟨C * ∫ u : ℝ, Real.exp (-(1 / 4) * |u|), mul_nonneg hC0
    (integral_nonneg fun _ => (Real.exp_pos _).le), fun L hL => ?_⟩
  have hpt : ∀ u, ‖chiEightTail L u‖ * Real.exp (1 / 2 * |u|) ≤
      Real.exp (-(L / 4)) * (C * Real.exp (-(1 / 4) * |u|)) := by
    intro u
    unfold chiEightTail indicator
    split_ifs with h
    · have h' : L < |u| := h
      calc ‖chiEightKernel u‖ * Real.exp (1 / 2 * |u|)
          ≤ C * Real.exp (-|u|) * Real.exp (1 / 2 * |u|) :=
            mul_le_mul_of_nonneg_right (hC u) (Real.exp_pos _).le
        _ = C * Real.exp (-(1 / 2) * |u|) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        _ ≤ C * (Real.exp (-(L / 4)) * Real.exp (-(1 / 4) * |u|)) := by
            gcongr
            rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
        _ = Real.exp (-(L / 4)) * (C * Real.exp (-(1 / 4) * |u|)) := by ring
    · simp only [norm_zero, zero_mul]; positivity
  calc ∫ u : ℝ, ‖chiEightTail L u‖ * Real.exp (1 / 2 * |u|)
      ≤ ∫ u : ℝ, Real.exp (-(L / 4)) * (C * Real.exp (-(1 / 4) * |u|)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => by positivity)
          ((hint.const_mul C).const_mul _) (Eventually.of_forall hpt)
    _ = C * (∫ u : ℝ, Real.exp (-(1 / 4) * |u|)) * Real.exp (-(L / 4)) := by
        rw [integral_const_mul, integral_const_mul]; ring

theorem norm_paperFT_chiEightTail_le (L : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (chiEightTail L) z‖ ≤ ∫ u : ℝ, ‖chiEightTail L u‖ * Real.exp (1 / 2 * |u|) :=
  norm_paperFT_le_of_norm_le_chiEightKernel (aestronglyMeasurable_chiEightTail L)
    (norm_chiEightTail_le L) hz

/-! ### The symbol energy against the archimedean part -/

theorem integrable_normSq_paperFT_mul_arch {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))) := by
  have hS := integrable_normSq_paperFT_mul_weilAtomSymbol hf hfs
  have hcos := integrable_normSq_paperFT_mul_cos hf hfs
  have hsum : Integrable (fun τ : ℝ => ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
      (2 * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n)) *
        (‖paperFT f τ‖ ^ 2 * Real.cos (τ * Real.log n))) :=
    integrable_finsetSum _ fun n _ => (hcos _).const_mul _
  refine (hS.add hsum).congr (Eventually.of_forall fun τ => ?_)
  simp only [Pi.add_apply]
  unfold weilAtomSymbol
  have harg : ∀ n : ℕ, 2 * π * Real.log n * (τ / (2 * π)) = τ * Real.log n := fun n => by
    field_simp
  simp only [harg]
  rw [mul_sub, Finset.mul_sum]
  have : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (2 * ((ArithmeticFunction.vonMangoldt n : ℝ) /
      Real.sqrt n)) * (‖paperFT f τ‖ ^ 2 * Real.cos (τ * Real.log n)) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, ‖paperFT f τ‖ ^ 2 *
        ((ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
          (2 * Real.cos (τ * Real.log n))) :=
    Finset.sum_congr rfl fun n _ => by ring
  rw [this]; ring

/-- **Symbol energy of arbitrary weights.**  For a level-`a` test,
`∫ |h_f|² S_lam = ∫ |h_f|² S_∞ - 2π ∑_{2 ≤ n ≤ e^{2a}} lam(n) n^{-1/2} Re(k(log n) + k(-log n))`,
where `S_∞` is the archimedean symbol and `k = f ⋆ f̃`. -/
theorem integral_weilAtomSymbol_eq_arch_sub {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (lam : ℕ → ℝ) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))) -
      2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, lam n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re := by
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  have harg : ∀ (τ : ℝ) (n : ℕ), 2 * π * Real.log n * (τ / (2 * π)) = τ * Real.log n :=
    fun τ n => by field_simp
  have hpt : ∀ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam N (τ / (2 * π)) =
      ‖paperFT f τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) -
        ∑ n ∈ Finset.Icc 2 N, (2 * (lam n / Real.sqrt n)) *
          (‖paperFT f τ‖ ^ 2 * Real.cos (τ * Real.log n)) := by
    intro τ
    unfold weilAtomSymbol
    simp only [harg]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring
  have hcos := integrable_normSq_paperFT_mul_cos hf hfs
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub
    (integrable_normSq_paperFT_mul_arch hf hfs)
    (integrable_finsetSum _ fun n _ => (hcos _).const_mul _),
    integral_finsetSum _ fun n _ => (hcos _).const_mul _]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_normSq_paperFT_mul_cos_eq hf hfs]
  ring

/-! ### The explicit formula of `L(s, χ₈)` in symbol form -/

theorem dirichletChiEight_isPrimitive : dirichletChiEight.IsPrimitive :=
  quadraticCharacterEight_isPrimitive

/-- The zeros of `L(s, χ₈)` in the critical strip, with multiplicities. -/
def chiEightZeros : ZeroConfig :=
  Zeta23.ThmE.LZeros (Zeta23.ThmE.LSeam_of (q := 8) (by norm_num) dirichletChiEight_isPrimitive)

theorem parity_dirichletChiEight : Zeta23.ThmE.parity dirichletChiEight = 0 := by
  unfold Zeta23.ThmE.parity; rw [if_pos dirichletChiEight_even]

theorem coeff_dirichletChiEight (n : ℕ) :
    Zeta23.ThmE.coeff dirichletChiEight n = ((chiEight n : ℝ) : ℂ) := by
  unfold Zeta23.ThmE.coeff
  exact_mod_cast dirichletChiEight_nat n

theorem archimedeanWeilSymbol_div (τ : ℝ) :
    archimedeanWeilSymbol (τ / (2 * π)) =
      (Complex.digamma (1 / 4 + ((0 : ℕ) : ℂ) / 2 + I * τ / 2)).re + Real.log (8 / π) -
        Real.log 8 := by
  rw [archimedeanWeilSymbol_eq, Real.log_div (by norm_num) Real.pi_ne_zero]
  have : ((1 / 4 : ℝ) : ℂ) + ((π * (τ / (2 * π)) : ℝ) : ℂ) * I =
      1 / 4 + ((0 : ℕ) : ℂ) / 2 + I * τ / 2 := by
    have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    rw [show π * (τ / (2 * π)) = τ / 2 by field_simp]
    push_cast; ring
  rw [this]; ring

/-- **The twisted Weil energy is the `L(s, χ₈)` zero side minus the conductor.**  For a `C²` test
supported in `[-a, a]`,
`∫ |h_f|² S_{Λχ₈} = 2π Re W_{χ₈}(f) - log 8 ∫ |h_f|²`,
where `W_{χ₈}(f) = ∑_ρ m_ρ h_f(γ_ρ) conj(h_f(conj γ_ρ))` runs over the zeros of `L(s, χ₈)`.  This is
the explicit formula of `L(s, χ₈)`: its archimedean part is that of `ζ` shifted by `log 8`. -/
theorem integral_weilAtomSymbol_chiEight {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * chiEight n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      2 * π * (chiEightZeros.W f f).re - Real.log 8 * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 := by
  obtain ⟨hfc, hkd, hks, hki, hFk⟩ := weilTest_self_data hf hfs
  set k := EF.weilTest f f with hk
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  obtain ⟨-, hEF⟩ := Zeta23.ThmE.EF_lit_chi_L (q := 8) (χ := dirichletChiEight) (by norm_num)
    dirichletChiEight_isPrimitive k hkd (EF.hasCompactSupport_of_tsupport_subset hks)
  -- the zero side
  have hW : chiEightZeros.W f f = ∑' ρ : chiEightZeros.carrier,
      (chiEightZeros.mult ρ : ℂ) * paperFT k (gammaOf ρ) := by
    unfold ZeroConfig.W
    congr 1; funext ρ
    simp only [ZeroConfig.Wsummand, hk, EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc,
      mul_assoc]
  -- the prime side is a finite sum
  have hk0 : ∀ y : ℝ, 2 * a < |y| → k y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hks hmem
      have : |y| ≤ 2 * a := abs_le.mpr ⟨this.1, this.2⟩
      linarith
  have hprime : ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (Zeta23.ThmE.coeff dirichletChiEight n * k (Real.log n) +
        (starRingEnd ℂ) (Zeta23.ThmE.coeff dirichletChiEight n) * k (-Real.log n)) =
      ∑ n ∈ Finset.Icc 2 N, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n * chiEight n : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n)) := by
    rw [tsum_eq_sum (s := Finset.Icc 2 N)]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [coeff_dirichletChiEight, Complex.conj_ofReal]; push_cast; ring
    · intro n hn
      rw [Finset.mem_Icc, not_and_or] at hn
      rcases hn with hn | hn
      · have : n = 0 ∨ n = 1 := by omega
        rcases this with rfl | rfl <;> simp
      · push Not at hn
        have hexp : Real.exp (2 * a) < n := (Nat.floor_lt (Real.exp_pos _).le).mp hn
        have hlog : 2 * a < Real.log n := by
          rw [← Real.log_exp (2 * a)]; exact Real.log_lt_log (Real.exp_pos _) hexp
        have hl0 : 0 ≤ Real.log n := le_trans (by linarith) hlog.le
        rw [hk0 _ (by rw [abs_of_nonneg hl0]; exact hlog),
          hk0 _ (by rw [abs_neg, abs_of_nonneg hl0]; exact hlog)]
        simp
  -- the archimedean side
  have harch : ∫ r : ℝ, paperFT k r * ((((Complex.digamma (1 / 4 + ((0 : ℕ) : ℂ) / 2 +
      I * r / 2)).re + Real.log (((8 : ℕ) : ℝ) / π) : ℝ)) : ℂ) =
      ((∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (archimedeanWeilSymbol (r / (2 * π)) + Real.log 8) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; funext r
    rw [hk, paperFT_weilTest_self_ofReal hf.continuous hfc, archimedeanWeilSymbol_div]
    push_cast; ring
  have hEF' : ∑' ρ : chiEightZeros.carrier, (chiEightZeros.mult ρ : ℂ) * paperFT k (gammaOf ρ) =
      Zeta23.ThmE.literatureRHSchi (Zeta23.ThmE.parity dirichletChiEight) 8
        (Zeta23.ThmE.coeff dirichletChiEight) k := hEF
  clear hEF
  rw [← hW, Zeta23.ThmE.literatureRHSchi, parity_dirichletChiEight, hprime, harch] at hEF'
  have hEF := hEF'
  -- real parts
  have hre := congrArg Complex.re hEF
  simp only [Complex.add_re, Complex.neg_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hre
  have hdiv : ((1 / (2 * π) : ℂ)).re = 1 / (2 * π) := by
    rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have hdivim : ((1 / (2 * π) : ℂ)).im = 0 := by
    rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_im]
  rw [hdiv, hdivim, zero_mul, sub_zero] at hre
  -- assemble with the arch-sum form of the symbol energy
  rw [integral_weilAtomSymbol_eq_arch_sub hf hfs]
  have hI2 : ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (archimedeanWeilSymbol (r / (2 * π)) + Real.log 8) =
      (∫ r : ℝ, ‖paperFT f r‖ ^ 2 * archimedeanWeilSymbol (r / (2 * π))) +
        Real.log 8 * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_add (integrable_normSq_paperFT_mul_arch hf hfs)
      ((integrable_normSq_paperFT hf hfs).const_mul _)]
    congr 1; funext r; ring
  rw [hI2] at hre
  have hsum : ∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n * chiEight n) /
      Real.sqrt n * (k (Real.log n) + k (-Real.log n)).re =
      ∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n / Real.sqrt n * chiEight n) *
        (k (Real.log n) + k (-Real.log n)).re :=
    Finset.sum_congr rfl fun n _ => by ring
  rw [hsum]
  have hπ : (0 : ℝ) < π := Real.pi_pos
  field_simp at hre ⊢
  simp only [Complex.add_re] at hre ⊢
  linarith

/-! ### The double radical test -/

/-- `g_R = f_R ⋆ K_{≤4R}`: the truncated radical test of `ζ` convolved with the truncated theta
kernel of `L(s, χ₈)`.  Its transform vanishes approximately at the zeros of both functions. -/
def conductorTest (R : ℝ) : ℝ → ℂ :=
  convolution (weilRadicalTest R) (chiEightCore (4 * R)) (ContinuousLinearMap.mul ℝ ℂ) volume

theorem contDiff_conductorTest (R : ℝ) : ContDiff ℝ 2 (conductorTest R) :=
  (hasCompactSupport_weilRadicalTest R).contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ)
    (n := 2) (contDiff_weilRadicalTest R) (integrable_chiEightCore _).locallyIntegrable

theorem conductorTest_eq_zero {R x : ℝ} (hx : 5 * R < |x|) :
    conductorTest R x = 0 := by
  unfold conductorTest
  rw [convolution_def]
  have : ∀ t : ℝ, (ContinuousLinearMap.mul ℝ ℂ) (weilRadicalTest R t)
      (chiEightCore (4 * R) (x - t)) = 0 := by
    intro t
    simp only [ContinuousLinearMap.mul_apply']
    by_cases ht : R < |t|
    · rw [weilRadicalTest_eq_zero ht, zero_mul]
    · push Not at ht
      have hxt : 4 * R < |x - t| := by have := abs_sub_abs_le_abs_sub x t; linarith
      have : x - t ∉ Icc (-(4 * R)) (4 * R) := fun hm => by
        have := abs_le.mpr ⟨hm.1, hm.2⟩; linarith
      simp [chiEightCore, indicator, this]
  simp [this]

theorem tsupport_conductorTest (R : ℝ) :
    tsupport (conductorTest R) ⊆ Icc (-(5 * R)) (5 * R) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h : ¬ 5 * R < |x| := fun h => hx (conductorTest_eq_zero h)
  push Not at h
  exact ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩

theorem paperFT_conductorTest (R : ℝ) (z : ℂ) :
    paperFT (conductorTest R) z =
      paperFT (weilRadicalTest R) z * paperFT (chiEightCore (4 * R)) z :=
  paperFT_convolution
    (((contDiff_weilRadicalTest R).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_weilRadicalTest R).mul_right)
    (integrable_chiEightCore_mul_exp _ z)

theorem paperFT_conductorTest_half_I (R : ℝ) : paperFT (conductorTest R) (I / 2) = 0 := by
  rw [paperFT_conductorTest, paperFT_weilRadicalTest_half_I, zero_mul]

theorem paperFT_conductorTest_neg_half_I (R : ℝ) :
    paperFT (conductorTest R) (-(I / 2)) = 0 := by
  rw [paperFT_conductorTest, paperFT_weilRadicalTest_neg_half_I, zero_mul]

/-! ### Zero sides of the double radical test -/

/-- A zero-side bound from a pointwise bound at the two evaluation points of each zero. -/
theorem norm_zeroConfig_W_le_of_pointwise (Z : ZeroConfig)
    (hsum : Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))))
    {f : ℝ → ℂ} {P Q : ℝ} (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q)
    (h1 : ∀ ρ : Z.carrier, ‖paperFT f (gammaOf ρ)‖ ≤ P)
    (h2 : ∀ ρ : Z.carrier, ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖ ≤
      Q * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) :
    ‖Z.W f f‖ ≤ (5 / 4) * (∑' ρ : Z.carrier,
      (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) * (P * Q) := by
  have hpt : ∀ ρ : Z.carrier, ‖Z.Wsummand f f ρ‖ ≤
      (5 / 4) * (P * Q) * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    have hq := one_div_one_add_abs_im_sq_le (Z.strip ρ ρ.2)
    unfold ZeroConfig.Wsummand
    rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
    have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    calc (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ * ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (Z.mult ρ : ℝ) * P * (Q * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) := by
          gcongr
          · exact h1 ρ
          · exact h2 ρ
      _ ≤ (Z.mult ρ : ℝ) * P * (Q * ((5 / 4) * (1 / (1 + Complex.normSq (gammaOf ρ))))) := by
          gcongr
      _ = (5 / 4) * (P * Q) * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by ring
  have hsum' : Summable (fun ρ : Z.carrier => ‖Z.Wsummand f f ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsum.mul_left _)
  unfold ZeroConfig.W
  refine (norm_tsum_le_tsum_norm hsum').trans ?_
  refine (Summable.tsum_le_tsum hpt hsum' (hsum.mul_left _)).trans (le_of_eq ?_)
  rw [tsum_mul_left]; ring

theorem summable_chiEightZeros :
    Summable (fun ρ : chiEightZeros.carrier =>
      (chiEightZeros.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.ThmE.localCountChi (q := 8) (χ := dirichletChiEight)
    (by norm_num) dirichletChiEight_isPrimitive
  refine WeilEF.zero_sum_inv_sq_gen chiEightZeros hA₀ fun t => ?_
  have := Zeta23.ThmE.LZeros_N (Zeta23.ThmE.LSeam_of (q := 8) (by norm_num)
    dirichletChiEight_isPrimitive) t (t + 1)
  simpa [chiEightZeros, this] using hloc t

theorem summable_zetaZeroConfig :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
  have := WeilEF.zero_sum_inv_sq zetaSeam
  simpa [zetaZeroConfig] using this

theorem norm_paperFT_riemannPhiCore_le (L : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (riemannPhiCore L) z‖ ≤ ∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|) := by
  unfold paperFT
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _)
    (integrable_norm_riemannPhiKernel_mul_exp (by norm_num)) (Eventually.of_forall fun u => ?_))
  simp only
  rw [norm_mul]
  have hc : ‖riemannPhiCore L u‖ ≤ ‖Φ u‖ := by
    unfold riemannPhiCore indicator; split_ifs <;> simp
  exact mul_le_mul hc (norm_cexp_I_mul_le_exp hz u) (norm_nonneg _) (norm_nonneg _)

/-- **The `ζ` zero side of the double radical test decays.**  `‖W_ζ(g_R)‖ ≤ K R e^{-R/2}`. -/
theorem exists_norm_W_zeta_conductorTest_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R →
    ‖zetaZeroConfig.W (conductorTest R) (conductorTest R)‖ ≤ K * (R * Real.exp (-(R / 2))) := by
  obtain ⟨K₀, hK₀, hK⟩ := exists_weilRadicalTest_norms_le
  obtain ⟨C₆, hC₆0, hC₆⟩ := exists_superexp_le 6
  set E₀ := 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) with hE₀
  have hE0 : 0 ≤ E₀ := by
    have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
    have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
    rw [hE₀]; positivity
  set A := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hA
  have hA0 : 0 ≤ A := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  set B₈ := ∫ u : ℝ, ‖chiEightKernel u‖ * Real.exp (1 / 2 * |u|) with hB₈
  have hB₈0 : 0 ≤ B₈ := integral_nonneg fun _ => by positivity
  set SZ := ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) with hSZ
  have hSZ0 : 0 ≤ SZ := tsum_nonneg fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by have := Complex.normSq_nonneg (gammaOf (ρ : ℂ)); linarith)
  refine ⟨5 / 4 * SZ * (E₀ * C₆ * Real.exp (1 / 4) * A * B₈ * (K₀ * B₈)), by positivity,
    fun R hR => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  set ε := ∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|) with hε
  have hε0 : 0 ≤ ε := integral_nonneg fun _ => by positivity
  have hεle : ε ≤ E₀ * C₆ * Real.exp (-(R - 1 / 4)) :=
    riemannPhiTail_bound_le E₀ C₆ hE₀ hC₆ hR (by norm_num)
  have h := norm_zeroConfig_W_le_of_pointwise zetaZeroConfig summable_zetaZeroConfig
    (f := conductorTest R) (P := ε * A * B₈) (Q := Real.exp (R / 2) * (R * K₀) * B₈)
    (by positivity) (by positivity) ?_ ?_
  · rw [← hSZ] at h
    refine h.trans ?_
    have hexp : Real.exp (-(R - 1 / 4)) * Real.exp (R / 2) =
        Real.exp (1 / 4) * Real.exp (-(R / 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc 5 / 4 * SZ * (ε * A * B₈ * (Real.exp (R / 2) * (R * K₀) * B₈))
        ≤ 5 / 4 * SZ * ((E₀ * C₆ * Real.exp (-(R - 1 / 4))) * A * B₈ *
            (Real.exp (R / 2) * (R * K₀) * B₈)) := by gcongr
      _ = 5 / 4 * SZ * (E₀ * C₆ * A * B₈ * (K₀ * B₈)) * R *
            (Real.exp (-(R - 1 / 4)) * Real.exp (R / 2)) := by ring
      _ = _ := by rw [hexp]; ring
  · intro ρ
    have hmem := ρ.2
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
    obtain ⟨hc1, -⟩ := paperFT_riemannPhiCore_at_zero hmem R
    rw [paperFT_conductorTest, norm_mul, paperFT_weilRadicalTest, hc1, norm_mul, norm_neg]
    exact mul_le_mul (mul_le_mul (norm_paperFT_riemannPhiTail_le (by norm_num) hIm)
      (norm_paperFT_weilBumpPolarFree_le (by linarith)) (norm_nonneg _) hε0)
      (norm_paperFT_chiEightCore_le _ hIm) (norm_nonneg _) (by positivity)
  · intro ρ
    have hmem := ρ.2
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact (WeilEF.abs_gammaOf_im_lt hstrip').le
    rw [paperFT_conductorTest, norm_mul]
    have hv2 : ‖paperFT (weilRadicalTest R) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤
        Real.exp (R / 2) * (R * K₀) * (1 / (1 + |(ρ : ℂ).im|) ^ 2) := by
      have h := norm_paperFT_le_decay (contDiff_weilRadicalTest R)
        (fun u hu => by
          by_contra h; push Not at h; exact hu (weilRadicalTest_eq_zero h))
        ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))
      have hre : ((starRingEnd ℂ) (gammaOf (ρ : ℂ))).re = (ρ : ℂ).im := by
        rw [Complex.conj_re, WeilEF.gammaOf_re]
      rw [hre] at h
      refine h.trans ?_
      have he : Real.exp (|((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| * R) ≤ Real.exp (R / 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hden : 0 < (1 + |(ρ : ℂ).im|) ^ 2 := by positivity
      rw [div_eq_mul_one_div, mul_assoc]
      rw [show Real.exp (R / 2) * (R * K₀) * (1 / (1 + |(ρ : ℂ).im|) ^ 2) =
        Real.exp (R / 2) * (R * K₀ * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) by ring]
      exact mul_le_mul he (mul_le_mul_of_nonneg_right (hK R hR0) (by positivity))
        (by positivity) (Real.exp_pos _).le
    calc ‖paperFT (weilRadicalTest R) ((starRingEnd ℂ) (gammaOf ρ))‖ *
          ‖paperFT (chiEightCore (4 * R)) ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (Real.exp (R / 2) * (R * K₀) * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) * B₈ :=
          mul_le_mul hv2 (norm_paperFT_chiEightCore_le _ hIm') (norm_nonneg _) (by positivity)
      _ = Real.exp (R / 2) * (R * K₀) * B₈ * (1 / (1 + |(ρ : ℂ).im|) ^ 2) := by ring

/-- **The `L(s, χ₈)` zero side of the double radical test decays.**  At each zero of `L(s, χ₈)` the
theta factor sees only its tail beyond `4R`, which is `O(e^{-R})`. -/
theorem exists_norm_W_chiEight_conductorTest_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R →
    ‖chiEightZeros.W (conductorTest R) (conductorTest R)‖ ≤ K * (R * Real.exp (-(R / 2))) := by
  obtain ⟨K₀, hK₀, hK⟩ := exists_weilRadicalTest_norms_le
  obtain ⟨C₈, hC₈0, hC₈⟩ := exists_integral_chiEightTail_le
  set A := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hA
  have hA0 : 0 ≤ A := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  set B₈ := ∫ u : ℝ, ‖chiEightKernel u‖ * Real.exp (1 / 2 * |u|) with hB₈
  have hB₈0 : 0 ≤ B₈ := integral_nonneg fun _ => by positivity
  set BΦ := ∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|) with hBΦ
  have hBΦ0 : 0 ≤ BΦ := integral_nonneg fun _ => by positivity
  set S₈ := ∑' ρ : chiEightZeros.carrier,
    (chiEightZeros.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) with hS₈
  have hS₈0 : 0 ≤ S₈ := tsum_nonneg fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by have := Complex.normSq_nonneg (gammaOf (ρ : ℂ)); linarith)
  refine ⟨5 / 4 * S₈ * (BΦ * A * C₈ * (K₀ * B₈)), by positivity, fun R hR => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  have htail : ∫ u : ℝ, ‖chiEightTail (4 * R) u‖ * Real.exp (1 / 2 * |u|) ≤
      C₈ * Real.exp (-R) := by
    have := hC₈ (4 * R) (by linarith)
    rwa [show 4 * R / 4 = R by ring] at this
  have hstripOf : ∀ ρ : chiEightZeros.carrier, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := fun ρ => by
    have h : Zeta23.ThmE.IsNontrivialZeroL dirichletChiEight (ρ : ℂ) := ρ.2
    exact ⟨h.2.1, h.2.2⟩
  have h := norm_zeroConfig_W_le_of_pointwise chiEightZeros summable_chiEightZeros
    (f := conductorTest R) (P := BΦ * A * (C₈ * Real.exp (-R)))
    (Q := Real.exp (R / 2) * (R * K₀) * B₈) (by positivity) (by positivity) ?_ ?_
  · rw [← hS₈] at h
    refine h.trans (le_of_eq ?_)
    have hexp : Real.exp (-R) * Real.exp (R / 2) = Real.exp (-(R / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc 5 / 4 * S₈ * (BΦ * A * (C₈ * Real.exp (-R)) * (Real.exp (R / 2) * (R * K₀) * B₈))
        = 5 / 4 * S₈ * (BΦ * A * C₈ * (K₀ * B₈)) * R * (Real.exp (-R) * Real.exp (R / 2)) := by
          ring
      _ = _ := by rw [hexp]; ring
  · intro ρ
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt (hstripOf ρ)).le
    have hzero : paperFT chiEightKernel (gammaOf ρ) = 0 :=
      paperFT_chiEightKernel_gammaOf_eq_zero ρ.2
    rw [paperFT_conductorTest, norm_mul, paperFT_weilRadicalTest, norm_mul,
      paperFT_chiEightCore_eq _ hIm, hzero, zero_sub, norm_neg]
    refine mul_le_mul (mul_le_mul (norm_paperFT_riemannPhiCore_le R hIm)
      (norm_paperFT_weilBumpPolarFree_le (by linarith)) (norm_nonneg _) hBΦ0)
      ((norm_paperFT_chiEightTail_le _ hIm).trans htail) (norm_nonneg _) (by positivity)
  · intro ρ
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact (WeilEF.abs_gammaOf_im_lt (hstripOf ρ)).le
    rw [paperFT_conductorTest, norm_mul]
    have hv2 : ‖paperFT (weilRadicalTest R) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤
        Real.exp (R / 2) * (R * K₀) * (1 / (1 + |(ρ : ℂ).im|) ^ 2) := by
      have h := norm_paperFT_le_decay (contDiff_weilRadicalTest R)
        (fun u hu => by
          by_contra h; push Not at h; exact hu (weilRadicalTest_eq_zero h))
        ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))
      have hre : ((starRingEnd ℂ) (gammaOf (ρ : ℂ))).re = (ρ : ℂ).im := by
        rw [Complex.conj_re, WeilEF.gammaOf_re]
      rw [hre] at h
      refine h.trans ?_
      have he : Real.exp (|((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| * R) ≤ Real.exp (R / 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hden : 0 < (1 + |(ρ : ℂ).im|) ^ 2 := by positivity
      rw [div_eq_mul_one_div, mul_assoc]
      rw [show Real.exp (R / 2) * (R * K₀) * (1 / (1 + |(ρ : ℂ).im|) ^ 2) =
        Real.exp (R / 2) * (R * K₀ * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) by ring]
      exact mul_le_mul he (mul_le_mul_of_nonneg_right (hK R hR0) (by positivity))
        (by positivity) (Real.exp_pos _).le
    calc ‖paperFT (weilRadicalTest R) ((starRingEnd ℂ) (gammaOf ρ))‖ *
          ‖paperFT (chiEightCore (4 * R)) ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (Real.exp (R / 2) * (R * K₀) * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) * B₈ :=
          mul_le_mul hv2 (norm_paperFT_chiEightCore_le _ hIm') (norm_nonneg _) (by positivity)
      _ = Real.exp (R / 2) * (R * K₀) * B₈ * (1 / (1 + |(ρ : ℂ).im|) ^ 2) := by ring

/-! ### The limit transform and its mass on the real line -/

/-- The limit transform `G(z) = Φ̂(z) κ̂₂(z) K̂(z)` of the double radical tests. -/
def conductorLimit (z : ℂ) : ℂ :=
  paperFT Φ z * paperFT weilBumpPolarFree z * paperFT chiEightKernel z

theorem superExpDecay_weilBumpPolarFree : SuperExpDecay weilBumpPolarFree :=
  ⟨contDiff_weilBumpPolarFree.continuous, fun c =>
    (contDiff_weilBumpPolarFree.continuous.norm.mul (by fun_prop)).integrable_of_hasCompactSupport
      hasCompactSupport_weilBumpPolarFree.norm.mul_right⟩

theorem differentiableOn_conductorLimit : DifferentiableOn ℂ conductorLimit unitStripSet := by
  have h1 : Differentiable ℂ (paperFT Φ) := by
    intro z
    have : paperFT Φ = fun z => xi (1 / 2 + I * z) := by
      funext z; rw [paperFT_riemannPhiKernel, riemannPhiTransform_eq_xi]
    rw [this]
    exact (xi_differentiable _).comp z (by fun_prop)
  have h2 := superExpDecay_weilBumpPolarFree.differentiable_paperFT
  have h3 : DifferentiableOn ℂ (paperFT chiEightKernel) unitStripSet := by
    have : paperFT chiEightKernel = fun z => thetaPowerXiC (1 / 2) (-z) := by
      funext z; exact paperFT_chiEightKernel z
    rw [this]
    refine (differentiableOn_thetaPowerXiC (by norm_num)).comp (by fun_prop) fun z hz => ?_
    show |(-z).im| < 1
    rw [Complex.neg_im, abs_neg]; exact hz
  exact ((h1.differentiableOn).mul h2.differentiableOn).mul h3

theorem integral_weilBump_mul_exp_pos : 0 < ∫ u : ℝ, weilBump u * Real.exp (3 / 4 * u) := by
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    ((weilBump.contDiff (n := 0)).continuous.mul (by fun_prop))
    weilBump.hasCompactSupport.mul_right
    (fun u => mul_nonneg weilBump.nonneg (Real.exp_pos _).le) ?_
  rw [weilBump.one_of_mem_closedBall (by simp [weilBump])]; simp

theorem conductorLimit_ne_zero : conductorLimit (-(3 / 4 * I)) ≠ 0 := by
  unfold conductorLimit
  have hz : 1 / 2 + I * -(3 / 4 * I) = (5 / 4 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · rw [paperFT_riemannPhiKernel, riemannPhiTransform_eq_xi, hz]
    intro h
    have h1 := (xi_eq_zero_iff (s := 5 / 4) (by norm_num) (by norm_num)).mp h
    exact riemannZeta_ne_zero_of_one_lt_re (by norm_num) h1
  · rw [paperFT_weilBumpPolarFree]
    have h0 : paperFT weilBumpC (-(3 / 4 * I)) =
        ((∫ u : ℝ, weilBump u * Real.exp (3 / 4 * u) : ℝ) : ℂ) := by
      unfold paperFT weilBumpC
      rw [← integral_complex_ofReal]
      congr 1; funext u
      push_cast
      congr 1; congr 1; ring_nf; rw [Complex.I_sq]; ring
    rw [h0]
    refine mul_ne_zero ?_ (by exact_mod_cast integral_weilBump_mul_exp_pos.ne')
    ring_nf; rw [Complex.I_sq]; norm_num
  · rw [paperFT_chiEightKernel_eq (by simp; norm_num), hz]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · have : (0 : ℝ) < Real.sqrt 2 / 4 := by positivity
      exact_mod_cast this.ne'
    · rw [Ne, Complex.cpow_eq_zero_iff]; norm_num
    · intro h
      have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor dirichletChiEight
        (5 / 4) (Or.inr (by norm_num))
      rw [h, zero_div] at hL
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re dirichletChiEight
        (Or.inl dirichletChiEight_ne_one) (by norm_num) hL

/-- The limit transform does not vanish identically on the real line. -/
theorem exists_real_conductorLimit_ne_zero : ∃ τ₀ : ℝ, conductorLimit τ₀ ≠ 0 := by
  by_contra h
  push Not at h
  have han := differentiableOn_conductorLimit.analyticOnNhd isOpen_unitStripSet
  have hconn : IsPreconnected unitStripSet := by
    refine (Convex.isPreconnected ?_)
    intro x hx y hy s' t' hs ht hst
    show |(s' • x + t' • y).im| < 1
    have hx' : |x.im| < 1 := hx
    have hy' : |y.im| < 1 := hy
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    calc |s' * x.im + t' * y.im| ≤ s' * |x.im| + t' * |y.im| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ < 1 := by
          rcases eq_or_lt_of_le hs with h0 | h0
          · subst h0; simp at hst; subst hst; simpa using hy'
          · nlinarith [mul_lt_mul_of_pos_left hx' h0, mul_le_mul_of_nonneg_left hy'.le ht]
  have h0mem : (0 : ℂ) ∈ unitStripSet := by show |(0 : ℂ).im| < 1; simp
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), conductorLimit z = 0 := by
    have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
    exact htend.frequently (Eventually.frequently (Eventually.of_forall fun t => h t))
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hconn h0mem hfreq
  have hmem : -(3 / 4 * I) ∈ unitStripSet := by
    show |(-(3 / 4 * I)).im| < 1; simp; norm_num
  exact conductorLimit_ne_zero (hzero hmem)

/-- On the real line the double radical tests converge uniformly to the limit transform. -/
theorem exists_norm_paperFT_conductorTest_sub_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ τ : ℝ,
    ‖paperFT (conductorTest R) τ - conductorLimit τ‖ ≤ K * Real.exp (-R) := by
  obtain ⟨C₆, hC₆0, hC₆⟩ := exists_superexp_le 6
  obtain ⟨C₈, hC₈0, hC₈⟩ := exists_integral_chiEightTail_le
  set E₀ := 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) with hE₀
  have hE0 : 0 ≤ E₀ := by
    have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
    have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
    rw [hE₀]; positivity
  set A := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hA
  have hA0 : 0 ≤ A := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  set B₈ := ∫ u : ℝ, ‖chiEightKernel u‖ * Real.exp (1 / 2 * |u|) with hB₈
  have hB₈0 : 0 ≤ B₈ := integral_nonneg fun _ => by positivity
  set BΦ := ∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|) with hBΦ
  have hBΦ0 : 0 ≤ BΦ := integral_nonneg fun _ => by positivity
  refine ⟨A * (BΦ * C₈ + E₀ * C₆ * Real.exp (1 / 4) * B₈), by positivity, fun R hR τ => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  have hτ : |((τ : ℂ)).im| ≤ 1 / 2 := by simp
  set T₈ := paperFT (chiEightTail (4 * R)) τ with hT₈
  set Tζ := paperFT (riemannPhiTail R) τ with hTζ
  have hT₈b : ‖T₈‖ ≤ C₈ * Real.exp (-R) := by
    refine (norm_paperFT_chiEightTail_le _ hτ).trans ?_
    have := hC₈ (4 * R) (by linarith)
    rwa [show 4 * R / 4 = R by ring] at this
  have hTζb : ‖Tζ‖ ≤ E₀ * C₆ * Real.exp (1 / 4) * Real.exp (-R) := by
    refine (norm_paperFT_riemannPhiTail_le (by norm_num) hτ).trans
      ((riemannPhiTail_bound_le E₀ C₆ hE₀ hC₆ hR (by norm_num)).trans (le_of_eq ?_))
    rw [mul_assoc (E₀ * C₆), ← Real.exp_add]; congr 2; ring
  have hK : ‖paperFT chiEightKernel τ‖ ≤ B₈ :=
    norm_paperFT_le_of_norm_le_chiEightKernel continuous_chiEightKernel.aestronglyMeasurable
      (fun u => le_rfl) hτ
  have hcoreζ : ‖paperFT (riemannPhiCore R) τ‖ ≤ BΦ := norm_paperFT_riemannPhiCore_le R hτ
  have hκ : ‖paperFT weilBumpPolarFree τ‖ ≤ A :=
    norm_paperFT_weilBumpPolarFree_le (by simp only [Complex.ofReal_im, abs_zero]; norm_num)
  have hΦ : paperFT Φ τ = paperFT (riemannPhiCore R) τ + Tζ := by
    rw [paperFT_riemannPhiCore_eq, paperFT_riemannPhiKernel]; ring
  have hdiff : paperFT (conductorTest R) τ - conductorLimit τ =
      -(paperFT weilBumpPolarFree τ * (paperFT (riemannPhiCore R) τ * T₈ +
        Tζ * paperFT chiEightKernel τ)) := by
    unfold conductorLimit
    rw [paperFT_conductorTest, paperFT_weilRadicalTest, paperFT_chiEightCore_eq _ hτ, hΦ]
    ring
  rw [hdiff, norm_neg, norm_mul]
  calc ‖paperFT weilBumpPolarFree τ‖ * ‖paperFT (riemannPhiCore R) τ * T₈ +
        Tζ * paperFT chiEightKernel τ‖
      ≤ A * (BΦ * (C₈ * Real.exp (-R)) + E₀ * C₆ * Real.exp (1 / 4) * Real.exp (-R) * B₈) := by
        refine mul_le_mul hκ ((norm_add_le _ _).trans ?_) (norm_nonneg _) hA0
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul hcoreζ hT₈b (norm_nonneg _) hBΦ0)
          (mul_le_mul hTζb hK (norm_nonneg _) (by positivity))
    _ = A * (BΦ * C₈ + E₀ * C₆ * Real.exp (1 / 4) * B₈) * Real.exp (-R) := by ring

/-- **Mass of the double radical tests.**  `∫ |h_{g_R}|² ≥ c > 0` for all large `R`. -/
theorem exists_integral_normSq_conductorTest_ge : ∃ c R₀ : ℝ, 0 < c ∧ 1 ≤ R₀ ∧
    ∀ R : ℝ, R₀ ≤ R → c ≤ ∫ τ : ℝ, ‖paperFT (conductorTest R) τ‖ ^ 2 := by
  obtain ⟨τ₀, hτ₀⟩ := exists_real_conductorLimit_ne_zero
  obtain ⟨K, hK0, hK⟩ := exists_norm_paperFT_conductorTest_sub_le
  set m := ‖conductorLimit τ₀‖ with hm
  have hm0 : 0 < m := norm_pos_iff.mpr hτ₀
  -- continuity of the limit on the real line
  have hcont : ContinuousAt (fun τ : ℝ => conductorLimit τ) τ₀ := by
    have hd := differentiableOn_conductorLimit.differentiableAt
      (isOpen_unitStripSet.mem_nhds (show |((τ₀ : ℂ)).im| < 1 by simp))
    exact hd.continuousAt.comp Complex.continuous_ofReal.continuousAt
  obtain ⟨η, hη0, hη⟩ := Metric.continuousAt_iff.mp hcont (m / 2) (by linarith)
  -- the approximation error eventually below m/4
  have hev : ∀ᶠ R in atTop, K * Real.exp (-R) ≤ m / 4 := by
    have ht : Tendsto (fun R : ℝ => K * Real.exp (-R)) atTop (𝓝 0) := by
      simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul K
    exact ht.eventually (ge_mem_nhds (by linarith))
  obtain ⟨R₁, hR₁⟩ := hev.exists_forall_of_atTop
  refine ⟨η * (m / 4) ^ 2, max R₁ 1, by positivity, le_max_right _ _, fun R hR => ?_⟩
  have hR1 : 1 ≤ R := le_trans (le_max_right _ _) hR
  have herr := hR₁ R (le_trans (le_max_left _ _) hR)
  have hlow : ∀ τ ∈ Icc (τ₀ - η / 2) (τ₀ + η / 2),
      (m / 4) ^ 2 ≤ ‖paperFT (conductorTest R) τ‖ ^ 2 := by
    intro τ hτ
    have hd : dist τ τ₀ < η := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hτ.1, hτ.2]
    have h1 := hη hd
    rw [dist_eq_norm] at h1
    have h2 : m / 2 ≤ ‖conductorLimit τ‖ := by
      have := norm_sub_norm_le (conductorLimit τ₀) (conductorLimit τ)
      rw [norm_sub_rev] at h1
      linarith
    have h3 := (hK R hR1 τ).trans herr
    have h4 : m / 4 ≤ ‖paperFT (conductorTest R) τ‖ := by
      have := norm_sub_norm_le (conductorLimit τ) (paperFT (conductorTest R) τ)
      rw [norm_sub_rev] at h3
      linarith
    exact pow_le_pow_left₀ (by positivity) h4 2
  have hint := integrable_normSq_paperFT (contDiff_conductorTest R) (tsupport_conductorTest R)
  calc η * (m / 4) ^ 2 = ∫ τ in Icc (τ₀ - η / 2) (τ₀ + η / 2), (m / 4) ^ 2 := by
        rw [setIntegral_const]
        simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by linarith)]; ring
    _ ≤ ∫ τ in Icc (τ₀ - η / 2) (τ₀ + η / 2), ‖paperFT (conductorTest R) τ‖ ^ 2 :=
        setIntegral_mono_on (integrableOn_const (by simp) (by simp)) hint.integrableOn
          measurableSet_Icc hlow
    _ ≤ ∫ τ : ℝ, ‖paperFT (conductorTest R) τ‖ ^ 2 :=
        setIntegral_le_integral hint (Eventually.of_forall fun _ => by positivity)

/-! ### Deleting the primes `p ≡ ±3 (mod 8)` -/

theorem integrable_normSq_paperFT_mul_weilAtomSymbol_of {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (lam : ℕ → ℝ) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) := by
  have hcos := integrable_normSq_paperFT_mul_cos hf hfs
  refine ((integrable_normSq_paperFT_mul_arch hf hfs).sub
    (integrable_finsetSum (Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊) fun n _ =>
      (hcos (Real.log n)).const_mul (2 * (lam n / Real.sqrt n)))).congr
    (Eventually.of_forall fun τ => ?_)
  simp only [Pi.sub_apply]
  unfold weilAtomSymbol
  have harg : ∀ n : ℕ, 2 * π * Real.log n * (τ / (2 * π)) = τ * Real.log n := fun n => by
    field_simp
  simp only [harg]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by ring

/-- The weights `Λ(n)(1 - t + tχ₈(n))` interpolate affinely between `Λ` and `Λχ₈`. -/
theorem weilAtomSymbol_chiEightMix (t : ℝ) (N : ℕ) (ξ : ℝ) :
    weilAtomSymbol (fun n => ArithmeticFunction.vonMangoldt n * (1 - t + t * chiEight n)) N ξ =
      (1 - t) * weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) N ξ +
        t * weilAtomSymbol (fun n => ArithmeticFunction.vonMangoldt n * chiEight n) N ξ := by
  unfold weilAtomSymbol
  have hs : ∑ n ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt n * (1 - t + t * chiEight n) *
      (1 / Real.sqrt n) * (2 * Real.cos (2 * π * Real.log n * ξ)) =
      (1 - t) * ∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (1 / Real.sqrt n) * (2 * Real.cos (2 * π * Real.log n * ξ)) +
      t * ∑ n ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt n * chiEight n *
        (1 / Real.sqrt n) * (2 * Real.cos (2 * π * Real.log n * ξ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hs]; ring

/-- **Exact energy of the mixed weights.**  For a polar-constrained level-`a` test,
`∫ |h_f|² S_{Λ(1-t+tχ₈)} = 2π(1-t) Re W_ζ(f) + t (2π Re W_{χ₈}(f) - log 8 ∫ |h_f|²)`. -/
theorem integral_weilAtomSymbol_chiEightMix {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0)
    (hm : paperFT f (-(I / 2)) = 0) (t : ℝ) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (1 - t + t * chiEight n))
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      2 * π * (1 - t) * (zetaZeroConfig.W f f).re +
        t * (2 * π * (chiEightZeros.W f f).re - Real.log 8 * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2) := by
  have hΛ := integrable_normSq_paperFT_mul_weilAtomSymbol hf hfs
  have hχ := integrable_normSq_paperFT_mul_weilAtomSymbol_of hf hfs
    (fun n => ArithmeticFunction.vonMangoldt n * chiEight n)
  have hpt : ∀ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
      (fun n => ArithmeticFunction.vonMangoldt n * (1 - t + t * chiEight n))
      ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      (1 - t) * (‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) +
      t * (‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * chiEight n) ⌊Real.exp (2 * a)⌋₊
          (τ / (2 * π))) := by
    intro τ; rw [weilAtomSymbol_chiEightMix]; ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add (hΛ.const_mul _)
    (hχ.const_mul _), integral_const_mul, integral_const_mul,
    integral_weilAtomSymbol_chiEight ha hf hfs]
  have hW := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hf hfs hp hm
  have hWre : (zetaZeroConfig.W f f).re = 1 / (2 * π) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ⌊Real.exp (2 * a)⌋₊
        (τ / (2 * π)) := by
    rw [hW, Complex.ofReal_re]
  rw [hWre]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **Weil positivity fails when the primes `p ≡ ±3 (mod 8)` are weighted down.**  For every
`t > 0` the weights `Λ(n)(1 - t + tχ₈(n))` give negative finite-atom Weil symbol energy on some
polar-constrained `C²` test.  At `t = 1/2` these are the von Mangoldt weights on `n ≡ ±1 (mod 8)`
with half weight on the powers of `2`; at `t = 1` they are the twisted weights `Λχ₈`.

On the tests `f_R ⋆ K_{≤4R}`, radical for both `ζ` and `L(s, χ₈)`, both zero sides are
`O(R e^{-R/2})` while `∫ |h|² ≥ c`, so the energy is `-t log 8 ∫ |h|² + o(1)`: the defect is the
logarithm of the conductor. -/
theorem chiEightMix_weilAtomSymbol_not_nonneg {t : ℝ} (ht : 0 < t) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (1 - t + t * chiEight n))
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  obtain ⟨c, R₀, hc, hR₀, hmass⟩ := exists_integral_normSq_conductorTest_ge
  obtain ⟨KW, hKW0, hKW⟩ := exists_norm_W_zeta_conductorTest_le
  obtain ⟨K8, hK80, hK8⟩ := exists_norm_W_chiEight_conductorTest_le
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  set M := 2 * π * |1 - t| * KW + 2 * π * t * K8 with hM
  have hM0 : 0 ≤ M := by positivity
  have hlim : Tendsto (fun R : ℝ => M * (R * Real.exp (-(R / 2)))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    have h2 := (h.const_mul 2).const_mul M
    simp only [mul_zero] at h2
    refine h2.congr fun R => ?_
    simp only [Function.comp_apply, id, pow_one]; ring
  obtain ⟨R, hRsmall, hRbig⟩ := ((hlim.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < t * Real.log 8 * c))).and (eventually_ge_atTop R₀)).exists
  have hR1 : 1 ≤ R := hR₀.trans hRbig
  have hR0 : 0 ≤ R := by linarith
  refine ⟨5 * R, by linarith, conductorTest R, contDiff_conductorTest R,
    tsupport_conductorTest R, paperFT_conductorTest_half_I R,
    paperFT_conductorTest_neg_half_I R, ?_⟩
  rw [integral_weilAtomSymbol_chiEightMix (by linarith) (contDiff_conductorTest R)
    (tsupport_conductorTest R) (paperFT_conductorTest_half_I R)
    (paperFT_conductorTest_neg_half_I R)]
  have hW1 : (1 - t) * (zetaZeroConfig.W (conductorTest R) (conductorTest R)).re ≤
      |1 - t| * (KW * (R * Real.exp (-(R / 2)))) := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hKW R hR1))
      (abs_nonneg _)
  have hW2 : (chiEightZeros.W (conductorTest R) (conductorTest R)).re ≤
      K8 * (R * Real.exp (-(R / 2))) :=
    (Complex.re_le_norm _).trans (hK8 R hR1)
  have hm := hmass R hRbig
  have hπ : 0 < π := Real.pi_pos
  have key : 2 * π * (1 - t) * (zetaZeroConfig.W (conductorTest R) (conductorTest R)).re +
      t * (2 * π * (chiEightZeros.W (conductorTest R) (conductorTest R)).re) ≤
      M * (R * Real.exp (-(R / 2))) := by
    have h1 := mul_le_mul_of_nonneg_left hW1 (by positivity : (0 : ℝ) ≤ 2 * π)
    have h2 := mul_le_mul_of_nonneg_left hW2 (by positivity : (0 : ℝ) ≤ 2 * π * t)
    rw [hM]
    nlinarith
  have hc8 : t * Real.log 8 * c ≤ t * (Real.log 8 * ∫ τ : ℝ, ‖paperFT (conductorTest R) τ‖ ^ 2) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm hlog8.le) ht.le
  nlinarith

end RHTower

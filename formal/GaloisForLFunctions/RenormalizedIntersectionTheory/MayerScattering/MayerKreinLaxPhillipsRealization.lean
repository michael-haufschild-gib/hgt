import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.LewisPeriodReflectionPositivity
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCoreMellin
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEpsteinHeightMeasurability
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Linear Independence of Resonant Period Cores and Canonical Krein–Lax–Phillips Realization

This module constructs the canonical `s`-independent Krein–Lax–Phillips realization on the actual
space of Cauchy-transformed Mayer/Lewis period cores:

1. **Unconditional Linear Independence on `(0, ∞)`:** Both the resonant Mayer scattering cores
   `s ↦ fieldCore (2 * s)` and the Cauchy-transformed Lewis period cores
   `s ↦ mayerPeriodCore s = positiveMellinConvolution (cauchyKernel (2 * s)) (fieldCore (2 * s))`
   indexed by `upperMayerResonances` (`0 < Re s < 1/2`, `0 < Im s`, `IsMayerScatteringResonance s`)
   are linearly independent over `ℂ` on `(0, ∞)` (hence in `ℝ → ℂ`).
2. **Canonical `s`-Independent Krein–Lax–Phillips Space `W_PM`:** On
   `mayerPeriodKreinSpace = span_ℂ {mayerPeriodCore s | s ∈ upperMayerResonances}`, we construct:
   - the positive-definite Hermitian inner product `mayerKreinPosInner`,
   - the unitary Riemann–Mayer reflection involution `mayerKreinReflection` (`Θ_PM(b_s) = b_{s^♯}`),
   - the reflection-invariant indefinite Krein form `mayerKreinForm` (`[u, v]_PM = ⟨u, Θ_PM v⟩^+`),
   - the Lax–Phillips resonance generator `mayerLaxPhillipsGenerator` (`B_PM(b_s) = -i(s - 1/4) b_s`),
     which is Krein self-adjoint (`[B_PM u, v]_PM = [u, B_PM v]_PM`).
3. **Sharp Off-Line Negative Norm, Polar Index, and Four-Way RH Equivalence:**
   - Every critical-line resonance `s.re = 1/4` has real eigenvalue `s.im` and `[b_s, b_s]_PM = 1`.
   - Every off-line resonance `s.re ≠ 1/4` produces an explicit antisymmetric period combination
     `η_s^- = b_s - b_{s^♯}` with `[η_s^-, η_s^-]_PM = -2 < 0`.
   - The subspace `mayerNegativeSubspace` spanned by `{η_s^- | s ∈ upperRightMayerResonances}` is
     strictly negative definite for `[·, ·]_PM`, has basis indexed by `upperRightMayerResonances`
     satisfying `2 * upperRightMayerResonances.encard = boostPolarIndex ratCorr`, and
     `(∀ u, 0 ≤ ([u, u]_PM).re) ↔ (∀ s ∈ upperMayerResonances, s.re = 1/4) ↔ RiemannHypothesis ↔
       RenormalizedHodgeIndex ratCorr`.
-/

open Complex Set Filter MeasureTheory Topology Finset
open scoped BigOperators
open GaloisForLFunctions.AdelicKreinGeometry GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone MayerCauchyMellinSymbol MayerScatteringCore MayerCoreMellin
open MayerEpsteinHeightMeasurability

set_option autoImplicit false

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-! ## Upper Mayer resonances and Cauchy-transformed Lewis period cores -/

/-- Upper-half-plane Mayer scattering resonances (`0 < Re s < 1/2`, `0 < Im s`). -/
def upperMayerResonances : Set ℂ :=
  {s | 0 < s.im ∧ IsMayerScatteringResonance s}

/-- `riemannMayerReflect` restricts to an involution of `upperMayerResonances`. -/
def reflectUpperResonance : upperMayerResonances ≃ upperMayerResonances where
  toFun s := ⟨riemannMayerReflect s.1,
    ⟨by rw [riemannMayerReflect_im]; exact s.2.1,
     isMayerScatteringResonance_reflect_iff.mpr s.2.2⟩⟩
  invFun s := ⟨riemannMayerReflect s.1,
    ⟨by rw [riemannMayerReflect_im]; exact s.2.1,
     isMayerScatteringResonance_reflect_iff.mpr s.2.2⟩⟩
  left_inv s := Subtype.ext (riemannMayerReflect_involutive s.1)
  right_inv s := Subtype.ext (riemannMayerReflect_involutive s.1)

@[simp]
theorem reflectUpperResonance_coe (s : upperMayerResonances) :
    (reflectUpperResonance s : ℂ) = riemannMayerReflect s.1 := rfl

@[simp]
theorem reflectUpperResonance_involutive (s : upperMayerResonances) :
    reflectUpperResonance (reflectUpperResonance s) = s :=
  Subtype.ext (riemannMayerReflect_involutive s.1)

theorem reflectUpperResonance_eq_self_iff (s : upperMayerResonances) :
    reflectUpperResonance s = s ↔ s.1.re = 1 / 4 := by
  rw [Subtype.ext_iff, reflectUpperResonance_coe, riemannMayerReflect_fixed_iff]

/-- The actual Cauchy-transformed Lewis period core associated to `fieldCore (2s)` on `(0, ∞)`. -/
def mayerPeriodCore (s : ℂ) : ℝ → ℂ :=
  _root_.RHTower.positiveMellinConvolution (cauchyKernel (2 * s)) (fieldCore (2 * s))

/-- On `periodSegment`, at any upper Mayer resonance `s`, `mayerPeriodCore s` equals the actual
Mayer scattering period minus its outgoing/incoming boundary power pair. -/
theorem mayerPeriodCore_eq_periodValue_sub_boundary {s : ℂ} (hs : s ∈ upperMayerResonances)
    {a : ℝ} (ha : a ∈ MayerScatteringPeriod.periodSegment) :
    mayerPeriodCore s a =
      MayerScatteringPeriod.periodValue (2 * s) a -
        (2 * riemannZeta (2 * s - 1) / (2 * s - 1)) * scatteringPowers (2 * s) a := by
  obtain ⟨him, hres⟩ := hs
  have hw0 : 0 < (2 * s).re := by simp; linarith [hres.1]
  have hwim : 0 < (2 * s).im := by simp; linarith
  have hζ0 : riemannZeta (2 * s) = 0 :=
    (isMayerScatteringResonance_iff_zeta_zero hres.1 hres.2.1).mp hres
  have h := cauchyKernel_core_period hw0 hwim ha
  unfold mayerPeriodCore
  rw [h, hζ0, zero_mul, sub_zero]

private theorem cauchyWeight_inv_eq {w : ℂ} {t : ℝ} (ht : 0 < t) :
    cauchyWeight w t⁻¹ = (t : ℂ) ^ (w + 2) * cauchyWeight w t := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have ht2_pos : 0 < t ^ 2 := sq_pos_of_pos ht
  have hsum_pos : 0 < 1 + t ^ 2 := by positivity
  have hfac : ((1 + (t⁻¹) ^ 2 : ℝ) : ℂ) =
      (((t ^ 2)⁻¹ : ℝ) : ℂ) * ((1 + t ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp [ht.ne']
    ring
  have hpow_t2 : (((t ^ 2)⁻¹ : ℝ) : ℂ) ^ (-((w + 2) / 2)) = (t : ℂ) ^ (w + 2) := by
    rw [ofReal_inv_cpow_pos ht2_pos, neg_neg, show (t ^ 2 : ℝ) = t * t by ring,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ht.le ht.le,
      ← Complex.cpow_add _ _ htC]
    congr 1
    ring
  unfold cauchyWeight
  rw [hfac,
    Complex.mul_cpow_ofReal_nonneg (inv_pos.mpr ht2_pos).le hsum_pos.le, hpow_t2]

/-- Every `mayerPeriodCore s` (`Re s > 0`, `Im s > 0`) is a `+1` fixed function of the Lewis
modular inversion `lewisModularInversion s` across `(0, ∞)`. -/
theorem lewisModularInversion_mayerPeriodCore {s : ℂ} (hs0 : 0 < s.re) (hsim : 0 < s.im)
    {a : ℝ} (ha : 0 < a) :
    lewisModularInversion s (mayerPeriodCore s) a = mayerPeriodCore s a := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  dsimp only [lewisModularInversion, mayerPeriodCore, _root_.RHTower.positiveMellinConvolution]
  rw [integral_Ioi_zero_inv_subst]
  have hcongr :
      (∫ t in Ioi (0 : ℝ),
          t ^ (-2 : ℝ) • (cauchyKernel (2 * s) t⁻¹ * fieldCore (2 * s) (a⁻¹ / t⁻¹) / ↑t⁻¹)) =
        (a : ℂ) ^ (2 * s) *
          ∫ t in Ioi (0 : ℝ), cauchyKernel (2 * s) t * fieldCore (2 * s) (a / t) / ↑t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have ht_invC : ((t⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_pos.mpr ht0).ne'
    have hdiv : a⁻¹ / t⁻¹ = (a / t)⁻¹ := by field_simp [ha.ne', ht0.ne']
    have hcore : fieldCore (2 * s) (a / t)⁻¹ =
        (a : ℂ) ^ (2 * s) * (t : ℂ) ^ (-(2 * s)) * fieldCore (2 * s) (a / t) := by
      have hrec := lewisModularInversion_fieldCore hs0 hsim (div_pos ha ht0)
      dsimp only [lewisModularInversion] at hrec
      have hquot : ((a / t : ℝ) : ℂ) ^ (2 * s) = (a : ℂ) ^ (2 * s) * (t : ℂ) ^ (-(2 * s)) := by
        rw [div_eq_mul_inv, Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg ha.le (inv_pos.mpr ht0).le,
          ofReal_inv_cpow_pos ht0]
      calc
        fieldCore (2 * s) (a / t)⁻¹ =
            ((a / t : ℝ) : ℂ) ^ (2 * s) *
              (((a / t : ℝ) : ℂ) ^ (-(2 * s)) * fieldCore (2 * s) (a / t)⁻¹) := by
          rw [← mul_assoc, ← Complex.cpow_add _ _
            (Complex.ofReal_ne_zero.mpr (div_pos ha ht0).ne'), add_neg_cancel,
            Complex.cpow_zero, one_mul]
        _ = ((a / t : ℝ) : ℂ) ^ (2 * s) * fieldCore (2 * s) (a / t) := by rw [hrec]
        _ = (a : ℂ) ^ (2 * s) * (t : ℂ) ^ (-(2 * s)) * fieldCore (2 * s) (a / t) := by rw [hquot]
    have ht_jac : ((t ^ (-2 : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ (-2 : ℂ) := by
      simpa using Complex.ofReal_cpow ht0.le (-2 : ℝ)
    have hker_inv : cauchyKernel (2 * s) t⁻¹ / ((t⁻¹ : ℝ) : ℂ) =
        (averagingFactor (2 * s))⁻¹ * ((t : ℂ) ^ (2 * s + 2) * cauchyWeight (2 * s) t) := by
      unfold cauchyKernel
      rw [cauchyWeight_inv_eq ht0,
        show (averagingFactor (2 * s))⁻¹ * ((t⁻¹ : ℝ) : ℂ) *
            ((t : ℂ) ^ (2 * s + 2) * cauchyWeight (2 * s) t) =
          ((averagingFactor (2 * s))⁻¹ * ((t : ℂ) ^ (2 * s + 2) * cauchyWeight (2 * s) t)) *
            ((t⁻¹ : ℝ) : ℂ) by ring,
        mul_div_cancel_right₀ _ ht_invC]
    have hker : cauchyKernel (2 * s) t * fieldCore (2 * s) (a / t) / (t : ℂ) =
        (averagingFactor (2 * s))⁻¹ * cauchyWeight (2 * s) t * fieldCore (2 * s) (a / t) := by
      unfold cauchyKernel
      rw [show (averagingFactor (2 * s))⁻¹ * (t : ℂ) * cauchyWeight (2 * s) t *
            fieldCore (2 * s) (a / t) =
          ((averagingFactor (2 * s))⁻¹ * cauchyWeight (2 * s) t * fieldCore (2 * s) (a / t)) *
            (t : ℂ) by ring,
        mul_div_cancel_right₀ _ htC]
    have hexp1 : (t : ℂ) ^ (-2 : ℂ) * (t : ℂ) ^ (2 * s + 2) * (t : ℂ) ^ (-(2 * s)) = 1 := by
      rw [← Complex.cpow_add _ _ htC, ← Complex.cpow_add _ _ htC,
        show (-2 : ℂ) + (2 * s + 2) + -(2 * s) = 0 by ring, Complex.cpow_zero]
    rw [Complex.real_smul, ht_jac, hdiv, hcore,
      show cauchyKernel (2 * s) t⁻¹ *
          ((a : ℂ) ^ (2 * s) * (t : ℂ) ^ (-(2 * s)) * fieldCore (2 * s) (a / t)) / ↑t⁻¹ =
        (cauchyKernel (2 * s) t⁻¹ / ↑t⁻¹) *
          ((a : ℂ) ^ (2 * s) * (t : ℂ) ^ (-(2 * s)) * fieldCore (2 * s) (a / t)) by ring,
      hker_inv, hker]
    calc
      (t : ℂ) ^ (-2 : ℂ) * ((averagingFactor (2 * s))⁻¹ *
          ((t : ℂ) ^ (2 * s + 2) * cauchyWeight (2 * s) t) *
          ((a : ℂ) ^ (2 * s) * (t : ℂ) ^ (-(2 * s)) * fieldCore (2 * s) (a / t)))
          = ((t : ℂ) ^ (-2 : ℂ) * (t : ℂ) ^ (2 * s + 2) * (t : ℂ) ^ (-(2 * s))) *
              ((a : ℂ) ^ (2 * s) * ((averagingFactor (2 * s))⁻¹ *
                cauchyWeight (2 * s) t * fieldCore (2 * s) (a / t))) := by ring
      _ = (a : ℂ) ^ (2 * s) * ((averagingFactor (2 * s))⁻¹ *
            cauchyWeight (2 * s) t * fieldCore (2 * s) (a / t)) := by rw [hexp1, one_mul]
  rw [hcongr, ← mul_assoc, ← Complex.cpow_add _ _ haC, neg_add_cancel, Complex.cpow_zero, one_mul]

/-! ## Unconditional linear independence via Mellin continuation and pole extraction -/

private theorem gammaR_mul_zeta_eq_xi_div {z : ℂ} (hz0 : 0 < z.re) (hz1 : z ≠ 1) :
    Gammaℝ z * riemannZeta z = 2 * _root_.RHTower.xi z / (z * (z - 1)) := by
  have hzne0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz0; exact lt_irrefl 0 hz0
  have hG : Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hz0
  have hden : z * (z - 1) ≠ 0 := mul_ne_zero hzne0 (sub_ne_zero.mpr hz1)
  have hΛ : Gammaℝ z * riemannZeta z = completedRiemannZeta z := by
    rw [riemannZeta_def_of_ne_zero hzne0]
    field_simp [hG]
  have hxi := _root_.RHTower.xi_eq_half_mul hzne0 hz1
  rw [hΛ, hxi]
  field_simp [hden]

private theorem differentiableAt_finset_prod {α : Type*} (T : Finset α) (g : α → ℂ → ℂ) (u : ℂ)
    (hg : ∀ m ∈ T, DifferentiableAt ℂ (g m) u) :
    DifferentiableAt ℂ (fun z => ∏ m ∈ T, g m z) u := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have hfun : (fun z => ∏ m ∈ insert a s, g m z) =
        fun z => g a z * ∏ m ∈ s, g m z := by
      ext z
      exact Finset.prod_insert has
    rw [hfun]
    exact (hg a (Finset.mem_insert_self a s)).mul
      (ih fun m hm => hg m (Finset.mem_insert_of_mem hm))

private theorem differentiableAt_finset_sum {α : Type*} (T : Finset α) (g : α → ℂ → ℂ) (u : ℂ)
    (hg : ∀ m ∈ T, DifferentiableAt ℂ (g m) u) :
    DifferentiableAt ℂ (fun z => ∑ m ∈ T, g m z) u := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have hfun : (fun z => ∑ m ∈ insert a s, g m z) =
        fun z => g a z + ∑ m ∈ s, g m z := by
      ext z
      exact Finset.sum_insert has
    rw [hfun]
    exact (hg a (Finset.mem_insert_self a s)).add
      (ih fun m hm => hg m (Finset.mem_insert_of_mem hm))

/-- Shared analytic pole-separation theorem: if a finite linear combination of two-zeta Mellin
kernels `M_j(u) Λ(u) Λ(2 s_j - u) / Γ_ℝ(2 s_j)` vanishes on the common convergence strip
`{0 < Re u < μ, Im u > 0}` and each multiplier `M_j` is holomorphic and nonvanishing on
`{Re u < μ, Im u > 0}`, then every coefficient `c_k` vanishes. -/
private theorem mellin_spectral_linear_relation_eq_zero
    (S : Finset upperMayerResonances) (c : upperMayerResonances → ℂ)
    (M : upperMayerResonances → ℂ → ℂ)
    (hM_diff : ∀ j ∈ S, ∀ u : ℂ, u.re < 2 * j.1.re → 0 < u.im → DifferentiableAt ℂ (M j) u)
    (hM_ne : ∀ j ∈ S, ∀ u : ℂ, u.re < 2 * j.1.re → 0 < u.im → M j u ≠ 0)
    (hsum : ∀ u : ℂ, 0 < u.re → (∀ j ∈ S, u.re < 2 * j.1.re) → 0 < u.im →
      ∑ j ∈ S, c j * (M j u *
        (Gammaℝ u * Gammaℝ (2 * j.1 - u) / Gammaℝ (2 * j.1) *
          riemannZeta u * riemannZeta (2 * j.1 - u))) = 0) :
    ∀ k ∈ S, c k = 0 := by
  classical
  intro k hk
  have hS_ne : S.Nonempty := ⟨k, hk⟩
  let μ : ℝ := (S.image (fun j : upperMayerResonances => 2 * j.1.re)).min' (hS_ne.image _)
  have hμ_pos : 0 < μ := by
    obtain ⟨j, _, hμ_eq⟩ :=
      Finset.mem_image.mp (Finset.min'_mem (S.image fun j : upperMayerResonances => 2 * j.1.re) _)
    dsimp only [μ]
    rw [← hμ_eq]
    linarith [j.2.2.1]
  have hμ_lt_one : μ < 1 := by
    have hle : μ ≤ 2 * k.1.re :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem _ hk)
    linarith [k.2.2.2.1]
  have hμ_le : ∀ j ∈ S, μ ≤ 2 * j.1.re := fun j hj =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem _ hj)
  let U : Set ℂ := {u : ℂ | u.re < μ ∧ 0 < u.im}
  let U₀ : Set ℂ := {u : ℂ | 0 < u.re ∧ u.re < μ ∧ 0 < u.im}
  have hU_open : IsOpen U :=
    (isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hU₀_open : IsOpen U₀ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter hU_open
  have hU₀_sub : U₀ ⊆ U := fun _ hu => hu.2
  have hU_conv : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    simp only [U, Set.mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.smul_re,
      Complex.smul_im, smul_eq_mul] at hx hy ⊢
    by_cases ha0 : a = 0
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using hy
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      constructor
      · calc
          a * x.re + b * y.re < a * μ + b * μ := by
            have h1 : a * x.re < a * μ := mul_lt_mul_of_pos_left hx.1 hap
            have h2 : b * y.re ≤ b * μ := mul_le_mul_of_nonneg_left hy.1.le hb
            linarith
          _ = (a + b) * μ := by ring
          _ = μ := by rw [hab, one_mul]
      · exact add_pos_of_pos_of_nonneg (mul_pos hap hx.2) (mul_nonneg hb hy.2.le)
  let P : upperMayerResonances → ℂ → ℂ := fun j u =>
    ∏ m ∈ S.erase j, ((2 * m.1 - u) * (2 * m.1 - 1 - u))
  let F : ℂ → ℂ := fun u =>
    ∑ j ∈ S, (4 * c j / Gammaℝ (2 * j.1)) * M j u *
      _root_.RHTower.xi u * _root_.RHTower.xi (2 * j.1 - u) * P j u
  have hF_diff : DifferentiableOn ℂ F U := by
    intro u hu
    have hd_sum : DifferentiableAt ℂ F u := by
      refine differentiableAt_finset_sum S
        (fun j z => (4 * c j / Gammaℝ (2 * j.1)) * M j z *
          _root_.RHTower.xi z * _root_.RHTower.xi (2 * j.1 - z) * P j z) u fun j hj => ?_
      have hdM : DifferentiableAt ℂ (M j) u :=
        hM_diff j hj u (lt_of_lt_of_le hu.1 (hμ_le j hj)) hu.2
      have hdxi1 : DifferentiableAt ℂ _root_.RHTower.xi u := _root_.RHTower.xi_differentiable u
      have hdxi2 : DifferentiableAt ℂ (fun z => _root_.RHTower.xi (2 * j.1 - z)) u :=
        (_root_.RHTower.xi_differentiable _).comp u (differentiableAt_const (2 * j.1) |>.sub differentiableAt_id)
      have hdP : DifferentiableAt ℂ (P j) u :=
        differentiableAt_finset_prod (S.erase j)
          (fun m z => (2 * m.1 - z) * (2 * m.1 - 1 - z)) u fun m _ =>
          ((differentiableAt_const (2 * m.1) |>.sub differentiableAt_id).mul
            (differentiableAt_const (2 * m.1 - 1) |>.sub differentiableAt_id))
      exact ((((differentiableAt_const _).mul hdM).mul hdxi1).mul hdxi2).mul hdP
    exact hd_sum.differentiableWithinAt
  have hF_an : AnalyticOnNhd ℂ F U := hF_diff.analyticOnNhd hU_open
  have hF_zero_U₀ : ∀ u ∈ U₀, F u = 0 := by
    intro u ⟨hu0, huμ, huim⟩
    have hu1 : u ≠ 1 := fun h => by rw [h, Complex.one_re] at huμ; linarith
    have hu_ne0 : u ≠ 0 := fun h => by rw [h, Complex.zero_re] at hu0; exact lt_irrefl 0 hu0
    have hrel := hsum u hu0 (fun j hj => lt_of_lt_of_le huμ (hμ_le j hj)) huim
    let D : ℂ := u * (u - 1) * ∏ m ∈ S, ((2 * m.1 - u) * (2 * m.1 - 1 - u))
    have hF_eq : F u = D * ∑ j ∈ S, c j * (M j u *
        (Gammaℝ u * Gammaℝ (2 * j.1 - u) / Gammaℝ (2 * j.1) *
          riemannZeta u * riemannZeta (2 * j.1 - u))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_re_pos : 0 < (2 * j.1 - u).re := by
        have h2re : (2 * j.1 - u).re = 2 * j.1.re - u.re := by simp
        rw [h2re]
        linarith [hμ_le j hj]
      have hj_re_lt1 : (2 * j.1 - u).re < 1 := by
        have h2re : (2 * j.1 - u).re = 2 * j.1.re - u.re := by simp
        rw [h2re]
        linarith [j.2.2.2.1]
      have hj_ne1 : 2 * j.1 - u ≠ 1 := fun h => by
        rw [h, Complex.one_re] at hj_re_lt1
        exact lt_irrefl 1 hj_re_lt1
      have hj_ne0 : 2 * j.1 - u ≠ 0 := fun h => by
        rw [h, Complex.zero_re] at hj_re_pos
        exact lt_irrefl 0 hj_re_pos
      have hG_u := gammaR_mul_zeta_eq_xi_div hu0 hu1
      have hG_j := gammaR_mul_zeta_eq_xi_div hj_re_pos hj_ne1
      have hprod_split : (∏ m ∈ S, ((2 * m.1 - u) * (2 * m.1 - 1 - u))) =
          ((2 * j.1 - u) * (2 * j.1 - 1 - u)) * P j u :=
        (Finset.mul_prod_erase S (fun m => (2 * m.1 - u) * (2 * m.1 - 1 - u)) hj).symm
      have hG2j : Gammaℝ (2 * j.1) ≠ 0 :=
        Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith [j.2.2.1])
      have hsub1 : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
      have hj_sub1 : 2 * j.1 - 1 - u ≠ 0 := by
        rw [show 2 * j.1 - 1 - u = (2 * j.1 - u) - 1 by ring]
        exact sub_ne_zero.mpr hj_ne1
      have hrew : Gammaℝ u * Gammaℝ (2 * j.1 - u) / Gammaℝ (2 * j.1) *
          riemannZeta u * riemannZeta (2 * j.1 - u) =
          (Gammaℝ u * riemannZeta u) * (Gammaℝ (2 * j.1 - u) * riemannZeta (2 * j.1 - u)) /
            Gammaℝ (2 * j.1) := by ring
      dsimp only [D]
      rw [hprod_split, hrew, hG_u, hG_j,
        show 2 * j.1 - u - 1 = 2 * j.1 - 1 - u by ring]
      field_simp [hu_ne0, hsub1, hj_ne0, hj_sub1, hG2j]
      ring
    rw [hF_eq, hrel, mul_zero]
  let ustar : ℂ := ((μ / 2 : ℝ) : ℂ) + I
  have hustar : ustar ∈ U₀ := by
    simp only [U₀, ustar, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.I_re,
      add_zero, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]
    exact ⟨by linarith, by linarith, zero_lt_one⟩
  have hF_zero_U : EqOn F 0 U := by
    apply hF_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU_conv.isPreconnected (hU₀_sub hustar)
    filter_upwards [hU₀_open.mem_nhds hustar] with z hz
    exact hF_zero_U₀ z hz
  let uk : ℂ := 2 * k.1 - 1
  have huk_U : uk ∈ U := by
    simp only [U, uk, Set.mem_setOf_eq]
    have hre : (2 * k.1 - 1).re = 2 * k.1.re - 1 := by simp
    have him : (2 * k.1 - 1).im = 2 * k.1.im := by simp
    rw [hre, him]
    exact ⟨by linarith [k.2.2.2.1], by linarith [k.2.1]⟩
  have hFuk : F uk = 0 := hF_zero_U huk_U
  have hsingle : F uk =
      (4 * c k / Gammaℝ (2 * k.1)) * M k uk *
        _root_.RHTower.xi uk * _root_.RHTower.xi (2 * k.1 - uk) * P k uk := by
    dsimp only [F]
    refine Finset.sum_eq_single k (fun j hj hjk => ?_) (fun hnot => absurd hk hnot)
    have hk_erase : k ∈ S.erase j := Finset.mem_erase.mpr ⟨hjk.symm, hk⟩
    have hP0 : P j uk = 0 := by
      dsimp only [P]
      refine Finset.prod_eq_zero hk_erase ?_
      dsimp only [uk]
      ring
    rw [hP0, mul_zero]
  rw [hsingle] at hFuk
  have hG2k : Gammaℝ (2 * k.1) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith [k.2.2.1])
  have hMk : M k uk ≠ 0 :=
    hM_ne k hk uk (lt_of_lt_of_le huk_U.1 (hμ_le k hk)) huk_U.2
  have hxi_uk : _root_.RHTower.xi uk ≠ 0 := by
    have href : _root_.RHTower.xi uk = _root_.RHTower.xi (2 - 2 * k.1) := by
      rw [← _root_.RHTower.xi_one_sub uk]
      congr 1
      dsimp [uk]
      ring
    rw [href]
    have hgt1 : 1 < (2 - 2 * k.1).re := by
      have hre : (2 - 2 * k.1).re = 2 - 2 * k.1.re := by simp
      rw [hre]
      linarith [k.2.2.2.1]
    have hne1 : 2 - 2 * k.1 ≠ 1 := fun h => by
      rw [h, Complex.one_re] at hgt1
      exact lt_irrefl 1 hgt1
    intro h0
    exact riemannZeta_ne_zero_of_one_lt_re hgt1
      ((_root_.RHTower.xi_eq_zero_iff (zero_lt_one.trans hgt1) hne1).mp h0)
  have hxi_one : _root_.RHTower.xi (2 * k.1 - uk) ≠ 0 := by
    rw [show 2 * k.1 - uk = 1 by dsimp [uk]; ring, _root_.RHTower.xi_one]
    norm_num
  have hPk : P k uk ≠ 0 := by
    dsimp only [P]
    rw [Finset.prod_ne_zero_iff]
    intro m hm
    have hmk : m ≠ k := (Finset.mem_erase.mp hm).1
    have hmk_val : m.1 ≠ k.1 := fun h => hmk (Subtype.ext h)
    apply mul_ne_zero
    · intro h0
      have hre := congrArg Complex.re h0
      have hre_lhs : (2 * m.1 - uk).re = 2 * m.1.re - 2 * k.1.re + 1 := by
        dsimp [uk]; simp; ring
      rw [hre_lhs, Complex.zero_re] at hre
      linarith [m.2.2.1, k.2.2.2.1]
    · intro h0
      apply hmk_val
      dsimp [uk] at h0
      linear_combination (1 / 2 : ℂ) * h0
  rcases mul_eq_zero.mp hFuk with h1 | h0
  · rcases mul_eq_zero.mp h1 with h2 | h0
    · rcases mul_eq_zero.mp h2 with h3 | h0
      · rcases mul_eq_zero.mp h3 with h4 | h0
        · rw [div_eq_zero_iff] at h4
          rcases h4 with h4 | h4
          · exact (mul_eq_zero.mp h4).resolve_left (by norm_num)
          · exact absurd h4 hG2k
        · exact absurd h0 hMk
      · exact absurd h0 hxi_uk
    · exact absurd h0 hxi_one
  · exact absurd h0 hPk

/-- **Unconditional Linear Independence of Resonant Mayer Scattering Cores on `(0, ∞)`.** -/
theorem resonantFieldCore_linearIndependent_Ioi :
    LinearIndependent ℂ (fun (s : upperMayerResonances) (a : Ioi (0 : ℝ)) => fieldCore (2 * s.1) a.1) := by
  rw [linearIndependent_iff']
  intro S c hcomb
  have hpt : ∀ a ∈ Ioi (0 : ℝ), ∑ j ∈ S, c j * fieldCore (2 * j.1) a = 0 := by
    intro a ha
    have hv := congrFun hcomb ⟨a, ha⟩
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hv
  refine mellin_spectral_linear_relation_eq_zero S c (fun _ _ => 1)
    (fun _ _ _ _ _ => differentiableAt_const 1)
    (fun _ _ _ _ _ => one_ne_zero) ?_
  intro u hu0 hu_lt huim
  have hm : ∀ j ∈ S, HasMellin (fieldCore (2 * j.1)) u
      (Gammaℝ u * Gammaℝ (2 * j.1 - u) / Gammaℝ (2 * j.1) *
        riemannZeta u * riemannZeta (2 * j.1 - u)) := by
    intro j hj
    have hlt2j := hu_lt j hj
    have hu1 : u.re < 1 := by linarith [j.2.2.2.1]
    have hwu0 : 0 < (2 * j.1 - u).re := by
      have hre : (2 * j.1 - u).re = 2 * j.1.re - u.re := by simp
      rw [hre]; linarith
    have hwu1 : (2 * j.1 - u).re < 1 := by
      have hre : (2 * j.1 - u).re = 2 * j.1.re - u.re := by simp
      rw [hre]; linarith [j.2.2.2.1]
    have hwim : 0 < (2 * j.1).im := by simp; linarith [j.2.1]
    exact core_hasMellin_gammaR hu0 hu1 hwu0 hwu1 hwim
  have hint : ∀ j ∈ S,
      IntegrableOn (fun a : ℝ => c j * ((a : ℂ) ^ (u - 1) * fieldCore (2 * j.1) a)) (Ioi 0) := by
    intro j hj
    have hi : IntegrableOn (fun a : ℝ => (a : ℂ) ^ (u - 1) * fieldCore (2 * j.1) a) (Ioi 0) := by
      simpa only [MellinConvergent, smul_eq_mul] using (hm j hj).1
    exact hi.const_mul (c j)
  have hval : ∀ j ∈ S,
      (∫ a in Ioi (0 : ℝ), c j * ((a : ℂ) ^ (u - 1) * fieldCore (2 * j.1) a)) =
        c j * (1 * (Gammaℝ u * Gammaℝ (2 * j.1 - u) / Gammaℝ (2 * j.1) *
          riemannZeta u * riemannZeta (2 * j.1 - u))) := by
    intro j hj
    rw [one_mul, integral_const_mul, ← (hm j hj).2]
    rfl
  calc
    (∑ j ∈ S, c j * (1 * (Gammaℝ u * Gammaℝ (2 * j.1 - u) / Gammaℝ (2 * j.1) *
        riemannZeta u * riemannZeta (2 * j.1 - u))))
        = ∑ j ∈ S, ∫ a in Ioi (0 : ℝ), c j * ((a : ℂ) ^ (u - 1) * fieldCore (2 * j.1) a) :=
      Finset.sum_congr rfl fun j hj => (hval j hj).symm
    _ = ∫ a in Ioi (0 : ℝ), ∑ j ∈ S, c j * ((a : ℂ) ^ (u - 1) * fieldCore (2 * j.1) a) :=
      (integral_finsetSum S hint).symm
    _ = ∫ a in Ioi (0 : ℝ), (0 : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
      have hfactor : (∑ j ∈ S, c j * ((a : ℂ) ^ (u - 1) * fieldCore (2 * j.1) a)) =
          (a : ℂ) ^ (u - 1) * ∑ j ∈ S, c j * fieldCore (2 * j.1) a := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hfactor, hpt a ha, mul_zero]
    _ = 0 := integral_zero _ _

theorem resonantFieldCore_linearIndependent :
    LinearIndependent ℂ (fun s : upperMayerResonances => fieldCore (2 * s.1)) := by
  let resMap : (ℝ → ℂ) →ₗ[ℂ] (Ioi (0 : ℝ) → ℂ) :=
    { toFun := fun f a => f a.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact LinearIndependent.of_comp resMap resonantFieldCore_linearIndependent_Ioi

private theorem measurable_cauchyKernel (w : ℂ) : Measurable (cauchyKernel w) := by
  unfold cauchyKernel cauchyWeight
  fun_prop

private theorem measurable_fieldCore_of_im_pos {w : ℂ} (him : 0 < w.im) :
    Measurable (fieldCore w) := by
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_im] at him; exact lt_irrefl 0 him
  have hw2 : w ≠ 2 := fun h => by rw [h] at him; norm_num at him
  have he := measurable_epsteinField hw0 hw2
  unfold fieldCore scatteringPowers
  fun_prop

private theorem gamma_avoids_neg_nat_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    ∀ n : ℕ, z ≠ -(n : ℂ) := by
  intro n hn
  have h := congrArg Complex.im hn
  simp only [Complex.neg_im, Complex.natCast_im, neg_zero] at h
  exact hz.ne' h

private theorem gamma_avoids_neg_nat_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ∀ n : ℕ, z ≠ -(n : ℂ) := by
  intro n hn
  have h := congrArg Complex.re hn
  simp only [Complex.neg_re, Complex.natCast_re] at h
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- **Unconditional Linear Independence of Resonant Cauchy–Lewis Period Cores on `(0, ∞)`.** -/
theorem mayerPeriodCore_linearIndependent_Ioi :
    LinearIndependent ℂ (fun (s : upperMayerResonances) (a : Ioi (0 : ℝ)) => mayerPeriodCore s.1 a.1) := by
  rw [linearIndependent_iff']
  intro S c hcomb
  have hpt : ∀ a ∈ Ioi (0 : ℝ), ∑ j ∈ S, c j * mayerPeriodCore j.1 a = 0 := by
    intro a ha
    have hv := congrFun hcomb ⟨a, ha⟩
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hv
  refine mellin_spectral_linear_relation_eq_zero S c (fun j u => symbol (2 * j.1) u)
    (fun j _ u hu_lt huim => ?_)
    (fun j _ u hu_lt huim => ?_) ?_
  · have him1 : 0 < ((u + 1) / 2).im := by simp; linarith
    have hre2 : 0 < ((2 * j.1 + 1 - u) / 2).re := by
      have hr : ((2 * j.1 + 1 - u) / 2).re = (2 * j.1.re + 1 - u.re) / 2 := by simp
      rw [hr]; linarith
    have hre_den : 0 < ((2 * j.1 + 1) / 2).re := by
      have hr : ((2 * j.1 + 1) / 2).re = (2 * j.1.re + 1) / 2 := by simp
      rw [hr]; linarith [j.2.2.1]
    have hg1 := (Complex.differentiableAt_Gamma _ (gamma_avoids_neg_nat_of_im_pos him1)).comp u
      ((differentiableAt_id.add_const (1 : ℂ)).div_const 2)
    have hg2 := (Complex.differentiableAt_Gamma _ (gamma_avoids_neg_nat_of_re_pos hre2)).comp u
      ((differentiableAt_const (2 * j.1 + 1) |>.sub differentiableAt_id).div_const 2)
    have hden_ne : (Real.pi : ℂ) ^ (1 / 2 : ℂ) * Gamma ((2 * j.1 + 1) / 2) ≠ 0 :=
      mul_ne_zero
        (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
        (Complex.Gamma_ne_zero (gamma_avoids_neg_nat_of_re_pos hre_den))
    unfold symbol
    exact (hg1.mul hg2).div (differentiableAt_const _) hden_ne
  · have him1 : 0 < ((u + 1) / 2).im := by simp; linarith
    have hre2 : 0 < ((2 * j.1 + 1 - u) / 2).re := by
      have hr : ((2 * j.1 + 1 - u) / 2).re = (2 * j.1.re + 1 - u.re) / 2 := by simp
      rw [hr]; linarith
    have hre_den : 0 < ((2 * j.1 + 1) / 2).re := by
      have hr : ((2 * j.1 + 1) / 2).re = (2 * j.1.re + 1) / 2 := by simp
      rw [hr]; linarith [j.2.2.1]
    unfold symbol
    exact div_ne_zero
      (mul_ne_zero (Complex.Gamma_ne_zero (gamma_avoids_neg_nat_of_im_pos him1))
        (Complex.Gamma_ne_zero (gamma_avoids_neg_nat_of_re_pos hre2)))
      (mul_ne_zero
        (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
        (Complex.Gamma_ne_zero (gamma_avoids_neg_nat_of_re_pos hre_den)))
  · intro u hu0 hu_lt huim
    have hm : ∀ j ∈ S, HasMellin (mayerPeriodCore j.1) u
        (symbol (2 * j.1) u *
          (Gammaℝ u * Gammaℝ (2 * j.1 - u) / Gammaℝ (2 * j.1) *
            riemannZeta u * riemannZeta (2 * j.1 - u))) := by
      intro j hj
      have hlt2j := hu_lt j hj
      have hw0 : 0 < (2 * j.1).re := by simp; linarith [j.2.2.1]
      have hwim : 0 < (2 * j.1).im := by simp; linarith [j.2.1]
      have hu1 : u.re < 1 := by linarith [j.2.2.2.1]
      have hwu0 : 0 < (2 * j.1 - u).re := by
        have hr : (2 * j.1 - u).re = 2 * j.1.re - u.re := by simp
        rw [hr]; linarith
      have hwu1 : (2 * j.1 - u).re < 1 := by
        have hr : (2 * j.1 - u).re = 2 * j.1.re - u.re := by simp
        rw [hr]; linarith [j.2.2.2.1]
      have hwu_ker : u.re < (2 * j.1).re + 1 := by
        have hr : (2 * j.1).re = 2 * j.1.re := by simp
        rw [hr]
        linarith
      have hker := cauchyKernel_hasMellin hw0 (by linarith : -1 < u.re) hwu_ker
      have hcore := core_hasMellin_gammaR hu0 hu1 hwu0 hwu1 hwim
      have hconv := _root_.RHTower.hasMellin_positiveMellinConvolution
        (measurable_cauchyKernel (2 * j.1)) (measurable_fieldCore_of_im_pos hwim)
        hker.1 hcore.1
      rw [hker.2, hcore.2] at hconv
      exact hconv
    have hint : ∀ j ∈ S,
        IntegrableOn (fun a : ℝ => c j * ((a : ℂ) ^ (u - 1) * mayerPeriodCore j.1 a)) (Ioi 0) := by
      intro j hj
      have hi : IntegrableOn (fun a : ℝ => (a : ℂ) ^ (u - 1) * mayerPeriodCore j.1 a) (Ioi 0) := by
        simpa only [MellinConvergent, smul_eq_mul] using (hm j hj).1
      exact hi.const_mul (c j)
    have hval : ∀ j ∈ S,
        (∫ a in Ioi (0 : ℝ), c j * ((a : ℂ) ^ (u - 1) * mayerPeriodCore j.1 a)) =
          c j * (symbol (2 * j.1) u *
            (Gammaℝ u * Gammaℝ (2 * j.1 - u) / Gammaℝ (2 * j.1) *
              riemannZeta u * riemannZeta (2 * j.1 - u))) := by
      intro j hj
      rw [integral_const_mul, ← (hm j hj).2]
      rfl
    calc
      (∑ j ∈ S, c j * (symbol (2 * j.1) u *
          (Gammaℝ u * Gammaℝ (2 * j.1 - u) / Gammaℝ (2 * j.1) *
            riemannZeta u * riemannZeta (2 * j.1 - u))))
          = ∑ j ∈ S, ∫ a in Ioi (0 : ℝ), c j * ((a : ℂ) ^ (u - 1) * mayerPeriodCore j.1 a) :=
        Finset.sum_congr rfl fun j hj => (hval j hj).symm
      _ = ∫ a in Ioi (0 : ℝ), ∑ j ∈ S, c j * ((a : ℂ) ^ (u - 1) * mayerPeriodCore j.1 a) :=
        (integral_finsetSum S hint).symm
      _ = ∫ a in Ioi (0 : ℝ), (0 : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
        have hfactor : (∑ j ∈ S, c j * ((a : ℂ) ^ (u - 1) * mayerPeriodCore j.1 a)) =
            (a : ℂ) ^ (u - 1) * ∑ j ∈ S, c j * mayerPeriodCore j.1 a := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [hfactor, hpt a ha, mul_zero]
      _ = 0 := integral_zero _ _

/-- **Unconditional Linear Independence of Resonant Cauchy–Lewis Period Cores in `ℝ → ℂ`.** -/
theorem mayerPeriodCore_linearIndependent :
    LinearIndependent ℂ (fun s : upperMayerResonances => mayerPeriodCore s.1) := by
  let resMap : (ℝ → ℂ) →ₗ[ℂ] (Ioi (0 : ℝ) → ℂ) :=
    { toFun := fun f a => f a.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact LinearIndependent.of_comp resMap mayerPeriodCore_linearIndependent_Ioi

/-! ## Canonical `s`-independent Krein–Lax–Phillips realization on `W_PM` -/

/-- The actual function subspace spanned by the resonant Cauchy–Lewis period cores. -/
def mayerPeriodKreinSpace : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ (Set.range fun s : upperMayerResonances => mayerPeriodCore s.1)

/-- Canonical basis of `mayerPeriodKreinSpace` formed by the actual resonant period cores. -/
def mayerPeriodBasis : Module.Basis upperMayerResonances ℂ mayerPeriodKreinSpace :=
  Module.Basis.span mayerPeriodCore_linearIndependent

@[simp]
theorem coe_mayerPeriodBasis (s : upperMayerResonances) :
    (mayerPeriodBasis s : ℝ → ℂ) = mayerPeriodCore s.1 :=
  Module.Basis.coe_span_apply mayerPeriodCore_linearIndependent s

/-- Positive-definite `s`-independent Hermitian inner product on `mayerPeriodKreinSpace`. -/
def mayerKreinPosInner (u v : mayerPeriodKreinSpace) : ℂ :=
  (mayerPeriodBasis.repr u).sum fun s cu =>
    cu * (starRingEnd ℂ) (mayerPeriodBasis.repr v s)

theorem mayerKreinPosInner_eq_sum_of_subset {u v : mayerPeriodKreinSpace}
    {S : Finset upperMayerResonances}
    (hS : (mayerPeriodBasis.repr u).support ⊆ S) :
    mayerKreinPosInner u v =
      ∑ s ∈ S, mayerPeriodBasis.repr u s * (starRingEnd ℂ) (mayerPeriodBasis.repr v s) :=
  Finsupp.sum_of_support_subset (mayerPeriodBasis.repr u) hS _ (fun _ _ => zero_mul _)

theorem mayerKreinPosInner_conj_symm (u v : mayerPeriodKreinSpace) :
    (starRingEnd ℂ) (mayerKreinPosInner u v) = mayerKreinPosInner v u := by
  classical
  let S : Finset upperMayerResonances :=
    (mayerPeriodBasis.repr u).support ∪ (mayerPeriodBasis.repr v).support
  rw [mayerKreinPosInner_eq_sum_of_subset Finset.subset_union_left,
    mayerKreinPosInner_eq_sum_of_subset Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem mayerKreinPosInner_add_left (u₁ u₂ v : mayerPeriodKreinSpace) :
    mayerKreinPosInner (u₁ + u₂) v = mayerKreinPosInner u₁ v + mayerKreinPosInner u₂ v := by
  unfold mayerKreinPosInner
  rw [map_add]
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem mayerKreinPosInner_smul_left (c : ℂ) (u v : mayerPeriodKreinSpace) :
    mayerKreinPosInner (c • u) v = c * mayerKreinPosInner u v := by
  classical
  let S : Finset upperMayerResonances := (mayerPeriodBasis.repr u).support
  have hsub : (mayerPeriodBasis.repr (c • u)).support ⊆ S := by
    rw [map_smul]
    exact Finsupp.support_smul
  rw [mayerKreinPosInner_eq_sum_of_subset hsub,
    mayerKreinPosInner_eq_sum_of_subset Finset.Subset.rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem mayerKreinPosInner_self_eq (u : mayerPeriodKreinSpace) :
    mayerKreinPosInner u u =
      ∑ s ∈ (mayerPeriodBasis.repr u).support, ((‖mayerPeriodBasis.repr u s‖ ^ 2 : ℝ) : ℂ) := by
  unfold mayerKreinPosInner Finsupp.sum
  refine Finset.sum_congr rfl fun s _ => ?_
  dsimp only
  rw [Complex.mul_conj', Complex.ofReal_pow]

theorem mayerKreinPosInner_self_im (u : mayerPeriodKreinSpace) :
    (mayerKreinPosInner u u).im = 0 := by
  rw [mayerKreinPosInner_self_eq, ← Complex.ofReal_sum, Complex.ofReal_im]

theorem mayerKreinPosInner_self_re_nonneg (u : mayerPeriodKreinSpace) :
    0 ≤ (mayerKreinPosInner u u).re := by
  rw [mayerKreinPosInner_self_eq, ← Complex.ofReal_sum, Complex.ofReal_re]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Positive-definiteness of `mayerKreinPosInner`: `(mayerKreinPosInner u u).re = 0 ↔ u = 0`. -/
theorem mayerKreinPosInner_self_re_eq_zero_iff (u : mayerPeriodKreinSpace) :
    (mayerKreinPosInner u u).re = 0 ↔ u = 0 := by
  rw [mayerKreinPosInner_self_eq, ← Complex.ofReal_sum, Complex.ofReal_re,
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  constructor
  · intro h
    apply mayerPeriodBasis.repr.injective
    rw [map_zero]
    ext s
    by_cases hs : s ∈ (mayerPeriodBasis.repr u).support
    · have h0 := sq_eq_zero_iff.mp (h s hs)
      exact norm_eq_zero.mp h0
    · exact Finsupp.notMem_support_iff.mp hs
  · rintro rfl
    simp

theorem mayerKreinPosInner_self_re_pos_iff (u : mayerPeriodKreinSpace) :
    0 < (mayerKreinPosInner u u).re ↔ u ≠ 0 := by
  constructor
  · intro hp h0
    subst h0
    have hz := (mayerKreinPosInner_self_re_eq_zero_iff 0).mpr rfl
    linarith
  · intro hne
    exact lt_of_le_of_ne (mayerKreinPosInner_self_re_nonneg u)
      (fun hz => hne ((mayerKreinPosInner_self_re_eq_zero_iff u).mp hz.symm))

/-- The Riemann–Mayer reflection operator `Θ_PM` on `mayerPeriodKreinSpace`, sending the resonant
period core `b_s` to `b_{1/2 - conj s}`. -/
def mayerKreinReflection : mayerPeriodKreinSpace →ₗ[ℂ] mayerPeriodKreinSpace :=
  mayerPeriodBasis.constr ℂ (fun s => mayerPeriodBasis (reflectUpperResonance s))

@[simp]
theorem mayerKreinReflection_basis (s : upperMayerResonances) :
    mayerKreinReflection (mayerPeriodBasis s) = mayerPeriodBasis (reflectUpperResonance s) :=
  mayerPeriodBasis.constr_basis ℂ _ s

theorem mayerKreinReflection_involutive (u : mayerPeriodKreinSpace) :
    mayerKreinReflection (mayerKreinReflection u) = u := by
  have hcomp : mayerKreinReflection.comp mayerKreinReflection = LinearMap.id := by
    refine mayerPeriodBasis.ext fun s => ?_
    simp
  exact LinearMap.congr_fun hcomp u

theorem repr_mayerKreinReflection (v : mayerPeriodKreinSpace) (s : upperMayerResonances) :
    mayerPeriodBasis.repr (mayerKreinReflection v) s =
      mayerPeriodBasis.repr v (reflectUpperResonance s) := by
  classical
  let L₁ : mayerPeriodKreinSpace →ₗ[ℂ] ℂ :=
    (mayerPeriodBasis.coord s).comp mayerKreinReflection
  let L₂ : mayerPeriodKreinSpace →ₗ[ℂ] ℂ :=
    mayerPeriodBasis.coord (reflectUpperResonance s)
  have heq : L₁ = L₂ := by
    refine mayerPeriodBasis.ext fun t => ?_
    change mayerPeriodBasis.repr (mayerKreinReflection (mayerPeriodBasis t)) s =
      mayerPeriodBasis.repr (mayerPeriodBasis t) (reflectUpperResonance s)
    rw [mayerKreinReflection_basis, mayerPeriodBasis.repr_self, mayerPeriodBasis.repr_self,
      Finsupp.single_apply, Finsupp.single_apply]
    have hiff : reflectUpperResonance t = s ↔ t = reflectUpperResonance s :=
      ⟨fun h => by rw [← h, reflectUpperResonance_involutive],
       fun h => by rw [h, reflectUpperResonance_involutive]⟩
    by_cases h : reflectUpperResonance t = s
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (mt hiff.mpr h)]
  exact LinearMap.congr_fun heq v

/-- `mayerKreinReflection` is self-adjoint for `mayerKreinPosInner`. -/
theorem mayerKreinPosInner_reflection_adj (u v : mayerPeriodKreinSpace) :
    mayerKreinPosInner (mayerKreinReflection u) v =
      mayerKreinPosInner u (mayerKreinReflection v) := by
  classical
  let S : Finset upperMayerResonances :=
    (mayerPeriodBasis.repr (mayerKreinReflection u)).support ∪ (mayerPeriodBasis.repr v).support
  let T : Finset upperMayerResonances := S.map reflectUpperResonance.toEmbedding
  have hsubL : (mayerPeriodBasis.repr (mayerKreinReflection u)).support ⊆ S :=
    Finset.subset_union_left
  have hsubR : (mayerPeriodBasis.repr u).support ⊆ T := by
    intro t ht
    rw [Finset.mem_map]
    refine ⟨reflectUpperResonance t, Finset.mem_union_left _ ?_,
      reflectUpperResonance_involutive t⟩
    rw [Finsupp.mem_support_iff, repr_mayerKreinReflection, reflectUpperResonance_involutive]
    exact Finsupp.mem_support_iff.mp ht
  rw [mayerKreinPosInner_eq_sum_of_subset hsubL, mayerKreinPosInner_eq_sum_of_subset hsubR]
  dsimp only [T]
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun s _ => ?_
  change mayerPeriodBasis.repr (mayerKreinReflection u) s *
      (starRingEnd ℂ) (mayerPeriodBasis.repr v s) =
    mayerPeriodBasis.repr u (reflectUpperResonance s) *
      (starRingEnd ℂ) (mayerPeriodBasis.repr (mayerKreinReflection v) (reflectUpperResonance s))
  rw [repr_mayerKreinReflection, repr_mayerKreinReflection, reflectUpperResonance_involutive]

/-- `mayerKreinReflection` is unitary for `mayerKreinPosInner`. -/
theorem mayerKreinPosInner_reflection_unitary (u v : mayerPeriodKreinSpace) :
    mayerKreinPosInner (mayerKreinReflection u) (mayerKreinReflection v) =
      mayerKreinPosInner u v := by
  rw [mayerKreinPosInner_reflection_adj, mayerKreinReflection_involutive]

/-- The reflection-invariant indefinite Krein Hermitian pairing `[u, v]_PM := ⟨u, Θ_PM v⟩_PM^+`. -/
def mayerKreinForm (u v : mayerPeriodKreinSpace) : ℂ :=
  mayerKreinPosInner u (mayerKreinReflection v)

theorem mayerKreinForm_conj_symm (u v : mayerPeriodKreinSpace) :
    (starRingEnd ℂ) (mayerKreinForm u v) = mayerKreinForm v u := by
  unfold mayerKreinForm
  rw [mayerKreinPosInner_conj_symm, mayerKreinPosInner_reflection_adj]

theorem mayerKreinForm_self_im (u : mayerPeriodKreinSpace) :
    (mayerKreinForm u u).im = 0 := by
  have h := mayerKreinForm_conj_symm u u
  have him := congrArg Complex.im h
  simp only [Complex.conj_im] at him
  linarith

theorem mayerKreinForm_reflection_invariant (u v : mayerPeriodKreinSpace) :
    mayerKreinForm (mayerKreinReflection u) (mayerKreinReflection v) = mayerKreinForm u v := by
  unfold mayerKreinForm
  rw [mayerKreinPosInner_reflection_unitary]

theorem mayerKreinForm_basis {s t : upperMayerResonances} :
    mayerKreinForm (mayerPeriodBasis s) (mayerPeriodBasis t) =
      if s = reflectUpperResonance t then 1 else 0 := by
  classical
  unfold mayerKreinForm mayerKreinPosInner
  rw [mayerKreinReflection_basis, mayerPeriodBasis.repr_self, mayerPeriodBasis.repr_self,
    Finsupp.sum_single_index (zero_mul _), one_mul, Finsupp.single_apply]
  by_cases h : reflectUpperResonance t = s
  · rw [if_pos h, if_pos h.symm, map_one]
  · rw [if_neg h, if_neg (Ne.symm h), map_zero]

/-! ## The Krein self-adjoint Lax–Phillips resonance generator `B_PM` -/

/-- Centered Lax–Phillips resonance eigenvalue `-i(s - 1/4)`, real iff `Re s = 1/4`. -/
def mayerLaxPhillipsEigenvalue (s : ℂ) : ℂ :=
  -I * (s - 1 / 4)

@[simp]
theorem mayerLaxPhillipsEigenvalue_re (s : ℂ) :
    (mayerLaxPhillipsEigenvalue s).re = s.im := by
  unfold mayerLaxPhillipsEigenvalue
  simp

@[simp]
theorem mayerLaxPhillipsEigenvalue_im (s : ℂ) :
    (mayerLaxPhillipsEigenvalue s).im = 1 / 4 - s.re := by
  unfold mayerLaxPhillipsEigenvalue
  simp

theorem mayerLaxPhillipsEigenvalue_im_eq_zero_iff (s : ℂ) :
    (mayerLaxPhillipsEigenvalue s).im = 0 ↔ s.re = 1 / 4 := by
  rw [mayerLaxPhillipsEigenvalue_im]
  constructor <;> intro h <;> linarith

theorem conj_mayerLaxPhillipsEigenvalue_reflect (s : ℂ) :
    (starRingEnd ℂ) (mayerLaxPhillipsEigenvalue (riemannMayerReflect s)) =
      mayerLaxPhillipsEigenvalue s := by
  unfold mayerLaxPhillipsEigenvalue riemannMayerReflect
  simp only [map_mul, map_neg, Complex.conj_I, map_sub, map_div₀, map_one, map_ofNat,
    Complex.conj_conj]
  ring

/-- The Lax–Phillips resonance operator `B_PM` on `mayerPeriodKreinSpace`, with eigenvectors
`mayerPeriodBasis s` and eigenvalues `mayerLaxPhillipsEigenvalue s.1 = -i(s - 1/4)`. -/
def mayerLaxPhillipsGenerator : mayerPeriodKreinSpace →ₗ[ℂ] mayerPeriodKreinSpace :=
  mayerPeriodBasis.constr ℂ (fun s => mayerLaxPhillipsEigenvalue s.1 • mayerPeriodBasis s)

@[simp]
theorem mayerLaxPhillipsGenerator_basis (s : upperMayerResonances) :
    mayerLaxPhillipsGenerator (mayerPeriodBasis s) =
      mayerLaxPhillipsEigenvalue s.1 • mayerPeriodBasis s :=
  mayerPeriodBasis.constr_basis ℂ _ s

theorem repr_mayerLaxPhillipsGenerator (u : mayerPeriodKreinSpace) (s : upperMayerResonances) :
    mayerPeriodBasis.repr (mayerLaxPhillipsGenerator u) s =
      mayerLaxPhillipsEigenvalue s.1 * mayerPeriodBasis.repr u s := by
  classical
  let L₁ : mayerPeriodKreinSpace →ₗ[ℂ] ℂ :=
    (mayerPeriodBasis.coord s).comp mayerLaxPhillipsGenerator
  let L₂ : mayerPeriodKreinSpace →ₗ[ℂ] ℂ :=
    mayerLaxPhillipsEigenvalue s.1 • mayerPeriodBasis.coord s
  have heq : L₁ = L₂ := by
    refine mayerPeriodBasis.ext fun t => ?_
    change mayerPeriodBasis.repr (mayerLaxPhillipsGenerator (mayerPeriodBasis t)) s =
      mayerLaxPhillipsEigenvalue s.1 * mayerPeriodBasis.repr (mayerPeriodBasis t) s
    rw [mayerLaxPhillipsGenerator_basis, map_smul, mayerPeriodBasis.repr_self,
      Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.single_apply]
    by_cases h : t = s
    · subst h; simp
    · simp [h]
  exact LinearMap.congr_fun heq u

/-- **Krein Self-Adjointness of the Lax–Phillips Generator `B_PM`.** -/
theorem mayerKreinForm_laxPhillipsGenerator_selfAdjoint (u v : mayerPeriodKreinSpace) :
    mayerKreinForm (mayerLaxPhillipsGenerator u) v =
      mayerKreinForm u (mayerLaxPhillipsGenerator v) := by
  classical
  let S : Finset upperMayerResonances :=
    (mayerPeriodBasis.repr u).support ∪ (mayerPeriodBasis.repr (mayerLaxPhillipsGenerator u)).support
  have hsubL : (mayerPeriodBasis.repr (mayerLaxPhillipsGenerator u)).support ⊆ S :=
    Finset.subset_union_right
  have hsubR : (mayerPeriodBasis.repr u).support ⊆ S :=
    Finset.subset_union_left
  unfold mayerKreinForm
  rw [mayerKreinPosInner_eq_sum_of_subset hsubL, mayerKreinPosInner_eq_sum_of_subset hsubR]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [repr_mayerLaxPhillipsGenerator, repr_mayerKreinReflection, repr_mayerKreinReflection,
    repr_mayerLaxPhillipsGenerator, map_mul, reflectUpperResonance_coe,
    conj_mayerLaxPhillipsEigenvalue_reflect]
  ring

/-! ## Sharp Krein sign dichotomy, negative subspace, polar index, and RH equivalence -/

/-- Every critical-line resonance (`Re s = 1/4`) has unit positive Krein self-pairing. -/
theorem mayerKreinForm_basis_self_of_re_eq_quarter {s : upperMayerResonances}
    (hs : s.1.re = 1 / 4) :
    mayerKreinForm (mayerPeriodBasis s) (mayerPeriodBasis s) = 1 := by
  rw [mayerKreinForm_basis, if_pos ((reflectUpperResonance_eq_self_iff s).mpr hs).symm]

/-- Every off-line resonance (`Re s ≠ 1/4`) is a null resonant vector `[b_s, b_s]_PM = 0`. -/
theorem mayerKreinForm_basis_self_of_re_ne_quarter {s : upperMayerResonances}
    (hs : s.1.re ≠ 1 / 4) :
    mayerKreinForm (mayerPeriodBasis s) (mayerPeriodBasis s) = 0 := by
  rw [mayerKreinForm_basis, if_neg (fun h => hs ((reflectUpperResonance_eq_self_iff s).mp h.symm))]

/-- Explicit antisymmetric reflected period state associated to an upper Mayer resonance. -/
def mayerOffLineNegativeState (s : upperMayerResonances) : mayerPeriodKreinSpace :=
  mayerPeriodBasis s - mayerPeriodBasis (reflectUpperResonance s)

theorem mayerKreinReflection_offLineNegativeState (s : upperMayerResonances) :
    mayerKreinReflection (mayerOffLineNegativeState s) = -mayerOffLineNegativeState s := by
  unfold mayerOffLineNegativeState
  rw [map_sub, mayerKreinReflection_basis, mayerKreinReflection_basis,
    reflectUpperResonance_involutive]
  abel

/-- **Negative Krein Norm Produced by Every Resonance Off `Re s = 1/4`.** -/
theorem mayerKreinForm_offLineNegativeState_self {s : upperMayerResonances}
    (hs : s.1.re ≠ 1 / 4) :
    mayerKreinForm (mayerOffLineNegativeState s) (mayerOffLineNegativeState s) = -2 := by
  have hne : reflectUpperResonance s ≠ s :=
    fun h => hs ((reflectUpperResonance_eq_self_iff s).mp h)
  unfold mayerKreinForm
  rw [mayerKreinReflection_offLineNegativeState, ← neg_one_smul ℂ (mayerOffLineNegativeState s),
    ← mayerKreinPosInner_conj_symm, mayerKreinPosInner_smul_left,
    map_mul, map_neg, map_one, mayerKreinPosInner_conj_symm]
  unfold mayerOffLineNegativeState
  have hself : mayerKreinPosInner (mayerPeriodBasis s - mayerPeriodBasis (reflectUpperResonance s))
      (mayerPeriodBasis s - mayerPeriodBasis (reflectUpperResonance s)) = 2 := by
    classical
    rw [mayerKreinPosInner_self_eq]
    have hrep : mayerPeriodBasis.repr
        (mayerPeriodBasis s - mayerPeriodBasis (reflectUpperResonance s)) =
        Finsupp.single s 1 - Finsupp.single (reflectUpperResonance s) 1 := by
      rw [map_sub, mayerPeriodBasis.repr_self, mayerPeriodBasis.repr_self]
    have hsupp : (mayerPeriodBasis.repr
        (mayerPeriodBasis s - mayerPeriodBasis (reflectUpperResonance s))).support =
        {s, reflectUpperResonance s} := by
      ext t
      rw [hrep, Finsupp.mem_support_iff, Finset.mem_insert, Finset.mem_singleton,
        Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
      by_cases hts : t = s
      · subst hts
        simp [hne]
      · by_cases htr : t = reflectUpperResonance s
        · subst htr
          simp [hne, hne.symm]
        · simp [hts, htr, Ne.symm hts, Ne.symm htr]
    rw [hsupp, Finset.sum_pair hne.symm, hrep, Finsupp.sub_apply, Finsupp.sub_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne, Finsupp.single_eq_of_ne hne.symm,
      Finsupp.single_eq_same]
    norm_num
  rw [hself]
  ring

theorem mayerOffLineNegativeState_ne_zero {s : upperMayerResonances} (hs : s.1.re ≠ 1 / 4) :
    mayerOffLineNegativeState s ≠ 0 := by
  intro h0
  have heq : mayerPeriodBasis s = mayerPeriodBasis (reflectUpperResonance s) :=
    sub_eq_zero.mp h0
  exact hs ((reflectUpperResonance_eq_self_iff s).mp (mayerPeriodBasis.injective heq).symm)

/-- Canonical inclusion of `upperRightMayerResonances` (`1/4 < Re s`, `0 < Im s`) into
`upperMayerResonances`. -/
def ofUpperRightResonance (s : upperRightMayerResonances) : upperMayerResonances :=
  ⟨s.1, s.2.2⟩

theorem mayerOffLineNegativeState_upperRight_linearIndependent :
    LinearIndependent ℂ (fun s : upperRightMayerResonances =>
      mayerOffLineNegativeState (ofUpperRightResonance s)) := by
  rw [linearIndependent_iff']
  intro S c hsum k hk
  have hcoord := congrArg (fun u => mayerPeriodBasis.repr u (ofUpperRightResonance k)) hsum
  simp only [map_sum, map_smul, map_zero, Finsupp.coe_finsetSum, Finsupp.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at hcoord
  have hterm : ∀ s ∈ S,
      c s * mayerPeriodBasis.repr (mayerOffLineNegativeState (ofUpperRightResonance s))
        (ofUpperRightResonance k) = if s = k then c s else 0 := by
    intro s _
    unfold mayerOffLineNegativeState
    rw [map_sub, mayerPeriodBasis.repr_self, mayerPeriodBasis.repr_self, Finsupp.sub_apply,
      Finsupp.single_apply, Finsupp.single_apply]
    have hrefl_ne : reflectUpperResonance (ofUpperRightResonance s) ≠ ofUpperRightResonance k := by
      intro heq
      have hre := congrArg (fun x : upperMayerResonances => x.1.re) heq
      change (riemannMayerReflect s.1).re = k.1.re at hre
      rw [riemannMayerReflect_re] at hre
      linarith [s.2.1, k.2.1]
    rw [if_neg hrefl_ne, sub_zero]
    by_cases hsk : s = k
    · subst hsk; simp
    · have hne_u : ofUpperRightResonance s ≠ ofUpperRightResonance k :=
        fun h => hsk (Subtype.ext (congrArg (fun x : upperMayerResonances => x.1) h))
      simp [hsk, hne_u]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S k c, if_pos hk] at hcoord
  exact hcoord

/-- The strictly negative-definite subspace `W_PM^- ⊂ W_PM` generated by upper right-half
Mayer resonances. -/
def mayerNegativeSubspace : Submodule ℂ mayerPeriodKreinSpace :=
  Submodule.span ℂ
    (Set.range fun s : upperRightMayerResonances =>
      mayerOffLineNegativeState (ofUpperRightResonance s))

/-- Canonical basis of `mayerNegativeSubspace` indexed by `upperRightMayerResonances`. -/
def mayerNegativeBasis : Module.Basis upperRightMayerResonances ℂ mayerNegativeSubspace :=
  Module.Basis.span mayerOffLineNegativeState_upperRight_linearIndependent

theorem mayerKreinReflection_eq_neg_on_negativeSubspace {w : mayerPeriodKreinSpace}
    (hw : w ∈ mayerNegativeSubspace) :
    mayerKreinReflection w = -w := by
  have hle : mayerNegativeSubspace ≤ LinearMap.ker (mayerKreinReflection + LinearMap.id) := by
    rw [mayerNegativeSubspace, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
      mayerKreinReflection_offLineNegativeState, neg_add_cancel]
  have hker := LinearMap.mem_ker.mp (hle hw)
  rw [LinearMap.add_apply, LinearMap.id_apply] at hker
  exact eq_neg_of_add_eq_zero_left hker

/-- **Strict Negative-Definiteness of `mayerNegativeSubspace`.** For every nonzero
`w ∈ mayerNegativeSubspace`, `([w, w]_PM).re = -(⟨w, w⟩_PM^+).re < 0`. -/
theorem mayerKreinForm_neg_on_negativeSubspace {w : mayerPeriodKreinSpace}
    (hw : w ∈ mayerNegativeSubspace) (hne : w ≠ 0) :
    (mayerKreinForm w w).re < 0 := by
  have heq : mayerKreinForm w w = -mayerKreinPosInner w w := by
    unfold mayerKreinForm
    rw [mayerKreinReflection_eq_neg_on_negativeSubspace hw, ← neg_one_smul ℂ w,
      ← mayerKreinPosInner_conj_symm, mayerKreinPosInner_smul_left,
      map_mul, map_neg, map_one, mayerKreinPosInner_conj_symm, neg_one_mul]
  rw [heq, Complex.neg_re, Left.neg_neg_iff]
  exact (mayerKreinPosInner_self_re_pos_iff w).mpr hne

/-- Twice the index-set cardinality of the basis `mayerNegativeBasis` of `W_PM^-` equals the
Weil–Hodge polar defect `boostPolarIndex ratCorr`. -/
theorem two_mul_encard_negativeBasisIndex_eq_boostPolarIndex :
    2 * upperRightMayerResonances.encard = boostPolarIndex ratCorr :=
  boostPolarIndex_ratCorr_eq_two_mul_encard_upperRightMayerResonances.symm

/-- **Unconditional Four-Way Equivalence:**
1. Krein positivity on the space `W_PM` of resonant Cauchy–Lewis period cores,
2. Critical-line confinement `Re s = 1/4` of all upper Mayer resonances (reality of all
   eigenvalues of the Krein self-adjoint Lax–Phillips operator `B_PM`),
3. `RiemannHypothesis`,
4. `RenormalizedHodgeIndex ratCorr`. -/
theorem mayerKreinPositivity_iff_upperResonances_critical :
    (∀ u : mayerPeriodKreinSpace, 0 ≤ (mayerKreinForm u u).re) ↔
      ∀ s : upperMayerResonances, s.1.re = 1 / 4 := by
  constructor
  · intro hpos s
    by_contra hne
    have hneg := mayerKreinForm_offLineNegativeState_self hne
    have hp := hpos (mayerOffLineNegativeState s)
    rw [hneg] at hp
    norm_num at hp
  · intro hall u
    have hid : mayerKreinReflection = LinearMap.id := by
      refine mayerPeriodBasis.ext fun s => ?_
      rw [mayerKreinReflection_basis, LinearMap.id_apply,
        (reflectUpperResonance_eq_self_iff s).mpr (hall s)]
    unfold mayerKreinForm
    rw [hid, LinearMap.id_apply]
    exact mayerKreinPosInner_self_re_nonneg u

theorem mayerKreinPositivity_iff_riemannHypothesis :
    (∀ u : mayerPeriodKreinSpace, 0 ≤ (mayerKreinForm u u).re) ↔ RiemannHypothesis := by
  rw [mayerKreinPositivity_iff_upperResonances_critical,
    riemannHypothesis_iff_forall_isMayerScatteringResonance_re]
  constructor
  · intro hall s hs
    have him := im_ne_zero_of_isMayerScatteringResonance hs
    rcases lt_or_gt_of_ne him with hneg | hpos
    · have hconj : ((starRingEnd ℂ) s) ∈ upperMayerResonances :=
        ⟨by simp; linarith, isMayerScatteringResonance_conj_iff.mpr hs⟩
      have hre := hall ⟨(starRingEnd ℂ) s, hconj⟩
      simpa using hre
    · exact hall ⟨s, hpos, hs⟩
  · intro hall s
    exact hall s.1 s.2.2

theorem mayerKreinPositivity_iff_renormalizedHodgeIndex :
    (∀ u : mayerPeriodKreinSpace, 0 ≤ (mayerKreinForm u u).re) ↔
      RenormalizedHodgeIndex ratCorr := by
  rw [mayerKreinPositivity_iff_riemannHypothesis, riemannHypothesis_iff_renormalizedHodgeIndex]

#print axioms lewisModularInversion_mayerPeriodCore
#print axioms resonantFieldCore_linearIndependent
#print axioms mayerPeriodCore_linearIndependent
#print axioms mayerKreinPosInner_self_re_eq_zero_iff
#print axioms mayerKreinPosInner_reflection_unitary
#print axioms mayerKreinForm_laxPhillipsGenerator_selfAdjoint
#print axioms mayerKreinForm_offLineNegativeState_self
#print axioms mayerKreinForm_neg_on_negativeSubspace
#print axioms two_mul_encard_negativeBasisIndex_eq_boostPolarIndex
#print axioms mayerKreinPositivity_iff_riemannHypothesis
#print axioms mayerKreinPositivity_iff_renormalizedHodgeIndex

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

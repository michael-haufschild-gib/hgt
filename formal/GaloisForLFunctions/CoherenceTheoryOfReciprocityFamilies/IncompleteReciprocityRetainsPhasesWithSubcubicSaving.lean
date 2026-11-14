import GaloisForLFunctions.MetaplecticMobiusDescent.Mellin.UniformPolynomialKernels
import GaloisForLFunctions.MetaplecticMobiusDescent.GaussSums.UnitTensorCoefficients
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.PrimeFamiliesAndIdealCounts

/-!
# Incomplete Reciprocity Retains Root-Number Phases With Sub-Cubic Defect Saving

For a nonzero Eisenstein modulus `c ∈ O = ℤ[ω]`, a character `Ψ : (O / (c)) →* ℂ` (`‖Ψ‖ ≤ 1`), a
smooth compactly supported window `W₀ ∈ C_c^∞([a, b])` (`0 < a < b`) twisted by a complex variable
`s ∈ ℂ` via `W_s(y) = y^{1/2 - s} W₀(y)`, a sum scale `X > 0`, and independent direct and dual cube
cutoffs `Y₀, Y₀' > 1`, splitting the ideal-indexed Gauss sum `completedIdealT` and its polar-free
finite-cusp reflection `completedT_finite_cusp_full_reflection` gives the exact arithmetic
reciprocity identity

`incompleteIdealT_{Y₀}(Ψ_c, W_s, X) = incompleteCuspDual_{Y₀'}(c, Ψ, d, W_s, X) + reciprocityBoundaryDefect_{Y₀, Y₀'}(c, Ψ, d, W_s, X)`.

This module proves:

1. **Exact target, dual `1 - s` scaling, root-number phases, and non-reducibility:**
   - `vstar_complexTwistedWindow_apply`: on `(0, ∞)`, `Vstar (W_s) y = y^{1 - s} W₀(y)`.
   - `incompleteIdealT_cusp_reciprocity`: exact doubly-incomplete cusp reciprocity identity.
   - `incompleteIdealSummand_retains_target` and `incompleteReciprocity_retains_rootNumber_phases`:
     for `Y₀ > 1`, the `J = (1)` reciprocal/Möbius target summand is retained untouched while good
     prime factors retain all unit-modulus local Gauss root-number phases.
   - `exists_nonreducible_incompleteIdealT_subcubic`: for any dyadic window `0 < a < b < 4a` and any
     strictly sub-cubic exponent `0 < η < 1/3`, `incompleteIdealT (X^η)` is strictly unequal to the
     full monomial completion `completedIdealT` at arbitrarily large scales `X`.

2. **Uniform defect power saving across the super-conductor reflection box vs sub-conductor barrier:**
   - `directCubeTail_uniform_box_bound`: uniformly on any compact rectangle `ℛ ⊆ ℂ`,
     `‖directCubeTail_{≥ Y₀}(Ψ, W_s, X)‖ ≤ C_dir(ℛ, W₀) · X · Y₀^{-3}`.
   - `dualCubeTail_uniform_box_bound`: uniformly on `ℛ` and for every `N : ℕ`,
     `‖dualCubeTail_{≥ Y₀'}(c, Ψ, d_can, W_s, X)‖ ≤ C_dual(ℛ, W₀, N) · |O/(9c)| · s_c(X)^{-2} · (s_c(X) · Y₀'³)^{-N}`.
   - `milestone_one_subcubic_power_saving`: for any `0 < δ < 1` and `1/6 < η < 1/3` with
     `η' = max(δ/3, (1 - δ)/3) < 1/3`, uniformly over `X ≥ 1`, `N(c) ≤ X^{1 - δ}`, `‖Ψ‖ ≤ 1`, and
     `s ∈ ℛ`, `‖reciprocityBoundaryDefect_{X^η, X^{η'}}‖ ≤ C · X^{1/2 - min(3η - 1/2, 1)}`, saving
     a uniform power below both the trivial bound `X` and square-root cancellation `X^{1/2}`.
   - `subconductor_dual_scale_obstruction`: in the sub-conductor regime `N(c) ≥ X^{1 + κ}` (`κ > 0`),
     the primitive cusp reflection scale times `(X^{η'})³` is `O(X^{-2κ})` for every `η' ≤ 1/3`.
-/

noncomputable section

open Complex Set Filter MeasureTheory NumberField IsDedekindDomain
open scoped BigOperators Classical Topology SchwartzMap ContDiff MatrixGroups

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

open MetaplecticMobiusDescent
open MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicEisenstein
open MetaplecticMobiusDescent.CubicEisenstein.SchwartzPlanePoisson
open MetaplecticMobiusDescent.CubicEisenstein.CompletedGauss
open MetaplecticMobiusDescent.CubicEisenstein.CompletedHeight
open MetaplecticMobiusDescent.CubicEisenstein.EisensteinLatticeCount

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-! ### 1. Complex-twisted radial windows and uniform Schwartz seminorm bounds on rectangles -/

/-- The radial window `y^{1/2 - s} W₀(y)` twisted by `s ∈ ℂ`, zero on `(-∞, 0]`. -/
def complexTwistedWindow (W₀ : ℝ → ℂ) (s : ℂ) (y : ℝ) : ℂ :=
  if 0 < y then (y : ℂ) ^ ((1 / 2 : ℂ) - s) * W₀ y else 0

/-- Compact rectangular complex parameter box `{s ∈ ℂ | σ₁ ≤ Re s ≤ σ₂ ∧ |Im s| ≤ T}`. -/
def complexParameterBox (σ₁ σ₂ T : ℝ) : Set ℂ :=
  {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ σ₂ ∧ |s.im| ≤ T}

theorem isCompact_complexParameterBox (σ₁ σ₂ T : ℝ) :
    IsCompact (complexParameterBox σ₁ σ₂ T) := by
  have hclosed : IsClosed (complexParameterBox σ₁ σ₂ T) :=
    (isClosed_le continuous_const continuous_re).inter
      ((isClosed_le continuous_re continuous_const).inter
        (isClosed_le continuous_im.abs continuous_const))
  set R : ℝ := max (|σ₁| + |σ₂|) 0 + max T 0
  refine Metric.isCompact_of_isClosed_isBounded hclosed
    (Metric.isBounded_iff_subset_closedBall (0 : ℂ) |>.mpr ⟨R, fun s hs => ?_⟩)
  rw [Metric.mem_closedBall, dist_zero_right]
  have hre : |s.re| ≤ max (|σ₁| + |σ₂|) 0 := by
    have habs : |s.re| ≤ |σ₁| + |σ₂| :=
      abs_le.mpr ⟨by linarith [hs.1, neg_abs_le σ₁, abs_nonneg σ₂],
        by linarith [hs.2.1, le_abs_self σ₂, abs_nonneg σ₁]⟩
    exact habs.trans (le_max_left _ _)
  have him : |s.im| ≤ max T 0 := hs.2.2.trans (le_max_left _ _)
  calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ ≤ R := add_le_add hre him

/-- On `(0, ∞)`, `Vstar` shifts `y^{1/2 - s} W₀(y)` to the dual Mellin exponent `y^{1 - s} W₀(y)`. -/
theorem vstar_complexTwistedWindow_apply (W₀ : ℝ → ℂ) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    Vstar (complexTwistedWindow W₀ s) y = (y : ℂ) ^ ((1 : ℂ) - s) * W₀ y := by
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [Vstar, complexTwistedWindow, if_pos hy, ← mul_assoc]
  congr 1
  have hsqrt : (Real.sqrt y : ℂ) = (y : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hy.le]
    push_cast
    rfl
  rw [hsqrt, ← Complex.cpow_add _ _ hyc]
  congr 1
  ring

theorem complexTwistedWindow_support (W₀ : ℝ → ℂ) {a b : ℝ}
    (hs : Function.support W₀ ⊆ Icc a b) (s : ℂ) :
    Function.support (complexTwistedWindow W₀ s) ⊆ Icc a b := by
  intro y hy
  apply hs
  intro hz
  exact hy (by simp [complexTwistedWindow, hz])

/-- Smooth representation of `complexTwistedWindow W₀ s` via `patchedLog` on `Icc a b`. -/
theorem complexTwistedWindow_eq_exp_patchedLog (W₀ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hs : Function.support W₀ ⊆ Icc a b) (s : ℂ) (y : ℝ) :
    complexTwistedWindow W₀ s y =
      Complex.exp (((1 / 2 : ℂ) - s) * (patchedLog a b ha y : ℂ)) * W₀ y := by
  by_cases hw : W₀ y = 0
  · simp [complexTwistedWindow, hw]
  · have hy_mem : y ∈ Icc a b := hs hw
    have hy : 0 < y := lt_of_lt_of_le ha hy_mem.1
    have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    rw [complexTwistedWindow, if_pos hy, patchedLog_eq_log a b ha y hy_mem,
      Complex.cpow_def_of_ne_zero hyc, Complex.ofReal_log hy.le]
    ring_nf

/-- Smooth representation of `Vstar (complexTwistedWindow W₀ s)` via `patchedLog` on `Icc a b`. -/
theorem vstar_complexTwistedWindow_eq_exp_patchedLog (W₀ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hs : Function.support W₀ ⊆ Icc a b) (s : ℂ) (y : ℝ) :
    Vstar (complexTwistedWindow W₀ s) y =
      Complex.exp (((1 : ℂ) - s) * (patchedLog a b ha y : ℂ)) * W₀ y := by
  by_cases hw : W₀ y = 0
  · simp [Vstar, complexTwistedWindow, hw]
  · have hy_mem : y ∈ Icc a b := hs hw
    have hy : 0 < y := lt_of_lt_of_le ha hy_mem.1
    have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    rw [vstar_complexTwistedWindow_apply W₀ s hy, patchedLog_eq_log a b ha y hy_mem,
      Complex.cpow_def_of_ne_zero hyc, Complex.ofReal_log hy.le]
    ring_nf

theorem complexTwistedWindow_contDiff (W₀ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hs : Function.support W₀ ⊆ Icc a b) (hW : ContDiff ℝ ∞ W₀) (s : ℂ) :
    ContDiff ℝ ∞ (complexTwistedWindow W₀ s) := by
  have heq : complexTwistedWindow W₀ s =
      fun y => Complex.exp (((1 / 2 : ℂ) - s) * (patchedLog a b ha y : ℂ)) * W₀ y :=
    funext (complexTwistedWindow_eq_exp_patchedLog W₀ ha hs s)
  rw [heq]
  have hlog : ContDiff ℝ ∞ (fun y : ℝ => (patchedLog a b ha y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (patchedLog_temperate a b ha).1
  exact (Complex.contDiff_exp.comp (contDiff_const.mul hlog)).mul hW

/-- The compactly supported Schwartz function attached to `Vstar (complexTwistedWindow W₀ s)`. -/
def vstarTwistedSchwartz (W₀ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hs : Function.support W₀ ⊆ Icc a b) (hW : ContDiff ℝ ∞ W₀) (s : ℂ) : 𝓢(ℝ, ℂ) :=
  vstarSchwartz (complexTwistedWindow W₀ s) a b ha
    (complexTwistedWindow_support W₀ hs s) (complexTwistedWindow_contDiff W₀ ha hs hW s)

@[simp]
theorem vstarTwistedSchwartz_apply (W₀ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hs : Function.support W₀ ⊆ Icc a b) (hW : ContDiff ℝ ∞ W₀) (s : ℂ) (y : ℝ) :
    vstarTwistedSchwartz W₀ ha hs hW s y = Vstar (complexTwistedWindow W₀ s) y :=
  rfl

/-- Every finite family of Schwartz seminorms of `Vstar (complexTwistedWindow W₀ s)` is uniformly
bounded over any compact subset `K ⊆ ℂ`. -/
theorem vstarTwistedSchwartz_seminorm_uniform_bound (W₀ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (_hab : a ≤ b) (hs : Function.support W₀ ⊆ Icc a b) (hW : ContDiff ℝ ∞ W₀)
    {K : Set ℂ} (hK : IsCompact K) (S : Finset (ℕ × ℕ)) :
    ∃ M : ℝ, 0 < M ∧ ∀ s ∈ K,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (vstarTwistedSchwartz W₀ ha hs hW s) ≤ M := by
  let H : ℂ × ℝ → ℂ := fun p =>
    Complex.exp (((1 : ℂ) - p.1) * (patchedLog a b ha p.2 : ℂ)) * W₀ p.2
  have hlog : ContDiff ℝ ∞ (fun p : ℂ × ℝ => (patchedLog a b ha p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((patchedLog_temperate a b ha).1.comp contDiff_snd)
  have hsub : ContDiff ℝ ∞ (fun p : ℂ × ℝ => (1 : ℂ) - p.1) :=
    contDiff_const.sub contDiff_fst
  have hH : ContDiff ℝ ∞ H :=
    (Complex.contDiff_exp.comp (hsub.mul hlog)).mul (hW.comp contDiff_snd)
  have hsingle : ∀ z : ℕ × ℕ, ∃ B : ℝ, 0 < B ∧ ∀ s ∈ K,
      schwartzSeminormFamily ℝ ℝ ℂ z (vstarTwistedSchwartz W₀ ha hs hW s) ≤ B := by
    intro ⟨k, n⟩
    have hcont : Continuous (fun p : ℂ × ℝ => ‖p.2‖ ^ k * ‖iteratedFDeriv ℝ n H p‖) :=
      (continuous_snd.norm.pow k).mul
        ((hH.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).norm)
    obtain ⟨B₀, hB₀⟩ := (hK.prod isCompact_Icc).bddAbove_image hcont.continuousOn
    set L : ℝ := ‖ContinuousLinearMap.inr ℝ ℂ ℝ‖ ^ n
    refine ⟨max B₀ 0 * max L 1 + 1, by positivity, fun s hsK => ?_⟩
    refine SchwartzMap.seminorm_le_bound ℝ k n (vstarTwistedSchwartz W₀ ha hs hW s)
      (by positivity) fun y => ?_
    have hHs : ContDiff ℝ ∞ (fun q : ℂ × ℝ => H ((s, 0) + q)) :=
      hH.comp (contDiff_const.add contDiff_id)
    have hslice : (vstarTwistedSchwartz W₀ ha hs hW s : ℝ → ℂ) =
        (fun q : ℂ × ℝ => H ((s, 0) + q)) ∘ ContinuousLinearMap.inr ℝ ℂ ℝ := by
      funext u
      simpa [Function.comp, H] using vstar_complexTwistedWindow_eq_exp_patchedLog W₀ ha hs s u
    by_cases hy : y ∈ Icc a b
    · rw [hslice, (ContinuousLinearMap.inr ℝ ℂ ℝ).iteratedFDeriv_comp_right hHs y
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))]
      have htrans : iteratedFDeriv ℝ n (fun q : ℂ × ℝ => H ((s, 0) + q))
          (ContinuousLinearMap.inr ℝ ℂ ℝ y) = iteratedFDeriv ℝ n H (s, y) := by
        rw [iteratedFDeriv_comp_add_left]
        simp
      rw [htrans]
      have hcomp_norm :
          ‖(iteratedFDeriv ℝ n H (s, y)).compContinuousLinearMap
            (fun _ => ContinuousLinearMap.inr ℝ ℂ ℝ)‖ ≤
          ‖iteratedFDeriv ℝ n H (s, y)‖ * L := by
        simpa [L, Finset.prod_const, Finset.card_fin] using
          (iteratedFDeriv ℝ n H (s, y)).norm_compContinuousLinearMap_le
            (fun _ => ContinuousLinearMap.inr ℝ ℂ ℝ)
      have hpt : ‖y‖ ^ k * ‖iteratedFDeriv ℝ n H (s, y)‖ ≤ max B₀ 0 :=
        (hB₀ ⟨(s, y), ⟨hsK, hy⟩, rfl⟩).trans (le_max_left _ _)
      calc ‖y‖ ^ k * ‖(iteratedFDeriv ℝ n H (s, y)).compContinuousLinearMap
              (fun _ => ContinuousLinearMap.inr ℝ ℂ ℝ)‖
          ≤ ‖y‖ ^ k * (‖iteratedFDeriv ℝ n H (s, y)‖ * L) :=
            mul_le_mul_of_nonneg_left hcomp_norm (by positivity)
        _ = (‖y‖ ^ k * ‖iteratedFDeriv ℝ n H (s, y)‖) * L := by ring
        _ ≤ max B₀ 0 * max L 1 :=
            mul_le_mul hpt (le_max_left _ _) (by positivity) (le_max_right _ _)
        _ ≤ max B₀ 0 * max L 1 + 1 := by linarith
    · have hsupp_v : Function.support (vstarTwistedSchwartz W₀ ha hs hW s : ℝ → ℂ) ⊆ Icc a b :=
        Vstar_support _ a b (complexTwistedWindow_support W₀ hs s)
      have htsupp : tsupport (iteratedFDeriv ℝ n
          (vstarTwistedSchwartz W₀ ha hs hW s : ℝ → ℂ)) ⊆ Icc a b :=
        (tsupport_iteratedFDeriv_subset n).trans (closure_minimal hsupp_v isClosed_Icc)
      have hz : iteratedFDeriv ℝ n (vstarTwistedSchwartz W₀ ha hs hW s : ℝ → ℂ) y = 0 := by
        by_contra hne
        exact hy (htsupp (subset_tsupport _ hne))
      rw [hz, norm_zero, mul_zero]
      positivity
  choose B hB hB_bound using hsingle
  have hsum_pos : 0 < (∑ z ∈ S, B z) + 1 :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun z _ => (hB z).le) zero_lt_one
  refine ⟨(∑ z ∈ S, B z) + 1, hsum_pos, fun s hsK => ?_⟩
  refine Seminorm.finset_sup_apply_le hsum_pos.le fun z hz => ?_
  exact (hB_bound z s hsK).trans
    ((Finset.single_le_sum (fun w _ => (hB w).le) hz).trans (by linarith))

/-- Uniform supremum bound on `Vstar (complexTwistedWindow W₀ s)` over any compact subset `K ⊆ ℂ`. -/
theorem vstar_complexTwistedWindow_uniform_sup_bound (W₀ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hs : Function.support W₀ ⊆ Icc a b) (hW : ContDiff ℝ ∞ W₀)
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ M : ℝ, 0 < M ∧ ∀ s ∈ K, ∀ y : ℝ, ‖Vstar (complexTwistedWindow W₀ s) y‖ ≤ M := by
  obtain ⟨M, hM, hsem⟩ := vstarTwistedSchwartz_seminorm_uniform_bound W₀ ha hab hs hW hK {(0, 0)}
  refine ⟨M, hM, fun s hsK y => ?_⟩
  have h00 : schwartzSeminormFamily ℝ ℝ ℂ (0, 0) (vstarTwistedSchwartz W₀ ha hs hW s) ≤ M := by
    simpa using hsem s hsK
  have hpt := SchwartzMap.norm_le_seminorm ℝ (vstarTwistedSchwartz W₀ ha hs hW s) y
  exact hpt.trans h00

/-- Uniform rapid polynomial decay of `paperKernel (Vstar (complexTwistedWindow W₀ s))` over any
compact subset `K ⊆ ℂ`. -/
theorem paperKernel_complexTwistedWindow_uniform_bound (W₀ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hs : Function.support W₀ ⊆ Icc a b) (hW : ContDiff ℝ ∞ W₀)
    {K : Set ℂ} (hK : IsCompact K) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ K, ∀ x : ℝ, 0 < x →
      ‖paperKernel (Vstar (complexTwistedWindow W₀ s)) x‖ ≤ C * x ^ (-(N : ℝ)) := by
  obtain ⟨S, C₀, hC₀, hdecay⟩ := paperKernel_euler_source_power_decay a b ha N 0
  obtain ⟨M, hM, hsem⟩ := vstarTwistedSchwartz_seminorm_uniform_bound W₀ ha hab hs hW hK S
  refine ⟨C₀ * M, mul_pos hC₀ hM, fun s hsK x hx => ?_⟩
  have hsupp_s : Function.support (vstarTwistedSchwartz W₀ ha hs hW s : ℝ → ℂ) ⊆ Icc a b :=
    Vstar_support _ a b (complexTwistedWindow_support W₀ hs s)
  have h0 := (hdecay (vstarTwistedSchwartz W₀ ha hs hW s) hsupp_s x hx).2
  have heuler0 : LocalLogFourier.eulerDeriv
      (paperKernel (vstarTwistedSchwartz W₀ ha hs hW s)) 0 x =
      paperKernel (Vstar (complexTwistedWindow W₀ s)) x := by
    have hcoe : (vstarTwistedSchwartz W₀ ha hs hW s : ℝ → ℂ) =
        Vstar (complexTwistedWindow W₀ s) := by
      ext y; rfl
    simp [LocalLogFourier.eulerDeriv, hcoe]
  rw [heuler0] at h0
  calc ‖paperKernel (Vstar (complexTwistedWindow W₀ s)) x‖
      ≤ C₀ * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (vstarTwistedSchwartz W₀ ha hs hW s) *
          x ^ (-(N : ℝ)) := h0
    _ ≤ C₀ * M * x ^ (-(N : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hsem s hsK) hC₀.le) (Real.rpow_nonneg hx.le _)

/-! ### 2. Doubly-incomplete Eisenstein cube-Gauss reciprocity identity -/

/-- Direct summand of the incomplete Gauss sum with cube norm strictly below `Y₀`. -/
def incompleteIdealSummand (Y₀ : ℝ) (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  if (Ideal.absNorm J : ℝ) < Y₀ then CompletedGauss.summand Ψ W X I J else 0

/-- Omitted direct cube-tail summand with cube norm at least `Y₀`. -/
def directCubeTailSummand (Y₀ : ℝ) (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  if Y₀ ≤ (Ideal.absNorm J : ℝ) then CompletedGauss.summand Ψ W X I J else 0

/-- Incomplete ideal-indexed Eisenstein cube-Gauss sum truncated at `N(J) < Y₀`. -/
def incompleteIdealT (Y₀ : ℝ) (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, ∑' J : Ideal O, incompleteIdealSummand Y₀ Ψ W X I J

/-- Direct cube tail `N(J) ≥ Y₀` omitted by `incompleteIdealT`. -/
def directCubeTail (Y₀ : ℝ) (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, ∑' J : Ideal O, directCubeTailSummand Y₀ Ψ W X I J

/-- Dual full-index summand at cusp `d` with dual cube norm strictly below `Y₀'`. -/
def incompleteDualSummand (Y₀' : ℝ) (d : SourceCuspDatum) (W : ℝ → ℂ) (X : ℝ)
    (p : ThetaFullIndex) : ℂ :=
  if (Ideal.absNorm p.2.2.2.val : ℝ) < Y₀' then
    sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p) *
      paperKernel (Vstar W) (d.smoothingScale X *
        (‖ringComplex lambda‖ ^ (2 * p.2.1) * completedMellinLength p.2.2))
  else 0

/-- Dual full-index tail summand at cusp `d` with dual cube norm at least `Y₀'`. -/
def dualCubeTailSummand (Y₀' : ℝ) (d : SourceCuspDatum) (W : ℝ → ℂ) (X : ℝ)
    (p : ThetaFullIndex) : ℂ :=
  if Y₀' ≤ (Ideal.absNorm p.2.2.2.val : ℝ) then
    sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p) *
      paperKernel (Vstar W) (d.smoothingScale X *
        (‖ringComplex lambda‖ ^ (2 * p.2.1) * completedMellinLength p.2.2))
  else 0

/-- Incomplete reflected cusp dual truncated at dual cube norm `N(J') < Y₀'`. -/
def incompleteCuspDual (Y₀' : ℝ) (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (d : (O ⧸ Ideal.span {9 * c}) → SourceCuspDatum) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  thetaDerivativeScalar⁻¹ * ∑ i : O ⧸ Ideal.span {9 * c},
    finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
      (finiteThetaTwist c Ψ) i *
      ((d i).smoothingMultiplier * ∑' p : ThetaFullIndex, incompleteDualSummand Y₀' (d i) W X p)

/-- Dual cube tail `N(J') ≥ Y₀'` omitted on the reflected cusp side. -/
def dualCubeTail (Y₀' : ℝ) (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (d : (O ⧸ Ideal.span {9 * c}) → SourceCuspDatum) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  thetaDerivativeScalar⁻¹ * ∑ i : O ⧸ Ideal.span {9 * c},
    finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
      (finiteThetaTwist c Ψ) i *
      ((d i).smoothingMultiplier * ∑' p : ThetaFullIndex, dualCubeTailSummand Y₀' (d i) W X p)

/-- Total boundary defect of the doubly incomplete reciprocity transform. -/
def reciprocityBoundaryDefect (Y₀ Y₀' : ℝ) (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (d : (O ⧸ Ideal.span {9 * c}) → SourceCuspDatum) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  dualCubeTail Y₀' c hc Ψ d W X -
    directCubeTail Y₀ (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) W X

theorem incompleteIdealT_add_directCubeTail (Y₀ : ℝ) (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    incompleteIdealT Y₀ Ψ W X + directCubeTail Y₀ Ψ W X = completedIdealT Ψ W X := by
  have hpair : Summable (fun q : Ideal O × Ideal O => CompletedGauss.summand Ψ W X q.1 q.2) :=
    completedIdealT_summable Ψ W hW X hX
  have hI_sum : ∀ I : Ideal O, Summable (fun J : Ideal O => CompletedGauss.summand Ψ W X I J) :=
    fun I => hpair.prod_factor I
  have hinc_J : ∀ I : Ideal O, Summable (fun J : Ideal O => incompleteIdealSummand Y₀ Ψ W X I J) :=
    fun I => Summable.of_norm_bounded (hI_sum I).norm fun J => by
      unfold incompleteIdealSummand
      split_ifs <;> simp
  have htail_J : ∀ I : Ideal O, Summable (fun J : Ideal O => directCubeTailSummand Y₀ Ψ W X I J) :=
    fun I => Summable.of_norm_bounded (hI_sum I).norm fun J => by
      unfold directCubeTailSummand
      split_ifs <;> simp
  have hpt : ∀ I J : Ideal O,
      incompleteIdealSummand Y₀ Ψ W X I J + directCubeTailSummand Y₀ Ψ W X I J =
        CompletedGauss.summand Ψ W X I J := by
    intro I J
    unfold incompleteIdealSummand directCubeTailSummand
    by_cases hlt : (Ideal.absNorm J : ℝ) < Y₀
    · rw [if_pos hlt, if_neg (not_le.mpr hlt), add_zero]
    · rw [if_neg hlt, if_pos (not_lt.mp hlt), zero_add]
  have hinc_I : Summable (fun I : Ideal O => ∑' J : Ideal O, incompleteIdealSummand Y₀ Ψ W X I J) := by
    have hinc_pair : Summable (fun q : Ideal O × Ideal O =>
        incompleteIdealSummand Y₀ Ψ W X q.1 q.2) :=
      Summable.of_norm_bounded hpair.norm fun q => by
        unfold incompleteIdealSummand; split_ifs <;> simp
    exact hinc_pair.prod
  have htail_I : Summable (fun I : Ideal O => ∑' J : Ideal O, directCubeTailSummand Y₀ Ψ W X I J) := by
    have htail_pair : Summable (fun q : Ideal O × Ideal O =>
        directCubeTailSummand Y₀ Ψ W X q.1 q.2) :=
      Summable.of_norm_bounded hpair.norm fun q => by
        unfold directCubeTailSummand; split_ifs <;> simp
    exact htail_pair.prod
  unfold incompleteIdealT directCubeTail completedIdealT
  rw [← hinc_I.tsum_add htail_I]
  refine tsum_congr fun I => ?_
  rw [← (hinc_J I).tsum_add (htail_J I)]
  exact tsum_congr (hpt I)

/-- **Exact doubly-incomplete Eisenstein cusp reciprocity identity.** -/
theorem incompleteIdealT_cusp_reciprocity (Y₀ Y₀' : ℝ) (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (d : (O ⧸ Ideal.span {9 * c}) → SourceCuspDatum)
    (hd : ∀ i, (d i).point = thetaFourierTranslation (9 * c) i)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    incompleteIdealT Y₀ (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) W X =
      incompleteCuspDual Y₀' c hc Ψ d W X + reciprocityBoundaryDefect Y₀ Y₀' c hc Ψ d W X := by
  set Ψc : O →* ℂ := Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom
  have hW_cpt : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  have hdir := incompleteIdealT_add_directCubeTail Y₀ Ψc W hW_cpt X hX
  have hrefl := completedT_finite_cusp_full_reflection c hc Ψ d hd W a b ha hs hW X hX
  rw [← completedIdealT_eq_completedT Ψc W hW_cpt X hX] at hrefl
  have hdual_split :
      incompleteCuspDual Y₀' c hc Ψ d W X + dualCubeTail Y₀' c hc Ψ d W X =
        completedIdealT Ψc W X := by
    rw [hrefl]
    unfold incompleteCuspDual dualCubeTail
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_add, ← mul_add]
    congr 2
    have hfull_norm : Summable (fun p : ThetaFullIndex =>
        ‖sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p) *
          paperKernel (Vstar W) ((d i).smoothingScale X *
            sourceCuspRadialLength (thetaFullFrequency p))‖) :=
      sourceCusp_full_kernel_norm_summable (d i).index (d i).dualPoint (Vstar W) a b ha
        (Vstar_support W a b hs) (Vstar_contDiff W a b ha hs hW) ((d i).smoothingScale X)
        ((d i).smoothingScale_pos X hX)
    have hfull : Summable (fun p : ThetaFullIndex =>
        sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p) *
          paperKernel (Vstar W) ((d i).smoothingScale X *
            (‖ringComplex lambda‖ ^ (2 * p.2.1) * completedMellinLength p.2.2))) := by
      refine Summable.of_norm ?_
      simpa only [thetaFullFrequency_radialLength] using hfull_norm
    have hinc : Summable (incompleteDualSummand Y₀' (d i) W X) :=
      Summable.of_norm_bounded hfull.norm fun p => by
        unfold incompleteDualSummand
        split_ifs
        · exact le_rfl
        · rw [norm_zero]; exact norm_nonneg _
    have htail : Summable (dualCubeTailSummand Y₀' (d i) W X) :=
      Summable.of_norm_bounded hfull.norm fun p => by
        unfold dualCubeTailSummand
        split_ifs
        · exact le_rfl
        · rw [norm_zero]; exact norm_nonneg _
    rw [← hinc.tsum_add htail]
    refine tsum_congr fun p => ?_
    unfold incompleteDualSummand dualCubeTailSummand
    by_cases hlt : (Ideal.absNorm p.2.2.2.val : ℝ) < Y₀'
    · rw [if_pos hlt, if_neg (not_le.mpr hlt), add_zero]
    · rw [if_neg hlt, if_pos (not_lt.mp hlt), zero_add]
  change incompleteIdealT Y₀ Ψc W X =
    incompleteCuspDual Y₀' c hc Ψ d W X +
      (dualCubeTail Y₀' c hc Ψ d W X - directCubeTail Y₀ Ψc W X)
  linear_combination hdir - hdual_split

/-- **Exact target retention:** for any `Y₀ > 1`, the `J = (1)` summand of `incompleteIdealT`
equals the exact uncompleted Gauss column weight at `I`, without averaging or truncation loss. -/
theorem incompleteIdealSummand_retains_target {Y₀ : ℝ} (hY₀ : 1 < Y₀) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) {X : ℝ} (hX : 0 < X) (I : Ideal O) :
    incompleteIdealSummand Y₀ Ψ W X I 1 =
      (Real.sqrt X : ℂ)⁻¹ * columnWeight Ψ I * W ((Ideal.absNorm I : ℝ) / X) := by
  have hlt : (Ideal.absNorm (1 : Ideal O) : ℝ) < Y₀ := by
    rw [map_one Ideal.absNorm]; exact_mod_cast hY₀
  rw [incompleteIdealSummand, if_pos hlt, CompletedGauss.summand, map_one (cubeWeight Ψ),
    map_one Ideal.absNorm, mul_one, Nat.cast_one, one_pow, mul_one]
  exact vstar_source_normalization Ψ W X hX I

/-- **Exact root-number phase retention:** across any finite family of good maximal ideals `P i`,
the local cusp reflection retains the exact unit-modulus Gauss root-number phase times the
quadratic residue character. -/
theorem incompleteReciprocity_retains_rootNumber_phases
    {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (ψ : ∀ i, AddChar (O ⧸ P i) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ x : ∀ i, O ⧸ P i,
      (∑ h : ∀ i, (O ⧸ P i)ˣ, ∏ i,
        finiteAdditiveFourierCoeff (ψ i) (complexSexticChar (P i) (hg i)) (h i : O ⧸ P i) *
          ((complexSexticChar (P i) (hg i))⁻¹ ^ 2) (h i) *
          ψ i (x i * (((h i)⁻¹ : (O ⧸ P i)ˣ) : O ⧸ P i))) =
      ε * ∏ i, complexQuadraticChar (P i) (x i) :=
  finiteReflectionGauss_actual_quadratic_family P hg hchar ψ hψ

/-! ### 3. Strict non-reducibility to full monomial completion at every sub-cubic exponent -/

private lemma absNorm_power_of_two_is_cubicTwoIdeal_pow {I : Ideal O} (hI0 : I ≠ 0)
    (hodd : ∀ d : ℕ, d % 2 = 1 → d ∣ Ideal.absNorm I → d = 1) :
    ∃ r : ℕ, I = cubicTwoIdeal ^ r ∧ Ideal.absNorm I = 4 ^ r := by
  classical
  have hfactors : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, P = cubicTwoIdeal := by
    intro P hP
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    letI : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hP_dvd : P ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    have hNP_dvd : Ideal.absNorm P ∣ Ideal.absNorm I := by
      rcases hP_dvd with ⟨Q, rfl⟩
      rw [map_mul]
      exact dvd_mul_right _ _
    have hNP_gt1 : 1 < Ideal.absNorm P := by
      by_contra hle
      have hNP0 : Ideal.absNorm P ≠ 0 := fun h => hp.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
      have hNP1 : Ideal.absNorm P = 1 := by omega
      exact (Ideal.IsMaximal.ne_top ‹P.IsMaximal›) (Ideal.absNorm_eq_one_iff.mp hNP1)
    obtain ⟨q, hq_prime, hq_dvd_NP⟩ := Nat.exists_prime_and_dvd hNP_gt1.ne'
    have hq2 : q = 2 := by
      by_contra hne2
      have hq_odd : q % 2 = 1 := hq_prime.eq_two_or_odd.resolve_left hne2
      exact hq_prime.ne_one (hodd q hq_odd (hq_dvd_NP.trans hNP_dvd))
    subst hq2
    have h2_mem_P : (-2 : O) ∈ P := by
      by_contra hnot2
      have hnot_le : ¬ cubicTwoIdeal ≤ P :=
        fun hle => hnot2 (hle (Ideal.subset_span rfl))
      have hsup : cubicTwoIdeal ⊔ P = ⊤ := by
        by_contra hne_top
        have heq_sup := cubicTwoIdeal_isMaximal.eq_of_le hne_top le_sup_left
        have hP_le : P ≤ cubicTwoIdeal := heq_sup.symm ▸ le_sup_right
        have hP_eq := ‹P.IsMaximal›.eq_of_le cubicTwoIdeal_isMaximal.ne_top hP_le
        exact hnot_le hP_eq.symm.le
      have h1_mem : (1 : O) ∈ cubicTwoIdeal ⊔ P := by rw [hsup]; trivial
      rcases Submodule.mem_sup.mp h1_mem with ⟨u, hu, p, hp_mem, hup⟩
      rcases Ideal.mem_span_singleton.mp hu with ⟨a, rfl⟩
      have hp_eq : p = 1 + 2 * a := by linear_combination hup
      set n : ℤ := Algebra.norm ℤ p
      have hn_mem : (n : O) ∈ P := by
        rw [norm_int_eq_mul_conjO]
        exact P.mul_mem_right (conjO p) hp_mem
      have hnorm_n : Ideal.absNorm (Ideal.span {(n : O)}) = n.natAbs ^ 2 := by
        have hn_sq : Algebra.norm ℤ (n : O) = n ^ 2 := by
          apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → O))
          rw [norm_int_eq_mul_conjO]
          push_cast
          simp [sq]
        rw [Ideal.absNorm_span_singleton, hn_sq]
        exact Int.natAbs_pow _ 2
      have hdvd_P : Ideal.absNorm P ∣ n.natAbs ^ 2 := by
        rw [← hnorm_n]
        exact Ideal.absNorm_dvd_absNorm_of_le
          (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hn_mem))
      have h2_nat : 2 ∣ n.natAbs :=
        Nat.prime_two.dvd_of_dvd_pow (hq_dvd_NP.trans hdvd_P)
      have h2_int : (2 : ℤ) ∣ n := Int.dvd_natAbs.mp (by exact_mod_cast h2_nat)
      rcases h2_int with ⟨k, hk⟩
      have hn_O : (n : O) = 1 + 2 * (a + conjO a + 2 * a * conjO a) := by
        rw [norm_int_eq_mul_conjO, hp_eq, map_add, map_one, map_mul, map_ofNat]
        ring
      have h1_in_two : (1 : O) ∈ cubicTwoIdeal := by
        refine Ideal.mem_span_singleton.mpr ⟨a + conjO a + 2 * a * conjO a - (k : O), ?_⟩
        have hk_O : (n : O) = 2 * (k : O) := by exact_mod_cast hk
        linear_combination hk_O - hn_O
      exact cubicTwoIdeal_isMaximal.ne_top ((Ideal.eq_top_iff_one cubicTwoIdeal).mpr h1_in_two)
    have hle : cubicTwoIdeal ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h2_mem_P)
    exact (cubicTwoIdeal_isMaximal.eq_of_le ‹P.IsMaximal›.ne_top hle).symm
  set r : ℕ := (UniqueFactorizationMonoid.normalizedFactors I).card
  have hprod_eq : (UniqueFactorizationMonoid.normalizedFactors I).prod = cubicTwoIdeal ^ r := by
    have hmap : UniqueFactorizationMonoid.normalizedFactors I =
        Multiset.replicate r cubicTwoIdeal :=
      Multiset.eq_replicate.mpr ⟨rfl, hfactors⟩
    rw [hmap, Multiset.prod_replicate]
  have hI_eq : I = cubicTwoIdeal ^ r := by
    rw [← Ideal.prod_normalizedFactors_eq_self hI0, hprod_eq]
  refine ⟨r, hI_eq, ?_⟩
  rw [hI_eq, map_pow, cubicTwoIdeal_absNorm]

/-- **Strict non-reducibility to full monomial completion:** for any dyadic support `0 < a < b < 4a`,
any window `W₀` supported in `[a, b]` with `W₀(y₀) ≠ 0` at some `y₀ ∈ [a, b]`, and any strictly
sub-cubic cutoff exponent `0 < η < 1/3`, for arbitrarily large scales `X ≥ max X₀ 1` there exist a
nonzero modulus `c : O` and a bounded character `Ψ : (O ⧸ Ideal.span {c}) →* ℂ` (`∀ x, ‖Ψ x‖ ≤ 1`)
such that `incompleteIdealT (X^η)` strictly differs from `completedIdealT`. -/
theorem exists_nonreducible_incompleteIdealT_subcubic {a b y₀ η : ℝ} (ha : 0 < a)
    (hy₀_lo : a ≤ y₀) (hy₀_hi : y₀ ≤ b) (hdyad : b < 4 * a) (_hη0 : 0 < η) (hη : η < 1 / 3)
    (W₀ : ℝ → ℂ) (hs : Function.support W₀ ⊆ Icc a b) (hW_cpt : HasCompactSupport W₀)
    (hWy₀ : W₀ y₀ ≠ 0) (X₀ : ℝ) :
    ∃ (X : ℝ) (c : O), max X₀ 1 ≤ X ∧ c ≠ 0 ∧
      ∃ Ψ : (O ⧸ Ideal.span {c}) →* ℂ, (∀ x, ‖Ψ x‖ ≤ 1) ∧
        incompleteIdealT (X ^ η) (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) W₀ X ≠
          completedIdealT (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) W₀ X := by
  have hy₀_pos : 0 < y₀ := lt_of_lt_of_le ha hy₀_lo
  have hexp_pos : 0 < 1 - 3 * η := by linarith
  have htend1 : Tendsto (fun m : ℕ => ((4096 : ℝ) ^ m) / y₀) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4096)).atTop_div_const hy₀_pos
  have htend2 : Tendsto (fun m : ℕ => ((16 : ℝ) ^ (1 - 3 * η)) ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (Real.one_lt_rpow (by norm_num) hexp_pos)
  obtain ⟨m, hm1, hm_cut⟩ := ((htend1.eventually_ge_atTop (max X₀ 1)).and
    (htend2.eventually_ge_atTop (y₀ ^ (-η)))).exists
  set X : ℝ := (4096 : ℝ) ^ m / y₀
  have hX_pos : 0 < X := lt_of_lt_of_le zero_lt_one ((le_max_right X₀ 1).trans hm1)
  have hcut_le : X ^ η ≤ (16 : ℝ) ^ m := by
    have h4096 : ((4096 : ℝ) ^ m) ^ η = ((16 : ℝ) ^ (3 * η)) ^ m := by
      rw [show (4096 : ℝ) = (16 : ℝ) ^ (3 : ℕ) by norm_num, ← pow_mul,
        ← Real.rpow_natCast (16 : ℝ) (3 * m), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast ((16 : ℝ) ^ (3 * η)) m, ← Real.rpow_mul (by norm_num)]
      push_cast
      ring_nf
    have hX_eq : X ^ η = y₀ ^ (-η) * ((16 : ℝ) ^ (3 * η)) ^ m := by
      dsimp [X]
      rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity), h4096,
        Real.inv_rpow hy₀_pos.le, Real.rpow_neg hy₀_pos.le, mul_comm]
    rw [hX_eq]
    calc y₀ ^ (-η) * ((16 : ℝ) ^ (3 * η)) ^ m
        ≤ ((16 : ℝ) ^ (1 - 3 * η)) ^ m * ((16 : ℝ) ^ (3 * η)) ^ m :=
          mul_le_mul_of_nonneg_right hm_cut (by positivity)
      _ = ((16 : ℝ) ^ (1 - 3 * η) * (16 : ℝ) ^ (3 * η)) ^ m := (mul_pow _ _ m).symm
      _ = (16 : ℝ) ^ m := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 16)]
          norm_num
  set M : ℕ := ⌈b * X⌉₊ + 1
  set Cmod : ℕ := ∏ k ∈ Finset.range M, (2 * k + 1)
  have hCmod_pos : 0 < Cmod := Finset.prod_pos fun k _ => by omega
  set c : O := (Cmod : O)
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr hCmod_pos.ne'
  let Ψ : (O ⧸ Ideal.span {c}) →* ℂ :=
    { toFun := fun x => if IsUnit x then 1 else 0
      map_one' := by simp [isUnit_one]
      map_mul' := fun x y => by
        by_cases hx : IsUnit x <;> by_cases hy : IsUnit y <;>
          simp [hx, hy, IsUnit.mul_iff] }
  have hΨ_norm : ∀ x : O ⧸ Ideal.span {c}, ‖Ψ x‖ ≤ 1 := by
    intro x
    by_cases hu : IsUnit x <;> simp [Ψ, hu]
  refine ⟨X, c, hm1, hc, Ψ, hΨ_norm, ?_⟩
  set Ψc : O →* ℂ := Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom
  intro heq
  have htail_zero : directCubeTail (X ^ η) Ψc W₀ X = 0 := by
    have hadd := incompleteIdealT_add_directCubeTail (X ^ η) Ψc W₀ hW_cpt X hX_pos
    linear_combination hadd - heq
  set Jm : Ideal O := cubicTwoIdeal ^ (2 * m)
  have hJm_norm : Ideal.absNorm Jm = 16 ^ m := by
    dsimp [Jm]
    rw [map_pow, cubicTwoIdeal_absNorm, pow_mul]
    norm_num
  have hunique : ∀ I J : Ideal O, (I, J) ≠ (1, Jm) →
      directCubeTailSummand (X ^ η) Ψc W₀ X I J = 0 := by
    intro I J hne
    by_cases hJ_ge : X ^ η ≤ (Ideal.absNorm J : ℝ)
    swap
    · simp [directCubeTailSummand, hJ_ge]
    rw [directCubeTailSummand, if_pos hJ_ge]
    by_contra hnz
    have hsupp_prim := summand_primary_support Ψc W₀ X I J hnz
    have hI0 : I ≠ 0 := primaryIdealGenerator_ne_zero_ideal I hsupp_prim.1.2
    have hJ0 : J ≠ 0 := primaryIdealGenerator_ne_zero_ideal J hsupp_prim.2
    have hW_nz : W₀ ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 / X) ≠ 0 := by
      intro hw
      exact hnz (summand_zero_window Ψc W₀ X I J hw)
    have hratio_mem : (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 / X ∈ Icc a b := hs hW_nz
    have hprod_lo : a * X ≤ (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 :=
      (le_div_iff₀ hX_pos).mp hratio_mem.1
    have hprod_hi : (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 ≤ b * X :=
      (div_le_iff₀ hX_pos).mp hratio_mem.2
    have hNI_ge1 : 1 ≤ Ideal.absNorm I :=
      Nat.one_le_iff_ne_zero.mpr (fun h => hI0 (Ideal.absNorm_eq_zero_iff.mp h))
    have hNJ_ge1 : 1 ≤ Ideal.absNorm J :=
      Nat.one_le_iff_ne_zero.mpr (fun h => hJ0 (Ideal.absNorm_eq_zero_iff.mp h))
    have hNI_le : Ideal.absNorm I ≤ ⌈b * X⌉₊ := by
      have h1 : (Ideal.absNorm I : ℝ) ≤ (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 := by
        have : (1 : ℝ) ≤ (Ideal.absNorm J : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hNJ_ge1)
        nlinarith
      exact_mod_cast (h1.trans hprod_hi).trans (Nat.le_ceil (b * X))
    have hNJ_le : Ideal.absNorm J ≤ ⌈b * X⌉₊ := by
      have h1 : (Ideal.absNorm J : ℝ) ≤ (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 := by
        have hI1 : (1 : ℝ) ≤ Ideal.absNorm I := by exact_mod_cast hNI_ge1
        have hJ1 : (1 : ℝ) ≤ Ideal.absNorm J := by exact_mod_cast hNJ_ge1
        have hJ3 : (Ideal.absNorm J : ℝ) ≤ (Ideal.absNorm J : ℝ) ^ 3 :=
          le_self_pow₀ hJ1 (by norm_num)
        nlinarith
      exact_mod_cast (h1.trans hprod_hi).trans (Nat.le_ceil (b * X))
    have hodd_free : ∀ A : Ideal O, A ≠ 0 → primaryIdealGenerator A ≠ 0 →
        Ideal.absNorm A ≤ ⌈b * X⌉₊ → Ψc (primaryIdealGenerator A) ≠ 0 →
        ∀ d : ℕ, d % 2 = 1 → d ∣ Ideal.absNorm A → d = 1 := by
      intro A hA0 hAgen hNA hΨA d hd_odd hd_dvd
      by_contra hd1
      set k : ℕ := (d - 1) / 2
      have hk_eq : 2 * k + 1 = d := by omega
      have hk_lt : k < M := by
        have hd_le : d ≤ Ideal.absNorm A := Nat.le_of_dvd
          (Nat.pos_of_ne_zero (fun h => hA0 (Ideal.absNorm_eq_zero_iff.mp h))) hd_dvd
        dsimp [M]; omega
      have hd_dvd_Cmod : (d : O) ∣ c := by
        have hd_nat : d ∣ Cmod := by
          rw [← hk_eq]
          exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hk_lt)
        rcases hd_nat with ⟨t, ht⟩
        exact ⟨(t : O), by dsimp [c]; exact_mod_cast ht⟩
      have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {c}) (primaryIdealGenerator A)) := by
        by_contra hnu
        exact hΨA (by simp [Ψc, Ψ, hnu])
      rcases hunit with ⟨⟨u, v, huv, _⟩, hu_eq⟩
      obtain ⟨u₀, rfl⟩ := Ideal.Quotient.mk_surjective u
      obtain ⟨v₀, rfl⟩ := Ideal.Quotient.mk_surjective v
      have huv_mem : u₀ * v₀ - 1 ∈ Ideal.span {c} :=
        Ideal.Quotient.eq.mp (by simpa using huv)
      have hu_sub : u₀ - primaryIdealGenerator A ∈ Ideal.span {c} :=
        Ideal.Quotient.eq.mp hu_eq
      have hgv_mem : primaryIdealGenerator A * v₀ - 1 ∈ Ideal.span {c} := by
        have h1 : u₀ * v₀ - primaryIdealGenerator A * v₀ ∈ Ideal.span {c} := by
          rw [show u₀ * v₀ - primaryIdealGenerator A * v₀ =
            (u₀ - primaryIdealGenerator A) * v₀ by ring]
          exact Ideal.mul_mem_right v₀ _ hu_sub
        simpa using (Ideal.span {c}).sub_mem huv_mem h1
      rcases Ideal.mem_span_singleton.mp hgv_mem with ⟨q, hq⟩
      have hgv_eq : primaryIdealGenerator A * v₀ = 1 + c * q := by linear_combination hq
      have hnorm_natAbs : (Algebra.norm ℤ (primaryIdealGenerator A)).natAbs = Ideal.absNorm A := by
        rw [← Ideal.absNorm_span_singleton, (primaryIdealGenerator_spec A hAgen).1]
      have hd_dvd_normZ : (d : ℤ) ∣ Algebra.norm ℤ (primaryIdealGenerator A) := by
        rw [← Int.dvd_natAbs, hnorm_natAbs]
        exact_mod_cast hd_dvd
      have hd_dvd_gen_conj : (d : O) ∣ primaryIdealGenerator A * conjO (primaryIdealGenerator A) := by
        rw [← norm_int_eq_mul_conjO]
        rcases hd_dvd_normZ with ⟨w, hw⟩
        exact ⟨(w : O), by exact_mod_cast hw⟩
      have hd_dvd_lhs : (d : O) ∣ (primaryIdealGenerator A * v₀) *
          conjO (primaryIdealGenerator A * v₀) := by
        rw [map_mul, show (primaryIdealGenerator A * v₀) *
            (conjO (primaryIdealGenerator A) * conjO v₀) =
            (primaryIdealGenerator A * conjO (primaryIdealGenerator A)) *
              (v₀ * conjO v₀) by ring]
        exact dvd_mul_of_dvd_left hd_dvd_gen_conj _
      have hd_dvd_one : (d : O) ∣ (1 : O) := by
        rw [hgv_eq, map_add, map_one, map_mul] at hd_dvd_lhs
        have hc_conj : conjO c = c := by
          dsimp [c]
          exact map_natCast conjO Cmod
        rw [hc_conj] at hd_dvd_lhs
        have hd_dvd_rem : (d : O) ∣
            c * q + c * conjO q + (c * q) * (c * conjO q) := by
          rw [show c * q + c * conjO q + (c * q) * (c * conjO q) =
            c * (q + conjO q + c * q * conjO q) by ring]
          exact dvd_mul_of_dvd_left hd_dvd_Cmod _
        have hsum : (1 + c * q) * (1 + c * conjO q) =
            1 + (c * q + c * conjO q + (c * q) * (c * conjO q)) := by ring
        rw [hsum] at hd_dvd_lhs
        exact (dvd_add_left hd_dvd_rem).mp hd_dvd_lhs
      have hnorm_unit : Algebra.norm ℤ (d : O) ∣ Algebra.norm ℤ (1 : O) := by
        rcases hd_dvd_one with ⟨w, hw⟩
        exact ⟨Algebra.norm ℤ w, by rw [← map_mul, ← hw]⟩
      have hnorm_d : Algebra.norm ℤ (d : O) = (d : ℤ) ^ 2 := by
        apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → O))
        rw [norm_int_eq_mul_conjO]
        push_cast
        simp [sq]
      rw [hnorm_d, map_one] at hnorm_unit
      have hd_sq_nat : d ^ 2 ∣ 1 := by
        have h := Int.natAbs_dvd_natAbs.mpr hnorm_unit
        simpa [Int.natAbs_pow] using h
      have hd_eq1 : d ^ 2 = 1 := Nat.eq_one_of_dvd_one hd_sq_nat
      have : d = 1 := by nlinarith
      exact hd1 this
    have hΨI_nz : Ψc (primaryIdealGenerator I) ≠ 0 := by
      intro hz
      exact hnz (by simp [CompletedGauss.summand, columnWeight, hz])
    have hΨJ_nz : Ψc (primaryIdealGenerator J) ≠ 0 := by
      intro hz
      have hcw : cubeWeight Ψc J = 0 := by
        change star (angularFactor (primaryIdealGenerator J)) ^ 3 *
          Ψc (primaryIdealGenerator J) ^ 3 / _ = 0
        simp [hz]
      exact hnz (by simp [CompletedGauss.summand, hcw])
    obtain ⟨rI, hI_eq, hNI_pow⟩ :=
      absNorm_power_of_two_is_cubicTwoIdeal_pow hI0 (hodd_free I hI0 hsupp_prim.1.2 hNI_le hΨI_nz)
    obtain ⟨rJ, hJ_eq, hNJ_pow⟩ :=
      absNorm_power_of_two_is_cubicTwoIdeal_pow hJ0 (hodd_free J hJ0 hsupp_prim.2 hNJ_le hΨJ_nz)
    have hrI_le1 : rI ≤ 1 := by
      by_contra hgt
      have h2 : 2 ≤ rI := by omega
      have hdvd : cubicTwoIdeal * cubicTwoIdeal ∣ I := by
        rw [hI_eq]
        rcases Nat.exists_eq_add_of_le h2 with ⟨t, rfl⟩
        rw [pow_add, sq]
        exact dvd_mul_right _ _
      have hu := hsupp_prim.1.1 cubicTwoIdeal hdvd
      exact cubicTwoIdeal_isMaximal.ne_top (Ideal.isUnit_iff.mp hu)
    -- Bound `(Ideal.absNorm I) * (Ideal.absNorm J)^3` strictly between `(1/4)*4096^m` and `4*4096^m`.
    have hlo_strict : (4096 : ℝ) ^ m < 4 * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3) := by
      have ha4 : y₀ < 4 * a := lt_of_le_of_lt hy₀_hi hdyad
      have h1 : (a / y₀) * (4096 : ℝ) ^ m ≤
          (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 := by
        have h : a * ((4096 : ℝ) ^ m / y₀) = (a / y₀) * (4096 : ℝ) ^ m := by ring
        rwa [← h]
      have hpos64 : (0 : ℝ) < (4096 : ℝ) ^ m := by positivity
      have hgt_q : (1 / 4 : ℝ) < a / y₀ := by
        rw [div_lt_div_iff₀ (by norm_num) hy₀_pos]
        linarith
      nlinarith
    have hhi_strict : (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 < 4 * (4096 : ℝ) ^ m := by
      have hb4 : b / y₀ < 4 := by
        rw [div_lt_iff₀ hy₀_pos]
        linarith
      have h1 : (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 ≤
          (b / y₀) * (4096 : ℝ) ^ m := by
        have h : b * ((4096 : ℝ) ^ m / y₀) = (b / y₀) * (4096 : ℝ) ^ m := by ring
        rwa [← h]
      have hpos64 : (0 : ℝ) < (4096 : ℝ) ^ m := by positivity
      nlinarith
    have h64_m : (4096 : ℝ) ^ m = ((64 ^ (2 * m) : ℕ) : ℝ) := by
      push_cast; rw [pow_mul]; norm_num
    have h64_r : ((4 ^ rJ : ℕ) : ℝ) ^ 3 = ((64 ^ rJ : ℕ) : ℝ) := by
      push_cast; rw [← pow_mul, mul_comm rJ 3, pow_mul]; norm_num
    interval_cases rI
    · -- `I = 1`, `N(J)^3 = 64^rJ`, forcing `rJ = 2 * m`.
      have hI1 : I = 1 := by rw [hI_eq, pow_zero]
      rw [hNI_pow, hNJ_pow, pow_zero, Nat.cast_one, one_mul, h64_m, h64_r] at hlo_strict hhi_strict
      have hlo_nat : 64 ^ (2 * m) < 4 * 64 ^ rJ := by exact_mod_cast hlo_strict
      have hhi_nat : 64 ^ rJ < 4 * 64 ^ (2 * m) := by exact_mod_cast hhi_strict
      have hrJ_eq : rJ = 2 * m := by
        by_contra hne_r
        rcases lt_or_gt_of_ne hne_r with hlt | hgt
        · have hle : rJ + 1 ≤ 2 * m := hlt
          have hpow : 64 ^ (rJ + 1) ≤ 64 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) hle
          omega
        · have hle : 2 * m + 1 ≤ rJ := hgt
          have hpow : 64 ^ (2 * m + 1) ≤ 64 ^ rJ := Nat.pow_le_pow_right (by norm_num) hle
          omega
      exact hne (Prod.ext hI1 (by rw [hJ_eq, hrJ_eq]))
    · -- `I = cubicTwoIdeal`, `N(I) * N(J)^3 = 4 * 64^rJ`, impossible!
      rw [hNI_pow, hNJ_pow, pow_one, h64_m, h64_r] at hlo_strict hhi_strict
      have hlo_nat : 64 ^ (2 * m) < 16 * 64 ^ rJ := by
        have h : ((64 ^ (2 * m) : ℕ) : ℝ) < ((16 * 64 ^ rJ : ℕ) : ℝ) := by
          push_cast at hlo_strict ⊢; linarith
        exact_mod_cast h
      have hhi_nat : 4 * 64 ^ rJ < 4 * 64 ^ (2 * m) := by
        have h : ((4 * 64 ^ rJ : ℕ) : ℝ) < ((4 * 64 ^ (2 * m) : ℕ) : ℝ) := by
          push_cast at hhi_strict ⊢; linarith
        exact_mod_cast h
      have hrJ_lt : rJ < 2 * m := by
        by_contra hge
        have hpow : 64 ^ (2 * m) ≤ 64 ^ rJ := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hge)
        omega
      have hle : rJ + 1 ≤ 2 * m := hrJ_lt
      have hpow : 64 ^ (rJ + 1) ≤ 64 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) hle
      omega
  -- Collapse `directCubeTail` to the single nonzero term `(1, Jm)`.
  have htail_eq : directCubeTail (X ^ η) Ψc W₀ X =
      directCubeTailSummand (X ^ η) Ψc W₀ X 1 Jm := by
    unfold directCubeTail
    rw [tsum_eq_single 1]
    · exact tsum_eq_single Jm fun J hJ => hunique 1 J (fun h => hJ (Prod.mk.inj h).2)
    · intro I hI
      have h0 : ∀ J : Ideal O, directCubeTailSummand (X ^ η) Ψc W₀ X I J = 0 :=
        fun J => hunique I J (fun h => hI (Prod.mk.inj h).1)
      simp [h0]
  rw [htail_eq] at htail_zero
  -- Verify `directCubeTailSummand (X ^ η) Ψc W₀ X 1 Jm ≠ 0`.
  have hJm_ge : X ^ η ≤ (Ideal.absNorm Jm : ℝ) := by
    rw [hJm_norm]
    exact_mod_cast hcut_le
  rw [directCubeTailSummand, if_pos hJm_ge] at htail_zero
  -- `Jm = Ideal.span {((4 ^ m : ℕ) : O)}` with primary generator `((4 ^ m : ℕ) : O)`.
  have hJm_span : Jm = Ideal.span {((4 ^ m : ℕ) : O)} := by
    dsimp [Jm, cubicTwoIdeal]
    have hspan_pow : ∀ n : ℕ, (Ideal.span {(-2 : O)} : Ideal O) ^ n =
        Ideal.span {(-2 : O) ^ n} := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, pow_succ, ih, Ideal.span_singleton_mul_span_singleton]
    rw [hspan_pow, pow_mul]
    congr 2
    norm_num
  have h4m_prim : lambda ^ 2 ∣ ((4 ^ m : ℕ) : O) - 1 := by
    have h4m_eq : ((4 ^ m : ℕ) : O) = (-2 : O) ^ (2 * m) := by
      rw [pow_mul]
      norm_num
    rw [h4m_eq]
    have hdvd_neg2 : lambda ^ 2 ∣ (-2 : O) - 1 := neg_two_primary
    have hdvd_pow : ∀ n : ℕ, (-2 : O) - 1 ∣ (-2 : O) ^ n - 1 := fun n => by
      simpa only [one_pow] using sub_dvd_pow_sub_pow (-2 : O) 1 n
    exact hdvd_neg2.trans (hdvd_pow (2 * m))
  have hgen_Jm : primaryIdealGenerator Jm = ((4 ^ m : ℕ) : O) := by
    rw [hJm_span]
    exact primaryIdealGenerator_span _ (Nat.cast_ne_zero.mpr (by positivity)) h4m_prim
  have hCmod_odd : Cmod % 2 = 1 := by
    dsimp [Cmod]
    have hodd_prod : ∀ s : Finset ℕ, (∏ k ∈ s, (2 * k + 1)) % 2 = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          rw [Finset.prod_insert ha, Nat.mul_mod, ih]
          omega
    exact hodd_prod _
  have hcop : Nat.Coprime (4 ^ m) Cmod := by
    have h2 : Nat.Coprime 2 Cmod :=
      Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    simpa [pow_mul] using (h2.pow_left (2 * m))
  have hunit_Jm : IsUnit (Ideal.Quotient.mk (Ideal.span {c}) ((4 ^ m : ℕ) : O)) := by
    have hbez := Nat.gcd_eq_gcd_ab (4 ^ m) Cmod
    rw [hcop.gcd_eq_one] at hbez
    -- Cast Bézout identity `1 = 4^m * a + Cmod * b` to `O / (c)`.
    have hbez_O : ((4 ^ m : ℕ) : O) * (Nat.gcdA (4 ^ m) Cmod : O) +
        c * (Nat.gcdB (4 ^ m) Cmod : O) = 1 := by
      dsimp [c]
      exact_mod_cast hbez.symm
    have hmk : Ideal.Quotient.mk (Ideal.span {c}) ((4 ^ m : ℕ) : O) *
        Ideal.Quotient.mk (Ideal.span {c}) (Nat.gcdA (4 ^ m) Cmod : O) = 1 := by
      rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk (Ideal.span {c})), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact ⟨-(Nat.gcdB (4 ^ m) Cmod : O), by linear_combination hbez_O⟩
    exact IsUnit.of_mul_eq_one _ hmk
  have hΨ_Jm : Ψc (primaryIdealGenerator Jm) = 1 := by
    rw [hgen_Jm]
    exact if_pos hunit_Jm
  have hcw1 : columnWeight Ψc 1 / (Real.sqrt (Ideal.absNorm (1 : Ideal O) : ℝ) : ℂ) ≠ 0 := by
    have hsq1 : Squarefree (1 : Ideal O) := squarefree_one
    have hgen1 : primaryIdealGenerator (1 : Ideal O) ≠ 0 := by
      rw [primaryIdealGenerator_one]; exact one_ne_zero
    rw [columnWeight_div_sqrt Ψc 1 hsq1 hgen1, primaryIdealGenerator_one,
      normalizedCubicUnitGauss_one, map_one, map_one]
    norm_num
  have hcube_Jm : cubeWeight Ψc Jm ≠ 0 := by
    change star (angularFactor (primaryIdealGenerator Jm)) ^ 3 *
      Ψc (primaryIdealGenerator Jm) ^ 3 / (Ideal.absNorm Jm : ℂ) ≠ 0
    rw [hΨ_Jm]
    have hgen_nz : primaryIdealGenerator Jm ≠ 0 := by
      rw [hgen_Jm]; exact Nat.cast_ne_zero.mpr (by positivity)
    have hang_nz : star (angularFactor (primaryIdealGenerator Jm)) ^ 3 ≠ 0 :=
      pow_ne_zero 3 (star_ne_zero.mpr (by
        intro hz
        have := norm_angularFactor _ hgen_nz
        rw [hz, norm_zero] at this
        norm_num at this))
    have hnorm_nz : (Ideal.absNorm Jm : ℂ) ≠ 0 := by
      rw [hJm_norm]
      exact Nat.cast_ne_zero.mpr (by positivity)
    exact div_ne_zero (mul_ne_zero hang_nz (by norm_num)) hnorm_nz
  have hratio_eq : (Ideal.absNorm (1 : Ideal O) : ℝ) * (Ideal.absNorm Jm : ℝ) ^ 3 / X = y₀ := by
    rw [map_one Ideal.absNorm, hJm_norm]
    dsimp [X]
    push_cast
    rw [one_mul, ← pow_mul, show (16 : ℝ) ^ (m * 3) = (4096 : ℝ) ^ m by
      rw [mul_comm, pow_mul]; norm_num]
    field_simp [hy₀_pos.ne']
  have hvstar_nz : Vstar W₀ ((Ideal.absNorm (1 : Ideal O) : ℝ) * (Ideal.absNorm Jm : ℝ) ^ 3 / X) ≠ 0 := by
    rw [hratio_eq, Vstar]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy₀_pos).ne') hWy₀
  exact mul_ne_zero (mul_ne_zero hcw1 hcube_Jm) hvstar_nz htail_zero

/-! ### 4. Milestone 1: Uniform Defect Bounds and Sub-Cubic Power Saving -/

/-- **Uniform direct cube-tail bound on compact complex parameter boxes.** -/
theorem directCubeTail_uniform_box_bound (W₀ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : Function.support W₀ ⊆ Icc a b) (hW : ContDiff ℝ ∞ W₀) (σ₁ σ₂ T : ℝ) :
    ∃ C_dir : ℝ, 0 < C_dir ∧
      ∀ (Ψ : O →* ℂ), (∀ x, ‖Ψ x‖ ≤ 1) →
      ∀ (X Y₀ : ℝ), 0 < X → 1 ≤ Y₀ →
      ∀ s ∈ complexParameterBox σ₁ σ₂ T,
        ‖directCubeTail Y₀ Ψ (complexTwistedWindow W₀ s) X‖ ≤ C_dir * X * Y₀ ^ (-(3 : ℝ)) := by
  obtain ⟨M, hM, hsup⟩ := vstar_complexTwistedWindow_uniform_sup_bound W₀ ha hab hs hW
    (isCompact_complexParameterBox σ₁ σ₂ T)
  have _hb_pos : 0 < b := lt_of_lt_of_le ha hab
  set C_dir : ℝ := 65536 * b * M
  refine ⟨C_dir, by dsimp [C_dir]; positivity, fun Ψ hΨ X Y₀ hX hY₀ s hs_box => ?_⟩
  set Ws : ℝ → ℂ := complexTwistedWindow W₀ s
  have hWs_supp : Function.support Ws ⊆ Icc a b := complexTwistedWindow_support W₀ hs s
  have hWs_cpt : HasCompactSupport Ws :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hWs_supp
  by_cases hhigh : b * X < Y₀ ^ 3
  · -- Every summand with `Y₀ ≤ N(J)` lies outside the window support `[a, b]`.
    have hzero : ∀ I J : Ideal O, directCubeTailSummand Y₀ Ψ Ws X I J = 0 := by
      intro I J
      unfold directCubeTailSummand
      split_ifs with hJ_ge
      · by_cases hI0 : I = 0
        · rw [hI0, CompletedGauss.summand_zero_left]
        · by_cases hJ0 : J = 0
          · rw [hJ0, CompletedGauss.summand_zero_right]
          · apply summand_zero_window
            by_contra hw
            have hmem := hWs_supp hw
            have hprod_le : (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 ≤ b * X :=
              (div_le_iff₀ hX).mp hmem.2
            have hNI1 : (1 : ℝ) ≤ Ideal.absNorm I := by
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hI0 (Ideal.absNorm_eq_zero_iff.mp h))
            have hJ3 : Y₀ ^ 3 ≤ (Ideal.absNorm J : ℝ) ^ 3 :=
              pow_le_pow_left₀ (by linarith) hJ_ge 3
            have hYJ : Y₀ ^ 3 ≤ (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 := by
              calc Y₀ ^ 3 = 1 * Y₀ ^ 3 := (one_mul _).symm
                _ ≤ (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 :=
                    mul_le_mul hNI1 hJ3 (by positivity) (by positivity)
            linarith
      · rfl
    have htail0 : directCubeTail Y₀ Ψ Ws X = 0 := by simp [directCubeTail, hzero]
    rw [htail0, norm_zero]
    exact mul_nonneg (mul_nonneg (by dsimp [C_dir]; positivity) hX.le) (by positivity)
  · have hhigh' : Y₀ ^ 3 ≤ b * X := not_lt.mp hhigh
    have _hbX_ge1 : 1 ≤ b * X := (one_le_pow₀ hY₀).trans hhigh'
    -- Finite dyadic shells `2^k * Y₀ ≤ N(J) < 2^(k+1) * Y₀` for `k < L := ⌈b * X⌉₊ + 1`.
    set L : ℕ := ⌈b * X⌉₊ + 1
    set finIdeals : Finset (Ideal O) :=
      (Ideal.finite_setOf_absNorm_le (S := O) ⌈b * X⌉₊).toFinset
    -- Inner bound for any fixed `J` with `1 ≤ N(J)`:
    have hinner_bound : ∀ J : Ideal O, Y₀ ≤ (Ideal.absNorm J : ℝ) →
        ‖∑' I : Ideal O, directCubeTailSummand Y₀ Ψ Ws X I J‖ ≤
          128 * b * M * X / (Ideal.absNorm J : ℝ) ^ 4 := by
      intro J hJ_ge
      have hNJ_ge1 : 1 ≤ (Ideal.absNorm J : ℝ) := hY₀.trans hJ_ge
      have hNJ_pos : 0 < (Ideal.absNorm J : ℝ) := lt_of_lt_of_le zero_lt_one hNJ_ge1
      by_cases hH : (b * X) / (Ideal.absNorm J : ℝ) ^ 3 < 1
      · have hI_zero : ∀ I : Ideal O, directCubeTailSummand Y₀ Ψ Ws X I J = 0 := by
          intro I
          unfold directCubeTailSummand
          rw [if_pos hJ_ge]
          by_cases hI0 : I = 0
          · rw [hI0, CompletedGauss.summand_zero_left]
          · apply summand_zero_window
            by_contra hw
            have hprod_le : (Ideal.absNorm I : ℝ) ≤ (b * X) / (Ideal.absNorm J : ℝ) ^ 3 := by
              rw [le_div_iff₀ (pow_pos hNJ_pos 3)]
              exact (div_le_iff₀ hX).mp (hWs_supp hw).2
            have hNI1 : (1 : ℝ) ≤ Ideal.absNorm I := by
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hI0 (Ideal.absNorm_eq_zero_iff.mp h))
            linarith
        simp only [hI_zero, tsum_zero, norm_zero]
        positivity
      · have hH' : 1 ≤ (b * X) / (Ideal.absNorm J : ℝ) ^ 3 := not_lt.mp hH
        set S_I : Finset (Ideal O) := finIdeals.filter fun I =>
          I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ (b * X) / (Ideal.absNorm J : ℝ) ^ 3
        have hsupp_I : ∀ I : Ideal O, I ∉ S_I → directCubeTailSummand Y₀ Ψ Ws X I J = 0 := by
          intro I hnot
          unfold directCubeTailSummand
          rw [if_pos hJ_ge]
          by_cases hI0 : I = 0
          · rw [hI0, CompletedGauss.summand_zero_left]
          · apply summand_zero_window
            by_contra hw
            have hprod_le : (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 ≤ b * X :=
              (div_le_iff₀ hX).mp (hWs_supp hw).2
            have hNI_div : (Ideal.absNorm I : ℝ) ≤ (b * X) / (Ideal.absNorm J : ℝ) ^ 3 :=
              (le_div_iff₀ (pow_pos hNJ_pos 3)).mpr hprod_le
            have hNI_bX : Ideal.absNorm I ≤ ⌈b * X⌉₊ := by
              have h1 : (Ideal.absNorm I : ℝ) ≤ b * X := by
                have : (1 : ℝ) ≤ (Ideal.absNorm J : ℝ) ^ 3 := one_le_pow₀ hNJ_ge1
                nlinarith
              exact_mod_cast h1.trans (Nat.le_ceil (b * X))
            apply hnot
            simp only [S_I, Finset.mem_filter, finIdeals, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
            exact ⟨hNI_bX, hI0, hNI_div⟩
        rw [tsum_eq_sum hsupp_I]
        have hterm_I : ∀ I ∈ S_I, ‖directCubeTailSummand Y₀ Ψ Ws X I J‖ ≤
            M / (Ideal.absNorm J : ℝ) := by
          intro I _
          unfold directCubeTailSummand
          rw [if_pos hJ_ge]
          unfold CompletedGauss.summand
          rw [norm_mul, norm_mul]
          have hcol := columnWeight_div_sqrt_norm_le_one Ψ hΨ I
          have hcube : ‖cubeWeight Ψ J‖ ≤ (Ideal.absNorm J : ℝ)⁻¹ := by
            change ‖star (angularFactor (primaryIdealGenerator J)) ^ 3 *
              Ψ (primaryIdealGenerator J) ^ 3 / (Ideal.absNorm J : ℂ)‖ ≤ _
            rw [norm_div, norm_mul, norm_pow, norm_star, norm_pow, Complex.norm_natCast,
              ← one_div]
            refine div_le_div_of_nonneg_right ?_ hNJ_pos.le
            calc ‖angularFactor (primaryIdealGenerator J)‖ ^ 3 *
                    ‖Ψ (primaryIdealGenerator J)‖ ^ 3
                ≤ 1 * 1 := mul_le_mul
                  (pow_le_one₀ (norm_nonneg _) (norm_angularFactor_le_one _))
                  (pow_le_one₀ (norm_nonneg _) (hΨ _)) (by positivity) zero_le_one
              _ = 1 := one_mul 1
          have hv := hsup s hs_box ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 / X)
          calc ‖columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ)‖ *
                ‖cubeWeight Ψ J‖ *
                ‖Vstar Ws ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 / X)‖
              ≤ 1 * (Ideal.absNorm J : ℝ)⁻¹ * M :=
                mul_le_mul (mul_le_mul hcol hcube (norm_nonneg _) zero_le_one) hv
                  (norm_nonneg _) (by positivity)
            _ = M / (Ideal.absNorm J : ℝ) := by ring
        have hcard_I : (S_I.card : ℝ) ≤ 128 * ((b * X) / (Ideal.absNorm J : ℝ) ^ 3) :=
          finite_ideal_count_real S_I _ hH'
            (fun I hI => (Finset.mem_filter.mp hI).2.1)
            (fun I hI => (Finset.mem_filter.mp hI).2.2)
        calc ‖∑ I ∈ S_I, directCubeTailSummand Y₀ Ψ Ws X I J‖
            ≤ ∑ I ∈ S_I, ‖directCubeTailSummand Y₀ Ψ Ws X I J‖ := norm_sum_le _ _
          _ ≤ ∑ _I ∈ S_I, (M / (Ideal.absNorm J : ℝ)) := Finset.sum_le_sum hterm_I
          _ = (S_I.card : ℝ) * (M / (Ideal.absNorm J : ℝ)) := by simp
          _ ≤ (128 * ((b * X) / (Ideal.absNorm J : ℝ) ^ 3)) * (M / (Ideal.absNorm J : ℝ)) :=
              mul_le_mul_of_nonneg_right hcard_I (by positivity)
          _ = 128 * b * M * X / (Ideal.absNorm J : ℝ) ^ 4 := by ring
    -- Swap `I` and `J` in `directCubeTail`, then cover `J` by dyadic shells `k ∈ range L`.
    have hpair : Summable (fun q : Ideal O × Ideal O => directCubeTailSummand Y₀ Ψ Ws X q.1 q.2) :=
      Summable.of_norm_bounded (completedIdealT_summable Ψ Ws hWs_cpt X hX).norm fun q => by
        unfold directCubeTailSummand; split_ifs <;> simp
    have hswap_tail : directCubeTail Y₀ Ψ Ws X =
        ∑' J : Ideal O, ∑' I : Ideal O, directCubeTailSummand Y₀ Ψ Ws X I J := by
      unfold directCubeTail
      exact hpair.tsum_comm.symm
    rw [hswap_tail]
    set S_J : Finset (Ideal O) := finIdeals.filter fun J =>
      J ≠ 0 ∧ Y₀ ≤ (Ideal.absNorm J : ℝ)
    have hsupp_J : ∀ J : Ideal O, J ∉ S_J →
        (∑' I : Ideal O, directCubeTailSummand Y₀ Ψ Ws X I J) = 0 := by
      intro J hnot
      have hI0 : ∀ I : Ideal O, directCubeTailSummand Y₀ Ψ Ws X I J = 0 := by
        intro I
        by_cases hJ_ge : Y₀ ≤ (Ideal.absNorm J : ℝ)
        · unfold directCubeTailSummand
          rw [if_pos hJ_ge]
          by_cases hI_z : I = 0
          · rw [hI_z, CompletedGauss.summand_zero_left]
          · by_cases hJ_z : J = 0
            · rw [hJ_z, CompletedGauss.summand_zero_right]
            · apply summand_zero_window
              by_contra hw
              have hprod_le : (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 ≤ b * X :=
                (div_le_iff₀ hX).mp (hWs_supp hw).2
              have hNI1 : (1 : ℝ) ≤ Ideal.absNorm I := by
                exact_mod_cast Nat.one_le_iff_ne_zero.mpr
                  (fun h => hI_z (Ideal.absNorm_eq_zero_iff.mp h))
              have hNJ1 : (1 : ℝ) ≤ Ideal.absNorm J := hY₀.trans hJ_ge
              have hJ3 : (Ideal.absNorm J : ℝ) ≤ (Ideal.absNorm J : ℝ) ^ 3 :=
                le_self_pow₀ hNJ1 (by norm_num)
              have hNJ_bX : Ideal.absNorm J ≤ ⌈b * X⌉₊ := by
                have hle_bX : (Ideal.absNorm J : ℝ) ≤ b * X := by nlinarith
                exact_mod_cast hle_bX.trans (Nat.le_ceil (b * X))
              apply hnot
              simp only [S_J, Finset.mem_filter, finIdeals, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
              exact ⟨hNJ_bX, hJ_z, hJ_ge⟩
        · simp [directCubeTailSummand, hJ_ge]
      simp [hI0]
    rw [tsum_eq_sum hsupp_J]
    set shell : ℕ → Finset (Ideal O) := fun k =>
      S_J.filter fun J => (2 : ℝ) ^ k * Y₀ ≤ (Ideal.absNorm J : ℝ) ∧
        (Ideal.absNorm J : ℝ) < (2 : ℝ) ^ (k + 1) * Y₀
    have hcover : S_J ⊆ (Finset.range L).biUnion shell := by
      intro J hJ
      have hJ_mem := Finset.mem_filter.mp hJ
      have hNJ_le : (Ideal.absNorm J : ℝ) ≤ (⌈b * X⌉₊ : ℝ) := by
        have h1 : Ideal.absNorm J ≤ ⌈b * X⌉₊ := by
          simpa [finIdeals] using hJ_mem.1
        exact_mod_cast h1
      have htop : (Ideal.absNorm J : ℝ) < (2 : ℝ) ^ L * Y₀ := by
        have hpow_lt : L < 2 ^ L := Nat.lt_pow_self one_lt_two
        have hpow_r : (L : ℝ) < (2 : ℝ) ^ L := by exact_mod_cast hpow_lt
        have hL_gt : (⌈b * X⌉₊ : ℝ) < L := by dsimp [L]; push_cast; linarith
        nlinarith [hY₀]
      -- Pick largest `k < L` with `2^k * Y₀ ≤ N(J)`.
      let P : ℕ → Prop := fun k => k < L ∧ (2 : ℝ) ^ k * Y₀ ≤ (Ideal.absNorm J : ℝ)
      set k₀ := Nat.findGreatest P L
      have hk₀_spec : P k₀ := Nat.findGreatest_spec (P := P) (by omega : 0 ≤ L) ⟨by dsimp [L]; omega, by simpa using hJ_mem.2.2⟩
      have hk₀_next : (Ideal.absNorm J : ℝ) < (2 : ℝ) ^ (k₀ + 1) * Y₀ := by
        by_contra hge_not
        have hge : (2 : ℝ) ^ (k₀ + 1) * Y₀ ≤ (Ideal.absNorm J : ℝ) := not_lt.mp hge_not
        by_cases hk1_lt : k₀ + 1 < L
        · have hle_k := Nat.le_findGreatest hk1_lt.le (show P (k₀ + 1) from ⟨hk1_lt, hge⟩)
          omega
        · have hk1_eq : k₀ + 1 = L := by omega
          rw [hk1_eq] at hge
          linarith
      exact Finset.mem_biUnion.mpr ⟨k₀, Finset.mem_range.mpr hk₀_spec.1,
        Finset.mem_filter.mpr ⟨hJ, hk₀_spec.2, hk₀_next⟩⟩
    have hdisj : Set.PairwiseDisjoint (↑(Finset.range L) : Set ℕ) shell := by
      intro k₁ _ k₂ _ hne
      refine Finset.disjoint_left.mpr fun J hJ₁ hJ₂ => ?_
      have h1 := (Finset.mem_filter.mp hJ₁).2
      have h2 := (Finset.mem_filter.mp hJ₂).2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hpow : (2 : ℝ) ^ (k₁ + 1) ≤ (2 : ℝ) ^ k₂ :=
          pow_le_pow_right₀ (by norm_num) hlt
        nlinarith [hY₀]
      · have hpow : (2 : ℝ) ^ (k₂ + 1) ≤ (2 : ℝ) ^ k₁ :=
          pow_le_pow_right₀ (by norm_num) hgt
        nlinarith [hY₀]
    have hshell_bound : ∀ k ∈ Finset.range L,
        ∑ J ∈ shell k, ‖∑' I : Ideal O, directCubeTailSummand Y₀ Ψ Ws X I J‖ ≤
          (32768 * b * M * X * Y₀ ^ (-(3 : ℝ))) * ((1 / 8 : ℝ) ^ k) := by
      intro k _
      have hcard_k : ((shell k).card : ℝ) ≤ 128 * ((2 : ℝ) ^ (k + 1) * Y₀) := by
        refine finite_ideal_count_real (shell k) ((2 : ℝ) ^ (k + 1) * Y₀) ?_ ?_ ?_
        · have : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
          nlinarith
        · intro J hJ
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).2.1
        · intro J hJ
          exact (Finset.mem_filter.mp hJ).2.2.le
      have hterm_k : ∀ J ∈ shell k,
          ‖∑' I : Ideal O, directCubeTailSummand Y₀ Ψ Ws X I J‖ ≤
            128 * b * M * X / ((2 : ℝ) ^ k * Y₀) ^ 4 := by
        intro J hJ
        have hJf := Finset.mem_filter.mp hJ
        have hJ_ge : Y₀ ≤ (Ideal.absNorm J : ℝ) := (Finset.mem_filter.mp hJf.1).2.2
        have hlo_k : (2 : ℝ) ^ k * Y₀ ≤ (Ideal.absNorm J : ℝ) := hJf.2.1
        refine (hinner_bound J hJ_ge).trans ?_
        exact div_le_div_of_nonneg_left (by positivity)
          (pow_pos (by positivity) 4) (pow_le_pow_left₀ (by positivity) hlo_k 4)
      calc ∑ J ∈ shell k, ‖∑' I : Ideal O, directCubeTailSummand Y₀ Ψ Ws X I J‖
          ≤ ∑ _J ∈ shell k, (128 * b * M * X / ((2 : ℝ) ^ k * Y₀) ^ 4) :=
            Finset.sum_le_sum hterm_k
        _ = ((shell k).card : ℝ) * (128 * b * M * X / ((2 : ℝ) ^ k * Y₀) ^ 4) := by simp
        _ ≤ (128 * ((2 : ℝ) ^ (k + 1) * Y₀)) *
              (128 * b * M * X / ((2 : ℝ) ^ k * Y₀) ^ 4) :=
            mul_le_mul_of_nonneg_right hcard_k (by positivity)
        _ = (32768 * b * M * X * Y₀ ^ (-(3 : ℝ))) * ((1 / 8 : ℝ) ^ k) := by
            rw [Real.rpow_neg (by linarith : 0 ≤ Y₀), Real.rpow_ofNat, pow_succ, mul_pow]
            have h2k_ne : ((2 : ℝ) ^ k) ≠ 0 := pow_ne_zero k (by norm_num)
            have hY0_ne : Y₀ ≠ 0 := by linarith
            rw [div_pow, one_pow, show (8 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 3 by
              rw [← pow_mul, mul_comm, pow_mul]; norm_num]
            field_simp [h2k_ne, hY0_ne]
            ring
    have hgeom : ∑ k ∈ Finset.range L, ((1 / 8 : ℝ) ^ k) ≤ 2 := by
      have hsum_eq := geom_sum_eq (by norm_num : (1 / 8 : ℝ) ≠ 1) L
      have hpos_pow : 0 ≤ (1 / 8 : ℝ) ^ L := by positivity
      have hsimp : ((1 / 8 : ℝ) ^ L - 1) / (1 / 8 - 1) = (8 - 8 * (1 / 8 : ℝ) ^ L) / 7 := by ring
      linarith
    calc ‖∑ J ∈ S_J, ∑' I : Ideal O, directCubeTailSummand Y₀ Ψ Ws X I J‖
        ≤ ∑ J ∈ S_J, ‖∑' I : Ideal O, directCubeTailSummand Y₀ Ψ Ws X I J‖ := norm_sum_le _ _
      _ ≤ ∑ J ∈ (Finset.range L).biUnion shell,
            ‖∑' I : Ideal O, directCubeTailSummand Y₀ Ψ Ws X I J‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover (fun _ _ _ => norm_nonneg _)
      _ = ∑ k ∈ Finset.range L, ∑ J ∈ shell k,
            ‖∑' I : Ideal O, directCubeTailSummand Y₀ Ψ Ws X I J‖ :=
          Finset.sum_biUnion hdisj
      _ ≤ ∑ k ∈ Finset.range L,
            (32768 * b * M * X * Y₀ ^ (-(3 : ℝ))) * ((1 / 8 : ℝ) ^ k) :=
          Finset.sum_le_sum hshell_bound
      _ = (32768 * b * M * X * Y₀ ^ (-(3 : ℝ))) *
            ∑ k ∈ Finset.range L, ((1 / 8 : ℝ) ^ k) := (Finset.mul_sum _ _ _).symm
      _ ≤ (32768 * b * M * X * Y₀ ^ (-(3 : ℝ))) * 2 :=
          mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = C_dir * X * Y₀ ^ (-(3 : ℝ)) := by dsimp [C_dir]; ring

/-- **Uniform reflected dual cube-tail bound on compact complex parameter boxes.** -/
theorem dualCubeTail_uniform_box_bound (W₀ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : Function.support W₀ ⊆ Icc a b) (hW : ContDiff ℝ ∞ W₀) (σ₁ σ₂ T : ℝ) (N : ℕ) :
    ∃ C_dual : ℝ, 0 < C_dual ∧
      ∀ (c : O) (hc : c ≠ 0) [Fintype (O ⧸ Ideal.span {9 * c})]
        (Ψ : (O ⧸ Ideal.span {c}) →* ℂ), (∀ x, ‖Ψ x‖ ≤ 1) →
      ∀ (X Y₀' : ℝ), 0 < X → 1 ≤ Y₀' →
      ∀ s ∈ complexParameterBox σ₁ σ₂ T,
        ‖dualCubeTail Y₀' c hc Ψ
            (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc))
            (complexTwistedWindow W₀ s) X‖ ≤
          C_dual * (Fintype.card (O ⧸ Ideal.span {9 * c}) : ℝ) *
            (sourceReflectionScale * X / ‖ringComplex (9 * c)‖ ^ 4) ^ (-(2 : ℝ)) *
            ((sourceReflectionScale * X / ‖ringComplex (9 * c)‖ ^ 4) * Y₀' ^ 3) ^ (-(N : ℝ)) := by
  obtain ⟨B, hB, hker⟩ := paperKernel_complexTwistedWindow_uniform_bound W₀ ha hab hs hW
    (isCompact_complexParameterBox σ₁ σ₂ T) (N + 2)
  set S_mass : ℝ := ∑ j : Fin 3, sourceCuspRadialMass j
  have hS_mass : 0 ≤ S_mass := Finset.sum_nonneg fun j _ => sourceCuspRadialMass_nonneg j
  set C_dual : ℝ := ‖thetaDerivativeScalar⁻¹‖ * (9 * B * (S_mass + 1))
  have hC_dual : 0 < C_dual :=
    mul_pos (norm_pos_iff.mpr (inv_ne_zero thetaDerivativeScalar_ne_zero)) (by positivity)
  refine ⟨C_dual, hC_dual, fun c hc _ Ψ hΨ X Y₀' hX hY₀' s hs_box => ?_⟩
  set Ws : ℝ → ℂ := complexTwistedWindow W₀ s
  have hWs_supp : Function.support Ws ⊆ Icc a b := complexTwistedWindow_support W₀ hs s
  have hWs_diff : ContDiff ℝ ∞ Ws := complexTwistedWindow_contDiff W₀ ha hs hW s
  set hc9 : 9 * c ≠ 0 := mul_ne_zero (by norm_num) hc
  set sc : ℝ := sourceReflectionScale * X / ‖ringComplex (9 * c)‖ ^ 4
  have hsc_pos : 0 < sc := div_pos (mul_pos sourceReflectionScale_pos hX)
    (pow_pos (norm_pos_iff.mpr (ringComplex_ne_zero hc9)) 4)
  -- Bound each cusp `i : O ⧸ Ideal.span {9 * c}`.
  have hcusp : ∀ i : O ⧸ Ideal.span {9 * c},
      ‖∑' p : ThetaFullIndex,
          dualCubeTailSummand Y₀' (finiteTwistCusp (9 * c) hc9 i) Ws X p‖ ≤
        (B * (S_mass + 1)) * sc ^ (-(2 : ℝ)) * (sc * Y₀' ^ 3) ^ (-(N : ℝ)) := by
    intro i
    set d := finiteTwistCusp (9 * c) hc9 i
    have hd_pos : 0 < d.smoothingScale X := d.smoothingScale_pos X hX
    have hsc_le_d : sc ≤ d.smoothingScale X :=
      d.smoothingScale_lower (-3 * Quotient.out i) (9 * c) hc9
        (rationalSourceCusp_point _ _ hc9) X hX
    have hfull_sum : Summable (fun p : ThetaFullIndex =>
        ‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p) *
          paperKernel (Vstar Ws) (d.smoothingScale X *
            sourceCuspRadialLength (thetaFullFrequency p))‖) :=
      sourceCusp_full_kernel_norm_summable d.index d.dualPoint (Vstar Ws) a b ha
        (Vstar_support Ws a b hWs_supp) (Vstar_contDiff Ws a b ha hWs_supp hWs_diff)
        (d.smoothingScale X) hd_pos
    have htail_norm_sum : Summable (fun p : ThetaFullIndex =>
        ‖dualCubeTailSummand Y₀' d Ws X p‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => by
        unfold dualCubeTailSummand
        split_ifs
        · simp only [thetaFullFrequency_radialLength]; exact le_rfl
        · rw [norm_zero]; exact norm_nonneg _) hfull_sum
    have hmass_sum : Summable (fun h : O =>
        ‖sourceCuspRadialCoefficient d.index d.dualPoint h‖ *
          sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) := by
      simpa only [neg_div] using sourceCuspRadialCoefficient_weighted_summable d.index d.dualPoint
    have hmass_p : Summable (fun p : ThetaFullIndex =>
        ‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)‖ *
          sourceCuspRadialLength (thetaFullFrequency p) ^ (-(3 / 2 : ℝ))) :=
      hmass_sum.comp_injective thetaFullFrequency_injective
    have hcoef_nonneg : 0 ≤ B * sc ^ (-(2 : ℝ)) * (sc * Y₀' ^ 3) ^ (-(N : ℝ)) :=
      mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg hsc_pos.le _))
        (Real.rpow_nonneg (mul_pos hsc_pos (pow_pos (by linarith) 3)).le _)
    have hpt_le : ∀ p : ThetaFullIndex,
        ‖dualCubeTailSummand Y₀' d Ws X p‖ ≤
          (B * sc ^ (-(2 : ℝ)) * (sc * Y₀' ^ 3) ^ (-(N : ℝ))) *
            (‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)‖ *
              sourceCuspRadialLength (thetaFullFrequency p) ^ (-(3 / 2 : ℝ))) := by
      intro p
      unfold dualCubeTailSummand
      split_ifs with hp_ge
      · set L_p : ℝ := sourceCuspRadialLength (thetaFullFrequency p)
        have hLp_eq : ‖ringComplex lambda‖ ^ (2 * p.2.1) * completedMellinLength p.2.2 = L_p :=
          (thetaFullFrequency_radialLength p).symm
        rw [hLp_eq, norm_mul]
        have hLp_ge1 : 1 ≤ L_p := sourceCuspRadialLength_one_le _
        have hLp_pos : 0 < L_p := sourceCuspRadialLength_pos _
        -- `L_p ≥ Y₀'^3` when `Y₀' ≤ N(J')`.
        have hLp_ge_Y : Y₀' ^ 3 ≤ L_p := by
          rw [← hLp_eq, completedMellinLength_eq]
          have hlam_ge1 : (1 : ℝ) ≤ ‖ringComplex lambda‖ ^ (2 * p.2.1) := by
            have hlam_norm : (1 : ℝ) ≤ ‖ringComplex lambda‖ ^ 2 := by
              have h := ringComplex_norm_sq_eq_absNorm_span lambda
              have hne : (Ideal.span {lambda} : Ideal O) ≠ 0 :=
                Ideal.span_singleton_eq_bot.not.mpr residue_lambda_prime.1
              have h1 : 1 ≤ Ideal.absNorm (Ideal.span {lambda}) :=
                Nat.one_le_iff_ne_zero.mpr (fun h0 => hne (Ideal.absNorm_eq_zero_iff.mp h0))
              rw [h]
              exact_mod_cast h1
            rw [pow_mul]
            exact one_le_pow₀ hlam_norm
          have hNI_ge1 : (1 : ℝ) ≤ Ideal.absNorm p.2.2.1.val := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h0 =>
              (primaryIdealGenerator_ne_zero_ideal _ p.2.2.1.property.2)
                (Ideal.absNorm_eq_zero_iff.mp h0))
          have hJ3 : Y₀' ^ 3 ≤ (Ideal.absNorm p.2.2.2.val : ℝ) ^ 3 :=
            pow_le_pow_left₀ (by linarith) hp_ge 3
          calc Y₀' ^ 3 = 1 * (1 * Y₀' ^ 3) := by ring
            _ ≤ ‖ringComplex lambda‖ ^ (2 * p.2.1) *
                  ((Ideal.absNorm p.2.2.1.val : ℝ) * (Ideal.absNorm p.2.2.2.val : ℝ) ^ 3) :=
                mul_le_mul hlam_ge1
                  (mul_le_mul hNI_ge1 hJ3 (by positivity) (by positivity))
                  (by positivity) (by positivity)
        have hker_p := hker s hs_box (d.smoothingScale X * L_p) (mul_pos hd_pos hLp_pos)
        -- Factor `(d.smoothingScale X * L_p)^(-(N + 2))`.
        have hsplit_pow : (d.smoothingScale X * L_p) ^ (-((N + 2 : ℕ) : ℝ)) ≤
            sc ^ (-(2 : ℝ)) * (sc * Y₀' ^ 3) ^ (-(N : ℝ)) * L_p ^ (-(3 / 2 : ℝ)) := by
          have hexp_eq : (d.smoothingScale X * L_p) ^ (-((N + 2 : ℕ) : ℝ)) =
              (d.smoothingScale X) ^ (-(2 : ℝ)) *
                (d.smoothingScale X * L_p) ^ (-(N : ℝ)) * L_p ^ (-(2 : ℝ)) := by
            rw [Real.mul_rpow hd_pos.le hLp_pos.le, Real.mul_rpow hd_pos.le hLp_pos.le]
            have hd_add : d.smoothingScale X ^ (-((N + 2 : ℕ) : ℝ)) =
                d.smoothingScale X ^ (-(2 : ℝ)) * d.smoothingScale X ^ (-(N : ℝ)) := by
              rw [← Real.rpow_add hd_pos]; push_cast; ring_nf
            have hL_add : L_p ^ (-((N + 2 : ℕ) : ℝ)) =
                L_p ^ (-(N : ℝ)) * L_p ^ (-(2 : ℝ)) := by
              rw [← Real.rpow_add hLp_pos]; push_cast; ring_nf
            rw [hd_add, hL_add]
            ring
          rw [hexp_eq]
          have h1 : d.smoothingScale X ^ (-(2 : ℝ)) ≤ sc ^ (-(2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hsc_pos hsc_le_d (by norm_num)
          have h2 : (d.smoothingScale X * L_p) ^ (-(N : ℝ)) ≤
              (sc * Y₀' ^ 3) ^ (-(N : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (mul_pos hsc_pos (pow_pos (by linarith) 3))
              (mul_le_mul hsc_le_d hLp_ge_Y (pow_nonneg (by linarith) 3) hd_pos.le)
              (neg_nonpos.mpr (Nat.cast_nonneg N))
          have h3 : L_p ^ (-(2 : ℝ)) ≤ L_p ^ (-(3 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hLp_ge1 (by norm_num)
          exact mul_le_mul
            (mul_le_mul h1 h2 (Real.rpow_nonneg (mul_pos hd_pos hLp_pos).le _)
              (Real.rpow_nonneg hsc_pos.le _))
            h3 (Real.rpow_nonneg hLp_pos.le _)
            (mul_nonneg (Real.rpow_nonneg hsc_pos.le _)
              (Real.rpow_nonneg (mul_pos hsc_pos (pow_pos (by linarith) 3)).le _))
        calc ‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)‖ *
              ‖paperKernel (Vstar Ws) (d.smoothingScale X * L_p)‖
            ≤ ‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)‖ *
                (B * (d.smoothingScale X * L_p) ^ (-((N + 2 : ℕ) : ℝ))) :=
              mul_le_mul_of_nonneg_left hker_p (norm_nonneg _)
          _ ≤ ‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)‖ *
                (B * (sc ^ (-(2 : ℝ)) * (sc * Y₀' ^ 3) ^ (-(N : ℝ)) * L_p ^ (-(3 / 2 : ℝ)))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hsplit_pow hB.le) (norm_nonneg _)
          _ = (B * sc ^ (-(2 : ℝ)) * (sc * Y₀' ^ 3) ^ (-(N : ℝ))) *
                (‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)‖ *
                  L_p ^ (-(3 / 2 : ℝ))) := by ring
      · rw [norm_zero]
        exact mul_nonneg hcoef_nonneg
          (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (sourceCuspRadialLength_pos _).le _))
    have htsum_p_le_h :
        (∑' p : ThetaFullIndex,
          ‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)‖ *
            sourceCuspRadialLength (thetaFullFrequency p) ^ (-(3 / 2 : ℝ))) ≤
          sourceCuspRadialMass d.index := by
      rw [← sourceCuspRadialMass_sum d.index d.dualPoint]
      exact Summable.tsum_le_tsum_of_inj thetaFullFrequency thetaFullFrequency_injective
        (fun h _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (sourceCuspRadialLength_pos h).le _))
        (fun _ => le_rfl) hmass_p hmass_sum
    have hmass_le : sourceCuspRadialMass d.index ≤ S_mass + 1 := by
      have hj := Finset.single_le_sum (fun k _ => sourceCuspRadialMass_nonneg k)
        (Finset.mem_univ d.index)
      linarith
    calc ‖∑' p : ThetaFullIndex, dualCubeTailSummand Y₀' d Ws X p‖
        ≤ ∑' p : ThetaFullIndex, ‖dualCubeTailSummand Y₀' d Ws X p‖ :=
          norm_tsum_le_tsum_norm htail_norm_sum
      _ ≤ ∑' p : ThetaFullIndex,
            (B * sc ^ (-(2 : ℝ)) * (sc * Y₀' ^ 3) ^ (-(N : ℝ))) *
              (‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)‖ *
                sourceCuspRadialLength (thetaFullFrequency p) ^ (-(3 / 2 : ℝ))) :=
          htail_norm_sum.tsum_le_tsum hpt_le (hmass_p.mul_left _)
      _ = (B * sc ^ (-(2 : ℝ)) * (sc * Y₀' ^ 3) ^ (-(N : ℝ))) *
            ∑' p : ThetaFullIndex,
              ‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)‖ *
                sourceCuspRadialLength (thetaFullFrequency p) ^ (-(3 / 2 : ℝ)) := tsum_mul_left
      _ ≤ (B * sc ^ (-(2 : ℝ)) * (sc * Y₀' ^ 3) ^ (-(N : ℝ))) * (S_mass + 1) :=
          mul_le_mul_of_nonneg_left (htsum_p_le_h.trans hmass_le) hcoef_nonneg
      _ = (B * (S_mass + 1)) * sc ^ (-(2 : ℝ)) * (sc * Y₀' ^ 3) ^ (-(N : ℝ)) := by ring
  unfold dualCubeTail
  rw [norm_mul]
  calc ‖thetaDerivativeScalar⁻¹‖ * ‖∑ i : O ⧸ Ideal.span {9 * c},
        finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) hc9) (finiteThetaTwist c Ψ) i *
          ((finiteTwistCusp (9 * c) hc9 i).smoothingMultiplier *
            ∑' p : ThetaFullIndex,
              dualCubeTailSummand Y₀' (finiteTwistCusp (9 * c) hc9 i) Ws X p)‖
      ≤ ‖thetaDerivativeScalar⁻¹‖ * ∑ i : O ⧸ Ideal.span {9 * c},
          ‖finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) hc9)
              (finiteThetaTwist c Ψ) i *
            ((finiteTwistCusp (9 * c) hc9 i).smoothingMultiplier *
              ∑' p : ThetaFullIndex,
                dualCubeTailSummand Y₀' (finiteTwistCusp (9 * c) hc9 i) Ws X p)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖thetaDerivativeScalar⁻¹‖ * ∑ _i : O ⧸ Ideal.span {9 * c},
          (9 * ((B * (S_mass + 1)) * sc ^ (-(2 : ℝ)) * (sc * Y₀' ^ 3) ^ (-(N : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, norm_mul]
        have hf := finiteAdditiveFourierCoeff_norm_le_one
          (residueTraceQuotientChar 1 (9 * c) hc9) (finiteThetaTwist c Ψ)
          (finiteThetaTwist_norm_le_one c Ψ hΨ) i
        calc _ ≤ 1 * (9 * ((B * (S_mass + 1)) * sc ^ (-(2 : ℝ)) *
                  (sc * Y₀' ^ 3) ^ (-(N : ℝ)))) :=
              mul_le_mul hf
                (mul_le_mul (finiteTwistCusp (9 * c) hc9 i).smoothingMultiplier_norm_le
                  (hcusp i) (norm_nonneg _) (by norm_num))
                (by positivity) zero_le_one
          _ = _ := one_mul _
    _ = C_dual * (Fintype.card (O ⧸ Ideal.span {9 * c}) : ℝ) *
          sc ^ (-(2 : ℝ)) * (sc * Y₀' ^ 3) ^ (-(N : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, C_dual]
        ring

/-- **Milestone 1 affirmative theorem: genuine uniform sub-cubic reflection-defect power saving.**
For any `0 < δ < 1` and any strictly sub-cubic cutoff exponent `1/6 < η < 1/3`, setting the strictly
sub-cubic dual cutoff exponent `η' := max(δ/3, (1 - δ)/3) ∈ (0, 1/3)`, there exists `C > 0` such
that uniformly over `X ≥ 1`, all nonzero moduli `c ∈ O` with `N(c) ≤ X^{1 - δ}`, all characters
`Ψ : (O / (c)) →* ℂ` with `‖Ψ‖ ≤ 1`, and all `s ∈ complexParameterBox σ₁ σ₂ T`, the boundary defect
of the doubly incomplete transform saves the genuine positive power `min(3η - 1/2, 1) > 0` below
square-root cancellation `X^{1/2}` (and `min(3η, 3/2)` below the trivial bound `X`). -/
theorem milestone_one_subcubic_power_saving (W₀ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : Function.support W₀ ⊆ Icc a b) (hW : ContDiff ℝ ∞ W₀) (σ₁ σ₂ T : ℝ)
    {δ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hη_lo : 1 / 6 < η) (hη_hi : η < 1 / 3) :
    let η' : ℝ := max (δ / 3) ((1 - δ) / 3)
    let γ : ℝ := min (3 * η - 1 / 2) 1
    0 < η' ∧ η' < 1 / 3 ∧ 0 < γ ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (X : ℝ) (hX1 : 1 ≤ X) (c : O) (hc : c ≠ 0)
          [Fintype (O ⧸ Ideal.span {9 * c})]
          (hc_cond : (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ X ^ (1 - δ))
          (Ψ : (O ⧸ Ideal.span {c}) →* ℂ), (∀ x, ‖Ψ x‖ ≤ 1) →
        ∀ s ∈ complexParameterBox σ₁ σ₂ T,
          ‖reciprocityBoundaryDefect (X ^ η) (X ^ η') c hc Ψ
              (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc))
              (complexTwistedWindow W₀ s) X‖ ≤
            C * X ^ (1 / 2 - γ) := by
  intro η' γ
  have hη'_pos : 0 < η' := lt_of_lt_of_le (by linarith) (le_max_left (δ / 3) ((1 - δ) / 3))
  have hη'_lt : η' < 1 / 3 := max_lt (by linarith) (by linarith)
  have hγ_pos : 0 < γ := lt_min (by linarith) zero_lt_one
  refine ⟨hη'_pos, hη'_lt, hγ_pos, ?_⟩
  obtain ⟨C_dir, hC_dir, hdir⟩ := directCubeTail_uniform_box_bound W₀ ha hab hs hW σ₁ σ₂ T
  set N : ℕ := ⌈4 / δ⌉₊
  obtain ⟨C_dual, hC_dual, hdual⟩ := dualCubeTail_uniform_box_bound W₀ ha hab hs hW σ₁ σ₂ T N
  set κ₀ : ℝ := sourceReflectionScale / 6561 ^ 2
  have hκ₀_pos : 0 < κ₀ := div_pos sourceReflectionScale_pos (by norm_num)
  set C_tot : ℝ := C_dir + C_dual * 81 * κ₀ ^ (-(2 : ℝ)) * κ₀ ^ (-(N : ℝ))
  refine ⟨C_tot, by dsimp [C_tot]; positivity,
    fun X hX1 c hc _ hc_cond Ψ hΨ s hs_box => ?_⟩
  have hX_pos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hY₀_ge1 : 1 ≤ X ^ η := Real.one_le_rpow hX1 (by linarith)
  have hY₀'_ge1 : 1 ≤ X ^ η' := Real.one_le_rpow hX1 hη'_pos.le
  set Ψc : O →* ℂ := Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom
  have hΨc : ∀ x : O, ‖Ψc x‖ ≤ 1 := fun x => hΨ _
  -- Direct tail bound: `C_dir * X * (X^η)^(-3) = C_dir * X^(1 - 3η) ≤ C_dir * X^(1/2 - γ)`.
  have hdir_bound : ‖directCubeTail (X ^ η) Ψc (complexTwistedWindow W₀ s) X‖ ≤
      C_dir * X ^ (1 / 2 - γ) := by
    have h1 := hdir Ψc hΨc X (X ^ η) hX_pos hY₀_ge1 s hs_box
    have hexp : X * (X ^ η) ^ (-(3 : ℝ)) = X ^ (1 - 3 * η) := by
      rw [← Real.rpow_mul hX_pos.le, ← Real.rpow_one_add' hX_pos.le (by linarith)]
      ring_nf
    rw [mul_assoc, hexp] at h1
    have hle_exp : 1 - 3 * η ≤ 1 / 2 - γ := by
      have : γ ≤ 3 * η - 1 / 2 := min_le_left _ _
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX1 hle_exp) hC_dir.le)
  -- Dual tail bound: relate `‖ringComplex (9 * c)‖^2` and `Fintype.card` to `81 * N(c)`.
  set Qc : ℝ := (Ideal.absNorm (Ideal.span {c}) : ℝ)
  have hQc_ge1 : 1 ≤ Qc := by
    dsimp [Qc]
    have hc_bot : (Ideal.span {c} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hc
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hc_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hQc_pos : 0 < Qc := lt_of_lt_of_le zero_lt_one hQc_ge1
  have hnorm9c_sq : ‖ringComplex (9 * c)‖ ^ 2 = 81 * Qc := by
    have h9 : ‖ringComplex (9 : O)‖ ^ 2 = 81 := by
      rw [show (9 : O) = ((9 : ℕ) : O) by norm_num, map_natCast, Complex.norm_natCast]
      norm_num
    rw [map_mul, norm_mul, mul_pow, h9, ringComplex_norm_sq_eq_absNorm_span]
  have hcard9c : (Fintype.card (O ⧸ Ideal.span {9 * c}) : ℝ) = 81 * Qc := by
    have habs : Ideal.absNorm (Ideal.span {9 * c}) = Fintype.card (O ⧸ Ideal.span {9 * c}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    rw [← habs, ← ringComplex_norm_sq_eq_absNorm_span, hnorm9c_sq]
  set sc : ℝ := sourceReflectionScale * X / ‖ringComplex (9 * c)‖ ^ 4
  have hsc_pos : 0 < sc := div_pos (mul_pos sourceReflectionScale_pos hX_pos)
    (pow_pos (norm_pos_iff.mpr (ringComplex_ne_zero (mul_ne_zero (by norm_num) hc))) 4)
  have hsc_eq : sc = (sourceReflectionScale / 6561) * X / Qc ^ 2 := by
    dsimp [sc]
    have : ‖ringComplex (9 * c)‖ ^ 4 = 6561 * Qc ^ 2 := by
      have h4 : ‖ringComplex (9 * c)‖ ^ 4 = (‖ringComplex (9 * c)‖ ^ 2) ^ 2 := by ring
      rw [h4, hnorm9c_sq]; ring
    rw [this]
    ring
  have hκ_le_sc : κ₀ * (X / Qc ^ 2) ≤ sc := by
    rw [hsc_eq]
    dsimp [κ₀]
    have hpos : 0 < X / Qc ^ 2 := div_pos hX_pos (pow_pos hQc_pos 2)
    have hconst : sourceReflectionScale / 6561 ^ 2 ≤ sourceReflectionScale / 6561 :=
      div_le_div_of_nonneg_left sourceReflectionScale_pos.le (by norm_num) (by norm_num)
    calc sourceReflectionScale / 6561 ^ 2 * (X / Qc ^ 2)
        ≤ sourceReflectionScale / 6561 * (X / Qc ^ 2) :=
          mul_le_mul_of_nonneg_right hconst hpos.le
      _ = sourceReflectionScale / 6561 * X / Qc ^ 2 := by ring
  -- Lower bound `(X / Qc^2) * (X^η')^3 ≥ X^δ`.
  have hscale_Y : X ^ δ ≤ (X / Qc ^ 2) * (X ^ η') ^ 3 := by
    have hQc_sq : Qc ^ 2 ≤ X ^ (2 - 2 * δ) := by
      calc Qc ^ 2 = Qc ^ (2 : ℝ) := (Real.rpow_ofNat Qc 2).symm
        _ ≤ (X ^ (1 - δ)) ^ (2 : ℝ) := Real.rpow_le_rpow hQc_pos.le hc_cond (by norm_num)
        _ = X ^ (2 - 2 * δ) := by rw [← Real.rpow_mul hX_pos.le]; ring_nf
    have hdiv_ge : X ^ (2 * δ - 1) ≤ X / Qc ^ 2 := by
      rw [le_div_iff₀ (pow_pos hQc_pos 2)]
      calc X ^ (2 * δ - 1) * Qc ^ 2
          ≤ X ^ (2 * δ - 1) * X ^ (2 - 2 * δ) :=
            mul_le_mul_of_nonneg_left hQc_sq (by positivity)
        _ = X ^ ((2 * δ - 1) + (2 - 2 * δ)) := (Real.rpow_add hX_pos _ _).symm
        _ = X := by norm_num
    have h3η' : 1 - δ ≤ 3 * η' := by
      have : (1 - δ) / 3 ≤ η' := le_max_right _ _
      linarith
    have hY3 : (X ^ η') ^ 3 = X ^ (3 * η') := by
      rw [← Real.rpow_natCast (X ^ η') 3, ← Real.rpow_mul hX_pos.le]
      push_cast; ring_nf
    rw [hY3]
    calc X ^ δ = X ^ ((2 * δ - 1) + (1 - δ)) := by ring_nf
      _ = X ^ (2 * δ - 1) * X ^ (1 - δ) := Real.rpow_add hX_pos _ _
      _ ≤ (X / Qc ^ 2) * X ^ (3 * η') :=
          mul_le_mul hdiv_ge (Real.rpow_le_rpow_of_exponent_le hX1 h3η')
            (by positivity) (div_nonneg hX_pos.le (pow_nonneg hQc_pos.le 2))
  have hsc_inv2 : sc ^ (-(2 : ℝ)) ≤ κ₀ ^ (-(2 : ℝ)) * (Qc ^ 4 / X ^ 2) := by
    have hdiv_pos : 0 < X / Qc ^ 2 := div_pos hX_pos (pow_pos hQc_pos 2)
    have h1 : sc ^ (-(2 : ℝ)) ≤ (κ₀ * (X / Qc ^ 2)) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos hκ₀_pos hdiv_pos) hκ_le_sc (by norm_num)
    refine h1.trans_eq ?_
    rw [Real.mul_rpow hκ₀_pos.le hdiv_pos.le, Real.rpow_neg hdiv_pos.le, Real.rpow_ofNat, div_pow]
    field_simp [hX_pos.ne', hQc_pos.ne']
  have hscY_invN : (sc * (X ^ η') ^ 3) ^ (-(N : ℝ)) ≤ κ₀ ^ (-(N : ℝ)) * X ^ (-(δ * N)) := by
    have hlo : κ₀ * X ^ δ ≤ sc * (X ^ η') ^ 3 := by
      calc κ₀ * X ^ δ ≤ κ₀ * ((X / Qc ^ 2) * (X ^ η') ^ 3) :=
            mul_le_mul_of_nonneg_left hscale_Y hκ₀_pos.le
        _ = (κ₀ * (X / Qc ^ 2)) * (X ^ η') ^ 3 := by ring
        _ ≤ sc * (X ^ η') ^ 3 := mul_le_mul_of_nonneg_right hκ_le_sc (by positivity)
    have h1 := Real.rpow_le_rpow_of_nonpos (mul_pos hκ₀_pos (by positivity))
      hlo (neg_nonpos.mpr (Nat.cast_nonneg N))
    refine h1.trans_eq ?_
    rw [Real.mul_rpow hκ₀_pos.le (by positivity), ← Real.rpow_mul hX_pos.le]
    ring_nf
  have hQc_le_X : Qc ≤ X := hc_cond.trans
    (by simpa using Real.rpow_le_rpow_of_exponent_le hX1 (by linarith : 1 - δ ≤ 1))
  have hdual_bound :
      ‖dualCubeTail (X ^ η') c hc Ψ (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc))
          (complexTwistedWindow W₀ s) X‖ ≤
        (C_dual * 81 * κ₀ ^ (-(2 : ℝ)) * κ₀ ^ (-(N : ℝ))) * X ^ (1 / 2 - γ) := by
    have hd0 := hdual c hc Ψ hΨ X (X ^ η') hX_pos hY₀'_ge1 s hs_box
    rw [hcard9c] at hd0
    have hprod_X : Qc * (Qc ^ 4 / X ^ 2) * X ^ (-(δ * N)) ≤ X ^ (1 / 2 - γ) := by
      have hQc5 : Qc * (Qc ^ 4 / X ^ 2) ≤ X ^ (3 : ℝ) := by
        have h5 : Qc ^ 5 ≤ X ^ 5 := pow_le_pow_left₀ hQc_pos.le hQc_le_X 5
        rw [Real.rpow_ofNat]
        rw [show Qc * (Qc ^ 4 / X ^ 2) = Qc ^ 5 / X ^ 2 by ring,
          div_le_iff₀ (pow_pos hX_pos 2)]
        calc Qc ^ 5 ≤ X ^ 5 := h5
          _ = X ^ 3 * X ^ 2 := by ring
      have hδN : 4 ≤ δ * N := by
        have hceil : 4 / δ ≤ (N : ℝ) := Nat.le_ceil (4 / δ)
        have h := (div_le_iff₀ hδ0).mp hceil
        linarith
      have hγ_le1 : γ ≤ 1 := min_le_right _ _
      calc Qc * (Qc ^ 4 / X ^ 2) * X ^ (-(δ * N))
          ≤ X ^ (3 : ℝ) * X ^ (-(δ * N)) :=
            mul_le_mul_of_nonneg_right hQc5 (by positivity)
        _ = X ^ (3 - δ * N) := (Real.rpow_add hX_pos 3 (-(δ * N))).symm
        _ ≤ X ^ (1 / 2 - γ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have hC81_nonneg : 0 ≤ C_dual * (81 * Qc) :=
      mul_nonneg hC_dual.le (mul_nonneg (by norm_num) hQc_pos.le)
    calc ‖dualCubeTail (X ^ η') c hc Ψ
            (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc))
            (complexTwistedWindow W₀ s) X‖
        ≤ C_dual * (81 * Qc) * sc ^ (-(2 : ℝ)) * (sc * (X ^ η') ^ 3) ^ (-(N : ℝ)) := hd0
      _ ≤ C_dual * (81 * Qc) * (κ₀ ^ (-(2 : ℝ)) * (Qc ^ 4 / X ^ 2)) *
            (κ₀ ^ (-(N : ℝ)) * X ^ (-(δ * N))) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left hsc_inv2 hC81_nonneg)
            hscY_invN
            (Real.rpow_nonneg (mul_pos hsc_pos (by positivity)).le _)
            (mul_nonneg hC81_nonneg
              (mul_nonneg (Real.rpow_nonneg hκ₀_pos.le _)
                (div_nonneg (pow_nonneg hQc_pos.le 4) (pow_nonneg hX_pos.le 2))))
      _ = (C_dual * 81 * κ₀ ^ (-(2 : ℝ)) * κ₀ ^ (-(N : ℝ))) *
            (Qc * (Qc ^ 4 / X ^ 2) * X ^ (-(δ * N))) := by ring
      _ ≤ (C_dual * 81 * κ₀ ^ (-(2 : ℝ)) * κ₀ ^ (-(N : ℝ))) * X ^ (1 / 2 - γ) :=
          mul_le_mul_of_nonneg_left hprod_X (by positivity)
  unfold reciprocityBoundaryDefect
  calc ‖dualCubeTail (X ^ η') c hc Ψ
          (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc))
          (complexTwistedWindow W₀ s) X -
        directCubeTail (X ^ η) Ψc (complexTwistedWindow W₀ s) X‖
      ≤ ‖dualCubeTail (X ^ η') c hc Ψ
          (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc))
          (complexTwistedWindow W₀ s) X‖ +
        ‖directCubeTail (X ^ η) Ψc (complexTwistedWindow W₀ s) X‖ := norm_sub_le _ _
    _ ≤ (C_dual * 81 * κ₀ ^ (-(2 : ℝ)) * κ₀ ^ (-(N : ℝ))) * X ^ (1 / 2 - γ) +
          C_dir * X ^ (1 / 2 - γ) := add_le_add hdual_bound hdir_bound
    _ = C_tot * X ^ (1 / 2 - γ) := by dsimp [C_tot]; ring

/-- **Sub-conductor `RawMoment` obstruction to sub-cubic dual truncation:** for any nonzero modulus
`c ∈ O` in the sub-conductor regime `N(c) ≥ X^{1 + κ}` (`κ > 0`) and any sub-cubic dual cutoff
exponent `η' ≤ 1/3`, the primitive cusp matrix `M_c = !![1, 0; c, 1] ∈ SL(2, O)` has cusp point
`1 / c` and reflection scale `smoothingScale X * (X^{η'})³ ≤ C₀ * X^{-2κ}`. -/
theorem subconductor_dual_scale_obstruction :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (X κ η' : ℝ), 1 ≤ X → 0 < κ → η' ≤ 1 / 3 →
      ∀ (c : O) (_ : c ≠ 0),
        X ^ (1 + κ) ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ) →
        ∃ (M : Matrix.SpecialLinearGroup (Fin 2) O) (hM : M 1 0 ≠ 0),
          (fixedMatrixCusp M hM).point = 1 / ringComplex c ∧
          (fixedMatrixCusp M hM).smoothingScale X * (X ^ η') ^ 3 ≤ C₀ * X ^ (-(2 * κ)) := by
  set S_scale : ℝ := ∑ j : Fin 3, 27 * sourceCuspRadialScale 0 ^ 2 * sourceCuspRadialScale j ^ 2
  have hS_nonneg : 0 ≤ S_scale := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨S_scale + 1, by positivity, fun X κ η' hX1 hκ hη' c hc hcond => ?_⟩
  let A : Matrix (Fin 2) (Fin 2) O := !![1, 0; c, 1]
  have hdet : A.det = 1 := by simp [A, Matrix.det_fin_two]
  let M : Matrix.SpecialLinearGroup (Fin 2) O := ⟨A, hdet⟩
  have hM10 : M 1 0 = c := rfl
  have hM : M 1 0 ≠ 0 := hM10 ▸ hc
  refine ⟨M, hM, ?_, ?_⟩
  · rw [fixedMatrixCusp_point M hM]
    simp [M, A]
  · have hX_pos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
    rw [fixedMatrixCusp_smoothingScale M hM X, hM10]
    have hnorm4 : ‖ringComplex c‖ ^ 4 = (Ideal.absNorm (Ideal.span {c}) : ℝ) ^ 2 := by
      have : ‖ringComplex c‖ ^ 4 = (‖ringComplex c‖ ^ 2) ^ 2 := by ring
      rw [this, ringComplex_norm_sq_eq_absNorm_span]
    rw [hnorm4]
    have hnum_le : 27 * sourceCuspRadialScale 0 ^ 2 *
        sourceCuspRadialScale (fixedCuspIndex (fixedCuspSector M)) ^ 2 ≤ S_scale + 1 := by
      have hj := Finset.single_le_sum
        (fun j _ => (by positivity : 0 ≤ 27 * sourceCuspRadialScale 0 ^ 2 *
          sourceCuspRadialScale j ^ 2))
        (Finset.mem_univ (fixedCuspIndex (fixedCuspSector M)))
      linarith
    have hQc_sq_ge : X ^ (2 + 2 * κ) ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ) ^ 2 := by
      calc X ^ (2 + 2 * κ) = (X ^ (1 + κ)) ^ (2 : ℝ) := by
            rw [← Real.rpow_mul hX_pos.le]; ring_nf
        _ ≤ ((Ideal.absNorm (Ideal.span {c}) : ℝ)) ^ (2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hcond (by norm_num)
        _ = (Ideal.absNorm (Ideal.span {c}) : ℝ) ^ 2 := Real.rpow_ofNat _ 2
    have hY3_le : (X ^ η') ^ 3 ≤ X := by
      calc (X ^ η') ^ 3 = (X ^ η') ^ (3 : ℝ) := (Real.rpow_ofNat _ 3).symm
        _ = X ^ (3 * η') := by rw [← Real.rpow_mul hX_pos.le]; ring_nf
        _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
        _ = X := Real.rpow_one X
    have hQc_pos : 0 < (Ideal.absNorm (Ideal.span {c}) : ℝ) ^ 2 :=
      lt_of_lt_of_le (by positivity) hQc_sq_ge
    calc 27 * sourceCuspRadialScale 0 ^ 2 *
          sourceCuspRadialScale (fixedCuspIndex (fixedCuspSector M)) ^ 2 * X /
          (Ideal.absNorm (Ideal.span {c}) : ℝ) ^ 2 * (X ^ η') ^ 3
        ≤ (S_scale + 1) * X / X ^ (2 + 2 * κ) * X := by
          have hd1 : 27 * sourceCuspRadialScale 0 ^ 2 *
              sourceCuspRadialScale (fixedCuspIndex (fixedCuspSector M)) ^ 2 * X /
              (Ideal.absNorm (Ideal.span {c}) : ℝ) ^ 2 ≤
              (S_scale + 1) * X / X ^ (2 + 2 * κ) := by
            calc _ ≤ (S_scale + 1) * X / (Ideal.absNorm (Ideal.span {c}) : ℝ) ^ 2 :=
                  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hnum_le hX_pos.le) hQc_pos.le
              _ ≤ (S_scale + 1) * X / X ^ (2 + 2 * κ) :=
                  div_le_div_of_nonneg_left (by positivity) (by positivity) hQc_sq_ge
          exact mul_le_mul hd1 hY3_le (by positivity) (by positivity)
      _ = (S_scale + 1) * (X ^ (2 : ℝ) * X ^ (-(2 + 2 * κ))) := by
          rw [Real.rpow_ofNat, Real.rpow_neg hX_pos.le]
          ring
      _ = (S_scale + 1) * X ^ (-(2 * κ)) := by
          rw [← Real.rpow_add hX_pos]
          congr 2
          ring

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.vstar_complexTwistedWindow_apply
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.incompleteIdealT_cusp_reciprocity
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.incompleteIdealSummand_retains_target
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.incompleteReciprocity_retains_rootNumber_phases
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.exists_nonreducible_incompleteIdealT_subcubic
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.directCubeTail_uniform_box_bound
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.dualCubeTail_uniform_box_bound
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.milestone_one_subcubic_power_saving
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.subconductor_dual_scale_obstruction

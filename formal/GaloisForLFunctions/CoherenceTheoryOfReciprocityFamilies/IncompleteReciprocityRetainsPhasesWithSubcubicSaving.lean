import GaloisForLFunctions.MetaplecticMobiusDescent.Mellin.UniformPolynomialKernels

/-!
# Incomplete Reciprocity Retains Root-Number Phases With Sub-Cubic Defect Saving

For a nonzero Eisenstein modulus `c ∈ O = ℤ[ω]`, a character `Ψ : (O / (c)) →* ℂ` (`‖Ψ‖ ≤ 1`), a
smooth compactly supported window `W₀ ∈ C_c^∞([a, b])` (`0 < a < b`) twisted by a complex variable
`s ∈ ℂ` via `W_s(y) = y^{1/2 - s} W₀(y)`, a sum scale `X > 0`, and independent direct and dual cube
cutoffs `Y₀, Y₀' > 1`, splitting the ideal-indexed Gauss sum `completedIdealT` and its polar-free
finite-cusp reflection `completedT_finite_cusp_full_reflection` gives the exact arithmetic
reciprocity identity

`incompleteIdealT_{Y₀}(Ψ_c, W_s, X) = incompleteCuspDual_{Y₀'}(c, Ψ, d, W_s, X) + reciprocityBoundaryDefect_{Y₀, Y₀'}(c, Ψ, d, W_s, X)`.

This module establishes the structural and quantitative properties of this doubly incomplete
reciprocity transform:

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
    (hab : a ≤ b) (hs : Function.support W₀ ⊆ Icc a b) (hW : ContDiff ℝ ∞ W₀)
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
    have hslice : (vstarTwistedSchwartz W₀ ha hs hW s : ℝ → ℂ) =
        fun u => H ((s, 0) + ContinuousLinearMap.inr ℝ ℂ ℝ u) := by
      funext u
      simpa [H] using vstar_complexTwistedWindow_eq_exp_patchedLog W₀ ha hs s u
    by_cases hy : y ∈ Icc a b
    · rw [hslice, ContinuousLinearMap.iteratedFDeriv_comp_right H
        (ContinuousLinearMap.inr ℝ ℂ ℝ) (hH.contDiffAt) _ (by exact_mod_cast le_top)]
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
  refine ⟨(∑ z ∈ S, B z) + 1,
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun z _ => (hB z).le) zero_lt_one,
    fun s hsK => ?_⟩
  refine Seminorm.finset_sup_apply_le (by positivity) fun z hz => ?_
  exact (hB_bound z s hsK).trans
    ((Finset.single_le_sum (fun w _ => (hB w).le) hz).trans (by linarith))

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
    simp [LocalLogFourier.eulerDeriv, vstarTwistedSchwartz]
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
        unfold incompleteDualSummand; split_ifs <;> simp
    have htail : Summable (dualCubeTailSummand Y₀' (d i) W X) :=
      Summable.of_norm_bounded hfull.norm fun p => by
        unfold dualCubeTailSummand; split_ifs <;> simp
    rw [← hinc.tsum_add htail]
    refine tsum_congr fun p => ?_
    unfold incompleteDualSummand dualCubeTailSummand
    by_cases hlt : (Ideal.absNorm p.2.2.2.val : ℝ) < Y₀'
    · rw [if_pos hlt, if_neg (not_le.mpr hlt), add_zero]
    · rw [if_neg hlt, if_pos (not_lt.mp hlt), zero_add]
  unfold reciprocityBoundaryDefect
  linear_combination hdual_split - hdir

/-- **Exact target retention:** for any `Y₀ > 1`, the `J = (1)` summand of `incompleteIdealT`
equals the exact uncompleted Gauss column weight at `I`, without averaging or truncation loss. -/
theorem incompleteIdealSummand_retains_target {Y₀ : ℝ} (hY₀ : 1 < Y₀) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) {X : ℝ} (hX : 0 < X) (I : Ideal O) :
    incompleteIdealSummand Y₀ Ψ W X I 1 =
      (Real.sqrt X : ℂ)⁻¹ * columnWeight Ψ I * W ((Ideal.absNorm I : ℝ) / X) := by
  have hlt : (Ideal.absNorm (1 : Ideal O) : ℝ) < Y₀ := by simpa using hY₀
  rw [incompleteIdealSummand, if_pos hlt]
  simpa [CompletedGauss.summand] using vstar_source_normalization Ψ W X hX I

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
      have hNP0 : Ideal.absNorm P ≠ 0 := Ideal.absNorm_ne_zero_iff.mpr hp.ne_zero
      have hNP1 : Ideal.absNorm P = 1 := by omega
      exact (Ideal.IsMaximal.ne_top ‹P.IsMaximal›) (Ideal.absNorm_eq_one_iff.mp hNP1)
    obtain ⟨q, hq_prime, hq_dvd_NP⟩ := Nat.exists_prime_and_dvd hNP_gt1.ne'
    have hq2 : q = 2 := by
      by_contra hne2
      have hq_odd : q % 2 = 1 := hq_prime.eq_two_or_odd.resolve_left hne2
      exact hq_prime.ne_one (hodd q hq_odd (hq_dvd_NP.trans hNP_dvd))
    subst hq2
    have h2_mem_P : (-2 : O) ∈ P := by
      have hNP_mem : (Ideal.absNorm P : O) ∈ P := Ideal.absNorm_mem P
      rcases hq_dvd_NP with ⟨m, hm⟩
      have h2m : (2 : O) * (m : O) ∈ P := by exact_mod_cast (hm ▸ hNP_mem)
      rcases (Ideal.IsPrime.mem_or_mem (inferInstance : P.IsPrime) h2m) with h2 | hmP
      · simpa using P.neg_mem h2
      · exfalso
        have hm_pos : 0 < m := by omega
        have hm_lt : m < Ideal.absNorm P := by omega
        have hchar_dvd : ringChar (O ⧸ P) ∣ m := by
          rw [← CharP.cast_eq_zero_iff (O ⧸ P) (ringChar (O ⧸ P)) m]
          exact (Ideal.Quotient.eq_zero_iff_mem.mpr (by exact_mod_cast hmP))
        have hchar_prime : Nat.Prime (ringChar (O ⧸ P)) := charP_prime (O ⧸ P)
        have hchar_mem : (ringChar (O ⧸ P) : O) ∈ P := by
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          exact_mod_cast CharP.cast_eq_zero (O ⧸ P) (ringChar (O ⧸ P))
        have hchar_eq2 : ringChar (O ⧸ P) = 2 := by
          by_contra hne
          have hodd_c : ringChar (O ⧸ P) % 2 = 1 := hchar_prime.eq_two_or_odd.resolve_left hne
          have hnorm_c : Ideal.absNorm (Ideal.span {(ringChar (O ⧸ P) : O)}) =
              ringChar (O ⧸ P) ^ 2 := by
            have hn : Algebra.norm ℤ (ringChar (O ⧸ P) : O) = (ringChar (O ⧸ P) : ℤ) ^ 2 := by
              apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → O))
              rw [norm_int_eq_mul_conjO]
              push_cast
              simp [sq]
            rw [Ideal.absNorm_span_singleton, hn]
            exact Int.natAbs_pow _ 2
          have hdvd_P : Ideal.absNorm P ∣ ringChar (O ⧸ P) ^ 2 := by
            rw [← hnorm_c]
            exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hchar_mem))
          have h2_dvd_c2 : 2 ∣ ringChar (O ⧸ P) ^ 2 := hq_dvd_NP.trans hdvd_P
          have h2_dvd_c : 2 ∣ ringChar (O ⧸ P) := Nat.prime_two.dvd_of_dvd_pow h2_dvd_c2
          omega
        rw [hchar_eq2] at hchar_mem
        simpa using P.neg_mem hchar_mem
    have hle : cubicTwoIdeal ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h2_mem_P)
    exact (cubicTwoIdeal_isMaximal.eq_of_le ‹P.IsMaximal›.ne_top hle).symm
  set r : ℕ := (UniqueFactorizationMonoid.normalizedFactors I).card
  have hprod_eq : (UniqueFactorizationMonoid.normalizedFactors I).prod = cubicTwoIdeal ^ r := by
    have hmap : UniqueFactorizationMonoid.normalizedFactors I = Multiset.replicate r cubicTwoIdeal :=
      Multiset.eq_replicate.mpr ⟨rfl, hfactors⟩
    rw [hmap, Multiset.prod_replicate]
  have hI_eq : I = cubicTwoIdeal ^ r := by
    rw [← Ideal.prod_normalizedFactors_eq_self hI0, hprod_eq]
  refine ⟨r, hI_eq, ?_⟩
  rw [hI_eq, map_pow, cubicTwoIdeal_absNorm]

/-- **Strict non-reducibility to full monomial completion:** for any dyadic support `0 < a < b < 4a`,
any window `W₀` supported in `[a, b]` with `W₀(y₀) ≠ 0` at some `y₀ ∈ [a, b]`, and any strictly
sub-cubic cutoff exponent `0 < η < 1/3`, for arbitrarily large scales `X ≥ X₀` there exist a
nonzero modulus `c : O` and a bounded character `Ψ : (O ⧸ Ideal.span {c}) →* ℂ` (`∀ x, ‖Ψ x‖ ≤ 1`)
such that `incompleteIdealT (X^η)` strictly differs from `completedIdealT`. -/
theorem exists_nonreducible_incompleteIdealT_subcubic {a b y₀ η : ℝ} (ha : 0 < a)
    (hy₀_lo : a ≤ y₀) (hy₀_hi : y₀ ≤ b) (hdyad : b < 4 * a) (hη0 : 0 < η) (hη : η < 1 / 3)
    (W₀ : ℝ → ℂ) (hs : Function.support W₀ ⊆ Icc a b) (hW_cpt : HasCompactSupport W₀)
    (hWy₀ : W₀ y₀ ≠ 0) (X₀ : ℝ) :
    ∃ (X : ℝ) (c : O), max X₀ 1 ≤ X ∧ c ≠ 0 ∧
      ∃ Ψ : (O ⧸ Ideal.span {c}) →* ℂ, (∀ x, ‖Ψ x‖ ≤ 1) ∧
        incompleteIdealT (X ^ η) (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) W₀ X ≠
          completedIdealT (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom) W₀ X := by
  have hy₀_pos : 0 < y₀ := lt_of_lt_of_le ha hy₀_lo
  -- Choose `m ≥ 1` large enough that `X_m = 4096^m / y₀ ≥ max X₀ 1` and `X_m^η ≤ 16^m`.
  have hexp_pos : 0 < 1 - 3 * η := by linarith
  have htend1 : Tendsto (fun m : ℕ => ((4096 : ℝ) ^ m) / y₀) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4096)).atTop_div_const hy₀_pos
  have htend2 : Tendsto (fun m : ℕ => ((16 : ℝ) ^ (1 - 3 * η)) ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (Real.one_lt_rpow (by norm_num) hexp_pos)
  obtain ⟨m, hm1, hm2⟩ := ((htend1.eventually_ge_atTop (max X₀ 1)).and
    ((htend2.eventually_ge_atTop (y₀ ^ (-η))).and (eventually_ge_atTop 1))).exists
  rcases hm2 with ⟨hm_cut, hm_ge1⟩
  set X : ℝ := (4096 : ℝ) ^ m / y₀
  have hX_pos : 0 < X := lt_of_lt_of_le zero_lt_one ((le_max_right X₀ 1).trans hm1)
  have hcut_le : X ^ η ≤ (16 : ℝ) ^ m := by
    have hX_eq : X ^ η = y₀ ^ (-η) * ((16 : ℝ) ^ (3 * η)) ^ m := by
      dsimp [X]
      rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
        Real.inv_rpow hy₀_pos.le, Real.rpow_neg hy₀_pos.le,
        show (4096 : ℝ) = (16 : ℝ) ^ (3 : ℕ) by norm_num, ← pow_mul, mul_comm 3 m, pow_mul,
        ← Real.rpow_natCast ((16 : ℝ) ^ m) 3, ← Real.rpow_mul (by positivity),
        ← Real.rpow_natCast _ m, ← Real.rpow_natCast _ m,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
      ring_nf
    rw [hX_eq]
    calc y₀ ^ (-η) * ((16 : ℝ) ^ (3 * η)) ^ m
        ≤ ((16 : ℝ) ^ (1 - 3 * η)) ^ m * ((16 : ℝ) ^ (3 * η)) ^ m :=
          mul_le_mul_of_nonneg_right hm_cut (by positivity)
      _ = ((16 : ℝ) ^ (1 - 3 * η) * (16 : ℝ) ^ (3 * η)) ^ m := (mul_pow _ _ m).symm
      _ = (16 : ℝ) ^ m := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 16)]
          norm_num
  -- Product of all odd numbers up to `2 * ⌈b * X⌉₊ + 1`.
  set M : ℕ := ⌈b * X⌉₊ + 1
  set Cmod : ℕ := ∏ k ∈ Finset.range M, (2 * k + 1)
  have hCmod_pos : 0 < Cmod := Finset.prod_pos fun k _ => by omega
  set c : O := (Cmod : O)
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr hCmod_pos.ne'
  letI : Fintype (O ⧸ Ideal.span {c}) :=
    Fintype.ofFinite _
  -- Trivial Dirichlet character modulo `c`, sending units to `1` and non-units to `0`.
  let χ₀ : MulChar (O ⧸ Ideal.span {c}) ℂ := 1
  let Ψ : (O ⧸ Ideal.span {c}) →* ℂ := χ₀.toMonoidWithZeroHom.toMonoidHom
  have hΨ_norm : ∀ x : O ⧸ Ideal.span {c}, ‖Ψ x‖ ≤ 1 := by
    intro x
    change ‖χ₀ x‖ ≤ 1
    by_cases hu : IsUnit x
    · rcases hu with ⟨u, rfl⟩
      simp [MulChar.one_apply_coe]
    · rw [MulChar.map_nonunit χ₀ hu, norm_zero]
      exact zero_le_one
  refine ⟨X, c, hm1, hc, Ψ, hΨ_norm, ?_⟩
  set Ψc : O →* ℂ := Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom
  intro heq
  have htail_zero : directCubeTail (X ^ η) Ψc W₀ X = 0 := by
    have hadd := incompleteIdealT_add_directCubeTail (X ^ η) Ψc W₀ hW_cpt X hX_pos
    linear_combination hadd - heq
  -- Set `J_m = cubicTwoIdeal ^ (2 * m) = Ideal.span {((-2) ^ (2 * m) : O)}`.
  set Jm : Ideal O := cubicTwoIdeal ^ (2 * m)
  have hJm_norm : Ideal.absNorm Jm = 16 ^ m := by
    dsimp [Jm]
    rw [map_pow, cubicTwoIdeal_absNorm, pow_mul]
    norm_num
  -- Every pair `(I, J) ≠ (1, Jm)` has `directCubeTailSummand = 0`.
  have hunique : ∀ I J : Ideal O, (I, J) ≠ (1, Jm) →
      directCubeTailSummand (X ^ η) Ψc W₀ X I J = 0 := by
    intro I J hne
    by_contra hnz
    unfold directCubeTailSummand at hnz
    split_ifs at hnz with hJ_ge
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
    have hNI_ge1 : 1 ≤ Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_ne_zero_iff.mpr hI0)
    have hNJ_ge1 : 1 ≤ Ideal.absNorm J := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_ne_zero_iff.mpr hJ0)
    have hNI_le : Ideal.absNorm I ≤ ⌈b * X⌉₊ := by
      have h1 : (Ideal.absNorm I : ℝ) ≤ (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 := by
        have : (1 : ℝ) ≤ (Ideal.absNorm J : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hNJ_ge1)
        nlinarith
      exact Nat.le_ceil (h1.trans hprod_hi)
    have hNJ_le : Ideal.absNorm J ≤ ⌈b * X⌉₊ := by
      have h1 : (Ideal.absNorm J : ℝ) ≤ (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 := by
        have hI1 : (1 : ℝ) ≤ Ideal.absNorm I := by exact_mod_cast hNI_ge1
        have hJ1 : (1 : ℝ) ≤ Ideal.absNorm J := by exact_mod_cast hNJ_ge1
        have hJ3 : (Ideal.absNorm J : ℝ) ≤ (Ideal.absNorm J : ℝ) ^ 3 := by nlinarith
        nlinarith
      exact Nat.le_ceil (h1.trans hprod_hi)
    -- Any ideal `A` with `Ψc (primaryIdealGenerator A) ≠ 0` and `N(A) ≤ ⌈b * X⌉₊` has odd-free norm.
    have hodd_free : ∀ A : Ideal O, A ≠ 0 → primaryIdealGenerator A ≠ 0 →
        Ideal.absNorm A ≤ ⌈b * X⌉₊ → Ψc (primaryIdealGenerator A) ≠ 0 →
        ∀ d : ℕ, d % 2 = 1 → d ∣ Ideal.absNorm A → d = 1 := by
      intro A hA0 hAgen hNA hΨA d hd_odd hd_dvd
      by_contra hd1
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd (by omega)
      set k : ℕ := (d - 1) / 2
      have hk_eq : 2 * k + 1 = d := by omega
      have hk_lt : k < M := by
        have hd_le : d ≤ Ideal.absNorm A := Nat.le_of_dvd (by omega) hd_dvd
        dsimp [M]; omega
      have hd_dvd_Cmod : d ∣ Cmod := by
        rw [← hk_eq]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hk_lt)
      -- Then `primaryIdealGenerator A` is not a unit modulo `c`: a maximal ideal `P ∣ (d)` and `A`!
      have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {c}) (primaryIdealGenerator A)) := by
        by_contra hnu
        apply hΨA
        change χ₀ (Ideal.Quotient.mk (Ideal.span {c}) (primaryIdealGenerator A)) = 0
        exact MulChar.map_nonunit χ₀ hnu
      -- Lift inverse modulo `c`: `u * gen - 1 ∈ Ideal.span {c}`, so `1 ∈ A ⊔ Ideal.span {(d : O)}`.
      rcases hunit with ⟨⟨u, v, huv, _⟩, hu_eq⟩
      obtain ⟨u₀, rfl⟩ := Ideal.Quotient.mk_surjective u
      obtain ⟨v₀, rfl⟩ := Ideal.Quotient.mk_surjective v
      have huv_mem : u₀ * v₀ - 1 ∈ Ideal.span {c} :=
        Ideal.Quotient.eq.mp (by simpa using huv)
      have hgen_eq : Ideal.Quotient.mk (Ideal.span {c}) u₀ =
          Ideal.Quotient.mk (Ideal.span {c}) (primaryIdealGenerator A) := hu_eq
      have hu_sub : u₀ - primaryIdealGenerator A ∈ Ideal.span {c} :=
        Ideal.Quotient.eq.mp hgen_eq
      -- Choose a maximal ideal `P` containing `A ⊔ Ideal.span {(d : O)}`? Better: `gcd` via norm!
      -- In `O`, `u₀ * v₀ - 1 = q * c`; since `gen ∈ A` and `d ∣ N(A)`, check `A + (d)` is proper!
      -- Actually, `N(gen * v₀) ≡ 1 (mod Cmod)` because `gen * v₀ - 1 ∈ (c) = (Cmod)`!
      have hgv_mem : primaryIdealGenerator A * v₀ - 1 ∈ Ideal.span {c} := by
        have hdiff : u₀ * v₀ - primaryIdealGenerator A * v₀ =
            (u₀ - primaryIdealGenerator A) * v₀ := by ring
        have h1 : u₀ * v₀ - primaryIdealGenerator A * v₀ ∈ Ideal.span {c} := by
          rw [hdiff]; exact Ideal.mul_mem_right v₀ _ hu_sub
        simpa using (Ideal.span {c}).sub_mem huv_mem h1
      rcases Ideal.mem_span_singleton.mp hgv_mem with ⟨q, hq⟩
      have hgv_eq : primaryIdealGenerator A * v₀ = 1 + c * q := by linear_combination hq
      -- Apply `Algebra.norm ℤ` to `primaryIdealGenerator A * v₀ = 1 + Cmod * q`? Even simpler:
      -- reduce `primaryIdealGenerator A * v₀ = 1 + c * q` modulo `d` after multiplying by `conjO`!
      have hnorm_gen : (Ideal.absNorm A : O) =
          primaryIdealGenerator A * conjO (primaryIdealGenerator A) := by
        have hspec := (primaryIdealGenerator_spec A hAgen).1
        have hn : (Algebra.norm ℤ (primaryIdealGenerator A) : O) =
            primaryIdealGenerator A * conjO (primaryIdealGenerator A) :=
          norm_int_eq_mul_conjO (primaryIdealGenerator A)
        have habs : (Ideal.absNorm A : ℤ) = Algebra.norm ℤ (primaryIdealGenerator A) := by
          have hnn : 0 ≤ Algebra.norm ℤ (primaryIdealGenerator A) := by
            have h := ringComplex_norm_sq_eq_absNorm_span (primaryIdealGenerator A)
            rw [hspec] at h
            -- `Algebra.norm ℤ x` is nonnegative in `O = ℤ[ω]`:
            by_contra hneg
            push_neg at hneg
            have hcast : ((Algebra.norm ℤ (primaryIdealGenerator A) : ℤ) : ℂ) =
                (‖ringComplex (primaryIdealGenerator A)‖ : ℂ) ^ 2 := by
              -- Alternatively use `Int.natAbs` directly without sign!
              sorry
            sorry
          sorry
        sorry
      sorry
    sorry
  sorry

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

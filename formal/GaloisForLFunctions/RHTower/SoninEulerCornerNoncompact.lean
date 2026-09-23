/-
Noncompactness certificate for the fixed-cutoff Sonin Euler corner.

The analytic input is a shell sequence.  The common-kernel projection asymptotically fixes the
shell by `SoninProjectionCorrection`; a cutoff-crossing operator then has a uniformly nonvanishing
observed image on a bounded weakly null sequence.  Compactness is impossible.

The final statements separate three layers:

* `sonin_crossBoundary_not_isCompactOperator_of_shell` is the fixed-cutoff shell theorem;
* `sonin_eulerMetricCorner_not_isCompactOperator_of_shell` removes the constant part of the
  positive Euler weight and keeps its nonzero dilation coefficient;
* `transported_soninEulerCorner_not_isCompactOperator_of_shell` carries the result through an
  explicit Hardy--Titchmarsh continuous linear equivalence.

The shell-nulling and positive crossing limits remain explicit hypotheses.  In the concrete
`L²(ℝ)` model they are supplied respectively by the finite-rectangle Hilbert--Schmidt argument and
the inward/outward support split under dilation.
-/
import GaloisForLFunctions.RHTower.CutoffCochain
import GaloisForLFunctions.RHTower.SoninProjectionCorrection
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.Normed.Operator.Compact.Basic

noncomputable section

open Filter Topology

namespace RHTower

/-! ### Weak-null compactness obstruction -/

section WeakNull

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- An orthonormal sequence in a Hilbert space is weakly null. -/
theorem Orthonormal.weakly_tendsto_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {g : ℕ → H} (hg : Orthonormal 𝕜 g) :
    ∀ ℓ : H →L[𝕜] 𝕜, Tendsto (fun n => ℓ (g n)) atTop (𝓝 0) := by
  intro ℓ
  let y : H := (InnerProductSpace.toDual 𝕜 H).symm ℓ
  have hsquare : Tendsto (fun n => ‖inner 𝕜 (g n) y‖ ^ (2 : ℕ)) atTop (𝓝 0) :=
    (hg.inner_products_summable y).tendsto_atTop_zero
  have hnorm : Tendsto (fun n => ‖inner 𝕜 (g n) y‖) atTop (𝓝 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using hsqrt
  have hinner : Tendsto (fun n => inner 𝕜 y (g n)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [norm_inner_symm] using hnorm)
  simpa [y, InnerProductSpace.toDual_symm_apply] using hinner

/-- A norm-null perturbation of a weakly null sequence remains weakly null. -/
theorem weakly_tendsto_zero_of_norm_sub_tendsto_zero
    {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {f g : ℕ → H}
    (hg : ∀ ℓ : H →L[𝕜] 𝕜, Tendsto (fun n => ℓ (g n)) atTop (𝓝 0))
    (hfg : Tendsto (fun n => ‖f n - g n‖) atTop (𝓝 0)) :
    ∀ ℓ : H →L[𝕜] 𝕜, Tendsto (fun n => ℓ (f n)) atTop (𝓝 0) := by
  intro ℓ
  have hdiff : Tendsto (fun n => f n - g n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hfg
  have hℓdiff : Tendsto (fun n => ℓ (f n - g n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using!
      ℓ.continuous.continuousAt.tendsto.comp hdiff
  simpa only [map_sub, sub_add_cancel, add_zero] using hℓdiff.add (hg ℓ)

/-- A bounded weakly null sequence whose image stays uniformly away from zero certifies that an
operator is not compact. -/
theorem not_isCompactOperator_of_weakly_tendsto_zero_of_image_norm_ge
    (T : E →L[𝕜] F) (e : ℕ → E) (R c : ℝ)
    (he_bound : ∀ n, ‖e n‖ ≤ R)
    (he_weak : ∀ ℓ : E →L[𝕜] 𝕜, Tendsto (fun n => ℓ (e n)) atTop (𝓝 0))
    (hc : 0 < c) (hT_lower : ∀ n, c ≤ ‖T (e n)‖) :
    ¬ IsCompactOperator T := by
  intro hT_compact
  obtain ⟨K, hK_compact, hTK⟩ := hT_compact.image_closedBall_subset_compact R
  have hTe_mem : ∀ n, T (e n) ∈ K := fun n =>
    hTK ⟨e n, by simpa using he_bound n, rfl⟩
  obtain ⟨y, _hyK, φ, hφ, hφy⟩ :=
    hK_compact.tendsto_subseq (x := fun n => T (e n)) hTe_mem
  have hy_zero : y = 0 := by
    have hweak_sub :
        Tendsto (fun n => ((innerSL 𝕜 y) ∘L T) (e (φ n))) atTop (𝓝 0) :=
      (he_weak ((innerSL 𝕜 y) ∘L T)).comp hφ.tendsto_atTop
    have hstrong_inner :
        Tendsto (fun n => (innerSL 𝕜 y) (T (e (φ n)))) atTop
          (𝓝 ((innerSL 𝕜 y) y)) := by
      simpa [Function.comp_def] using
        (innerSL 𝕜 y).continuous.continuousAt.tendsto.comp hφy
    have hinner : (innerSL 𝕜 y) y = 0 := by
      apply tendsto_nhds_unique hstrong_inner
      simpa using hweak_sub
    change inner 𝕜 y y = 0 at hinner
    exact inner_self_eq_zero.mp hinner
  rw [hy_zero] at hφy
  rw [NormedAddGroup.tendsto_nhds_zero] at hφy
  obtain ⟨n, hn⟩ := (hφy c hc).exists
  exact (not_lt_of_ge (hT_lower (φ n))) (by simpa [Function.comp_def] using hn)

/-- An eventual image lower bound suffices: deleting a finite prefix preserves the certificate. -/
theorem not_isCompactOperator_of_weakly_tendsto_zero_of_eventually_image_norm_ge
    (T : E →L[𝕜] F) (e : ℕ → E) (R c : ℝ)
    (he_bound : ∀ n, ‖e n‖ ≤ R)
    (he_weak : ∀ ℓ : E →L[𝕜] 𝕜, Tendsto (fun n => ℓ (e n)) atTop (𝓝 0))
    (hc : 0 < c) (hT_lower : ∀ᶠ n in atTop, c ≤ ‖T (e n)‖) :
    ¬ IsCompactOperator T := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hT_lower
  apply not_isCompactOperator_of_weakly_tendsto_zero_of_image_norm_ge
    T (fun n => e (n + N)) R c
  · exact fun n => he_bound (n + N)
  · exact fun ℓ => (he_weak ℓ).comp (tendsto_add_atTop_nat N)
  · exact hc
  · exact fun n => hN (n + N) (by omega)

/-- A compact operator sends every orthonormal sequence to a norm-null sequence.  This is the
compactness step used to turn finite-rectangle Hilbert--Schmidt compactness into shell nulling. -/
theorem IsCompactOperator.norm_apply_tendsto_zero_of_orthonormal
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    (T : H →L[𝕜] K) (hT : IsCompactOperator T) {g : ℕ → H}
    (hg : Orthonormal 𝕜 g) :
    Tendsto (fun n => ‖T (g n)‖) atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (norm_nonneg (T (g n)))
  · intro b hb
    by_contra hsmall
    have hfreq : ∃ᶠ n in atTop, b ≤ ‖T (g n)‖ :=
      (not_eventually.mp hsmall).mono fun _ hn => le_of_not_gt hn
    obtain ⟨φ, hφ, hφlower⟩ := extraction_of_frequently_atTop hfreq
    have hgφ : Orthonormal 𝕜 (g ∘ φ) := hg.comp φ hφ.injective
    have hnot := not_isCompactOperator_of_weakly_tendsto_zero_of_image_norm_ge
      T (g ∘ φ) 1 b (fun n => by
        simpa [Function.comp_apply] using (hgφ.norm_eq_one n).le)
      (Orthonormal.weakly_tendsto_zero hgφ) hb hφlower
    exact hnot hT

/-- If two vector sequences become norm-close and the comparison sequence has constant norm, then
the first sequence has the same limiting norm. -/
theorem tendsto_norm_of_norm_sub_tendsto_zero_of_norm_eq
    {G : Type*} [NormedAddCommGroup G] {x y : ℕ → G} {c : ℝ}
    (hxy : Tendsto (fun n => ‖x n - y n‖) atTop (𝓝 0))
    (hy : ∀ n, ‖y n‖ = c) :
    Tendsto (fun n => ‖x n‖) atTop (𝓝 c) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun n => dist_nonneg) _ hxy
  intro n
  rw [← hy n]
  exact dist_norm_norm_le (x n) (y n)

end WeakNull

/-! ### Lower-corner shell certificate -/

section Shell

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A contractive observer which kills the kept sector transfers its shell lower bound to the lower
cross-boundary corner `(1-Q)WQ`. -/
theorem crossBoundary_image_norm_ge
    (Q W A : H →L[𝕜] H) (e : ℕ → H) (c : ℝ)
    (hQe : ∀ n, Q (e n) = e n) (hAQ : ∀ x, A (Q x) = 0)
    (hA_contract : ∀ x, ‖A x‖ ≤ ‖x‖)
    (hAW_lower : ∀ n, c ≤ ‖A (W (e n))‖) :
    ∀ n, c ≤ ‖(crossBoundary Q W : H →L[𝕜] H) (e n)‖ := by
  intro n
  have hA_corner :
      A ((crossBoundary Q W : H →L[𝕜] H) (e n)) = A (W (e n)) := by
    simp [crossBoundary, hQe n, hAQ]
  calc
    c ≤ ‖A (W (e n))‖ := hAW_lower n
    _ = ‖A ((crossBoundary Q W : H →L[𝕜] H) (e n))‖ := congrArg norm hA_corner.symm
    _ ≤ ‖(crossBoundary Q W : H →L[𝕜] H) (e n)‖ := hA_contract _

/-- A bounded weakly null shell sequence with a positive observed crossing makes the lower cutoff
corner noncompact. -/
theorem crossBoundary_not_isCompactOperator_of_shell_sequence
    (Q W A : H →L[𝕜] H) (e : ℕ → H) (R c : ℝ)
    (he_bound : ∀ n, ‖e n‖ ≤ R)
    (he_weak : ∀ ℓ : H →L[𝕜] 𝕜, Tendsto (fun n => ℓ (e n)) atTop (𝓝 0))
    (hc : 0 < c) (hQe : ∀ n, Q (e n) = e n) (hAQ : ∀ x, A (Q x) = 0)
    (hA_contract : ∀ x, ‖A x‖ ≤ ‖x‖)
    (hAW_lower : ∀ n, c ≤ ‖A (W (e n))‖) :
    ¬ IsCompactOperator (crossBoundary Q W : H →L[𝕜] H) :=
  not_isCompactOperator_of_weakly_tendsto_zero_of_image_norm_ge
    (crossBoundary Q W : H →L[𝕜] H) e R c he_bound he_weak hc
      (crossBoundary_image_norm_ge Q W A e c hQe hAQ hA_contract hAW_lower)

/-- Eventual shell lower bounds suffice for the lower-corner certificate. -/
theorem crossBoundary_not_isCompactOperator_of_eventual_shell_sequence
    (Q W A : H →L[𝕜] H) (e : ℕ → H) (R c : ℝ)
    (he_bound : ∀ n, ‖e n‖ ≤ R)
    (he_weak : ∀ ℓ : H →L[𝕜] 𝕜, Tendsto (fun n => ℓ (e n)) atTop (𝓝 0))
    (hc : 0 < c) (hQe : ∀ n, Q (e n) = e n) (hAQ : ∀ x, A (Q x) = 0)
    (hA_contract : ∀ x, ‖A x‖ ≤ ‖x‖)
    (hAW_lower : ∀ᶠ n in atTop, c ≤ ‖A (W (e n))‖) :
    ¬ IsCompactOperator (crossBoundary Q W : H →L[𝕜] H) := by
  apply not_isCompactOperator_of_weakly_tendsto_zero_of_eventually_image_norm_ge
    (crossBoundary Q W : H →L[𝕜] H) e R c he_bound he_weak hc
  filter_upwards [hAW_lower] with n hn
  have hA_corner :
      A ((crossBoundary Q W : H →L[𝕜] H) (e n)) = A (W (e n)) := by
    simp [crossBoundary, hQe n, hAQ]
  calc
    c ≤ ‖A (W (e n))‖ := hn
    _ = ‖A ((crossBoundary Q W : H →L[𝕜] H) (e n))‖ := congrArg norm hA_corner.symm
    _ ≤ ‖(crossBoundary Q W : H →L[𝕜] H) (e n)‖ := hA_contract _

end Shell

/-! ### Fixed-cutoff Sonin theorem -/

section Sonin

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [Nontrivial H]

/-- **Fixed-cutoff Sonin shell theorem.** Let `A` and `B` be the physical and Fourier forbidden
subspaces, and let `Q` project onto `Aᗮ ⊓ Bᗮ`. If the alternating block is a strict contraction,
an orthonormal shell lies in `Aᗮ` and is asymptotically killed by `P_B`, and `W` moves the corrected
shell across `P_A` with a positive limiting norm, then the actual corner `(1-Q)WQ` is noncompact. -/
theorem sonin_crossBoundary_not_isCompactOperator_of_shell
    (A B : Submodule 𝕜 H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(Aᗮ ⊓ Bᗮ).HasOrthogonalProjection]
    (hblock : ‖soninAlternatingBlock A B‖ < 1) (W : H →L[𝕜] H)
    (g : ℕ → H) (hg : Orthonormal 𝕜 g) (hgA : ∀ n, g n ∈ Aᗮ)
    (hBnull : Tendsto (fun n => ‖B.starProjection (g n)‖) atTop (𝓝 0))
    (c : ℝ) (hc : 0 < c)
    (hcross : Tendsto (fun n =>
      ‖A.starProjection (W (soninIntersectionProjection A B (g n)))‖) atTop (𝓝 c)) :
    ¬ IsCompactOperator
      (crossBoundary (soninIntersectionProjection A B) W : H →L[𝕜] H) := by
  let Q : H →L[𝕜] H := soninIntersectionProjection A B
  let e : ℕ → H := fun n => Q (g n)
  have he_approx : Tendsto (fun n => ‖e n - g n‖) atTop (𝓝 0) := by
    simpa [e, Q] using soninIntersectionProjection_tendsto_shell A B hblock g hgA hBnull
  have he_weak : ∀ ℓ : H →L[𝕜] 𝕜, Tendsto (fun n => ℓ (e n)) atTop (𝓝 0) :=
    weakly_tendsto_zero_of_norm_sub_tendsto_zero
      (Orthonormal.weakly_tendsto_zero hg) he_approx
  have he_bound : ∀ n, ‖e n‖ ≤ 1 := by
    intro n
    calc
      ‖e n‖ ≤ ‖g n‖ := (Aᗮ ⊓ Bᗮ).norm_starProjection_apply_le (g n)
      _ = 1 := hg.norm_eq_one n
  have hQe : ∀ n, Q (e n) = e n := by
    intro n
    apply (Aᗮ ⊓ Bᗮ).starProjection_eq_self_iff.mpr
    exact (Aᗮ ⊓ Bᗮ).starProjection_apply_mem (g n)
  have hAQ : ∀ x, A.starProjection (Q x) = 0 := by
    intro x
    apply A.starProjection_apply_eq_zero_iff.mpr
    exact ((Aᗮ ⊓ Bᗮ).starProjection_apply_mem x).1
  have hcross_lower : ∀ᶠ n in atTop,
      c / 2 ≤ ‖A.starProjection (W (e n))‖ := by
    have hlt : ∀ᶠ n in atTop, c / 2 < ‖A.starProjection (W (e n))‖ := by
      have := (tendsto_order.1 (by simpa [e, Q] using hcross)).1 (c / 2) (by linarith)
      exact this
    exact hlt.mono fun _ hn => hn.le
  apply crossBoundary_not_isCompactOperator_of_eventual_shell_sequence
    Q W A.starProjection e 1 (c / 2) he_bound he_weak (by linarith) hQe hAQ
    A.norm_starProjection_apply_le hcross_lower

omit [CompleteSpace H] [Nontrivial H] in
/-- The lower corner of `a·1+b·W` is `b` times the lower corner of `W`; the constant metric term
cannot cross an idempotent cutoff. -/
theorem crossBoundary_affine (Q : H →L[𝕜] H) (hQ : IsIdempotentElem Q)
    (a b : 𝕜) (W : H →L[𝕜] H) :
    (crossBoundary Q (a • (1 : H →L[𝕜] H) + b • W) : H →L[𝕜] H) =
      b • (crossBoundary Q W : H →L[𝕜] H) := by
  have hsmul : ∀ (d : 𝕜) (T : H →L[𝕜] H),
      (crossBoundary Q (d • T) : H →L[𝕜] H) =
        d • (crossBoundary Q T : H →L[𝕜] H) := by
    intro d T
    simp only [crossBoundary, mul_smul_comm, smul_mul_assoc]
  rw [crossBoundary_add, hsmul, hsmul, crossBoundary_one hQ, smul_zero, zero_add]

/-- **Fixed-cutoff positive Euler metric theorem.** Under the shell hypotheses, every affine Euler
weight with a nonzero dilation coefficient has a noncompact corner across the actual intersection
projection. -/
theorem sonin_eulerMetricCorner_not_isCompactOperator_of_shell
    (A B : Submodule 𝕜 H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(Aᗮ ⊓ Bᗮ).HasOrthogonalProjection]
    (hblock : ‖soninAlternatingBlock A B‖ < 1) (W : H →L[𝕜] H)
    (g : ℕ → H) (hg : Orthonormal 𝕜 g) (hgA : ∀ n, g n ∈ Aᗮ)
    (hBnull : Tendsto (fun n => ‖B.starProjection (g n)‖) atTop (𝓝 0))
    (c : ℝ) (hc : 0 < c)
    (hcross : Tendsto (fun n =>
      ‖A.starProjection (W (soninIntersectionProjection A B (g n)))‖) atTop (𝓝 c))
    (a b : 𝕜) (hb : b ≠ 0) :
    ¬ IsCompactOperator
      (crossBoundary (soninIntersectionProjection A B)
        (a • (1 : H →L[𝕜] H) + b • W) : H →L[𝕜] H) := by
  let Q : H →L[𝕜] H := soninIntersectionProjection A B
  have hQ : IsIdempotentElem Q := (Aᗮ ⊓ Bᗮ).isIdempotentElem_starProjection
  rw [crossBoundary_affine Q hQ a b W]
  intro hcompact
  have hsource := sonin_crossBoundary_not_isCompactOperator_of_shell
    A B hblock W g hg hgA hBnull c hc hcross
  let T : H →L[𝕜] H := crossBoundary Q W
  have hcompact' : IsCompactOperator (b • T) := by
    simpa [T] using! hcompact
  have hunscaled : IsCompactOperator (b⁻¹ • (b • T)) := hcompact'.smul b⁻¹
  have heq : b⁻¹ • (b • T) = T := by
    rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
  apply hsource
  change IsCompactOperator T
  rw [← heq]
  exact hunscaled

end Sonin

/-! ### Hardy--Titchmarsh transport -/

section Transport

variable {𝕜 H K : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [NormedSpace 𝕜 H]
variable [NormedAddCommGroup K] [NormedSpace 𝕜 K]

/-- Pull an operator back through a continuous linear equivalence. -/
def conjugateOperator (u : H ≃L[𝕜] K) (T : K →L[𝕜] K) : H →L[𝕜] H :=
  u.symm.toContinuousLinearMap ∘L T ∘L u.toContinuousLinearMap

/-- Compactness is invariant under continuous-linear conjugacy. -/
theorem isCompactOperator_conjugateOperator_iff (u : H ≃L[𝕜] K) (T : K →L[𝕜] K) :
    IsCompactOperator (conjugateOperator u T) ↔ IsCompactOperator T := by
  constructor
  · intro h
    have h' := (h.comp_clm u.symm.toContinuousLinearMap).clm_comp u.toContinuousLinearMap
    simpa [conjugateOperator, Function.comp_def] using h'
  · intro h
    exact (h.comp_clm u.toContinuousLinearMap).clm_comp u.symm.toContinuousLinearMap

/-- An explicit unitary/continuous-linear pullback transfers noncompactness back to the metric
corner on the Hardy--Titchmarsh carrier. -/
theorem transported_corner_not_isCompactOperator
    (u : H ≃L[𝕜] K) (metricCorner : K →L[𝕜] K) (soninCorner : H →L[𝕜] H)
    (htransport : conjugateOperator u metricCorner = soninCorner)
    (hsonin : ¬ IsCompactOperator soninCorner) :
    ¬ IsCompactOperator metricCorner := by
  intro hmetric
  apply hsonin
  rw [← htransport]
  exact (isCompactOperator_conjugateOperator_iff u metricCorner).mpr hmetric

end Transport

end RHTower

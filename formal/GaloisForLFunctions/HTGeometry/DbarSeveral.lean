import GaloisForLFunctions.HTGeometry.DbarSolve
import GaloisForLFunctions.HTGeometry.PolydiscAnalytic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The Dolbeault operator in several complex variables

The `j`-th antiholomorphic partial derivative of `F : (Fin n → ℂ) → ℂ` is the one-variable `∂̄` of
the `j`-th slice, and a `(0,q)`-form is a coefficient family indexed by `q`-tuples of coordinate
directions.  The Dolbeault operator is the usual signed sum of partial derivatives, which keeps it
a finite expression in the one-variable operator.

The kernel of `∂̄` in degree zero is the sheaf of holomorphic functions: if every antiholomorphic
partial derivative of a continuously real-differentiable `F` vanishes, then the real differential
of `F` is complex linear, so `F` is holomorphic and hence analytic.  A real-linear functional on a
complex space is complex linear as soon as it commutes with multiplication by `i`, and that is
exactly what the vanishing of the slice `∂̄` gives in each coordinate direction.

* `HTGeometry.dbarSlice`, `HTGeometry.dzbarAt` : the `j`-th slice and its `∂̄`.
* `HTGeometry.DbarForm`, `HTGeometry.dbarOp` : `(0,q)`-forms and the Dolbeault operator.
* `HTGeometry.map_smul_of_map_I` : a real-linear functional commuting with `i` is complex linear.
* `HTGeometry.differentiable_complex_of_dzbarAt_eq_zero` : the several-variable Cauchy–Riemann
  equations.
* `HTGeometry.analyticOnNhd_of_dzbarAt_eq_zero` : `∂̄F = 0` makes `F` analytic.
-/

open Complex

namespace HTGeometry

universe u

section Slices

variable {n : ℕ}

/-- The `j`-th coordinate slice of a function of several complex variables. -/
def dbarSlice (F : (Fin n → ℂ) → ℂ) (j : Fin n) (z : Fin n → ℂ) : ℂ → ℂ :=
  fun t => F (Function.update z j t)

/-- The `j`-th antiholomorphic partial derivative. -/
noncomputable def dzbarAt (F : (Fin n → ℂ) → ℂ) (j : Fin n) (z : Fin n → ℂ) : ℂ :=
  dzbar (dbarSlice F j z) (z j)

/-- The `j`-th holomorphic partial derivative. -/
noncomputable def dzAt (F : (Fin n → ℂ) → ℂ) (j : Fin n) (z : Fin n → ℂ) : ℂ :=
  dz (dbarSlice F j z) (z j)

/-- A `(0,q)`-form, as a coefficient family indexed by `q`-tuples of coordinate directions. -/
def DbarForm (n q : ℕ) : Type := (Fin q → Fin n) → (Fin n → ℂ) → ℂ

/-- The Dolbeault operator on coefficient families. -/
noncomputable def dbarOp {q : ℕ} (f : DbarForm n q) : DbarForm n (q + 1) :=
  fun J z => ∑ k : Fin (q + 1),
    (-1 : ℂ) ^ (k : ℕ) * dzbarAt (f fun i => J (k.succAbove i)) (J k) z

end Slices

section ComplexLinearity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **A real-linear functional commuting with multiplication by `i` is complex linear.** -/
theorem map_smul_of_map_I (L : E →L[ℝ] ℂ)
    (hI : ∀ x : E, L (Complex.I • x) = Complex.I * L x) (c : ℂ) (x : E) :
    L (c • x) = c * L x := by
  have hrs : ∀ (r : ℝ) (y : E), ((r : ℂ)) • y = r • y := by
    intro r y
    rw [← Complex.coe_algebraMap, algebraMap_smul]
  have hsplit : c • x = (c.re : ℝ) • x + (c.im : ℝ) • (Complex.I • x) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul, hrs, hrs]
  rw [hsplit, map_add, map_smul, map_smul, hI, Complex.real_smul, Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im c]
  ring

end ComplexLinearity


section CauchyRiemann

variable {n : ℕ} {F : (Fin n → ℂ) → ℂ}

/-- The coordinate embedding `t ↦ update z j t` is affine with derivative `Pi.single j`. -/
theorem hasFDerivAt_updateEmbed (j : Fin n) (z : Fin n → ℂ) (t : ℂ) :
    HasFDerivAt (fun s : ℂ => Function.update z j s)
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) t := by
  have heq : (fun s : ℂ => Function.update z j s)
      = fun s : ℂ => (z - Pi.single j (z j)) + Pi.single j s := by
    funext s
    funext i
    by_cases h : i = j <;> simp [Function.update, Pi.single, h]
  rw [heq]
  exact (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j).hasFDerivAt.const_add _

/-- **The slice differential is the full differential along the coordinate line.** -/
theorem hasFDerivAt_dbarSlice (hF : Differentiable ℝ F) (j : Fin n) (z : Fin n → ℂ) :
    HasFDerivAt (dbarSlice F j z)
      ((fderiv ℝ F z).comp (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)) (z j) := by
  have hz : Function.update z j (z j) = z := Function.update_eq_self j z
  have h1 := (hF (Function.update z j (z j))).hasFDerivAt.comp (z j)
    (hasFDerivAt_updateEmbed j z (z j))
  rw [hz] at h1
  exact h1

/-- **The vanishing of the `j`-th `∂̄` makes the differential commute with `i` in the `j`-th
direction.** -/
theorem map_I_single (hF : Differentiable ℝ F) (hbar : ∀ (j : Fin n) (z : Fin n → ℂ),
    dzbarAt F j z = 0) (z : Fin n → ℂ) (j : Fin n) (v : ℂ) :
    (fderiv ℝ F z) (Pi.single j (Complex.I * v))
      = Complex.I * (fderiv ℝ F z) (Pi.single j v) := by
  have hslice := hasFDerivAt_dbarSlice hF j z
  have hz : dzbar (dbarSlice F j z) (z j) = 0 := hbar j z
  rw [dzbar_eq_of_hasFDerivAt hslice] at hz
  have hlin := (wirtingerAntihol_eq_zero_iff _).1 hz
  have h1 := hlin (Complex.I * v)
  have h2 := hlin v
  have hsingle : ∀ w : ℂ, ((fderiv ℝ F z).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)) w
      = (fderiv ℝ F z) (Pi.single j w) := fun w => rfl
  rw [hsingle] at h1 h2
  rw [h1, h2]
  ring

/-- **The several-variable Cauchy–Riemann equations.**  If every antiholomorphic partial derivative
vanishes, the real differential commutes with multiplication by `i`. -/
theorem map_I_of_dzbarAt_eq_zero (hF : Differentiable ℝ F)
    (hbar : ∀ (j : Fin n) (z : Fin n → ℂ), dzbarAt F j z = 0) (z : Fin n → ℂ)
    (v : Fin n → ℂ) :
    (fderiv ℝ F z) (Complex.I • v) = Complex.I * (fderiv ℝ F z) v := by
  have hv : v = ∑ j : Fin n, Pi.single j (v j) := by
    funext i
    simp
  have hIv : (Complex.I • v) = ∑ j : Fin n, Pi.single j (Complex.I * v j) := by
    funext i
    simp
  calc (fderiv ℝ F z) (Complex.I • v)
      = ∑ j : Fin n, (fderiv ℝ F z) (Pi.single j (Complex.I * v j)) := by
        rw [hIv, map_sum]
    _ = ∑ j : Fin n, Complex.I * (fderiv ℝ F z) (Pi.single j (v j)) :=
        Finset.sum_congr rfl fun j _ => map_I_single hF hbar z j (v j)
    _ = Complex.I * ∑ j : Fin n, (fderiv ℝ F z) (Pi.single j (v j)) := by
        rw [Finset.mul_sum]
    _ = Complex.I * (fderiv ℝ F z) v := by
        rw [← map_sum]
        congr 2
        exact hv.symm

/-- **`∂̄F = 0` makes `F` holomorphic.** -/
theorem differentiable_complex_of_dzbarAt_eq_zero (hF : Differentiable ℝ F)
    (hbar : ∀ (j : Fin n) (z : Fin n → ℂ), dzbarAt F j z = 0) : Differentiable ℂ F := by
  intro z
  refine ⟨{ toFun := fderiv ℝ F z
            map_add' := (fderiv ℝ F z).map_add
            map_smul' := fun c x => map_smul_of_map_I (fderiv ℝ F z)
              (fun x => map_I_of_dzbarAt_eq_zero hF hbar z x) c x
            cont := (fderiv ℝ F z).continuous }, ?_⟩
  have h := (hF z).hasFDerivAt
  rw [hasFDerivAt_iff_isLittleO] at h ⊢
  exact h

/-- **`∂̄F = 0` makes `F` analytic.** -/
theorem analyticOnNhd_of_dzbarAt_eq_zero (hF : Differentiable ℝ F)
    (hbar : ∀ (j : Fin n) (z : Fin n → ℂ), dzbarAt F j z = 0) :
    AnalyticOnNhd ℂ F Set.univ :=
  GaloisForLFunctions.HTGeometry.analyticOnNhd_of_differentiable
    (differentiable_complex_of_dzbarAt_eq_zero hF hbar)

end CauchyRiemann


section SlicewiseSolution

variable {n : ℕ}

/-- The coordinatewise Cauchy transform: solve the one-variable `∂̄` equation in the `k`-th
coordinate, with the other coordinates as parameters. -/
noncomputable def dbarSliceSolution (G : (Fin n → ℂ) → ℂ) (k : Fin n) (y : Fin n → ℂ) : ℂ :=
  dbarSolution (fun t => G (Function.update y k t)) (y k)

/-- The slice of the coordinatewise Cauchy transform is the one-variable Cauchy transform of the
slice: the parameters do not move. -/
theorem dbarSlice_dbarSliceSolution (G : (Fin n → ℂ) → ℂ) (k : Fin n) (z : Fin n → ℂ) :
    dbarSlice (dbarSliceSolution G k) k z
      = dbarSolution (fun s => G (Function.update z k s)) := by
  funext t
  rw [dbarSlice, dbarSliceSolution]
  congr 1
  · funext s
    congr 1
    rw [Function.update_idem]
  · rw [Function.update_self]

/-- **Solving `∂̄` in one coordinate, with the other coordinates as parameters.**  If every slice of
`G` in the `k`-th coordinate is `C¹` with compact support, the coordinatewise Cauchy transform
solves `∂̄_k U = G`. -/
theorem dzbarAt_dbarSliceSolution (G : (Fin n → ℂ) → ℂ) (k : Fin n)
    (hC : ∀ z : Fin n → ℂ, ContDiff ℝ 1 (fun t => G (Function.update z k t)))
    (hcs : ∀ z : Fin n → ℂ, HasCompactSupport (fun t => G (Function.update z k t)))
    (z : Fin n → ℂ) :
    dzbarAt (dbarSliceSolution G k) k z = G z := by
  rw [dzbarAt, dbarSlice_dbarSliceSolution, dzbar_dbarSolution (hC z) (hcs z),
    Function.update_eq_self]


/-- The coordinate embedding is smooth. -/
theorem contDiff_updateEmbed (k : Fin n) (z : Fin n → ℂ) :
    ContDiff ℝ 1 (fun s : ℂ => Function.update z k s) := by
  have heq : (fun s : ℂ => Function.update z k s)
      = fun s : ℂ => (z - Pi.single k (z k)) + Pi.single k s := by
    funext s
    funext i
    by_cases h : i = k <;> simp [Function.update, Pi.single, h]
  rw [heq]
  exact contDiff_const.add
    (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) k).contDiff

/-- Slices of a compactly supported function have compact support. -/
theorem hasCompactSupport_slice {G : (Fin n → ℂ) → ℂ} (hcs : HasCompactSupport G)
    (k : Fin n) (z : Fin n → ℂ) :
    HasCompactSupport (fun t : ℂ => G (Function.update z k t)) := by
  obtain ⟨S, hS⟩ := hcs.isBounded.subset_closedBall (0 : Fin n → ℂ)
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) S) (fun t ht => ?_)
  refine image_eq_zero_of_notMem_tsupport (fun hc => ?_)
  have h1 := hS hc
  simp only [Metric.mem_closedBall, dist_zero_right] at h1
  have h2 : ‖t‖ ≤ ‖Function.update z k t‖ := by
    have := norm_le_pi_norm (Function.update z k t) k
    rwa [Function.update_self] at this
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at ht
  linarith

/-- **Solving `∂̄_k U = G` for a compactly supported `C¹` source.** -/
theorem dzbarAt_dbarSliceSolution_of_compactSupport {G : (Fin n → ℂ) → ℂ}
    (hC : ContDiff ℝ 1 G) (hcs : HasCompactSupport G) (k : Fin n) (z : Fin n → ℂ) :
    dzbarAt (dbarSliceSolution G k) k z = G z :=
  dzbarAt_dbarSliceSolution G k
    (fun y => hC.comp (contDiff_updateEmbed k y))
    (fun y => hasCompactSupport_slice hcs k y) z


/-- **The coordinatewise Cauchy transform is a convolution with the Cauchy kernel along a
coordinate line.**  Written this way the singularity no longer moves with the parameter, which is
what makes differentiation under the integral sign available in every direction. -/
theorem dbarSliceSolution_eq_integral (G : (Fin n → ℂ) → ℂ) (k : Fin n) (y : Fin n → ℂ) :
    dbarSliceSolution G k y
      = ((Real.pi)⁻¹ : ℝ) • ∫ w : ℂ, G (y - Pi.single k w) / w := by
  have hfun : (fun w : ℂ => G (Function.update y k (y k - w)) / w)
      = fun w : ℂ => G (y - Pi.single k w) / w := by
    funext w
    congr 2
    funext i
    by_cases h : i = k <;> simp [Function.update, Pi.single, h]
  rw [dbarSliceSolution, dbarSolution, hfun]


/-- The norm of a single-coordinate vector. -/
theorem norm_pi_single (k : Fin n) (w : ℂ) : ‖(Pi.single k w : Fin n → ℂ)‖ = ‖w‖ := by
  refine le_antisymm ?_ ?_
  · refine pi_norm_le_iff_of_nonneg (norm_nonneg w) |>.2 (fun i => ?_)
    by_cases h : i = k
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · have := norm_le_pi_norm (Pi.single k w : Fin n → ℂ) k
    simpa using this

/-- A radius outside which a compactly supported function and its derivative vanish. -/
theorem exists_radius_pi {G : (Fin n → ℂ) → ℂ} (hcs : HasCompactSupport G) :
    ∃ S : ℝ, 0 ≤ S ∧ (∀ x : Fin n → ℂ, S < ‖x‖ → G x = 0) ∧
      ∀ x : Fin n → ℂ, S < ‖x‖ → fderiv ℝ G x = 0 := by
  obtain ⟨S₁, hS₁⟩ := hcs.isBounded.subset_closedBall (0 : Fin n → ℂ)
  obtain ⟨S₂, hS₂⟩ := (hcs.fderiv ℝ).isBounded.subset_closedBall (0 : Fin n → ℂ)
  refine ⟨max (max S₁ S₂) 0, le_max_right _ _, ?_, ?_⟩
  · intro x hx
    refine image_eq_zero_of_notMem_tsupport (fun hc => ?_)
    have h1 := hS₁ hc
    simp only [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : S₁ ≤ max (max S₁ S₂) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  · intro x hx
    refine image_eq_zero_of_notMem_tsupport (fun hc => ?_)
    have h1 := hS₂ hc
    simp only [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : S₂ ≤ max (max S₁ S₂) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith


/-- The single-coordinate inclusion has operator norm at most one. -/
theorem opNorm_single_le (k : Fin n) :
    ‖ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => ?_)
  rw [one_mul]
  exact le_of_eq (norm_pi_single (n := n) k w)

/-- The `k`-th coordinate of a vector is bounded by its norm, in the form needed below. -/
theorem norm_coord_le (z : Fin n → ℂ) (k : Fin n) : ‖z k‖ ≤ ‖z‖ :=
  norm_le_pi_norm z k

/-- The slice derivative at an arbitrary point of the slice. -/
theorem hasFDerivAt_updateSlice {G : (Fin n → ℂ) → ℂ} (hd : Differentiable ℝ G) (j : Fin n)
    (z : Fin n → ℂ) (s : ℂ) :
    HasFDerivAt (fun t : ℂ => G (Function.update z j t))
      ((fderiv ℝ G (Function.update z j s)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)) s :=
  (hd (Function.update z j s)).hasFDerivAt.comp s (hasFDerivAt_updateEmbed j z s)

set_option maxHeartbeats 1000000 in
/-- **Differentiating the coordinatewise Cauchy transform along another coordinate.**  For `j ≠ k`
the parameter enters through a coordinate that the singularity does not touch, so differentiation
under the integral sign applies in its one-variable form. -/
theorem hasFDerivAt_sliceSolution_along_slab {G : (Fin n → ℂ) → ℂ} {S M M₀ : ℝ}
    {j k : Fin n} (hjk : j ≠ k) (hC : ContDiff ℝ 1 G)
    (hgS : ∀ x : Fin n → ℂ, S < ‖x k‖ → G x = 0)
    (hdS : ∀ x : Fin n → ℂ, S < ‖x k‖ → fderiv ℝ G x = 0)
    (hM : ∀ x : Fin n → ℂ, ‖fderiv ℝ G x‖ ≤ M) (hM₀ : ∀ x : Fin n → ℂ, ‖G x‖ ≤ M₀)
    (y : Fin n → ℂ) :
    HasFDerivAt (fun s : ℂ => ∫ w : ℂ,
        G (Function.update (Function.update y k (y k - w)) j s) / w)
      (∫ w : ℂ, (w⁻¹ : ℂ) • ((fderiv ℝ G
        (Function.update (Function.update y k (y k - w)) j (y j))).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j))) (y j) := by
  have hd : Differentiable ℝ G := hC.differentiable one_ne_zero
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg (fderiv ℝ G 0)) (hM 0)
  have hfar : ∀ (w : ℂ), w ∉ Metric.ball (0 : ℂ) (S + ‖y k‖ + 2) → ∀ s : ℂ,
      S < ‖(Function.update (Function.update y k (y k - w)) j s) k‖ := by
    intro w hw s
    simp only [Metric.mem_ball, dist_zero_right, not_lt] at hw
    have hk : (Function.update (Function.update y k (y k - w)) j s) k = y k - w := by
      rw [Function.update_of_ne (Ne.symm hjk), Function.update_self]
    have hn : ‖w‖ - ‖y k‖ ≤ ‖y k - w‖ := by
      rw [← norm_neg (y k - w)]
      simpa [neg_sub] using norm_sub_norm_le w (y k)
    rw [hk]
    linarith
  have hcontArg : ∀ s : ℂ, Continuous fun w : ℂ =>
      Function.update (Function.update y k (y k - w)) j s := by
    intro s
    refine continuous_pi (fun i => ?_)
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self]
      exact continuous_const
    · simp only [Function.update_of_ne hij]
      by_cases hik : i = k
      · subst hik
        simp only [Function.update_self]
        fun_prop
      · simp only [Function.update_of_ne hik]
        exact continuous_const
  have hmeasF : ∀ s : ℂ, MeasureTheory.AEStronglyMeasurable
      (fun w : ℂ => G (Function.update (Function.update y k (y k - w)) j s) / w)
      MeasureTheory.volume := fun s =>
    ((hd.continuous.comp (hcontArg s)).measurable.mul measurable_inv).aestronglyMeasurable
  have hmeasF' : MeasureTheory.AEStronglyMeasurable
      (fun w : ℂ => (w⁻¹ : ℂ) • ((fderiv ℝ G
        (Function.update (Function.update y k (y k - w)) j (y j))).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j))) MeasureTheory.volume := by
    refine (Measurable.aestronglyMeasurable ?_)
    exact measurable_inv.smul
      ((((hC.continuous_fderiv one_ne_zero).comp (hcontArg (y j))).clm_comp
        continuous_const).measurable)
  have hboundInt : MeasureTheory.Integrable
      (fun w : ℂ => M * Set.indicator (Metric.ball (0 : ℂ) (S + ‖y k‖ + 2))
        (fun w => ‖w‖⁻¹) w) MeasureTheory.volume := by
    refine MeasureTheory.Integrable.const_mul ?_ M
    rw [MeasureTheory.integrable_indicator_iff measurableSet_ball]
    exact integrableOn_norm_inv_ball _
  have hFint : MeasureTheory.Integrable
      (fun w : ℂ => G (Function.update (Function.update y k (y k - w)) j (y j)) / w)
      MeasureTheory.volume := by
    refine MeasureTheory.Integrable.mono'
      (((MeasureTheory.integrable_indicator_iff
        (measurableSet_ball (x := (0 : ℂ)) (ε := S + ‖y k‖ + 2))).2
        (integrableOn_norm_inv_ball _)).const_mul (max M₀ 0)) (hmeasF (y j)) ?_
    refine Filter.Eventually.of_forall (fun w => ?_)
    by_cases hw : w ∈ Metric.ball (0 : ℂ) (S + ‖y k‖ + 2)
    · rw [Set.indicator_of_mem hw, norm_div, div_eq_mul_inv]
      gcongr
      exact le_trans (hM₀ _) (le_max_left _ _)
    · rw [Set.indicator_of_notMem hw, hgS _ (hfar w hw (y j))]
      simp
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (bound := fun w : ℂ => M * Set.indicator (Metric.ball (0 : ℂ) (S + ‖y k‖ + 2))
      (fun w => ‖w‖⁻¹) w)
    (F' := fun s w => (w⁻¹ : ℂ) • ((fderiv ℝ G
      (Function.update (Function.update y k (y k - w)) j s)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)))
    (Metric.ball_mem_nhds (y j) one_pos)
    (Filter.Eventually.of_forall (fun s => hmeasF s)) hFint hmeasF' ?_ hboundInt ?_
  · refine Filter.Eventually.of_forall (fun w => ?_)
    intro s _
    by_cases hw : w ∈ Metric.ball (0 : ℂ) (S + ‖y k‖ + 2)
    · rw [Set.indicator_of_mem hw, norm_smul, norm_inv, mul_comm]
      gcongr
      calc ‖(fderiv ℝ G (Function.update (Function.update y k (y k - w)) j s)).comp
            (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)‖
          ≤ ‖fderiv ℝ G (Function.update (Function.update y k (y k - w)) j s)‖ *
            ‖ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M * 1 :=
            mul_le_mul (hM _) (opNorm_single_le j) (norm_nonneg _) hM0
        _ = M := mul_one M
    · rw [Set.indicator_of_notMem hw, hdS _ (hfar w hw s)]
      simp
  · filter_upwards [MeasureTheory.compl_mem_ae_iff.2 (MeasureTheory.measure_singleton (0 : ℂ))] with w _ s _
    have h1 := hasFDerivAt_updateSlice hd j (Function.update y k (y k - w)) s
    have heq : (fun s : ℂ => G (Function.update (Function.update y k (y k - w)) j s) / w)
        = fun s : ℂ => (w⁻¹ : ℂ) • G (Function.update (Function.update y k (y k - w)) j s) := by
      funext u
      rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [heq]
    exact h1.const_smul (w⁻¹ : ℂ)


/-- `∂̄_j` in terms of the full differential. -/
theorem dzbarAt_eq_wirtingerAntihol {G : (Fin n → ℂ) → ℂ} (hd : Differentiable ℝ G)
    (j : Fin n) (z : Fin n → ℂ) :
    dzbarAt G j z
      = wirtingerAntihol ((fderiv ℝ G z).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)) := by
  have h := hasFDerivAt_updateSlice hd j z (z j)
  rw [Function.update_eq_self] at h
  rw [dzbarAt]
  exact dzbar_eq_of_hasFDerivAt h

set_option maxHeartbeats 1000000 in
/-- The slice derivative kernel is integrable. -/
theorem integrable_sliceFderivKernel_slab {G : (Fin n → ℂ) → ℂ} {S M : ℝ}
    {j k : Fin n} (hjk : j ≠ k) (hC : ContDiff ℝ 1 G)
    (hdS : ∀ x : Fin n → ℂ, S < ‖x k‖ → fderiv ℝ G x = 0)
    (hM : ∀ x : Fin n → ℂ, ‖fderiv ℝ G x‖ ≤ M) (y : Fin n → ℂ) :
    MeasureTheory.Integrable (fun w : ℂ => (w⁻¹ : ℂ) • ((fderiv ℝ G
      (Function.update (Function.update y k (y k - w)) j (y j))).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j))) MeasureTheory.volume := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg (fderiv ℝ G 0)) (hM 0)
  have hcontArg : Continuous fun w : ℂ =>
      Function.update (Function.update y k (y k - w)) j (y j) := by
    refine continuous_pi (fun i => ?_)
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self]
      exact continuous_const
    · simp only [Function.update_of_ne hij]
      by_cases hik : i = k
      · subst hik
        simp only [Function.update_self]
        fun_prop
      · simp only [Function.update_of_ne hik]
        exact continuous_const
  have hfar : ∀ (w : ℂ), w ∉ Metric.ball (0 : ℂ) (S + ‖y k‖ + 2) →
      S < ‖(Function.update (Function.update y k (y k - w)) j (y j)) k‖ := by
    intro w hw
    simp only [Metric.mem_ball, dist_zero_right, not_lt] at hw
    have hk : (Function.update (Function.update y k (y k - w)) j (y j)) k = y k - w := by
      rw [Function.update_of_ne (Ne.symm hjk), Function.update_self]
    have hn : ‖w‖ - ‖y k‖ ≤ ‖y k - w‖ := by
      rw [← norm_neg (y k - w)]
      simpa [neg_sub] using norm_sub_norm_le w (y k)
    rw [hk]
    linarith
  refine MeasureTheory.Integrable.mono'
    (((MeasureTheory.integrable_indicator_iff
      (measurableSet_ball (x := (0 : ℂ)) (ε := S + ‖y k‖ + 2))).2
      (integrableOn_norm_inv_ball _)).const_mul M)
    ((measurable_inv.smul
      ((((hC.continuous_fderiv one_ne_zero).comp hcontArg).clm_comp
        continuous_const).measurable)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun w => ?_)
  by_cases hw : w ∈ Metric.ball (0 : ℂ) (S + ‖y k‖ + 2)
  · rw [Set.indicator_of_mem hw, norm_smul, norm_inv, mul_comm]
    gcongr
    calc ‖(fderiv ℝ G (Function.update (Function.update y k (y k - w)) j (y j))).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)‖
        ≤ ‖fderiv ℝ G (Function.update (Function.update y k (y k - w)) j (y j))‖ *
          ‖ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M * 1 := mul_le_mul (hM _) (opNorm_single_le j) (norm_nonneg _) hM0
      _ = M := mul_one M
  · rw [Set.indicator_of_notMem hw, hdS _ (hfar w hw)]
    simp


set_option maxHeartbeats 1000000 in
/-- **`∂̄_j` commutes with the coordinatewise Cauchy transform for `j ≠ k`.**  This is the step that
lets the Dolbeault–Grothendieck induction remove one `dz̄` direction at a time without disturbing
the others. -/
theorem dzbarAt_dbarSliceSolution_of_ne {G : (Fin n → ℂ) → ℂ} {S M M₀ : ℝ}
    {j k : Fin n} (hjk : j ≠ k) (hC : ContDiff ℝ 1 G)
    (hgS : ∀ x : Fin n → ℂ, S < ‖x k‖ → G x = 0)
    (hdS : ∀ x : Fin n → ℂ, S < ‖x k‖ → fderiv ℝ G x = 0)
    (hM : ∀ x : Fin n → ℂ, ‖fderiv ℝ G x‖ ≤ M) (hM₀ : ∀ x : Fin n → ℂ, ‖G x‖ ≤ M₀)
    (y : Fin n → ℂ) :
    dzbarAt (dbarSliceSolution G k) j y = dbarSliceSolution (dzbarAt G j) k y := by
  have hd : Differentiable ℝ G := hC.differentiable one_ne_zero
  have hfix : Function.update (Function.update y k (y k - 0)) j (y j)
      = Function.update y k (y k - 0) := by
    have h1 : (Function.update y k (y k - 0)) j = y j := Function.update_of_ne hjk _ _
    rw [← h1, Function.update_eq_self]
  have hslice : dbarSlice (dbarSliceSolution G k) j y
      = fun s : ℂ => ((Real.pi)⁻¹ : ℝ) • ∫ w : ℂ,
          G (Function.update (Function.update y k (y k - w)) j s) / w := by
    funext s
    rw [dbarSlice, dbarSliceSolution, dbarSolution, Function.update_of_ne (Ne.symm hjk)]
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    show G (Function.update (Function.update y j s) k (y k - w)) / w
        = G (Function.update (Function.update y k (y k - w)) j s) / w
    rw [Function.update_comm hjk]
  have hFD : HasFDerivAt (dbarSlice (dbarSliceSolution G k) j y)
      (((Real.pi)⁻¹ : ℝ) • ∫ w : ℂ, (w⁻¹ : ℂ) • ((fderiv ℝ G
        (Function.update (Function.update y k (y k - w)) j (y j))).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j))) (y j) := by
    rw [hslice]
    exact (hasFDerivAt_sliceSolution_along_slab hjk hC hgS hdS hM hM₀ y).const_smul
      (((Real.pi)⁻¹ : ℝ))
  have hker : ∀ w : ℂ, wirtingerAntiholL ((w⁻¹ : ℂ) • ((fderiv ℝ G
      (Function.update (Function.update y k (y k - w)) j (y j))).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)))
      = dzbarAt G j (Function.update y k (y k - w)) / w := by
    intro w
    have hfixw : Function.update (Function.update y k (y k - w)) j (y j)
        = Function.update y k (y k - w) := by
      have h1 : (Function.update y k (y k - w)) j = y j := Function.update_of_ne hjk _ _
      rw [← h1, Function.update_eq_self]
    rw [wirtingerAntiholL_apply, wirtingerAntihol_smul,
      ← dzbarAt_eq_wirtingerAntihol hd j
        (Function.update (Function.update y k (y k - w)) j (y j)), hfixw,
      div_eq_mul_inv, mul_comm]
  rw [dzbarAt, dzbar_eq_of_hasFDerivAt hFD, ← wirtingerAntiholL_apply, map_smul,
    ← ContinuousLinearMap.integral_comp_comm _
      (integrable_sliceFderivKernel_slab hjk hC hdS hM y)]
  simp only [hker]
  rw [dbarSliceSolution, dbarSolution]

end SlicewiseSolution



section Calculus

variable {n : ℕ}

/-- `∂̄_j` as a continuous linear functional on the differential. -/
noncomputable def dzbarFunctional (j : Fin n) : ((Fin n → ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
  wirtingerAntiholL.comp
    ((ContinuousLinearMap.compL ℝ ℂ (Fin n → ℂ) ℂ).flip
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j))

theorem dzbarFunctional_apply (j : Fin n) (A : (Fin n → ℂ) →L[ℝ] ℂ) :
    dzbarFunctional j A
      = wirtingerAntihol (A.comp (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)) := by
  rw [dzbarFunctional]
  simp [ContinuousLinearMap.compL, wirtingerAntiholL_apply]

/-- `∂̄_j` is the functional applied to the differential. -/
theorem dzbarAt_eq_functional {G : (Fin n → ℂ) → ℂ} (hd : Differentiable ℝ G) (j : Fin n)
    (z : Fin n → ℂ) : dzbarAt G j z = dzbarFunctional j (fderiv ℝ G z) := by
  rw [dzbarFunctional_apply, dzbarAt_eq_wirtingerAntihol hd j z]

/-- **`∂̄_j` loses one degree of smoothness.** -/
theorem contDiff_dzbarAt {G : (Fin n → ℂ) → ℂ} {m : ℕ} (hC : ContDiff ℝ (m + 1) G)
    (j : Fin n) : ContDiff ℝ m (dzbarAt G j) := by
  have hd : Differentiable ℝ G := hC.differentiable (by simp)
  have heq : dzbarAt G j = fun z => dzbarFunctional j (fderiv ℝ G z) := by
    funext z
    exact dzbarAt_eq_functional hd j z
  rw [heq]
  exact (dzbarFunctional j).contDiff.comp (hC.fderiv_right le_rfl)

/-- **`∂̄_j` is additive.** -/
theorem dzbarAt_add {F G : (Fin n → ℂ) → ℂ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (j : Fin n) (z : Fin n → ℂ) :
    dzbarAt (fun x => F x + G x) j z = dzbarAt F j z + dzbarAt G j z := by
  have hFG : Differentiable ℝ fun x => F x + G x := fun x => (hF x).add (hG x)
  have hadd : fderiv ℝ (fun x => F x + G x) z = fderiv ℝ F z + fderiv ℝ G z :=
    ((hF z).hasFDerivAt.add (hG z).hasFDerivAt).fderiv
  rw [dzbarAt_eq_functional hFG j z, dzbarAt_eq_functional hF j z,
    dzbarAt_eq_functional hG j z, hadd, map_add]

/-- **`∂̄_j` preserves compact support.** -/
theorem hasCompactSupport_dzbarAt {G : (Fin n → ℂ) → ℂ} (hd : Differentiable ℝ G)
    (hcs : HasCompactSupport G) (j : Fin n) : HasCompactSupport (dzbarAt G j) := by
  have heq : dzbarAt G j = (fun A => dzbarFunctional j A) ∘ fderiv ℝ G := by
    funext z
    exact dzbarAt_eq_functional hd j z
  rw [heq]
  exact (hcs.fderiv ℝ).comp_left (map_zero _)

end Calculus


section PiCauchy

variable {n : ℕ}

/-- Far from the origin in the integration variable, the argument leaves any fixed ball. -/
theorem pi_far_norm (k : Fin n) (y₀ : Fin n → ℂ) (S : ℝ) :
    ∀ (w : ℂ), w ∉ Metric.ball (0 : ℂ) (S + ‖y₀‖ + 2) → ∀ y ∈ Metric.ball y₀ 1,
      S < ‖y - (Pi.single k w : Fin n → ℂ)‖ := by
  intro w hw y hy
  simp only [Metric.mem_ball, dist_zero_right, not_lt] at hw
  simp only [Metric.mem_ball, dist_eq_norm] at hy
  have hyn : ‖y‖ ≤ ‖y₀‖ + 1 := by
    have := norm_sub_norm_le y y₀
    linarith [le_of_lt hy]
  have hn : ‖(Pi.single k w : Fin n → ℂ)‖ - ‖y‖ ≤ ‖y - (Pi.single k w : Fin n → ℂ)‖ := by
    rw [← norm_neg (y - (Pi.single k w : Fin n → ℂ))]
    simpa [neg_sub] using norm_sub_norm_le (Pi.single k w : Fin n → ℂ) y
  rw [norm_pi_single (n := n) k w] at hn
  linarith

/-- The translated argument is continuous in the integration variable. -/
theorem pi_continuous_arg (k : Fin n) (y : Fin n → ℂ) :
    Continuous fun w : ℂ => y - (Pi.single k w : Fin n → ℂ) :=
  continuous_const.sub (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) k).continuous

theorem pi_measF {G : (Fin n → ℂ) → ℂ} (hd : Differentiable ℝ G) (k : Fin n) (y : Fin n → ℂ) :
    MeasureTheory.AEStronglyMeasurable
      (fun w : ℂ => G (y - Pi.single k w) / w) MeasureTheory.volume :=
  ((hd.continuous.comp (pi_continuous_arg k y)).measurable.mul
    measurable_inv).aestronglyMeasurable

theorem pi_measF' {G : (Fin n → ℂ) → ℂ} (hC : ContDiff ℝ 1 G) (k : Fin n) (y : Fin n → ℂ) :
    MeasureTheory.AEStronglyMeasurable
      (fun w : ℂ => (w⁻¹ : ℂ) • fderiv ℝ G (y - Pi.single k w)) MeasureTheory.volume :=
  (measurable_inv.smul
    (((hC.continuous_fderiv one_ne_zero).comp (pi_continuous_arg k y)).measurable)).aestronglyMeasurable

theorem pi_boundInt (M T : ℝ) :
    MeasureTheory.Integrable
      (fun w : ℂ => M * Set.indicator (Metric.ball (0 : ℂ) T) (fun w => ‖w‖⁻¹) w)
      MeasureTheory.volume := by
  refine MeasureTheory.Integrable.const_mul ?_ M
  rw [MeasureTheory.integrable_indicator_iff measurableSet_ball]
  exact integrableOn_norm_inv_ball T

theorem pi_Fint {G : (Fin n → ℂ) → ℂ} (hd : Differentiable ℝ G) {S M₀ : ℝ}
    (hgS : ∀ x : Fin n → ℂ, S < ‖x‖ → G x = 0) (hM₀ : ∀ x : Fin n → ℂ, ‖G x‖ ≤ M₀)
    (k : Fin n) (y₀ : Fin n → ℂ) :
    MeasureTheory.Integrable
      (fun w : ℂ => G (y₀ - Pi.single k w) / w) MeasureTheory.volume := by
  refine MeasureTheory.Integrable.mono'
    (((MeasureTheory.integrable_indicator_iff
      (measurableSet_ball (x := (0 : ℂ)) (ε := S + ‖y₀‖ + 2))).2
      (integrableOn_norm_inv_ball _)).const_mul (max M₀ 0))
    (pi_measF hd k y₀) ?_
  refine Filter.Eventually.of_forall (fun w => ?_)
  by_cases hw : w ∈ Metric.ball (0 : ℂ) (S + ‖y₀‖ + 2)
  · rw [Set.indicator_of_mem hw, norm_div, div_eq_mul_inv]
    gcongr
    exact le_trans (hM₀ _) (le_max_left _ _)
  · rw [Set.indicator_of_notMem hw,
      hgS _ (pi_far_norm k y₀ S w hw y₀ (Metric.mem_ball_self one_pos))]
    simp

theorem pi_bound {G : (Fin n → ℂ) → ℂ} {S M : ℝ}
    (hdS : ∀ x : Fin n → ℂ, S < ‖x‖ → fderiv ℝ G x = 0)
    (hM : ∀ x : Fin n → ℂ, ‖fderiv ℝ G x‖ ≤ M) (k : Fin n) (y₀ : Fin n → ℂ) :
    ∀ᵐ w : ℂ, ∀ y ∈ Metric.ball y₀ 1,
      ‖(w⁻¹ : ℂ) • fderiv ℝ G (y - Pi.single k w)‖
        ≤ M * Set.indicator (Metric.ball (0 : ℂ) (S + ‖y₀‖ + 2)) (fun w => ‖w‖⁻¹) w := by
  refine Filter.Eventually.of_forall (fun w => ?_)
  intro y hy
  by_cases hw : w ∈ Metric.ball (0 : ℂ) (S + ‖y₀‖ + 2)
  · rw [Set.indicator_of_mem hw, norm_smul, norm_inv, mul_comm]
    gcongr
    exact hM _
  · rw [Set.indicator_of_notMem hw, hdS _ (pi_far_norm k y₀ S w hw y hy)]
    rw [norm_smul, norm_zero, mul_zero, mul_zero]

theorem pi_diff {G : (Fin n → ℂ) → ℂ} (hd : Differentiable ℝ G) (k : Fin n) (y₀ : Fin n → ℂ) :
    ∀ᵐ w : ℂ, ∀ y ∈ Metric.ball y₀ 1,
      HasFDerivAt (fun y : Fin n → ℂ => G (y - Pi.single k w) / w)
        ((w⁻¹ : ℂ) • fderiv ℝ G (y - Pi.single k w)) y := by
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2
    (MeasureTheory.measure_singleton (0 : ℂ))] with w _ y _
  have h1 : HasFDerivAt (fun y : Fin n → ℂ => G (y - Pi.single k w))
      (fderiv ℝ G (y - Pi.single k w)) y := by
    have h2 := (hd (y - Pi.single k w)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).sub_const (Pi.single k w))
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2
  have heq : (fun y : Fin n → ℂ => G (y - Pi.single k w) / w)
      = fun y : Fin n → ℂ => (w⁻¹ : ℂ) • G (y - Pi.single k w) := by
    funext s
    rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact h1.const_smul (w⁻¹ : ℂ)


set_option maxHeartbeats 4000000 in
/-- **Differentiation of the coordinatewise Cauchy transform under the integral sign, in all
directions at once.**  Every side condition is a separate lemma above, so this is a single
application of the dominated-derivative theorem. -/
theorem hasFDerivAt_piCauchyIntegral {G : (Fin n → ℂ) → ℂ} (hC : ContDiff ℝ 1 G)
    (hcs : HasCompactSupport G) (k : Fin n) (y₀ : Fin n → ℂ) :
    HasFDerivAt (fun y : Fin n → ℂ => ∫ w : ℂ, G (y - Pi.single k w) / w)
      (∫ w : ℂ, (w⁻¹ : ℂ) • fderiv ℝ G (y₀ - Pi.single k w)) y₀ := by
  obtain ⟨S, hS0, hgS, hdS⟩ := exists_radius_pi hcs
  obtain ⟨M, hM⟩ := (hcs.fderiv ℝ).exists_bound_of_continuous (hC.continuous_fderiv one_ne_zero)
  obtain ⟨M₀, hM₀⟩ := hcs.exists_bound_of_continuous (hC.differentiable one_ne_zero).continuous
  have hd : Differentiable ℝ G := hC.differentiable one_ne_zero
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.ball_mem_nhds y₀ one_pos)
    (Filter.Eventually.of_forall (fun y => pi_measF hd k y))
    (pi_Fint hd hgS hM₀ k y₀)
    (pi_measF' hC k y₀)
    (pi_bound hdS hM k y₀)
    (pi_boundInt M (S + ‖y₀‖ + 2))
    (pi_diff hd k y₀)

end PiCauchy


section BanachTransform

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The coordinatewise Cauchy transform of a Banach-valued function. -/
noncomputable def piCauchyB (G : (Fin n → ℂ) → E) (k : Fin n) (y : Fin n → ℂ) : E :=
  ∫ w : ℂ, (w⁻¹ : ℂ) • G (y - Pi.single k w)

omit [CompleteSpace E] in
theorem piB_measF {G : (Fin n → ℂ) → E} (hcont : Continuous G) (k : Fin n) (y : Fin n → ℂ) :
    MeasureTheory.AEStronglyMeasurable
      (fun w : ℂ => (w⁻¹ : ℂ) • G (y - Pi.single k w)) MeasureTheory.volume :=
  (measurable_inv.aestronglyMeasurable).smul
    ((hcont.comp (pi_continuous_arg k y)).aestronglyMeasurable)

omit [CompleteSpace E] in
theorem piB_Fint {G : (Fin n → ℂ) → E} (hcont : Continuous G) {S M₀ : ℝ}
    (hgS : ∀ x : Fin n → ℂ, S < ‖x‖ → G x = 0) (hM₀ : ∀ x : Fin n → ℂ, ‖G x‖ ≤ M₀)
    (k : Fin n) (y₀ : Fin n → ℂ) :
    MeasureTheory.Integrable
      (fun w : ℂ => (w⁻¹ : ℂ) • G (y₀ - Pi.single k w)) MeasureTheory.volume := by
  refine MeasureTheory.Integrable.mono'
    (((MeasureTheory.integrable_indicator_iff
      (measurableSet_ball (x := (0 : ℂ)) (ε := S + ‖y₀‖ + 2))).2
      (integrableOn_norm_inv_ball _)).const_mul (max M₀ 0))
    (piB_measF hcont k y₀) ?_
  refine Filter.Eventually.of_forall (fun w => ?_)
  by_cases hw : w ∈ Metric.ball (0 : ℂ) (S + ‖y₀‖ + 2)
  · rw [Set.indicator_of_mem hw, norm_smul, norm_inv, mul_comm]
    gcongr
    exact le_trans (hM₀ _) (le_max_left _ _)
  · rw [Set.indicator_of_notMem hw,
      hgS _ (pi_far_norm k y₀ S w hw y₀ (Metric.mem_ball_self one_pos)),
      norm_smul, norm_zero, mul_zero, mul_zero]

omit [CompleteSpace E] in
theorem piB_bound {G : (Fin n → ℂ) → E} {S M : ℝ}
    (hgS : ∀ x : Fin n → ℂ, S < ‖x‖ → G x = 0) (hM : ∀ x : Fin n → ℂ, ‖G x‖ ≤ M)
    (k : Fin n) (y₀ : Fin n → ℂ) :
    ∀ᵐ w : ℂ, ∀ y ∈ Metric.ball y₀ 1,
      ‖(w⁻¹ : ℂ) • G (y - Pi.single k w)‖
        ≤ M * Set.indicator (Metric.ball (0 : ℂ) (S + ‖y₀‖ + 2)) (fun w => ‖w‖⁻¹) w := by
  refine Filter.Eventually.of_forall (fun w => ?_)
  intro y hy
  by_cases hw : w ∈ Metric.ball (0 : ℂ) (S + ‖y₀‖ + 2)
  · rw [Set.indicator_of_mem hw, norm_smul, norm_inv, mul_comm]
    gcongr
    exact hM _
  · rw [Set.indicator_of_notMem hw, hgS _ (pi_far_norm k y₀ S w hw y hy),
      norm_smul, norm_zero, mul_zero, mul_zero]

omit [CompleteSpace E] in
set_option maxHeartbeats 2000000 in
/-- **The Banach-valued coordinatewise Cauchy transform of a continuous compactly supported
function is continuous.** -/
theorem continuous_piCauchyB {G : (Fin n → ℂ) → E} (hcont : Continuous G)
    (hcs : HasCompactSupport G) (k : Fin n) : Continuous (piCauchyB G k) := by
  obtain ⟨S, hS⟩ := hcs.isBounded.subset_closedBall (0 : Fin n → ℂ)
  obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuous hcont
  have hgS : ∀ x : Fin n → ℂ, S < ‖x‖ → G x = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport (fun hc => ?_)
    have := hS hc
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  refine continuous_iff_continuousAt.2 (fun y₀ => ?_)
  refine MeasureTheory.continuousAt_of_dominated
    (F := fun y w => (w⁻¹ : ℂ) • G (y - Pi.single k w))
    (bound := fun w : ℂ => M * Set.indicator (Metric.ball (0 : ℂ) (S + ‖y₀‖ + 2))
      (fun w => ‖w‖⁻¹) w)
    (Filter.Eventually.of_forall (fun y => piB_measF hcont k y))
    (Filter.eventually_iff_exists_mem.2
      ⟨Metric.ball y₀ 1, Metric.ball_mem_nhds y₀ one_pos,
        fun y hy => (piB_bound hgS hM k y₀).mono (fun w hw => hw y hy)⟩)
    (pi_boundInt M (S + ‖y₀‖ + 2))
    (Filter.Eventually.of_forall (fun w => (continuous_const.smul
      (hcont.comp (by fun_prop))).continuousAt))


omit [CompleteSpace E] in
theorem piB_diff {G : (Fin n → ℂ) → E} (hd : Differentiable ℝ G) (k : Fin n) (y₀ : Fin n → ℂ) :
    ∀ᵐ w : ℂ, ∀ y ∈ Metric.ball y₀ 1,
      HasFDerivAt (fun y : Fin n → ℂ => (w⁻¹ : ℂ) • G (y - Pi.single k w))
        ((w⁻¹ : ℂ) • fderiv ℝ G (y - Pi.single k w)) y := by
  refine Filter.Eventually.of_forall (fun w => ?_)
  intro y _
  have h1 : HasFDerivAt (fun y : Fin n → ℂ => G (y - Pi.single k w))
      (fderiv ℝ G (y - Pi.single k w)) y := by
    have h2 := (hd (y - Pi.single k w)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).sub_const (Pi.single k w))
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2
  exact h1.const_smul (w⁻¹ : ℂ)

omit [CompleteSpace E] in
set_option maxHeartbeats 4000000 in
/-- **The differential of the Banach-valued coordinatewise Cauchy transform is the transform of the
differential.** -/
theorem hasFDerivAt_piCauchyB {G : (Fin n → ℂ) → E} (hC : ContDiff ℝ 1 G)
    (hcs : HasCompactSupport G) (k : Fin n) (y₀ : Fin n → ℂ) :
    HasFDerivAt (piCauchyB G k) (piCauchyB (fderiv ℝ G) k y₀) y₀ := by
  obtain ⟨S, hS⟩ := hcs.isBounded.subset_closedBall (0 : Fin n → ℂ)
  obtain ⟨S', hS'⟩ := (hcs.fderiv ℝ).isBounded.subset_closedBall (0 : Fin n → ℂ)
  obtain ⟨M, hM⟩ := (hcs.fderiv ℝ).exists_bound_of_continuous (hC.continuous_fderiv one_ne_zero)
  obtain ⟨M₀, hM₀⟩ := hcs.exists_bound_of_continuous (hC.differentiable one_ne_zero).continuous
  have hd : Differentiable ℝ G := hC.differentiable one_ne_zero
  have hgS : ∀ x : Fin n → ℂ, S < ‖x‖ → G x = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport (fun hc => ?_)
    have := hS hc
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have hgS' : ∀ x : Fin n → ℂ, S' < ‖x‖ → fderiv ℝ G x = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport (fun hc => ?_)
    have := hS' hc
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.ball_mem_nhds y₀ one_pos)
    (Filter.Eventually.of_forall (fun y => piB_measF hd.continuous k y))
    (piB_Fint hd.continuous hgS hM₀ k y₀)
    (piB_measF (hC.continuous_fderiv one_ne_zero) k y₀)
    (piB_bound hgS' hM k y₀)
    (pi_boundInt M (S' + ‖y₀‖ + 2))
    (piB_diff hd k y₀)


/-- **The Banach-valued coordinatewise Cauchy transform preserves smoothness.**  The differential
of the transform is the transform of the differential, so the statement propagates by induction on
the order. -/
theorem contDiff_piCauchyB (k : Fin n) :
    ∀ (m : ℕ) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F]
      (G : (Fin n → ℂ) → F), ContDiff ℝ m G → HasCompactSupport G →
      ContDiff ℝ m (piCauchyB G k) := by
  intro m
  induction m with
  | zero =>
      intro F _ _ G hC hcs
      rw [Nat.cast_zero, contDiff_zero] at hC ⊢
      exact continuous_piCauchyB hC hcs k
  | succ m ih =>
      intro F _ _ G hC hcs
      have hC1 : ContDiff ℝ 1 G := hC.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
      have hsucc : ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by push_cast; ring
      have hfder : ContDiff ℝ (m : WithTop ℕ∞) (fderiv ℝ G) := by
        rw [hsucc] at hC
        exact (contDiff_succ_iff_fderiv.1 hC).2.2
      have hIH : ContDiff ℝ (m : WithTop ℕ∞) (piCauchyB (fderiv ℝ G) k) :=
        ih _ hfder (hcs.fderiv ℝ)
      have hfd : fderiv ℝ (piCauchyB G k) = piCauchyB (fderiv ℝ G) k := by
        funext y
        exact (hasFDerivAt_piCauchyB hC1 hcs k y).fderiv
      rw [hsucc, contDiff_succ_iff_fderiv]
      refine ⟨fun y => (hasFDerivAt_piCauchyB hC1 hcs k y).differentiableAt, ?_, ?_⟩
      · intro htop
        exact absurd htop (by exact_mod_cast (WithTop.natCast_ne_top m))
      · rw [hfd]
        exact hIH


/-- `T_k` preserves `C^∞`. -/
theorem contDiff_infty_piCauchyB (k : Fin n) {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (G : (Fin n → ℂ) → F)
    (hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (hcs : HasCompactSupport G) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (piCauchyB G k) :=
  contDiff_infty.2 fun m => contDiff_piCauchyB k m G (contDiff_infty.1 hC m) hcs

end BanachTransform

section SmoothSliceSolution

variable {n : ℕ}

/-- The scalar coordinatewise Cauchy transform is `π⁻¹` times the Banach-valued one. -/
theorem dbarSliceSolution_eq_piCauchyB (G : (Fin n → ℂ) → ℂ) (k : Fin n) (y : Fin n → ℂ) :
    dbarSliceSolution G k y = ((Real.pi)⁻¹ : ℝ) • piCauchyB G k y := by
  rw [dbarSliceSolution_eq_integral, piCauchyB]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
  show G (y - Pi.single k w) / w = (w⁻¹ : ℂ) • G (y - Pi.single k w)
  rw [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- **The coordinatewise Cauchy transform of a smooth compactly supported source is smooth.** -/
theorem contDiff_infty_dbarSliceSolution (G : (Fin n → ℂ) → ℂ) (k : Fin n)
    (hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (hcs : HasCompactSupport G) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dbarSliceSolution G k) := by
  have heq : dbarSliceSolution G k = fun y => ((Real.pi)⁻¹ : ℝ) • piCauchyB G k y := by
    funext y
    exact dbarSliceSolution_eq_piCauchyB G k y
  rw [heq]
  exact (contDiff_infty_piCauchyB k G hC hcs).const_smul _

end SmoothSliceSolution




section Slab

variable {n : ℕ}

/-- Compact support gives slab support in every coordinate: if `G` vanishes outside a ball of
radius `S`, it vanishes whenever a single coordinate exceeds `S`. -/
theorem slab_of_compactSupport {G : (Fin n → ℂ) → ℂ} {S : ℝ} (k : Fin n)
    (hgS : ∀ x : Fin n → ℂ, S < ‖x‖ → G x = 0) :
    ∀ x : Fin n → ℂ, S < ‖x k‖ → G x = 0 :=
  fun x hx => hgS x (lt_of_lt_of_le hx (norm_coord_le x k))

/-- **The far-field estimate in slab form.**  Only the `k`-th coordinate of the integration point
moves, so the estimate needs only the `k`-th coordinate of the base point. -/
theorem slab_far_norm (k : Fin n) (y₀ : Fin n → ℂ) (S : ℝ) :
    ∀ (w : ℂ), w ∉ Metric.ball (0 : ℂ) (S + ‖y₀ k‖ + 2) → ∀ y ∈ Metric.ball y₀ 1,
      S < ‖(y - (Pi.single k w : Fin n → ℂ)) k‖ := by
  intro w hw y hy
  simp only [Metric.mem_ball, dist_zero_right, not_lt] at hw
  simp only [Metric.mem_ball, dist_eq_norm] at hy
  have hcoord : (y - (Pi.single k w : Fin n → ℂ)) k = y k - w := by simp
  have hyk : ‖y k‖ ≤ ‖y₀ k‖ + 1 := by
    have h1 : ‖y k - y₀ k‖ ≤ ‖y - y₀‖ := by
      have := norm_coord_le (y - y₀) k
      simpa using this
    have h2 := norm_sub_norm_le (y k) (y₀ k)
    linarith [le_of_lt hy]
  have hn : ‖w‖ - ‖y k‖ ≤ ‖y k - w‖ := by
    rw [← norm_neg (y k - w)]
    simpa [neg_sub] using norm_sub_norm_le w (y k)
  rw [hcoord]
  linarith

/-- The slab far-field estimate for the `j ≠ k` slice, where the `k`-th coordinate of the
integration point is `y_k − w` regardless of the `j`-th parameter. -/
theorem slab_far_slice {j k : Fin n} (hjk : j ≠ k) (y : Fin n → ℂ) (S : ℝ) :
    ∀ (w : ℂ), w ∉ Metric.ball (0 : ℂ) (S + ‖y k‖ + 2) → ∀ s : ℂ,
      S < ‖(Function.update (Function.update y k (y k - w)) j s) k‖ := by
  intro w hw s
  simp only [Metric.mem_ball, dist_zero_right, not_lt] at hw
  have hk : (Function.update (Function.update y k (y k - w)) j s) k = y k - w := by
    rw [Function.update_of_ne (Ne.symm hjk), Function.update_self]
  have hn : ‖w‖ - ‖y k‖ ≤ ‖y k - w‖ := by
    rw [← norm_neg (y k - w)]
    simpa [neg_sub] using norm_sub_norm_le w (y k)
  rw [hk]
  linarith


/-- Slab support gives compactly supported slices in the `k`-th coordinate, uniformly in the other
coordinates.  This is the hypothesis the Dolbeault induction actually supplies, since its cutoff is
a function of the `k`-th coordinate alone. -/
theorem hasCompactSupport_slice_of_slab {G : (Fin n → ℂ) → ℂ} {S : ℝ} {k : Fin n}
    (hgS : ∀ x : Fin n → ℂ, S < ‖x k‖ → G x = 0) (z : Fin n → ℂ) :
    HasCompactSupport (fun t : ℂ => G (Function.update z k t)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) S) (fun t ht => ?_)
  refine hgS _ ?_
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at ht
  rwa [Function.update_self]

/-- **Solving `∂̄_k U = G` for a slab-supported source.**  The cutoff of the Dolbeault induction is a
function of the `k`-th coordinate only, so the source is not compactly supported; what it does have
is compactly supported slices in the `k`-th coordinate, and that is all the transform needs. -/
theorem dzbarAt_dbarSliceSolution_of_slab {G : (Fin n → ℂ) → ℂ} {S : ℝ} {k : Fin n}
    (hC : ContDiff ℝ 1 G) (hgS : ∀ x : Fin n → ℂ, S < ‖x k‖ → G x = 0) (z : Fin n → ℂ) :
    dzbarAt (dbarSliceSolution G k) k z = G z :=
  dzbarAt_dbarSliceSolution G k
    (fun y => hC.comp (contDiff_updateEmbed k y))
    (fun y => hasCompactSupport_slice_of_slab hgS y) z


/-- `∂̄` is homogeneous under a constant real scalar. -/
theorem dzbar_const_smul (c : ℝ) (g : ℂ → ℂ) (z : ℂ) :
    dzbar (fun t => (c : ℝ) • g t) z = (c : ℝ) • dzbar g z := by
  by_cases hg : DifferentiableAt ℝ g z
  · have h1 : HasFDerivAt (fun t => (c : ℝ) • g t) (c • fderiv ℝ g z) z :=
      hg.hasFDerivAt.const_smul c
    rw [dzbar_eq_of_hasFDerivAt h1, dzbar, wirtingerAntihol, wirtingerAntihol]
    simp only [smul_apply, Complex.real_smul]
    ring
  · have h2 : ¬ DifferentiableAt ℝ (fun t => (c : ℝ) • g t) z ∨ c = 0 := by
      by_cases hc : c = 0
      · exact Or.inr hc
      · refine Or.inl (fun hd => hg ?_)
        have h3 := hd.const_smul (c⁻¹ : ℝ)
        have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
        have h4 : ((c⁻¹ : ℝ) • fun t => (c : ℝ) • g t) = g := by
          funext t
          simp only [Pi.smul_apply, Complex.real_smul, Complex.ofReal_inv]
          rw [← mul_assoc, inv_mul_cancel₀ hcC, one_mul]
        rwa [h4] at h3
    rcases h2 with h2 | h2
    · rw [dzbar, dzbar, fderiv_zero_of_not_differentiableAt hg,
        fderiv_zero_of_not_differentiableAt h2]
      simp [wirtingerAntihol]
    · subst h2
      simp [dzbar, wirtingerAntihol]

/-- **A cutoff in the `k`-th coordinate alone commutes with `∂̄_j` for `j ≠ k`.**  This is why the
Dolbeault induction cuts off in one variable only: the cutoff is constant along every other
coordinate line, so it passes through the corresponding Wirtinger derivative. -/
theorem dzbarAt_slabCutoff_smul {f : (Fin n → ℂ) → ℂ} {j k : Fin n} (hjk : j ≠ k)
    (chi : ℂ → ℝ) (z : Fin n → ℂ) :
    dzbarAt (fun x => (chi (x k) : ℝ) • f x) j z = (chi (z k) : ℝ) • dzbarAt f j z := by
  have hslice : dbarSlice (fun x => (chi (x k) : ℝ) • f x) j z
      = fun t => (chi (z k) : ℝ) • dbarSlice f j z t := by
    funext t
    rw [dbarSlice, dbarSlice, Function.update_of_ne (Ne.symm hjk)]
  rw [dzbarAt, hslice, dzbar_const_smul, dzbarAt]


/-- **Vanishing along the `k`-th coordinate line kills the transported derivative.**  This is the
mechanism of the Dolbeault induction: `T_k` is nonlocal only along the `k`-th line, and the other
coordinates never move, so `∂̄_j T_k(F)` vanishes at a point as soon as `∂̄_j F` vanishes on the whole
`k`-line through it.  On a polydisc that hypothesis is exactly what `∂̄`-closedness supplies. -/
theorem dzbarAt_dbarSliceSolution_eq_zero {F : (Fin n → ℂ) → ℂ} {S M M₀ : ℝ}
    {j k : Fin n} (hjk : j ≠ k) (hC : ContDiff ℝ 1 F)
    (hgS : ∀ x : Fin n → ℂ, S < ‖x k‖ → F x = 0)
    (hdS : ∀ x : Fin n → ℂ, S < ‖x k‖ → fderiv ℝ F x = 0)
    (hM : ∀ x : Fin n → ℂ, ‖fderiv ℝ F x‖ ≤ M) (hM₀ : ∀ x : Fin n → ℂ, ‖F x‖ ≤ M₀)
    (z : Fin n → ℂ) (hvan : ∀ t : ℂ, dzbarAt F j (Function.update z k t) = 0) :
    dzbarAt (dbarSliceSolution F k) j z = 0 := by
  rw [dzbarAt_dbarSliceSolution_of_ne hjk hC hgS hdS hM hM₀ z, dbarSliceSolution, dbarSolution]
  have hzero : (fun w : ℂ => (fun t => dzbarAt F j (Function.update z k t)) (z k - w) / w)
      = fun _ : ℂ => (0 : ℂ) := by
    funext w
    show dzbarAt F j (Function.update z k (z k - w)) / w = 0
    rw [hvan (z k - w), zero_div]
  rw [hzero]
  simp


/-- **One step of the Dolbeault–Grothendieck induction.**  The coordinatewise Cauchy transform of
the top coefficient solves the equation in the top direction and leaves untouched every direction
along which the coefficient is `∂̄`-closed on the whole `k`-line.  The two clauses are exactly what
the induction consumes: the first removes the direction `k`, the second says no direction above `k`
is created. -/
theorem dbar_induction_step {F : (Fin n → ℂ) → ℂ} {S M M₀ : ℝ} {k : Fin n}
    (hC : ContDiff ℝ 1 F)
    (hgS : ∀ x : Fin n → ℂ, S < ‖x k‖ → F x = 0)
    (hdS : ∀ x : Fin n → ℂ, S < ‖x k‖ → fderiv ℝ F x = 0)
    (hM : ∀ x : Fin n → ℂ, ‖fderiv ℝ F x‖ ≤ M) (hM₀ : ∀ x : Fin n → ℂ, ‖F x‖ ≤ M₀) :
    ∃ U : (Fin n → ℂ) → ℂ,
      (∀ z, dzbarAt U k z = F z) ∧
      ∀ j, j ≠ k → ∀ z : Fin n → ℂ,
        (∀ t : ℂ, dzbarAt F j (Function.update z k t) = 0) → dzbarAt U j z = 0 :=
  ⟨dbarSliceSolution F k,
    fun z => dzbarAt_dbarSliceSolution_of_slab hC hgS z,
    fun _ hjk z hvan => dzbarAt_dbarSliceSolution_eq_zero hjk hC hgS hdS hM hM₀ z hvan⟩

end Slab


section Polydisc

variable {n : ℕ}

/-- A polydisc: the product of coordinate discs. -/
def polydisc (c : Fin n → ℂ) (r : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ i, z i ∈ Metric.ball (c i) (r i)}

theorem mem_polydisc_iff {c : Fin n → ℂ} {r : Fin n → ℝ} {z : Fin n → ℂ} :
    z ∈ polydisc c r ↔ ∀ i, z i ∈ Metric.ball (c i) (r i) := Iff.rfl

/-- A polydisc grows with its radii. -/
theorem polydisc_mono {c : Fin n → ℂ} {r r' : Fin n → ℝ} (h : ∀ i, r' i ≤ r i) :
    polydisc c r' ⊆ polydisc c r := by
  intro z hz i
  exact Metric.ball_subset_ball (h i) (hz i)

/-- **A polydisc is closed under moving one coordinate inside its own disc.**  This is the property
that makes the Dolbeault induction work: the `k`-line through a point of the polydisc, restricted to
the `k`-th disc, stays inside the polydisc, which is exactly the hypothesis of
`dzbarAt_dbarSliceSolution_eq_zero`. -/
theorem update_mem_polydisc {c : Fin n → ℂ} {r : Fin n → ℝ} {z : Fin n → ℂ} {k : Fin n}
    (hz : z ∈ polydisc c r) {t : ℂ} (ht : t ∈ Metric.ball (c k) (r k)) :
    Function.update z k t ∈ polydisc c r := by
  intro i
  by_cases hik : i = k
  · subst hik
    rwa [Function.update_self]
  · rw [Function.update_of_ne hik]
    exact hz i


/-- A function vanishing near a point has vanishing `∂̄_j` there. -/
theorem dzbarAt_eq_zero_of_eventually_zero {g : (Fin n → ℂ) → ℂ} {j : Fin n} {z : Fin n → ℂ}
    (h : ∀ᶠ y in nhds z, g y = 0) : dzbarAt g j z = 0 := by
  have hz : (fun s : ℂ => Function.update z j s) (z j) = z := Function.update_eq_self j z
  have hcont : Filter.Tendsto (fun s : ℂ => Function.update z j s) (nhds (z j)) (nhds z) := by
    have hc : ContinuousAt (fun s : ℂ => Function.update z j s) (z j) :=
      ((contDiff_updateEmbed j z).continuous).continuousAt
    have : Filter.Tendsto (fun s : ℂ => Function.update z j s) (nhds (z j))
        (nhds ((fun s : ℂ => Function.update z j s) (z j))) := hc
    rwa [hz] at this
  have hs : (dbarSlice g j z) =ᶠ[nhds (z j)] (fun _ => (0 : ℂ)) := hcont.eventually h
  rw [dzbarAt, dzbar, hs.fderiv_eq]
  simp [wirtingerAntihol]

/-- On a polydisc, `∂̄`-closedness plus vanishing above `k` makes `∂̄_j f_k` vanish on the whole
`k`-line through any point of the polydisc, once the line is cut down to the `k`-th disc.  This is
the hypothesis `dzbarAt_dbarSliceSolution_eq_zero` consumes. -/
theorem dzbarAt_vanishes_on_line {f : Fin n → (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : Fin n → ℝ}
    {j k : Fin n} (hclosed : ∀ z ∈ polydisc c r, dzbarAt (f k) j z = dzbarAt (f j) k z)
    (hfj : ∀ z ∈ polydisc c r, f j z = 0)
    (hopen : IsOpen (polydisc c r))
    {z : Fin n → ℂ} (hz : z ∈ polydisc c r) {t : ℂ} (ht : t ∈ Metric.ball (c k) (r k)) :
    dzbarAt (f k) j (Function.update z k t) = 0 := by
  have hmem : Function.update z k t ∈ polydisc c r := update_mem_polydisc hz ht
  rw [hclosed _ hmem]
  refine dzbarAt_eq_zero_of_eventually_zero ?_
  exact Filter.eventually_of_mem (hopen.mem_nhds hmem) (fun y hy => hfj y hy)


/-- A polydisc is open. -/
theorem isOpen_polydisc (c : Fin n → ℂ) (r : Fin n → ℝ) : IsOpen (polydisc c r) := by
  have : polydisc c r = ⋂ i : Fin n, (fun z : Fin n → ℂ => z i) ⁻¹' Metric.ball (c i) (r i) := by
    ext z
    simp [polydisc, Set.mem_iInter]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    (Metric.isOpen_ball).preimage (continuous_apply i)

/-- **The cut-off source is `∂̄_j`-closed along the whole `k`-line.**  Off the support of the cutoff
the product vanishes; on it the point stays in the polydisc, where `∂̄`-closedness applies.  This is
the hypothesis of `dzbarAt_dbarSliceSolution_eq_zero`, now discharged from polydisc data. -/
theorem dzbarAt_cutoff_vanishes_on_line {f : Fin n → (Fin n → ℂ) → ℂ} {c : Fin n → ℂ}
    {r : Fin n → ℝ} {j k : Fin n} (hjk : j ≠ k)
    (hclosed : ∀ z ∈ polydisc c r, dzbarAt (f k) j z = dzbarAt (f j) k z)
    (hfj : ∀ z ∈ polydisc c r, f j z = 0)
    (chi : ℂ → ℝ) (hchi : ∀ t : ℂ, chi t ≠ 0 → t ∈ Metric.ball (c k) (r k))
    {z : Fin n → ℂ} (hz : z ∈ polydisc c r) (t : ℂ) :
    dzbarAt (fun x => (chi (x k) : ℝ) • f k x) j (Function.update z k t) = 0 := by
  rw [dzbarAt_slabCutoff_smul hjk chi, Function.update_self]
  by_cases ht : chi t = 0
  · rw [ht, zero_smul]
  · rw [dzbarAt_vanishes_on_line hclosed hfj (isOpen_polydisc c r) hz (hchi t ht), smul_zero]

/-- The cut-off source is slab supported in the `k`-th coordinate. -/
theorem cutoff_slab_support {g : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : Fin n → ℝ} {k : Fin n}
    (chi : ℂ → ℝ) (hchi : ∀ t : ℂ, chi t ≠ 0 → t ∈ Metric.ball (c k) (r k))
    (x : Fin n → ℂ) (hx : ‖c k‖ + r k < ‖x k‖) :
    (fun y => (chi (y k) : ℝ) • g y) x = 0 := by
  have hnot : chi (x k) = 0 := by
    by_contra hne
    have hmem := hchi (x k) hne
    simp only [Metric.mem_ball, Complex.dist_eq] at hmem
    have := norm_sub_norm_le (x k) (c k)
    linarith
  simp only
  rw [hnot, zero_smul]


/-- **The Dolbeault–Grothendieck induction step on a polydisc.**  Cutting the top coefficient off in
its own coordinate makes it slab supported, so the coordinatewise Cauchy transform applies; the
cutoff is invisible on the polydisc, where it is one, and it kills the part of every coordinate line
that leaves the polydisc, so no direction along which the datum vanishes is disturbed. -/
theorem dbar_polydisc_step {f : Fin n → (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r r' : Fin n → ℝ}
    {k : Fin n} {S M M₀ : ℝ} (hr : ∀ i, r' i ≤ r i) (chi : ℂ → ℝ)
    (hchi : ∀ t : ℂ, chi t ≠ 0 → t ∈ Metric.ball (c k) (r k))
    (hone : ∀ z ∈ polydisc c r', chi (z k) = 1)
    (hCF : ContDiff ℝ 1 (fun x : Fin n → ℂ => (chi (x k) : ℝ) • f k x))
    (hgS : ∀ x : Fin n → ℂ, S < ‖x k‖ → (chi (x k) : ℝ) • f k x = 0)
    (hdS : ∀ x : Fin n → ℂ, S < ‖x k‖ →
      fderiv ℝ (fun y : Fin n → ℂ => (chi (y k) : ℝ) • f k y) x = 0)
    (hM : ∀ x : Fin n → ℂ, ‖fderiv ℝ (fun y : Fin n → ℂ => (chi (y k) : ℝ) • f k y) x‖ ≤ M)
    (hM₀ : ∀ x : Fin n → ℂ, ‖(chi (x k) : ℝ) • f k x‖ ≤ M₀)
    (hclosed : ∀ j : Fin n, ∀ z ∈ polydisc c r, dzbarAt (f k) j z = dzbarAt (f j) k z) :
    ∃ U : (Fin n → ℂ) → ℂ,
      (∀ z ∈ polydisc c r', dzbarAt U k z = f k z) ∧
      ∀ j : Fin n, j ≠ k → (∀ y ∈ polydisc c r, f j y = 0) →
        ∀ z ∈ polydisc c r', dzbarAt U j z = 0 := by
  refine ⟨dbarSliceSolution (fun x : Fin n → ℂ => (chi (x k) : ℝ) • f k x) k, ?_, ?_⟩
  · intro z hz
    rw [dzbarAt_dbarSliceSolution_of_slab hCF hgS z]
    show (chi (z k) : ℝ) • f k z = f k z
    rw [hone z hz, one_smul]
  · intro j hjk hfj z hz
    refine dzbarAt_dbarSliceSolution_eq_zero hjk hCF hgS hdS hM hM₀ z (fun t => ?_)
    exact dzbarAt_cutoff_vanishes_on_line hjk (hclosed j) hfj chi hchi (polydisc_mono hr hz) t


/-- `∂̄_j` of the zero function. -/
@[simp] theorem dzbarAt_zero (j : Fin n) (z : Fin n → ℂ) :
    dzbarAt (fun _ : Fin n → ℂ => (0 : ℂ)) j z = 0 :=
  dzbarAt_eq_zero_of_eventually_zero (Filter.Eventually.of_forall fun _ => rfl)

/-- `∂̄_j` is subtractive. -/
theorem dzbarAt_sub {F G : (Fin n → ℂ) → ℂ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (j : Fin n) (z : Fin n → ℂ) :
    dzbarAt (fun x => F x - G x) j z = dzbarAt F j z - dzbarAt G j z := by
  have hFG : Differentiable ℝ fun x => F x - G x := fun x => (hF x).sub (hG x)
  have hsub : fderiv ℝ (fun x => F x - G x) z = fderiv ℝ F z - fderiv ℝ G z :=
    ((hF z).hasFDerivAt.sub (hG z).hasFDerivAt).fderiv
  rw [dzbarAt_eq_functional hFG j z, dzbarAt_eq_functional hF j z,
    dzbarAt_eq_functional hG j z, hsub, map_sub]

/-- **Combining a partial solution with a solution of the residue.**  If `U` solves part of the
system and `v` solves the residue `f − ∂̄U` on a set, their sum solves `f` there.  This is the
assembly step of the Dolbeault induction. -/
theorem dzbarAt_add_solution {f : Fin n → (Fin n → ℂ) → ℂ} {U v : (Fin n → ℂ) → ℂ}
    (hU : Differentiable ℝ U) (hv : Differentiable ℝ v) {P : Set (Fin n → ℂ)}
    (hres : ∀ j : Fin n, ∀ z ∈ P, dzbarAt v j z = f j z - dzbarAt U j z) :
    ∀ j : Fin n, ∀ z ∈ P, dzbarAt (fun x => U x + v x) j z = f j z := by
  intro j z hz
  rw [dzbarAt_add hU hv j z, hres j z hz]
  ring


/-- **The antiholomorphic partial derivatives commute.**  Each `∂̄_j` is a fixed continuous linear
functional applied to the differential, so the iterated operator is that pair of functionals applied
to the second differential, and symmetry of the second differential is symmetry in `i` and `j`. -/
theorem dzbarAt_comm {F : (Fin n → ℂ) → ℂ} (hC : ContDiff ℝ 2 F) (i j : Fin n) (z : Fin n → ℂ) :
    dzbarAt (dzbarAt F j) i z = dzbarAt (dzbarAt F i) j z := by
  have hd1 : Differentiable ℝ F := hC.differentiable (by norm_num)
  have hfd : ContDiff ℝ 1 (fderiv ℝ F) := hC.fderiv_right le_rfl
  have hd2 : Differentiable ℝ (fderiv ℝ F) := hfd.differentiable one_ne_zero
  have hsecond : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) z) z := (hd2 z).hasFDerivAt
  have hsym : ∀ v w : Fin n → ℂ,
      (fderiv ℝ (fderiv ℝ F) z) v w = (fderiv ℝ (fderiv ℝ F) z) w v :=
    second_derivative_symmetric (fun y => (hd1 y).hasFDerivAt) hsecond
  have key : ∀ a b : Fin n,
      dzbarAt (dzbarAt F b) a z
        = dzbarFunctional a ((dzbarFunctional b).comp (fderiv ℝ (fderiv ℝ F) z)) := by
    intro a b
    have hDb : dzbarAt F b = fun y => dzbarFunctional b (fderiv ℝ F y) := by
      funext y
      exact dzbarAt_eq_functional hd1 b y
    have hfb : HasFDerivAt (fun y : Fin n → ℂ => dzbarFunctional b (fderiv ℝ F y))
        ((dzbarFunctional b).comp (fderiv ℝ (fderiv ℝ F) z)) z :=
      (dzbarFunctional b).hasFDerivAt.comp z hsecond
    rw [hDb]
    rw [dzbarAt_eq_functional (G := fun y : Fin n → ℂ => dzbarFunctional b (fderiv ℝ F y))
      (fun y => ((dzbarFunctional b).hasFDerivAt.comp y ((hd2 y).hasFDerivAt)).differentiableAt)
      a z, hfb.fderiv]
  rw [key i j, key j i]
  simp only [dzbarFunctional_apply, wirtingerAntihol, ContinuousLinearMap.coe_comp,
    Function.comp_apply]
  rw [hsym (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) i 1)
        (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j 1),
    hsym (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) i 1)
        (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j Complex.I),
    hsym (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) i Complex.I)
        (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j 1),
    hsym (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) i Complex.I)
        (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j Complex.I)]
  ring


/-- The Cauchy integrand of a slab-supported source vanishes outside a disc of radius `S` about the
`k`-th coordinate of the base point.  The disc moves with the base point, which is why a bound
uniform in the base point needs more than the fixed-ball estimate. -/
theorem cauchyIntegrand_eq_zero_of_notMem {G : (Fin n → ℂ) → ℂ} {S : ℝ} {k : Fin n}
    (hgS : ∀ x : Fin n → ℂ, S < ‖x k‖ → G x = 0) (y : Fin n → ℂ) {w : ℂ}
    (hw : w ∉ Metric.closedBall (y k) S) : G (y - Pi.single k w) = 0 := by
  refine hgS _ ?_
  have hcoord : (y - (Pi.single k w : Fin n → ℂ)) k = y k - w := by simp
  rw [hcoord]
  simp only [Metric.mem_closedBall, Complex.dist_eq, not_le] at hw
  rwa [← norm_neg (y k - w), neg_sub]

/-- The integrand is supported in that disc. -/
theorem cauchyIntegrand_support_subset {G : (Fin n → ℂ) → ℂ} {S : ℝ} {k : Fin n}
    (hgS : ∀ x : Fin n → ℂ, S < ‖x k‖ → G x = 0) (y : Fin n → ℂ) :
    Function.support (fun w : ℂ => G (y - Pi.single k w) / w)
      ⊆ Metric.closedBall (y k) S := by
  intro w hw
  by_contra hnot
  refine hw ?_
  show G (y - Pi.single k w) / w = 0
  rw [cauchyIntegrand_eq_zero_of_notMem hgS y hnot, zero_div]

end Polydisc

section UniformBound

open MeasureTheory Real Set
open scoped ENNReal

variable {n : ℕ}

/-- **The coordinatewise Cauchy transform of a bounded slab-supported function is bounded, with a
bound independent of the base point.**  The integrand vanishes off the disc of radius `S` about
`y k`, and that moving disc is split at `‖w‖ = S`: on the centred ball of radius `S` the kernel
`‖w‖⁻¹` has total mass `2πS`, and off it the kernel is at most `S⁻¹` while the moving disc has
area `πS²`.  Splitting this way, rather than comparing the moving disc with a centred one, is what
makes the bound uniform. -/
theorem enorm_cauchyIntegral_le {G : (Fin n → ℂ) → ℂ} {S M : ℝ} {k : Fin n} (hS : 0 < S)
    (hM0 : 0 ≤ M)
    (hgS : ∀ x : Fin n → ℂ, S < ‖x k‖ → G x = 0) (hM : ∀ x : Fin n → ℂ, ‖G x‖ ≤ M)
    (y : Fin n → ℂ) :
    ‖∫ w : ℂ, G (y - Pi.single k w) / w‖ₑ
      ≤ ENNReal.ofReal M * (ENNReal.ofReal S * ENNReal.ofReal (2 * π))
        + ENNReal.ofReal (M / S) * (ENNReal.ofReal S ^ 2 * NNReal.pi) := by
  refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
  have hle : ∀ w : ℂ, ‖G (y - Pi.single k w) / w‖ₑ
      ≤ Set.indicator (Metric.ball (0 : ℂ) S) (fun w => ENNReal.ofReal M * ENNReal.ofReal ‖w‖⁻¹) w
        + Set.indicator (Metric.closedBall (y k) S)
            (fun _ => ENNReal.ofReal (M / S)) w := by
    intro w
    by_cases hw : w ∈ Metric.closedBall (y k) S
    · have hbound : ‖G (y - Pi.single k w) / w‖ ≤ M * ‖w‖⁻¹ := by
        rw [norm_div, div_eq_mul_inv]
        gcongr
        exact hM _
      by_cases hw2 : w ∈ Metric.ball (0 : ℂ) S
      · refine le_trans ?_ (le_add_of_nonneg_right bot_le)
        rw [Set.indicator_of_mem hw2, ← ENNReal.ofReal_mul hM0, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hbound
      · refine le_trans ?_ (le_add_of_nonneg_left bot_le)
        rw [Set.indicator_of_mem hw]
        simp only [Metric.mem_ball, dist_zero_right, not_lt] at hw2
        have hb2 : ‖G (y - Pi.single k w) / w‖ ≤ M / S := by
          refine le_trans hbound ?_
          rw [div_eq_mul_inv]
          gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hb2
    · rw [cauchyIntegrand_eq_zero_of_notMem hgS y hw, zero_div]
      simp
  refine le_trans (lintegral_mono hle) ?_
  rw [lintegral_add_left (by measurability), lintegral_indicator measurableSet_ball,
    lintegral_indicator measurableSet_closedBall]
  gcongr
  · rw [lintegral_const_mul' _ _ (by simp : ENNReal.ofReal M ≠ ⊤)]
    gcongr
    rw [← lintegral_indicator measurableSet_ball]
    exact lintegral_ball_norm_inv S
  · rw [MeasureTheory.setLIntegral_const, Complex.volume_closedBall]

/-- **The uniform bound in real form.**  A bounded function supported in the slab `‖x k‖ ≤ S` has
coordinatewise Cauchy transform bounded by `3πMS` at every base point. -/
theorem norm_cauchyIntegral_le {G : (Fin n → ℂ) → ℂ} {S M : ℝ} {k : Fin n} (hS : 0 < S)
    (hM0 : 0 ≤ M)
    (hgS : ∀ x : Fin n → ℂ, S < ‖x k‖ → G x = 0) (hM : ∀ x : Fin n → ℂ, ‖G x‖ ≤ M)
    (y : Fin n → ℂ) :
    ‖∫ w : ℂ, G (y - Pi.single k w) / w‖ ≤ 3 * π * M * S := by
  have h := enorm_cauchyIntegral_le hS hM0 hgS hM y
  have hrhs : ENNReal.ofReal M * (ENNReal.ofReal S * ENNReal.ofReal (2 * π))
      + ENNReal.ofReal (M / S) * (ENNReal.ofReal S ^ 2 * NNReal.pi)
      = ENNReal.ofReal (3 * π * M * S) := by
    have hpi : ((NNReal.pi : NNReal) : ℝ≥0∞) = ENNReal.ofReal π := by
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    rw [hpi, ← ENNReal.ofReal_pow hS.le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  rw [hrhs, ← ofReal_norm] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

end UniformBound

section CompactCutoff

variable {n : ℕ}

/-- **`∂̄_j` is local**: it depends only on the germ of the function at the point. -/
theorem dzbarAt_congr_of_eventuallyEq {g g' : (Fin n → ℂ) → ℂ} {j : Fin n} {z : Fin n → ℂ}
    (h : ∀ᶠ y in nhds z, g y = g' y) : dzbarAt g j z = dzbarAt g' j z := by
  have hz : (fun s : ℂ => Function.update z j s) (z j) = z := Function.update_eq_self j z
  have hcont : Filter.Tendsto (fun s : ℂ => Function.update z j s) (nhds (z j)) (nhds z) := by
    have hc : ContinuousAt (fun s : ℂ => Function.update z j s) (z j) :=
      ((contDiff_updateEmbed j z).continuous).continuousAt
    have h1 : Filter.Tendsto (fun s : ℂ => Function.update z j s) (nhds (z j))
        (nhds ((fun s : ℂ => Function.update z j s) (z j))) := hc
    rwa [hz] at h1
  have hs : (dbarSlice g j z) =ᶠ[nhds (z j)] (dbarSlice g' j z) := hcont.eventually h
  rw [dzbarAt, dzbarAt, dzbar, dzbar, hs.fderiv_eq]

/-- A compactly supported function is slab supported in every coordinate, with a positive
radius. -/
theorem exists_slab_of_hasCompactSupport {E : Type*} [NormedAddCommGroup E]
    {G : (Fin n → ℂ) → E} (hcs : HasCompactSupport G)
    (k : Fin n) : ∃ S : ℝ, 0 < S ∧ ∀ x : Fin n → ℂ, S < ‖x k‖ → G x = 0 := by
  obtain ⟨R, hR, hzero⟩ := hcs.exists_pos_le_norm
  exact ⟨R, hR, fun x hx => hzero x (le_trans hx.le (norm_coord_le x k))⟩

/-- **The Dolbeault induction step with a compactly supported cutoff.**  The cutoff is a function
of the `k`-th coordinate alone times one that does not depend on that coordinate; the product is
compactly supported, so the coordinatewise Cauchy transform is smooth, while the second factor is
invisible to `∂̄_j` along every `k`-line meeting the polydisc, because it is one on the polydisc and
constant along that line.  Hence no direction along which the datum vanishes is disturbed. -/
theorem dbar_polydisc_step_smooth {f : Fin n → (Fin n → ℂ) → ℂ} {c : Fin n → ℂ}
    {r r' : Fin n → ℝ} {k : Fin n} (hr : ∀ i, r' i ≤ r i)
    (chi : ℂ → ℝ) (psi : (Fin n → ℂ) → ℝ)
    (hchi : ∀ t : ℂ, chi t ≠ 0 → t ∈ Metric.ball (c k) (r k))
    (hchione : ∀ z ∈ polydisc c r', chi (z k) = 1)
    (hpsione : ∀ z ∈ polydisc c r, psi z = 1)
    (hCG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f k x)))
    (hcs : HasCompactSupport (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f k x)))
    (hclosed : ∀ j : Fin n, ∀ z ∈ polydisc c r, dzbarAt (f k) j z = dzbarAt (f j) k z) :
    ∃ U : (Fin n → ℂ) → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U ∧
      (∀ z ∈ polydisc c r', dzbarAt U k z = f k z) ∧
      ∀ j : Fin n, j ≠ k → (∀ y ∈ polydisc c r, f j y = 0) →
        ∀ z ∈ polydisc c r', dzbarAt U j z = 0 := by
  set F : (Fin n → ℂ) → ℂ :=
    fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f k x) with hF
  have hC1 : ContDiff ℝ 1 F := hCG.of_le (by exact_mod_cast le_top)
  obtain ⟨S, hS, hgS⟩ := exists_slab_of_hasCompactSupport hcs k
  obtain ⟨Sd, hSd, hdS⟩ :=
    exists_slab_of_hasCompactSupport (hcs.fderiv ℝ) k
  obtain ⟨M, hM⟩ :=
    (hcs.fderiv ℝ).exists_bound_of_continuous (hC1.continuous_fderiv one_ne_zero)
  obtain ⟨M₀, hM₀⟩ := hcs.exists_bound_of_continuous hC1.continuous
  set T : ℝ := max S Sd with hT
  have hgT : ∀ x : Fin n → ℂ, T < ‖x k‖ → F x = 0 :=
    fun x hx => hgS x (lt_of_le_of_lt (le_max_left _ _) hx)
  have hdT : ∀ x : Fin n → ℂ, T < ‖x k‖ → fderiv ℝ F x = 0 :=
    fun x hx => hdS x (lt_of_le_of_lt (le_max_right _ _) hx)
  refine ⟨dbarSliceSolution F k, contDiff_infty_dbarSliceSolution F k hCG hcs, ?_, ?_⟩
  · intro z hz
    rw [dzbarAt_dbarSliceSolution_of_slab hC1 hgT z, hF]
    show (chi (z k) : ℝ) • ((psi z : ℝ) • f k z) = f k z
    rw [hchione z hz, hpsione z (polydisc_mono hr hz), one_smul, one_smul]
  · intro j hjk hfj z hz
    refine dzbarAt_dbarSliceSolution_eq_zero hjk hC1 hgT hdT hM hM₀ z ?_
    intro t
    have hslice : dzbarAt F j (Function.update z k t)
        = (chi t : ℝ) • dzbarAt (fun x : Fin n → ℂ => (psi x : ℝ) • f k x) j
            (Function.update z k t) := by
      rw [hF, dzbarAt_slabCutoff_smul hjk chi, Function.update_self]
    rw [hslice]
    by_cases ht : chi t = 0
    · rw [ht, zero_smul]
    · have hmem : Function.update z k t ∈ polydisc c r :=
        update_mem_polydisc (polydisc_mono hr hz) (hchi t ht)
      have hloc : dzbarAt (fun x : Fin n → ℂ => (psi x : ℝ) • f k x) j (Function.update z k t)
          = dzbarAt (f k) j (Function.update z k t) := by
        refine dzbarAt_congr_of_eventuallyEq ?_
        refine Filter.eventually_of_mem ((isOpen_polydisc c r).mem_nhds hmem) (fun y hy => ?_)
        show (psi y : ℝ) • f k y = f k y
        rw [hpsione y hy, one_smul]
      rw [hloc, hclosed j _ hmem]
      have hzero : dzbarAt (f j) k (Function.update z k t) = 0 := by
        refine dzbarAt_eq_zero_of_eventually_zero ?_
        exact Filter.eventually_of_mem ((isOpen_polydisc c r).mem_nhds hmem) (fun y hy => hfj y hy)
      rw [hzero, smul_zero]

end CompactCutoff

end HTGeometry

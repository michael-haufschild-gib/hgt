import GaloisForLFunctions.HTGeometry.DbarSolve
import GaloisForLFunctions.HTGeometry.PolydiscAnalytic

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

end SlicewiseSolution

end HTGeometry

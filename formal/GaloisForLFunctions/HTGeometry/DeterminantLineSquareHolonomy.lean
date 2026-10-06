import GaloisForLFunctions.HTGeometry.DeterminantLineEdgeHolonomy

/-!
# The determinant-line holonomy of a square

For a smooth square `q ↦ P₊ + C(q)` of orthogonal projections whose points carry admissible frames,
choose (Lebesgue number) a grid on which every small rectangle carries a smooth admissible lift.

* `rect_holonomy`: on each lifted rectangle, Stokes' theorem and the cancellation of determinant
  coordinates at the corners give
  `hol(bottom) · hol(right) = exp ∫∫ Tr(P[∂ₛP, ∂ₜP]) · hol(top) · hol(left)`.
* `square_holonomy`: multiplying over the grid, interior segments cancel (segment holonomies are
  lift independent), the boundary segments assemble into the edge holonomies of the four sides, and
  the double integrals add up: the same identity holds for the whole unit square.
-/

set_option autoImplicit false

open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section SquareLift

variable {Q Pp : H →L[ℂ] H} {C : ℝ × ℝ → SLSpace H}

/-- The horizontal line `τ ↦ C(τ, y)` of a square. -/
def hLine (C : ℝ × ℝ → SLSpace H) (y : ℝ) : ℝ → SLSpace H := fun τ => C (τ, y)

/-- The vertical line `τ ↦ C(x, τ)` of a square. -/
def vLine (C : ℝ × ℝ → SLSpace H) (x : ℝ) : ℝ → SLSpace H := fun τ => C (x, τ)

/-- A smooth admissible lift of a square over an open neighbourhood of `R`. -/
structure SquareLift (Q Pp : H →L[ℂ] H) (C : ℝ × ℝ → SLSpace H) (R : Set (ℝ × ℝ)) where
  /-- the open domain of the lift -/
  U : Set (ℝ × ℝ)
  isOpen_U : IsOpen U
  subset : R ⊆ U
  /-- the Hilbert–Schmidt displacement of the lifted frames -/
  Y : ℝ × ℝ → HSpace ℂ H
  /-- the finite-dimensional range of the `ran Q`-defects -/
  V : Submodule ℂ H
  finiteDimensional_V : FiniteDimensional ℂ V
  smooth : ContDiffOn ℝ ⊤ Y U
  frame : ∀ q ∈ U, IsFrameOf Q (frameOf Q (Y q)) (Pp + (C q).op)
  admissible : ∀ q ∈ U, Y q ∈ admissibleSubspace Q V

namespace SquareLift

variable {R : Set (ℝ × ℝ)} (L : SquareLift Q Pp C R)

/-- The restriction of a square lift to a horizontal segment. -/
def hLift (y a b : ℝ) (h : Set.Icc a b ×ˢ {y} ⊆ L.U) : PathLift Q Pp (hLine C y) a b where
  U := (fun τ : ℝ => (τ, y)) ⁻¹' L.U
  isOpen_U := L.isOpen_U.preimage (continuous_id.prodMk continuous_const)
  Icc_subset := fun τ hτ => h ⟨hτ, rfl⟩
  Y := fun τ => L.Y (τ, y)
  V := L.V
  finiteDimensional_V := L.finiteDimensional_V
  smooth := (L.smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn
    (fun _ hτ => hτ)).of_le (by norm_num)
  frame := fun τ hτ => L.frame _ hτ
  admissible := fun τ hτ => L.admissible _ hτ

/-- The restriction of a square lift to a vertical segment. -/
def vLift (x a b : ℝ) (h : {x} ×ˢ Set.Icc a b ⊆ L.U) : PathLift Q Pp (vLine C x) a b where
  U := (fun τ : ℝ => (x, τ)) ⁻¹' L.U
  isOpen_U := L.isOpen_U.preimage (continuous_const.prodMk continuous_id)
  Icc_subset := fun τ hτ => h ⟨rfl, hτ⟩
  Y := fun τ => L.Y (x, τ)
  V := L.V
  finiteDimensional_V := L.finiteDimensional_V
  smooth := (L.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ hτ => hτ)).of_le (by norm_num)
  frame := fun τ hτ => L.frame _ hτ
  admissible := fun τ hτ => L.admissible _ hτ

theorem deriv_hLift {y τ : ℝ} (hτ : (τ, y) ∈ L.U) :
    deriv (fun τ => L.Y (τ, y)) τ = fderiv ℝ L.Y (τ, y) (1, 0) := by
  have hd : DifferentiableAt ℝ L.Y (τ, y) :=
    (L.smooth.contDiffAt (L.isOpen_U.mem_nhds hτ)).differentiableAt (by norm_num)
  have hl : HasDerivAt (fun τ : ℝ => (τ, y)) ((1 : ℝ), (0 : ℝ)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ y)
  exact (hd.hasFDerivAt.comp_hasDerivAt τ hl).deriv

theorem deriv_vLift {x τ : ℝ} (hτ : (x, τ) ∈ L.U) :
    deriv (fun τ => L.Y (x, τ)) τ = fderiv ℝ L.Y (x, τ) (0, 1) := by
  have hd : DifferentiableAt ℝ L.Y (x, τ) :=
    (L.smooth.contDiffAt (L.isOpen_U.mem_nhds hτ)).differentiableAt (by norm_num)
  have hl : HasDerivAt (fun τ : ℝ => (x, τ)) ((0 : ℝ), (1 : ℝ)) τ :=
    (hasDerivAt_const τ x).prodMk (hasDerivAt_id τ)
  exact (hd.hasFDerivAt.comp_hasDerivAt τ hl).deriv

end SquareLift

end SquareLift


/-! ## The holonomy of a lifted rectangle -/

section Rect

variable {Q Pp : H →L[ℂ] H} {C : ℝ × ℝ → SLSpace H}

/-- **Holonomy around a lifted rectangle**: bottom · right = `exp ∫∫ Tr(P[∂ₛP, ∂ₜP])` · top · left. -/
theorem rect_holonomy (hQ : IsStarProjection Q) (hC : ContDiff ℝ ⊤ C) {x₀ x₁ y₀ y₁ : ℝ}
    (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) (L : SquareLift Q Pp C (Set.Icc x₀ x₁ ×ˢ Set.Icc y₀ y₁)) :
    segHol Q Pp (hLine C y₀) x₀ x₁ * segHol Q Pp (vLine C x₁) y₀ y₁ =
      Complex.exp (∫ x in x₀..x₁, ∫ y in y₀..y₁, squareCurvature Pp C (x, y)) *
        (segHol Q Pp (hLine C y₁) x₀ x₁ * segHol Q Pp (vLine C x₀) y₀ y₁) := by
  haveI := L.finiteDimensional_V
  have hR : ∀ {a b}, a ∈ Set.Icc x₀ x₁ → b ∈ Set.Icc y₀ y₁ → (a, b) ∈ L.U :=
    fun ha hb => L.subset ⟨ha, hb⟩
  have hy₀ : y₀ ∈ Set.Icc y₀ y₁ := ⟨le_rfl, hy⟩
  have hy₁ : y₁ ∈ Set.Icc y₀ y₁ := ⟨hy, le_rfl⟩
  have hx₀ : x₀ ∈ Set.Icc x₀ x₁ := ⟨le_rfl, hx⟩
  have hx₁ : x₁ ∈ Set.Icc x₀ x₁ := ⟨hx, le_rfl⟩
  set hb := L.hLift y₀ x₀ x₁ fun q hq =>
    L.subset ⟨hq.1, by rw [Set.mem_singleton_iff.mp hq.2]; exact hy₀⟩
  set ht := L.hLift y₁ x₀ x₁ fun q hq =>
    L.subset ⟨hq.1, by rw [Set.mem_singleton_iff.mp hq.2]; exact hy₁⟩
  set vl := L.vLift x₀ y₀ y₁ fun q hq =>
    L.subset ⟨by rw [Set.mem_singleton_iff.mp hq.1]; exact hx₀, hq.2⟩
  set vr := L.vLift x₁ y₀ y₁ fun q hq =>
    L.subset ⟨by rw [Set.mem_singleton_iff.mp hq.1]; exact hx₁, hq.2⟩
  rw [segHol_eq hQ hx hb, segHol_eq hQ hy vr, segHol_eq hQ hx ht, segHol_eq hQ hy vl]
  -- the line integrals are the boundary terms of Stokes' theorem
  have iS : ∀ y ∈ Set.Icc y₀ y₁, (∫ τ in x₀..x₁, detConnection Q (L.Y (τ, y))
      (deriv (fun τ => L.Y (τ, y)) τ)) = ∫ τ in x₀..x₁, liftConnS Q L.Y (τ, y) := by
    intro y hy'
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [Set.uIcc_of_le hx] at hτ
    simp only [liftConnS]
    rw [L.deriv_hLift (hR hτ hy')]
  have iT : ∀ x ∈ Set.Icc x₀ x₁, (∫ τ in y₀..y₁, detConnection Q (L.Y (x, τ))
      (deriv (fun τ => L.Y (x, τ)) τ)) = ∫ τ in y₀..y₁, liftConnT Q L.Y (x, τ) := by
    intro x hx'
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [Set.uIcc_of_le hy] at hτ
    simp only [liftConnT]
    rw [L.deriv_vLift (hR hx' hτ)]
  have hstokes := integral_squareCurvature_eq (V := L.V) hQ L.isOpen_U
    (fun q _ => hC.contDiffAt.of_le (by norm_num))
    (fun q hq => (L.smooth.contDiffAt (L.isOpen_U.mem_nhds hq)).of_le (by norm_num))
    L.frame L.admissible hx hy L.subset
  -- corner coordinates
  have hD : ∀ {a b}, a ∈ Set.Icc x₀ x₁ → b ∈ Set.Icc y₀ y₁ →
      detCoord Q (Pp + (C (a, b)).op) (frameOf Q (L.Y (a, b))) ≠ 0 := by
    intro a b ha hb'
    refine detCoord_ne_zero hQ ⟨L.frame _ (hR ha hb'), ?_, L.V, inferInstance, fun z => ?_⟩
    · simpa [frameOf] using (L.Y (a, b)).isHS
    · have hQQ : Q (Q z) = Q z := by rw [← mul_apply_eq_comp, hQ.isIdempotentElem.eq]
      have : (Q * frameOf Q (L.Y (a, b)) - Q) z = Q ((L.Y (a, b)).op z) := by
        simp [frameOf, mul_add, sub_apply, hQQ]
      rw [this]; exact (L.admissible _ (hR ha hb')).1 z
  unfold edgeFactor
  simp only [hb, ht, vl, vr, SquareLift.hLift, SquareLift.vLift, hLine, vLine]
  rw [iS y₀ hy₀, iS y₁ hy₁, iT x₀ hx₀, iT x₁ hx₁, hstokes]
  have d00 := hD hx₀ hy₀; have d10 := hD hx₁ hy₀; have d01 := hD hx₀ hy₁; have d11 := hD hx₁ hy₁
  rw [show ∀ a b c d : ℂ, a + b - c - d = (a + b) - (c + d) by intros; ring, Complex.exp_sub,
    Complex.exp_add, Complex.exp_add]
  have := Complex.exp_ne_zero (∫ τ in x₀..x₁, liftConnS Q L.Y (τ, y₁))
  have := Complex.exp_ne_zero (∫ τ in y₀..y₁, liftConnT Q L.Y (x₀, τ))
  field_simp

end Rect


/-! ## Auxiliary facts for the grid -/

section Grid

theorem prod_range_div_succ {f : ℕ → ℂ} (hf : ∀ j, f j ≠ 0) (m : ℕ) :
    ∏ j ∈ Finset.range m, f j / f (j + 1) = f 0 / f m := by
  induction m with
  | zero => simp [div_self (hf 0)]
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    field_simp [hf m, hf (m + 1)]

variable {Pp : H →L[ℂ] H} {C : ℝ × ℝ → SLSpace H}

/-- The curvature density of a smooth square is continuous. -/
theorem continuous_squareCurvature (hC : ContDiff ℝ ⊤ C) :
    Continuous (squareCurvature Pp C) := by
  have hd : Continuous fun q => fderiv ℝ C q := hC.continuous_fderiv (by norm_num)
  have hX : Continuous fun q => (fderiv ℝ C q (1, 0)).toHS :=
    (slSubmodule H).subtypeL.continuous.comp (hd.clm_apply continuous_const)
  have hY : Continuous fun q => (fderiv ℝ C q (0, 1)).toHS :=
    (slSubmodule H).subtypeL.continuous.comp (hd.clm_apply continuous_const)
  have hP : Continuous fun q => Pp + (C q).op :=
    continuous_const.add ((SLSpace.opCLM H).continuous.comp hC.continuous)
  have heq : squareCurvature Pp C = fun q =>
      HSpace.traceL (HSpace.lmulL (Pp + (C q).op) (fderiv ℝ C q (1, 0)).toHS)
          (fderiv ℝ C q (0, 1)).toHS -
        HSpace.traceL (HSpace.lmulL (Pp + (C q).op) (fderiv ℝ C q (0, 1)).toHS)
          (fderiv ℝ C q (1, 0)).toHS := by
    funext q
    simp only [squareCurvature, detCurvature, HSpace.traceL_apply, HSpace.op_lmulL]
    set X := fderiv ℝ C q (1, 0)
    set Y := fderiv ℝ C q (0, 1)
    show opTrace ((Pp + (C q).op) * (X.op * Y.op - Y.op * X.op)) =
      opTrace ((Pp + (C q).op) * X.op * Y.op) - opTrace ((Pp + (C q).op) * Y.op * X.op)
    rw [mul_sub, ← mul_assoc, ← mul_assoc]
    exact opTrace_sub_of_mem (mul_mem_hsTraceIdeal (X.isHS.comp_left _) Y.isHS)
      (mul_mem_hsTraceIdeal (Y.isHS.comp_left _) X.isHS)
  rw [heq]
  have hA : Continuous fun q => HSpace.lmulL (Pp + (C q).op) (fderiv ℝ C q (1, 0)).toHS :=
    (HSpace.lmulL.continuous.comp hP).clm_apply hX
  have hB : Continuous fun q => HSpace.lmulL (Pp + (C q).op) (fderiv ℝ C q (0, 1)).toHS :=
    (HSpace.lmulL.continuous.comp hP).clm_apply hY
  exact ((HSpace.traceL.continuous.comp hA).clm_apply hY).sub
    ((HSpace.traceL.continuous.comp hB).clm_apply hX)

/-- Grid additivity of the double integral over the unit square. -/
theorem integral_unitSquare_eq_sum {f : ℝ × ℝ → ℂ} (hf : Continuous f) {m : ℕ} (hm : 0 < m) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f (x, y) =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        ∫ x in (i / m : ℝ)..((i + 1) / m), ∫ y in (j / m : ℝ)..((j + 1) / m), f (x, y) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  set a : ℕ → ℝ := fun k => k / m
  have ha0 : a 0 = 0 := by simp [a]
  have ham : a m = 1 := by simp [a, hmR]
  have hsucc : ∀ k : ℕ, a (k + 1) = ((k : ℝ) + 1) / m := fun k => by simp [a]
  have hfx : ∀ x, Continuous fun y => f (x, y) := fun x => hf.comp (continuous_const.prodMk
    continuous_id)
  have hinner : ∀ x, (∫ y in (0 : ℝ)..1, f (x, y)) =
      ∑ j ∈ Finset.range m, ∫ y in (j / m : ℝ)..((j + 1) / m), f (x, y) := by
    intro x
    have h := intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := m)
      (μ := MeasureTheory.volume) (fun k _ => (hfx x).intervalIntegrable _ _)
    rw [ha0, ham] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [a, Nat.cast_add, Nat.cast_one]
  have huncurry : Function.uncurry (fun x y => f (x, y)) = f := by funext p; rfl
  have hcont : ∀ c d : ℝ, Continuous fun x => ∫ y in c..d, f (x, y) := fun c d =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x y => f (x, y)) (by rw [huncurry]; exact hf) c d
  simp_rw [hinner]
  have h := intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := m)
    (μ := MeasureTheory.volume) (f := fun x => ∑ j ∈ Finset.range m, ∫ y in (j / m : ℝ)..((j + 1) / m), f (x, y))
    (fun k _ => (continuous_finsetSum _ fun j _ => hcont _ _).intervalIntegrable _ _)
  rw [ha0, ham] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont _ _).intervalIntegrable _ _)]
  simp only [a, Nat.cast_add, Nat.cast_one]

end Grid


/-! ## The holonomy of a square -/

section Square

variable {Q Pp : H →L[ℂ] H} {C : ℝ × ℝ → SLSpace H}

/-- The grid rectangle `[i/m, (i+1)/m] × [j/m, (j+1)/m]`. -/
def gridRect (m i j : ℕ) : Set (ℝ × ℝ) :=
  Set.Icc ((i : ℝ) / m) ((i + 1) / m) ×ˢ Set.Icc ((j : ℝ) / m) ((j + 1) / m)

/-- **Squares in the admissible sector have lifted grids.** -/
theorem exists_grid_lifts (hQ : IsStarProjection Q) (hC : ContDiff ℝ ⊤ C)
    (hproj : ∀ q, IsStarProjection (Pp + (C q).op))
    (hsec : ∀ q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      ∃ u, IsAdmissibleFrame Q u (Pp + (C q).op)) :
    ∃ m, 0 < m ∧ ∀ i < m, ∀ j < m, Nonempty (SquareLift Q Pp C (gridRect m i j)) := by
  classical
  set K := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  have hloc : ∀ q : K, ∃ (U : Set (ℝ × ℝ)) (Y : ℝ × ℝ → HSpace ℂ H) (V : Submodule ℂ H),
      IsOpen U ∧ (q : ℝ × ℝ) ∈ U ∧ FiniteDimensional ℂ V ∧ ContDiffOn ℝ ⊤ Y U ∧
      (∀ x ∈ U, IsFrameOf Q (frameOf Q (Y x)) (Pp + (C x).op)) ∧
      (∀ x ∈ U, Y x ∈ admissibleSubspace Q V) := fun q =>
    exists_local_lift hQ hC hproj (hsec q q.2).choose_spec
  choose U Y V hU hqU hV hY hfr hadm using hloc
  obtain ⟨δ, hδ, hcov⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc.prod isCompact_Icc)
    (c := U) hU (fun q hq => Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hqU ⟨q, hq⟩⟩)
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  have hmR : (0 : ℝ) < m := lt_trans (by positivity) hm
  have hm0 : 0 < m := by exact_mod_cast hmR
  have hstep : 1 / (m : ℝ) < δ := by
    rw [div_lt_iff₀ hmR]; rw [div_lt_iff₀ hδ] at hm; linarith
  refine ⟨m, hm0, fun i hi j hj => ?_⟩
  have hc : ∀ k < m, (0 : ℝ) ≤ k / m ∧ (k : ℝ) / m ≤ 1 := fun k hk =>
    ⟨by positivity, by rw [div_le_one hmR]; exact_mod_cast hk.le⟩
  obtain ⟨p, hball⟩ := hcov ((i : ℝ) / m, (j : ℝ) / m) ⟨hc i hi, hc j hj⟩
  have hsub : gridRect m i j ⊆ U p := by
    intro q hq
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
    have e1 : ((i : ℝ) + 1) / m = i / m + 1 / m := by ring
    have e2 : ((j : ℝ) + 1) / m = j / m + 1 / m := by ring
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hq
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  exact ⟨⟨U p, hU p, hsub, Y p, V p, hV p, hY p, hfr p, hadm p⟩⟩

theorem prod_range_succ_div {f : ℕ → ℂ} (hf : ∀ j, f j ≠ 0) (m : ℕ) :
    ∏ j ∈ Finset.range m, f (j + 1) / f j = f m / f 0 := by
  induction m with
  | zero => simp [div_self (hf 0)]
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    field_simp [hf m, hf 0]

/-- **The holonomy of a square in the admissible sector**:
`hol(bottom) · hol(right) = exp ∫∫ Tr(P[∂ₛP, ∂ₜP]) · hol(top) · hol(left)`. -/
theorem square_holonomy (hQ : IsStarProjection Q) (hC : ContDiff ℝ ⊤ C)
    (hproj : ∀ q, IsStarProjection (Pp + (C q).op))
    (hsec : ∀ q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      ∃ u, IsAdmissibleFrame Q u (Pp + (C q).op)) :
    edgeHol Q Pp (hLine C 0) * edgeHol Q Pp (vLine C 1) =
      Complex.exp (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, squareCurvature Pp C (x, y)) *
        (edgeHol Q Pp (hLine C 1) * edgeHol Q Pp (vLine C 0)) := by
  obtain ⟨m, hm, hL⟩ := exists_grid_lifts hQ hC hproj hsec
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hle : ∀ k : ℕ, (k : ℝ) / m ≤ ((k : ℝ) + 1) / m := fun k => by gcongr; linarith
  -- segment holonomies on the grid lines
  set Sh : ℕ → ℕ → ℂ := fun j i => segHol Q Pp (hLine C ((j : ℝ) / m)) (i / m) ((i + 1) / m)
  set Sv : ℕ → ℕ → ℂ := fun i j => segHol Q Pp (vLine C ((i : ℝ) / m)) (j / m) ((j + 1) / m)
  have hSh : ∀ j i, Sh j i ≠ 0 := fun j i => segHol_ne_zero hQ (hle i)
  have hSv : ∀ i j, Sv i j ≠ 0 := fun i j => segHol_ne_zero hQ (hle j)
  set E : ℕ → ℕ → ℂ := fun i j => Complex.exp (∫ x in ((i : ℝ) / m)..((i + 1) / m),
    ∫ y in ((j : ℝ) / m)..((j + 1) / m), squareCurvature Pp C (x, y))
  have hcast : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := fun k => by push_cast; ring
  have hrect : ∀ i < m, ∀ j < m, E i j = Sh j i / Sh (j + 1) i * (Sv (i + 1) j / Sv i j) := by
    intro i hi j hj
    obtain ⟨L⟩ := hL i hi j hj
    have h := rect_holonomy hQ hC (hle i) (hle j) L
    have e1 : Sh (j + 1) i = segHol Q Pp (hLine C (((j : ℝ) + 1) / m)) (i / m) ((i + 1) / m) := by
      simp only [Sh, hcast]
    have e2 : Sv (i + 1) j = segHol Q Pp (vLine C (((i : ℝ) + 1) / m)) (j / m) ((j + 1) / m) := by
      simp only [Sv, hcast]
    rw [e1, e2]
    simp only [Sh, Sv]
    have n1 := segHol_ne_zero (Q := Q) (Pp := Pp) (e := hLine C (((j : ℝ) + 1) / m)) hQ (hle i)
    have n2 := segHol_ne_zero (Q := Q) (Pp := Pp) (e := vLine C ((i : ℝ) / m)) hQ (hle j)
    field_simp
    rw [h]
    simp only [E]
    ring
  -- telescoping over the grid
  have hprod : ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m, E i j =
      (∏ i ∈ Finset.range m, Sh 0 i) / (∏ i ∈ Finset.range m, Sh m i) *
        ((∏ j ∈ Finset.range m, Sv m j) / (∏ j ∈ Finset.range m, Sv 0 j)) := by
    rw [Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun j hj =>
      hrect i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)]
    simp only [Finset.prod_mul_distrib]
    rw [Finset.prod_comm (f := fun i j => Sv (i + 1) j / Sv i j)]
    have hh : ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m, Sh j i / Sh (j + 1) i =
        ∏ i ∈ Finset.range m, Sh 0 i / Sh m i :=
      Finset.prod_congr rfl fun i _ => prod_range_div_succ (f := fun j => Sh j i)
        (fun j => hSh j i) m
    have hv : ∏ j ∈ Finset.range m, ∏ i ∈ Finset.range m, Sv (i + 1) j / Sv i j =
        ∏ j ∈ Finset.range m, Sv m j / Sv 0 j :=
      Finset.prod_congr rfl fun j _ => prod_range_succ_div (f := fun i => Sv i j)
        (fun i => hSv i j) m
    rw [hh, hv, Finset.prod_div_distrib, Finset.prod_div_distrib]
  -- the double integral
  have hsum : ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m, E i j =
      Complex.exp (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, squareCurvature Pp C (x, y)) := by
    rw [integral_unitSquare_eq_sum (continuous_squareCurvature hC) hm, Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.exp_sum]
  -- the four boundary edges are computed at level `m`
  have hm1 : ((m - 1 : ℕ) : ℝ) + 1 = m := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hm.ne'), Nat.cast_one]; ring
  have hmm : (m : ℝ) / m = 1 := div_self hmR.ne'
  have fb : FineLevel Q Pp (hLine C 0) m := fun i hi => by
    obtain ⟨L⟩ := hL i hi 0 hm
    refine ⟨L.hLift 0 _ _ fun q hq => L.subset ⟨hq.1, ?_⟩⟩
    rw [Set.mem_singleton_iff.mp hq.2]; simp [hmR.le]
  have ft : FineLevel Q Pp (hLine C 1) m := fun i hi => by
    obtain ⟨L⟩ := hL i hi (m - 1) (Nat.sub_lt hm one_pos)
    refine ⟨L.hLift 1 _ _ fun q hq => L.subset ⟨hq.1, ?_⟩⟩
    rw [Set.mem_singleton_iff.mp hq.2, hm1, hmm]
    exact ⟨by rw [div_le_one hmR]; exact_mod_cast Nat.sub_le m 1, le_rfl⟩
  have fl : FineLevel Q Pp (vLine C 0) m := fun j hj => by
    obtain ⟨L⟩ := hL 0 hm j hj
    refine ⟨L.vLift 0 _ _ fun q hq => L.subset ⟨?_, hq.2⟩⟩
    rw [Set.mem_singleton_iff.mp hq.1]; simp [hmR.le]
  have fr : FineLevel Q Pp (vLine C 1) m := fun j hj => by
    obtain ⟨L⟩ := hL (m - 1) (Nat.sub_lt hm one_pos) j hj
    refine ⟨L.vLift 1 _ _ fun q hq => L.subset ⟨?_, hq.2⟩⟩
    rw [Set.mem_singleton_iff.mp hq.1, hm1, hmm]
    exact ⟨by rw [div_le_one hmR]; exact_mod_cast Nat.sub_le m 1, le_rfl⟩
  have eb : edgeHol Q Pp (hLine C 0) = ∏ i ∈ Finset.range m, Sh 0 i := by
    rw [edgeHol_eq hQ hm fb]; simp [levelHol, Sh]
  have et : edgeHol Q Pp (hLine C 1) = ∏ i ∈ Finset.range m, Sh m i := by
    rw [edgeHol_eq hQ hm ft]; simp only [levelHol, Sh, hmm]
  have el : edgeHol Q Pp (vLine C 0) = ∏ j ∈ Finset.range m, Sv 0 j := by
    rw [edgeHol_eq hQ hm fl]; simp [levelHol, Sv]
  have er : edgeHol Q Pp (vLine C 1) = ∏ j ∈ Finset.range m, Sv m j := by
    rw [edgeHol_eq hQ hm fr]; simp only [levelHol, Sv, hmm]
  have nt : ∏ i ∈ Finset.range m, Sh m i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hSh m i
  have nl : ∏ j ∈ Finset.range m, Sv 0 j ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hSv 0 j
  rw [← hsum, hprod, eb, et, el, er]
  field_simp

end Square

end

end GaloisForLFunctions.HTGeometry

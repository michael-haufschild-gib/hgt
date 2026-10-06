import GaloisForLFunctions.HTGeometry.DeterminantLineGraphCapHolonomy

/-!
# Holomorphic spheres have nonnegative integral determinant degree

* `detKahlerForm_tangent`: at an orthogonal projection `P`, for tangent vectors `X, Y`
  (`PX + XP = X`), `ω_det(X, Y) = Im Tr(x† y)/π` with `x = (1 − P)XP`, `y = (1 − P)YP`.
* A holomorphic chart is a smooth map `z ↦ P(z)` of projections with `(1 − P)∂_{z̄}P P = 0`; then
  `(1 − P) DP[v] P = v · (1 − P)∂_zP P` and, along any smooth `φ : ℝ² → ℂ`,
  `ω_det(∂ₛ, ∂ₜ) = Im(conj(∂ₛφ) ∂ₜφ) · ‖(1 − P)∂_zP P‖²_HS / π` (`HolChart.squareKahler_comp`).
  In polar coordinates the northern square has density `2r‖·‖² ≥ 0`, the southern (orientation
  reversing) square `−2r‖·‖² ≤ 0`.
* A holomorphic sphere is a pair of charts glued by `w = 1/z`; its fundamental chain
  (north − south) is a cycle (`HolSphere.isCycle`), so its degree `∫_B ω_det` is an integer, and it
  is nonnegative: `HolSphere.exists_degree_eq_nat`.
-/

set_option autoImplicit false

open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The Kähler form on tangent vectors -/

section Tangent

variable {P X Y : H →L[ℂ] H}

/-- Derivatives of projection-valued maps are tangent: `PẊ + ẊP = Ẋ`. -/
theorem tangent_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Pp : H →L[ℂ] H}
    {F : E → SLSpace H} {z : E} (hF : DifferentiableAt ℝ F z)
    (hproj : ∀ z, IsIdempotentElem (Pp + (F z).op)) (v : E) :
    (Pp + (F z).op) * (fderiv ℝ F z v).op + (fderiv ℝ F z v).op * (Pp + (F z).op) =
      (fderiv ℝ F z v).op := by
  set g : E → H →L[ℂ] H := fun z => Pp + (F z).op
  have hg : HasFDerivAt g ((SLSpace.opCLM H).comp (fderiv ℝ F z)) z :=
    ((hasFDerivAt_const Pp z).add
      ((SLSpace.opCLM H).hasFDerivAt.comp z hF.hasFDerivAt)).congr_fderiv (by ext; simp)
  have hgg := hg.mul' hg
  have hfun : (g * g) = g := funext fun z => (hproj z).eq
  rw [hfun] at hgg
  have h := congrArg (fun L => L v) (hgg.unique hg)
  simpa [g] using h

/-- `P X Y = ((1 − P)XP)† ((1 − P)YP)` for tangent vectors at an orthogonal projection. -/
theorem mul_tangent_eq (hP : IsStarProjection P) (hXs : IsSelfAdjoint X)
    (hX : P * X + X * P = X) (hY : P * Y + Y * P = Y) :
    P * X * Y = adjoint ((1 - P) * X * P) * ((1 - P) * Y * P) := by
  have hPi := hP.isIdempotentElem
  have hadj : adjoint ((1 - P) * X * P) = P * X * (1 - P) := by
    rw [← star_eq_adjoint, star_mul, star_mul, star_sub, star_one, hP.isSelfAdjoint.star_eq,
      hXs.star_eq, mul_assoc]
  have hPX : P * X = P * X * (1 - P) := by
    rw [mul_sub, mul_one, tangent_compress hPi hX, sub_zero]
  have hcY : (1 - P) * Y = (1 - P) * Y * P := by
    calc (1 - P) * Y = (1 - P) * Y * P + (1 - P) * Y * (1 - P) := by noncomm_ring
      _ = (1 - P) * Y * P := by rw [tangent_compress_compl hPi hY, add_zero]
  have hcc : (1 - P) * (1 - P) = 1 - P := hPi.one_sub.eq
  calc P * X * Y = P * X * (1 - P) * Y := by rw [← hPX]
    _ = P * X * ((1 - P) * Y) := by rw [mul_assoc]
    _ = P * X * ((1 - P) * Y * P) := by rw [← hcY]
    _ = P * X * ((1 - P) * (1 - P) * Y * P) := by rw [hcc]
    _ = P * X * (1 - P) * ((1 - P) * Y * P) := by noncomm_ring
    _ = adjoint ((1 - P) * X * P) * ((1 - P) * Y * P) := by rw [hadj]

/-- **The determinant-line Kähler form on tangent vectors** at an orthogonal projection `P`:
`ω_det(X, Y) = Im Tr(x† y) / π`, `x = (1 − P)XP`, `y = (1 − P)YP`. -/
theorem detKahlerForm_tangent (hP : IsStarProjection P) (hXs : IsSelfAdjoint X)
    (hYs : IsSelfAdjoint Y) (hXh : IsHilbertSchmidt X) (hYh : IsHilbertSchmidt Y)
    (hX : P * X + X * P = X) (hY : P * Y + Y * P = Y) :
    detKahlerForm P X Y =
      (opTrace (adjoint ((1 - P) * X * P) * ((1 - P) * Y * P))).im / Real.pi := by
  have hxh : IsHilbertSchmidt ((1 - P) * X * P) := (hXh.comp_left _).comp_right _
  have hyh : IsHilbertSchmidt ((1 - P) * Y * P) := (hYh.comp_left _).comp_right _
  have hm1 := mul_mem_hsTraceIdeal hxh.adjoint hyh
  have hm2 := mul_mem_hsTraceIdeal hyh.adjoint hxh
  rw [detKahlerForm, detCurvature, mul_sub, ← mul_assoc, ← mul_assoc, mul_tangent_eq hP hXs hX hY,
    mul_tangent_eq hP hYs hY hX, opTrace_sub_of_mem hm1 hm2]
  set x := (1 - P) * X * P
  set y := (1 - P) * Y * P
  have hconj : opTrace (adjoint y * x) = (starRingEnd ℂ) (opTrace (adjoint x * y)) := by
    rw [← opTrace_adjoint]
    congr 1
    rw [← star_eq_adjoint (adjoint x * y), star_mul, star_eq_adjoint, star_eq_adjoint,
      adjoint_adjoint]
  rw [hconj, Complex.sub_conj]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  field_simp
  ring

end Tangent

/-! ## Holomorphic charts -/

section Holomorphic

variable {Pp : H →L[ℂ] H}

variable (Pp) in
/-- A holomorphic chart of the restricted Grassmannian: a smooth map `z ↦ P(z) = P₊ + f(z)` of
orthogonal projections whose range varies holomorphically, `(1 − P) ∂_{z̄}P P = 0`. -/
structure HolChart where
  /-- the displacement `P(z) − P₊` -/
  map : ℂ → SLSpace H
  smooth : ContDiff ℝ ⊤ map
  proj : ∀ z, IsStarProjection (Pp + (map z).op)
  holo : ∀ z, (1 - (Pp + (map z).op)) *
    ((fderiv ℝ map z 1).op + Complex.I • (fderiv ℝ map z Complex.I).op) * (Pp + (map z).op) = 0

/-- The `(1,0)`-derivative of a holomorphic chart, `(1 − P) ∂_z P P`. -/
def HolChart.normal (f : HolChart Pp) (z : ℂ) : H →L[ℂ] H :=
  (1 - (Pp + (f.map z).op)) * (fderiv ℝ f.map z 1).op * (Pp + (f.map z).op)

theorem HolChart.isHilbertSchmidt_normal (f : HolChart Pp) (z : ℂ) :
    IsHilbertSchmidt (f.normal z) :=
  ((fderiv ℝ f.map z 1).isHS.comp_left _).comp_right _

/-- The derivative of a holomorphic chart is complex linear modulo `P`:
`(1 − P) Df[v] P = v · (1 − P) ∂_z P P`. -/
theorem HolChart.compress_fderiv (f : HolChart Pp) (z v : ℂ) :
    (1 - (Pp + (f.map z).op)) * (fderiv ℝ f.map z v).op * (Pp + (f.map z).op) = v • f.normal z := by
  have hh := f.holo z
  have hv : fderiv ℝ f.map z v = v.re • fderiv ℝ f.map z 1 + v.im • fderiv ℝ f.map z Complex.I := by
    conv_lhs => rw [← Complex.re_add_im v]
    rw [show (v.re : ℂ) + v.im * Complex.I = v.re • (1 : ℂ) + v.im • Complex.I by
      simp [Complex.real_smul], map_add, map_smul, map_smul]
  rw [hv, SLSpace.op_add, SLSpace.op_smul, SLSpace.op_smul]
  unfold HolChart.normal
  generalize Pp + (f.map z).op = P at hh ⊢
  generalize (fderiv ℝ f.map z 1).op = X₁ at hh ⊢
  generalize (fderiv ℝ f.map z Complex.I).op = X₂ at hh ⊢
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc] at hh
  have h2 : (1 - P) * X₂ * P = Complex.I • ((1 - P) * X₁ * P) := by
    have : Complex.I • ((1 - P) * X₁ * P + Complex.I • ((1 - P) * X₂ * P)) = 0 := by
      rw [hh, smul_zero]
    rw [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, add_neg_eq_zero] at this
    exact this.symm
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, h2, smul_smul,
    ← add_smul, Complex.re_add_im]

/-- **The determinant-line Kähler density of a holomorphic chart** pulled back by a smooth map
`φ : ℝ² → ℂ`: `ω_det(∂ₛ, ∂ₜ) = Im(conj(∂ₛφ) ∂ₜφ) · ‖(1 − P)∂_zP P‖²_HS / π`; the first factor is
the Jacobian of `φ`. -/
theorem HolChart.squareKahler_comp (f : HolChart Pp) {φ : ℝ × ℝ → ℂ} (hφ : Differentiable ℝ φ)
    (q : ℝ × ℝ) :
    squareKahler Pp (f.map ∘ φ) q =
      ((starRingEnd ℂ) (fderiv ℝ φ q (1, 0)) * fderiv ℝ φ q (0, 1)).im *
        hsNormSq (f.normal (φ q)) / Real.pi := by
  have hfd : DifferentiableAt ℝ f.map (φ q) := f.smooth.differentiable (by simp) _
  have hself : hsInner (f.normal (φ q)) (f.normal (φ q)) = (hsNormSq (f.normal (φ q)) : ℂ) := by
    rw [hsInner, hsNormSq, Complex.ofReal_tsum]
    exact tsum_congr fun i => by rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hchain : ∀ w, fderiv ℝ (f.map ∘ φ) q w = fderiv ℝ f.map (φ q) (fderiv ℝ φ q w) := fun w => by
    rw [fderiv_comp q hfd (hφ q)]; rfl
  set a := fderiv ℝ φ q (1, 0)
  set b := fderiv ℝ φ q (0, 1)
  have hP := f.proj (φ q)
  have htan := fun v => tangent_fderiv hfd (fun z => (f.proj z).isIdempotentElem) v
  rw [squareKahler, hchain, hchain, Function.comp_apply,
    detKahlerForm_tangent hP (fderiv ℝ f.map (φ q) a).isSelfAdjoint
      (fderiv ℝ f.map (φ q) b).isSelfAdjoint (fderiv ℝ f.map (φ q) a).isHS
      (fderiv ℝ f.map (φ q) b).isHS (htan a) (htan b),
    f.compress_fderiv, f.compress_fderiv, map_smulₛₗ, smul_mul_assoc, mul_smul_comm, smul_smul,
    opTrace_smul', ContinuousLinearMap.mul_def, opTrace_adjoint_comp_self, hself,
    Complex.im_mul_ofReal]

theorem conj_exp_two_pi_mul_exp (y : ℝ) :
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * y)) *
      Complex.exp (2 * Real.pi * Complex.I * y) = 1 := by
  have h := normSq_capCoord_one y
  simp only [capCoord, Complex.ofReal_one, one_mul] at h
  rw [mul_comm, Complex.mul_conj, h, Complex.ofReal_one]

/-- The northern polar square `(r, θ) ↦ f(r e^{2πiθ})` of a holomorphic chart. -/
def HolChart.north (f : HolChart Pp) : GrSquare Pp where
  map := f.map ∘ capCoord
  smooth := f.smooth.comp contDiff_capCoord
  proj _ := f.proj _

/-- The southern polar square `(r, θ) ↦ f(r e^{-2πiθ})` of a holomorphic chart. -/
def HolChart.south (f : HolChart Pp) : GrSquare Pp where
  map := f.map ∘ fun q => (starRingEnd ℂ) (capCoord q)
  smooth := f.smooth.comp (Complex.conjCLE.contDiff.comp contDiff_capCoord)
  proj _ := f.proj _

theorem HolChart.squareKahler_north (f : HolChart Pp) (q : ℝ × ℝ) :
    squareKahler Pp f.north.map q = 2 * q.1 * hsNormSq (f.normal (capCoord q)) := by
  rw [HolChart.north, f.squareKahler_comp (contDiff_capCoord.differentiable (by simp)),
    fderiv_capCoord_fst, fderiv_capCoord_snd]
  have h := conj_exp_two_pi_mul_exp q.2
  have hpi := Real.pi_ne_zero
  have him : ((starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * q.2)) *
      (q.1 * (Complex.exp (2 * Real.pi * Complex.I * q.2) * (2 * Real.pi * Complex.I)))).im =
      2 * Real.pi * q.1 := by
    rw [show (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * q.2)) *
      (q.1 * (Complex.exp (2 * Real.pi * Complex.I * q.2) * (2 * Real.pi * Complex.I))) =
      ((starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * q.2)) *
        Complex.exp (2 * Real.pi * Complex.I * q.2)) * ((2 * Real.pi * q.1 : ℝ) * Complex.I) by
      push_cast; ring, h, one_mul, Complex.im_ofReal_mul, Complex.I_im, mul_one]
  rw [him]; field_simp

theorem HolChart.squareKahler_south (f : HolChart Pp) (q : ℝ × ℝ) :
    squareKahler Pp f.south.map q =
      -(2 * q.1 * hsNormSq (f.normal ((starRingEnd ℂ) (capCoord q)))) := by
  have hφ : Differentiable ℝ fun q : ℝ × ℝ => (starRingEnd ℂ) (capCoord q) :=
    (Complex.conjCLE.contDiff.comp contDiff_capCoord).differentiable (by simp)
  have hd : ∀ w, fderiv ℝ (fun q : ℝ × ℝ => (starRingEnd ℂ) (capCoord q)) q w =
      (starRingEnd ℂ) (fderiv ℝ capCoord q w) := fun w => by
    have := (Complex.conjCLE.hasFDerivAt.comp q
      ((contDiff_capCoord.differentiable (by simp)) q).hasFDerivAt).fderiv
    rw [show (fun q : ℝ × ℝ => (starRingEnd ℂ) (capCoord q)) = ⇑Complex.conjCLE ∘ capCoord from rfl,
      this]
    rfl
  rw [HolChart.south, f.squareKahler_comp hφ, hd, hd, fderiv_capCoord_fst, fderiv_capCoord_snd]
  have h := conj_exp_two_pi_mul_exp q.2
  have him : ((starRingEnd ℂ) ((starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * q.2))) *
      (starRingEnd ℂ) (q.1 * (Complex.exp (2 * Real.pi * Complex.I * q.2) *
        (2 * Real.pi * Complex.I)))).im = -(2 * Real.pi * q.1) := by
    rw [Complex.conj_conj, map_mul, map_mul, Complex.conj_ofReal, map_mul, map_mul, map_ofNat,
      Complex.conj_ofReal, Complex.conj_I,
      show Complex.exp (2 * Real.pi * Complex.I * q.2) * (q.1 * ((starRingEnd ℂ)
        (Complex.exp (2 * Real.pi * Complex.I * q.2)) * (2 * Real.pi * -Complex.I))) =
      ((starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * q.2)) *
        Complex.exp (2 * Real.pi * Complex.I * q.2)) * ((-(2 * Real.pi * q.1) : ℝ) * Complex.I) by
      push_cast; ring, h, one_mul, Complex.im_ofReal_mul, Complex.I_im, mul_one]
  rw [him]; field_simp

theorem HolChart.integral_north_nonneg (f : HolChart Pp) :
    0 ≤ ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, squareKahler Pp f.north.map (x, y) :=
  intervalIntegral.integral_nonneg zero_le_one fun x hx =>
    intervalIntegral.integral_nonneg zero_le_one fun y _ => by
      rw [f.squareKahler_north]
      exact mul_nonneg (mul_nonneg zero_le_two hx.1) (hsNormSq_nonneg _)

theorem HolChart.integral_south_nonpos (f : HolChart Pp) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, squareKahler Pp f.south.map (x, y) ≤ 0 := by
  have h : 0 ≤ ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, -squareKahler Pp f.south.map (x, y) :=
    intervalIntegral.integral_nonneg zero_le_one fun x hx =>
      intervalIntegral.integral_nonneg zero_le_one fun y _ => by
        rw [f.squareKahler_south, neg_neg]
        exact mul_nonneg (mul_nonneg zero_le_two hx.1) (hsNormSq_nonneg _)
  simp only [intervalIntegral.integral_neg] at h
  linarith

end Holomorphic

/-! ## Holomorphic spheres -/

section Sphere

variable {Pp : H →L[ℂ] H}

variable (Pp) in
/-- A holomorphic sphere in the restricted Grassmannian: two holomorphic charts glued by
`w = 1/z`. -/
structure HolSphere where
  /-- the chart near `z = 0` -/
  north : HolChart Pp
  /-- the chart near `z = ∞`, in the coordinate `w = 1/z` -/
  south : HolChart Pp
  glue : ∀ w : ℂ, w ≠ 0 → south.map w = north.map w⁻¹

/-- The fundamental cycle of a holomorphic sphere: the northern polar square minus the southern
one (the south chart reverses orientation). -/
def HolSphere.chain (B : HolSphere Pp) : GrChain Pp where
  len := 2
  coeff := ![1, -1]
  sq := ![B.north.north, B.south.south]

/-- The degree `⟨c₁(L_det), [B]⟩ = ∫_B ω_det` of a holomorphic sphere. -/
def HolSphere.degree (B : HolSphere Pp) : ℝ := B.chain.kahlerIntegral

theorem HolSphere.degree_eq (B : HolSphere Pp) :
    B.degree = (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, squareKahler Pp B.north.north.map (x, y)) -
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, squareKahler Pp B.south.south.map (x, y) := by
  unfold HolSphere.degree GrChain.kahlerIntegral GrChain.kahlerOn
  refine (Fin.sum_univ_two _).trans ?_
  simp [HolSphere.chain, sub_eq_add_neg]

theorem HolChart.north_edge_top (f : HolChart Pp) : f.north.edge 2 = f.north.edge 0 := by
  funext τ
  simp [GrSquare.edge, hLine, HolChart.north, capCoord_snd_one]

theorem HolChart.south_edge_top (f : HolChart Pp) : f.south.edge 2 = f.south.edge 0 := by
  funext τ
  simp [GrSquare.edge, hLine, HolChart.south, capCoord_snd_one]

theorem HolChart.north_edge_left (f : HolChart Pp) : IsDegeneratePath (f.north.edge 3) := by
  intro τ
  simp [GrSquare.edge, vLine, HolChart.north, capCoord]

theorem HolChart.south_edge_left (f : HolChart Pp) : IsDegeneratePath (f.south.edge 3) := by
  intro τ
  simp [GrSquare.edge, vLine, HolChart.south, capCoord]

theorem HolSphere.south_edge_right (B : HolSphere Pp) :
    B.south.south.edge 1 = B.north.north.edge 1 := by
  funext τ
  have he : Complex.exp (2 * Real.pi * Complex.I * τ) ≠ 0 := Complex.exp_ne_zero _
  have hinv : ((starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * τ)))⁻¹ =
      Complex.exp (2 * Real.pi * Complex.I * τ) := by
    exact inv_eq_of_mul_eq_one_right (conj_exp_two_pi_mul_exp τ)
  simp only [GrSquare.edge, vLine, HolChart.north, HolChart.south, Function.comp_apply, capCoord,
    Complex.ofReal_one, one_mul]
  rw [B.glue _ ((map_ne_zero _).mpr he), hinv]

open Classical in
/-- The boundary multiplicity of a path in the boundary of `a · S`. -/
def squareBdry (S : GrSquare Pp) (a : ℤ) (e : ℝ → SLSpace H) : ℤ :=
  ∑ j : Fin 4, if S.edge j = e then a * edgeSign j else 0

open Classical in
theorem squareBdry_of_periodic (S : GrSquare Pp) (a : ℤ) {e : ℝ → SLSpace H}
    (h2 : S.edge 2 = S.edge 0) (h3 : S.edge 3 ≠ e) :
    squareBdry S a e = if S.edge 1 = e then a else 0 := by
  unfold squareBdry
  rw [Fin.sum_univ_four, h2, if_neg h3]
  simp only [edgeSign]
  split_ifs <;> ring

theorem HolSphere.bdry_chain (B : HolSphere Pp) (e : ℝ → SLSpace H) :
    B.chain.bdry e = squareBdry B.north.north 1 e + squareBdry B.south.south (-1) e := by
  unfold GrChain.bdry GrChain.bdryOn
  exact Fin.sum_univ_two _

/-- **The fundamental chain of a holomorphic sphere is a cycle.** -/
theorem HolSphere.isCycle (B : HolSphere Pp) : B.chain.IsCycle := by
  intro e he
  have hN3 : B.north.north.edge 3 ≠ e := fun h => he (h ▸ B.north.north_edge_left)
  have hS3 : B.south.south.edge 3 ≠ e := fun h => he (h ▸ B.south.south_edge_left)
  rw [B.bdry_chain, squareBdry_of_periodic _ _ B.north.north_edge_top hN3,
    squareBdry_of_periodic _ _ B.south.south_edge_top hS3, B.south_edge_right]
  split_ifs <;> ring

/-- **The degree of a holomorphic sphere is a natural number**: it is an integer because the sphere
is a cycle, and nonnegative because `ω_det` is positive on holomorphic curves. -/
theorem HolSphere.exists_degree_eq_nat (B : HolSphere Pp) : ∃ m : ℕ, B.degree = m := by
  obtain ⟨z, hz⟩ := B.chain.kahlerIntegral_mem_int B.isCycle
  have hnn : 0 ≤ B.degree := by
    rw [B.degree_eq]
    linarith [B.north.integral_north_nonneg, B.south.integral_south_nonpos]
  have hz' : B.degree = z := hz
  refine ⟨z.toNat, ?_⟩
  rw [hz']
  have : (0 : ℝ) ≤ z := hz' ▸ hnn
  have hz0 : 0 ≤ z := by exact_mod_cast this
  exact_mod_cast (Int.toNat_of_nonneg hz0).symm

end Sphere

end

end GaloisForLFunctions.HTGeometry

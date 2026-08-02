import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestBoundaryScore

/-!
# Exact Gamma--Hardy boundary transgression of the primitive Euler source

The primitive Euler horizon is not merely a decomposition of two positive
matrices.  If its moving endpoint is complexified to `L`, differentiation
of the compact Gamma/co-Poisson head gives the endpoint kernel, while
differentiation of the translated Hardy tail gives its negative.  Thus the
retained prime-power endpoint is an exact, oriented chain boundary:

`d/dL (head, tail) = (endpoint, -endpoint)`.

This file constructs the corresponding split boundary complex and proves
that its Green primitive is exactly the endpoint kernel.  The finite-`σ`
endpoint Gram and its critical Fisher limit therefore live in the relative
Green channel; their sum trace is zero.

The source Fisher primitive is then sewn back to the complementary Hardy
tail.  This produces, unconditionally and on every finite right-half-plane
packet, a positive augmented Gram whose test block is the *unshifted* Hardy
Cauchy Gram, whose boundary diagonal is four, and whose boundary column is
the literal primitive-source Fisher column.  It has exactly the ambient
geometry and budget of the Xi Ward boundary Gram, but does not identify its
column with the Xi Ward response.
-/

open Complex Filter Matrix Set
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-! ## Analytic moving-horizon kernels -/

/-- Endpoint kernel created by moving the Gamma/Hardy horizon. -/
def eulerPrimitiveAnalyticHorizonEndpointKernel
    (L w v : ℂ) : ℂ :=
  (Complex.exp ∘ fun z : ℂ => -(w + star v) * z) L

/-- Complexified compact-head kernel. -/
def eulerPrimitiveAnalyticHorizonHeadKernel
    (L w v : ℂ) : ℂ :=
  (1 - eulerPrimitiveAnalyticHorizonEndpointKernel L w v) /
    (w + star v)

/-- Complexified translated-tail kernel. -/
def eulerPrimitiveAnalyticHorizonTailKernel
    (L w v : ℂ) : ℂ :=
  eulerPrimitiveAnalyticHorizonEndpointKernel L w v /
    (w + star v)

theorem eulerPrimitiveAnalyticHorizonHeadKernel_add_tail
    {L w v : ℂ} (h : w + star v ≠ 0) :
    eulerPrimitiveAnalyticHorizonHeadKernel L w v +
        eulerPrimitiveAnalyticHorizonTailKernel L w v =
      1 / (w + star v) := by
  simp only [eulerPrimitiveAnalyticHorizonHeadKernel,
    eulerPrimitiveAnalyticHorizonTailKernel]
  field_simp [h]
  ring

theorem hasDerivAt_eulerPrimitiveAnalyticHorizonEndpointKernel
    (L w v : ℂ) :
    HasDerivAt
      (fun z => eulerPrimitiveAnalyticHorizonEndpointKernel z w v)
      (eulerPrimitiveAnalyticHorizonEndpointKernel L w v *
        (-(w + star v))) L := by
  let s : ℂ := w + star v
  have h :=
    (Complex.hasDerivAt_exp (-s * L)).comp L
      ((hasDerivAt_id L).const_mul (-s))
  have h' :
      HasDerivAt
        (Complex.exp ∘ fun z : ℂ => -s * z)
        (eulerPrimitiveAnalyticHorizonEndpointKernel L w v * (-s)) L :=
    h.congr_deriv (by
      simp [eulerPrimitiveAnalyticHorizonEndpointKernel, s])
  apply h'.congr_of_eventuallyEq
  filter_upwards with z
  rfl

/-- The compact Gamma/co-Poisson head gains the moving endpoint. -/
theorem hasDerivAt_eulerPrimitiveAnalyticHorizonHeadKernel
    {L w v : ℂ} (h : w + star v ≠ 0) :
    HasDerivAt
      (fun z => eulerPrimitiveAnalyticHorizonHeadKernel z w v)
      (eulerPrimitiveAnalyticHorizonEndpointKernel L w v) L := by
  have hd :=
    ((hasDerivAt_eulerPrimitiveAnalyticHorizonEndpointKernel L w v).const_sub
      1).div_const (w + star v)
  apply hd.congr_deriv
  field_simp [h]

/-- The translated Hardy tail loses the same moving endpoint. -/
theorem hasDerivAt_eulerPrimitiveAnalyticHorizonTailKernel
    {L w v : ℂ} (h : w + star v ≠ 0) :
    HasDerivAt
      (fun z => eulerPrimitiveAnalyticHorizonTailKernel z w v)
      (-eulerPrimitiveAnalyticHorizonEndpointKernel L w v) L := by
  have hd :=
    (hasDerivAt_eulerPrimitiveAnalyticHorizonEndpointKernel L w v).div_const
      (w + star v)
  apply hd.congr_deriv
  field_simp [h]

/-- The analytic tail at the literal action `log n` is the actual
prime-power translated Hardy tail. -/
theorem eulerPrimitiveAnalyticHorizonTailKernel_log_eq
    {N : ℕ} (n : ℕ) (w : Fin N → ℂ) (i j : Fin N) :
    eulerPrimitiveAnalyticHorizonTailKernel (Real.log n : ℂ)
        (w i) (w j) =
      eulerPrimitiveHorizonTailTransportMatrix n w i j := by
  rw [eulerPrimitiveAnalyticHorizonTailKernel,
    eulerPrimitiveAnalyticHorizonEndpointKernel,
    eulerPrimitiveHorizonTailTransportMatrix,
    eulerPrimitiveHorizonMultiplier,
    star_eulerPrimitiveHorizonMultiplier]
  simp only [Function.comp_apply, div_eq_mul_inv]
  rw [show
      -(w i + star (w j)) * (Real.log n : ℂ) =
        (-(w i) * (Real.log n : ℂ)) +
          (-(star (w j)) * (Real.log n : ℂ)) by ring,
    Complex.exp_add]
  simp [rightHalfPlaneHardyCauchyGram]
  ring

/-- The analytic head at `log n` is the actual reflected
Gamma/co-Poisson compact head. -/
theorem eulerPrimitiveAnalyticHorizonHeadKernel_log_eq
    {N : ℕ} (n : ℕ) (w : Fin N → ℂ)
    (hw : ∀ i, 0 < (w i).re) (i j : Fin N) :
    eulerPrimitiveAnalyticHorizonHeadKernel (Real.log n : ℂ)
        (w i) (w j) =
      eulerPrimitiveHorizonHeadFibreMatrix n w i j := by
  have hs : w i + star (w j) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp only [Complex.add_re, RCLike.star_def, Complex.conj_re,
      Complex.zero_re] at hre
    linarith [hw i, hw j]
  have hanalytic :=
    eulerPrimitiveAnalyticHorizonHeadKernel_add_tail
      (L := (Real.log n : ℂ)) hs
  have hsource :=
    congrArg
      (fun M : Matrix (Fin N) (Fin N) ℂ => M i j)
      (eulerPrimitiveHorizonHeadFibreMatrix_add_tail n w hw)
  rw [Matrix.add_apply] at hsource
  rw [eulerPrimitiveAnalyticHorizonTailKernel_log_eq] at hanalytic
  change
    eulerPrimitiveHorizonHeadFibreMatrix n w i j +
        eulerPrimitiveHorizonTailTransportMatrix n w i j =
      1 / (w i + star (w j)) at hsource
  linear_combination hanalytic - hsource

/-! ## Split oriented boundary complex -/

/-- Two legs of the Gamma-head/Hardy-tail boundary. -/
abbrev EulerPrimitiveHorizonBoundaryCochain (ι : Type*) :=
  Matrix ι ι ℂ × Matrix ι ι ℂ

/-- An endpoint enters the head and leaves the tail with opposite
orientation. -/
def eulerPrimitiveHorizonBoundary
    (ι : Type*) :
    Matrix ι ι ℂ →ₗ[ℂ] EulerPrimitiveHorizonBoundaryCochain ι where
  toFun E := (E, -E)
  map_add' E F := by
    ext <;> simp [add_comm]
  map_smul' c E := by
    ext <;> simp

/-- Boundary-blind sum trace. -/
def eulerPrimitiveHorizonBoundaryTrace
    (ι : Type*) :
    EulerPrimitiveHorizonBoundaryCochain ι →ₗ[ℂ] Matrix ι ι ℂ where
  toFun z := z.1 + z.2
  map_add' z u := by
    ext i j
    simp
    ring
  map_smul' c z := by
    ext i j
    simp
    ring

/-- Canonical representative of the absolute Hardy trace. -/
def eulerPrimitiveHorizonBoundaryTraceInclusion
    (ι : Type*) :
    Matrix ι ι ℂ →ₗ[ℂ] EulerPrimitiveHorizonBoundaryCochain ι where
  toFun G := (0, G)
  map_add' G H := by
    ext <;> simp
  map_smul' c G := by
    ext <;> simp

/-- Green primitive: retain the compact-head leg before sum trace. -/
def eulerPrimitiveHorizonBoundaryGreen
    (ι : Type*) :
    EulerPrimitiveHorizonBoundaryCochain ι →ₗ[ℂ] Matrix ι ι ℂ where
  toFun z := z.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem eulerPrimitiveHorizonBoundaryTrace_boundary
    {ι : Type*} (E : Matrix ι ι ℂ) :
    eulerPrimitiveHorizonBoundaryTrace ι
        (eulerPrimitiveHorizonBoundary ι E) = 0 := by
  ext i j
  simp [eulerPrimitiveHorizonBoundaryTrace,
    eulerPrimitiveHorizonBoundary]

@[simp]
theorem eulerPrimitiveHorizonBoundaryGreen_boundary
    {ι : Type*} (E : Matrix ι ι ℂ) :
    eulerPrimitiveHorizonBoundaryGreen ι
        (eulerPrimitiveHorizonBoundary ι E) = E :=
  rfl

/-- Exact Green splitting.  The relative endpoint primitive and absolute
Hardy trace are complementary, before any scalar orientation trace. -/
theorem eulerPrimitiveHorizonBoundaryGreenDecomposition
    {ι : Type*} (z : EulerPrimitiveHorizonBoundaryCochain ι) :
    eulerPrimitiveHorizonBoundary ι
        (eulerPrimitiveHorizonBoundaryGreen ι z) +
      eulerPrimitiveHorizonBoundaryTraceInclusion ι
        (eulerPrimitiveHorizonBoundaryTrace ι z) = z := by
  rcases z with ⟨H, T⟩
  ext <;> simp [eulerPrimitiveHorizonBoundary,
    eulerPrimitiveHorizonBoundaryGreen,
    eulerPrimitiveHorizonBoundaryTrace,
    eulerPrimitiveHorizonBoundaryTraceInclusion]

/-- Entrywise moving-horizon differential is the exact oriented endpoint
boundary, and Green contraction recovers that endpoint. -/
theorem eulerPrimitiveMovingHorizon_derivative_transgression
    {N : ℕ} {L : ℂ} (w : Fin N → ℂ)
    (hw : ∀ i, 0 < (w i).re) (i j : Fin N) :
    HasDerivAt
        (fun z =>
          eulerPrimitiveAnalyticHorizonHeadKernel z (w i) (w j))
        (eulerPrimitiveAnalyticHorizonEndpointKernel L (w i) (w j)) L ∧
      HasDerivAt
        (fun z =>
          eulerPrimitiveAnalyticHorizonTailKernel z (w i) (w j))
        (-eulerPrimitiveAnalyticHorizonEndpointKernel L (w i) (w j)) L := by
  have hs : w i + star (w j) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp only [Complex.add_re, RCLike.star_def, Complex.conj_re,
      Complex.zero_re] at hre
    linarith [hw i, hw j]
  exact
    ⟨hasDerivAt_eulerPrimitiveAnalyticHorizonHeadKernel hs,
      hasDerivAt_eulerPrimitiveAnalyticHorizonTailKernel hs⟩

/-! ## Literal prime-power endpoint as Green primitive -/

/-- At a retained prime-power label, the analytic endpoint is the outer
product of the two literal Euler endpoint features. -/
theorem eulerPrimitiveAnalyticHorizonEndpointKernel_log_eq_featurePair
    {sigma : ℝ} {ι : Type*} (a : ι → ℂ) (n : ℕ) (i j : ι) :
    eulerPrimitiveAnalyticHorizonEndpointKernel (Real.log n : ℂ)
        (((sigma : ℂ) - 1) * a i)
        (((sigma : ℂ) - 1) * a j) =
      eulerPrimitiveBoundaryEndpointFeature sigma (a i) n *
        star (eulerPrimitiveBoundaryEndpointFeature sigma (a j) n) := by
  simp only [eulerPrimitiveBoundaryEndpointFeature]
  rw [star_eulerPrimitiveHorizonMultiplier,
    eulerPrimitiveHorizonMultiplier]
  rw [eulerPrimitiveAnalyticHorizonEndpointKernel]
  simp only [Function.comp_apply]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Finite-`σ` endpoint boundary: its sum trace vanishes and its canonical
Green primitive is the actual normalized von-Mangoldt endpoint Gram. -/
def eulerPrimitiveBoundaryEndpointTransgression
    {ι : Type*} [Fintype ι] (sigma : ℝ) (a : ι → ℂ) :
    EulerPrimitiveHorizonBoundaryCochain ι :=
  eulerPrimitiveHorizonBoundary ι
    (eulerPrimitiveBoundaryEndpointGram sigma a)

theorem eulerPrimitiveBoundaryEndpointTransgression_exact
    {ι : Type*} [Fintype ι] (sigma : ℝ) (a : ι → ℂ) :
    eulerPrimitiveHorizonBoundaryTrace ι
        (eulerPrimitiveBoundaryEndpointTransgression sigma a) = 0 ∧
      eulerPrimitiveHorizonBoundaryGreen ι
          (eulerPrimitiveBoundaryEndpointTransgression sigma a) =
        eulerPrimitiveBoundaryEndpointGram sigma a := by
  exact
    ⟨eulerPrimitiveHorizonBoundaryTrace_boundary _,
      eulerPrimitiveHorizonBoundaryGreen_boundary _⟩

/-! ## Unshifted four-unit Hardy realization of the Fisher primitive -/

/-- Inclusion of the test block into the augmented test/boundary packet. -/
noncomputable def eulerPrimitiveBoundaryTestEmbedding
    {N : ℕ} : Matrix (Fin N ⊕ Unit) (Fin N) ℂ := by
  classical
  exact fun r j =>
    match r with
    | Sum.inl i => if i = j then 1 else 0
    | Sum.inr _ => 0

/-- Complementary Hardy tail lifted with zero boundary row and column. -/
def eulerPrimitiveBoundaryAugmentedTailGram
    {N : ℕ} (a : Fin N → ℂ) :
    Matrix (Fin N ⊕ Unit) (Fin N ⊕ Unit) ℂ :=
  eulerPrimitiveBoundaryTestEmbedding (N := N) *
    eulerPrimitiveHorizonBlowupTailGram a *
    (eulerPrimitiveBoundaryTestEmbedding (N := N))ᴴ

@[simp]
theorem eulerPrimitiveBoundaryAugmentedTailGram_test_test
    {N : ℕ} (a : Fin N → ℂ) (i j : Fin N) :
    eulerPrimitiveBoundaryAugmentedTailGram a
        (Sum.inl i) (Sum.inl j) =
      eulerPrimitiveHorizonBlowupTailGram a i j := by
  classical
  simp [eulerPrimitiveBoundaryAugmentedTailGram,
    eulerPrimitiveBoundaryTestEmbedding, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

@[simp]
theorem eulerPrimitiveBoundaryAugmentedTailGram_test_boundary
    {N : ℕ} (a : Fin N → ℂ) (i : Fin N) :
    eulerPrimitiveBoundaryAugmentedTailGram a
        (Sum.inl i) (Sum.inr ()) = 0 := by
  classical
  simp [eulerPrimitiveBoundaryAugmentedTailGram,
    eulerPrimitiveBoundaryTestEmbedding, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

@[simp]
theorem eulerPrimitiveBoundaryAugmentedTailGram_boundary_test
    {N : ℕ} (a : Fin N → ℂ) (j : Fin N) :
    eulerPrimitiveBoundaryAugmentedTailGram a
        (Sum.inr ()) (Sum.inl j) = 0 := by
  classical
  simp [eulerPrimitiveBoundaryAugmentedTailGram,
    eulerPrimitiveBoundaryTestEmbedding, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

@[simp]
theorem eulerPrimitiveBoundaryAugmentedTailGram_boundary_boundary
    {N : ℕ} (a : Fin N → ℂ) :
    eulerPrimitiveBoundaryAugmentedTailGram a
        (Sum.inr ()) (Sum.inr ()) = 0 := by
  classical
  simp [eulerPrimitiveBoundaryAugmentedTailGram,
    eulerPrimitiveBoundaryTestEmbedding, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

theorem eulerPrimitiveBoundaryAugmentedTailGram_posSemidef
    {N : ℕ} (a : Fin N → ℂ) (ha : ∀ i, 0 < (a i).re) :
    (eulerPrimitiveBoundaryAugmentedTailGram a).PosSemidef := by
  simpa [eulerPrimitiveBoundaryAugmentedTailGram] using
    (eulerPrimitiveHorizonBlowupTailGram_posSemidef a ha)
      |>.mul_mul_conjTranspose_same
        (eulerPrimitiveBoundaryTestEmbedding (N := N))

/-- Source-side four-unit boundary Gram on the unshifted Hardy space. -/
def eulerPrimitiveBoundaryFullHardyFisherGram
    {N : ℕ} (a : Fin N → ℂ) :
    Matrix (Fin N ⊕ Unit) (Fin N ⊕ Unit) ℂ
  | Sum.inl i, Sum.inl j =>
      rightHalfPlaneHardyCauchyGram a i j
  | Sum.inl i, Sum.inr _ =>
      eulerPrimitiveBoundaryFisherColumn a i
  | Sum.inr _, Sum.inl j =>
      star (eulerPrimitiveBoundaryFisherColumn a j)
  | Sum.inr _, Sum.inr _ => 4

theorem eulerPrimitiveBoundaryFullHardyFisherGram_eq_head_add_tail
    {N : ℕ} (a : Fin N → ℂ) (ha : ∀ i, 0 < (a i).re) :
    eulerPrimitiveBoundaryFullHardyFisherGram a =
      eulerPrimitiveBoundaryFisherGram a +
        eulerPrimitiveBoundaryAugmentedTailGram a := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · have hsplit :=
      congrArg
        (fun M : Matrix (Fin N) (Fin N) ℂ => M i j)
        (eulerPrimitiveHorizonBlowupHeadGram_add_tail a ha)
    simpa [eulerPrimitiveBoundaryFullHardyFisherGram,
      eulerPrimitiveBoundaryFisherGram,
      eulerPrimitiveHorizonBlowupHeadGram,
      shiftedPolarRightHalfPlaneGram,
      eulerPrimitiveBoundaryAugmentedTailGram_test_test,
      add_assoc, add_comm, add_left_comm] using hsplit.symm
  · rcases j with ⟨⟩
    simp [eulerPrimitiveBoundaryFullHardyFisherGram,
      eulerPrimitiveBoundaryFisherGram]
  · rcases i with ⟨⟩
    simp [eulerPrimitiveBoundaryFullHardyFisherGram,
      eulerPrimitiveBoundaryFisherGram]
  · rcases i with ⟨⟩
    rcases j with ⟨⟩
    simp [eulerPrimitiveBoundaryFullHardyFisherGram,
      eulerPrimitiveBoundaryFisherGram]

/--
**Unconditional source four-unit boundary law.**  The exact endpoint Green
primitive, after restoring its complementary Hardy tail, gives a positive
augmented Gram with the unshifted Hardy block and boundary budget four.
-/
theorem eulerPrimitiveBoundaryFullHardyFisherGram_posSemidef
    {N : ℕ} (a : Fin N → ℂ) (ha : ∀ i, 0 < (a i).re) :
    (eulerPrimitiveBoundaryFullHardyFisherGram a).PosSemidef := by
  rw [eulerPrimitiveBoundaryFullHardyFisherGram_eq_head_add_tail a ha]
  exact
    (eulerPrimitiveBoundaryFisherGram_posSemidef a ha).add
      (eulerPrimitiveBoundaryAugmentedTailGram_posSemidef a ha)

theorem eulerPrimitiveBoundaryFullHardyFisherGram_test_test
    {N : ℕ} (a : Fin N → ℂ) (i j : Fin N) :
    eulerPrimitiveBoundaryFullHardyFisherGram a
        (Sum.inl i) (Sum.inl j) =
      rightHalfPlaneHardyCauchyGram a i j :=
  rfl

theorem eulerPrimitiveBoundaryFullHardyFisherGram_test_boundary
    {N : ℕ} (a : Fin N → ℂ) (i : Fin N) :
    eulerPrimitiveBoundaryFullHardyFisherGram a
        (Sum.inl i) (Sum.inr ()) =
      eulerPrimitiveBoundaryFisherColumn a i :=
  rfl

theorem eulerPrimitiveBoundaryFullHardyFisherGram_boundary_boundary
    {N : ℕ} (a : Fin N → ℂ) :
    eulerPrimitiveBoundaryFullHardyFisherGram a
        (Sum.inr ()) (Sum.inr ()) = 4 :=
  rfl

end

end RHTower

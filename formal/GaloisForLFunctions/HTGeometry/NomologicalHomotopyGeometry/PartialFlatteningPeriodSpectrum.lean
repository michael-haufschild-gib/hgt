import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.CotangentDoubleCyclicCompletion
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.LawValuedForms
import GaloisForLFunctions.HTGeometry.ManifoldProductFubini

open DifferentialGeometry TensorProduct
open scoped Manifold ContDiff

/-!
# Length-three partial flattening: curvature, periods, observers and recurrence

Let `Σ` be a closed oriented surface and `N` a closed oriented three-manifold, with top forms
`ω ∈ Ω²(Σ)`, `η ∈ Ω³(N)` of integrals `m = ∫_Σ ω`, `n = ∫_N η`. In the three-storey law
`L = ⟨x, y, w⟩`, `[x, y] = w`, consider on `Σ × N` the law connection `a_t = ωx + tηy`.

* **Curvature** (`productLawConnection_curv5`): the curvature vanishes in form degrees `3, 4` and
  above `5`, and `F₅(t) = −t (ω ∧ η) ⊗ w` is closed; the summands `ωx` and `tηy` are separately
  flat.
* **Period reconstruction** (`period_reconstruction`): if `m n ≠ 0`, then `t = 0`, `F₅(t) = 0`,
  `[F₅(t)] = 0` in de Rham cohomology and `Π(t) = ∫ F₅(t) = −t m n w = 0` are equivalent; the
  period is injective in `t` with range the line `ℝw`, and the obstruction spectrum of the flat
  base `ωx` contains the whole line of classes `−t [ω ∧ η] w`.
* **Proper faces** (`curv5_restrict_slices`): restricted to any slice `Σ × {p}` or `{s} × N`, the
  fifth curvature vanishes.
* **Observers** (`observer_erases_iff`, `observers_reconstruct_iff`): strict morphisms carry
  curvature and period naturally; an observer erases the whole history exactly when it kills `w`.
* **Cyclic completion** (`cyclicCompletion_curv5_and_period`): the statements embed unchanged in
  the shifted cotangent double `T*[d]L`.
* **Recurrence and properness** (`periodPhase_periodic`, `lawPeriod_action_proper`): modulo the
  lattice `ℓℤw`, the period phase has exact period `ℓ / |mn|`, while the lifted period escapes
  linearly and the action `‖Π(t)‖² = m²n²‖w‖²t²` is proper and vanishes only at `t = 0`.
-/

namespace GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry

noncomputable section

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  {H₁ H₂ : Type*} [TopologicalSpace H₁] [TopologicalSpace H₂]
  {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂} [I₁.Boundaryless]
  [I₂.Boundaryless]
  {Sf N : Type*} [TopologicalSpace Sf] [ChartedSpace H₁ Sf] [IsManifold I₁ ∞ Sf]
  [TopologicalSpace N] [ChartedSpace H₂ N] [IsManifold I₂ ∞ N]

/-- The pullback of `ω` to `Σ × N` along the first projection. -/
def pr1Form {k : ℕ} (α₂ : DifferentialForm I₁ Sf k) : DifferentialForm (I₁.prod I₂) (Sf × N) k :=
  DifferentialForm.pullback Prod.fst
    (contMDiff_fst : ContMDiff (I₁.prod I₂) I₁ ∞ (Prod.fst : Sf × N → Sf)) α₂

/-- The pullback of `η` to `Σ × N` along the second projection. -/
def pr2Form {k : ℕ} (η : DifferentialForm I₂ N k) : DifferentialForm (I₁.prod I₂) (Sf × N) k :=
  DifferentialForm.pullback Prod.snd
    (contMDiff_snd : ContMDiff (I₁.prod I₂) I₂ ∞ (Prod.snd : Sf × N → N)) η

/-- **The product law connection** `a_t = ω x + t η y` on `Σ × N`. -/
def productLawConnection (α₂ : DifferentialForm I₁ Sf 2) (η : DifferentialForm I₂ N 3) (t : ℝ) :
    LawConnection (I₁.prod I₂) (Sf × N) ThreeStorey :=
  ⟨pr1Form α₂ ⊗ₜ gx, t • (pr2Form η ⊗ₜ gy), 0⟩

/-! ## Bracket values of the three-storey law -/

theorem bracket_gx_gx : threeStoreyLaw.bracket gx gx = 0 := by
  simp [threeStoreyLaw_bracket, gx]

theorem bracket_gy_gy : threeStoreyLaw.bracket gy gy = 0 := by
  simp [threeStoreyLaw_bracket, gy]

theorem bracket_gx_gy : threeStoreyLaw.bracket gx gy = gw := threeStoreyBracket_x_y

theorem bracket_gy_gx : threeStoreyLaw.bracket gy gx = -gw := by
  simp [threeStoreyLaw_bracket, gx, gy, gw]

theorem koszulSign_neg_one_three : koszulSign (-1) ((3 : ℕ) : ℤ) = -1 := by norm_num [koszulSign]

theorem koszulSign_neg_two_two : koszulSign (-2) ((2 : ℕ) : ℤ) = 1 := by norm_num [koszulSign]

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [I₁.Boundaryless] [I₂.Boundaryless] in
/-- On `Σ × N`, `π₂*η ∧ π₁*ω = π₁*ω ∧ π₂*η` (degrees `3` and `2`, sign `(−1)^6 = 1`). -/
theorem wedge_pr2Form_pr1Form (α₂ : DifferentialForm I₁ Sf 2) (η₃ : DifferentialForm I₂ N 3) :
    (DifferentialForm.wedge (pr2Form (I₁ := I₁) (Sf := Sf) η₃) (pr1Form (I₂ := I₂) (N := N) α₂) :
      DifferentialForm (I₁.prod I₂) (Sf × N) 5) =
    DifferentialForm.wedge (pr1Form α₂) (pr2Form η₃) := by
  have h := DifferentialForm.wedge_comm (pr1Form (I₂ := I₂) (N := N) α₂)
    (pr2Form (I₁ := I₁) (Sf := Sf) η₃)
  apply ContMDiffSection.ext
  intro z
  have hz := congrArg (fun θ => θ z) h
  simp only [DifferentialForm.reindex_apply, DifferentialForm.smul_apply] at hz
  rw [hz]
  ext v
  simp only [ContinuousAlternatingMap.domDomCongr_apply, ContinuousAlternatingMap.smul_apply]
  norm_num
  congr 1

/-! ## The later interaction curvature -/

omit [FiniteDimensional ℝ E₂] in
open _root_.HTGeometry in
theorem exteriorDerivative_pr1Form_eq_zero (h₁ : Module.finrank ℝ E₁ = 2)
    (α₂ : DifferentialForm I₁ Sf 2) :
    DifferentialForm.exteriorDerivative (pr1Form (I₂ := I₂) (N := N) α₂) = 0 := by
  rw [pr1Form, ← DifferentialForm.exteriorDerivative_pullback,
    SmoothDeRham.differentialForm_eq_zero_of_finrank_lt (by omega)
      (DifferentialForm.exteriorDerivative α₂)]
  exact (DifferentialForm.pullbackLinearMap Prod.fst
    (contMDiff_fst : ContMDiff (I₁.prod I₂) I₁ ∞ (Prod.fst : Sf × N → Sf)) 3).map_zero

omit [FiniteDimensional ℝ E₁] in
open _root_.HTGeometry in
theorem exteriorDerivative_pr2Form_eq_zero (h₂ : Module.finrank ℝ E₂ = 3)
    (η₃ : DifferentialForm I₂ N 3) :
    DifferentialForm.exteriorDerivative (pr2Form (I₁ := I₁) (Sf := Sf) η₃) = 0 := by
  rw [pr2Form, ← DifferentialForm.exteriorDerivative_pullback,
    SmoothDeRham.differentialForm_eq_zero_of_finrank_lt (by omega)
      (DifferentialForm.exteriorDerivative η₃)]
  exact (DifferentialForm.pullbackLinearMap Prod.snd
    (contMDiff_snd : ContMDiff (I₁.prod I₂) I₂ ∞ (Prod.snd : Sf × N → N)) 4).map_zero

omit [I₁.Boundaryless] [I₂.Boundaryless] in
/-- Law-valued forms above the dimension of `Σ × N` vanish. -/
theorem lawForm_eq_zero_of_dim_lt (h₁ : Module.finrank ℝ E₁ = 2) (h₂ : Module.finrank ℝ E₂ = 3)
    {k : ℕ} (hk : 5 < k) (A : LawForm (I₁.prod I₂) (Sf × N) ThreeStorey k) : A = 0 := by
  induction A using TensorProduct.induction_on with
  | zero => rfl
  | tmul α u =>
    rw [_root_.HTGeometry.SmoothDeRham.differentialForm_eq_zero_of_finrank_lt (by
      rw [Module.finrank_prod, h₁, h₂]; omega) α, TensorProduct.zero_tmul]
  | add A B hA hB => rw [hA, hB, add_zero]

section Curvature

variable (h₁ : Module.finrank ℝ E₁ = 2) (h₂ : Module.finrank ℝ E₂ = 3)
  (α₂ : DifferentialForm I₁ Sf 2) (η₃ : DifferentialForm I₂ N 3)
include h₁ h₂

omit [FiniteDimensional ℝ E₂] h₂ in
/-- No curvature in form degree three. -/
theorem productLawConnection_curv3 (t : ℝ) :
    (productLawConnection α₂ η₃ t).curv3 = 0 := by
  simp [LawConnection.curv3, productLawConnection, lawDiff_tmul,
    exteriorDerivative_pr1Form_eq_zero h₁]

omit [FiniteDimensional ℝ E₁] h₁ in
/-- No curvature in form degree four: the correction `tηy` is an order-four partial flattening. -/
theorem productLawConnection_curv4 (t : ℝ) :
    (productLawConnection α₂ η₃ t).curv4 threeStoreyLaw = 0 := by
  simp only [LawConnection.curv4, productLawConnection, map_smul, lawDiff_tmul,
    exteriorDerivative_pr2Form_eq_zero h₂, TensorProduct.zero_tmul, smul_zero, zero_add]
  rw [lawBracket_tmul, bracket_gx_gx, TensorProduct.tmul_zero, smul_zero, smul_zero]

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] h₁ h₂ in
/-- **The later interaction curvature** `F₅(t) = −t ω ∧ η ⊗ w`. -/
theorem productLawConnection_curv5 (t : ℝ) :
    (productLawConnection α₂ η₃ t).curv5 threeStoreyLaw =
      (-t) • (productForm α₂ η₃ ⊗ₜ gw) := by
  simp only [LawConnection.curv5, productLawConnection, map_zero, zero_add, map_smul,
    LinearMap.smul_apply]
  rw [lawBracket_tmul, lawBracket_tmul, bracket_gx_gy, bracket_gy_gx, koszulSign_neg_one_three,
    koszulSign_neg_two_two, wedge_pr2Form_pr1Form, TensorProduct.tmul_neg]
  show _ = (-t) • (DifferentialForm.wedge (pr1Form α₂) (pr2Form η₃) ⊗ₜ gw)
  module

omit [I₁.Boundaryless] [I₂.Boundaryless] in
/-- The curvature has no components above form degree five. -/
theorem productLawConnection_curv_high (t : ℝ) :
    (productLawConnection α₂ η₃ t).curv6 threeStoreyLaw = 0 ∧
      (productLawConnection α₂ η₃ t).curv7 threeStoreyLaw = 0 ∧
        (productLawConnection α₂ η₃ t).curv8 threeStoreyLaw = 0 :=
  ⟨lawForm_eq_zero_of_dim_lt h₁ h₂ (by norm_num) _,
    lawForm_eq_zero_of_dim_lt h₁ h₂ (by norm_num) _,
    lawForm_eq_zero_of_dim_lt h₁ h₂ (by norm_num) _⟩

/-- `dF₅(t) = 0`. -/
theorem productLawConnection_curv5_closed (t : ℝ) :
    lawDiff 5 ((productLawConnection α₂ η₃ t).curv5 threeStoreyLaw) = 0 :=
  lawForm_eq_zero_of_dim_lt h₁ h₂ (by norm_num) _

/-- The first summand `ω x` alone. -/
def firstSummand : LawConnection (I₁.prod I₂) (Sf × N) ThreeStorey := ⟨pr1Form α₂ ⊗ₜ gx, 0, 0⟩

/-- The second summand `t η y` alone. -/
def secondSummand (t : ℝ) : LawConnection (I₁.prod I₂) (Sf × N) ThreeStorey :=
  ⟨0, t • (pr2Form η₃ ⊗ₜ gy), 0⟩

omit [FiniteDimensional ℝ E₂] h₂ in
/-- **The proper components are separately flat**: `Curv(ωx) = 0`. -/
theorem firstSummand_flat :
    (firstSummand (I₂ := I₂) (N := N) α₂).curv3 = 0 ∧
      (firstSummand (I₂ := I₂) (N := N) α₂).curv4 threeStoreyLaw = 0 ∧
        (firstSummand (I₂ := I₂) (N := N) α₂).curv5 threeStoreyLaw = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [LawConnection.curv3, firstSummand, lawDiff_tmul, exteriorDerivative_pr1Form_eq_zero h₁]
  · simp only [LawConnection.curv4, firstSummand, map_zero, zero_add]
    rw [lawBracket_tmul, bracket_gx_gx, TensorProduct.tmul_zero, smul_zero, smul_zero]
  · simp [LawConnection.curv5, firstSummand]

omit [FiniteDimensional ℝ E₁] h₁ in
/-- `Curv(tηy) = 0`. -/
theorem secondSummand_flat (t : ℝ) :
    (secondSummand (I₁ := I₁) (Sf := Sf) η₃ t).curv3 = 0 ∧
      (secondSummand (I₁ := I₁) (Sf := Sf) η₃ t).curv4 threeStoreyLaw = 0 ∧
        (secondSummand (I₁ := I₁) (Sf := Sf) η₃ t).curv5 threeStoreyLaw = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [LawConnection.curv3, secondSummand]
  · simp [LawConnection.curv4, secondSummand, lawDiff_tmul,
      exteriorDerivative_pr2Form_eq_zero h₂]
  · simp [LawConnection.curv5, secondSummand]

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [I₁.Boundaryless] [I₂.Boundaryless] h₁
  h₂ in
/-- `a_t = ωx + tηy`. -/
theorem productLawConnection_eq_add (t : ℝ) :
    productLawConnection α₂ η₃ t = firstSummand α₂ + secondSummand η₃ t := by
  simp only [productLawConnection, firstSummand, secondSummand]
  rfl

end Curvature

/-! ## Period reconstruction -/

section Periods

variable [MeasurableSpace E₁] [BorelSpace E₁] [MeasurableSpace E₂] [BorelSpace E₂] [T2Space Sf]
  [CompactSpace Sf] [T2Space N] [CompactSpace N]
  (μ₁ : MeasureTheory.Measure E₁) [μ₁.IsAddHaarMeasure] (μ₂ : MeasureTheory.Measure E₂)
  [μ₂.IsAddHaarMeasure] (o₁ : ManifoldOrientation I₁ Sf 2) (o₂ : ManifoldOrientation I₂ N 3)
  (e₁ : Orientation ℝ E₁ (Fin 2)) (e₂ : Orientation ℝ E₂ (Fin 3)) (b₁ : Fin 2 → E₁)
  (b₂ : Fin 3 → E₂) (α₂ : DifferentialForm I₁ Sf 2) (η₃ : DifferentialForm I₂ N 3)

/-- **The lifted fifth period** `Π(t) = ∫_{Σ×N} F₅(t)`. -/
def lawPeriod (t : ℝ) : ThreeStorey :=
  lawIntegral (μ₁.prod μ₂) (prodManifoldOrientation o₁ o₂)
    (prodOrientation o₁.dimension_eq o₂.dimension_eq e₁ e₂) (splitFrame b₁ b₂)
    ((productLawConnection α₂ η₃ t).curv5 threeStoreyLaw)

/-- **The period formula**: `Π(t) = −t m n w`, with `m = ∫_Σ ω`, `n = ∫_N η`. -/
theorem lawPeriod_eq (t : ℝ) :
    lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ t =
      (-t * topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃) • gw := by
  rw [lawPeriod, productLawConnection_curv5, map_smul,
    lawIntegral_tmul, topFormIntegral_productForm, smul_smul]
  ring_nf

/-- **Period reconstruction**: the vanishing conditions on parameter, curvature, class and
period are equivalent. -/
theorem period_reconstruction (hm : topFormIntegral μ₁ o₁ e₁ b₁ α₂ ≠ 0)
    (hn : topFormIntegral μ₂ o₂ e₂ b₂ η₃ ≠ 0) (t : ℝ) :
    List.TFAE [t = 0,
      (productLawConnection α₂ η₃ t).curv5 threeStoreyLaw = 0,
      lawClass (k := 4) (by rw [Module.finrank_prod, o₁.dimension_eq, o₂.dimension_eq])
        ((productLawConnection α₂ η₃ t).curv5 threeStoreyLaw) = 0,
      lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ t = 0] := by
  tfae_have 1 → 2 := by
    intro ht
    rw [productLawConnection_curv5, ht, neg_zero, zero_smul]
  tfae_have 2 → 3 := by
    intro h
    rw [h, map_zero]
  tfae_have 3 → 4 := by
    intro h
    rw [lawPeriod, ← lawCohomologyIntegral_lawClass (k := 4) (μ₁.prod μ₂)
      (prodManifoldOrientation o₁ o₂ :)
      (prodOrientation o₁.dimension_eq o₂.dimension_eq e₁ e₂ :) (splitFrame b₁ b₂ :)
      (by rw [Module.finrank_prod, o₁.dimension_eq, o₂.dimension_eq]), h, map_zero]
  tfae_have 4 → 1 := by
    intro h
    rw [lawPeriod_eq] at h
    have hw : gw ≠ 0 := by simp [gw]
    have hc := (smul_eq_zero.mp h).resolve_right hw
    have : t * (topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃) = 0 := by
      linear_combination -hc
    exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero hm hn)
  tfae_finish

/-- **Reconstruction of the partial-flattening parameter**:
`t = −Π(t)_w / (m n)`. -/
theorem parameter_eq_neg_period_div (hm : topFormIntegral μ₁ o₁ e₁ b₁ α₂ ≠ 0)
    (hn : topFormIntegral μ₂ o₂ e₂ b₂ η₃ ≠ 0) (t : ℝ) :
    t = -(lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ t).2.2 /
      (topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃) := by
  rw [lawPeriod_eq]
  simp only [gw, Prod.smul_mk, smul_eq_mul, mul_one]
  field_simp

/-! ## Obstruction and period spectra -/

/-- Corrections of `a₀` that keep the curvature zero through form degree four
(order-four partial flattenings). -/
def partialFlatteningsFour (a₀ : LawConnection (I₁.prod I₂) (Sf × N) ThreeStorey) :
    Set (LawConnection (I₁.prod I₂) (Sf × N) ThreeStorey) :=
  {β | (a₀ + β).curv3 = 0 ∧ (a₀ + β).curv4 threeStoreyLaw = 0}

/-- The fifth obstruction spectrum: classes of the degree-five curvature over all order-four
partial flattenings. -/
def obstructionSpectrumFive (a₀ : LawConnection (I₁.prod I₂) (Sf × N) ThreeStorey) :
    Set ((_root_.HTGeometry.SmoothDeRham.complex (IM := I₁.prod I₂) (M := Sf × N)).cohomology
      (4 + 1) ⊗[ℝ] ThreeStorey) :=
  (fun β => lawClass (k := 4) (by rw [Module.finrank_prod, o₁.dimension_eq, o₂.dimension_eq])
    ((a₀ + β).curv5 threeStoreyLaw)) '' partialFlatteningsFour a₀

omit [MeasurableSpace E₁] [BorelSpace E₁] [MeasurableSpace E₂] [BorelSpace E₂] [T2Space Sf]
  [CompactSpace Sf] [T2Space N] [CompactSpace N] in
/-- **The obstruction spectrum**: the obstruction spectrum of the flat base `ωx` contains the full
line of classes `−t [ω ∧ η] w`. -/
theorem obstructionSpectrumFive_contains_line (t : ℝ) :
    (-t) • lawClass (k := 4) (by rw [Module.finrank_prod, o₁.dimension_eq, o₂.dimension_eq])
        ((productForm α₂ η₃ :) ⊗ₜ gw) ∈
      obstructionSpectrumFive o₁ o₂ (firstSummand α₂) := by
  refine ⟨secondSummand η₃ t, ⟨?_, ?_⟩, ?_⟩
  · rw [← productLawConnection_eq_add]
    exact productLawConnection_curv3 o₁.dimension_eq α₂ η₃ t
  · rw [← productLawConnection_eq_add]
    exact productLawConnection_curv4 o₂.dimension_eq α₂ η₃ t
  · simp only
    rw [← productLawConnection_eq_add,
      productLawConnection_curv5, map_smul]

/-- **The period spectrum**: `{Π(t)} = ℝ w`. -/
theorem range_lawPeriod (hm : topFormIntegral μ₁ o₁ e₁ b₁ α₂ ≠ 0)
    (hn : topFormIntegral μ₂ o₂ e₂ b₂ η₃ ≠ 0) :
    Set.range (lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃) = ((ℝ ∙ gw : Submodule ℝ ThreeStorey) :
      Set ThreeStorey) := by
  ext v
  simp only [Set.mem_range, SetLike.mem_coe, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, (lawPeriod_eq μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ t).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨-c / (topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃), ?_⟩
    rw [lawPeriod_eq]
    congr 1
    field_simp

/-- The period is linear in the partial-flattening parameter: `Π(t) = t · (−m n w)`. -/
theorem lawPeriod_eq_toSpanSingleton (t : ℝ) :
    lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ t =
      LinearMap.toSpanSingleton ℝ ThreeStorey
        ((-(topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃)) • gw) t := by
  rw [lawPeriod_eq, LinearMap.toSpanSingleton_apply, smul_smul]
  ring_nf

/-- The partial-flattening line embeds injectively into the period line. -/
theorem lawPeriod_injective (hm : topFormIntegral μ₁ o₁ e₁ b₁ α₂ ≠ 0)
    (hn : topFormIntegral μ₂ o₂ e₂ b₂ η₃ ≠ 0) :
    Function.Injective (lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃) := by
  intro s t hst
  rw [parameter_eq_neg_period_div μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ hm hn s,
    parameter_eq_neg_period_div μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ hm hn t, hst]

end Periods

/-! ## Proper faces do not see the interaction -/

/-- The law-valued pullback along a smooth map. -/
def lawPullback {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold I' ∞ M'] (f : M' → Sf × N) (hf : ContMDiff I' (I₁.prod I₂) ∞ f) (k : ℕ) :
    LawForm (I₁.prod I₂) (Sf × N) ThreeStorey k →ₗ[ℝ] LawForm I' M' ThreeStorey k :=
  TensorProduct.map (DifferentialForm.pullbackLinearMap f hf k) LinearMap.id

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [I₁.Boundaryless] [I₂.Boundaryless] in
/-- A law-valued form of degree above the dimension of the target restricts to zero. -/
theorem lawPullback_eq_zero_of_finrank_lt {E' H' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold I' ∞ M'] (f : M' → Sf × N) (hf : ContMDiff I' (I₁.prod I₂) ∞ f) {k : ℕ}
    (hk : Module.finrank ℝ E' < k) (A : LawForm (I₁.prod I₂) (Sf × N) ThreeStorey k) :
    lawPullback f hf k A = 0 := by
  induction A using TensorProduct.induction_on with
  | zero => simp
  | tmul α u =>
    rw [lawPullback, TensorProduct.map_tmul,
      _root_.HTGeometry.SmoothDeRham.differentialForm_eq_zero_of_finrank_lt hk
        (DifferentialForm.pullbackLinearMap f hf k α), TensorProduct.zero_tmul]
  | add A B hA hB => rw [map_add, hA, hB, add_zero]

/-- **Invisibility on proper faces**: the interaction curvature restricts to zero on every slice
`Σ × {y₀}` and `{x₀} × N`. -/
theorem curv5_restrict_slices (h₁ : Module.finrank ℝ E₁ = 2) (h₂ : Module.finrank ℝ E₂ = 3)
    (α₂ : DifferentialForm I₁ Sf 2) (η₃ : DifferentialForm I₂ N 3) (t : ℝ) (x₀ : Sf) (y₀ : N) :
    lawPullback (fun x : Sf => (x, y₀)) (contMDiff_id.prodMk contMDiff_const) 5
        ((productLawConnection α₂ η₃ t).curv5 threeStoreyLaw) = 0 ∧
      lawPullback (fun y : N => (x₀, y)) (contMDiff_const.prodMk contMDiff_id) 5
        ((productLawConnection α₂ η₃ t).curv5 threeStoreyLaw) = 0 :=
  ⟨lawPullback_eq_zero_of_finrank_lt _ _ (by omega) _,
    lawPullback_eq_zero_of_finrank_lt _ _ (by omega) _⟩

/-! ## Observers -/

section Observers

variable [MeasurableSpace E₁] [BorelSpace E₁] [MeasurableSpace E₂] [BorelSpace E₂] [T2Space Sf]
  [CompactSpace Sf] [T2Space N] [CompactSpace N]
  (μ₁ : MeasureTheory.Measure E₁) [μ₁.IsAddHaarMeasure] (μ₂ : MeasureTheory.Measure E₂)
  [μ₂.IsAddHaarMeasure] (o₁ : ManifoldOrientation I₁ Sf 2) (o₂ : ManifoldOrientation I₂ N 3)
  (e₁ : Orientation ℝ E₁ (Fin 2)) (e₂ : Orientation ℝ E₂ (Fin 3)) (b₁ : Fin 2 → E₁)
  (b₂ : Fin 3 → E₂) (α₂ : DifferentialForm I₁ Sf 2) (η₃ : DifferentialForm I₂ N 3)
  {V' : Type*} [AddCommGroup V'] [Module ℝ V'] {G' : GradedLieAlgebra V'}

/-- **Observer naturality**: `Curv(q a_t) = q F₅(t)` and `∫ Curv(q a_t) = q Π(t)`. -/
theorem observer_curv5_and_period (q : GradedLieHom threeStoreyLaw G') (t : ℝ) :
    ((productLawConnection α₂ η₃ t).map q.toLinearMap).curv5 G' =
        lawMap q.toLinearMap 5 ((productLawConnection α₂ η₃ t).curv5 threeStoreyLaw) ∧
      lawIntegral (μ₁.prod μ₂) (prodManifoldOrientation o₁ o₂)
          (prodOrientation o₁.dimension_eq o₂.dimension_eq e₁ e₂) (splitFrame b₁ b₂)
          (((productLawConnection α₂ η₃ t).map q.toLinearMap).curv5 G') =
        q.toLinearMap (lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ t) := by
  refine ⟨LawConnection.curv5_map q _, ?_⟩
  rw [LawConnection.curv5_map q, lawPeriod]
  exact lawIntegral_lawMap _ _ _ _ q.toLinearMap _

/-- **Sharp erasure criterion**: an observer erases the whole later interaction history
exactly when it kills `w`. -/
theorem observer_erases_iff (hm : topFormIntegral μ₁ o₁ e₁ b₁ α₂ ≠ 0)
    (hn : topFormIntegral μ₂ o₂ e₂ b₂ η₃ ≠ 0) (q : ThreeStorey →ₗ[ℝ] V') :
    (∀ t, q (lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ t) = 0) ↔ q gw = 0 := by
  constructor
  · intro h
    have h1 := h 1
    rw [lawPeriod_eq, map_smul] at h1
    refine (smul_eq_zero.mp h1).resolve_left ?_
    simpa using mul_ne_zero hm hn
  · intro h t
    rw [lawPeriod_eq, map_smul, h, smul_zero]

/-- **Joint reconstruction** by a family of observers: the family recovers `t` exactly when some
member does not kill `w`. -/
theorem observers_reconstruct_iff (hm : topFormIntegral μ₁ o₁ e₁ b₁ α₂ ≠ 0)
    (hn : topFormIntegral μ₂ o₂ e₂ b₂ η₃ ≠ 0) {ι : Type*} (q : ι → ThreeStorey →ₗ[ℝ] V') :
    Function.Injective (fun t i => q i (lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ t)) ↔
      ∃ i, q i gw ≠ 0 := by
  have hmn : topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃ ≠ 0 :=
    mul_ne_zero hm hn
  constructor
  · intro hinj
    by_contra hall
    push Not at hall
    have h01 : (fun i => q i (lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ 0)) =
        (fun i => q i (lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ 1)) := by
      funext i
      rw [lawPeriod_eq, lawPeriod_eq, map_smul, map_smul, hall i, smul_zero, smul_zero]
    exact zero_ne_one (hinj h01)
  · rintro ⟨i, hi⟩ s t hst
    have h := congrFun hst i
    simp only [lawPeriod_eq, map_smul] at h
    have h' := sub_eq_zero.mpr h
    rw [← sub_smul] at h'
    have hc := (smul_eq_zero.mp h').resolve_right hi
    have : (s - t) * (topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃) = 0 := by
      linear_combination -hc
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hmn)

/-- Serial observation cannot repair erasure: a later observer receives zero. -/
theorem serial_observer_erases {V'' : Type*} [AddCommGroup V''] [Module ℝ V'']
    (q : ThreeStorey →ₗ[ℝ] V') (hq : q gw = 0) (q' : V' →ₗ[ℝ] V'') (t : ℝ) :
    q' (q (lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ t)) = 0 := by
  rw [lawPeriod_eq, map_smul, hq, smul_zero, map_zero]

/-- **Cyclic completion**: pushed into the shifted cotangent double `T*[d]L`, the
product connection has curvature the image of `F₅(t)` and period `(Π(t), 0)`; the completed period
still recovers the partial-flattening parameter. -/
theorem cyclicCompletion_curv5_and_period (d : ℤ) (t : ℝ) :
    ((productLawConnection α₂ η₃ t).map (cotangentInclusion (d := d)).toLinearMap).curv5
        (cotangentLaw d) =
      lawMap (cotangentInclusion (d := d)).toLinearMap 5
        ((productLawConnection α₂ η₃ t).curv5 threeStoreyLaw) ∧
    lawIntegral (μ₁.prod μ₂) (prodManifoldOrientation o₁ o₂)
        (prodOrientation o₁.dimension_eq o₂.dimension_eq e₁ e₂) (splitFrame b₁ b₂)
        (((productLawConnection α₂ η₃ t).map (cotangentInclusion (d := d)).toLinearMap).curv5
          (cotangentLaw d)) =
      (lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ t, 0) :=
  observer_curv5_and_period μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ cotangentInclusion t

theorem cyclicCompletion_period_injective (hm : topFormIntegral μ₁ o₁ e₁ b₁ α₂ ≠ 0)
    (hn : topFormIntegral μ₂ o₂ e₂ b₂ η₃ ≠ 0) (d : ℤ) :
    Function.Injective fun t => lawIntegral (μ₁.prod μ₂) (prodManifoldOrientation o₁ o₂)
      (prodOrientation o₁.dimension_eq o₂.dimension_eq e₁ e₂) (splitFrame b₁ b₂)
      (((productLawConnection α₂ η₃ t).map (cotangentInclusion (d := d)).toLinearMap).curv5
        (cotangentLaw d)) := by
  intro s t hst
  simp only [(cyclicCompletion_curv5_and_period μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ d _).2,
    Prod.mk.injEq, and_true] at hst
  exact lawPeriod_injective μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ hm hn hst

end Observers

/-! ## Recurrent compact period phase with proper lifted history -/

section Recurrence

variable [MeasurableSpace E₁] [BorelSpace E₁] [MeasurableSpace E₂] [BorelSpace E₂] [T2Space Sf]
  [CompactSpace Sf] [T2Space N] [CompactSpace N]
  (μ₁ : MeasureTheory.Measure E₁) [μ₁.IsAddHaarMeasure] (μ₂ : MeasureTheory.Measure E₂)
  [μ₂.IsAddHaarMeasure] (o₁ : ManifoldOrientation I₁ Sf 2) (o₂ : ManifoldOrientation I₂ N 3)
  (e₁ : Orientation ℝ E₁ (Fin 2)) (e₂ : Orientation ℝ E₂ (Fin 3)) (b₁ : Fin 2 → E₁)
  (b₂ : Fin 3 → E₂) (α₂ : DifferentialForm I₁ Sf 2) (η₃ : DifferentialForm I₂ N 3)

/-- The period lattice `Λ = ℓ ℤ w`. -/
def periodLattice (ℓ : ℝ) : AddSubgroup ThreeStorey := AddSubgroup.zmultiples (ℓ • gw)

/-- The compact period-phase observer `h_ℓ(t) = Π(t) mod Λ`. -/
def periodPhase (ℓ : ℝ) (t : ℝ) : ThreeStorey ⧸ periodLattice ℓ :=
  QuotientAddGroup.mk (lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ t)

/-- **Exact recurrence**: with `T = ℓ/|mn|`, `h_ℓ(t + T) = h_ℓ(t)`. -/
theorem periodPhase_periodic (hm : topFormIntegral μ₁ o₁ e₁ b₁ α₂ ≠ 0)
    (hn : topFormIntegral μ₂ o₂ e₂ b₂ η₃ ≠ 0) (ℓ : ℝ) (t : ℝ) :
    periodPhase μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ ℓ
        (t + ℓ / |topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃|) =
      periodPhase μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ ℓ t := by
  set m := topFormIntegral μ₁ o₁ e₁ b₁ α₂
  set n := topFormIntegral μ₂ o₂ e₂ b₂ η₃
  have hc0 : m * n ≠ 0 := mul_ne_zero hm hn
  unfold periodPhase
  rw [QuotientAddGroup.eq, lawPeriod_eq, lawPeriod_eq]
  rw [show -((-(t + ℓ / |m * n|) * m * n) • gw) + (-t * m * n) • gw =
      (ℓ / |m * n| * (m * n)) • gw by rw [← neg_smul, ← add_smul]; congr 1; ring]
  rcases lt_or_gt_of_ne hc0 with h | h
  · refine ⟨-1, ?_⟩
    rw [abs_of_neg h]
    show (-1 : ℤ) • (ℓ • gw) = _
    rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    congr 1
    field_simp
    push_cast
    ring
  · refine ⟨1, ?_⟩
    rw [abs_of_pos h]
    show (1 : ℤ) • (ℓ • gw) = _
    rw [one_zsmul]
    congr 1
    field_simp

/-- **Linear escape of the lift**: along `t_k = kT` the lifted period has size
`k ℓ ‖w‖` for any norm on the marked line. -/
theorem lawPeriod_norm_at_recurrences (hm : topFormIntegral μ₁ o₁ e₁ b₁ α₂ ≠ 0)
    (hn : topFormIntegral μ₂ o₂ e₂ b₂ η₃ ≠ 0) {ℓ : ℝ} (hℓ : 0 < ℓ) (nrm : ThreeStorey → ℝ)
    (hnrm : ∀ c : ℝ, nrm (c • gw) = |c| * nrm gw) (k : ℕ) :
    nrm (lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃
      (k * (ℓ / |topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃|))) =
      k * ℓ * nrm gw := by
  have hc0 := mul_ne_zero hm hn
  rw [lawPeriod_eq, hnrm]
  congr 1
  rw [show -(↑k * (ℓ / |topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃|)) *
      topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃ =
      -(↑k * ℓ) * ((topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃) /
        |topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃|) by ring,
    abs_mul, abs_neg, abs_div, abs_abs, div_self (abs_ne_zero.mpr hc0), mul_one,
    abs_of_nonneg (by positivity)]

theorem lawPeriod_norm_tendsto (hm : topFormIntegral μ₁ o₁ e₁ b₁ α₂ ≠ 0)
    (hn : topFormIntegral μ₂ o₂ e₂ b₂ η₃ ≠ 0) {ℓ : ℝ} (hℓ : 0 < ℓ) (nrm : ThreeStorey → ℝ)
    (hnrm : ∀ c : ℝ, nrm (c • gw) = |c| * nrm gw) (hw : 0 < nrm gw) :
    Filter.Tendsto (fun k : ℕ => nrm (lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃
      (k * (ℓ / |topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃|))))
      Filter.atTop Filter.atTop := by
  simp_rw [lawPeriod_norm_at_recurrences μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ hm hn hℓ nrm hnrm,
    mul_assoc]
  exact tendsto_natCast_atTop_atTop.atTop_mul_const (mul_pos hℓ hw)

/-- The lifted action `A(t) = ‖Π(t)‖²`. -/
theorem lawPeriod_action_eq (nrm : ThreeStorey → ℝ) (hnrm : ∀ c : ℝ, nrm (c • gw) = |c| * nrm gw)
    (t : ℝ) :
    nrm (lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ t) ^ 2 =
      topFormIntegral μ₁ o₁ e₁ b₁ α₂ ^ 2 * topFormIntegral μ₂ o₂ e₂ b₂ η₃ ^ 2 * nrm gw ^ 2 *
        t ^ 2 := by
  rw [lawPeriod_eq, hnrm, mul_pow, sq_abs]
  ring

/-- **Properness of the lifted action**: `A(t) → ∞` as `|t| → ∞`, and
`A(t) = 0 ⟺ t = 0`. -/
theorem lawPeriod_action_proper (hm : topFormIntegral μ₁ o₁ e₁ b₁ α₂ ≠ 0)
    (hn : topFormIntegral μ₂ o₂ e₂ b₂ η₃ ≠ 0) (nrm : ThreeStorey → ℝ)
    (hnrm : ∀ c : ℝ, nrm (c • gw) = |c| * nrm gw) (hw : 0 < nrm gw) :
    Filter.Tendsto (fun t => nrm (lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ t) ^ 2)
        (Filter.cocompact ℝ) Filter.atTop ∧
      ∀ t, nrm (lawPeriod μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ t) ^ 2 = 0 ↔ t = 0 := by
  have hK : 0 < topFormIntegral μ₁ o₁ e₁ b₁ α₂ ^ 2 * topFormIntegral μ₂ o₂ e₂ b₂ η₃ ^ 2 *
      nrm gw ^ 2 := by positivity
  refine ⟨?_, fun t => ?_⟩
  · simp_rw [lawPeriod_action_eq μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ nrm hnrm]
    refine Filter.Tendsto.const_mul_atTop hK ?_
    rw [cocompact_eq_atBot_atTop, Filter.tendsto_sup]
    refine ⟨?_, Filter.tendsto_pow_atTop two_ne_zero⟩
    have h := (Filter.tendsto_pow_atTop (α := ℝ) two_ne_zero).comp Filter.tendsto_neg_atBot_atTop
    simpa [Function.comp_def] using h
  · rw [lawPeriod_action_eq μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ α₂ η₃ nrm hnrm]
    constructor
    · intro h
      exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp ((mul_eq_zero.mp h).resolve_left hK.ne')
    · rintro rfl
      ring

omit [I₁.Boundaryless] [I₂.Boundaryless] [BorelSpace E₁] [BorelSpace E₂] [μ₁.IsAddHaarMeasure]
  [μ₂.IsAddHaarMeasure] in
/-- Recurrence period times escape slope is the lattice length:
`(ℓ/|mn|) · (|mn| ‖w‖) = ℓ ‖w‖`. -/
theorem recurrence_period_mul_escape_slope (hm : topFormIntegral μ₁ o₁ e₁ b₁ α₂ ≠ 0)
    (hn : topFormIntegral μ₂ o₂ e₂ b₂ η₃ ≠ 0) (ℓ : ℝ) (nrm : ThreeStorey → ℝ) :
    ℓ / |topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃| *
        (|topFormIntegral μ₁ o₁ e₁ b₁ α₂ * topFormIntegral μ₂ o₂ e₂ b₂ η₃| * nrm gw) =
      ℓ * nrm gw := by
  have h := abs_ne_zero.mpr (mul_ne_zero hm hn)
  field_simp

end Recurrence

end

end GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry

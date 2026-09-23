import Mathlib.Analysis.Normed.Module.Basic

/-!
# Repair torsors and the least-work selector no-go

The projection `K × W → W` has an affine space of linear splittings.  Vertical shears act simply
transitively on that space, so exact repair data contain no invariant origin.  Moreover every
splitting is the unique minimum of an explicitly manufactured positive squared-norm cost on each
fibre.  Thus least-work selection becomes constitutive only after its cost geometry is derived
independently.
-/

namespace GaloisForLFunctions.HTGeometry

section AlgebraicRepairTorsor

variable {𝕜 K W : Type*} [Field 𝕜]
  [AddCommGroup K] [Module 𝕜 K]
  [AddCommGroup W] [Module 𝕜 W]

/-- Projection from repair-plus-target data to the target. -/
def constitutiveRepairProjection : K × W →ₗ[𝕜] W where
  toFun := Prod.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- First-coordinate map used to recover the parameter of a splitting. -/
def constitutiveRepairFirst : K × W →ₗ[𝕜] K where
  toFun := Prod.fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Linear splitting with vertical parameter `h`. -/
def constitutiveRepairSection (h : W →ₗ[𝕜] K) : W →ₗ[𝕜] K × W where
  toFun w := (h w, w)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- Vertical shear preserving the target projection. -/
def constitutiveRepairShear (a : W →ₗ[𝕜] K) : K × W →ₗ[𝕜] K × W where
  toFun x := (x.1 + a x.2, x.2)
  map_add' x y := by simp [add_assoc, add_left_comm, add_comm]
  map_smul' c x := by simp [smul_add]

/-- Every vertical shear is a linear automorphism, with inverse shear `-a`. -/
def constitutiveRepairShearEquiv (a : W →ₗ[𝕜] K) :
    (K × W) ≃ₗ[𝕜] (K × W) where
  toLinearMap := constitutiveRepairShear a
  invFun := constitutiveRepairShear (-a)
  left_inv x := by ext <;> simp [constitutiveRepairShear]
  right_inv x := by ext <;> simp [constitutiveRepairShear]

/-- Every displayed repair section splits the target projection. -/
theorem constitutiveRepairProjection_section (h : W →ₗ[𝕜] K) :
    constitutiveRepairProjection.comp (constitutiveRepairSection h) = LinearMap.id := by
  ext w
  rfl

/-- Vertical shears preserve the target projection exactly. -/
theorem constitutiveRepairProjection_shear (a : W →ₗ[𝕜] K) :
    constitutiveRepairProjection.comp (constitutiveRepairShear a) =
      constitutiveRepairProjection := by
  rfl

/-- **Splitting classification.** Every linear splitting is uniquely determined by its vertical
coordinate. -/
theorem constitutiveRepairSection_classification (s : W →ₗ[𝕜] K × W)
    (hs : constitutiveRepairProjection.comp s = LinearMap.id) :
    s = constitutiveRepairSection (constitutiveRepairFirst.comp s) := by
  ext w
  · rfl
  · have hw := LinearMap.congr_fun hs w
    exact hw

/-- Repair parameters are recovered faithfully from their sections. -/
theorem constitutiveRepairSection_injective :
    Function.Injective
      (constitutiveRepairSection (𝕜 := 𝕜) (K := K) (W := W)) := by
  intro h h' heq
  ext w
  have hw := LinearMap.congr_fun heq w
  exact congrArg Prod.fst hw

/-- Shearing a section translates its affine repair parameter. -/
theorem constitutiveRepairShear_section (a h : W →ₗ[𝕜] K) :
    (constitutiveRepairShear a).comp (constitutiveRepairSection h) =
      constitutiveRepairSection (h + a) := by
  ext w <;> simp [constitutiveRepairShear, constitutiveRepairSection, add_comm]

/-- Any repair selector is transported to any other by an explicit shear. -/
theorem constitutiveRepairShear_transitive (h h' : W →ₗ[𝕜] K) :
    (constitutiveRepairShear (h' - h)).comp (constitutiveRepairSection h) =
      constitutiveRepairSection h' := by
  rw [constitutiveRepairShear_section]
  ext w <;> simp [constitutiveRepairSection]

/-- **Simple transitivity.** The unique shear sending `h` to `h'` has parameter `h' - h`. -/
theorem constitutiveRepairShear_section_eq_iff (a h h' : W →ₗ[𝕜] K) :
    (constitutiveRepairShear a).comp (constitutiveRepairSection h) =
        constitutiveRepairSection h' ↔
      a = h' - h := by
  rw [constitutiveRepairShear_section]
  constructor
  · intro heq
    have hh : h + a = h' := constitutiveRepairSection_injective heq
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hh)
  · intro ha
    rw [ha]
    ext w <;> simp [constitutiveRepairSection]

/-- **No intrinsic selector.** A nonzero vertical shear fixes no repair section. -/
theorem constitutiveRepairShear_no_fixed_section (a : W →ₗ[𝕜] K) (ha : a ≠ 0)
    (h : W →ₗ[𝕜] K) :
    (constitutiveRepairShear a).comp (constitutiveRepairSection h) ≠
      constitutiveRepairSection h := by
  rw [constitutiveRepairShear_section]
  intro heq
  have hh := constitutiveRepairSection_injective heq
  apply ha
  have hadd : h + a = h + 0 := by simpa using hh
  exact add_left_cancel hadd

end AlgebraicRepairTorsor

section ManufacturedLeastWork

variable {K W : Type*}
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Squared-norm cost manufactured around the repair selector `h`. -/
def constitutiveRepairCost (h : W →ₗ[ℝ] K) (x : K × W) : ℝ :=
  ‖x.1 - h x.2‖ ^ (2 : ℕ) + ‖x.2‖ ^ (2 : ℕ)

/-- The selected lift has only the target contribution to its manufactured cost. -/
theorem constitutiveRepairCost_section (h : W →ₗ[ℝ] K) (w : W) :
    constitutiveRepairCost h (constitutiveRepairSection h w) = ‖w‖ ^ (2 : ℕ) := by
  simp [constitutiveRepairCost, constitutiveRepairSection]

/-- Exact Pythagorean decomposition of every lift around the selected repair. -/
theorem constitutiveRepairCost_decomposition (h : W →ₗ[ℝ] K) (w : W) (z : K) :
    constitutiveRepairCost h (h w + z, w) =
      constitutiveRepairCost h (constitutiveRepairSection h w) + ‖z‖ ^ (2 : ℕ) := by
  simp [constitutiveRepairCost, constitutiveRepairSection, add_comm]

/-- Every repair selector is a minimum-cost lift for the cost manufactured around it. -/
theorem constitutiveRepairCost_minimal (h : W →ₗ[ℝ] K) (w : W) (x : K × W)
    (hx : constitutiveRepairProjection (𝕜 := ℝ) x = w) :
    constitutiveRepairCost h (constitutiveRepairSection h w) ≤
      constitutiveRepairCost h x := by
  change x.2 = w at hx
  subst w
  rw [constitutiveRepairCost_section]
  simp only [constitutiveRepairCost]
  exact le_add_of_nonneg_left (sq_nonneg ‖x.1 - h x.2‖)

/-- **Manufactured least-work no-go.** In each fibre the chosen repair is the unique minimizer of
its manufactured cost, for every possible repair parameter `h`. -/
theorem constitutiveRepairCost_eq_min_iff (h : W →ₗ[ℝ] K) (w : W) (x : K × W)
    (hx : constitutiveRepairProjection (𝕜 := ℝ) x = w) :
    constitutiveRepairCost h x =
        constitutiveRepairCost h (constitutiveRepairSection h w) ↔
      x = constitutiveRepairSection h w := by
  change x.2 = w at hx
  subst w
  rw [constitutiveRepairCost_section]
  simp only [constitutiveRepairCost]
  constructor
  · intro heq
    have hz : ‖x.1 - h x.2‖ ^ (2 : ℕ) = 0 := by linarith
    have hfirst : x.1 = h x.2 := by
      have hnorm : ‖x.1 - h x.2‖ = 0 := (sq_eq_zero_iff).mp hz
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    ext <;> simp [constitutiveRepairSection, hfirst]
  · intro heq
    rw [heq]
    simp [constitutiveRepairSection]

/-- Closed capstone: every displayed repair section is the unique minimizer of some explicit
positive squared-norm cost on every target fibre. -/
theorem constitutiveEveryRepairSelector_isManufacturedUniqueMinimum :
    ∀ (h : W →ₗ[ℝ] K) (w : W) (x : K × W),
      constitutiveRepairProjection (𝕜 := ℝ) x = w →
        constitutiveRepairCost h (constitutiveRepairSection h w) ≤
            constitutiveRepairCost h x ∧
          (constitutiveRepairCost h x =
                constitutiveRepairCost h (constitutiveRepairSection h w) ↔
            x = constitutiveRepairSection h w) := by
  intro h w x hx
  exact ⟨constitutiveRepairCost_minimal h w x hx,
    constitutiveRepairCost_eq_min_iff h w x hx⟩

end ManufacturedLeastWork

end GaloisForLFunctions.HTGeometry

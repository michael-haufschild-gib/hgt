import GaloisForLFunctions.RHTower.FokasLenellsSpaceEstimates
import GaloisForLFunctions.RHTower.FokasLenellsTimeEstimates

/-!
# Joint space-time stability of the actual RH reconstruction

The separately proved spatial and temporal derivative bounds combine into
global quantitative control over both physical parameters. The same
Lipschitz constant works for both Hardy boundary values, the reconstruction
density, all traces, and all horizontal holomorphic slices.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem twoParameter_bound {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → ℝ → E) (A B : ℝ)
    (ht : ∀ t s x, ‖f t x-f s x‖ ≤ A*|t-s|)
    (hx : ∀ t x y, ‖f t x-f t y‖ ≤ B*|x-y|) (t x s y : ℝ) :
    ‖f t x-f s y‖ ≤ A*|t-s|+B*|x-y| := by
  calc
    _ = ‖(f t x-f s x)+(f s x-f s y)‖ := by congr 1; abel
    _ ≤ ‖f t x-f s x‖+‖f s x-f s y‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (ht t s x) (hx s x y)

private theorem twoParameter_lipschitz {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → ℝ → E) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ t x s y, ‖f t x-f s y‖ ≤ A*|t-s|+B*|x-y|) :
    LipschitzWith ⟨A+B,add_nonneg hA hB⟩ (fun p : ℝ × ℝ => f p.1 p.2) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro p q
  have ht : |p.1-q.1| ≤ ‖p-q‖ := by
    change |p.1-q.1| ≤ max |p.1-q.1| |p.2-q.2|
    exact le_max_left _ _
  have hx : |p.2-q.2| ≤ ‖p-q‖ := by
    change |p.2-q.2| ≤ max |p.1-q.1| |p.2-q.2|
    exact le_max_right _ _
  calc
    _ ≤ A*|p.1-q.1|+B*|p.2-q.2| := hf _ _ _ _
    _ ≤ A*‖p-q‖+B*‖p-q‖ := add_le_add (mul_le_mul_of_nonneg_left ht hA) (mul_le_mul_of_nonneg_left hx hB)
    _ = _ := by change _ = (A+B)*‖p-q‖; ring

/-- A common finite Lipschitz constant for the full physical parameter plane. -/
def directSpaceTimeSize (q : SchwartzMap ℝ ℂ) : NNReal :=
  ⟨directRHTimeSize q+directRHSpaceSize q,add_nonneg (directRHTimeSize_nonneg q) (directRHSpaceSize_nonneg q)⟩

theorem directLowerCorrection_parameters_bound (q : SchwartzMap ℝ ℂ) (t x s y : ℝ) (i : Fin 2) :
    ‖directLowerCorrection q t x i-directLowerCorrection q s y i‖ ≤
      directRHTimeSize q*|t-s|+directRHSpaceSize q*|x-y| :=
  twoParameter_bound (fun t x => directLowerCorrection q t x i) _ _
    (fun t s x => directLowerCorrection_time_bound q t s x i) (fun t x y => directLowerCorrection_space_bound q t x y i) t x s y

theorem directUpperCorrection_parameters_bound (q : SchwartzMap ℝ ℂ) (t x s y : ℝ) (i : Fin 2) :
    ‖directUpperCorrection q t x i-directUpperCorrection q s y i‖ ≤
      directRHTimeSize q*|t-s|+directRHSpaceSize q*|x-y| :=
  twoParameter_bound (fun t x => directUpperCorrection q t x i) _ _
    (fun t s x => directUpperCorrection_time_bound q t s x i) (fun t x y => directUpperCorrection_space_bound q t x y i) t x s y

theorem directRHDensity_parameters_bound (q : SchwartzMap ℝ ℂ) (t x s y : ℝ) (i : Fin 2) :
    ‖directRHDensity q t x i-directRHDensity q s y i‖ ≤
      directRHTimeSize q*|t-s|+directRHSpaceSize q*|x-y| :=
  twoParameter_bound (fun t x => directRHDensity q t x i) _ _
    (fun t s x => directRHDensity_time_bound q t s x i) (fun t x y => directRHDensity_space_bound q t x y i) t x s y

theorem directTrace_parameters_bound (q : SchwartzMap ℝ ℂ) (t x s y : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) :
    ‖directTrace q t x i upper h-directTrace q s y i upper h‖ ≤
      directRHTimeSize q*|t-s|+directRHSpaceSize q*|x-y| :=
  twoParameter_bound (fun t x => directTrace q t x i upper h) _ _
    (fun t s x => directTrace_time_bound q t s x i upper h) (fun t x y => directTrace_space_bound q t x y i upper h) t x s y

theorem directAnalyticSlice_parameters_bound (q : SchwartzMap ℝ ℂ) (t x s y : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    ‖directAnalyticSlice q t x i upper a-directAnalyticSlice q s y i upper a‖ ≤
      directRHTimeSize q*|t-s|+directRHSpaceSize q*|x-y| :=
  twoParameter_bound (fun t x => directAnalyticSlice q t x i upper a) _ _
    (fun t s x => directAnalyticSlice_time_bound q t s x i upper a) (fun t x y => directAnalyticSlice_space_bound q t x y i upper a) t x s y

/-- The actual lower Hardy correction is globally Lipschitz over the entire space-time plane. -/
theorem directLowerCorrection_lipschitz_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    LipschitzWith (directSpaceTimeSize q) (fun p : ℝ × ℝ => directLowerCorrection q p.1 p.2 i) :=
  twoParameter_lipschitz _ _ _ (directRHTimeSize_nonneg q) (directRHSpaceSize_nonneg q)
    (fun t x s y => directLowerCorrection_parameters_bound q t x s y i)

theorem directUpperCorrection_lipschitz_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    LipschitzWith (directSpaceTimeSize q) (fun p : ℝ × ℝ => directUpperCorrection q p.1 p.2 i) :=
  twoParameter_lipschitz _ _ _ (directRHTimeSize_nonneg q) (directRHSpaceSize_nonneg q)
    (fun t x s y => directUpperCorrection_parameters_bound q t x s y i)

theorem directRHDensity_lipschitz_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    LipschitzWith (directSpaceTimeSize q) (fun p : ℝ × ℝ => directRHDensity q p.1 p.2 i) :=
  twoParameter_lipschitz _ _ _ (directRHTimeSize_nonneg q) (directRHSpaceSize_nonneg q)
    (fun t x s y => directRHDensity_parameters_bound q t x s y i)

/-- One Lipschitz constant works for all Cauchy trace heights, including the boundary. -/
theorem directTrace_lipschitz_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) (upper : Bool) (h : ℝ) :
    LipschitzWith (directSpaceTimeSize q) (fun p : ℝ × ℝ => directTrace q p.1 p.2 i upper h) :=
  twoParameter_lipschitz _ _ _ (directRHTimeSize_nonneg q) (directRHSpaceSize_nonneg q)
    (fun t x s y => directTrace_parameters_bound q t x s y i upper h)

/-- All actual holomorphic slices share the same global space-time Lipschitz constant. -/
theorem directAnalyticSlice_lipschitz_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    LipschitzWith (directSpaceTimeSize q) (fun p : ℝ × ℝ => directAnalyticSlice q p.1 p.2 i upper a) :=
  twoParameter_lipschitz _ _ _ (directRHTimeSize_nonneg q) (directRHSpaceSize_nonneg q)
    (fun t x s y => directAnalyticSlice_parameters_bound q t x s y i upper a)

/-- Joint physical-parameter stability of every actual off-contour matrix entry. -/
theorem directAnalyticMatrix_parameters_bound (q : SchwartzMap ℝ ℂ) (t x s y : ℝ)
    (i j : Fin 2) (upper : Bool) (r a : ℝ) :
    ‖directAnalyticMatrix q t x (halfPlanePoint upper r a) i j-directAnalyticMatrix q s y (halfPlanePoint upper r a) i j‖ ≤
      (2*Real.pi)⁻¹*Real.sqrt (Real.pi/Real.exp a)*(directRHTimeSize q*|t-s|+directRHSpaceSize q*|x-y|) := by
  have hh := twoParameter_bound (fun t x => directAnalyticMatrix q t x (halfPlanePoint upper r a) i j)
    ((2*Real.pi)⁻¹*Real.sqrt (Real.pi/Real.exp a)*directRHTimeSize q)
    ((2*Real.pi)⁻¹*Real.sqrt (Real.pi/Real.exp a)*directRHSpaceSize q)
    (fun t s x => directAnalyticMatrix_time_bound q t s x i j upper r a)
    (fun t x y => directAnalyticMatrix_space_bound q t x y i j upper r a) t x s y
  convert hh using 1
  ring

end
end RHTower.FokasLenells

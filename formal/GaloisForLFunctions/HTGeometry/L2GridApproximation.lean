import GaloisForLFunctions.HTGeometry.UniformGridStep
import GaloisForLFunctions.HTGeometry.FiniteApproxTotallyBounded
import Mathlib.MeasureTheory.Function.L2Space

/-!
# A Kolmogorov–Riesz criterion from a uniform derivative bound

A family of differentiable functions on the line which is uniformly bounded in `L²`, uniformly tight
in the height, and has a uniform `L²` bound on its derivatives is totally bounded in `L²`.  The
finite-dimensional approximants are the step functions of a uniform grid on `[-R, R]`: the grid
error is `mesh × ‖f'‖₂` by the interval Poincaré estimate, and the discarded tail is small by
tightness.
-/

open MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## `L²` norms of representatives -/

theorem norm_toLp_sq {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    ‖hf.toLp f‖ ^ 2 = ∫ x : ℝ, f x ^ 2 := by
  have h := @real_inner_self_eq_norm_sq (Lp ℝ 2 (volume : Measure ℝ)) _ _ (hf.toLp f)
  rw [← h, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]
  simp [sq]

theorem norm_toLp_sub_sq {f g : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x : ℝ, (f x - g x) ^ 2 := by
  have hsub : hf.toLp f - hg.toLp g = (hf.sub hg).toLp (fun x => f x - g x) :=
    (MemLp.toLp_sub hf hg).symm
  rw [hsub, norm_toLp_sq]

/-! ## The grid step function as an element of `L²` -/

/-- The `L²` class of the indicator of a grid cell. -/
def gridBasisLp (a h : ℝ) (j : ℕ) : Lp ℝ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 (measurableSet_gridCell a h j) measure_Ioc_lt_top.ne (1 : ℝ)

/-- The `L²` class of the left-endpoint step function of `f` on the grid. -/
def gridStepLp (f : ℝ → ℝ) (a h : ℝ) (M : ℕ) : Lp ℝ 2 (volume : Measure ℝ) :=
  ∑ j ∈ Finset.range M, f (a + j * h) • gridBasisLp a h j

theorem coeFn_gridStepLp (f : ℝ → ℝ) (a h : ℝ) (M : ℕ) :
    (gridStepLp f a h M : ℝ → ℝ) =ᵐ[volume] gridStep f a h M := by
  rw [gridStepLp]
  refine (Lp.coeFn_sum _ _).trans ?_
  have hterm : ∀ j ∈ Finset.range M,
      ((f (a + j * h) • gridBasisLp a h j : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ)
        =ᵐ[volume] fun x => f (a + j * h) * (gridCell a h j).indicator 1 x := by
    intro j _
    refine (Lp.coeFn_smul _ _).trans ?_
    filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
      (hs := measurableSet_gridCell a h j) (hμs := measure_Ioc_lt_top.ne) (c := (1 : ℝ))]
      with x hx
    rw [Pi.smul_apply, hx, smul_eq_mul]
    congr 1
    by_cases hxc : x ∈ gridCell a h j
    · rw [Set.indicator_of_mem hxc, Set.indicator_of_mem hxc]
      simp
    · rw [Set.indicator_of_notMem hxc, Set.indicator_of_notMem hxc]
  have hsum : (fun x : ℝ => ∑ j ∈ Finset.range M,
      ((f (a + j * h) • gridBasisLp a h j : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) x)
      =ᵐ[volume] fun x : ℝ => ∑ j ∈ Finset.range M,
        f (a + j * h) * (gridCell a h j).indicator 1 x := by
    have := (MeasureTheory.ae_all_iff (ι := { j // j ∈ Finset.range M })).2
      (fun j => hterm j.1 j.2)
    filter_upwards [this] with x hx
    refine Finset.sum_congr rfl fun j hj => ?_
    exact hx ⟨j, hj⟩
  exact hsum

theorem memLp_gridStep (f : ℝ → ℝ) (a h : ℝ) (M : ℕ) :
    MemLp (gridStep f a h M) 2 (volume : Measure ℝ) :=
  (Lp.memLp (gridStepLp f a h M)).ae_eq (coeFn_gridStepLp f a h M)

/-- The finite-dimensional span of the grid basis. -/
def gridSpace (a h : ℝ) (M : ℕ) : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)) :=
  Submodule.span ℝ (Set.range fun j : Fin M => gridBasisLp a h (j : ℕ))

theorem finiteDimensional_gridSpace (a h : ℝ) (M : ℕ) :
    FiniteDimensional ℝ (gridSpace a h M) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem gridStepLp_mem (f : ℝ → ℝ) (a h : ℝ) (M : ℕ) :
    gridStepLp f a h M ∈ gridSpace a h M := by
  rw [gridStepLp]
  refine Submodule.sum_mem _ fun j hj => ?_
  refine Submodule.smul_mem _ _ ?_
  refine Submodule.subset_span ?_
  simp only [Finset.mem_range] at hj
  exact ⟨⟨j, hj⟩, rfl⟩

end GaloisForLFunctions.HTGeometry

end

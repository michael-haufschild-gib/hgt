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
    ‖hf.toLp f‖ ^ (2 : ℕ) = ∫ x : ℝ, f x ^ (2 : ℕ) := by
  have h := @real_inner_self_eq_norm_sq (Lp ℝ 2 (volume : Measure ℝ)) _ _ (hf.toLp f)
  rw [← h, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]
  simp [sq]

theorem norm_toLp_sub_sq {f g : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    ‖hf.toLp f - hg.toLp g‖ ^ (2 : ℕ) = ∫ x : ℝ, (f x - g x) ^ (2 : ℕ) := by
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
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have hterm : ∀ j ∈ Finset.range M,
      ((f (a + j * h) • gridBasisLp a h j : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ)
        =ᵐ[volume] fun x => f (a + j * h) * (gridCell a h j).indicator 1 x := by
    intro j _
    refine (Lp.coeFn_smul _ _).trans ?_
    have hind : ⇑(gridBasisLp a h j) =ᵐ[volume] (gridCell a h j).indicator fun _ => (1 : ℝ) :=
      indicatorConstLp_coeFn
    filter_upwards [hind] with x hx
    rw [Pi.smul_apply, hx, smul_eq_mul]
    rfl
  have hsum : (fun x : ℝ => ∑ j ∈ Finset.range M,
      ((f (a + j * h) • gridBasisLp a h j : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) x)
      =ᵐ[volume] fun x : ℝ => ∑ j ∈ Finset.range M,
        f (a + j * h) * (gridCell a h j).indicator 1 x := by
    have := (MeasureTheory.ae_all_iff (ι := { j // j ∈ Finset.range M })).2
      (fun j => hterm j.1 j.2)
    filter_upwards [this] with x hx
    refine Finset.sum_congr rfl fun j hj => ?_
    exact hx ⟨j, hj⟩
  have hfun : (∑ i ∈ Finset.range M,
      ((f (a + i * h) • gridBasisLp a h i : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ))
      = fun x : ℝ => ∑ j ∈ Finset.range M,
        ((f (a + j * h) • gridBasisLp a h j : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) x := by
    funext x
    rw [Finset.sum_apply]
  rw [hfun]
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


theorem gridStepLp_eq_toLp (f : ℝ → ℝ) (a h : ℝ) (M : ℕ) :
    gridStepLp f a h M = (memLp_gridStep f a h M).toLp (gridStep f a h M) :=
  Lp.ext ((coeFn_gridStepLp f a h M).trans (MemLp.coeFn_toLp _).symm)

theorem compl_Ioc_ae_eq_abs_gt (R : ℝ) :
    (Set.Ioc (-R) R)ᶜ =ᵐ[volume] {x : ℝ | R < |x|} := by
  have hsub1 : (Set.Ioc (-R) R)ᶜ \ {x : ℝ | R < |x|} ⊆ {(-R : ℝ)} := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and] at hx1
    simp only [Set.mem_setOf_eq, not_lt] at hx2
    obtain ⟨hl, hu⟩ := abs_le.mp hx2
    have hx0 : ¬ (-R < x) := fun hlt => (hx1 hlt) hu
    have hxe : x = -R := le_antisymm (not_lt.mp hx0) hl
    simpa using hxe
  have hsub2 : {x : ℝ | R < |x|} \ (Set.Ioc (-R) R)ᶜ ⊆ (∅ : Set ℝ) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [Set.mem_compl_iff, not_not, Set.mem_Ioc] at hx2
    simp only [Set.mem_setOf_eq] at hx1
    obtain ⟨h1, h2⟩ := hx2
    have habs : |x| ≤ R := abs_le.mpr ⟨by linarith, h2⟩
    exact absurd hx1 (not_lt.mpr habs)
  exact MeasureTheory.ae_eq_set.2
    ⟨measure_mono_null hsub1 (by simp), measure_mono_null hsub2 (by simp)⟩

/-- **Kolmogorov–Riesz from a uniform derivative bound.**  A family of differentiable functions on
the line that is uniformly `L²`-bounded, uniformly tight, and has uniformly `L²`-bounded derivatives
is totally bounded in `L²`. -/
theorem totallyBounded_toLp_of_tight_deriv
    {ι : Type*} {f f' : ι → ℝ → ℝ} {Mb D : ℝ}
    (hmem : ∀ i : ι, MemLp (f i) 2 (volume : Measure ℝ))
    (hderiv : ∀ (i : ι) (x : ℝ), HasDerivAt (f i) (f' i x) x)
    (hcont' : ∀ i : ι, Continuous (f' i))
    (hbound : ∀ i : ι, ∫ x : ℝ, f i x ^ (2 : ℕ) ≤ Mb)
    (hD : 0 ≤ D)
    (hderivInt : ∀ i : ι, Integrable (fun x => f' i x ^ (2 : ℕ)) volume)
    (hderivBound : ∀ i : ι, ∫ x : ℝ, f' i x ^ (2 : ℕ) ≤ D)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ i : ι,
        (∫ x in {x : ℝ | R < |x|}, f i x ^ (2 : ℕ)) ≤ ε) :
    TotallyBounded (Set.range fun i : ι => (hmem i).toLp (f i)) := by
  refine totallyBounded_of_finiteDimensional_approx (M := Real.sqrt Mb) ?_ ?_
  · rintro g ⟨i, rfl⟩
    have h1 : ‖(hmem i).toLp (f i)‖ ^ (2 : ℕ) = ∫ x : ℝ, f i x ^ (2 : ℕ) := norm_toLp_sq _
    have h2 : ‖(hmem i).toLp (f i)‖ ^ (2 : ℕ) ≤ Mb := by
      rw [h1]
      exact hbound i
    have h3 : (0 : ℝ) ≤ ‖(hmem i).toLp (f i)‖ := norm_nonneg _
    have h4 := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq h3] at h4
  · intro ε hε
    obtain ⟨R, hR, htailR⟩ := htail (ε ^ (2 : ℕ) / 2) (by positivity)
    obtain ⟨Mc, hMc⟩ := exists_nat_gt (8 * R ^ (2 : ℕ) * (D + 1) / ε ^ (2 : ℕ))
    have hK0 : (0 : ℝ) < 8 * R ^ (2 : ℕ) * (D + 1) / ε ^ (2 : ℕ) := by positivity
    have hMc0 : 0 < Mc := by
      rcases Nat.eq_zero_or_pos Mc with hz | hp
      · exfalso
        rw [hz] at hMc
        simp only [Nat.cast_zero] at hMc
        linarith
      · exact hp
    have hMcR : (0 : ℝ) < (Mc : ℝ) := by exact_mod_cast hMc0
    obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = 2 * R / (Mc : ℝ) := ⟨_, rfl⟩
    have hh : 0 < h := by
      rw [hh_def]
      positivity
    have hend : -R + (Mc : ℝ) * h = R := by
      have hne : (Mc : ℝ) ≠ 0 := ne_of_gt hMcR
      rw [hh_def]
      field_simp
      ring
    refine ⟨gridSpace (-R) h Mc, finiteDimensional_gridSpace (-R) h Mc, ?_⟩
    rintro g ⟨i, rfl⟩
    refine ⟨gridStepLp (f i) (-R) h Mc, gridStepLp_mem _ _ _ _, ?_⟩
    -- the squared error splits into a grid part and a tail part
    have hmemStep : MemLp (gridStep (f i) (-R) h Mc) 2 (volume : Measure ℝ) :=
      memLp_gridStep _ _ _ _
    have hnorm : ‖(hmem i).toLp (f i) - gridStepLp (f i) (-R) h Mc‖ ^ (2 : ℕ)
        = ∫ x : ℝ, (f i x - gridStep (f i) (-R) h Mc x) ^ (2 : ℕ) := by
      rw [gridStepLp_eq_toLp]
      exact norm_toLp_sub_sq (hmem i) hmemStep
    have hintErr : Integrable (fun x : ℝ => (f i x - gridStep (f i) (-R) h Mc x) ^ (2 : ℕ)) volume := by
      refine (memLp_two_iff_integrable_sq ?_).1 ((hmem i).sub hmemStep)
      exact ((hmem i).sub hmemStep).aestronglyMeasurable
    have hsplit := MeasureTheory.integral_add_compl
      (μ := (volume : Measure ℝ)) (s := Set.Ioc (-R) R) measurableSet_Ioc hintErr
    have hgrid : (∫ x in Set.Ioc (-R) R, (f i x - gridStep (f i) (-R) h Mc x) ^ (2 : ℕ))
        ≤ h ^ (2 : ℕ) * D := by
      have hbase := integral_sub_gridStep_sq_le (f := f i) (f' := f' i) (a := -R) hh Mc
        (hderiv i) (hcont' i)
      rw [hend] at hbase
      have hle : (∫ x in Set.Ioc (-R) R, f' i x ^ (2 : ℕ)) ≤ D := by
        refine le_trans (MeasureTheory.setIntegral_le_integral (hderivInt i) ?_) (hderivBound i)
        filter_upwards with x
        exact sq_nonneg _
      have hpos : (0 : ℝ) ≤ h ^ (2 : ℕ) := sq_nonneg h
      calc (∫ x in Set.Ioc (-R) R, (f i x - gridStep (f i) (-R) h Mc x) ^ (2 : ℕ))
          ≤ h ^ (2 : ℕ) * ∫ x in Set.Ioc (-R) R, f' i x ^ (2 : ℕ) := hbase
        _ ≤ h ^ (2 : ℕ) * D := mul_le_mul_of_nonneg_left hle hpos
    have htailErr : (∫ x in (Set.Ioc (-R) R)ᶜ, (f i x - gridStep (f i) (-R) h Mc x) ^ (2 : ℕ))
        ≤ ε ^ (2 : ℕ) / 2 := by
      have hzero : ∀ x ∈ (Set.Ioc (-R) R)ᶜ,
          (f i x - gridStep (f i) (-R) h Mc x) ^ (2 : ℕ) = f i x ^ (2 : ℕ) := by
        intro x hx
        have := gridStep_eq_zero (f := f i) (a := -R) (h := h) hh.le (M := Mc) (x := x) (by
          rw [hend]
          exact hx)
        rw [this, sub_zero]
      have heq : (∫ x in (Set.Ioc (-R) R)ᶜ, f i x ^ (2 : ℕ))
          = ∫ x in {x : ℝ | R < |x|}, f i x ^ (2 : ℕ) :=
        MeasureTheory.setIntegral_congr_set (compl_Ioc_ae_eq_abs_gt R)
      rw [MeasureTheory.setIntegral_congr_fun (MeasurableSet.compl measurableSet_Ioc) hzero, heq]
      exact htailR i
    have hmeshD : h ^ (2 : ℕ) * D ≤ ε ^ (2 : ℕ) / 2 := by
      have hMcsq : 8 * R ^ (2 : ℕ) * (D + 1) / ε ^ (2 : ℕ) < (Mc : ℝ) ^ (2 : ℕ) := by
        have h1 : (1 : ℝ) ≤ (Mc : ℝ) := by exact_mod_cast hMc0
        nlinarith
      have hε2 : (0 : ℝ) < ε ^ (2 : ℕ) := by positivity
      rw [div_lt_iff₀ hε2] at hMcsq
      rw [hh_def]
      have hexp : (2 * R / (Mc : ℝ)) ^ (2 : ℕ) * D = 4 * R ^ (2 : ℕ) * D / (Mc : ℝ) ^ (2 : ℕ) := by
        field_simp
        ring
      rw [hexp, div_le_iff₀ (by positivity)]
      nlinarith
    have htotal : ‖(hmem i).toLp (f i) - gridStepLp (f i) (-R) h Mc‖ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) := by
      rw [hnorm, ← hsplit]
      linarith
    have hnn : (0 : ℝ) ≤ ‖(hmem i).toLp (f i) - gridStepLp (f i) (-R) h Mc‖ := norm_nonneg _
    nlinarith [htotal, hnn, hε]

end GaloisForLFunctions.HTGeometry

end

import GaloisForLFunctions.HTGeometry.PoincareHopf.LocalIndex

/-!
# Additivity of the Brouwer degree

If finitely many pairwise disjoint open subsets of `Ω` contain every solution of `f x = y` in the
closure of `Ω`, the degree on `Ω` is the sum of the degrees on the pieces.  A single admissible
radius works for `Ω` and for all the pieces at once, because every boundary involved lies in the
compact set where `f x ≠ y`; against that weight the degree integrand is supported inside the union
of the pieces, so the integral splits.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {Ω : Set (Fin n → ℝ)} {y : Fin n → ℝ}

/-- On a compact set avoiding the value `y`, the map stays a definite distance away. -/
theorem exists_pos_two_lt_of_isCompact {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hf : Continuous f) (hne : ∀ x ∈ K, f x ≠ y) :
    ∃ ρ > 0, ∀ x ∈ K, ρ + ρ < ‖f x - y‖ := by
  rcases eq_empty_or_nonempty K with hemp | hne'
  · exact ⟨1, one_pos, fun x hx => absurd hx (by rw [hemp]; exact notMem_empty x)⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne'
      (((hf.sub continuous_const).norm).continuousOn)
    have hpos : 0 < ‖f x₀ - y‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact hne x₀ hx₀
    refine ⟨‖f x₀ - y‖ / 3, by linarith, fun x hx => ?_⟩
    have hle : ‖f x₀ - y‖ ≤ ‖f x - y‖ := hmin hx
    linarith

/-- **Additivity of the degree** over finitely many disjoint open pieces. -/
theorem degree_eq_sum_of_disjoint {ι : Type*} [Fintype ι]
    (hf : ContDiff ℝ 2 f) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (U : ι → Set (Fin n → ℝ)) (hU : ∀ i, IsOpen (U i)) (hUsub : ∀ i, U i ⊆ Ω)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hout : ∀ x ∈ closure Ω \ (⋃ i, U i), f x ≠ y) :
    degree f Ω y = ∑ i, degree f (U i) y := by
  classical
  set K := closure Ω \ (⋃ i, U i) with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ (hΩb.closure.subset Set.sdiff_subset)
    exact isClosed_closure.sdiff (isOpen_iUnion hU)
  obtain ⟨ρ, hρpos, hρ⟩ := exists_pos_two_lt_of_isCompact hKc hf.continuous hout
  -- every boundary in sight lies in `K`
  have hfrontΩ : frontier Ω ⊆ K := by
    intro x hx
    rw [hΩ.frontier_eq] at hx
    refine ⟨hx.1, ?_⟩
    rintro ⟨S, ⟨i, rfl⟩, hxU⟩
    exact hx.2 (hUsub i hxU)
  have hfrontU : ∀ i, frontier (U i) ⊆ K := by
    intro i x hx
    rw [(hU i).frontier_eq] at hx
    refine ⟨closure_mono (hUsub i) hx.1, ?_⟩
    rintro ⟨S, ⟨j, rfl⟩, hxU⟩
    by_cases hij : j = i
    · exact hx.2 (hij ▸ hxU)
    · have hd := hdisj j i hij
      have hmem : x ∈ closure (U i) := hx.1
      have hnb : U j ∈ nhds x := (hU j).mem_nhds hxU
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff_nhds.mp hmem (U j) hnb
      exact Set.disjoint_left.mp hd hz1 hz2
  have hadmΩ : AdmissibleRadius f Ω y ρ := ⟨hρpos, fun x hx => hρ x (hfrontΩ hx)⟩
  have hadmU : ∀ i, AdmissibleRadius f (U i) y ρ :=
    fun i => ⟨hρpos, fun x hx => hρ x (hfrontU i hx)⟩
  have hbc : ContDiff ℝ 1 (bumpWeight (n := n) ρ) := bumpWeight_contDiff hρpos
  have hbs : ∀ w : Fin n → ℝ, ρ ≤ ‖w‖ → bumpWeight ρ w = 0 := bumpWeight_eq_zero hρpos
  have hbm : ∫ w, bumpWeight (n := n) ρ w = 1 := bumpWeight_integral hρpos
  rw [degree_eq_degIntegral hf hΩ hΩb hadmΩ hbc hbs hbm]
  have hUi : ∀ i, degree f (U i) y = degIntegral (fun x => f x - y) (U i) (bumpWeight ρ) :=
    fun i => degree_eq_degIntegral hf (hU i) (hΩb.subset (hUsub i)) (hadmU i) hbc hbs hbm
  simp only [hUi]
  set h : (Fin n → ℝ) → ℝ :=
    fun x => bumpWeight ρ (f x - y) * (jac (fun x => f x - y) x).det with hh
  have hzero : ∀ x ∈ K, h x = 0 := by
    intro x hx
    have hb := hρ x hx
    rw [hh]
    simp only
    rw [hbs (f x - y) (by linarith), zero_mul]
  have hind : Ω.indicator h = ∑ i, (U i).indicator h := by
    funext x
    by_cases hxU : ∃ i, x ∈ U i
    · obtain ⟨i, hi⟩ := hxU
      rw [Set.indicator_of_mem (hUsub i hi), Finset.sum_apply,
        Finset.sum_eq_single i (fun j _ hji => ?_) (fun hcon => absurd (Finset.mem_univ i) hcon),
        Set.indicator_of_mem hi]
      exact Set.indicator_of_notMem (fun hj => Set.disjoint_left.mp (hdisj j i hji) hj hi) _
    · push Not at hxU
      have hnot : x ∉ ⋃ i, U i := by
        rintro ⟨S, ⟨i, rfl⟩, hxi⟩
        exact hxU i hxi
      have hsum : (∑ i, (U i).indicator h) x = 0 := by
        rw [Finset.sum_apply]
        exact Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (hxU i) _
      rw [hsum]
      by_cases hxΩ : x ∈ Ω
      · rw [Set.indicator_of_mem hxΩ]
        exact hzero x ⟨subset_closure hxΩ, hnot⟩
      · rw [Set.indicator_of_notMem hxΩ]
  have hcont : Continuous h := by
    rw [hh]
    exact (hbc.continuous.comp (hf.continuous.sub continuous_const)).mul
      (continuous_det_jac (hf.sub contDiff_const))
  have hintU : ∀ i, Integrable ((U i).indicator h) := by
    intro i
    rw [MeasureTheory.integrable_indicator_iff (hU i).measurableSet]
    exact integrableOn_of_continuous hcont (hU i).measurableSet (hΩb.subset (hUsub i))
  calc degIntegral (fun x => f x - y) Ω (bumpWeight ρ)
      = ∫ x, Ω.indicator h x := by
        rw [degIntegral, ← MeasureTheory.integral_indicator hΩ.measurableSet]
    _ = ∫ x, (∑ i, (U i).indicator h) x := by rw [hind]
    _ = ∑ i, ∫ x, (U i).indicator h x := by
        simp only [Finset.sum_apply]
        exact MeasureTheory.integral_finsetSum _ fun i _ => hintU i
    _ = ∑ i, degIntegral (fun x => f x - y) (U i) (bumpWeight ρ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [degIntegral, ← MeasureTheory.integral_indicator (hU i).measurableSet]

end GaloisForLFunctions.HTGeometry.PoincareHopf

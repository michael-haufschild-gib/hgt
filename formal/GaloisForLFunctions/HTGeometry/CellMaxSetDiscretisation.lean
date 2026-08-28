import Mathlib
import GaloisForLFunctions.HTGeometry.CellMaxDiscretisation

/-!
# Cell-max discretisation restricted to a closed set

`exists_spaced_families_integral_le` discretises the integral of a continuous function over a *full*
interval by its values at two well-spaced families of points.  A large-values estimate, however, is
available only on the set where a Dirichlet polynomial is large, and the sample points must lie in
that set.

For a **closed** restricting set `U` the same argument works verbatim: each closed cell meets `U` in
a compact set, a continuous integrand attains its maximum there at a point *of `U`*, and the
integral over `U ∩ cell` is at most the cell length times that maximum.  Splitting the cells by
parity again produces two families spaced by the cell length.

The set of ordinates on which a Dirichlet polynomial's amplitude exceeds a threshold is closed —
it is the preimage of a closed half-line under a continuous function — so this is exactly the
discretisation Matomäki–Teräväinen's Proposition 4.2 needs to pass from a bound over finite
one-spaced frequency sets to a bound over an arbitrary amplitude level set.

* `iUnion_Ioc_cells` — the cells tile the half-open interval;
* `exists_cell_max_setIntegral_le` — the maxima, taken inside `U`;
* `exists_spaced_families_setIntegral_le` — the two spaced families, both inside `U`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

/-- The half-open cells of length `Δ` tile `Ioc a (a + mΔ)`. -/
theorem iUnion_Ioc_cells (a Δ : ℝ) (hΔ : 0 ≤ Δ) :
    ∀ m : ℕ, (⋃ k ∈ Finset.range m, Set.Ioc (a + (k : ℝ) * Δ) (a + ((k : ℝ) + 1) * Δ))
      = Set.Ioc a (a + (m : ℝ) * Δ) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep : (⋃ k ∈ Finset.range (m + 1),
            Set.Ioc (a + (k : ℝ) * Δ) (a + ((k : ℝ) + 1) * Δ))
          = (⋃ k ∈ Finset.range m, Set.Ioc (a + (k : ℝ) * Δ) (a + ((k : ℝ) + 1) * Δ))
            ∪ Set.Ioc (a + (m : ℝ) * Δ) (a + ((m : ℝ) + 1) * Δ) := by
        rw [Finset.range_add_one]
        simp [Set.union_comm]
      rw [hstep, ih]
      have h1 : a ≤ a + (m : ℝ) * Δ := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
      have h2 : a + (m : ℝ) * Δ ≤ a + ((m : ℝ) + 1) * Δ := by nlinarith
      rw [Set.Ioc_union_Ioc_eq_Ioc h1 h2]
      congr 1
      push_cast
      ring

/-- **Cell maxima inside a closed set.**  Splitting `Ioc a (a+mΔ)` into `m` cells of length `Δ`, a
continuous nonnegative integrand attains a maximum on each compact set `U ∩ cell` that is nonempty,
and the integral over `U ∩ Ioc a (a+mΔ)` is at most `Δ` times the sum of those maxima.  Every
maximiser lies in `U`. -/
theorem exists_cell_max_setIntegral_le {F : ℝ → ℝ} (hF : Continuous F) (hF0 : ∀ t, 0 ≤ F t)
    {U : Set ℝ} (hU : IsClosed U) (a Δ : ℝ) (hΔ : 0 < Δ) (m : ℕ) :
    ∃ (K : Finset ℕ) (c : ℕ → ℝ),
      (∀ k ∈ K, k < m)
      ∧ (∀ k, k < m → c k ∈ Set.Icc (a + (k : ℝ) * Δ) (a + ((k : ℝ) + 1) * Δ))
      ∧ (∀ k ∈ K, c k ∈ U)
      ∧ (∫ t in U ∩ Set.Ioc a (a + (m : ℝ) * Δ), F t) ≤ ∑ k ∈ K, Δ * F (c k) := by
  classical
  set cell : ℕ → Set ℝ := fun k => Set.Icc (a + (k : ℝ) * Δ) (a + ((k : ℝ) + 1) * Δ) with hcell
  set open_cell : ℕ → Set ℝ := fun k => Set.Ioc (a + (k : ℝ) * Δ) (a + ((k : ℝ) + 1) * Δ)
    with hopen
  -- the maximiser of each cell that meets `U`
  have hmax : ∀ k : ℕ, ∃ x : ℝ, x ∈ cell k ∧
      ((U ∩ cell k).Nonempty → x ∈ U ∧ IsMaxOn F (U ∩ cell k) x) := by
    intro k
    by_cases hne : (U ∩ cell k).Nonempty
    · have hcompact : IsCompact (U ∩ cell k) :=
        (isCompact_Icc.inter_left hU)
      obtain ⟨x, hx, hxmax⟩ := hcompact.exists_isMaxOn hne hF.continuousOn
      exact ⟨x, hx.2, fun _ => ⟨hx.1, hxmax⟩⟩
    · exact ⟨a + (k : ℝ) * Δ, Set.mem_Icc.mpr ⟨le_refl _, by nlinarith [hΔ.le]⟩,
        fun h => absurd h hne⟩
  choose c hcmem hcmax using hmax
  set K : Finset ℕ := (Finset.range m).filter (fun k => (U ∩ cell k).Nonempty) with hK
  refine ⟨K, c, ?_, fun k _ => hcmem k, ?_, ?_⟩
  · intro k hk
    exact Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  · intro k hk
    exact ((hcmax k) (Finset.mem_filter.mp hk).2).1
  -- the integral splits over the disjoint half-open cells
  · have hmeas : ∀ k ∈ Finset.range m, MeasurableSet (U ∩ open_cell k) := by
      intro k _
      exact hU.measurableSet.inter measurableSet_Ioc
    have hdisj : (Finset.range m : Set ℕ).Pairwise
        (Function.onFun Disjoint (fun k => U ∩ open_cell k)) := by
      intro k _ k' _ hne
      refine Set.disjoint_left.mpr ?_
      intro t ht ht'
      have h1 := ht.2
      have h2 := ht'.2
      simp only [hopen, Set.mem_Ioc] at h1 h2
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have : (k : ℝ) + 1 ≤ (k' : ℝ) := by exact_mod_cast hlt
        nlinarith [h1.2, h2.1, hΔ.le]
      · have : (k' : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hlt
        nlinarith [h2.2, h1.1, hΔ.le]
    have hintOn : ∀ k ∈ Finset.range m, IntegrableOn F (U ∩ open_cell k) := by
      intro k _
      refine (hF.integrableOn_Icc (a := a + (k : ℝ) * Δ)
        (b := a + ((k : ℝ) + 1) * Δ)).mono_set ?_
      intro t ht
      exact Set.Ioc_subset_Icc_self ht.2
    have hunion : (⋃ k ∈ Finset.range m, U ∩ open_cell k)
        = U ∩ Set.Ioc a (a + (m : ℝ) * Δ) := by
      rw [← Set.inter_iUnion₂]
      congr 1
      exact iUnion_Ioc_cells a Δ hΔ.le m
    have hsplit : (∫ t in U ∩ Set.Ioc a (a + (m : ℝ) * Δ), F t)
        = ∑ k ∈ Finset.range m, ∫ t in U ∩ open_cell k, F t := by
      rw [← hunion]
      exact integral_biUnion_finset (Finset.range m) hmeas hdisj hintOn
    rw [hsplit]
    -- discard the cells that miss `U`, bound the others by the cell length times the maximum
    have hzero : ∀ k ∈ Finset.range m, k ∉ K → (∫ t in U ∩ open_cell k, F t) = 0 := by
      intro k hk hkK
      have hne : ¬ (U ∩ cell k).Nonempty := fun h => hkK (Finset.mem_filter.mpr ⟨hk, h⟩)
      have hempty : U ∩ open_cell k = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro t ht
        exact hne ⟨t, ht.1, Set.Ioc_subset_Icc_self ht.2⟩
      rw [hempty]
      simp
    have hKsub : K ⊆ Finset.range m := Finset.filter_subset _ _
    have hrestrict : ∑ k ∈ K, (∫ t in U ∩ open_cell k, F t)
        = ∑ k ∈ Finset.range m, ∫ t in U ∩ open_cell k, F t :=
      Finset.sum_subset hKsub hzero
    rw [← hrestrict]
    refine Finset.sum_le_sum fun k hk => ?_
    have hkr : k ∈ Finset.range m := hKsub hk
    have hne : (U ∩ cell k).Nonempty := (Finset.mem_filter.mp hk).2
    have hsub : U ∩ open_cell k ⊆ U ∩ cell k := by
      intro t ht
      exact ⟨ht.1, Set.Ioc_subset_Icc_self ht.2⟩
    have hbound : ∀ t ∈ U ∩ open_cell k, F t ≤ F (c k) := fun t ht =>
      (hcmax k hne).2 (hsub ht)
    have hvolfin : volume (U ∩ open_cell k) < ⊤ := by
      refine lt_of_le_of_lt (measure_mono (Set.inter_subset_right)) ?_
      rw [hopen, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    have hconstint : IntegrableOn (fun _ : ℝ => F (c k)) (U ∩ open_cell k) :=
      integrableOn_const (ne_of_lt hvolfin) (by simp)
    have hmono : (∫ t in U ∩ open_cell k, F t) ≤ ∫ _t in U ∩ open_cell k, F (c k) :=
      setIntegral_mono_on (hintOn k hkr) hconstint (hmeas k hkr) hbound
    refine hmono.trans ?_
    rw [setIntegral_const, smul_eq_mul]
    have hvol : (volume (U ∩ open_cell k)).toReal ≤ Δ := by
      have hle : volume (U ∩ open_cell k) ≤ volume (open_cell k) :=
        measure_mono Set.inter_subset_right
      have hval : volume (open_cell k) = ENNReal.ofReal Δ := by
        rw [hopen, Real.volume_Ioc]
        congr 1
        ring
      rw [hval] at hle
      calc (volume (U ∩ open_cell k)).toReal ≤ (ENNReal.ofReal Δ).toReal :=
            ENNReal.toReal_mono (by simp) hle
        _ = Δ := ENNReal.toReal_ofReal hΔ.le
    exact mul_le_mul_of_nonneg_right hvol (hF0 (c k))

/-- **Two spaced families inside a closed set.**  Discretising by cell maxima taken inside `U` and
splitting the cells by parity, the integral of a continuous nonnegative function over
`U ∩ Ioc a (a+mΔ)` is at most the cell length times the sum of its values over two `Δ`-spaced finite
sets of points, **both contained in `U`**.  This is the form a large-values bound valid only on an
amplitude level set consumes. -/
theorem exists_spaced_families_setIntegral_le {F : ℝ → ℝ} (hF : Continuous F)
    (hF0 : ∀ t, 0 ≤ F t) {U : Set ℝ} (hU : IsClosed U) (a Δ : ℝ) (hΔ : 0 < Δ) (m : ℕ) :
    ∃ S₁ S₂ : Finset ℝ,
      (↑S₁ ⊆ U ∩ Set.Icc a (a + (m : ℝ) * Δ))
      ∧ (↑S₂ ⊆ U ∩ Set.Icc a (a + (m : ℝ) * Δ))
      ∧ (∀ t ∈ S₁, ∀ u ∈ S₁, t ≠ u → Δ ≤ |t - u|)
      ∧ (∀ t ∈ S₂, ∀ u ∈ S₂, t ≠ u → Δ ≤ |t - u|)
      ∧ (∫ t in U ∩ Set.Ioc a (a + (m : ℝ) * Δ), F t)
          ≤ Δ * ((∑ t ∈ S₁, F t) + ∑ t ∈ S₂, F t) := by
  classical
  obtain ⟨K, c, hKm, hc, hcU, hint⟩ := exists_cell_max_setIntegral_le hF hF0 hU a Δ hΔ m
  set E : Finset ℕ := K.filter (fun k => k % 2 = 0) with hE
  set O : Finset ℕ := K.filter (fun k => ¬(k % 2 = 0)) with hO
  have hEm : ∀ k ∈ E, k < m := fun k hk => hKm k (Finset.mem_filter.mp hk).1
  have hOm : ∀ k ∈ O, k < m := fun k hk => hKm k (Finset.mem_filter.mp hk).1
  have hEU : ∀ k ∈ E, c k ∈ U := fun k hk => hcU k (Finset.mem_filter.mp hk).1
  have hOU : ∀ k ∈ O, c k ∈ U := fun k hk => hcU k (Finset.mem_filter.mp hk).1
  have hcIcc : ∀ k, k < m → c k ∈ Set.Icc a (a + (m : ℝ) * Δ) := by
    intro k hk
    have h := hc k hk
    rw [Set.mem_Icc] at h ⊢
    have hk' : ((k : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hk
    constructor
    · nlinarith [Nat.cast_nonneg (α := ℝ) k, hΔ.le, h.1]
    · nlinarith [hΔ.le, h.2]
  have hEpar : ∀ k ∈ E, ∀ k' ∈ E, k % 2 = k' % 2 := by
    intro k hk k' hk'
    rw [hE, Finset.mem_filter] at hk hk'
    rw [hk.2, hk'.2]
  have hOpar : ∀ k ∈ O, ∀ k' ∈ O, k % 2 = k' % 2 := by
    intro k hk k' hk'
    rw [hO, Finset.mem_filter] at hk hk'
    omega
  have hinj : ∀ (P : Finset ℕ), (∀ k ∈ P, k < m) →
      (∀ k ∈ P, ∀ k' ∈ P, k % 2 = k' % 2) → Set.InjOn c P := by
    intro P hPm hPpar k hk k' hk' hval
    by_contra hne
    have hsp := cell_points_spaced hΔ.le (fun j hj => hc j hj) (hPm k hk) (hPm k' hk')
      (hPpar k hk k' hk') hne
    rw [hval] at hsp
    simp at hsp
    linarith [hsp]
  refine ⟨E.image c, O.image c, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [Finset.coe_image, Set.mem_image] at ht
    obtain ⟨k, hk, rfl⟩ := ht
    exact ⟨hEU k hk, hcIcc k (hEm k hk)⟩
  · intro t ht
    rw [Finset.coe_image, Set.mem_image] at ht
    obtain ⟨k, hk, rfl⟩ := ht
    exact ⟨hOU k hk, hcIcc k (hOm k hk)⟩
  · intro t ht u hu hne
    rw [Finset.mem_image] at ht hu
    obtain ⟨k, hk, hkt⟩ := ht
    obtain ⟨k', hk', hku⟩ := hu
    have hkk' : k ≠ k' := by
      intro h
      rw [h, hku] at hkt
      exact hne hkt.symm
    rw [← hkt, ← hku]
    exact cell_points_spaced hΔ.le (fun j hj => hc j hj) (hEm k hk) (hEm k' hk')
      (hEpar k hk k' hk') hkk'
  · intro t ht u hu hne
    rw [Finset.mem_image] at ht hu
    obtain ⟨k, hk, hkt⟩ := ht
    obtain ⟨k', hk', hku⟩ := hu
    have hkk' : k ≠ k' := by
      intro h
      rw [h, hku] at hkt
      exact hne hkt.symm
    rw [← hkt, ← hku]
    exact cell_points_spaced hΔ.le (fun j hj => hc j hj) (hOm k hk) (hOm k' hk')
      (hOpar k hk k' hk') hkk'
  · refine hint.trans (le_of_eq ?_)
    rw [Finset.sum_image (fun k hk k' hk' h => hinj E hEm hEpar hk hk' h),
      Finset.sum_image (fun k hk k' hk' h => hinj O hOm hOpar hk hk' h)]
    rw [hE, hO, ← Finset.mul_sum]
    congr 1
    exact (Finset.sum_filter_add_sum_filter_not K (fun k => k % 2 = 0) (fun k => F (c k))).symm

end GaloisForLFunctions.HTGeometry

end

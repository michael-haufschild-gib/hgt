import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateReturnSpacing

/-!
# Gap statistics of finely resolved zero-gate returns

A gap longer than the minimum resolution signals a threshold exit. The
disjoint cells of such exits lie in a thin band around the return threshold.
This controls their count, while the mean-spacing law controls their total duration.
-/

open Filter Finset MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- The recorded gaps strictly longer than the required separation. -/
def resolvedLongGapIndices (t : ℕ → ℝ) (h : ℝ) (j : ℕ) : Finset (Fin j) :=
  Finset.univ.filter fun i => t i.val + h < t (i.val + 1)

/-- Total elapsed time in the gaps strictly longer than the required separation. -/
def resolvedLongGapTime (t : ℕ → ℝ) (h : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ resolvedLongGapIndices t h j, (t (i.val + 1) - t i.val)

/-- The proportion of recorded gaps that strictly exceed the separation. -/
def resolvedLongGapFraction (t : ℕ → ℝ) (h : ℝ) (j : ℕ) : ℝ :=
  ((resolvedLongGapIndices t h j).card : ℝ) / (j : ℝ)

private theorem resolvedElapsed_lower (t : ℕ → ℝ) (a h : ℝ) (hzero : t 0 = a)
    (hstep : ∀ i, t i + h ≤ t (i + 1)) (j : ℕ) : a + (j : ℝ) * h ≤ t j := by
  induction j with
  | zero => simpa only [Nat.cast_zero, zero_mul, add_zero] using hzero.ge
  | succ j ih =>
      have hs := hstep j
      rw [Nat.cast_succ, add_mul, one_mul]
      linarith only [ih, hs]

/-- Each long gap charges a disjoint resolution cell to an exit layer.
The initial cell may start outside the return set. -/
theorem resolvedLongGapIndices_card_mul_le (A B : Set ℝ) (t : ℕ → ℝ) (a h : ℝ)
    (hh : 0 < h) (hzero : t 0 = a)
    (hfirst : ∀ i, IsLeast {v | t i + h ≤ v ∧ v ∈ A} (t (i + 1)))
    (hlayer : ∀ u ∈ A, u + h ∉ A → Ioc u (u + h) ⊆ B) (j : ℕ) :
    ((resolvedLongGapIndices t h j).card : ℝ) * h ≤ h + volume.real (B ∩ Icc a (t j)) := by
  classical
  let s := resolvedLongGapIndices t h j
  let W (i : Fin j) := Ioc (t i.val) (t i.val + h)
  have hstep (i : ℕ) := (hfirst i).1.1
  have hmono : Monotone t := monotone_nat_of_le_succ fun i =>
    (le_add_of_nonneg_right hh.le).trans (hstep i)
  have disj (i k : Fin j) (hik : i < k) : Disjoint (W i) (W k) := by
    refine Set.disjoint_left.mpr fun u hu hv => ?_
    have he := (hstep i.val).trans (hmono (show i.val + 1 ≤ k.val from hik))
    exact (not_lt_of_ge (hu.2.trans he)) hv.1
  have hdisj : (↑s : Set (Fin j)).PairwiseDisjoint W := by
    intro i _ k _ hik
    exact (lt_or_gt_of_ne hik).elim (disj i k) (fun hk => (disj k i hk).symm)
  have hsub : (⋃ i ∈ s, W i) ⊆ Ioc a (a + h) ∪ (B ∩ Icc a (t j)) := by
    intro u hu
    obtain ⟨i, hi'⟩ := mem_iUnion.mp hu
    obtain ⟨hi, hu⟩ := mem_iUnion.mp hi'
    have hlong : t i.val + h < t (i.val + 1) := (mem_filter.mp hi).2
    have hu' : t i.val < u ∧ u ≤ t i.val + h := hu
    have hfail : t i.val + h ∉ A := fun h =>
      (not_le_of_gt hlong) ((hfirst i.val).2 ⟨le_rfl, h⟩)
    by_cases hi0 : i.val = 0
    · exact Or.inl (by simpa only [W, hi0, hzero] using hu)
    · have hit : t i.val ∈ A := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        simpa only [hk] using (hfirst k).1.2
      have hleft : a ≤ t i.val := hzero ▸ hmono (Nat.zero_le i.val)
      exact Or.inr ⟨hlayer _ hit hfail hu,
        hleft.trans hu'.1.le, (hu'.2.trans (hstep i.val)).trans (hmono i.isLt)⟩
  have hfinite : volume (Ioc a (a + h) ∪ (B ∩ Icc a (t j))) ≠ ⊤ :=
    (measure_union_lt_top measure_Ioc_lt_top (lt_top_iff_ne_top.mpr
      (measure_ne_top_of_subset Set.inter_subset_right measure_Icc_lt_top.ne))).ne
  calc
    ((resolvedLongGapIndices t h j).card : ℝ) * h = ∑ i ∈ s, volume.real (W i) := by
      have hm (i : Fin j) : volume.real (W i) = h := by
        change volume.real (Ioc (t i.val) (t i.val + h)) = h
        rw [Real.volume_real_Ioc_of_le (le_add_of_nonneg_right hh.le), add_sub_cancel_left]
      simp only [hm, sum_const, nsmul_eq_mul, s]
    _ = volume.real (⋃ i ∈ s, W i) :=
      (measureReal_biUnion_finset hdisj (fun _ _ => measurableSet_Ioc)
        (fun _ _ => measure_Ioc_lt_top.ne)).symm
    _ ≤ volume.real (Ioc a (a + h) ∪ (B ∩ Icc a (t j))) := measureReal_mono hsub hfinite
    _ ≤ h + volume.real (B ∩ Icc a (t j)) := by
      have he := measureReal_union_le (μ := volume) (Ioc a (a + h)) (B ∩ Icc a (t j))
      rwa [Real.volume_real_Ioc_of_le (le_add_of_nonneg_right hh.le), add_sub_cancel_left] at he

/-- A Lipschitz trajectory that leaves a return threshold by the next
resolution point stays in the corresponding tolerance band on its exit cell. -/
theorem zeroGateExitCell_subset_band {n : ℕ} (H : selfAdjoint (Reg n)) (l r s h u : ℝ)
    (hl : zeroGateArcTolerance l + circuitHamiltonianSpectralWidth H / 2 * h ≤ zeroGateArcTolerance r)
    (hs : zeroGateArcTolerance r + circuitHamiltonianSpectralWidth H / 2 * h ≤ zeroGateArcTolerance s)
    (hu : u ∈ zeroGateReturnSet H r) (hexit : u + h ∉ zeroGateReturnSet H r) :
    Ioc u (u + h) ⊆ zeroGateReturnSet H s \ zeroGateReturnSet H l := by
  obtain ⟨L, hL, hLip⟩ := orbitCircuitDistance_lipschitz_spectralWidth H 0
  have hw : 0 ≤ circuitHamiltonianSpectralWidth H / 2 :=
    div_nonneg (circuitHamiltonianSpectralWidth_nonneg H) zero_le_two
  intro x hx
  have dxu := hLip.dist_le_mul x u
  have dxx := hLip.dist_le_mul (u + h) x
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1.le), hL] at dxu
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.2), hL] at dxx
  have hxu : x - u ≤ h := by linarith only [hx.2]
  have hxx : u + h - x ≤ h := by linarith only [hx.1]
  have hxu' := mul_le_mul_of_nonneg_left hxu hw
  have hxx' := mul_le_mul_of_nonneg_left hxx hw
  change orbitCircuitDistance H 0 u ≤ zeroGateArcTolerance r at hu
  change ¬ orbitCircuitDistance H 0 (u + h) ≤ zeroGateArcTolerance r at hexit
  constructor
  · change orbitCircuitDistance H 0 x ≤ zeroGateArcTolerance s
    linarith only [(abs_le.mp dxu).2, hu, hxu', hs]
  · intro hx'
    change orbitCircuitDistance H 0 x ≤ zeroGateArcTolerance l at hx'
    apply hexit
    linarith only [(abs_le.mp dxx).2, hx', hxx', hl]

private theorem zeroGateBand_occupation {n : ℕ} (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (l s : Icc (0 : ℝ) (1 / 2)) (hls : (l : ℝ) < s) (a : ℝ) :
    Tendsto (fun T => volume.real ((zeroGateReturnSet H s \ zeroGateReturnSet H l) ∩ Icc a T) /
      (T - a)) atTop (𝓝 (zeroGateArcDensity (2 ^ n) s - zeroGateArcDensity (2 ^ n) l)) := by
  have hl : MeasurableSet (zeroGateReturnSet H l) :=
    (isClosed_le (orbitCircuitDistance_lipschitz H 0).continuous continuous_const).measurableSet
  have hsub : zeroGateReturnSet H l ⊆ zeroGateReturnSet H s := fun _ hx =>
    hx.trans (strictMonoOn_zeroGateArcTolerance l.2 s.2 hls).le
  have hlim := (maximallyProjective_zeroGateOccupation_from_start H hmax s a).sub
    (maximallyProjective_zeroGateOccupation_from_start H hmax l a)
  refine hlim.congr fun T => ?_
  have he : (zeroGateReturnSet H s \ zeroGateReturnSet H l) ∩ Icc a T =
      (zeroGateReturnSet H s ∩ Icc a T) \ (zeroGateReturnSet H l ∩ Icc a T) := by
    ext x
    simp only [mem_inter_iff, Set.mem_sdiff]
    tauto
  rw [he, measureReal_sdiff (inter_subset_inter_left _ hsub) (hl.inter measurableSet_Icc)
    (measure_ne_top_of_subset Set.inter_subset_right measure_Icc_lt_top.ne), sub_div]

private theorem exists_zeroGateBand_small (n : ℕ) (r : Ioo (0 : ℝ) (1 / 2)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ l s : Icc (0 : ℝ) (1 / 2), (l : ℝ) < r ∧ (r : ℝ) < s ∧
      zeroGateArcDensity (2 ^ n) s - zeroGateArcDensity (2 ^ n) l < δ := by
  let p := zeroGateArcDensity (2 ^ n)
  have hc : ContinuousAt p (r : ℝ) :=
    (continuous_const.mul (continuous_id.pow (2 ^ n - 1))).continuousAt
  have hlr : ∀ᶠ l in 𝓝[<] (r : ℝ), l < (r : ℝ) := self_mem_nhdsWithin
  have hrs : ∀ᶠ s in 𝓝[>] (r : ℝ), (r : ℝ) < s := self_mem_nhdsWithin
  have hleft : ∀ᶠ l in 𝓝[<] (r : ℝ), 0 < l ∧ l < (r : ℝ) ∧ p r - δ / 2 < p l :=
    ((eventually_gt_nhds r.2.1).filter_mono nhdsWithin_le_nhds).and
      (hlr.and ((hc.tendsto.eventually (eventually_gt_nhds (sub_lt_self _ (half_pos hδ)))).filter_mono
        nhdsWithin_le_nhds))
  have hright : ∀ᶠ s in 𝓝[>] (r : ℝ), (r : ℝ) < s ∧ s < 1 / 2 ∧ p s < p r + δ / 2 :=
    hrs.and (((eventually_lt_nhds r.2.2).filter_mono nhdsWithin_le_nhds).and
      ((hc.tendsto.eventually (eventually_lt_nhds (lt_add_of_pos_right _ (half_pos hδ)))).filter_mono
        nhdsWithin_le_nhds))
  obtain ⟨l, hl0, hlr, hl⟩ := hleft.exists
  obtain ⟨s, hrs, hsHalf, hs⟩ := hright.exists
  refine ⟨⟨l, hl0.le, (hlr.trans r.2.2).le⟩, ⟨s, (r.2.1.trans hrs).le, hsHalf.le⟩, hlr, hrs, ?_⟩
  change p s - p l < δ
  linarith only [hl, hs]

/-- In the joint fine-resolution and long-observation limit, the fraction
of recorded gaps exceeding the minimum separation tends to zero. -/
theorem maximallyProjective_zeroGateLongGapFraction_joint {n : ℕ} (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (r : Ioo (0 : ℝ) (1 / 2)) (a η : ℝ) (hη : 0 < η) :
    ∃ h₀ > 0, ∃ R > 0, ∀ h > 0, h ≤ h₀ →
      ∀ t, IsZeroGateReturnSequence H r a h t → ∀ j : ℕ, R ≤ (j : ℝ) * h →
        resolvedLongGapFraction t h j < η := by
  let p := zeroGateArcDensity (2 ^ n) r
  have hp : 0 < p := by
    change 0 < (↑(2 ^ n : ℕ) : ℝ) * (r : ℝ) ^ (2 ^ n - 1)
    exact mul_pos (by positivity) (pow_pos r.2.1 _)
  let C := p⁻¹ + 1
  have hC : 0 < C := add_pos (inv_pos.mpr hp) zero_lt_one
  let δ := η / (2 * C)
  have hδ : 0 < δ := div_pos hη (mul_pos zero_lt_two hC)
  obtain ⟨l, s, hlr, hrs, hband⟩ := exists_zeroGateBand_small n r hδ
  let B := zeroGateReturnSet H s \ zeroGateReturnSet H l
  have hlm := zeroGateBand_occupation H hmax l s (hlr.trans hrs) a
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlm.eventually (eventually_lt_nhds hband))
  obtain ⟨hmean, hmpos, Rmean, _, hmeanBound⟩ :=
    maximallyProjective_zeroGateSpacing_joint H hmax r a 1 zero_lt_one
  let w := circuitHamiltonianSpectralWidth H / 2
  have hw : 0 ≤ w := div_nonneg (circuitHamiltonianSpectralWidth_nonneg H) zero_le_two
  have hw1 : 0 < 1 + w := add_pos_of_pos_of_nonneg zero_lt_one hw
  have hrI : (r : ℝ) ∈ Icc (0 : ℝ) (1 / 2) := Ioo_subset_Icc_self r.2
  have hlo := strictMonoOn_zeroGateArcTolerance l.2 hrI hlr
  have hhi := strictMonoOn_zeroGateArcTolerance hrI s.2 hrs
  let Δ := min (zeroGateArcTolerance r - zeroGateArcTolerance l)
    (zeroGateArcTolerance s - zeroGateArcTolerance r)
  have hΔ : 0 < Δ := lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi)
  let h₀ := min hmean (min (η / 4) (Δ / (1 + w)))
  let R := max Rmean (max 1 (T - a))
  have hR1 : 1 ≤ R := (le_max_left 1 (T - a)).trans (le_max_right Rmean _)
  refine ⟨h₀, lt_min hmpos (lt_min (div_pos hη (by positivity)) (div_pos hΔ hw1)),
    R, zero_lt_one.trans_le hR1, ?_⟩
  intro h hh hsmall t ht j hj
  let J := (j : ℝ) * h
  have hJ1 : 1 ≤ J := hR1.trans hj
  have hJ : 0 < J := zero_lt_one.trans_le hJ1
  have hjpos : 0 < (j : ℝ) := pos_of_mul_pos_left hJ hh.le
  have hTj : T ≤ t j := by
    have h₁ : T - a ≤ J := (le_max_right 1 (T - a)).trans ((le_max_right Rmean _).trans hj)
    have h₂ := resolvedElapsed_lower t a h ht.1 (fun i => (ht.2 i).1.1) j
    change a + J ≤ t j at h₂
    linarith only [h₁, h₂]
  have htpos : 0 < t j - a := by
    have he := resolvedElapsed_lower t a h ht.1 (fun i => (ht.2 i).1.1) j
    change a + J ≤ t j at he
    linarith only [he, hJ]
  have hsmallMean : h ≤ hmean := hsmall.trans (min_le_left _ _)
  have hsmallAux : h ≤ min (η / 4) (Δ / (1 + w)) := hsmall.trans (min_le_right _ _)
  have hwall : w * h ≤ Δ := by
    calc
      w * h ≤ (1 + w) * h := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hh.le
      _ ≤ Δ := by rw [mul_comm]; exact (le_div_iff₀ hw1).mp (hsmallAux.trans (min_le_right _ _))
  have hlbudget : zeroGateArcTolerance l + w * h ≤ zeroGateArcTolerance r := by
    have he := hwall.trans (min_le_left (zeroGateArcTolerance r - zeroGateArcTolerance l)
      (zeroGateArcTolerance s - zeroGateArcTolerance r))
    linarith only [he]
  have hsbudget : zeroGateArcTolerance r + w * h ≤ zeroGateArcTolerance s := by
    have he := hwall.trans (min_le_right (zeroGateArcTolerance r - zeroGateArcTolerance l)
      (zeroGateArcTolerance s - zeroGateArcTolerance r))
    linarith only [he]
  have hcount := resolvedLongGapIndices_card_mul_le (zeroGateReturnSet H r) B t a h hh ht.1 ht.2
    (fun u hu hv => zeroGateExitCell_subset_band H l r s h u hlbudget hsbudget hu hv) j
  have hm := (abs_lt.mp (hmeanBound h hh hsmallMean t ht j ((le_max_left _ _).trans hj))).2
  have hmean' : t j - a < C * J := by
    apply (div_lt_iff₀ hJ).mp
    change (t j - a) / J - p⁻¹ < 1 at hm
    change (t j - a) / J < p⁻¹ + 1
    linarith only [hm]
  have hvol : volume.real (B ∩ Icc a (t j)) < η / 2 * J := by
    have h1 : volume.real (B ∩ Icc a (t j)) < δ * (t j - a) :=
      (div_lt_iff₀ htpos).mp (hT _ hTj)
    have h2 := mul_lt_mul_of_pos_left hmean' hδ
    have hδC : δ * C = η / 2 := by
      dsimp only [δ]
      field_simp [hC.ne']
    rw [← mul_assoc, hδC] at h2
    exact h1.trans h2
  have hs' : h ≤ η / 4 * J := (hsmallAux.trans (min_le_left _ _)).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hJ1 (div_nonneg hη.le (by positivity)))
  have hlt : ((resolvedLongGapIndices t h j).card : ℝ) * h < η * J := by
    linarith only [hcount, hvol, hs', mul_pos hη hJ]
  apply (div_lt_iff₀ hjpos).mpr
  apply (mul_lt_mul_iff_of_pos_right hh).mp
  rw [mul_assoc η (j : ℝ) h]
  exact hlt

private theorem sum_resolved_gaps (t : ℕ → ℝ) (j : ℕ) :
    (∑ i : Fin j, (t (i.val + 1) - t i.val)) = t j - t 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih]
      ring

/-- The minimum-size gaps have total time equal to their count times `h`. -/
theorem resolvedLongGapTime_balance (t : ℕ → ℝ) (h : ℝ) (j : ℕ)
    (hstep : ∀ i, t i + h ≤ t (i + 1)) :
    resolvedLongGapTime t h j + ((j : ℝ) - (resolvedLongGapIndices t h j).card) * h = t j - t 0 := by
  classical
  let S := resolvedLongGapIndices t h j
  let U : Finset (Fin j) := univ
  let g (i : Fin j) := t (i.val + 1) - t i.val
  have hSU : S ⊆ U := subset_univ _
  have hshort (i : Fin j) (hi : i ∈ U \ S) : g i = h := by
    have hn : ¬ t i.val + h < t (i.val + 1) := fun hlt =>
      (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ i, hlt⟩)
    change t (i.val + 1) - t i.val = h
    linarith only [not_lt.mp hn, hstep i.val]
  have hg : ∑ i ∈ U \ S, g i = (↑(U \ S).card : ℝ) * h := by
    rw [sum_congr rfl hshort, sum_const, nsmul_eq_mul]
  have hsum := sum_sdiff (f := g) hSU
  rw [hg] at hsum
  have hcard : (↑(U \ S).card : ℝ) = (j : ℝ) - S.card := by
    rw [card_sdiff, Finset.inter_eq_left.mpr hSU, Nat.cast_sub (Finset.card_le_card hSU)]
    simp only [U, card_univ, Fintype.card_fin]
  rw [hcard] at hsum
  change (resolvedLongGapTime t h j : ℝ) + ((j : ℝ) - S.card) * h = _
  rw [add_comm]
  exact hsum.trans (sum_resolved_gaps t j)

/-- Time spent in gaps exceeding `M` resolution units. -/
def resolvedGapTailTime (t : ℕ → ℝ) (h : ℝ) (j : ℕ) (M : ℝ) : ℝ :=
  ∑ i ∈ (univ : Finset (Fin j)).filter (fun i => M * h < t (i.val + 1) - t i.val),
    (t (i.val + 1) - t i.val)

/-- Raising the gap threshold from one to `M` removes at most `M*h` time
per long gap. -/
theorem resolvedLongGapTime_sub_tail_bounds (t : ℕ → ℝ) {h M : ℝ} (hh : 0 < h) (hM : 1 ≤ M)
    (j : ℕ) :
    0 ≤ resolvedLongGapTime t h j - resolvedGapTailTime t h j M ∧
    resolvedLongGapTime t h j - resolvedGapTailTime t h j M ≤
      M * h * (resolvedLongGapIndices t h j).card := by
  classical
  let S := resolvedLongGapIndices t h j
  let g (i : Fin j) := t (i.val + 1) - t i.val
  let T := univ.filter (fun i => M * h < g i)
  have h' : h ≤ M * h := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hM hh.le
  have hTS : T ⊆ S := by
    intro i hi
    have hgap : h < g i := h'.trans_lt (mem_filter.mp hi).2
    exact mem_filter.mpr ⟨mem_univ i, by dsimp only [g] at hgap; linarith only [hgap]⟩
  have hsum := sum_sdiff (f := g) hTS
  change (∑ i ∈ S \ T, g i) + resolvedGapTailTime t h j M = resolvedLongGapTime t h j at hsum
  have he : resolvedLongGapTime t h j - resolvedGapTailTime t h j M = ∑ i ∈ S \ T, g i := by
    linarith only [hsum]
  rw [he]
  refine ⟨sum_nonneg (fun i hi => ?_), ?_⟩
  · have hmem : i ∈ resolvedLongGapIndices t h j := (Finset.mem_sdiff.mp hi).1
    rw [resolvedLongGapIndices, Finset.mem_filter] at hmem
    have hgap := hmem.2
    dsimp only [g]
    linarith only [hgap, hh]
  · calc
      _ ≤ ∑ _ ∈ S \ T, M * h := by
        apply sum_le_sum
        intro i hi
        exact not_lt.mp (fun hi' => (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ i, hi'⟩))
      _ ≤ ∑ _ ∈ S, M * h := sum_le_sum_of_subset_of_nonneg sdiff_subset
        (fun _ _ _ => mul_nonneg (zero_le_one.trans hM) hh.le)
      _ = _ := by simp only [sum_const, nsmul_eq_mul, S, mul_comm]

/-- The elapsed-time share of large gaps differs from `1-p` by at most the
error in the occupied share plus the count of exceptional gaps weighted by `M+1`. -/
theorem abs_resolvedGapTailShare_sub_le (t : ℕ → ℝ) (a h M p : ℝ) (j : ℕ)
    (hzero : t 0 = a) (hstep : ∀ i, t i + h ≤ t (i + 1))
    (hh : 0 < h) (hM : 1 ≤ M) (hj : 0 < (j : ℝ)) :
    |resolvedGapTailTime t h j M / (t j - a) - (1 - p)| ≤
      |((j : ℝ) * h) / (t j - a) - p| + (M + 1) * resolvedLongGapFraction t h j := by
  let X := (j : ℝ) * h
  let D := t j - a
  let F := resolvedLongGapFraction t h j
  let q := X / D
  let E := resolvedLongGapTime t h j - resolvedGapTailTime t h j M
  have hX : 0 < X := mul_pos hj hh
  have hXD : X ≤ D := by
    have h := resolvedElapsed_lower t a h hzero hstep j
    change a + X ≤ t j at h
    linarith only [h]
  have hD : 0 < D := hX.trans_le hXD
  have hq0 : 0 ≤ q := div_nonneg hX.le hD.le
  have hq1 : q ≤ 1 := (div_le_iff₀ hD).mpr (by simpa only [one_mul] using hXD)
  have hF : 0 ≤ F := div_nonneg (Nat.cast_nonneg _) hj.le
  obtain ⟨hE0, hE⟩ := resolvedLongGapTime_sub_tail_bounds t hh hM j
  have hmF : 0 ≤ M * F := mul_nonneg (zero_le_one.trans hM) hF
  have hEd : E / D ≤ M * F := by
    apply (div_le_iff₀ hD).mpr
    change E ≤ M * F * D
    calc
      E ≤ M * h * (resolvedLongGapIndices t h j).card := hE
      _ = M * F * X := by
        dsimp only [F, X, resolvedLongGapFraction]
        field_simp [hj.ne']
      _ ≤ M * F * D := mul_le_mul_of_nonneg_left hXD hmF
  have hFq : |F * q| ≤ F := by
    rw [abs_of_nonneg (mul_nonneg hF hq0)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hq1 hF
  have hbalance := resolvedLongGapTime_balance t h j hstep
  rw [hzero] at hbalance
  change resolvedLongGapTime t h j + ((j : ℝ) - (resolvedLongGapIndices t h j).card) * h = D at hbalance
  have htail : resolvedGapTailTime t h j M = D - ((j : ℝ) - (resolvedLongGapIndices t h j).card) * h - E := by
    dsimp only [E]
    linarith only [hbalance]
  have he : resolvedGapTailTime t h j M / D - (1 - p) = (p - q) + (F * q - E / D) := by
    rw [htail]
    dsimp only [q, X, F, resolvedLongGapFraction]
    field_simp [hD.ne', hj.ne']
    ring
  change |resolvedGapTailTime t h j M / D - (1 - p)| ≤ |q - p| + (M + 1) * F
  rw [he]
  have habs : |F * q - E / D| ≤ |F * q| + |E / D| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (F * q) (-(E / D))
  calc
    _ ≤ |p - q| + (|F * q| + |E / D|) := (abs_add_le _ _).trans
      (add_le_add le_rfl habs)
    _ ≤ |q - p| + (F + M * F) := by
      rw [abs_sub_comm p q, abs_of_nonneg (div_nonneg hE0 hD.le)]
      exact add_le_add le_rfl (add_le_add hFq hEd)
    _ = _ := by ring

/-- For any fixed multiple of the resolution, the gaps beyond that multiple
carry limiting time share `1-p`, where `p` is the zero-gate occupation. -/
theorem maximallyProjective_zeroGateGapTail_joint {n : ℕ} (H : selfAdjoint (Reg n))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (r : Ioo (0 : ℝ) (1 / 2)) (a M η : ℝ) (hM : 1 ≤ M) (hη : 0 < η) :
    ∃ h₀ > 0, ∃ R > 0, ∀ h > 0, h ≤ h₀ →
      ∀ t, IsZeroGateReturnSequence H r a h t → ∀ j : ℕ, R ≤ (j : ℝ) * h →
        resolvedLongGapFraction t h j < η ∧
        |resolvedGapTailTime t h j M / (t j - a) - (1 - zeroGateArcDensity (2 ^ n) r)| < η := by
  let p := zeroGateArcDensity (2 ^ n) r
  have hp : 0 < p := by
    change 0 < (↑(2 ^ n : ℕ) : ℝ) * (r : ℝ) ^ (2 ^ n - 1)
    exact mul_pos (by positivity) (pow_pos r.2.1 _)
  have hM' : 0 < M + 1 := by linarith only [hM]
  let ε := (η / 2) / (M + 1)
  have hε : 0 < ε := div_pos (half_pos hη) hM'
  have hεM : (M + 1) * ε = η / 2 := by
    dsimp only [ε]
    rw [mul_comm, div_mul_cancel₀ _ hM'.ne']
  have hεη : ε < η := by
    apply (div_lt_iff₀ hM').mpr
    have hm := mul_le_mul_of_nonneg_left hM hη.le
    rw [mul_add, mul_one]
    linarith only [hm, hη]
  have hc : ContinuousAt (fun x : ℝ => x⁻¹) p⁻¹ := continuousAt_inv₀ (inv_ne_zero hp.ne')
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hc (η / 2) (half_pos hη)
  obtain ⟨hc₀, hcpos, Rc, hRc, hcount⟩ := maximallyProjective_zeroGateLongGapFraction_joint H hmax r a ε hε
  obtain ⟨hm₀, hmpos, Rm, hRm, hmean⟩ := maximallyProjective_zeroGateSpacing_joint H hmax r a δ hδ
  refine ⟨min hc₀ hm₀, lt_min hcpos hmpos, max Rc Rm, hRc.trans_le (le_max_left _ _), ?_⟩
  intro h hh hsmall t ht j hj
  have hf := hcount h hh (hsmall.trans (min_le_left _ _)) t ht j ((le_max_left _ _).trans hj)
  have hm := hmean h hh (hsmall.trans (min_le_right _ _)) t ht j ((le_max_right _ _).trans hj)
  have hjpos : 0 < (j : ℝ) := pos_of_mul_pos_left (hRc.trans_le ((le_max_left _ _).trans hj)) hh.le
  have hshare : |((j : ℝ) * h) / (t j - a) - p| < η / 2 := by
    have he := hnear (x := (t j - a) / ((j : ℝ) * h)) (by rwa [Real.dist_eq])
    simpa only [Real.dist_eq, inv_div, inv_inv] using he
  have htail := abs_resolvedGapTailShare_sub_le t a h M p j ht.1 (fun i => (ht.2 i).1.1) hh hM hjpos
  refine ⟨hf.trans hεη, htail.trans_lt ?_⟩
  have hh' := mul_lt_mul_of_pos_left hf hM'
  rw [hεM] at hh'
  linarith only [hshare, hh']

/-- On one typical Gaussian path, the separation-sized gaps dominate the
count while larger gaps retain the complementary elapsed-time share. -/
theorem gaussian_path_zeroGateGapTail_joint :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ r : Ioo (0 : ℝ) (1 / 2), ∀ a M η : ℝ,
      1 ≤ M → 0 < η →
      let u := pathPauliDisorderShell ω (k + 1)
      let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
      ∃ h₀ > 0, ∃ R > 0, ∀ h > 0, h ≤ h₀ →
        ∃! t, IsZeroGateReturnSequence H r a h t ∧ ∀ j : ℕ, R ≤ (j : ℝ) * h →
          resolvedLongGapFraction t h j < η ∧
          |resolvedGapTailTime t h j M / (t j - a) - (1 - zeroGateArcDensity (2 ^ (k + 3)) r)| < η := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro k r a M η hM hη
  let u := pathPauliDisorderShell ω (k + 1)
  let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
  obtain ⟨h₀, h₀pos, R, hR, htail⟩ := maximallyProjective_zeroGateGapTail_joint H (hω k) r a M η hM hη
  refine ⟨h₀, h₀pos, R, hR, fun h hh hs => ?_⟩
  obtain ⟨t, ht⟩ := exists_zeroGateReturnSequence H ⟨r, r.2.1, r.2.2.le⟩ a h
  exact ⟨t, ⟨ht, htail h hh hs t ht⟩, fun v hv => zeroGateReturnSequence_unique hv.1 ht⟩

#print axioms resolvedLongGapIndices_card_mul_le
#print axioms zeroGateExitCell_subset_band
#print axioms maximallyProjective_zeroGateLongGapFraction_joint
#print axioms resolvedLongGapTime_balance
#print axioms resolvedLongGapTime_sub_tail_bounds
#print axioms abs_resolvedGapTailShare_sub_le
#print axioms maximallyProjective_zeroGateGapTail_joint
#print axioms gaussian_path_zeroGateGapTail_joint

end

end GaloisForLFunctions.HTGeometry

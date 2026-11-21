import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualTube

/-!
# Euclidean distance from noncontextual onsite support

The optimal onsite projection retains the largest axis at each regular
site and all axes at one exceptional site. The exceptional site is one
whose two discarded axes carry the largest squared mass.
-/

open Matrix Filter Set MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private def axisPeak (x : Fin 3 → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun a => x a ^ 2

/-- Squared onsite mass discarded by keeping the axis of largest absolute value. -/
def onsiteDiscardEnergy (x : Fin 3 → ℝ) : ℝ := (∑ a, x a ^ 2) - axisPeak x

private theorem axisPeak_le_total (x : Fin 3 → ℝ) : axisPeak x ≤ ∑ a, x a ^ 2 := by
  apply Finset.sup'_le
  intro a ha
  exact Finset.single_le_sum (fun b _ => sq_nonneg (x b)) ha

private theorem le_axisPeak (x : Fin 3 → ℝ) (a : Fin 3) : x a ^ 2 ≤ axisPeak x :=
  Finset.le_sup' (fun b => x b ^ 2) (Finset.mem_univ a)

private theorem exists_axisPeak (x : Fin 3 → ℝ) : ∃ a, axisPeak x = x a ^ 2 := by
  obtain ⟨a, _, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun b : Fin 3 => x b ^ 2)
  exact ⟨a, h⟩

theorem onsiteDiscardEnergy_nonneg (x : Fin 3 → ℝ) : 0 ≤ onsiteDiscardEnergy x :=
  sub_nonneg.mpr (axisPeak_le_total x)

private theorem onsiteDiscardEnergy_le_total (x : Fin 3 → ℝ) : onsiteDiscardEnergy x ≤ ∑ a, x a ^ 2 :=
  sub_le_self _ ((sq_nonneg (x 0)).trans (le_axisPeak x 0))

private theorem erase_axis_energy (x : Fin 3 → ℝ) (a : Fin 3) :
    (∑ b ∈ Finset.univ.erase a, x b ^ 2) = (∑ b, x b ^ 2) - x a ^ 2 := by
  conv_rhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  ring

private def rowSquaredError (x y : Fin 3 → ℝ) : ℝ := ∑ a, (x a - y a) ^ 2

private theorem rowSquaredError_nonneg (x y : Fin 3 → ℝ) : 0 ≤ rowSquaredError x y :=
  Finset.sum_nonneg fun a _ => sq_nonneg (x a - y a)

private theorem onsiteDiscardEnergy_le_rowSquaredError (x y : Fin 3 → ℝ)
    (hy : ({a | y a ≠ 0} : Set (Fin 3)).Subsingleton) : onsiteDiscardEnergy x ≤ rowSquaredError x y := by
  obtain ⟨a, ha⟩ : ∃ a : Fin 3, ∀ b ≠ a, y b = 0 := by
    by_cases he : ∃ a, y a ≠ 0
    · obtain ⟨a, ha⟩ := he
      exact ⟨a, fun b hb => Classical.byContradiction fun h => hb (hy h ha)⟩
    · exact ⟨0, fun b _ => Classical.byContradiction fun h => he ⟨b, h⟩⟩
  calc
    _ ≤ (∑ b, x b ^ 2) - x a ^ 2 := sub_le_sub_left (le_axisPeak x a) _
    _ = ∑ b ∈ Finset.univ.erase a, x b ^ 2 := (erase_axis_energy x a).symm
    _ = ∑ b ∈ Finset.univ.erase a, (x b - y b) ^ 2 := by
      exact Finset.sum_congr rfl fun b hb => by rw [ha b (Finset.ne_of_mem_erase hb), sub_zero]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun b _ _ => sq_nonneg _

private theorem rowSquaredError_keep_peak (x : Fin 3 → ℝ) (a : Fin 3) (ha : axisPeak x = x a ^ 2) :
    rowSquaredError x (fun b => if b = a then x b else 0) = onsiteDiscardEnergy x := by
  unfold rowSquaredError onsiteDiscardEnergy
  rw [ha, ← erase_axis_energy x a]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  simp only [if_true, sub_self, zero_pow (by omega : 2 ≠ 0), zero_add]
  exact Finset.sum_congr rfl fun b hb => by rw [if_neg (Finset.ne_of_mem_erase hb), sub_zero]

variable {n : ℕ}

/-- The onsite coefficients of a path shell at one site. -/
def pathOnsiteRow (u : PathShell n) (s : Fin (n + 2)) (a : Fin 3) : ℝ := u (.inl (s, a))

/-- Squared error in all onsite coordinates, omitting bonds. -/
def onsiteSquaredError (u v : PathShell n) : ℝ := ∑ s, rowSquaredError (pathOnsiteRow u s) (pathOnsiteRow v s)

/-- The squared onsite projection distance to noncontextual support. -/
def noncontextualOnsiteSquaredDistance (u : PathShell n) : ℝ :=
  (∑ s, onsiteDiscardEnergy (pathOnsiteRow u s)) -
    Finset.univ.sup' Finset.univ_nonempty (fun s => onsiteDiscardEnergy (pathOnsiteRow u s))

/-- Every noncontextual path Hamiltonian pays the regular-site costs
outside one possible multiaxis site. -/
theorem noncontextualOnsiteSquaredDistance_le (u v : PathShell n)
    (hv : PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1))) :
    noncontextualOnsiteSquaredDistance u ≤ onsiteSquaredError u v := by
  classical
  let B := multiAxisSites {ia | v (.inl ia) ≠ 0}
  have hb : B.Subsingleton := path_noncontextual_forbids_two_multiaxis_sites v hv
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 2), ∀ s ≠ j, s ∉ B := by
    by_cases he : B.Nonempty
    · obtain ⟨j, hj⟩ := he
      exact ⟨j, fun _ hne hs => hne (hb hs hj)⟩
    · exact ⟨0, fun s _ hs => he ⟨s, hs⟩⟩
  have hs (s : Fin (n + 2)) (hne : s ≠ j) : ({a | pathOnsiteRow v s a ≠ 0} : Set (Fin 3)).Subsingleton := by
    intro a ha b hb
    by_contra he
    exact hj s hne ⟨a, b, ha, hb, he⟩
  have hpeak := Finset.le_sup' (fun s => onsiteDiscardEnergy (pathOnsiteRow u s)) (Finset.mem_univ j)
  calc
    _ ≤ (∑ s, onsiteDiscardEnergy (pathOnsiteRow u s)) - onsiteDiscardEnergy (pathOnsiteRow u j) :=
      sub_le_sub_left hpeak _
    _ = ∑ s ∈ Finset.univ.erase j, onsiteDiscardEnergy (pathOnsiteRow u s) := by
      conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      ring
    _ ≤ ∑ s ∈ Finset.univ.erase j, rowSquaredError (pathOnsiteRow u s) (pathOnsiteRow v s) := by
      exact Finset.sum_le_sum fun s hs' => onsiteDiscardEnergy_le_rowSquaredError _ _ (hs s (Finset.ne_of_mem_erase hs'))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ => rowSquaredError_nonneg _ _

/-- Keep the strongest axis on each regular site and take as exceptional
the site with the greatest discarded mass. This attains the distance. -/
theorem exists_noncontextualOnsiteSquaredDistance_minimizer (u : PathShell n) :
    ∃ v : PathShell n, PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)) ∧
      onsiteSquaredError u v = noncontextualOnsiteSquaredDistance u := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun s : Fin (n + 2) => onsiteDiscardEnergy (pathOnsiteRow u s))
  choose a ha using fun s : Fin (n + 2) => exists_axisPeak (pathOnsiteRow u s)
  let v : PathShell n := WithLp.toLp 2 fun l => match l with
    | .inl (s, b) => if s = j ∨ b = a s then u (.inl (s, b)) else 0
    | .inr _ => 0
  have hv (s : Fin (n + 2)) (hs : s ≠ j) :
      pathOnsiteRow v s = fun b => if b = a s then pathOnsiteRow u s b else 0 := by
    funext b
    change (if s = j ∨ b = a s then u (.inl (s,b)) else 0) = _
    simp only [hs, false_or, pathOnsiteRow]
  have hsite (s : Fin (n + 2)) (hs : s ∈ multiAxisSites {ia | v (.inl ia) ≠ 0}) : s = j := by
    by_contra hne
    rcases hs with ⟨b, c, hb, hc, hbc⟩
    have hkeep (b : Fin 3) (h : pathOnsiteRow v s b ≠ 0) : b = a s := by
      by_contra hb
      exact h (by simp only [hv s hne, if_neg hb])
    exact hbc ((hkeep b hb).trans (hkeep c hc).symm)
  refine ⟨v, path_noncontextual_of_zero_bonds v (fun _ => rfl) (fun s hs t ht =>
    (hsite s hs).trans (hsite t ht).symm), ?_⟩
  have hvj : pathOnsiteRow v j = pathOnsiteRow u j := by
    funext b
    change (if j = j ∨ b = a j then u (.inl (j,b)) else 0) = _
    simp only [true_or, if_true, pathOnsiteRow]
  have he : (∑ s ∈ Finset.univ.erase j, rowSquaredError (pathOnsiteRow u s) (pathOnsiteRow v s)) =
      ∑ s ∈ Finset.univ.erase j, onsiteDiscardEnergy (pathOnsiteRow u s) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hv s (Finset.ne_of_mem_erase hs), rowSquaredError_keep_peak _ _ (ha s)]
  unfold onsiteSquaredError noncontextualOnsiteSquaredDistance
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hvj]
  have hz : rowSquaredError (pathOnsiteRow u j) (pathOnsiteRow u j) = 0 := by simp [rowSquaredError]
  rw [hz, zero_add, he, hj]
  conv_rhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  ring

/-- The optimal onsite cost is a lower bound on squared operator distance
to every noncontextual path Hamiltonian. -/
theorem noncontextualOnsiteSquaredDistance_le_operator (u v : PathShell n)
    (hv : PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1))) :
    noncontextualOnsiteSquaredDistance u ≤ ‖pathHamiltonian u - pathHamiltonian v‖ ^ 2 := by
  refine (noncontextualOnsiteSquaredDistance_le u v hv).trans ?_
  have h : onsiteSquaredError u v ≤ ‖u - v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]
    change onsiteSquaredError u v ≤ onsiteSquaredError u v +
      ∑ e : Fin (n + 1), ∑ a : Fin 3, ∑ b : Fin 3, (u (.inr (e, a, b)) - v (.inr (e, a, b))) ^ 2
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  exact h.trans (pow_le_pow_left₀ (norm_nonneg _) (pathShell_dist_le_pathHamiltonian_dist u v) 2)

theorem measurable_onsiteDiscardEnergy : Measurable onsiteDiscardEnergy := by
  have hsq (a : Fin 3) : Measurable (fun x : Fin 3 → ℝ => x a ^ 2) := (measurable_pi_apply a).pow_const 2
  have he : axisPeak = Finset.univ.sup' Finset.univ_nonempty (fun a (x : Fin 3 → ℝ) => x a ^ 2) := by
    funext x
    unfold axisPeak
    exact (Finset.sup'_apply (C := fun _ : Fin 3 → ℝ => ℝ) (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty)
      (fun a (y : Fin 3 → ℝ) => y a ^ 2) x).symm
  have hpeak : Measurable axisPeak := by
    rw [he]
    exact Finset.measurable_sup' Finset.univ_nonempty (fun a _ => hsq a)
  exact (Finset.measurable_sum _ fun a _ => hsq a).sub hpeak

private theorem integrable_onsiteDiscardEnergy : Integrable onsiteDiscardEnergy gaussianOnsiteRowLaw := by
  have hstd : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).integrable_sq
  have hsq (a : Fin 3) : Integrable (fun x : Fin 3 → ℝ => x a ^ 2) gaussianOnsiteRowLaw :=
    (measurePreserving_eval_infinitePi (fun _ : Fin 3 => gaussianReal 0 1) a).integrable_comp_of_integrable hstd
  have hs : Integrable (fun x : Fin 3 → ℝ => ∑ a, x a ^ 2) gaussianOnsiteRowLaw :=
    integrable_finsetSum _ fun a _ => hsq a
  refine hs.mono' measurable_onsiteDiscardEnergy.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (onsiteDiscardEnergy_nonneg x)]
  exact onsiteDiscardEnergy_le_total x

/-- Mean squared onsite loss per regular site under standard Gaussian disorder. -/
def gaussianOnsiteDiscardMean : ℝ := ∫ x, onsiteDiscardEnergy x ∂gaussianOnsiteRowLaw

theorem gaussianOnsiteDiscardMean_pos : 0 < gaussianOnsiteDiscardMean := by
  classical
  apply (integral_pos_iff_support_of_nonneg onsiteDiscardEnergy_nonneg integrable_onsiteDiscardEnergy).mpr
  let B : Set (Fin 3 → ℝ) := ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).pi fun _ => Icc (1 : ℝ) 2
  have hsub : B ⊆ Function.support onsiteDiscardEnergy := by
    intro x hx
    obtain ⟨a, ha⟩ := exists_axisPeak x
    obtain ⟨b, hb⟩ : ∃ b : Fin 3, b ≠ a := by
      by_cases he : a = 0
      · subst a
        exact ⟨1, Ne.symm Fin.zero_ne_one⟩
      · exact ⟨0, Ne.symm he⟩
    have hlarge : 1 ≤ x b := ((Set.mem_pi.mp hx) b (by simp)).1
    have hs : 1 ≤ x b ^ 2 := by nlinarith only [hlarge, sq_nonneg (x b - 1)]
    have h := Finset.single_le_sum (s := Finset.univ.erase a) (f := fun c => x c ^ 2)
      (fun c _ => sq_nonneg (x c)) (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩)
    rw [erase_axis_energy, ← ha] at h
    exact ne_of_gt (zero_lt_one.trans_le (hs.trans h))
  have hmass : gaussianOnsiteRowLaw B = (gaussianReal 0 1 (Icc (1 : ℝ) 2)) ^ 3 := by
    unfold gaussianOnsiteRowLaw B
    rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_Icc), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  apply lt_of_lt_of_le _ (measure_mono hsub)
  rw [hmass]
  exact pos_iff_ne_zero.mpr (pow_ne_zero _ (gaussianReal_Icc_pos (by norm_num : (1 : ℝ) < 2)).ne')

/-- Along a single Gaussian path, every integrable measurable function of
the onsite row obeys the strong law of large numbers. -/
theorem gaussian_ae_onsiteRow_mean (f : (Fin 3 → ℝ) → ℝ)
    (hf : Measurable f) (hi : Integrable f gaussianOnsiteRowLaw) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto
      (fun N : ℕ => (∑ j ∈ Finset.range N, f (gaussianOnsiteRow ω j)) / (N : ℝ))
      atTop (𝓝 (∫ x, f x ∂gaussianOnsiteRowLaw)) := by
  letI : IsProbabilityMeasure gaussianOnsiteRowLaw := by unfold gaussianOnsiteRowLaw; infer_instance
  let ν := Measure.infinitePi fun _ : ℕ => gaussianOnsiteRowLaw
  let X (i : ℕ) (z : ℕ → Fin 3 → ℝ) := f (z i)
  have hident (i : ℕ) : IdentDistrib (X i) f ν gaussianOnsiteRowLaw := by
    have hm := measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianOnsiteRowLaw) i
    have hEval : IdentDistrib (Function.eval i) id ν gaussianOnsiteRowLaw :=
      ⟨hm.measurable.aemeasurable, measurable_id.aemeasurable, by rw [Measure.map_id]; exact hm.map_eq⟩
    exact hEval.comp hf
  have hindep : iIndepFun X ν :=
    iIndepFun_infinitePi (P := fun _ : ℕ => gaussianOnsiteRowLaw)
      (X := fun _ => f) (fun _ => hf)
  have h := strong_law_ae_real X ((hident 0).integrable_iff.mpr hi)
    (fun _ _ hij => hindep.indepFun hij) (fun i => (hident i).trans (hident 0).symm)
  rw [(hident 0).integral_eq] at h
  exact (measurePreserving_gaussianOnsiteRows (fun i : ℕ => i) (fun _ _ h => h)).quasiMeasurePreserving.ae h

private theorem tendsto_inv_succ_natCast :
    Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

private theorem tendsto_prefixSummand_div_of_tendsto_mean {x : ℕ → ℝ} {μ : ℝ}
    (hmean : Tendsto (fun k : ℕ => (∑ j ∈ Finset.range k, x j) / (k : ℝ)) atTop (𝓝 μ)) :
    Tendsto (fun k : ℕ => x k / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  let S (k : ℕ) := ∑ j ∈ Finset.range k, x j
  let D (k : ℕ) : ℝ := (k + 1 : ℕ)
  have hr (k : ℕ) : (k : ℝ) / D k = 1 - (D k)⁻¹ := by
    have hd : 0 < D k := by dsimp [D]; positivity
    have hk : (k : ℝ) = D k - 1 := by simp [D]
    conv_lhs => rw [hk]
    rw [sub_div, div_self hd.ne', one_div]
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hfac : Tendsto (fun k : ℕ => (k : ℝ) / D k) atTop (𝓝 1) := by
    have h : Tendsto (fun k => (1 : ℝ) - (D k)⁻¹) atTop (𝓝 1) := by
      simpa only [sub_zero] using hconst.sub tendsto_inv_succ_natCast
    exact h.congr' (Eventually.of_forall fun k => (hr k).symm)
  have hS : Tendsto (fun k => S k / (k : ℝ)) atTop (𝓝 μ) := hmean
  have hnext : Tendsto (fun k => S (k + 1) / D k) atTop (𝓝 μ) :=
    hmean.comp (tendsto_add_atTop_nat 1)
  have hzero : Tendsto (fun k => S (k + 1) / D k - (S k / (k : ℝ)) * ((k : ℝ) / D k))
      atTop (𝓝 0) := by
    simpa only [mul_one, sub_self] using hnext.sub (hS.mul hfac)
  refine hzero.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hcancel : (S k / (k : ℝ)) * ((k : ℝ) / D k) = S k / D k := by
    rw [← mul_div_assoc, div_mul_cancel₀ _ (Nat.cast_pos.mpr hk : 0 < (k : ℝ)).ne']
  change S (k + 1) / D k - (S k / (k : ℝ)) * ((k : ℝ) / D k) = x k / D k
  rw [hcancel, ← sub_div]
  simp only [S, Finset.sum_range_succ, add_sub_cancel_left]

private theorem prefixNonempty (k : ℕ) : (Finset.range (k + 1)).Nonempty :=
  ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩

private def prefixMaximum (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).sup' (prefixNonempty k) x

private theorem tendsto_prefixMaximum_div_of_tendsto_mean (x : ℕ → ℝ) (hx : ∀ j, 0 ≤ x j)
    {μ : ℝ} (hmean : Tendsto (fun k : ℕ => (∑ j ∈ Finset.range k, x j) / (k : ℝ))
      atTop (𝓝 μ)) :
    Tendsto (fun k : ℕ => prefixMaximum x k / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have ht := tendsto_prefixSummand_div_of_tendsto_mean hmean
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun k => ha.trans_le (div_nonneg
      ((hx 0).trans (Finset.le_sup' x (Finset.mem_range.mpr (Nat.succ_pos k)))) (Nat.cast_nonneg _))
  · intro b hb
    obtain ⟨K, hK⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 b hb)
    let B := ∑ j ∈ Finset.range K, x j
    have hconst : Tendsto (fun _ : ℕ => B) atTop (𝓝 B) := tendsto_const_nhds
    have hB : Tendsto (fun k : ℕ => B / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using hconst.mul tendsto_inv_succ_natCast
    filter_upwards [(tendsto_order.mp hB).2 b hb] with k hk
    obtain ⟨j, hj, hjmax⟩ := Finset.exists_mem_eq_sup' (prefixNonempty k) x
    change prefixMaximum x k = x j at hjmax
    change prefixMaximum x k / ((k + 1 : ℕ) : ℝ) < b
    rw [hjmax]
    by_cases h : j < K
    · have hle : x j ≤ B := Finset.single_le_sum (fun i _ => hx i) (Finset.mem_range.mpr h)
      exact (div_le_div_of_nonneg_right hle (Nat.cast_nonneg _)).trans_lt hk
    · have hle : ((j + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) :=
        Nat.cast_le.mpr (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
      exact (div_le_div_of_nonneg_left (hx j) (Nat.cast_pos.mpr (Nat.succ_pos j)) hle).trans_lt
        (hK j (le_of_not_gt h))

/-- The discarded mass per site converges almost surely to its Gaussian mean.
The one exceptional site contributes a vanishing fraction of the squared cost. -/
theorem gaussian_ae_noncontextualOnsiteSquaredDistance_mean :
    ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto
      (fun k : ℕ => noncontextualOnsiteSquaredDistance (pathPauliDisorderShell ω k) / ((k + 2 : ℕ) : ℝ))
      atTop (𝓝 gaussianOnsiteDiscardMean) := by
  filter_upwards [gaussian_ae_onsiteRow_mean onsiteDiscardEnergy measurable_onsiteDiscardEnergy
    integrable_onsiteDiscardEnergy] with ω hω
  let x (j : ℕ) := onsiteDiscardEnergy (gaussianOnsiteRow ω j)
  have hs : Tendsto (fun k : ℕ => (∑ j ∈ Finset.range k, x j) / (k : ℝ))
      atTop (𝓝 gaussianOnsiteDiscardMean) := hω
  have hm := tendsto_prefixMaximum_div_of_tendsto_mean x (fun j => onsiteDiscardEnergy_nonneg _) hs
  have hs' : Tendsto (fun k : ℕ => (∑ j ∈ Finset.range (k + 2), x j) / ((k + 2 : ℕ) : ℝ))
      atTop (𝓝 gaussianOnsiteDiscardMean) := hs.comp (tendsto_add_atTop_nat 2)
  have hm' : Tendsto (fun k : ℕ => prefixMaximum x (k + 1) / ((k + 2 : ℕ) : ℝ))
      atTop (𝓝 0) := hm.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun k : ℕ => (∑ j ∈ Finset.range (k + 2), x j) / ((k + 2 : ℕ) : ℝ) -
      prefixMaximum x (k + 1) / ((k + 2 : ℕ) : ℝ)) atTop (𝓝 gaussianOnsiteDiscardMean) := by
    simpa only [sub_zero] using hs'.sub hm'
  refine hlim.congr' (Eventually.of_forall fun k => ?_)
  have hmax : Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (k + 2) => x i.val) =
      prefixMaximum x (k + 1) := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      exact Finset.le_sup' x (Finset.mem_range.mpr i.isLt)
    · apply Finset.sup'_le
      intro j hj
      let i : Fin (k + 2) := ⟨j, Finset.mem_range.mp hj⟩
      exact Finset.le_sup' (fun i : Fin (k + 2) => x i.val) (Finset.mem_univ i)
  change (∑ j ∈ Finset.range (k + 2), x j) / ((k + 2 : ℕ) : ℝ) -
    prefixMaximum x (k + 1) / ((k + 2 : ℕ) : ℝ) =
    ((∑ i : Fin (k + 2), x i.val) - Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin (k + 2) => x i.val)) / ((k + 2 : ℕ) : ℝ)
  rw [hmax, sub_div, Fin.sum_univ_eq_sum_range x]

/-- Every coefficient below the square root of the mean onsite loss gives
an eventual operator distance lower bound proportional to the square root of path length. -/
theorem gaussian_ae_eventually_noncontextual_operator_gap :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ c : ℝ, 0 ≤ c → c ^ 2 < gaussianOnsiteDiscardMean →
      ∀ᶠ k : ℕ in atTop, ∀ v : PathShell k,
        PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)) →
          c * Real.sqrt ((k + 2 : ℕ) : ℝ) ≤ ‖pathHamiltonian (pathPauliDisorderShell ω k) - pathHamiltonian v‖ := by
  filter_upwards [gaussian_ae_noncontextualOnsiteSquaredDistance_mean] with ω hω
  intro c hc hμ
  filter_upwards [(tendsto_order.mp hω).1 (c ^ 2) hμ] with k hk
  intro v hv
  have hN : 0 < ((k + 2 : ℕ) : ℝ) := by positivity
  have hl := (lt_div_iff₀ hN).mp hk
  have hsq : (c * Real.sqrt ((k + 2 : ℕ) : ℝ)) ^ 2 ≤
      ‖pathHamiltonian (pathPauliDisorderShell ω k) - pathHamiltonian v‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hN.le]
    exact hl.le.trans (noncontextualOnsiteSquaredDistance_le_operator _ _ hv)
  exact (sq_le_sq₀ (mul_nonneg hc (Real.sqrt_nonneg _)) (norm_nonneg _)).mp hsq

#print axioms noncontextualOnsiteSquaredDistance_le
#print axioms exists_noncontextualOnsiteSquaredDistance_minimizer
#print axioms noncontextualOnsiteSquaredDistance_le_operator
#print axioms gaussianOnsiteDiscardMean_pos
#print axioms gaussian_ae_onsiteRow_mean
#print axioms gaussian_ae_noncontextualOnsiteSquaredDistance_mean
#print axioms gaussian_ae_eventually_noncontextual_operator_gap

end

end GaloisForLFunctions.HTGeometry

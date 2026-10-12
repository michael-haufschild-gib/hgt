import GaloisForLFunctions.RHTower.ShiftAverageCrowdedPersistence
import GaloisForLFunctions.RHTower.XiCosineShiftDeepZeroBudget

/-!
# Crowded persistence of a deep zero of `Ξ` under the cosine producer

Let `ζ₀ = xiSpectralPoint q₀` be a zero of `Ξ` with `η + r < Im ζ₀ − h`. Fix a finite set `Ex` of
other zero copies and suppose:
* every copy outside `{q₀} ∪ Ex` lies at height `≤ η`;
* the copies in `Ex` change the modulus ratio across the shift by at most a factor `B` on the circle
  `|z − (ζ₀ − ih)| = r`, and none of them lies at `z + ih` for `z` on the circle;
* a set `Nb` of further copies lies at heights `≥ −η` and within horizontal distance `H` of `ζ₀`;
* `((2h + r)/r)·B·√(1 − κ)^{#Nb} < 1`, with `κ = crowdKappa ζ₀ h r η H`.

**Theorem** (`exists_zero_cosShiftXi_of_crowded`). Then `cos(hD)Ξ` has a zero `z` with
`|z − (ζ₀ − ih)| ≤ r` and `Im z > η`, in particular a nonreal zero.

**Proof.** For large `n` the Hadamard polynomial `R_n` (`xiRealApprox`) carries `q₀`, `Ex` and `Nb`
among its roots. Its remaining roots are zeros of `Ξ` below height `η`. The polynomial crowded
persistence law (`exists_zero_shiftAvg_near_deep_root`) gives a root `z_n` of the shift average of
`R_n` in the ball. These converge locally uniformly to `cos(hD)Ξ`, and a limit point of the `z_n`
in the closed ball is a zero.

So a deep zero of `ξ` stays a defect of the cosine producer for every depth `h` below its own depth
minus `η + r`, once enough shallow zeros crowd around it. The cosine ladder therefore does not
amplify: lowering its real-rootedness threshold below the depth of a crowded deep zero is impossible.
-/

open Complex Filter Topology Set Polynomial Metric

namespace RHTower.CosineCrowdedPersistence

open GaloisForLFunctions.HTGeometry RHTower.DeBruijn RHTower.CosineDefectBudget
  RHTower.CrowdedPersistence

noncomputable section

theorem eventually_subset_xiPairedCopyFinset (F : Finset XiZeroCopy) :
    ∀ᶠ n in atTop, F ⊆ xiPairedCopyFinset (xiConjClosedFinset n) :=
  (Filter.tendsto_atTop.mp
    (xiPairedCopyFinset_tendsto_atTop.comp xiConjClosedFinset_tendsto)) F

theorem roots_map_xiRealApprox (n : ℕ) :
    ((xiRealApprox n).map Complex.ofRealHom).roots =
      (xiPairedCopyFinset (xiConjClosedFinset n)).val.map xiSpectralPoint := by
  rw [map_xiRealApprox, roots_C_mul _ XiC_zero_ne_zero, roots_xiZeroPoly]

/-- One step: once the Hadamard polynomial `R_n` carries `q₀`, `Ex` and `Nb`, its shift average has
a root within `r` of `ζ₀ − ih`. -/
theorem exists_zero_shiftAvg_xiRealApprox_of_crowded {q₀ : XiZeroCopy} {Ex Nb : Finset XiZeroCopy}
    {h r η H B : ℝ} (hh : 0 < h) (hr : 0 < r) (hη : 0 ≤ η) (hB0 : 0 ≤ B)
    (hgap : η + r < (xiSpectralPoint q₀).im - h) (hq₀Ex : q₀ ∉ Ex) {n : ℕ}
    (hshallow : ∀ q ∈ xiPairedCopyFinset (xiConjClosedFinset n), q ≠ q₀ → q ∉ Ex →
      (xiSpectralPoint q).im ≤ η)
    (hExne : ∀ q ∈ Ex, ∀ z ∈ sphere (xiSpectralPoint q₀ - h * I) r, z + h * I ≠ xiSpectralPoint q)
    (hExB : ∀ z ∈ sphere (xiSpectralPoint q₀ - h * I) r,
      (Ex.val.map fun q => ‖z - h * I - xiSpectralPoint q‖).prod ≤
        B * (Ex.val.map fun q => ‖z + h * I - xiSpectralPoint q‖).prod)
    (hNb : ∀ q ∈ Nb, q ≠ q₀ ∧ q ∉ Ex ∧
      |(xiSpectralPoint q).re - (xiSpectralPoint q₀).re| ≤ H ∧ -η ≤ (xiSpectralPoint q).im)
    (hcrowd : (2 * h + r) / r * B *
      Real.sqrt (1 - crowdKappa (xiSpectralPoint q₀) h r η H) ^ Nb.card < 1)
    (hn : insert q₀ Ex ∪ Nb ⊆ xiPairedCopyFinset (xiConjClosedFinset n)) :
    ∃ z, ‖z - (xiSpectralPoint q₀ - h * I)‖ < r ∧
      ((shiftAvg h (xiRealApprox n)).map Complex.ofRealHom).eval z = 0 := by
  classical
  set T := xiPairedCopyFinset (xiConjClosedFinset n) with hT
  set A : Finset XiZeroCopy := insert q₀ Ex with hA
  have hAT : A ⊆ T := fun q hq => hn (Finset.mem_union_left _ hq)
  have hdisj : Disjoint A (T \ A) := Finset.disjoint_sdiff
  have hAval : A.val = q₀ ::ₘ Ex.val := Finset.insert_val_of_notMem hq₀Ex
  have hTval : T.val = q₀ ::ₘ (Ex.val + (T \ A).val) := by
    have h1 : T.val = (A.disjUnion (T \ A) hdisj).val := by
      rw [Finset.disjUnion_eq_union, Finset.union_sdiff_of_subset hAT]
    rw [h1, Finset.disjUnion_val, hAval, Multiset.cons_add]
  have hdecomp : ((xiRealApprox n).map Complex.ofRealHom).roots =
      xiSpectralPoint q₀ ::ₘ (Ex.val.map xiSpectralPoint + (T \ A).val.map xiSpectralPoint) := by
    rw [roots_map_xiRealApprox, ← hT, hTval, Multiset.map_cons, Multiset.map_add]
  have hSbelow : ∀ ζ ∈ (T \ A).val.map xiSpectralPoint, ζ.im ≤ η := by
    intro ζ hζ
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hζ
    have hq' := Finset.mem_sdiff.mp (Finset.mem_val.mp hq)
    have hq'' := hq'.2
    rw [hA, Finset.mem_insert, not_or] at hq''
    exact hshallow q hq'.1 hq''.1 hq''.2
  have hEne : ∀ ζ ∈ Ex.val.map xiSpectralPoint, ∀ z ∈ sphere (xiSpectralPoint q₀ - h * I) r,
      z + h * I ≠ ζ := by
    intro ζ hζ z hz
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hζ
    exact hExne q (Finset.mem_val.mp hq) z hz
  have hEB : ∀ z ∈ sphere (xiSpectralPoint q₀ - h * I) r,
      ((Ex.val.map xiSpectralPoint).map fun ζ => ‖z - h * I - ζ‖).prod ≤
        B * ((Ex.val.map xiSpectralPoint).map fun ζ => ‖z + h * I - ζ‖).prod := by
    intro z hz
    rw [Multiset.map_map, Multiset.map_map]
    exact hExB z hz
  -- the neighbours are among the roots of `S`
  have hNbS : Nb.card ≤ Multiset.card (((T \ A).val.map xiSpectralPoint).filter fun ζ =>
      |ζ.re - (xiSpectralPoint q₀).re| ≤ H ∧ -η ≤ ζ.im) := by
    have hsub : Nb ⊆ T \ A := by
      intro q hq
      obtain ⟨h1, h2, _, _⟩ := hNb q hq
      refine Finset.mem_sdiff.mpr ⟨hn (Finset.mem_union_right _ hq), ?_⟩
      rw [hA, Finset.mem_insert, not_or]
      exact ⟨h1, h2⟩
    have hle : Nb.val.map xiSpectralPoint ≤ (T \ A).val.map xiSpectralPoint :=
      Multiset.map_le_map (Finset.val_le_iff.mpr hsub)
    have hfilt : (Nb.val.map xiSpectralPoint).filter (fun ζ =>
        |ζ.re - (xiSpectralPoint q₀).re| ≤ H ∧ -η ≤ ζ.im) = Nb.val.map xiSpectralPoint := by
      rw [Multiset.filter_eq_self]
      intro ζ hζ
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hζ
      obtain ⟨_, _, h3, h4⟩ := hNb q (Finset.mem_val.mp hq)
      exact ⟨h3, h4⟩
    have := Multiset.card_le_card (Multiset.filter_le_filter (fun ζ =>
      |ζ.re - (xiSpectralPoint q₀).re| ≤ H ∧ -η ≤ ζ.im) hle)
    rwa [hfilt, Multiset.card_map, Finset.card_val] at this
  have hκ : 0 ≤ crowdKappa (xiSpectralPoint q₀) h r η H := by
    unfold crowdKappa
    have : 0 ≤ (xiSpectralPoint q₀).im - h - r - η := by linarith
    positivity
  have hρ1 : Real.sqrt (1 - crowdKappa (xiSpectralPoint q₀) h r η H) ≤ 1 := by
    rw [Real.sqrt_le_one]
    linarith
  have hcrowd' : (2 * h + r) / r * B * Real.sqrt (1 - crowdKappa (xiSpectralPoint q₀) h r η H) ^
      Multiset.card (((T \ A).val.map xiSpectralPoint).filter fun ζ =>
        |ζ.re - (xiSpectralPoint q₀).re| ≤ H ∧ -η ≤ ζ.im) < 1 := by
    refine lt_of_le_of_lt ?_ hcrowd
    refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (Real.sqrt_nonneg _) hρ1 hNbS) ?_
    have : 0 ≤ 2 * h + r := by linarith
    positivity
  obtain ⟨z, hz, -, hz0⟩ := exists_zero_shiftAvg_near_deep_root (xiRealApprox_ne_zero n) hdecomp
    hh hr hη hgap hSbelow hEne hEB hcrowd'
  exact ⟨z, hz, hz0⟩

/-- **Crowded persistence for `Ξ`.** -/
theorem exists_zero_cosShiftXi_of_crowded {q₀ : XiZeroCopy} {Ex Nb : Finset XiZeroCopy}
    {h r η H B : ℝ} (hh : 0 < h) (hr : 0 < r) (hη : 0 ≤ η) (hB0 : 0 ≤ B)
    (hgap : η + r < (xiSpectralPoint q₀).im - h) (hq₀Ex : q₀ ∉ Ex)
    (hshallow : ∀ q, q ≠ q₀ → q ∉ Ex → (xiSpectralPoint q).im ≤ η)
    (hExne : ∀ q ∈ Ex, ∀ z ∈ sphere (xiSpectralPoint q₀ - h * I) r, z + h * I ≠ xiSpectralPoint q)
    (hExB : ∀ z ∈ sphere (xiSpectralPoint q₀ - h * I) r,
      (Ex.val.map fun q => ‖z - h * I - xiSpectralPoint q‖).prod ≤
        B * (Ex.val.map fun q => ‖z + h * I - xiSpectralPoint q‖).prod)
    (hNb : ∀ q ∈ Nb, q ≠ q₀ ∧ q ∉ Ex ∧
      |(xiSpectralPoint q).re - (xiSpectralPoint q₀).re| ≤ H ∧ -η ≤ (xiSpectralPoint q).im)
    (hcrowd : (2 * h + r) / r * B *
      Real.sqrt (1 - crowdKappa (xiSpectralPoint q₀) h r η H) ^ Nb.card < 1) :
    ∃ z, ‖z - (xiSpectralPoint q₀ - h * I)‖ ≤ r ∧ η < z.im ∧ cosShiftXi h z = 0 := by
  set w₀ := xiSpectralPoint q₀ - h * I with hw₀
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_subset_xiPairedCopyFinset (insert q₀ Ex ∪ Nb))
  choose zs hzs using fun n : ℕ => exists_zero_shiftAvg_xiRealApprox_of_crowded hh hr hη hB0 hgap
    hq₀Ex (fun q _ => hshallow q) hExne hExB hNb hcrowd (hN₀ (n + N₀) (by omega))
  have hmem : ∀ n, zs n ∈ closedBall w₀ r := fun n => by
    rw [mem_closedBall, dist_eq_norm]
    exact (hzs n).1.le
  obtain ⟨z, hz, φ, hφ, hlim⟩ := (isCompact_closedBall w₀ r).tendsto_subseq hmem
  have hψ : Tendsto (fun n => φ n + N₀) atTop atTop :=
    tendsto_atTop_mono (fun n => (hφ.id_le n).trans (Nat.le_add_right _ _)) tendsto_id
  have hconv : TendstoLocallyUniformly
      (fun n z => ((shiftAvg h (xiRealApprox (φ n + N₀))).map Complex.ofRealHom).eval z)
      (cosShiftXi h) atTop := by
    intro u hu x
    obtain ⟨t, ht, hev⟩ := tendstoLocallyUniformly_shiftAvg_xiRealApprox h u hu x
    exact ⟨t, ht, hψ.eventually hev⟩
  have hcont : ContinuousAt (cosShiftXi h) z :=
    (differentiable_cosShiftXi h).continuous.continuousAt
  have htend := hconv.tendsto_comp hcont hlim
  have hzero : cosShiftXi h z = 0 := by
    refine tendsto_nhds_unique htend ?_
    have : (fun n => ((shiftAvg h (xiRealApprox (φ n + N₀))).map Complex.ofRealHom).eval
        ((zs ∘ φ) n)) = fun _ => 0 := funext fun n => (hzs (φ n)).2
    rw [this]
    exact tendsto_const_nhds
  refine ⟨z, by simpa [mem_closedBall, dist_eq_norm] using hz, ?_, hzero⟩
  have h1 := Complex.abs_im_le_norm (z - w₀)
  have h2 : ‖z - w₀‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
  have e : (z - w₀).im = z.im - ((xiSpectralPoint q₀).im - h) := by simp [hw₀]
  rw [e, abs_le] at h1
  linarith

/-- **Crowded persistence with an infinite exceptional set.** The exceptional copies may form any
set, provided every finite part of it changes the modulus ratio by at most `B` on the circle. -/
theorem exists_zero_cosShiftXi_of_exceptionalSet {q₀ : XiZeroCopy} {Exc : Set XiZeroCopy}
    {Nb : Finset XiZeroCopy} {h r η H B : ℝ} (hh : 0 < h) (hr : 0 < r) (hη : 0 ≤ η) (hB0 : 0 ≤ B)
    (hgap : η + r < (xiSpectralPoint q₀).im - h) (hq₀ : q₀ ∉ Exc)
    (hclass : ∀ q, q ≠ q₀ → q ∉ Exc → (xiSpectralPoint q).im ≤ η)
    (hExcne : ∀ q ∈ Exc, ∀ z ∈ sphere (xiSpectralPoint q₀ - h * I) r,
      z + h * I ≠ xiSpectralPoint q)
    (hExcB : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, q ∈ Exc) →
      ∀ z ∈ sphere (xiSpectralPoint q₀ - h * I) r,
        (F.val.map fun q => ‖z - h * I - xiSpectralPoint q‖).prod ≤
          B * (F.val.map fun q => ‖z + h * I - xiSpectralPoint q‖).prod)
    (hNb : ∀ q ∈ Nb, q ≠ q₀ ∧ q ∉ Exc ∧
      |(xiSpectralPoint q).re - (xiSpectralPoint q₀).re| ≤ H ∧ -η ≤ (xiSpectralPoint q).im)
    (hcrowd : (2 * h + r) / r * B *
      Real.sqrt (1 - crowdKappa (xiSpectralPoint q₀) h r η H) ^ Nb.card < 1) :
    ∃ z, ‖z - (xiSpectralPoint q₀ - h * I)‖ ≤ r ∧ η < z.im ∧ cosShiftXi h z = 0 := by
  classical
  set w₀ := xiSpectralPoint q₀ - h * I with hw₀
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_subset_xiPairedCopyFinset (insert q₀ Nb))
  have hstep : ∀ n : ℕ, ∃ z, ‖z - w₀‖ < r ∧
      ((shiftAvg h (xiRealApprox (n + N₀))).map Complex.ofRealHom).eval z = 0 := by
    intro n
    set T := xiPairedCopyFinset (xiConjClosedFinset (n + N₀)) with hT
    set Ex := T.filter (· ∈ Exc) with hEx
    have hT0 := hN₀ (n + N₀) (by omega)
    have hq₀Ex : q₀ ∉ Ex := fun h' => hq₀ (Finset.mem_filter.mp h').2
    have hsub : insert q₀ Ex ∪ Nb ⊆ T := by
      intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hT0 (Finset.mem_insert_self _ _)
        · exact (Finset.mem_filter.mp hq).1
      · exact hT0 (Finset.mem_insert_of_mem hq)
    exact exists_zero_shiftAvg_xiRealApprox_of_crowded hh hr hη hB0 hgap hq₀Ex
      (fun q hqT hq₀' hqEx => hclass q hq₀' fun hE => hqEx (Finset.mem_filter.mpr ⟨hqT, hE⟩))
      (fun q hq => hExcne q (Finset.mem_filter.mp hq).2)
      (hExcB Ex fun q hq => (Finset.mem_filter.mp hq).2)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := hNb q hq
        exact ⟨h1, fun h' => h2 (Finset.mem_filter.mp h').2, h3, h4⟩)
      hcrowd hsub
  choose zs hzs using hstep
  have hmem : ∀ n, zs n ∈ closedBall w₀ r := fun n => by
    rw [mem_closedBall, dist_eq_norm]
    exact (hzs n).1.le
  obtain ⟨z, hz, φ, hφ, hlim⟩ := (isCompact_closedBall w₀ r).tendsto_subseq hmem
  have hψ : Tendsto (fun n => φ n + N₀) atTop atTop :=
    tendsto_atTop_mono (fun n => (hφ.id_le n).trans (Nat.le_add_right _ _)) tendsto_id
  have hconv : TendstoLocallyUniformly
      (fun n z => ((shiftAvg h (xiRealApprox (φ n + N₀))).map Complex.ofRealHom).eval z)
      (cosShiftXi h) atTop := by
    intro u hu x
    obtain ⟨t, ht, hev⟩ := tendstoLocallyUniformly_shiftAvg_xiRealApprox h u hu x
    exact ⟨t, ht, hψ.eventually hev⟩
  have hcont : ContinuousAt (cosShiftXi h) z :=
    (differentiable_cosShiftXi h).continuous.continuousAt
  have htend := hconv.tendsto_comp hcont hlim
  have hzero : cosShiftXi h z = 0 := by
    refine tendsto_nhds_unique htend ?_
    have : (fun n => ((shiftAvg h (xiRealApprox (φ n + N₀))).map Complex.ofRealHom).eval
        ((zs ∘ φ) n)) = fun _ => 0 := funext fun n => (hzs (φ n)).2
    rw [this]
    exact tendsto_const_nhds
  refine ⟨z, by simpa [mem_closedBall, dist_eq_norm] using hz, ?_, hzero⟩
  have h1 := Complex.abs_im_le_norm (z - w₀)
  have h2 : ‖z - w₀‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
  have e : (z - w₀).im = z.im - ((xiSpectralPoint q₀).im - h) := by simp [hw₀]
  rw [e, abs_le] at h1
  linarith

end

end RHTower.CosineCrowdedPersistence

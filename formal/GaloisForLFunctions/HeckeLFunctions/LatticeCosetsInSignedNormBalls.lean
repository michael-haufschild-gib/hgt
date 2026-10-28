import GaloisForLFunctions.ArtinMertens.TheIdealCountHasAPowerSavingErrorTerm

/-!
# Lattice cosets in signed norm balls

The ray class count needs lattice **cosets** in sub-cones of the fundamental cone cut out by signs
at real places.

* **Translated dilates** (`exists_abs_ncard_vadd_smul_sub_le`): if `∂Y` is covered by finitely many
  `M`-Lipschitz images of cube faces, then `|#((v + tY) ∩ Λ) covol(Λ) − tⁿ vol Y| ≤ C tⁿ⁻¹` for all
  `t ≥ 1`, uniformly in the translation `v`.
* **Signed norm balls** (`signedNormBall`): `Y_σ = normLeOne ∩ {σ_w x_w > 0, w ∈ S}`. Their frontier
  lies in that of `normLeOne` (`frontier_signedNormBall_subset`): a limit point with `x_w = 0` has
  norm `0`, so is outside the cone. Their volume does not depend on `σ`
  (`measureReal_signedNormBall_eq`): the sign flips `negAt` preserve the cone and the volume.
* **Cosets in signed balls** (`exists_abs_ncard_vadd_signedNormBall_sub_le`):
  `|#((v + T^{1/n} Y_σ) ∩ Λ) covol(Λ) − T vol(Y_σ)| ≤ C T^{1−1/n}` uniformly in `v`.
-/

noncomputable section

open MeasureTheory Metric Set Bornology Module NumberField NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone NumberField.InfinitePlace
open scoped Pointwise NNReal Classical

namespace GaloisForLFunctions.HeckeLFunctions

open GaloisForLFunctions.ArtinMertens

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Lattice points in translated dilates**: the count of `(v + tY) ∩ L` is
`tⁿ vol(Y)/covol(L) + O(tⁿ⁻¹)` uniformly in the translation `v`. -/
theorem exists_abs_ncard_vadd_smul_sub_le {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    (hι : Fintype.card ι = finrank ℝ E) {φ : J → (ι → ℝ) → E} {M : ℝ≥0}
    (hφ : ∀ j, LipschitzOnWith M (φ j) (Icc 0 1)) (i₀ : J → ι) {c : J → ℝ}
    (hc : ∀ j, c j ∈ Icc (0 : ℝ) 1) {Y : Set E} (hY : IsBounded Y)
    (hfr : frontier Y ⊆ ⋃ j, φ j '' cubeFace (i₀ j) (c j)) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ∀ v : E,
      |(((v +ᵥ t • Y) ∩ (L : Set E)).ncard : ℝ) * ZLattice.covolume L μ -
          t ^ finrank ℝ E * μ.real Y| ≤ C * t ^ (finrank ℝ E - 1) := by
  obtain ⟨d₀, hd₀⟩ := (isBounded_latticeCell L).subset_closedBall 0
  set d := max d₀ 1 with hd
  have hdpos : 0 < d := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hcell : latticeCell L ⊆ closedBall 0 d :=
    hd₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  refine ⟨Fintype.card J * ((M : ℝ) / d + 3) ^ (Fintype.card ι - 1) *
    μ.real (closedBall (0 : E) (3 * d)), fun t ht v => ?_⟩
  have ht0 : 0 < t := by linarith
  -- the volume of `v + tY` is `tⁿ vol Y`
  have hvol : μ.real (v +ᵥ t • Y) = t ^ finrank ℝ E * μ.real Y := by
    rw [measureReal_def, measure_vadd, Measure.addHaar_smul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonneg (pow_nonneg ht0.le _), ← measureReal_def]
  -- its frontier is covered by the `tM`-Lipschitz maps `y ↦ t φ_j(y) + v`
  let h : E ≃ₜ E := (Homeomorph.smulOfNeZero t ht0.ne').trans (Homeomorph.addLeft v)
  have himg : (h : E → E) '' Y = v +ᵥ t • Y := by
    ext x
    simp only [h, Homeomorph.trans_apply, Homeomorph.coe_addLeft, mem_image, mem_vadd_set,
      mem_smul_set, vadd_eq_add]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨t • y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  have hfrt : frontier (v +ᵥ t • Y) ⊆
      ⋃ j, (fun y => v + t • φ j y) '' cubeFace (i₀ j) (c j) := by
    rw [← himg, ← h.image_frontier]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨j, y, hy, rfl⟩ := mem_iUnion.mp (hfr hz)
    exact mem_iUnion.mpr ⟨j, y, hy, rfl⟩
  have hlipt : ∀ j, LipschitzOnWith (⟨t, ht0.le⟩ * M) (fun y => v + t • φ j y) (Icc 0 1) := by
    intro j
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos ht0, NNReal.coe_mul]
    calc t * dist (φ j a) (φ j b) ≤ t * (M * dist a b) :=
          mul_le_mul_of_nonneg_left ((hφ j).dist_le_mul a ha b hb) ht0.le
      _ = _ := (mul_assoc t (M : ℝ) (dist a b)).symm
  have hthick := measureReal_cthickening_iUnion_image_cubeFace_le μ hlipt i₀ hc hdpos
  have hbdd : IsBounded (⋃ j, (fun y => v + t • φ j y) '' cubeFace (i₀ j) (c j)) := by
    refine isBounded_iUnion.mpr fun j => ?_
    exact ((isCompact_Icc.inter_right (isClosed_eq (continuous_apply (i₀ j))
      continuous_const)).image_of_continuousOn
      ((hlipt j).continuousOn.mono inter_subset_left)).isBounded
  have hTfin : μ (cthickening d (⋃ j, (fun y => v + t • φ j y) '' cubeFace (i₀ j) (c j))) ≠ ⊤ :=
    hbdd.cthickening.measure_lt_top.ne
  have hYt : IsBounded (v +ᵥ t • Y) := by
    rw [← himg]
    exact (hY.smul₀ t).vadd v |>.subset (by rw [himg])
  have hA := abs_ncard_mul_covolume_sub_le μ L hcell hYt
  rw [hvol] at hA
  have hceil : ((⌈((⟨t, ht0.le⟩ * M : ℝ≥0) : ℝ) / d⌉₊ + 2 : ℕ) : ℝ) ≤ t * ((M : ℝ) / d + 3) := by
    have hc' := Nat.ceil_lt_add_one (div_nonneg (NNReal.coe_nonneg (⟨t, ht0.le⟩ * M)) hdpos.le)
    have hMd : 0 ≤ (M : ℝ) / d := div_nonneg M.2 hdpos.le
    have hmul : ((⟨t, ht0.le⟩ * M : ℝ≥0) : ℝ) / d = t * ((M : ℝ) / d) := by
      rw [NNReal.coe_mul]
      exact mul_div_assoc t (M : ℝ) d
    rw [hmul] at hc'
    rw [Nat.cast_add, Nat.cast_ofNat, hmul]
    nlinarith
  calc |(((v +ᵥ t • Y) ∩ (L : Set E)).ncard : ℝ) * ZLattice.covolume L μ -
          t ^ finrank ℝ E * μ.real Y|
      ≤ μ.real (cthickening d (frontier (v +ᵥ t • Y))) := hA
    _ ≤ μ.real (cthickening d (⋃ j, (fun y => v + t • φ j y) '' cubeFace (i₀ j) (c j))) :=
        measureReal_mono (cthickening_subset_of_subset d hfrt) hTfin
    _ ≤ _ := hthick
    _ ≤ Fintype.card J * (t * ((M : ℝ) / d + 3)) ^ (Fintype.card ι - 1) *
          μ.real (closedBall (0 : E) (3 * d)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hceil _) (Nat.cast_nonneg _)) measureReal_nonneg
    _ = Fintype.card J * ((M : ℝ) / d + 3) ^ (Fintype.card ι - 1) *
          μ.real (closedBall (0 : E) (3 * d)) * t ^ (finrank ℝ E - 1) := by
        rw [mul_pow, hι]
        ring

end Affine

section Signed

variable {K : Type*} [Field K] [NumberField K]

/-- The **sign region** `{x : σ_w x_w > 0 for w ∈ S}` at a set `S` of real places. -/
def signRegion (S : Set {w : InfinitePlace K // w.IsReal}) (σ : S → ℤˣ) : Set (mixedSpace K) :=
  {x | ∀ w : S, 0 < ((σ w : ℤ) : ℝ) * x.1 w}

/-- The **signed norm ball** `Y_σ = normLeOne ∩ signRegion S σ`. -/
def signedNormBall (S : Set {w : InfinitePlace K // w.IsReal}) (σ : S → ℤˣ) :
    Set (mixedSpace K) :=
  normLeOne K ∩ signRegion S σ

theorem isOpen_signRegion (S : Set {w : InfinitePlace K // w.IsReal}) (σ : S → ℤˣ) :
    IsOpen (signRegion S σ) := by
  have : signRegion S σ = ⋂ w : S, {x : mixedSpace K | 0 < ((σ w : ℤ) : ℝ) * x.1 w} := by
    ext x
    simp [signRegion]
  rw [this]
  exact isOpen_iInter_of_finite fun w =>
    isOpen_lt continuous_const (continuous_const.mul ((continuous_apply _).comp continuous_fst))

/-- **The frontier of a signed norm ball** lies in that of `normLeOne`. -/
theorem frontier_signedNormBall_subset (S : Set {w : InfinitePlace K // w.IsReal})
    (σ : S → ℤˣ) : frontier (signedNormBall S σ) ⊆ frontier (normLeOne K) := by
  intro x hx
  rcases frontier_inter_subset (normLeOne K) (signRegion S σ) hx with ⟨h, -⟩ | ⟨hcl, hfr⟩
  · exact h
  · -- a frontier point of the sign region has some coordinate `0`, so norm `0`
    refine ⟨hcl, fun hint => ?_⟩
    have hxY : x ∈ normLeOne K := interior_subset hint
    have hnotin : x ∉ signRegion S σ := by
      rw [(isOpen_signRegion S σ).frontier_eq] at hfr
      exact hfr.2
    simp only [signRegion, mem_setOf_eq, not_forall, not_lt] at hnotin
    obtain ⟨w, hw⟩ := hnotin
    have hle : 0 ≤ ((σ w : ℤ) : ℝ) * x.1 w := by
      have hclos : closure (signRegion S σ) ⊆ {y : mixedSpace K | 0 ≤ ((σ w : ℤ) : ℝ) * y.1 w} :=
        closure_minimal (fun y hy => (hy w).le) (isClosed_le continuous_const
          (continuous_const.mul ((continuous_apply _).comp continuous_fst)))
      exact hclos (frontier_subset_closure hfr)
    have hzero : x.1 w = 0 := by
      have hσ : ((σ w : ℤ) : ℝ) ≠ 0 := by
        rcases Int.units_eq_one_or (σ w) with h | h <;> simp [h]
      have := le_antisymm hw hle
      exact (mul_eq_zero.mp this).resolve_left hσ
    have hpos := normAtPlace_pos_of_mem hxY.1 w.1.1
    rw [normAtPlace_apply_of_isReal w.1.2] at hpos
    exact (ne_of_gt hpos) (by simp [hzero])

theorem negAt_mem_normLeOne_iff (T : Set {w : InfinitePlace K // w.IsReal}) (x : mixedSpace K) :
    negAt T x ∈ normLeOne K ↔ x ∈ normLeOne K := by
  have hlog : logMap (negAt T x) = logMap x := by
    ext w
    simp only [logMap_apply, normAtPlace_negAt, norm_negAt]
  simp only [mem_normLeOne, norm_negAt]
  rw [show negAt T x ∈ fundamentalCone K ↔ x ∈ fundamentalCone K by
    simp only [fundamentalCone, mem_sdiff, mem_preimage, hlog, mem_setOf_eq, norm_negAt]]

/-- **The volume of a signed norm ball does not depend on the signs**. -/
theorem measureReal_signedNormBall_eq (S : Set {w : InfinitePlace K // w.IsReal})
    (σ σ' : S → ℤˣ) :
    volume.real (signedNormBall S σ) = volume.real (signedNormBall S σ') := by
  -- flip the coordinates where the signs differ
  set T : Set {w : InfinitePlace K // w.IsReal} := {w | ∃ hw : w ∈ S, σ ⟨w, hw⟩ ≠ σ' ⟨w, hw⟩}
  have hpre : negAt T ⁻¹' signedNormBall S σ = signedNormBall S σ' := by
    ext x
    show (negAt T x ∈ normLeOne K ∧ negAt T x ∈ signRegion S σ) ↔
      (x ∈ normLeOne K ∧ x ∈ signRegion S σ')
    rw [negAt_mem_normLeOne_iff]
    refine and_congr_right fun _ => ?_
    simp only [signRegion, mem_setOf_eq]
    refine forall_congr' fun w => ?_
    by_cases hw : w.1 ∈ T
    · rw [negAt_apply_isReal_and_mem _ hw]
      obtain ⟨hwS, hne⟩ : ∃ hw : w.1 ∈ S, σ ⟨w.1, hw⟩ ≠ σ' ⟨w.1, hw⟩ := hw
      have hne' : σ w ≠ σ' w := hne
      have hσ : σ' w = -σ w := by
        rcases Int.units_eq_one_or (σ w) with h | h <;>
          rcases Int.units_eq_one_or (σ' w) with h' | h' <;> simp_all [eq_comm]
      rw [hσ]
      constructor <;> intro h <;> push_cast at h ⊢ <;> linarith
    · rw [negAt_apply_isReal_and_notMem _ hw]
      have hσ : σ w = σ' w := by
        by_contra hne
        exact hw ⟨w.2, hne⟩
      rw [hσ]
  have hmeas : MeasurableSet (signedNormBall S σ) :=
    (measurableSet_normLeOne K).inter (isOpen_signRegion S σ).measurableSet
  rw [← hpre, measureReal_def, measureReal_def,
    (volume_preserving_negAt (s := T)).measure_preimage hmeas.nullMeasurableSet]

/-- **Lattice cosets in signed norm balls**: uniformly in the translation `v`,
`|#((v + T^{1/n} Y_σ) ∩ Λ) covol(Λ) − T vol(Y_σ)| ≤ C T^{1−1/n}` for `T ≥ 1`. -/
theorem exists_abs_ncard_vadd_signedNormBall_sub_le (Λ : Submodule ℤ (mixedSpace K))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (S : Set {w : InfinitePlace K // w.IsReal})
    (σ : S → ℤˣ) :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T → ∀ v : mixedSpace K,
      |(((v +ᵥ (T ^ ((finrank ℚ K : ℝ)⁻¹)) • signedNormBall S σ) ∩
          (Λ : Set (mixedSpace K))).ncard : ℝ) * ZLattice.covolume Λ volume -
        T * volume.real (signedNormBall S σ)| ≤ C * T ^ (1 - (finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨M, hM⟩ := exists_lipschitzOnWith_boundaryParam (K := K)
  have hbdd : IsBounded (signedNormBall S σ) := (isBounded_normLeOne K).subset inter_subset_left
  obtain ⟨C, hC⟩ := exists_abs_ncard_vadd_smul_sub_le (volume : Measure (mixedSpace K)) Λ
    (card_paramIndex K)
    (φ := fun j : ({w : InfinitePlace K // w.IsReal} → Bool) × paramIndex K × Bool =>
      boundaryParam j.1) (fun j => hM j.1) (fun j => j.2.1)
    (c := fun j => if j.2.2 then 1 else 0) (fun j => by split_ifs <;> simp) hbdd
    ((frontier_signedNormBall_subset S σ).trans (frontier_normLeOne_subset (K := K)))
  refine ⟨C, fun T hT v => ?_⟩
  have hn : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have hn1 : (1 : ℕ) ≤ finrank ℚ K := finrank_pos
  have hT0 : 0 < T := by linarith
  have ht1 : 1 ≤ T ^ ((finrank ℚ K : ℝ)⁻¹) := Real.one_le_rpow hT (by positivity)
  have h := hC _ ht1 v
  have hdim : finrank ℝ (mixedSpace K) = finrank ℚ K := mixedEmbedding.finrank K
  have htn : (T ^ ((finrank ℚ K : ℝ)⁻¹)) ^ finrank ℚ K = T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le, inv_mul_cancel₀ hn.ne', Real.rpow_one]
  have htn1 : (T ^ ((finrank ℚ K : ℝ)⁻¹)) ^ (finrank ℚ K - 1) = T ^ (1 - (finrank ℚ K : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le, Nat.cast_sub hn1, Nat.cast_one,
      show ((finrank ℚ K : ℝ))⁻¹ * ((finrank ℚ K : ℝ) - 1) = 1 - (finrank ℚ K : ℝ)⁻¹ by field_simp]
  rwa [hdim, htn, htn1] at h

end Signed

end GaloisForLFunctions.HeckeLFunctions

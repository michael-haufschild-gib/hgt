import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid
import GaloisForLFunctions.HTGeometry.GateCodebookDivergence

/-!
# Curve codebooks

A deterministic encoder with countable codomain and Borel fibres pushes a probability measure
forward to a genuine probability law on words, which is what the gate-cost decomposition consumes.

For a Lipschitz curve on a window, a mesh of spacing `delta / v` produces a codebook of at most
`⌈vW/delta⌉ + 1` shortest words which reproduces every point of the curve within `eps + delta`,
and every selected word is at least as long as the robust complexity at the wider radius.
-/

open scoped BigOperators Classical
open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Pushforward

variable {X : Type*} [MeasurableSpace X]

/-- **The word law of a deterministic encoder is a probability law.** -/
theorem hasSum_encoderLaw (mu : Measure X) [IsProbabilityMeasure mu]
    {beta : Type*} [Countable beta] (f : X → beta)
    (hf : ∀ b, MeasurableSet (f ⁻¹' {b})) :
    HasSum (fun b => mu.real (f ⁻¹' {b})) 1 := by
  classical
  have hdisj : Pairwise (Function.onFun Disjoint fun b => f ⁻¹' {b}) := by
    intro b₁ b₂ hb
    refine Set.disjoint_left.mpr fun x hx₁ hx₂ => hb ?_
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx₁ hx₂
    rw [← hx₁, ← hx₂]
  have hcover : (⋃ b, f ⁻¹' {b}) = Set.univ := by
    ext x
    simp
  have hmeas : mu (⋃ b, f ⁻¹' {b}) = ∑' b, mu (f ⁻¹' {b}) :=
    measure_iUnion hdisj hf
  rw [hcover, measure_univ] at hmeas
  have hne : ∀ b, mu (f ⁻¹' {b}) ≠ ⊤ := fun b => measure_ne_top mu _
  have hsummable : Summable (fun b => mu.real (f ⁻¹' {b})) := by
    apply ENNReal.summable_toReal
    rw [← hmeas]
    exact ENNReal.one_ne_top
  have hval : (∑' b, mu.real (f ⁻¹' {b})) = 1 := by
    simp only [measureReal_def]
    rw [← ENNReal.tsum_toReal_eq hne, ← hmeas]
    simp
  exact hval ▸ hsummable.hasSum

end Pushforward

section Codebook

variable {Γ : Type*} [Encodable Γ]
variable {X : Type*} [MetricSpace X]

/-- **`(19)`--`(20)`, the curve codebook.**  A Lipschitz curve on a window is reproduced within
`eps + delta` by finitely many shortest words, one per mesh point of spacing `delta / v`. -/
theorem exists_curve_codebook (endpoint : List Γ → X) (gamma : ℝ → X)
    {v W eps delta : ℝ} (hv : 0 < v) (hdelta : 0 < delta)
    (hlip : ∀ s t : ℝ, dist (gamma s) (gamma t) ≤ v * |s - t|)
    (hfin : ∀ t ∈ Set.Icc (0 : ℝ) W, ∃ w, Qualifies endpoint eps (gamma t) w) :
    ∃ (code : ℝ → List Γ) (s : Finset (List Γ)),
      s.card ≤ plateauGridCount W (delta / v) ∧
      (∀ w : List Γ, MeasurableSet (code ⁻¹' {w})) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) W, code t ∈ s) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) W, dist (endpoint (code t)) (gamma t) ≤ eps + delta) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) W,
        wordComplexity endpoint (eps + delta) (gamma t) ≤ (code t).length) := by
  classical
  set mesh : ℝ := delta / v with hmeshdef
  have hmesh : 0 < mesh := div_pos hdelta hv
  set N : ℕ := plateauGridCount W mesh with hNdef
  set grid : ℕ → ℝ := fun j => plateauGridPoint 0 mesh j with hgriddef
  set idx : ℝ → ℕ := fun t => ⌊t / mesh⌋₊ with hidxdef
  set code : ℝ → List Γ := fun t => firstQualifying endpoint eps (gamma (grid (idx t))) with hcode
  have hgridmem : ∀ t ∈ Set.Icc (0 : ℝ) W, grid (idx t) ∈ Set.Icc (0 : ℝ) W ∧
      |t - grid (idx t)| ≤ mesh ∧ idx t < N := by
    intro t ht
    obtain ⟨ht0, htW⟩ := ht
    have hnn : (0 : ℝ) ≤ t / mesh := div_nonneg ht0 hmesh.le
    have hfloor_le : ((idx t : ℕ) : ℝ) ≤ t / mesh := Nat.floor_le hnn
    have hlt : t / mesh < ((idx t : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hlow : ((idx t : ℕ) : ℝ) * mesh ≤ t := by
      rw [← le_div_iff₀ hmesh]; exact hfloor_le
    have hhigh : t < (((idx t : ℕ) : ℝ) + 1) * mesh := by
      rw [← div_lt_iff₀ hmesh]; exact hlt
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [hgriddef, plateauGridPoint, zero_add]
      positivity
    · simp only [hgriddef, plateauGridPoint, zero_add]
      linarith
    · simp only [hgriddef, plateauGridPoint, zero_add]
      rw [abs_le]
      constructor <;> linarith
    · have hWmesh : t / mesh ≤ W / mesh := by gcongr
      have hle : idx t ≤ ⌈W / mesh⌉₊ :=
        le_trans (Nat.floor_le_floor hWmesh) (Nat.floor_le_ceil _)
      simp only [hNdef, plateauGridCount]
      omega
  refine ⟨code, (Finset.range N).image (fun j => firstQualifying endpoint eps (gamma (grid j))),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (Finset.card_image_le) (by simp)
  · intro w
    have hidxmeas : Measurable idx := by
      rw [hidxdef]
      exact Nat.measurable_floor.comp (measurable_id.div_const mesh)
    have hpre : code ⁻¹' {w}
        = idx ⁻¹' ((fun j : ℕ => firstQualifying endpoint eps (gamma (grid j))) ⁻¹' {w}) := rfl
    rw [hpre]
    exact hidxmeas (MeasurableSpace.measurableSet_top)
  · intro t ht
    obtain ⟨_, _, hlt⟩ := hgridmem t ht
    exact Finset.mem_image.mpr ⟨idx t, Finset.mem_range.mpr hlt, rfl⟩
  · intro t ht
    obtain ⟨hmem, hnear, _⟩ := hgridmem t ht
    have hq := hfin _ hmem
    have hcodeq : dist (endpoint (code t)) (gamma (grid (idx t))) ≤ eps :=
      firstQualifying_qualifies hq
    calc
      dist (endpoint (code t)) (gamma t) ≤
          dist (endpoint (code t)) (gamma (grid (idx t))) +
            dist (gamma (grid (idx t))) (gamma t) := dist_triangle _ _ _
      _ ≤ eps + v * |grid (idx t) - t| := by
          exact add_le_add hcodeq (hlip _ _)
      _ ≤ eps + delta := by
          have habs : |grid (idx t) - t| ≤ mesh := by
            rw [abs_sub_comm]; exact hnear
          have : v * |grid (idx t) - t| ≤ v * mesh := by
            exact mul_le_mul_of_nonneg_left habs hv.le
          rw [hmeshdef] at this
          rw [mul_div_cancel₀ _ (ne_of_gt hv)] at this
          linarith
  · intro t ht
    obtain ⟨hmem, hnear, _⟩ := hgridmem t ht
    have hq := hfin _ hmem
    have hcodeq : dist (endpoint (code t)) (gamma (grid (idx t))) ≤ eps :=
      firstQualifying_qualifies hq
    have hreach : dist (endpoint (code t)) (gamma t) ≤ eps + delta := by
      calc
        dist (endpoint (code t)) (gamma t) ≤
            dist (endpoint (code t)) (gamma (grid (idx t))) +
              dist (gamma (grid (idx t))) (gamma t) := dist_triangle _ _ _
        _ ≤ eps + v * |grid (idx t) - t| := add_le_add hcodeq (hlip _ _)
        _ ≤ eps + delta := by
            have habs : |grid (idx t) - t| ≤ mesh := by
              rw [abs_sub_comm]; exact hnear
            have hmul : v * |grid (idx t) - t| ≤ v * mesh :=
              mul_le_mul_of_nonneg_left habs hv.le
            rw [hmeshdef, mul_div_cancel₀ _ (ne_of_gt hv)] at hmul
            linarith
    exact Nat.sInf_le ⟨code t, rfl, hreach⟩

end Codebook

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.AnalyticGermDomain
import GaloisForLFunctions.HTGeometry.GermSliceAdmissible
import GaloisForLFunctions.HTGeometry.SliceRootCount
import GaloisForLFunctions.HTGeometry.SliceWeierstrassFactorization

/-!
# The zero set of a vanishing regular germ surjects onto the parameters

If a holomorphic function vanishes at a point and its slice in the distinguished coordinate is not
identically zero there, then the slice over *every* nearby parameter value also has a zero, and the
zero can be taken inside any prescribed neighbourhood of the original point.

This is the projection statement behind the analytic half of the propagation of coprimality: a
non-unit divisor of a germ produces, over every nearby parameter, an actual common zero of the two
functions it divides.  The proof is the root count of the slice: it is locally constant in the
parameters (`HTGeometry.card_sliceRoots_const_of_isPreconnected`), it is at least one at the original
parameter because the function vanishes there, hence it is at least one nearby, and the roots lie
strictly inside the admissible circle.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric

variable {n : ℕ}

/-- **Zeros over every nearby parameter, at the origin.** -/
theorem eventually_exists_slice_zero_zero {f : (Fin (n + 1) → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f (0 : Fin (n + 1) → ℂ)) (hf0 : f (0 : Fin (n + 1) → ℂ) = 0)
    (hreg : ¬ (fun z : ℂ => f (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0)
    {W : Set (Fin (n + 1) → ℂ)} (hW : W ∈ 𝓝 (0 : Fin (n + 1) → ℂ)) :
    ∀ᶠ y in 𝓝 (0 : Fin n → ℂ),
      ∃ z : ℂ, (Fin.cons z y : Fin (n + 1) → ℂ) ∈ W ∧ f (Fin.cons z y) = 0 := by
  classical
  obtain ⟨ρ, hρ, hρW⟩ := Metric.mem_nhds_iff.mp hW
  obtain ⟨r, hr, hfr⟩ := exists_ball_analyticOnNhd hf
  set R : ℝ := min ρ r with hR
  have hRpos : 0 < R := lt_min hρ hr
  set U : Set (Fin (n + 1) → ℂ) := ball (0 : Fin (n + 1) → ℂ) R with hU
  have hUopen : IsOpen U := isOpen_ball
  have h0U : (0 : Fin (n + 1) → ℂ) ∈ U := mem_ball_self hRpos
  have hUW : U ⊆ W := fun w hw => hρW (ball_subset_ball (min_le_left _ _) hw)
  have hUr : U ⊆ ball (0 : Fin (n + 1) → ℂ) r := ball_subset_ball (min_le_right _ _)
  have hfd : DifferentiableOn ℂ f U :=
    (hfr.mono hUr).differentiableOn
  obtain ⟨t, δ, htpos, hδpos, -, hdisc, hnez, hadm, -⟩ :=
    HTGeometry.exists_sliceAdmissible_nhds hUopen h0U hfd hreg
  set V : Set (Fin n → ℂ) := ball (0 : Fin n → ℂ) δ with hV
  have hVopen : IsOpen V := isOpen_ball
  have hVconn : IsPreconnected V := (convex_ball (0 : Fin n → ℂ) δ).isPreconnected
  have h0V : (0 : Fin n → ℂ) ∈ V := mem_ball_self hδpos
  have hcons0 : (Fin.cons (0 : ℂ) (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) = 0 := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp
  have hmem0 : (0 : ℂ) ∈ HTGeometry.sliceRoots f t (0 : Fin n → ℂ) := by
    refine (HTGeometry.slice_eq_zero_iff_mem_sliceRoots htpos (hadm _ h0V) (by simpa using htpos)).mp ?_
    rw [hcons0]
    exact hf0
  have hcard0 : 0 < (HTGeometry.sliceRoots f t (0 : Fin n → ℂ)).card :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨0, hmem0⟩
  have hVmem : V ∈ 𝓝 (0 : Fin n → ℂ) := hVopen.mem_nhds h0V
  filter_upwards [hVmem] with y hy
  have hcard : (HTGeometry.sliceRoots f t (0 : Fin n → ℂ)).card = (HTGeometry.sliceRoots f t y).card :=
    HTGeometry.card_sliceRoots_const_of_isPreconnected hUopen hVopen hfd htpos hdisc hnez hadm hVconn h0V hy
  have hne : (HTGeometry.sliceRoots f t y) ≠ 0 := by
    intro h
    rw [h] at hcard
    simp only [Multiset.card_zero] at hcard
    omega
  obtain ⟨z, hz⟩ := Multiset.exists_mem_of_ne_zero hne
  have hznorm : ‖z‖ < t := HTGeometry.sliceRoots_norm_lt htpos (hadm y hy) z hz
  refine ⟨z, hUW (hdisc y hy z hznorm.le), ?_⟩
  exact (HTGeometry.slice_eq_zero_iff_mem_sliceRoots htpos (hadm y hy) hznorm).mpr hz

/-- Translating a split point: `Fin.cons z y + w₀ = Fin.cons (z + w₀ 0) (y + Fin.tail w₀)`. -/
theorem cons_add (z : ℂ) (y : Fin n → ℂ) (w₀ : Fin (n + 1) → ℂ) :
    (Fin.cons z y : Fin (n + 1) → ℂ) + w₀
      = (Fin.cons (z + w₀ 0) (y + Fin.tail w₀) : Fin (n + 1) → ℂ) := by
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ j => simp [Fin.tail]

/-- **Zeros over every nearby parameter, at an arbitrary point.** -/
theorem eventually_exists_slice_zero {f : (Fin (n + 1) → ℂ) → ℂ} {w₀ : Fin (n + 1) → ℂ}
    (hf : AnalyticAt ℂ f w₀) (hf0 : f w₀ = 0)
    (hreg : ¬ (fun z : ℂ => f (Fin.cons z (Fin.tail w₀))) =ᶠ[𝓝 (w₀ 0)] 0)
    {W : Set (Fin (n + 1) → ℂ)} (hW : W ∈ 𝓝 w₀) :
    ∀ᶠ y in 𝓝 (Fin.tail w₀),
      ∃ z : ℂ, (Fin.cons z y : Fin (n + 1) → ℂ) ∈ W ∧ f (Fin.cons z y) = 0 := by
  classical
  set F : (Fin (n + 1) → ℂ) → ℂ := fun w => f (w + w₀) with hF
  have hshift : AnalyticAt ℂ (fun w : Fin (n + 1) → ℂ => w + w₀) (0 : Fin (n + 1) → ℂ) := by
    have h := (analyticAt_id (𝕜 := ℂ) (z := (0 : Fin (n + 1) → ℂ))).add
      (analyticAt_const (v := w₀))
    rw [Pi.add_def] at h
    exact h
  have hFA : AnalyticAt ℂ F (0 : Fin (n + 1) → ℂ) := by
    refine AnalyticAt.comp ?_ hshift
    simpa using hf
  have hF0 : F (0 : Fin (n + 1) → ℂ) = 0 := by
    rw [hF]
    simpa using hf0
  have hFreg : ¬ (fun z : ℂ => F (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0 := by
    intro hcon
    refine hreg ?_
    have hmap : Filter.Tendsto (fun z : ℂ => z - w₀ 0) (𝓝 (w₀ 0)) (𝓝 (0 : ℂ)) := by
      have hc := (Filter.tendsto_id (x := 𝓝 (w₀ 0))).sub
        (tendsto_const_nhds (x := w₀ 0) (f := 𝓝 (w₀ 0)))
      rwa [sub_self] at hc
    filter_upwards [hmap.eventually hcon] with z hz
    have hcons : (Fin.cons (z - w₀ 0) (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) + w₀
        = (Fin.cons z (Fin.tail w₀) : Fin (n + 1) → ℂ) := by
      rw [cons_add]
      congr 1
      · ring
      · simp
    have hz' : F (Fin.cons (z - w₀ 0) (0 : Fin n → ℂ)) = 0 := hz
    rw [hF] at hz'
    simp only at hz'
    rw [hcons] at hz'
    exact hz'
  set W' : Set (Fin (n + 1) → ℂ) := (fun w : Fin (n + 1) → ℂ => w + w₀) ⁻¹' W with hW'
  have hW'mem : W' ∈ 𝓝 (0 : Fin (n + 1) → ℂ) := by
    refine ContinuousAt.preimage_mem_nhds ?_ (by simpa using hW)
    exact (continuous_id.add continuous_const).continuousAt
  have hmain := eventually_exists_slice_zero_zero hFA hF0 hFreg hW'mem
  have htend : Filter.Tendsto (fun y : Fin n → ℂ => y - Fin.tail w₀)
      (𝓝 (Fin.tail w₀)) (𝓝 (0 : Fin n → ℂ)) := by
    have hc := (Filter.tendsto_id (x := 𝓝 (Fin.tail w₀))).sub
      (tendsto_const_nhds (x := Fin.tail w₀) (f := 𝓝 (Fin.tail w₀)))
    rwa [sub_self] at hc
  filter_upwards [htend.eventually hmain] with y hy
  obtain ⟨z, hzW, hzzero⟩ := hy
  refine ⟨z + w₀ 0, ?_, ?_⟩
  · have hcons : (Fin.cons z (y - Fin.tail w₀) : Fin (n + 1) → ℂ) + w₀
        = (Fin.cons (z + w₀ 0) y : Fin (n + 1) → ℂ) := by
      rw [cons_add]
      congr 1
      simp
    have := hzW
    rw [hW', Set.mem_preimage, hcons] at this
    exact this
  · have hcons : (Fin.cons z (y - Fin.tail w₀) : Fin (n + 1) → ℂ) + w₀
        = (Fin.cons (z + w₀ 0) y : Fin (n + 1) → ℂ) := by
      rw [cons_add]
      congr 1
      simp
    have hz' : F (Fin.cons z (y - Fin.tail w₀)) = 0 := hzzero
    rw [hF] at hz'
    simp only at hz'
    rw [hcons] at hz'
    exact hz'

end GaloisForLFunctions.HTGeometry

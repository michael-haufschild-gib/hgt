import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare

/-!
# Uniform separation of a finite maximal exponential packet

A cofinally neutral countable mode family with one superunit mode has a finite maximal packet.
This strengthens maximal-radius extraction by placing every complementary mode below one common
strictly smaller radius.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- **Uniform finite maximal-packet separation.** -/
theorem exists_finite_maximal_norm_packet_uniformly_separated
    {ι : Type*} (b : ι → ℂ)
    (hb : Tendsto b cofinite (nhds 1)) {i0 : ι} (hi0 : 1 < ‖b i0‖) :
    ∃ D : Finset ι, ∃ r beta : ℝ,
      1 < r ∧ beta < r ∧ D.Nonempty ∧
        (∀ i ∈ D, ‖b i‖ = r) ∧ (∀ i ∉ D, ‖b i‖ ≤ beta) := by
  classical
  obtain ⟨D, r, hr, hDne, hD, hDsub⟩ :=
    exists_finite_maximal_norm_packet_of_tendsto_cofinite_one b hb hi0
  let a : ℝ := (1 + r) / 2
  have ha1 : 1 < a := by dsimp only [a]; linarith
  have har : a < r := by dsimp only [a]; linarith
  have hev : ∀ᶠ i : ι in cofinite, b i ∈ Metric.ball (1 : ℂ) (a - 1) :=
    hb (Metric.ball_mem_nhds _ (sub_pos.mpr ha1))
  have hbad : {i : ι | b i ∉ Metric.ball (1 : ℂ) (a - 1)}.Finite := by
    have hfin := Filter.mem_cofinite.mp (Filter.eventually_iff.mp hev)
    simpa only [Set.compl_setOf] using hfin
  have hsuper : {i : ι | a ≤ ‖b i‖}.Finite := by
    apply hbad.subset
    intro i hi hball
    change a ≤ ‖b i‖ at hi
    have hdist : ‖b i - 1‖ < a - 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hball
    have htri : ‖b i‖ ≤ ‖b i - 1‖ + 1 := by
      calc
        ‖b i‖ = ‖(b i - 1) + 1‖ := by ring_nf
        _ ≤ ‖b i - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖b i - 1‖ + 1 := by norm_num
    linarith
  let S : Finset ι := hsuper.toFinset
  let T : Finset ι := S.filter (fun i => i ∉ D)
  by_cases hT : T.Nonempty
  · obtain ⟨q, hqT, hqmax⟩ := Finset.exists_max_image T (fun i => ‖b i‖) hT
    let beta : ℝ := max a ‖b q‖
    have hqnotD : q ∉ D := (Finset.mem_filter.mp hqT).2
    have hqr : ‖b q‖ < r := hDsub q hqnotD
    have hbetar : beta < r := max_lt har hqr
    refine ⟨D, r, beta, hr, hbetar, hDne, hD, ?_⟩
    intro i hiD
    by_cases hiS : i ∈ S
    · have hiT : i ∈ T := Finset.mem_filter.mpr ⟨hiS, hiD⟩
      exact (hqmax i hiT).trans (le_max_right _ _)
    · have hia : ‖b i‖ < a := by
        apply lt_of_not_ge
        intro hai
        apply hiS
        simpa only [S, Set.Finite.mem_toFinset] using hai
      exact hia.le.trans (le_max_left _ _)
  · have hbound : ∀ i ∉ D, ‖b i‖ ≤ a := by
      intro i hiD
      have hiS : i ∉ S := by
        intro hiS
        exact hT ⟨i, Finset.mem_filter.mpr ⟨hiS, hiD⟩⟩
      have hia : ‖b i‖ < a := by
        apply lt_of_not_ge
        intro hai
        apply hiS
        simpa only [S, Set.Finite.mem_toFinset] using hai
      exact hia.le
    exact ⟨D, r, a, hr, har, hDne, hD, hbound⟩

end


end RHTower

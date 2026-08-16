import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Volume packing forces a close pair

Finitely many points of a ball whose mutual distances are all at least `δ` carry disjoint open
balls of radius `δ/2` inside a slightly larger ball, so their number is bounded by the ratio of
volumes.  Reading the bound backwards, a set of `N` points of the ball of radius `ρ` always has two
distinct points at distance at most `2ρ/(N^{1/d}-1)`, where `d` is the dimension.

This is the deterministic observer-compression mechanism: exponentially many observed vectors in a
bounded region of a low-dimensional observer space must crowd.
-/

open MeasureTheory Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- **Volume packing bound.**  A `δ`-separated finite subset of the ball of radius `ρ` has at most
`((ρ + δ/2)/(δ/2))^d` elements. -/
theorem card_mul_pow_le_of_separated (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Finset E) (ρ δ : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hball : ∀ x ∈ S, ‖x‖ ≤ ρ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ ‖x - y‖) :
    (S.card : ℝ) * (δ / 2) ^ (Module.finrank ℝ E) ≤ (ρ + δ / 2) ^ (Module.finrank ℝ E) := by
  classical
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  have hdisj : (↑S : Set E).PairwiseDisjoint fun x => ball x (δ / 2) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.mpr fun z hz hz' => ?_
    have h1 : dist x z < δ / 2 := by
      rw [dist_comm]
      exact mem_ball.mp hz
    have h2 : dist z y < δ / 2 := mem_ball.mp hz'
    have h3 : dist x y < δ := by
      have := dist_triangle x z y
      linarith
    have h4 := hsep x hx y hy hxy
    rw [← dist_eq_norm] at h4
    linarith
  have hsub : (⋃ x ∈ S, ball x (δ / 2)) ⊆ ball 0 (ρ + δ / 2) := by
    intro z hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    rw [mem_ball, dist_zero_right]
    have h1 : ‖z - x‖ < δ / 2 := by
      rw [← dist_eq_norm]
      exact mem_ball.mp hzx
    have h2 : ‖x‖ ≤ ρ := hball x hx
    calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ < δ / 2 + ρ := by linarith
      _ = ρ + δ / 2 := by ring
  have hmeas := measure_biUnion_finset (μ := μ) hdisj
    (fun b _ => measurableSet_ball)
  have hle : ∑ x ∈ S, μ (ball x (δ / 2)) ≤ μ (ball 0 (ρ + δ / 2)) := by
    rw [← hmeas]
    exact measure_mono hsub
  have hballval : ∀ x : E, μ (ball x (δ / 2)) =
      ENNReal.ofReal ((δ / 2) ^ (Module.finrank ℝ E)) * μ (ball 0 1) :=
    fun x => Measure.addHaar_ball μ x hhalf.le
  rw [Finset.sum_congr rfl fun x _ => hballval x, Finset.sum_const, nsmul_eq_mul,
    Measure.addHaar_ball μ (0 : E) (by linarith : (0:ℝ) ≤ ρ + δ / 2), ← mul_assoc] at hle
  have hpos : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hfin : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hcancel := (ENNReal.mul_le_mul_iff_left hpos hfin).mp hle
  have hcast : ((S.card : ENNReal)) * ENNReal.ofReal ((δ / 2) ^ (Module.finrank ℝ E)) =
      ENNReal.ofReal ((S.card : ℝ) * (δ / 2) ^ (Module.finrank ℝ E)) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp
  rw [hcast] at hcancel
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcancel

/-- **Deterministic observer compression.**  Any finite set of more than one point inside the ball
of radius `ρ` has two distinct points whose distance is at most `2ρ/(N^{1/d}-1)`, in the
division-free form. -/
theorem exists_pair_norm_sub_mul_le (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Finset E) (ρ : ℝ) (hρ : 0 ≤ ρ) (hcard : 1 < S.card)
    (hball : ∀ x ∈ S, ‖x‖ ≤ ρ) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧
      ((S.card : ℝ) ^ ((Module.finrank ℝ E : ℝ)⁻¹) - 1) * ‖x - y‖ ≤ 2 * ρ := by
  classical
  set d := Module.finrank ℝ E with hd
  have hdpos : 0 < d := Module.finrank_pos
  set T := (S ×ˢ S).filter fun z : E × E => z.1 ≠ z.2 with hT
  have hTne : T.Nonempty := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
    exact ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩⟩
  obtain ⟨z, hzT, hzmin⟩ := T.exists_min_image (fun w : E × E => ‖w.1 - w.2‖) hTne
  rw [hT, Finset.mem_filter, Finset.mem_product] at hzT
  set δ := ‖z.1 - z.2‖ with hδ
  have hδpos : 0 < δ := by
    rw [hδ, norm_pos_iff, sub_ne_zero]
    exact hzT.2
  have hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    exact hzmin (x, y) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩)
  have hpack := card_mul_pow_le_of_separated μ S ρ δ hρ hδpos hball hsep
  have hroot : ((S.card : ℝ) ^ ((d : ℝ)⁻¹)) ^ d = (S.card : ℝ) := by
    rw [← Real.rpow_natCast ((S.card : ℝ) ^ ((d : ℝ)⁻¹)) d, ← Real.rpow_mul (by positivity),
      inv_mul_cancel₀ (by exact_mod_cast hdpos.ne'), Real.rpow_one]
  have hkey : (((S.card : ℝ) ^ ((d : ℝ)⁻¹)) * (δ / 2)) ^ d ≤ (ρ + δ / 2) ^ d := by
    rw [mul_pow, hroot]
    exact hpack
  have hrootpos : (0 : ℝ) ≤ (S.card : ℝ) ^ ((d : ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
  have hlin : ((S.card : ℝ) ^ ((d : ℝ)⁻¹)) * (δ / 2) ≤ ρ + δ / 2 := by
    refine le_of_pow_le_pow_left₀ hdpos.ne' (by linarith) hkey
  exact ⟨z.1, hzT.1.1, z.2, hzT.1.2, hzT.2, by nlinarith [hlin]⟩


/-- **A maximal separated subset of a ball is a net.**  For every radius and every scale there is a
finite subset of the ball obeying the packing bound whose `ε`-balls already cover the ball. -/
theorem exists_finset_net (μ : Measure E) [μ.IsAddHaarMeasure] (R ε : ℝ) (hR : 0 ≤ R)
    (hε : 0 < ε) :
    ∃ T : Finset E, T.Nonempty ∧ (∀ x ∈ T, ‖x‖ ≤ R) ∧
      (∀ x : E, ‖x‖ ≤ R → ∃ t ∈ T, ‖x - t‖ < ε) ∧
      (T.card : ℝ) * (ε / 2) ^ (Module.finrank ℝ E) ≤ (R + ε / 2) ^ (Module.finrank ℝ E) := by
  classical
  set d := Module.finrank ℝ E with hd
  set 𝒮 : Set ℕ := {n | ∃ T : Finset E, (∀ x ∈ T, ‖x‖ ≤ R) ∧
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ε ≤ ‖x - y‖) ∧ T.card = n} with h𝒮
  have hne : 𝒮.Nonempty := ⟨0, ∅, by simp, by simp, by simp⟩
  have hbdd : BddAbove 𝒮 := by
    refine ⟨⌈(R + ε / 2) ^ d / (ε / 2) ^ d⌉₊, ?_⟩
    rintro n ⟨T, hT1, hT2, rfl⟩
    have hpack := card_mul_pow_le_of_separated μ T R ε hR hε hT1 hT2
    have hpos : (0 : ℝ) < (ε / 2) ^ d := by positivity
    have hle : (T.card : ℝ) ≤ (R + ε / 2) ^ d / (ε / 2) ^ d := by
      rw [le_div_iff₀ hpos]
      exact hpack
    have := hle.trans (Nat.le_ceil _)
    exact_mod_cast this
  obtain ⟨T, hT1, hT2, hTcard⟩ := Nat.sSup_mem hne hbdd
  have hcover : ∀ x : E, ‖x‖ ≤ R → ∃ t ∈ T, ‖x - t‖ < ε := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have hxT : x ∉ T := by
      intro h
      have hxx := hcon x h
      rw [sub_self, norm_zero] at hxx
      linarith
    have hins : (insert x T).card = T.card + 1 := Finset.card_insert_of_notMem hxT
    have hmem : (insert x T).card ∈ 𝒮 := by
      refine ⟨insert x T, ?_, ?_, rfl⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hx
        · exact hT1 y hy
      · intro y hy z hz hyz
        rcases Finset.mem_insert.mp hy with hy1 | hy1
        · subst hy1
          rcases Finset.mem_insert.mp hz with hz1 | hz1
          · exact absurd hz1.symm hyz
          · exact hcon z hz1
        · rcases Finset.mem_insert.mp hz with hz1 | hz1
          · subst hz1
            rw [← norm_neg, neg_sub]
            exact hcon y hy1
          · exact hT2 y hy1 z hz1 hyz
    have hle := le_csSup hbdd hmem
    omega
  refine ⟨T, ?_, hT1, hcover, card_mul_pow_le_of_separated μ T R ε hR hε hT1 hT2⟩
  obtain ⟨t, ht, -⟩ := hcover 0 (by simpa using hR)
  exact ⟨t, ht⟩

section ReplicaActions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The observed action vector of a replica multiplicity vector. -/
def replicaObservedAction (v : ι → E) (p : ι → ℕ) : E := ∑ j, (p j : ℝ) • v j

theorem norm_replicaObservedAction_le {v : ι → E} {L : ℝ} (hL : ∀ j, ‖v j‖ ≤ L)
    {r : ℕ} {p : ι → ℕ} (hp : p ∈ (Finset.univ.piAntidiag r : Finset (ι → ℕ))) :
    ‖replicaObservedAction v p‖ ≤ r * L := by
  classical
  have hsum : ∑ j, p j = r := by
    have h := (Finset.mem_piAntidiag.mp hp).1
    simpa using h
  calc ‖replicaObservedAction v p‖ ≤ ∑ j, ‖(p j : ℝ) • v j‖ := norm_sum_le _ _
    _ = ∑ j, (p j : ℝ) * ‖v j‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_smul, Real.norm_natCast]
    _ ≤ ∑ j, (p j : ℝ) * L :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hL j) (by positivity)
    _ = (∑ j, (p j : ℝ)) * L := by rw [Finset.sum_mul]
    _ = r * L := by
        rw [show (∑ j, (p j : ℝ)) = ((∑ j, p j : ℕ) : ℝ) by push_cast; ring, hsum]

/-- **Theorem A: observer-dimension crowding of replica actions.**  Among the multiplicity vectors
of replica order `r` there are two distinct ones whose observed action vectors are within
`2rL/(N^{1/d}-1)` of each other, where `N` is their number and `d` the observer dimension. -/
theorem exists_pair_replicaObservedAction_mul_le (μ : Measure E) [μ.IsAddHaarMeasure]
    (v : ι → E) (L : ℝ) (hL0 : 0 ≤ L) (hL : ∀ j, ‖v j‖ ≤ L) (r : ℕ)
    (hcard : 1 < (Finset.univ.piAntidiag r : Finset (ι → ℕ)).card) :
    ∃ p ∈ (Finset.univ.piAntidiag r : Finset (ι → ℕ)),
      ∃ q ∈ (Finset.univ.piAntidiag r : Finset (ι → ℕ)), p ≠ q ∧
        (((Finset.univ.piAntidiag r : Finset (ι → ℕ)).card : ℝ) ^
              ((Module.finrank ℝ E : ℝ)⁻¹) - 1) *
            ‖replicaObservedAction v p - replicaObservedAction v q‖ ≤ 2 * (r * L) := by
  classical
  set P := (Finset.univ.piAntidiag r : Finset (ι → ℕ)) with hP
  have hNpos : (0 : ℝ) < (P.card : ℝ) := by
    have : 0 < P.card := lt_trans Nat.zero_lt_one hcard
    exact_mod_cast this
  have hcoeff : (0 : ℝ) ≤ ((P.card : ℝ) ^ ((Module.finrank ℝ E : ℝ)⁻¹) - 1) := by
    have h1 : (1 : ℝ) ≤ (P.card : ℝ) := by
      have : 1 ≤ P.card := le_of_lt hcard
      exact_mod_cast this
    have := Real.one_le_rpow h1 (by positivity : (0:ℝ) ≤ ((Module.finrank ℝ E : ℝ)⁻¹))
    linarith
  by_cases hinj : Set.InjOn (replicaObservedAction v) (P : Set (ι → ℕ))
  · have hsimage : (P.image (replicaObservedAction v)).card = P.card :=
      Finset.card_image_of_injOn hinj
    have hballmem : ∀ x ∈ P.image (replicaObservedAction v), ‖x‖ ≤ r * L := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      exact norm_replicaObservedAction_le hL hp
    have hSc : 1 < (P.image (replicaObservedAction v)).card := by rw [hsimage]; exact hcard
    obtain ⟨x, hx, y, hy, hxy, hbound⟩ :=
      exists_pair_norm_sub_mul_le μ (P.image (replicaObservedAction v)) (r * L)
        (by positivity) hSc hballmem
    rw [hsimage] at hbound
    rw [Finset.mem_image] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    exact ⟨p, hp, q, hq, fun h => hxy (by rw [h]), hbound⟩
  · rw [Set.injOn_iff_injective] at hinj
    have hex : ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧
        replicaObservedAction v p = replicaObservedAction v q := by
      by_contra hcon
      push Not at hcon
      refine hinj fun a b hab => ?_
      by_contra hne
      exact hne (Subtype.ext (hcon a.1 a.2 b.1 b.2 (fun h => hne (Subtype.ext h)) hab).elim)
    obtain ⟨p, hp, q, hq, hpq, heq⟩ := hex
    refine ⟨p, hp, q, hq, hpq, ?_⟩
    rw [heq, sub_self, norm_zero, mul_zero]
    positivity

end ReplicaActions

end GaloisForLFunctions.HTGeometry

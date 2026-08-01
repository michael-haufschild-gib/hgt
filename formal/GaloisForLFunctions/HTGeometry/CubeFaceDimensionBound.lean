import GaloisForLFunctions.HTGeometry.PoincareMiranda
import GaloisForLFunctions.HTGeometry.LipschitzImageNonvalue

/-!
# Essential cube faces bound the dimension of the ambient space

Suppose a compact set `S` in a finite-dimensional normed space carries `r` pairs of disjoint compact
subsets, and a continuous map of the `r`-cube into `S` sends the two faces `x j = 0` and `x j = 1`
into the `j`-th pair.  Then `r` cannot exceed the dimension of the ambient space.

The two ingredients pull in opposite directions.  Signed distance functions to the pairs are
Lipschitz, so their joint image has Hausdorff dimension at most the dimension of the ambient space,
and a value arbitrarily close to the origin is omitted whenever `r` is larger.  Poincaré–Miranda
says the omitted value must be attained, since the sign conditions on the faces are exactly its
hypotheses.  The tension resolves only if `r` is at most the ambient dimension.
-/

open Metric Set

namespace GaloisForLFunctions

theorem le_finrank_of_cube_faces {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {r : ℕ} {A B : Fin r → Set E} {S : Set E}
    (hA : ∀ j, IsCompact (A j)) (hAne : ∀ j, (A j).Nonempty)
    (hB : ∀ j, IsCompact (B j)) (hBne : ∀ j, (B j).Nonempty)
    (hdisj : ∀ j, Disjoint (A j) (B j))
    {γ : EuclideanSpace ℝ (Fin r) → E} (hγ : ContinuousOn γ (unitCube r))
    (hγS : ∀ x ∈ unitCube r, γ x ∈ S)
    (hA0 : ∀ x ∈ unitCube r, ∀ j, x j = 0 → γ x ∈ A j)
    (hB1 : ∀ x ∈ unitCube r, ∀ j, x j = 1 → γ x ∈ B j) :
    r ≤ Module.finrank ℝ E := by
  classical
  by_contra hcon
  push Not at hcon
  have hrpos : 0 < r := lt_of_le_of_lt (Nat.zero_le _) hcon
  haveI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hrpos
  -- uniform separation of the pairs
  have hsep : ∀ j, ∃ δ : ℝ, 0 < δ ∧ (∀ y ∈ A j, δ ≤ infDist y (B j)) ∧
      (∀ y ∈ B j, δ ≤ infDist y (A j)) := by
    intro j
    obtain ⟨a, haA, hamin⟩ := (hA j).exists_isMinOn (hAne j)
      (continuous_infDist_pt (B j)).continuousOn
    obtain ⟨b, hbB, hbmin⟩ := (hB j).exists_isMinOn (hBne j)
      (continuous_infDist_pt (A j)).continuousOn
    have ha0 : 0 < infDist a (B j) := by
      rw [← (hB j).isClosed.notMem_iff_infDist_pos (hBne j)]
      intro hmem
      exact (Set.disjoint_left.mp (hdisj j) haA) hmem
    have hb0 : 0 < infDist b (A j) := by
      rw [← (hA j).isClosed.notMem_iff_infDist_pos (hAne j)]
      intro hmem
      exact (Set.disjoint_right.mp (hdisj j) hbB) hmem
    exact ⟨min (infDist a (B j)) (infDist b (A j)), lt_min ha0 hb0,
      fun y hy => le_trans (min_le_left _ _) (hamin hy),
      fun y hy => le_trans (min_le_right _ _) (hbmin hy)⟩
  choose δ hδpos hδA hδB using hsep
  set δ₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty δ with hδ₀def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def, Finset.lt_inf'_iff]
    exact fun j _ => hδpos j
  have hδ₀le : ∀ j, δ₀ ≤ δ j := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  -- the separating observables
  set u : Fin r → E → ℝ := fun j y => infDist y (A j) - infDist y (B j) with hudef
  have hulip : ∀ j, LipschitzWith 2 (u j) := by
    intro j
    have h := (lipschitz_infDist_pt (A j)).sub (lipschitz_infDist_pt (B j))
    have hc : (1 : NNReal) + 1 = 2 := by norm_num
    rw [hc] at h
    exact h
  obtain ⟨v, hvnorm, hvnot⟩ :=
    exists_norm_lt_notMem_lipschitz_pi_image hulip S hcon hδ₀pos
  have hvj : ∀ j, |v j| < δ₀ := by
    intro j
    have h1 : ‖v j‖ ≤ ‖v‖ := norm_le_pi_norm v j
    have := lt_of_le_of_lt h1 hvnorm
    rwa [Real.norm_eq_abs] at this
  -- the Poincaré–Miranda field
  set G : EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin r) :=
    fun x => WithLp.toLp 2 (fun j => u j (γ x) - v j) with hGdef
  have hGapply : ∀ x j, G x j = u j (γ x) - v j := fun x j => rfl
  have hGcont : ContinuousOn G (unitCube r) := by
    rw [hGdef]
    refine (PiLp.continuous_toLp 2 _).comp_continuousOn ?_
    refine continuousOn_pi.2 fun j => ?_
    exact (((hulip j).continuous).comp_continuousOn hγ).sub continuousOn_const
  have hneg : ∀ x ∈ unitCube r, ∀ j, x j = 0 → G x j ≤ 0 := by
    intro x hx j hxj
    have hmem : γ x ∈ A j := hA0 x hx j hxj
    have h1 : u j (γ x) = -infDist (γ x) (B j) := by
      rw [hudef]
      simp only
      rw [infDist_zero_of_mem hmem]
      ring
    have h2 : δ j ≤ infDist (γ x) (B j) := hδA j (γ x) hmem
    have h3 : |v j| < δ₀ := hvj j
    have h4 : δ₀ ≤ δ j := hδ₀le j
    rw [hGapply, h1]
    have h5 : v j ≥ -|v j| := neg_abs_le (v j)
    linarith
  have hpos : ∀ x ∈ unitCube r, ∀ j, x j = 1 → 0 ≤ G x j := by
    intro x hx j hxj
    have hmem : γ x ∈ B j := hB1 x hx j hxj
    have h1 : u j (γ x) = infDist (γ x) (A j) := by
      rw [hudef]
      simp only
      rw [infDist_zero_of_mem hmem]
      ring
    have h2 : δ j ≤ infDist (γ x) (A j) := hδB j (γ x) hmem
    have h3 : |v j| < δ₀ := hvj j
    have h4 : δ₀ ≤ δ j := hδ₀le j
    rw [hGapply, h1]
    have h5 : v j ≤ |v j| := le_abs_self (v j)
    linarith
  obtain ⟨x, hxcube, hxzero⟩ := poincare_miranda hGcont hneg hpos
  have hval : (fun j => u j (γ x)) = v := by
    funext j
    have hz := hxzero j
    rw [hGapply] at hz
    linarith
  exact hvnot (γ x) (hγS x hxcube) hval

end GaloisForLFunctions

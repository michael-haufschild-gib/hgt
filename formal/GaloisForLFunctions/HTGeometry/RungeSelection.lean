import GaloisForLFunctions.HTGeometry.RungeGridContour
import GaloisForLFunctions.HTGeometry.RungeEdgeApprox

/-!
# The Runge grid selection

The squares selected for the Runge contour are those *contained* in `Ω` and in a large ball — not
those meeting the compact set `K`.  With a mesh small compared with `dist(K, ℂ∖Ω)` and a ball large
compared with `K`, every square meeting `K` is still selected, so the contour representation holds
on `K`; and the bounded components of `ℂ ∖ K` inside `Ω` are filled by selected squares, so no
surviving edge encircles them.  A surviving edge therefore has a neighbouring square that either
leaves `Ω` — providing a pole target outside `Ω` within `2s` — or leaves the ball — placing the edge
far from `K`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set

noncomputable section

/-- The selection predicate: the square lies in `Ω` and in the ball of radius `R`. -/
def SelSquare (s : ℝ) (Ω : Set ℂ) (R : ℝ) (p : ℤ × ℤ) : Prop :=
  gridSquare s p.1 p.2 ⊆ Ω ∧ gridSquare s p.1 p.2 ⊆ Metric.ball (0 : ℂ) R

theorem mem_gridSquare_corner {s : ℝ} (hs : 0 < s) (p : ℤ × ℤ) :
    gridCorner s p.1 p.2 ∈ gridSquare s p.1 p.2 := by
  refine mem_gridSquare.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [gridCorner_re]
  · rw [gridCorner_re]; nlinarith
  · rw [gridCorner_im]
  · rw [gridCorner_im]; nlinarith

/-- Outside a large index box the square cannot lie in the ball. -/
theorem not_selSquare_of_index_large {s R : ℝ} (hs : 0 < s) {Ω : Set ℂ} {p : ℤ × ℤ}
    (hp : R ≤ s * |(p.1 : ℝ)| ∨ R ≤ s * |(p.2 : ℝ)|) : ¬ SelSquare s Ω R p := by
  rintro ⟨-, hball⟩
  have hmem := hball (mem_gridSquare_corner hs p)
  rw [Metric.mem_ball, dist_zero_right] at hmem
  have hre : |(gridCorner s p.1 p.2).re| ≤ ‖gridCorner s p.1 p.2‖ := Complex.abs_re_le_norm _
  have him : |(gridCorner s p.1 p.2).im| ≤ ‖gridCorner s p.1 p.2‖ := Complex.abs_im_le_norm _
  rw [gridCorner_re] at hre
  rw [gridCorner_im] at him
  rw [abs_mul, abs_of_pos hs] at hre him
  rcases hp with h | h <;> linarith


/-- **The Runge grid selection.**  A mesh, a radius, a tube width and the finite set of selected
squares, adapted to a compact subset of an open set. -/
theorem exists_rungeSelection {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ (s R δ : ℝ) (S : Finset (ℤ × ℤ)),
      0 < s ∧ 0 < R ∧ 0 < δ ∧ 4 * s < δ ∧ 16 * s < R ∧
      (∀ z ∈ K, ‖z‖ ≤ R / 8) ∧
      (∀ w : ℂ, (∃ z ∈ K, dist w z < δ) → w ∈ Ω) ∧
      (∀ p : ℤ × ℤ, p ∈ S ↔ SelSquare s Ω R p) ∧
      GridSelects S s K := by
  classical
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hΩ hKΩ
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := 8 * (|R₀| + 1) with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    have : (0:ℝ) ≤ |R₀| := abs_nonneg R₀
    linarith
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R / 8 := by
    intro z hz
    have := hR₀ hz
    rw [Metric.mem_closedBall, dist_zero_right] at this
    have hle : R₀ ≤ |R₀| := le_abs_self R₀
    rw [hRdef]
    linarith
  set s : ℝ := min (δ / 5) (R / 17) with hsdef
  have hspos : 0 < s := lt_min (by positivity) (by positivity)
  have hsδ : 4 * s < δ := by
    have h := min_le_left (δ / 5) (R / 17)
    rw [← hsdef] at h
    linarith
  have hsR : 16 * s < R := by
    have h := min_le_right (δ / 5) (R / 17)
    rw [← hsdef] at h
    linarith
  set M : ℤ := ⌈R / s⌉ with hMdef
  set S : Finset (ℤ × ℤ) :=
    ((Finset.Icc (-M) M) ×ˢ (Finset.Icc (-M) M)).filter (fun p => SelSquare s Ω R p) with hSdef
  have hMbound : ∀ k : ℤ, s * |(k : ℝ)| < R → k ∈ Finset.Icc (-M) M := by
    intro k hk
    have hceil : R / s ≤ (M : ℝ) := by
      rw [hMdef]
      exact_mod_cast Int.le_ceil (R / s)
    have habs : |(k : ℝ)| < (M : ℝ) := by
      have : |(k : ℝ)| < R / s := by
        rw [lt_div_iff₀ hspos]
        linarith [hk]
      linarith
    have h1 : -(M : ℝ) < (k : ℝ) := by
      have := abs_lt.1 habs
      linarith [this.1]
    have h2 : (k : ℝ) < (M : ℝ) := (abs_lt.1 habs).2
    refine Finset.mem_Icc.2 ⟨?_, ?_⟩
    · have : ((-M : ℤ) : ℝ) ≤ (k : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : (k : ℝ) ≤ ((M : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  have hmemS : ∀ p : ℤ × ℤ, p ∈ S ↔ SelSquare s Ω R p := by
    intro p
    constructor
    · intro hp
      exact (Finset.mem_filter.1 hp).2
    · intro hp
      refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨?_, ?_⟩, hp⟩
      · refine hMbound p.1 ?_
        by_contra hcon
        push Not at hcon
        exact not_selSquare_of_index_large hspos (Or.inl hcon) hp
      · refine hMbound p.2 ?_
        by_contra hcon
        push Not at hcon
        exact not_selSquare_of_index_large hspos (Or.inr hcon) hp
  refine ⟨s, R, δ, S, hspos, hRpos, hδ, hsδ, hsR, hKR, ?_, hmemS, ?_⟩
  · intro w hw
    obtain ⟨z, hzK, hwz⟩ := hw
    exact hthick (Metric.mem_thickening_iff.2 ⟨z, hzK, hwz⟩)
  · intro p hp
    obtain ⟨q, hqsq, hqK⟩ := hp
    refine (hmemS p).2 ⟨?_, ?_⟩
    · intro w hw
      refine hthick (Metric.mem_thickening_iff.2 ⟨q, hqK, ?_⟩)
      have := dist_le_two_mul_of_mem_gridSquare hspos hw hqsq
      linarith
    · intro w hw
      rw [Metric.mem_ball, dist_zero_right]
      have hd := dist_le_two_mul_of_mem_gridSquare hspos hw hqsq
      have hq := hKR q hqK
      have : ‖w‖ ≤ ‖q‖ + dist w q := by
        have := norm_sub_norm_le w q
        rw [← dist_eq_norm] at this
        linarith
      linarith


/-! ## The tube around the compact set -/

/-- The closed `ρ`-tube around `K`. -/
def tubeAround (K : Set ℂ) (ρ : ℝ) : Set ℂ :=
  (fun q : ℂ × ℂ => q.1 + q.2) '' (K ×ˢ Metric.closedBall (0 : ℂ) ρ)

theorem isCompact_tubeAround {K : Set ℂ} (hK : IsCompact K) (ρ : ℝ) :
    IsCompact (tubeAround K ρ) :=
  (hK.prod (isCompact_closedBall (0 : ℂ) ρ)).image (by fun_prop)

theorem mem_tubeAround {K : Set ℂ} {ρ : ℝ} {z : ℂ} :
    z ∈ tubeAround K ρ ↔ ∃ z₀ ∈ K, dist z z₀ ≤ ρ := by
  constructor
  · rintro ⟨⟨z₀, v⟩, ⟨hz₀, hv⟩, rfl⟩
    refine ⟨z₀, hz₀, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    simpa [dist_eq_norm] using hv
  · rintro ⟨z₀, hz₀, hd⟩
    refine ⟨⟨z₀, z - z₀⟩, ⟨hz₀, ?_⟩, by ring⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa [dist_eq_norm] using hd

theorem subset_tubeAround {K : Set ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) : K ⊆ tubeAround K ρ := by
  intro z hz
  exact mem_tubeAround.2 ⟨z, hz, by simpa using hρ⟩

/-! ## Pole targets on a non-selected square -/

/-- Every point of a non-selected square supplies a pole that can be pushed off `Ω` or to
infinity, uniformly on the tube around `K`. -/
theorem approxOn_kernel_of_notSelSquare {Ω K : Set ℂ} {s R δ : ℝ}
    (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩne : Ω.Nonempty) (hΩinf : Ω.Infinite)
    (hs : 0 < s) (hR : 0 < R) (h4s : 4 * s < δ) (h16s : 16 * s < R)
    (hKR : ∀ z ∈ K, ‖z‖ ≤ R / 8)
    (hΩtube : ∀ w : ℂ, (∃ z ∈ K, dist w z < δ) → w ∈ Ω)
    {p' : ℤ × ℤ} (hp' : ¬ SelSquare s Ω R p') {w : ℂ} (hw : w ∈ gridSquare s p'.1 p'.2) :
    (∀ z ∈ tubeAround K (2 * s), w ≠ z) ∧
      ApproxOn (tubeAround K (2 * s)) (RungeDA Ω) (fun z => (z - w)⁻¹) := by
  classical
  by_cases hΩsub : gridSquare s p'.1 p'.2 ⊆ Ω
  · -- the square leaves the ball
    have hball : ¬ gridSquare s p'.1 p'.2 ⊆ Metric.ball (0 : ℂ) R := fun hcon => hp' ⟨hΩsub, hcon⟩
    obtain ⟨b, hbsq, hb⟩ := Set.not_subset.1 hball
    have hbR : R ≤ ‖b‖ := by
      rw [Metric.mem_ball, dist_zero_right] at hb
      exact not_lt.1 hb
    have hwb : dist w b ≤ 2 * s := dist_le_two_mul_of_mem_gridSquare hs hw hbsq
    have hwnorm : R - 2 * s ≤ ‖w‖ := by
      have h1 : ‖b‖ - ‖w‖ ≤ ‖b - w‖ := norm_sub_norm_le _ _
      have h2 : ‖b - w‖ = dist w b := by rw [dist_eq_norm, norm_sub_rev]
      rw [h2] at h1
      linarith
    have htube : ∀ z ∈ tubeAround K (2 * s), ‖z‖ ≤ R / 8 + 2 * s := by
      intro z hz
      obtain ⟨z₀, hz₀, hd⟩ := mem_tubeAround.1 hz
      have h1 : ‖z‖ - ‖z₀‖ ≤ ‖z - z₀‖ := norm_sub_norm_le _ _
      have h2 : ‖z - z₀‖ = dist z z₀ := (dist_eq_norm z z₀).symm
      have h3 := hKR z₀ hz₀
      rw [h2] at h1
      linarith
    have hRK : 0 < R / 8 + 2 * s := by positivity
    have hfar : 2 * (R / 8 + 2 * s) ≤ ‖w‖ := by linarith
    refine ⟨?_, approxOn_cauchyKernel_of_far hRK htube hfar⟩
    intro z hz hcon
    have := htube z hz
    rw [← hcon] at this
    linarith
  · -- the square leaves `Ω`
    obtain ⟨b, hbsq, hb⟩ := Set.not_subset.1 hΩsub
    have hwb : ‖w - b‖ ≤ 2 * s := by
      have := dist_le_two_mul_of_mem_gridSquare hs hw hbsq
      rwa [dist_eq_norm] at this
    have hbK : ∀ z₀ ∈ K, δ ≤ dist b z₀ := by
      intro z₀ hz₀
      by_contra hcon
      push Not at hcon
      exact hb (hΩtube b ⟨z₀, hz₀, hcon⟩)
    have htube : ∀ z ∈ tubeAround K (2 * s), δ - 2 * s ≤ ‖z - b‖ := by
      intro z hz
      obtain ⟨z₀, hz₀, hd⟩ := mem_tubeAround.1 hz
      have h1 := hbK z₀ hz₀
      have h2 : dist b z₀ ≤ dist b z + dist z z₀ := dist_triangle b z z₀
      have h3 : dist b z = ‖z - b‖ := by rw [dist_eq_norm, norm_sub_rev]
      rw [h3] at h2
      linarith
    have hrd : 2 * s < δ - 2 * s := by linarith
    refine ⟨?_, approxOn_cauchyKernel_of_nearOutside hΩo hΩc hΩne hΩinf hb (by positivity) hrd
      hwb htube⟩
    intro z hz hcon
    have h1 := htube z hz
    rw [← hcon] at h1
    linarith


/-! ## Edge points lie in both neighbouring squares -/

theorem hEdgePoint_mem_squares {s : ℝ} (hs : 0 < s) (p : ℤ × ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1))) :
    ((x : ℂ) + ((s * (p.2 : ℝ) : ℝ) : ℂ) * Complex.I) ∈ gridSquare s p.1 p.2 ∧
      ((x : ℂ) + ((s * (p.2 : ℝ) : ℝ) : ℂ) * Complex.I) ∈ gridSquare s p.1 (p.2 - 1) := by
  have hre : ((x : ℂ) + ((s * (p.2 : ℝ) : ℝ) : ℂ) * Complex.I).re = x := cornerPt_re _ _
  have him : ((x : ℂ) + ((s * (p.2 : ℝ) : ℝ) : ℂ) * Complex.I).im = s * (p.2 : ℝ) :=
    cornerPt_im _ _
  constructor
  · refine mem_gridSquare.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hre]; exact hx.1
    · rw [hre]; exact hx.2
    · rw [him]
    · rw [him]; nlinarith
  · refine mem_gridSquare.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hre]; exact hx.1
    · rw [hre]; exact hx.2
    · rw [him]; push_cast; nlinarith
    · rw [him]; push_cast; nlinarith

theorem vEdgePoint_mem_squares {s : ℝ} (hs : 0 < s) (p : ℤ × ℤ) {t : ℝ}
    (ht : t ∈ Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1))) :
    (((s * (p.1 : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I) ∈ gridSquare s p.1 p.2 ∧
      (((s * (p.1 : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I) ∈ gridSquare s (p.1 - 1) p.2 := by
  have hre : (((s * (p.1 : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = s * (p.1 : ℝ) :=
    cornerPt_re _ _
  have him : (((s * (p.1 : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I).im = t := cornerPt_im _ _
  constructor
  · refine mem_gridSquare.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hre]
    · rw [hre]; nlinarith
    · rw [him]; exact ht.1
    · rw [him]; exact ht.2
  · refine mem_gridSquare.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hre]; push_cast; nlinarith
    · rw [hre]; push_cast; nlinarith
    · rw [him]; exact ht.1
    · rw [him]; exact ht.2

theorem exists_notSelSquare_of_hCoeff_ne {s R : ℝ} {Ω : Set ℂ} {S : Finset (ℤ × ℤ)}
    (hmemS : ∀ q : ℤ × ℤ, q ∈ S ↔ SelSquare s Ω R q) {p : ℤ × ℤ} (hne : hCoeff S p ≠ 0) :
    (¬ SelSquare s Ω R p ∧ SelSquare s Ω R (p.1, p.2 - 1)) ∨
      (SelSquare s Ω R p ∧ ¬ SelSquare s Ω R (p.1, p.2 - 1)) := by
  classical
  by_cases h1 : p ∈ S <;> by_cases h2 : (p.1, p.2 - 1) ∈ S
  · exact absurd (by rw [hCoeff, if_pos h1, if_pos h2, sub_self]) hne
  · exact Or.inr ⟨(hmemS p).1 h1, fun hcon => h2 ((hmemS _).2 hcon)⟩
  · exact Or.inl ⟨fun hcon => h1 ((hmemS p).2 hcon), (hmemS _).1 h2⟩
  · exact absurd (by rw [hCoeff, if_neg h1, if_neg h2, sub_self]) hne

theorem exists_notSelSquare_of_vCoeff_ne {s R : ℝ} {Ω : Set ℂ} {S : Finset (ℤ × ℤ)}
    (hmemS : ∀ q : ℤ × ℤ, q ∈ S ↔ SelSquare s Ω R q) {p : ℤ × ℤ} (hne : vCoeff S p ≠ 0) :
    (¬ SelSquare s Ω R p ∧ SelSquare s Ω R (p.1 - 1, p.2)) ∨
      (SelSquare s Ω R p ∧ ¬ SelSquare s Ω R (p.1 - 1, p.2)) := by
  classical
  by_cases h1 : p ∈ S <;> by_cases h2 : (p.1 - 1, p.2) ∈ S
  · exact absurd (by rw [vCoeff, if_pos h2, if_pos h1, sub_self]) hne
  · exact Or.inr ⟨(hmemS p).1 h1, fun hcon => h2 ((hmemS _).2 hcon)⟩
  · exact Or.inl ⟨fun hcon => h1 ((hmemS p).2 hcon), (hmemS _).1 h2⟩
  · exact absurd (by rw [vCoeff, if_neg h2, if_neg h1, sub_self]) hne

end

end GaloisForLFunctions.HTGeometry

import Mathlib

/-!
# Parameter count, Lipschitz constant, and covering entropy

A separated subset of a Euclidean ball has cardinality bounded by the ratio of ball volumes, so a
maximal separated subset is a net of controlled size.  Pushing that net forward through a Lipschitz
map turns it into a net of the image, and an image dense in a target turns it into a cover of the
target at twice the density radius.

Consequently the covering number of any target densely covered by the Lipschitz image of a bounded
`m`-parameter set is at most one plus the parameter-to-resolution ratio, raised to the number of
parameters.  Equivalently, the Lipschitz constant is at least the `m`-th root of the target's
covering number.
-/

open Metric MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section CoveringNumber

variable {Y : Type*} [PseudoMetricSpace Y]

/-- The least number of closed balls of one radius that cover a set. -/
def coveringNumber (S : Set Y) (r : ℝ) : ℕ∞ :=
  ⨅ (t : Finset Y) (_ : S ⊆ ⋃ y ∈ t, closedBall y r), (t.card : ℕ∞)

theorem coveringNumber_le {S : Set Y} {r : ℝ} {t : Finset Y}
    (ht : S ⊆ ⋃ y ∈ t, closedBall y r) : coveringNumber S r ≤ (t.card : ℕ∞) := by
  refine le_trans (iInf_le _ t) ?_
  exact iInf_le _ ht

end CoveringNumber

section SeparatedNet

variable {m : ℕ}

/-- A separated subset of a Euclidean ball has cardinality bounded by the ball volume ratio. -/
private theorem card_le_of_separated {R δ : ℝ} (hm : 0 < m) (hδ : 0 < δ) (hR : 0 ≤ R)
    {t : Finset (EuclideanSpace ℝ (Fin m))}
    (hball : ∀ x ∈ t, x ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) R)
    (hsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → δ ≤ dist x y) :
    (t.card : ℝ) * (δ / 2) ^ m ≤ (R + δ / 2) ^ m := by
  classical
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nontrivial (EuclideanSpace ℝ (Fin m)) := by infer_instance
  set μ : Measure (EuclideanSpace ℝ (Fin m)) := volume with hμ
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := finrank_euclideanSpace_fin
  have hballvol : ∀ (x : EuclideanSpace ℝ (Fin m)) (r : ℝ), 0 ≤ r →
      μ (ball x r) = ENNReal.ofReal (r ^ m) * μ (ball 0 1) := by
    intro x r hr
    rw [Measure.addHaar_ball _ _ hr, hdim]
  have hdisj : ∀ x ∈ t, ∀ y ∈ t, x ≠ y →
      Disjoint (ball x (δ / 2)) (ball y (δ / 2)) := by
    intro x hx y hy hxy
    refine ball_disjoint_ball ?_
    have := hsep x hx y hy hxy
    linarith
  have hunion : (⋃ x ∈ t, ball x (δ / 2)) ⊆
      ball (0 : EuclideanSpace ℝ (Fin m)) (R + δ / 2) := by
    refine iUnion₂_subset fun x hx => ?_
    intro z hz
    have hx' : dist x 0 ≤ R := by
      have := hball x hx
      rwa [mem_closedBall] at this
    have hz' : dist z x < δ / 2 := by
      rwa [mem_ball] at hz
    rw [mem_ball]
    calc dist z 0 ≤ dist z x + dist x 0 := dist_triangle _ _ _
      _ < δ / 2 + R := by linarith
      _ = R + δ / 2 := by ring
  have hmeas : μ (⋃ x ∈ t, ball x (δ / 2)) = ∑ x ∈ t, μ (ball x (δ / 2)) :=
    measure_biUnion_finset (fun x hx y hy hxy => hdisj x hx y hy hxy)
      (fun x _ => measurableSet_ball)
  have hle : (∑ x ∈ t, μ (ball x (δ / 2))) ≤ μ (ball 0 (R + δ / 2)) := by
    rw [← hmeas]
    exact measure_mono hunion
  have hconst : ∀ x ∈ t, μ (ball x (δ / 2)) = ENNReal.ofReal ((δ / 2) ^ m) * μ (ball 0 1) :=
    fun x _ => hballvol x (δ / 2) (by linarith)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul,
    hballvol 0 (R + δ / 2) (by linarith), ← mul_assoc] at hle
  have hunit : μ (ball (0 : EuclideanSpace ℝ (Fin m)) 1) ≠ 0 :=
    (measure_ball_pos μ 0 one_pos).ne'
  have hunittop : μ (ball (0 : EuclideanSpace ℝ (Fin m)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hcancel : (t.card : ENNReal) * ENNReal.ofReal ((δ / 2) ^ m) ≤
      ENNReal.ofReal ((R + δ / 2) ^ m) :=
    (ENNReal.mul_le_mul_iff_left hunit hunittop).mp hle
  have hnn2 : (0 : ℝ) ≤ (R + δ / 2) ^ m := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at hcancel
  exact (ENNReal.ofReal_le_ofReal_iff hnn2).mp hcancel


/-- A maximal separated subset of a bounded parameter set is a net of controlled size. -/
theorem exists_separated_net {R δ : ℝ} (hm : 0 < m) (hδ : 0 < δ) (hR : 0 ≤ R)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : K ⊆ closedBall 0 R) :
    ∃ t : Finset (EuclideanSpace ℝ (Fin m)), ↑t ⊆ K ∧
      (t.card : ℝ) * (δ / 2) ^ m ≤ (R + δ / 2) ^ m ∧
      ∀ x ∈ K, ∃ y ∈ t, dist x y < δ := by
  classical
  set Good : Finset (EuclideanSpace ℝ (Fin m)) → Prop := fun t =>
    (↑t ⊆ K) ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → δ ≤ dist x y with hGood
  set N : Set ℕ := {n | ∃ t, Good t ∧ t.card = n} with hN
  have hNne : N.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  have hbound : ∀ t : Finset (EuclideanSpace ℝ (Fin m)), Good t →
      (t.card : ℝ) * (δ / 2) ^ m ≤ (R + δ / 2) ^ m := by
    intro t ht
    exact card_le_of_separated hm hδ hR (fun x hx => hK (ht.1 hx)) ht.2
  have hδm : (0 : ℝ) < (δ / 2) ^ m := by positivity
  have hNbdd : ∀ n ∈ N, n ≤ ⌈(R + δ / 2) ^ m / (δ / 2) ^ m⌉₊ := by
    rintro n ⟨t, ht, rfl⟩
    have hb := hbound t ht
    have : (t.card : ℝ) ≤ (R + δ / 2) ^ m / (δ / 2) ^ m := by
      rw [le_div_iff₀ hδm]
      exact hb
    exact Nat.cast_le.mp (le_trans this (Nat.le_ceil _))
  have hmem : sSup N ∈ N := Nat.sSup_mem hNne ⟨_, hNbdd⟩
  obtain ⟨t, ht, htcard⟩ := hmem
  refine ⟨t, ht.1, hbound t ht, ?_⟩
  intro x hx
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hxnot : x ∉ t := by
    intro hxt
    have := hcon x hxt
    simp at this
    linarith
  have hins : Good (insert x t) := by
    refine ⟨?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hz) with rfl | hz'
      · exact hx
      · exact ht.1 hz'
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · rcases Finset.mem_insert.mp hb with rfl | hb'
        · exact absurd rfl hab
        · exact hcon b hb'
      · rcases Finset.mem_insert.mp hb with rfl | hb'
        · rw [dist_comm]
          exact hcon a ha'
        · exact ht.2 a ha' b hb' hab
  have hcardins : (insert x t).card = t.card + 1 := Finset.card_insert_of_notMem hxnot
  have hle : (insert x t).card ≤ sSup N :=
    le_csSup ⟨_, hNbdd⟩ ⟨insert x t, hins, rfl⟩
  rw [hcardins, htcard] at hle
  omega

end SeparatedNet

section CoverageBarrier

variable {m : ℕ} {Y : Type*} [PseudoMetricSpace Y]

/-- **Parameter--time--coverage law.**  A target densely covered by the Lipschitz image of a
bounded `m`-parameter set has a cover at twice the density radius whose cardinality is at most one
plus the parameter-to-resolution ratio, raised to the number of parameters. -/
theorem exists_cover_card_le {R L ε : ℝ} (hm : 0 < m) (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε)
    {K : Set (EuclideanSpace ℝ (Fin m))} {S : Set Y}
    (hK : K ⊆ closedBall 0 R) (F : EuclideanSpace ℝ (Fin m) → Y)
    (hF : ∀ x ∈ K, ∀ y ∈ K, dist (F x) (F y) ≤ L * dist x y)
    (hdense : ∀ z ∈ S, ∃ x ∈ K, dist z (F x) ≤ ε) :
    ∃ t : Finset Y, S ⊆ ⋃ y ∈ t, closedBall y (2 * ε) ∧
      (t.card : ℝ) ≤ (1 + 2 * R * L / ε) ^ m := by
  classical
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · -- a constant image needs one ball
    rcases Set.eq_empty_or_nonempty K with hKe | ⟨x₀, hx₀⟩
    · refine ⟨∅, ?_, ?_⟩
      · intro z hz
        obtain ⟨x, hx, -⟩ := hdense z hz
        exact absurd hx (by rw [hKe]; exact fun h => h)
      · simp
        positivity
    · refine ⟨{F x₀}, ?_, ?_⟩
      · intro z hz
        obtain ⟨x, hx, hd⟩ := hdense z hz
        refine Set.mem_iUnion₂.mpr ⟨F x₀, Finset.mem_singleton_self _, ?_⟩
        have hconst : dist (F x) (F x₀) ≤ 0 := by
          have := hF x hx x₀ hx₀
          rw [← hL0] at this
          simpa using this
        rw [mem_closedBall]
        calc dist z (F x₀) ≤ dist z (F x) + dist (F x) (F x₀) := dist_triangle _ _ _
          _ ≤ ε + 0 := by linarith
          _ ≤ 2 * ε := by linarith
      · rw [Finset.card_singleton]
        have h1 : (1 : ℝ) ≤ 1 + 2 * R * L / ε := by
          rw [← hL0]
          simp
        calc ((1 : ℕ) : ℝ) = 1 ^ m := by norm_num
          _ ≤ (1 + 2 * R * L / ε) ^ m := pow_le_pow_left₀ (by norm_num) h1 m
  · set δ : ℝ := ε / L with hδdef
    have hδ : 0 < δ := div_pos hε hLpos
    obtain ⟨t, htK, htcard, htnet⟩ := exists_separated_net hm hδ hR K hK
    refine ⟨t.image F, ?_, ?_⟩
    · intro z hz
      obtain ⟨x, hx, hd⟩ := hdense z hz
      obtain ⟨y, hy, hxy⟩ := htnet x hx
      refine Set.mem_iUnion₂.mpr ⟨F y, Finset.mem_image_of_mem F hy, ?_⟩
      have hFxy : dist (F x) (F y) ≤ L * dist x y := hF x hx y (htK hy)
      have hLd : L * dist x y ≤ L * δ := by
        exact mul_le_mul_of_nonneg_left hxy.le hL
      have hLδ : L * δ = ε := by
        rw [hδdef]
        field_simp
      rw [mem_closedBall]
      calc dist z (F y) ≤ dist z (F x) + dist (F x) (F y) := dist_triangle _ _ _
        _ ≤ ε + ε := by
            refine add_le_add hd ?_
            calc dist (F x) (F y) ≤ L * dist x y := hFxy
              _ ≤ L * δ := hLd
              _ = ε := hLδ
        _ = 2 * ε := by ring
    · refine le_trans (Nat.cast_le.mpr Finset.card_image_le) ?_
      have hδm : (0 : ℝ) < (δ / 2) ^ m := by positivity
      have hcard : (t.card : ℝ) ≤ ((R + δ / 2) / (δ / 2)) ^ m := by
        rw [div_pow, le_div_iff₀ hδm]
        exact htcard
      refine le_trans hcard (le_of_eq ?_)
      congr 1
      rw [hδdef]
      field_simp
      ring


section RootForm

/-- Taking the `m`-th root of a covering comparison. -/
theorem rpow_inv_le_of_le_pow {m : ℕ} (hm : 0 < m) {N c : ℝ} (hN : 0 ≤ N) (hc : 0 ≤ c)
    (h : N ≤ (1 + c) ^ m) : N ^ ((m : ℝ)⁻¹) ≤ 1 + c := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hbase : (0 : ℝ) ≤ 1 + c := by linarith
  have hstep : N ^ ((m : ℝ)⁻¹) ≤ ((1 + c) ^ m) ^ ((m : ℝ)⁻¹) :=
    Real.rpow_le_rpow hN h (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  rw [← Real.rpow_natCast (1 + c) m, ← Real.rpow_mul hbase,
    mul_inv_cancel₀ (ne_of_gt hmpos), Real.rpow_one]

/-- **Parameter--time--coverage law, root form.**  The Lipschitz constant of a bounded
`m`-parameter family whose image is `ε`-dense in a target is at least the `m`-th root of the
target's covering number, scaled by the resolution over the parameter radius. -/
theorem le_lipschitz_of_covering {m : ℕ} (hm : 0 < m) {R L ε N : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (hε : 0 < ε) (hN : 0 ≤ N)
    {Y : Type*} [PseudoMetricSpace Y] {K : Set (EuclideanSpace ℝ (Fin m))} {S : Set Y}
    (hK : K ⊆ closedBall 0 R) (F : EuclideanSpace ℝ (Fin m) → Y)
    (hF : ∀ x ∈ K, ∀ y ∈ K, dist (F x) (F y) ≤ L * dist x y)
    (hdense : ∀ z ∈ S, ∃ x ∈ K, dist z (F x) ≤ ε)
    (hcov : ∀ t : Finset Y, S ⊆ (⋃ y ∈ t, closedBall y (2 * ε)) → N ≤ (t.card : ℝ)) :
    ε / (2 * R) * (N ^ ((m : ℝ)⁻¹) - 1) ≤ L := by
  obtain ⟨t, hcover, hcard⟩ := exists_cover_card_le hm hR.le hL hε hK F hF hdense
  have hNle : N ≤ (1 + 2 * R * L / ε) ^ m := le_trans (hcov t hcover) hcard
  have hc : (0 : ℝ) ≤ 2 * R * L / ε := by positivity
  have hroot := rpow_inv_le_of_le_pow hm hN hc hNle
  have h2R : (0 : ℝ) < 2 * R := by linarith
  have hdiv : 2 * R * L / ε * ε = 2 * R * L := by field_simp
  have hstep : (N ^ ((m : ℝ)⁻¹) - 1) * ε ≤ 2 * R * L := by
    calc (N ^ ((m : ℝ)⁻¹) - 1) * ε ≤ (2 * R * L / ε) * ε :=
          mul_le_mul_of_nonneg_right (by linarith [hroot]) hε.le
      _ = 2 * R * L := hdiv
  rw [div_mul_eq_mul_div, div_le_iff₀ h2R]
  nlinarith [hstep]

end RootForm

/-- **Image net.**  The Lipschitz image of a bounded `m`-parameter set has an `ε`-net whose size is
at most one plus the parameter-to-resolution ratio, raised to the number of parameters. -/
theorem exists_image_net_card_le {R L ε : ℝ} (hm : 0 < m) (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε)
    {K : Set (EuclideanSpace ℝ (Fin m))} {Y : Type*} [PseudoMetricSpace Y]
    (hK : K ⊆ closedBall 0 R) (F : EuclideanSpace ℝ (Fin m) → Y)
    (hF : ∀ x ∈ K, ∀ y ∈ K, dist (F x) (F y) ≤ L * dist x y) :
    ∃ t : Finset Y, F '' K ⊆ (⋃ y ∈ t, closedBall y ε) ∧
      (t.card : ℝ) ≤ (1 + 2 * R * L / ε) ^ m := by
  classical
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · rcases Set.eq_empty_or_nonempty K with hKe | ⟨x₀, hx₀⟩
    · refine ⟨∅, ?_, ?_⟩
      · rw [hKe]
        simp
      · simp
        positivity
    · refine ⟨{F x₀}, ?_, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩
        refine Set.mem_iUnion₂.mpr ⟨F x₀, Finset.mem_singleton_self _, ?_⟩
        have hconst : dist (F x) (F x₀) ≤ 0 := by
          have := hF x hx x₀ hx₀
          rw [← hL0] at this
          simpa using this
        rw [mem_closedBall]
        linarith
      · rw [Finset.card_singleton]
        have h1 : (1 : ℝ) ≤ 1 + 2 * R * L / ε := by
          rw [← hL0]
          simp
        calc ((1 : ℕ) : ℝ) = 1 ^ m := by norm_num
          _ ≤ (1 + 2 * R * L / ε) ^ m := pow_le_pow_left₀ (by norm_num) h1 m
  · set δ : ℝ := ε / L with hδdef
    have hδ : 0 < δ := div_pos hε hLpos
    obtain ⟨T, hTK, hTcard, hTnet⟩ := exists_separated_net hm hδ hR K hK
    refine ⟨T.image F, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := hTnet x hx
      refine Set.mem_iUnion₂.mpr ⟨F y, Finset.mem_image_of_mem F hy, ?_⟩
      rw [mem_closedBall]
      calc dist (F x) (F y) ≤ L * dist x y := hF x hx y (hTK hy)
        _ ≤ L * δ := mul_le_mul_of_nonneg_left hxy.le hL
        _ = ε := by rw [hδdef]; field_simp
    · refine le_trans (Nat.cast_le.mpr Finset.card_image_le) ?_
      have hδm : (0 : ℝ) < (δ / 2) ^ m := by positivity
      have hcard : (T.card : ℝ) ≤ ((R + δ / 2) / (δ / 2)) ^ m := by
        rw [div_pow, le_div_iff₀ hδm]
        exact hTcard
      refine le_trans hcard (le_of_eq ?_)
      congr 1
      rw [hδdef]
      field_simp
      ring

end CoverageBarrier

end

end GaloisForLFunctions.HTGeometry

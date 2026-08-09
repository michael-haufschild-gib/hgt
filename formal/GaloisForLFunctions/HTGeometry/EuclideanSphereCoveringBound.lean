import Mathlib

/-!
# Volumetric covering bound for Euclidean balls and spheres

A set of points in a Euclidean ball of radius `R` whose mutual distances exceed `η` carries
disjoint balls of radius `η/2` inside the ball of radius `R + η/2`.  Comparing Haar volumes bounds
its cardinality by `((R + η/2)/(η/2))^m`.  A maximal such set is an `η`-net, so the covering
number of the unit sphere obeys `N(S^{m−1}, η) ≤ (1 + 2/η)^m`.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace HTGeometry

section Packing

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem volume_ball_eq_pow_mul (x : E) {r : ℝ} (hr : 0 ≤ r) [Nontrivial E] :
    volume (Metric.ball x r) =
      ENNReal.ofReal (r ^ m) * volume (Metric.ball (0 : E) 1) := by
  rw [Measure.addHaar_ball volume x hr, finrank_euclideanSpace_fin]

/-- A finite `η`-separated subset of a ball of radius `R` has at most
`((R + η/2)/(η/2))^m` points. -/
theorem card_mul_pow_le_of_separated_finset [Nontrivial E]
    {η R : ℝ} (hη : 0 < η) (hR : 0 ≤ R) (T : Finset E)
    (hT : ∀ x ∈ T, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → η < dist x y) :
    (T.card : ℝ) * (η / 2) ^ m ≤ (R + η / 2) ^ m := by
  classical
  set V : ℝ≥0∞ := volume (Metric.ball (0 : E) 1) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos volume (0 : E) one_pos).ne'
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  have hVpos : 0 < V.toReal := ENNReal.toReal_pos hV0 hVtop
  have hhalf : (0 : ℝ) < η / 2 := by linarith
  -- disjointness
  have hdisj : (T : Set E).PairwiseDisjoint fun x => Metric.ball x (η / 2) := by
    intro x hx y hy hxy
    refine Metric.ball_disjoint_ball ?_
    have := hsep x hx y hy hxy
    linarith
  -- containment
  have hsubset : (⋃ x ∈ T, Metric.ball x (η / 2)) ⊆ Metric.ball (0 : E) (R + η / 2) := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp hz
    have hxn : ‖x‖ ≤ R := hT x hx
    have hzd : dist z x < η / 2 := Metric.mem_ball.mp hzx
    have : dist z 0 ≤ dist z x + dist x 0 := dist_triangle z x 0
    have hx0 : dist x 0 = ‖x‖ := by simp [dist_eq_norm]
    rw [hx0] at this
    exact Metric.mem_ball.mpr (by linarith)
  -- volumes
  have hballvol : ∀ x : E, volume (Metric.ball x (η / 2)) = ENNReal.ofReal ((η / 2) ^ m) * V :=
    fun x => volume_ball_eq_pow_mul x hhalf.le
  have hsumvol : volume (⋃ x ∈ T, Metric.ball x (η / 2)) =
      ∑ _x ∈ T, ENNReal.ofReal ((η / 2) ^ m) * V := by
    rw [measure_biUnion_finset hdisj (fun a _ => measurableSet_ball)]
    exact Finset.sum_congr rfl fun x _ => hballvol x
  have hbig : volume (Metric.ball (0 : E) (R + η / 2)) =
      ENNReal.ofReal ((R + η / 2) ^ m) * V :=
    volume_ball_eq_pow_mul 0 (by linarith)
  have hmono : volume (⋃ x ∈ T, Metric.ball x (η / 2)) ≤
      volume (Metric.ball (0 : E) (R + η / 2)) := measure_mono hsubset
  rw [hsumvol, hbig, Finset.sum_const, nsmul_eq_mul] at hmono
  -- pass to real numbers
  have hfin : ((T.card : ℝ≥0∞) * (ENNReal.ofReal ((η / 2) ^ m) * V)).toReal =
      (T.card : ℝ) * ((η / 2) ^ m * V.toReal) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity)]
  have hfin2 : (ENNReal.ofReal ((R + η / 2) ^ m) * V).toReal = (R + η / 2) ^ m * V.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have htopR : ENNReal.ofReal ((R + η / 2) ^ m) * V ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVtop
  have hreal := ENNReal.toReal_mono htopR hmono
  rw [hfin, hfin2] at hreal
  refine le_of_mul_le_mul_right ?_ hVpos
  linarith [hreal]

/-- A separated subset of a ball of radius `R` is finite with the volumetric cardinality bound. -/
theorem finite_and_ncard_le_of_separated [Nontrivial E]
    {η R : ℝ} (hη : 0 < η) (hR : 0 ≤ R) (S : Set E)
    (hS : ∀ x ∈ S, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → η < dist x y) :
    S.Finite ∧ (S.ncard : ℝ) * (η / 2) ^ m ≤ (R + η / 2) ^ m := by
  classical
  have hhalf : (0 : ℝ) < η / 2 := by linarith
  have hbound : (0 : ℝ) < (R + η / 2) ^ m / (η / 2) ^ m := by positivity
  have hfin : S.Finite := by
    by_contra hinf
    have hinf' : S.Infinite := hinf
    obtain ⟨T, hTS, hTcard⟩ :=
      hinf'.exists_subset_card_eq (⌈(R + η / 2) ^ m / (η / 2) ^ m⌉₊ + 1)
    have hkey := card_mul_pow_le_of_separated_finset hη hR T
      (fun x hx => hS x (hTS hx)) (fun x hx y hy hxy => hsep x (hTS hx) y (hTS hy) hxy)
    rw [hTcard] at hkey
    have hpow : (0 : ℝ) < (η / 2) ^ m := by positivity
    have hlt : (R + η / 2) ^ m / (η / 2) ^ m <
        ((⌈(R + η / 2) ^ m / (η / 2) ^ m⌉₊ : ℝ) + 1) := by
      have := Nat.le_ceil ((R + η / 2) ^ m / (η / 2) ^ m)
      linarith
    rw [div_lt_iff₀ hpow] at hlt
    push_cast at hkey
    linarith
  refine ⟨hfin, ?_⟩
  have hkey := card_mul_pow_le_of_separated_finset hη hR hfin.toFinset
    (fun x hx => hS x (hfin.mem_toFinset.mp hx))
    (fun x hx y hy hxy => hsep x (hfin.mem_toFinset.mp hx) y (hfin.mem_toFinset.mp hy) hxy)
  have hcard : S.ncard = hfin.toFinset.card := Set.ncard_eq_toFinset_card S hfin
  rwa [hcard]


/-- **Maximal separated net.**  A bounded set in Euclidean space has a finite `η`-net inside
itself whose cardinality obeys the volumetric packing bound. -/
theorem exists_separated_net [Nontrivial E]
    {η R : ℝ} (hη : 0 < η) (hR : 0 ≤ R) (A : Set E) (hA : ∀ x ∈ A, ‖x‖ ≤ R) :
    ∃ C : Finset E, ↑C ⊆ A ∧ (C.card : ℝ) * (η / 2) ^ m ≤ (R + η / 2) ^ m ∧
      ∀ x ∈ A, ∃ z ∈ C, dist x z ≤ η := by
  classical
  have hpow : (0 : ℝ) < (η / 2) ^ m := by positivity
  set B : ℝ := (R + η / 2) ^ m / (η / 2) ^ m with hB
  set K : Set ℕ := {n | ∃ C : Finset E, ↑C ⊆ A ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → η < dist x y) ∧ C.card = n} with hK
  have hKne : K.Nonempty := ⟨0, ∅, by simp, by simp, by simp⟩
  have hKbdd : ∀ n ∈ K, n ≤ ⌈B⌉₊ := by
    rintro n ⟨C, hCA, hCsep, rfl⟩
    have hcard := card_mul_pow_le_of_separated_finset hη hR C
      (fun x hx => hA x (hCA hx)) hCsep
    have hle : (C.card : ℝ) ≤ B := by rw [hB, le_div_iff₀ hpow]; linarith
    have : (C.card : ℝ) ≤ (⌈B⌉₊ : ℝ) := le_trans hle (Nat.le_ceil B)
    exact_mod_cast this
  have hmem : sSup K ∈ K := Nat.sSup_mem hKne ⟨⌈B⌉₊, hKbdd⟩
  obtain ⟨C, hCA, hCsep, hCcard⟩ := hmem
  refine ⟨C, hCA, ?_, ?_⟩
  · exact card_mul_pow_le_of_separated_finset hη hR C (fun x hx => hA x (hCA hx)) hCsep
  · intro x hx
    by_contra hcon
    have hxsep : ∀ z ∈ C, η < dist x z := by
      intro z hz
      by_contra hle
      exact hcon ⟨z, hz, not_lt.mp hle⟩
    have hxnot : x ∉ C := by
      intro hxC
      have := hxsep x hxC
      simp at this
      linarith
    have hins : ↑(insert x C) ⊆ A := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyC
      · exact hx
      · exact hCA hyC
    have hinssep : ∀ u ∈ insert x C, ∀ v ∈ insert x C, u ≠ v → η < dist u v := by
      intro u hu v hv huv
      rcases Finset.mem_insert.mp hu with rfl | huC
      · rcases Finset.mem_insert.mp hv with rfl | hvC
        · exact absurd rfl huv
        · exact hxsep v hvC
      · rcases Finset.mem_insert.mp hv with rfl | hvC
        · rw [dist_comm]; exact hxsep u huC
        · exact hCsep u huC v hvC huv
    have hmemK : (insert x C).card ∈ K := ⟨insert x C, hins, hinssep, rfl⟩
    have hle := le_csSup ⟨⌈B⌉₊, fun n hn => hKbdd n hn⟩ hmemK
    rw [Finset.card_insert_of_notMem hxnot, hCcard] at hle
    omega

/-- **Lipschitz orbit cover.**  The image of a bounded Euclidean set under a Lipschitz map has a
finite net of actual image points, of volumetrically bounded cardinality. -/
theorem exists_lipschitz_image_net [Nontrivial E] {Y : Type*} [MetricSpace Y]
    {η R L : ℝ} (hη : 0 < η) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (A : Set E) (hA : ∀ x ∈ A, ‖x‖ ≤ R) (F : E → Y)
    (hF : ∀ x ∈ A, ∀ y ∈ A, dist (F x) (F y) ≤ L * dist x y) :
    ∃ Z : Finset Y, (Z.card : ℝ) * (η / 2) ^ m ≤ (R + η / 2) ^ m ∧
      (∀ z ∈ Z, ∃ x ∈ A, F x = z) ∧
      ∀ x ∈ A, ∃ z ∈ Z, dist (F x) z ≤ L * η := by
  classical
  obtain ⟨C, hCA, hCcard, hCnet⟩ := exists_separated_net hη hR A hA
  refine ⟨C.image F, ?_, ?_, ?_⟩
  · have hle : ((C.image F).card : ℝ) ≤ (C.card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    have hpow : (0 : ℝ) ≤ (η / 2) ^ m := by positivity
    nlinarith [hCcard, hle, hpow]
  · intro z hz
    obtain ⟨x, hxC, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨x, hCA hxC, rfl⟩
  · intro x hx
    obtain ⟨z, hzC, hxz⟩ := hCnet x hx
    refine ⟨F z, Finset.mem_image_of_mem F hzC, ?_⟩
    exact le_trans (hF x hx z (hCA hzC)) (by nlinarith [dist_nonneg (x := x) (y := z)])

/-- **Unit-sphere Lipschitz cover.**  Every `L`-Lipschitz image of the Euclidean unit sphere has
an `ε`-net of at most `(1 + 2L/ε)^m` actual image points. -/
theorem exists_unitSphere_lipschitz_net [Nontrivial E] {Y : Type*} [MetricSpace Y]
    {eps L : ℝ} (heps : 0 < eps) (hL : 0 < L) (F : E → Y)
    (hF : ∀ x ∈ Metric.sphere (0 : E) 1, ∀ y ∈ Metric.sphere (0 : E) 1,
      dist (F x) (F y) ≤ L * dist x y) :
    ∃ Z : Finset Y, (Z.card : ℝ) ≤ (1 + 2 * L / eps) ^ m ∧
      (∀ z ∈ Z, ∃ x ∈ Metric.sphere (0 : E) 1, F x = z) ∧
      ∀ x ∈ Metric.sphere (0 : E) 1, ∃ z ∈ Z, dist (F x) z ≤ eps := by
  classical
  have hη : (0 : ℝ) < eps / L := by positivity
  have hA : ∀ x ∈ Metric.sphere (0 : E) 1, ‖x‖ ≤ 1 := by
    intro x hx
    rw [mem_sphere_iff_norm, sub_zero] at hx
    exact le_of_eq hx
  obtain ⟨Z, hZcard, hZim, hZnet⟩ :=
    exists_lipschitz_image_net hη (by norm_num : (0:ℝ) ≤ 1) hL.le
      (Metric.sphere (0 : E) 1) hA F hF
  refine ⟨Z, ?_, hZim, ?_⟩
  · have hpow : (0 : ℝ) < (eps / L / 2) ^ m := by positivity
    have hkey : (Z.card : ℝ) ≤ (1 + eps / L / 2) ^ m / (eps / L / 2) ^ m := by
      rw [le_div_iff₀ hpow]; linarith [hZcard]
    have hval : (1 + eps / L / 2) ^ m / (eps / L / 2) ^ m = (1 + 2 * L / eps) ^ m := by
      rw [← div_pow]
      congr 1
      field_simp
      ring
    rwa [hval] at hkey
  · intro x hx
    obtain ⟨z, hz, hd⟩ := hZnet x hx
    refine ⟨z, hz, ?_⟩
    have : L * (eps / L) = eps := by field_simp
    linarith [hd, this.le, this.ge]

end Packing

end HTGeometry

import GaloisForLFunctions.BezoutValuationIncidence.MobiusMagnitudePatternDensity

/-!
# Joint magnitude laws at real source horizons

A fixed collection of shifts crosses at most a bounded number of positions
at each complementary-divisor band boundary. The limiting fixed-band pattern
laws therefore transfer to the literal truncated Möbius source. Raw pattern
masses are affine between successive integer horizons; dividing by the real
horizon gives a nonnegative finite probability law with total mass one.
All statements are unconditional. No assertion identifies positive-density
support with patterns attained only at moving band boundaries.
-/

open Filter Topology Finset
open scoped BigOperators Classical

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false
variable {m : ℕ}

/-- Literal shifted source-magnitude patterns on an initial segment of the j-th band. -/
def moebiusSourceMagnitudeBandPatternCount (j N L : ℕ)
    (h : Fin m → ℕ) (a : Fin m → ℝ) : ℕ :=
  ((Ioc (j * N) (j * N + L)).filter
    (fun n => ∀ i, |sieveSeq N moebiusReal (n + h i)| = a i)).card

private theorem source_band_agrees (j : ℕ) (N : ℕ+) {n : ℕ}
    (hn : j * (N : ℕ) < n) (hn1 : n ≠ 1)
    (h : Fin m → ℕ) (hhi : ∀ i, n + h i ≤ (j + 1) * (N : ℕ)) (i : Fin m) :
    |sieveSeq N moebiusReal (n + h i)| = moebiusBandMagnitude j (n + h i) := by
  have hn0 : 0 < n + h i := by omega
  have hn1' : n + h i ≠ 1 := by omega
  have hj : (n + h i - 1) / (N : ℕ) = j := by
    apply Nat.div_eq_of_lt_le
    · omega
    · have hh := hhi i
      omega
  have he := abs_sieveSeq_moebius_eq_bandMagnitude N ⟨n + h i, hn0⟩
  change |sieveSeq N moebiusReal (n + h i)| =
    if n + h i = 1 then 1 else moebiusBandMagnitude ((n + h i - 1) / (N : ℕ)) (n + h i) at he
  simpa only [if_neg hn1', hj] using he

private theorem band_boundary_count_le (j : ℕ) (N : ℕ+) (L : Fin ((N : ℕ) + 1))
    (h : Fin m → ℕ) :
    ((Ioc (j * (N : ℕ)) (j * (N : ℕ) + L)).filter
      (fun n => n = 1 ∨ ∃ i, (j + 1) * (N : ℕ) < n + h i)).card ≤ 1 + ∑ i, h i := by
  let V : ℕ := (j + 1) * (N : ℕ)
  let B (i : Fin m) := Ioc (V - h i) V
  have hL : j * (N : ℕ) + L ≤ V := by
    have := L.isLt
    dsimp [V]
    nlinarith
  have hsub : ((Ioc (j * (N : ℕ)) (j * (N : ℕ) + L)).filter
      (fun n => n = 1 ∨ ∃ i, V < n + h i)) ⊆ {1} ∪ univ.biUnion B := by
    intro n hn
    obtain ⟨hn, hb⟩ := mem_filter.mp hn
    obtain ⟨hn0, hnL⟩ := mem_Ioc.mp hn
    rcases hb with rfl | ⟨i, hi⟩
    · simp
    apply mem_union.mpr
    right
    apply mem_biUnion.mpr
    refine ⟨i, mem_univ _, ?_⟩
    apply mem_Ioc.mpr
    constructor <;> omega
  calc
    _ ≤ ({1} ∪ univ.biUnion B).card := card_le_card hsub
    _ ≤ ({1} : Finset ℕ).card + (univ.biUnion B).card := card_union_le _ _
    _ ≤ 1 + ∑ i : Fin m, (B i).card := by
      simpa only [card_singleton] using Nat.add_le_add_left (card_biUnion_le (s := univ) (t := B)) 1
    _ ≤ 1 + ∑ i : Fin m, h i := by
      apply Nat.add_le_add_left
      apply sum_le_sum
      intro i _
      simp only [B, Nat.card_Ioc]
      omega

/-- Fixed shifts change at most a bounded number of positions at a source-band boundary. -/
theorem moebiusSourceMagnitudeBandPatternCount_error (j : ℕ) (N : ℕ+)
    (L : Fin ((N : ℕ) + 1)) (h : Fin m → ℕ) (a : Fin m → ℝ) :
    |(moebiusSourceMagnitudeBandPatternCount j N L h a : ℝ) -
      (((Ioc (j * (N : ℕ)) (j * (N : ℕ) + L)).filter
        (fun n => ∀ i, moebiusBandMagnitude j (n + h i) = a i)).card : ℝ)| ≤
      1 + ∑ i, (h i : ℝ) := by
  let S := Ioc (j * (N : ℕ)) (j * (N : ℕ) + L)
  let bad (n : ℕ) := n = 1 ∨ ∃ i, (j + 1) * (N : ℕ) < n + h i
  have he : |(moebiusSourceMagnitudeBandPatternCount j N L h a : ℝ) -
      ((S.filter (fun n => ∀ i, moebiusBandMagnitude j (n + h i) = a i)).card : ℝ)| ≤
        ((S.filter bad).card : ℝ) := by
    have hs : (moebiusSourceMagnitudeBandPatternCount j N L h a : ℝ) =
        ∑ n ∈ S, if ∀ i, |sieveSeq N moebiusReal (n + h i)| = a i then (1 : ℝ) else 0 := by
      simp only [sum_boole, moebiusSourceMagnitudeBandPatternCount, S]
    have hb : ((S.filter (fun n => ∀ i, moebiusBandMagnitude j (n + h i) = a i)).card : ℝ) =
        ∑ n ∈ S, if ∀ i, moebiusBandMagnitude j (n + h i) = a i then (1 : ℝ) else 0 := by
      simp only [sum_boole]
    rw [hs, hb, ← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ n ∈ S, if bad n then (1 : ℝ) else 0 := by
        apply sum_le_sum
        intro n hn
        by_cases hbad : bad n
        · rw [if_pos hbad]
          split_ifs <;> norm_num
        · have hg : n ≠ 1 ∧ ∀ i, n + h i ≤ (j + 1) * (N : ℕ) := by
            simpa only [bad, not_or, not_exists, not_lt] using hbad
          have hsame := source_band_agrees j N (mem_Ioc.mp hn).1 hg.1 h hg.2
          simp only [hsame, sub_self, abs_zero, if_neg hbad, le_refl]
      _ = _ := Finset.sum_boole bad S
  exact he.trans (by exact_mod_cast band_boundary_count_le j N L h)

private theorem pattern_interval_count_eq_sub (j K M : ℕ) (hKM : K ≤ M)
    (h : Fin m → ℕ) (a : Fin m → ℝ) :
    (((Ioc K M).filter (fun n => ∀ i, moebiusBandMagnitude j (n + h i) = a i)).card : ℝ) =
      (moebiusBandPatternCount j M h a : ℝ) - moebiusBandPatternCount j K h a := by
  have h0 (X : ℕ) : Ioc 0 X = Icc 1 X := by
    ext n
    simp only [mem_Ioc, mem_Icc]
    omega
  have hs := sum_Ioc_consecutive
    (fun n => if ∀ i, moebiusBandMagnitude j (n + h i) = a i then (1 : ℝ) else 0)
      (Nat.zero_le K) hKM
  simp only [sum_boole, h0] at hs
  change (moebiusBandPatternCount j K h a : ℝ) + _ = moebiusBandPatternCount j M h a at hs
  linarith

private theorem scaled_pattern_count (j : ℕ) (h : Fin m → ℕ) (a : Fin m → ℝ)
    (A : ℝ) (hA : 0 ≤ A) :
    Tendsto (fun N : ℕ => (moebiusBandPatternCount j ⌊A * N⌋₊ h a : ℝ) / N) atTop
      (𝓝 (A * moebiusBandPatternDensity j h a)) := by
  rcases hA.eq_or_lt with hA | hA
  · rw [← hA]
    simp [moebiusBandPatternCount]
  have hf := tendsto_nat_floor_mul_atTop A hA
  have hr : Tendsto (fun N : ℕ => (⌊A * N⌋₊ : ℝ) / N) atTop (𝓝 A) :=
    (tendsto_nat_floor_mul_div_atTop hA.le).comp tendsto_natCast_atTop_atTop
  have hm := ((tendsto_moebiusBandPatternFrequency j h a).comp hf).mul hr
  have he : (fun N : ℕ => (moebiusBandPatternCount j ⌊A * N⌋₊ h a : ℝ) / ⌊A * N⌋₊ *
      ((⌊A * N⌋₊ : ℝ) / N)) =ᶠ[atTop]
      (fun N : ℕ => (moebiusBandPatternCount j ⌊A * N⌋₊ h a : ℝ) / N) := by
    filter_upwards [hf.eventually (eventually_ge_atTop 1)] with N hN
    have hne : (⌊A * N⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (show ⌊A * N⌋₊ ≠ 0 by omega)
    field_simp
  simpa only [mul_comm] using hm.congr' he

private theorem band_end_floor (j N : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    j * N + ⌊(t : ℝ) * N⌋₊ = ⌊((j : ℝ) + (t : ℝ)) * N⌋₊ := by
  have hnonneg : 0 ≤ (t : ℝ) * N := mul_nonneg t.property.1 (Nat.cast_nonneg N)
  rw [add_mul, add_comm ((j : ℝ) * N), ← Nat.cast_mul, Nat.floor_add_natCast hnonneg]
  omega

/-- Every fractional source band has the same shifted magnitude law, scaled by its length. -/
theorem tendsto_moebiusSourceMagnitudeBandPatternCount (j : ℕ)
    (t : Set.Icc (0 : ℝ) 1) (h : Fin m → ℕ) (a : Fin m → ℝ) :
    Tendsto (fun N : ℕ =>
      (moebiusSourceMagnitudeBandPatternCount j N ⌊(t : ℝ) * N⌋₊ h a : ℝ) / N) atTop
        (𝓝 ((t : ℝ) * moebiusBandPatternDensity j h a)) := by
  let f (N : ℕ) : ℝ :=
    (((Ioc (j * N) (j * N + ⌊(t : ℝ) * N⌋₊)).filter
      (fun n => ∀ i, moebiusBandMagnitude j (n + h i) = a i)).card : ℝ) / N
  have hmean : Tendsto f atTop (𝓝 ((t : ℝ) * moebiusBandPatternDensity j h a)) := by
    have hu := scaled_pattern_count j h a ((j : ℝ) + (t : ℝ))
      (add_nonneg (Nat.cast_nonneg _) t.property.1)
    have hl := scaled_pattern_count j h a (j : ℝ) (Nat.cast_nonneg _)
    have hh := hu.sub hl
    have he (N : ℕ) : f N =
        (moebiusBandPatternCount j ⌊((j : ℝ) + (t : ℝ)) * N⌋₊ h a : ℝ) / N -
          (moebiusBandPatternCount j ⌊(j : ℝ) * N⌋₊ h a : ℝ) / N := by
      dsimp [f]
      rw [pattern_interval_count_eq_sub j _ _ (Nat.le_add_right _ _) h a,
        sub_div, band_end_floor, ← Nat.cast_mul, Nat.floor_natCast]
    simp_rw [← he] at hh
    have hc : ((j : ℝ) + (t : ℝ)) * moebiusBandPatternDensity j h a -
        (j : ℝ) * moebiusBandPatternDensity j h a = (t : ℝ) * moebiusBandPatternDensity j h a := by ring
    rw [hc] at hh
    exact hh
  have hdiff : Tendsto (fun N : ℕ =>
      (moebiusSourceMagnitudeBandPatternCount j N ⌊(t : ℝ) * N⌋₊ h a : ℝ) / N - f N)
        atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => (1 + ∑ i, (h i : ℝ)) / N)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hL : ⌊(t : ℝ) * N⌋₊ ≤ N := by
        apply Nat.floor_le_of_le
        have := t.property.2
        have hNN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith
      have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have he := moebiusSourceMagnitudeBandPatternCount_error j ⟨N, by omega⟩
        ⟨⌊(t : ℝ) * N⌋₊, by change ⌊(t : ℝ) * N⌋₊ < N + 1; omega⟩ h a
      dsimp [f]
      rw [← sub_div, abs_div, abs_of_pos hNr]
      exact (div_le_div_iff_of_pos_right hNr).mpr he
    · exact tendsto_const_div_atTop_nhds_zero_nat _
  have hh := hdiff.add hmean
  simpa only [sub_add_cancel, zero_add] using hh

/-- Literal joint magnitude-pattern count in a finite source prefix. -/
def moebiusSourceMagnitudePatternCount (N M : ℕ) (h : Fin m → ℕ) (a : Fin m → ℝ) : ℕ :=
  ((Icc 1 M).filter (fun n => ∀ i, |sieveSeq N moebiusReal (n + h i)| = a i)).card

/-- Raw joint magnitude mass at a real horizon between adjacent integers. -/
def cofinalMobiusJointMagnitudeMass (K : ℕ) (t : Set.Icc (0 : ℝ) 1)
    (h : Fin m → ℕ) (a : Fin m → ℝ) : ℝ :=
  (∑ j ∈ range K, moebiusBandPatternDensity j h a) +
    (t : ℝ) * moebiusBandPatternDensity K h a

private theorem source_prefix_split (N K M : ℕ) (hKM : K ≤ M)
    (h : Fin m → ℕ) (a : Fin m → ℝ) :
    moebiusSourceMagnitudePatternCount N M h a = moebiusSourceMagnitudePatternCount N K h a +
      ((Ioc K M).filter (fun n => ∀ i, |sieveSeq N moebiusReal (n + h i)| = a i)).card := by
  have h0 (X : ℕ) : Ioc 0 X = Icc 1 X := by
    ext n
    simp only [mem_Ioc, mem_Icc]
    omega
  have hs := sum_Ioc_consecutive
    (fun n => if ∀ i, |sieveSeq N moebiusReal (n + h i)| = a i then (1 : ℕ) else 0)
      (Nat.zero_le K) hKM
  simpa only [sum_boole, Nat.cast_id, h0, moebiusSourceMagnitudePatternCount] using hs.symm

private theorem source_prefix_band_partition (K N L : ℕ)
    (h : Fin m → ℕ) (a : Fin m → ℝ) :
    moebiusSourceMagnitudePatternCount N (K * N + L) h a =
      (∑ j ∈ range K, moebiusSourceMagnitudeBandPatternCount j N N h a) +
        moebiusSourceMagnitudeBandPatternCount K N L h a := by
  have hwhole (K : ℕ) : moebiusSourceMagnitudePatternCount N (K * N) h a =
      ∑ j ∈ range K, moebiusSourceMagnitudeBandPatternCount j N N h a := by
    induction K with
    | zero => simp [moebiusSourceMagnitudePatternCount]
    | succ K ih =>
      rw [Finset.sum_range_succ, Nat.succ_mul]
      simpa only [ih, moebiusSourceMagnitudeBandPatternCount] using
        source_prefix_split N (K * N) (K * N + N) (Nat.le_add_right _ _) h a
  simpa only [hwhole, moebiusSourceMagnitudeBandPatternCount] using
    source_prefix_split N (K * N) (K * N + L) (Nat.le_add_right _ _) h a

/-- Joint magnitude masses interpolate affinely between successive integer source horizons. -/
theorem tendsto_moebiusSourceMagnitudePatternCount (K : ℕ)
    (t : Set.Icc (0 : ℝ) 1) (h : Fin m → ℕ) (a : Fin m → ℝ) :
    Tendsto (fun N : ℕ =>
      (moebiusSourceMagnitudePatternCount N ⌊((K : ℝ) + (t : ℝ)) * N⌋₊ h a : ℝ) / N)
      atTop (𝓝 (cofinalMobiusJointMagnitudeMass K t h a)) := by
  have hfull (j : ℕ) : Tendsto (fun N : ℕ =>
      (moebiusSourceMagnitudeBandPatternCount j N N h a : ℝ) / N) atTop
        (𝓝 (moebiusBandPatternDensity j h a)) := by
    simpa using tendsto_moebiusSourceMagnitudeBandPatternCount j ⟨1, by norm_num⟩ h a
  have hh := (tendsto_finsetSum (range K) (fun j _ => hfull j)).add
    (tendsto_moebiusSourceMagnitudeBandPatternCount K t h a)
  have he (N : ℕ) :
      (moebiusSourceMagnitudePatternCount N ⌊((K : ℝ) + (t : ℝ)) * N⌋₊ h a : ℝ) / N =
      (∑ j ∈ range K, (moebiusSourceMagnitudeBandPatternCount j N N h a : ℝ) / N) +
        (moebiusSourceMagnitudeBandPatternCount K N ⌊(t : ℝ) * N⌋₊ h a : ℝ) / N := by
    rw [← band_end_floor, source_prefix_band_partition]
    push_cast
    rw [add_div, sum_div]
  simpa only [← he, cofinalMobiusJointMagnitudeMass] using hh

/-- Normalized joint magnitude law for every real source horizon at least one. -/
def cofinalMobiusJointMagnitudeDensity (K : ℕ+) (t : Set.Icc (0 : ℝ) 1)
    (h : Fin m → ℕ) (a : Fin m → ℝ) : ℝ :=
  cofinalMobiusJointMagnitudeMass K t h a / ((K : ℝ) + (t : ℝ))

/-- Literal finite-prefix joint magnitude frequencies converge to the explicit band mixture. -/
theorem tendsto_moebiusSourceMagnitudePatternFrequency (K : ℕ+)
    (t : Set.Icc (0 : ℝ) 1) (h : Fin m → ℕ) (a : Fin m → ℝ) :
    Tendsto (fun N : ℕ =>
      (moebiusSourceMagnitudePatternCount N ⌊((K : ℝ) + (t : ℝ)) * N⌋₊ h a : ℝ) /
        ⌊((K : ℝ) + (t : ℝ)) * N⌋₊) atTop
      (𝓝 (cofinalMobiusJointMagnitudeDensity K t h a)) := by
  have hA : 0 < (K : ℝ) + (t : ℝ) := add_pos_of_pos_of_nonneg
    (by exact_mod_cast K.pos) t.property.1
  have hden : Tendsto (fun N : ℕ => (⌊((K : ℝ) + (t : ℝ)) * N⌋₊ : ℝ) / N) atTop
      (𝓝 ((K : ℝ) + (t : ℝ))) :=
    (tendsto_nat_floor_mul_div_atTop hA.le).comp tendsto_natCast_atTop_atTop
  have hh := (tendsto_moebiusSourceMagnitudePatternCount K t h a).div hden (ne_of_gt hA)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  change ((moebiusSourceMagnitudePatternCount N ⌊((K : ℝ) + (t : ℝ)) * N⌋₊ h a : ℝ) / N) /
      ((⌊((K : ℝ) + (t : ℝ)) * N⌋₊ : ℝ) / N) =
    (moebiusSourceMagnitudePatternCount N ⌊((K : ℝ) + (t : ℝ)) * N⌋₊ h a : ℝ) /
      ⌊((K : ℝ) + (t : ℝ)) * N⌋₊
  field_simp [hNr]

private theorem sum_band_density_upto (K j : ℕ) (hj : j ≤ K) (h : Fin m → ℕ) :
    ∑ a : Fin m → Fin (K + 1), moebiusBandPatternDensity j h (fun i => ((a i : ℕ) : ℝ)) = 1 := by
  let e (b : Fin m → Fin (j + 1)) : Fin m → Fin (K + 1) :=
    fun i => ⟨b i, lt_of_lt_of_le (b i).isLt (Nat.add_le_add_right hj 1)⟩
  have hinj : Function.Injective e := by
    intro b c hbc
    funext i
    apply Fin.ext
    exact congrArg (fun q : Fin (K + 1) => q.val) (congrFun hbc i)
  let F (a : Fin m → Fin (K + 1)) := moebiusBandPatternDensity j h (fun i => ((a i : ℕ) : ℝ))
  have hout (a : Fin m → Fin (K + 1)) (ha : a ∉ univ.image e) : F a = 0 := by
    by_contra hd
    obtain ⟨b, hb⟩ := (moebiusBandPatternDensity_support j h (fun i => ((a i : ℕ) : ℝ))).resolve_left hd
    have heq : e b = a := by
      funext i
      apply Fin.ext
      exact_mod_cast (hb i).symm
    exact ha (mem_image.mpr ⟨b, mem_univ _, heq⟩)
  have hs : (∑ a ∈ univ.image e, F a) = ∑ a, F a :=
    Finset.sum_subset (subset_univ _) (fun a _ ha => hout a ha)
  calc
    _ = ∑ a ∈ univ.image e, F a := hs.symm
    _ = ∑ b : Fin m → Fin (j + 1), moebiusBandPatternDensity j h (fun i => ((b i : ℕ) : ℝ)) := by
      rw [Finset.sum_image (fun _ _ _ _ hbc => hinj hbc)]
    _ = 1 := sum_moebiusBandPatternDensity j h

/-- Every normalized real-horizon joint magnitude law has total mass one. -/
theorem sum_cofinalMobiusJointMagnitudeDensity (K : ℕ+) (t : Set.Icc (0 : ℝ) 1)
    (h : Fin m → ℕ) :
    ∑ a : Fin m → Fin ((K : ℕ) + 1),
      cofinalMobiusJointMagnitudeDensity K t h (fun i => ((a i : ℕ) : ℝ)) = 1 := by
  have hmass : (∑ a : Fin m → Fin ((K : ℕ) + 1),
      cofinalMobiusJointMagnitudeMass K t h (fun i => ((a i : ℕ) : ℝ))) = (K : ℝ) + (t : ℝ) := by
    unfold cofinalMobiusJointMagnitudeMass
    rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
    have hs : (∑ j ∈ range (K : ℕ), ∑ a : Fin m → Fin ((K : ℕ) + 1),
        moebiusBandPatternDensity j h (fun i => ((a i : ℕ) : ℝ))) = (K : ℝ) := by
      calc
        _ = ∑ _j ∈ range (K : ℕ), (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact sum_band_density_upto K j (Nat.le_of_lt (mem_range.mp hj)) h
        _ = _ := by simp
    rw [hs, sum_moebiusBandPatternDensity, mul_one]
  unfold cofinalMobiusJointMagnitudeDensity
  rw [← Finset.sum_div, hmass]
  apply div_self
  have hK : (0 : ℝ) < K := by exact_mod_cast K.pos
  exact ne_of_gt (add_pos_of_pos_of_nonneg hK t.property.1)

/-- Joint magnitude probabilities are nonnegative without any correlation hypothesis. -/
theorem cofinalMobiusJointMagnitudeDensity_nonneg (K : ℕ+) (t : Set.Icc (0 : ℝ) 1)
    (h : Fin m → ℕ) (a : Fin m → ℝ) :
    0 ≤ cofinalMobiusJointMagnitudeDensity K t h a := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (tendsto_moebiusSourceMagnitudePatternFrequency K t h a)
  exact Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The real-horizon joint law has finite support in the nonnegative integer magnitude alphabet. -/
theorem cofinalMobiusJointMagnitudeDensity_support (K : ℕ+) (t : Set.Icc (0 : ℝ) 1)
    (h : Fin m → ℕ) (a : Fin m → ℝ) :
    cofinalMobiusJointMagnitudeDensity K t h a = 0 ∨
      ∃ b : Fin m → Fin ((K : ℕ) + 1), ∀ i, a i = ((b i : ℕ) : ℝ) := by
  by_cases ha : ∃ b : Fin m → Fin ((K : ℕ) + 1), ∀ i, a i = ((b i : ℕ) : ℝ)
  · exact Or.inr ha
  left
  have hz (j : ℕ) (hj : j ≤ K) : moebiusBandPatternDensity j h a = 0 := by
    by_contra hd
    obtain ⟨b, hb⟩ := (moebiusBandPatternDensity_support j h a).resolve_left hd
    exact ha ⟨fun i => ⟨b i, lt_of_lt_of_le (b i).isLt (Nat.add_le_add_right hj 1)⟩, hb⟩
  have hs : (∑ j ∈ range (K : ℕ), moebiusBandPatternDensity j h a) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact hz j (Nat.le_of_lt (mem_range.mp hj))
  simp only [cofinalMobiusJointMagnitudeDensity, cofinalMobiusJointMagnitudeMass,
    hs, hz K le_rfl, mul_zero, add_zero, zero_div]

end
end GaloisForLFunctions.BezoutValuationIncidence

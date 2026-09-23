import GaloisForLFunctions.HTGeometry.ThermodynamicPathFieldSelection

/-!
# Absolute summability of the selected thermodynamic path field

The one countable onsite-plus-edge Pauli field selected around the nested inverse-power center is
absolutely summable.  Quantitative inverse-square majorants are proved separately for onsite and
edge shells, then assembled across the sum/product label space.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem nestedInfiniteEdgeWeight_le_inverseSquare (e : ℕ) :
    nestedInfiniteEdgeWeight e ≤ 4 / (((e + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  unfold nestedInfiniteEdgeWeight
  split_ifs with he
  · rcases he with ⟨m, rfl⟩
    have hdiv : (m + m) / 2 = m := by omega
    rw [hdiv]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [show (0 : ℝ) ≤ m by positivity]
  · have hnat : e + 1 ≤ 2 * (e / 2 + 2) := by omega
    have hreal : ((e + 1 : ℕ) : ℝ) ≤ 2 * ((e / 2 + 2 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hbaseNat : 1 ≤ e / 2 + 2 := by omega
    have hbase : (1 : ℝ) ≤ ((e / 2 + 2 : ℕ) : ℝ) := by
      exact_mod_cast hbaseNat
    let x : ℝ := ((e / 2 + 2 : ℕ) : ℝ)
    let y : ℝ := ((e + 1 : ℕ) : ℝ)
    have hx0 : 0 ≤ x := by positivity
    have hy0 : 0 ≤ y := by positivity
    have hxy : y ≤ 2 * x := by simpa [x, y] using hreal
    have hySq : y ^ (2 : ℕ) ≤ 4 * x ^ (2 : ℕ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy)
        (add_nonneg hy0 (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hx0))]
    have hxSq : x ^ (2 : ℕ) ≤ x ^ (4 : ℕ) := by
      have hxSqOne : 1 ≤ x ^ (2 : ℕ) := one_le_pow₀ (by simpa [x] using hbase)
      nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hxSqOne)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simpa [x, y] using hySq.trans (mul_le_mul_of_nonneg_left hxSq (by norm_num))

theorem nestedInfiniteEdgeWeight_nonneg_thermodynamicPathCoefficientSummability (e : ℕ) :
    0 ≤ nestedInfiniteEdgeWeight e := by
  unfold nestedInfiniteEdgeWeight
  split_ifs <;> positivity

theorem infinitePathRadius_le_inverseSquare (i : InfinitePathLabel) :
    infinitePathRadius i ≤ 1 / ((((i.elim Prod.fst Prod.fst) + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  rcases i with ⟨s, q⟩ | ⟨e, ab⟩
  · change 1 / (1000000 * (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ))) ≤
      1 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ))
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (((s + 1 : ℕ) : ℝ))]
  · change 1 / (1000000 * (((e + 1 : ℕ) : ℝ) ^ (2 : ℕ))) ≤
      1 / (((e + 1 : ℕ) : ℝ) ^ (2 : ℕ))
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (((e + 1 : ℕ) : ℝ))]

theorem nestedInfinitePathCenter_onsite_abs_le
    (s : ℕ) (q : Fin 3) :
    |nestedInfinitePathCenter (Sum.inl (s, q))| ≤
      5 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  change |if q = 2 then
    -(nestedInfiniteEdgeWeight s +
      if s = 0 then 0 else nestedInfiniteEdgeWeight (s - 1)) / 4 else 0| ≤ _
  by_cases hq : q = 2
  · rw [if_pos hq]
    have hw0 := nestedInfiniteEdgeWeight_nonneg_thermodynamicPathCoefficientSummability s
    have hw := nestedInfiniteEdgeWeight_le_inverseSquare s
    by_cases hs : s = 0
    · subst s
      rw [if_pos rfl, add_zero,
        show -nestedInfiniteEdgeWeight 0 / 4 = -(nestedInfiniteEdgeWeight 0 / 4) by ring,
        abs_neg, abs_of_nonneg (div_nonneg hw0 (by norm_num))]
      norm_num at hw ⊢
      linarith
    · have hspos : 0 < s := Nat.pos_of_ne_zero hs
      have hwPrev0 := nestedInfiniteEdgeWeight_nonneg_thermodynamicPathCoefficientSummability (s - 1)
      have hwPrev := nestedInfiniteEdgeWeight_le_inverseSquare (s - 1)
      have hsCast : (1 : ℝ) ≤ s := by exact_mod_cast hspos
      have hcompare : (1 : ℝ) / (s : ℝ) ^ (2 : ℕ) ≤
          4 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        push_cast
        nlinarith
      have hwPrev' : nestedInfiniteEdgeWeight (s - 1) ≤
          4 / (s : ℝ) ^ (2 : ℕ) := by
        have hnat : s - 1 + 1 = s := by omega
        simpa [hnat] using hwPrev
      have hwPrevFinal : nestedInfiniteEdgeWeight (s - 1) ≤
          16 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
        calc
          nestedInfiniteEdgeWeight (s - 1) ≤ 4 / (s : ℝ) ^ (2 : ℕ) := hwPrev'
          _ = 4 * (1 / (s : ℝ) ^ (2 : ℕ)) := by ring
          _ ≤ 4 * (4 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ))) :=
            mul_le_mul_of_nonneg_left hcompare (by norm_num)
          _ = 16 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by ring
      rw [if_neg hs,
        show -(nestedInfiniteEdgeWeight s + nestedInfiniteEdgeWeight (s - 1)) / 4 =
          -((nestedInfiniteEdgeWeight s + nestedInfiniteEdgeWeight (s - 1)) / 4) by ring,
        abs_neg, abs_of_nonneg (div_nonneg (add_nonneg hw0 hwPrev0) (by norm_num))]
      calc
        (nestedInfiniteEdgeWeight s + nestedInfiniteEdgeWeight (s - 1)) / 4 ≤
            (4 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) +
              16 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ))) / 4 :=
          div_le_div_of_nonneg_right (add_le_add hw hwPrevFinal) (by norm_num)
        _ = 5 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by ring
  · rw [if_neg hq, abs_zero]
    positivity

theorem nestedInfinitePathCenter_edge_abs_le
    (e : ℕ) (ab : Fin 3 × Fin 3) :
    |nestedInfinitePathCenter (Sum.inr (e, ab))| ≤
      1 / (((e + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  change |if ab = ((2 : Fin 3), (2 : Fin 3)) then
    nestedInfiniteEdgeWeight e / 4 else 0| ≤ _
  by_cases hab : ab = ((2 : Fin 3), (2 : Fin 3))
  · rw [if_pos hab,
      abs_of_nonneg (div_nonneg (nestedInfiniteEdgeWeight_nonneg_thermodynamicPathCoefficientSummability e) (by norm_num))]
    have hw := nestedInfiniteEdgeWeight_le_inverseSquare e
    calc
      nestedInfiniteEdgeWeight e / 4 ≤
          (4 / (((e + 1 : ℕ) : ℝ) ^ (2 : ℕ))) / 4 :=
        div_le_div_of_nonneg_right hw (by norm_num)
      _ = 1 / (((e + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by ring
  · rw [if_neg hab, abs_zero]
    positivity

theorem selectedPath_onsite_abs_le
    {p : InfinitePathLabel → ℝ}
    (hp : ∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i)
    (s : ℕ) (q : Fin 3) :
    |p (Sum.inl (s, q))| ≤ 6 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  let i : InfinitePathLabel := Sum.inl (s, q)
  have hdiff : |p i - nestedInfinitePathCenter i| ≤ infinitePathRadius i :=
    (hp i).le
  have hradius : infinitePathRadius i ≤ 1 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
    simpa [i] using infinitePathRadius_le_inverseSquare i
  have hcenter := nestedInfinitePathCenter_onsite_abs_le s q
  calc
    |p i| = |(p i - nestedInfinitePathCenter i) + nestedInfinitePathCenter i| := by ring_nf
    _ ≤ |p i - nestedInfinitePathCenter i| + |nestedInfinitePathCenter i| := abs_add_le _ _
    _ ≤ infinitePathRadius i + 5 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
      add_le_add hdiff hcenter
    _ ≤ 1 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) +
        5 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
      add_le_add hradius le_rfl
    _ = 6 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by ring

theorem selectedPath_edge_abs_le
    {p : InfinitePathLabel → ℝ}
    (hp : ∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i)
    (e : ℕ) (ab : Fin 3 × Fin 3) :
    |p (Sum.inr (e, ab))| ≤ 2 / (((e + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  let i : InfinitePathLabel := Sum.inr (e, ab)
  have hdiff : |p i - nestedInfinitePathCenter i| ≤ infinitePathRadius i :=
    (hp i).le
  have hradius : infinitePathRadius i ≤ 1 / (((e + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
    simpa [i] using infinitePathRadius_le_inverseSquare i
  have hcenter := nestedInfinitePathCenter_edge_abs_le e ab
  calc
    |p i| = |(p i - nestedInfinitePathCenter i) + nestedInfinitePathCenter i| := by ring_nf
    _ ≤ |p i - nestedInfinitePathCenter i| + |nestedInfinitePathCenter i| := abs_add_le _ _
    _ ≤ infinitePathRadius i + 1 / (((e + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
      add_le_add hdiff hcenter
    _ ≤ 1 / (((e + 1 : ℕ) : ℝ) ^ (2 : ℕ)) +
        1 / (((e + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
      add_le_add hradius le_rfl
    _ = 2 / (((e + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by ring

def selectedPathOnsiteMass (p : InfinitePathLabel → ℝ) (s : ℕ) : ℝ :=
  ∑ q : Fin 3, |p (Sum.inl (s, q))|

def selectedPathEdgeMass (p : InfinitePathLabel → ℝ) (e : ℕ) : ℝ :=
  ∑ ab : Fin 3 × Fin 3, |p (Sum.inr (e, ab))|

theorem selectedPathOnsiteMass_le
    {p : InfinitePathLabel → ℝ}
    (hp : ∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i)
    (s : ℕ) :
    selectedPathOnsiteMass p s ≤
      18 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  unfold selectedPathOnsiteMass
  calc
    ∑ q : Fin 3, |p (Sum.inl (s, q))| ≤
        ∑ _q : Fin 3, 6 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
      Finset.sum_le_sum fun q _ => selectedPath_onsite_abs_le hp s q
    _ = 18 / (((s + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by simp; ring

theorem selectedPathEdgeMass_le
    {p : InfinitePathLabel → ℝ}
    (hp : ∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i)
    (e : ℕ) :
    selectedPathEdgeMass p e ≤
      18 / (((e + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  unfold selectedPathEdgeMass
  calc
    ∑ ab : Fin 3 × Fin 3, |p (Sum.inr (e, ab))| ≤
        ∑ _ab : Fin 3 × Fin 3, 2 / (((e + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
      Finset.sum_le_sum fun ab _ => selectedPath_edge_abs_le hp e ab
    _ = 18 / (((e + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by simp; ring

theorem summable_pathShiftedInverseSquare :
    Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ))) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).2 hbase
  simpa [Nat.add_comm] using hshift

theorem summable_selectedPathOnsiteMass
    {p : InfinitePathLabel → ℝ}
    (hp : ∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i) :
    Summable (selectedPathOnsiteMass p) := by
  apply Summable.of_nonneg_of_le
    (fun s => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (selectedPathOnsiteMass_le hp)
  simpa [div_eq_mul_inv] using
    summable_pathShiftedInverseSquare.mul_left 18

theorem summable_selectedPathEdgeMass
    {p : InfinitePathLabel → ℝ}
    (hp : ∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i) :
    Summable (selectedPathEdgeMass p) := by
  apply Summable.of_nonneg_of_le
    (fun e => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (selectedPathEdgeMass_le hp)
  simpa [div_eq_mul_inv] using
    summable_pathShiftedInverseSquare.mul_left 18

theorem summable_abs_selectedPathCoefficient
    {p : InfinitePathLabel → ℝ}
    (hp : ∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i) :
    Summable (fun i => |p i|) := by
  have hOn : Summable (fun sq : ℕ × Fin 3 => |p (Sum.inl sq)|) := by
    apply (summable_prod_of_nonneg fun _ => abs_nonneg _).2
    refine ⟨fun _ => summable_of_hasFiniteSupport (Set.toFinite _), ?_⟩
    convert summable_selectedPathOnsiteMass hp using 1
    funext s
    rw [selectedPathOnsiteMass, tsum_fintype]
  have hEdge : Summable (fun eab : ℕ × (Fin 3 × Fin 3) => |p (Sum.inr eab)|) := by
    apply (summable_prod_of_nonneg fun _ => abs_nonneg _).2
    refine ⟨fun _ => summable_of_hasFiniteSupport (Set.toFinite _), ?_⟩
    convert summable_selectedPathEdgeMass hp using 1
    funext e
    rw [selectedPathEdgeMass, tsum_fintype]
  exact Summable.sum (fun i => |p i|)
    (by simpa [Function.comp_def] using hOn)
    (by simpa [Function.comp_def] using hEdge)

/-- One field is simultaneously nested-centered, projective on every finite prefix, and absolutely
summable across all onsite and edge Pauli coordinates. -/
theorem exists_nestedCentered_allPrefixes_projective_summable :
    ∃ p : InfinitePathLabel → ℝ,
      (∀ i, |p i - nestedInfinitePathCenter i| < infinitePathRadius i) ∧
      (∀ k, coefficientRestrict (numberedPathToInfinite k) p ∈ chainProjectiveGood k) ∧
      Summable (fun i => |p i|) := by
  obtain ⟨p, hpclose, hpgood⟩ := exists_nestedCentered_allPrefixes_projective
  exact ⟨p, hpclose, hpgood, summable_abs_selectedPathCoefficient hpclose⟩

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.InfiniteRankWeilTheory.WellFoundedTowersSelfImprove
import GaloisForLFunctions.HTGeometry.PositiveWolffMeasure

/-!
# Well-foundedness is necessary: Wolff towers

The infinite-rank Hasse–Weil principle (`WeilTower.mergedWeight_eq_zero_of_norm_ne_one`) assumes
that the outer part of the tower is well-founded — finitely many modes above every radius `> 1`, the
tower form of ZAL. The hypothesis cannot be dropped, not even with positive weights and full symmetry.

A positive Wolff measure on the annulus `3/2 < |z| < 2` (`HTGeometry.PositiveWolffMeasure`) is a
countable family of points with positive summable weights whose moments `Σ c_x x^k` and `Σ c_x x^{−k}`
vanish for every `k ≥ 1`. Closing it under conjugation and under `z ↦ 1/z̄` gives the **Wolff tower**
(`wolffTower`): a Weil tower with positive real weights compatible with the reflection, every mode off
the unit circle, outer modes accumulating at radius `2`, and level sums vanishing at every nonzero level
(`levelSum_wolffTower_eq_zero`). So:

* `not_wellFoundedAbove_wolffTower`: its outer part is not well-founded;
* `exists_tower_bounded_without_wellFounded`: its level sums are bounded at every level, while every
  mode off the circle has positive merged weight. The conclusion of the infinite-rank Hasse–Weil
  principle fails.

What excludes such a tower for `ζ` is not positivity of the weights (the Wolff weights are positive)
but the arithmetic of the zeros: ZAL, or the continuous family of towers over all bases, whose lag
determines the zero abscissa (`TheCrudeStepAndTheCount`).
-/

open Complex GaloisForLFunctions.HTGeometry.PositiveWolffMeasure

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- The base point `x` or `x̄`. -/
def wolffBase (c : Bool) (x : ℂ) : ℂ := if c then starRingEnd ℂ x else x

/-- A mode of the Wolff tower: outer `x, x̄`, inner `1/x̄, 1/x`. -/
def wolffMode (o c : Bool) (x : ℂ) : ℂ :=
  if o then wolffBase c x else (starRingEnd ℂ (wolffBase c x))⁻¹

theorem norm_wolffBase (c : Bool) (x : ℂ) : ‖wolffBase c x‖ = ‖x‖ := by
  cases c <;> simp [wolffBase]

/-- The Wolff tower built from a positive Wolff family `t` with weights `w`. -/
def wolffTower (t : Set ℂ) (ht : ∀ x ∈ t, x ≠ 0) : WeilTower ((Bool × Bool) × t) where
  z p := wolffMode p.1.1 p.1.2 p.2
  conjPerm := Equiv.prodCongr (Equiv.prodCongr (Equiv.refl Bool)
    (Function.Involutive.toPerm _ Bool.not_not)) (Equiv.refl t)
  z_conjPerm p := by
    obtain ⟨⟨o, c⟩, x⟩ := p
    cases o <;> cases c <;>
      simp [wolffMode, wolffBase, Equiv.prodCongr_apply, Function.Involutive.coe_toPerm]
  invPerm := Equiv.prodCongr (Equiv.prodCongr (Function.Involutive.toPerm _ Bool.not_not)
    (Function.Involutive.toPerm _ Bool.not_not)) (Equiv.refl t)
  z_invPerm p := by
    obtain ⟨⟨o, c⟩, x⟩ := p
    have hx : (x : ℂ) ≠ 0 := ht x x.2
    have hxc : starRingEnd ℂ (x : ℂ) ≠ 0 := (map_ne_zero _).mpr hx
    cases o <;> cases c <;>
      simp [wolffMode, wolffBase, Equiv.prodCongr_apply, Function.Involutive.coe_toPerm, hx, hxc]

/-- The data of a positive Wolff family on `3/2 < |z| < 2`. -/
theorem exists_wolff_family :
    ∃ (t : Set ℂ) (c : ℂ → ℝ), t ⊆ annulus (3 / 2) 2 ∧ (∀ x ∈ t, 0 < c x) ∧
      (∀ R' < 2, ∃ x ∈ t, R' < ‖x‖) ∧ Summable (fun x : t => c x) ∧
      (∀ k : ℕ, 1 ≤ k → HasSum (fun x : t => (c x : ℂ) * (x : ℂ) ^ k) 0) ∧
      (∀ k : ℕ, 1 ≤ k → HasSum (fun x : t => (c x : ℂ) * ((x : ℂ) ^ k)⁻¹) 0) := by
  obtain ⟨t, c, -, htA, hc, hacc, hsum, hpos, hneg⟩ :=
    exists_positive_wolff_annulus (r := 3 / 2) (R := 2) (by norm_num) (by norm_num)
  exact ⟨t, c, htA, hc, hacc, hsum.summable, hpos, hneg (by norm_num)⟩

theorem norm_mem_annulus {x : ℂ} (hx : x ∈ annulus (3 / 2) 2) : 3 / 2 < ‖x‖ ∧ ‖x‖ < 2 := hx

theorem ne_zero_of_mem_annulus {x : ℂ} (hx : x ∈ annulus (3 / 2) 2) : x ≠ 0 := by
  intro h
  have := (norm_mem_annulus hx).1
  rw [h, norm_zero] at this
  norm_num at this

theorem norm_wolffMode {o c : Bool} {x : ℂ} (hx : x ∈ annulus (3 / 2) 2) :
    (o = true → 3 / 2 < ‖wolffMode o c x‖ ∧ ‖wolffMode o c x‖ < 2) ∧
      (o = false → ‖wolffMode o c x‖ < 2 / 3) := by
  obtain ⟨h1, h2⟩ := norm_mem_annulus hx
  refine ⟨fun ho => ?_, fun ho => ?_⟩
  · subst ho; simp only [wolffMode, if_true, norm_wolffBase]; exact ⟨h1, h2⟩
  · subst ho
    simp only [wolffMode, Bool.false_eq_true, if_false, norm_inv, Complex.norm_conj,
      norm_wolffBase]
    rw [inv_lt_comm₀ (by linarith) (by norm_num)]
    linarith

theorem norm_wolffMode_lt_two (o c : Bool) {x : ℂ} (hx : x ∈ annulus (3 / 2) 2) :
    ‖wolffMode o c x‖ < 2 := by
  cases o
  · have := (norm_wolffMode (o := false) (c := c) hx).2 rfl; linarith
  · exact ((norm_wolffMode (o := true) (c := c) hx).1 rfl).2

theorem norm_wolffMode_ne_one (o c : Bool) {x : ℂ} (hx : x ∈ annulus (3 / 2) 2) :
    ‖wolffMode o c x‖ ≠ 1 := by
  intro h
  cases o
  · have := (norm_wolffMode (o := false) (c := c) hx).2 rfl; linarith
  · have := ((norm_wolffMode (o := true) (c := c) hx).1 rfl).1; linarith

/-- **The Wolff tower is invisible.** Its level sums vanish at every level `ν ≥ 1`. -/
theorem levelSum_wolffTower_eq_zero {t : Set ℂ} {c : ℂ → ℝ} (htA : t ⊆ annulus (3 / 2) 2)
    (hc : ∀ x ∈ t, 0 < c x) (hsum : Summable (fun x : t => c x))
    (hpos : ∀ k : ℕ, 1 ≤ k → HasSum (fun x : t => (c x : ℂ) * (x : ℂ) ^ k) 0)
    (hneg : ∀ k : ℕ, 1 ≤ k → HasSum (fun x : t => (c x : ℂ) * ((x : ℂ) ^ k)⁻¹) 0)
    {ν : ℕ} (hν : 1 ≤ ν) :
    levelSum (wolffTower t fun _ hx => ne_zero_of_mem_annulus (htA hx)).z
      (fun p => (c p.2 : ℂ)) ν = 0 := by
  set f : (Bool × Bool) × t → ℂ := fun p => (c p.2 : ℂ) * wolffMode p.1.1 p.1.2 p.2 ^ (ν : ℤ)
    with hf
  have hbound : ∀ p, ‖f p‖ ≤ c p.2 * 2 ^ ν := by
    rintro ⟨⟨o, c'⟩, x⟩
    have hcp := (hc x x.2).le
    simp only [hf]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcp, zpow_natCast, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_wolffMode_lt_two o c' (htA x.2)).le ν) hcp
  have hsumP : Summable fun p : (Bool × Bool) × t => c (p.2 : ℂ) :=
    (summable_prod_of_nonneg (f := fun p : (Bool × Bool) × t => c (p.2 : ℂ))
      fun p => (hc p.2 p.2.2).le).2 ⟨fun _ => hsum, Summable.of_finite⟩
  have hfs : Summable f := Summable.of_norm_bounded (hsumP.mul_right _) hbound
  have hslice : ∀ oc : Bool × Bool, Summable fun x : t => f (oc, x) := fun oc =>
    hfs.comp_injective (Prod.mk_right_injective oc)
  have e1 : ∀ x : t, f ((true, false), x) = (c x : ℂ) * (x : ℂ) ^ ν := fun x => by
    simp [hf, wolffMode, wolffBase]
  have e2 : ∀ x : t, f ((true, true), x) = starRingEnd ℂ ((c x : ℂ) * (x : ℂ) ^ ν) := fun x => by
    simp [hf, wolffMode, wolffBase]
  have e3 : ∀ x : t, f ((false, true), x) = (c x : ℂ) * ((x : ℂ) ^ ν)⁻¹ := fun x => by
    simp [hf, wolffMode, wolffBase]
  have e4 : ∀ x : t, f ((false, false), x) = starRingEnd ℂ ((c x : ℂ) * ((x : ℂ) ^ ν)⁻¹) :=
    fun x => by simp [hf, wolffMode, wolffBase]
  unfold levelSum
  change ∑' p, f p = 0
  rw [hfs.tsum_prod' hslice, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool,
    Fintype.sum_bool, Fintype.sum_bool]
  simp only [e1, e2, e3, e4, ← conj_tsum, (hpos ν hν).tsum_eq, (hneg ν hν).tsum_eq, map_zero,
    add_zero]

/-- **The Wolff tower.** A Weil tower with positive real weights compatible with the reflection,
every mode off the unit circle, outer modes accumulating at radius `2`, and level sums vanishing at
every level `ν ≥ 1`. -/
theorem exists_wolff_tower :
    ∃ (ι : Type) (T : WeilTower ι) (b : ι → ℂ), Summable (fun i => ‖b i‖) ∧
      (∀ i, b (T.reflPerm i) = starRingEnd ℂ (b i)) ∧ (∀ i, 0 < (b i).re ∧ (b i).im = 0) ∧
      (∀ i, ‖T.z i‖ ≠ 1) ∧ (∀ i, ‖T.z i‖ < 2) ∧ (∀ R' < 2, ∃ i, R' < ‖T.z i‖) ∧
      ∀ ν : ℕ, 1 ≤ ν → levelSum T.z b ν = 0 := by
  obtain ⟨t, c, htA, hc, hacc, hsum, hpos, hneg⟩ := exists_wolff_family
  refine ⟨(Bool × Bool) × t, wolffTower t fun _ hx => ne_zero_of_mem_annulus (htA hx),
    fun p => (c p.2 : ℂ), ?_, fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_,
    fun R' hR' => ?_, fun ν hν => levelSum_wolffTower_eq_zero htA hc hsum hpos hneg hν⟩
  · refine (summable_prod_of_nonneg fun p => norm_nonneg _).2 ⟨fun _ => ?_, Summable.of_finite⟩
    exact hsum.congr fun x => by
      rw [Complex.norm_real, Real.norm_of_nonneg (hc x x.2).le]
  · show (c (WeilTower.reflPerm _ p).2 : ℂ) = starRingEnd ℂ (c p.2 : ℂ)
    rw [Complex.conj_ofReal]
    rfl
  · exact ⟨by simpa using hc p.2 p.2.2, by simp⟩
  · exact norm_wolffMode_ne_one p.1.1 p.1.2 (htA p.2.2)
  · exact norm_wolffMode_lt_two p.1.1 p.1.2 (htA p.2.2)
  · obtain ⟨x, hx, hRx⟩ := hacc R' hR'
    exact ⟨((true, false), ⟨x, hx⟩), by simpa [wolffTower, wolffMode, wolffBase] using hRx⟩

/-- Modes of modulus `< 2` accumulating at `2` are not well-founded above `1`. -/
theorem not_wellFoundedAbove_of_accumulates {ι : Type*} {z : ι → ℂ} (hlt : ∀ i, ‖z i‖ < 2)
    (hacc : ∀ R' < 2, ∃ i, R' < ‖z i‖) : ¬ WellFoundedAbove z 1 := by
  intro hwf
  have hfin := hwf (7 / 4) (by norm_num)
  by_cases hne : {i | 7 / 4 < ‖z i‖}.Nonempty
  · obtain ⟨i₀, -, hmax⟩ :=
      hfin.toFinset.exists_max_image (fun i => ‖z i‖) (by simpa using hne)
    obtain ⟨j, hj⟩ := hacc (max ‖z i₀‖ (7 / 4)) (max_lt (hlt i₀) (by norm_num))
    have hjA : j ∈ hfin.toFinset := by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact lt_of_le_of_lt (le_max_right _ _) hj
    have := hmax j hjA
    linarith [le_max_left ‖z i₀‖ (7 / 4)]
  · obtain ⟨j, hj⟩ := hacc (7 / 4) (by norm_num)
    exact hne ⟨j, hj⟩

/-- **Well-foundedness cannot be dropped.** There is a Weil tower with positive weights compatible
with the reflection, not well-founded above `1`, whose level sums are bounded at every level, while
every mode lies off the unit circle with nonzero merged weight. -/
theorem exists_tower_bounded_without_wellFounded :
    ∃ (ι : Type) (T : WeilTower ι) (b : ι → ℂ), Summable (fun i => ‖b i‖) ∧
      (∀ i, b (T.reflPerm i) = starRingEnd ℂ (b i)) ∧ ¬ WellFoundedAbove T.z 1 ∧
      (∃ C : ℝ, ∀ ν : ℕ, ‖levelSum T.z b ν‖ ≤ C) ∧ (∀ i, ‖T.z i‖ ≠ 1) ∧
      ∀ (i : ι) (F : Finset ι), (∀ j, T.z j = T.z i → j ∈ F) →
        (∑ j ∈ F with T.z j = T.z i, b j) ≠ 0 := by
  classical
  obtain ⟨ι, T, b, hsum, hrefl, hpos, hne1, hlt2, hacc, hzero⟩ := exists_wolff_tower
  refine ⟨ι, T, b, hsum, hrefl, not_wellFoundedAbove_of_accumulates hlt2 hacc,
    ⟨‖levelSum T.z b 0‖, fun ν => ?_⟩, hne1, fun i F hF => ?_⟩
  · rcases Nat.eq_zero_or_pos ν with h | h
    · rw [h, Nat.cast_zero]
    · rw [hzero ν h, norm_zero]; exact norm_nonneg _
  · intro h0
    have hre := congrArg Complex.re h0
    rw [Complex.re_sum, Complex.zero_re] at hre
    have : 0 < ∑ j ∈ F with T.z j = T.z i, (b j).re :=
      Finset.sum_pos (fun j _ => (hpos j).1) ⟨i, Finset.mem_filter.2 ⟨hF i rfl, rfl⟩⟩
    linarith

end GaloisForLFunctions.InfiniteRankWeilTheory

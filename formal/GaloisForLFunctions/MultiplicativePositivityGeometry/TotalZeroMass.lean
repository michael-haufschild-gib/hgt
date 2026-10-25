import GaloisForLFunctions.MultiplicativePositivityGeometry.ArithmeticRealization

/-!
# The total zero mass law

Let `D` be even positive definite on `ℝ` with `D ≤ 0` off the origin: nonnegative weights and all
boundary poles at `0`. Then the zero masses `−D(z)` at any finite set of distinct positive heights
add up to at most `D(0)/2` (`total_zero_mass_le`). No independence or commensurability of the
heights is assumed.

* A pole of order `k` carries at most `k/2` units of zero mass on the whole half-line. This extends
  the progression law to arbitrary configurations.
* With an integer divisor at most `D(0)/2` heights carry zeros (`card_zero_heights_le`). A simple pole
  admits none (`eq_zero_of_simple_pole`): a second proof of `ζ(1+it) ≠ 0`, without the character
  theorem.
* The bound is attained by the double pole `ζ(s)²/(ζ(s+it₀)ζ(s−it₀))`
  (`doublePoleProfile_total_mass`).

*Proof.* Sum the Gram form with unit coefficients over `F_N = {Σ_{z ∈ Z} n_z z : 0 ≤ n_z < N}`
(`folnerSet`). A pair of points contributes `D(0)` when the points coincide, `D(z)` when they differ
by `±z`, and something `≤ 0` otherwise (`pointwise_bound`). Since `F_N + z ⊆ F_{N+1}`, at least
`2|F_N| − |F_{N+1}|` pairs differ by `z` (`card_shift_mem_ge`). `|F_N| ≤ N^{|Z|}` grows polynomially,
so `|F_{N+1}| ≤ (1 + ε)|F_N|` for some `N` (`exists_folner_step`).
-/

open Finset Filter Topology

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- The Gram form of a positive-definite function over a finite set, with unit coefficients. -/
theorem IsEvenPosDef.sum_finset_nonneg {G : Type*} [AddCommGroup G] {φ : G → ℝ}
    (hφ : IsEvenPosDef φ) (F : Finset G) : 0 ≤ ∑ x ∈ F, ∑ y ∈ F, φ (x - y) := by
  have key : ∀ f : G → G → ℝ, ∑ i : Fin F.card, ∑ j : Fin F.card,
      f (F.equivFin.symm i) (F.equivFin.symm j) = ∑ x ∈ F, ∑ y ∈ F, f x y := by
    intro f
    rw [← Finset.sum_coe_sort F, ← Equiv.sum_comp F.equivFin.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort F, ← Equiv.sum_comp F.equivFin.symm]
  have h := hφ.posDef F.card (fun i => (F.equivFin.symm i : G)) (fun _ => 1)
  calc (0 : ℝ) ≤ ∑ i : Fin F.card, ∑ j : Fin F.card,
        φ ((F.equivFin.symm i : G) - F.equivFin.symm j) := by simpa using h
    _ = ∑ x ∈ F, ∑ y ∈ F, φ (x - y) := key fun x y => φ (x - y)

/-- The Følner set `F_N = {Σ_{z ∈ Z} n_z z : 0 ≤ n_z < N}`. -/
noncomputable def folnerSet (Z : Finset ℝ) (N : ℕ) : Finset ℝ :=
  (Fintype.piFinset fun _ : Z => range N).image fun n => ∑ z : Z, (n z : ℝ) * z

theorem card_folnerSet_le (Z : Finset ℝ) (N : ℕ) : (folnerSet Z N).card ≤ N ^ Z.card := by
  unfold folnerSet
  refine card_image_le.trans ?_
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ,
    Fintype.card_coe]

theorem zero_mem_folnerSet (Z : Finset ℝ) {N : ℕ} (hN : 1 ≤ N) : (0 : ℝ) ∈ folnerSet Z N := by
  unfold folnerSet
  refine Finset.mem_image.mpr ⟨fun _ => 0, ?_, by simp⟩
  simp only [Fintype.mem_piFinset, Finset.mem_range]
  intro
  omega

theorem folnerSet_mono (Z : Finset ℝ) (N : ℕ) : folnerSet Z N ⊆ folnerSet Z (N + 1) := by
  unfold folnerSet
  refine Finset.image_subset_image fun n hn => ?_
  simp only [Fintype.mem_piFinset, Finset.mem_range] at hn ⊢
  intro z
  have := hn z
  omega

theorem add_mem_folnerSet {Z : Finset ℝ} {N : ℕ} {z : ℝ} (hz : z ∈ Z) {x : ℝ}
    (hx : x ∈ folnerSet Z N) : x + z ∈ folnerSet Z (N + 1) := by
  classical
  unfold folnerSet at hx ⊢
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  refine Finset.mem_image.mpr ⟨fun w => n w + if (w : ℝ) = z then 1 else 0, ?_, ?_⟩
  · simp only [Fintype.mem_piFinset, Finset.mem_range] at hn ⊢
    intro w
    have := hn w
    split_ifs <;> omega
  · simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, add_mul,
      Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single ⟨z, hz⟩]
    · simp
    · intro w _ hw
      rw [if_neg fun h => hw (Subtype.ext h)]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- At least `2|F_N| − |F_{N+1}|` points `y ∈ F_N` have `y + z ∈ F_N`. -/
theorem card_shift_mem_ge {Z : Finset ℝ} {N : ℕ} {z : ℝ} (hz : z ∈ Z) :
    2 * ((folnerSet Z N).card : ℝ) - (folnerSet Z (N + 1)).card ≤
      ((folnerSet Z N).filter fun y => y + z ∈ folnerSet Z N).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := folnerSet Z N)
    (fun y => y + z ∈ folnerSet Z N)
  have hbad : ((folnerSet Z N).filter fun y => ¬ (y + z ∈ folnerSet Z N)).card ≤
      (folnerSet Z (N + 1) \ folnerSet Z N).card := by
    refine Finset.card_le_card_of_injOn (fun y => y + z) (fun y hy => ?_) ?_
    · simp only [Finset.coe_filter, Set.mem_setOf_eq] at hy
      simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe]
      exact ⟨add_mem_folnerSet hz hy.1, hy.2⟩
    · intro a _ b _ h
      simpa using h
  have hle : (folnerSet Z N).card ≤ (folnerSet Z (N + 1)).card :=
    Finset.card_le_card (folnerSet_mono Z N)
  have hsd := Finset.card_sdiff_of_subset (folnerSet_mono Z N)
  have h1 : (((folnerSet Z N).filter fun y => ¬ (y + z ∈ folnerSet Z N)).card : ℝ) ≤
      (folnerSet Z (N + 1)).card - (folnerSet Z N).card := by
    rw [← Nat.cast_sub hle]
    exact_mod_cast hbad.trans hsd.le
  have h2 : (((folnerSet Z N).filter fun y => y + z ∈ folnerSet Z N).card : ℝ) +
      ((folnerSet Z N).filter fun y => ¬ (y + z ∈ folnerSet Z N)).card =
        (folnerSet Z N).card := by exact_mod_cast hsplit
  linarith

/-- Polynomial growth: some step of the Følner sequence grows by at most `1 + ε`. -/
theorem exists_folner_step (Z : Finset ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, 1 ≤ N ∧ ((folnerSet Z (N + 1)).card : ℝ) ≤ (1 + ε) * (folnerSet Z N).card := by
  by_contra hcon
  push Not at hcon
  have hgrow : ∀ N : ℕ, (1 + ε) ^ N ≤ ((folnerSet Z (N + 1)).card : ℝ) := by
    intro N
    induction N with
    | zero =>
      simp only [pow_zero, zero_add]
      exact_mod_cast (Finset.card_pos.mpr ⟨0, zero_mem_folnerSet Z le_rfl⟩ : 0 < _)
    | succ N ih =>
      have h := hcon (N + 1) (by omega)
      calc (1 + ε) ^ (N + 1) = (1 + ε) * (1 + ε) ^ N := by ring
        _ ≤ (1 + ε) * ((folnerSet Z (N + 1)).card : ℝ) := by gcongr
        _ ≤ ((folnerSet Z (N + 1 + 1)).card : ℝ) := h.le
  have hpoly : ∀ N : ℕ, ((folnerSet Z (N + 1)).card : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ Z.card :=
    fun N => by exact_mod_cast card_folnerSet_le Z (N + 1)
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt Z.card
    (show (1 : ℝ) < 1 + ε by linarith)
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (1 + ε) by positivity))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hev
  have h := hn₀ (n₀ + 1) (by omega)
  rw [div_lt_div_iff₀ (by positivity) (by positivity), pow_succ] at h
  have h2 : ((n₀ + 1 : ℕ) : ℝ) ^ Z.card < (1 + ε) ^ n₀ := by
    have h3 : ((n₀ + 1 : ℕ) : ℝ) ^ Z.card * (1 + ε) < (1 + ε) ^ n₀ * (1 + ε) := by linarith
    exact lt_of_mul_lt_mul_right h3 (by linarith)
  linarith [hgrow n₀, hpoly n₀]

variable {D : ℝ → ℝ}

/-- Each pair contributes `D(0)`, `D(±z)` or something nonpositive. -/
theorem pointwise_bound (hD : IsEvenPosDef D) (hnp : ∀ u, u ≠ 0 → D u ≤ 0) {Z : Finset ℝ}
    (hZ : ∀ z ∈ Z, 0 < z) (x y : ℝ) :
    D (x - y) ≤ (if x = y then D 0 else 0) + (if x - y ∈ Z then D (x - y) else 0) +
      (if y - x ∈ Z then D (y - x) else 0) := by
  by_cases hxy : x = y
  · subst hxy
    have h0 : (0 : ℝ) ∉ Z := fun h => lt_irrefl 0 (hZ 0 h)
    simp [h0]
  · rw [if_neg hxy]
    by_cases h1 : x - y ∈ Z
    · have h2 : y - x ∉ Z := fun h => by
        have := hZ _ h
        have := hZ _ h1
        linarith
      rw [if_pos h1, if_neg h2]
      simp
    · rw [if_neg h1]
      by_cases h2 : y - x ∈ Z
      · rw [if_pos h2, show y - x = -(x - y) by ring, hD.even]
        simp
      · rw [if_neg h2]
        simpa using hnp (x - y) (sub_ne_zero.mpr hxy)

/-- Pairs differing by an element of `Z`, counted through `z ∈ Z`. -/
theorem sum_sum_ite_mem (F Z : Finset ℝ) (D : ℝ → ℝ) :
    ∑ x ∈ F, ∑ y ∈ F, (if x - y ∈ Z then D (x - y) else 0) =
      ∑ z ∈ Z, D z * ((F.filter fun y => y + z ∈ F).card : ℝ) := by
  classical
  rw [Finset.sum_comm]
  have hinner : ∀ y, ∑ x ∈ F, (if x - y ∈ Z then D (x - y) else 0) =
      ∑ z ∈ Z, (if y + z ∈ F then D z else 0) := by
    intro y
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun x => x - y) (fun z => y + z) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.2, by simpa using hx.1⟩
    · intro z hz
      simp only [Finset.mem_filter] at hz ⊢
      exact ⟨hz.2, by simpa using hz.1⟩
    · intro x _
      simp
    · intro z _
      simp
    · intro x _
      rfl
  simp_rw [hinner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **The total zero mass law.** If `D` is even positive definite and `D ≤ 0` off the origin, the
zero masses at any finite set of positive heights add up to at most `D(0)/2`. -/
theorem total_zero_mass_le (hD : IsEvenPosDef D) (hnp : ∀ u, u ≠ 0 → D u ≤ 0) {Z : Finset ℝ}
    (hZ : ∀ z ∈ Z, 0 < z) : ∑ z ∈ Z, -D z ≤ D 0 / 2 := by
  classical
  set S := ∑ z ∈ Z, D z with hS
  -- The Gram form on every Følner set.
  have hgram : ∀ N : ℕ, 0 ≤ ((folnerSet Z N).card : ℝ) * D 0 +
      2 * ∑ z ∈ Z, D z * ((folnerSet Z N).filter fun y => y + z ∈ folnerSet Z N).card := by
    intro N
    have h0 := hD.sum_finset_nonneg (folnerSet Z N)
    have hpt : ∑ x ∈ folnerSet Z N, ∑ y ∈ folnerSet Z N, D (x - y) ≤
        ∑ x ∈ folnerSet Z N, ∑ y ∈ folnerSet Z N, ((if x = y then D 0 else 0) +
          (if x - y ∈ Z then D (x - y) else 0) + (if y - x ∈ Z then D (y - x) else 0)) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => pointwise_bound hD hnp hZ x y
    have hdiag : ∑ x ∈ folnerSet Z N, ∑ y ∈ folnerSet Z N, (if x = y then D 0 else 0) =
        ((folnerSet Z N).card : ℝ) * D 0 := by
      rw [Finset.sum_congr rfl fun x hx => by rw [Finset.sum_ite_eq, if_pos hx],
        Finset.sum_const, nsmul_eq_mul]
    have h1 := sum_sum_ite_mem (folnerSet Z N) Z D
    have h2 : ∑ x ∈ folnerSet Z N, ∑ y ∈ folnerSet Z N, (if y - x ∈ Z then D (y - x) else 0) =
        ∑ z ∈ Z, D z * ((folnerSet Z N).filter fun y => y + z ∈ folnerSet Z N).card := by
      rw [Finset.sum_comm]
      exact sum_sum_ite_mem (folnerSet Z N) Z D
    simp only [Finset.sum_add_distrib] at hpt
    rw [hdiag, h1, h2] at hpt
    linarith
  by_contra hcon
  push Not at hcon
  have hSneg : D 0 / 2 < -S := by
    rw [hS, ← Finset.sum_neg_distrib]
    exact hcon
  have hD0 := hD.apply_zero_nonneg
  have hSpos : 0 < -S := by linarith
  set ε := (2 * (-S) - D 0) / (4 * (-S)) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  obtain ⟨N, hN1, hN⟩ := exists_folner_step Z hε0
  have hg := hgram N
  have hFpos : (0 : ℝ) < (folnerSet Z N).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, zero_mem_folnerSet Z hN1⟩
  -- Each `z` has at least `(1 − ε)|F_N|` partner pairs.
  have hcnt : ∀ z ∈ Z, D z * ((folnerSet Z N).filter fun y => y + z ∈ folnerSet Z N).card ≤
      D z * ((1 - ε) * (folnerSet Z N).card) := by
    intro z hz
    have hc := card_shift_mem_ge (N := N) hz
    have hDz := hnp z (hZ z hz).ne'
    have : (1 - ε) * ((folnerSet Z N).card : ℝ) ≤
        ((folnerSet Z N).filter fun y => y + z ∈ folnerSet Z N).card := by linarith
    exact mul_le_mul_of_nonpos_left this hDz
  have hsum : ∑ z ∈ Z, D z * ((folnerSet Z N).filter fun y => y + z ∈ folnerSet Z N).card ≤
      (1 - ε) * (folnerSet Z N).card * S := by
    calc _ ≤ ∑ z ∈ Z, D z * ((1 - ε) * (folnerSet Z N).card) := Finset.sum_le_sum hcnt
      _ = (1 - ε) * (folnerSet Z N).card * S := by
        rw [hS, Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
  have hmul : 0 ≤ ((folnerSet Z N).card : ℝ) * (D 0 + 2 * (1 - ε) * S) := by nlinarith
  have h' := (mul_nonneg_iff_of_pos_left hFpos).mp hmul
  have hSne : S ≠ 0 := (by linarith : S < 0).ne
  have e : 2 * (1 - ε) * (-S) = (2 * (-S) + D 0) / 2 := by
    rw [hε]
    field_simp
    ring
  nlinarith

/-- **Boundary form.** The total zero mass of a boundary datum without off-origin poles. -/
theorem boundary_total_zero_mass_le {ι : Type*} {lam : ι → ℝ} {w : ℝ → ι → ℝ}
    (hB : IsBoundaryDivisor lam w D) (hnp : ∀ u, u ≠ 0 → D u ≤ 0) {Z : Finset ℝ}
    (hZ : ∀ z ∈ Z, 0 < z) : ∑ z ∈ Z, -D z ≤ D 0 / 2 :=
  total_zero_mass_le hB.isEvenPosDef hnp hZ

/-- **Zero count.** With an integer divisor, at most `D(0)/2` positive heights carry zeros. -/
theorem card_zero_heights_le (hD : IsEvenPosDef D) (hnp : ∀ u, u ≠ 0 → D u ≤ 0)
    (hint : ∀ u, ∃ n : ℤ, D u = n) {Z : Finset ℝ} (hZ : ∀ z ∈ Z, 0 < z)
    (hzero : ∀ z ∈ Z, D z < 0) : (Z.card : ℝ) ≤ D 0 / 2 := by
  have hone : ∀ z ∈ Z, (1 : ℝ) ≤ -D z := fun z hz => by
    obtain ⟨n, hn⟩ := hint z
    have hneg := hzero z hz
    rw [hn] at hneg ⊢
    have hn' : n < 0 := by exact_mod_cast hneg
    have : n ≤ -1 := by omega
    have : (n : ℝ) ≤ -1 := by exact_mod_cast this
    linarith
  calc (Z.card : ℝ) = ∑ _z ∈ Z, (1 : ℝ) := by simp
    _ ≤ ∑ z ∈ Z, -D z := Finset.sum_le_sum hone
    _ ≤ D 0 / 2 := total_zero_mass_le hD hnp hZ

/-- **A simple pole admits no boundary zero**, from the total mass law alone. -/
theorem eq_zero_of_simple_pole (hD : IsEvenPosDef D) (h0 : D 0 = 1)
    (hint : ∀ u, ∃ n : ℤ, D u = n) (hnp : ∀ u, u ≠ 0 → D u ≤ 0) {u : ℝ} (hu : u ≠ 0) :
    D u = 0 := by
  -- Reduce to a positive height by evenness.
  have key : ∀ z, 0 < z → D z = 0 := by
    intro z hz
    by_contra hne
    have hlt : D z < 0 := lt_of_le_of_ne (hnp z hz.ne') hne
    have := card_zero_heights_le hD hnp hint (Z := {z}) (by simpa using hz) (by simpa using hlt)
    rw [h0, Finset.card_singleton] at this
    norm_num at this
  rcases lt_or_gt_of_ne hu with h | h
  · rw [← hD.even]
    exact key (-u) (by linarith)
  · exact key u h

/-- **Sharpness.** The double pole carries exactly `D(0)/2 = 1` units of zero mass. -/
theorem doublePoleProfile_total_mass {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∑ z ∈ ({t₀} : Finset ℝ), -doublePoleProfile t₀ z = doublePoleProfile t₀ 0 / 2 := by
  rw [Finset.sum_singleton, doublePoleProfile_has_zero ht₀.ne', doublePoleProfile_zero ht₀.ne']
  norm_num

end GaloisForLFunctions.MultiplicativePositivityGeometry

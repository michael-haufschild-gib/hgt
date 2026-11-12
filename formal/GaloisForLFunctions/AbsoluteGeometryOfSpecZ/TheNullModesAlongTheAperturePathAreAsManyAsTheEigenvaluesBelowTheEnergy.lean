import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheIndexAtAnApertureIsTheSumOfTheNullitiesBelowIt

/-!
# The null modes along the aperture path are as many as the eigenvalues below the energy

Weil's form at the aperture `a`, shifted by the energy `E`, has the index `negativeRank a E` and
the nullity `weilNullity a E`. An energy with a null mode is an **eigenvalue** of Weil's form at
the aperture `a`; the nullity is its multiplicity.

* **The index law in the energy.** The index at `(a, E)` is the number of eigenvalues below `E`,
  with multiplicity (`negativeRank_eq_sum_eigenvalues`). The index grows by the nullity across
  an energy (`negativeRank_add_nullity_le_of_energy_lt`), it is constant just below an energy
  (`exists_left_energy_negativeRank_eq`: a negative form on a finite-dimensional space is
  uniformly negative), it jumps by exactly the nullity just above
  (`exists_right_energy_negativeRank_eq`: extra negative unit vectors orthogonal to the
  nonpositive space would have a weak limit that is a null mode orthogonal to itself), and it
  vanishes at the ground energy.
* **Two paths, one index.** The null modes met along the aperture path up to `b` at the energy
  `E` are as many as the eigenvalues below `E` at the aperture `b`
  (`sum_nullity_apertures_eq_sum_eigenvalues`).
* **The conservation law of a rectangle.** For `a ≤ b` and `E₁ ≤ E₂`, widening the aperture at
  the energy `E₁` and then raising the energy at `b` meets as many null modes as raising the
  energy at `a` and then widening the aperture at `E₂` (`null_modes_along_two_paths`): the number
  of null modes met between two points of the (aperture, energy) plane does not depend on the
  monotone path.

Both index laws are instances of one counting law for a step function on the line
(`count_eq_sum_jumps`).
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower _root_.RHTower.PaperRestrictedWeil
open ArithmeticContinuationAndCriticalEnergy HTGeometry SignedArithmeticEnergyIncidence

/-! ### The counting law of a step function -/

section Counting

variable {N ν : ℝ → ℕ}

/-- The jumps at finitely many points below `t` sum to at most the count at `t`. -/
theorem sum_jumps_le_count (hmono : ∀ s t, s < t → N s + ν s ≤ N t) (F : Finset ℝ) (t : ℝ)
    (hF : ∀ s ∈ F, s < t) : ∑ s ∈ F, ν s ≤ N t := by
  classical
  induction F using Finset.induction_on_max generalizing t with
  | empty => simp only [Finset.sum_empty, Nat.zero_le]
  | insert a s hmax ih =>
      have ha : a < t := hF a (Finset.mem_insert_self a s)
      have hsum := ih a (fun x hx => hmax x hx)
      have hstep := hmono a t ha
      have hnot : a ∉ s := fun h => (lt_irrefl a) (hmax a h)
      rw [Finset.sum_insert hnot]
      omega

/-- Only finitely many points below `t` carry a jump. -/
theorem finite_jumps_below (hmono : ∀ s t, s < t → N s + ν s ≤ N t) (t : ℝ) :
    Set.Finite {s : ℝ | s < t ∧ 0 < ν s} := by
  let S := {s : ℝ | s < t ∧ 0 < ν s}
  let f : S → Fin (N t) := fun a =>
    ⟨N a.1, by
      have h := hmono a.1 t a.2.1
      have hp := a.2.2
      omega⟩
  have hinj : Function.Injective f := by
    intro a c heq
    have hn : N a.1 = N c.1 := congrArg Fin.val heq
    rcases lt_trichotomy a.1 c.1 with hlt | he | hgt
    · have h := hmono _ _ hlt
      have hp := a.2.2
      omega
    · exact Subtype.ext he
    · have h := hmono _ _ hgt
      have hp := c.2.2
      omega
  letI : Finite S := Finite.of_injective f hinj
  exact Set.toFinite S

/-- The count is at most the sum of the jumps below: induction on the count. Below the last
point `s` of count less than `n` the law holds; just to the right of `s` the count is `n`, so `s`
carries the missing jump. -/
theorem count_le_sum_jumps (hmono : ∀ s t, s < t → N s + ν s ≤ N t)
    (hright : ∀ s, ∃ t, s < t ∧ ∀ c, s < c → c ≤ t → N c = N s + ν s)
    (hleft : ∀ t, ∃ s, s < t ∧ N s = N t) (hzero : ∃ s₀, N s₀ = 0) :
    ∀ (n : ℕ) (t : ℝ), N t = n → n ≤ ∑ s ∈ (finite_jumps_below hmono t).toFinset, ν s := by
  classical
  have hmono' : ∀ s t, s ≤ t → N s ≤ N t := by
    intro s t hst
    rcases lt_or_eq_of_le hst with h | rfl
    · have := hmono s t h
      omega
    · exact le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hb
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Nat.zero_le _
    obtain ⟨a₀, ha₀⟩ := hzero
    -- the points of count below `n`
    obtain ⟨T, hT⟩ : ∃ T : Set ℝ, T = {t | N t < n} := ⟨_, rfl⟩
    have hT0 : a₀ ∈ T := by
      rw [hT]
      show N a₀ < n
      omega
    have hTb : ∀ t ∈ T, t ≤ b := by
      intro t ht
      rw [hT] at ht
      have ht' : N t < n := ht
      by_contra hlt
      have := hmono' b t (not_le.mp hlt).le
      omega
    have hbdd : BddAbove T := ⟨b, hTb⟩
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = sSup T := ⟨_, rfl⟩
    -- left continuity: the count at `s` is below `n`
    have hsn : N s < n := by
      obtain ⟨c, hcs, hc⟩ := hleft s
      rw [hs] at hcs
      obtain ⟨t, ht, hct⟩ := exists_lt_of_lt_csSup ⟨a₀, hT0⟩ hcs
      rw [hT] at ht
      have ht' : N t < n := ht
      have := hmono' c t hct.le
      omega
    have hsb : s < b := by
      refine lt_of_le_of_ne (hs ▸ csSup_le ⟨a₀, hT0⟩ hTb) fun h => ?_
      rw [h] at hsn
      omega
    -- just to the right of `s` the count is `n`
    obtain ⟨b', hsb', hjump⟩ := hright s
    have hc₀s : s < min b' b := lt_min hsb' hsb
    have hc₀j : N (min b' b) = N s + ν s := hjump _ hc₀s (min_le_left _ _)
    have hc₀n : N (min b' b) = n := by
      have hle := hmono' (min b' b) b (min_le_right _ _)
      have hge : n ≤ N (min b' b) := by
        by_contra hlt
        have hmem : min b' b ∈ T := by
          rw [hT]
          exact not_le.mp hlt
        exact absurd (le_csSup hbdd hmem) (not_le.mpr (hs ▸ hc₀s))
      omega
    have hih := ih (N s) hsn s rfl
    have hsub : (finite_jumps_below hmono s).toFinset ⊆ (finite_jumps_below hmono b).toFinset := by
      intro a ha
      rw [Set.Finite.mem_toFinset] at ha ⊢
      exact ⟨ha.1.trans hsb, ha.2⟩
    rcases Nat.eq_zero_or_pos (ν s) with h0 | hpos
    · have h1 := Finset.sum_le_sum_of_subset (f := ν) hsub
      omega
    · have hs_not : s ∉ (finite_jumps_below hmono s).toFinset := fun h =>
        lt_irrefl _ ((Set.Finite.mem_toFinset _).mp h).1
      have hins : insert s (finite_jumps_below hmono s).toFinset ⊆
          (finite_jumps_below hmono b).toFinset := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact (Set.Finite.mem_toFinset _).mpr ⟨hsb, hpos⟩
        · exact hsub ha
      have h1 := Finset.sum_le_sum_of_subset (f := ν) hins
      rw [Finset.sum_insert hs_not] at h1
      omega

/-- **The counting law.** A count on the line that grows by the jump across every point, is
constant just below every point, jumps by exactly the jump just above it and vanishes somewhere
is the sum of the jumps below. -/
theorem count_eq_sum_jumps (hmono : ∀ s t, s < t → N s + ν s ≤ N t)
    (hright : ∀ s, ∃ t, s < t ∧ ∀ c, s < c → c ≤ t → N c = N s + ν s)
    (hleft : ∀ t, ∃ s, s < t ∧ N s = N t) (hzero : ∃ s₀, N s₀ = 0) (t : ℝ) :
    N t = ∑ s ∈ (finite_jumps_below hmono t).toFinset, ν s :=
  le_antisymm (count_le_sum_jumps hmono hright hleft hzero _ t rfl)
    (sum_jumps_le_count hmono _ t fun _ hs => ((Set.Finite.mem_toFinset _).mp hs).1)

end Counting

/-! ### The index as a function of the energy -/

/-- The quadratic form at two energies differs by the mass. -/
theorem operator_quadratic_energy (a : SuzukiPositiveAperture) (E E' : ℝ) (u : Space a) :
    (inner ℂ (operator a E' u) u).re = (inner ℂ (operator a E u) u).re -
      (E' - E) * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  rw [operator_quadratic, operator_quadratic]
  ring

/-- The mass of a vector is at most its form norm. -/
theorem norm_formToAperture_sq_le (a : SuzukiPositiveAperture) (u : Space a) :
    ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _)
    (((ccmArchimedeanFormToAperture a).le_opNorm u).trans
      (mul_le_of_le_one_left (norm_nonneg u) (norm_ccmArchimedeanFormToAperture_le_one a))) 2

/-- **The index grows by the nullity across an energy**: the negative space and the null modes at
the lower energy are strictly negative at the higher one. -/
theorem negativeRank_add_nullity_le_of_energy_lt (a : SuzukiPositiveAperture) {E₁ E₂ : ℝ}
    (h : E₁ < E₂) : negativeRank a E₁ + weilNullity a E₁ ≤ negativeRank a E₂ := by
  have hd := PaperNegativePart.negativeSpace_disjoint_ker
    (operator a E₁) (operator_selfAdjoint a E₁)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (negativeSpace a E₁) (operator a E₁).toLinearMap.ker
  rw [hd.eq_bot] at hdim
  simp only [finrank_bot, add_zero] at hdim
  have hq : ∀ u ∈ negativeSpace a E₁ ⊔ (operator a E₁).toLinearMap.ker,
      (inner ℂ (operator a E₂ u) u).re ≤
        -(E₂ - E₁) * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
    intro u hu
    have h1 := PaperNegativePart.nonpositive_on_negativeSpace_sup_ker
      (operator a E₁) (operator_selfAdjoint a E₁) hu
    rw [operator_quadratic_energy a E₁ E₂ u]
    linarith
  have hfin := PaperNegativePart.nonpositive_subspace_dimension_le (operator a E₂)
    (operator_selfAdjoint a E₂) (negativeSpace a E₁ ⊔ (operator a E₁).toLinearMap.ker)
    (fun u hu => (hq u hu).trans (by
      nlinarith [sq_nonneg ‖ccmArchimedeanFormToAperture a u‖]))
    (fun u hu hz => by
      have h2 := hq u hu
      rw [hz, inner_zero_left, Complex.zero_re] at h2
      have h3 : ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤ 0 := by nlinarith
      have h4 : ‖ccmArchimedeanFormToAperture a u‖ = 0 :=
        pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm h3 (sq_nonneg _))
      exact ccmArchimedeanFormToAperture_injective a
        (by rw [norm_eq_zero.mp h4, map_zero]))
  rw [negativeRank, weilNullity, ← hdim]
  exact hfin.2

/-- A form that is negative on a finite-dimensional space is uniformly negative on it. -/
theorem exists_neg_bound_of_finiteDimensional {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (T : H →L[ℂ] H) (W : Submodule ℂ H) [FiniteDimensional ℂ W]
    (hneg : ∀ x ∈ W, x ≠ 0 → (inner ℂ (T x) x).re < 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ W, (inner ℂ (T x) x).re ≤ -c * ‖x‖ ^ 2 := by
  have hscale : ∀ (r : ℝ) (y : H),
      (inner ℂ (T ((r : ℂ) • y)) ((r : ℂ) • y)).re = r ^ 2 * (inner ℂ (T y) y).re := by
    intro r y
    rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    ring
  by_cases hW : ∀ x ∈ W, x = 0
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    rw [hW x hx]
    simp
  push Not at hW
  obtain ⟨x₁, hx₁, hx₁0⟩ := hW
  haveI : ProperSpace W := FiniteDimensional.proper_rclike ℂ W
  obtain ⟨f, hf⟩ : ∃ f : W → ℝ, f = fun x : W => (inner ℂ (T (x : H)) (x : H)).re := ⟨_, rfl⟩
  have hfc : Continuous f := by
    rw [hf]
    exact Complex.continuous_re.comp (continuous_inner.comp
      ((T.continuous.comp continuous_subtype_val).prodMk continuous_subtype_val))
  -- every nonzero vector of `W` is a positive multiple of a unit vector of `W`
  have hunit : ∀ x ∈ W, x ≠ 0 → ∃ y : W, y ∈ Metric.sphere (0 : W) 1 ∧
      x = ((‖x‖ : ℝ) : ℂ) • (y : H) := by
    intro x hx hx0
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    refine ⟨((‖x‖ : ℂ)⁻¹) • (⟨x, hx⟩ : W), ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr]
      exact inv_mul_cancel₀ hr.ne'
    · show x = ((‖x‖ : ℝ) : ℂ) • (((‖x‖ : ℂ)⁻¹) • x)
      rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'), one_smul]
  obtain ⟨y₁, hy₁, -⟩ := hunit x₁ hx₁ hx₁0
  obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_sphere (0 : W) 1).exists_isMaxOn ⟨y₁, hy₁⟩
    hfc.continuousOn
  have hx₀' : (x₀ : H) ≠ 0 := by
    intro h0
    have h1 : ‖x₀‖ = 1 := mem_sphere_zero_iff_norm.mp hx₀
    rw [Subtype.ext (show (x₀ : H) = ((0 : W) : H) from h0), norm_zero] at h1
    exact zero_ne_one h1
  have hm : f x₀ < 0 := by
    rw [hf]
    exact hneg x₀ x₀.2 hx₀'
  refine ⟨-f x₀, neg_pos.mpr hm, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · rw [hx0]
    simp
  · obtain ⟨y, hy, hxy⟩ := hunit x hx hx0
    have hfy : f y ≤ f x₀ := isMaxOn_iff.mp hmax y hy
    have h2 := hscale ‖x‖ (y : H)
    rw [← hxy] at h2
    have h3 : (inner ℂ (T (y : H)) (y : H)).re = f y := by rw [hf]
    rw [h2, h3]
    nlinarith [sq_nonneg ‖x‖]

/-- **Left continuity in the energy.** The index at an energy is attained at a lower energy. -/
theorem exists_left_energy_negativeRank_eq (a : SuzukiPositiveAperture) (E : ℝ) :
    ∃ E' : ℝ, E' < E ∧ negativeRank a E' = negativeRank a E := by
  obtain ⟨c, hc, hbound⟩ := exists_neg_bound_of_finiteDimensional (operator a E)
    (negativeSpace a E) (fun x hx hx0 =>
      PaperNegativePart.negativeSpace_strict _ (operator_selfAdjoint a E) hx hx0)
  refine ⟨E - c / 2, by linarith,
    le_antisymm (negativeRank_monotone a (by linarith)) ?_⟩
  have hq : ∀ u ∈ negativeSpace a E,
      (inner ℂ (operator a (E - c / 2) u) u).re ≤ -(c / 2) * ‖u‖ ^ 2 := by
    intro u hu
    have h1 := hbound u hu
    have h2 := norm_formToAperture_sq_le a u
    rw [operator_quadratic_energy a E (E - c / 2) u]
    nlinarith
  exact (PaperNegativePart.nonpositive_subspace_dimension_le (operator a (E - c / 2))
    (operator_selfAdjoint a (E - c / 2)) (negativeSpace a E)
    (fun u hu => (hq u hu).trans (by nlinarith [sq_nonneg ‖u‖]))
    (fun u hu hz => by
      have h2 := hq u hu
      rw [hz, inner_zero_left, Complex.zero_re] at h2
      have h3 : ‖u‖ ^ 2 ≤ 0 := by nlinarith
      exact norm_eq_zero.mp
        (pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm h3 (sq_nonneg _))))).2

/-- Some energy just above has no more negative directions than the nonpositive space. -/
theorem exists_right_energy_negativeRank_le (a : SuzukiPositiveAperture) (E : ℝ) :
    ∃ n : ℕ, negativeRank a (E + 1 / ((n : ℝ) + 1)) ≤ negativeRank a E + weilNullity a E := by
  classical
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℂ (Space a),
      W = negativeSpace a E ⊔ (operator a E).toLinearMap.ker := ⟨_, rfl⟩
  haveI : FiniteDimensional ℂ W := by
    rw [hW]
    infer_instance
  have hdim : Module.finrank ℂ W = negativeRank a E + weilNullity a E := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq
      (negativeSpace a E) (operator a E).toLinearMap.ker
    rw [(PaperNegativePart.negativeSpace_disjoint_ker
      (operator a E) (operator_selfAdjoint a E)).eq_bot, finrank_bot, add_zero] at hd
    rw [hW]
    exact hd
  by_contra hn
  push Not at hn
  have hex : ∀ n : ℕ, ∃ u : Space a, u ∈ negativeSpace a (E + 1 / ((n : ℝ) + 1)) ∧
      ‖u‖ = 1 ∧ u ∈ Wᗮ := fun n =>
    exists_unit_mem_orthogonal_of_finrank_lt (negativeSpace a (E + 1 / ((n : ℝ) + 1))) W
      (by rw [hdim]; exact hn n)
  choose u hu hnorm horth using hex
  have hq : ∀ n, compactPerturbedEnergy (ccmArchimedeanFormToAperture a)
      (ccmRestrictedWeilBoundedRemainder a - (E : ℂ) • 1) (u n) ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    rw [← operator_quadratic_eq_compactEnergy]
    have h1 := PaperNegativePart.negativeSpace_strict _ (operator_selfAdjoint a _) (hu n)
      (fun hz => by simpa only [hz, norm_zero, zero_ne_one] using hnorm n)
    rw [operator_quadratic_energy a E (E + 1 / ((n : ℝ) + 1)) (u n)] at h1
    have h2 := norm_formToAperture_sq_le a (u n)
    rw [hnorm n, one_pow] at h2
    have h3 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    nlinarith [sq_nonneg ‖ccmArchimedeanFormToAperture a (u n)‖]
  obtain ⟨v, φ, hφ, -, hweak⟩ := exists_weakConvC_subseq_of_bounded u (fun n => (hnorm n).le)
  have hlim : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  obtain ⟨hv0, hvq⟩ := compactPerturbation_unit_weakLimit_of_energy_upper_bound
    (isCompactOperator_ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a - (E : ℂ) • 1) hweak (fun n => hnorm (φ n)) hlim
    (fun n => hq (φ n))
  rw [← operator_quadratic_eq_compactEnergy] at hvq
  have hvorth : ∀ y ∈ W, inner ℂ y v = 0 := by
    intro y hy
    have ht := hweak (innerSL ℂ y)
    have hz : ∀ n, inner ℂ y (u (φ n)) = 0 := fun n =>
      (Submodule.mem_orthogonal _ _).mp (horth (φ n)) y hy
    have ht' : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (inner ℂ y v)) := by
      simpa only [innerSL_apply_apply, Function.comp_apply, hz] using ht
    exact tendsto_nhds_unique ht' tendsto_const_nhds
  have hvneg : v ∈ (negativeSpace a E)ᗮ :=
    (Submodule.mem_orthogonal _ _).mpr fun y hy =>
      hvorth y (hW ▸ (show negativeSpace a E ≤ _ from le_sup_left) hy)
  have hvker : (operator a E) v = 0 :=
    PaperNegativePart.apply_eq_zero_of_nonpositive_orthogonal
      (operator a E) (operator_selfAdjoint a E) hvneg hvq
  exact hv0 (inner_self_eq_zero.mp
    (hvorth v (hW ▸ (show (operator a E).toLinearMap.ker ≤ _ from le_sup_right) hvker)))

/-- **Right continuity in the energy.** Just above an energy the index is the index plus the
nullity. -/
theorem exists_right_energy_negativeRank_eq (a : SuzukiPositiveAperture) (E : ℝ) :
    ∃ E' : ℝ, E < E' ∧ ∀ c : ℝ, E < c → c ≤ E' →
      negativeRank a c = negativeRank a E + weilNullity a E := by
  obtain ⟨n, hn⟩ := exists_right_energy_negativeRank_le a E
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact ⟨E + 1 / ((n : ℝ) + 1), by linarith, fun c hc hcE =>
    le_antisymm ((negativeRank_monotone a hcE).trans hn)
      (negativeRank_add_nullity_le_of_energy_lt a hc)⟩

/-! ### The index law in the energy -/

/-- The eigenvalues of Weil's form at the aperture `a` below the energy `E`. -/
def eigenvaluesBelow (a : SuzukiPositiveAperture) (E : ℝ) : Finset ℝ :=
  (finite_jumps_below (N := negativeRank a) (ν := weilNullity a)
    (fun _ _ h => negativeRank_add_nullity_le_of_energy_lt a h) E).toFinset

theorem mem_eigenvaluesBelow {a : SuzukiPositiveAperture} {E s : ℝ} :
    s ∈ eigenvaluesBelow a E ↔ s < E ∧ 0 < weilNullity a s := by
  rw [eigenvaluesBelow, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- **The index law in the energy.** The negative index of Weil's form at the aperture `a`,
shifted by the energy `E`, is the number of its eigenvalues below `E`, with multiplicity. -/
theorem negativeRank_eq_sum_eigenvalues (a : SuzukiPositiveAperture) (E : ℝ) :
    negativeRank a E = ∑ s ∈ eigenvaluesBelow a E, weilNullity a s :=
  count_eq_sum_jumps (fun _ _ h => negativeRank_add_nullity_le_of_energy_lt a h)
    (exists_right_energy_negativeRank_eq a) (exists_left_energy_negativeRank_eq a)
    ⟨ccmRestrictedWeilGroundEnergy a, (negativeRank_eq_zero_iff_ground a _).mpr le_rfl⟩ E

/-- **The ground energy is the lowest eigenvalue.** -/
theorem weilNullity_groundEnergy_pos (a : SuzukiPositiveAperture) :
    0 < weilNullity a (ccmRestrictedWeilGroundEnergy a) := by
  obtain ⟨E', hE', hjump⟩ := exists_right_energy_negativeRank_eq a (ccmRestrictedWeilGroundEnergy a)
  have h1 := hjump E' hE' le_rfl
  have h2 := (negativeRank_pos_iff_ground a E').mpr hE'
  have h3 := (negativeRank_eq_zero_iff_ground a (ccmRestrictedWeilGroundEnergy a)).mpr le_rfl
  omega

/-- No energy below the ground energy is an eigenvalue. -/
theorem weilNullity_eq_zero_of_lt_groundEnergy (a : SuzukiPositiveAperture) {E : ℝ}
    (h : E < ccmRestrictedWeilGroundEnergy a) : weilNullity a E = 0 := by
  have h1 := negativeRank_add_nullity_le_of_energy_lt a h
  have h3 := (negativeRank_eq_zero_iff_ground a (ccmRestrictedWeilGroundEnergy a)).mpr le_rfl
  omega

/-! ### Two paths, one index -/

/-- **Two paths, one index.** The null modes met along the aperture path up to `b` at the energy
`E` are as many as the eigenvalues below `E` at the aperture `b`. -/
theorem sum_nullity_apertures_eq_sum_eigenvalues (b : SuzukiPositiveAperture) (E : ℝ) :
    ∑ a ∈ resonantBelow b E, weilNullity a E = ∑ s ∈ eigenvaluesBelow b E, weilNullity b s := by
  rw [← negativeRank_eq_sum_nullity, negativeRank_eq_sum_eigenvalues]

/-- The index between two apertures: the null modes met from `a` to `b`. -/
theorem negativeRank_eq_add_sum_nullity_between {a b : SuzukiPositiveAperture}
    (hab : a.1 ≤ b.1) (E : ℝ) :
    negativeRank b E = negativeRank a E +
      ∑ c ∈ (resonantBelow b E).filter (fun c => a.1 ≤ c.1), weilNullity c E := by
  classical
  have hfil : (resonantBelow b E).filter (fun c => ¬ a.1 ≤ c.1) = resonantBelow a E := by
    ext c
    rw [Finset.mem_filter, mem_resonantBelow, mem_resonantBelow, not_le]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans_le hab, h.2⟩, h.1⟩⟩
  rw [negativeRank_eq_sum_nullity b E, negativeRank_eq_sum_nullity a E, ← hfil, add_comm]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- The index between two energies: the eigenvalues from `E₁` to `E₂`. -/
theorem negativeRank_eq_add_sum_eigenvalues_between (a : SuzukiPositiveAperture) {E₁ E₂ : ℝ}
    (hE : E₁ ≤ E₂) :
    negativeRank a E₂ = negativeRank a E₁ +
      ∑ s ∈ (eigenvaluesBelow a E₂).filter (fun s => E₁ ≤ s), weilNullity a s := by
  classical
  have hfil : (eigenvaluesBelow a E₂).filter (fun s => ¬ E₁ ≤ s) = eigenvaluesBelow a E₁ := by
    ext s
    rw [Finset.mem_filter, mem_eigenvaluesBelow, mem_eigenvaluesBelow, not_le]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans_le hE, h.2⟩, h.1⟩⟩
  rw [negativeRank_eq_sum_eigenvalues a E₂, negativeRank_eq_sum_eigenvalues a E₁, ← hfil,
    add_comm]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- **The conservation law of a rectangle.** Widening the aperture from `a` to `b` at the energy
`E₁` and then raising the energy to `E₂` at `b` meets as many null modes as raising the energy at
`a` and then widening the aperture at `E₂`. -/
theorem null_modes_along_two_paths {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) {E₁ E₂ : ℝ}
    (hE : E₁ ≤ E₂) :
    ∑ c ∈ (resonantBelow b E₁).filter (fun c => a.1 ≤ c.1), weilNullity c E₁ +
        ∑ s ∈ (eigenvaluesBelow b E₂).filter (fun s => E₁ ≤ s), weilNullity b s =
      ∑ s ∈ (eigenvaluesBelow a E₂).filter (fun s => E₁ ≤ s), weilNullity a s +
        ∑ c ∈ (resonantBelow b E₂).filter (fun c => a.1 ≤ c.1), weilNullity c E₂ := by
  have h1 := negativeRank_eq_add_sum_nullity_between hab E₁
  have h2 := negativeRank_eq_add_sum_eigenvalues_between b hE
  have h3 := negativeRank_eq_add_sum_eigenvalues_between a hE
  have h4 := negativeRank_eq_add_sum_nullity_between hab E₂
  omega

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

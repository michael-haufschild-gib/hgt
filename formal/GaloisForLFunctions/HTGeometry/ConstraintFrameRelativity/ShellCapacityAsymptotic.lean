import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellCapacitySharpScale

/-!
# The exact leading asymptotic of the Boolean shell capacity

At low temperature the capacity of an ordered prime aperture is governed by the two smallest
primes alone:

`D(σ) / p_1^{-σ} → π² (λ_1 - λ_0)² / λ_0²`.

Every Cauchy--Binet weight product other than the pair `(p_0, p_1)` is `o(p_0^{-σ} p_1^{-σ})`,
while the energy moment is `p_0^{-σ} λ_0² (1 + o(1))`.
-/

namespace HTGeometry.ConstraintFrameRelativity

open Finset Filter

/-- A base larger than one decays to zero along negative exponents. -/
theorem tendsto_rpow_neg_atTop_of_one_lt {b : ℝ} (hb : 1 < b) :
    Tendsto (fun σ : ℝ => b ^ (-σ)) atTop (nhds 0) := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hlog : 0 < Real.log b := Real.log_pos hb
  have hrw : (fun σ : ℝ => b ^ (-σ)) = fun σ : ℝ => (Real.exp (σ * Real.log b))⁻¹ := by
    funext σ
    rw [Real.rpow_def_of_pos hb0, ← Real.exp_neg]
    congr 1
    ring
  rw [hrw]
  exact (Real.tendsto_exp_atTop.comp
    (Filter.Tendsto.atTop_mul_const hlog tendsto_id)).inv_tendsto_atTop

namespace Aperture

variable (F : Aperture)

/-! ## Ratios of fugacities and weights -/

theorem fug_div_fug (i j : Fin F.card) (σ : ℝ) :
    F.fug i σ / F.fug j σ = ((F.prime i : ℝ) / (F.prime j : ℝ)) ^ (-σ) := by
  rw [fug, fug, Real.div_rpow (F.prime_pos i).le (F.prime_pos j).le]

theorem tendsto_fug_div_fug {i j : Fin F.card} (hij : j < i) :
    Tendsto (fun σ => F.fug i σ / F.fug j σ) atTop (nhds 0) := by
  have hlt : (F.prime j : ℝ) < (F.prime i : ℝ) := by exact_mod_cast F.strictMono hij
  have hb : 1 < (F.prime i : ℝ) / (F.prime j : ℝ) := by
    rw [lt_div_iff₀ (F.prime_pos j)]
    linarith
  simpa only [F.fug_div_fug] using tendsto_rpow_neg_atTop_of_one_lt hb

theorem wt_div_fug_eq (i : Fin F.card) (σ : ℝ) :
    F.wt i σ / F.fug i σ = ((1 + F.fug i σ) ^ 2)⁻¹ := by
  have hx := F.fug_pos i σ
  have h1 : (0 : ℝ) < 1 + F.fug i σ := by linarith
  rw [wt, occVar_eq hx.le]
  field_simp

theorem tendsto_wt_div_fug (i : Fin F.card) :
    Tendsto (fun σ => F.wt i σ / F.fug i σ) atTop (nhds 1) := by
  simp only [F.wt_div_fug_eq]
  have h1 : Tendsto (fun σ => (1 + F.fug i σ) ^ 2) atTop (nhds 1) := by
    have h := (F.tendsto_fug_atTop i).const_add (1 : ℝ)
    simpa using h.pow 2
  simpa using h1.inv₀ (by norm_num)

theorem wt_div_fug_nonneg (i j : Fin F.card) (σ : ℝ) : 0 ≤ F.wt i σ / F.fug j σ :=
  div_nonneg (F.wt_pos i σ).le (F.fug_pos j σ).le

/-- Away from the least prime, the weight is negligible against the least fugacity. -/
theorem tendsto_wt_div_fug_least {i : Fin F.card} (hi : F.least < i) :
    Tendsto (fun σ => F.wt i σ / F.fug F.least σ) atTop (nhds 0) := by
  refine squeeze_zero' (g := fun σ => F.fug i σ / F.fug F.least σ)
    (Filter.Eventually.of_forall fun σ => F.wt_div_fug_nonneg i F.least σ)
    (Filter.Eventually.of_forall fun σ => ?_) (F.tendsto_fug_div_fug hi)
  have hd := F.fug_pos F.least σ
  gcongr
  exact F.wt_le_fug i σ

/-- Away from the second prime, the weight is negligible against the second fugacity. -/
theorem tendsto_wt_div_fug_second {i : Fin F.card} (hi : F.second < i) :
    Tendsto (fun σ => F.wt i σ / F.fug F.second σ) atTop (nhds 0) := by
  refine squeeze_zero' (g := fun σ => F.fug i σ / F.fug F.second σ)
    (Filter.Eventually.of_forall fun σ => F.wt_div_fug_nonneg i F.second σ)
    (Filter.Eventually.of_forall fun σ => ?_) (F.tendsto_fug_div_fug hi)
  have hd := F.fug_pos F.second σ
  gcongr
  exact F.wt_le_fug i σ

theorem wt_div_fug_least_le_one (i : Fin F.card) {σ : ℝ} (hσ : 0 ≤ σ) :
    F.wt i σ / F.fug F.least σ ≤ 1 := by
  rw [div_le_one (F.fug_pos F.least σ)]
  exact le_trans (F.wt_le_fug i σ) (F.fug_antitone (F.least_le i) hσ)

theorem second_le_of_ne_least {i : Fin F.card} (hi : i ≠ F.least) : F.second ≤ i := by
  simp only [second, Fin.le_def]
  have hne : i.val ≠ 0 := by
    intro h
    exact hi (Fin.ext (by simpa [least] using h))
  omega

theorem wt_div_fug_second_le_one {i : Fin F.card} (hi : i ≠ F.least) {σ : ℝ} (hσ : 0 ≤ σ) :
    F.wt i σ / F.fug F.second σ ≤ 1 := by
  rw [div_le_one (F.fug_pos F.second σ)]
  exact le_trans (F.wt_le_fug i σ) (F.fug_antitone (F.second_le_of_ne_least hi) hσ)

/-! ## The normalised energy moment -/

theorem tendsto_capC_div_fug_least :
    Tendsto (fun σ => capC (fun i => F.wt i σ) F.clock / F.fug F.least σ) atTop
      (nhds ((F.clock F.least) ^ 2)) := by
  have hrw : ∀ σ : ℝ, capC (fun i => F.wt i σ) F.clock / F.fug F.least σ
      = ∑ i, F.wt i σ / F.fug F.least σ * F.clock i ^ 2 := by
    intro σ
    rw [capC, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hrw]
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin F.card)),
      Tendsto (fun σ => F.wt i σ / F.fug F.least σ * F.clock i ^ 2) atTop
        (nhds (if i = F.least then (F.clock F.least) ^ 2 else 0)) := by
    intro i _
    by_cases hi : i = F.least
    · subst hi
      rw [if_pos rfl]
      simpa using (F.tendsto_wt_div_fug F.least).mul_const ((F.clock F.least) ^ 2)
    · rw [if_neg hi]
      have hlt : F.least < i := lt_of_le_of_ne (F.least_le i) (Ne.symm hi)
      simpa using (F.tendsto_wt_div_fug_least hlt).mul_const (F.clock i ^ 2)
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin F.card)) hterm
  simpa using h

/-! ## The normalised Gram determinant -/

/-- The normalised Cauchy--Binet term of an ordered pair. -/
noncomputable def pairTerm (i j : Fin F.card) (σ : ℝ) : ℝ :=
  F.wt i σ * F.wt j σ / (F.fug F.least σ * F.fug F.second σ) * (F.clock i - F.clock j) ^ 2

/-- The limiting value of a normalised Cauchy--Binet term. -/
noncomputable def pairLimit (i j : Fin F.card) : ℝ :=
  (if i = F.least ∧ j = F.second then (F.clock F.second - F.clock F.least) ^ 2 else 0)
    + (if i = F.second ∧ j = F.least then (F.clock F.second - F.clock F.least) ^ 2 else 0)

theorem pairTerm_factor (i j : Fin F.card) (σ : ℝ) :
    F.pairTerm i j σ
      = F.wt i σ / F.fug F.least σ * (F.wt j σ / F.fug F.second σ)
        * (F.clock i - F.clock j) ^ 2 := by
  have h0 := (F.fug_pos F.least σ).ne'
  have h1 := (F.fug_pos F.second σ).ne'
  rw [pairTerm]
  field_simp

theorem pairTerm_factor_swap (i j : Fin F.card) (σ : ℝ) :
    F.pairTerm i j σ
      = F.wt j σ / F.fug F.least σ * (F.wt i σ / F.fug F.second σ)
        * (F.clock i - F.clock j) ^ 2 := by
  have h0 := (F.fug_pos F.least σ).ne'
  have h1 := (F.fug_pos F.second σ).ne'
  rw [pairTerm]
  field_simp

/-- A product bound with one factor at most one. -/
theorem bound_helper {a b c L : ℝ} (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hcL : c ≤ L) :
    a * b * c ≤ b * L := by
  nlinarith [mul_nonneg hb0 hc0, mul_nonneg (sub_nonneg.mpr ha1) (mul_nonneg hb0 hc0),
    mul_le_mul_of_nonneg_left hcL hb0]

theorem pairTerm_nonneg (i j : Fin F.card) (σ : ℝ) : 0 ≤ F.pairTerm i j σ := by
  rw [pairTerm_factor]
  exact mul_nonneg (mul_nonneg (F.wt_div_fug_nonneg i F.least σ)
    (F.wt_div_fug_nonneg j F.second σ)) (sq_nonneg _)

theorem tendsto_pairTerm (i j : Fin F.card) :
    Tendsto (F.pairTerm i j) atTop (nhds (F.pairLimit i j)) := by
  have hlt := F.least_lt_second
  have hzero : ∀ g : ℝ → ℝ, Tendsto g atTop (nhds 0) →
      (∀ σ : ℝ, 0 ≤ σ → F.pairTerm i j σ ≤ g σ * (F.clock F.greatest) ^ 2) →
      Tendsto (F.pairTerm i j) atTop (nhds 0) := by
    intro g hg hb
    refine squeeze_zero' (g := fun σ => g σ * (F.clock F.greatest) ^ 2)
      (Filter.Eventually.of_forall fun σ => F.pairTerm_nonneg i j σ) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with σ hσ using hb σ hσ
    · simpa using hg.mul_const ((F.clock F.greatest) ^ 2)
  by_cases hij : i = j
  · subst hij
    have hlim : F.pairLimit i i = 0 := by
      rw [pairLimit]
      have h1 : ¬ (i = F.least ∧ i = F.second) := by
        rintro ⟨rfl, h⟩
        exact absurd h hlt.ne
      have h2 : ¬ (i = F.second ∧ i = F.least) := by
        rintro ⟨rfl, h⟩
        exact absurd h.symm hlt.ne
      rw [if_neg h1, if_neg h2, add_zero]
    rw [hlim]
    have hzz : F.pairTerm i i = fun _ => 0 := by
      funext σ
      simp [pairTerm]
    rw [hzz]
    exact tendsto_const_nhds
  by_cases hA : i = F.least ∧ j = F.second
  · obtain ⟨rfl, rfl⟩ := hA
    have h2 : ¬ (F.least = F.second ∧ F.second = F.least) := by
      rintro ⟨h, -⟩
      exact absurd h hlt.ne
    rw [pairLimit, if_pos ⟨rfl, rfl⟩, if_neg h2, add_zero]
    have hfun : F.pairTerm F.least F.second
        = fun σ => F.wt F.least σ / F.fug F.least σ * (F.wt F.second σ / F.fug F.second σ)
          * (F.clock F.second - F.clock F.least) ^ 2 := by
      funext σ
      rw [F.pairTerm_factor]
      ring
    rw [hfun]
    have ha := F.tendsto_wt_div_fug F.least
    have hb := F.tendsto_wt_div_fug F.second
    have h := (ha.mul hb).mul_const ((F.clock F.second - F.clock F.least) ^ 2)
    simpa using h
  by_cases hB : i = F.second ∧ j = F.least
  · obtain ⟨rfl, rfl⟩ := hB
    have h1 : ¬ (F.second = F.least ∧ F.least = F.second) := by
      rintro ⟨h, -⟩
      exact absurd h.symm hlt.ne
    rw [pairLimit, if_neg h1, if_pos ⟨rfl, rfl⟩, zero_add]
    have hfun : F.pairTerm F.second F.least
        = fun σ => F.wt F.least σ / F.fug F.least σ * (F.wt F.second σ / F.fug F.second σ)
          * (F.clock F.second - F.clock F.least) ^ 2 := by
      funext σ
      exact F.pairTerm_factor_swap _ _ σ
    rw [hfun]
    have ha := F.tendsto_wt_div_fug F.least
    have hb := F.tendsto_wt_div_fug F.second
    have h := (ha.mul hb).mul_const ((F.clock F.second - F.clock F.least) ^ 2)
    simpa using h
  · have hlim : F.pairLimit i j = 0 := by
      rw [pairLimit, if_neg hA, if_neg hB, add_zero]
    rw [hlim]
    by_cases hi0 : i = F.least
    · subst hi0
      have hjne : j ≠ F.second := fun h => hA ⟨rfl, h⟩
      have hjl : j ≠ F.least := fun h => hij h.symm
      have hjlt : F.second < j :=
        lt_of_le_of_ne (F.second_le_of_ne_least hjl) (Ne.symm hjne)
      refine hzero (fun σ => F.wt j σ / F.fug F.second σ)
        (F.tendsto_wt_div_fug_second hjlt) ?_
      intro σ hσ
      rw [F.pairTerm_factor]
      exact bound_helper (F.wt_div_fug_least_le_one _ hσ) (F.wt_div_fug_nonneg j F.second σ)
        (sq_nonneg _) (F.sq_clock_sub_le _ _)
    · by_cases hj0 : j = F.least
      · subst hj0
        have hine : i ≠ F.second := fun h => hB ⟨h, rfl⟩
        have hilt : F.second < i :=
          lt_of_le_of_ne (F.second_le_of_ne_least hi0) (Ne.symm hine)
        refine hzero (fun σ => F.wt i σ / F.fug F.second σ)
          (F.tendsto_wt_div_fug_second hilt) ?_
        intro σ hσ
        rw [F.pairTerm_factor_swap]
        exact bound_helper (F.wt_div_fug_least_le_one _ hσ) (F.wt_div_fug_nonneg i F.second σ)
          (sq_nonneg _) (F.sq_clock_sub_le _ _)
      · have hilt : F.least < i := lt_of_le_of_ne (F.least_le i) (Ne.symm hi0)
        refine hzero (fun σ => F.wt i σ / F.fug F.least σ)
          (F.tendsto_wt_div_fug_least hilt) ?_
        intro σ hσ
        rw [F.pairTerm_factor]
        have hcomm : F.wt i σ / F.fug F.least σ * (F.wt j σ / F.fug F.second σ)
            * (F.clock i - F.clock j) ^ 2
            = F.wt j σ / F.fug F.second σ * (F.wt i σ / F.fug F.least σ)
              * (F.clock i - F.clock j) ^ 2 := by
          ring
        rw [hcomm]
        exact bound_helper (F.wt_div_fug_second_le_one hj0 hσ) (F.wt_div_fug_nonneg i F.least σ)
          (sq_nonneg _) (F.sq_clock_sub_le _ _)

theorem sum_pairLimit :
    ∑ i, ∑ j, F.pairLimit i j = 2 * (F.clock F.second - F.clock F.least) ^ 2 := by
  classical
  have key : ∀ (a b i : Fin F.card),
      ∑ j, (if i = a ∧ j = b then (F.clock F.second - F.clock F.least) ^ 2 else 0)
        = if i = a then (F.clock F.second - F.clock F.least) ^ 2 else 0 := by
    intro a b i
    by_cases hi : i = a
    · have hpt : ∀ j : Fin F.card,
          (if i = a ∧ j = b then (F.clock F.second - F.clock F.least) ^ 2 else 0)
            = (if j = b then (F.clock F.second - F.clock F.least) ^ 2 else 0) := by
        intro j
        by_cases hj : j = b <;> simp [hi, hj]
      rw [Finset.sum_congr rfl fun j _ => hpt j, if_pos hi]
      simp
    · have hpt : ∀ j : Fin F.card,
          (if i = a ∧ j = b then (F.clock F.second - F.clock F.least) ^ 2 else 0) = 0 := by
        intro j
        simp [hi]
      rw [Finset.sum_congr rfl fun j _ => hpt j, if_neg hi]
      simp
  have hinner : ∀ i : Fin F.card, ∑ j, F.pairLimit i j
      = (if i = F.least then (F.clock F.second - F.clock F.least) ^ 2 else 0)
        + (if i = F.second then (F.clock F.second - F.clock F.least) ^ 2 else 0) := by
    intro i
    simp only [pairLimit]
    rw [Finset.sum_add_distrib, key F.least F.second i, key F.second F.least i]
  have h1 : ∑ _i : Fin F.card,
      (if _i = F.least then (F.clock F.second - F.clock F.least) ^ 2 else 0)
      = (F.clock F.second - F.clock F.least) ^ 2 := by simp
  have h2 : ∑ _i : Fin F.card,
      (if _i = F.second then (F.clock F.second - F.clock F.least) ^ 2 else 0)
      = (F.clock F.second - F.clock F.least) ^ 2 := by simp
  rw [Finset.sum_congr rfl fun i _ => hinner i, Finset.sum_add_distrib, h1, h2]
  ring

theorem tendsto_gram_div_fug_mul :
    Tendsto (fun σ => (capA (fun i => F.wt i σ) * capC (fun i => F.wt i σ) F.clock
        - capB (fun i => F.wt i σ) F.clock ^ 2) / (F.fug F.least σ * F.fug F.second σ))
      atTop (nhds ((F.clock F.second - F.clock F.least) ^ 2)) := by
  have hrw : ∀ σ : ℝ, (capA (fun i => F.wt i σ) * capC (fun i => F.wt i σ) F.clock
      - capB (fun i => F.wt i σ) F.clock ^ 2) / (F.fug F.least σ * F.fug F.second σ)
      = (∑ i, ∑ j, F.pairTerm i j σ) / 2 := by
    intro σ
    have hpt : ∑ i, ∑ j, F.pairTerm i j σ
        = (∑ i, ∑ j, F.wt i σ * F.wt j σ * (F.clock i - F.clock j) ^ 2)
          / (F.fug F.least σ * F.fug F.second σ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pairTerm]
      ring
    rw [capA_mul_capC_sub_capB_sq, hpt]
    ring
  simp only [hrw]
  have hsum : Tendsto (fun σ => ∑ i, ∑ j, F.pairTerm i j σ) atTop
      (nhds (∑ i, ∑ j, F.pairLimit i j)) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    exact tendsto_finsetSum _ fun j _ => F.tendsto_pairTerm i j
  rw [F.sum_pairLimit] at hsum
  have h := hsum.div_const 2
  simpa using h

/-- **The exact leading asymptotic.** -/
theorem tendsto_capacity_div_fug_second :
    Tendsto (fun σ => F.capacity σ / F.fug F.second σ) atTop
      (nhds (Real.pi ^ 2 * (F.clock F.second - F.clock F.least) ^ 2
        / (F.clock F.least) ^ 2)) := by
  have hl : (F.clock F.least) ^ 2 ≠ 0 := by
    have := F.clock_pos F.least
    positivity
  have hrw : ∀ σ : ℝ, F.capacity σ / F.fug F.second σ
      = Real.pi ^ 2 * ((capA (fun i => F.wt i σ) * capC (fun i => F.wt i σ) F.clock
            - capB (fun i => F.wt i σ) F.clock ^ 2) / (F.fug F.least σ * F.fug F.second σ))
        / (capC (fun i => F.wt i σ) F.clock / F.fug F.least σ) := by
    intro σ
    have hC := (F.energy_moment_pos σ).ne'
    have h0 := (F.fug_pos F.least σ).ne'
    have h1 := (F.fug_pos F.second σ).ne'
    rw [capacity, schurCapacity_eq_ratio (F.energy_moment_pos σ)]
    field_simp
  simp only [hrw]
  have hnum := (F.tendsto_gram_div_fug_mul).const_mul (Real.pi ^ 2)
  have hden := F.tendsto_capC_div_fug_least
  exact hnum.div hden hl

end Aperture

end HTGeometry.ConstraintFrameRelativity

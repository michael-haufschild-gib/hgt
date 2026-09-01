import GaloisForLFunctions.HTGeometry.StaircaseAssignment

/-!
# Degree functions and determinants

A *degree function* on a field is `⊥` exactly at zero, additive on products and subadditive on sums:
the weighted degree of a rational function, the negative of a valuation, the order of a Laurent or
Puiseux germ.  Such a function detects nonvanishing of a determinant whenever the assignment problem
for the matrix of entry degrees has a strict optimum, and in particular whenever the entry degrees
form a staircase.

This is the purely algebraic counterpart of the measured criterion in
`LogScaleDeterminantNonCancellation`: no filter, no analysis, and zero entries are handled for free
because `⊥` is smaller than everything.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [CommRing K] [IsDomain K]

/-- A degree function: `⊥` exactly at zero, additive on products, subadditive on sums. -/
structure IsDegree (d : K → WithBot ℤ) : Prop where
  eq_bot : ∀ x : K, d x = ⊥ ↔ x = 0
  map_mul : ∀ x y : K, d (x * y) = d x + d y
  map_add_le : ∀ x y : K, d (x + y) ≤ max (d x) (d y)

namespace IsDegree

variable {d : K → WithBot ℤ} (hd : IsDegree d)

include hd

omit [IsDomain K] in
theorem ne_bot {x : K} (hx : x ≠ 0) : d x ≠ ⊥ := fun h => hx ((hd.eq_bot x).mp h)

theorem map_one : d 1 = 0 := by
  have h := hd.map_mul 1 1
  rw [one_mul] at h
  obtain ⟨a, ha⟩ : ∃ a : ℤ, d 1 = (a : WithBot ℤ) := by
    cases hdd : d 1 with
    | bot => exact absurd hdd (hd.ne_bot one_ne_zero)
    | coe a => exact ⟨a, rfl⟩
  rw [ha] at h ⊢
  have : (a : ℤ) = a + a := by exact_mod_cast h
  have ha0 : a = 0 := by omega
  rw [ha0]
  rfl

theorem map_neg (x : K) : d (-x) = d x := by
  have hsq : d (-1 : K) + d (-1 : K) = 0 := by
    have := hd.map_mul (-1 : K) (-1 : K)
    rw [neg_mul_neg, one_mul, hd.map_one] at this
    exact this.symm
  obtain ⟨a, ha⟩ : ∃ a : ℤ, d (-1 : K) = (a : WithBot ℤ) := by
    cases hdd : d (-1 : K) with
    | bot => exact absurd hdd (hd.ne_bot (by norm_num))
    | coe a => exact ⟨a, rfl⟩
  rw [ha] at hsq
  have ha0 : a = 0 := by
    have : (a : ℤ) + a = 0 := by exact_mod_cast hsq
    omega
  have hneg : d (-x) = d ((-1 : K) * x) := by rw [neg_one_mul]
  rw [hneg, hd.map_mul, ha, ha0]
  simp

/-- **A strictly dominated summand does not move the degree.** -/
theorem map_add_of_lt {x y : K} (h : d y < d x) : d (x + y) = d x := by
  refine le_antisymm (le_trans (hd.map_add_le x y) (by simp [max_eq_left h.le])) ?_
  have hxy : x = (x + y) + (-y) := by ring
  have h2 : d x ≤ max (d (x + y)) (d y) := by
    calc d x = d ((x + y) + (-y)) := by rw [← hxy]
      _ ≤ max (d (x + y)) (d (-y)) := hd.map_add_le _ _
      _ = max (d (x + y)) (d y) := by rw [hd.map_neg y]
  rcases le_total (d y) (d (x + y)) with hcase | hcase
  · rwa [max_eq_left hcase] at h2
  · rw [max_eq_right hcase] at h2
    exact absurd h (not_lt.mpr h2)

omit [IsDomain K] in
/-- A finite sum of strictly dominated terms is strictly dominated. -/
theorem sum_lt {ι : Type*} {s : Finset ι} {f : ι → K} {c : WithBot ℤ} (hc : c ≠ ⊥)
    (h : ∀ i ∈ s, d (f i) < c) : d (∑ i ∈ s, f i) < c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, (hd.eq_bot 0).mpr rfl]
      exact bot_lt_iff_ne_bot.mpr hc
  | insert b t hb ih =>
      rw [Finset.sum_insert hb]
      refine lt_of_le_of_lt (hd.map_add_le _ _) ?_
      exact max_lt (h b (Finset.mem_insert_self b t))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **A finite sum with a strict maximum has that degree.** -/
theorem map_sum_of_unique_max {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → K} {i₀ : ι}
    (hi₀ : i₀ ∈ s) (hne : f i₀ ≠ 0) (hmax : ∀ i ∈ s, i ≠ i₀ → d (f i) < d (f i₀)) :
    d (∑ i ∈ s, f i) = d (f i₀) := by
  rw [← Finset.add_sum_erase s f hi₀]
  refine hd.map_add_of_lt (hd.sum_lt (hd.ne_bot hne) ?_)
  intro i hi
  exact hmax i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)

end IsDegree

/-- **Nonvanishing of a determinant from a strict optimum of the degree assignment problem.** -/
theorem det_ne_zero_of_unique_max_deg {d : K → WithBot ℤ} (hd : IsDegree d) {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) (σ₀ : Equiv.Perm (Fin N))
    (hne : ∀ i, M (σ₀ i) i ≠ 0)
    (hmax : ∀ σ : Equiv.Perm (Fin N), σ ≠ σ₀ →
      d (∏ i, M (σ i) i) < d (∏ i, M (σ₀ i) i)) :
    M.det ≠ 0 := by
  classical
  set f : Equiv.Perm (Fin N) → K :=
    fun σ => ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, M (σ i) i with hf
  have hsign : ∀ σ : Equiv.Perm (Fin N), d (f σ) = d (∏ i, M (σ i) i) := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [hf]; simp [h]
    · rw [hf]; simp only [h]
      push_cast
      rw [neg_one_mul, hd.map_neg]
  have hprod : ∏ i, M (σ₀ i) i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  have hfne : f σ₀ ≠ 0 := by
    rw [hf]
    exact mul_ne_zero (by rcases Int.units_eq_one_or (Equiv.Perm.sign σ₀) with h | h <;>
      simp [h]) hprod
  have hdet : d M.det = d (f σ₀) := by
    rw [Matrix.det_apply']
    refine hd.map_sum_of_unique_max (Finset.mem_univ σ₀) hfne fun σ _ hσ => ?_
    rw [hsign σ, hsign σ₀]
    exact hmax σ hσ
  intro h0
  rw [h0, (hd.eq_bot 0).mpr rfl] at hdet
  exact hd.ne_bot hfne hdet.symm

/-- The degree of a finite product is the sum of the degrees. -/
theorem IsDegree.map_prod {d : K → WithBot ℤ} (hd : IsDegree d) {ι : Type*}
    (s : Finset ι) (f : ι → K) : d (∏ i ∈ s, f i) = ∑ i ∈ s, d (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hd.map_one
  | insert b t hb ih => rw [Finset.prod_insert hb, Finset.sum_insert hb, hd.map_mul, ih]

/-- Casting a finite integer sum into `WithBot ℤ`. -/
theorem withBot_coe_sum {ι : Type*} (s : Finset ι) (g : ι → ℤ) :
    ((∑ i ∈ s, g i : ℤ) : WithBot ℤ) = ∑ i ∈ s, ((g i : ℤ) : WithBot ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b t hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, ← ih]; rfl

/-- **The staircase criterion, algebraically.**  If the entry degrees are separable on a staircase
cut out by a permutation and strictly sub-separable off it, the determinant is nonzero.  Entries may
vanish off the staircase: `⊥` is strictly smaller than every integer. -/
theorem det_ne_zero_of_staircase_deg {d : K → WithBot ℤ} (hd : IsDegree d) {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) (c w : Fin N → ℤ) (P : Equiv.Perm (Fin N))
    (heq : ∀ i j, j ≤ P i → d (M j i) = ((c i - w j : ℤ) : WithBot ℤ))
    (hlt : ∀ i j, P i < j → d (M j i) < ((c i - w j : ℤ) : WithBot ℤ)) :
    M.det ≠ 0 := by
  classical
  have hstair : ∀ i, M (P i) i ≠ 0 := by
    intro i h0
    have := heq i (P i) le_rfl
    rw [h0, (hd.eq_bot 0).mpr rfl] at this
    exact (WithBot.bot_ne_coe) this
  have htarget : d (∏ i, M (P i) i) = (((∑ i, c i) - ∑ j, w j : ℤ) : WithBot ℤ) := by
    rw [hd.map_prod]
    have : ∀ i : Fin N, d (M (P i) i) = ((c i - w (P i) : ℤ) : WithBot ℤ) :=
      fun i => heq i (P i) le_rfl
    rw [Finset.sum_congr rfl (fun i _ => this i), ← withBot_coe_sum]
    congr 1
    rw [Finset.sum_sub_distrib, Equiv.sum_comp P w]
  refine det_ne_zero_of_unique_max_deg hd M P hstair ?_
  intro σ hσ
  rw [htarget, hd.map_prod]
  by_cases hzero : ∃ i, M (σ i) i = 0
  · obtain ⟨i₀, hi₀⟩ := hzero
    have hbot : d (M (σ i₀) i₀) = ⊥ := (hd.eq_bot _).mpr hi₀
    have : ∑ i, d (M (σ i) i) = ⊥ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hbot]
      exact WithBot.bot_add _
    rw [this]
    exact bot_lt_iff_ne_bot.mpr (by exact WithBot.coe_ne_bot)
  · push Not at hzero
    choose e he using fun i : Fin N => (by
      cases hdd : d (M (σ i) i) with
      | bot => exact absurd hdd (hd.ne_bot (hzero i))
      | coe a => exact ⟨a, rfl⟩ : ∃ a : ℤ, d (M (σ i) i) = (a : WithBot ℤ))
    have hle : ∀ i, e i ≤ c i - w (σ i) := by
      intro i
      rcases le_or_gt (σ i) (P i) with h | h
      · have := heq i (σ i) h
        rw [he i] at this
        exact le_of_eq (by exact_mod_cast this)
      · have := hlt i (σ i) h
        rw [he i] at this
        exact le_of_lt (by exact_mod_cast this)
    obtain ⟨i₀, hi₀⟩ : ∃ i, P i < σ i := by
      by_contra hc
      push Not at hc
      exact hσ (perm_eq_of_le σ P fun i => hc i)
    have hstrict : e i₀ < c i₀ - w (σ i₀) := by
      have := hlt i₀ (σ i₀) hi₀
      rw [he i₀] at this
      exact_mod_cast this
    have hsum : ∑ i, e i < (∑ i, c i) - ∑ j, w j := by
      calc ∑ i, e i < ∑ i, (c i - w (σ i)) :=
            Finset.sum_lt_sum (fun i _ => hle i) ⟨i₀, Finset.mem_univ _, hstrict⟩
        _ = (∑ i, c i) - ∑ j, w j := by rw [Finset.sum_sub_distrib, Equiv.sum_comp σ w]
    rw [Finset.sum_congr rfl (fun i _ => he i), ← withBot_coe_sum]
    exact_mod_cast hsum

end GaloisForLFunctions.HTGeometry

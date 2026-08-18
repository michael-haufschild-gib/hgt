import Mathlib

/-!
# Bagchi's rounding lemma

A combination `∑ a_j x_j` of `n` vectors of a `d`-dimensional complex normed space, with all
coefficients in the closed unit disc, can be replaced by a combination with all coefficients on the
unit *circle*, at a total cost of at most `d` times the largest vector:

```text
‖∑ b_j x_j - ∑ a_j x_j‖  ≤  d · max_j ‖x_j‖ ,      |b_j| = 1 .
```

This is Lemma 4.1 of Bagchi's joint universality paper, used by Andersson (arXiv:2408.15713,
Lemma 3) to turn a solution of a linear system with coefficients bounded by one into a genuinely
unimodular multiplicative phase.

The proof is the standard exchange argument.  While more than `d` coefficients are strictly inside
the disc, the corresponding vectors are linearly dependent, so the coefficient vector may be moved
along a line in the kernel — leaving the combination unchanged — until one more coefficient reaches
the circle.  Once at most `d` coefficients remain inside, each is radially pushed to the circle, at
a cost of at most `1 - |a_j| ≤ 1` per coefficient.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Moving from a point strictly inside the unit disc along a nonzero direction, there is a first
time at which the unit circle is reached. -/
theorem exists_first_hit_one {u v : ℂ} (hu : ‖u‖ < 1) (hv : v ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ‖u + (t : ℂ) * v‖ = 1 ∧
      ∀ r : ℝ, 0 ≤ r → r < t → ‖u + (r : ℂ) * v‖ < 1 := by
  classical
  set f : ℝ → ℝ := fun t => ‖u + (t : ℂ) * v‖ with hfdef
  have hfcont : Continuous f := by
    refine Continuous.norm ?_
    exact continuous_const.add ((Complex.continuous_ofReal).mul continuous_const)
  have hf0 : f 0 < 1 := by simpa [hfdef] using hu
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set T : ℝ := (1 + ‖u‖) / ‖v‖ with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hfT : 1 ≤ f T := by
    have h1 : ‖(T : ℂ) * v‖ = T * ‖v‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hT0]
    have h2 : ‖(T : ℂ) * v‖ - ‖u‖ ≤ ‖u + (T : ℂ) * v‖ := by
      have := norm_sub_norm_le ((T : ℂ) * v) (-u)
      simp only [norm_neg, sub_neg_eq_add] at this
      calc ‖(T : ℂ) * v‖ - ‖u‖ ≤ ‖(T : ℂ) * v - -u‖ := by
            have h3 := norm_sub_norm_le ((T : ℂ) * v) (-u)
            simpa using h3
        _ = ‖u + (T : ℂ) * v‖ := by rw [sub_neg_eq_add]; rw [add_comm]
    rw [h1] at h2
    have h4 : T * ‖v‖ = 1 + ‖u‖ := by
      rw [hTdef, div_mul_cancel₀ _ (ne_of_gt hvpos)]
    rw [h4] at h2
    simpa [hfdef] using by linarith
  set S : Set ℝ := {t : ℝ | 0 ≤ t ∧ 1 ≤ f t} with hSdef
  have hSne : S.Nonempty := ⟨T, hT0, hfT⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  have hSclosed : IsClosed S := by
    have h1 : IsClosed {t : ℝ | 0 ≤ t} := isClosed_le continuous_const continuous_id
    have h2 : IsClosed {t : ℝ | 1 ≤ f t} := isClosed_le continuous_const hfcont
    exact h1.inter h2
  set t : ℝ := sInf S with htdef
  have htS : t ∈ S := hSclosed.csInf_mem hSne hSbdd
  have ht0 : 0 ≤ t := htS.1
  have htpos : 0 < t := by
    rcases lt_or_eq_of_le ht0 with h | h
    · exact h
    · exfalso
      rw [← h] at htS
      linarith [htS.2, hf0]
  have hlow : ∀ r : ℝ, 0 ≤ r → r < t → f r < 1 := by
    intro r hr0 hrt
    by_contra hc
    have : r ∈ S := ⟨hr0, not_lt.mp hc⟩
    exact absurd (csInf_le hSbdd this) (not_le.mpr hrt)
  have hle : f t ≤ 1 := by
    have hnb : (nhdsWithin t (Set.Iio t)).NeBot := by infer_instance
    have htend : Filter.Tendsto f (nhdsWithin t (Set.Iio t)) (nhds (f t)) :=
      (hfcont.tendsto t).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_gt_nhds htpos)] with r hr1 hr2
    exact le_of_lt (hlow r (le_of_lt hr2) hr1)
  exact ⟨t, htpos, le_antisymm hle htS.2, hlow⟩


variable [FiniteDimensional ℂ E]

/-- **One exchange step.**  With more coefficients strictly inside the disc than the dimension, one
of them can be moved to the unit circle without changing the combination. -/
theorem exists_reduce_free {n : ℕ} (x : Fin n → E) (a : Fin n → ℂ) (ha : ∀ j, ‖a j‖ ≤ 1)
    (hcard : Module.finrank ℂ E
      < (Finset.univ.filter (fun j : Fin n => ‖a j‖ < 1)).card) :
    ∃ a' : Fin n → ℂ, (∀ j, ‖a' j‖ ≤ 1) ∧ (∑ j, a' j • x j = ∑ j, a j • x j) ∧
      (Finset.univ.filter (fun j : Fin n => ‖a' j‖ < 1)).card
        < (Finset.univ.filter (fun j : Fin n => ‖a j‖ < 1)).card := by
  classical
  set Fr : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => ‖a j‖ < 1) with hFrdef
  have hFrlt : ∀ j ∈ Fr, ‖a j‖ < 1 := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  -- linear dependence of the free vectors
  have hdep : ¬ LinearIndependent ℂ (fun i : (Fr : Finset (Fin n)) => x (i : Fin n)) := by
    intro hli
    have hle := hli.fintype_card_le_finrank
    rw [Fintype.card_coe] at hle
    omega
  obtain ⟨g, hgsum, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  set c : Fin n → ℂ := fun j => if h : j ∈ Fr then g ⟨j, h⟩ else 0 with hcdef
  have hczero : ∀ j, j ∉ Fr → c j = 0 := by
    intro j hj
    rw [hcdef]
    simp only
    rw [dif_neg hj]
  have hcmem : ∀ j, c j ≠ 0 → j ∈ Fr := by
    intro j hj
    by_contra hc
    exact hj (hczero j hc)
  have hcsum : ∑ j, c j • x j = 0 := by
    have h1 : ∑ j ∈ Fr, c j • x j = ∑ i : (Fr : Finset (Fin n)), g i • x (i : Fin n) := by
      rw [← Finset.sum_attach Fr (fun j => c j • x j)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcdef]
      simp only
      rw [dif_pos i.2]
    have h2 : ∑ j, c j • x j = ∑ j ∈ Fr, c j • x j := by
      refine (Finset.sum_subset (Finset.subset_univ Fr) ?_).symm
      intro j _ hj
      rw [hczero j hj, zero_smul]
    rw [h2, h1, hgsum]
  -- the first hitting times
  have hex : ∀ j : Fin n, ∃ t : ℝ, c j ≠ 0 →
      (0 < t ∧ ‖a j + (t : ℂ) * c j‖ = 1 ∧
        ∀ r : ℝ, 0 ≤ r → r < t → ‖a j + (r : ℂ) * c j‖ < 1) := by
    intro j
    by_cases h : c j = 0
    · exact ⟨0, fun hc => absurd h hc⟩
    · obtain ⟨t, ht⟩ := exists_first_hit_one (hFrlt j (hcmem j h)) h
      exact ⟨t, fun _ => ht⟩
  choose t ht using hex
  set J : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => c j ≠ 0) with hJdef
  have hJne : J.Nonempty := by
    refine ⟨(i₀ : Fin n), ?_⟩
    rw [hJdef, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hcdef]
    simp only
    rw [dif_pos i₀.2]
    simpa using hi₀
  obtain ⟨jstar, hjstar, hjstareq⟩ := Finset.exists_mem_eq_inf' hJne t
  set t₀ : ℝ := J.inf' hJne t with ht₀def
  have hjstarc : c jstar ≠ 0 := (Finset.mem_filter.mp hjstar).2
  refine ⟨fun j => a j + (t₀ : ℂ) * c j, ?_, ?_, ?_⟩
  · intro j
    show ‖a j + (t₀ : ℂ) * c j‖ ≤ 1
    by_cases hc : c j = 0
    · rw [hc, mul_zero, add_zero]
      exact ha j
    · have hmin : t₀ ≤ t j := by
        rw [ht₀def]
        exact Finset.inf'_le _ (by rw [hJdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hc⟩)
      rcases lt_or_eq_of_le hmin with hlt | heq
      · exact le_of_lt ((ht j hc).2.2 t₀ (by
          rw [ht₀def]
          exact le_of_lt (lt_of_lt_of_le (ht jstar hjstarc).1 (by rw [← hjstareq]))) hlt)
      · rw [heq]
        exact le_of_eq (ht j hc).2.1
  · show ∑ j, (a j + (t₀ : ℂ) * c j) • x j = ∑ j, a j • x j
    have h1 : ∑ j, ((t₀ : ℂ) * c j) • x j = (t₀ : ℂ) • ∑ j, c j • x j := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
    calc ∑ j, (a j + (t₀ : ℂ) * c j) • x j
        = ∑ j, (a j • x j + ((t₀ : ℂ) * c j) • x j) := by
          exact Finset.sum_congr rfl fun j _ => by rw [add_smul]
      _ = (∑ j, a j • x j) + ∑ j, ((t₀ : ℂ) * c j) • x j := Finset.sum_add_distrib
      _ = ∑ j, a j • x j := by rw [h1, hcsum, smul_zero, add_zero]
  · have hsub : (Finset.univ.filter (fun j : Fin n => ‖a j + (t₀ : ℂ) * c j‖ < 1)) ⊆ Fr := by
      intro j hj
      have hj' : ‖a j + (t₀ : ℂ) * c j‖ < 1 := (Finset.mem_filter.mp hj).2
      by_cases hc : c j = 0
      · rw [hFrdef, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hc, mul_zero, add_zero] at hj'
        exact hj'
      · exact hcmem j hc
    have hnotmem : jstar ∉ (Finset.univ.filter (fun j : Fin n => ‖a j + (t₀ : ℂ) * c j‖ < 1)) := by
      intro hmem
      have hj' : ‖a jstar + (t₀ : ℂ) * c jstar‖ < 1 := (Finset.mem_filter.mp hmem).2
      have heq : t₀ = t jstar := hjstareq
      rw [heq] at hj'
      linarith [(ht jstar hjstarc).2.1]
    have hjstarFr : jstar ∈ Fr := hcmem jstar hjstarc
    exact Finset.card_lt_card ⟨hsub, fun hcon => hnotmem (hcon hjstarFr)⟩


omit [FiniteDimensional ℂ E] in
/-- **Radial rounding.**  If at most `d` coefficients are strictly inside the disc, pushing each of
them radially to the circle costs at most `d` times the largest vector. -/
theorem exists_rounding_of_card_le {n : ℕ} (x : Fin n → E) (a : Fin n → ℂ)
    (ha : ∀ j, ‖a j‖ ≤ 1) {C : ℝ} (hC : ∀ j, ‖x j‖ ≤ C) (hC0 : 0 ≤ C) {d : ℕ}
    (hcard : (Finset.univ.filter (fun j : Fin n => ‖a j‖ < 1)).card ≤ d) :
    ∃ b : Fin n → ℂ, (∀ j, ‖b j‖ = 1) ∧
      ‖∑ j, b j • x j - ∑ j, a j • x j‖ ≤ (d : ℝ) * C := by
  classical
  set Fr : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => ‖a j‖ < 1) with hFrdef
  set b : Fin n → ℂ := fun j => if a j = 0 then 1 else a j / ((‖a j‖ : ℝ) : ℂ) with hbdef
  have hbnorm : ∀ j, ‖b j‖ = 1 := by
    intro j
    rw [hbdef]
    simp only
    by_cases h : a j = 0
    · rw [if_pos h, norm_one]
    · rw [if_neg h, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (by simpa using h)]
  have hbeq : ∀ j, j ∉ Fr → b j = a j := by
    intro j hj
    have h1 : ¬ ‖a j‖ < 1 := by
      intro hc
      exact hj (by rw [hFrdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hc⟩)
    have h2 : ‖a j‖ = 1 := le_antisymm (ha j) (not_lt.mp h1)
    have hne : a j ≠ 0 := by
      intro hc
      rw [hc, norm_zero] at h2
      norm_num at h2
    rw [hbdef]
    simp only
    rw [if_neg hne, h2]
    norm_num
  have hbdiff : ∀ j, ‖b j - a j‖ ≤ 1 := by
    intro j
    rw [hbdef]
    simp only
    by_cases h : a j = 0
    · rw [if_pos h, h, sub_zero, norm_one]
    · rw [if_neg h]
      have hpos : (0:ℝ) < ‖a j‖ := norm_pos_iff.mpr h
      have hfac : a j / ((‖a j‖ : ℝ) : ℂ) - a j = a j * (((‖a j‖ : ℝ) : ℂ)⁻¹ - 1) := by
        field_simp
      rw [hfac, norm_mul]
      have hinv : ‖((‖a j‖ : ℝ) : ℂ)⁻¹ - 1‖ = 1 / ‖a j‖ - 1 := by
        have h1 : ((‖a j‖ : ℝ) : ℂ)⁻¹ - 1 = (((1 / ‖a j‖ - 1 : ℝ)) : ℂ) := by
          push_cast
          field_simp
        rw [h1, Complex.norm_real, Real.norm_of_nonneg ?_]
        rw [le_sub_iff_add_le, zero_add, le_div_iff₀ hpos, one_mul]
        exact ha j
      rw [hinv]
      have : ‖a j‖ * (1 / ‖a j‖ - 1) = 1 - ‖a j‖ := by field_simp
      rw [this]
      linarith [norm_nonneg (a j)]
  refine ⟨b, hbnorm, ?_⟩
  have hsub : ∑ j, b j • x j - ∑ j, a j • x j = ∑ j ∈ Fr, (b j - a j) • x j := by
    rw [← Finset.sum_sub_distrib]
    have hall : ∑ j, (b j • x j - a j • x j) = ∑ j, (b j - a j) • x j :=
      Finset.sum_congr rfl fun j _ => by rw [sub_smul]
    rw [hall]
    refine (Finset.sum_subset (Finset.subset_univ Fr) ?_).symm
    intro j _ hj
    rw [hbeq j hj, sub_self, zero_smul]
  rw [hsub]
  calc ‖∑ j ∈ Fr, (b j - a j) • x j‖ ≤ ∑ j ∈ Fr, ‖(b j - a j) • x j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Fr, C := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul]
        calc ‖b j - a j‖ * ‖x j‖ ≤ 1 * ‖x j‖ :=
              mul_le_mul_of_nonneg_right (hbdiff j) (norm_nonneg _)
          _ = ‖x j‖ := one_mul _
          _ ≤ C := hC j
    _ = (Fr.card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d : ℝ) * C := by
        refine mul_le_mul_of_nonneg_right ?_ hC0
        exact_mod_cast hcard

/-- **Bagchi's rounding lemma.** -/
theorem exists_unimodular_rounding {n : ℕ} (x : Fin n → E) (a : Fin n → ℂ)
    (ha : ∀ j, ‖a j‖ ≤ 1) {C : ℝ} (hC : ∀ j, ‖x j‖ ≤ C) (hC0 : 0 ≤ C) :
    ∃ b : Fin n → ℂ, (∀ j, ‖b j‖ = 1) ∧
      ‖∑ j, b j • x j - ∑ j, a j • x j‖ ≤ (Module.finrank ℂ E : ℝ) * C := by
  classical
  suffices h : ∀ (m : ℕ) (a : Fin n → ℂ), (∀ j, ‖a j‖ ≤ 1) →
      (Finset.univ.filter (fun j : Fin n => ‖a j‖ < 1)).card ≤ m →
      ∃ b : Fin n → ℂ, (∀ j, ‖b j‖ = 1) ∧
        ‖∑ j, b j • x j - ∑ j, a j • x j‖ ≤ (Module.finrank ℂ E : ℝ) * C by
    exact h _ a ha (le_refl _)
  intro m
  induction m with
  | zero =>
      intro a ha hcard
      exact exists_rounding_of_card_le x a ha hC hC0 (le_trans hcard (Nat.zero_le _))
  | succ m ih =>
      intro a ha hcard
      by_cases hle : (Finset.univ.filter (fun j : Fin n => ‖a j‖ < 1)).card
          ≤ Module.finrank ℂ E
      · exact exists_rounding_of_card_le x a ha hC hC0 hle
      · obtain ⟨a', ha', hsum, hlt⟩ := exists_reduce_free x a ha (not_le.mp hle)
        obtain ⟨b, hb, hbound⟩ := ih a' ha' (by omega)
        exact ⟨b, hb, by rw [hsum] at hbound; exact hbound⟩

end GaloisForLFunctions.HTGeometry

end

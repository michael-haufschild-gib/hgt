import Mathlib

/-!
# Counting an interval by residues

The remainder of a sieve compares the number of integers of an interval satisfying a congruence
condition with its expected density.  Both sides split over the residues modulo the sieve's divisor,
so the comparison reduces to the elementary count of an interval inside one residue class, which is
its length over the modulus up to one unit.
-/

namespace RHTower.Sieve

open Finset

/-- **A congruence-invariant condition splits over residues.** -/
theorem card_filter_eq_sum_residues {e : ℕ} (he : 0 < e) (M : ℕ) (P : ℕ → Prop)
    [DecidablePred P] (hP : ∀ m₁ m₂ : ℕ, m₁ % e = m₂ % e → (P m₁ ↔ P m₂)) :
    (((Finset.Icc 1 M).filter P).card)
      = ∑ r ∈ (Finset.range e).filter P,
          (((Finset.Icc 1 M).filter (fun m => m % e = r)).card) := by
  classical
  have hcongr : ∀ r ∈ (Finset.range e).filter P,
      ((Finset.Icc 1 M).filter (fun m => m % e = r)).card
        = ((Finset.Icc 1 M).filter (fun m => P m ∧ m % e = r)).card := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    refine congrArg Finset.card (Finset.filter_congr fun m hm => ?_)
    constructor
    · intro hmr
      refine ⟨?_, hmr⟩
      refine (hP m r ?_).2 hr.2
      rw [hmr, Nat.mod_eq_of_lt hr.1]
    · intro h
      exact h.2
  rw [Finset.sum_congr rfl hcongr]
  have hdisj : ∀ r ∈ (Finset.range e).filter P, ∀ r' ∈ (Finset.range e).filter P, r ≠ r' →
      Disjoint ((Finset.Icc 1 M).filter (fun m => P m ∧ m % e = r))
        ((Finset.Icc 1 M).filter (fun m => P m ∧ m % e = r')) := by
    intro r _ r' _ hne
    refine Finset.disjoint_left.2 fun m hm hm' => ?_
    rw [Finset.mem_filter] at hm hm'
    exact hne (hm.2.2 ▸ hm'.2.2 ▸ rfl)
  rw [← Finset.card_biUnion hdisj]
  refine congrArg Finset.card (Finset.ext fun m => ?_)
  rw [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨hmI, hmP⟩
    refine ⟨m % e, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ he, ?_⟩
      exact (hP (m % e) m (by simp)).2 hmP
    · exact Finset.mem_filter.2 ⟨hmI, hmP, rfl⟩
  · rintro ⟨r, -, hmr⟩
    rw [Finset.mem_filter] at hmr
    exact ⟨hmr.1, hmr.2.1⟩

/-- **An interval meets a residue class in its length over the modulus, up to one.** -/
theorem card_residue_class_le {e : ℕ} (he : 0 < e) (M r : ℕ) :
    (((Finset.Icc 1 M).filter (fun m => m % e = r)).card : ℝ) ≤ (M : ℝ) / (e : ℝ) + 1 := by
  classical
  have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  set F : Finset ℕ := (Finset.Icc 1 M).filter (fun m => m % e = r) with hF
  have hmap : ∀ m ∈ F, m / e ∈ Finset.range (M / e + 1) := by
    intro m hm
    rw [hF, Finset.mem_filter, Finset.mem_Icc] at hm
    rw [Finset.mem_range]
    have : m / e ≤ M / e := Nat.div_le_div_right hm.1.2
    omega
  have hinj : ∀ m ∈ F, ∀ n ∈ F, m / e = n / e → m = n := by
    intro m hm n hn hmn
    rw [hF, Finset.mem_filter] at hm hn
    have hm' := Nat.div_add_mod m e
    have hn' := Nat.div_add_mod n e
    rw [hm.2] at hm'
    rw [hn.2] at hn'
    rw [hmn] at hm'
    exact hm'.symm.trans hn'
  have hcard : F.card ≤ (Finset.range (M / e + 1)).card :=
    Finset.card_le_card_of_injOn (fun m => m / e) hmap (fun m hm n hn h => hinj m hm n hn h)
  rw [Finset.card_range] at hcard
  have hcast : (F.card : ℝ) ≤ ((M / e : ℕ) : ℝ) + 1 := by
    have : (F.card : ℝ) ≤ ((M / e + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    push_cast at this
    linarith
  have hdiv : ((M / e : ℕ) : ℝ) ≤ (M : ℝ) / (e : ℝ) := Nat.cast_div_le
  linarith

/-- **An interval meets a residue class at least its length over the modulus, minus one.** -/
theorem card_residue_class_ge {e : ℕ} (he : 0 < e) (M : ℕ) {r : ℕ} (hr : r < e) :
    (M : ℝ) / (e : ℝ) - 1
      ≤ ((((Finset.Icc 1 M).filter (fun m => m % e = r)).card : ℕ) : ℝ) := by
  classical
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  set r' : ℕ := if r = 0 then e else r with hr'
  have hr'1 : 1 ≤ r' := by
    rw [hr']
    split_ifs with h <;> omega
  have hr'e : r' ≤ e := by
    rw [hr']
    split_ifs with h <;> omega
  have hr'mod : r' % e = r := by
    rw [hr']
    split_ifs with h
    · rw [Nat.mod_self, h]
    · exact Nat.mod_eq_of_lt hr
  rcases Nat.lt_or_ge M r' with hMr | hMr
  · have h1 : (M : ℝ) < (r' : ℝ) := by exact_mod_cast hMr
    have h2 : (r' : ℝ) ≤ (e : ℝ) := by exact_mod_cast hr'e
    have : (M : ℝ) / (e : ℝ) ≤ 1 := by
      rw [div_le_one heR]
      linarith
    have h0 : (0 : ℝ) ≤ ((((Finset.Icc 1 M).filter (fun m => m % e = r)).card : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  · set J : ℕ := (M - r') / e + 1 with hJ
    have hmaps : ∀ j ∈ Finset.range J, j * e + r' ∈ (Finset.Icc 1 M).filter (fun m => m % e = r) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hjle : j ≤ (M - r') / e := by omega
      have hup : j * e ≤ M - r' := by
        calc j * e ≤ ((M - r') / e) * e := Nat.mul_le_mul_right e hjle
          _ ≤ M - r' := Nat.div_mul_le_self _ _
      refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, hr'mod]
    have hinj : ∀ j ∈ Finset.range J, ∀ j' ∈ Finset.range J, j * e + r' = j' * e + r' → j = j' := by
      intro j _ j' _ hEq
      have : j * e = j' * e := by omega
      exact Nat.eq_of_mul_eq_mul_right he this
    have hcard : J ≤ ((Finset.Icc 1 M).filter (fun m => m % e = r)).card := by
      have := Finset.card_le_card_of_injOn (fun j => j * e + r') hmaps
        (fun j hj j' hj' h => hinj j (by simpa using hj) j' (by simpa using hj') h)
      rwa [Finset.card_range] at this
    have hJR : (M : ℝ) / (e : ℝ) - 1 ≤ (J : ℝ) := by
      have hr'R : (r' : ℝ) ≤ (e : ℝ) := by exact_mod_cast hr'e
      have hkey : (M - r' : ℕ) < ((M - r') / e + 1) * e := by
        have h1 := Nat.div_add_mod (M - r') e
        have h2 : (M - r') % e < e := Nat.mod_lt _ he
        nlinarith [h1, h2]
      have hcast : ((M - r' : ℕ) : ℝ) < ((((M - r') / e : ℕ) : ℝ) + 1) * (e : ℝ) := by
        exact_mod_cast hkey
      rw [Nat.cast_sub hMr] at hcast
      have hstep : (M : ℝ) / (e : ℝ) - 1 ≤ ((M : ℝ) - (r' : ℝ)) / (e : ℝ) := by
        rw [sub_div]
        have hone : (r' : ℝ) / (e : ℝ) ≤ 1 := by
          rw [div_le_one heR]
          exact hr'R
        linarith
      have hfrac : ((M : ℝ) - (r' : ℝ)) / (e : ℝ) ≤ (((M - r') / e : ℕ) : ℝ) + 1 := by
        rw [div_le_iff₀ heR]
        linarith [hcast]
      rw [hJ]
      push_cast
      linarith [hstep, hfrac]
    have hJcast : (J : ℝ) ≤ ((((Finset.Icc 1 M).filter (fun m => m % e = r)).card : ℕ) : ℝ) := by
      exact_mod_cast hcard
    linarith

end RHTower.Sieve

import GaloisForLFunctions.HTGeometry.ParabolicOrbifoldTwelveCharge

/-!
# The six parabolic sphere signatures are exactly the parabolic data

The parabolic sphere signatures are enumerated, and every statement about them is a statement about
that enumeration.  Nothing says the list is complete.  It is: a cone point of order `k ≥ 2` has angle
defect `1 - 1/k ∈ [1/2, 1)` and a cusp has defect `1`, so total defect `2` bounds the number of cone
points by four and the number of cusps by two, and the remaining cases are the classical solutions of
`1/a + 1/b + 1/c = 1`.

* `coneDefect`, `orbifoldDefect`;
* **`parabolic_triple_classification`** — `1/a + 1/b + 1/c = 1` for `2 ≤ a ≤ b ≤ c` has exactly the
  solutions `(2,3,6)`, `(2,4,4)`, `(3,3,3)`;
* **`parabolic_signature_classification`** — every parabolic cone-order list with its cusp count is
  one of six;
* **`exists_parabolicSphereSignature_iff`** — the enumeration is exactly the parabolic data.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Angle defect of a cone point of order `k`. -/
def coneDefect (k : ℕ) : ℚ := 1 - ((k : ℚ))⁻¹

/-- Total angle defect of a list of cone orders together with a cusp count, each cusp contributing
one. -/
def orbifoldDefect (m : List ℕ) (c : ℕ) : ℚ := (m.map coneDefect).sum + c

theorem coneDefect_ge_half {k : ℕ} (hk : 2 ≤ k) : (1 : ℚ) / 2 ≤ coneDefect k := by
  have hk2 : (2 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hinv : ((k : ℚ))⁻¹ ≤ (2 : ℚ)⁻¹ := by
    apply inv_anti₀ (by norm_num) hk2
  rw [coneDefect]
  linarith

theorem coneDefect_lt_one {k : ℕ} (hk : 2 ≤ k) : coneDefect k < 1 := by
  have hk2 : (2 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hpos : (0 : ℚ) < ((k : ℚ))⁻¹ := by positivity
  rw [coneDefect]
  linarith

theorem coneDefect_eq_half {k : ℕ} (hk : 2 ≤ k) (h : coneDefect k = (1 : ℚ) / 2) : k = 2 := by
  have hk0 : (k : ℚ) ≠ 0 := by
    have : (2 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
    linarith
  rw [coneDefect] at h
  have : (k : ℚ) = 2 := by
    field_simp at h
    linarith
  exact_mod_cast this

theorem coneDefectSum_nonneg (m : List ℕ) (hm : ∀ k ∈ m, 2 ≤ k) :
    0 ≤ (m.map coneDefect).sum := by
  induction m with
  | nil => simp
  | cons a t ih =>
    have ha := coneDefect_ge_half (hm a (List.mem_cons_self ..))
    have ht := ih fun k hk => hm k (List.mem_cons_of_mem a hk)
    simp only [List.map_cons, List.sum_cons]
    linarith

/-! ### The parabolic triples -/

/-- **The parabolic triples.**  For weakly increasing cone orders at least two, the reciprocal sum
is one exactly for `(2,3,6)`, `(2,4,4)` and `(3,3,3)`. -/
theorem parabolic_triple_classification {a b c : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hsum : ((a : ℚ))⁻¹ + ((b : ℚ))⁻¹ + ((c : ℚ))⁻¹ = 1) :
    (a = 2 ∧ b = 3 ∧ c = 6) ∨ (a = 2 ∧ b = 4 ∧ c = 4) ∨ (a = 3 ∧ b = 3 ∧ c = 3) := by
  have hb : 2 ≤ b := le_trans ha hab
  have hc : 2 ≤ c := le_trans hb hbc
  have haq : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hbq : (2 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
  have hcq : (2 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc
  have habq : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast hab
  have hbcq : (b : ℚ) ≤ (c : ℚ) := by exact_mod_cast hbc
  have hinvba : ((b : ℚ))⁻¹ ≤ ((a : ℚ))⁻¹ := inv_anti₀ (by linarith) habq
  have hinvcb : ((c : ℚ))⁻¹ ≤ ((b : ℚ))⁻¹ := inv_anti₀ (by linarith) hbcq
  have hale : a ≤ 3 := by
    by_contra hcon
    push Not at hcon
    have h4 : (4 : ℚ) ≤ (a : ℚ) := by exact_mod_cast hcon
    have : ((a : ℚ))⁻¹ ≤ (4 : ℚ)⁻¹ := inv_anti₀ (by norm_num) h4
    have hb4 : ((b : ℚ))⁻¹ ≤ (4 : ℚ)⁻¹ := le_trans hinvba this
    have hc4 : ((c : ℚ))⁻¹ ≤ (4 : ℚ)⁻¹ := le_trans hinvcb hb4
    linarith
  interval_cases a
  · -- a = 2
    have hsum2 : ((b : ℚ))⁻¹ + ((c : ℚ))⁻¹ = 1 / 2 := by
      norm_num at hsum
      linarith
    have hble : b ≤ 4 := by
      by_contra hcon
      push Not at hcon
      have h5 : (5 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hcon
      have hb5 : ((b : ℚ))⁻¹ ≤ (5 : ℚ)⁻¹ := inv_anti₀ (by norm_num) h5
      have hc5 : ((c : ℚ))⁻¹ ≤ (5 : ℚ)⁻¹ := le_trans hinvcb hb5
      linarith
    have hbgt : 3 ≤ b := by
      by_contra hcon
      push Not at hcon
      have : b = 2 := by omega
      subst this
      have hcpos : (0 : ℚ) < ((c : ℚ))⁻¹ := by positivity
      norm_num at hsum2
      linarith
    interval_cases b
    · left
      refine ⟨rfl, rfl, ?_⟩
      have : ((c : ℚ))⁻¹ = 1 / 6 := by norm_num at hsum2; linarith
      have hc0 : (c : ℚ) ≠ 0 := by linarith
      have : (c : ℚ) = 6 := by field_simp at this; linarith
      exact_mod_cast this
    · right; left
      refine ⟨rfl, rfl, ?_⟩
      have : ((c : ℚ))⁻¹ = 1 / 4 := by norm_num at hsum2; linarith
      have hc0 : (c : ℚ) ≠ 0 := by linarith
      have : (c : ℚ) = 4 := by field_simp at this; linarith
      exact_mod_cast this
  · -- a = 3
    have hb3 : b = 3 := by
      by_contra hcon
      have hb4 : 4 ≤ b := by omega
      have h4 : (4 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb4
      have hbi : ((b : ℚ))⁻¹ ≤ (4 : ℚ)⁻¹ := inv_anti₀ (by norm_num) h4
      have hci : ((c : ℚ))⁻¹ ≤ (4 : ℚ)⁻¹ := le_trans hinvcb hbi
      norm_num at hsum
      linarith
    subst hb3
    right; right
    refine ⟨rfl, rfl, ?_⟩
    have : ((c : ℚ))⁻¹ = 1 / 3 := by norm_num at hsum; linarith
    have hc0 : (c : ℚ) ≠ 0 := by linarith
    have : (c : ℚ) = 3 := by field_simp at this; linarith
    exact_mod_cast this

/-! ### The classification -/

/-- **Every parabolic cone datum is one of six.**  Cone defects lie in `[1/2, 1)` and cusps
contribute one, so the list has at most four entries; the remaining cases are the reciprocal
equations solved above. -/
theorem parabolic_signature_classification {m : List ℕ} {c : ℕ}
    (hm : ∀ k ∈ m, 2 ≤ k) (hsorted : m.Pairwise (· ≤ ·)) (hdef : orbifoldDefect m c = 2) :
    (m = [] ∧ c = 2) ∨ (m = [2, 2] ∧ c = 1) ∨ (m = [2, 2, 2, 2] ∧ c = 0) ∨
      (m = [2, 3, 6] ∧ c = 0) ∨ (m = [2, 4, 4] ∧ c = 0) ∨ (m = [3, 3, 3] ∧ c = 0) := by
  rcases m with _ | ⟨a, _ | ⟨b, _ | ⟨e, _ | ⟨d, _ | ⟨f, t⟩⟩⟩⟩⟩
  · left
    refine ⟨rfl, ?_⟩
    simp only [orbifoldDefect, List.map_nil, List.sum_nil, zero_add] at hdef
    exact_mod_cast hdef
  · exfalso
    have ha := hm a (by simp)
    have h1 := coneDefect_ge_half ha
    have h2 := coneDefect_lt_one ha
    simp only [orbifoldDefect, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hdef
    have hlt : (c : ℚ) < 2 := by linarith
    have hgt : (1 : ℚ) < (c : ℚ) := by linarith
    have h3 : c < 2 := by exact_mod_cast hlt
    have h4 : 1 < c := by exact_mod_cast hgt
    omega
  · have ha := hm a (by simp)
    have hb := hm b (by simp)
    have ha1 := coneDefect_ge_half ha
    have ha2 := coneDefect_lt_one ha
    have hb1 := coneDefect_ge_half hb
    have hb2 := coneDefect_lt_one hb
    simp only [orbifoldDefect, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hdef
    have hlt : (c : ℚ) < 2 := by linarith
    have hgt : (0 : ℚ) < (c : ℚ) := by linarith
    have h3 : c < 2 := by exact_mod_cast hlt
    have h4 : 0 < c := by exact_mod_cast hgt
    have hc1 : c = 1 := by omega
    subst hc1
    have haval : coneDefect a = 1 / 2 := by
      norm_num at hdef
      linarith
    have hbval : coneDefect b = 1 / 2 := by
      norm_num at hdef
      linarith
    rw [coneDefect_eq_half ha haval, coneDefect_eq_half hb hbval]
    right; left
    exact ⟨rfl, rfl⟩
  · have ha := hm a (by simp)
    have hb := hm b (by simp)
    have he := hm e (by simp)
    have ha1 := coneDefect_ge_half ha
    have hb1 := coneDefect_ge_half hb
    have he1 := coneDefect_ge_half he
    have ha2 := coneDefect_lt_one ha
    have hb2 := coneDefect_lt_one hb
    have he2 := coneDefect_lt_one he
    simp only [orbifoldDefect, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hdef
    have hlt : (c : ℚ) < 1 := by linarith
    have h3 : c < 1 := by exact_mod_cast hlt
    have hc0 : c = 0 := by omega
    subst hc0
    simp only [List.pairwise_cons] at hsorted
    obtain ⟨hfa, hrest⟩ := hsorted
    obtain ⟨hfb, -⟩ := hrest
    have hab : a ≤ b := hfa b (by simp)
    have hbe : b ≤ e := hfb e (by simp)
    have hsum : ((a : ℚ))⁻¹ + ((b : ℚ))⁻¹ + ((e : ℚ))⁻¹ = 1 := by
      simp only [coneDefect] at hdef
      push_cast at hdef
      linarith
    rcases parabolic_triple_classification ha hab hbe hsum with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩
    · right; right; right; left; exact ⟨rfl, rfl⟩
    · right; right; right; right; left; exact ⟨rfl, rfl⟩
    · right; right; right; right; right; exact ⟨rfl, rfl⟩
  · have ha := hm a (by simp)
    have hb := hm b (by simp)
    have he := hm e (by simp)
    have hd := hm d (by simp)
    have ha1 := coneDefect_ge_half ha
    have hb1 := coneDefect_ge_half hb
    have he1 := coneDefect_ge_half he
    have hd1 := coneDefect_ge_half hd
    simp only [orbifoldDefect, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hdef
    have hcz : (c : ℚ) ≤ 0 := by linarith
    have hcnn : (0 : ℚ) ≤ (c : ℚ) := by positivity
    have hc0 : c = 0 := by
      have : (c : ℚ) = 0 := le_antisymm hcz hcnn
      exact_mod_cast this
    subst hc0
    have haval : coneDefect a = 1 / 2 := by norm_num at hdef; linarith
    have hbval : coneDefect b = 1 / 2 := by norm_num at hdef; linarith
    have heval : coneDefect e = 1 / 2 := by norm_num at hdef; linarith
    have hdval : coneDefect d = 1 / 2 := by norm_num at hdef; linarith
    rw [coneDefect_eq_half ha haval, coneDefect_eq_half hb hbval, coneDefect_eq_half he heval,
      coneDefect_eq_half hd hdval]
    right; right; left
    exact ⟨rfl, rfl⟩
  · exfalso
    have ha1 := coneDefect_ge_half (hm a (by simp))
    have hb1 := coneDefect_ge_half (hm b (by simp))
    have he1 := coneDefect_ge_half (hm e (by simp))
    have hd1 := coneDefect_ge_half (hm d (by simp))
    have hf1 := coneDefect_ge_half (hm f (by simp))
    have ht : 0 ≤ (t.map coneDefect).sum :=
      coneDefectSum_nonneg t fun k hk => hm k (by simp [hk])
    have hcnn : (0 : ℚ) ≤ (c : ℚ) := by positivity
    simp only [orbifoldDefect, List.map_cons, List.sum_cons] at hdef
    linarith

/-! ### The enumeration is complete -/

theorem parabolicSphereSignature_coneOrders_two_le (s : ParabolicSphereSignature) :
    ∀ k ∈ s.finiteConeOrders, 2 ≤ k := by
  cases s <;> decide

theorem parabolicSphereSignature_coneOrders_sorted (s : ParabolicSphereSignature) :
    s.finiteConeOrders.Pairwise (· ≤ ·) := by
  cases s <;> decide

theorem parabolicSphereSignature_orbifoldDefect (s : ParabolicSphereSignature) :
    orbifoldDefect s.finiteConeOrders s.cuspCount = 2 := by
  cases s <;>
    norm_num [orbifoldDefect, coneDefect, ParabolicSphereSignature.finiteConeOrders,
      ParabolicSphereSignature.cuspCount]

/-- **The enumeration is exactly the parabolic data.**  A cone-order list with a cusp count comes
from a parabolic sphere signature precisely when its orders are at least two, weakly increasing, and
its total angle defect is two. -/
theorem exists_parabolicSphereSignature_iff {m : List ℕ} {c : ℕ} :
    (∃ s : ParabolicSphereSignature, s.finiteConeOrders = m ∧ s.cuspCount = c) ↔
      ((∀ k ∈ m, 2 ≤ k) ∧ m.Pairwise (· ≤ ·) ∧ orbifoldDefect m c = 2) := by
  constructor
  · rintro ⟨s, rfl, rfl⟩
    exact ⟨parabolicSphereSignature_coneOrders_two_le s,
      parabolicSphereSignature_coneOrders_sorted s, parabolicSphereSignature_orbifoldDefect s⟩
  · rintro ⟨hm, hs, hd⟩
    rcases parabolic_signature_classification hm hs hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨.twoCusps, rfl, rfl⟩
    · exact ⟨.twoTwosCusp, rfl, rfl⟩
    · exact ⟨.fourTwos, rfl, rfl⟩
    · exact ⟨.twoThreeSix, rfl, rfl⟩
    · exact ⟨.twoFourFour, rfl, rfl⟩
    · exact ⟨.threeThrees, rfl, rfl⟩

end GaloisForLFunctions.HTGeometry

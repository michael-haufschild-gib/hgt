/-
# The equilibrium constraint pushes past the gap midpoint on decreasing-gap fields

On the equal-spacing lattice the `k`-th behind and `k`-th ahead poles cancel exactly at a
gap's midpoint, so the field there equals the count of unpaired behind poles and the
equilibrium — the point where the field meets the level `−(total pole count)` — sits
strictly right of the midpoint: its distance to the ahead pole is under half the gap. On a
field with decreasing gaps each behind partner is FARTHER than its ahead partner, so the
pairs no longer cancel; each pair contributes a deficit bounded by the mean-value box
`((B−A)/2)·csch²(A/2)` at the nearer (ahead) distance. The push survives whenever the total
deficit stays under the budget `2M + 2E + 2` — the unpaired coth excess plus the level
itself — uniformly in the configuration: the conclusion `s < δ/2` is exactly the hypothesis
under which the paired energy response `dW/ds < 0` operates.
-/
import GaloisForLFunctions.RHTower.SpurLattice
import GaloisForLFunctions.RHTower.LegAdiabatic

noncomputable section

namespace RHTower

open Finset

/-- **The field level decides the side of the midpoint**: on a pole-free gap the field is
strictly decreasing, so if its midpoint value still exceeds the level `c`, any equilibrium
at level `c` inside the gap lies strictly right of the midpoint. -/
theorem equilibrium_gt_midpoint {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b c x : ℝ}
    (hne : s.Nonempty) (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k) (hab : a < b)
    (hmid : c < cothField s t ((a + b) / 2))
    (hx : x ∈ Set.Ioo a b) (heq : cothField s t x = c) :
    (a + b) / 2 < x := by
  by_contra hle
  have hle' : x ≤ (a + b) / 2 := not_lt.mp hle
  have hmidmem : (a + b) / 2 ∈ Set.Ioo a b :=
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  rcases eq_or_lt_of_le hle' with hEq | hlt
  · rw [hEq] at heq
    linarith
  · have hanti := cothField_strictAntiOn s t hne hpoles hx hmidmem hlt
    rw [heq] at hanti
    linarith

/-- **Paired-deficit lower bound for a two-train sum**: `M` behind/ahead distance pairs with
the ahead partner nearer (`0 < A k ≤ B k`) plus `E` positive unpaired behind distances. The
paired `coth` differences lose at most the mean-value boxes, the unpaired terms each exceed
`1`, so the total sits above `E` minus the deficit sum. -/
theorem paired_train_sum_ge {M E : ℕ} {A B ex : ℕ → ℝ}
    (hpair : ∀ k ∈ range M, 0 < A k ∧ A k ≤ B k)
    (hex : ∀ j ∈ range E, 0 < ex j) :
    (E : ℝ) - (∑ k ∈ range M, ((B k - A k) / 2) * (rcsch (A k / 2)) ^ 2)
      ≤ (∑ k ∈ range M, (rcoth (B k / 2) - rcoth (A k / 2)))
        + ∑ j ∈ range E, rcoth (ex j / 2) := by
  have hdef : ∀ k ∈ range M,
      -(((B k - A k) / 2) * (rcsch (A k / 2)) ^ 2)
        ≤ rcoth (B k / 2) - rcoth (A k / 2) := by
    intro k hk
    obtain ⟨hA, hAB⟩ := hpair k hk
    have := rcoth_pair_le' (show (0 : ℝ) < A k / 2 by positivity)
      (show A k / 2 ≤ B k / 2 by linarith)
    have harg : (B k / 2 - A k / 2) * (rcsch (A k / 2)) ^ 2
        = ((B k - A k) / 2) * (rcsch (A k / 2)) ^ 2 := by ring
    linarith [harg ▸ this]
  have h1 : -(∑ k ∈ range M, ((B k - A k) / 2) * (rcsch (A k / 2)) ^ 2)
      ≤ ∑ k ∈ range M, (rcoth (B k / 2) - rcoth (A k / 2)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum hdef
  have h2 : (E : ℝ) ≤ ∑ j ∈ range E, rcoth (ex j / 2) := by
    calc (E : ℝ) = ∑ _j ∈ range E, (1 : ℝ) := by simp
      _ ≤ ∑ j ∈ range E, rcoth (ex j / 2) :=
          Finset.sum_le_sum (fun j hj =>
            (one_lt_rcoth_of_pos (by have := hex j hj; positivity)).le)
  linarith

/-- The field of the structured configuration, split by index block: `M` paired-behind poles
(`t k`, `k < M`), their `M` ahead partners (`t (M+k)`), `E` unpaired far-behind poles
(`t (2M+j)`), and the two gap-edge poles `t (2M+E) = a`, `t (2M+E+1) = b`. -/
theorem structured_field_eq (M E : ℕ) (t : ℕ → ℝ) (x : ℝ) :
    cothField (range (2 * M + E + 2)) t x
      = (∑ k ∈ range M, rcoth ((x - t k) / 2))
        + (∑ k ∈ range M, rcoth ((x - t (M + k)) / 2))
        + (∑ j ∈ range E, rcoth ((x - t (2 * M + j)) / 2))
        + rcoth ((x - t (2 * M + E)) / 2) + rcoth ((x - t (2 * M + E + 1)) / 2) := by
  simp only [cothField]
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive (fun n => rcoth ((x - t n) / 2))
      (Nat.zero_le M) (by omega : M ≤ 2 * M + E + 2),
    ← Finset.sum_Ico_consecutive (fun n => rcoth ((x - t n) / 2))
      (by omega : M ≤ 2 * M) (by omega : 2 * M ≤ 2 * M + E + 2),
    ← Finset.sum_Ico_consecutive (fun n => rcoth ((x - t n) / 2))
      (by omega : 2 * M ≤ 2 * M + E) (by omega : 2 * M + E ≤ 2 * M + E + 2)]
  have h1 : ∑ n ∈ Finset.Ico 0 M, rcoth ((x - t n) / 2)
      = ∑ k ∈ range M, rcoth ((x - t k) / 2) := by
    rw [← Finset.range_eq_Ico]
  have h2 : ∑ n ∈ Finset.Ico M (2 * M), rcoth ((x - t n) / 2)
      = ∑ k ∈ range M, rcoth ((x - t (M + k)) / 2) := by
    rw [Finset.sum_Ico_eq_sum_range, show 2 * M - M = M by omega]
  have h3 : ∑ n ∈ Finset.Ico (2 * M) (2 * M + E), rcoth ((x - t n) / 2)
      = ∑ j ∈ range E, rcoth ((x - t (2 * M + j)) / 2) := by
    rw [Finset.sum_Ico_eq_sum_range, show 2 * M + E - 2 * M = E by omega]
  have h4 : ∑ n ∈ Finset.Ico (2 * M + E) (2 * M + E + 2), rcoth ((x - t n) / 2)
      = rcoth ((x - t (2 * M + E)) / 2) + rcoth ((x - t (2 * M + E + 1)) / 2) := by
    rw [show 2 * M + E + 2 = (2 * M + E + 1) + 1 from rfl,
      Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega),
      Finset.Ico_self, Finset.sum_empty, zero_add]
  rw [h1, h2, h3, h4]
  ring

/-- **The midpoint push on decreasing-gap configurations**: `M` behind/ahead pole pairs with
every ahead partner at most as far from the gap midpoint as its behind partner (the
decreasing-gap trace), `E` unpaired far-behind poles, and the two gap-edge poles. If the
total paired mean-value deficit stays under the budget `2M + 2E + 2`, then the equilibrium
at level `−(2M + E + 2)` sits strictly right of the midpoint — its distance to the ahead
gap edge is under half the gap width, the hypothesis of the paired energy response. -/
theorem midpoint_push_of_deficit {M E : ℕ} {t : ℕ → ℝ} {a b x : ℝ} (hab : a < b)
    (hpB : ∀ k ∈ range M, t k ≤ a)
    (hpA : ∀ k ∈ range M, b ≤ t (M + k))
    (hpair : ∀ k ∈ range M, t (M + k) - (a + b) / 2 ≤ (a + b) / 2 - t k)
    (hpX : ∀ j ∈ range E, t (2 * M + j) ≤ a)
    (hea : t (2 * M + E) = a) (heb : t (2 * M + E + 1) = b)
    (hbudget : (∑ k ∈ range M,
        ((((a + b) / 2 - t k) - (t (M + k) - (a + b) / 2)) / 2)
          * (rcsch ((t (M + k) - (a + b) / 2) / 2)) ^ 2)
      < 2 * (M : ℝ) + 2 * E + 2)
    (hx : x ∈ Set.Ioo a b)
    (heq : cothField (range (2 * M + E + 2)) t x = -(2 * (M : ℝ) + E + 2)) :
    b - x < (b - a) / 2 := by
  set m : ℝ := (a + b) / 2 with hm
  have hma : a < m := by rw [hm]; linarith
  have hmb : m < b := by rw [hm]; linarith
  -- the field value at the midpoint, block by block
  have hmid : -(2 * (M : ℝ) + E + 2) < cothField (range (2 * M + E + 2)) t m := by
    rw [structured_field_eq]
    -- the two gap-edge terms cancel
    have hedge : rcoth ((m - t (2 * M + E)) / 2) + rcoth ((m - t (2 * M + E + 1)) / 2)
        = 0 := by
      rw [hea, heb, show (m - b) / 2 = -((b - m) / 2) by ring, rcoth_neg,
        show (m - a) / 2 = (b - m) / 2 by rw [hm]; ring]
      ring
    -- the ahead partners flip sign
    have hflip : ∀ k ∈ range M, rcoth ((m - t (M + k)) / 2)
        = -rcoth ((t (M + k) - m) / 2) := by
      intro k _
      rw [show (m - t (M + k)) / 2 = -((t (M + k) - m) / 2) by ring, rcoth_neg]
    have hflipsum : (∑ k ∈ range M, rcoth ((m - t (M + k)) / 2))
        = -∑ k ∈ range M, rcoth ((t (M + k) - m) / 2) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl hflip
    have hkey := paired_train_sum_ge (M := M) (E := E)
      (A := fun k => t (M + k) - m) (B := fun k => m - t k)
      (ex := fun j => m - t (2 * M + j))
      (fun k hk => ⟨by have := hpA k hk; linarith, hpair k hk⟩)
      (fun j hj => by have := hpX j hj; linarith)
    have hsub : (∑ k ∈ range M, (rcoth ((m - t k) / 2) - rcoth ((t (M + k) - m) / 2)))
        = (∑ k ∈ range M, rcoth ((m - t k) / 2))
          - ∑ k ∈ range M, rcoth ((t (M + k) - m) / 2) := by
      rw [Finset.sum_sub_distrib]
    rw [hsub] at hkey
    linarith [hkey, hbudget, hedge, hflipsum]
  -- poles avoid the open gap
  have hpoles : ∀ k ∈ range (2 * M + E + 2), t k ≤ a ∨ b ≤ t k := by
    intro k hk
    rw [Finset.mem_range] at hk
    rcases Nat.lt_or_ge k M with h1 | h1
    · exact Or.inl (hpB k (Finset.mem_range.mpr h1))
    rcases Nat.lt_or_ge k (2 * M) with h2 | h2
    · right
      have : k = M + (k - M) := by omega
      rw [this]
      exact hpA (k - M) (Finset.mem_range.mpr (by omega))
    rcases Nat.lt_or_ge k (2 * M + E) with h3 | h3
    · left
      have : k = 2 * M + (k - 2 * M) := by omega
      rw [this]
      exact hpX (k - 2 * M) (Finset.mem_range.mpr (by omega))
    rcases Nat.lt_or_ge k (2 * M + E + 1) with h4 | h4
    · left
      have : k = 2 * M + E := by omega
      rw [this, hea]
    · right
      have : k = 2 * M + E + 1 := by omega
      rw [this, heb]
  have hne : (range (2 * M + E + 2)).Nonempty :=
    Finset.nonempty_range_iff.mpr (by omega)
  have hpush := equilibrium_gt_midpoint (range (2 * M + E + 2)) t hne hpoles hab hmid hx heq
  rw [← hm] at hpush
  linarith [hpush, hma, hmb]

end RHTower

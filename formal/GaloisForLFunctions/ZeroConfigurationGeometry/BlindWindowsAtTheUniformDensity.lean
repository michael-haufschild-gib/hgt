import GaloisForLFunctions.ZeroConfigurationGeometry.BlindWindowsForPerturbedLattices
import GaloisForLFunctions.HTGeometry.SeparatedPointCount
import Mathlib.Combinatorics.Hall.Basic

/-!
# Blind windows at the uniform density

A real configuration `(λ_i)` has *count bound* `(D, C)` if every finite subfamily inside an
interval `[a, b]` has at most `D(b − a) + C` members. Its upper uniform density is then at most
`D`.

* **Matching to a lattice** (`exists_injective_near_int`). A configuration with count bound
  `(1, C)` admits an injection `σ` into `ℤ` with `|λ_i − σ(i)| ≤ (C + 1)/2`. Hall's condition holds
  by splitting a finite subfamily at gaps wider than `C + 1`: across a gap the integer
  neighbourhoods are disjoint, and a gap-free family sees every integer of its hull widened by
  `(C + 1)/2` (`card_le_card_biUnion_intNbhd`).
* **Blind windows** (`exists_window_blind_of_count_le`). With count bound `(D, C)`, every
  aperture `> πD` has a window blind to all `λ_i` that sees any given `z₀` off them. The matched
  points, completed by a shifted copy of the unused lattice points, form a bounded perturbation of
  `D⁻¹ℤ`, which `exists_window_blind_to_perturbed_lattice` blinds.
* Upper uniform density below `D` (`exists_window_blind_of_density_le`) and separation `δ`
  (`exists_window_blind_of_separated`, aperture `> π/δ`) are the two standard forms of the count
  bound.

No separation, no regularity of the local density and no lattice structure is assumed; points may
repeat. The aperture `πD` is the Jensen threshold of density `D`.
-/

open MeasureTheory Complex Set Filter
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23

/-- The integers within distance `M` of `x`. -/
def intNbhd (M x : ℝ) : Finset ℤ := Finset.Icc ⌈x - M⌉ ⌊x + M⌋

theorem mem_intNbhd {M x : ℝ} {k : ℤ} : k ∈ intNbhd M x ↔ |x - k| ≤ M := by
  rw [intNbhd, Finset.mem_Icc, Int.ceil_le, Int.le_floor, abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Hall's condition for a configuration with count bound `(1, C)`.** -/
theorem card_le_card_biUnion_intNbhd {ι : Type*} (x : ι → ℝ) {C M : ℝ} (hM : C + 1 ≤ 2 * M)
    (hcount : ∀ (s : Finset ι) (a b : ℝ), a ≤ b → (∀ i ∈ s, x i ∈ Icc a b) →
      (s.card : ℝ) ≤ b - a + C)
    (s : Finset ι) : s.card ≤ (s.biUnion fun i => intNbhd M (x i)).card := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  obtain ⟨i₀, hi₀, ha⟩ := s.exists_mem_eq_inf' hs x
  obtain ⟨i₁, hi₁, hb⟩ := s.exists_mem_eq_sup' hs x
  set a := s.inf' hs x
  set b := s.sup' hs x
  have hax : ∀ i ∈ s, a ≤ x i := fun i hi => s.inf'_le x hi
  have hxb : ∀ i ∈ s, x i ≤ b := fun i hi => s.le_sup' x hi
  have hab : a ≤ b := (hax i₀ hi₀).trans (hxb i₀ hi₀)
  have hC1 : 1 ≤ C := by
    have := hcount {i₀} (x i₀) (x i₀) le_rfl (by simp)
    simpa using this
  by_cases hgap : ∃ c : ℝ, a < c ∧ c < b ∧ ∀ i ∈ s, M < |x i - c|
  · -- split at the gap: the two halves have disjoint neighbourhoods
    obtain ⟨c, hac, hcb, hfar⟩ := hgap
    have h₁ : s.filter (fun i => x i < c) ⊂ s :=
      Finset.filter_ssubset.mpr ⟨i₁, hi₁, not_lt.mpr (by rw [← hb]; exact hcb.le)⟩
    have h₂ : s.filter (fun i => ¬ x i < c) ⊂ s :=
      Finset.filter_ssubset.mpr ⟨i₀, hi₀, not_not.mpr (by rw [← ha]; exact hac)⟩
    have hU : s.biUnion (fun i => intNbhd M (x i)) =
        (s.filter fun i => x i < c).biUnion (fun i => intNbhd M (x i)) ∪
          (s.filter fun i => ¬ x i < c).biUnion (fun i => intNbhd M (x i)) := by
      rw [← Finset.union_biUnion, Finset.filter_union_filter_not_eq]
    have hdisj : Disjoint ((s.filter fun i => x i < c).biUnion (fun i => intNbhd M (x i)))
        ((s.filter fun i => ¬ x i < c).biUnion (fun i => intNbhd M (x i))) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      obtain ⟨i, hi, hki⟩ := Finset.mem_biUnion.mp hk1
      obtain ⟨j, hj, hkj⟩ := Finset.mem_biUnion.mp hk2
      rw [Finset.mem_filter] at hi hj
      rw [mem_intNbhd, abs_le] at hki hkj
      have hjc := not_lt.mp hj.2
      have hi' : x i < c - M := by
        rcases lt_abs.mp (hfar i hi.1) with h | h <;> linarith [hi.2]
      have hj' : c + M < x j := by
        rcases lt_abs.mp (hfar j hj.1) with h | h <;> linarith
      linarith [hki.1, hkj.2]
    rw [hU, Finset.card_union_of_disjoint hdisj]
    have e1 := ih _ h₁
    have e2 := ih _ h₂
    have e3 := Finset.card_filter_add_card_filter_not (s := s) (fun i => x i < c)
    omega
  · -- no gap: the neighbourhoods cover every integer of the widened hull
    push Not at hgap
    have hsub : Finset.Icc ⌈a - M⌉ ⌊b + M⌋ ⊆ s.biUnion (fun i => intNbhd M (x i)) := by
      intro k hk
      rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor] at hk
      rw [Finset.mem_biUnion]
      by_cases h1 : (k : ℝ) ≤ a + M
      · exact ⟨i₀, hi₀, mem_intNbhd.mpr (by rw [← ha, abs_le]; constructor <;> linarith)⟩
      by_cases h2 : b - M ≤ (k : ℝ)
      · exact ⟨i₁, hi₁, mem_intNbhd.mpr (by rw [← hb, abs_le]; constructor <;> linarith)⟩
      push Not at h1 h2
      obtain ⟨i, hi, hik⟩ := hgap k (by linarith) (by linarith)
      exact ⟨i, hi, mem_intNbhd.mpr hik⟩
    have hcs : (s.card : ℝ) ≤ b - a + C := hcount s a b hab fun i hi => ⟨hax i hi, hxb i hi⟩
    have hcard := Finset.card_le_card hsub
    rw [Int.card_Icc] at hcard
    have hfl : b + M - 1 < (⌊b + M⌋ : ℝ) := Int.sub_one_lt_floor _
    have hce : (⌈a - M⌉ : ℝ) < a - M + 1 := Int.ceil_lt_add_one _
    have hlt : (s.card : ℝ) < ((⌊b + M⌋ + 1 - ⌈a - M⌉ : ℤ) : ℝ) := by push_cast; linarith
    have key : (s.card : ℤ) < ⌊b + M⌋ + 1 - ⌈a - M⌉ := by exact_mod_cast hlt
    omega

/-- **Matching a configuration of count bound `(1, C)` into `ℤ`.** -/
theorem exists_injective_near_int {ι : Type*} (x : ι → ℝ) {C : ℝ}
    (hcount : ∀ (s : Finset ι) (a b : ℝ), a ≤ b → (∀ i ∈ s, x i ∈ Icc a b) →
      (s.card : ℝ) ≤ b - a + C) :
    ∃ σ : ι → ℤ, Function.Injective σ ∧ ∀ i, |x i - σ i| ≤ (C + 1) / 2 := by
  classical
  obtain ⟨σ, hσ, hσm⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun i => intNbhd ((C + 1) / 2) (x i))).mp
    (card_le_card_biUnion_intNbhd x (by linarith) hcount)
  exact ⟨σ, hσ, fun i => mem_intNbhd.mp (hσm i)⟩

/-- **Blind windows at the uniform density.** A real configuration with count bound `(D, C)` is
blinded, at every aperture `> πD`, by a window that sees any given point off it. -/
theorem exists_window_blind_of_count_le {ι : Type*} (lam : ι → ℝ) {D C r : ℝ} (hD : 0 < D)
    (hcount : ∀ (s : Finset ι) (a b : ℝ), a ≤ b → (∀ i ∈ s, lam i ∈ Icc a b) →
      (s.card : ℝ) ≤ D * (b - a) + C)
    (hr : π * D < r) {z₀ : ℂ} (hz₀ : ∀ i, z₀ ≠ lam i) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ i, paperFT f (lam i) = 0) ∧ paperFT f z₀ ≠ 0 := by
  classical
  have hC : 0 ≤ C := by simpa using hcount ∅ 0 0 le_rfl (by simp)
  set h := D⁻¹ with hh_def
  have hh : 0 < h := inv_pos.mpr hD
  -- the rescaled configuration `Dλ` has count bound `(1, C)`
  have hcount' : ∀ (s : Finset ι) (a b : ℝ), a ≤ b → (∀ i ∈ s, D * lam i ∈ Icc a b) →
      (s.card : ℝ) ≤ b - a + C := by
    intro s a b hab hs
    have := hcount s (a / D) (b / D) (div_le_div_of_nonneg_right hab hD.le) fun i hi => by
      obtain ⟨h1, h2⟩ := hs i hi
      exact ⟨(div_le_iff₀ hD).mpr (by linarith), (le_div_iff₀ hD).mpr (by linarith)⟩
    calc (s.card : ℝ) ≤ D * (b / D - a / D) + C := this
      _ = b - a + C := by field_simp
  obtain ⟨σ, hσ, hσd⟩ := exists_injective_near_int (fun i => D * lam i) hcount'
  -- unused lattice points are shifted off `z₀`
  obtain ⟨c, ⟨hc0, hch⟩, hcE⟩ := SquareRootThreshold.exists_mem_Ioo_notMem_of_countable hh
    (Set.countable_range fun k : ℤ => z₀.re - k * h)
  set ν : ℤ → ℝ := fun k => if hk : ∃ i, σ i = k then lam hk.choose else k * h + c with hν
  have hνin : ∀ k (hk : ∃ i, σ i = k), ν k = lam hk.choose := fun k hk => by
    simp only [hν, dif_pos hk]
  have hνout : ∀ k, (¬ ∃ i, σ i = k) → ν k = k * h + c := fun k hk => by
    simp only [hν, dif_neg hk]
  have hνσ : ∀ i, ν (σ i) = lam i := fun i => by
    have hk : ∃ j, σ j = σ i := ⟨i, rfl⟩
    rw [hνin _ hk, hσ hk.choose_spec]
  have hνb : ∀ k : ℤ, |ν k - k * h| ≤ (C + 1) / 2 * h + h := by
    intro k
    by_cases hk : ∃ i, σ i = k
    · obtain ⟨j, hjl, hj⟩ : ∃ j, lam hk.choose = lam j ∧ σ j = k := ⟨_, rfl, hk.choose_spec⟩
      rw [hνin k hk, hjl, ← hj]
      have e : lam j - (σ j : ℝ) * h = h * (D * lam j - σ j) := by
        rw [hh_def]; field_simp
      rw [e, abs_mul, abs_of_pos hh]
      have := hσd j
      nlinarith
    · rw [hνout k hk, add_sub_cancel_left, abs_of_pos hc0]
      nlinarith
  have hz₀' : ∀ k, z₀ ≠ ν k := by
    intro k hk0
    by_cases hk : ∃ i, σ i = k
    · exact hz₀ hk.choose (by rw [hk0, hνin k hk])
    · apply hcE
      refine ⟨k, ?_⟩
      have := congrArg Complex.re hk0
      rw [Complex.ofReal_re, hνout k hk] at this
      show z₀.re - k * h = c
      linarith
  obtain ⟨f, hf, hfν, hf0⟩ := exists_window_blind_to_perturbed_lattice hh
    (by rw [hh_def, div_inv_eq_mul]; exact hr) ν hνb hz₀'
  exact ⟨f, hf, fun i => by rw [← hνσ i]; exact hfν (σ i), hf0⟩

/-- **Upper uniform density.** If every finite subfamily inside an interval of length `R ≥ R₀`
has at most `DR` members, every aperture `> πD` has a window blind to the configuration that sees
any given point off it. -/
theorem exists_window_blind_of_density_le {ι : Type*} (lam : ι → ℝ) {D R₀ r : ℝ} (hD : 0 < D)
    (hR₀ : 0 ≤ R₀)
    (hdens : ∀ (s : Finset ι) (a R : ℝ), R₀ ≤ R → (∀ i ∈ s, lam i ∈ Icc a (a + R)) →
      (s.card : ℝ) ≤ D * R)
    (hr : π * D < r) {z₀ : ℂ} (hz₀ : ∀ i, z₀ ≠ lam i) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ i, paperFT f (lam i) = 0) ∧ paperFT f z₀ ≠ 0 := by
  refine exists_window_blind_of_count_le lam (C := D * R₀) hD (fun s a b hab hs => ?_) hr hz₀
  rcases le_total R₀ (b - a) with h | h
  · have := hdens s a (b - a) h fun i hi => by rw [add_sub_cancel]; exact hs i hi
    nlinarith
  · have := hdens s a R₀ le_rfl fun i hi => ⟨(hs i hi).1, by linarith [(hs i hi).2]⟩
    nlinarith

/-- **Separated configurations.** If distinct members of the configuration are at distance at
least `δ > 0`, every aperture `> π/δ` has a window blind to it that sees any given point off it. -/
theorem exists_window_blind_of_separated {ι : Type*} (lam : ι → ℝ) {δ r : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ |lam i - lam j|) (hr : π / δ < r) {z₀ : ℂ}
    (hz₀ : ∀ i, z₀ ≠ lam i) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ i, paperFT f (lam i) = 0) ∧ paperFT f z₀ ≠ 0 := by
  classical
  have hinj : Function.Injective lam := fun i j e => by
    by_contra hne
    have := hsep i j hne
    rw [e, sub_self, abs_zero] at this
    linarith
  refine exists_window_blind_of_count_le lam (C := 1) (inv_pos.mpr hδ)
    (fun s a b hab hs => ?_) (by rw [← div_eq_mul_inv]; exact hr) hz₀
  have := card_le_of_separated_of_subset_Icc hδ hab (s.image lam)
    (fun x hx y hy hxy => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
      exact hsep i j fun e => hxy (by rw [e]))
    (fun x hx => by obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx; exact hs i hi)
  rw [Finset.card_image_of_injective _ hinj] at this
  calc (s.card : ℝ) ≤ (b - a) / δ + 1 := this
    _ = δ⁻¹ * (b - a) + 1 := by rw [div_eq_inv_mul]

end GaloisForLFunctions.ZeroConfigurationGeometry

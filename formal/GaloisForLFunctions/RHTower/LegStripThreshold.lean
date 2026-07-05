/-
# The inverted-response strip: exact midpoint reduction and the cotangent threshold

For a field `Σ_k coth((x − t_k)/2)` with equilibrium level `−(pole count)`, an equilibrium in a
gap sits LEFT of the gap midpoint (the "inverted-response strip") exactly when the ahead pole
crowd outweighs the behind one at the midpoint. Two exact facts pin this down.

* **Midpoint reduction** (`cothField_midpoint_split`, `strip_iff_excess`): writing
  `coth(u/2) = 1 + 2/(e^u − 1)` for `u > 0` and its odd reflection for `u < 0`, the field at the
  midpoint splits into a signed pole count plus twice a behind-minus-ahead *excess* balance. The
  equilibrium is left of the midpoint iff the ahead excess exceeds the behind excess by more than
  the behind pole count — a finite, exact criterion with no `coth` left.

* **Cotangent threshold** (`stripResidue`, `stripResidue_eq_one_iff`, `stripResidue_gt_one_iff`):
  on the harmonic pole class the excess balance has continuum residue `Φ(c) = 1 − (π/c)cot(π/c)`
  (the behind and ahead excess sums each diverge logarithmically and cancel; the finite residue
  is this cotangent — the derivation is the accompanying note). The strip is present iff
  `Φ(c) > 1`, and since `cos(π/c)` controls the sign of `(π/c)cot(π/c)` on `(0, π)`, the threshold
  `Φ(c) = 1` is the first zero of the cotangent, `π/c = π/2`, i.e. `c = 2` — uniquely, with the
  strip on the sub-harmonic side `c < 2`.
-/
import GaloisForLFunctions.RHTower.SpurLattice

open Classical

noncomputable section

namespace RHTower

open Finset Real

/-! ### The pole excess and the exact midpoint field decomposition -/

/-- Excess of `coth` over its horizontal asymptote as a function of pole distance:
`poleExcess u = 1/(e^u − 1)`, so `coth(u/2) = 1 + 2·poleExcess u` for `u > 0`. -/
def poleExcess (u : ℝ) : ℝ := 1 / (Real.exp u - 1)

/-- For a positive distance, `coth(u/2)` exceeds its asymptote `1` by twice the excess. -/
theorem rcoth_half_pos {u : ℝ} (hu : 0 < u) : rcoth (u / 2) = 1 + 2 * poleExcess u := by
  have h := rcoth_sub_one (show (0 : ℝ) < u / 2 by linarith)
  rw [show 2 * (u / 2) = u by ring] at h
  rw [poleExcess]
  have hval : rcoth (u / 2) = 1 + 2 / (Real.exp u - 1) := by linarith
  rw [hval]; ring

/-- For a negative distance, `coth(u/2)` falls below `−1` by twice the reflected excess. -/
theorem rcoth_half_neg {u : ℝ} (hu : u < 0) : rcoth (u / 2) = -1 - 2 * poleExcess (-u) := by
  have hpos : (0 : ℝ) < -u := by linarith
  have h1 : rcoth (u / 2) = - rcoth ((-u) / 2) := by
    rw [show u / 2 = -((-u) / 2) by ring, rcoth_neg]
  rw [h1, rcoth_half_pos hpos]; ring

/-- **Exact midpoint field decomposition**: at a point `m` avoided by every pole, the field
`Σ_k coth((m − t_k)/2)` equals the signed pole count `#{behind} − #{ahead}` plus twice the
behind-minus-ahead excess balance. Pure finite rearrangement via `rcoth_half_pos/neg`. -/
theorem cothField_midpoint_split {ι : Type*} (s : Finset ι) (t : ι → ℝ) (m : ℝ)
    (hne : ∀ k ∈ s, t k ≠ m) :
    cothField s t m
      = ((s.filter (fun k => t k < m)).card : ℝ) - (s.filter (fun k => m < t k)).card
        + 2 * ((∑ k ∈ s.filter (fun k => t k < m), poleExcess (m - t k))
               - ∑ k ∈ s.filter (fun k => m < t k), poleExcess (t k - m)) := by
  set A := s.filter (fun k => t k < m) with hA
  set B := s.filter (fun k => m < t k) with hB
  have hsplit : A ∪ B = s := by
    rw [hA, hB, ← Finset.filter_or]
    apply Finset.filter_true_of_mem
    intro k hk
    rcases lt_trichotomy (t k) m with h | h | h
    · exact Or.inl h
    · exact absurd h (hne k hk)
    · exact Or.inr h
  have hdisj : Disjoint A B := by
    rw [hA, hB, Finset.disjoint_filter]
    intro k _ hlt
    exact not_lt.mpr (le_of_lt hlt)
  have hb : (∑ k ∈ A, rcoth ((m - t k) / 2)) = ∑ k ∈ A, (1 + 2 * poleExcess (m - t k)) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [hA, Finset.mem_filter] at hk
    exact rcoth_half_pos (by linarith [hk.2])
  have ha : (∑ k ∈ B, rcoth ((m - t k) / 2)) = ∑ k ∈ B, (-1 - 2 * poleExcess (t k - m)) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [hB, Finset.mem_filter] at hk
    rw [rcoth_half_neg (by linarith [hk.2]), show -(m - t k) = t k - m by ring]
  have hbsum : (∑ k ∈ A, (1 + 2 * poleExcess (m - t k)))
      = (A.card : ℝ) + 2 * ∑ k ∈ A, poleExcess (m - t k) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum]
    simp
  have hasum : (∑ k ∈ B, (-1 - 2 * poleExcess (t k - m)))
      = -(B.card : ℝ) - 2 * ∑ k ∈ B, poleExcess (t k - m) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum]
    simp
  have key : cothField s t m
      = (∑ k ∈ A, rcoth ((m - t k) / 2)) + ∑ k ∈ B, rcoth ((m - t k) / 2) := by
    rw [cothField, ← Finset.sum_union hdisj, hsplit]
  rw [key, hb, ha, hbsum, hasum]; ring

/-- **The strip criterion in excess form**: with the gap `(a, b)` pole-free and an equilibrium
`xEq` at the level `−(pole count)` inside it, the equilibrium lies left of the midpoint `m`
exactly when the ahead excess beats the behind excess by more than the behind pole count. The
`coth` field has been eliminated: the criterion is a finite inequality among `1/(e^·−1)` terms. -/
theorem strip_iff_excess {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b m xEq : ℝ}
    (hsne : s.Nonempty) (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k)
    (hne : ∀ k ∈ s, t k ≠ m)
    (hmgap : m ∈ Set.Ioo a b) (hxgap : xEq ∈ Set.Ioo a b)
    (hlevel : cothField s t xEq = -(s.card : ℝ)) :
    xEq < m ↔ ((s.filter (fun k => t k < m)).card : ℝ)
        < (∑ k ∈ s.filter (fun k => m < t k), poleExcess (t k - m))
          - ∑ k ∈ s.filter (fun k => t k < m), poleExcess (m - t k) := by
  have hsplit : s.filter (fun k => t k < m) ∪ s.filter (fun k => m < t k) = s := by
    rw [← Finset.filter_or]
    apply Finset.filter_true_of_mem
    intro k hk
    rcases lt_trichotomy (t k) m with h | h | h
    · exact Or.inl h
    · exact absurd h (hne k hk)
    · exact Or.inr h
  have hdisj : Disjoint (s.filter (fun k => t k < m)) (s.filter (fun k => m < t k)) := by
    rw [Finset.disjoint_filter]; intro k _ hlt; exact not_lt.mpr (le_of_lt hlt)
  have hcard : ((s.filter (fun k => t k < m)).card : ℝ)
      + ((s.filter (fun k => m < t k)).card : ℝ) = (s.card : ℝ) := by
    rw [← Nat.cast_add, ← Finset.card_union_of_disjoint hdisj, hsplit]
  have hmono := cothField_strictAntiOn s t hsne hpoles
  have hlt_iff : xEq < m ↔ cothField s t m < cothField s t xEq := by
    constructor
    · intro h; exact hmono hxgap hmgap h
    · intro h
      by_contra hcon
      rw [not_lt] at hcon
      rcases eq_or_lt_of_le hcon with he | hlt
      · rw [he] at h; exact lt_irrefl _ h
      · exact absurd (hmono hmgap hxgap hlt) (not_lt.mpr (le_of_lt h))
  rw [hlt_iff, hlevel, cothField_midpoint_split s t m hne]
  constructor
  · intro h; nlinarith [hcard]
  · intro h; nlinarith [hcard]

/-! ### The cotangent threshold `Φ(c) = 1 − (π/c)cot(π/c)` -/

/-- The continuum residue of the behind-minus-ahead excess balance on the harmonic pole class:
`Φ(c) = 1 − (π/c)cot(π/c)`. Its value crosses `1` exactly at `c = 2`. -/
def stripResidue (c : ℝ) : ℝ := 1 - (π / c) * Real.cot (π / c)

/-- On `(1, ∞)` the argument `π/c` lies in `(0, π)`, where `π/c > 0` and `sin(π/c) > 0`, so the
sign of `(π/c)cot(π/c)` is the sign of `cos(π/c)`. -/
theorem piC_cot_eq {c : ℝ} (hc : 1 < c) :
    (π / c) * Real.cot (π / c) = (π / c) * Real.cos (π / c) / Real.sin (π / c)
      ∧ 0 < π / c ∧ 0 < Real.sin (π / c) := by
  have hpi := Real.pi_pos
  have hc0 : 0 < c := by linarith
  have h1 : 0 < π / c := by positivity
  have h2 : π / c < π := by rw [div_lt_iff₀ hc0]; nlinarith [hpi]
  refine ⟨?_, h1, Real.sin_pos_of_pos_of_lt_pi h1 h2⟩
  rw [Real.cot_eq_cos_div_sin]; ring

/-- **`Φ(2) = 1`**: at the harmonic value the cotangent vanishes (`cos(π/2) = 0`). -/
theorem stripResidue_two : stripResidue 2 = 1 := by
  rw [stripResidue, Real.cot_eq_cos_div_sin, Real.cos_pi_div_two]
  simp

/-- **The threshold is `c = 2`, uniquely**: for `c > 1`, `Φ(c) = 1` iff `c = 2`. The residue
equals `1` iff `(π/c)cot(π/c) = 0` iff `cos(π/c) = 0`, and on `(0, π)` the cosine vanishes only
at `π/2`, forcing `π/c = π/2`, i.e. `c = 2`. -/
theorem stripResidue_eq_one_iff {c : ℝ} (hc : 1 < c) : stripResidue c = 1 ↔ c = 2 := by
  have hpi := Real.pi_pos
  have hc0 : 0 < c := by linarith
  obtain ⟨hcot, hpos, hsin⟩ := piC_cot_eq hc
  have h2 : π / c < π := by rw [div_lt_iff₀ hc0]; nlinarith [hpi]
  constructor
  · intro h
    have hzero : (π / c) * Real.cot (π / c) = 0 := by rw [stripResidue] at h; linarith
    have hcos : Real.cos (π / c) = 0 := by
      have h0 : (π / c) * Real.cos (π / c) / Real.sin (π / c) = 0 := by rw [← hcot]; exact hzero
      rcases div_eq_zero_iff.mp h0 with hnum | hs
      · rcases mul_eq_zero.mp hnum with h' | h'
        · exact absurd h' (ne_of_gt hpos)
        · exact h'
      · exact absurd hs (ne_of_gt hsin)
    have hmem : π / c ∈ Set.Icc (0 : ℝ) π := ⟨le_of_lt hpos, le_of_lt h2⟩
    have hmemh : (π / 2 : ℝ) ∈ Set.Icc (0 : ℝ) π := ⟨by positivity, by linarith⟩
    have heq : Real.cos (π / c) = Real.cos (π / 2) := by rw [hcos, Real.cos_pi_div_two]
    have hpc : π / c = π / 2 := Real.strictAntiOn_cos.injOn hmem hmemh heq
    have hmul : π * 2 = π * c :=
      (div_eq_div_iff (ne_of_gt hc0) (by norm_num : (2 : ℝ) ≠ 0)).mp hpc
    exact (mul_left_cancel₀ (ne_of_gt hpi) hmul).symm
  · intro h; rw [h]; exact stripResidue_two

/-- **The strip is the sub-harmonic side**: for `c > 1`, `Φ(c) > 1` iff `c < 2`. Above `1` the
residue means `(π/c)cot(π/c) < 0`, i.e. `cos(π/c) < 0`, i.e. `π/c > π/2` (cosine negative on
`(π/2, π)`), i.e. `c < 2`. -/
theorem stripResidue_gt_one_iff {c : ℝ} (hc : 1 < c) : 1 < stripResidue c ↔ c < 2 := by
  have hpi := Real.pi_pos
  have hc0 : 0 < c := by linarith
  obtain ⟨hcot, hpos, hsin⟩ := piC_cot_eq hc
  have h2 : π / c < π := by rw [div_lt_iff₀ hc0]; nlinarith [hpi]
  have hcos_iff : Real.cos (π / c) < 0 ↔ c < 2 := by
    constructor
    · intro h
      by_contra hcon
      rw [not_lt] at hcon
      have hle : π / c ≤ π / 2 := by rw [div_le_div_iff₀ hc0 (by norm_num)]; nlinarith [hpi]
      have hmem : π / c ∈ Set.Icc (0 : ℝ) π := ⟨le_of_lt hpos, le_of_lt h2⟩
      have hcos_nonneg : 0 ≤ Real.cos (π / c) := by
        rcases eq_or_lt_of_le hle with he | hlt
        · rw [he, Real.cos_pi_div_two]
        · have hmemh : (π / 2 : ℝ) ∈ Set.Icc (0 : ℝ) π := ⟨by positivity, by linarith⟩
          have := Real.strictAntiOn_cos hmem hmemh hlt
          rw [Real.cos_pi_div_two] at this; linarith
      linarith
    · intro h
      have hlt : (π / 2 : ℝ) < π / c := by rw [div_lt_div_iff₀ (by norm_num) hc0]; nlinarith [hpi]
      have hmemh : (π / 2 : ℝ) ∈ Set.Icc (0 : ℝ) π := ⟨by positivity, by linarith⟩
      have hmem : π / c ∈ Set.Icc (0 : ℝ) π := ⟨le_of_lt hpos, le_of_lt h2⟩
      have := Real.strictAntiOn_cos hmemh hmem hlt
      rw [Real.cos_pi_div_two] at this; linarith
  rw [← hcos_iff, stripResidue, hcot]
  constructor
  · intro h
    have hquot : (π / c) * Real.cos (π / c) / Real.sin (π / c) < 0 := by linarith
    by_contra hcon
    rw [not_lt] at hcon
    have : 0 ≤ (π / c) * Real.cos (π / c) := mul_nonneg (le_of_lt hpos) hcon
    have : 0 ≤ (π / c) * Real.cos (π / c) / Real.sin (π / c) := div_nonneg this (le_of_lt hsin)
    linarith
  · intro h
    have hnum : (π / c) * Real.cos (π / c) < 0 := mul_neg_of_pos_of_neg hpos h
    have : (π / c) * Real.cos (π / c) / Real.sin (π / c) < 0 := div_neg_of_neg_of_pos hnum hsin
    linarith

/-! ### The residue as an explicit convergent series (the continuum-limit closed form) -/

section Series
open Complex

/-- **The residue is the excess series** `Φ(c) = Σ_{n≥1} 2/((cn)² − 1)`, for `c > 1`. This is the
closed-form half of the continuum limit: evaluating the Mittag-Leffler cotangent expansion
(`cot_series_rep`) at `x = 1/c` turns the paired excess balance into this explicit sum. It makes
the threshold transparent — at `c = 2` the terms `2/(4n²−1) = 1/(2n−1) − 1/(2n+1)` telescope to
`1`, and `Φ` is manifestly decreasing in `c`. -/
theorem stripResidue_eq_tsum {c : ℝ} (hc : 1 < c) :
    stripResidue c = ∑' n : ℕ+, 2 / ((c * (n : ℝ)) ^ 2 - 1) := by
  have hcpos : 0 < c := by linarith
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hmem : ((1 / c : ℝ) : ℂ) ∈ integerComplement := by
    rw [mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have hnr : (n : ℝ) = 1 / c := by
      have h : (((n : ℤ) : ℝ) : ℂ) = ((1 / c : ℝ) : ℂ) := by rw [← hn]; push_cast; ring
      have := Complex.ofReal_injective h; simpa using this
    have h0 : (0 : ℝ) < 1 / c := by positivity
    have h1 : 1 / c < 1 := by rw [div_lt_one hcpos]; exact hc
    have hn0 : (0 : ℤ) < n := by
      have : (0 : ℝ) < (n : ℝ) := by rw [hnr]; exact h0
      exact_mod_cast this
    have hn1 : n < 1 := by
      have : (n : ℝ) < 1 := by rw [hnr]; exact h1
      exact_mod_cast this
    omega
  have hseries := cot_series_rep hmem
  have hterm : ∀ n : ℕ+,
      (1 / (((1 / c : ℝ) : ℂ) - ((n : ℕ) : ℂ)) + 1 / (((1 / c : ℝ) : ℂ) + ((n : ℕ) : ℂ)))
        = (((-2 * c / ((c * (n : ℝ)) ^ 2 - 1) : ℝ)) : ℂ) := by
    intro n
    have hm1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.pos
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have h1c : 1 / c < 1 := by rw [div_lt_one hcpos]; exact hc
    have h0c : (0 : ℝ) < 1 / c := by positivity
    have hcn : 1 < c * (n : ℝ) := by
      nlinarith [hm1, hc, hcpos,
        mul_nonneg (le_of_lt hcpos) (show (0 : ℝ) ≤ (n : ℝ) - 1 by linarith)]
    have hden : (0 : ℝ) < (c * (n : ℝ)) ^ 2 - 1 := by nlinarith [hcn]
    have hr1 : (1 / c - (n : ℝ)) ≠ 0 := by intro h; nlinarith [hm1, h1c, h]
    have hr2 : (1 / c + (n : ℝ)) ≠ 0 := by intro h; nlinarith [hnpos, h0c, h]
    have hRealId : 1 / (1 / c - (n : ℝ)) + 1 / (1 / c + (n : ℝ))
        = -2 * c / ((c * (n : ℝ)) ^ 2 - 1) := by
      rw [div_add_div _ _ hr1 hr2, div_eq_div_iff (mul_ne_zero hr1 hr2) (ne_of_gt hden)]
      field_simp
      ring
    rw [← hRealId]; push_cast; ring
  have hsumeq : (∑' n : ℕ+,
        (1 / (((1 / c : ℝ) : ℂ) - ((n : ℕ) : ℂ)) + 1 / (((1 / c : ℝ) : ℂ) + ((n : ℕ) : ℂ))))
      = ∑' n : ℕ+, (((-2 * c / ((c * (n : ℝ)) ^ 2 - 1) : ℝ)) : ℂ) := tsum_congr hterm
  rw [hsumeq, ← Complex.ofReal_tsum] at hseries
  have hL : (↑π * (↑π * ((1 / c : ℝ) : ℂ)).cot) = ((π * Real.cot (π / c) : ℝ) : ℂ) := by
    rw [show (↑π * ((1 / c : ℝ) : ℂ)) = ((π / c : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cot]
    push_cast; ring
  have hInv : (1 : ℂ) / ((1 / c : ℝ) : ℂ) = ((c : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, one_div_one_div]
  rw [hL, hInv, ← Complex.ofReal_add] at hseries
  have hreal : π * Real.cot (π / c) = c + ∑' n : ℕ+, (-2 * c / ((c * (n : ℝ)) ^ 2 - 1)) :=
    Complex.ofReal_injective hseries
  rw [stripResidue]
  have hdiv : (∑' n : ℕ+, (-2 * c / ((c * (n : ℝ)) ^ 2 - 1))) / c
      = -∑' n : ℕ+, 2 / ((c * (n : ℝ)) ^ 2 - 1) := by
    rw [div_eq_mul_inv, ← tsum_mul_right, ← tsum_neg]
    exact tsum_congr (fun n => by field_simp)
  have hkey : (π / c) * Real.cot (π / c) = 1 - ∑' n : ℕ+, 2 / ((c * (n : ℝ)) ^ 2 - 1) := by
    rw [show (π / c) * Real.cot (π / c) = (π * Real.cot (π / c)) / c by ring, hreal, add_div,
      div_self hcne, hdiv]; ring
  rw [hkey]; ring

/-- The excess series `Σ 2/((cn)² − 1)` converges for `c > 1`: term by term it is dominated by
`(2/(c²−1))·(1/n²)`, using `(cn)² − 1 ≥ (c²−1)n²`. -/
theorem stripResidue_series_summable {c : ℝ} (hc : 1 < c) :
    Summable (fun n : ℕ+ => 2 / ((c * (n : ℝ)) ^ 2 - 1)) := by
  have hc2 : (0 : ℝ) < c ^ 2 - 1 := by nlinarith [hc]
  have hbase : Summable (fun n : ℕ+ => 1 / ((n : ℝ)) ^ 2) :=
    ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)).comp_injective PNat.coe_injective
  have hmaj : Summable (fun n : ℕ+ => (2 / (c ^ 2 - 1)) * (1 / (n : ℝ) ^ 2)) := hbase.mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · have hm1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.pos
    have hden : (0 : ℝ) < (c * (n : ℝ)) ^ 2 - 1 := by
      nlinarith [hm1, hc, mul_nonneg (show (0:ℝ) ≤ c by linarith) (show (0:ℝ) ≤ (n:ℝ) - 1 by linarith)]
    positivity
  · have hm1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.pos
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlow : (c ^ 2 - 1) * (n : ℝ) ^ 2 ≤ (c * (n : ℝ)) ^ 2 - 1 := by nlinarith [hm1]
    have hElow : (0 : ℝ) < (c ^ 2 - 1) * (n : ℝ) ^ 2 := by positivity
    calc 2 / ((c * (n : ℝ)) ^ 2 - 1)
        ≤ 2 / ((c ^ 2 - 1) * (n : ℝ) ^ 2) := by gcongr
      _ = (2 / (c ^ 2 - 1)) * (1 / (n : ℝ) ^ 2) := by field_simp

end Series

/-! ### The continuum residue as an improper integral

The excess series has an integral avatar. Expanding `1/(e^u − 1) = Σ_{n≥1} e^{−nu}` and using
the Laplace transform of `sinh`, the residue equals
`Φ(c) = ∫_0^∞ (2/c) · sinh(u/c) · 1/(e^u − 1) du`. This is the shape in which the continuum limit
of the discrete excess balance `(A − B)/i` is naturally read: the integrand is exactly the
`u → 0` scaling profile of a `coth`-excess pair separated by log-distance `u`. -/

section EulerMaclaurin
open MeasureTheory

/-- The elementary Laplace integral `∫_0^∞ e^{−a u} du = a⁻¹` for `a > 0`, obtained from the unit
exponential integral by the scaling `u ↦ a u`. -/
theorem integral_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    ∫ u in Set.Ioi (0:ℝ), Real.exp (-(a * u)) = a⁻¹ := by
  have h := integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) 0 ha
  simp only [mul_zero, smul_eq_mul] at h
  rw [integral_exp_neg_Ioi] at h
  simp only [neg_zero, Real.exp_zero, mul_one] at h
  simpa using h

/-- **Geometric expansion of the pole excess.** For `u > 0`, `poleExcess u = 1/(e^u − 1)` is the
sum of the geometric shells `Σ_{n≥1} e^{−n u}`. This is the series that turns the excess balance
into a sum of Laplace-integrable pieces. -/
theorem poleExcess_hasSum {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ+ => Real.exp (-(n : ℝ) * u)) (poleExcess u) := by
  set x := Real.exp (-u) with hx
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x < 1 := by rw [hx]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : HasSum (fun n : ℕ => x ^ n) (1 - x)⁻¹ := hasSum_geometric_of_lt_one hx0 hx1
  have hshift : HasSum (fun n : ℕ => x ^ (n + 1)) ((1 - x)⁻¹ - 1) :=
    (hasSum_nat_add_iff (f := fun n : ℕ => x ^ n) 1).mpr (by simpa using hgeo)
  have hfun : (fun m : ℕ+ => x ^ (m : ℕ)) ∘ (Equiv.pnatEquivNat.symm : ℕ → ℕ+)
      = fun n : ℕ => x ^ (n + 1) := by
    funext n
    simp only [Function.comp_apply]
    congr 1
  have hre : HasSum (fun m : ℕ+ => x ^ (m : ℕ)) ((1 - x)⁻¹ - 1) := by
    refine (Equiv.hasSum_iff Equiv.pnatEquivNat.symm).mp ?_
    rw [hfun]; exact hshift
  have hE : (1 : ℝ) < Real.exp u := Real.one_lt_exp_iff.mpr hu
  have hval : (1 - x)⁻¹ - 1 = poleExcess u := by
    have hx' : x = (Real.exp u)⁻¹ := by rw [hx, Real.exp_neg]
    rw [poleExcess, hx']
    have h1 : Real.exp u - 1 ≠ 0 := by linarith
    have hEpos : 0 < Real.exp u := Real.exp_pos _
    have h2 : (1 : ℝ) - (Real.exp u)⁻¹ ≠ 0 := by
      have : (Real.exp u)⁻¹ < 1 := by rw [inv_lt_one₀ hEpos]; exact hE
      linarith
    field_simp
    ring
  have hpow : ∀ m : ℕ+, Real.exp (-(m : ℝ) * u) = x ^ (m : ℕ) := by
    intro m
    rw [hx, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [← hval, show (fun n : ℕ+ => Real.exp (-(n : ℝ) * u)) = (fun m : ℕ+ => x ^ (m : ℕ))
    from funext hpow]
  exact hre

/-- Positivity of the near exponent `n − 1/c > 0` for `n ≥ 1`, `c > 1`. -/
theorem shell_ha1 {c : ℝ} (hc : 1 < c) (n : ℕ+) : 0 < (n : ℝ) - 1 / c := by
  have hm1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.pos
  have hc0 : 0 < c := by linarith
  have : 1 / c < 1 := by rw [div_lt_one hc0]; exact hc
  linarith

/-- Positivity of the far exponent `n + 1/c > 0`. -/
theorem shell_ha2 {c : ℝ} (hc : 1 < c) (n : ℕ+) : 0 < (n : ℝ) + 1 / c := by
  have hm1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.pos
  have hc0 : 0 < c := by linarith
  have : 0 < 1 / c := by positivity
  linarith

/-- The `n`-th shell `(2/c)·sinh(u/c)·e^{−n u}` as a difference of two decaying exponentials with
rates `n − 1/c` and `n + 1/c`. -/
theorem shell_eq {c : ℝ} (n : ℕ+) (u : ℝ) :
    (2 / c) * Real.sinh (u / c) * Real.exp (-(n : ℝ) * u)
      = (1 / c) * (Real.exp (-(((n : ℝ) - 1 / c) * u)) - Real.exp (-(((n : ℝ) + 1 / c) * u))) := by
  rw [Real.sinh_eq]
  rw [show -(((n : ℝ) - 1 / c) * u) = u / c + (-(n : ℝ) * u) by ring,
      show -(((n : ℝ) + 1 / c) * u) = (-(u / c)) + (-(n : ℝ) * u) by ring,
      Real.exp_add, Real.exp_add]
  ring

/-- Each shell is integrable on `(0, ∞)`, being a difference of decaying exponentials. -/
theorem shell_integrableOn {c : ℝ} (hc : 1 < c) (n : ℕ+) :
    IntegrableOn (fun u => (2 / c) * Real.sinh (u / c) * Real.exp (-(n : ℝ) * u)) (Set.Ioi 0) := by
  have h1 : IntegrableOn (fun u => Real.exp (-(((n : ℝ) - 1 / c) * u))) (Set.Ioi 0) := by
    have := exp_neg_integrableOn_Ioi (0 : ℝ) (shell_ha1 hc n)
    exact this.congr_fun (fun u _ => congrArg Real.exp (by ring)) measurableSet_Ioi
  have h2 : IntegrableOn (fun u => Real.exp (-(((n : ℝ) + 1 / c) * u))) (Set.Ioi 0) := by
    have := exp_neg_integrableOn_Ioi (0 : ℝ) (shell_ha2 hc n)
    exact this.congr_fun (fun u _ => congrArg Real.exp (by ring)) measurableSet_Ioi
  have hd : IntegrableOn
      (fun u => (1 / c) * (Real.exp (-(((n : ℝ) - 1 / c) * u)) - Real.exp (-(((n : ℝ) + 1 / c) * u))))
      (Set.Ioi 0) := (h1.sub h2).const_mul (1 / c)
  exact hd.congr_fun (fun u _ => (shell_eq n u).symm) measurableSet_Ioi

/-- Each shell is nonnegative on `(0, ∞)` (positive `sinh` times positive exponentials). -/
theorem shell_nonneg {c : ℝ} (hc : 1 < c) (n : ℕ+) : ∀ u ∈ Set.Ioi (0 : ℝ),
    0 ≤ (2 / c) * Real.sinh (u / c) * Real.exp (-(n : ℝ) * u) := by
  intro u hu
  have hu0 : (0 : ℝ) < u := hu
  have hc0 : 0 < c := by linarith
  have huc : 0 < u / c := by positivity
  have hsinh : 0 < Real.sinh (u / c) := Real.sinh_pos_iff.mpr huc
  have hexp : 0 < Real.exp (-(n : ℝ) * u) := Real.exp_pos _
  have h2c : 0 < 2 / c := by positivity
  exact (mul_pos (mul_pos h2c hsinh) hexp).le

/-- **The shell Laplace transform.** The `n`-th shell integrates to `2/((cn)² − 1)`:
`∫_0^∞ (2/c)·sinh(u/c)·e^{−n u} du = (1/c)·[(n−1/c)⁻¹ − (n+1/c)⁻¹] = 2/((cn)² − 1)`. -/
theorem shell_integral {c : ℝ} (hc : 1 < c) (n : ℕ+) :
    (∫ u in Set.Ioi (0 : ℝ), (2 / c) * Real.sinh (u / c) * Real.exp (-(n : ℝ) * u))
      = 2 / ((c * (n : ℝ)) ^ 2 - 1) := by
  have hc0 : 0 < c := by linarith
  have ha1 := shell_ha1 hc n
  have ha2 := shell_ha2 hc n
  have h1 : IntegrableOn (fun u => Real.exp (-(((n : ℝ) - 1 / c) * u))) (Set.Ioi 0) := by
    have := exp_neg_integrableOn_Ioi (0 : ℝ) ha1
    exact this.congr_fun (fun u _ => congrArg Real.exp (by ring)) measurableSet_Ioi
  have h2 : IntegrableOn (fun u => Real.exp (-(((n : ℝ) + 1 / c) * u))) (Set.Ioi 0) := by
    have := exp_neg_integrableOn_Ioi (0 : ℝ) ha2
    exact this.congr_fun (fun u _ => congrArg Real.exp (by ring)) measurableSet_Ioi
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => shell_eq n u)]
  rw [integral_const_mul, integral_sub h1 h2, integral_exp_neg_mul_Ioi ha1,
    integral_exp_neg_mul_Ioi ha2]
  have hm1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.pos
  have hcn : (1 : ℝ) < c * (n : ℝ) := by
    nlinarith [hm1, hc, mul_nonneg (show (0:ℝ) ≤ c by linarith) (show (0:ℝ) ≤ (n:ℝ) - 1 by linarith)]
  have hne1 : ((n : ℝ) - 1 / c) ≠ 0 := ne_of_gt ha1
  have hne2 : ((n : ℝ) + 1 / c) ≠ 0 := ne_of_gt ha2
  have hd1 : c * (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hd2 : c * (n : ℝ) + 1 ≠ 0 := ne_of_gt (by linarith)
  rw [show (c * (n : ℝ)) ^ 2 - 1 = (c * (n : ℝ) - 1) * (c * (n : ℝ) + 1) by ring]
  field_simp
  ring

/-- **The Euler–Maclaurin integral is the excess series.** For `c > 1`,
`∫_0^∞ (2/c)·sinh(u/c)·1/(e^u − 1) du = Σ_{n≥1} 2/((cn)² − 1)`. The geometric expansion of the
excess splits the integrand into the shells `poleExcess_hasSum`; the sum and the integral are
exchanged by the `L¹` interchange (`integral_tsum`), whose hypothesis is finiteness of
`Σ_n ∫ |shell_n|`, itself finite because each `∫ shell_n = 2/((cn)² − 1)` and that series
converges; each shell is then evaluated by `shell_integral`. -/
theorem poleExcess_integral_eq_tsum {c : ℝ} (hc : 1 < c) :
    (∫ u in Set.Ioi (0 : ℝ), (2 / c) * Real.sinh (u / c) * poleExcess u)
      = ∑' n : ℕ+, 2 / ((c * (n : ℝ)) ^ 2 - 1) := by
  have hc0 : 0 < c := by linarith
  have hmeas : ∀ n : ℕ+, AEStronglyMeasurable
      (fun u => (2 / c) * Real.sinh (u / c) * Real.exp (-(n : ℝ) * u))
      (volume.restrict (Set.Ioi 0)) := by
    intro n
    apply Continuous.aestronglyMeasurable
    fun_prop
  have hpt : ∀ u ∈ Set.Ioi (0 : ℝ),
      (2 / c) * Real.sinh (u / c) * poleExcess u
        = ∑' n : ℕ+, (2 / c) * Real.sinh (u / c) * Real.exp (-(n : ℝ) * u) := by
    intro u hu
    have hu0 : 0 < u := hu
    have hsum : poleExcess u = ∑' n : ℕ+, Real.exp (-(n : ℝ) * u) :=
      (poleExcess_hasSum hu0).tsum_eq.symm
    rw [hsum, ← tsum_mul_left]
  have hL1 : ∑' n : ℕ+, ∫⁻ u, ‖(2 / c) * Real.sinh (u / c) * Real.exp (-(n : ℝ) * u)‖ₑ
      ∂(volume.restrict (Set.Ioi 0)) ≠ ⊤ := by
    have hterm : ∀ n : ℕ+,
        (∫⁻ u, ‖(2 / c) * Real.sinh (u / c) * Real.exp (-(n : ℝ) * u)‖ₑ
          ∂(volume.restrict (Set.Ioi 0)))
          = ENNReal.ofReal (2 / ((c * (n : ℝ)) ^ 2 - 1)) := by
      intro n
      have hnn_ae : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
          (fun u => (2 / c) * Real.sinh (u / c) * Real.exp (-(n : ℝ) * u)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu using shell_nonneg hc n u hu
      calc ∫⁻ u, ‖(2 / c) * Real.sinh (u / c) * Real.exp (-(n : ℝ) * u)‖ₑ
              ∂(volume.restrict (Set.Ioi 0))
          = ∫⁻ u, ENNReal.ofReal ((2 / c) * Real.sinh (u / c) * Real.exp (-(n : ℝ) * u))
              ∂(volume.restrict (Set.Ioi 0)) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
            rw [enorm_eq_ofReal (shell_nonneg hc n u hu)]
        _ = ENNReal.ofReal (∫ u, (2 / c) * Real.sinh (u / c) * Real.exp (-(n : ℝ) * u)
              ∂(volume.restrict (Set.Ioi 0))) :=
            (ofReal_integral_eq_lintegral_ofReal (shell_integrableOn hc n) hnn_ae).symm
        _ = ENNReal.ofReal (2 / ((c * (n : ℝ)) ^ 2 - 1)) := by rw [shell_integral hc n]
    rw [tsum_congr hterm]
    have hnn : ∀ n : ℕ+, 0 ≤ 2 / ((c * (n : ℝ)) ^ 2 - 1) := by
      intro n
      have hm1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.pos
      have hden : 0 < (c * (n : ℝ)) ^ 2 - 1 := by
        nlinarith [hm1, hc, mul_nonneg (show (0:ℝ) ≤ c by linarith) (show (0:ℝ) ≤ (n:ℝ) - 1 by linarith)]
      positivity
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn (stripResidue_series_summable hc)]
    exact ENNReal.ofReal_ne_top
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_tsum hmeas hL1]
  exact tsum_congr (fun n => shell_integral hc n)

/-- **The strip residue as an improper integral.** For `c > 1`,
`Φ(c) = 1 − (π/c)cot(π/c) = ∫_0^∞ (2/c)·sinh(u/c)·1/(e^u − 1) du`. Chaining the series form
(`stripResidue_eq_tsum`) with the integral evaluation (`poleExcess_integral_eq_tsum`) closes the
loop between the closed-form residue and the continuum integral of the excess balance. -/
theorem stripResidue_eq_integral {c : ℝ} (hc : 1 < c) :
    stripResidue c
      = ∫ u in Set.Ioi (0 : ℝ), (2 / c) * Real.sinh (u / c) * poleExcess u :=
  (stripResidue_eq_tsum hc).trans (poleExcess_integral_eq_tsum hc).symm

end EulerMaclaurin

/-! ### The Riemann-sum step of the continuum limit -/

section RiemannSum
open MeasureTheory intervalIntegral Filter Topology

/-- **Antitone Riemann sums converge to the integral** on `[0,1]`: for `f` antitone on `[0,1]`,
the left-endpoint average `(1/i)·Σ_{k<i} f(k/i)` tends to `∫_0^1 f`. This is the Riemann-sum step
of the continuum passage `(A−B)/i → Φ(c)`, isolated as a reusable fact (mathlib has the
sum↔integral sandwich but not this limit). Proof: the sum-integral comparison gives
`∫_0^1 f ≤ (1/i)Σ_{k<i}f(k/i)` and `(1/i)Σ_{k<i}f((k+1)/i) ≤ ∫_0^1 f`, and the two averages
differ by the telescoping `(f 0 − f 1)/i → 0`, so a squeeze delivers the limit. -/
theorem tendsto_riemann_sum_antitone {f : ℝ → ℝ} (hf : AntitoneOn f (Set.Icc 0 1)) :
    Tendsto (fun i : ℕ => (1 / (i : ℝ)) * ∑ k ∈ Finset.range i, f ((k : ℝ) / i)) atTop
      (𝓝 (∫ x in (0:ℝ)..1, f x)) := by
  set I : ℝ := ∫ x in (0:ℝ)..1, f x with hI
  have hstep : ∀ i : ℕ, 1 ≤ i →
      (AntitoneOn (fun x => f (x / (i : ℝ))) (Set.Icc 0 (0 + (i : ℝ))))
        ∧ (∫ x in (0:ℝ)..(0 + (i : ℝ)), f (x / (i : ℝ))) = (i : ℝ) • I := by
    intro i hi1
    have hi : (0 : ℝ) < i := by exact_mod_cast hi1
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      rw [zero_add] at ha hb
      exact hf ⟨div_nonneg ha.1 hi.le, by rw [div_le_one hi]; exact ha.2⟩
        ⟨div_nonneg hb.1 hi.le, by rw [div_le_one hi]; exact hb.2⟩ (by gcongr)
    · rw [show (0:ℝ) + (i : ℝ) = (i : ℝ) by ring, integral_comp_div f (ne_of_gt hi),
        zero_div, div_self (ne_of_gt hi)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => I)
    (h := fun i : ℕ => I + (f 0 - f 1) / (i : ℝ)) tendsto_const_nhds ?_ ?_ ?_
  · have h0 : Tendsto (fun i : ℕ => (f 0 - f 1) / (i : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa using tendsto_const_nhds.add h0
  · filter_upwards [eventually_ge_atTop 1] with i hi1
    have hi : (0 : ℝ) < i := by exact_mod_cast hi1
    obtain ⟨hganti, hsub⟩ := hstep i hi1
    have hlow := hganti.integral_le_sum
    rw [hsub, smul_eq_mul] at hlow
    have hsum : (∑ k ∈ Finset.range i, f ((0 + (k:ℝ)) / i)) = ∑ k ∈ Finset.range i, f ((k:ℝ) / i) :=
      Finset.sum_congr rfl (fun k _ => by rw [zero_add])
    rw [hsum] at hlow
    show I ≤ (1 / (i:ℝ)) * ∑ k ∈ Finset.range i, f ((k:ℝ) / i)
    rw [one_div_mul_eq_div, le_div_iff₀ hi]; nlinarith [hlow]
  · filter_upwards [eventually_ge_atTop 1] with i hi1
    have hi : (0 : ℝ) < i := by exact_mod_cast hi1
    obtain ⟨hganti, hsub⟩ := hstep i hi1
    have hupp := hganti.sum_le_integral
    rw [hsub, smul_eq_mul] at hupp
    have hupp' : (∑ k ∈ Finset.range i, f (((k:ℕ)+1 : ℕ) / (i:ℝ))) ≤ (i:ℝ) * I :=
      le_trans (le_of_eq (Finset.sum_congr rfl (fun k _ => by rw [zero_add]))) hupp
    have htel : (∑ k ∈ Finset.range i, f ((k:ℝ)/(i:ℝ))) - (f 0 - f 1)
        = ∑ k ∈ Finset.range i, f (((k:ℕ)+1 : ℕ) / (i:ℝ)) := by
      have hkey := Finset.sum_range_sub' (fun k => f ((k:ℝ)/(i:ℝ))) i
      rw [Finset.sum_sub_distrib] at hkey
      have e0 : f (((0:ℕ):ℝ)/(i:ℝ)) = f 0 := by norm_num
      have e1 : f (((i:ℕ):ℝ)/(i:ℝ)) = f 1 := by rw [div_self (ne_of_gt hi)]
      rw [e0, e1] at hkey
      linarith [hkey]
    show (1 / (i:ℝ)) * ∑ k ∈ Finset.range i, f ((k:ℝ)/i) ≤ I + (f 0 - f 1)/(i:ℝ)
    rw [one_div_mul_eq_div, div_le_iff₀ hi]
    have hrw : (∑ k ∈ Finset.range i, f ((k:ℝ)/i))
        = (∑ k ∈ Finset.range i, f (((k:ℕ)+1:ℕ)/(i:ℝ))) + (f 0 - f 1) := by linarith [htel]
    rw [hrw]
    have hcancel : (f 0 - f 1) / (i:ℝ) * (i:ℝ) = f 0 - f 1 := by field_simp
    nlinarith [hupp', hcancel]

/-- **The near part of one shell, formalized.** Expanding `1/(e^u − 1) = Σ_{n≥1} e^{−nu}`, the
excess balance splits into shells whose `n`-th ahead term has continuum profile `(1+x)^{−r}`
(`r = nc`, bounded and antitone — unlike the singular full excess). Its `[0,1]` Riemann sum
converges to `∫_0^1 (1+x)^{−r}` for every `r ≥ 0`. This is `tendsto_riemann_sum_antitone` on the
concrete shell function, the discrete-to-continuum step made explicit on a genuine piece of the
limit. -/
theorem tendsto_riemann_sum_shell {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun i : ℕ => (1 / (i : ℝ)) * ∑ k ∈ Finset.range i, (1 + (k : ℝ) / i) ^ (-r)) atTop
      (𝓝 (∫ x in (0:ℝ)..1, (1 + x) ^ (-r))) := by
  refine tendsto_riemann_sum_antitone (fun a ha b hb hab => ?_)
  exact Real.rpow_le_rpow_of_nonpos (by linarith [ha.1]) (by linarith) (by linarith)

/-- **Improper monotone Riemann sums converge to the half-line integral.** For `f` antitone and
nonnegative on `[0,∞)` and integrable on `(0,∞)`, the mesh-`1/i` sample average
`(1/i)·Σ_{k≥0} f(k/i)` tends to `∫_0^∞ f`. This is the infinite-domain upgrade of
`tendsto_riemann_sum_antitone`: a genuine improper Riemann sum, with the summability of the sample
sequence part of the conclusion. Proof: for each mesh the finite sum↔integral sandwich (rescaled by
`integral_comp_div`) squeezes `∫_0^{N/i} f` between `(1/i)Σ_{k<N} f((k+1)/i)` and
`(1/i)Σ_{k<N} f(k/i)`; letting `N → ∞` (`intervalIntegral_tendsto_integral_Ioi`, the tail bounded by
`∫_0^∞ f`) pins `∫_0^∞ f ≤ (1/i)·∑' ≤ ∫_0^∞ f + f(0)/i`, and `f(0)/i → 0` gives the outer limit. -/
theorem tendsto_riemann_sum_antitone_Ioi {f : ℝ → ℝ}
    (hanti : AntitoneOn f (Set.Ici 0)) (hnn : ∀ x ∈ Set.Ici (0:ℝ), 0 ≤ f x)
    (hint : IntegrableOn f (Set.Ioi 0)) :
    Tendsto (fun i : ℕ => (1 / (i:ℝ)) * ∑' k : ℕ, f ((k:ℝ) / i)) atTop
      (𝓝 (∫ x in Set.Ioi 0, f x)) := by
  set I : ℝ := ∫ x in Set.Ioi 0, f x with hI
  have hf0nn : (0:ℝ) ≤ f 0 := hnn 0 (Set.mem_Ici.mpr le_rfl)
  have hI0 : 0 ≤ I := by
    rw [hI]; exact setIntegral_nonneg measurableSet_Ioi (fun x hx => hnn x (Set.mem_Ici.mpr (le_of_lt hx)))
  have hganti : ∀ (i:ℕ), 0 < (i:ℝ) → ∀ N:ℕ,
      AntitoneOn (fun x => f (x / (i:ℝ))) (Set.Icc 0 (0 + (N:ℝ))) := by
    intro i hi N a ha b hb hab
    rw [zero_add] at ha hb
    exact hanti (div_nonneg ha.1 hi.le) (div_nonneg hb.1 hi.le) (by gcongr)
  have hscale : ∀ (i:ℕ), 0 < (i:ℝ) → ∀ N:ℕ,
      (∫ x in (0:ℝ)..(N:ℝ), f (x / (i:ℝ))) = (i:ℝ) * ∫ x in (0:ℝ)..((N:ℝ)/i), f x := by
    intro i hi N
    rw [integral_comp_div f (ne_of_gt hi), zero_div, smul_eq_mul]
  have hsum_le : ∀ (i:ℕ), 0 < (i:ℝ) → ∀ N:ℕ,
      (∑ k ∈ Finset.range N, f (((k+1 : ℕ):ℝ)/i)) ≤ (i:ℝ) * ∫ x in (0:ℝ)..((N:ℝ)/i), f x := by
    intro i hi N
    have hsil := (hganti i hi N).sum_le_integral
    simp only [zero_add] at hsil
    rwa [hscale i hi N] at hsil
  have hint_le : ∀ (i:ℕ), 0 < (i:ℝ) → ∀ N:ℕ,
      (i:ℝ) * ∫ x in (0:ℝ)..((N:ℝ)/i), f x ≤ ∑ k ∈ Finset.range N, f ((k:ℝ)/i) := by
    intro i hi N
    have hils := (hganti i hi N).integral_le_sum
    simp only [zero_add] at hils
    rwa [hscale i hi N] at hils
  have htail : ∀ (i:ℕ), 0 < (i:ℝ) → ∀ N:ℕ, ∫ x in (0:ℝ)..((N:ℝ)/i), f x ≤ I := by
    intro i hi N
    have hNi : (0:ℝ) ≤ (N:ℝ)/i := by positivity
    rw [intervalIntegral.integral_of_le hNi, hI]
    refine setIntegral_mono_set hint ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hnn x (Set.mem_Ici.mpr (le_of_lt hx))
    · exact Filter.Eventually.of_forall (fun x hx => hx.1)
  have htends : ∀ (i:ℕ), 0 < (i:ℝ) →
      Tendsto (fun N:ℕ => ∫ x in (0:ℝ)..((N:ℝ)/i), f x) atTop (𝓝 I) := by
    intro i hi
    rw [hI]
    exact intervalIntegral_tendsto_integral_Ioi 0 hint
      (tendsto_natCast_atTop_atTop.atTop_div_const hi)
  have hpartial : ∀ (i:ℕ), 0 < (i:ℝ) → ∀ N:ℕ,
      ∑ k ∈ Finset.range N, f ((k:ℝ)/i) ≤ (i:ℝ)*I + f 0 := by
    intro i hi N
    have e1 : (∑ k ∈ Finset.range N, f ((k:ℝ)/i)) + f ((N:ℝ)/i)
        = (∑ k ∈ Finset.range N, f (((k+1 : ℕ):ℝ)/i)) + f 0 := by
      have s1 := Finset.sum_range_succ (fun k => f ((k:ℝ)/i)) N
      have s2 := Finset.sum_range_succ' (fun k => f ((k:ℝ)/i)) N
      rw [s1] at s2
      simpa using s2
    have hshift_le : ∑ k ∈ Finset.range N, f (((k+1 : ℕ):ℝ)/i) ≤ (i:ℝ) * I :=
      le_trans (hsum_le i hi N) (mul_le_mul_of_nonneg_left (htail i hi N) hi.le)
    have hNnn : 0 ≤ f ((N:ℝ)/i) := hnn _ (Set.mem_Ici.mpr (by positivity))
    linarith [e1, hshift_le, hNnn]
  have hsummable : ∀ (i:ℕ), 0 < (i:ℝ) → Summable (fun k:ℕ => f ((k:ℝ)/i)) := by
    intro i hi
    exact summable_of_sum_range_le (c := (i:ℝ)*I + f 0)
      (fun k => hnn _ (Set.mem_Ici.mpr (by positivity))) (hpartial i hi)
  have hlow : ∀ (i:ℕ), 0 < (i:ℝ) → I ≤ (1/(i:ℝ)) * ∑' k : ℕ, f ((k:ℝ)/i) := by
    intro i hi
    have hbound : ∀ N:ℕ, ∫ x in (0:ℝ)..((N:ℝ)/i), f x ≤ (1/(i:ℝ)) * ∑' k : ℕ, f ((k:ℝ)/i) := by
      intro N
      have h2 : ∑ k ∈ Finset.range N, f ((k:ℝ)/i) ≤ ∑' k : ℕ, f ((k:ℝ)/i) :=
        (hsummable i hi).sum_le_tsum (Finset.range N) (fun k _ => hnn _ (Set.mem_Ici.mpr (by positivity)))
      have hle : (i:ℝ) * ∫ x in (0:ℝ)..((N:ℝ)/i), f x ≤ ∑' k : ℕ, f ((k:ℝ)/i) :=
        le_trans (hint_le i hi N) h2
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hi]
      linarith [hle]
    exact le_of_tendsto (htends i hi) (Filter.Eventually.of_forall hbound)
  have hupp : ∀ (i:ℕ), 0 < (i:ℝ) → (1/(i:ℝ)) * ∑' k : ℕ, f ((k:ℝ)/i) ≤ I + f 0 / i := by
    intro i hi
    have htsum_le : ∑' k : ℕ, f ((k:ℝ)/i) ≤ (i:ℝ)*I + f 0 :=
      tsum_le_of_sum_range_le (fun k => hnn _ (Set.mem_Ici.mpr (by positivity))) (hpartial i hi)
    rw [one_div, inv_mul_le_iff₀ hi]
    have hrw : (i:ℝ)*(I + f 0/i) = (i:ℝ)*I + f 0 := by field_simp
    rw [hrw]
    exact htsum_le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => I)
    (h := fun i:ℕ => I + f 0 / (i:ℝ)) tendsto_const_nhds ?_ ?_ ?_
  · have h0 : Tendsto (fun i:ℕ => f 0 / (i:ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa using tendsto_const_nhds.add h0
  · filter_upwards [eventually_ge_atTop 1] with i hi1
    exact hlow i (by exact_mod_cast hi1)
  · filter_upwards [eventually_ge_atTop 1] with i hi1
    exact hupp i (by exact_mod_cast hi1)

end RiemannSum

end RHTower

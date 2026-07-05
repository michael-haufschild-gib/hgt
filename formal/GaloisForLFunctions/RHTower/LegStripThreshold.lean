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
    have hm1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.one_le
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
  · have hm1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.one_le
    have hden : (0 : ℝ) < (c * (n : ℝ)) ^ 2 - 1 := by
      nlinarith [hm1, hc, mul_nonneg (show (0:ℝ) ≤ c by linarith) (show (0:ℝ) ≤ (n:ℝ) - 1 by linarith)]
    positivity
  · have hm1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.one_le
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlow : (c ^ 2 - 1) * (n : ℝ) ^ 2 ≤ (c * (n : ℝ)) ^ 2 - 1 := by nlinarith [hm1]
    have hElow : (0 : ℝ) < (c ^ 2 - 1) * (n : ℝ) ^ 2 := by positivity
    calc 2 / ((c * (n : ℝ)) ^ 2 - 1)
        ≤ 2 / ((c ^ 2 - 1) * (n : ℝ) ^ 2) := by gcongr
      _ = (2 / (c ^ 2 - 1)) * (1 / (n : ℝ) ^ 2) := by field_simp

end Series

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

end RiemannSum

end RHTower

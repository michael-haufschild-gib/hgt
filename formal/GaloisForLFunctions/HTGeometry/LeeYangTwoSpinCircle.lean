import GaloisForLFunctions.Core

/-!
# The two-spin Lee–Yang polynomial: forced confinement, marginal decoupling, fake region

`leeYangTwoSpin b z w = 1 + b z + b w + z w` is the grand partition polynomial of the
two-site ferromagnet in the complex fugacities `z, w`, with real coupling `b`.  The
single algebraic identity

`‖1 + b z‖² − ‖b + z‖² = (1 − b²)(1 − ‖z‖²)`   (`normSq_contraction`)

drives a complete trichotomy in the coupling:

* **forced** (`|b| ≤ 1`, strictly inside `|b| < 1`): a zero cannot have both
  fugacities in the open unit disc (`leeYang_confinement`,
  `leeYang_confinement_strict`); on the diagonal all zeros lie on the unit circle
  (`diagonal_zeros_on_circle`) — the smallest instance of the Lee–Yang circle law;
* **marginal** (`b = ±1`): the polynomial factorizes
  (`leeYangTwoSpin_marginal_pos`, `leeYangTwoSpin_marginal_neg`) — the interaction
  decouples into independent sites, the zero set degenerates to the pinned pair of
  hyperplanes `z = ∓1 ∨ w = ∓1` (`leeYangTwoSpin_marginal_zero_iff`), and on the
  diagonal the two circle zeros collide into a double root
  (`leeYangTwoSpin_marginal_diagonal_sq`).  The confining mechanism does not fail by
  leaking zeros; it fails by *degenerating*;
* **anti-forced** (`|b| > 1`): zeros enter the open polydisc
  (`exists_zero_in_polydisk`, `exists_zero_in_polydisk_of_lt_neg`) — the wrong-sign
  region, rejected exactly by the sign of `1 − b²`.

`twoSpinConfined_iff_abs_le_one` packages the trichotomy: confinement holds precisely
on the closed coupling interval `|b| ≤ 1` (`twoSpinConfined_eq_Icc`), whose interior
is the forced region, whose boundary is the degeneration locus, and whose complement
is the fake region.
-/

open Complex

namespace GaloisForLFunctions

noncomputable section

/-- The two-site Lee–Yang grand partition polynomial with real coupling `b` in the
complex fugacities `z`, `w`. -/
def leeYangTwoSpin (b : ℝ) (z w : ℂ) : ℂ :=
  1 + (b : ℂ) * z + (b : ℂ) * w + z * w

/-- Splitting off the second fugacity: the polynomial is affine in `w` with Möbius
coefficients in `z`. -/
theorem leeYangTwoSpin_split (b : ℝ) (z w : ℂ) :
    leeYangTwoSpin b z w = (1 + (b : ℂ) * z) + w * ((b : ℂ) + z) := by
  unfold leeYangTwoSpin
  ring

/-- The diagonal of the two-spin polynomial is the palindromic quadratic
`z² + 2 b z + 1`. -/
theorem leeYangTwoSpin_diagonal (b : ℝ) (z : ℂ) :
    leeYangTwoSpin b z z = z ^ (2 : ℕ) + 2 * (b : ℂ) * z + 1 := by
  unfold leeYangTwoSpin
  ring

/-- **The Lee–Yang contraction identity.** The defect of the Möbius factor
`w = −(1 + b z)/(b + z)` against the unit circle is governed by the sign of
`1 − b²`. -/
theorem normSq_contraction (b : ℝ) (z : ℂ) :
    normSq (1 + (b : ℂ) * z) - normSq ((b : ℂ) + z)
      = (1 - b ^ (2 : ℕ)) * (1 - normSq z) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- A nonnegative real with square one is one. -/
private theorem eq_one_of_sq_eq_one_of_nonneg {x : ℝ} (h : x ^ (2 : ℕ) = 1) (hx : 0 ≤ x) :
    x = 1 := by
  have h3 : (x - 1) * (x + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h3 with h4 | h4
  · linarith
  · linarith

/-- **Forced confinement (the Lee–Yang circle mechanism).** For `|b| ≤ 1` a zero of
the two-spin polynomial cannot have both fugacities in the open unit disc. -/
theorem leeYang_confinement {b : ℝ} (hb : |b| ≤ 1) {z w : ℂ}
    (h0 : leeYangTwoSpin b z w = 0) (hz : ‖z‖ < 1) : 1 ≤ ‖w‖ := by
  have hb2 : b ^ (2 : ℕ) ≤ 1 := (sq_le_one_iff_abs_le_one b).mpr hb
  have hzsq : normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hkey : normSq ((b : ℂ) + z) ≤ normSq (1 + (b : ℂ) * z) := by
    have hmul : 0 ≤ (1 - b ^ (2 : ℕ)) * (1 - normSq z) :=
      mul_nonneg (by linarith) (by linarith)
    linarith [normSq_contraction b z]
  by_cases hbz : (b : ℂ) + z = 0
  · exfalso
    have hzeq : z = -(b : ℂ) := by linear_combination hbz
    have h1 : (1 : ℂ) + (b : ℂ) * z = 0 := by
      rw [leeYangTwoSpin_split, hbz, mul_zero, add_zero] at h0
      exact h0
    rw [hzeq] at h1
    have hb1 : (1 - b ^ (2 : ℕ) : ℝ) = 0 := by
      have hc : ((1 - b ^ (2 : ℕ) : ℝ) : ℂ) = 0 := by
        push_cast
        linear_combination h1
      exact_mod_cast hc
    have hzb : ‖z‖ = |b| := by
      rw [hzeq, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg b, sq_abs b]
  · have hw : ‖w‖ * ‖(b : ℂ) + z‖ = ‖1 + (b : ℂ) * z‖ := by
      rw [← norm_mul]
      have hwz : w * ((b : ℂ) + z) = -(1 + (b : ℂ) * z) := by
        rw [leeYangTwoSpin_split] at h0
        linear_combination h0
      rw [hwz, norm_neg]
    have hpos : 0 < ‖(b : ℂ) + z‖ := norm_pos_iff.mpr hbz
    have hle : ‖(b : ℂ) + z‖ ≤ ‖1 + (b : ℂ) * z‖ := by
      have hsq : ‖(b : ℂ) + z‖ ^ (2 : ℕ) ≤ ‖1 + (b : ℂ) * z‖ ^ (2 : ℕ) := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
        exact hkey
      calc ‖(b : ℂ) + z‖ = Real.sqrt (‖(b : ℂ) + z‖ ^ (2 : ℕ)) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (‖1 + (b : ℂ) * z‖ ^ (2 : ℕ)) := Real.sqrt_le_sqrt hsq
        _ = ‖1 + (b : ℂ) * z‖ := Real.sqrt_sq (norm_nonneg _)
    by_contra hcon
    rw [not_le] at hcon
    have hlt2 := mul_lt_mul_of_pos_right hcon hpos
    rw [one_mul] at hlt2
    linarith

/-- Strictly inside the forced region the confinement is strict. -/
theorem leeYang_confinement_strict {b : ℝ} (hb : |b| < 1) {z w : ℂ}
    (h0 : leeYangTwoSpin b z w = 0) (hz : ‖z‖ < 1) : 1 < ‖w‖ := by
  have hb2 : b ^ (2 : ℕ) < 1 := by nlinarith [sq_abs b, abs_nonneg b]
  have hzsq : normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hkey : normSq ((b : ℂ) + z) < normSq (1 + (b : ℂ) * z) := by
    have hmul : 0 < (1 - b ^ (2 : ℕ)) * (1 - normSq z) :=
      mul_pos (by linarith) (by linarith)
    linarith [normSq_contraction b z]
  by_cases hbz : (b : ℂ) + z = 0
  · exfalso
    have h1 : (1 : ℂ) + (b : ℂ) * z = 0 := by
      rw [leeYangTwoSpin_split, hbz, mul_zero, add_zero] at h0
      exact h0
    rw [hbz, h1] at hkey
    simp at hkey
  · have hw : ‖w‖ * ‖(b : ℂ) + z‖ = ‖1 + (b : ℂ) * z‖ := by
      rw [← norm_mul]
      have hwz : w * ((b : ℂ) + z) = -(1 + (b : ℂ) * z) := by
        rw [leeYangTwoSpin_split] at h0
        linear_combination h0
      rw [hwz, norm_neg]
    have hpos : 0 < ‖(b : ℂ) + z‖ := norm_pos_iff.mpr hbz
    have hlt : ‖(b : ℂ) + z‖ < ‖1 + (b : ℂ) * z‖ := by
      have hsq : ‖(b : ℂ) + z‖ ^ (2 : ℕ) < ‖1 + (b : ℂ) * z‖ ^ (2 : ℕ) := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
        exact hkey
      calc ‖(b : ℂ) + z‖ = Real.sqrt (‖(b : ℂ) + z‖ ^ (2 : ℕ)) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ < Real.sqrt (‖1 + (b : ℂ) * z‖ ^ (2 : ℕ)) := Real.sqrt_lt_sqrt (sq_nonneg _) hsq
        _ = ‖1 + (b : ℂ) * z‖ := Real.sqrt_sq (norm_nonneg _)
    by_contra hcon
    rw [not_lt] at hcon
    have hle2 := mul_le_mul_of_nonneg_right hcon hpos.le
    rw [one_mul] at hle2
    linarith

/-- **The circle law in its smallest instance.** For `|b| ≤ 1` every zero of the
diagonal polynomial `z² + 2 b z + 1` lies on the unit circle.  The proof pairs each
zero with its conjugate: either the zero is real and pinned at `−b` with `b² = 1`, or
the conjugate is the reciprocal partner and `z z̄ = 1` by Vieta. -/
theorem diagonal_zeros_on_circle {b : ℝ} (hb : |b| ≤ 1) {z : ℂ}
    (h0 : z ^ (2 : ℕ) + 2 * (b : ℂ) * z + 1 = 0) : ‖z‖ = 1 := by
  have hb2 : b ^ (2 : ℕ) ≤ 1 := (sq_le_one_iff_abs_le_one b).mpr hb
  have hw0 : ((starRingEnd ℂ) z) ^ (2 : ℕ) + 2 * (b : ℂ) * ((starRingEnd ℂ) z) + 1 = 0 := by
    have h := congrArg (starRingEnd ℂ) h0
    simpa [map_add, map_mul, map_pow, map_one, map_zero, map_ofNat,
      Complex.conj_ofReal] using h
  have hfactor : (z - (starRingEnd ℂ) z) * (z + (starRingEnd ℂ) z + 2 * (b : ℂ)) = 0 := by
    linear_combination h0 - hw0
  rcases mul_eq_zero.mp hfactor with hcase | hcase
  · -- the zero is real: it is pinned at `−b` and the coupling is marginal
    have hconj : (starRingEnd ℂ) z = z := by linear_combination -hcase
    have hzre : ((z.re : ℝ) : ℂ) = z := Complex.conj_eq_iff_re.mp hconj
    have hreal : z.re ^ (2 : ℕ) + 2 * b * z.re + 1 = 0 := by
      have hc : ((z.re ^ (2 : ℕ) + 2 * b * z.re + 1 : ℝ) : ℂ) = 0 := by
        push_cast
        rw [hzre]
        linear_combination h0
      exact_mod_cast hc
    have h1 : (z.re + b) ^ (2 : ℕ) = b ^ (2 : ℕ) - 1 := by linear_combination hreal
    have h2 : (z.re + b) ^ (2 : ℕ) = 0 :=
      le_antisymm (by linarith) (sq_nonneg _)
    have hr0 : z.re + b = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2
    have hb1 : b ^ (2 : ℕ) = 1 := by linear_combination h2 - h1
    have hr : z.re = -b := by linear_combination hr0
    calc ‖z‖ = ‖((z.re : ℝ) : ℂ)‖ := by rw [hzre]
      _ = |z.re| := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ = |b| := by rw [hr, abs_neg]
      _ = 1 := eq_one_of_sq_eq_one_of_nonneg (by rw [sq_abs]; exact hb1) (abs_nonneg b)
  · -- the conjugate is the reciprocal Vieta partner: `z z̄ = 1`
    have hzw : z + 2 * (b : ℂ) = -(starRingEnd ℂ) z := by linear_combination hcase
    have hprod : z * (starRingEnd ℂ) z = 1 := by
      linear_combination z * hzw - h0
    rw [Complex.mul_conj] at hprod
    have hn : normSq z = 1 := by exact_mod_cast hprod
    have h2 : ‖z‖ ^ (2 : ℕ) = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hn
    exact eq_one_of_sq_eq_one_of_nonneg h2 (norm_nonneg z)

/-- **Marginal decoupling, positive end.** At coupling `b = 1` the two-spin polynomial
factorizes: the interaction decouples into independent sites. -/
theorem leeYangTwoSpin_marginal_pos (z w : ℂ) :
    leeYangTwoSpin 1 z w = (1 + z) * (1 + w) := by
  unfold leeYangTwoSpin
  push_cast
  ring

/-- **Marginal decoupling, negative end.** At coupling `b = −1` the two-spin
polynomial factorizes with the reflected pinned point. -/
theorem leeYangTwoSpin_marginal_neg (z w : ℂ) :
    leeYangTwoSpin (-1) z w = (1 - z) * (1 - w) := by
  unfold leeYangTwoSpin
  push_cast
  ring

/-- At the marginal coupling the zero set degenerates to the pinned hyperplane pair:
the forcing mechanism does not leak zeros off the circle, it collapses them onto a
single point of it. -/
theorem leeYangTwoSpin_marginal_zero_iff (z w : ℂ) :
    leeYangTwoSpin 1 z w = 0 ↔ z = -1 ∨ w = -1 := by
  rw [leeYangTwoSpin_marginal_pos, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · rintro (h | h)
    · exact Or.inl (by rw [h]; ring)
    · exact Or.inr (by rw [h]; ring)

/-- On the diagonal the marginal polynomial is a perfect square: the two circle zeros
collide at the pinned point `z = −1` — the degeneration of the mechanism is a
collision of zeros at the boundary of the forced region. -/
theorem leeYangTwoSpin_marginal_diagonal_sq (z : ℂ) :
    leeYangTwoSpin 1 z z = (1 + z) ^ (2 : ℕ) := by
  unfold leeYangTwoSpin
  push_cast
  ring

/-- Reflecting the coupling reflects the fugacities. -/
theorem leeYangTwoSpin_neg_coupling (b : ℝ) (z w : ℂ) :
    leeYangTwoSpin (-b) z w = leeYangTwoSpin b (-z) (-w) := by
  unfold leeYangTwoSpin
  push_cast
  ring

/-- **The anti-forced (fake) region.** For coupling `b > 1` confinement fails from
inside: the diagonal acquires a zero strictly inside the unit disc. -/
theorem exists_zero_in_polydisk {b : ℝ} (hb : 1 < b) :
    ∃ z : ℂ, ‖z‖ < 1 ∧ z ≠ 0 ∧ leeYangTwoSpin b z z = 0 := by
  have h0 : (0 : ℝ) ≤ b ^ (2 : ℕ) - 1 := by nlinarith
  have hs := Real.sq_sqrt h0
  set r : ℝ := -b + Real.sqrt (b ^ (2 : ℕ) - 1) with hr
  have hrneg : r < 0 := by
    have hlt : Real.sqrt (b ^ (2 : ℕ) - 1) < b := by
      rw [Real.sqrt_lt' (by linarith)]
      linarith
    rw [hr]
    linarith
  have hrabs : |r| < 1 := by
    rw [abs_of_neg hrneg]
    have h1 : b - 1 < Real.sqrt (b ^ (2 : ℕ) - 1) := by
      rw [show (b - 1 < Real.sqrt (b ^ (2 : ℕ) - 1)) ↔ ((b - 1) ^ (2 : ℕ) < b ^ (2 : ℕ) - 1) from
        Real.lt_sqrt (by linarith)]
      nlinarith
    rw [hr]
    linarith
  have hzero : r ^ (2 : ℕ) + 2 * b * r + 1 = 0 := by
    rw [hr]
    linear_combination hs
  refine ⟨(r : ℂ), ?_, ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact hrabs
  · exact Complex.ofReal_ne_zero.mpr hrneg.ne
  · rw [leeYangTwoSpin_diagonal]
    have hc : ((r ^ (2 : ℕ) + 2 * b * r + 1 : ℝ) : ℂ) = 0 := by
      rw [hzero]
      norm_num
    push_cast at hc
    linear_combination hc

/-- The anti-forced region at the negative end, by coupling reflection. -/
theorem exists_zero_in_polydisk_of_lt_neg {b : ℝ} (hb : b < -1) :
    ∃ z : ℂ, ‖z‖ < 1 ∧ z ≠ 0 ∧ leeYangTwoSpin b z z = 0 := by
  obtain ⟨z, hz1, hz0, hzero⟩ := exists_zero_in_polydisk (b := -b) (by linarith)
  refine ⟨-z, by simpa using hz1, neg_ne_zero.mpr hz0, ?_⟩
  rw [← leeYangTwoSpin_neg_coupling]
  simpa using hzero

/-- The confinement predicate: no zero of the two-spin polynomial has both fugacities
in the open unit disc. -/
def TwoSpinConfined (b : ℝ) : Prop :=
  ∀ z w : ℂ, leeYangTwoSpin b z w = 0 → ‖z‖ < 1 → 1 ≤ ‖w‖

/-- **The trichotomy packaged.** Confinement holds exactly on the closed coupling
interval `|b| ≤ 1`: its interior is the forced region, its boundary the degeneration
locus, its complement the fake region rejected by the sign of `1 − b²`. -/
theorem twoSpinConfined_iff_abs_le_one (b : ℝ) : TwoSpinConfined b ↔ |b| ≤ 1 := by
  constructor
  · intro h
    by_contra hb
    rcases lt_abs.mp (not_le.mp hb) with h1 | h1
    · obtain ⟨z, hz1, _, hzero⟩ := exists_zero_in_polydisk h1
      exact absurd hz1 (not_lt.mpr (h z z hzero hz1))
    · obtain ⟨z, hz1, _, hzero⟩ := exists_zero_in_polydisk_of_lt_neg (by linarith)
      exact absurd hz1 (not_lt.mpr (h z z hzero hz1))
  · intro hb z w h0 hz
    exact leeYang_confinement hb h0 hz

/-- The confined couplings form the closed interval `[−1, 1]`. -/
theorem twoSpinConfined_eq_Icc : {b : ℝ | TwoSpinConfined b} = Set.Icc (-1) 1 := by
  ext b
  simp [twoSpinConfined_iff_abs_le_one, abs_le]

end

end GaloisForLFunctions

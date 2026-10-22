import GaloisForLFunctions.RHTower.CCM.CCMRelativeLogDerivCoordinateIndex
import GaloisForLFunctions.HTGeometry.ShiftedDerivativeCoercivity

/-!
# The completed causal quotient and its one exponential-weight seam

Two exact mechanisms drive the card.

*Strict contraction.*  Along the horizontal segment from `c` to `c + 2ω` the squared modulus of an
entire function with positive logarithmic-derivative real part is strictly increasing, because

```text
d/dt normSq (X (c + t)) = 2 Re (conj (X) X') = 2 normSq (X) Re (X'/X) > 0 .
```

Hence `|X(c)/X(c + 2ω)| < 1` unconditionally on the region where `Re (X'/X) > 0`, which the
classical zero strip supplies for `Re w > 1/2`.

*Safe weighted width.*  For every centred zero `mu` with `Re mu < d`,

```text
|d + ω + i t − mu|² − |d − ω + i t − mu|² = 4 ω (d − Re mu) > 0 ,
```

so each paired canonical-product factor is no larger on the left line than on the right one.  This
is the factorwise comparison behind the unconditional safe width `0 ≤ a ≤ ω`; the target width is
`a_ω = 1/2 + ω`, so the invariant prelimit deficit is exactly `1/2`.
-/

open Complex Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The strict contraction -/

/-- The logarithmic-derivative form of the squared-modulus derivative. -/
theorem re_mul_conj_eq_normSq_mul {z w : ℂ} (hz : z ≠ 0) :
    (w * (starRingEnd ℂ) z).re = ‖z‖ ^ (2 : ℕ) * (w / z).re := by
  have hnorm : ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) = (starRingEnd ℂ) z * z := by
    rw [← Complex.normSq_eq_conj_mul_self]
    rw [Complex.normSq_eq_norm_sq]
  have hval : w * (starRingEnd ℂ) z = ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) * (w / z) := by
    rw [hnorm]
    field_simp
  rw [hval, Complex.re_ofReal_mul]

/-- **Equation (7).**  Positive logarithmic-derivative real part makes the squared modulus
strictly increase along the horizontal segment. -/
theorem strictMonoOn_normSq_shift {X X' : ℂ → ℂ} {c : ℂ} {ω : ℝ}
    (hd : ∀ u : ℂ, HasDerivAt X (X' u) u)
    (hne : ∀ t : ℝ, X (c + (t : ℂ)) ≠ 0)
    (hpos : ∀ t : ℝ, t ∈ Ioo (0 : ℝ) (2 * ω) → 0 < (X' (c + (t : ℂ)) / X (c + (t : ℂ))).re) :
    StrictMonoOn (fun t : ℝ => ‖X (c + (t : ℂ))‖ ^ (2 : ℕ)) (Icc (0 : ℝ) (2 * ω)) := by
  have hcurve : ∀ t : ℝ, HasDerivAt (fun s : ℝ => X (c + (s : ℂ))) (X' (c + (t : ℂ))) t := by
    intro t
    have hofr : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have hlin : HasDerivAt (fun s : ℝ => c + (s : ℂ)) 1 t := by
      simpa using hofr.const_add c
    have h := (hd (c + (t : ℂ))).scomp t hlin
    rw [one_smul] at h
    exact h
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ‖X (c + (s : ℂ))‖ ^ (2 : ℕ))
      (2 * (X' (c + (t : ℂ)) * (starRingEnd ℂ) (X (c + (t : ℂ)))).re) t :=
    fun t => GaloisForLFunctions.HTGeometry.hasDerivAt_normSq_comp (hcurve t)
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
  · exact fun t _ => ((hderiv t).continuousAt).continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hderiv t).deriv, re_mul_conj_eq_normSq_mul (hne t)]
    have h1 : 0 < ‖X (c + (t : ℂ))‖ ^ (2 : ℕ) := by
      have := norm_pos_iff.2 (hne t)
      positivity
    have h2 := hpos t ht
    positivity

/-- **Equation (2).**  The completed causal quotient is a strict contraction on the region where
the logarithmic derivative has positive real part. -/
theorem normSq_lt_normSq_shift {X X' : ℂ → ℂ} {c : ℂ} {ω : ℝ} (hω : 0 < ω)
    (hd : ∀ u : ℂ, HasDerivAt X (X' u) u)
    (hne : ∀ t : ℝ, X (c + (t : ℂ)) ≠ 0)
    (hpos : ∀ t : ℝ, t ∈ Ioo (0 : ℝ) (2 * ω) → 0 < (X' (c + (t : ℂ)) / X (c + (t : ℂ))).re) :
    ‖X c‖ ^ (2 : ℕ) < ‖X (c + ((2 * ω : ℝ) : ℂ))‖ ^ (2 : ℕ) := by
  have hmono := strictMonoOn_normSq_shift hd hne hpos
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (2 * ω) := ⟨le_refl _, by linarith⟩
  have h1 : (2 * ω : ℝ) ∈ Icc (0 : ℝ) (2 * ω) := ⟨by linarith, le_refl _⟩
  have h := hmono h0 h1 (by linarith)
  simpa using h

/-! ## The safe weighted width -/

/-- **Equation (10d).**  The exact factorwise comparison across the shift. -/
theorem normSq_shift_difference (d ω t : ℝ) (μ : ℂ) :
    Complex.normSq ((((d + ω : ℝ)) : ℂ) + Complex.I * (t : ℂ) - μ)
        - Complex.normSq ((((d - ω : ℝ)) : ℂ) + Complex.I * (t : ℂ) - μ)
      = 4 * ω * (d - μ.re) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- **Equation (10d), consequence.**  Every paired canonical-product factor is no larger on the
left line than on the right one. -/
theorem normSq_shift_le (d t : ℝ) {ω : ℝ} (hω : 0 ≤ ω) {μ : ℂ} (hμ : μ.re ≤ d) :
    Complex.normSq ((((d - ω : ℝ)) : ℂ) + Complex.I * (t : ℂ) - μ)
      ≤ Complex.normSq ((((d + ω : ℝ)) : ℂ) + Complex.I * (t : ℂ) - μ) := by
  have h := normSq_shift_difference d ω t μ
  have hnn : 0 ≤ 4 * ω * (d - μ.re) := by
    have : 0 ≤ d - μ.re := by linarith
    positivity
  linarith

/-! ## The distinguished exponent and the invariant half-unit -/

/-- The distinguished exponent `(11)`. -/
def distinguishedExponent (ω : ℝ) : ℝ := 1 / 2 + ω

/-- **Equation (25a).**  The invariant prelimit deficit between the target width and the
unconditional safe width is exactly one half, at every positive shift. -/
theorem distinguishedExponent_sub_safeWidth (ω : ℝ) :
    distinguishedExponent ω - ω = 1 / 2 := by
  unfold distinguishedExponent
  ring

/-- **Equation (12).**  Conjugation by the distinguished exponent shifts the quotient to the
symmetric shifted form. -/
theorem shifted_quotient_arguments (ω : ℝ) (z : ℂ) :
    (1 + (z - ((distinguishedExponent ω : ℝ) : ℂ)) = 1 / 2 - (ω : ℂ) + z)
      ∧ (1 + 2 * (ω : ℂ) + (z - ((distinguishedExponent ω : ℝ) : ℂ))
          = 1 / 2 + (ω : ℂ) + z) := by
  unfold distinguishedExponent
  constructor <;> push_cast <;> ring

/-- **Equations (15)–(16).**  The substitution `u = z + a_ω`, `q = v + a_ω` turns the ordinary
Schur denominator into the shifted Cauchy denominator of `(14)`. -/
theorem schur_denominator_substitution (ω : ℝ) (z v : ℂ) :
    (z + ((distinguishedExponent ω : ℝ) : ℂ))
        + (starRingEnd ℂ) (v + ((distinguishedExponent ω : ℝ) : ℂ))
      = 1 + 2 * (ω : ℂ) + z + (starRingEnd ℂ) v := by
  unfold distinguishedExponent
  rw [map_add, Complex.conj_ofReal]
  push_cast
  ring

/-- **Equation (30).**  The Blaschke zero attached to an off-line zero. -/
def blaschkeZero (ω : ℝ) (ρ : ℂ) : ℂ := ρ - ((distinguishedExponent ω : ℝ) : ℂ)

theorem re_blaschkeZero_pos {ω : ℝ} {ρ : ℂ} (h : distinguishedExponent ω < ρ.re) :
    0 < (blaschkeZero ω ρ).re := by
  unfold blaschkeZero
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith

end GaloisForLFunctions.RHTower

end

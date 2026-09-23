import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Projective-drift no-go for a charged clock

A persistent scalar constraint of positive clock charge cannot carry a
genuinely projective (Möbius) drift: the only projective transformations
that intertwine a nontrivial multiplicative clock dilation are the pure
scalings.  This is the algebraic heart of the charged-phase rigidity in
the clock-character classification — the fact that at positive charge the
constraint is multiplication by a single constant on a homogeneous core
generator.

Concretely, a Möbius transformation `x ↦ (a x + b)/(c x + d)` whose
composite with a nontrivial scaling `x ↦ μ x` (`μ ≠ 0, 1, -1`) satisfies
the intertwining identity `A(μ·q) = μ·A(q)` at a transcendental point `q`
must be diagonal (`b = c = 0`), i.e. the scaling `x ↦ (a/d) x`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **Coefficient no-go.**  The intertwining of a Möbius matrix `(a b; c d)`
with a scaling by `μ ≠ 0, 1, -1`, read off coefficient-by-coefficient
(the `q²`, `q¹`, `q⁰` relations), forces the off-diagonal entries `b, c`
to vanish. -/
theorem mobius_scaling_coeffs {K : Type*} [Field K]
    {a b c d μ : K} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) (hμm1 : μ ≠ -1)
    (hinv : a * d - b * c ≠ 0)
    (hq2 : a * c * μ = a * c * μ ^ (2 : ℕ))
    (hq1 : a * d * μ + b * c = a * d * μ + b * c * μ ^ (2 : ℕ))
    (hq0 : b * d = b * d * μ) :
    c = 0 ∧ b = 0 := by
  have hμ1' : (1 : K) - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hμ1)
  have hμm1' : (1 : K) + μ ≠ 0 := by
    intro h
    exact hμm1 (eq_neg_of_add_eq_zero_right h)
  -- the `q²` relation kills `a·c`
  have hac : a * c = 0 := by
    have h : a * c * (μ * (1 - μ)) = 0 := by linear_combination hq2
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' (mul_ne_zero hμ0 hμ1')
  -- the `q⁰` relation kills `b·d`
  have hbd : b * d = 0 := by
    have h : b * d * (1 - μ) = 0 := by linear_combination hq0
    exact (mul_eq_zero.mp h).resolve_right hμ1'
  -- the `q¹` relation kills `b·c`
  have hbc : b * c = 0 := by
    have h : b * c * ((1 - μ) * (1 + μ)) = 0 := by linear_combination hq1
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' (mul_ne_zero hμ1' hμm1')
  -- invertibility with `b·c = 0` forces the diagonal nonzero
  have had : a * d ≠ 0 := fun h => hinv (by rw [h, hbc, sub_zero])
  have ha : a ≠ 0 := left_ne_zero_of_mul had
  have hd : d ≠ 0 := right_ne_zero_of_mul had
  exact ⟨(mul_eq_zero.mp hac).resolve_left ha,
    (mul_eq_zero.mp hbd).resolve_right hd⟩

/-- **Projective-drift no-go.**  If a Möbius transformation `(a b; c d)`
intertwines the scaling `x ↦ μ x` (`μ ≠ 0, 1, -1`) at a point `q` whose
powers `1, q, q²` are linearly independent over the base field, then the
transformation is diagonal: `b = c = 0`.

The linear-independence hypothesis is exactly transcendence of `q` over
the constants; it is what the differential Lüroth generator supplies. -/
theorem mobius_commuting_scaling_forces_diagonal
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {a b c d μ : K} (q : F)
    (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) (hμm1 : μ ≠ -1)
    (hinv : a * d - b * c ≠ 0)
    (hlin : ∀ x y z : K, algebraMap K F x + algebraMap K F y * q
        + algebraMap K F z * q ^ (2 : ℕ) = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (hcomm : (algebraMap K F a * (algebraMap K F μ * q) + algebraMap K F b)
          * (algebraMap K F c * q + algebraMap K F d)
        = algebraMap K F μ * (algebraMap K F a * q + algebraMap K F b)
          * (algebraMap K F c * (algebraMap K F μ * q)
            + algebraMap K F d)) :
    c = 0 ∧ b = 0 := by
  -- extract the three coefficient relations from the transcendence of `q`
  have hcoeff : algebraMap K F (b * d - b * d * μ)
      + algebraMap K F (a * d * μ + b * c - (a * d * μ + b * c * μ ^ (2 : ℕ)))
        * q
      + algebraMap K F (a * c * μ - a * c * μ ^ (2 : ℕ)) * q ^ (2 : ℕ) = 0 := by
    simp only [map_sub, map_mul, map_add, map_pow]
    linear_combination hcomm
  obtain ⟨h0, h1, h2⟩ := hlin _ _ _ hcoeff
  exact mobius_scaling_coeffs hμ0 hμ1 hμm1 hinv
    (sub_eq_zero.mp h2) (sub_eq_zero.mp h1) (sub_eq_zero.mp h0)

/-- **Charged-phase linearization.**  A diagonal Möbius transformation is
the pure scaling `x ↦ (a/d) x`: at positive clock charge the constraint
is multiplication by the single constant `a/d`. -/
theorem mobius_diagonal_eq_scaling
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {a b c d : K} (q : F) (hb : b = 0) (hc : c = 0) :
    (algebraMap K F a * q + algebraMap K F b)
        / (algebraMap K F c * q + algebraMap K F d)
      = algebraMap K F (a / d) * q := by
  subst hb; subst hc
  simp only [map_zero, add_zero, zero_mul, zero_add]
  rw [map_div₀]
  exact mul_div_right_comm _ _ _

/-- **Charged-phase rigidity.**  Let `Φ, ρ` be `C`-algebra endomorphisms of `E` with `ρ q = μ q`
a nontrivial scaling (`μ ≠ 0, 1, -1`), let `Φ` act on the generator by the Möbius relation
`Φ q · (c q + d) = a q + b` with `ad - bc ≠ 0`, and suppose `Φ` and `ρ` commute at `q`.  If the
powers `1, q, q²` are linearly independent over `C`, then `Φ` is multiplication by the single
constant `a/d`:

`Φ q = (a/d) · q`.

This is the charged phase of the clock-character law: a positive-charge persistent scalar cannot
support nonlinear projective drift.  The Möbius and scaling representations are the differential
Lüroth and PGL₂-cocharacter inputs; the commutation is `ρ_λ Φ = Φ ρ_λ`. -/
theorem charged_clock_forces_multiplicative
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    (Φ ρ : E →ₐ[C] E) {a b c d μ : C} (q : E)
    (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) (hμm1 : μ ≠ -1)
    (hinv : a * d - b * c ≠ 0)
    (hlin : ∀ x y z : C, algebraMap C E x + algebraMap C E y * q
        + algebraMap C E z * q ^ (2 : ℕ) = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (hρq : ρ q = algebraMap C E μ * q)
    (hΦq : Φ q * (algebraMap C E c * q + algebraMap C E d)
        = algebraMap C E a * q + algebraMap C E b)
    (hcomm : Φ (ρ q) = ρ (Φ q)) :
    Φ q = algebraMap C E (a / d) * q := by
  -- the clock's action on `Φ q`, read off the Möbius relation
  have hρΦq : ρ (Φ q)
        * (algebraMap C E c * (algebraMap C E μ * q) + algebraMap C E d)
      = algebraMap C E a * (algebraMap C E μ * q) + algebraMap C E b := by
    have h := congrArg ρ hΦq
    simpa only [map_mul, map_add, AlgHom.commutes, hρq] using h
  -- commutation identifies `ρ (Φ q)` with `μ · Φ q`
  have hρΦ_eq : ρ (Φ q) = algebraMap C E μ * Φ q := by
    have h := hcomm
    rw [hρq, map_mul, AlgHom.commutes] at h
    exact h.symm
  have hI := hρΦq
  rw [hρΦ_eq] at hI
  -- the cross-multiplied intertwining identity, with no denominators
  have hpoly :
      (algebraMap C E a * (algebraMap C E μ * q) + algebraMap C E b)
        * (algebraMap C E c * q + algebraMap C E d)
      = algebraMap C E μ * (algebraMap C E a * q + algebraMap C E b)
        * (algebraMap C E c * (algebraMap C E μ * q) + algebraMap C E d) := by
    linear_combination
      (-(algebraMap C E c * q + algebraMap C E d)) * hI
      + (algebraMap C E μ
          * (algebraMap C E c * (algebraMap C E μ * q) + algebraMap C E d))
        * hΦq
  -- the projective-drift no-go forces the Möbius map diagonal
  obtain ⟨hc0, hb0⟩ :=
    mobius_commuting_scaling_forces_diagonal q hμ0 hμ1 hμm1 hinv hlin hpoly
  -- diagonal Möbius is pure scaling
  have hd0 : d ≠ 0 := fun h => hinv (by rw [hc0, hb0, h]; ring)
  have hdE : algebraMap C E d ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hd0).map (algebraMap C E)).ne_zero
  rw [hc0, hb0] at hΦq
  simp only [map_zero, zero_mul, zero_add, add_zero] at hΦq
  rw [map_div₀]
  field_simp
  linear_combination hΦq


end GaloisForLFunctions.HTGeometry

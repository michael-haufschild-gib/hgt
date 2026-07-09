/-
# Vertical periodicity dichotomy for critical-strip zeros

A meromorphic datum `f` on `ℂ` satisfies the *periodicity dichotomy* when every zero `ρ` in the
open critical strip `0 < Re ρ < 1` is either pinned to the critical line `Re ρ = ½` or lies on a
full two-sided vertical arithmetic progression of zeros `{ρ + kTi : k ∈ ℤ}` of some real period
`T > 0`. Off the line, in other words, the divisor is forced to be vertically periodic.

Column-factored Dirichlet data — finite products `F(s) = ∏_{i ∈ t} Ψᵢ(i^{−s})` of prime columns —
satisfy the dichotomy *unconditionally through the right disjunct*: any column zero already
propagates along the vertical progression of period `2π/log i` of the column responsible for it,
so there is never any need to reach the critical line. The dichotomy is stable under multiplying by
a column form, and its violation is an additive invariant: the *aperiodic core*, a zero that lies
on no full vertical progression, is inherited by one of the factors of any product.

The strip-localisation of `riemannZeta` zeros (no zeros on `Re ≥ 1`, and the reflection `ξ(1−s) =
ξ(s)` forcing `Re > 0` on the nontrivial divisor) turns the dichotomy for `riemannZeta` into an
exact restatement of the Riemann hypothesis, *once* the off-line vertical progressions are excluded:
under the hypothesis that no nontrivial strip zero off the line carries a vertical progression, the
dichotomy for `riemannZeta` and the Riemann hypothesis are equivalent. The column forms are the
regime where the aperiodicity that RH must exclude is structurally impossible, so RH lives entirely
in the aperiodic core outside the column regime.
-/
import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.DAColumnDivisor
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace RHTower

open Complex

/-- The vertical periodicity dichotomy for a datum `f`: every zero in the open critical strip
`0 < Re ρ < 1` is either on the critical line `Re ρ = ½` or sits on a full two-sided vertical
arithmetic progression of zeros `{ρ + kTi : k ∈ ℤ}` of some real period `T > 0`. The divisor off
the line is thus vertically periodic. -/
def PeriodicityDichotomy (f : ℂ → ℂ) : Prop :=
  ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → f ρ = 0 →
    ρ.re = 1/2 ∨ ∃ T : ℝ, 0 < T ∧ ∀ k : ℤ, f (ρ + (k * T) * Complex.I) = 0

/-- A column form satisfies the periodicity dichotomy through the right disjunct always. A strip
zero of `F` is a zero of the responsible column `i`, and that column depends on `s` only through
`i^{−s}`, invariant under the vertical shift of period `T = 2π/log i > 0`; so `F` vanishes on the
whole progression `{ρ + kTi : k ∈ ℤ}` and never needs to reach the critical line. Positivity of the
period uses `π > 0` and `log i > 0` for `i ≥ 2`. -/
theorem columnForm_periodicityDichotomy {t : Finset ℕ} {Ψ : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hF : ColumnForm t Ψ F) (ht : ∀ i ∈ t, 2 ≤ i) : PeriodicityDichotomy F := by
  intro ρ _ _ h0
  refine Or.inr ?_
  obtain ⟨i, hi, hall⟩ := columnForm_zero_periodic hF ht h0
  refine ⟨2 * Real.pi / Real.log i, ?_, fun k => ?_⟩
  · apply div_pos
    · have := Real.pi_pos; linarith
    · exact Real.log_pos (by have := ht i hi; exact_mod_cast (show (1 : ℕ) < i by omega))
  · convert hall k using 2
    push_cast
    ring

/-- Two column forms multiply to a column form over the union of their index sets: the summand of
the union product splits by `∏ (aᵢ · bᵢ) = (∏ aᵢ)(∏ bᵢ)`, and each guarded factor collapses to the
product over its own index set, since `(t₁ ∪ t₂) ∩ t₁ = t₁` and `(t₁ ∪ t₂) ∩ t₂ = t₂`. -/
theorem columnForm_mul {t₁ t₂ : Finset ℕ} {Ψ₁ Ψ₂ : ℕ → ℂ → ℂ} {F G : ℂ → ℂ}
    (h₁ : ColumnForm t₁ Ψ₁ F) (h₂ : ColumnForm t₂ Ψ₂ G) :
    ColumnForm (t₁ ∪ t₂)
      (fun i u => (if i ∈ t₁ then Ψ₁ i u else 1) * (if i ∈ t₂ then Ψ₂ i u else 1))
      (fun s => F s * G s) := by
  intro s
  show F s * G s =
      ∏ i ∈ t₁ ∪ t₂,
        (if i ∈ t₁ then Ψ₁ i ((i : ℂ) ^ (-s)) else 1) *
          (if i ∈ t₂ then Ψ₂ i ((i : ℂ) ^ (-s)) else 1)
  rw [Finset.prod_mul_distrib, h₁ s, h₂ s]
  congr 1
  · rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_left]
  · rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_right]

/-- The dichotomy is stable under multiplication by a column form. A strip zero of `f · g` is a zero
of a factor. If `g` vanishes, its column progression of period `2π/log i` lifts to the product
(multiplying by anything preserves the zero). If `f` vanishes, the dichotomy for `f` either pins `ρ`
to the line or yields an `f`-progression, which again lifts to the product. -/
theorem periodicityDichotomy_mul_columnForm {f g : ℂ → ℂ} {t : Finset ℕ} {Ψ : ℕ → ℂ → ℂ}
    (hf : PeriodicityDichotomy f) (hg : ColumnForm t Ψ g) (ht : ∀ i ∈ t, 2 ≤ i) :
    PeriodicityDichotomy (fun s => f s * g s) := by
  intro ρ hpos hlt1 h0
  have h0' : f ρ * g ρ = 0 := h0
  rcases mul_eq_zero.mp h0' with hfρ | hgρ
  · rcases hf ρ hpos hlt1 hfρ with hhalf | ⟨T, hT, hprog⟩
    · exact Or.inl hhalf
    · exact Or.inr ⟨T, hT, fun k => mul_eq_zero_of_left (hprog k) _⟩
  · refine Or.inr ?_
    obtain ⟨i, hi, hall⟩ := columnForm_zero_periodic hg ht hgρ
    refine ⟨2 * Real.pi / Real.log i, ?_, fun k => ?_⟩
    · apply div_pos
      · have := Real.pi_pos; linarith
      · exact Real.log_pos (by have := ht i hi; exact_mod_cast (show (1 : ℕ) < i by omega))
    · refine mul_eq_zero_of_right _ ?_
      convert hall k using 2
      push_cast
      ring

/-- A zero of `f` at `ρ` that lies on no full vertical progression of zeros — the aperiodic core of
the divisor at `ρ`. -/
def AperiodicZeroAt (f : ℂ → ℂ) (ρ : ℂ) : Prop :=
  f ρ = 0 ∧ ¬ ∃ T : ℝ, 0 < T ∧ ∀ k : ℤ, f (ρ + (k * T) * Complex.I) = 0

/-- The aperiodic core is subadditive under products: an aperiodic zero of `f · g` at `ρ` is an
aperiodic zero of one of the factors. The product zero comes from a factor, and that factor's zero
must itself be aperiodic — a full progression of factor-zeros would lift to the product,
contradicting aperiodicity there. -/
theorem aperiodicZeroAt_mul {f g : ℂ → ℂ} {ρ : ℂ}
    (h : AperiodicZeroAt (fun s => f s * g s) ρ) : AperiodicZeroAt f ρ ∨ AperiodicZeroAt g ρ := by
  obtain ⟨hz, hnp⟩ := h
  have hz' : f ρ * g ρ = 0 := hz
  rcases mul_eq_zero.mp hz' with hf | hg
  · refine Or.inl ⟨hf, ?_⟩
    rintro ⟨T, hT, hprog⟩
    exact hnp ⟨T, hT, fun k => mul_eq_zero_of_left (hprog k) _⟩
  · refine Or.inr ⟨hg, ?_⟩
    rintro ⟨T, hT, hprog⟩
    exact hnp ⟨T, hT, fun k => mul_eq_zero_of_right _ (hprog k)⟩

/-- Under the exclusion of off-line vertical progressions of `riemannZeta`-zeros in the strip, the
periodicity dichotomy for `riemannZeta` is equivalent to the Riemann hypothesis.

Forward: a strip zero of `ζ` with `Re < 1` (no zeros on `Re ≥ 1`) and `Re > 0` (the reflection
`ξ(1−s) = ξ(s)` sends a putative `Re ≤ 0` zero to a `Re ≥ 1` zero of `ζ`, excluded) meets the
dichotomy; the right disjunct is a progression, forbidden off the line by hypothesis, so `Re = ½`.

Backward: a strip zero is nontrivial (trivial zeros have `Re ≤ −2 < 0`) and `≠ 1` (its `Re < 1`),
so the Riemann hypothesis pins it to the line — the left disjunct. -/
theorem periodicityDichotomy_zeta_iff_riemannHypothesis
    (hAP : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1/2 →
      ¬ ∃ T : ℝ, 0 < T ∧ ∀ k : ℤ, riemannZeta (ρ + (k * T) * Complex.I) = 0) :
    PeriodicityDichotomy riemannZeta ↔ RiemannHypothesis := by
  constructor
  · intro hdich s hζ htriv hs1
    have hlt1 : s.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hζ
      norm_num at hζ
    have hgt0 : 0 < s.re := by
      by_contra h
      have h' : s.re ≤ 0 := not_lt.mp h
      have hxis : xi s = 0 := xi_eq_zero_of_zeta_eq_zero hζ htriv hs1
      have hxiw : xi (1 - s) = 0 := by rw [xi_one_sub]; exact hxis
      have hwre : 1 ≤ (1 - s).re := by
        simp only [Complex.sub_re, Complex.one_re]; linarith
      have hw1 : (1 - s) ≠ 1 := fun hh => hs0 (sub_eq_self.mp hh)
      have hwpos : 0 < (1 - s).re := lt_of_lt_of_le zero_lt_one hwre
      have hζw : riemannZeta (1 - s) = 0 := (xi_eq_zero_iff hwpos hw1).mp hxiw
      exact riemannZeta_ne_zero_of_one_le_re hwre hζw
    rcases hdich s hgt0 hlt1 hζ with hhalf | hprog
    · exact hhalf
    · by_contra hne
      exact hAP s hgt0 hlt1 hne hprog
  · intro hRH ρ hpos hlt1 hζ
    refine Or.inl ?_
    apply hRH ρ hζ
    · rintro ⟨n, rfl⟩
      have hre' : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
        simp [Complex.mul_re]
      rw [hre'] at hpos
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    · intro hh
      rw [hh, Complex.one_re] at hlt1
      exact lt_irrefl 1 hlt1

end RHTower

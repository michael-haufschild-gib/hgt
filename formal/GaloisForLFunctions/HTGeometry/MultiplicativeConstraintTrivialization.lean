import Mathlib.Algebra.Algebra.Field
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Tactic.FieldSimp

/-!
# Multiplicative constraint trivialization

A source whose translation multipliers lie in a smaller field belongs to that field exactly when
the multiplier system can already be trivialized there, provided the simultaneous fixed field
descends to the base.  This is the algebraic local-to-global obstruction behind the proposed
differential-algebraic anomaly of the elliptic gamma function.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Two nonzero sources with the same multiplicative constraint multipliers differ by a nonzero
simultaneous constant.  This is the derivation-free uniqueness theorem behind the pretemporal
interpretation: global compatibility selects the source before any differential structure is
chosen. -/
theorem multiplicative_constraint_source_unique_up_to_constant
    {I C M : Type*} [Field C] [Field M] [Algebra C M]
    (sigma : I → M ≃+* M)
    (hfixed : ∀ z : M, (∀ i, sigma i z = z) → ∃ c : C, algebraMap C M c = z)
    (a : I → M) {x y : M} (hx : x ≠ 0) (hy : y ≠ 0)
    (hshiftx : ∀ i, sigma i x = a i * x)
    (hshifty : ∀ i, sigma i y = a i * y) :
    ∃ c : C, c ≠ 0 ∧ x = algebraMap C M c * y := by
  let z : M := x / y
  have hzfixed : ∀ i, sigma i z = z := by
    intro i
    have hai : a i ≠ 0 := by
      intro hai
      have hsigmay : sigma i y ≠ 0 := (map_ne_zero (sigma i)).2 hy
      exact hsigmay (by simpa [hai] using hshifty i)
    dsimp only [z]
    rw [map_div₀, hshiftx, hshifty]
    field_simp
  obtain ⟨c, hc⟩ := hfixed z hzfixed
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hx
    have hz0 : z = 0 := by
      rw [← hc, hc0, map_zero]
    rcases div_eq_zero_iff.mp hz0 with hx0 | hy0
    · exact hx0
    · exact (hy hy0).elim
  refine ⟨c, hc0, ?_⟩
  rw [hc]
  dsimp only [z]
  field_simp

/-- A multiplicative constraint system has a nonzero base-field trivializing section if and only
if its given solution descends to the base field.  The forward implication is the substantive one:
the quotient of two solutions is simultaneously fixed, hence descends by `hfixed`.

No cocycle, Picard--Vessiot, or differential-algebraic assumption is hidden in this theorem.
Those structures enter applications through the choice of `B`, `M`, and the automorphism family. -/
theorem exists_base_multiplicative_trivialization_iff_exists_base_source
    {I B M : Type*} [Field B] [Field M] [Algebra B M]
    (tau : I → B ≃+* B) (sigma : I → M ≃+* M)
    (hcomp : ∀ i b, sigma i (algebraMap B M b) = algebraMap B M (tau i b))
    (halg : Function.Injective (algebraMap B M))
    (hfixed : ∀ z : M, (∀ i, sigma i z = z) → ∃ b : B, algebraMap B M b = z)
    (a : I → B) {x : M} (hx : x ≠ 0)
    (hshift : ∀ i, sigma i x = algebraMap B M (a i) * x) :
    (∃ b : B, b ≠ 0 ∧ ∀ i, tau i b = a i * b) ↔
      ∃ b : B, algebraMap B M b = x := by
  constructor
  · rintro ⟨b, hb, hbshift⟩
    let z : M := x / algebraMap B M b
    have hbM : algebraMap B M b ≠ 0 := by
      simpa using halg.ne hb
    have hzfixed : ∀ i, sigma i z = z := by
      intro i
      have hai : a i ≠ 0 := by
        intro hai
        have htau : tau i b ≠ 0 := (map_ne_zero (tau i)).2 hb
        exact htau (by simpa [hai] using hbshift i)
      dsimp only [z]
      rw [map_div₀, hshift, hcomp, hbshift, map_mul]
      have haiM : algebraMap B M (a i) ≠ 0 := by
        simpa using halg.ne hai
      field_simp
    obtain ⟨c, hc⟩ := hfixed z hzfixed
    refine ⟨b * c, ?_⟩
    rw [map_mul, hc]
    dsimp only [z]
    field_simp
  · rintro ⟨b, hbsource⟩
    have hb : b ≠ 0 := by
      intro hb
      apply hx
      rw [← hbsource, hb, map_zero]
    refine ⟨b, hb, ?_⟩
    intro i
    exact halg (calc
      algebraMap B M (tau i b) = sigma i (algebraMap B M b) := (hcomp i b).symm
      _ = sigma i x := congrArg (sigma i) hbsource
      _ = algebraMap B M (a i) * x := hshift i
      _ = algebraMap B M (a i) * algebraMap B M b := congrArg _ hbsource.symm
      _ = algebraMap B M (a i * b) := (map_mul (algebraMap B M) (a i) b).symm)

/-- If the source does not descend to the base, its multiplicative constraint system has no
base-field trivialization.  In the intended application the base is the full differentially
algebraic meromorphic sector, so this is the exact nontriviality statement rather than a metaphor. -/
theorem no_base_multiplicative_trivialization_of_no_base_source
    {I B M : Type*} [Field B] [Field M] [Algebra B M]
    (tau : I → B ≃+* B) (sigma : I → M ≃+* M)
    (hcomp : ∀ i b, sigma i (algebraMap B M b) = algebraMap B M (tau i b))
    (halg : Function.Injective (algebraMap B M))
    (hfixed : ∀ z : M, (∀ i, sigma i z = z) → ∃ b : B, algebraMap B M b = z)
    (a : I → B) {x : M} (hx : x ≠ 0)
    (hshift : ∀ i, sigma i x = algebraMap B M (a i) * x)
    (hnotbase : ¬ ∃ b : B, algebraMap B M b = x) :
    ¬ ∃ b : B, b ≠ 0 ∧ ∀ i, tau i b = a i * b := by
  intro htrivial
  apply hnotbase
  exact (exists_base_multiplicative_trivialization_iff_exists_base_source
    tau sigma hcomp halg hfixed a hx hshift).mp htrivial

end

end GaloisForLFunctions

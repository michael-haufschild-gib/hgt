import GaloisForLFunctions.RHTower.PrimeCoShiftModel
import GaloisForLFunctions.RHTower.RiemannComplexModularCharacterLaw
import GaloisForLFunctions.RHTower.DeningerArithmeticThreeTermCohomology
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# Reflection-odd singular cohomology of the all-prime co-shift

The all-prime co-shift eigenprofile at `s` is `n ↦ n⁻ˢ`.  Every finite
coordinate truncation belongs to `ℓ²`, so finite algebraic cohomology erases
the difference between the profile and its functional-equation reflection.
The full difference need not be square summable.

This file makes that completion defect into a literal three-term complex

`ℓ²(ℕ₊) → (ℕ₊ → ℂ) → 0`.

Its reflection-odd class is zero exactly on the critical line.  It is
anti-invariant under reflection, while every finite truncation is a boundary.
Thus the obstruction is genuinely singular/cofinal, not a finite packet
class.  On the Xi divisor, global vanishing is exactly RH; that final
vanishing is an endpoint, not asserted here as an unconditional source law.
-/

namespace RHTower.PrimeCoShift

open RHTower
open scoped ENNReal

noncomputable section

/-- Forget the square-summability certificate of a co-shift Hilbert vector. -/
def primeCoShiftSequenceInclusion : H →ₗ[ℂ] (ℕ+ → ℂ) where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Singular co-shift complex: square-summable profiles are boundaries. -/
def primeCoShiftSingularThreeTermComplex :
    DeningerArithmeticThreeTermComplex ℂ H (ℕ+ → ℂ) ℂ where
  d0 := primeCoShiftSequenceInclusion
  d1 := 0
  d1_comp_d0 := by simp

/-- Singular middle cohomology of the all-prime co-shift row. -/
abbrev PrimeCoShiftSingularH1 := primeCoShiftSingularThreeTermComplex.H1

/-- Difference of forward and reflected all-prime co-shift eigenprofiles. -/
def primeCoShiftReflectionOddGroundFun (s : ℂ) : ℕ+ → ℂ :=
  groundFun s - groundFun (criticalLineReflectionPoint s)

/-- The reflection-odd profile as a degree-one cocycle. -/
def primeCoShiftReflectionOddCocycle (s : ℂ) :
    primeCoShiftSingularThreeTermComplex.cycles1 :=
  ⟨primeCoShiftReflectionOddGroundFun s, by
    change (0 : (ℕ+ → ℂ) →ₗ[ℂ] ℂ)
      (primeCoShiftReflectionOddGroundFun s) = 0
    rfl⟩

/-- Singular/cofinal secondary class of the reflected co-shift pair. -/
def primeCoShiftReflectionOddClass (s : ℂ) : PrimeCoShiftSingularH1 :=
  Submodule.Quotient.mk (primeCoShiftReflectionOddCocycle s)

/-- At or below the Hilbert wall, the formal co-shift eigenprofile is not in
`ℓ²`. -/
theorem not_memℓp_groundFun {s : ℂ} (hs : s.re ≤ 1 / 2) :
    ¬ Memℓp (groundFun s) 2 := by
  intro hmem
  have hsum :
      Summable fun n : ℕ+ => ‖groundFun s n‖ ^ (2 : ℝ≥0∞).toReal :=
    hmem.summable (by norm_num)
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2] at hsum
  have hprofile : ∀ n : ℕ+, ‖groundFun s n‖ ^ (2 : ℝ) =
      (((n : ℕ) : ℝ) ^ (2 * s.re))⁻¹ := by
    intro n
    have hn : 0 < (n : ℕ) := n.property
    have hb : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [groundFun, Complex.norm_natCast_cpow_of_pos hn]
    simp only [Complex.neg_re]
    rw [← Real.rpow_mul hb, ← Real.rpow_neg hb]
    congr 1
    ring
  exact not_summable_rpow_inv_of_le hs (hsum.congr hprofile)

/-- Exact `ℓ²` abscissa of the formal common co-shift eigenprofile. -/
theorem memℓp_groundFun_iff (s : ℂ) :
    Memℓp (groundFun s) 2 ↔ 1 / 2 < s.re := by
  constructor
  · intro hmem
    by_contra hnot
    exact not_memℓp_groundFun (le_of_not_gt hnot) hmem
  · exact memℓp_groundFun

/-- The singular class is zero precisely when its representative is an
`ℓ²` boundary. -/
theorem primeCoShiftReflectionOddClass_eq_zero_iff_memℓp (s : ℂ) :
    primeCoShiftReflectionOddClass s = 0 ↔
      Memℓp (primeCoShiftReflectionOddGroundFun s) 2 := by
  rw [primeCoShiftReflectionOddClass,
    DeningerArithmeticThreeTermComplex.H1_mk_eq_zero_iff]
  constructor
  · rintro ⟨x, hx⟩
    change primeCoShiftSequenceInclusion x =
      primeCoShiftReflectionOddGroundFun s at hx
    rw [← hx]
    exact x.property
  · intro hmem
    refine ⟨⟨primeCoShiftReflectionOddGroundFun s, hmem⟩, ?_⟩
    rfl

/-- The difference `n⁻ˢ - n⁻⁽¹⁻s̄⁾` is square summable only when it vanishes
identically.  Off the line, exactly one of its two terms lies in `ℓ²`. -/
theorem memℓp_primeCoShiftReflectionOddGroundFun_iff (s : ℂ) :
    Memℓp (primeCoShiftReflectionOddGroundFun s) 2 ↔
      s.re = 1 / 2 := by
  constructor
  · intro hodd
    by_cases hline : s.re = 1 / 2
    · exact hline
    rcases lt_or_gt_of_ne hline with hleft | hright
    · have hreflect : 1 / 2 < (criticalLineReflectionPoint s).re := by
        have hw := criticalLineReflectionPoint_weight s
        linarith
      have href : Memℓp (groundFun (criticalLineReflectionPoint s)) 2 :=
        memℓp_groundFun hreflect
      have hs : Memℓp (groundFun s) 2 := by
        have := hodd.add href
        simpa [primeCoShiftReflectionOddGroundFun, sub_add_cancel] using this
      exact False.elim ((not_memℓp_groundFun (le_of_lt hleft)) hs)
    · have hs : Memℓp (groundFun s) 2 := memℓp_groundFun hright
      have href : Memℓp (groundFun (criticalLineReflectionPoint s)) 2 := by
        have := hs.sub hodd
        simpa [primeCoShiftReflectionOddGroundFun,
          sub_sub_cancel_left] using this
      have hreflect : (criticalLineReflectionPoint s).re ≤ 1 / 2 := by
        have hw := criticalLineReflectionPoint_weight s
        linarith
      exact False.elim ((not_memℓp_groundFun hreflect) href)
  · intro hline
    have href : criticalLineReflectionPoint s = s := by
      apply Complex.ext
      · rw [criticalLineReflectionPoint, Complex.sub_re,
          Complex.one_re, Complex.conj_re]
        linarith
      · simp [criticalLineReflectionPoint]
    rw [primeCoShiftReflectionOddGroundFun, href, sub_self]
    apply memℓp_gen
    have hz : Summable (fun _ : ℕ+ => (0 : ℝ)) := summable_zero
    convert hz using 1
    norm_num

/-- **PCS singular-class classification.**  The full reflection-odd
co-shift class vanishes exactly on the critical line. -/
theorem primeCoShiftReflectionOddClass_eq_zero_iff (s : ℂ) :
    primeCoShiftReflectionOddClass s = 0 ↔ s.re = 1 / 2 := by
  rw [primeCoShiftReflectionOddClass_eq_zero_iff_memℓp,
    memℓp_primeCoShiftReflectionOddGroundFun_iff]

/-- Critical-line reflection is involutive on the co-shift parameter. -/
theorem criticalLineReflectionPoint_involutive (s : ℂ) :
    criticalLineReflectionPoint (criticalLineReflectionPoint s) = s := by
  rw [criticalLineReflectionPoint, criticalLineReflectionPoint,
    map_sub, map_one, Complex.conj_conj]
  ring

/-- The profile is genuinely reflection-odd. -/
theorem primeCoShiftReflectionOddGroundFun_reflection (s : ℂ) :
    primeCoShiftReflectionOddGroundFun (criticalLineReflectionPoint s) =
      -primeCoShiftReflectionOddGroundFun s := by
  funext n
  simp only [primeCoShiftReflectionOddGroundFun, Pi.sub_apply, Pi.neg_apply,
    criticalLineReflectionPoint_involutive]
  ring

/-- Reflection negates the singular cohomology class. -/
theorem primeCoShiftReflectionOddClass_reflection (s : ℂ) :
    primeCoShiftReflectionOddClass (criticalLineReflectionPoint s) =
      -primeCoShiftReflectionOddClass s := by
  have heq :
      primeCoShiftReflectionOddCocycle (criticalLineReflectionPoint s) =
        -primeCoShiftReflectionOddCocycle s := by
    apply Subtype.ext
    exact primeCoShiftReflectionOddGroundFun_reflection s
  change Submodule.Quotient.mk
      (primeCoShiftReflectionOddCocycle (criticalLineReflectionPoint s)) =
    -Submodule.Quotient.mk (primeCoShiftReflectionOddCocycle s)
  rw [← Submodule.Quotient.mk_neg, heq]

/-- Restriction of the singular representative to a finite coordinate set. -/
def finitePrimeCoShiftReflectionOddGroundFun
    (S : Finset ℕ+) (s : ℂ) : ℕ+ → ℂ :=
  fun n => if n ∈ S then primeCoShiftReflectionOddGroundFun s n else 0

theorem memℓp_finitePrimeCoShiftReflectionOddGroundFun
    (S : Finset ℕ+) (s : ℂ) :
    Memℓp (finitePrimeCoShiftReflectionOddGroundFun S s) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  refine summable_of_ne_finset_zero (s := S) fun n hn => ?_
  simp [finitePrimeCoShiftReflectionOddGroundFun, hn]

/-- Every finite coordinate restriction is a cocycle. -/
def finitePrimeCoShiftReflectionOddCocycle
    (S : Finset ℕ+) (s : ℂ) :
    primeCoShiftSingularThreeTermComplex.cycles1 :=
  ⟨finitePrimeCoShiftReflectionOddGroundFun S s, by
    change (0 : (ℕ+ → ℂ) →ₗ[ℂ] ℂ)
      (finitePrimeCoShiftReflectionOddGroundFun S s) = 0
    rfl⟩

/-- Cohomology class of a finite coordinate restriction. -/
def finitePrimeCoShiftReflectionOddClass
    (S : Finset ℕ+) (s : ℂ) : PrimeCoShiftSingularH1 :=
  Submodule.Quotient.mk (finitePrimeCoShiftReflectionOddCocycle S s)

/-- **Finite exactness erases the obstruction.**  Every finite truncation is
an `ℓ²` boundary, at every spectral parameter. -/
theorem finitePrimeCoShiftReflectionOddClass_eq_zero
    (S : Finset ℕ+) (s : ℂ) :
    finitePrimeCoShiftReflectionOddClass S s = 0 := by
  rw [finitePrimeCoShiftReflectionOddClass,
    DeningerArithmeticThreeTermComplex.H1_mk_eq_zero_iff]
  exact ⟨⟨finitePrimeCoShiftReflectionOddGroundFun S s,
    memℓp_finitePrimeCoShiftReflectionOddGroundFun S s⟩, rfl⟩

/-- On the critical line, the reflected profiles agree before quotienting. -/
theorem primeCoShiftReflectionOddGroundFun_eq_zero_of_re_eq_half
    {s : ℂ} (hs : s.re = 1 / 2) :
    primeCoShiftReflectionOddGroundFun s = 0 := by
  have href : criticalLineReflectionPoint s = s := by
    apply Complex.ext
    · rw [criticalLineReflectionPoint, Complex.sub_re,
        Complex.one_re, Complex.conj_re]
      linarith
    · simp [criticalLineReflectionPoint]
  simp [primeCoShiftReflectionOddGroundFun, href]

/-- **Terminal regular-boundary classification.**  Let an arbitrary source
module map linearly into all co-shift profiles.  If every boundary it produces
is square summable, then the reflection-odd profile is a boundary exactly on
the critical line.  Domain size, finite presentation, and the choice of
differential do not matter.  Any surviving PCS differential must therefore
have a genuinely non-`ℓ²` image. -/
theorem primeCoShiftReflectionOddGroundFun_mem_regularBoundary_iff
    {A : Type*} [AddCommGroup A] [Module ℂ A]
    (d0 : A →ₗ[ℂ] (ℕ+ → ℂ))
    (hregular : LinearMap.range d0 ≤
      LinearMap.range primeCoShiftSequenceInclusion)
    (s : ℂ) :
    primeCoShiftReflectionOddGroundFun s ∈ LinearMap.range d0 ↔
      s.re = 1 / 2 := by
  constructor
  · intro hboundary
    obtain ⟨x, hx⟩ := hregular hboundary
    apply (memℓp_primeCoShiftReflectionOddGroundFun_iff s).mp
    rw [← hx]
    exact x.property
  · intro hline
    rw [primeCoShiftReflectionOddGroundFun_eq_zero_of_re_eq_half hline]
    exact Submodule.zero_mem _

/-- Global vanishing of the singular reflection-odd class on the Xi divisor. -/
def XiReflectionOddPrimeCoShiftClassVanishes : Prop :=
  ∀ rho : ℂ, xi rho = 0 → primeCoShiftReflectionOddClass rho = 0

/-- Global singular co-shift class vanishing is exactly RH. -/
theorem xiReflectionOddPrimeCoShiftClassVanishes_iff_riemannHypothesis :
    XiReflectionOddPrimeCoShiftClassVanishes ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  simp only [XiReflectionOddPrimeCoShiftClassVanishes,
    primeCoShiftReflectionOddClass_eq_zero_iff]

/-- Failure of RH is detected by a nonzero singular co-shift class at an
actual Xi zero. -/
theorem
    exists_xiReflectionOddPrimeCoShiftClass_ne_zero_iff_not_riemannHypothesis :
    (∃ rho : ℂ,
      xi rho = 0 ∧ primeCoShiftReflectionOddClass rho ≠ 0) ↔
      ¬ RiemannHypothesis := by
  constructor
  · rintro ⟨rho, hrho, hclass⟩ hRH
    have hvanish : XiReflectionOddPrimeCoShiftClassVanishes :=
      xiReflectionOddPrimeCoShiftClassVanishes_iff_riemannHypothesis.mpr hRH
    exact hclass (hvanish rho hrho)
  · intro hnot
    have hfail : ¬ XiReflectionOddPrimeCoShiftClassVanishes := by
      exact hnot ∘
        xiReflectionOddPrimeCoShiftClassVanishes_iff_riemannHypothesis.mp
    rw [XiReflectionOddPrimeCoShiftClassVanishes] at hfail
    obtain ⟨rho, hlocal⟩ := Classical.not_forall.mp hfail
    have hrho : xi rho = 0 := by
      by_contra hne
      exact hlocal (fun hzero => False.elim (hne hzero))
    have hclass : primeCoShiftReflectionOddClass rho ≠ 0 := by
      intro hzero
      exact hlocal (fun _ => hzero)
    exact ⟨rho, hrho, hclass⟩

end

end RHTower.PrimeCoShift

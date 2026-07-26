import GaloisForLFunctions.HTGeometry.AbstractSpectralGraded
import GaloisForLFunctions.HTGeometry.AbstractSpectralDefect
import GaloisForLFunctions.RHTower.XiPoissonLineBoundRH
import GaloisForLFunctions.RHTower.XiSpectralFamily
import GaloisForLFunctions.RHTower.XiHeatShellMinimum
import GaloisForLFunctions.RHTower.XiDivisorSupportedMetric

/-!
# The Xi divisor as an abstract spectral family

The Poisson family of the Xi divisor satisfies the index-free admissibility interface, so the
rigidity theorem for abstract spectral families applies to it verbatim and returns the Riemann
Hypothesis.  Nothing about zeta enters the argument: the input is a countable set of points in the
right half-plane with heights bounded below, displacements below one half, summable real-time
weight, finite shells and a conjugating involution, and the output is that the points are real.

The graded form gives the same statement with an exponent: a bound `exp (lam |x|)` for the trace on
one vertical line bounds every displacement by `lam`, so on the Xi divisor it is a zero-free strip
of half-width `lam` around the critical line.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The Poisson family of the Xi divisor as an abstract spectral family.  No transport is needed:
`RHTower.SpectralFamily` *is* `HTGeometry.AbstractSpectralFamily XiZeroCopy`. -/
def xiPoissonAbstract : HTGeometry.AbstractSpectralFamily XiZeroCopy :=
  xiPoissonFamily xiPoissonBottomHeight_pos

theorem xiPoissonAbstract_pt (q : XiZeroCopy) : xiPoissonAbstract.pt q = xiPoissonPoint q := rfl

theorem xiPoissonAbstract_traceC (τ : ℂ) : xiPoissonAbstract.traceC τ = xiPoissonTraceC τ := rfl

/-- Vanishing displacement in the Poisson coordinate is the critical line. -/
theorem xiSpectralPoint_real_of_xiPoissonPoint_im_eq_zero
    (h : ∀ q : XiZeroCopy, (xiPoissonPoint q).im = 0) (q : XiZeroCopy) :
    ∃ r : ℝ, xiSpectralPoint q = (r : ℂ) := by
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  have him : (xiSpectralPoint q).im = 0 := by
    have hq := h q
    rw [xiPoissonPoint] at hq
    split_ifs at hq with hc
    · exact hq
    · rw [Complex.neg_im, neg_eq_zero] at hq
      exact hq
  conv_lhs => rw [← Complex.re_add_im (xiSpectralPoint q)]
  rw [him]
  simp

/-- **The Riemann Hypothesis from index-free spectral rigidity.**  The Xi divisor is one admissible
family among others; the vertical-line bound forces its points to be real for reasons that make no
reference to zeta. -/
theorem riemannHypothesis_of_abstract_line_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖xiPoissonAbstract.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    RiemannHypothesis := by
  have hall := xiPoissonAbstract.im_eq_zero_of_line_bound_all hσ hline
  exact riemannHypothesis_of_xiSpectralPoint_real
    (xiSpectralPoint_real_of_xiPoissonPoint_im_eq_zero hall)

/-- **The graded criterion on the Xi divisor.**  A growth exponent `lam` for the Poisson trace on one
vertical line is a zero-free strip: every zero has `|Re rho - 1/2| <= lam`. -/
theorem abs_re_sub_half_le_of_abstract_line_growth {σ C lam : ℝ} (hσ : 0 < σ) (hlam : 0 ≤ lam)
    (hline : ∀ x : ℝ,
      ‖xiPoissonAbstract.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C * Real.exp (lam * |x|))
    (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ lam := by
  have hall := xiPoissonAbstract.abs_im_le_of_line_growth_all hσ hlam hline q
  rw [xiPoissonAbstract_pt, xiPoissonPoint] at hall
  split_ifs at hall with hc
  · exact hall
  · rwa [Complex.neg_im, abs_neg] at hall

end

end RHTower

namespace RHTower

noncomputable section

theorem xiPoissonAbstract_defect (σ : ℝ) :
    xiPoissonAbstract.defect σ = xiPoissonTraceReal σ - (xiPoissonTraceC (σ : ℂ)).re := rfl

theorem xiPoissonPoint_im_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis)
    (q : XiZeroCopy) : (xiPoissonPoint q).im = 0 := by
  obtain ⟨σ, C, hσ, hline⟩ := riemannHypothesis_iff_exists_xiPoissonTrace_line_bound.mp hRH
  exact xiPoissonAbstract.im_eq_zero_of_line_bound_all hσ hline q

/-- **The defect criterion for the Riemann Hypothesis.**  For any real time `σ ∈ (0, 4π]`, RH is
equivalent to the single scalar equation `xiPoissonTraceReal σ = Re (xiPoissonTraceC σ)`: the
Poisson trace of the Xi divisor attains its own majorant at one point of the positive real axis. -/
theorem riemannHypothesis_iff_xiPoissonDefect_eq_zero {σ : ℝ} (hσ : 0 < σ)
    (hle : σ ≤ 4 * Real.pi) :
    RiemannHypothesis ↔ xiPoissonTraceReal σ = (xiPoissonTraceC (σ : ℂ)).re := by
  have hkey : (xiPoissonTraceReal σ = (xiPoissonTraceC (σ : ℂ)).re) ↔
      xiPoissonAbstract.defect σ = 0 := by
    rw [xiPoissonAbstract_defect, sub_eq_zero]
  rw [hkey]
  constructor
  · intro hRH
    exact xiPoissonAbstract.defect_eq_zero_of_im_eq_zero hσ
      (fun q => xiPoissonPoint_im_eq_zero_of_riemannHypothesis hRH q)
  · intro h
    exact riemannHypothesis_of_xiSpectralPoint_real
      (xiSpectralPoint_real_of_xiPoissonPoint_im_eq_zero
        (xiPoissonAbstract.im_eq_zero_of_defect_eq_zero hσ hle h))

end

end RHTower

namespace RHTower

noncomputable section

theorem sq_im_xiPoissonPoint_eq (q : XiZeroCopy) :
    (xiPoissonPoint q).im ^ 2 = (xiSpectralPoint q).im ^ 2 := by
  rw [xiPoissonPoint]
  split_ifs with hc
  · rfl
  · rw [Complex.neg_im]; ring

/-- **A defect bound is an explicit zero-free region.**  Since `(xiSpectralPoint q).im = 1/2 - Re ρ`,
an upper bound `M` for the defect `xiPoissonTraceReal σ - Re (xiPoissonTraceC σ)` at one real time
`σ ∈ (0, 2π]` bounds the distance of every zero from the critical line by
`(π/σ) sqrt(M/2) exp(σ |Im ρ| / 2)`. -/
theorem sq_im_xiSpectralPoint_le_of_defect_le {σ M : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 2 * Real.pi)
    (h : xiPoissonTraceReal σ - (xiPoissonTraceC (σ : ℂ)).re ≤ M) (q : XiZeroCopy) :
    (xiSpectralPoint q).im ^ 2 ≤
      Real.pi ^ 2 / (2 * σ ^ 2) * M * Real.exp (σ * (xiPoissonPoint q).re) := by
  have hd : xiPoissonAbstract.defect σ ≤ M := by rw [xiPoissonAbstract_defect]; exact h
  have hb := xiPoissonAbstract.sq_im_le_of_defect_le hσ hσ' hd q
  rw [xiPoissonAbstract_pt, sq_im_xiPoissonPoint_eq] at hb
  exact hb

end

end RHTower

namespace RHTower

noncomputable section

/-- The Poisson displacement energy of the Xi divisor: the second moment of the distance of the
zeros from the critical line, weighted by `exp (-σ |Im ρ|)`. -/
theorem xiPoissonAbstract_energy (σ : ℝ) :
    xiPoissonAbstract.energy σ = ∑' q : XiZeroCopy,
      Real.exp (-(σ * (xiPoissonPoint q).re)) * (xiSpectralPoint q).im ^ 2 := by
  rw [HTGeometry.AbstractSpectralFamily.energy]
  refine tsum_congr fun q => ?_
  rw [xiPoissonAbstract_pt, sq_im_xiPoissonPoint_eq]
  rfl

/-- **The energy criterion for the Riemann Hypothesis.**  For any real time `σ ∈ (0, 2π]`, RH is the
vanishing of the weighted second moment of the distance of the zeros from the critical line. -/
theorem riemannHypothesis_iff_xiPoissonEnergy_eq_zero {σ : ℝ} (hσ : 0 < σ)
    (hσ' : σ ≤ 2 * Real.pi) :
    RiemannHypothesis ↔ xiPoissonAbstract.energy σ = 0 := by
  constructor
  · intro hRH
    exact (xiPoissonAbstract.im_eq_zero_iff_energy_eq_zero hσ hσ').mp
      (fun q => xiPoissonPoint_im_eq_zero_of_riemannHypothesis hRH q)
  · intro h
    exact riemannHypothesis_of_xiSpectralPoint_real
      (xiSpectralPoint_real_of_xiPoissonPoint_im_eq_zero
        ((xiPoissonAbstract.im_eq_zero_iff_energy_eq_zero hσ hσ').mpr h))

end

end RHTower

namespace RHTower

noncomputable section

/-- **RH as a single scalar inequality.**  The reverse inequality
`Re (xiPoissonTraceC σ) ≤ xiPoissonTraceReal σ` is unconditional, so RH is exactly the assertion that
the Poisson trace of the Xi divisor is not smaller than its own majorant at one real time. -/
theorem riemannHypothesis_iff_xiPoissonTraceReal_le {σ : ℝ} (hσ : 0 < σ)
    (hle : σ ≤ 4 * Real.pi) :
    RiemannHypothesis ↔ xiPoissonTraceReal σ ≤ (xiPoissonTraceC (σ : ℂ)).re := by
  have hiff := xiPoissonAbstract.im_eq_zero_iff_traceReal_le hσ hle
  constructor
  · intro hRH
    exact hiff.mp fun q => xiPoissonPoint_im_eq_zero_of_riemannHypothesis hRH q
  · intro h
    exact riemannHypothesis_of_xiSpectralPoint_real
      (xiSpectralPoint_real_of_xiPoissonPoint_im_eq_zero (hiff.mpr h))

/-- **Zero density from an energy bound.**  If the Poisson energy at time `σ` is at most `M`, then a
finite set of zeros with `|Im ρ| ≤ T` and `|Re ρ - 1/2| ≥ η` has at most `M exp(σ T) / η²`
elements. -/
theorem card_le_of_xiPoissonEnergy_le {σ M T η : ℝ} (hσ : 0 < σ) (hη : 0 < η)
    (h : xiPoissonAbstract.energy σ ≤ M) (s : Finset XiZeroCopy)
    (hs : ∀ q ∈ s, (xiPoissonPoint q).re ≤ T ∧ η ≤ |(xiSpectralPoint q).im|) :
    (s.card : ℝ) * (η ^ 2 * Real.exp (-(σ * T))) ≤ M := by
  refine xiPoissonAbstract.card_le_of_energy_le hσ hη h s fun q hq => ?_
  obtain ⟨hT, hη'⟩ := hs q hq
  refine ⟨hT, ?_⟩
  have habs : |(xiPoissonPoint q).im| = |(xiSpectralPoint q).im| := by
    rw [xiPoissonPoint]
    split_ifs with hc
    · rfl
    · rw [Complex.neg_im, abs_neg]
  rw [xiPoissonAbstract_pt, habs]
  exact hη'

end

end RHTower

namespace RHTower

noncomputable section

/-- **The unconditional window for the Xi divisor.**  With no hypothesis on the zeros,
`Re (xiPoissonTraceC σ)` lies within a relative `σ²/8` of `xiPoissonTraceReal σ`; the Riemann
Hypothesis is exactly the statement that the two are equal. -/
theorem xiPoissonTraceReal_mul_le_re_xiPoissonTraceC {σ : ℝ} (hσ : 0 < σ) :
    (1 - σ ^ 2 / 8) * xiPoissonTraceReal σ ≤ (xiPoissonTraceC (σ : ℂ)).re :=
  xiPoissonAbstract.traceReal_mul_le_re_traceC hσ

end

end RHTower

namespace RHTower

noncomputable section

/-- **The functional-equation reflection is invisible in the Poisson coordinate.**  The map
`ρ ↦ 1 - ρ` negates the centred spectral point, and the Poisson point is that point folded into the
closed right half-plane, so the two copies of a reflection pair carry the *same* Poisson point.  The
Poisson coordinate is therefore the quotient of the Xi divisor by the functional equation. -/
theorem xiPoissonPoint_reflect (q : XiZeroCopy) :
    xiPoissonPoint (xiZeroCopyReflectEquiv q) = xiPoissonPoint q := by
  have hpos : 0 < (xiPoissonPoint q).re :=
    lt_of_lt_of_le xiPoissonBottomHeight_pos (xiPoissonBottomCopy_min q)
  have hne : (xiSpectralPoint q).re ≠ 0 := by
    intro h
    have hz : (xiPoissonPoint q).re = 0 := by
      simp only [xiPoissonPoint]
      split_ifs <;> simp [h]
    linarith
  simp only [xiPoissonPoint, xiSpectralPoint_reflect, Complex.neg_re]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [if_pos (by linarith : (0:ℝ) ≤ -(xiSpectralPoint q).re), if_neg (not_le.mpr hlt)]
  · rw [if_neg (not_le.mpr (by linarith : -(xiSpectralPoint q).re < 0)),
      if_pos (by linarith : (0:ℝ) ≤ (xiSpectralPoint q).re), neg_neg]

end

end RHTower

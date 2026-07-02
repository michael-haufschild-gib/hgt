/-
# Real-pair exposed one-sided point: β₁ is the witness, one clause remains

The audited 07-answer (basilica refutation: strictly one-sided points are `μ`-null at
`c = −1`) closes every measure-based selection of an exposed one-sided point.  For REAL
parameter pairs a direct pointwise witness survives: with `β₂ < β₁`, the β-fixed point
of `c₁`

* lies off `K_{c₂}` — the real slice `K_{c₂} ∩ ℝ = [−β₂, β₂]` (`RealSliceDynamics`), and
* is visible from infinity — the real ray `(β₁, ∞)` is an unbounded preconnected carrier
  inside the joint complement,

so `ExposedOneSided (c₁, c₂)` reduces to the SINGLE remaining clause
`OneSidedAt c₁ β₁` — one local access at one repelling fixed point — a sharp scope cut
of the ray-landing epic for the real-pair class.

* `betaFixed_lt_betaFixed` — `β` is strictly decreasing on the real slice.
* `realPair_exposedOneSided_of_oneSidedAt_beta` — the reduction described above.
* `q62_phiMero_realPair_of_oneSidedAt_beta` — capstone wiring: for real
  `−2 ≤ c₁ < c₂ ≤ 1/4`, both nonexceptional, `OneSidedAt c₁ β₁` plus smooth-piece
  rigidity (both orientations) give `NoRelation` for the Böttcher pair.

Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.Q62BothConnectedExposed
import GaloisForLFunctions.Bottcher.RealSliceDynamics

open Set Metric Bornology

namespace Bottcher

/-- `β` is strictly decreasing on the real slice. -/
theorem betaFixed_lt_betaFixed {c₁ c₂ : ℝ} (hlt : c₁ < c₂) (hc₂4 : c₂ ≤ 1 / 4) :
    betaFixed c₂ < betaFixed c₁ := by
  unfold betaFixed
  have h : Real.sqrt (1 - 4 * c₂) < Real.sqrt (1 - 4 * c₁) :=
    Real.sqrt_lt_sqrt (by linarith) (by linarith)
  linarith

/-- **Real-pair exposed one-sided point.**  For real parameters with `β₂ < β₁`, the β-fixed
point of `c₁` is off `K_{c₂}` (real slice `K_{c₂} ∩ ℝ = [−β₂, β₂]`) and visible from infinity
along the real ray `(β₁, ∞)`; one-sidedness at the single point `β₁` is the only remaining
input. -/
theorem realPair_exposedOneSided_of_oneSidedAt_beta {c₁ c₂ : ℝ}
    (hc₁4 : c₁ ≤ 1 / 4) (hc₂4 : c₂ ≤ 1 / 4) (hβ : betaFixed c₂ < betaFixed c₁)
    (hos : OneSidedAt (c₁ : ℂ) (betaFixed c₁ : ℂ)) :
    ExposedOneSided (c₁ : ℂ) (c₂ : ℂ) := by
  refine ⟨(betaFixed c₁ : ℂ), hos, not_mem_filledJulia_of_betaFixed_lt hc₂4 hβ, ?_⟩
  refine ⟨(fun t : ℝ => (t : ℂ)) '' Ioi (betaFixed c₁), ?_, ?_, ?_, ?_⟩
  · exact isPreconnected_Ioi.image _ Complex.continuous_ofReal.continuousOn
  · intro hbd
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbd
    set t : ℝ := max (betaFixed c₁ + 1) (C + 1) with htdef
    have htmem : (t : ℂ) ∈ (fun s : ℝ => (s : ℂ)) '' Ioi (betaFixed c₁) := by
      refine ⟨t, ?_, rfl⟩
      have h1 : betaFixed c₁ + 1 ≤ t := le_max_left _ _
      exact mem_Ioi.mpr (by linarith)
    have hnorm := hC _ htmem
    rw [Complex.norm_real, Real.norm_eq_abs] at hnorm
    have hCt : C + 1 ≤ t := le_max_right _ _
    have hta : t ≤ C := (le_abs_self t).trans hnorm
    linarith
  · rintro _ ⟨t, ht, rfl⟩
    simp only [mem_compl_iff, mem_union, not_or]
    exact ⟨not_mem_filledJulia_of_betaFixed_lt hc₁4 ht,
      not_mem_filledJulia_of_betaFixed_lt hc₂4 (hβ.trans ht)⟩
  · rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((betaFixed c₁ + ε / 2 : ℝ) : ℂ),
      ⟨betaFixed c₁ + ε / 2, mem_Ioi.mpr (by linarith), rfl⟩, ?_⟩
    have h1 : (betaFixed c₁ : ℂ) - ((betaFixed c₁ + ε / 2 : ℝ) : ℂ) = ((-(ε / 2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [dist_eq_norm, h1, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
    linarith

/-- **Real-pair both-connected capstone (conditional).**  For real `−2 ≤ c₁ < c₂ ≤ 1/4`, both
nonexceptional, the whole both-connected chain fires from `OneSidedAt c₁ β₁` (the single
remaining analytic clause of the exposure input) plus smooth-piece rigidity (both
orientations): `NoRelation` for the Böttcher pair. -/
theorem q62_phiMero_realPair_of_oneSidedAt_beta
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℝ} (hlt : c₁ < c₂) (hc₁2 : -2 ≤ c₁) (hc₂4 : c₂ ≤ 1 / 4)
    (hc₁0 : (c₁ : ℂ) ≠ 0) (hc₁m2 : (c₁ : ℂ) ≠ -2) (hc₂0 : (c₂ : ℂ) ≠ 0) (hc₂m2 : (c₂ : ℂ) ≠ -2)
    (hU₁ : U ⊆ escapeOpen (c₁ : ℂ)) (hU₂ : U ⊆ escapeOpen (c₂ : ℂ))
    (hos : OneSidedAt (c₁ : ℂ) (betaFixed c₁ : ℂ))
    (hrig12 : SmoothPieceRigidity (c₁ : ℂ) (c₂ : ℂ))
    (hrig21 : SmoothPieceRigidity (c₂ : ℂ) (c₁ : ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero (c₁ : ℂ) hU₁) (phiMero (c₂ : ℂ) hU₂) := by
  have hc₁4 : c₁ ≤ 1 / 4 := hlt.le.trans hc₂4
  have hc₂2 : -2 ≤ c₂ := hc₁2.trans hlt.le
  exact q62_phiMero_bothconnected_of_op6 hUo hUc hUne hUinf
    (real_mem_mandelbrot hc₁2 hc₁4) (real_mem_mandelbrot hc₂2 hc₂4)
    hc₁0 hc₁m2 hc₂0 hc₂m2 hU₁ hU₂
    (Or.inl (realPair_exposedOneSided_of_oneSidedAt_beta hc₁4 hc₂4
      (betaFixed_lt_betaFixed hlt hc₂4) hos))
    hrig12 hrig21

end Bottcher

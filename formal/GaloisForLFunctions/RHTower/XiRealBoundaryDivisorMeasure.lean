import GaloisForLFunctions.RHTower.RealBoundaryDivisorLimit
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.HTGeometry.WeightedAtomHilbert
import GaloisForLFunctions.RHTower.SlabMassSquareCertificate

/-!
# The canonical positive real-boundary divisor measure of `Ξ`

`XiC z = ξ(½ + i z)` is entire and Schwarz-real (`RHTower.XiC_conj`), so the general boundary
identity of `RHTower.RealBoundaryDivisorLimit` applies verbatim.  Two things are established here.

**The measure.**  `tendsto_xiBoundaryDensity_setIntegral` is formula `(6)`: the boundary density

```text
ν_ε(t) = -(1/π) Im (Ξ'/Ξ)(t + iε)
```

converges, as `ε ↓ 0` and against every test function supported in a real interval, to

```text
ν_Ξ = ∑_{γ ∈ ℝ, Ξ(γ) = 0} ord_γ(Ξ) · δ_γ.
```

The definition of `ν_ε` refers only to the theta-source function and its logarithmic derivative;
the zeros are an output, never an input.  Nonreal conjugate pairs are visible in `Ξ'/Ξ` but produce
no jump across the real axis, so they contribute no atom.

**The Hilbert space.**  Formula `(7)`.  The atom weights `ord_γ(Ξ)` are positive integers
(`one_le_xiRealMult`), so the weighted form `‖c‖²_Ξ = ∑_γ m_γ |c_γ|²` is realised without any
weighted-measure machinery, by giving each real zero `m_γ` atoms:
`XiBoundaryHilbert = ℓ²(Σ γ, Fin m_γ)`.  It is complete and positive by construction, its norm on
finitely supported data is exactly `(7)` (`norm_xiOfFinsupp_sq`), and real translation acts on the
atom at `γ` by the character `exp (-i a γ)`, hence unitarily and as a one-parameter group
(`xiBoundaryTranslation_zero`, `xiBoundaryTranslation_add`).  Multiplicity enters as an atom count,
so the nilpotent local jets are never inserted into the space.

The remaining assertion of the source card — that the analytic Xi defect is *exhausted* by `ν_Ξ` —
is equivalent to RH and is deliberately not proved here.
-/

noncomputable section

open Complex Filter Topology Metric Set MeasureTheory ProbabilityTheory
open RHTower.RealBoundaryDivisor GaloisForLFunctions.HTGeometry

namespace RHTower.XiRealBoundary

open RHTower

/-- The centered completed Xi function does not vanish on the lower imaginary ray. -/
theorem XiC_neg_I_ne_zero : XiC (-Complex.I) ≠ 0 := by
  rw [XiC]
  refine xi_ne_zero_of_one_le_re ?_
  have h : (1 : ℂ) / 2 + (-Complex.I) * Complex.I = 3 / 2 := by
    rw [neg_mul, Complex.I_mul_I]
    ring
  rw [h]
  norm_num

/-- `XiC` never vanishes identically near a point. -/
theorem not_XiC_eventuallyEq_zero (z : ℂ) : ¬ (XiC =ᶠ[𝓝 z] 0) := by
  intro h
  have hXian : AnalyticOnNhd ℂ XiC Set.univ := fun w _ =>
    (XiC_differentiable.differentiableOn.analyticOnNhd isOpen_univ) w (Set.mem_univ w)
  have hzero : Set.EqOn XiC 0 Set.univ :=
    hXian.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) h
  exact XiC_neg_I_ne_zero (hzero (Set.mem_univ _))

/-- `XiC` is not identically zero on any ball. -/
theorem exists_XiC_ne_zero_in_ball (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ z₀ ∈ ball c R, XiC z₀ ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  refine not_XiC_eventuallyEq_zero c ?_
  exact Filter.eventually_iff_exists_mem.mpr
    ⟨ball c R, isOpen_ball.mem_nhds (mem_ball_self hR), fun u hu => hcon u hu⟩

/-- **The canonical positive real-boundary divisor measure of `Ξ`.**  The boundary density
`-(1/π)·Im (Ξ'/Ξ)(t + iε)` converges, as `ε ↓ 0`, against every test function supported in a real
interval, to the positive atomic measure carried by the *real* zeros of `Ξ`, each weighted by its
analytic multiplicity.  The density uses only the theta-source function and its logarithmic
derivative: no list of zeros is assumed. -/
theorem tendsto_xiBoundaryDensity_setIntegral {c r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ t : ℝ, t ∉ Ioo (c - r) (c + r) → φ t = 0) :
    ∃ Γ : Finset ℝ,
      (∀ γ : ℝ, γ ∈ Γ ↔ ((γ : ℂ) ∈ ball (c : ℂ) R ∧ XiC (γ : ℂ) = 0)) ∧
      Tendsto (fun ε : ℝ => ∫ t in Icc (c - r) (c + r), φ t * boundaryDensity XiC ε t)
        (𝓝[>] 0) (𝓝 (∑ γ ∈ Γ, ((analyticOrderAt XiC (γ : ℂ)).toNat : ℝ) * φ γ)) := by
  obtain ⟨z₀, hz₀, hXz₀⟩ := exists_XiC_ne_zero_in_ball (c : ℂ) (lt_of_le_of_lt hr hrR)
  exact tendsto_boundaryDensity_setIntegral XiC_differentiable XiC_conj hr hrR hz₀ hXz₀ hφ hsupp

/-! ## The positive semisimple boundary Hilbert space -/

/-- A real zero of the centered completed Xi function. -/
def XiRealZero : Type := {γ : ℝ // XiC ((γ : ℝ) : ℂ) = 0}

/-- The analytic multiplicity carried by a real Xi zero: the positive weight of its boundary
atom. -/
def xiRealMult (γ : XiRealZero) : ℕ := (analyticOrderAt XiC ((γ.1 : ℝ) : ℂ)).toNat

/-- **Every boundary atom weight is positive.** -/
theorem one_le_xiRealMult (γ : XiRealZero) : 1 ≤ xiRealMult γ := by
  have han : AnalyticAt ℂ XiC ((γ.1 : ℝ) : ℂ) :=
    (XiC_differentiable.differentiableOn.analyticOnNhd isOpen_univ) _ (Set.mem_univ _)
  have hne0 : analyticOrderAt XiC ((γ.1 : ℝ) : ℂ) ≠ 0 := han.analyticOrderAt_ne_zero.mpr γ.2
  have hnetop : analyticOrderAt XiC ((γ.1 : ℝ) : ℂ) ≠ ⊤ := fun h =>
    not_XiC_eventuallyEq_zero _ (analyticOrderAt_eq_top.mp h)
  have hpos : 0 < (analyticOrderAt XiC ((γ.1 : ℝ) : ℂ)).toNat := by
    rcases Nat.eq_zero_or_pos (analyticOrderAt XiC ((γ.1 : ℝ) : ℂ)).toNat with h | h
    · exact absurd (ENat.toNat_eq_zero.mp h) (by tauto)
    · exact h
  exact hpos

/-- The atoms of the Xi real-boundary divisor: one copy of each real zero per unit of its
analytic multiplicity.  Multiplicity is carried as an atom count, so the local jets never enter
the Hilbert space. -/
def XiBoundaryAtom : Type := Σ γ : XiRealZero, Fin (xiRealMult γ)

/-- **The positive semisimple Hilbert space of the Xi real-boundary divisor.** -/
abbrev XiBoundaryHilbert : Type := lp (fun _ : XiBoundaryAtom => ℂ) 2

/-- Finitely supported real-zero data, spread over the multiplicity copies. -/
def xiOfFinsupp (c : XiRealZero →₀ ℂ) : XiBoundaryHilbert :=
  ⟨fun q => c q.1, memℓp_two_of_eq_zero_outside
    (s := c.support.sigma (fun _ => Finset.univ)) (by
      intro q hq
      by_contra hcon
      exact hq (Finset.mem_sigma.mpr
        ⟨Finsupp.mem_support_iff.mpr hcon, Finset.mem_univ _⟩))⟩

@[simp] theorem xiOfFinsupp_apply (c : XiRealZero →₀ ℂ) (q : XiBoundaryAtom) :
    xiOfFinsupp c q = c q.1 := rfl

/-- **The boundary norm is the divisor-weighted `ℓ²` form.**  This is formula `(7)`: the norm of
finitely supported real-zero data is `∑_γ m_γ |c_γ|²`, with `m_γ` the positive analytic
multiplicity of the real zero `γ`. -/
theorem norm_xiOfFinsupp_sq (c : XiRealZero →₀ ℂ) :
    ‖xiOfFinsupp c‖ ^ 2 = ∑ γ ∈ c.support, (xiRealMult γ : ℝ) * ‖c γ‖ ^ 2 := by
  rw [lp_two_norm_sq_eq_tsum]
  exact tsum_sigma_fiberConst xiRealMult (fun γ => c γ) c.support
    (fun a ha => Finsupp.notMem_support_iff.mp ha)

/-- The boundary character of a real translation: the atom at `γ` carries `exp (-i a γ)`. -/
def xiTranslationPhase (a : ℝ) (q : XiBoundaryAtom) : ℂ :=
  Complex.exp (((-(a * q.1.1) : ℝ) : ℂ) * I)

theorem norm_xiTranslationPhase (a : ℝ) (q : XiBoundaryAtom) :
    ‖xiTranslationPhase a q‖ = 1 := by
  rw [xiTranslationPhase, Complex.norm_exp_ofReal_mul_I]

/-- **Real translation acts unitarily on the boundary Hilbert space**, by the character
`exp (-i a γ)` on the atom at `γ`. -/
def xiBoundaryTranslation (a : ℝ) : XiBoundaryHilbert ≃ₗᵢ[ℂ] XiBoundaryHilbert :=
  lpPhaseUnitary (xiTranslationPhase a) (norm_xiTranslationPhase a)

@[simp] theorem xiBoundaryTranslation_apply (a : ℝ) (f : XiBoundaryHilbert)
    (q : XiBoundaryAtom) :
    xiBoundaryTranslation a f q = Complex.exp (((-(a * q.1.1) : ℝ) : ℂ) * I) * f q := rfl

theorem xiBoundaryTranslation_zero :
    xiBoundaryTranslation 0 = LinearIsometryEquiv.refl ℂ XiBoundaryHilbert := by
  refine LinearIsometryEquiv.ext (fun f => ?_)
  refine lp.ext (funext fun q => ?_)
  simp

theorem xiBoundaryTranslation_add (a b : ℝ) :
    xiBoundaryTranslation (a + b)
      = (xiBoundaryTranslation b).trans (xiBoundaryTranslation a) := by
  refine LinearIsometryEquiv.ext (fun f => ?_)
  refine lp.ext (funext fun q => ?_)
  simp only [xiBoundaryTranslation_apply, LinearIsometryEquiv.trans_apply, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The boundary translation group is unitary and norm preserving.** -/
theorem norm_xiBoundaryTranslation (a : ℝ) (f : XiBoundaryHilbert) :
    ‖xiBoundaryTranslation a f‖ = ‖f‖ := (xiBoundaryTranslation a).norm_map f

end RHTower.XiRealBoundary

namespace RHTower.XiRealBoundary

open RHTower

/-! ## The exact limitation -/

/-- Statement `(8)`: the analytic Xi defect is exhausted by the real-boundary divisor measure,
i.e. every zero of `Ξ` is one of its boundary atoms. -/
def XiBoundaryExhaustsDivisor : Prop := ∀ z : ℂ, XiC z = 0 → z.im = 0

/-- **The exact limitation, at the source.**  Exhaustion of the analytic Xi divisor by the
positive real-boundary measure `ν_Ξ` is *exactly* the Riemann Hypothesis.  The construction of
`ν_Ξ` is unconditional; the exhaustion assertion is not part of it. -/
theorem xiBoundaryExhaustsDivisor_iff_riemannHypothesis :
    XiBoundaryExhaustsDivisor ↔ RiemannHypothesis :=
  RHTower.SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero.symm

end RHTower.XiRealBoundary

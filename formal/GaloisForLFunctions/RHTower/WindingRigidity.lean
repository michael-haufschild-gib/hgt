/-
Polar factorization of the archimedean envelope along the critical line, and the winding
rigidity of the finite carrier.

The envelope's logarithmic derivative along the line is the winding datum, so the envelope
factorizes exactly: basepoint value, times the real exponential of the winding-modulus
primitive, times the unimodular exponential of the winding-phase primitive.  Reality of the
completed carrier on the line then yields an unconditional identity — the finite carrier
times the envelope's polar data is the real value of the completed carrier — so on every
segment where the completed carrier keeps one sign, the carrier's phase is the exact
anti-rotation of the winding phase.  The winding rate carries the explicit floor
`(log(u/2π) − 4/u² − π/u)/2`, so the phase lock advances at least at that rate: a sign
change is the only mechanism that can interrupt it.
-/
import GaloisForLFunctions.RHTower.WindingFloor
import GaloisForLFunctions.RHTower.SeamSignTransport

open Complex Metric MeasureTheory

namespace RHTower

theorem continuous_archWinding : Continuous archWinding := by
  rw [continuous_iff_continuousAt]
  intro u
  exact (hasDerivAt_archWinding u).continuousAt

/-- The winding modulus: the primitive of the envelope's modulus rate from a basepoint. -/
noncomputable def windingModulus (γ u : ℝ) : ℝ := ∫ t in γ..u, -(archWinding t).im

theorem hasDerivAt_windingModulus (γ u : ℝ) :
    HasDerivAt (windingModulus γ) (-(archWinding u).im) u := by
  show HasDerivAt (fun u : ℝ => ∫ t in γ..u, -(archWinding t).im) _ u
  exact (((Complex.continuous_im.comp continuous_archWinding).neg).integral_hasStrictDerivAt
    γ u).hasDerivAt

/-- **Polar factorization of the envelope along the line**: the envelope is its basepoint
value times the exponential of the winding-modulus and winding-phase primitives. -/
theorem archFactor_line_polar (γ τ : ℝ) :
    archFactor (linePt τ) = archFactor (linePt γ) *
      Complex.exp (((windingModulus γ τ : ℝ) : ℂ) +
        Complex.I * ((windingPhase γ τ : ℝ) : ℂ)) := by
  set X : ℝ → ℂ := fun τ => ((windingModulus γ τ : ℝ) : ℂ) +
    Complex.I * ((windingPhase γ τ : ℝ) : ℂ) with hX_def
  have hXderiv : ∀ u : ℝ, HasDerivAt X
      (((-(archWinding u).im : ℝ) : ℂ) + Complex.I * ((windingRate u : ℝ) : ℂ)) u := by
    intro u
    exact ((hasDerivAt_windingModulus γ u).ofReal_comp).add
      (((hasDerivAt_windingPhase γ u).ofReal_comp).const_mul Complex.I)
  have hF : ∀ u : ℝ, HasDerivAt (fun τ : ℝ => archFactor (linePt τ) * Complex.exp (-X τ))
      0 u := by
    intro u
    have hE : HasDerivAt (fun τ : ℝ => Complex.exp (-X τ))
        (Complex.exp (-X u) * -(((-(archWinding u).im : ℝ) : ℂ) +
          Complex.I * ((windingRate u : ℝ) : ℂ))) u :=
      ((hXderiv u).neg).cexp
    have hprod := (hasDerivAt_archFactor_line u).mul hE
    have hval : archFactorDeriv (linePt u) * Complex.I * Complex.exp (-X u) +
        archFactor (linePt u) * (Complex.exp (-X u) *
          -(((-(archWinding u).im : ℝ) : ℂ) +
            Complex.I * ((windingRate u : ℝ) : ℂ))) = 0 := by
      rw [archFactorDeriv_eq_mul_archWinding u]
      have hwI : archWinding u * Complex.I =
          ((-(archWinding u).im : ℝ) : ℂ) +
            Complex.I * (((archWinding u).re : ℝ) : ℂ) := by
        push_cast
        linear_combination (-Complex.I) * Complex.re_add_im (archWinding u) +
          (((archWinding u).im : ℂ)) * Complex.I_sq
      have hrate : ((windingRate u : ℝ) : ℂ) = (((archWinding u).re : ℝ) : ℂ) := rfl
      rw [hrate]
      linear_combination (archFactor (linePt u) * Complex.exp (-X u)) * hwI
    exact hval ▸ hprod
  have hconst := is_const_of_deriv_eq_zero
    (fun u => (hF u).differentiableAt)
    (fun u => (hF u).deriv) τ γ
  have hXγ : X γ = 0 := by
    rw [hX_def]
    simp [windingModulus, windingPhase, intervalIntegral.integral_same]
  rw [hXγ, neg_zero, Complex.exp_zero, mul_one] at hconst
  have hexp_ne : Complex.exp (-X τ) ≠ 0 := Complex.exp_ne_zero _
  calc archFactor (linePt τ)
      = archFactor (linePt τ) * Complex.exp (-X τ) * Complex.exp (X τ) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = archFactor (linePt γ) * Complex.exp (X τ) := by rw [hconst]

/-- **The winding-rigidity identity** (unconditional): the finite carrier times the
envelope's polar data equals the real value of the completed carrier on the line. -/
theorem gN_line_winding_rigidity (N : ℕ) (γ τ : ℝ) :
    archFactor (linePt γ) *
      Complex.exp (((windingModulus γ τ : ℝ) : ℂ) +
        Complex.I * ((windingPhase γ τ : ℝ) : ℂ)) * gN N (linePt τ) =
      (((completedGN N (linePt τ)).re : ℝ) : ℂ) := by
  rw [← archFactor_line_polar γ τ]
  have him : (completedGN N (linePt τ)).im = 0 :=
    completedGN_im_eq_zero_on_line (by rw [linePt_re])
  show completedGN N (linePt τ) = _
  exact Complex.ext rfl (by simp [him])

/-- **Phase lock on sign-constant segments.**  Where the completed carrier keeps positive
sign on the line, the winding-rotated carrier `arch(γ)·e^{iΘ}·g_N` is a positive real: the
carrier's phase anti-rotates the winding phase exactly, at the winding rate's explicit
floor, until a sign change interrupts it. -/
theorem carrier_ray_of_sign_constant (N : ℕ) {γ a b : ℝ}
    (hpos : ∀ τ ∈ Set.Icc a b, 0 < (completedGN N (linePt τ)).re) :
    ∀ τ ∈ Set.Icc a b, ∃ r : ℝ, 0 < r ∧
      archFactor (linePt γ) *
        (Complex.exp (Complex.I * ((windingPhase γ τ : ℝ) : ℂ)) * gN N (linePt τ)) =
        (r : ℂ) := by
  intro τ hτ
  refine ⟨(completedGN N (linePt τ)).re * Real.exp (-(windingModulus γ τ)),
    mul_pos (hpos τ hτ) (Real.exp_pos _), ?_⟩
  have hid := gN_line_winding_rigidity N γ τ
  rw [Complex.exp_add] at hid
  rw [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
  have hMne : Complex.exp (((windingModulus γ τ : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  rw [Complex.exp_neg]
  field_simp
  linear_combination hid

end RHTower

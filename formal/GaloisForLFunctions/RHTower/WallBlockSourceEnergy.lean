import GaloisForLFunctions.RHTower.WallForcedProfileWindow
import GaloisForLFunctions.RHTower.WallBlockSliceProfile

/-!
# The energy of the block source

The source of the one-block equation is the angular transform of the profile, halved and rotated by
`−i/2`.  Its frequency energy is therefore `π/2` times the physical energy: the Plancherel factor
`2π` divided by four.  This is the card's `(12)` in the form the window estimate consumes, and it is
the only place the source's normalisation enters the constant.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- The block source is the angular transform of the profile, halved and rotated. -/
theorem blockSource_eq_angularTransform {g : ℝ → X} {m : ℝ}
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) (t : ℝ) :
    blockSource g m t = (-(Complex.I) / 2 : ℂ) • vectorAngularTransform g t := by
  rw [blockSource, vectorAngularTransform]
  congr 1
  have hext : (∫ L in Icc m (m + 1), Complex.exp (-(Complex.I) * (L : ℂ) * (t : ℂ)) • g L)
      = ∫ L : ℝ, Complex.exp (-(Complex.I) * (L : ℂ) * (t : ℂ)) • g L :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun L hL => by rw [hsupp L hL, smul_zero])
  rw [hext]
  refine integral_congr_ae (Filter.Eventually.of_forall fun L => ?_)
  have hcomm : -(Complex.I) * (L : ℂ) * (t : ℂ) = -(Complex.I) * (t : ℂ) * (L : ℂ) := by ring
  show Complex.exp (-(Complex.I) * (L : ℂ) * (t : ℂ)) • g L
      = Complex.exp (-(Complex.I) * (t : ℂ) * (L : ℂ)) • g L
  rw [hcomm]

omit [CompleteSpace X] in
theorem norm_blockSource {g : ℝ → X} {m : ℝ}
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) (t : ℝ) :
    ‖blockSource g m t‖ = (1 / 2) * ‖vectorAngularTransform g t‖ := by
  rw [blockSource_eq_angularTransform hsupp, norm_smul]
  congr 1
  rw [norm_div, norm_neg, Complex.norm_I]
  norm_num

/-- **`(12)` for the block source.**  Its frequency energy is `π/2` times the physical energy: the
Plancherel factor `2π` halved twice by the factor `−i/2`. -/
theorem integral_norm_sq_blockSource {g : ℝ → X} {m : ℝ}
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) :
    (∫ t : ℝ, ‖blockSource g m t‖ ^ 2) = (Real.pi / 2) * ∫ L : ℝ, ‖g L‖ ^ 2 := by
  have hg1 : Integrable g := integrable_zeroExtension hg2 hsupp
  have hpar := integral_norm_sq_vectorAngularTransform_eq hg1 hg2
  have hrw : (fun t : ℝ => ‖blockSource g m t‖ ^ 2)
      = fun t : ℝ => (1 / 4 : ℝ) * ‖vectorAngularTransform g t‖ ^ 2 := by
    funext t
    rw [norm_blockSource hsupp]
    ring
  rw [hrw, integral_const_mul, hpar]
  ring

end GaloisForLFunctions.RHTower

import GaloisForLFunctions.HTGeometry.HolomorphicBranch
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The holomorphic Gamma-ratio branch on the unit strip

The scalar factor of the Gamma frequency transport is the square root of `Γ(1+iz)/Γ(1-iz)` with the
branch equal to one at the origin.  On the strip `|Im z| < 1` the ratio is holomorphic and
nonvanishing — both arguments have real part in `(0,2)`, so neither Gamma factor meets a pole — and
the strip is convex, hence simply connected.  Therefore the branch exists, is holomorphic, and is
normalised at the origin.
-/

open Set Complex

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The open horizontal strip with imaginary part between two bounds. -/
def imStrip (a b : ℝ) : Set ℂ := {z : ℂ | a < z.im ∧ z.im < b}

theorem mem_imStrip {a b : ℝ} {z : ℂ} : z ∈ imStrip a b ↔ a < z.im ∧ z.im < b := Iff.rfl

theorem isOpen_imStrip (a b : ℝ) : IsOpen (imStrip a b) := by
  have : imStrip a b = Complex.im ⁻¹' (Ioo a b) := rfl
  rw [this]
  exact isOpen_Ioo.preimage Complex.continuous_im

theorem convex_imStrip (a b : ℝ) : Convex ℝ (imStrip a b) := by
  have hpre : imStrip a b = (Complex.imLm : ℂ →ₗ[ℝ] ℝ) ⁻¹' (Ioo a b) := rfl
  rw [hpre]
  exact (convex_Ioo a b).linear_preimage Complex.imLm

theorem zero_mem_imStrip : (0 : ℂ) ∈ imStrip (-1) 1 := by
  constructor <;> simp

theorem isSimplyConnected_imStrip (a b : ℝ) (h : a < b) : IsSimplyConnected (imStrip a b) := by
  refine isSimplyConnected_of_convex (convex_imStrip a b) ⟨((a + b) / 2 : ℝ) * Complex.I, ?_⟩
  constructor <;> simp <;> linarith

/-- The Gamma ratio of the frequency transport. -/
def gammaRatio (z : ℂ) : ℂ := Complex.Gamma (1 + Complex.I * z) / Complex.Gamma (1 - Complex.I * z)

theorem re_one_add_I_mul (z : ℂ) : (1 + Complex.I * z).re = 1 - z.im := by
  simp
  ring

theorem re_one_sub_I_mul (z : ℂ) : (1 - Complex.I * z).re = 1 + z.im := by
  simp

/-- On the unit strip neither Gamma argument meets a pole. -/
theorem gammaArg_ne_pole {z : ℂ} (hz : z ∈ imStrip (-1) 1) :
    (∀ m : ℕ, 1 + Complex.I * z ≠ -(m : ℂ)) ∧ ∀ m : ℕ, 1 - Complex.I * z ≠ -(m : ℂ) := by
  obtain ⟨h1, h2⟩ := hz
  constructor
  · intro m hcon
    have hre : (1 + Complex.I * z).re = -(m : ℝ) := by
      rw [hcon]
      simp
    rw [re_one_add_I_mul] at hre
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  · intro m hcon
    have hre : (1 - Complex.I * z).re = -(m : ℝ) := by
      rw [hcon]
      simp
    rw [re_one_sub_I_mul] at hre
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith

theorem differentiableOn_gammaRatio : DifferentiableOn ℂ gammaRatio (imStrip (-1) 1) := by
  intro z hz
  obtain ⟨hp1, hp2⟩ := gammaArg_ne_pole hz
  have hlin1 : DifferentiableAt ℂ (fun w : ℂ => 1 + Complex.I * w) z :=
    (differentiable_id.const_mul Complex.I).const_add 1 |>.differentiableAt
  have hlin2 : DifferentiableAt ℂ (fun w : ℂ => 1 - Complex.I * w) z :=
    (differentiable_const 1).sub (differentiable_id.const_mul Complex.I) |>.differentiableAt
  have hg1 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (1 + Complex.I * w)) z :=
    (Complex.differentiableAt_Gamma _ hp1).comp z hlin1
  have hg2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (1 - Complex.I * w)) z :=
    (Complex.differentiableAt_Gamma _ hp2).comp z hlin2
  exact ((hg1.div hg2 (Complex.Gamma_ne_zero hp2))).differentiableWithinAt

theorem gammaRatio_ne_zero {z : ℂ} (hz : z ∈ imStrip (-1) 1) : gammaRatio z ≠ 0 := by
  obtain ⟨hp1, hp2⟩ := gammaArg_ne_pole hz
  exact div_ne_zero (Complex.Gamma_ne_zero hp1) (Complex.Gamma_ne_zero hp2)

theorem gammaRatio_zero : gammaRatio 0 = 1 := by
  rw [gammaRatio]
  simp [Complex.Gamma_one]

/-- **The holomorphic branch of `[Γ(1+iz)/Γ(1-iz)]^{1/2}` on the unit strip, normalised at the
origin.** -/
theorem exists_gammaRatioSqrt :
    ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (imStrip (-1) 1) ∧
      (∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) ∧ E 0 = 1 ∧
      ∀ z ∈ imStrip (-1) 1, E z ≠ 0 :=
  exists_differentiableOn_sq_eq (isOpen_imStrip (-1) 1)
    (isSimplyConnected_imStrip (-1) 1 (by norm_num)) differentiableOn_gammaRatio
    (fun _ hz => gammaRatio_ne_zero hz) zero_mem_imStrip gammaRatio_zero

end

end GaloisForLFunctions.RHTower

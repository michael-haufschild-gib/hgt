import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A boundary-corrected Hardy identity for cusp tails

For a compact `C¹` profile supported in the positive half-line, retain the
lower boundary value when completing the square with logarithmic derivative
`k-1/(2*y)`. The exact cusp energy above height `Y` is the completed square,
a nonnegative `k/y` potential when `k` is nonnegative, and the boundary term
`(k-1/(2*Y))*f(Y)^(2 : ℕ)`.

Consequently the isolated cusp tail satisfies the quarter-energy inequality
when `k*Y >= 1/2`, even with a nonzero trace at the lower boundary. The frequency
parameterization used below covers exactly this range. At zero frequency the
identity gives the complete Hardy boundary defect.

Every derivative and set integral is the actual calculus operation on a bundled
compact `C¹` test function. No global automorphic gluing, Fourier expansion, or
congruence spectral-gap statement is asserted.
-/

open MeasureTheory Set Filter Topology
open scoped Distributions

namespace GaloisForLFunctions.RHTower.SelbergCuspHardyBoundary
noncomputable section

/-- The open positive half-line supporting the cusp test profiles. -/
def positiveRay : TopologicalSpace.Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩
/-- Compactly supported real `C¹` profiles in the positive half-line. -/
abbrev Profile := TestFunction positiveRay ℝ 1

/-- Division of the profile by height, smooth through zero because the profile vanishes nearby. -/
def divided (f : Profile) (y : ℝ) : ℝ := f y / y

private theorem compact_mul (u v : ℝ → ℝ) (hu : HasCompactSupport u) :
    HasCompactSupport (fun y => u y * v y) := by
  convert hu.mul_right (f' := v) using 1 <;> rfl

private theorem compact_mul_left (u v : ℝ → ℝ) (hv : HasCompactSupport v) :
    HasCompactSupport (fun y => u y * v y) := by
  convert hv.mul_left (f := u) using 1 <;> rfl

private theorem compact_div (u v : ℝ → ℝ) (hu : HasCompactSupport u) :
    HasCompactSupport (fun y => u y / v y) := by
  simpa only [div_eq_mul_inv] using compact_mul u (fun y => (v y)⁻¹) hu

private theorem compact_sq (u : ℝ → ℝ) (hu : HasCompactSupport u) :
    HasCompactSupport (fun y => u y ^ (2 : ℕ)) := by
  simpa only [pow_two] using compact_mul u u hu

private theorem compact_square_integrable (u : ℝ → ℝ)
    (hc : Continuous u) (hs : HasCompactSupport u) : Integrable (fun y => u y ^ (2 : ℕ)) :=
  (hc.pow 2).integrable_of_hasCompactSupport (compact_sq u hs)

/-- Division by height preserves the actual `C¹` regularity of these profiles. -/
theorem divided_contDiff (f : Profile) : ContDiff ℝ 1 (divided f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y = 0
  · subst y
    have hn : (0 : ℝ) ∉ tsupport f := by
      intro h
      have hz := f.tsupport_subset h
      change (0 : ℝ) < 0 at hz
      exact lt_irrefl 0 hz
    have he : divided f =ᶠ[𝓝 0] (fun _ => 0) := by
      filter_upwards [(isClosed_closure : IsClosed (tsupport f)).isOpen_compl.mem_nhds hn] with y hy
      simp [divided, image_eq_zero_of_notMem_tsupport hy]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact f.contDiff.contDiffAt.div contDiffAt_id hy

/-- The divided profile still has compact support. -/
theorem divided_compact (f : Profile) : HasCompactSupport (divided f) :=
  compact_div f (fun y => y) f.hasCompactSupport

/-- The exact boundary flux in the cusp square completion. -/
def flux (f : Profile) (k : ℝ) (y : ℝ) : ℝ :=
  k * f y ^ (2 : ℕ) - f y * divided f y / 2

/-- The boundary flux is a `C¹` function on the whole real line. -/
theorem flux_contDiff (f : Profile) (k : ℝ) : ContDiff ℝ 1 (flux f k) := by
  exact (contDiff_const.mul (f.contDiff.pow 2)).sub
    ((f.contDiff.mul (divided_contDiff f)).div_const 2)

/-- The flux has compact support, so its upper endpoint vanishes. -/
theorem flux_compact (f : Profile) (k : ℝ) : HasCompactSupport (flux f k) := by
  have h₁ : HasCompactSupport (fun y => k * f y ^ (2 : ℕ)) := by
    exact compact_mul_left (fun _ => k) (fun y => f y ^ (2 : ℕ)) (compact_sq f f.hasCompactSupport)
  have h₂ : HasCompactSupport (fun y => f y * divided f y / 2) :=
    compact_div _ (fun _ => 2) (compact_mul f (divided f) f.hasCompactSupport)
  exact h₁.sub h₂

private theorem flux_hasDerivAt (f : Profile) (k : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (flux f k)
      (2 * k * f y * deriv f y - deriv f y * divided f y + divided f y ^ (2 : ℕ) / 2) y := by
  have hf := (f.contDiff.differentiable one_ne_zero y).hasDerivAt
  have hg : HasDerivAt (divided f) ((deriv f y * y - f y) / y ^ (2 : ℕ)) y := by
    convert hf.div (hasDerivAt_id y) hy using 1 <;> first | rfl | simp
  have h := ((hf.pow 2).const_mul k).sub ((hf.mul hg).div_const 2)
  convert h using 1 <;> try rfl
  unfold divided
  field_simp [hy]
  ring

/-- Squared first derivative after the frequency and Hardy corrections. -/
def squareField (f : Profile) (k : ℝ) (y : ℝ) : ℝ :=
  (deriv f y + k * f y - divided f y / 2) ^ (2 : ℕ)

/-- Vertical plus horizontal energy density minus one quarter of hyperbolic mass. -/
def excessField (f : Profile) (k : ℝ) (y : ℝ) : ℝ :=
  deriv f y ^ (2 : ℕ) + k ^ (2 : ℕ) * f y ^ (2 : ℕ) - divided f y ^ (2 : ℕ) / 4

private theorem field_decomposition (f : Profile) (k : ℝ) {y : ℝ} (hy : y ≠ 0) :
    excessField f k y = squareField f k y + k * f y * divided f y - deriv (flux f k) y := by
  rw [(flux_hasDerivAt f k hy).deriv]
  unfold excessField squareField
  ring

/-- The completed square is actually integrable. -/
theorem squareField_integrable (f : Profile) (k : ℝ) : Integrable (squareField f k) := by
  have hc : Continuous (fun y => deriv f y + k * f y - divided f y / 2) :=
    ((f.contDiff.continuous_deriv le_rfl).add (continuous_const.mul f.continuous)).sub
      ((divided_contDiff f).continuous.div_const 2)
  have hs : HasCompactSupport (fun y => deriv f y + k * f y - divided f y / 2) :=
    (f.hasCompactSupport.deriv.add (compact_mul_left (fun _ => k) f f.hasCompactSupport)).sub
      (compact_div (divided f) (fun _ => 2) (divided_compact f))
  exact (hc.pow 2).integrable_of_hasCompactSupport (compact_sq _ hs)

/-- The remaining frequency potential is actually integrable. -/
theorem cross_integrable (f : Profile) (k : ℝ) :
    Integrable (fun y => k * f y * divided f y) := by
  have hc : Continuous (fun y => k * f y * divided f y) :=
    (continuous_const.mul f.continuous).mul (divided_contDiff f).continuous
  exact hc.integrable_of_hasCompactSupport
    (compact_mul (fun y => k * f y) (divided f)
      (compact_mul_left (fun _ => k) f f.hasCompactSupport))

/-- The quarter-energy excess is actually integrable. -/
theorem excessField_integrable (f : Profile) (k : ℝ) : Integrable (excessField f k) := by
  have h₁ : Integrable (fun y => deriv f y ^ (2 : ℕ)) :=
    compact_square_integrable (deriv f) (f.contDiff.continuous_deriv le_rfl) f.hasCompactSupport.deriv
  have h₂ : Integrable (fun y => k ^ (2 : ℕ) * f y ^ (2 : ℕ)) :=
    (compact_square_integrable f f.continuous f.hasCompactSupport).const_mul (k ^ (2 : ℕ))
  have h₃ : Integrable (fun y => divided f y ^ (2 : ℕ) / 4) :=
    (compact_square_integrable (divided f) (divided_contDiff f).continuous (divided_compact f)).div_const 4
  exact (h₁.add h₂).sub h₃

/-- Exact cusp Hardy identity with the lower seam contribution retained. -/
theorem cusp_hardy_identity (f : Profile) (k h : ℝ) :
    (∫ y in Ioi (Real.exp h), excessField f k y) =
      (∫ y in Ioi (Real.exp h), squareField f k y) +
        (∫ y in Ioi (Real.exp h), k * f y * divided f y) +
          (k - 1 / (2 * Real.exp h)) * f (Real.exp h) ^ (2 : ℕ) := by
  have hflux : Integrable (deriv (flux f k)) :=
    ((flux_contDiff f k).continuous_deriv le_rfl).integrable_of_hasCompactSupport
      (flux_compact f k).deriv
  have hpoint : (∫ y in Ioi (Real.exp h), excessField f k y) =
      ∫ y in Ioi (Real.exp h), squareField f k y + k * f y * divided f y - deriv (flux f k) y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    exact field_decomposition f k (ne_of_gt ((Real.exp_pos h).trans hy))
  have hs : IntegrableOn (squareField f k) (Ioi (Real.exp h)) := (squareField_integrable f k).integrableOn
  have hc : IntegrableOn (fun y => k * f y * divided f y) (Ioi (Real.exp h)) :=
    (cross_integrable f k).integrableOn
  have hsub := integral_sub (hs.add hc) (hflux.integrableOn (s := Ioi (Real.exp h)))
  have hadd := integral_add hs hc
  simp only [Pi.add_apply] at hsub hadd
  rw [hpoint, hsub, hadd,
    HasCompactSupport.integral_Ioi_deriv_eq (flux_contDiff f k) (flux_compact f k)]
  unfold flux divided
  ring

/-- Frequencies with a nonnegative lower boundary coefficient at height `exp h`. -/
def tailFrequency (h u : ℝ) : ℝ := (1 / 2 + u ^ (2 : ℕ)) / Real.exp h

/-- Every frequency in this parameterization is strictly positive. -/
theorem tailFrequency_pos (h u : ℝ) : 0 < tailFrequency h u := by
  unfold tailFrequency
  positivity

/-- The lower seam coefficient is exactly a nonnegative square divided by height. -/
theorem tailFrequency_boundary (h u : ℝ) :
    tailFrequency h u - 1 / (2 * Real.exp h) = u ^ (2 : ℕ) / Real.exp h := by
  unfold tailFrequency
  ring

/-- The parameterization covers exactly all frequencies above the stated threshold. -/
theorem range_tailFrequency (h : ℝ) :
    Set.range (tailFrequency h) = Ici (1 / (2 * Real.exp h)) := by
  ext k
  constructor
  · rintro ⟨u, rfl⟩
    change 1 / (2 * Real.exp h) ≤ tailFrequency h u
    rw [← sub_nonneg, tailFrequency_boundary]
    positivity
  · intro hk
    have hnonneg : 0 ≤ k * Real.exp h - 1 / 2 := by
      have h := (div_le_iff₀ (by positivity : 0 < 2 * Real.exp h)).mp hk
      linarith
    refine ⟨Real.sqrt (k * Real.exp h - 1 / 2), ?_⟩
    unfold tailFrequency
    rw [Real.sq_sqrt hnonneg]
    field_simp [(Real.exp_pos h).ne']
    ring

/-- The cusp energy excess is nonnegative for the full parameterized frequency range. -/
theorem cusp_hardy_nonneg (f : Profile) (h u : ℝ) :
    0 ≤ ∫ y in Ioi (Real.exp h), excessField f (tailFrequency h u) y := by
  rw [cusp_hardy_identity]
  have hsq : 0 ≤ ∫ y in Ioi (Real.exp h), squareField f (tailFrequency h u) y := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro y _
    exact sq_nonneg _
  have hc : 0 ≤ ∫ y in Ioi (Real.exp h), tailFrequency h u * f y * divided f y := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro y hy
    have hypos := (Real.exp_pos h).trans hy
    have he : tailFrequency h u * f y * divided f y = tailFrequency h u * f y ^ (2 : ℕ) / y := by
      unfold divided
      ring
    rw [he]
    exact div_nonneg (mul_nonneg (tailFrequency_pos h u).le (sq_nonneg _)) hypos.le
  have hb : 0 ≤ (tailFrequency h u - 1 / (2 * Real.exp h)) * f (Real.exp h) ^ (2 : ℕ) := by
    rw [tailFrequency_boundary]
    positivity
  exact add_nonneg (add_nonneg hsq hc) hb

/-- The isolated cusp tail obeys the quarter-energy bound with its boundary value unrestricted. -/
theorem cusp_tail_quarter (f : Profile) (h u : ℝ) :
    (1 / 4 : ℝ) * (∫ y in Ioi (Real.exp h), divided f y ^ (2 : ℕ)) ≤
      ∫ y in Ioi (Real.exp h), deriv f y ^ (2 : ℕ) + tailFrequency h u ^ (2 : ℕ) * f y ^ (2 : ℕ) := by
  have h₁ := compact_square_integrable (deriv f) (f.contDiff.continuous_deriv le_rfl)
    f.hasCompactSupport.deriv
  have h₂ := (compact_square_integrable f f.continuous f.hasCompactSupport).const_mul (tailFrequency h u ^ (2 : ℕ))
  have h₃ := compact_square_integrable (divided f) (divided_contDiff f).continuous (divided_compact f)
  have hs := integral_sub ((h₁.add h₂).integrableOn (s := Ioi (Real.exp h)))
    ((h₃.div_const 4).integrableOn (s := Ioi (Real.exp h)))
  simp only [Pi.add_apply, integral_div] at hs
  have hnonneg := cusp_hardy_nonneg f h u
  unfold excessField at hnonneg
  rw [hs] at hnonneg
  linarith

/-- At zero frequency the exact negative lower Hardy boundary defect remains. -/
theorem pure_hardy_boundary_identity (f : Profile) (h : ℝ) :
    (∫ y in Ioi (Real.exp h), deriv f y ^ (2 : ℕ) - divided f y ^ (2 : ℕ) / 4) =
      (∫ y in Ioi (Real.exp h), (deriv f y - divided f y / 2) ^ (2 : ℕ)) -
        f (Real.exp h) ^ (2 : ℕ) / (2 * Real.exp h) := by
  have hzero := cusp_hardy_identity f 0 h
  simp only [excessField, squareField, zero_mul, zero_pow (by simp : (2 : ℕ) ≠ 0),
    add_zero, zero_sub, integral_zero] at hzero
  convert hzero using 1
  ring

end
end GaloisForLFunctions.RHTower.SelbergCuspHardyBoundary

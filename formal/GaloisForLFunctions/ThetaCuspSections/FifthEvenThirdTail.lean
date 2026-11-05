import GaloisForLFunctions.ThetaCuspSections.FifthEvenThirdTailModel
/-!
# Exact radial tail of theta atoms one and three

The two ordered cross pairs have rate ten and multiplicity eighteen.
Their literal integrals are the gamma moments of their signed radial polynomial.
-/
noncomputable section
open MeasureTheory Set
namespace GaloisForLFunctions.ThetaCuspSections.FifthThirdTail
open FifthRateTail FifthAtomTail

private theorem integral_thirdLinear {μ : Measure ℝ} (f : ℕ → ℝ → ℝ)
 (hf : ∀ n, Integrable (f n) μ) (k : ℕ) (hk : k≤8) :
 thirdLinear (fun n => ∫ t, f n t ∂μ) k=
  ∫ t, thirdLinear (fun n => f n t) k ∂μ := by
 have he : (fun t => thirdLinear (fun n => f n t) k)=
   (fun t => ∑ j ∈ Finset.range 19,
    thirdLinear (fun n => if n=j then 1 else 0) k*f j t) :=
   funext (fun t => thirdLinear_sum k hk (fun n => f n t))
 rw [he,integral_finsetSum _ (fun j _ => (hf j).const_mul _)]
 rw [thirdLinear_sum k hk (fun n => ∫ t, f n t ∂μ)]
 simp only [integral_const_mul]

/-- The signed rate-ten density is integrable on every positive radial ray. -/
theorem third_radial_integrable (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 IntegrableOn (fun t => rateBoundary 10 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (9*t^2) k).eval (10*t)) (Ioi q) := by
 have he : (fun t => rateBoundary 10 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (9*t^2) k).eval (10*t))=
   fun t => ∑ j ∈ Finset.range 19,
    thirdLinear (fun n => if n=j then 1 else 0) k*(rateBoundary 10 t*t^j) := by
  funext t
  rw [← thirdLinear_pow t k hk,← thirdLinear_smul _ _ k hk,thirdLinear_sum k hk]
 rw [he]
 exact integrable_finsetSum _ (fun j _ =>
  (weighted_power_integrable (by norm_num : (0:ℝ)<10) j hq).const_mul _)

/-- Every literal rate-ten radial tail is its exact gamma recurrence model. -/
theorem third_radial_tail_eq (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 (∫ t in Ioi q, rateBoundary 10 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (9*t^2) k).eval (10*t))=
  rateBoundary 10 q*thirdLinear (fun n => gRate 10 n q (rateGammaMass 10 q)) k := by
 calc
  _ = ∫ t in Ioi q, thirdLinear (fun n => rateBoundary 10 t*t^n) k := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [← thirdLinear_pow t k hk,thirdLinear_smul _ _ k hk]
  _ = thirdLinear (fun n => ∫ t in Ioi q, rateBoundary 10 t*t^n) k :=
    (integral_thirdLinear _
      (fun n => weighted_power_integrable (by norm_num : (0:ℝ)<10) n hq) k hk).symm
  _ = thirdLinear (fun n => rateBoundary 10 q*gRate 10 n q (rateGammaMass 10 q)) k := by
    congr 1
    funext n
    exact integral_rateBoundary_mul_pow (by norm_num : (0:ℝ)<10) n hq
  _ = _ := thirdLinear_smul _ _ k hk

/-- The two ordered unequal-pair tails with indices one and three. -/
def thirdRadialTailMatrix (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 18*∫ t in Ioi q, rateBoundary 10 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (9*t^2) (i.val+j.val)).eval (10*t)

/-- The first gamma correction pays both literal ordered tails of atoms one and three. -/
theorem thirdRadialTailMatrix_reserve_posDef {q : ℝ} (hq : 3≤q) :
 (thirdRadialTailMatrix q+(boundary q*(3/(8*q))) • model 0 1).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 obtain ⟨hL,hU⟩ := rateGammaMass_bounds (by norm_num : (0:ℝ)<10) hq0
 have hW : Real.exp (-8*q)≤3^24/((20:ℝ)^8*q^24) := by
  simpa only [Nat.cast_ofNat] using exponential_polynomial_envelope 24 8 (by norm_num) hq
 have hM := reserveModel_posDef hq hL hU (Real.exp_pos _).le hW
 have he : thirdRadialTailMatrix q+(boundary q*(3/(8*q))) • model 0 1=
   boundary q • reserveModel q (rateGammaMass 10 q) (Real.exp (-8*q)) := by
  ext i j
  dsimp only [thirdRadialTailMatrix,reserveModel,model,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  rw [third_radial_tail_eq (i.val+j.val) (by omega) hq0,
    rateBoundary_relative,moment_eq_linearMoment _ _ _ (by omega)]
  norm_num only [show (10:ℝ)-2=8 by norm_num]
  ring
 rw [he]
 exact hM.smul (boundary_pos hq0)

end GaloisForLFunctions.ThetaCuspSections.FifthThirdTail

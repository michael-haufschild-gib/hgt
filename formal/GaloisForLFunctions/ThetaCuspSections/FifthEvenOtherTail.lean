import GaloisForLFunctions.ThetaCuspSections.FifthEvenOtherTailModel
/-!
# Literal tail payments for the remaining unequal theta pairs

Each of the four remaining pairs, with both orderings retained, is paid
by one eighth of the cubic first-atom gamma reserve on the scale-three ray.
-/
noncomputable section
open MeasureTheory Set
namespace GaloisForLFunctions.ThetaCuspSections.FifthOtherTail
open FifthRateTail FifthAtomTail

namespace p14

private theorem integral_pairLinear {μ : Measure ℝ} (f : ℕ → ℝ → ℝ)
 (hf : ∀ n, Integrable (f n) μ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => ∫ t, f n t ∂μ) k=
  ∫ t, pairLinear (fun n => f n t) k ∂μ := by
 have he : (fun t => pairLinear (fun n => f n t) k)=
   (fun t => ∑ j ∈ Finset.range 19,
    pairLinear (fun n => if n=j then 1 else 0) k*f j t) :=
   funext (fun t => pairLinear_sum k hk (fun n => f n t))
 rw [he,integral_finsetSum _ (fun j _ => (hf j).const_mul _)]
 rw [pairLinear_sum k hk (fun n => ∫ t, f n t ∂μ)]
 simp only [integral_const_mul]

/-- The signed rate-17 density is integrable on every positive radial ray. -/
theorem pair_radial_integrable (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 IntegrableOn (fun t => rateBoundary 17 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (16*t^2) k).eval (17*t)) (Ioi q) := by
 have he : (fun t => rateBoundary 17 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (16*t^2) k).eval (17*t))=
   fun t => ∑ j ∈ Finset.range 19,
    pairLinear (fun n => if n=j then 1 else 0) k*(rateBoundary 17 t*t^j) := by
  funext t
  rw [← pairLinear_pow t k hk,← pairLinear_smul _ _ k hk,pairLinear_sum k hk]
 rw [he]
 exact integrable_finsetSum _ (fun j _ =>
  (weighted_power_integrable (by norm_num : (0:ℝ)<17) j hq).const_mul _)

/-- Every literal rate-17 radial tail is its exact gamma recurrence model. -/
theorem pair_radial_tail_eq (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 (∫ t in Ioi q, rateBoundary 17 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (16*t^2) k).eval (17*t))=
  rateBoundary 17 q*pairLinear (fun n => gRate 17 n q (rateGammaMass 17 q)) k := by
 calc
  _ = ∫ t in Ioi q, pairLinear (fun n => rateBoundary 17 t*t^n) k := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [← pairLinear_pow t k hk,pairLinear_smul _ _ k hk]
  _ = pairLinear (fun n => ∫ t in Ioi q, rateBoundary 17 t*t^n) k :=
    (integral_pairLinear _
      (fun n => weighted_power_integrable (by norm_num : (0:ℝ)<17) n hq) k hk).symm
  _ = pairLinear (fun n => rateBoundary 17 q*gRate 17 n q (rateGammaMass 17 q)) k := by
    congr 1
    funext n
    exact integral_rateBoundary_mul_pow (by norm_num : (0:ℝ)<17) n hq
  _ = _ := pairLinear_smul _ _ k hk

/-- The two ordered unequal-pair tails with squared-index product 16. -/
def pairRadialTailMatrix (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 (2*16)*∫ t in Ioi q, rateBoundary 17 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (16*t^2) (i.val+j.val)).eval (17*t)

/-- One eighth of the cubic gamma reserve pays both ordered pair tails. -/
theorem pairRadialTailMatrix_reserve_posDef {q : ℝ} (hq : 3≤q) :
 (pairRadialTailMatrix q+(boundary q*(3/(256*q^2)-3/(1024*q^3))) • model 0 1).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 obtain ⟨hL,hU⟩ := rateGammaMass_bounds (by norm_num : (0:ℝ)<17) hq0
 have hW : Real.exp (-15*q)≤3^45/((20:ℝ)^15*q^45) := by
  simpa only [Nat.cast_ofNat] using exponential_polynomial_envelope 45 15 (by norm_num) hq
 have hM := reserveModel_posDef hq hL hU (Real.exp_pos _).le hW
 have he : pairRadialTailMatrix q+(boundary q*(3/(256*q^2)-3/(1024*q^3))) • model 0 1=
   boundary q • reserveModel q (rateGammaMass 17 q) (Real.exp (-15*q)) := by
  ext i j
  dsimp only [pairRadialTailMatrix,reserveModel,model,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  rw [pair_radial_tail_eq (i.val+j.val) (by omega) hq0,
    rateBoundary_relative,moment_eq_linearMoment _ _ _ (by omega)]
  norm_num only [show (17:ℝ)-2=15 by norm_num]
  ring
 rw [he]
 exact hM.smul (boundary_pos hq0)

end p14

namespace p23

private theorem integral_pairLinear {μ : Measure ℝ} (f : ℕ → ℝ → ℝ)
 (hf : ∀ n, Integrable (f n) μ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => ∫ t, f n t ∂μ) k=
  ∫ t, pairLinear (fun n => f n t) k ∂μ := by
 have he : (fun t => pairLinear (fun n => f n t) k)=
   (fun t => ∑ j ∈ Finset.range 19,
    pairLinear (fun n => if n=j then 1 else 0) k*f j t) :=
   funext (fun t => pairLinear_sum k hk (fun n => f n t))
 rw [he,integral_finsetSum _ (fun j _ => (hf j).const_mul _)]
 rw [pairLinear_sum k hk (fun n => ∫ t, f n t ∂μ)]
 simp only [integral_const_mul]

/-- The signed rate-13 density is integrable on every positive radial ray. -/
theorem pair_radial_integrable (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 IntegrableOn (fun t => rateBoundary 13 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (36*t^2) k).eval (13*t)) (Ioi q) := by
 have he : (fun t => rateBoundary 13 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (36*t^2) k).eval (13*t))=
   fun t => ∑ j ∈ Finset.range 19,
    pairLinear (fun n => if n=j then 1 else 0) k*(rateBoundary 13 t*t^j) := by
  funext t
  rw [← pairLinear_pow t k hk,← pairLinear_smul _ _ k hk,pairLinear_sum k hk]
 rw [he]
 exact integrable_finsetSum _ (fun j _ =>
  (weighted_power_integrable (by norm_num : (0:ℝ)<13) j hq).const_mul _)

/-- Every literal rate-13 radial tail is its exact gamma recurrence model. -/
theorem pair_radial_tail_eq (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 (∫ t in Ioi q, rateBoundary 13 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (36*t^2) k).eval (13*t))=
  rateBoundary 13 q*pairLinear (fun n => gRate 13 n q (rateGammaMass 13 q)) k := by
 calc
  _ = ∫ t in Ioi q, pairLinear (fun n => rateBoundary 13 t*t^n) k := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [← pairLinear_pow t k hk,pairLinear_smul _ _ k hk]
  _ = pairLinear (fun n => ∫ t in Ioi q, rateBoundary 13 t*t^n) k :=
    (integral_pairLinear _
      (fun n => weighted_power_integrable (by norm_num : (0:ℝ)<13) n hq) k hk).symm
  _ = pairLinear (fun n => rateBoundary 13 q*gRate 13 n q (rateGammaMass 13 q)) k := by
    congr 1
    funext n
    exact integral_rateBoundary_mul_pow (by norm_num : (0:ℝ)<13) n hq
  _ = _ := pairLinear_smul _ _ k hk

/-- The two ordered unequal-pair tails with squared-index product 36. -/
def pairRadialTailMatrix (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 (2*36)*∫ t in Ioi q, rateBoundary 13 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (36*t^2) (i.val+j.val)).eval (13*t)

/-- One eighth of the cubic gamma reserve pays both ordered pair tails. -/
theorem pairRadialTailMatrix_reserve_posDef {q : ℝ} (hq : 3≤q) :
 (pairRadialTailMatrix q+(boundary q*(3/(256*q^2)-3/(1024*q^3))) • model 0 1).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 obtain ⟨hL,hU⟩ := rateGammaMass_bounds (by norm_num : (0:ℝ)<13) hq0
 have hW : Real.exp (-11*q)≤3^33/((20:ℝ)^11*q^33) := by
  simpa only [Nat.cast_ofNat] using exponential_polynomial_envelope 33 11 (by norm_num) hq
 have hM := reserveModel_posDef hq hL hU (Real.exp_pos _).le hW
 have he : pairRadialTailMatrix q+(boundary q*(3/(256*q^2)-3/(1024*q^3))) • model 0 1=
   boundary q • reserveModel q (rateGammaMass 13 q) (Real.exp (-11*q)) := by
  ext i j
  dsimp only [pairRadialTailMatrix,reserveModel,model,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  rw [pair_radial_tail_eq (i.val+j.val) (by omega) hq0,
    rateBoundary_relative,moment_eq_linearMoment _ _ _ (by omega)]
  norm_num only [show (13:ℝ)-2=11 by norm_num]
  ring
 rw [he]
 exact hM.smul (boundary_pos hq0)

end p23

namespace p24

private theorem integral_pairLinear {μ : Measure ℝ} (f : ℕ → ℝ → ℝ)
 (hf : ∀ n, Integrable (f n) μ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => ∫ t, f n t ∂μ) k=
  ∫ t, pairLinear (fun n => f n t) k ∂μ := by
 have he : (fun t => pairLinear (fun n => f n t) k)=
   (fun t => ∑ j ∈ Finset.range 19,
    pairLinear (fun n => if n=j then 1 else 0) k*f j t) :=
   funext (fun t => pairLinear_sum k hk (fun n => f n t))
 rw [he,integral_finsetSum _ (fun j _ => (hf j).const_mul _)]
 rw [pairLinear_sum k hk (fun n => ∫ t, f n t ∂μ)]
 simp only [integral_const_mul]

/-- The signed rate-20 density is integrable on every positive radial ray. -/
theorem pair_radial_integrable (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 IntegrableOn (fun t => rateBoundary 20 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (64*t^2) k).eval (20*t)) (Ioi q) := by
 have he : (fun t => rateBoundary 20 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (64*t^2) k).eval (20*t))=
   fun t => ∑ j ∈ Finset.range 19,
    pairLinear (fun n => if n=j then 1 else 0) k*(rateBoundary 20 t*t^j) := by
  funext t
  rw [← pairLinear_pow t k hk,← pairLinear_smul _ _ k hk,pairLinear_sum k hk]
 rw [he]
 exact integrable_finsetSum _ (fun j _ =>
  (weighted_power_integrable (by norm_num : (0:ℝ)<20) j hq).const_mul _)

/-- Every literal rate-20 radial tail is its exact gamma recurrence model. -/
theorem pair_radial_tail_eq (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 (∫ t in Ioi q, rateBoundary 20 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (64*t^2) k).eval (20*t))=
  rateBoundary 20 q*pairLinear (fun n => gRate 20 n q (rateGammaMass 20 q)) k := by
 calc
  _ = ∫ t in Ioi q, pairLinear (fun n => rateBoundary 20 t*t^n) k := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [← pairLinear_pow t k hk,pairLinear_smul _ _ k hk]
  _ = pairLinear (fun n => ∫ t in Ioi q, rateBoundary 20 t*t^n) k :=
    (integral_pairLinear _
      (fun n => weighted_power_integrable (by norm_num : (0:ℝ)<20) n hq) k hk).symm
  _ = pairLinear (fun n => rateBoundary 20 q*gRate 20 n q (rateGammaMass 20 q)) k := by
    congr 1
    funext n
    exact integral_rateBoundary_mul_pow (by norm_num : (0:ℝ)<20) n hq
  _ = _ := pairLinear_smul _ _ k hk

/-- The two ordered unequal-pair tails with squared-index product 64. -/
def pairRadialTailMatrix (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 (2*64)*∫ t in Ioi q, rateBoundary 20 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (64*t^2) (i.val+j.val)).eval (20*t)

/-- One eighth of the cubic gamma reserve pays both ordered pair tails. -/
theorem pairRadialTailMatrix_reserve_posDef {q : ℝ} (hq : 3≤q) :
 (pairRadialTailMatrix q+(boundary q*(3/(256*q^2)-3/(1024*q^3))) • model 0 1).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 obtain ⟨hL,hU⟩ := rateGammaMass_bounds (by norm_num : (0:ℝ)<20) hq0
 have hW : Real.exp (-18*q)≤3^54/((20:ℝ)^18*q^54) := by
  simpa only [Nat.cast_ofNat] using exponential_polynomial_envelope 54 18 (by norm_num) hq
 have hM := reserveModel_posDef hq hL hU (Real.exp_pos _).le hW
 have he : pairRadialTailMatrix q+(boundary q*(3/(256*q^2)-3/(1024*q^3))) • model 0 1=
   boundary q • reserveModel q (rateGammaMass 20 q) (Real.exp (-18*q)) := by
  ext i j
  dsimp only [pairRadialTailMatrix,reserveModel,model,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  rw [pair_radial_tail_eq (i.val+j.val) (by omega) hq0,
    rateBoundary_relative,moment_eq_linearMoment _ _ _ (by omega)]
  norm_num only [show (20:ℝ)-2=18 by norm_num]
  ring
 rw [he]
 exact hM.smul (boundary_pos hq0)

end p24

namespace p34

private theorem integral_pairLinear {μ : Measure ℝ} (f : ℕ → ℝ → ℝ)
 (hf : ∀ n, Integrable (f n) μ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => ∫ t, f n t ∂μ) k=
  ∫ t, pairLinear (fun n => f n t) k ∂μ := by
 have he : (fun t => pairLinear (fun n => f n t) k)=
   (fun t => ∑ j ∈ Finset.range 19,
    pairLinear (fun n => if n=j then 1 else 0) k*f j t) :=
   funext (fun t => pairLinear_sum k hk (fun n => f n t))
 rw [he,integral_finsetSum _ (fun j _ => (hf j).const_mul _)]
 rw [pairLinear_sum k hk (fun n => ∫ t, f n t ∂μ)]
 simp only [integral_const_mul]

/-- The signed rate-25 density is integrable on every positive radial ray. -/
theorem pair_radial_integrable (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 IntegrableOn (fun t => rateBoundary 25 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (144*t^2) k).eval (25*t)) (Ioi q) := by
 have he : (fun t => rateBoundary 25 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (144*t^2) k).eval (25*t))=
   fun t => ∑ j ∈ Finset.range 19,
    pairLinear (fun n => if n=j then 1 else 0) k*(rateBoundary 25 t*t^j) := by
  funext t
  rw [← pairLinear_pow t k hk,← pairLinear_smul _ _ k hk,pairLinear_sum k hk]
 rw [he]
 exact integrable_finsetSum _ (fun j _ =>
  (weighted_power_integrable (by norm_num : (0:ℝ)<25) j hq).const_mul _)

/-- Every literal rate-25 radial tail is its exact gamma recurrence model. -/
theorem pair_radial_tail_eq (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 (∫ t in Ioi q, rateBoundary 25 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (144*t^2) k).eval (25*t))=
  rateBoundary 25 q*pairLinear (fun n => gRate 25 n q (rateGammaMass 25 q)) k := by
 calc
  _ = ∫ t in Ioi q, pairLinear (fun n => rateBoundary 25 t*t^n) k := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [← pairLinear_pow t k hk,pairLinear_smul _ _ k hk]
  _ = pairLinear (fun n => ∫ t in Ioi q, rateBoundary 25 t*t^n) k :=
    (integral_pairLinear _
      (fun n => weighted_power_integrable (by norm_num : (0:ℝ)<25) n hq) k hk).symm
  _ = pairLinear (fun n => rateBoundary 25 q*gRate 25 n q (rateGammaMass 25 q)) k := by
    congr 1
    funext n
    exact integral_rateBoundary_mul_pow (by norm_num : (0:ℝ)<25) n hq
  _ = _ := pairLinear_smul _ _ k hk

/-- The two ordered unequal-pair tails with squared-index product 144. -/
def pairRadialTailMatrix (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 (2*144)*∫ t in Ioi q, rateBoundary 25 t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (144*t^2) (i.val+j.val)).eval (25*t)

/-- One eighth of the cubic gamma reserve pays both ordered pair tails. -/
theorem pairRadialTailMatrix_reserve_posDef {q : ℝ} (hq : 3≤q) :
 (pairRadialTailMatrix q+(boundary q*(3/(256*q^2)-3/(1024*q^3))) • model 0 1).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 obtain ⟨hL,hU⟩ := rateGammaMass_bounds (by norm_num : (0:ℝ)<25) hq0
 have hW : Real.exp (-23*q)≤3^69/((20:ℝ)^23*q^69) := by
  simpa only [Nat.cast_ofNat] using exponential_polynomial_envelope 69 23 (by norm_num) hq
 have hM := reserveModel_posDef hq hL hU (Real.exp_pos _).le hW
 have he : pairRadialTailMatrix q+(boundary q*(3/(256*q^2)-3/(1024*q^3))) • model 0 1=
   boundary q • reserveModel q (rateGammaMass 25 q) (Real.exp (-23*q)) := by
  ext i j
  dsimp only [pairRadialTailMatrix,reserveModel,model,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  rw [pair_radial_tail_eq (i.val+j.val) (by omega) hq0,
    rateBoundary_relative,moment_eq_linearMoment _ _ _ (by omega)]
  norm_num only [show (25:ℝ)-2=23 by norm_num]
  ring
 rw [he]
 exact hM.smul (boundary_pos hq0)

end p34

end GaloisForLFunctions.ThetaCuspSections.FifthOtherTail

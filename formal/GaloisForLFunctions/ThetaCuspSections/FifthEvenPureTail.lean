import GaloisForLFunctions.ThetaCuspSections.FifthEvenTailRateMoments
/-!
# Exact scaling of pure-atom fifth even radial tails

A pure theta atom rescales the first-atom radial variable. Its integrated
matrix is a positive scalar multiple of the first-atom tail at the enlarged
cutoff, so every pure atom is strict from scale three.
-/
noncomputable section
open MeasureTheory Set Matrix
namespace GaloisForLFunctions.ThetaCuspSections.FifthPureTail
open FifthAtomTail FifthRateTail

private theorem linearMoment_pow (q : ℝ) (k : ℕ) (hk : k≤8) :
 linearMoment (fun n => q^n) k=
  (_root_.RHTower.thetaPairRadialEvenPolynomial (q^2) k).eval (2*q) := by
 rw [EightCrossData.radial_eq q k hk]
 interval_cases k <;> simp only [linearMoment,EightCrossData.rMoment,pow_zero,pow_one,mul_one]
 all_goals rfl

private theorem linearMoment_sum (k : ℕ) (hk : k≤8) (m : ℕ → ℝ) :
 linearMoment m k=∑ j ∈ Finset.range 11,
  linearMoment (fun n => if n=j then 1 else 0) k*m j := by
 interval_cases k <;> norm_num [linearMoment,Finset.sum_range_succ] <;> ring

/-- Radial density of a pure atom whose squared index is `c`. -/
def pureDensity (c : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
 rateBoundary (2*c) t*
  (_root_.RHTower.thetaPairRadialEvenPolynomial ((c*t)^2) k).eval (2*(c*t))

/-- Every pure radial jet is integrable on a positive ray. -/
theorem pureDensity_integrable {c q : ℝ} (hc : 0<c) (hq : 0<q)
 (k : ℕ) (hk : k≤8) : IntegrableOn (pureDensity c k) (Ioi q) := by
 have he : pureDensity c k=fun t => ∑ j ∈ Finset.range 11,
   (linearMoment (fun n => if n=j then 1 else 0) k*c^j)*
    (rateBoundary (2*c) t*t^j) := by
  funext t
  dsimp only [pureDensity]
  rw [← linearMoment_pow (c*t) k hk,← linearMoment_smul _ _ k hk,
    linearMoment_sum k hk]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_pow]
  ring
 rw [he]
 exact integrable_finsetSum _ (fun j _ =>
  (weighted_power_integrable (mul_pos (by norm_num) hc) j hq).const_mul _)

/-- The square of the radial index is the source multiplicity of a pure pair. -/
def pureRadialTailMatrix (c q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 c^2*∫ t in Ioi q, pureDensity c (i.val+j.val) t

/-- Linear radial scaling identifies the pure tail exactly. -/
theorem pureRadialTailMatrix_eq {c q : ℝ} (hc : 0<c) (hq : 0<q) :
 pureRadialTailMatrix c q=(c/c^(3/2:ℝ)) • radialTailMatrix (c*q) := by
 have hcR := Real.rpow_pos_of_pos hc (3/2:ℝ)
 have hd (t : ℝ) (ht : 0<t) :
   boundary (c*t)=c^(3/2:ℝ)*rateBoundary (2*c) t := by
  unfold boundary rateBoundary
  rw [Real.mul_rpow hc.le ht.le,
    show (-2:ℝ)*(c*t)= -(2*c)*t by ring]
  ring
 ext i j
 have he := integral_comp_mul_left_Ioi
  (fun u => boundary u*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (u^2) (i.val+j.val)).eval (2*u)) q hc
 have hs : (∫ t in Ioi q, boundary (c*t)*
   (_root_.RHTower.thetaPairRadialEvenPolynomial ((c*t)^2) (i.val+j.val)).eval (2*(c*t)))=
   c^(3/2:ℝ)*∫ t in Ioi q, pureDensity c (i.val+j.val) t := by
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [hd t (hq.trans ht)]
  dsimp only [pureDensity]
  ring
 rw [hs] at he
 simp only [smul_eq_mul] at he
 dsimp only [pureRadialTailMatrix,radialTailMatrix,Matrix.smul_apply,smul_eq_mul]
 apply mul_right_cancel₀ hcR.ne'
 calc
  _ = c*(c*(c^(3/2:ℝ)*(∫ t in Ioi q, pureDensity c (i.val+j.val) t))) := by ring
  _ = c*(c*(c⁻¹*(∫ t in Ioi (c*q), boundary t*
    (_root_.RHTower.thetaPairRadialEvenPolynomial (t^2) (i.val+j.val)).eval (2*t)))) := by rw [he]
  _ = _ := by field_simp [hc.ne',hcR.ne']

/-- Every pure atom retains strict fifth-tail positivity on the scale-three ray. -/
theorem pureRadialTailMatrix_posDef {c q : ℝ} (hc : 1≤c) (hq : 3≤q) :
 (pureRadialTailMatrix c q).PosDef := by
 have hc0 : 0<c := lt_of_lt_of_le (by norm_num) hc
 have hq0 : 0<q := lt_of_lt_of_le (by norm_num) hq
 have hmul := mul_le_mul_of_nonneg_right hc hq0.le
 have hcq : 3≤c*q := hq.trans (by simpa only [one_mul] using hmul)
 rw [pureRadialTailMatrix_eq hc0 hq0]
 exact (radialTailMatrix_posDef hcq).smul (div_pos hc0 (Real.rpow_pos_of_pos hc0 _))

end GaloisForLFunctions.ThetaCuspSections.FifthPureTail

import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspPairedFourier

/-!
# The full original theta-cusp tail and complex squared source: exact constant Fourier components.

This leaf proves the displayed source or cusp identity. Causal continuation,
left-QNM evaluation and Hawking-clock extinction remain separate obligations.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMCuspProjection
open D4BMAngularSeries D4BMGlobalAngularResponse
noncomputable section

/-- The actual complex amplitude of one unsigned scalar Fourier--Bessel mode. -/
def amplitude (u : ℂ) (y : ℝ) (N : ℕ) : ℂ :=
  coefficient u 0 N*(Real.rpow y (1/2):ℂ)*modifiedBesselKOrder (2*Real.pi*((N:ℝ)+1)*y) u

private theorem term_eq_amplitude (u : ℂ) (negative : Bool) (N : ℕ) (x y : ℝ) :
    term u u (1/2) 0 negative N ![x,y] = amplitude u y N*
      (if negative then character (-(N+1)) x else character (N+1) x) := by
  have hp : d4BMCompletedEisensteinFourierPhase negative N x =
      (if negative then character (-(N+1)) x else character (N+1) x) := by
    cases negative <;> simp only [Bool.false_eq_true,if_false,if_true,
      d4BMCompletedEisensteinFourierPhase,d4BMFourierSign,character]
    all_goals congr 1; push_cast; ring
  simp only [term,Matrix.cons_val_zero,Matrix.cons_val_one,hp,amplitude]
  ring

/-- Absolute convergence retains every original coefficient at every positive height. -/
theorem amplitude_norm_summable (u : ℂ) {y : ℝ} (hy : 0 < y) :
    Summable (fun N => ‖amplitude u y N‖) := by
  have he := (term_summable u u (1/2) 0 false ![0,y] hy).norm
  simpa only [term_eq_amplitude,Bool.false_eq_true,if_false,character,Complex.ofReal_zero,
    mul_zero,Complex.exp_zero,mul_one] using he

/-- The opposite-frequency amplitude squares are also absolutely summable. -/
theorem amplitude_sq_norm_summable (u : ℂ) {y : ℝ} (hy : 0 < y) :
    Summable (fun N => ‖amplitude u y N^2‖) := by
  have h := (amplitude_norm_summable u hy).mul_norm (amplitude_norm_summable u hy)
  have hd := h.comp_injective (i := fun N : ℕ => (N,N)) (by
    intro a b hab
    exact congrArg Prod.fst hab)
  simpa only [Function.comp_def,pow_two] using hd

/-- Exact identification of the full signed scalar tail with its original paired frequencies. -/
theorem tail_eq_series (u : ℂ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    tail u ![x,y] = 2*series (amplitude u y) x := by
  change 2*(d4BMCompletedEisensteinSignedSqrtWhittakerTail u u false x 0 0 y+
    d4BMCompletedEisensteinSignedSqrtWhittakerTail u u true x 0 0 y) = _
  have hp := signedTail_eq_value u u false 0 0 ![x,y] hy
  have hm := signedTail_eq_value u u true 0 0 ![x,y] hy
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Nat.cast_zero,zero_add] at hp hm
  rw [hp,hm]
  norm_num only [Nat.cast_zero,zero_add]
  congr 1
  rw [value,value,← (term_summable u u (1/2) 0 false ![x,y] hy).tsum_add
    (term_summable u u (1/2) 0 true ![x,y] hy)]
  apply tsum_congr
  intro N
  rw [term_eq_amplitude,term_eq_amplitude]
  simp only [Bool.false_eq_true,if_false,if_true,wave]
  ring

/-- The complete scalar tail has zero horizontal average, with no spectral restriction. -/
theorem mean_tail (u : ℂ) {y : ℝ} (hy : 0 < y) :
    mean (fun x => tail u ![x,y]) = 0 := by
  simp_rw [tail_eq_series u hy]
  change (∫ x in Ioc (-1/2:ℝ) (1/2), 2*series (amplitude u y) x)=0
  rw [integral_const_mul]
  change 2*mean (series (amplitude u y))=0
  rw [mean_series _ (amplitude_norm_summable u hy),mul_zero]

/-- The full complex square retains exactly the paired opposite-frequency source.
No modulus square or positivity hypothesis replaces this phase-sensitive coefficient. -/
theorem mean_tail_sq (u : ℂ) {y : ℝ} (hy : 0 < y) :
    mean (fun x => tail u ![x,y] ^2) = 8*∑' N, amplitude u y N^2 := by
  simp_rw [tail_eq_series u hy,mul_pow]
  change (∫ x in Ioc (-1/2:ℝ) (1/2), (2:ℂ)^2*series (amplitude u y) x^2)=_
  rw [integral_const_mul]
  change (2:ℂ)^2*mean (fun x => series (amplitude u y) x^2)=_
  rw [mean_series_sq _ (amplitude_norm_summable u hy)]
  ring

/-- The full squared-source remainder has an exact convergent constant Fourier coefficient. -/
theorem mean_squareRemainder (u : ℂ) {y : ℝ} (hy : 0 < y) :
    mean (fun x => squareRemainder u ![x,y]) = 8*∑' N, amplitude u y N^2 := by
  have ht : Continuous (fun x => tail u ![x,y]) := by
    have he : (fun x => tail u ![x,y]) = fun x => 2*series (amplitude u y) x :=
      funext (tail_eq_series u hy)
    rw [he]
    exact continuous_const.mul (series_continuous _ (amplitude_norm_summable u hy))
  simp_rw [squareRemainder_eq]
  simp only [← mul_assoc]
  change (∫ x in Ioc (-1/2:ℝ) (1/2),
    (2*principal u ![0,y])*tail u ![x,y]+tail u ![x,y] ^2)=_
  have h1 : IntegrableOn (fun x => (2*principal u ![0,y])*tail u ![x,y])
      (Ioc (-1/2:ℝ) (1/2)) := (continuous_const.mul ht).integrableOn_Ioc
  have h2 : IntegrableOn (fun x => tail u ![x,y] ^2) (Ioc (-1/2:ℝ) (1/2)) :=
    (ht.pow 2).integrableOn_Ioc
  rw [integral_add h1 h2,integral_const_mul]
  change (2*principal u ![0,y])*mean (fun x => tail u ![x,y])+
    mean (fun x => tail u ![x,y] ^2)=_
  rw [mean_tail u hy,mul_zero,zero_add,mean_tail_sq u hy]

/-- The actual admitted full forcing sees the opposite-frequency sum above its cutoff. -/
theorem mean_forcing_high (q : XiZeroCopy) (branch : Bool) {y : ℝ} (hy : 3 < y) :
    mean (fun x => forcing q branch ![x,y]) =
      4*parameter q branch*∑' N, amplitude (center q) y N^2 := by
  have hh (x : ℝ) := forcing_high q branch ![x,y] hy
  simp_rw [hh]
  change (∫ x in Ioc (-1/2:ℝ) (1/2),
    (parameter q branch/2)*squareRemainder (center q) ![x,y])=_
  rw [integral_const_mul]
  change (parameter q branch/2)*mean (fun x => squareRemainder (center q) ![x,y])=_
  rw [mean_squareRemainder _ (by linarith)]
  ring

end
end RHTower.D4BMCuspProjection

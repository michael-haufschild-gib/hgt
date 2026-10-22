import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalBaseCircleJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeSourceJetGrowth
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCuspJets

/-! Actual angular jets of the original native circle mean on unbounded radii.
Finite weighted-jet closure supplies explicit exponential radius growth while
retaining arbitrary cusp decay and the original half-square normalization. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace RHTower.D4BMNativeAngularGrowth
open D4BMGlobalAngularResponse D4BMNativeCircle D4BMSquareCuspJets D4BMOriginalBaseCircleJets D4BMAngularSeries
open D4BMNativeCuspJets D4BMNativeSourceJetGrowth
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
noncomputable section
set_option autoImplicit false
private abbrev P := Fin 4 → ℝ
private abbrev Field := P → ℂ

private theorem circle_coefficients (d theta : ℝ) (hd : 0 ≤ d) :
    |offset d theta| ≤ Real.exp d ∧ |height d theta| ≤ Real.exp d := by
  have hD := denominator_pos d theta
  have hs := Real.sinh_nonneg_iff.mpr hd
  have hS : |Real.sin theta| ≤ denominator d theta := by
    have hid : (denominator d theta)^(2 : ℕ)-(radialNumerator d theta)^(2 : ℕ)=(Real.sin theta)^(2 : ℕ) := by
      calc
        _ = (Real.cosh d^(2 : ℕ)-Real.sinh d^(2 : ℕ))*(1-Real.cos theta^(2 : ℕ)) := by
          unfold denominator radialNumerator; ring
        _ = _ := by rw [Real.cosh_sq_sub_sinh_sq]; nlinarith [Real.sin_sq_add_cos_sq theta]
    nlinarith [sq_nonneg (radialNumerator d theta),sq_abs (Real.sin theta)]
  constructor
  · rw [offset,abs_div,abs_mul,abs_of_nonneg hs,abs_of_pos hD]
    calc
      _ ≤ Real.sinh d*denominator d theta/denominator d theta := by gcongr
      _ = Real.sinh d := mul_div_cancel_right₀ _ hD.ne'
      _ ≤ Real.exp d := by rw [← Real.cosh_add_sinh]; linarith [Real.cosh_pos d]
  · have hl : Real.exp (-d) ≤ denominator d theta := by
      rw [← Real.cosh_sub_sinh]
      dsimp [denominator]
      nlinarith [Real.cos_le_one theta]
    rw [height,abs_of_pos (one_div_pos.mpr hD)]
    calc
      _ ≤ 1/Real.exp (-d) := one_div_le_one_div_of_le (Real.exp_pos _) hl
      _ = Real.exp d := by rw [Real.exp_neg,one_div,inv_inv]

private theorem weighted_bound (u : ℂ) (word : List (Fin 2)) (a b N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ d theta x k : ℝ, 0 ≤ d → 0 ≤ k →
      ‖weighted a b (coordinateJet word (squareRemainder u)) d theta x k‖ ≤
        C*Real.exp (B*d-(N:ℝ)*k) := by
  obtain ⟨C,B,hC,hB,h⟩ := squareRemainder_circle_jet_bound u word N (a+b)
  refine ⟨C,B+(a+b:ℕ),hC,by positivity,?_⟩
  intro d theta x k hd hk
  have hc := circle_coefficients d theta hd
  have hU : ‖U d theta k‖ ≤ Real.exp (k+d) := by
    simpa [U,Real.exp_add,abs_mul,abs_of_pos (Real.exp_pos k)] using
      mul_le_mul_of_nonneg_left hc.1 (Real.exp_nonneg k)
  have hY : ‖Y d theta k‖ ≤ Real.exp (k+d) := by
    simpa [Y,Real.exp_add,abs_mul,abs_of_pos (Real.exp_pos k)] using
      mul_le_mul_of_nonneg_left hc.2 (Real.exp_nonneg k)
  calc
    _ ≤ (Real.exp (k+d))^a*(Real.exp (k+d))^b*
        ‖coordinateJet word (squareRemainder u) (logCircle d theta x k)‖ := by
      simp only [weighted,norm_mul,norm_pow]
      gcongr
    _ = Real.exp ((a+b:ℕ)*d)*(Real.exp ((a+b:ℕ)*k)*
        ‖coordinateJet word (squareRemainder u) (logCircle d theta x k)‖) := by
      rw [← pow_add,← Real.exp_nat_mul,← mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp ((a+b:ℕ)*d)*(C*Real.exp (B*d-(N:ℝ)*k)) :=
      mul_le_mul_of_nonneg_left (h d theta x k hd hk) (Real.exp_nonneg _)
    _ = C*Real.exp ((B+(a+b:ℕ))*d-(N:ℝ)*k) := by
      rw [mul_left_comm,← Real.exp_add]
      congr 2
      ring

private inductive Represented (u : ℂ) : Field → Prop
  | term (a b : ℕ) (word : List (Fin 2)) : Represented u
      (fun p => weighted a b (coordinateJet word (squareRemainder u)) (p 0) (p 1) (p 2) (p 3))
  | add {f g : Field} : Represented u f → Represented u g → Represented u (fun p => f p+g p)
  | scale (c : ℂ) {f : Field} : Represented u f → Represented u (fun p => c*f p)
  | congr {f g : Field} : Represented u f → f=g → Represented u g

private theorem Represented.smooth {u : ℂ} {f : Field} (h : Represented u f) :
    ContDiff ℝ ∞ f := by
  induction h with
  | term a b word => exact weighted_smooth a b _ (squareRemainder_jet_smooth u word)
  | add _ _ hf hg => exact hf.add hg
  | scale c _ hf => exact contDiff_const.mul hf
  | congr _ he hf => exact he ▸ hf

private theorem coordinate_update (f : Field) (hf : ContDiff ℝ ∞ f) (p : P) (i : Fin 4) :
    coordDeriv i f p=deriv (fun t => f (Function.update p i t)) (p i) := by
  have h := (hf.differentiable (by simp) p).hasFDerivAt
  have h' : HasFDerivAt f (fderiv ℝ f p) (Function.update p i (p i)) := by
    simpa only [Function.update_eq_self] using h
  simpa only [Function.update_eq_self,coordDeriv,Function.comp_def] using
    (h'.comp_hasDerivAt (p i) (hasDerivAt_update p i (p i))).deriv.symm

private theorem term_derivative (u : ℂ) (a b : ℕ) (word : List (Fin 2)) (i : Fin 2) :
    Represented u (coordDeriv i.succ.succ
      (fun p => weighted a b (coordinateJet word (squareRemainder u)) (p 0) (p 1) (p 2) (p 3))) := by
  have hf := squareRemainder_jet_smooth u word
  have hs := weighted_smooth a b _ hf
  fin_cases i
  · apply (Represented.term a b (0::word)).congr
    funext p
    rw [coordinate_update _ hs]
    simpa [coordinateJet,Function.update_apply] using
      (weighted_horizontal a b _ hf (p 0) (p 1) (p 2) (p 3)).deriv.symm
  · apply ((Represented.scale ((a:ℂ)+(b:ℂ)) (Represented.term a b word)).add
      (Represented.term (a+1) b (0::word)) |>.add
      (Represented.term a (b+1) (1::word))).congr
    funext p
    rw [coordinate_update _ hs]
    simpa [coordinateJet,Function.update_apply] using
      (weighted_height a b _ hf (p 0) (p 1) (p 2) (p 3)).deriv.symm

private theorem Represented.derivative {u : ℂ} {f : Field} (h : Represented u f) (i : Fin 2) :
    Represented u (coordDeriv i.succ.succ f) := by
  induction h with
  | term a b word => exact term_derivative u a b word i
  | @add f g hf hg ihf ihg =>
      apply (ihf.add ihg).congr
      funext p
      change _=(fderiv ℝ (fun p => f p+g p) p) (Pi.single i.succ.succ 1)
      rw [fderiv_fun_add (hf.smooth.differentiable (by simp) p)
        (hg.smooth.differentiable (by simp) p)]
      rfl
  | @scale c f hf ih =>
      apply (Represented.scale c ih).congr
      funext p
      simp only [coordDeriv,fderiv_const_mul (hf.smooth.differentiable (by simp) p),
        smul_apply,smul_eq_mul]
  | congr _ he ih => exact he ▸ ih

private theorem Represented.bound {u : ℂ} {f : Field} (h : Represented u f) (N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ d theta x k : ℝ, 0 ≤ d → 0 ≤ k →
      ‖f ![d,theta,x,k]‖ ≤ C*Real.exp (B*d-(N:ℝ)*k) := by
  induction h with
  | term a b word => exact weighted_bound u word a b N
  | @add f g hf hg ihf ihg =>
      obtain ⟨C,B,hC,hB,hf⟩ := ihf
      obtain ⟨D,E,hD,hE,hg⟩ := ihg
      refine ⟨C+D,B+E,add_nonneg hC hD,add_nonneg hB hE,?_⟩
      intro d theta x k hd hk
      calc
        _ ≤ ‖f ![d,theta,x,k]‖+‖g ![d,theta,x,k]‖ := norm_add_le _ _
        _ ≤ C*Real.exp (B*d-(N:ℝ)*k)+D*Real.exp (E*d-(N:ℝ)*k) :=
          add_le_add (hf d theta x k hd hk) (hg d theta x k hd hk)
        _ ≤ C*Real.exp ((B+E)*d-(N:ℝ)*k)+D*Real.exp ((B+E)*d-(N:ℝ)*k) := by
          apply add_le_add <;> gcongr <;> linarith
        _ = _ := by ring
  | @scale c f hf ih =>
      obtain ⟨C,B,hC,hB,hf⟩ := ih
      refine ⟨‖c‖*C,B,mul_nonneg (norm_nonneg _) hC,hB,?_⟩
      intro d theta x k hd hk
      rw [norm_mul,mul_assoc]
      exact mul_le_mul_of_nonneg_left (hf d theta x k hd hk) (norm_nonneg c)
  | congr _ he ih => exact he ▸ ih

private theorem Represented.angularJets {u : ℂ} {f : Field} (h : Represented u f)
    (word : List (Fin 2)) : Represented u (nativeIntegrandJet (word.map Fin.succ) f) := by
  induction word with
  | nil => exact h
  | cons i word ih =>
      fin_cases i
      · exact ih.derivative 0
      · exact ih.derivative 1

private theorem circle_represented (q : XiZeroCopy) :
    Represented (D4BMGlobalAngularResponse.center q) (circleRemainder q) := by
  apply (Represented.scale (1/2) (Represented.term 0 0 [])).congr
  funext p
  change (1/2:ℂ)*weighted 0 0 (squareRemainder (D4BMGlobalAngularResponse.center q))
    (p 0) (p 1) (p 2) (p 3)=
    squareRemainder (D4BMGlobalAngularResponse.center q) (logCircle (p 0) (p 1) (p 2) (p 3))/2
  simp only [weighted,pow_zero,one_mul]
  ring

private theorem average_bound {f : ℝ → ℂ} {B : ℝ}
    (hb : ∀ theta, ‖f theta‖ ≤ B) : ‖average f‖ ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := MeasureTheory.volume.restrict (Ioc 0 (2*Real.pi)))
    (Filter.Eventually.of_forall fun theta => hb theta)
  have hm : (MeasureTheory.volume.restrict (Ioc 0 (2*Real.pi))).real Set.univ=2*Real.pi := by
    simp [MeasureTheory.Measure.real,Real.volume_Ioc,Real.pi_pos.le]
  rw [hm] at h
  unfold D4BMNativeCircle.average
  rw [norm_mul,norm_div,norm_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ ≤ (1/(2*Real.pi))*(B*(2*Real.pi)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = B := by field_simp

/-- All actual horizontal/log-height jets of the original half-square circle mean
have arbitrary cusp decay with exponential radius growth. No compact-radius
constant is extrapolated to the unbounded causal domain. -/
theorem native_angular_jet_bound (q : XiZeroCopy) (word : List (Fin 2)) (N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ d x k : ℝ, 0 ≤ d → 0 ≤ k →
      ‖nativeJet (word.map Fin.succ)
        (fun p => cuspMeanRemainder q (p 0) (p 1) (p 2)) ![d,x,k]‖ ≤
        C*Real.exp (B*d-(N:ℝ)*k) := by
  obtain ⟨C,B,hC,hB,h⟩ := ((circle_represented q).angularJets word).bound N
  refine ⟨C,B,hC,hB,?_⟩
  intro d x k hd hk
  rw [nativeCuspJet_integral]
  exact average_bound (fun theta => h d theta x k hd hk)

end
end RHTower.D4BMNativeAngularGrowth

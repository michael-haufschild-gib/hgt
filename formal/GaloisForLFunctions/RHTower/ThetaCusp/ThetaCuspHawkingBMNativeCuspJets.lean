import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSquareCuspJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCuspTransport

/-! Actual radius and base-coordinate jets of the complete native cusp remainder.
All differentiated circle coefficients and the original averaging measure are retained. -/
open Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMNativeCuspJets
open D4BMNativeCircle D4BMSquareCuspJets D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
private abbrev P := Fin 4 → ℝ
private abbrev C := Fin 2 → ℝ
private abbrev Field := P → ℂ
private abbrev D := @coordDeriv 4

private def select : P →L[ℝ] C :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 1]
private theorem select_apply (p : P) : select p=![p 0,p 1] := by
  ext j
  fin_cases j <;> rfl
private def circleMap (p : P) : C := logCircle (p 0) (p 1) (p 2) (p 3)
private def off (z : C) : ℝ := offset (z 0) (z 1)
private def hei (z : C) : ℝ := height (z 0) (z 1)
private def direction (i : Fin 4) : C := select (Pi.single i 1)
private def rdiff (i : Fin 4) (c : C → ℝ) (z : C) : ℝ :=
  fderiv ℝ c z (direction i)
private def cdiff (i : Fin 4) (c : C → ℂ) (z : C) : ℂ :=
  fderiv ℝ c z (direction i)
private def delta (i j : Fin 4) : ℝ := if i=j then 1 else 0
private def horizontalCoefficient (i : Fin 4) (z : C) : ℝ :=
  delta i 3 * off z + rdiff i off z
private def verticalCoefficient (i : Fin 4) (z : C) : ℝ :=
  delta i 3 * hei z + rdiff i hei z
private def heightMonomial (m : ℕ) (p : P) : ℂ :=
  Complex.exp ((m:ℂ)*(p 3:ℂ))
private def pullJet (u : ℂ) (word : List (Fin 2)) (p : P) : ℂ :=
  coordinateJet word (squareRemainder u) (circleMap p)
private def term (u : ℂ) (m : ℕ) (word : List (Fin 2)) (c : C → ℂ) (p : P) : ℂ :=
  c (select p)*heightMonomial m p*pullJet u word p

private theorem off_smooth : ContDiff ℝ ∞ off := by
  unfold off offset
  apply ContDiff.div
  · fun_prop
  · unfold denominator; fun_prop
  · intro z; exact (denominator_pos (z 0) (z 1)).ne'
private theorem hei_smooth : ContDiff ℝ ∞ hei := by
  unfold hei height
  apply ContDiff.div contDiff_const
  · unfold denominator; fun_prop
  · intro z; exact (denominator_pos (z 0) (z 1)).ne'
private theorem rdiff_smooth (i : Fin 4) {c : C → ℝ} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (rdiff i c) :=
  (hc.fderiv_right (by simp)).clm_apply contDiff_const
private theorem cdiff_smooth (i : Fin 4) {c : C → ℂ} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (cdiff i c) :=
  (hc.fderiv_right (by simp)).clm_apply contDiff_const
private theorem horizontalCoefficient_smooth (i : Fin 4) :
    ContDiff ℝ ∞ (horizontalCoefficient i) :=
  (contDiff_const.mul off_smooth).add (rdiff_smooth i off_smooth)
private theorem verticalCoefficient_smooth (i : Fin 4) :
    ContDiff ℝ ∞ (verticalCoefficient i) :=
  (contDiff_const.mul hei_smooth).add (rdiff_smooth i hei_smooth)
private theorem circleMap_smooth : ContDiff ℝ ∞ circleMap := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  apply contDiffAt_pi.mpr
  intro j
  fin_cases j <;> dsimp [circleMap,logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')
private theorem circleMap_pos (p : P) : 0 < circleMap p 1 :=
  mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
private theorem pullJet_smooth (u : ℂ) (word : List (Fin 2)) :
    ContDiff ℝ ∞ (pullJet u word) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact ((squareRemainder_jet_smooth u word).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds (circleMap_pos p))).comp p
      circleMap_smooth.contDiffAt
private theorem heightMonomial_smooth (m : ℕ) : ContDiff ℝ ∞ (heightMonomial m) := by
  exact (contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (3:Fin 4)))).cexp
private theorem term_smooth (u : ℂ) (m : ℕ) (word : List (Fin 2)) (c : C → ℂ)
    (hc : ContDiff ℝ ∞ c) : ContDiff ℝ ∞ (term u m word c) :=
  ((hc.comp select.contDiff).mul (heightMonomial_smooth m)).mul (pullJet_smooth u word)

private theorem D_mul {f g : Field} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin 4) (p : P) : D i (fun z => f z*g z) p=D i f p*g p+f p*D i g p := by
  simp only [D,coordDeriv,fderiv_fun_mul (hf.differentiable (by simp) p)
    (hg.differentiable (by simp) p),add_apply,smul_apply,smul_eq_mul]
  ring
private theorem D_add {f g : Field} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin 4) (p : P) : D i (fun z => f z+g z) p=D i f p+D i g p := by
  simp only [D,coordDeriv,fderiv_fun_add (hf.differentiable (by simp) p)
    (hg.differentiable (by simp) p),add_apply]
private theorem D_coefficient {c : C → ℂ} (hc : ContDiff ℝ ∞ c) (i : Fin 4) (p : P) :
    D i (fun z => c (select z)) p=cdiff i c (select p) := by
  unfold D coordDeriv cdiff direction
  have h := (hc.differentiable (by simp) (select p)).hasFDerivAt.comp p select.hasFDerivAt
  simp only [Function.comp_def] at h
  rw [h.fderiv]
  rfl
private theorem D_heightMonomial (m : ℕ) (i : Fin 4) (p : P) :
    D i (heightMonomial m) p=(delta i 3:ℂ)*(m:ℂ)*heightMonomial m p := by
  have hc := Complex.ofRealCLM.hasFDerivAt.comp p (hasFDerivAt_apply (𝕜 := ℝ) 3 p)
  have he := (hc.const_mul (m:ℂ)).cexp
  have he' : HasFDerivAt (heightMonomial m)
      (heightMonomial m p • (m:ℂ) • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 3)) p := by
    simpa only [heightMonomial,Function.comp_def,Complex.ofRealCLM_apply] using! he
  change fderiv ℝ (heightMonomial m) p (Pi.single i 1)=_
  rw [he'.fderiv]
  fin_cases i
  · simp [delta,ContinuousLinearMap.comp_apply]
  · simp [delta,ContinuousLinearMap.comp_apply]
  · simp [delta,ContinuousLinearMap.comp_apply]
  · simp [delta,ContinuousLinearMap.comp_apply]
    ring

private theorem circleMap_direction (i : Fin 4) (p : P) :
    fderiv ℝ circleMap p (Pi.single i 1)=
      ![delta i 2+Real.exp (p 3)*horizontalCoefficient i (select p),
        Real.exp (p 3)*verticalCoefficient i (select p)] := by
  have hO := (off_smooth.differentiable (by simp) (select p)).hasFDerivAt.comp p select.hasFDerivAt
  have hH := (hei_smooth.differentiable (by simp) (select p)).hasFDerivAt.comp p select.hasFDerivAt
  have hE := (hasFDerivAt_apply (𝕜 := ℝ) 3 p).exp
  have hx := (hasFDerivAt_apply (𝕜 := ℝ) 2 p).add (hE.mul hO)
  have hy := hE.mul hH
  let Lx : P →L[ℝ] ℝ := ContinuousLinearMap.proj 2 +
    (Real.exp (p 3) • (fderiv ℝ off (select p)).comp select +
      off (select p) • Real.exp (p 3) • ContinuousLinearMap.proj 3)
  let Ly : P →L[ℝ] ℝ := Real.exp (p 3) • (fderiv ℝ hei (select p)).comp select +
    hei (select p) • Real.exp (p 3) • ContinuousLinearMap.proj 3
  have hm : HasFDerivAt circleMap (ContinuousLinearMap.pi ![Lx,Ly]) p := by
    apply hasFDerivAt_pi.mpr
    intro j
    fin_cases j
    · change HasFDerivAt (fun z : P => z 2+Real.exp (z 3)*offset (z 0) (z 1)) Lx p
      simpa only [Function.comp_def,Pi.add_apply,Pi.mul_apply,select_apply,off,Lx] using! hx
    · change HasFDerivAt (fun z : P => Real.exp (z 3)*height (z 0) (z 1)) Ly p
      simpa only [Function.comp_def,Pi.mul_apply,select_apply,hei,Ly] using! hy
  rw [hm.fderiv]
  ext j
  fin_cases j <;> fin_cases i <;> simp [Lx,Ly,ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,
    horizontalCoefficient,verticalCoefficient,rdiff,direction,delta]
  all_goals ring

private theorem linear_coordinates (L : C →L[ℝ] ℂ) (v : C) :
    L v=(v 0:ℂ)*L (Pi.single 0 1)+(v 1:ℂ)*L (Pi.single 1 1) := by
  rw [pi_eq_sum_univ' v,map_sum]
  simp [Fin.sum_univ_two,Complex.real_smul]
private theorem D_pullJet (u : ℂ) (word : List (Fin 2)) (i : Fin 4) (p : P) :
    D i (pullJet u word) p=(delta i 2:ℂ)*pullJet u (0::word) p+
      heightMonomial 1 p*((horizontalCoefficient i (select p):ℂ)*pullJet u (0::word) p+
        (verticalCoefficient i (select p):ℂ)*pullJet u (1::word) p) := by
  have hf := ((squareRemainder_jet_smooth u word).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds (circleMap_pos p))).differentiableAt
      (by simp)
  unfold D coordDeriv pullJet
  have h := hf.hasFDerivAt.comp p (circleMap_smooth.differentiable (by simp) p).hasFDerivAt
  simp only [Function.comp_def] at h
  rw [h.fderiv,ContinuousLinearMap.comp_apply,circleMap_direction,linear_coordinates]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,
    coordinateJet,coordDeriv,heightMonomial,Nat.cast_one,one_mul,← Complex.ofReal_exp]
  push_cast
  ring

private theorem heightMonomial_succ (m : ℕ) (p : P) :
    heightMonomial m p*heightMonomial 1 p=heightMonomial (m+1) p := by
  unfold heightMonomial
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private def nextCoefficient (i : Fin 4) (m : ℕ) (c : C → ℂ) (z : C) : ℂ :=
  cdiff i c z+(delta i 3:ℂ)*(m:ℂ)*c z
private theorem nextCoefficient_smooth (i : Fin 4) (m : ℕ) {c : C → ℂ}
    (hc : ContDiff ℝ ∞ c) : ContDiff ℝ ∞ (nextCoefficient i m c) :=
  (cdiff_smooth i hc).add (contDiff_const.mul hc)

private theorem D_term (u : ℂ) (m : ℕ) (word : List (Fin 2)) (c : C → ℂ)
    (hc : ContDiff ℝ ∞ c) (i : Fin 4) (p : P) :
    D i (term u m word c) p=
      term u m word (nextCoefficient i m c) p+
      term u m (0::word) (fun z => (delta i 2:ℂ)*c z) p+
      term u (m+1) (0::word) (fun z => c z*(horizontalCoefficient i z:ℂ)) p+
      term u (m+1) (1::word) (fun z => c z*(verticalCoefficient i z:ℂ)) p := by
  have hcs : ContDiff ℝ ∞ (fun z : P => c (select z)) := by
    simpa only [Function.comp_def] using hc.comp select.contDiff
  unfold term
  rw [D_mul (hcs.mul (heightMonomial_smooth m)) (pullJet_smooth u word),
    D_mul hcs (heightMonomial_smooth m),D_coefficient hc,
    D_heightMonomial,D_pullJet]
  dsimp [nextCoefficient]
  linear_combination
    (c (select p)*((horizontalCoefficient i (select p):ℂ)*pullJet u (0::word) p+
      (verticalCoefficient i (select p):ℂ)*pullJet u (1::word) p))*heightMonomial_succ m p

private inductive Represented (u : ℂ) : Field → Prop
  | term (m : ℕ) (word : List (Fin 2)) (c : C → ℂ) (hc : ContDiff ℝ ∞ c) :
      Represented u (term u m word c)
  | add {f g : Field} : Represented u f → Represented u g → Represented u (fun p => f p+g p)
  | congr {f g : Field} : Represented u f → f=g → Represented u g

private theorem Represented.smooth {u : ℂ} {f : Field} (h : Represented u f) : ContDiff ℝ ∞ f := by
  induction h with
  | term m word c hc => exact term_smooth u m word c hc
  | add _ _ hf hg => exact hf.add hg
  | congr _ he hf => simpa only [← he] using hf

private theorem Represented.derivative {u : ℂ} {f : Field} (h : Represented u f) (i : Fin 4) :
    Represented u (D i f) := by
  induction h with
  | term m word c hc =>
      apply (Represented.add (Represented.add (Represented.add
        (Represented.term m word (nextCoefficient i m c) (nextCoefficient_smooth i m hc))
        (Represented.term m (0::word) (fun z => (delta i 2:ℂ)*c z) (contDiff_const.mul hc)))
        (Represented.term (m+1) (0::word) (fun z => c z*(horizontalCoefficient i z:ℂ))
          (hc.mul (Complex.ofRealCLM.contDiff.comp (horizontalCoefficient_smooth i)))))
        (Represented.term (m+1) (1::word) (fun z => c z*(verticalCoefficient i z:ℂ))
          (hc.mul (Complex.ofRealCLM.contDiff.comp (verticalCoefficient_smooth i))))).congr
      funext p
      exact (D_term u m word c hc i p).symm
  | add hf hg ihf ihg =>
      apply (Represented.add ihf ihg).congr
      funext p
      exact (D_add hf.smooth hg.smooth i p).symm
  | congr hf he ih => simpa only [← he] using ih

private theorem circle_height_lower (p : P) (hd : 0 ≤ p 0) :
    Real.exp (p 3-p 0) ≤ circleMap p 1 := by
  have hu : denominator (p 0) (p 1) ≤ Real.exp (p 0) := by
    rw [← Real.cosh_add_sinh]
    have hs := Real.sinh_nonneg_iff.mpr hd
    dsimp [denominator]
    nlinarith [Real.neg_one_le_cos (p 1)]
  rw [Real.exp_sub]
  change Real.exp (p 3)/Real.exp (p 0) ≤ Real.exp (p 3)*(1/denominator (p 0) (p 1))
  rw [← div_eq_mul_one_div]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (denominator_pos _ _) hu

private theorem pullJet_bound (u : ℂ) (word : List (Fin 2)) (N : ℕ) (radius : Ici (0:ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : P, 0 ≤ p 0 → p 0 ≤ radius.val → radius.val ≤ p 3 →
      ‖pullJet u word p‖ ≤ B*Real.exp ((N:ℝ)*(radius.val-p 3)) := by
  obtain ⟨B,hB,hb⟩ := squareRemainder_jet_weighted_bound u (N:ℂ) word ⟨1,by norm_num⟩
  refine ⟨B,hB,?_⟩
  intro p hd hr hk
  have hlow : Real.exp (p 3-radius.val) ≤ circleMap p 1 :=
    (Real.exp_le_exp.mpr (by linarith)).trans (circle_height_lower p hd)
  have hz : 1 ≤ circleMap p 1 :=
    (Real.one_le_exp_iff.mpr (sub_nonneg.mpr hk)).trans hlow
  have h := hb (circleMap p) hz
  rw [norm_mul,Complex.cpow_natCast,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (circleMap_pos p)] at h
  have he : Real.exp ((N:ℝ)*(p 3-radius.val)) ≤ (circleMap p 1)^N := by
    rw [Real.exp_nat_mul]
    gcongr
  have hp : Real.exp ((N:ℝ)*(p 3-radius.val))*‖pullJet u word p‖ ≤ B :=
    (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans h
  have ht : ‖pullJet u word p‖ ≤ B/Real.exp ((N:ℝ)*(p 3-radius.val)) :=
    (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hp)
  convert ht using 1
  rw [div_eq_mul_inv,← Real.exp_neg]
  congr 2
  ring

private theorem Represented.bound {u : ℂ} {f : Field} (h : Represented u f)
    (N : ℕ) (radius : Ici (0:ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : P, 0 ≤ p 0 → p 0 ≤ radius.val →
      p 1 ∈ Icc 0 (2*Real.pi) → radius.val ≤ p 3 →
      ‖f p‖ ≤ B*Real.exp ((N:ℝ)*(radius.val-p 3)) := by
  induction h with
  | term m word c hc =>
      have hc' : Continuous (fun z : ℝ × ℝ => c ![z.1,z.2]) :=
        hc.continuous.comp (by fun_prop)
      obtain ⟨A,hA⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
        (hc'.continuousOn : ContinuousOn (fun z : ℝ × ℝ => c ![z.1,z.2])
          (Icc 0 radius.val ×ˢ Icc 0 (2*Real.pi)))
      obtain ⟨B,hB,hb⟩ := pullJet_bound u word (N+m) radius
      refine ⟨max 0 A*B*Real.exp ((m:ℝ)*radius.val),by positivity,?_⟩
      intro p hd hr htheta hk
      have hcoef : ‖c (select p)‖ ≤ max 0 A :=
        by simpa only [select_apply] using
          (hA (p 0,p 1) ⟨⟨hd,hr⟩,htheta⟩).trans (le_max_right 0 A)
      have hm : ‖heightMonomial m p‖=Real.exp ((m:ℝ)*p 3) := by
        simp [heightMonomial,Complex.norm_exp,Complex.mul_re]
      have hexp : Real.exp ((m:ℝ)*p 3)*Real.exp (((N+m:ℕ):ℝ)*(radius.val-p 3))=
          Real.exp ((m:ℝ)*radius.val)*Real.exp ((N:ℝ)*(radius.val-p 3)) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        push_cast
        ring
      change ‖c (select p)*heightMonomial m p*pullJet u word p‖ ≤ _
      rw [norm_mul,norm_mul,hm]
      calc
        _ ≤ (max 0 A*Real.exp ((m:ℝ)*p 3))*(B*Real.exp (((N+m:ℕ):ℝ)*(radius.val-p 3))) := by
          gcongr
          exact hb p hd hr hk
        _ = (max 0 A*B)*(Real.exp ((m:ℝ)*p 3)*Real.exp (((N+m:ℕ):ℝ)*(radius.val-p 3))) := by ring
        _ = _ := by rw [hexp]; ring
  | add hf hg ihf ihg =>
      obtain ⟨A,hA,ha⟩ := ihf
      obtain ⟨B,hB,hb⟩ := ihg
      refine ⟨A+B,add_nonneg hA hB,?_⟩
      intro p hd hr htheta hk
      exact (norm_add_le _ _).trans ((add_le_add (ha p hd hr htheta hk)
        (hb p hd hr htheta hk)).trans_eq (by ring))
  | congr hf he ih => simpa only [← he] using ih

private abbrev Q := Fin 3 → ℝ
private def insertTheta (p : Q) (theta : ℝ) : P := ![p 0,theta,p 1,p 2]
private def insertLinear : Q →L[ℝ] P :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,0,ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 2]
private def embed (i : Fin 3) : Fin 4 := ![0,2,3] i
private def meanField (F : Field) (p : Q) : ℂ := average (fun theta => F (insertTheta p theta))
private def partialMap (F : Field) (p : Q) (theta : ℝ) : Q →L[ℝ] ℂ :=
  (fderiv ℝ F (insertTheta p theta)).comp insertLinear

private theorem insertTheta_smooth : ContDiff ℝ ∞ (fun z : Q × ℝ => insertTheta z.1 z.2) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> dsimp [insertTheta] <;> fun_prop
private theorem insertTheta_derivative (theta : ℝ) (p : Q) :
    HasFDerivAt (fun q => insertTheta q theta) insertLinear p := by
  apply hasFDerivAt_pi.mpr
  intro j
  fin_cases j
  · exact hasFDerivAt_apply (𝕜 := ℝ) 0 p
  · exact hasFDerivAt_const theta p
  · exact hasFDerivAt_apply (𝕜 := ℝ) 1 p
  · exact hasFDerivAt_apply (𝕜 := ℝ) 2 p
private theorem partialMap_smooth {F : Field} (hf : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun z : Q × ℝ => partialMap F z.1 z.2) :=
  ((hf.fderiv_right (by simp)).comp insertTheta_smooth).clm_comp contDiff_const
private theorem partialMap_derivative {F : Field} (hf : ContDiff ℝ ∞ F) (p : Q) (theta : ℝ) :
    HasFDerivAt (fun q => F (insertTheta q theta)) (partialMap F p theta) p := by
  have h := (hf.differentiable (by simp) (insertTheta p theta)).hasFDerivAt.comp p
    (insertTheta_derivative theta p)
  simpa only [Function.comp_def,partialMap] using h
private theorem partialMap_integrable {F : Field} (hf : ContDiff ℝ ∞ F) (p : Q) :
    Integrable (partialMap F p) (volume.restrict (Ioc 0 (2*Real.pi))) := by
  have hc : Continuous (partialMap F p) :=
    (partialMap_smooth hf).continuous.comp (continuous_const.prodMk continuous_id)
  exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem meanField_derivative {F : Field} (hf : ContDiff ℝ ∞ F) (p : Q) :
    HasFDerivAt (meanField F)
      ((1/(2*Real.pi:ℂ)) • ∫ theta in Ioc 0 (2*Real.pi), partialMap F p theta) p := by
  have hc : Continuous (fun z : Q × ℝ => F (insertTheta z.1 z.2)) :=
    hf.continuous.comp insertTheta_smooth.continuous
  have hd := (partialMap_smooth hf).continuous
  obtain ⟨A,hA⟩ := ((isCompact_closedBall p 1).prod isCompact_Icc).exists_bound_of_continuousOn
    (hd.continuousOn : ContinuousOn (fun z : Q × ℝ => partialMap F z.1 z.2)
      (Metric.closedBall p 1 ×ˢ Icc 0 (2*Real.pi)))
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Ioc 0 (2*Real.pi)))
    (F := fun q theta => F (insertTheta q theta)) (F' := partialMap F)
    (s := Metric.closedBall p 1) (bound := fun _ => A)
    (Metric.closedBall_mem_nhds p (by norm_num))
    (Eventually.of_forall (fun q =>
      ((hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).restrict))
    ((hc.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (((hd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).restrict)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with theta htheta
        intro q hq
        exact hA (q,theta) ⟨hq,⟨htheta.1.le,htheta.2⟩⟩)
    (integrable_const A)
    (Eventually.of_forall (fun theta q _ => partialMap_derivative hf q theta))
  exact h.const_mul (1/(2*Real.pi:ℂ))

private theorem meanField_coordinate_derivative {F : Field} (hf : ContDiff ℝ ∞ F)
    (i : Fin 3) (p : Q) :
    coordDeriv i (meanField F) p=meanField (D (embed i) F) p := by
  unfold coordDeriv
  rw [(meanField_derivative hf p).fderiv]
  simp only [smul_apply,smul_eq_mul]
  rw [ContinuousLinearMap.integral_apply (partialMap_integrable hf p)]
  unfold meanField D4BMNativeCircle.average
  congr 1
  apply integral_congr_ae
  filter_upwards with theta
  have he : insertLinear (Pi.single i 1)=Pi.single (embed i) 1 := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [insertLinear,embed]
  simp only [partialMap,ContinuousLinearMap.comp_apply,he,D,coordDeriv]

/-- Actual ordered radius/horizontal/log-height derivatives of a native field. -/
def nativeJet : List (Fin 3) → (Q → ℂ) → Q → ℂ
  | [], f => f
  | i::word, f => coordDeriv i (nativeJet word f)
/-- Ordered actual integrand derivatives corresponding to radius and base-coordinate jets. -/
def nativeIntegrandJet : List (Fin 3) → Field → Field
  | [], F => F
  | i::word, F => D (embed i) (nativeIntegrandJet word F)
private theorem Represented.jet {u : ℂ} {F : Field} (h : Represented u F) (word : List (Fin 3)) :
    Represented u (nativeIntegrandJet word F) := by
  induction word with
  | nil => exact h
  | cons i word ih => exact ih.derivative (embed i)
private theorem jet_meanField {u : ℂ} {F : Field} (h : Represented u F) (word : List (Fin 3)) :
    nativeJet word (meanField F)=meanField (nativeIntegrandJet word F) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      change coordDeriv i (nativeJet word (meanField F))=meanField (D (embed i) (nativeIntegrandJet word F))
      rw [ih]
      funext p
      exact meanField_coordinate_derivative (h.jet word).smooth i p

/-- The full source remainder at the original hyperbolic circle point, with its half-square normalization. -/
def circleRemainder (q : XiZeroCopy) (p : P) : ℂ :=
  squareRemainder (D4BMGlobalAngularResponse.center q) (circleMap p)/2
private theorem circleRemainder_represented (q : XiZeroCopy) :
    Represented (D4BMGlobalAngularResponse.center q) (circleRemainder q) := by
  apply (Represented.term 0 [] (fun _ => (1/2:ℂ)) contDiff_const).congr
  funext p
  simp [term,heightMonomial,pullJet,coordinateJet,circleRemainder]
  ring
private theorem circleRemainder_mean (q : XiZeroCopy) :
    meanField (circleRemainder q)=fun p : Q => cuspMeanRemainder q (p 0) (p 1) (p 2) := by
  funext p
  exact (cuspMeanRemainder_integral q (p 0) (p 1) (p 2)).symm

/-- Every native derivative is the integral of the corresponding actual
integrand derivative. Both original measure and full remainder are retained. -/
theorem nativeCuspJet_integral (q : XiZeroCopy) (word : List (Fin 3)) (d x k : ℝ) :
    nativeJet word (fun p => cuspMeanRemainder q (p 0) (p 1) (p 2)) ![d,x,k]=
      average (fun theta => nativeIntegrandJet word (circleRemainder q) ![d,theta,x,k]) := by
  rw [← circleRemainder_mean,jet_meanField (circleRemainder_represented q)]
  rfl

private theorem average_norm_le {f : ℝ → ℂ} {B : ℝ}
    (hb : ∀ theta ∈ Icc 0 (2*Real.pi), ‖f theta‖ ≤ B) : ‖average f‖ ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc 0 (2*Real.pi)))
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with theta htheta
        exact hb theta ⟨htheta.1.le,htheta.2⟩)
  have hm : (volume.restrict (Ioc 0 (2*Real.pi))).real Set.univ=2*Real.pi := by
    simp [Measure.real,Real.volume_Ioc,Real.pi_pos.le]
  rw [hm] at h
  unfold D4BMNativeCircle.average
  rw [norm_mul,norm_div,norm_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ ≤ (1/(2*Real.pi))*(B*(2*Real.pi)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = B := by field_simp

/-- All radius/base-coordinate jets of the original native cusp remainder have
arbitrary decay order, uniformly in horizontal position and compact radius. -/
theorem nativeCuspJet_rapid_bound (q : XiZeroCopy) (word : List (Fin 3))
    (N : ℕ) (radius : Ici (0:ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ d x k : ℝ, 0 ≤ d → d ≤ radius.val → radius.val ≤ k →
      ‖nativeJet word (fun p => cuspMeanRemainder q (p 0) (p 1) (p 2)) ![d,x,k]‖ ≤
        B*Real.exp ((N:ℝ)*(radius.val-k)) := by
  obtain ⟨B,hB,hb⟩ := ((circleRemainder_represented q).jet word).bound N radius
  refine ⟨B,hB,?_⟩
  intro d x k hd hr hk
  rw [nativeCuspJet_integral]
  apply average_norm_le
  intro theta htheta
  exact hb ![d,theta,x,k] hd hr htheta hk

/-- Every inverse-height-weighted native jet vanishes even along arbitrary
horizontal and compact-radius paths. No regularity or convergence of the paths is assumed. -/
theorem nativeCuspJet_weighted_tendsto_zero (q : XiZeroCopy) (word : List (Fin 3))
    (N : ℕ) (radius : Ici (0:ℝ)) (path : ℝ → Icc 0 radius.val) (X : ℝ → ℝ) :
    Tendsto (fun k : ℝ => (Real.exp ((N:ℝ)*k):ℂ)*
      nativeJet word (fun p => cuspMeanRemainder q (p 0) (p 1) (p 2)) ![(path k).val,X k,k])
      atTop (𝓝 0) := by
  obtain ⟨B,hB,hb⟩ := nativeCuspJet_rapid_bound q word (N+1) radius
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
    (B*Real.exp (((N+1:ℕ):ℝ)*radius.val))
  apply squeeze_zero_norm' _ (by simpa using ht)
  filter_upwards [eventually_ge_atTop radius.val] with k hk
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp ((N:ℝ)*k)*(B*Real.exp (((N+1:ℕ):ℝ)*(radius.val-k))) := by
      gcongr
      exact hb (path k).val (X k) k (path k).property.1 (path k).property.2 hk
    _ = B*Real.exp (((N:ℝ)+1)*radius.val)*Real.exp (-k) := by
      have he : Real.exp ((N:ℝ)*k)*Real.exp (((N+1:ℕ):ℝ)*(radius.val-k))=
          Real.exp (((N:ℝ)+1)*radius.val)*Real.exp (-k) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        push_cast
        ring
      calc
        _ = B*(Real.exp ((N:ℝ)*k)*Real.exp (((N+1:ℕ):ℝ)*(radius.val-k))) := by ring
        _ = _ := by rw [he]; ring

end
end RHTower.D4BMNativeCuspJets

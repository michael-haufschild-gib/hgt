import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCuspJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeAngularGreen
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCausalSourceAdjoint
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCircleGauss

/-! The full native angular Green density and all three original cusp channels. -/
open Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMNativeAngularCurrent
open D4BMNativeCircle D4BMJointSource D4BMNativeCuspJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
private abbrev Point := Fin 3 → ℝ
private abbrev Field := Point → ℂ
private abbrev D := @coordDeriv 3

private def E (a : ℂ) (p : Point) : ℂ := Complex.exp (a*(p 2:ℂ))
private theorem E_smooth (a : ℂ) : ContDiff ℝ ∞ (E a) := by
  unfold E
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (contDiff_apply ℝ ℝ (2:Fin 3)))).cexp
private theorem E_mul (a b : ℂ) (p : Point) : E a p*E b p=E (a+b) p := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  ring
private theorem D_E (a : ℂ) (i : Fin 3) (p : Point) :
    D i (E a) p=if i=2 then a*E a p else 0 := by
  have hc := (Complex.ofRealCLM.hasFDerivAt).comp p (hasFDerivAt_apply (𝕜 := ℝ) 2 p)
  have he := (hc.const_mul a).cexp
  have he' : HasFDerivAt (E a)
      (E a p • a • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 2)) p := by
    simpa only [E, Function.comp_def, Complex.ofRealCLM_apply] using! he
  change fderiv ℝ (E a) p (Pi.single i 1) = _
  rw [he'.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  fin_cases i <;> simp
  ring
private theorem D_mul {f g : Field} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin 3) (p : Point) :
    D i (fun z => f z*g z) p=D i f p*g p+f p*D i g p := by
  simp only [D,coordDeriv,fderiv_fun_mul (hf.differentiable (by simp) p)
    (hg.differentiable (by simp) p),add_apply,smul_apply,smul_eq_mul]
  ring
private theorem D_sub {f g : Field} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin 3) (p : Point) :
    D i (fun z => f z-g z) p=D i f p-D i g p := by
  simp only [D,coordDeriv,fderiv_fun_sub (hf.differentiable (by simp) p)
    (hg.differentiable (by simp) p),sub_apply]
private theorem D_smooth {f : Field} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (D i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem circle_smooth (a : ℂ) : ContDiff ℝ ∞ (powerCircle a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro d
  have h := (D4BMCausalSourceKernel.legendre_contDiffAt (-a) (Real.cosh_pos d)).comp d
    (show ContDiffAt ℝ ∞ Real.cosh d by fun_prop)
  simpa only [Function.comp_def,← powerCircle_eq_legendre] using h

/-- Actual logarithmic-height derivatives of the three transported principal powers. -/
def principalJet (q : XiZeroCopy) (n : ℕ) (p : Point) : ℂ :=
  ∑ i : Fin 3, principalAmplitude q i*(principalExponent q i)^n*
    powerCircle (principalExponent q i) (p 0)*E (principalExponent q i) p

private theorem coefficient_smooth (q : XiZeroCopy) (n : ℕ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun d => principalAmplitude q i*(principalExponent q i)^n*
      powerCircle (principalExponent q i) d) :=
  contDiff_const.mul (circle_smooth _)
private theorem term_smooth (q : XiZeroCopy) (n : ℕ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun p : Point => principalAmplitude q i*(principalExponent q i)^n*
      powerCircle (principalExponent q i) (p 0)*E (principalExponent q i) p) :=
  ((coefficient_smooth q n i).comp (contDiff_apply ℝ ℝ (0:Fin 3))).mul (E_smooth _)
private theorem principal_smooth (q : XiZeroCopy) (n : ℕ) : ContDiff ℝ ∞ (principalJet q n) := by
  unfold principalJet
  exact ContDiff.sum (fun i _ => term_smooth q n i)
private theorem coefficient_derivative {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c)
    (i : Fin 3) (p : Point) : D i (fun z => c (z 0)) p=if i=0 then deriv c (p 0) else 0 := by
  have hd := (hc.differentiable (by simp) (p 0)).hasDerivAt.hasFDerivAt.comp p
    (hasFDerivAt_apply (𝕜 := ℝ) 0 p)
  have he := congrArg (fun T : Point →L[ℝ] ℂ => T (Pi.single i 1)) hd.fderiv
  fin_cases i <;> simpa [D,Function.comp_def] using! he
private theorem principal_derivatives (q : XiZeroCopy) (n : ℕ) (p : Point) :
    D 1 (principalJet q n) p=0 ∧ D 2 (principalJet q n) p=principalJet q (n+1) p := by
  have hd (j : Fin 3) : D j (principalJet q n) p=
      ∑ i : Fin 3, D j (fun z : Point => principalAmplitude q i*(principalExponent q i)^n*
        powerCircle (principalExponent q i) (z 0)*E (principalExponent q i) z) p := by
    unfold D coordDeriv principalJet
    rw [fderiv_fun_sum (fun i _ => (term_smooth q n i).differentiable (by simp) p)]
    simp
  have ht (i j : Fin 3) : D j (fun z : Point => principalAmplitude q i*(principalExponent q i)^n*
      powerCircle (principalExponent q i) (z 0)*E (principalExponent q i) z) p =
      (if j=0 then deriv (fun d => principalAmplitude q i*(principalExponent q i)^n*
        powerCircle (principalExponent q i) d) (p 0) else 0)*E (principalExponent q i) p+
      (principalAmplitude q i*(principalExponent q i)^n*powerCircle (principalExponent q i) (p 0))*
        (if j=2 then principalExponent q i*E (principalExponent q i) p else 0) := by
    have hc : ContDiff ℝ ∞ (fun z : Point => principalAmplitude q i*(principalExponent q i)^n*
        powerCircle (principalExponent q i) (z 0)) := by
      simpa only [Function.comp_def] using!
        (coefficient_smooth q n i).comp (contDiff_apply ℝ ℝ (0:Fin 3))
    rw [D_mul hc (E_smooth _)]
    rw [coefficient_derivative (coefficient_smooth q n i),D_E]
  constructor
  · simp only [hd,ht]
    simp
  · rw [hd]
    simp only [ht,show (2:Fin 3) ≠ 0 by decide,if_false,zero_mul,ite_true,zero_add]
    unfold principalJet
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring

private theorem exp_cpow (a : ℂ) (k : ℝ) : (Real.exp k:ℂ)^a=Complex.exp (a*(k:ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos k).ne'),
    ← Complex.ofReal_log (Real.exp_pos k).le,Real.log_exp]
  congr 1
  ring
private theorem principal_zero (q : XiZeroCopy) :
    principalJet q 0=fun p => transportedPrincipal q (p 0) (p 2) := by
  funext p
  simp only [principalJet,transportedPrincipal,pow_zero,mul_one,exp_cpow,E]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The original full theta-source native mean on radius/horizontal/log-height coordinates. -/
def nativeField (q : XiZeroCopy) (p : Point) : ℂ := mean q (p 0) (p 1) (p 2)
/-- The entire native remainder after exactly the original three cusp powers. -/
def nativeRemainder (q : XiZeroCopy) (p : Point) : ℂ := cuspMeanRemainder q (p 0) (p 1) (p 2)
private theorem full_smooth (q : XiZeroCopy) : ContDiff ℝ ∞ (nativeField q) := by
  have h := (D4BMNativeResponse.nativeMean_joint_smooth q).comp
    (show ContDiff ℝ ∞ (fun p : Point => (p 0,p 1,p 2)) by fun_prop)
  simpa only [nativeField,Function.comp_def] using! h
private theorem rem_eq (q : XiZeroCopy) : nativeRemainder q=fun p => nativeField q p-principalJet q 0 p := by
  rw [principal_zero]
  rfl
private theorem rem_smooth (q : XiZeroCopy) : ContDiff ℝ ∞ (nativeRemainder q) := by
  rw [rem_eq]
  exact (full_smooth q).sub (principal_smooth q 0)

/-- Exact first and second angular derivatives of the original full native source. -/
theorem native_angular_jet_decomposition (q : XiZeroCopy) (p : Point) :
    nativeJet [2] (nativeField q) p=principalJet q 1 p+nativeJet [2] (nativeRemainder q) p ∧
    nativeJet [2,2] (nativeField q) p=principalJet q 2 p+nativeJet [2,2] (nativeRemainder q) p ∧
    nativeJet [1,1] (nativeField q) p=nativeJet [1,1] (nativeRemainder q) p := by
  have h1 : D 2 (nativeRemainder q)=fun z => D 2 (nativeField q) z-principalJet q 1 z := by
    funext z
    rw [rem_eq,D_sub (full_smooth q) (principal_smooth q 0), (principal_derivatives q 0 z).2]
  have hx : D 1 (nativeRemainder q)=D 1 (nativeField q) := by
    funext z
    rw [rem_eq,D_sub (full_smooth q) (principal_smooth q 0),(principal_derivatives q 0 z).1,sub_zero]
  change D 2 (nativeField q) p=principalJet q 1 p+D 2 (nativeRemainder q) p ∧
    D 2 (D 2 (nativeField q)) p=principalJet q 2 p+D 2 (D 2 (nativeRemainder q)) p ∧
    D 1 (D 1 (nativeField q)) p=D 1 (D 1 (nativeRemainder q)) p
  rw [h1,D_sub (D_smooth (full_smooth q) 2) (principal_smooth q 1),
    (principal_derivatives q 1 p).2,hx]
  exact ⟨by ring,by ring,rfl⟩

/-- Original vertical angular Green density in the native logarithmic-height chart.
The factors exp(k) and exp(-k) retain the height Jacobian. -/
def verticalGreen (q : XiZeroCopy) (d e X k : ℝ) : ℂ :=
  E 1 ![d,X,k]*(nativeJet [2] (nativeField q) ![d,X,k]*nativeJet [1,1] (nativeField q) ![e,X,k]-
    nativeJet [2] (nativeField q) ![e,X,k]*nativeJet [1,1] (nativeField q) ![d,X,k])+
  E (-1) ![d,X,k]*(nativeJet [2] (nativeField q) ![d,X,k]*nativeJet [2,2] (nativeField q) ![e,X,k]-
    nativeJet [2] (nativeField q) ![e,X,k]*nativeJet [2,2] (nativeField q) ![d,X,k])

/-- The exact principal boundary contribution; no finite-part prescription is applied. -/
def principalFlux (q : XiZeroCopy) (d e X k : ℝ) : ℂ :=
  E (-1) ![d,X,k]*(principalJet q 1 ![d,X,k]*principalJet q 2 ![e,X,k]-
    principalJet q 1 ![e,X,k]*principalJet q 2 ![d,X,k])

/-- Coefficient of the antisymmetric interaction of two original cusp powers. -/
def pairCoefficient (q : XiZeroCopy) (i j : Fin 3) (d e : ℝ) : ℂ :=
  principalAmplitude q i*principalAmplitude q j*principalExponent q i*principalExponent q j*
    (principalExponent q j-principalExponent q i)*
    (powerCircle (principalExponent q i) d*powerCircle (principalExponent q j) e-
      powerCircle (principalExponent q j) d*powerCircle (principalExponent q i) e)

private theorem triple_exp (a b k : ℂ) :
    Complex.exp (-k)*Complex.exp (a*k)*Complex.exp (b*k)=Complex.exp ((a+b-1)*k) := by
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  ring

/-- All three principal cusp interactions survive explicitly, with exponents
2q, 1 and 2-2q; every completed amplitude and both native radii are retained. -/
theorem principalFlux_three_channels (q : XiZeroCopy) (d e X k : ℝ) :
    principalFlux q d e X k=
      pairCoefficient q 0 1 d e*Complex.exp (2*(q.1:ℂ)*(k:ℂ))+
      pairCoefficient q 0 2 d e*Complex.exp (k:ℂ)+
      pairCoefficient q 1 2 d e*Complex.exp ((2-2*(q.1:ℂ))*(k:ℂ)) := by
  have hbase : principalFlux q d e X k=
      pairCoefficient q 0 1 d e*(Complex.exp (-(k:ℂ))*
        Complex.exp (principalExponent q 0*(k:ℂ))*Complex.exp (principalExponent q 1*(k:ℂ)))+
      pairCoefficient q 0 2 d e*(Complex.exp (-(k:ℂ))*
        Complex.exp (principalExponent q 0*(k:ℂ))*Complex.exp (principalExponent q 2*(k:ℂ)))+
      pairCoefficient q 1 2 d e*(Complex.exp (-(k:ℂ))*
        Complex.exp (principalExponent q 1*(k:ℂ))*Complex.exp (principalExponent q 2*(k:ℂ))) := by
    simp only [principalFlux,principalJet,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
      E,pairCoefficient,Matrix.cons_val_zero,Matrix.cons_val,
      pow_one,neg_one_mul,
      show (Fin.succ (0:Fin 2):Fin 3)=1 by rfl,
      show (Fin.succ (Fin.succ (0:Fin 1)):Fin 3)=2 by rfl]
    ring
  rw [hbase]
  simp only [triple_exp]
  have h01 : principalExponent q 0+principalExponent q 1-1=2*(q.1:ℂ) := by
    simp [principalExponent]
  have h02 : principalExponent q 0+principalExponent q 2-1=1 := by
    change 2*(q.1:ℂ)+(2-2*(q.1:ℂ))-1=1
    ring
  have h12 : principalExponent q 1+principalExponent q 2-1=2-2*(q.1:ℂ) := by
    change 1+(2-2*(q.1:ℂ))-1=2-2*(q.1:ℂ)
    ring
  rw [h01,h02,h12,one_mul]

/-- Complex-weighted decay of every actual native remainder derivative, with
the full signed source and arbitrary horizontal path retained. -/
theorem weighted_native_remainder_tendsto_zero (q : XiZeroCopy) (word : List (Fin 3))
    (d : Ici (0:ℝ)) (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*nativeJet word (nativeRemainder q) ![d.val,X k,k])
      atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt w.re
  obtain ⟨B,hB,hb⟩ := nativeCuspJet_rapid_bound q word N d
  have ht := Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (sub_neg.mpr hN)).2 tendsto_id)
  apply squeeze_zero_norm' _ (by simpa using ht.const_mul (B*Real.exp ((N:ℝ)*d.val)))
  filter_upwards [eventually_ge_atTop d.val] with k hk
  rw [norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  calc
    _ ≤ Real.exp (w.re*k)*(B*Real.exp ((N:ℝ)*(d.val-k))) := by
      gcongr
      exact hb d.val (X k) k d.property le_rfl hk
    _ = B*Real.exp ((N:ℝ)*d.val)*Real.exp ((w.re-(N:ℝ))*k) := by
      have he : Real.exp (w.re*k)*Real.exp ((N:ℝ)*(d.val-k))=
          Real.exp ((N:ℝ)*d.val)*Real.exp ((w.re-(N:ℝ))*k) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      calc
        _ = B*(Real.exp (w.re*k)*Real.exp ((N:ℝ)*(d.val-k))) := by ring
        _ = _ := by rw [he]; ring

private theorem principal_rem_zero (q : XiZeroCopy) (n : ℕ) (word : List (Fin 3))
    (d : ℝ) (e : Ici (0:ℝ)) (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => E w ![d,X k,k]*principalJet q n ![d,X k,k]*
      nativeJet word (nativeRemainder q) ![e.val,X k,k]) atTop (𝓝 0) := by
  have ht (i : Fin 3) := (weighted_native_remainder_tendsto_zero q word e X
    (w+principalExponent q i)).const_mul
      (principalAmplitude q i*(principalExponent q i)^n*powerCircle (principalExponent q i) d)
  have hs := tendsto_finsetSum Finset.univ (fun i _ => ht i)
  simp only [mul_zero,Finset.sum_const_zero] at hs
  convert hs using 1
  funext k
  simp only [principalJet,Finset.sum_mul,Finset.mul_sum,E,Matrix.cons_val_zero,
    Matrix.cons_val]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (w+principalExponent q i)*(k:ℂ)=w*(k:ℂ)+principalExponent q i*(k:ℂ) by ring,
    Complex.exp_add]
  ring

private theorem rem_rem_zero (q : XiZeroCopy) (a b : List (Fin 3))
    (d e : Ici (0:ℝ)) (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => E w ![d.val,X k,k]*nativeJet a (nativeRemainder q) ![d.val,X k,k]*
      nativeJet b (nativeRemainder q) ![e.val,X k,k]) atTop (𝓝 0) := by
  have h := (weighted_native_remainder_tendsto_zero q a d X w).mul
    (weighted_native_remainder_tendsto_zero q b e X 0)
  simpa only [E,Matrix.cons_val,zero_mul,Complex.exp_zero,one_mul] using h

/-- The full native angular current has precisely the three principal cusp
channels. Its complete remaining source contribution vanishes after every
complex height weight, along any horizontal path. -/
theorem verticalGreen_cusp_expansion (q : XiZeroCopy) (d e : Ici (0:ℝ))
    (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      (verticalGreen q d.val e.val (X k) k-principalFlux q d.val e.val (X k) k))
      atTop (𝓝 0) := by
  have h := (((principal_rem_zero q 1 [1,1] d.val e X (w+1)).sub
    (principal_rem_zero q 1 [1,1] e.val d X (w+1))).add
      ((rem_rem_zero q [2] [1,1] d e X (w+1)).sub
        (rem_rem_zero q [2] [1,1] e d X (w+1)))).add
    (((((principal_rem_zero q 1 [2,2] d.val e X (w-1)).add
       (principal_rem_zero q 2 [2] e.val d X (w-1))).add
       (rem_rem_zero q [2] [2,2] d e X (w-1))).sub
       ((principal_rem_zero q 1 [2,2] e.val d X (w-1)).add
        (principal_rem_zero q 2 [2] d.val e X (w-1)))).sub
        (rem_rem_zero q [2] [2,2] e d X (w-1)))
  convert h using 1
  · funext k
    obtain ⟨hd1,hd2,hdx⟩ := native_angular_jet_decomposition q ![d.val,X k,k]
    obtain ⟨he1,he2,hex⟩ := native_angular_jet_decomposition q ![e.val,X k,k]
    simp only [verticalGreen,principalFlux,hd1,hd2,hdx,he1,he2,hex,E,
      Matrix.cons_val]
    rw [show (w+1)*(k:ℂ)=w*(k:ℂ)+(k:ℂ) by ring,
      show (w-1)*(k:ℂ)=w*(k:ℂ)-(k:ℂ) by ring,Complex.exp_add,Complex.exp_sub]
    simp only [one_mul,neg_one_mul,Complex.exp_neg]
    ring
  · simp


private theorem slice_first {f : Field} (hf : ContDiff ℝ ∞ f) (i : Fin 3) (p : Point) :
    deriv (fun x => f (Function.update p i x)) (p i)=D i f p := by
  have hi : HasDerivAt (fun x : ℝ => Function.update p i x) (Pi.single i 1) (p i) := by
    apply hasDerivAt_pi.mpr
    intro j
    by_cases h : j=i
    · subst j
      simpa using! hasDerivAt_id (p i)
    · simpa [h] using! hasDerivAt_const (p i) (p j)
  have hF : HasFDerivAt f (fderiv ℝ f p) (Function.update p i (p i)) := by
    simpa only [Function.update_eq_self] using! (hf.differentiable (by simp) p).hasFDerivAt
  simpa [D,coordDeriv] using! (hF.comp_hasDerivAt (p i) hi).deriv
private theorem slice_second {f : Field} (hf : ContDiff ℝ ∞ f) (i : Fin 3) (p : Point) :
    deriv (deriv (fun x => f (Function.update p i x))) (p i)=D i (D i f) p := by
  have he : deriv (fun x => f (Function.update p i x))=fun x => D i f (Function.update p i x) := by
    funext x
    simpa using! slice_first hf i (Function.update p i x)
  rw [he,slice_first (D_smooth hf i)]
private theorem native_slices (q : XiZeroCopy) (d X k : ℝ) :
    deriv (mean q d X) k=nativeJet [2] (nativeField q) ![d,X,k] ∧
    deriv (deriv (mean q d X)) k=nativeJet [2,2] (nativeField q) ![d,X,k] ∧
    deriv (deriv (fun x => mean q d x k)) X=nativeJet [1,1] (nativeField q) ![d,X,k] := by
  have h1 (x : ℝ) : Function.update (![d,X,k]:Point) 1 x=![d,x,k] := by
    ext i
    fin_cases i <;> simp
  have h2 (x : ℝ) : Function.update (![d,X,k]:Point) 2 x=![d,X,x] := by
    ext i
    fin_cases i <;> simp
  refine ⟨?_,?_,?_⟩
  · simpa only [h2,nativeField,Matrix.cons_val,nativeJet] using slice_first (full_smooth q) 2 ![d,X,k]
  · simpa only [h2,nativeField,Matrix.cons_val,nativeJet] using slice_second (full_smooth q) 2 ![d,X,k]
  · simpa only [h1,nativeField,Matrix.cons_val,nativeJet] using slice_second (full_smooth q) 1 ![d,X,k]
private theorem log_first (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (y : ℝ) (hy : 0 < y) :
    deriv (fun r => f (Real.log r)) y=(y:ℂ)⁻¹*deriv f (Real.log y) := by
  have h := ((hf.differentiable (by simp) (Real.log y)).hasDerivAt.scomp y
    (Real.hasDerivAt_log hy.ne')).deriv
  simpa only [Function.comp_def,Complex.real_smul,Complex.ofReal_inv] using! h
private theorem log_second (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (y : ℝ) (hy : 0 < y) :
    (y:ℂ)^(2 : ℕ)*deriv (deriv (fun r => f (Real.log r))) y =
      deriv (deriv f) (Real.log y)-deriv f (Real.log y) := by
  have hf' : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hsecond := (((Complex.ofRealCLM.hasDerivAt (x := y)).inv
    (by exact_mod_cast hy.ne' : (y:ℂ)≠0)).mul
    (((hf'.differentiable (by simp)) (Real.log y)).hasDerivAt.scomp y
      (Real.hasDerivAt_log hy.ne')))
  have he : deriv (fun r => f (Real.log r)) =ᶠ[𝓝 y]
      (fun r : ℝ => (r:ℂ)⁻¹*deriv f (Real.log r)) := by
    filter_upwards [Ioi_mem_nhds hy] with r hr
    exact log_first f hf r hr
  change HasDerivAt (fun r : ℝ => (r:ℂ)⁻¹*deriv f (Real.log r)) _ y at hsecond
  rw [he.deriv_eq,hsecond.deriv]
  simp only [Pi.inv_apply,Function.comp_apply,Complex.ofRealCLM_apply,Complex.real_smul,
    Complex.ofReal_inv,Complex.ofReal_one]
  have hyc : (y:ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  field_simp [hyc]
  ring

/-- Vertical coexact Green density expressed with actual derivatives in the
original horizontal/height coordinates: F_Y Delta G-G_Y Delta F. -/
def originalVerticalGreen (q : XiZeroCopy) (d e X Y : ℝ) : ℂ :=
  deriv (fun y => mean q d X (Real.log y)) Y*
    ((Y:ℂ)^(2 : ℕ)*(deriv (deriv (fun x => mean q e x (Real.log Y))) X+
      deriv (deriv (fun y => mean q e X (Real.log y))) Y))-
  deriv (fun y => mean q e X (Real.log y)) Y*
    ((Y:ℂ)^(2 : ℕ)*(deriv (deriv (fun x => mean q d x (Real.log Y))) X+
      deriv (deriv (fun y => mean q d X (Real.log y))) Y))

/-- Exact height-coordinate dictionary for the original native angular current. -/
theorem originalVerticalGreen_eq (q : XiZeroCopy) (d e X k : ℝ) :
    originalVerticalGreen q d e X (Real.exp k)=verticalGreen q d e X k := by
  have hs (r : ℝ) : ContDiff ℝ ∞ (mean q r X) := by
    simpa only [Function.comp_def] using!
      (D4BMNativeResponse.nativeMean_joint_smooth q).comp
        (show ContDiff ℝ ∞ (fun k : ℝ => (r,X,k)) by fun_prop)
  have hl (r : ℝ) := log_second (mean q r X) (hs r) (Real.exp k) (Real.exp_pos k)
  simp only [Real.log_exp] at hl
  simp only [originalVerticalGreen,log_first _ (hs _) _ (Real.exp_pos k),Real.log_exp,
    mul_add,hl]
  obtain ⟨hd1,hd2,hdx⟩ := native_slices q d X k
  obtain ⟨he1,he2,hex⟩ := native_slices q e X k
  rw [hd1,hd2,hdx,he1,he2,hex]
  simp only [verticalGreen,E,Matrix.cons_val,one_mul,neg_one_mul,
    Complex.exp_neg,← Complex.ofReal_exp]
  have hne : (Real.exp k:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos k).ne'
  field_simp [hne]
  ring

/-- The three-channel cusp expansion holds for the actual original-height
Green current, with every remainder derivative and source mode retained. -/
theorem originalVerticalGreen_cusp_expansion (q : XiZeroCopy) (d e : Ici (0:ℝ))
    (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      (originalVerticalGreen q d.val e.val (X k) (Real.exp k)-principalFlux q d.val e.val (X k) k))
      atTop (𝓝 0) := by
  simp only [originalVerticalGreen_eq]
  exact verticalGreen_cusp_expansion q d e X w


end
end RHTower.D4BMNativeAngularCurrent

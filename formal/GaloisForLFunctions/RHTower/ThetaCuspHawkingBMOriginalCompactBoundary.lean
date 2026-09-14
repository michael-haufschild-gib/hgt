import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalContactCusp

/-!
The complete original metric boundary after compact-time cusp restoration.

All four source/physical-reader transfers have uniform three-power expansions
on every fixed `0 < a <= b`, `R > 1`, and nonreal temporal frequency. Their
coefficients retain both endpoint values, the original source Laplacian and
full forcing. The actual finite-time boundary identity therefore admits the
same three-power subtraction after time integration. For the original
diagonal/reflected angular readers its prescribed finite part is zero.

This does not take the onset, infinite-time or horizon limits. The moving
corner and full temporal/metric/QNM matching remain separate obligations.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry ScalarTwoJet
namespace RHTower.D4BMOriginalCompactBoundary
open D4BMOriginalContactCusp D4BMLeftModeRadialEquation
open D4BMJointSource D4BMOriginalAngularCurrent D4BMOriginalOrbitCurrent
open D4BMOriginalSourceContact D4BMOriginalReaderEquation D4BMOriginalOrbitCusp
open D4BMOriginalCuspFlux D4BMOriginalMetricCusp D4BMMetricReconstruction
open D4BMAngularSeries
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
private abbrev P := Fin 4 → ℝ
private abbrev A := Fin 2 → ℝ
local notation "L" => hyperbolicLaplacian

private theorem coordinate_update {n : ℕ} (f : (Fin n → ℝ) → ℂ)
    (x : Fin n → ℝ) (i : Fin n) (hf : DifferentiableAt ℝ f x) :
    coordDeriv i f x=deriv (fun a => f (Function.update x i a)) (x i) := by
  have hf' : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
    simpa only [Function.update_eq_self] using hf.hasFDerivAt
  have h := hf'.comp_hasDerivAt (x i) (hasDerivAt_update x i (x i))
  simpa only [Function.update_eq_self,coordDeriv,Function.comp_def] using h.deriv.symm

private theorem exp_cpow (a : ℂ) (k : ℝ) :
    (Real.exp k:ℂ)^a=Complex.exp (a*(k:ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos k).ne'),
    ← Complex.ofReal_log (Real.exp_pos k).le,Real.log_exp]
  congr 1
  ring

private theorem positive_nhds {z : A} (hy : 0<z 1) : domain∈𝓝 z :=
  (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hy

private theorem power_laplacian_sum {ι : Type*} (s : Finset ι) (F : ι → A → ℂ)
    {z : A} (hF : ∀ i∈s, ContDiffAt ℝ 2 (F i) z) :
    L (fun x => ∑ i∈s, F i x) z=∑ i∈s, L (F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change (z 1:ℂ)^2*(fderiv ℝ (fun x => fderiv ℝ (fun _ : A => (0:ℂ)) x (Pi.single 0 1)) z (Pi.single 0 1)+
      fderiv ℝ (fun x => fderiv ℝ (fun _ : A => (0:ℂ)) x (Pi.single 1 1)) z (Pi.single 1 1))=0
    simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hyperbolicLaplacian_add (hF i (Finset.mem_insert_self _ _))
      (ContDiffAt.sum (fun j hj => hF j (Finset.mem_insert_of_mem hj)))).trans
        (congrArg (fun a => L (F i) z+a) (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))))

private theorem principal_laplacian (q : XiZeroCopy) (z : A) (hy : 0<z 1) :
    L (principalSquare q) z=∑ i : Fin 3, principalAmplitude q i*
      principalExponent q i*(principalExponent q i-1)*(z 1:ℂ)^(principalExponent q i) := by
  have he : principalSquare q=ᶠ[𝓝 z] fun v => ∑ i : Fin 3,
      principalAmplitude q i*(v 1:ℂ)^(principalExponent q i) := by
    filter_upwards [positive_nhds hy] with v hv
    exact principalSquare_expansion q v hv
  have hs (i : Fin 3) : ContDiffAt ℝ 2
      (fun v : A => principalAmplitude q i*(v 1:ℂ)^(principalExponent q i)) z :=
    contDiffAt_const.mul ((height_cpow_contDiffOn (principalExponent q i) 2).contDiffAt (positive_nhds hy))
  rw [hyperbolicLaplacian_congr he,power_laplacian_sum Finset.univ _ (fun i _ => hs i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hyperbolicLaplacian_const_mul
    ((height_cpow_contDiffOn (principalExponent q i) 2).contDiffAt (positive_nhds hy)),
    height_cpow_hyperbolicLaplacian _ z hy]
  ring

private theorem square_decomposition (q : XiZeroCopy) :
    D4BMModularCore.fullSquarePotential q=fun z => principalSquare q z+
      (1/2:ℂ)*D4BMGlobalAngularResponse.squareRemainder (D4BMGlobalAngularResponse.center q) z := by
  funext z
  dsimp [D4BMModularCore.fullSquarePotential,principalSquare,D4BMGlobalAngularResponse.squareRemainder]
  ring

private theorem square_laplacian_decomposition (q : XiZeroCopy) (z : A) (hy : 0<z 1) :
    L (D4BMModularCore.fullSquarePotential q) z=L (principalSquare q) z+
      (1/2:ℂ)*L (D4BMGlobalAngularResponse.squareRemainder (D4BMGlobalAngularResponse.center q)) z := by
  have hp : ContDiffAt ℝ 2 (principalSquare q) z :=
    ((principalSquare_smooth q).contDiffAt (positive_nhds hy)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hs : ContDiffAt ℝ 2
      (D4BMGlobalAngularResponse.squareRemainder (D4BMGlobalAngularResponse.center q)) z :=
    ((D4BMSquareCuspJets.squareRemainder_jet_smooth (D4BMGlobalAngularResponse.center q) []).contDiffAt
      (positive_nhds hy)).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [square_decomposition q,hyperbolicLaplacian_add hp (contDiffAt_const.mul hs),
    hyperbolicLaplacian_const_mul hs]

private theorem square_jet_exp (q : XiZeroCopy) (word : List (Fin 2)) (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      D4BMSquareCuspJets.coordinateJet word
        (D4BMGlobalAngularResponse.squareRemainder (D4BMGlobalAngularResponse.center q))
        ![X k,Real.exp k]) atTop (𝓝 0) := by
  have h := (D4BMSquareCuspJets.squareRemainder_jet_tendsto_zero
    (D4BMGlobalAngularResponse.center q) w word (fun y => X (Real.log y))).comp Real.tendsto_exp_atTop
  simpa only [Function.comp_def,Real.log_exp,exp_cpow] using h

private theorem square_expansion (q : XiZeroCopy) (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      (D4BMModularCore.fullSquarePotential q ![X k,Real.exp k]-
        ∑ i : Fin 3, principalAmplitude q i*Complex.exp (principalExponent q i*(k:ℂ))))
      atTop (𝓝 0) := by
  have h := (square_jet_exp q [] X w).const_mul (1/2:ℂ)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [] with k
  rw [square_decomposition q]
  simp only [principalSquare_expansion q ![X k,Real.exp k] (Real.exp_pos k),Matrix.cons_val,exp_cpow,
    D4BMSquareCuspJets.coordinateJet]
  ring

private theorem square_laplacian_expansion (q : XiZeroCopy) (X : ℝ → ℝ) (w : ℂ) :
    Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
      (L (D4BMModularCore.fullSquarePotential q) ![X k,Real.exp k]-
        ∑ i : Fin 3, principalAmplitude q i*principalExponent q i*(principalExponent q i-1)*
          Complex.exp (principalExponent q i*(k:ℂ)))) atTop (𝓝 0) := by
  have h := ((square_jet_exp q [0,0] X (w+2)).add
    (square_jet_exp q [1,1] X (w+2))).const_mul (1/2:ℂ)
  simp only [zero_add,mul_zero] at h
  apply h.congr'
  filter_upwards [] with k
  rw [square_laplacian_decomposition q _ (Real.exp_pos k),principal_laplacian q _ (Real.exp_pos k)]
  simp only [Matrix.cons_val,exp_cpow,D4BMSquareCuspJets.coordinateJet]
  have he : Complex.exp ((w+2)*(k:ℂ))=Complex.exp (w*(k:ℂ))*(Real.exp k:ℂ)^2 := by
    rw [show (w+2)*(k:ℂ)=w*(k:ℂ)+2*(k:ℂ) by ring,Complex.exp_add,
      ← exp_cpow (2:ℂ) k,Complex.cpow_two]
  rw [he]
  dsimp only [hyperbolicLaplacian]
  simp only [Matrix.cons_val]
  ring

private def weightedHeight (w : ℂ) (z : A) : ℂ := Complex.exp (w*(z 1:ℂ))
private def UniformRapid {ι : Type*} (F : ι → A → ℂ) : Prop :=
  ∀ (w : ℂ) (P : ℝ → ι) (X : ℝ → ℝ),
    Tendsto (fun k : ℝ => weightedHeight w ![X k,k]*F (P k) ![X k,k]) atTop (𝓝 0)
private theorem UniformRapid.congr {ι : Type*} {F G : ι → A → ℂ}
    (hF : UniformRapid F) (he : ∀ p z,F p z=G p z) : UniformRapid G := by
  intro w P X
  exact (hF w P X).congr' (Eventually.of_forall (fun k => by rw [he]))
private theorem UniformRapid.add {ι : Type*} {F G : ι → A → ℂ}
    (hF : UniformRapid F) (hG : UniformRapid G) : UniformRapid (fun p z => F p z+G p z) := by
  intro w P X
  simpa only [mul_add,add_zero] using (hF w P X).add (hG w P X)
private theorem UniformRapid.sub {ι : Type*} {F G : ι → A → ℂ}
    (hF : UniformRapid F) (hG : UniformRapid G) : UniformRapid (fun p z => F p z-G p z) := by
  intro w P X
  simpa only [mul_sub,sub_zero] using (hF w P X).sub (hG w P X)
private theorem UniformRapid.scale {ι : Type*} {F : ι → A → ℂ}
    (hF : UniformRapid F) (c : ℂ) : UniformRapid (fun p z => c*F p z) := by
  intro w P X
  convert (hF w P X).const_mul c using 1
  · funext k; ring
  · simp
private theorem UniformRapid.mul {ι : Type*} {F G : ι → A → ℂ}
    (hF : UniformRapid F) (hG : UniformRapid G) : UniformRapid (fun p z => F p z*G p z) := by
  intro w P X
  simpa only [weightedHeight,zero_mul,Complex.exp_zero,one_mul,mul_zero,mul_assoc]
    using (hF w P X).mul (hG 0 P X)
private theorem UniformRapid.exp_mul {ι : Type*} {F : ι → A → ℂ}
    (hF : UniformRapid F) (c : ℂ) : UniformRapid (fun p z => weightedHeight c z*F p z) := by
  intro w P X
  have he (z : A) : weightedHeight w z*weightedHeight c z=weightedHeight (w+c) z := by
    unfold weightedHeight
    rw [← Complex.exp_add]
    congr 1
    ring
  simpa only [← mul_assoc,he] using hF (w+c) P X
private theorem UniformRapid.coeff {ι : Type*} {F : ι → A → ℂ}
    (hF : UniformRapid F) (c : ι → ℂ) (hc : ∃ C : ℝ, ∀ p,‖c p‖≤C) :
    UniformRapid (fun p z => c p*F p z) := by
  obtain ⟨C,hC⟩ := hc
  intro w P X
  have ht := (hF w P X).norm.const_mul C
  simp only [norm_zero,mul_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [] with k
  rw [mul_left_comm,norm_mul]
  exact mul_le_mul_of_nonneg_right (hC (P k)) (norm_nonneg _)

private def UniformModerate {ι : Type*} (F : ι → A → ℂ) : Prop :=
  ∀ G : ι → A → ℂ, UniformRapid G → UniformRapid (fun p z => F p z*G p z)
private theorem UniformModerate.exp {ι : Type*} (c : ℂ) :
    UniformModerate (fun (_ : ι) z => weightedHeight c z) := fun _ h => h.exp_mul c
private theorem UniformModerate.coeff {ι : Type*} {F : ι → A → ℂ}
    (hF : UniformModerate F) (c : ι → ℂ) (hc : ∃ C : ℝ,∀ p,‖c p‖≤C) :
    UniformModerate (fun p z => c p*F p z) := by
  intro G hG
  exact ((hF G hG).coeff c hc).congr (fun p z => by ring)
private theorem UniformModerate.add {ι : Type*} {F G : ι → A → ℂ}
    (hF : UniformModerate F) (hG : UniformModerate G) : UniformModerate (fun p z => F p z+G p z) := by
  intro H hH
  exact ((hF H hH).add (hG H hH)).congr (fun p z => by ring)
private theorem UniformRapid.mul_moderate {ι : Type*} {F G : ι → A → ℂ}
    (hF : UniformRapid F) (hG : UniformModerate G) : UniformRapid (fun p z => F p z*G p z) :=
  (hG F hF).congr (fun _ _ => mul_comm _ _)
private theorem UniformModerate.sum_three {ι : Type*} (F : Fin 3 → ι → A → ℂ)
    (hF : ∀ i,UniformModerate (F i)) : UniformModerate (fun p z => ∑ i : Fin 3,F i p z) := by
  simpa only [Fin.sum_univ_three] using ((hF 0).add (hF 1)).add (hF 2)

private theorem weighted_limit {f : ℝ → ℂ}
    (hf : ∀ N : ℕ,∃ D B : ℝ,0≤B ∧ ∀ k : ℝ,D≤k → ‖f k‖≤B*Real.exp (-(N:ℝ)*k))
    (w : ℂ) : Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*f k) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt w.re
  obtain ⟨D,B,hB,hf⟩ := hf N
  have ht := Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (sub_neg.mpr hN)).2 tendsto_id)
  apply squeeze_zero_norm' _ (by simpa using ht.const_mul B)
  filter_upwards [eventually_ge_atTop D] with k hk
  rw [norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  calc
    _ ≤ Real.exp (w.re*k)*(B*Real.exp (-(N:ℝ)*k)) :=
      mul_le_mul_of_nonneg_left (hf k hk) (Real.exp_pos _).le
    _ = B*Real.exp ((w.re-(N:ℝ))*k) := by
      rw [mul_left_comm,← Real.exp_add]
      congr 2
      ring

private theorem source_jet_uniform (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (T : Ici (0:ℝ)) (word : List (Fin 2)) :
    UniformRapid (fun pr : Icc 0 T.val × Icc 0 T.val => fun z =>
      D4BMSquareCuspJets.coordinateJet word (D4BMOriginalCuspJets.remainder q br amp pr.1 pr.2) z) := by
  intro w P X
  change Tendsto (fun k : ℝ => Complex.exp (w*(k:ℂ))*
    D4BMSquareCuspJets.coordinateJet word (D4BMOriginalCuspJets.remainder q br amp (P k).1 (P k).2) ![X k,k]) atTop (𝓝 0)
  apply weighted_limit _ w
  intro N
  obtain ⟨D,B,hD,hB,h⟩ := D4BMOriginalCausalPeriod.original_remainder_jet_compact_rapid_bound q br amp word N T
  refine ⟨D,B*Real.exp ((N:ℝ)*D),by positivity,?_⟩
  intro k hk
  calc
    _ ≤ B*Real.exp ((N:ℝ)*(D-k)) := h _ (P k).1.property _ (P k).2.property (X k) k hk
    _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring


private theorem UniformRapid.comp {ι κ : Type*} {F : ι → A → ℂ}
    (hF : UniformRapid F) (f : κ → ι) : UniformRapid (fun p z => F (f p) z) :=
  fun w P X => hF w (fun k => f (P k)) X

private theorem clock_source_jet_uniform (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (a b R : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (word : List (Fin 2)) :
    UniformRapid (fun p : Icc a b => fun z => D4BMSquareCuspJets.coordinateJet word
      (D4BMOriginalCuspJets.remainder q br amp p (p-2*D4BMIngoingCoordinates.tortoise R)) z) := by
  have hx : D4BMIngoingCoordinates.tortoise R<0 := by
    have h := Real.log_lt_log (show 0<R-1 by linarith) (show R-1<R+1 by linarith)
    dsimp [D4BMIngoingCoordinates.tortoise]
    linarith
  let T : Ici (0:ℝ) := ⟨b-2*D4BMIngoingCoordinates.tortoise R,by change 0≤b-2*D4BMIngoingCoordinates.tortoise R;linarith⟩
  let f : Icc a b → Icc 0 T.val × Icc 0 T.val := fun p =>
    (⟨p.val,⟨(ha.trans_le p.property.1).le,by change p.val≤b-2*D4BMIngoingCoordinates.tortoise R;linarith [p.property.2]⟩⟩,
     ⟨p.val-2*D4BMIngoingCoordinates.tortoise R,⟨by linarith [p.property.1],by change p.val-2*D4BMIngoingCoordinates.tortoise R≤b-2*D4BMIngoingCoordinates.tortoise R;linarith [p.property.2]⟩⟩)
  exact (source_jet_uniform q br amp T word).comp f

private theorem source_value_uniform (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (a b R : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) :
    UniformRapid (fun p : Icc a b => fun z => sourceScalar q br amp ![p,R,z 0,Real.exp (z 1)]-
      ∑ i : Fin 3,principalCoefficient q br amp p R i*weightedHeight (principalExponent q i) z) := by
  apply ((clock_source_jet_uniform q br amp a b R ha hab hr []).scale (R:ℂ)).congr
  intro p z
  have h := (original_source_logarithmic_remainders q br amp p
    (p-2*D4BMIngoingCoordinates.tortoise R) (z 0) (z 1)).1
  change (R:ℂ)*D4BMOriginalCuspJets.remainder q br amp p (p-2*D4BMIngoingCoordinates.tortoise R) ![z 0,z 1]=
    (R:ℂ)*D4BMOriginalAngularGreen.source q br amp p (p-2*D4BMIngoingCoordinates.tortoise R) ![z 0,Real.exp (z 1)]-_
  rw [h]
  simp only [principalCoefficient,weightedHeight,D4BMSquareCuspJets.coordinateJet,Fin.sum_univ_three]
  ring

private theorem angular_eta (z : A) : (![z 0,z 1] : A)=z := by
  ext i
  fin_cases i <;> rfl

private theorem source_normal_uniform (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (a b R : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) :
    UniformRapid (fun p : Icc a b => fun z => coordDeriv 3 (sourceScalar q br amp) ![p,R,z 0,Real.exp (z 1)]-
      ∑ i : Fin 3,principalCoefficient q br amp p R i*principalExponent q i*
        weightedHeight (principalExponent q i-1) z) := by
  apply (((clock_source_jet_uniform q br amp a b R ha hab hr [1]).exp_mul (-1)).scale (R:ℂ)).congr
  intro p z
  have hs := original_source_normal q br amp p R ![z 0,Real.exp (z 1)] (ha.trans_le p.property.1) hr (Real.exp_pos _)
  simp only [Matrix.cons_val] at hs
  rw [hs]
  have hj := (original_source_logarithmic_remainders q br amp p
    (p-2*D4BMIngoingCoordinates.tortoise R) (z 0) (z 1)).2.1
  change coordDeriv 1 (D4BMOriginalAngularGreen.source q br amp p
    (p-2*D4BMIngoingCoordinates.tortoise R)) ![z 0,Real.exp (z 1)]=_ at hj
  rw [hj]
  simp only [angular_eta,weightedHeight,principalCoefficient,Fin.sum_univ_three,neg_one_mul]
  ring

private theorem source_laplacian_uniform (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (a b R : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) :
    UniformRapid (fun p : Icc a b => fun z => angularLap (sourceScalar q br amp) ![p,R,z 0,Real.exp (z 1)]-
      ∑ i : Fin 3,principalCoefficient q br amp p R i*principalExponent q i*(principalExponent q i-1)*
        weightedHeight (principalExponent q i) z) := by
  have h := ((((clock_source_jet_uniform q br amp a b R ha hab hr [0,0]).exp_mul 2).add
    (clock_source_jet_uniform q br amp a b R ha hab hr [1,1])).sub
    (clock_source_jet_uniform q br amp a b R ha hab hr [1])).scale (R:ℂ)
  apply h.congr
  intro p z
  have hs := source_angular_restriction q br amp p R ![z 0,Real.exp (z 1)] (ha.trans_le p.property.1) hr (Real.exp_pos _)
  simp only [Matrix.cons_val] at hs
  rw [hs]
  have hj := (original_source_logarithmic_remainders q br amp p
    (p-2*D4BMIngoingCoordinates.tortoise R) (z 0) (z 1)).2.2
  change hyperbolicLaplacian (D4BMOriginalAngularGreen.source q br amp p
    (p-2*D4BMIngoingCoordinates.tortoise R)) ![z 0,Real.exp (z 1)]=_ at hj
  rw [hj]
  simp only [angular_eta,weightedHeight,principalCoefficient,Fin.sum_univ_three]
  ring

private theorem principal_time_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) (R : ℝ) (i : Fin 3) :
    Continuous (fun p : ℝ => principalCoefficient q br amp p R i) := by
  let s := D4BMModularCore.physicalRate q br
  have hL : Continuous (radialLift s 0 amp 1) := continuous_iff_continuousAt.mpr
    (fun x => (radialLift_hasDerivAt s 0 amp 1 x).continuousAt)
  have hO : Continuous (timeOnset (2*s)) := continuous_iff_continuousAt.mpr
    (fun p => (timeOnset_hasDerivAt (2*s) p).continuousAt)
  have hD := (D4BMNativeResponse.radialResponse_continuous (-principalExponent q i) s amp).comp
    (show Continuous (fun p : ℝ => ((p+(p-2*D4BMIngoingCoordinates.tortoise R))/2,
      (p-(p-2*D4BMIngoingCoordinates.tortoise R))/2)) by fun_prop)
  have hN := (hL.comp (show Continuous (fun p : ℝ => (p-(p-2*D4BMIngoingCoordinates.tortoise R))/2) by fun_prop)).mul hO
  exact ((hD.const_mul (principalAmplitude q i)).add (hN.mul_const (principalAmplitude q i))).const_mul (R:ℂ)


private theorem compact_time_bound (c : ℝ → ℂ) (hc : Continuous c) (a b : ℝ) :
    ∃ C : ℝ,∀ p : Icc a b,‖c p‖≤C := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s:=Icc a b) hc.continuousOn
  exact ⟨C,fun p => hC p p.property⟩

private theorem reader_value_uniform {ι : Type*} (r : XiZeroCopy) :
    UniformRapid (fun (_ : ι) z => D4BMLiteralCusp.scalar (physicalAngularParameter r) ![z 0,Real.exp (z 1)]-
      readerCoefficient r*weightedHeight (readerExponent r) z) := by
  intro w _P X
  obtain ⟨C,hC,hbound⟩ := D4BMGlobalAngularResponse.weighted_tail_bounded (physicalAngularParameter r) (w+1) 1 (by norm_num)
  apply squeeze_zero_norm' _ (by simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with k hk
  have hp := D4BMJointSource.physicalScalar_principal r ![X k,Real.exp k]
  have he : D4BMLiteralCusp.scalar (physicalAngularParameter r) ![X k,Real.exp k]-
      readerCoefficient r*Complex.exp (readerExponent r*(k:ℂ))=
      D4BMGlobalAngularResponse.tail (physicalAngularParameter r) ![X k,Real.exp k] := by
    simp only [Matrix.cons_val,exp_cpow] at hp
    change D4BMLiteralCusp.scalar (physicalAngularParameter r) ![X k,Real.exp k]-
      reflectedCompletedLambda ((r.1:ℂ)-1)*Complex.exp ((1-(r.1:ℂ)/2)*(k:ℂ))=_
    rw [← hp]
    change (D4BMGlobalAngularResponse.principal (physicalAngularParameter r) ![X k,Real.exp k]+
      D4BMGlobalAngularResponse.tail (physicalAngularParameter r) ![X k,Real.exp k])-
      D4BMGlobalAngularResponse.principal (physicalAngularParameter r) ![X k,Real.exp k]=_
    ring
  have hb := hbound ![X k,Real.exp k] (Real.one_le_exp hk)
  simp only [Matrix.cons_val,exp_cpow] at hb
  simp only [weightedHeight,Matrix.cons_val,he]
  have hsplit : Complex.exp (w*(k:ℂ))*D4BMGlobalAngularResponse.tail (physicalAngularParameter r) ![X k,Real.exp k]=
      Complex.exp (-(k:ℂ))*(Complex.exp ((w+1)*(k:ℂ))*
        D4BMGlobalAngularResponse.tail (physicalAngularParameter r) ![X k,Real.exp k]) := by
    rw [← mul_assoc,← Complex.exp_add]
    congr 2
    ring
  rw [hsplit,norm_mul]
  have hn : ‖Complex.exp (-(k:ℂ))‖=Real.exp (-k) := by simp [Complex.norm_exp]
  rw [hn]
  exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq (mul_comm _ _)

private theorem reader_normal_uniform {ι : Type*} (r : XiZeroCopy) :
    UniformRapid (fun (_ : ι) z => coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) ![z 0,Real.exp (z 1)]-
      readerCoefficient r*readerExponent r*weightedHeight (readerExponent r-1) z) := by
  intro w _P X
  simpa only [weightedHeight,Matrix.cons_val] using original_reader_normal_expansion r X w

private theorem forcing_time_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) (R : ℝ) :
    Continuous (fun p : ℝ => forcingValueCoefficient q br amp p R) ∧
    Continuous (fun p : ℝ => forcingLaplacianCoefficient q br amp p R) := by
  let s := D4BMModularCore.physicalRate q br
  have hO : Continuous (timeOnset (2*s)) := continuous_iff_continuousAt.mpr
    (fun p => (timeOnset_hasDerivAt (2*s) p).continuousAt)
  constructor
  · exact (hO.const_mul _).mul_const _
  · exact (hO.const_mul _).mul_const _

/-- The original full forcing's three principal angular coefficients. -/
def forcingPrincipalCoefficient (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (p R : ℝ) (i : Fin 3) : ℂ :=
  (forcingValueCoefficient q br amp p R+
    forcingLaplacianCoefficient q br amp p R*principalExponent q i*(principalExponent q i-1))*principalAmplitude q i

private theorem forcing_uniform (q : XiZeroCopy) (br : Bool) (amp : ℂ) (a b R : ℝ) :
    UniformRapid (fun p : Icc a b => fun z => originalForcing q br amp ![p,R,z 0,Real.exp (z 1)]-
      ∑ i : Fin 3,forcingPrincipalCoefficient q br amp p R i*weightedHeight (principalExponent q i) z) := by
  have hS : UniformRapid (fun (_ : Icc a b) z => D4BMModularCore.fullSquarePotential q ![z 0,Real.exp (z 1)]-
      ∑ i : Fin 3,principalAmplitude q i*weightedHeight (principalExponent q i) z) := by
    intro w _P X
    simpa only [weightedHeight,Matrix.cons_val] using square_expansion q X w
  have hL : UniformRapid (fun (_ : Icc a b) z => L (D4BMModularCore.fullSquarePotential q) ![z 0,Real.exp (z 1)]-
      ∑ i : Fin 3,principalAmplitude q i*principalExponent q i*(principalExponent q i-1)*weightedHeight (principalExponent q i) z) := by
    intro w _P X
    simpa only [weightedHeight,Matrix.cons_val] using square_laplacian_expansion q X w
  have hc := forcing_time_continuous q br amp R
  have h := (hS.coeff (fun p => forcingValueCoefficient q br amp p R)
    (compact_time_bound _ hc.1 a b)).add
      (hL.coeff (fun p => forcingLaplacianCoefficient q br amp p R) (compact_time_bound _ hc.2 a b))
  apply h.congr
  intro p z
  rw [original_forcing_laplacian q br amp ![p,R,z 0,Real.exp (z 1)] (Real.exp_pos _)]
  simp only [Matrix.cons_val]
  rw [D4BMHorizon.scalarLaplacian_eq _ ![z 0,Real.exp (z 1)] (Real.exp_pos _)]
  simp only [Matrix.cons_val,forcingPrincipalCoefficient,Fin.sum_univ_three,hyperbolicLaplacian]
  ring

private theorem UniformRapid.product_remainder {ι : Type*} {F G P Q : ι → A → ℂ}
    (hF : UniformRapid (fun p z => F p z-P p z))
    (hG : UniformRapid (fun p z => G p z-Q p z))
    (hP : UniformModerate P) (hQ : UniformModerate Q) :
    UniformRapid (fun p z => F p z*G p z-P p z*Q p z) := by
  have h := ((hF.mul_moderate hQ).add (hP _ hG)).add (hF.mul hG)
  exact h.congr (fun p z => by ring)

private theorem weightedHeight_mul (u v : ℂ) (z : A) :
    weightedHeight u z*weightedHeight v z=weightedHeight (u+v) z := by
  unfold weightedHeight
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem uniform_product_three_single (a b : ℝ) (F G : ℝ → A → ℂ)
    (c : ℝ → Fin 3 → ℂ) (d : ℝ → ℂ) (alpha : Fin 3 → ℂ) (beta : ℂ)
    (hc : ∀ i,Continuous (fun p => c p i)) (hd : Continuous d)
    (hF : UniformRapid (fun p : Icc a b => fun z => F p z-∑ i : Fin 3,c p i*weightedHeight (alpha i) z))
    (hG : UniformRapid (fun p : Icc a b => fun z => G p z-d p*weightedHeight beta z)) :
    UniformRapid (fun p : Icc a b => fun z => F p z*G p z-
      ∑ i : Fin 3,c p i*d p*weightedHeight (alpha i+beta) z) := by
  have hP := UniformModerate.sum_three
    (fun i (p : Icc a b) z => c p i*weightedHeight (alpha i) z)
    (fun i => (UniformModerate.exp (alpha i)).coeff (fun p : Icc a b => c p i) (compact_time_bound _ (hc i) a b))
  have hQ := (UniformModerate.exp beta).coeff (fun p : Icc a b => d p) (compact_time_bound _ hd a b)
  apply (hF.product_remainder hG hP hQ).congr
  intro p z
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← weightedHeight_mul]
  ring

private theorem mode_amplitude_continuous (r : XiZeroCopy) (w : ℂ) (outer : Bool) (R : ℝ) :
    Continuous (fun p : ℝ => modeAmplitude r w outer ![p,R]) := by
  dsimp [modeAmplitude]
  fun_prop

private theorem mode_normal (r : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool)
    (x : P) (hr : 1<x 1) (hy : 0<x 3) :
    coordDeriv 3 (modeScalar r w outer) x=modeAmplitude r w outer ![x 0,x 1]*
      coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) ![x 2,x 3] := by
  have hn (z : A) (hz : 0<z 1) :
      coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) z=
        deriv (fun Y => D4BMLiteralCusp.scalar (physicalAngularParameter r) ![z 0,Y]) (z 1) := by
    rw [coordinate_update _ _ _ ((D4BMLiteralCusp.scalar_contDiffAt
      (physicalAngularParameter r) 2 z hz).differentiableAt (by norm_num))]
    congr 1
  rw [coordinate_update _ _ _ ((modeScalar_smooth r w hw outer x hr hy).differentiableAt (by simp))]
  simp_rw [modeScalar_value]
  simp only [angularPoint,Function.update_self,
    Function.update_of_ne (by decide : (0:Fin 4)≠3),
    Function.update_of_ne (by decide : (1:Fin 4)≠3),
    Function.update_of_ne (by decide : (2:Fin 4)≠3)]
  rw [deriv_const_mul_field,hn ![x 2,x 3] hy]
  rfl

private theorem mode_value_uniform (r : XiZeroCopy) (w : ℂ) (outer : Bool) (a b R : ℝ) :
    UniformRapid (fun p : Icc a b => fun z => modeScalar r w outer ![p,R,z 0,Real.exp (z 1)]-
      (modeAmplitude r w outer ![p,R]*readerCoefficient r)*weightedHeight (readerExponent r) z) := by
  have h := (reader_value_uniform (ι:=Icc a b) r).coeff
    (fun p => modeAmplitude r w outer ![p,R]) (compact_time_bound _ (mode_amplitude_continuous r w outer R) a b)
  apply h.congr
  intro p z
  rw [modeScalar_value]
  simp only [modeAmplitude,angularPoint,Matrix.cons_val]
  ring

private theorem mode_normal_uniform (r : XiZeroCopy) (w : ℂ) (hw : w.im≠0)
    (outer : Bool) (a b R : ℝ) (hr : 1<R) :
    UniformRapid (fun p : Icc a b => fun z => coordDeriv 3 (modeScalar r w outer) ![p,R,z 0,Real.exp (z 1)]-
      (modeAmplitude r w outer ![p,R]*readerCoefficient r*readerExponent r)*weightedHeight (readerExponent r-1) z) := by
  have h := (reader_normal_uniform (ι:=Icc a b) r).coeff
    (fun p => modeAmplitude r w outer ![p,R]) (compact_time_bound _ (mode_amplitude_continuous r w outer R) a b)
  apply h.congr
  intro p z
  have hn := mode_normal r w hw outer ![p,R,z 0,Real.exp (z 1)] hr (Real.exp_pos _)
  simp only [Matrix.cons_val] at hn
  rw [hn]
  ring

private theorem UniformRapid.uniform {ι : Type*} [Nonempty ι] {F : ι → A → ℂ}
    (hF : UniformRapid F) (w : ℂ) (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᶠ k : ℝ in atTop,∀ p : ι,∀ X : ℝ,‖weightedHeight w ![X,k]*F p ![X,k]‖<epsilon := by
  classical
  let Z : ℝ → ι×ℝ := fun k =>
    if h : ∃ z : ι×ℝ,epsilon≤‖weightedHeight w ![z.2,k]*F z.1 ![z.2,k]‖ then h.choose else (Classical.choice ‹Nonempty ι›,0)
  have ht := Metric.tendsto_nhds.mp (hF w (fun k => (Z k).1) (fun k => (Z k).2)) epsilon hepsilon
  filter_upwards [ht] with k hk p X
  rw [dist_zero_right] at hk
  by_contra h
  have he : ∃ z : ι×ℝ,epsilon≤‖weightedHeight w ![z.2,k]*F z.1 ![z.2,k]‖ := ⟨(p,X),le_of_not_gt h⟩
  have hb : epsilon≤‖weightedHeight w ![(Z k).2,k]*F (Z k).1 ![(Z k).2,k]‖ := by
    dsimp only [Z]
    rw [dif_pos he]
    exact he.choose_spec
  exact (not_lt_of_ge hb) hk

private theorem UniformRapid.time_integral (a b : ℝ) (hab : a≤b) (F : ℝ → A → ℂ)
    (hF : UniformRapid (fun p : Icc a b => F p)) (w : ℂ) :
    Tendsto (fun k : ℝ => ∫ p in a..b,∫ X in (-1/2:ℝ)..1/2,
      weightedHeight w ![X,k]*F p ![X,k]) atTop (𝓝 0) := by
  letI : Nonempty (Icc a b) := ⟨⟨a,le_rfl,hab⟩⟩
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  let delta := epsilon/(2*(b-a+1))
  have hd : 0<delta := by dsimp [delta]; positivity
  filter_upwards [hF.uniform w delta hd] with k hk
  have hinner (p : ℝ) (hp : p∈Icc a b) :
      ‖∫ X in (-1/2:ℝ)..1/2,weightedHeight w ![X,k]*F p ![X,k]‖≤delta := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=(-1/2:ℝ)) (b:=(1/2:ℝ)) (fun X _ => (hk ⟨p,hp⟩ X).le)
    norm_num only [sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,abs_one,mul_one] at h
    simpa only [neg_div] using h
  have ho := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=a) (b:=b) (fun p hp => hinner p (Ioc_subset_Icc_self (show p∈Ioc a b from uIoc_of_le hab ▸ hp)))
  rw [dist_zero_right]
  apply ho.trans_lt
  rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  dsimp [delta]
  apply (div_mul_eq_mul_div _ _ _).trans_lt
  apply (div_lt_iff₀ (by positivity : 0<2*(b-a+1))).mpr
  nlinarith

private def transferLeft (q r : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (j : Fin 4) : P → ℂ :=
  ![sourceScalar q br amp,modeScalar r w outer,angularLap (sourceScalar q br amp),originalForcing q br amp] j
private def transferRight (q r : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (j : Fin 4) : P → ℂ :=
  ![modeScalar r w outer,sourceScalar q br amp,modeScalar r w outer,modeScalar r w outer] j

/-- The four original transfers in the finite-time complete boundary identity:
`T(U,W)`, `T(W,U)`, `T(Delta U,W)` and `T(F,W)`. -/
def modeTransferCoefficient (q r : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (j : Fin 4) (p R : ℝ) (i : Fin 3) : ℂ :=
  let A := principalCoefficient q br amp p R i
  let a := principalExponent q i
  let B := modeAmplitude r w outer ![p,R]*readerCoefficient r
  let beta := readerExponent r
  ![A*(B*beta),(A*a)*B,(A*a*(a-1))*(B*beta),forcingPrincipalCoefficient q br amp p R i*(B*beta)] j

private theorem forcing_principal_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) (R : ℝ) (i : Fin 3) :
    Continuous (fun p => forcingPrincipalCoefficient q br amp p R i) := by
  have hc := forcing_time_continuous q br amp R
  exact (hc.1.add ((hc.2.mul_const _).mul_const _)).mul_const _

private theorem transfer_coefficient_continuous (q r : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (j : Fin 4) (R : ℝ) (i : Fin 3) : Continuous (fun p => modeTransferCoefficient q r br outer amp w j p R i) := by
  have hA := principal_time_continuous q br amp R i
  have hB := (mode_amplitude_continuous r w outer R).mul_const (readerCoefficient r)
  have hF := forcing_principal_continuous q br amp R i
  fin_cases j
  · exact hA.mul (hB.mul_const _)
  · exact (hA.mul_const _).mul hB
  · exact ((hA.mul_const _).mul_const _).mul (hB.mul_const _)
  · exact hF.mul (hB.mul_const _)

private theorem transfers_uniform (q r : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (a b R : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (j : Fin 4) :
    UniformRapid (fun p : Icc a b => fun z =>
      transfer (transferLeft q r br outer amp w j) (transferRight q r br outer amp w j) 1
        ![p,R,z 0,Real.exp (z 1)]-
      ∑ i : Fin 3,modeTransferCoefficient q r br outer amp w j p R i*weightedHeight (fluxExponent q r i) z) := by
  have hA := principal_time_continuous q br amp R
  have hB := (mode_amplitude_continuous r w outer R).mul_const (readerCoefficient r)
  have hBn := hB.mul_const (readerExponent r)
  fin_cases j
  · have h := uniform_product_three_single a b
      (fun p z => sourceScalar q br amp ![p,R,z 0,Real.exp (z 1)])
      (fun p z => coordDeriv 3 (modeScalar r w outer) ![p,R,z 0,Real.exp (z 1)])
      (fun p i => principalCoefficient q br amp p R i)
      (fun p => modeAmplitude r w outer ![p,R]*readerCoefficient r*readerExponent r)
      (principalExponent q) (readerExponent r-1) hA hBn
      (source_value_uniform q br amp a b R ha hab hr) (mode_normal_uniform r w hw outer a b R hr)
    apply h.congr
    intro p z
    simp only [transferLeft,transferRight,transfer,angularIndex,modeTransferCoefficient,Matrix.cons_val]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    unfold fluxExponent
    ring
  · have h := uniform_product_three_single a b
      (fun p z => coordDeriv 3 (sourceScalar q br amp) ![p,R,z 0,Real.exp (z 1)])
      (fun p z => modeScalar r w outer ![p,R,z 0,Real.exp (z 1)])
      (fun p i => principalCoefficient q br amp p R i*principalExponent q i)
      (fun p => modeAmplitude r w outer ![p,R]*readerCoefficient r)
      (fun i => principalExponent q i-1) (readerExponent r) (fun i => (hA i).mul_const _) hB
      (source_normal_uniform q br amp a b R ha hab hr) (mode_value_uniform r w outer a b R)
    apply h.congr
    intro p z
    simp only [transferLeft,transferRight,transfer,angularIndex,modeTransferCoefficient,Matrix.cons_val]
    rw [mul_comm (coordDeriv 3 (sourceScalar q br amp) _) (modeScalar r w outer _)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    unfold fluxExponent
    ring
  · have h := uniform_product_three_single a b
      (fun p z => angularLap (sourceScalar q br amp) ![p,R,z 0,Real.exp (z 1)])
      (fun p z => coordDeriv 3 (modeScalar r w outer) ![p,R,z 0,Real.exp (z 1)])
      (fun p i => principalCoefficient q br amp p R i*principalExponent q i*(principalExponent q i-1))
      (fun p => modeAmplitude r w outer ![p,R]*readerCoefficient r*readerExponent r)
      (principalExponent q) (readerExponent r-1) (fun i => ((hA i).mul_const _).mul_const _) hBn
      (source_laplacian_uniform q br amp a b R ha hab hr) (mode_normal_uniform r w hw outer a b R hr)
    apply h.congr
    intro p z
    simp only [transferLeft,transferRight,transfer,angularIndex,modeTransferCoefficient,Matrix.cons_val]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    unfold fluxExponent
    ring
  · have h := uniform_product_three_single a b
      (fun p z => originalForcing q br amp ![p,R,z 0,Real.exp (z 1)])
      (fun p z => coordDeriv 3 (modeScalar r w outer) ![p,R,z 0,Real.exp (z 1)])
      (fun p i => forcingPrincipalCoefficient q br amp p R i)
      (fun p => modeAmplitude r w outer ![p,R]*readerCoefficient r*readerExponent r)
      (principalExponent q) (readerExponent r-1) (forcing_principal_continuous q br amp R) hBn
      (forcing_uniform q br amp a b R) (mode_normal_uniform r w hw outer a b R hr)
    apply h.congr
    intro p z
    simp only [transferLeft,transferRight,transfer,angularIndex,modeTransferCoefficient,Matrix.cons_val]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    unfold fluxExponent
    ring

open GaloisForLFunctions.RHTower.SelbergMaassMean D4BMOriginalModularOrbit
private abbrev F := P → ℂ
private def ExteriorSmooth (U : F) : Prop :=
  ∀ x : P,0<x 0 → 1<x 1 → 0<x 3 → ContDiffAt ℝ ∞ U x

private theorem smooth_partial {U : F} (hU : ExteriorSmooth U) (i : Fin 4) :
    ExteriorSmooth (coordDeriv i U) := by
  intro x hp hr hy
  exact coordDeriv_contDiffAt (hU x hp hr hy) (by simp) i
private theorem contact_smooth {U : F} (hU : ExteriorSmooth U) : ExteriorSmooth (scalarContact U) := by
  intro x hp hr hy
  have h0 := smooth_partial hU 0 x hp hr hy
  have h1 := smooth_partial hU 1 x hp hr hy
  have h01 := smooth_partial (smooth_partial hU 1) 0 x hp hr hy
  have h10 := smooth_partial (smooth_partial hU 0) 1 x hp hr hy
  have h11 := smooth_partial (smooth_partial hU 1) 1 x hp hr hy
  have hR : ContDiffAt ℝ ∞ (fun z : P => (z 1:ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (1:Fin 4))).contDiffAt
  change ContDiffAt ℝ ∞ (fun z : P =>
    -(z 1:ℂ)^2*((z 1:ℂ)^2-1)*coordDeriv 1 (coordDeriv 1 U) z-
    (z 1:ℂ)^2*(coordDeriv 0 (coordDeriv 1 U) z+coordDeriv 1 (coordDeriv 0 U) z)-
    2*(z 1:ℂ)*coordDeriv 1 U z+2*(z 1:ℂ)*coordDeriv 0 U z) x
  exact ((((hR.pow 2).neg.mul ((hR.pow 2).sub contDiffAt_const)).mul h11).sub
    ((hR.pow 2).mul (h01.add h10)) |>.sub ((contDiffAt_const.mul hR).mul h1)).add
      ((contDiffAt_const.mul hR).mul h0)
private theorem source_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ExteriorSmooth (sourceScalar q branch amp) :=
  D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth q branch amp
private theorem lap_smooth {U : F} (hU : ExteriorSmooth U) :
    ExteriorSmooth (angularLap U) := by
  intro x hp hr hy
  have hY : ContDiffAt ℝ ∞ (fun z : P => (z 3:ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (3:Fin 4))).contDiffAt
  exact (hY.pow 2).mul ((smooth_partial (smooth_partial hU 2) 2 x hp hr hy).add
    (smooth_partial (smooth_partial hU 3) 3 x hp hr hy))

private theorem original_forcing_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ExteriorSmooth (D4BMOriginalSourceContact.originalForcing q branch amp) := by
  intro x hp hr hy
  let U := sourceScalar q branch amp
  have he : D4BMOriginalSourceContact.originalForcing q branch amp =ᶠ[𝓝 x]
      fun z => (((z 1:ℂ)^2-1)/(z 1:ℂ)^3)*
        (scalarContact U z-angularLap U z+2*U z) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hp,
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
      (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hz0 hz1 hz3
    have hc := original_scalar_contact q branch amp z hz0 hz1 hz3
    have hh : scalarContact U z-angularLap U z+2*U z=
        (z 1:ℂ)^3/((z 1:ℂ)^2-1)*D4BMOriginalSourceContact.originalForcing q branch amp z := by
      dsimp only [U]
      linear_combination hc
    rw [hh]
    have hR : (z 1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hf : (z 1:ℂ)^2-1≠0 := by exact_mod_cast (show (z 1)^2-1≠0 by nlinarith)
    field_simp [hR,hf]
  have hR : ContDiffAt ℝ ∞ (fun z : P => z 1) x :=
    (contDiff_apply ℝ ℝ (1:Fin 4)).contDiffAt
  have hnum : ContDiffAt ℝ ∞ (fun z : P => (z 1)^2-1) x :=
    (hR.pow 2).sub contDiffAt_const
  have hreal := hnum.div (hR.pow 3) (pow_ne_zero 3 (show x 1≠0 by linarith))
  have hs : ContDiffAt ℝ ∞ (fun z : P => ((z 1:ℂ)^2-1)/(z 1:ℂ)^3) x := by
    have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
    change ContDiffAt ℝ ∞ (fun z : P => ((((z 1)^2-1)/(z 1)^3:ℝ):ℂ)) x at hc
    simpa only [Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_pow,Complex.ofReal_one] using! hc
  have hv : ContDiffAt ℝ ∞ (fun z => scalarContact U z-angularLap U z+2*U z) x :=
    ((contact_smooth (source_smooth q branch amp) x hp hr hy).sub
      (lap_smooth (source_smooth q branch amp) x hp hr hy)).add
      (contDiffAt_const.mul (source_smooth q branch amp x hp hr hy))
  exact (hs.mul hv).congr_of_eventuallyEq he

private theorem mode_smooth (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool) :
    ExteriorSmooth (modeScalar q w outer) := by
  intro x hp hr hy
  exact modeScalar_smooth q w hw outer x hr hy

private theorem top_rectangle_continuous (U V : F) (hU : ExteriorSmooth U) (hV : ExteriorSmooth V)
    (a b R Y : ℝ) (ha : 0<a) (hr : 1<R) (hy : 0<Y) :
    ContinuousOn (fun z : ℝ×ℝ => transfer U V 1 (slice z.1 R (point z.2 Y)))
      (Icc a b ×ˢ Icc (-1/2:ℝ) (1/2:ℝ)) := by
  intro z hz
  have hu := hU (slice z.1 R (point z.2 Y)) (ha.trans_le hz.1.1) hr (by simpa [slice,point] using hy)
  have hv := smooth_partial hV 3 (slice z.1 R (point z.2 Y)) (ha.trans_le hz.1.1) hr (by simpa [slice,point] using hy)
  change ContinuousWithinAt (fun z : ℝ×ℝ => U (slice z.1 R (point z.2 Y))*coordDeriv 3 V (slice z.1 R (point z.2 Y))) _ z
  exact ((hu.continuousAt.mul hv.continuousAt).comp
    (f:=fun z : ℝ×ℝ => slice z.1 R (point z.2 Y))
    (show Continuous (fun z : ℝ×ℝ => slice z.1 R (point z.2 Y)) by unfold slice point; fun_prop).continuousAt).continuousWithinAt

private theorem top_time_integrable (U V : F) (hU : ExteriorSmooth U) (hV : ExteriorSmooth V)
    (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hy : 0<Y) :
    IntervalIntegrable (fun p => topFlux U V p R Y) volume a b := by
  have hi : Integrable (fun z : ℝ×ℝ => transfer U V 1 (slice z.1 R (point z.2 Y)))
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (-1/2:ℝ) (1/2:ℝ)))) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact ((top_rectangle_continuous U V hU hV a b R Y ha hr hy).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  simpa only [topFlux,← neg_div,intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2),IntegrableOn]
    using hi.integral_prod_left

private theorem transfer_subtraction (F G : P → ℂ) (p R Y : ℝ) (c : ℂ)
    (hF : ∀ X : ℝ, ContDiffAt ℝ ∞ F ![p,R,X,Y])
    (hG : ∀ X : ℝ, ContDiffAt ℝ ∞ G ![p,R,X,Y]) :
    (∫ X in (-1/2:ℝ)..1/2, transfer F G 1 ![p,R,X,Y]-c)=
      D4BMOriginalModularOrbit.topFlux F G p R Y-c := by
  have hm : Continuous (fun X : ℝ => (![p,R,X,Y]:P)) := by fun_prop
  have hc : Continuous (fun X : ℝ => transfer F G 1 ![p,R,X,Y]) := by
    apply continuous_iff_continuousAt.mpr
    intro X
    change ContinuousAt ((fun z : P => F z*coordDeriv 3 G z) ∘
      (fun u : ℝ => (![p,R,u,Y]:P))) X
    exact ((hF X).continuousAt.mul (coordDeriv_contDiffAt (m:=∞) (hG X) (by simp) 3).continuousAt).comp
      (f:=fun u : ℝ => (![p,R,u,Y]:P)) hm.continuousAt
  have hslice (X : ℝ) : slice p R (GaloisForLFunctions.RHTower.SelbergMaassMean.point X Y)=![p,R,X,Y] := by
    simp [slice,GaloisForLFunctions.RHTower.SelbergMaassMean.point]
  unfold D4BMOriginalModularOrbit.topFlux
  simp_rw [hslice]
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const]
  norm_num [smul_eq_mul]


private theorem UniformRapid.horizontal_integral {ι : Type*} {F : ι → A → ℂ}
    (hF : UniformRapid F) (p : ι) (w : ℂ) :
    Tendsto (fun k : ℝ => ∫ X in (-1/2:ℝ)..1/2,weightedHeight w ![X,k]*F p ![X,k]) atTop (𝓝 0) := by
  letI : Nonempty ι := ⟨p⟩
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  filter_upwards [hF.uniform w (epsilon/2) (half_pos hepsilon)] with k hk
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(-1/2:ℝ)) (b:=(1/2:ℝ)) (fun X _ => (hk p X).le)
  norm_num only [sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,abs_one,mul_one] at hi
  rw [dist_zero_right]
  simpa only [neg_div] using hi.trans_lt (half_lt_self hepsilon)

private theorem transfer_pair_smooth (q r : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (j : Fin 4) :
    ExteriorSmooth (transferLeft q r br outer amp w j) ∧ ExteriorSmooth (transferRight q r br outer amp w j) := by
  have hU := source_smooth q br amp
  have hW := mode_smooth r w hw outer
  fin_cases j
  · exact ⟨hU,hW⟩
  · exact ⟨hW,hU⟩
  · exact ⟨lap_smooth hU,hW⟩
  · exact ⟨original_forcing_smooth q br amp,hW⟩

private theorem transfer_time_restoration (q r : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (a b R : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (j : Fin 4) :
    Tendsto (fun k : ℝ =>
      (∫ p in a..b,D4BMOriginalModularOrbit.topFlux (transferLeft q r br outer amp w j)
        (transferRight q r br outer amp w j) p R (Real.exp k))-
      ∑ i : Fin 3,(∫ p in a..b,modeTransferCoefficient q r br outer amp w j p R i)*
        Complex.exp (fluxExponent q r i*(k:ℂ))) atTop (𝓝 0) := by
  let F := transferLeft q r br outer amp w j
  let G := transferRight q r br outer amp w j
  let c := fun p i => modeTransferCoefficient q r br outer amp w j p R i
  have hs := transfer_pair_smooth q r br outer amp w hw j
  have hc := transfer_coefficient_continuous q r br outer amp w j R
  have h := UniformRapid.time_integral a b hab
    (fun p z => transfer F G 1 ![p,R,z 0,Real.exp (z 1)]-
      ∑ i : Fin 3,c p i*weightedHeight (fluxExponent q r i) z)
    (transfers_uniform q r br outer amp w hw a b R ha hab hr j) 0
  simp only [weightedHeight,Matrix.cons_val,zero_mul,Complex.exp_zero,one_mul] at h
  apply h.congr'
  filter_upwards [] with k
  have hinner (p : ℝ) (hp : p∈uIcc a b) :
      (∫ X in (-1/2:ℝ)..1/2,transfer F G 1 ![p,R,X,Real.exp k]-
        ∑ i : Fin 3,c p i*Complex.exp (fluxExponent q r i*(k:ℂ)))=
      D4BMOriginalModularOrbit.topFlux F G p R (Real.exp k)-
        ∑ i : Fin 3,c p i*Complex.exp (fluxExponent q r i*(k:ℂ)) := by
    have hp' : 0<p := ha.trans_le ((uIcc_of_le hab ▸ hp).1)
    exact transfer_subtraction F G p R (Real.exp k) _
      (fun X => hs.1 _ hp' hr (Real.exp_pos _)) (fun X => hs.2 _ hp' hr (Real.exp_pos _))
  rw [intervalIntegral.integral_congr hinner]
  have hi (i : Fin 3) : IntervalIntegrable (fun p => c p i*Complex.exp (fluxExponent q r i*(k:ℂ))) volume a b :=
    ((hc i).mul_const _).intervalIntegrable _ _
  have hiSum : IntervalIntegrable (fun p => ∑ i : Fin 3,c p i*Complex.exp (fluxExponent q r i*(k:ℂ))) volume a b := by
    have hsC : Continuous (fun p => ∑ i : Fin 3,c p i*Complex.exp (fluxExponent q r i*(k:ℂ))) := by
      simp only [Fin.sum_univ_three]
      exact ((((hc 0).mul_const _).add ((hc 1).mul_const _)).add ((hc 2).mul_const _))
    exact hsC.intervalIntegrable a b
  rw [intervalIntegral.integral_sub (top_time_integrable F G hs.1 hs.2 a b R (Real.exp k) ha hab hr (Real.exp_pos _))
    hiSum,intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  simp only [intervalIntegral.integral_mul_const,c,F,G]

private theorem transfer_fixed_restoration (q r : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (p R : ℝ) (hp : 0<p) (hr : 1<R) (j : Fin 4) :
    Tendsto (fun k : ℝ =>
      D4BMOriginalModularOrbit.topFlux (transferLeft q r br outer amp w j)
        (transferRight q r br outer amp w j) p R (Real.exp k)-
      ∑ i : Fin 3,modeTransferCoefficient q r br outer amp w j p R i*
        Complex.exp (fluxExponent q r i*(k:ℂ))) atTop (𝓝 0) := by
  have hs := transfer_pair_smooth q r br outer amp w hw j
  have h := (transfers_uniform q r br outer amp w hw p p R hp le_rfl hr j).horizontal_integral
    (⟨p,le_rfl,le_rfl⟩ : Icc p p) 0
  simp only [weightedHeight,Matrix.cons_val,zero_mul,Complex.exp_zero,one_mul] at h
  apply h.congr'
  filter_upwards [] with k
  exact transfer_subtraction _ _ p R (Real.exp k) _
    (fun X => hs.1 _ hp hr (Real.exp_pos _)) (fun X => hs.2 _ hp hr (Real.exp_pos _))

/-- The three coefficients forced by the complete original boundary identity.
The first term retains both temporal endpoints; the four moments retain
source value, source normal derivative, source Laplacian and full forcing. -/
def compactBoundaryCoefficient (q r : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (a b R : ℝ) (i : Fin 3) : ℂ :=
  let f := (R:ℂ)^2-1
  let mu := eigenvalue r
  let lam := mu-2
  let c := modeTransferCoefficient q r br outer amp w
  (-lam*(c 0 b R i-c 0 a R i)+w*
    (mu*(∫ p in a..b,c 1 p R i)-(∫ p in a..b,c 2 p R i)-
      2*lam*(∫ p in a..b,c 0 p R i)-(R:ℂ)^3/f*(∫ p in a..b,c 3 p R i)))/((R:ℂ)^2*f)

/-- The actual complete metric boundary admits its original three-power
subtraction after compact-time integration. All estimates and integral
admission are supplied by the original fields. No horizon or unbounded-time
limit, spectral specialization, or extinction premise is used. -/
theorem mode_complete_boundary_compact_cusp (q r : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (a b R : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) :
    Tendsto (fun k : ℝ =>
      (∫ p in a..b,
        (D4BMOriginalModularOrbit.modeCompleteTopFlux q r br outer amp w 0 p R (Real.exp k)-
          D4BMOriginalModularOrbit.modeCompleteTopFlux q r br outer amp w 1 p R (Real.exp k)/((R:ℂ)^2-1))/(R:ℂ)^2)-
      ∑ i : Fin 3,compactBoundaryCoefficient q r br outer amp w a b R i*
        Complex.exp (fluxExponent q r i*(k:ℂ))) atTop (𝓝 0) := by
  let mu := eigenvalue r
  let lam := mu-2
  let f := (R:ℂ)^2-1
  let den := (R:ℂ)^2*f
  have ht := transfer_time_restoration q r br outer amp w hw a b R ha hab hr
  have hb := transfer_fixed_restoration q r br outer amp w hw b R (ha.trans_le hab) hr 0
  have ha' := transfer_fixed_restoration q r br outer amp w hw a R ha hr 0
  have hbulk := ((((ht 1).const_mul mu).sub (ht 2)).sub ((ht 0).const_mul (2*lam))).sub
    ((ht 3).const_mul ((R:ℂ)^3/f))
  have h := (((hb.sub ha').const_mul (-lam)).add (hbulk.const_mul w)).div_const den
  simp only [sub_zero,mul_zero,add_zero,zero_div] at h
  apply h.congr'
  filter_upwards [] with k
  have hi (j : Fin 4) : IntervalIntegrable (fun p => D4BMOriginalModularOrbit.topFlux
      (transferLeft q r br outer amp w j) (transferRight q r br outer amp w j) p R (Real.exp k)) volume a b := by
    have hs := transfer_pair_smooth q r br outer amp w hw j
    exact top_time_integrable _ _ hs.1 hs.2 a b R (Real.exp k) ha hab hr (Real.exp_pos _)
  have hc := D4BMOriginalModularOrbit.mode_complete_boundary_time_transfer
    q r br outer amp w hw a b R (Real.exp k) ha hab hr (Real.exp_pos _)
  dsimp only at hc
  have h0 := hi 0
  have h1 := hi 1
  have h2 := hi 2
  have h3 := hi 3
  simp only [transferLeft,transferRight,Matrix.cons_val] at h0 h1 h2 h3
  rw [hc]
  rw [intervalIntegral.integral_sub (((h1.const_mul (eigenvalue r)).sub h2).sub (h0.const_mul (2*(eigenvalue r-2))))
        (h3.const_mul ((R:ℂ)^3/((R:ℂ)^2-1))),
      intervalIntegral.integral_sub ((h1.const_mul (eigenvalue r)).sub h2) (h0.const_mul (2*(eigenvalue r-2))),
      intervalIntegral.integral_sub (h1.const_mul (eigenvalue r)) h2]
  simp only [intervalIntegral.integral_const_mul,transferLeft,transferRight,Matrix.cons_val,
    compactBoundaryCoefficient,Fin.sum_univ_three]
  dsimp only [den,f,lam,mu]
  ring

/-- For either original diagonal/reflected arithmetic reader, compact-time
integration creates no constant cusp term. The subtraction is precisely the
one prescribed by the complete current's frequency family. -/
theorem mode_complete_boundary_compact_finitePart (q r : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (a b R : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R)
    (hqr : (r.1:ℂ).im=(q.1:ℂ).im ∨ (r.1:ℂ).im= -(q.1:ℂ).im) :
    Tendsto (fun k : ℝ =>
      (∫ p in a..b,
        (D4BMOriginalModularOrbit.modeCompleteTopFlux q r br outer amp w 0 p R (Real.exp k)-
          D4BMOriginalModularOrbit.modeCompleteTopFlux q r br outer amp w 1 p R (Real.exp k)/((R:ℂ)^2-1))/(R:ℂ)^2)-
      ∑ i : Fin 3,if fluxExponent q r i=0 then 0 else
        compactBoundaryCoefficient q r br outer amp w a b R i*Complex.exp (fluxExponent q r i*(k:ℂ)))
      atTop (𝓝 0) := by
  simpa only [fluxExponent_nonzero_original q r hqr,if_false] using
    mode_complete_boundary_compact_cusp q r br outer amp w hw a b R ha hab hr

end
end RHTower.D4BMOriginalCompactBoundary

import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSquareCuspJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativePrincipalPowerExpansion
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticCutoffMellin

/-! Principal coefficients and physical cusp Green flux of the actual six quartic
contact fields. The expansion retains all nine ordered products of the original
three Weyl powers. Genuine height derivatives and Laplacians act on their full
finite sums. The final coefficient identity matches bulk and boundary terms at
the original physical angular parameter; it does not assert flux extinction. -/

open Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMQuarticPrincipalExpansion
open D4BMAngularSeries D4BMGlobalAngularResponse D4BMSquareCuspJets
open D4BMJointSource D4BMJointWave
noncomputable section
set_option autoImplicit false

private abbrev Field := (Fin 2 → ℝ) → ℂ
open D4BMQuarticCutoffMellin

private def powerSum {ι : Type*} [Fintype ι] (w a : ι → ℂ) : Field :=
  fun z => ∑ i, a i*(z 1:ℂ)^(w i)
private def PowerRep {ι : Type*} [Fintype ι] (w a : ι → ℂ) (f : Field) : Prop :=
  ∀ z, 0<z 1 → f z=powerSum w a z
private theorem PowerRep.germ {ι : Type*} [Fintype ι] {w a : ι → ℂ} {f : Field}
    (h : PowerRep w a f) {z : Fin 2 → ℝ} (hz : 0<z 1) : f =ᶠ[𝓝 z] powerSum w a := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with v hv
  exact h v hv
private theorem PowerRep.add {ι : Type*} [Fintype ι] {w a b : ι → ℂ} {f g : Field}
    (hf : PowerRep w a f) (hg : PowerRep w b g) :
    PowerRep w (fun i => a i+b i) (fun z => f z+g z) := by
  intro z hz
  change f z+g z=powerSum w (fun i => a i+b i) z
  rw [hf z hz,hg z hz]
  simp only [powerSum,add_mul,Finset.sum_add_distrib]
private theorem PowerRep.scale {ι : Type*} [Fintype ι] {w a : ι → ℂ} {f : Field}
    (hf : PowerRep w a f) (c : ℂ) : PowerRep w (fun i => c*a i) (fun z => c*f z) := by
  intro z hz
  change c*f z=powerSum w (fun i => c*a i) z
  rw [hf z hz]
  simp only [powerSum,Finset.mul_sum,mul_assoc]
private theorem PowerRep.coeff {ι : Type*} [Fintype ι] {w a b : ι → ℂ} {f : Field}
    (hf : PowerRep w a f) (he : ∀ i, a i=b i) : PowerRep w b f := by
  have hab : a=b := funext he
  simpa only [hab] using hf
private theorem power_laplacian_sum {ι : Type*} (s : Finset ι) (f : ι → Field)
    (z : Fin 2 → ℝ) (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) z) :
    hyperbolicLaplacian (fun x => ∑ i ∈ s, f i x) z=∑ i ∈ s, hyperbolicLaplacian (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty,zero_mul] using
        (hyperbolicLaplacian_const_mul (f := fun _ : Fin 2 → ℝ => (1:ℂ)) (z := z) contDiffAt_const (0:ℂ))
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [hyperbolicLaplacian_add (hf i (Finset.mem_insert_self _ _))
        (ContDiffAt.sum (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]
private theorem PowerRep.lap {ι : Type*} [Fintype ι] {w a : ι → ℂ} {f : Field}
    (hf : PowerRep w a f) : PowerRep w (fun i => w i*(w i-1)*a i) (hyperbolicLaplacian f) := by
  intro z hz
  have hn : domain ∈ 𝓝 z := (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
  have hp (i : ι) : ContDiffAt ℝ 2 (fun z : Fin 2 → ℝ => (z 1:ℂ)^(w i)) z :=
    (height_cpow_contDiffOn (w i) 2).contDiffAt hn
  rw [hyperbolicLaplacian_congr (hf.germ hz)]
  unfold powerSum
  rw [power_laplacian_sum _ _ z (fun i _ => contDiffAt_const.mul (hp i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [hyperbolicLaplacian_const_mul (hp i),height_cpow_hyperbolicLaplacian _ z hz]
  ring
private theorem principal_gradient_height (X Y : ℂ) :
    D4BMAngularSeries.gradient X Y (Pi.single 1 1)=Y := by
  change (0:ℝ) • X+(1:ℝ) • Y=Y
  simp only [zero_smul,one_smul,zero_add]
private theorem PowerRep.height_derivative {ι : Type*} [Fintype ι] {w a : ι → ℂ} {f : Field}
    (hf : PowerRep w a f) (z : Fin 2 → ℝ) (hz : 0<z 1) :
    coordDeriv 1 f z=∑ i, a i*w i*(z 1:ℂ)^(w i-1) := by
  have hd := HasFDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    (height_cpow_hasFDerivAt (w i) z hz).const_mul (a i))
  rw [coordDeriv,(hf.germ hz).fderiv_eq]
  change fderiv ℝ (fun z : Fin 2 → ℝ => ∑ i, a i*(z 1:ℂ)^(w i)) z (Pi.single 1 1)=_
  rw [hd.fderiv]
  simp only [sum_apply,smul_apply,smul_eq_mul,principal_gradient_height]
  apply Finset.sum_congr rfl
  intro i _
  ring
private def convolution3 (a b : Fin 3 → ℂ) : Fin 5 → ℂ :=
  ![a 0*b 0,a 0*b 1+a 1*b 0,a 0*b 2+a 1*b 1+a 2*b 0,a 1*b 2+a 2*b 1,a 2*b 2]
private def pairIndex (i j : Fin 3) : Fin 5 := ⟨i.val+j.val,by omega⟩
private theorem sum_five (v : Fin 5 → ℂ) :
    ∑ j, v j=v 0+v 1+v 2+v 3+v 4 := by
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_three]
  change v 0+(v 1+(v 2+v 3+v 4))=v 0+v 1+v 2+v 3+v 4
  ring

private theorem convolution3_sum (a b : Fin 3 → ℂ) (v : Fin 5 → ℂ) :
    (∑ i : Fin 3, ∑ j : Fin 3, (a i*b j)*v (pairIndex i j))=
      ∑ k : Fin 5, convolution3 a b k*v k := by
  simp only [Fin.sum_univ_three]
  rw [sum_five]
  change
    (a 0*b 0*v 0+a 0*b 1*v 1+a 0*b 2*v 2)+
      (a 1*b 0*v 1+a 1*b 1*v 2+a 1*b 2*v 3)+
      (a 2*b 0*v 2+a 2*b 1*v 3+a 2*b 2*v 4)=
    (a 0*b 0)*v 0+(a 0*b 1+a 1*b 0)*v 1+
      (a 0*b 2+a 1*b 1+a 2*b 0)*v 2+(a 1*b 2+a 2*b 1)*v 3+(a 2*b 2)*v 4
  ring

private theorem principal_exponent_add (q : XiZeroCopy) (i j : Fin 3) :
    nativePrincipalPowerExponent q i+nativePrincipalPowerExponent q j=
      quarticPrincipalExponent q (pairIndex i j) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [nativePrincipalPowerExponent,quarticPrincipalExponent,pairIndex] <;> ring
private theorem PowerRep.mul3 {q : XiZeroCopy} {a b : Fin 3 → ℂ} {f g : Field}
    (hf : PowerRep (nativePrincipalPowerExponent q) a f)
    (hg : PowerRep (nativePrincipalPowerExponent q) b g) :
    PowerRep (quarticPrincipalExponent q) (convolution3 a b) (fun z => f z*g z) := by
  intro z hz
  change f z*g z=powerSum (quarticPrincipalExponent q) (convolution3 a b) z
  have hn : (z 1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hp (i j : Fin 3) : (z 1:ℂ)^(nativePrincipalPowerExponent q i)*
      (z 1:ℂ)^(nativePrincipalPowerExponent q j)=
        (z 1:ℂ)^(quarticPrincipalExponent q (pairIndex i j)) := by
    rw [← Complex.cpow_add _ _ hn,principal_exponent_add]
  rw [hf z hz,hg z hz]
  unfold powerSum
  calc
    _ = ∑ i : Fin 3, ∑ j : Fin 3, (a i*b j)*
        ((z 1:ℂ)^(nativePrincipalPowerExponent q i)*(z 1:ℂ)^(nativePrincipalPowerExponent q j)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i : Fin 3, ∑ j : Fin 3, (a i*b j)*
        (z 1:ℂ)^(quarticPrincipalExponent q (pairIndex i j)) := by simp_rw [hp]
    _ = _ := convolution3_sum a b (fun j => (z 1:ℂ)^(quarticPrincipalExponent q j))
private def contactCoefficient (q : XiZeroCopy) (i : Fin 3) : ℂ :=
  let c := 7*((center q)^(2 : ℕ)-1/4)-2
  let r := nativePrincipalPowerExponent q i
  (c-2*r*(r-1))*nativePrincipalPowerCoefficient q i/8
private def spinTwoCoefficient (q : XiZeroCopy) (i : Fin 3) : ℂ :=
  let r := nativePrincipalPowerExponent q i
  (-r)*(r-1)*(r*(r-1)-2)*nativePrincipalPowerCoefficient q i

/-- All coefficients of each actual quartic principal expression, retaining every ordered Weyl pair. -/
def quarticPrincipalCoefficient (q : XiZeroCopy) (slot : Fin 6) : Fin 5 → ℂ :=
  let c := 7*((center q)^(2 : ℕ)-1/4)-2
  let Q2 := convolution3 (nativePrincipalPowerCoefficient q) (nativePrincipalPowerCoefficient q)
  let J2 := convolution3 (contactCoefficient q) (contactCoefficient q)
  let LJ := fun i => nativePrincipalPowerExponent q i*(nativePrincipalPowerExponent q i-1)*contactCoefficient q i
  let H := fun j => 2*J2 j+(c*(c-4)/96)*Q2 j
  ![Q2,J2,fun j => (1/2:ℂ)*(quarticPrincipalExponent q j*(quarticPrincipalExponent q j-1)*J2 j)+
      (-1:ℂ)*convolution3 (contactCoefficient q) LJ j,
    convolution3 (contactCoefficient q) (spinTwoCoefficient q),H,
    fun j => quarticPrincipalExponent q j*(quarticPrincipalExponent q j-1)*H j] slot
private def Qprincipal (q : XiZeroCopy) : Field :=
  fun z => (1/2:ℂ)*(principal (center q) z*principal (center q) z)
private def Jprincipal (q : XiZeroCopy) : Field :=
  fun z => (1/8:ℂ)*((7*((center q)^(2 : ℕ)-1/4)-2)*Qprincipal q z+
    (-2)*hyperbolicLaplacian (Qprincipal q) z)
private def Rprincipal (q : XiZeroCopy) : Field :=
  fun z => (-1)*hyperbolicLaplacian (hyperbolicLaplacian (Qprincipal q)) z+
    2*hyperbolicLaplacian (Qprincipal q) z
private theorem Q_power_rep (q : XiZeroCopy) :
    PowerRep (nativePrincipalPowerExponent q) (nativePrincipalPowerCoefficient q)
      (Qprincipal q) := by
  intro z hz
  have he := nativePrincipalSquare_eq_power_sum q hz
  change principalSquare q ![0,z 1]=_ at he
  change (1/2:ℂ)*(principal (center q) z*principal (center q) z)=
    ∑ i : Fin 3, nativePrincipalPowerCoefficient q i*(z 1:ℂ)^(nativePrincipalPowerExponent q i)
  rw [← he]
  change (1/2:ℂ)*(principal (center q) z*principal (center q) z)=(principal (center q) z)^(2 : ℕ)/2
  ring
private theorem J_power_rep (q : XiZeroCopy) :
    PowerRep (nativePrincipalPowerExponent q) (contactCoefficient q)
      (Jprincipal q) := by
  have h := (((Q_power_rep q).scale (7*((center q)^(2 : ℕ)-1/4)-2)).add
    ((Q_power_rep q).lap.scale (-2))).scale (1/8)
  apply h.coeff
  intro i
  dsimp [contactCoefficient]
  ring
private theorem R_power_rep (q : XiZeroCopy) :
    PowerRep (nativePrincipalPowerExponent q) (spinTwoCoefficient q)
      (Rprincipal q) := by
  have h := ((Q_power_rep q).lap.lap.scale (-1)).add ((Q_power_rep q).lap.scale 2)
  apply h.coeff
  intro i
  dsimp [spinTwoCoefficient]
  ring
private theorem quartic_principal_rep (q : XiZeroCopy) (slot : Fin 6) :
    PowerRep (quarticPrincipalExponent q) (quarticPrincipalCoefficient q slot)
      (quarticContactPrincipal q slot) := by
  have hQ := Q_power_rep q
  have hJ := J_power_rep q
  have hR := R_power_rep q
  have hQ2 := hQ.mul3 hQ
  have hJ2 := hJ.mul3 hJ
  have hG := (hJ2.lap.scale (1/2)).add ((hJ.mul3 hJ.lap).scale (-1))
  have hJR := hJ.mul3 hR
  let c : ℂ := 7*((center q)^(2 : ℕ)-1/4)-2
  have hH := (hJ2.scale 2).add (hQ2.scale (c*(c-4)/96))
  have hLH := hH.lap
  fin_cases slot
  · exact hQ2
  · exact hJ2
  · exact hG
  · exact hJR
  · exact hH
  · exact hLH

/-- Complete principal evaluations in the five source-derived height powers. -/
theorem quarticContactPrincipal_eq_power_sum (q : XiZeroCopy) (slot : Fin 6) (z : UpperHalfPlane) :
    quarticContactPrincipal q slot (coordinates z)=∑ j : Fin 5,
      quarticPrincipalCoefficient q slot j*(z.im:ℂ)^(quarticPrincipalExponent q j) :=
  quartic_principal_rep q slot (coordinates z) z.im_pos
/-- Genuine height derivative with each original indicial multiplier. -/
theorem quarticContactPrincipal_heightDeriv_eq_power_sum (q : XiZeroCopy) (slot : Fin 6)
    (z : UpperHalfPlane) :
    coordDeriv 1 (quarticContactPrincipal q slot) (coordinates z)=∑ j : Fin 5,
      quarticPrincipalCoefficient q slot j*quarticPrincipalExponent q j*
        (z.im:ℂ)^(quarticPrincipalExponent q j-1) :=
  (quartic_principal_rep q slot).height_derivative (coordinates z) z.im_pos
/-- The actual principal Laplacian without an assigned principal eigen-equation. -/
theorem quarticContactPrincipal_laplacian_eq_power_sum (q : XiZeroCopy) (slot : Fin 6)
    (z : UpperHalfPlane) :
    hyperbolicLaplacian (quarticContactPrincipal q slot) (coordinates z)=∑ j : Fin 5,
      (quarticPrincipalExponent q j*(quarticPrincipalExponent q j-1)*
        quarticPrincipalCoefficient q slot j)*(z.im:ℂ)^(quarticPrincipalExponent q j) :=
  (quartic_principal_rep q slot).lap (coordinates z) z.im_pos
private theorem physical_principal_height_derivative (q : XiZeroCopy) (z : Fin 2 → ℝ)
    (hz : 0<z 1) :
    coordDeriv 1 (principal (physicalAngularParameter q)) z=
      reflectedCompletedLambda ((q.1:ℂ)-1)*(1-(q.1:ℂ)/2)*(z 1:ℂ)^(-(q.1:ℂ)/2) := by
  have he : principal (physicalAngularParameter q)=fun z =>
      reflectedCompletedLambda ((q.1:ℂ)-1)*(z 1:ℂ)^(1-(q.1:ℂ)/2) :=
    funext (physicalScalar_principal q)
  have hd := (height_cpow_hasFDerivAt (1-(q.1:ℂ)/2) z hz).const_mul
    (reflectedCompletedLambda ((q.1:ℂ)-1))
  rw [coordDeriv,he,hd.fderiv]
  simp only [smul_apply,smul_eq_mul,principal_gradient_height]
  rw [show (1-(q.1:ℂ)/2)-1= -(q.1:ℂ)/2 by ring]
  ring

/-- Physical principal Green flux retaining its surviving Weyl coefficient and every source power. -/
theorem quarticContactPrincipalGreenFlux_physical_eq (q : XiZeroCopy) (slot : Fin 6)
    (z : UpperHalfPlane) :
    quarticContactPrincipalGreenFlux q slot (physicalAngularParameter q) (coordinates z)=
      reflectedCompletedLambda ((q.1:ℂ)-1)*∑ j : Fin 5,
        quarticPrincipalCoefficient q slot j*(quarticPrincipalExponent q j-1+(q.1:ℂ)/2)*
          (z.im:ℂ)^(quarticPhysicalMellinExponent q j) := by
  have hrep := quartic_principal_rep q slot
  have hn : (z.im:ℂ)≠0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
  unfold quarticContactPrincipalGreenFlux
  rw [physicalScalar_principal,hrep.height_derivative _ z.im_pos,
    hrep (coordinates z) z.im_pos,physical_principal_height_derivative q _ z.im_pos]
  change (reflectedCompletedLambda ((q.1:ℂ)-1)*(z.im:ℂ)^(1-(q.1:ℂ)/2))*
      (∑ j : Fin 5, quarticPrincipalCoefficient q slot j*quarticPrincipalExponent q j*
        (z.im:ℂ)^(quarticPrincipalExponent q j-1))-
      (∑ j : Fin 5, quarticPrincipalCoefficient q slot j*(z.im:ℂ)^(quarticPrincipalExponent q j))*
      (reflectedCompletedLambda ((q.1:ℂ)-1)*(1-(q.1:ℂ)/2)*(z.im:ℂ)^(-(q.1:ℂ)/2))=_
  rw [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h₁ : (z.im:ℂ)^(1-(q.1:ℂ)/2)*(z.im:ℂ)^(quarticPrincipalExponent q j-1)=
      (z.im:ℂ)^(quarticPhysicalMellinExponent q j) := by
    rw [← Complex.cpow_add _ _ hn]
    congr 1
    unfold quarticPhysicalMellinExponent
    ring
  have h₂ : (z.im:ℂ)^(quarticPrincipalExponent q j)*(z.im:ℂ)^(-(q.1:ℂ)/2)=
      (z.im:ℂ)^(quarticPhysicalMellinExponent q j) := by
    rw [← Complex.cpow_add _ _ hn]
    congr 1
    unfold quarticPhysicalMellinExponent
    ring
  calc
    _ = reflectedCompletedLambda ((q.1:ℂ)-1)*
        (quarticPrincipalCoefficient q slot j*quarticPrincipalExponent q j*
          ((z.im:ℂ)^(1-(q.1:ℂ)/2)*(z.im:ℂ)^(quarticPrincipalExponent q j-1))-
          quarticPrincipalCoefficient q slot j*(1-(q.1:ℂ)/2)*
          ((z.im:ℂ)^(quarticPrincipalExponent q j)*(z.im:ℂ)^(-(q.1:ℂ)/2))) := by ring
    _ = _ := by rw [h₁,h₂]; ring

/-- Each original H coefficient has exactly the bulk/flux indicial factor
needed by the physical second Green identity. -/
theorem quarticContactPrincipal_physical_bulk_flux_coefficient (q : XiZeroCopy) (j : Fin 5) :
    quarticPrincipalCoefficient q 5 j-
      ((q.1:ℂ)*((q.1:ℂ)-2)/4)*quarticPrincipalCoefficient q 4 j=
      quarticPhysicalMellinExponent q j*
        (quarticPrincipalExponent q j-1+(q.1:ℂ)/2)*quarticPrincipalCoefficient q 4 j := by
  change quarticPrincipalExponent q j*(quarticPrincipalExponent q j-1)*
      quarticPrincipalCoefficient q 4 j-
      ((q.1:ℂ)*((q.1:ℂ)-2)/4)*quarticPrincipalCoefficient q 4 j=_
  unfold quarticPhysicalMellinExponent
  ring

end
end RHTower.D4BMQuarticPrincipalExpansion

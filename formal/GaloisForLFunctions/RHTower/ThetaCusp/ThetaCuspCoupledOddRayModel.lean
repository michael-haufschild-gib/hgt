import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFirstAtomOddFourPositivity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCompensationNeutralAnchor
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCoupledOddDrift
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspMiddleCompensationReserve
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspScaleSevenCompensationSource

/-!
# Canonical coupled odd-four reserve on the scale-five ray

The exact first-atom central form, with the literal canonical compensation
and moving-coordinate drift, retains a one-seventh quadratic reserve for
all scales at least five. Four endpoint polynomial matrices prove the
sign; full-source mass, slope, and center estimates place the actual
coefficients between those endpoints. The native assembly separately
retains both unequal pairs, the pure second pair, and the complete tail.
-/

namespace RHTower.ThetaCuspCoupledOddRayModel
noncomputable section
-- Homogenized exact first-atom matrix, compensation lower endpoint,
-- drift endpoint, and the proposed 1/7 reserve. Source identification follows separately.
private def sourceSigmaHom (a b : ℝ) (far : Bool) : ℝ :=
  if far then 3000000000/4718592*(3*b^5-13*a^2*b^3/50)*(2*a-3*b)^2
  else 3000000000*(101/100)^2/4718592*
    (b^5+9*a*b^4/5-2*a^2*b^3/5)*(2*a-3*b)^2

private def sourceTauHom (a b : ℝ) (far drift : Bool) : ℝ :=
  if drift then
    if far then 3000000000*(101/100)^2/12582912*a*b^4*(2*a-3*b)^2
    else 3000000000*(101/100)^2/7864320*
      (a*b^4-107*b^5/40)*(2*a-3*b)^2
  else 0

private def entry00 (a b : ℝ) : ℝ := a^5*((1-1/7)*(2*a-3*b)^2+6*b^2)
private def entry01 (a b : ℝ) : ℝ := -6*a^5*b^2
private def entry11 (a b : ℝ) : ℝ :=
  ((2/3-1/7)*a^5-a^4*b/2)*(2*a-3*b)^2+12*a^5*b^2-6*a^4*b^3
private def entry12 (a b : ℝ) : ℝ :=
  5*a^4*b/12*(2*a-3*b)^2+15*a^4*b^3-10*a^5*b^2
private def entry13 (a b : ℝ) : ℝ := -15*a^4*b^3/2
private def entry22 (a b : ℝ) (far : Bool) : ℝ :=
  ((5/6-1/7)*a^5-25*a^4*b/12+25*a^3*b^2/24)*(2*a-3*b)^2+
    25*a^5*b^2-125*a^4*b^3/2+75*a^3*b^4/4+sourceSigmaHom a b far
private def entry23 (a b : ℝ) (far drift : Bool) : ℝ :=
  (5*a^4*b/4-25*a^3*b^2/16)*(2*a-3*b)^2-
    15*a^5*b^2+75*a^4*b^3-225*a^3*b^4/4-sourceTauHom a b far drift
private def entry33 (a b : ℝ) : ℝ :=
  ((5/7-1/7)*a^5-15*a^4*b/4+105*a^3*b^2/16-75*a^2*b^3/32)*(2*a-3*b)^2+
    30*a^5*b^2-180*a^4*b^3+2025*a^3*b^4/8-225*a^2*b^5/4

private def minor1 (a b : ℝ) : ℝ := entry00 a b
private def minor2 (a b : ℝ) : ℝ := entry00 a b*entry11 a b-(entry01 a b)^2
private def minor3 (a b : ℝ) (far : Bool) : ℝ :=
  minor2 a b*entry22 a b far-entry00 a b*(entry12 a b)^2
private def minor4 (a b : ℝ) (far drift : Bool) : ℝ :=
  minor2 a b*(entry22 a b far*entry33 a b-(entry23 a b far drift)^2)-
    entry00 a b*((entry12 a b)^2*entry33 a b-
      2*entry12 a b*entry13 a b*entry23 a b far drift+(entry13 a b)^2*entry22 a b far)

private def minorNorm1 (a b : ℝ) : {r : ℝ // minor1 a b=r} := by
  have h : minor1 a b=minor1 a b := rfl
  conv at h =>
    rhs
    norm_num [minor1,minor2,minor3,minor4,entry00,entry01,entry11,entry12,entry13,entry22,entry23,entry33,sourceSigmaHom,sourceTauHom]
    ring_nf
  exact ⟨_,h⟩

private def minorNorm2 (a b : ℝ) : {r : ℝ // minor2 a b=r} := by
  have h : minor2 a b=minor2 a b := rfl
  conv at h =>
    rhs
    norm_num [minor1,minor2,minor3,minor4,entry00,entry01,entry11,entry12,entry13,entry22,entry23,entry33,sourceSigmaHom,sourceTauHom]
    ring_nf
  exact ⟨_,h⟩

private def minorNorm3 (a b : ℝ) (far : Bool) : {r : ℝ // minor3 a b far=r} := by
  have h : minor3 a b far=minor3 a b far := rfl
  conv at h =>
    rhs
    unfold minor3
    simp only [(minorNorm2 a b).property]
    dsimp only [minorNorm2]
    unfold entry00 entry12 entry22
    unfold sourceSigmaHom
    ring_nf
  exact ⟨_,h⟩

private def minorNorm4 (a b : ℝ) (far drift : Bool) : {r : ℝ // minor4 a b far drift=r} := by
  have h : minor4 a b far drift=minor4 a b far drift := rfl
  conv at h =>
    rhs
    unfold minor4
    simp only [(minorNorm2 a b).property]
    dsimp only [minorNorm2]
    unfold entry00 entry12 entry22
    unfold entry13 entry23 entry33 sourceTauHom
    unfold sourceSigmaHom
    ring_nf
  exact ⟨_,h⟩

open Matrix

private def sigmaFloor (q : ℝ) (far : Bool) : ℝ :=
  if far then 3000000000*(3-13*q^2/50)/(4718592*q^5)
  else 3000000000*(101/100)^2*(1+9*q/5-2*q^2/5)/(4718592*q^5)

private def tauCeiling (q : ℝ) (far : Bool) : ℝ :=
  if far then 3000000000*(101/100)^2/(12582912*q^4)
  else 3000000000*(101/100)^2*(q-107/40)/(7864320*q^5)

private def endpointMatrix (q : ℝ) (far drift : Bool) (i j : Fin 4) : ℝ :=
  ThetaCuspOddCentral.centralMatrix (1/(2*q)) (6/(2*q-3)^2) i j -
    (if i=j then 1/7 else 0)+
    (if i=2 ∧ j=2 then sigmaFloor q far else 0)-
    (if (i=2 ∧ j=3) ∨ (i=3 ∧ j=2) then if drift then tauCeiling q far else 0 else 0)

private def homMatrix (a b : ℝ) (far drift : Bool) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![entry00 a b,entry01 a b,0,0;
     entry01 a b,entry11 a b,entry12 a b,entry13 a b;
     0,entry12 a b,entry22 a b far,entry23 a b far drift;
     0,entry13 a b,entry23 a b far drift,entry33 a b]

private theorem centralMatrix_explicit (v h : ℝ) : ThetaCuspOddCentral.centralMatrix v h =
      !![1+h,-h,0,0;
         -h,2/3-v+2*h*(1-v),5*v/6+h*(5*v-5/3),-5*v*h/2;
         0,5*v/6+h*(5*v-5/3),(5/6)*(1+5*h)*(1-5*v)+(25/6)*v^2*(1+3*h),
           5*v/2-25*v^2/4+h*(-5/2+25*v-75*v^2/2);
         0,-5*v*h/2,5*v/2-25*v^2/4+h*(-5/2+25*v-75*v^2/2),
           (5/7)*(1+7*h)-(15/2)*v*(1+8*h)+(15/4)*v^2*(7+45*h)-(75/4)*v^3*(1+4*h)] := rfl

private theorem source_endpoint_row0 {q : ℝ} (hq : 5 ≤ q) (far drift : Bool)
    (j : Fin 4) :
    q^5*(2*q-3)^2*endpointMatrix q far drift 0 j=homMatrix q 1 far drift 0 j := by
  have hq0 : q ≠ 0 := by linarith
  have hq3 : 2*q-3 ≠ 0 := by linarith
  have hq3n : -3+q*2 ≠ 0 := by linarith
  have hD : 9-q*12+q^2*4 ≠ 0 := by
    rw [show 9-q*12+q^2*4=(2*q-3)^2 by ring]
    exact pow_ne_zero 2 hq3
  unfold endpointMatrix
  rw [centralMatrix_explicit]
  fin_cases j <;>
    norm_num [homMatrix,entry00,entry01,entry11,entry12,entry13,entry22,entry23,entry33,
      Matrix.cons_val_two,Matrix.cons_val_three,Fin.ext_iff]
  all_goals field_simp [hq0,hq3]
  all_goals ring_nf
  all_goals field_simp [hq0,hq3,hq3n,hD]
  all_goals ring

private theorem source_endpoint_row1 {q : ℝ} (hq : 5 ≤ q) (far drift : Bool)
    (j : Fin 4) :
    q^5*(2*q-3)^2*endpointMatrix q far drift 1 j=homMatrix q 1 far drift 1 j := by
  have hq0 : q ≠ 0 := by linarith
  have hq3 : 2*q-3 ≠ 0 := by linarith
  have hq3n : -3+q*2 ≠ 0 := by linarith
  have hD : 9-q*12+q^2*4 ≠ 0 := by
    rw [show 9-q*12+q^2*4=(2*q-3)^2 by ring]
    exact pow_ne_zero 2 hq3
  unfold endpointMatrix
  rw [centralMatrix_explicit]
  fin_cases j <;>
    norm_num [homMatrix,entry00,entry01,entry11,entry12,entry13,entry22,entry23,entry33,
      Matrix.cons_val_two,Matrix.cons_val_three,Fin.ext_iff]
  all_goals field_simp [hq0,hq3]
  all_goals ring_nf
  all_goals field_simp [hq0,hq3,hq3n,hD]
  all_goals ring

private theorem source_endpoint_row2 {q : ℝ} (hq : 5 ≤ q) (far drift : Bool)
    (j : Fin 4) :
    q^5*(2*q-3)^2*endpointMatrix q far drift 2 j=homMatrix q 1 far drift 2 j := by
  have hq0 : q ≠ 0 := by linarith
  have hq3 : 2*q-3 ≠ 0 := by linarith
  have hq3n : -3+q*2 ≠ 0 := by linarith
  have hD : 9-q*12+q^2*4 ≠ 0 := by
    rw [show 9-q*12+q^2*4=(2*q-3)^2 by ring]
    exact pow_ne_zero 2 hq3
  unfold endpointMatrix
  rw [centralMatrix_explicit]
  fin_cases j <;>
    norm_num [homMatrix,entry00,entry01,entry11,entry12,entry13,entry22,entry23,entry33,
      Matrix.cons_val_two,Matrix.cons_val_three,Fin.ext_iff]
  all_goals
    cases far <;> cases drift <;>
      norm_num [sigmaFloor,tauCeiling,sourceSigmaHom,sourceTauHom]
  all_goals field_simp [hq0,hq3]
  all_goals ring_nf
  all_goals field_simp [hq0,hq3,hq3n,hD]
  all_goals ring

private theorem source_endpoint_row3 {q : ℝ} (hq : 5 ≤ q) (far drift : Bool)
    (j : Fin 4) :
    q^5*(2*q-3)^2*endpointMatrix q far drift 3 j=homMatrix q 1 far drift 3 j := by
  have hq0 : q ≠ 0 := by linarith
  have hq3 : 2*q-3 ≠ 0 := by linarith
  have hq3n : -3+q*2 ≠ 0 := by linarith
  have hD : 9-q*12+q^2*4 ≠ 0 := by
    rw [show 9-q*12+q^2*4=(2*q-3)^2 by ring]
    exact pow_ne_zero 2 hq3
  unfold endpointMatrix
  rw [centralMatrix_explicit]
  fin_cases j <;>
    norm_num [homMatrix,entry00,entry01,entry11,entry12,entry13,entry22,entry23,entry33,
      Matrix.cons_val_two,Matrix.cons_val_three,Fin.ext_iff]
  all_goals
    cases far <;> cases drift <;>
      norm_num [sigmaFloor,tauCeiling,sourceSigmaHom,sourceTauHom]
  all_goals field_simp [hq0,hq3]
  all_goals ring_nf
  all_goals field_simp [hq0,hq3,hq3n,hD]
  all_goals ring

private theorem source_endpoint_identify {q : ℝ} (hq : 5 ≤ q) (far drift : Bool)
    (i j : Fin 4) :
    q^5*(2*q-3)^2*endpointMatrix q far drift i j=homMatrix q 1 far drift i j := by
  fin_cases i
  · exact source_endpoint_row0 hq far drift j
  · exact source_endpoint_row1 hq far drift j
  · exact source_endpoint_row2 hq far drift j
  · exact source_endpoint_row3 hq far drift j

private theorem minor1_pos {u b : ℝ} (hu : 0 ≤ u) (hb : 0 < b) :
    0 < minor1 (5*b+u) b := by
  rw [(minorNorm1 (5*b+u) b).property]
  dsimp only [minorNorm1]
  ring_nf
  positivity

private theorem minor2_pos {u b : ℝ} (hu : 0 ≤ u) (hb : 0 < b) :
    0 < minor2 (5*b+u) b := by
  rw [(minorNorm2 (5*b+u) b).property]
  dsimp only [minorNorm2]
  ring_nf
  positivity

private theorem minor3_middle_pos {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hpos : 0 < u+t) :
    0 < minor3 (5*u+8*t) (u+t) false := by
  rw [(minorNorm3 (5*u+8*t) (u+t) false).property]
  dsimp only [minorNorm3]
  norm_num
  ring_nf
  rcases lt_or_eq_of_le hu with hu | hu
  · positivity
  · have htpos : 0 < t := by linarith
    subst u
    positivity

private theorem minor4_middle_pos {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hpos : 0 < u+t) :
    0 < minor4 (5*u+8*t) (u+t) false false := by
  rw [(minorNorm4 (5*u+8*t) (u+t) false false).property]
  dsimp only [minorNorm4]
  norm_num
  ring_nf
  rcases lt_or_eq_of_le hu with hu | hu
  · positivity
  · have htpos : 0 < t := by linarith
    subst u
    positivity

private theorem minor4_middle_drift_pos {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hpos : 0 < u+t) :
    0 < minor4 (5*u+8*t) (u+t) false true := by
  rw [(minorNorm4 (5*u+8*t) (u+t) false true).property]
  dsimp only [minorNorm4]
  norm_num
  ring_nf
  rcases lt_or_eq_of_le hu with hu | hu
  · positivity
  · have htpos : 0 < t := by linarith
    subst u
    positivity

private theorem minor3_far_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < minor3 (8+u) 1 true := by
  rw [(minorNorm3 (8+u) 1 true).property]
  dsimp only [minorNorm3]
  norm_num
  ring_nf
  positivity

private theorem minor4_far_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < minor4 (8+u) 1 true false := by
  rw [(minorNorm4 (8+u) 1 true false).property]
  dsimp only [minorNorm4]
  norm_num
  ring_nf
  positivity

private theorem minor4_far_drift_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < minor4 (8+u) 1 true true := by
  rw [(minorNorm4 (8+u) 1 true true).property]
  dsimp only [minorNorm4]
  norm_num
  ring_nf
  positivity

private def reducedDetSym4 (a b c d e f g h i j : ℝ) : ℝ :=
  (a*e*h-a*f^2-b^2*h+2*b*c*f-c^2*e)*j -
  ((e*h-f^2)*d^2+2*(c*f-b*h)*d*g+2*(b*f-c*e)*d*i+
   (a*h-c^2)*g^2+2*(b*c-a*f)*g*i+(a*e-b^2)*i^2)

private def symQuadratic (a b c d e f g h i j x y z w : ℝ) : ℝ :=
  a*x^2+2*b*x*y+2*c*x*z+2*d*x*w+e*y^2+2*f*y*z+2*g*y*w+
    h*z^2+2*i*z*w+j*w^2

private theorem symQuadratic_nonneg {a b c d e f g h i j : ℝ}
    (ha : 0 < a) (h2 : 0 < a*e-b^2)
    (h3 : 0 < a*e*h-a*f^2-b^2*h+2*b*c*f-c^2*e)
    (h4 : 0 ≤ reducedDetSym4 a b c d e f g h i j) (x y z w : ℝ) :
    0 ≤ symQuadratic a b c d e f g h i j x y z w := by
  let D2 := a*e-b^2
  let D3 := a*e*h-a*f^2-b^2*h+2*b*c*f-c^2*e
  let E := a*e*i-a*f*g-b^2*i+b*c*g+b*d*f-c*d*e
  have he : a*D2*D3*symQuadratic a b c d e f g h i j x y z w =
      D2*D3*(a*x+b*y+c*z+d*w)^2 +
      D3*(D2*y+(a*f-b*c)*z+(a*g-b*d)*w)^2 +
      a*(D3*z+E*w)^2+a*D2*reducedDetSym4 a b c d e f g h i j*w^2 := by
    dsimp [D2,D3,E,symQuadratic,reducedDetSym4]
    ring
  have hd2 : 0 < D2 := h2
  have hd3 : 0 < D3 := h3
  have hp : 0 ≤ a*D2*D3*symQuadratic a b c d e f g h i j x y z w := by
    rw [he]
    positivity
  exact (mul_nonneg_iff_of_pos_left (mul_pos (mul_pos ha hd2) hd3)).mp hp

private theorem hom_quadratic_nonneg {a b : ℝ} (far drift : Bool)
    (h1 : 0 < minor1 a b) (h2 : 0 < minor2 a b)
    (h3 : 0 < minor3 a b far) (h4 : 0 ≤ minor4 a b far drift) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i*y j*homMatrix a b far drift i j := by
  have h3' : 0 < entry00 a b*entry11 a b*entry22 a b far-
      entry00 a b*(entry12 a b)^2-(entry01 a b)^2*entry22 a b far+
      2*entry01 a b*0*entry12 a b-0^2*entry11 a b := by
    convert h3 using 1
    unfold minor3 minor2
    ring
  have h4' : 0 ≤ reducedDetSym4 (entry00 a b) (entry01 a b) 0 0
      (entry11 a b) (entry12 a b) (entry13 a b) (entry22 a b far)
      (entry23 a b far drift) (entry33 a b) := by
    convert h4 using 1
    unfold reducedDetSym4 minor4 minor2
    ring
  have h := symQuadratic_nonneg h1 h2 h3' h4' (y 0) (y 1) (y 2) (y 3)
  convert h using 1
  norm_num [homMatrix,Fin.sum_univ_succ,symQuadratic,minor1,
      Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals simp only [show (Fin.succ (2 : Fin 3) : Fin 4)=3 by rfl]
  all_goals ring_nf

private theorem first_two_pos {q : ℝ} (hq : 5 ≤ q) :
    0 < minor1 q 1 ∧ 0 < minor2 q 1 := by
  have h1 := minor1_pos (u:=q-5) (b:=1) (by linarith) (by norm_num)
  have h2 := minor2_pos (u:=q-5) (b:=1) (by linarith) (by norm_num)
  rw [show 5*(1:ℝ)+(q-5)=q by ring] at h1 h2
  exact ⟨h1,h2⟩

private theorem hom_middle_nonneg {q : ℝ} (hq : 5 ≤ q) (hqU : q ≤ 8)
    (drift : Bool) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i*y j*homMatrix q 1 false drift i j := by
  let u := (8-q)/3
  let t := (q-5)/3
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ha : 5*u+8*t=q := by dsimp [u,t]; ring
  have hb : u+t=1 := by dsimp [u,t]; ring
  have hpos : 0 < u+t := by rw [hb]; norm_num
  obtain ⟨h1,h2⟩ := first_two_pos hq
  have h3 := minor3_middle_pos hu ht hpos
  rw [ha,hb] at h3
  have h4 : 0 < minor4 q 1 false drift := by
    cases drift
    · have h := minor4_middle_pos hu ht hpos
      rwa [ha,hb] at h
    · have h := minor4_middle_drift_pos hu ht hpos
      rwa [ha,hb] at h
  exact hom_quadratic_nonneg false drift h1 h2 h3 h4.le y

private theorem hom_far_nonneg {q : ℝ} (hq : 8 ≤ q)
    (drift : Bool) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i*y j*homMatrix q 1 true drift i j := by
  have hu : 0 ≤ q-8 := by linarith
  obtain ⟨h1,h2⟩ := first_two_pos (show 5 ≤ q by linarith)
  have h3 := minor3_far_pos hu
  rw [show 8+(q-8)=q by ring] at h3
  have h4 : 0 < minor4 q 1 true drift := by
    cases drift
    · have h := minor4_far_pos hu
      rwa [show 8+(q-8)=q by ring] at h
    · have h := minor4_far_drift_pos hu
      rwa [show 8+(q-8)=q by ring] at h
  exact hom_quadratic_nonneg true drift h1 h2 h3 h4.le y

private theorem scaled_quadratic (L : ℝ) (M : Fin 4 → Fin 4 → ℝ) (y : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, y i*y j*(L*M i j)) =
      L*(∑ i : Fin 4, ∑ j : Fin 4, y i*y j*M i j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem endpoint_nonneg_of_hom {q : ℝ} (hq : 5 ≤ q)
    (far drift : Bool) (y : Fin 4 → ℝ)
    (h : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4,y i*y j*homMatrix q 1 far drift i j) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4,y i*y j*endpointMatrix q far drift i j := by
  have hq0 : 0 < q := by linarith
  have hq3 : 0 < 2*q-3 := by linarith
  have hL : 0 < q^5*(2*q-3)^2 := by positivity
  simp_rw [← source_endpoint_identify hq] at h
  rw [scaled_quadratic] at h
  exact (mul_nonneg_iff_of_pos_left hL).mp h

/-- Exact normalized first-atom energy with compensation and drift coefficients. -/
def centralEnergy (q sigma tau : ℝ) (y : Fin 4 → ℝ) : ℝ :=
  (∑ i : Fin 4, ∑ j : Fin 4,y i*y j*
    ThetaCuspOddCentral.centralMatrix (1/(2*q)) (6/(2*q-3)^2) i j)+sigma*(y 2)^2-2*tau*y 2*y 3

private theorem coordinate_mask_quadratic (a b : Fin 4) (v : ℝ) (y : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4,y i*y j*(if i=a ∧ j=b then v else 0))=y a*y b*v := by
  have he (i j : Fin 4) : y i*y j*(if i=a ∧ j=b then v else 0)=
      if i=a then if j=b then y i*y j*v else 0 else 0 := by
    by_cases hi : i=a <;> by_cases hj : j=b <;> simp [hi,hj]
  simp_rw [he]
  simp

private theorem diagonal_mask_quadratic (r : ℝ) (y : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4,y i*y j*(if i=j then r else 0))=r*∑ i : Fin 4,y i^2 := by
  have he (i j : Fin 4) : y i*y j*(if i=j then r else 0)=
      if j=i then r*y i^2 else 0 := by
    by_cases hij : i=j
    · subst j
      simp [pow_two,mul_comm]
    · simp [hij,Ne.symm hij]
  simp_rw [he]
  simp [Finset.mul_sum]

private theorem masked_quadratic (M : Fin 4 → Fin 4 → ℝ) (s t : ℝ) (y : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4,y i*y j*(M i j-(if i=j then 1/7 else 0)+
      (if i=2 ∧ j=2 then s else 0)-(if (i=2 ∧ j=3) ∨ (i=3 ∧ j=2) then t else 0)))=
      (∑ i : Fin 4, ∑ j : Fin 4,y i*y j*M i j)+s*(y 2)^2-2*t*y 2*y 3-
        (1/7)*∑ i : Fin 4,y i^2 := by
  have hcross (i j : Fin 4) : (if (i=2 ∧ j=3) ∨ (i=3 ∧ j=2) then t else 0)=
      (if i=2 ∧ j=3 then t else 0)+(if i=3 ∧ j=2 then t else 0) := by
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]
  simp_rw [hcross,mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  rw [diagonal_mask_quadratic,coordinate_mask_quadratic,coordinate_mask_quadratic,
    coordinate_mask_quadratic]
  ring

private theorem endpoint_energy (q : ℝ) (far drift : Bool) (y : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4,y i*y j*endpointMatrix q far drift i j)=
      centralEnergy q (sigmaFloor q far) (if drift then tauCeiling q far else 0) y-
        (1/7)*∑ i : Fin 4,y i^2 := by
  exact masked_quadratic
    (ThetaCuspOddCentral.centralMatrix (1/(2*q)) (6/(2*q-3)^2))
    (sigmaFloor q far) (if drift then tauCeiling q far else 0) y

private theorem tauCeiling_pos {q : ℝ} (hq : 5 ≤ q) (far : Bool) :
    0 < tauCeiling q far := by
  have hq0 : 0 < q := by linarith
  have hqt : 0 < q-107/40 := by linarith
  cases far <;> dsimp [tauCeiling] <;> positivity

private theorem affine_between_nonneg {A B T tau : ℝ}
    (hT : 0 < T) (h0 : 0 ≤ A) (h1 : 0 ≤ A-T*B)
    (htL : 0 ≤ tau) (htU : tau ≤ T) : 0 ≤ A-tau*B := by
  have h := add_nonneg (mul_nonneg (sub_nonneg.mpr htU) h0) (mul_nonneg htL h1)
  have he : (T-tau)*A+tau*(A-T*B)=T*(A-tau*B) := by ring
  rw [he] at h
  exact (mul_nonneg_iff_of_pos_left hT).mp h

private theorem centralEnergy_coercive_of_endpoints {q sigma tau : ℝ} (hq : 5 ≤ q)
    (far : Bool) (hs : sigmaFloor q far ≤ sigma) (htL : 0 ≤ tau) (htU : tau ≤ tauCeiling q far)
    (he : ∀ (drift : Bool) (y : Fin 4 → ℝ), 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4,y i*y j*endpointMatrix q far drift i j)
    (y : Fin 4 → ℝ) :
    (1/7)*∑ i : Fin 4,y i^2 ≤ centralEnergy q sigma tau y := by
  have h0 := he false y
  have h1 := he true y
  rw [endpoint_energy] at h0 h1
  change 0 ≤ centralEnergy q (sigmaFloor q far) 0 y-(1/7)*∑ i : Fin 4,y i^2 at h0
  change 0 ≤ centralEnergy q (sigmaFloor q far) (tauCeiling q far) y-
    (1/7)*∑ i : Fin 4,y i^2 at h1
  have h0' : 0 ≤ centralEnergy q (sigmaFloor q far) 0 y-(1/7)*∑ i : Fin 4,y i^2 := h0
  have h1' : 0 ≤ (centralEnergy q (sigmaFloor q far) 0 y-(1/7)*∑ i : Fin 4,y i^2)-
      tauCeiling q far*(2*y 2*y 3) := by
    convert h1 using 1
    unfold centralEnergy
    ring
  have ht := affine_between_nonneg (tauCeiling_pos hq far) h0' h1' htL htU
  have hs' := mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (y 2))
  unfold centralEnergy at ht ⊢
  nlinarith only [ht,hs']

private theorem centralEnergy_middle {q sigma tau : ℝ} (hq : 5 ≤ q) (hqU : q ≤ 8)
    (hs : sigmaFloor q false ≤ sigma) (htL : 0 ≤ tau) (htU : tau ≤ tauCeiling q false)
    (y : Fin 4 → ℝ) : (1/7)*∑ i : Fin 4,y i^2 ≤ centralEnergy q sigma tau y := by
  apply centralEnergy_coercive_of_endpoints hq false hs htL htU _ y
  intro drift y
  exact endpoint_nonneg_of_hom hq false drift y (hom_middle_nonneg hq hqU drift y)

private theorem centralEnergy_far {q sigma tau : ℝ} (hq : 8 ≤ q)
    (hs : sigmaFloor q true ≤ sigma) (htL : 0 ≤ tau) (htU : tau ≤ tauCeiling q true)
    (y : Fin 4 → ℝ) : (1/7)*∑ i : Fin 4,y i^2 ≤ centralEnergy q sigma tau y := by
  apply centralEnergy_coercive_of_endpoints (show 5 ≤ q by linarith) true hs htL htU _ y
  intro drift y
  exact endpoint_nonneg_of_hom (by linarith) true drift y (hom_far_nonneg hq drift y)

open ThetaCuspCoupledOddDrift

/-- Negative compensation at a nonnegative center lies strictly beyond scale five. -/
theorem five_lt_scale_of_compensation_neg {x : ℝ} (hx : 0 ≤ x)
    (hG : thetaCuspCenterCompensationSource x < 0) :
    5 < thetaCuspSingleAtomReflectionScale 1 x := by
  obtain ⟨τ, _, hτ5, _, hs⟩ := exists_thetaCuspCompensationNeutralAnchor
  have hτx := (hs x hx).2.2.mp hG
  have hq : thetaCuspSingleAtomReflectionScale 1 τ <
      thetaCuspSingleAtomReflectionScale 1 x := by
    dsimp [thetaCuspSingleAtomReflectionScale]
    have he := Real.exp_lt_exp.mpr (show 2*τ < 2*x by linarith only [hτx])
    simpa using mul_lt_mul_of_pos_left he Real.pi_pos
  exact hτ5.trans hq

/-- Literal canonical center compensation in the odd central normalization. -/
def normalizedCompensation (x : ℝ) : ℝ :=
  thetaCuspNativeOddCompensationCoefficient*thetaCuspCenterCompensationSource x /
    (4718592*thetaCuspSingleAtomReflectionScale 1 x^5*thetaCuspSourceTerm x 1^2)

private theorem normalizedCompensation_middle {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqU : thetaCuspSingleAtomReflectionScale 1 x ≤ 8) :
    sigmaFloor (thetaCuspSingleAtomReflectionScale 1 x) false ≤ normalizedCompensation x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  let C := thetaCuspNativeOddCompensationCoefficient
  let B := 1+(9/5)*q-(2/5)*q^2
  have hqm : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hqm
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1:ℕ))
  have hF : 0 < F := thetaCuspFullSource_pos_all x
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hC := thetaCuspNativeOddCompensationCoefficient_bounds
  have hC0 : 0 ≤ C := by dsimp [C]; linarith [hC.1]
  have hB : B ≤ 0 := by
    have he : B=(5-q)*(2*q+1)/5 := by dsimp [B]; ring
    rw [he]
    apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
    exact mul_nonpos_of_nonpos_of_nonneg (by dsimp [q]; linarith) (by positivity)
  have hm := pow_le_pow_left₀ hF.le (thetaCuspFullSource_mass_bounds_middle hqm).2 2
  have hG := thetaCuspCenterCompensationSource_quadratic_lower_eight hqm hqU
  change B*F^2 ≤ thetaCuspCenterCompensationSource x at hG
  have h1 := mul_le_mul_of_nonneg_left hG hC0
  have h2 := mul_le_mul_of_nonpos_right hC.2.le (show B*F^2 ≤ 0 from
    mul_nonpos_of_nonpos_of_nonneg hB (sq_nonneg F))
  have h3 := mul_le_mul_of_nonpos_left hm (show (3000000000:ℝ)*B ≤ 0 by linarith)
  have hraw : 3000000000*(101/100)^2*B*f^2 ≤ C*thetaCuspCenterCompensationSource x := by
    dsimp only [C,F,f] at h1 h2 h3 ⊢
    nlinarith only [h1,h2,h3]
  unfold normalizedCompensation
  change sigmaFloor q false ≤ C*thetaCuspCenterCompensationSource x/(4718592*q^5*f^2)
  apply (le_div_iff₀ (by positivity : 0 < 4718592*q^5*f^2)).mpr
  calc
    _ = 3000000000*(101/100)^2*B*f^2 := by
      dsimp [sigmaFloor,B]
      field_simp [hq0.ne']
    _ ≤ _ := hraw

private theorem source_center_tangent (x : ℝ) :
    10*x+107/40 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have he0 := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 93/200) 5
  norm_num [Finset.sum_range_succ] at he0
  have hp := mul_le_mul (show (31415/10000:ℝ) ≤ Real.pi by linarith [Real.pi_gt_d4])
    he0 (by norm_num) Real.pi_pos.le
  norm_num at hp
  have ht : 5 ≤ Real.pi*Real.exp (93/200:ℝ) := by linarith only [hp]
  have he := Real.add_one_le_exp (2*x-93/200)
  have hm := mul_le_mul_of_nonneg_right ht (Real.exp_pos (2*x-93/200)).le
  have hid : Real.pi*Real.exp (93/200)*Real.exp (2*x-93/200)=
      thetaCuspSingleAtomReflectionScale 1 x := by
    rw [mul_assoc, ← Real.exp_add]
    norm_num [thetaCuspSingleAtomReflectionScale]
  rw [hid] at hm
  linarith only [he,hm]

private theorem normalizedCanonicalDrift_middle {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    normalizedCanonicalDrift x ≤ tauCeiling (thetaCuspSingleAtomReflectionScale 1 x) false := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  let C := thetaCuspNativeOddCompensationCoefficient
  have hqm : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hqm
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1:ℕ))
  have hF : 0 < F := thetaCuspFullSource_pos_all x
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hC := thetaCuspNativeOddCompensationCoefficient_bounds
  have hm := pow_le_pow_left₀ hF.le (thetaCuspFullSource_mass_bounds_middle hqm).2 2
  have ht := source_center_tangent x
  change 10*x+107/40 ≤ q at ht
  have h1 := mul_le_mul_of_nonneg_right hC.2.le (show 0 ≤ x*F^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hm (show (0:ℝ) ≤ 3000000000*x by positivity)
  have h3 := mul_le_mul_of_nonneg_right ht (show 0 ≤ (3000000000:ℝ)*(101/100)^2*f^2/10 by positivity)
  have hraw : C*x*F^2 ≤ 3000000000*(101/100)^2*(q-107/40)*f^2/10 := by
    dsimp only [C,F,f] at h1 h2 h3 ⊢
    nlinarith only [h1,h2,h3]
  unfold normalizedCanonicalDrift
  change C*x*F^2/(786432*q^5*f^2) ≤ tauCeiling q false
  apply (div_le_iff₀ (by positivity : 0 < 786432*q^5*f^2)).mpr
  calc
    _ ≤ 3000000000*(101/100)^2*(q-107/40)*f^2/10 := hraw
    _ = _ := by
      dsimp [tauCeiling]
      field_simp [hq0.ne']
      ring

private theorem compensation_quadratic_far {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (3-13*thetaCuspSingleAtomReflectionScale 1 x^2/50)*thetaCuspSourceTerm x 1^2 ≤
      thetaCuspCenterCompensationSource x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  let d := deriv thetaCuspFullSource x
  have hqm : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hqm
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1:ℕ))
  have hF : 0 < F := thetaCuspFullSource_pos_all x
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hb := thetaCuspFullSource_mass_slope_le_scaleSeven (show 7 ≤ thetaCuspSingleAtomReflectionScale 1 x by linarith)
  change F ≤ (101/100)*f ∧ |d| ≤ (201/100)*q*f at hb
  have hprod := mul_le_mul hb.1 hb.2 (abs_nonneg d) (by positivity : (0:ℝ) ≤ (101/100)*f)
  have hprod1 : F*|d| ≤ (52/25)*q*f^2 := by
    nlinarith only [hprod,show 0 ≤ q*f^2 by positivity]
  have hprod2 := mul_le_mul_of_nonneg_left hprod1 (by positivity : (0:ℝ) ≤ 2*x)
  have hxd := sixteen_mul_center_le_firstAtomScale hx.le
  change 16*x ≤ q at hxd
  have hscale := mul_le_mul_of_nonneg_right hxd (by positivity : (0:ℝ) ≤ (13/50)*q*f^2)
  have hneg := mul_le_mul_of_nonneg_left (neg_abs_le d) (by positivity : (0:ℝ) ≤ 2*x*F)
  have hmass := pow_le_pow_left₀ hf.le (thetaCuspFullSource_mass_bounds_middle hqm).1 2
  change (3-13*q^2/50)*f^2 ≤ 3*F^2+2*x*F*d
  nlinarith only [hprod2,hscale,hneg,hmass]

private theorem normalizedCompensation_far {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    sigmaFloor (thetaCuspSingleAtomReflectionScale 1 x) true ≤ normalizedCompensation x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let C := thetaCuspNativeOddCompensationCoefficient
  let B := 3-13*q^2/50
  have hqm : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hqm
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1:ℕ))
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hC := thetaCuspNativeOddCompensationCoefficient_bounds
  have hC0 : 0 ≤ C := by dsimp [C]; linarith [hC.1]
  have hB : B ≤ 0 := by
    dsimp [B]
    have hq8 : 8 ≤ q := hq
    nlinarith [sq_nonneg (q-8)]
  have hG := compensation_quadratic_far hq
  change B*f^2 ≤ thetaCuspCenterCompensationSource x at hG
  have h1 := mul_le_mul_of_nonneg_left hG hC0
  have h2 := mul_le_mul_of_nonpos_right hC.2.le
    (show B*f^2 ≤ 0 from mul_nonpos_of_nonpos_of_nonneg hB (sq_nonneg f))
  have hraw : 3000000000*B*f^2 ≤ C*thetaCuspCenterCompensationSource x := by
    dsimp only [C] at h1 h2 ⊢
    nlinarith only [h1,h2]
  unfold normalizedCompensation
  change sigmaFloor q true ≤ C*thetaCuspCenterCompensationSource x/(4718592*q^5*f^2)
  apply (le_div_iff₀ (by positivity : 0 < 4718592*q^5*f^2)).mpr
  calc
    _ = 3000000000*B*f^2 := by
      dsimp [sigmaFloor,B]
      field_simp [hq0.ne']
    _ ≤ _ := hraw

private theorem normalizedCanonicalDrift_far {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    normalizedCanonicalDrift x ≤ tauCeiling (thetaCuspSingleAtomReflectionScale 1 x) true := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let F := thetaCuspFullSource x
  let C := thetaCuspNativeOddCompensationCoefficient
  have hqm : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hqm
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1:ℕ))
  have hF : 0 < F := thetaCuspFullSource_pos_all x
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hC := thetaCuspNativeOddCompensationCoefficient_bounds
  have hm := pow_le_pow_left₀ hF.le (thetaCuspFullSource_mass_bounds_middle hqm).2 2
  have ht := sixteen_mul_center_le_firstAtomScale hx.le
  change 16*x ≤ q at ht
  have h1 := mul_le_mul_of_nonneg_right hC.2.le (show 0 ≤ x*F^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hm (show (0:ℝ) ≤ 3000000000*x by positivity)
  have h3 := mul_le_mul_of_nonneg_right ht (show 0 ≤ (3000000000:ℝ)*(101/100)^2*f^2/16 by positivity)
  have hraw : C*x*F^2 ≤ 3000000000*(101/100)^2*q*f^2/16 := by
    dsimp only [C,F,f] at h1 h2 h3 ⊢
    nlinarith only [h1,h2,h3]
  unfold normalizedCanonicalDrift
  change C*x*F^2/(786432*q^5*f^2) ≤ tauCeiling q true
  apply (div_le_iff₀ (by positivity : 0 < 786432*q^5*f^2)).mpr
  calc
    _ ≤ 3000000000*(101/100)^2*q*f^2/16 := hraw
    _ = _ := by
      dsimp [tauCeiling]
      field_simp [hq0.ne']
      ring

/-- Actual canonical compensation and drift retain a one-seventh first-atom reserve on the full ray. -/
theorem source_central_coercive {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (y : Fin 4 → ℝ) :
    (1/7)*∑ i : Fin 4,y i^2 ≤
      centralEnergy (thetaCuspSingleAtomReflectionScale 1 x)
        (normalizedCompensation x) (normalizedCanonicalDrift x) y := by
  have htL := (normalizedCanonicalDrift_bounds hq).1
  by_cases hqU : thetaCuspSingleAtomReflectionScale 1 x ≤ 8
  · exact centralEnergy_middle hq hqU (normalizedCompensation_middle hq hqU)
      htL (normalizedCanonicalDrift_middle hq) y
  · have hq8 : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
    exact centralEnergy_far hq8 (normalizedCompensation_far hq8)
      htL (normalizedCanonicalDrift_far hq8) y

end
end RHTower.ThetaCuspCoupledOddRayModel

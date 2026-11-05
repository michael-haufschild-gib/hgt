import GaloisForLFunctions.ThetaCuspSections.FifthEvenFirstAtomTailModel
/-!
# Positive comparison matrices for the leading fifth even tail

The first-atom gamma reserve pays both endpoint models of the leading
unequal pair. Clearing the gamma and exponential envelopes gives polynomial
matrices whose five Schur signs are positive from scale three.
-/

noncomputable section
open Matrix
namespace GaloisForLFunctions.ThetaCuspSections.FifthMixedTail
open FifthAtomTail FifthLeadingPair

/-- Normalized half-integer tail recurrence with exponential rate five. -/
def g5 : ℕ → ℝ → ℝ → ℝ
 | 0, _, z => z
 | n+1, q, z => q^(n+1)/5+((2*n+5:ℕ):ℝ)/10*g5 n q z

/-- The leading unequal-pair radial polynomial applied to power moments. -/
def mixedLinear (m : ℕ → ℝ) : ℕ → ℝ
 | 0 => 9*(m 0) - (m 1) * 30 + (m 2) * 16
 | 1 => (m 1) * 300 - (m 2) * 1356 + (m 3) * 1400 - (m 4) * 576
 | 2 => -((m 1) * 1200) + (m 2) * 39696 - (m 3) * 171200 + (m 4) * 200784 - (m 5) * 108000 + (m 6) * 20736
 | 3 => (m 1) * 4800 - (m 2) * 707136 + (m 3) * 10073600 - (m 4) * 35416896 + (m 5) * 43089600 - (m 6) * 25790400 +
        (m 7) * 7620480 -
      (m 8) * 746496
 | 4 => -((m 1) * 19200) + (m 2) * 11602176 - (m 3) * 433126400 + (m 4) * 3651012864 - (m 5) * 10402022400 + (m 6) * 12499017216 -
            (m 7) * 7892398080 +
          (m 8) * 2788598016 -
        (m 9) * 468426240 +
      (m 10) * 26873856
 | 5 => (m 1) * 76800 - (m 2) * 186786816 + (m 3) * 16751820800 - (m 4) * 293872751616 + (m 5) * 1684623283200 -
                  (m 6) * 4002679526400 +
                (m 7) * 4618622453760 -
              (m 8) * 2987682527232 +
            (m 9) * 1157721984000 -
          (m 10) * 250538241024 +
        (m 11) * 26000455680 -
      (m 12) * 967458816
 | 6 => -((m 1) * 307200) + (m 2) * 2993197056 - (m 3) * 621740441600 + (m 4) * 21146177900544 - (m 5) * 220856989900800 +
                      (m 6) * 939708531818496 -
                    (m 7) * 1911756612648960 +
                  (m 8) * 2090002567606272 -
                (m 9) * 1357634344366080 +
              (m 10) * 554264510164992 -
            (m 11) * 138376171929600 +
          (m 12) * 19385214160896 -
        (m 13) * 1342349107200 +
      (m 14) * 34828517376
 | 7 => (m 1) * 1228800 - (m 2) * 47909584896 + (m 3) * 22681960448000 - (m 4) * 1440287890292736 + (m 5) * 25873229882572800 -
                          (m 6) * 183368931293184000 +
                        (m 7) * 614258629468323840 -
                      (m 8) * 1091711196399403008 +
                    (m 9) * 1124791456149504000 -
                  (m 10) * 723717393839751168 +
                (m 11) * 304249765406146560 -
              (m 12) * 82936975037349888 +
            (m 13) * 13929931575705600 -
          (m 14) * 1338962033885184 +
        (m 15) * 65738826547200 -
      (m 16) * 1253826625536
 | 8 => -((m 1) * 4915200) + (m 2) * 766627086336 - (m 3) * 821341473996800 + (m 4) * 95352120017485824 -
                                (m 5) * 2845887571309363200 +
                              (m 6) * 32060191465030680576 -
                            (m 7) * 167495442068487536640 +
                          (m 8) * 460233151236709613568 -
                        (m 9) * 725737675056009707520 +
                      (m 10) * 703779563626546987008 -
                    (m 11) * 444465339058343116800 +
                  (m 12) * 189568590591937609728 -
                (m 13) * 54676337965085491200 +
              (m 14) * 10342260481727397888 -
            (m 15) * 1222973202943180800 +
          (m 16) * 84812489945579520 -
        (m 17) * 3093817198510080 +
      (m 18) * 45137758519296
 | _ => 0

/-- Cubic lower gamma-mass enclosure at rate five. -/
def zL (q : ℝ) : ℝ := 1/5+3/(50*q)+3/(500*q^2)-3/(5000*q^3)
/-- Quadratic upper gamma-mass enclosure at rate five. -/
def zU (q : ℝ) : ℝ := 1/5+3/(50*q)+3/(500*q^2)
/-- First-atom lower moment plus the two ordered leading unequal pairs. -/
def totalMoment (q z w : ℝ) (k : ℕ) : ℝ :=
 linearMoment (fun n => g n q (1/2+3/(8*q))) k+
  8*w*mixedLinear (fun n => g5 n q z) k

/-- Cleared first-atom moments at the retained gamma lower mass. -/
def firstScaled : ℕ → ℝ → ℝ
 | 0, q => q/2+3/8
 | n+1, q => q^(n+2)/2+((2*n+5:ℕ):ℝ)/4*firstScaled n q
/-- Cleared rate-five moments at either gamma endpoint. -/
def crossScaled (upper : Bool) : ℕ → ℝ → ℝ
 | 0, q => q^3/5+3*q^2/50+3*q/500-(if upper then 0 else 3/5000)
 | n+1, q => q^(n+4)/5+((2*n+5:ℕ):ℝ)/10*crossScaled upper n q

/-- The leading comparison multiplied by the positive clearing factor `q¹²`. -/
def clearedMoment (upper : Bool) (q : ℝ) (k : ℕ) : ℝ :=
 q^11*linearMoment (fun n => firstScaled n q) k+
  (19683/1000)*mixedLinear (fun n => crossScaled upper n q) k

/-- The leading integrated moment model at the retained first-atom mass. -/
def leadingModel (q z w : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
 fun i j => totalMoment q z w (i.val+j.val)
/-- Polynomial comparison after clearing all positive endpoint powers. -/
def clearedMatrix (upper : Bool) (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
 fun i j => clearedMoment upper q (i.val+j.val)

namespace Lower

private def p0 (y : ℝ) : {v : ℝ // clearedMoment false (3+y) 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p1 (y : ℝ) : {v : ℝ // clearedMoment false (3+y) 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p2 (y : ℝ) : {v : ℝ // clearedMoment false (3+y) 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p3 (y : ℝ) : {v : ℝ // clearedMoment false (3+y) 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p4 (y : ℝ) : {v : ℝ // clearedMoment false (3+y) 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p5 (y : ℝ) : {v : ℝ // clearedMoment false (3+y) 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p6 (y : ℝ) : {v : ℝ // clearedMoment false (3+y) 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p7 (y : ℝ) : {v : ℝ // clearedMoment false (3+y) 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p8 (y : ℝ) : {v : ℝ // clearedMoment false (3+y) 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf
private def delta (y : ℝ) := (p0 y).val*(p2 y).val-((p1 y).val)^2

private def s00 (y : ℝ) := delta y*(p4 y).val-
  (p2 y).val*(p2 y).val*(p2 y).val+
  (p1 y).val*((p2 y).val*(p3 y).val+(p3 y).val*(p2 y).val)-
  (p0 y).val*(p3 y).val*(p3 y).val
private def c00 (y : ℝ) : {v : ℝ // s00 y=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [s00,delta,p0,p1,p2,p3,p4,p5,p6,p7,p8]
   ring_nf

private def s01 (y : ℝ) := delta y*(p5 y).val-
  (p2 y).val*(p2 y).val*(p3 y).val+
  (p1 y).val*((p2 y).val*(p4 y).val+(p3 y).val*(p3 y).val)-
  (p0 y).val*(p3 y).val*(p4 y).val
private def c01 (y : ℝ) : {v : ℝ // s01 y=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [s01,delta,p0,p1,p2,p3,p4,p5,p6,p7,p8]
   ring_nf

private def s02 (y : ℝ) := delta y*(p6 y).val-
  (p2 y).val*(p2 y).val*(p4 y).val+
  (p1 y).val*((p2 y).val*(p5 y).val+(p3 y).val*(p4 y).val)-
  (p0 y).val*(p3 y).val*(p5 y).val
private def c02 (y : ℝ) : {v : ℝ // s02 y=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [s02,delta,p0,p1,p2,p3,p4,p5,p6,p7,p8]
   ring_nf

private def s11 (y : ℝ) := delta y*(p6 y).val-
  (p2 y).val*(p3 y).val*(p3 y).val+
  (p1 y).val*((p3 y).val*(p4 y).val+(p4 y).val*(p3 y).val)-
  (p0 y).val*(p4 y).val*(p4 y).val
private def c11 (y : ℝ) : {v : ℝ // s11 y=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [s11,delta,p0,p1,p2,p3,p4,p5,p6,p7,p8]
   ring_nf

private def s12 (y : ℝ) := delta y*(p7 y).val-
  (p2 y).val*(p3 y).val*(p4 y).val+
  (p1 y).val*((p3 y).val*(p5 y).val+(p4 y).val*(p4 y).val)-
  (p0 y).val*(p4 y).val*(p5 y).val
private def c12 (y : ℝ) : {v : ℝ // s12 y=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [s12,delta,p0,p1,p2,p3,p4,p5,p6,p7,p8]
   ring_nf

private def s22 (y : ℝ) := delta y*(p8 y).val-
  (p2 y).val*(p4 y).val*(p4 y).val+
  (p1 y).val*((p4 y).val*(p5 y).val+(p5 y).val*(p4 y).val)-
  (p0 y).val*(p5 y).val*(p5 y).val
private def c22 (y : ℝ) : {v : ℝ // s22 y=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [s22,delta,p0,p1,p2,p3,p4,p5,p6,p7,p8]
   ring_nf

private theorem sign0 (y : ℝ) (hy : 0≤y) : 0<(p0 y).val := by
 dsimp only [p0]
 positivity
private theorem sign1 (y : ℝ) (hy : 0≤y) : 0<delta y := by
 dsimp only [delta,p0,p1,p2]
 ring_nf
 positivity
private theorem sign2 (y : ℝ) (hy : 0≤y) : 0<(c00 y).val := by
 dsimp only [c00]
 positivity
private theorem sign3 (y : ℝ) (hy : 0≤y) :
  0<(c00 y).val*(c11 y).val-((c01 y).val)^2 := by
 dsimp only [c00,c11,c01]
 ring_nf
 positivity
private theorem sign4 (y : ℝ) (hy : 0≤y) :
  0<((c00 y).val*(c11 y).val-((c01 y).val)^2)*(c22 y).val-
   ((c11 y).val*((c02 y).val)^2-2*(c01 y).val*(c02 y).val*(c12 y).val+
     (c00 y).val*((c12 y).val)^2) := by
 dsimp only [c00,c01,c02,c11,c12,c22]
 ring_nf
 positivity


private def lower (y : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => (p0 y).val | 1 => (p1 y).val | 2 => (p2 y).val
 | 3 => (p3 y).val | 4 => (p4 y).val | 5 => (p5 y).val
 | 6 => (p6 y).val | 7 => (p7 y).val | _ => (p8 y).val

private theorem lower_eq (y : ℝ) : lower y=clearedMatrix false (3+y) := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [lower,clearedMatrix,Nat.reduceAdd]
 all_goals first | exact (p0 y).property.symm | exact (p1 y).property.symm |
  exact (p2 y).property.symm | exact (p3 y).property.symm |
  exact (p4 y).property.symm | exact (p5 y).property.symm |
  exact (p6 y).property.symm | exact (p7 y).property.symm | exact (p8 y).property.symm

private theorem schur_cache (y : ℝ) :
 FifthLeadingPair.schur (lower y) 0 0=(c00 y).val ∧
 FifthLeadingPair.schur (lower y) 0 1=(c01 y).val ∧
 FifthLeadingPair.schur (lower y) 0 2=(c02 y).val ∧
 FifthLeadingPair.schur (lower y) 1 1=(c11 y).val ∧
 FifthLeadingPair.schur (lower y) 1 2=(c12 y).val ∧
 FifthLeadingPair.schur (lower y) 2 2=(c22 y).val := by
 have h00 := (c00 y).property
 have h01 := (c01 y).property
 have h02 := (c02 y).property
 have h11 := (c11 y).property
 have h12 := (c12 y).property
 have h22 := (c22 y).property
 simp only [FifthLeadingPair.schur,FifthLeadingPair.delta,FifthLeadingPair.tailIndex,lower]
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 all_goals dsimp only [s00,s01,s02,s11,s12,s22,delta] at h00 h01 h02 h11 h12 h22
 all_goals first | linear_combination h00 | linear_combination h01 |
  linear_combination h02 | linear_combination h11 | linear_combination h12 |
  linear_combination h22

/-- The lower tail comparison is strict from reflection scale three onward. -/
theorem cleared_posDef {q : ℝ} (hq : 3≤q) : (clearedMatrix false q).PosDef := by
 let y := q-3
 have hy : 0≤y := sub_nonneg.mpr hq
 have he : q=3+y := by dsimp [y]; ring
 rw [he,← lower_eq]
 obtain ⟨h00,h01,h02,h11,h12,h22⟩ := schur_cache y
 apply FifthLeadingPair.posDef_of_schur_signs
 · intro i j
   simp only [lower,Nat.add_comm]
 · exact sign0 y hy
 · exact sign1 y hy
 · rw [h00]
   exact sign2 y hy
 · rw [FifthLeadingPair.minor,h00,h01,h11]
   exact sign3 y hy
 · rw [FifthLeadingPair.determinant,FifthLeadingPair.minor,h00,h01,h02,h11,h12,h22]
   exact sign4 y hy

end Lower

namespace Upper

private def p0 (y : ℝ) : {v : ℝ // clearedMoment true (3+y) 0=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p1 (y : ℝ) : {v : ℝ // clearedMoment true (3+y) 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p2 (y : ℝ) : {v : ℝ // clearedMoment true (3+y) 2=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p3 (y : ℝ) : {v : ℝ // clearedMoment true (3+y) 3=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p4 (y : ℝ) : {v : ℝ // clearedMoment true (3+y) 4=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p5 (y : ℝ) : {v : ℝ // clearedMoment true (3+y) 5=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p6 (y : ℝ) : {v : ℝ // clearedMoment true (3+y) 6=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p7 (y : ℝ) : {v : ℝ // clearedMoment true (3+y) 7=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf

private def p8 (y : ℝ) : {v : ℝ // clearedMoment true (3+y) 8=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [clearedMoment,linearMoment,mixedLinear,firstScaled,crossScaled,Bool.false_eq_true,ite_false,ite_true]
   ring_nf
private def delta (y : ℝ) := (p0 y).val*(p2 y).val-((p1 y).val)^2

private def s00 (y : ℝ) := delta y*(p4 y).val-
  (p2 y).val*(p2 y).val*(p2 y).val+
  (p1 y).val*((p2 y).val*(p3 y).val+(p3 y).val*(p2 y).val)-
  (p0 y).val*(p3 y).val*(p3 y).val
private def c00 (y : ℝ) : {v : ℝ // s00 y=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [s00,delta,p0,p1,p2,p3,p4,p5,p6,p7,p8]
   ring_nf

private def s01 (y : ℝ) := delta y*(p5 y).val-
  (p2 y).val*(p2 y).val*(p3 y).val+
  (p1 y).val*((p2 y).val*(p4 y).val+(p3 y).val*(p3 y).val)-
  (p0 y).val*(p3 y).val*(p4 y).val
private def c01 (y : ℝ) : {v : ℝ // s01 y=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [s01,delta,p0,p1,p2,p3,p4,p5,p6,p7,p8]
   ring_nf

private def s02 (y : ℝ) := delta y*(p6 y).val-
  (p2 y).val*(p2 y).val*(p4 y).val+
  (p1 y).val*((p2 y).val*(p5 y).val+(p3 y).val*(p4 y).val)-
  (p0 y).val*(p3 y).val*(p5 y).val
private def c02 (y : ℝ) : {v : ℝ // s02 y=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [s02,delta,p0,p1,p2,p3,p4,p5,p6,p7,p8]
   ring_nf

private def s11 (y : ℝ) := delta y*(p6 y).val-
  (p2 y).val*(p3 y).val*(p3 y).val+
  (p1 y).val*((p3 y).val*(p4 y).val+(p4 y).val*(p3 y).val)-
  (p0 y).val*(p4 y).val*(p4 y).val
private def c11 (y : ℝ) : {v : ℝ // s11 y=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [s11,delta,p0,p1,p2,p3,p4,p5,p6,p7,p8]
   ring_nf

private def s12 (y : ℝ) := delta y*(p7 y).val-
  (p2 y).val*(p3 y).val*(p4 y).val+
  (p1 y).val*((p3 y).val*(p5 y).val+(p4 y).val*(p4 y).val)-
  (p0 y).val*(p4 y).val*(p5 y).val
private def c12 (y : ℝ) : {v : ℝ // s12 y=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [s12,delta,p0,p1,p2,p3,p4,p5,p6,p7,p8]
   ring_nf

private def s22 (y : ℝ) := delta y*(p8 y).val-
  (p2 y).val*(p4 y).val*(p4 y).val+
  (p1 y).val*((p4 y).val*(p5 y).val+(p5 y).val*(p4 y).val)-
  (p0 y).val*(p5 y).val*(p5 y).val
private def c22 (y : ℝ) : {v : ℝ // s22 y=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [s22,delta,p0,p1,p2,p3,p4,p5,p6,p7,p8]
   ring_nf

private theorem sign0 (y : ℝ) (hy : 0≤y) : 0<(p0 y).val := by
 dsimp only [p0]
 positivity
private theorem sign1 (y : ℝ) (hy : 0≤y) : 0<delta y := by
 dsimp only [delta,p0,p1,p2]
 ring_nf
 positivity
private theorem sign2 (y : ℝ) (hy : 0≤y) : 0<(c00 y).val := by
 dsimp only [c00]
 positivity
private theorem sign3 (y : ℝ) (hy : 0≤y) :
  0<(c00 y).val*(c11 y).val-((c01 y).val)^2 := by
 dsimp only [c00,c11,c01]
 ring_nf
 positivity
private theorem sign4 (y : ℝ) (hy : 0≤y) :
  0<((c00 y).val*(c11 y).val-((c01 y).val)^2)*(c22 y).val-
   ((c11 y).val*((c02 y).val)^2-2*(c01 y).val*(c02 y).val*(c12 y).val+
     (c00 y).val*((c12 y).val)^2) := by
 dsimp only [c00,c01,c02,c11,c12,c22]
 ring_nf
 positivity


private def lower (y : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => (p0 y).val | 1 => (p1 y).val | 2 => (p2 y).val
 | 3 => (p3 y).val | 4 => (p4 y).val | 5 => (p5 y).val
 | 6 => (p6 y).val | 7 => (p7 y).val | _ => (p8 y).val

private theorem lower_eq (y : ℝ) : lower y=clearedMatrix true (3+y) := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [lower,clearedMatrix,Nat.reduceAdd]
 all_goals first | exact (p0 y).property.symm | exact (p1 y).property.symm |
  exact (p2 y).property.symm | exact (p3 y).property.symm |
  exact (p4 y).property.symm | exact (p5 y).property.symm |
  exact (p6 y).property.symm | exact (p7 y).property.symm | exact (p8 y).property.symm

private theorem schur_cache (y : ℝ) :
 FifthLeadingPair.schur (lower y) 0 0=(c00 y).val ∧
 FifthLeadingPair.schur (lower y) 0 1=(c01 y).val ∧
 FifthLeadingPair.schur (lower y) 0 2=(c02 y).val ∧
 FifthLeadingPair.schur (lower y) 1 1=(c11 y).val ∧
 FifthLeadingPair.schur (lower y) 1 2=(c12 y).val ∧
 FifthLeadingPair.schur (lower y) 2 2=(c22 y).val := by
 have h00 := (c00 y).property
 have h01 := (c01 y).property
 have h02 := (c02 y).property
 have h11 := (c11 y).property
 have h12 := (c12 y).property
 have h22 := (c22 y).property
 simp only [FifthLeadingPair.schur,FifthLeadingPair.delta,FifthLeadingPair.tailIndex,lower]
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 all_goals dsimp only [s00,s01,s02,s11,s12,s22,delta] at h00 h01 h02 h11 h12 h22
 all_goals first | linear_combination h00 | linear_combination h01 |
  linear_combination h02 | linear_combination h11 | linear_combination h12 |
  linear_combination h22

/-- The lower tail comparison is strict from reflection scale three onward. -/
theorem cleared_posDef {q : ℝ} (hq : 3≤q) : (clearedMatrix true q).PosDef := by
 let y := q-3
 have hy : 0≤y := sub_nonneg.mpr hq
 have he : q=3+y := by dsimp [y]; ring
 rw [he,← lower_eq]
 obtain ⟨h00,h01,h02,h11,h12,h22⟩ := schur_cache y
 apply FifthLeadingPair.posDef_of_schur_signs
 · intro i j
   simp only [lower,Nat.add_comm]
 · exact sign0 y hy
 · exact sign1 y hy
 · rw [h00]
   exact sign2 y hy
 · rw [FifthLeadingPair.minor,h00,h01,h11]
   exact sign3 y hy
 · rw [FifthLeadingPair.determinant,FifthLeadingPair.minor,h00,h01,h02,h11,h12,h22]
   exact sign4 y hy

end Upper

/-- Every radial linear functional commutes with scalar multiplication. -/
theorem mixedLinear_smul (c : ℝ) (m : ℕ → ℝ) (k : ℕ) (hk : k≤8) :
 mixedLinear (fun n => c*m n) k=c*mixedLinear m k := by
 interval_cases k <;> simp only [mixedLinear] <;> ring

private theorem firstScaled_eq (n : ℕ) {q : ℝ} (hq : q≠0) :
 firstScaled n q=q*g n q (1/2+3/(8*q)) := by
 induction n with
 | zero => simp only [firstScaled,g]; field_simp [hq]
 | succ n ih =>
   simp only [firstScaled,g,ih]
   rw [show n+2=n+1+1 by omega,pow_succ]
   ring

private theorem crossScaled_eq (upper : Bool) (n : ℕ) {q : ℝ} (hq : q≠0) :
 crossScaled upper n q=q^3*g5 n q (if upper then zU q else zL q) := by
 induction n with
 | zero =>
   cases upper <;> simp only [crossScaled,g5,zL,zU,Bool.false_eq_true,ite_false,ite_true]
   all_goals field_simp [hq] <;> ring
 | succ n ih =>
   simp only [crossScaled,g5,ih]
   rw [show n+4=n+1+3 by omega,pow_add]
   ring

/-- The polynomial matrix is exactly a positive scalar multiple of the endpoint model. -/
theorem clearedMatrix_eq (upper : Bool) {q : ℝ} (hq : q≠0) :
 clearedMatrix upper q=q^12 • leadingModel q
   (if upper then zU q else zL q) (19683/(8000*q^9)) := by
 ext i j
 dsimp only [clearedMatrix,clearedMoment,leadingModel,totalMoment,Matrix.smul_apply,smul_eq_mul]
 rw [show (fun n => firstScaled n q)=(fun n => q*g n q (1/2+3/(8*q))) from
   funext (fun n => firstScaled_eq n hq),linearMoment_smul _ _ _ (by omega)]
 rw [show (fun n => crossScaled upper n q)=
   (fun n => q^3*g5 n q (if upper then zU q else zL q)) from
   funext (fun n => crossScaled_eq upper n hq),mixedLinear_smul _ _ _ (by omega)]
 field_simp [hq]
 ring

/-- Both extreme gamma masses retain a strict leading tail comparison. -/
theorem endpoint_posDef (upper : Bool) {q : ℝ} (hq : 3≤q) :
 (leadingModel q (if upper then zU q else zL q) (19683/(8000*q^9))).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hp : (clearedMatrix upper q).PosDef := by
  cases upper
  · exact Lower.cleared_posDef hq
  · exact Upper.cleared_posDef hq
 rw [clearedMatrix_eq upper hq0.ne'] at hp
 have h := hp.smul (inv_pos.mpr (pow_pos hq0 12))
 simpa only [smul_smul,inv_mul_cancel₀ (pow_pos hq0 12).ne',one_smul] using h

private theorem g5_affine (q a b t : ℝ) (n : ℕ) :
 g5 n q ((1-t)*a+t*b)=(1-t)*g5 n q a+t*g5 n q b := by
 induction n with
 | zero => rfl
 | succ n ih => simp only [g5,ih]; ring

private theorem mixedLinear_affine (m n : ℕ → ℝ) (t : ℝ) (k : ℕ) (hk : k≤8) :
 mixedLinear (fun j => (1-t)*m j+t*n j) k=
   (1-t)*mixedLinear m k+t*mixedLinear n k := by
 interval_cases k <;> simp only [mixedLinear] <;> ring

private theorem leadingModel_affine_gamma (q a b t w : ℝ) :
 leadingModel q ((1-t)*a+t*b) w=
   (1-t) • leadingModel q a w+t • leadingModel q b w := by
 ext i j
 dsimp only [leadingModel,totalMoment,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
 rw [show (fun n => g5 n q ((1-t)*a+t*b))=
   (fun n => (1-t)*g5 n q a+t*g5 n q b) from funext (g5_affine q a b t),
   mixedLinear_affine _ _ _ _ (by omega)]
 ring

private theorem leadingModel_affine_weight (q z a b t : ℝ) :
 leadingModel q z ((1-t)*a+t*b)=
   (1-t) • leadingModel q z a+t • leadingModel q z b := by
 ext i j
 dsimp only [leadingModel,totalMoment,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
 ring

private theorem convex_posDef {A B : Matrix (Fin 5) (Fin 5) ℝ}
 (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
 ((1-t) • A+t • B).PosDef := by
 by_cases hz : t=0
 · simpa only [hz,sub_zero,one_smul,zero_smul,add_zero] using hA
 have hp := (hB.smul (lt_of_le_of_ne ht (Ne.symm hz))).add_posSemidef
   (hA.posSemidef.smul (sub_nonneg.mpr ht1))
 simpa only [add_comm] using hp

/-- Every gamma mass in the two-sided enclosure has a strict endpoint comparison. -/
theorem gamma_interval_posDef {q z : ℝ} (hq : 3≤q) (hzL : zL q≤z) (hzU : z≤zU q) :
 (leadingModel q z (19683/(8000*q^9))).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hd : 0<zU q-zL q := by
  dsimp only [zL,zU]
  have h : 0<3/(5000*q^3) := by positivity
  linarith only [h]
 have ht : 0≤(z-zL q)/(zU q-zL q) := div_nonneg (sub_nonneg.mpr hzL) hd.le
 have ht1 : (z-zL q)/(zU q-zL q)≤1 := by
  apply (div_le_one hd).mpr
  linarith only [hzU]
 have he : z=(1-(z-zL q)/(zU q-zL q))*zL q+
   ((z-zL q)/(zU q-zL q))*zU q := by
  field_simp [hd.ne']
  ring
 rw [he,leadingModel_affine_gamma]
 exact convex_posDef (endpoint_posDef false hq) (endpoint_posDef true hq) ht ht1

/-- The full weight interval preserves the strict leading-tail comparison. -/
theorem leadingModel_posDef {q z w : ℝ} (hq : 3≤q)
 (hzL : zL q≤z) (hzU : z≤zU q) (hw : 0≤w) (hwU : w≤19683/(8000*q^9)) :
 (leadingModel q z w).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 have hW : 0<19683/(8000*q^9) := by positivity
 have ht : 0≤w/(19683/(8000*q^9)) := div_nonneg hw hW.le
 have ht1 : w/(19683/(8000*q^9))≤1 := (div_le_one hW).mpr hwU
 have h0 : (leadingModel q z 0).PosDef := by
  have hz0 : 1/2≤1/2+3/(8*q) := le_add_of_nonneg_right (by positivity)
  have hp := model_posDef hq hz0
  convert hp using 1
  ext i j
  dsimp only [leadingModel,totalMoment,FifthAtomTail.model]
  rw [moment_eq_linearMoment _ _ _ (by omega)]
  ring
 have he : w=(1-w/(19683/(8000*q^9)))*0+
   (w/(19683/(8000*q^9)))*(19683/(8000*q^9)) := by
  field_simp [hW.ne']
  ring
 rw [he,leadingModel_affine_weight]
 exact convex_posDef h0 (gamma_interval_posDef hq hzL hzU) ht ht1

private theorem exp_three_lower : (20 : ℝ)≤Real.exp 3 := by
 have h1 : (2718/1000:ℝ)≤Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
 have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) h1 3
 rw [← Real.exp_nat_mul] at hp
 norm_num at hp
 linarith only [hp]

/-- The leading relative exponential weight lies inside the polynomial envelope. -/
theorem exponential_envelope {q : ℝ} (hq : 3≤q) :
 Real.exp (-3*q)≤19683/(8000*q^9) := by
 have hq0 : 0<q := by linarith only [hq]
 have hp := _root_.RHTower.pow_mul_exp_neg_le_stationary_radius 9
  (a := 3) (t := q) (by norm_num) hq0.le
 have h9 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤20) exp_three_lower 3
 rw [← Real.exp_nat_mul] at h9
 norm_num at h9
 have he : Real.exp (-9:ℝ)≤1/8000 := by
  rw [Real.exp_neg,inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h9
 have hp' : q^9*Real.exp (-3*q)≤(3:ℝ)^9*Real.exp (-9) := by
  convert hp using 1 <;> norm_num
 have hh := mul_le_mul_of_nonneg_left he (show (0:ℝ)≤3^9 by positivity)
 apply (le_div_iff₀ (show 0<(8000:ℝ)*q^9 by positivity)).mpr
 nlinarith only [hp',hh]

end GaloisForLFunctions.ThetaCuspSections.FifthMixedTail

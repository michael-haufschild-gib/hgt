import GaloisForLFunctions.ThetaCuspSections.FifthEvenLeadingPairReserve
/-!
# The fifth even first-atom tail comparison

Integration by parts expresses the radial tail moments as a polynomial in
its lower endpoint and one normalized incomplete-gamma mass. At mass one
half the five Schur signs have positive coefficients in `q-3`.
-/

noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections.FifthAtomTail
open Matrix
/-- Normalized half-integer incomplete-gamma recurrence. -/
def g : ℕ → ℝ → ℝ → ℝ
| 0, _, z => z
| n+1, q, z => q^(n+1)/2 + ((2*n+5 : ℕ):ℝ)/4*g n q z
/-- The signed radial moment, as a linear combination of power moments. -/
def linearMoment (m : ℕ → ℝ) : ℕ → ℝ
 | 0 => 9*(m 0) - (m 1) * 12 + (m 2) * 4
 | 1 => (m 1) * 120 - (m 2) * 96 + (m 3) * 32
 | 2 => -((m 1) * 480) + (m 2) * 4416 - (m 3) * 2432 + (m 4) * 768
 | 3 => (m 1) * 1920 - (m 2) * 82176 + (m 3) * 253952 - (m 4) * 107520 + (m 5) * 30720
 | 4 => -((m 1) * 7680) + (m 2) * 1360896 - (m 3) * 12388352 + (m 4) * 19611648 - (m 5) * 6881280 + (m 6) * 1720320
 | 5 => (m 1) * 30720 - (m 2) * 21958656 + (m 3) * 500252672 - (m 4) * 1924055040 + (m 5) * 1899233280 - (m 6) * 578027520 +
      (m 7) * 123863040
 | 6 => -((m 1) * 122880) + (m 2) * 352075776 - (m 3) * 18886787072 + (m 4) * 150752329728 - (m 5) * 320229212160 +
          (m 6) * 221632266240 -
        (m 7) * 59949711360 +
      (m 8) * 10899947520
 | 7 => (m 1) * 491520 - (m 2) * 5636161536 + (m 3) * 694004744192 - (m 4) * 10699371970560 + (m 5) * 42564900618240 -
            (m 6) * 57797577277440 +
          (m 7) * 30323654000640 -
        (m 8) * 7368364523520 +
      (m 9) * 1133594542080
 | 8 => -((m 1) * 1966080) + (m 2) * 90190381056 - (m 3) * 25209606766592 + (m 4) * 723521013547008 - (m 5) * 5015348591984640 +
              (m 6) * 11904065218805760 -
            (m 7) * 11342746988052480 +
          (m 8) * 4763364265820160 -
        (m 9) * 1042906978713600 +
      (m 10) * 136031345049600
 | _ => 0

private def t0 (q z : ℝ) : ℝ := linearMoment (fun n => g n q z) 0
private def t1 (q z : ℝ) : ℝ := linearMoment (fun n => g n q z) 1
private def t2 (q z : ℝ) : ℝ := linearMoment (fun n => g n q z) 2
private def t3 (q z : ℝ) : ℝ := linearMoment (fun n => g n q z) 3
private def t4 (q z : ℝ) : ℝ := linearMoment (fun n => g n q z) 4
private def t5 (q z : ℝ) : ℝ := linearMoment (fun n => g n q z) 5
private def t6 (q z : ℝ) : ℝ := linearMoment (fun n => g n q z) 6
private def t7 (q z : ℝ) : ℝ := linearMoment (fun n => g n q z) 7
private def t8 (q z : ℝ) : ℝ := linearMoment (fun n => g n q z) 8

private def p0 (y : ℝ) : {v : ℝ // t0 (3+y) (1/2)=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [linearMoment,t0,g]
   ring_nf

private def p1 (y : ℝ) : {v : ℝ // t1 (3+y) (1/2)=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [linearMoment,t1,g]
   ring_nf

private def p2 (y : ℝ) : {v : ℝ // t2 (3+y) (1/2)=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [linearMoment,t2,g]
   ring_nf

private def p3 (y : ℝ) : {v : ℝ // t3 (3+y) (1/2)=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [linearMoment,t3,g]
   ring_nf

private def p4 (y : ℝ) : {v : ℝ // t4 (3+y) (1/2)=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [linearMoment,t4,g]
   ring_nf

private def p5 (y : ℝ) : {v : ℝ // t5 (3+y) (1/2)=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [linearMoment,t5,g]
   ring_nf

private def p6 (y : ℝ) : {v : ℝ // t6 (3+y) (1/2)=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [linearMoment,t6,g]
   ring_nf

private def p7 (y : ℝ) : {v : ℝ // t7 (3+y) (1/2)=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [linearMoment,t7,g]
   ring_nf

private def p8 (y : ℝ) : {v : ℝ // t8 (3+y) (1/2)=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs =>
   simp only [linearMoment,t8,g]
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

/-- The nine normalized signed tail moments through reflection order sixteen. -/
def moment (q z : ℝ) : ℕ → ℝ
 | 0 => t0 q z | 1 => t1 q z | 2 => t2 q z | 3 => t3 q z | 4 => t4 q z
 | 5 => t5 q z | 6 => t6 q z | 7 => t7 q z | 8 => t8 q z | _ => 0

/-- The fifth even normalized tail model. -/
def model (q z : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
 fun i j => moment q z (i.val+j.val)

private def lower (y : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => (p0 y).val | 1 => (p1 y).val | 2 => (p2 y).val
 | 3 => (p3 y).val | 4 => (p4 y).val | 5 => (p5 y).val
 | 6 => (p6 y).val | 7 => (p7 y).val | _ => (p8 y).val

private theorem lower_eq (y : ℝ) : lower y=model (3+y) (1/2) := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [lower,model,moment,Nat.reduceAdd]
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
theorem half_model_posDef {q : ℝ} (hq : 3≤q) : (model q (1/2)).PosDef := by
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


private theorem g_affine (q z : ℝ) (n : ℕ) :
 g n q z=g n q (1/2)+(z-1/2)*g n 0 1 := by
 induction n with
 | zero => simp only [g]; ring
 | succ n ih =>
   simp only [g,ih,pow_succ]
   ring

private theorem moment_affine (q z : ℝ) (k : ℕ) (hk : k≤8) :
 moment q z k=moment q (1/2) k+(z-1/2)*moment 0 1 k := by
 interval_cases k
 all_goals simp only [moment,linearMoment,t0,t1,t2,t3,t4,t5,t6,t7,t8,g_affine q z]
 all_goals ring

/-- Increasing the incomplete-gamma mass adds a fixed positive moment matrix. -/
theorem model_affine (q z : ℝ) :
 model q z=model q (1/2)+(z-1/2) • model 0 1 := by
 ext i j
 exact moment_affine q z (i.val+j.val) (by omega)

private def a0 : {v : ℝ // t0 0 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,t0,g]

private def a1 : {v : ℝ // t1 0 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,t1,g]

private def a2 : {v : ℝ // t2 0 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,t2,g]

private def a3 : {v : ℝ // t3 0 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,t3,g]

private def a4 : {v : ℝ // t4 0 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,t4,g]

private def a5 : {v : ℝ // t5 0 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,t5,g]

private def a6 : {v : ℝ // t6 0 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,t6,g]

private def a7 : {v : ℝ // t7 0 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,t7,g]

private def a8 : {v : ℝ // t8 0 1=v} := by
 refine ⟨?value,?certificate⟩
 case certificate =>
  conv_lhs => norm_num [linearMoment,t8,g]

private def massMatrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 match i.val+j.val with
 | 0 => a0.val | 1 => a1.val | 2 => a2.val | 3 => a3.val | 4 => a4.val
 | 5 => a5.val | 6 => a6.val | 7 => a7.val | _ => a8.val

private theorem mass_eq : massMatrix=model 0 1 := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  simp only [massMatrix,model,moment,Nat.reduceAdd]
 all_goals first | exact a0.property.symm | exact a1.property.symm |
  exact a2.property.symm | exact a3.property.symm | exact a4.property.symm |
  exact a5.property.symm | exact a6.property.symm | exact a7.property.symm | exact a8.property.symm

/-- The incomplete-gamma coefficient matrix is strictly positive. -/
theorem mass_model_posDef : (model 0 1).PosDef := by
 rw [← mass_eq]
 apply FifthLeadingPair.posDef_of_schur_signs
 · intro i j
   simp only [massMatrix,Nat.add_comm]
 all_goals norm_num [FifthLeadingPair.delta,FifthLeadingPair.schur,FifthLeadingPair.minor,
   FifthLeadingPair.determinant,FifthLeadingPair.tailIndex,massMatrix,a0,a1,a2,a3,a4,a5,a6,a7,a8]

/-- The full tail model is strict from scale three for every admissible gamma mass. -/
theorem model_posDef {q z : ℝ} (hq : 3≤q) (hz : 1/2≤z) : (model q z).PosDef := by
 rw [model_affine]
 exact (half_model_posDef hq).add_posSemidef
   (mass_model_posDef.posSemidef.smul (sub_nonneg.mpr hz))

/-- The matrix moments are the radial linear form evaluated on gamma moments. -/
theorem moment_eq_linearMoment (q z : ℝ) (k : ℕ) (hk : k≤8) :
 moment q z k=linearMoment (fun n => g n q z) k := by
 interval_cases k <;> rfl

/-- Common mass factors pass through every retained radial moment. -/
theorem linearMoment_smul (c : ℝ) (m : ℕ → ℝ) (k : ℕ) (hk : k≤8) :
 linearMoment (fun n => c*m n) k=c*linearMoment m k := by
 interval_cases k <;> simp only [linearMoment] <;> ring

end GaloisForLFunctions.ThetaCuspSections.FifthAtomTail

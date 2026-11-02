import GaloisForLFunctions.ArithmeticIndexDescent.PrimeWindowRowTails

/-!
# Coordinates of unit Haar and coarse sections

The exact reciprocal lower bounds on cell masses control finite packet
coefficients without depending on the outer detail horizon.
-/

noncomputable section
open Finset MeasureTheory
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open GaloisForLFunctions.BiarithmeticGaugeGeometry
namespace GaloisForLFunctions.ArithmeticIndexDescent

lemma abs_coordinate_le_of_unit_mass {ι : Type*} (S : Finset ι) (w c : ι → ℝ)
    (hw : ∀ j ∈ S,0≤w j) (hunit : (∑ j ∈ S,w j*c j^2)≤1)
    {i : ι} (hi : i∈S) {B : ℝ} (hB : 1≤B) (hlower : 1/B≤w i) :
    |c i| ≤B := by
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hterm : w i*c i^2≤1 :=
    (single_le_sum (fun j hj => mul_nonneg (hw j hj) (sq_nonneg _)) hi).trans hunit
  have hs : c i^2≤B := by
    have hdiv : c i^2/B≤1 := by
      calc
        _ = (1/B)*c i^2 := by ring
        _ ≤ w i*c i^2 := mul_le_mul_of_nonneg_right hlower (sq_nonneg _)
        _ ≤ 1 := hterm
    simpa only [one_mul] using (div_le_iff₀ hB0).mp hdiv
  apply (sq_le_sq₀ (abs_nonneg _) hB0.le).mp
  rw [sq_abs]
  exact hs.trans (by nlinarith only [mul_nonneg hB0.le (sub_nonneg.mpr hB)])

lemma abs_haar_coordinate_le_of_unit_mass {X a : ℕ} (d : ℕ → ℝ)
    (hd : (∑ j ∈ Icc 1 X,haarMass j*d j^2)≤1) (ha : a∈Icc 1 X) :
    |d a| ≤4*(a:ℝ)+3 := by
  apply abs_coordinate_le_of_unit_mass (Icc 1 X) haarMass d
    (fun j hj => (haarMass_pos (mem_Icc.mp hj).1).le) hd ha
  · have h := Nat.cast_nonneg (α := ℝ) a
    linarith only [h]
  · exact (haarMass_bounds (mem_Icc.mp ha).1).1

lemma abs_coarse_coordinate_le_of_unit_mass {M b : ℕ} (q : ℕ → ℝ)
    (hq : (∑ j ∈ Icc 1 M,logCellWidth j*q j^2)≤1) (hb : b∈Icc 1 M) :
    |q b| ≤(b:ℝ)+1 := by
  apply abs_coordinate_le_of_unit_mass (Icc 1 M) logCellWidth q
    (fun j hj => (logCellWidth_pos (mem_Icc.mp hj).1).le) hq hb
  · have h := Nat.cast_nonneg (α := ℝ) b
    linarith only [h]
  · exact inv_add_one_le_logCellWidth (mem_Icc.mp hb).1

lemma abs_unit_prime_packet_coefficient_le {X A M a b : ℕ} (d q : ℕ → ℝ)
    (hd : (∑ j ∈ Icc 1 X,haarMass j*d j^2)≤1)
    (hq : (∑ j ∈ Icc 1 M,logCellWidth j*q j^2)≤1)
    (ha : a∈Icc 1 (min X A)) (hb : b∈Icc 1 M) :
    |d a*q b| ≤7*((A:ℝ)+1)*((M:ℝ)+1) := by
  have haX : a∈Icc 1 X := mem_Icc.mpr
    ⟨(mem_Icc.mp ha).1,(mem_Icc.mp ha).2.trans (min_le_left _ _)⟩
  have haA : (a:ℝ)≤A := by exact_mod_cast
    (mem_Icc.mp ha).2.trans (min_le_right _ _)
  have hbM : (b:ℝ)≤M := by exact_mod_cast (mem_Icc.mp hb).2
  have hdA : |d a| ≤7*((A:ℝ)+1) := by
    apply (abs_haar_coordinate_le_of_unit_mass d hd haX).trans
    have hA0 := Nat.cast_nonneg (α := ℝ) A
    linarith only [haA,hA0]
  have hqM : |q b| ≤(M:ℝ)+1 :=
    (abs_coarse_coordinate_le_of_unit_mass q hq hb).trans (add_le_add hbM le_rfl)
  rw [abs_mul]
  exact mul_le_mul hdA hqM (abs_nonneg _) (by positivity)

lemma sum_Icc_split_at (f : ℕ → ℝ) (X A : ℕ) :
    (∑ a ∈ Icc 1 X,f a) =
      (∑ a ∈ Icc 1 (min X A),f a)+(∑ a ∈ Icc (A+1) X,f a) := by
  have hd : Disjoint (Icc 1 (min X A)) (Icc (A+1) X) := by
    rw [disjoint_left]
    intro a ha hb
    simp only [mem_Icc,le_min_iff] at ha hb
    omega
  have he : Icc 1 X=Icc 1 (min X A)∪Icc (A+1) X := by
    ext a
    simp only [mem_union,mem_Icc,le_min_iff]
    omega
  rw [he,sum_union hd]

/-- The expanding Haar pole is uniformly bounded on every unit detail section. -/
lemma abs_haar_exp_pos_sum_le_of_unit_mass {X : ℕ} (d : ℕ → ℝ)
    (hd : (∑ a ∈ Icc 1 X,haarMass a*d a^2)≤1) :
    |∑ a ∈ Icc 1 X,d a*(∫ u,haarProfile a u*Real.exp (u/2))| ≤ 1 := by
  have he : (∫ u,haarSectionProfile d X u*Real.exp (u/2)) =
      ∑ a ∈ Icc 1 X,d a*(∫ u,haarProfile a u*Real.exp (u/2)) := by
    unfold haarSectionProfile
    simp_rw [Finset.sum_mul,mul_assoc]
    rw [integral_finsetSum _ fun a _ =>
      (integrable_compact_bv_mul (haarProfile_bv a) (haarProfile_compact a)
        (show Continuous (fun u : ℝ => Real.exp (u/2)) by fun_prop)).const_mul (d a)]
    simp only [integral_const_mul]
  have hs := (haarSectionProfile_exp_pos_sq_le d X).trans hd
  rw [he] at hs
  apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
  simpa only [sq_abs,one_pow] using hs

/-- A polynomial coarse-range bound suffices for the opposite translated pole. -/
lemma abs_coarse_exp_neg_sum_le_of_unit_mass {M : ℕ} (q : ℕ → ℝ)
    (hq : (∑ b ∈ Icc 1 M,logCellWidth b*q b^2)≤1) :
    |∑ b ∈ Icc 1 M,q b*(∫ u,coarseProfile b u*Real.exp (-u/2))| ≤
      2*((M:ℝ)+1)^2 := by
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _b ∈ Icc 1 M,2*((M:ℝ)+1) := by
      apply sum_le_sum
      intro b hb
      rw [abs_mul]
      have hq' := abs_coarse_coordinate_le_of_unit_mass q hq hb
      have hc := coarseProfile_exp_neg_abs_le_two (mem_Icc.mp hb).1
      have hbM : (b:ℝ)≤M := by exact_mod_cast (mem_Icc.mp hb).2
      exact (mul_le_mul hq' hc (abs_nonneg _) (by positivity)).trans (by linarith only [hbM])
    _ = (M:ℝ)*(2*((M:ℝ)+1)) := by simp
    _ ≤ _ := by nlinarith only [Nat.cast_nonneg (α := ℝ) M]

#print axioms abs_haar_exp_pos_sum_le_of_unit_mass
#print axioms abs_coarse_exp_neg_sum_le_of_unit_mass
#print axioms abs_coordinate_le_of_unit_mass
#print axioms abs_haar_coordinate_le_of_unit_mass
#print axioms abs_coarse_coordinate_le_of_unit_mass
#print axioms abs_unit_prime_packet_coefficient_le
#print axioms sum_Icc_split_at
end GaloisForLFunctions.ArithmeticIndexDescent

import GaloisForLFunctions.ArithmeticIndexDescent.FullPrimeWindowRowBounds

/-!
# Uniform Hilbert tails of the full prime–pole matrix

The squared row majorant telescopes in the detail index. Weighted
Cauchy–Schwarz leaves a cubic coarse-index cost, uniformly in every detail
horizon and every pair of unit vectors in the original cell masses.
-/

noncomputable section
open Finset
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open GaloisForLFunctions.BiarithmeticGaugeGeometry
namespace GaloisForLFunctions.ArithmeticIndexDescent

lemma finite_weighted_pair_sq_le {ι : Type*} (S : Finset ι) (w d v : ι → ℝ)
    (hw : ∀ i ∈ S, 0<w i) :
    (∑ i ∈ S,d i*v i)^2 ≤ (∑ i ∈ S,w i*d i^2)*(∑ i ∈ S,v i^2/w i) := by
  have hp (i : ι) (hi : i∈S) :
      (Real.sqrt (w i)*d i)*(v i/Real.sqrt (w i))=d i*v i := by
    field_simp [(Real.sqrt_pos.mpr (hw i hi)).ne']
  have hd (i : ι) (hi : i∈S) :
      (Real.sqrt (w i)*d i)^2=w i*d i^2 := by
    rw [mul_pow,Real.sq_sqrt (hw i hi).le]
  have hv (i : ι) (hi : i∈S) :
      (v i/Real.sqrt (w i))^2=v i^2/w i := by
    rw [div_pow,Real.sq_sqrt (hw i hi).le]
  have h := sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (w i)*d i)
    (fun i => v i/Real.sqrt (w i))
  rwa [sum_congr rfl hp,sum_congr rfl hd,sum_congr rfl hv] at h

lemma sum_pronic_tail_le (A X : ℕ) :
    (∑ a ∈ Icc (A+1) X,1/((a:ℝ)*((a:ℝ)+1))) ≤ 1/((A:ℝ)+1) := by
  by_cases hAX : A+1≤X
  · have he (a : ℕ) (ha : a∈Icc (A+1) X) :
        1/((a:ℝ)*((a:ℝ)+1)) =
          -(1/((a+1:ℕ):ℝ))- -(1/(a:ℝ)) := by
      have ha0 : (0:ℝ)<a := by exact_mod_cast (show 0<a by have := (mem_Icc.mp ha).1;omega)
      push_cast
      field_simp [ha0.ne']
      ring
    rw [sum_congr rfl he,sum_Icc_sub hAX (fun a : ℕ => -(1/(a:ℝ)))]
    push_cast
    have hz : (0:ℝ) ≤ 1/((X:ℝ)+1) := by positivity
    linarith only [hz]
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hAX),sum_empty]
    positivity

/-- The entire detail tail is uniformly small in the original Haar and coarse masses. -/
theorem exists_fullPrimeWindowRemainder_hilbert_tail_bound :
    ∃ C : ℝ, 0<C ∧ ∀ Y A X M : ℕ, 1≤Y →
      ∀ d q : ℕ → ℝ,
      (∑ a ∈ Icc 1 X,haarMass a*d a^2) ≤ 1 →
      (∑ b ∈ Icc 1 M,logCellWidth b*q b^2) ≤ 1 →
      (∑ b ∈ Icc 1 M,q b*(∑ a ∈ Icc (A+1) X,
        d a*fullPrimeWindowRemainder Y a b))^2 ≤
          C*((M:ℝ)+1)^3/((A:ℝ)+1) := by
  obtain ⟨C,hC,hrow⟩ := exists_fullPrimeWindowRemainder_square_row_bound
  refine ⟨C,hC,?_⟩
  intro Y A X M hY d q hd hq
  let v (b : ℕ) := ∑ a ∈ Icc (A+1) X,d a*fullPrimeWindowRemainder Y a b
  have hmass : (∑ a ∈ Icc (A+1) X,haarMass a*d a^2) ≤ 1 := by
    apply le_trans ?_ hd
    apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_left (by omega : 1≤A+1))
    intro a ha _
    exact mul_nonneg (haarMass_pos (mem_Icc.mp ha).1).le (sq_nonneg _)
  -- The normalized row squares leave a telescoping pronic tail.
  have hv (b : ℕ) (hb : 1≤b) : (v b)^2 ≤ C*((b:ℝ)+1)/((A:ℝ)+1) := by
    have hcs := finite_weighted_pair_sq_le (Icc (A+1) X) haarMass d
      (fun a => fullPrimeWindowRemainder Y a b)
      (fun a ha => haarMass_pos (by have := (mem_Icc.mp ha).1;omega))
    have hn : 0 ≤ ∑ a ∈ Icc (A+1) X,
        (fullPrimeWindowRemainder Y a b)^2/haarMass a :=
      sum_nonneg fun a ha => div_nonneg (sq_nonneg _)
        (haarMass_pos (by have := (mem_Icc.mp ha).1;omega)).le
    have hs : ∀ a ∈ Icc (A+1) X,
        (fullPrimeWindowRemainder Y a b)^2/haarMass a ≤
          C*((b:ℝ)+1)*(1/((a:ℝ)*((a:ℝ)+1))) := by
      intro a ha
      have ha1 : 1≤a := by have := (mem_Icc.mp ha).1;omega
      rw [div_le_iff₀ (haarMass_pos ha1)]
      exact (hrow Y a b hY ha1 hb).trans_eq (by ring)
    calc
      _ ≤ _ := hcs
      _ ≤ 1*(∑ a ∈ Icc (A+1) X,(fullPrimeWindowRemainder Y a b)^2/haarMass a) :=
        mul_le_mul_of_nonneg_right hmass hn
      _ ≤ C*((b:ℝ)+1)*(∑ a ∈ Icc (A+1) X,1/((a:ℝ)*((a:ℝ)+1))) := by
        rw [one_mul,mul_sum]
        exact sum_le_sum hs
      _ ≤ C*((b:ℝ)+1)*(1/((A:ℝ)+1)) :=
        mul_le_mul_of_nonneg_left (sum_pronic_tail_le A X) (by positivity)
      _ = _ := by ring
  -- Coarse reciprocal masses produce only a cubic range cost.
  have hcs := finite_weighted_pair_sq_le (Icc 1 M) logCellWidth q v
    (fun b hb => logCellWidth_pos (mem_Icc.mp hb).1)
  have hn : 0 ≤ ∑ b ∈ Icc 1 M,(v b)^2/logCellWidth b :=
    sum_nonneg fun b hb => div_nonneg (sq_nonneg _)
      (logCellWidth_pos (mem_Icc.mp hb).1).le
  have hs (b : ℕ) (hb : b∈Icc 1 M) :
      (v b)^2/logCellWidth b ≤ C/((A:ℝ)+1)*((b:ℝ)+1)^2 := by
    have hb1 := (mem_Icc.mp hb).1
    have hw := (div_le_iff₀ (show (0:ℝ)<(b:ℝ)+1 by positivity)).mp
      (inv_add_one_le_logCellWidth hb1)
    have ht := mul_le_mul_of_nonneg_left hw
      (show 0≤C*((b:ℝ)+1)/((A:ℝ)+1) by positivity)
    rw [div_le_iff₀ (logCellWidth_pos hb1)]
    calc
      _ ≤ C*((b:ℝ)+1)/((A:ℝ)+1) := hv b hb1
      _ ≤ C*((b:ℝ)+1)/((A:ℝ)+1)*(logCellWidth b*((b:ℝ)+1)) := by
        simpa only [mul_one] using ht
      _ = C/((A:ℝ)+1)*((b:ℝ)+1)^2*logCellWidth b := by ring
  have hsum : (∑ b ∈ Icc 1 M,((b:ℝ)+1)^2) ≤ ((M:ℝ)+1)^3 := by
    calc
      _ ≤ ∑ _b ∈ Icc 1 M,((M:ℝ)+1)^2 := by
        apply sum_le_sum
        intro b hb
        apply pow_le_pow_left₀ (by positivity)
        exact add_le_add (by exact_mod_cast (mem_Icc.mp hb).2) le_rfl
      _ = (M:ℝ)*((M:ℝ)+1)^2 := by simp
      _ ≤ _ := by
        nlinarith only [sq_nonneg ((M:ℝ)+1)]
  calc
    _ ≤ _ := hcs
    _ ≤ 1*(∑ b ∈ Icc 1 M,(v b)^2/logCellWidth b) :=
      mul_le_mul_of_nonneg_right hq hn
    _ ≤ C/((A:ℝ)+1)*(∑ b ∈ Icc 1 M,((b:ℝ)+1)^2) := by
      rw [one_mul,mul_sum]
      exact sum_le_sum hs
    _ ≤ C/((A:ℝ)+1)*((M:ℝ)+1)^3 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

#print axioms finite_weighted_pair_sq_le
#print axioms sum_pronic_tail_le
#print axioms exists_fullPrimeWindowRemainder_hilbert_tail_bound
end GaloisForLFunctions.ArithmeticIndexDescent

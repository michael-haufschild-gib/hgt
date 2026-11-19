import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMoebiusPartOfAProducer
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.Spectrum.ResiduePrimitivesOfAFloorRow

/-!
# The discrepancy forced by two letters

A single ramp modulo k is an actual producer on the letters 1 and k.
The discrepancy is the difference of two quadratic residue primitives.
At half an even period the bound D k²/8 is attained, where D is the
height of the first step. In units of the peak, the loss is linear in k.
-/

open Finset GaloisForLFunctions.ArithmeticKreinLangerTheory
namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

noncomputable section

/-- Realize a single complete ramp with its exact peak and period. -/
theorem exists_two_letter_ramp {k : ℕ} (hk : 2 ≤ k) :
    ∃ (c : ℕ →₀ ℤ) (D : ℕ), IsProducer c D k ∧ c.support ⊆ {1,k} ∧
      (peak c : ℝ) = D*((k:ℝ)-1) ∧ ∀ n : ℕ, (stepWeight c n : ℝ) = D*((n%k:ℕ):ℝ) := by
  obtain ⟨c,D,hD,hzero,hbal,hstep,_,hsupp,_⟩ := exists_stencil_of_weights
    (J := {k}) (fun _ => 1) (fun p hp => (mem_singleton.mp hp) ▸ hk)
  have hr (r : ℕ) : (stepWeight c r : ℝ) = D*((r%k:ℕ):ℝ) := by simpa using hstep r
  have hP : IsProducer c D k := ⟨hzero,hbal,fun r => by
    have h := hr r
    exact_mod_cast (show (0:ℝ) ≤ stepWeight c r by rw [h]; positivity),hD,hk,fun r h => by
    obtain ⟨hlo,hhi⟩ := mem_Ico.mp h
    have he := hr r
    rw [Nat.mod_eq_of_lt hhi] at he
    have hle : (D:ℝ) ≤ stepWeight c r := by
      rw [he]
      exact le_mul_of_one_le_right (Nat.cast_nonneg _) (by exact_mod_cast hlo)
    exact_mod_cast hle⟩
  have hd : ∀ j ∈ c.support, j ∣ k := by
    intro j hj
    rcases (show j=1 ∨ j=k by simpa using hsupp hj) with rfl | rfl <;> simp
  have hpeak : stepWeight c (k-1) = peak c := by
    have h := stepWeight_reflect_add hzero hbal hd (show 0 < k by omega)
    simpa only [Nat.sub_zero,stepWeight_zero,add_zero,peak] using h
  refine ⟨c,D,hP,hsupp,?_,hr⟩
  rw [← hpeak,hr,Nat.mod_eq_of_lt (by omega),Nat.cast_sub (by omega : 1 ≤ k),Nat.cast_one]

private theorem ramp_discrepancy {c : ℕ →₀ ℤ} {D k : ℕ} (hk : 0 < k)
    (hp : (peak c : ℝ) = D*((k:ℝ)-1))
    (hr : ∀ n : ℕ, (stepWeight c n : ℝ) = D*((n%k:ℕ):ℝ)) (n L : ℕ) :
    (∑ j ∈ range L, (stepWeight c (n+j) : ℝ))-L*(peak c : ℝ)/2 =
      (D:ℝ)*k*(residuePrimitive k n-residuePrimitive k (n+L)) := by
  let F (r : ℕ) := (D:ℝ)*k*residuePrimitive k r
  have h (j : ℕ) : (stepWeight c (n+j) : ℝ)-(peak c : ℝ)/2 = F (n+j)-F (n+(j+1)) := by
    have ht := residue_primitive_step hk (n+j)
    rw [eq_div_iff (Nat.cast_ne_zero.mpr hk.ne')] at ht
    rw [hr,hp]
    unfold residue at ht
    dsimp only [F]
    rw [←Nat.add_assoc]
    linear_combination (D:ℝ)*ht
  have he := sum_congr (s₁ := range L) rfl (fun j _ => h j)
  rw [sum_range_sub' (fun j => F (n+j)) L] at he
  simpa only [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,←mul_div_assoc,Nat.add_zero,
    F,mul_sub] using he

/-- On every even alphabet size an actual producer attains its exact largest possible
interval discrepancy, which exceeds one eighth of the alphabet width times its peak. -/
theorem two_letter_exact_extremum {r : ℕ} (hr : 0 < r) :
    ∃ (c : ℕ →₀ ℤ) (D : ℕ), IsProducer c D (2*r) ∧ AlphabetLE c (2*r) ∧
      (∀ n L : ℕ, |(∑ j ∈ range L, (stepWeight c (n+j) : ℝ))-L*(peak c : ℝ)/2| ≤ D*(r:ℝ)^2/2) ∧
      |(∑ j ∈ range r, (stepWeight c j : ℝ))-r*(peak c : ℝ)/2| = D*(r:ℝ)^2/2 ∧
      (2*r : ℝ)*peak c/8 < D*(r:ℝ)^2/2 := by
  obtain ⟨c,D,hP,hs,hp,hm⟩ := exists_two_letter_ramp (show 2 ≤ 2*r by omega)
  have hr' : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hd := hP.m_pos
  have hprec := ramp_discrepancy (by omega : 0 < 2*r) hp hm
  have he (n : ℕ) : (0:ℝ) ≤ residuePrimitive (2*r) n ∧ residuePrimitive (2*r) n ≤ r/4 := by
    let x : ℝ := (n%(2*r):ℕ)
    have hx : 0 ≤ x := Nat.cast_nonneg _
    have hy : x ≤ 2*r := by
      dsimp only [x]
      exact_mod_cast (Nat.mod_lt n (by omega : 0 < 2*r)).le
    change 0 ≤ x*((2*r:ℕ)-x)/(2*(2*r:ℕ)) ∧ x*((2*r:ℕ)-x)/(2*(2*r:ℕ)) ≤ r/4
    push_cast
    exact ⟨div_nonneg (mul_nonneg hx (sub_nonneg.mpr hy)) (by positivity),
      (div_le_iff₀ (by positivity)).mpr (by nlinarith only [sq_nonneg (x-r)])⟩
  refine ⟨c,D,hP,fun j hj => ?_,fun n L => ?_,?_,?_⟩
  · rcases (show j=1 ∨ j=2*r by simpa using hs hj) with rfl | rfl <;> omega
  · rw [hprec,abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ D*(2*r:ℕ))]
    have H : |residuePrimitive (2*r) n - residuePrimitive (2*r) (n+L)| ≤ r/4 :=
      abs_le.mpr ⟨by linarith only [(he n).1,(he (n+L)).2],by linarith only [(he n).2,(he (n+L)).1]⟩
    have h := mul_le_mul_of_nonneg_left H (show 0 ≤ (D:ℝ)*(2*r:ℕ) by positivity)
    push_cast at h ⊢
    linarith only [h]
  · have h := congrArg abs (hprec 0 r)
    simp only [Nat.zero_add] at h
    have hz : residuePrimitive (2*r) 0 = 0 := by simp [residuePrimitive]
    have hm : residuePrimitive (2*r) r = r/4 := by
      rw [residuePrimitive,Nat.mod_eq_of_lt (by omega : r < 2*r)]
      push_cast
      field_simp
      <;> ring
    rw [h,hz,hm,zero_sub,abs_mul,abs_neg,abs_of_nonneg (by positivity : (0:ℝ) ≤ D*(2*r:ℕ)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ r/4)]
    push_cast
    ring
  · rw [hp]
    push_cast
    nlinarith only [mul_pos hd hr']

#print axioms exists_two_letter_ramp
#print axioms two_letter_exact_extremum

end

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

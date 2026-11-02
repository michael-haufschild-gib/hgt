import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineDiscreteJacobian

/-!
# Polynomial costs of exact spline correction

A common envelope for the finite scalar data controls the inverse correction
radius cubically, the number of nodes in degree six, and the height threshold
in degree nine. Multiplying the node-count bound by the grid spacing cancels
one frequency-scale factor, giving a degree-five bound for the grid span.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- The inverse correction radius has cubic growth in a common scalar envelope. -/
lemma inverse_spline_parameter_radius_le {X K Λ P Q : ℝ}
    (hX : 1 ≤ X) (hK : 1 ≤ K) (hΛ : 0 < Λ) (hΛK : Λ ≤ K*X)
    (hπ : 2/Real.pi ≤ K) (hP : 0 ≤ P) (hPX : P ≤ X) (hQ : 0 ≤ Q) (hQX : Q ≤ X) :
    1/(min ((Real.pi/(2*Λ))/(4*(P+1))) (1/(8*(Q*P^2+1)))) ≤ 24*K^2*X^3 := by
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  let h := Real.pi/(2*Λ)
  have hh : 0 < h := by dsimp only [h]; positivity
  have hP1 : 0 < P+1 := by positivity
  have hQ1 : 0 < Q*P^2+1 := by positivity
  have hhInv : 1/h ≤ K^2*X := by
    have he : 1/h=(2/Real.pi)*Λ := by dsimp only [h]; field_simp [hΛ.ne', Real.pi_ne_zero]
    rw [he]
    exact (mul_le_mul hπ hΛK hΛ.le hK0).trans_eq (by ring)
  have he1 : 1/(h/(4*(P+1)))=4*(P+1)*(1/h) := by
    field_simp [hh.ne',hP1.ne']
  have he2 : 1/(1/(8*(Q*P^2+1)))=8*(Q*P^2+1) := by
    field_simp [hQ1.ne']
  have hsum : 1/(min (h/(4*(P+1))) (1/(8*(Q*P^2+1)))) ≤
      4*(P+1)*(1/h)+8*(Q*P^2+1) := by
    rcases le_total (h/(4*(P+1))) (1/(8*(Q*P^2+1))) with hr | hr
    · rw [min_eq_left hr, he1]
      exact le_add_of_nonneg_right (by positivity)
    · rw [min_eq_right hr, he2]
      exact le_add_of_nonneg_left (by positivity)
  have hPX1 : P+1 ≤ 2*X := by linarith only [hPX,hX]
  have hfirst : 4*(P+1)*(1/h) ≤ 8*K^2*X^3 := by
    calc
      _ ≤ 4*(2*X)*(K^2*X) := mul_le_mul
        (mul_le_mul_of_nonneg_left hPX1 (by norm_num)) hhInv (by positivity) (by positivity)
      _ = 8*K^2*X^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX (by omega : 2 ≤ 3)) (by positivity)
  have hQP : Q*P^2 ≤ X^3 := by
    exact (mul_le_mul hQX (pow_le_pow_left₀ hP hPX 2) (sq_nonneg P) hX0).trans_eq (by ring)
  have hX3 : 1 ≤ X^3 := by simpa only [pow_zero] using pow_le_pow_right₀ hX (by omega : 0 ≤ 3)
  have hK2 : 1 ≤ K^2 := by simpa only [pow_zero] using pow_le_pow_right₀ hK (by omega : 0 ≤ 2)
  have hsecond : 8*(Q*P^2+1) ≤ 16*K^2*X^3 := by
    have h1 : Q*P^2+1 ≤ 2*X^3 := by linarith only [hQP,hX3]
    calc
      _ ≤ 16*X^3 := by linarith only [h1]
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hK2 (pow_nonneg hX0 3)]
  exact hsum.trans ((add_le_add hfirst hsecond).trans_eq (by ring))

#print axioms inverse_spline_parameter_radius_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- The grid span has one degree less than the node count because its spacing
cancels the frequency scale in the dominant term. -/
lemma spline_node_count_and_span_le {X K Λ A B η ρ : ℝ} {n : ℕ}
    (hX : 1 ≤ X) (hK : 1 ≤ K) (hΛ : 1 ≤ Λ) (hΛK : Λ ≤ K*X)
    (hπK : Real.pi ≤ K) (hKπ : 2/Real.pi ≤ K)
    (hAX : A ≤ X) (hB : 0 ≤ B) (hBX : B ≤ X)
    (hη : 0 < η) (hηX : 1/η ≤ X) (hρ : 0 < ρ) (hρX : 1/ρ ≤ 24*K^2*X^3)
    (hn : (n : ℝ) ≤ 2+8*A/(Real.pi/(2*Λ))+16*Λ*B/(η*ρ)) :
    (n : ℝ) ≤ 400*K^3*X^6 ∧ ((n : ℝ)+1)*(Real.pi/(2*Λ)) ≤ 210*K^3*X^5 := by
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  let h := Real.pi/(2*Λ)
  have hh : 0 < h := by dsimp only [h]; positivity
  have hhi : 1/h ≤ K^2*X := by
    have he : 1/h=(2/Real.pi)*Λ := by dsimp only [h]; field_simp [hΛ0.ne',Real.pi_ne_zero]
    rw [he]
    exact (mul_le_mul hKπ hΛK hΛ0.le hK0).trans_eq (by ring)
  have hhK : h ≤ K := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Λ)).2
    have hKL := mul_le_mul_of_nonneg_left hΛ hK0
    nlinarith only [hπK,hKL,hK]
  have hfirst : 8*A/h ≤ 8*K^2*X^2 := by
    rw [div_eq_mul_one_div]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hAX (by norm_num)) hhi
      (by positivity) (by positivity)).trans_eq (by ring)
  have hBη : B*(1/η) ≤ X^2 := by
    exact (mul_le_mul hBX hηX (by positivity) hX0).trans_eq (by ring)
  have hBηρ : B*(1/η)*(1/ρ) ≤ 24*K^2*X^5 := by
    exact (mul_le_mul hBη hρX (by positivity) (sq_nonneg X)).trans_eq (by ring)
  have hsecond : 16*Λ*B/(η*ρ) ≤ 384*K^3*X^6 := by
    have he : 16*Λ*B/(η*ρ)=16*Λ*(B*(1/η)*(1/ρ)) := by ring
    rw [he]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hΛK (by norm_num)) hBηρ
      (by positivity) (by positivity)).trans_eq (by ring)
  have hK3 : 1 ≤ K^3 := by simpa only [pow_zero] using pow_le_pow_right₀ hK (by omega : 0 ≤ 3)
  have hX6 : 1 ≤ X^6 := by simpa only [pow_zero] using pow_le_pow_right₀ hX (by omega : 0 ≤ 6)
  have hmon6 : 1 ≤ K^3*X^6 := by
    simpa only [one_mul] using mul_le_mul hK3 hX6 (by norm_num : (0 : ℝ) ≤ 1) (pow_nonneg hK0 3)
  have hsmall6 : K^2*X^2 ≤ K^3*X^6 := mul_le_mul
    (pow_le_pow_right₀ hK (by omega : 2 ≤ 3)) (pow_le_pow_right₀ hX (by omega : 2 ≤ 6))
    (pow_nonneg hX0 2) (pow_nonneg hK0 3)
  constructor
  · have hn' := hn.trans (add_le_add (add_le_add le_rfl hfirst) hsecond)
    nlinarith only [hn',hsmall6,hmon6]
  · have he : (2+8*A/h+16*Λ*B/(η*ρ)+1)*h=3*h+8*A+8*Real.pi*(B*(1/η)*(1/ρ)) := by
      dsimp only [h]
      field_simp [hΛ0.ne',Real.pi_ne_zero,hη.ne',hρ.ne']
      ring
    have hs : ((n : ℝ)+1)*h ≤ 3*h+8*A+8*Real.pi*(B*(1/η)*(1/ρ)) := by
      have hh' := mul_le_mul_of_nonneg_right (add_le_add hn (le_refl (1 : ℝ))) hh.le
      exact hh'.trans_eq he
    have hX5 : 1 ≤ X^5 := by simpa only [pow_zero] using pow_le_pow_right₀ hX (by omega : 0 ≤ 5)
    have hK3X5 : K ≤ K^3*X^5 := by
      have hKK3 : K ≤ K^3 := by simpa only [pow_one] using pow_le_pow_right₀ hK (by omega : 1 ≤ 3)
      simpa only [mul_one] using mul_le_mul hKK3 hX5 (by norm_num : (0 : ℝ) ≤ 1) (pow_nonneg hK0 3)
    have hXX5 : X ≤ K^3*X^5 := by
      have hXX5 : X ≤ X^5 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by omega : 1 ≤ 5)
      simpa only [one_mul] using mul_le_mul hK3 hXX5 hX0 (pow_nonneg hK0 3)
    have hthird : 8*Real.pi*(B*(1/η)*(1/ρ)) ≤ 192*K^3*X^5 := by
      exact (mul_le_mul (mul_le_mul_of_nonneg_left hπK (by norm_num)) hBηρ
        (by positivity) (by positivity)).trans_eq (by ring)
    have hs' := hs.trans (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hhK (by norm_num))
      (mul_le_mul_of_nonneg_left hAX (by norm_num))) hthird)
    nlinarith only [hs',hK3X5,hXX5,hK]

#print axioms spline_node_count_and_span_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- The height threshold has ninth-degree growth in the same scalar envelope. -/
lemma spline_height_threshold_le {X K C δ G B P ρ : ℝ}
    (hX : 1 ≤ X) (hK : 1 ≤ K) (hCX : C ≤ 210*K^3*X^5)
    (hδX : δ ≤ X) (hG : 0 ≤ G) (hGX : G ≤ X)
    (hB : 0 ≤ B) (hBX : B ≤ X) (hP : 0 ≤ P) (hPX : P ≤ X)
    (hρ : 0 < ρ) (hρX : 1/ρ ≤ 24*K^2*X^3) :
    1+64*((C+δ)*G+B)*P+64*(C+δ)*B/ρ ≤ 400000*K^5*X^9 := by
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hK3 : 1 ≤ K^3 := by simpa only [pow_zero] using pow_le_pow_right₀ hK (by omega : 0 ≤ 3)
  have hXX5 : X ≤ K^3*X^5 := by
    have hx : X ≤ X^5 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by omega : 1 ≤ 5)
    simpa only [one_mul] using mul_le_mul hK3 hx hX0 (pow_nonneg hK0 3)
  have hXX6 : X ≤ K^3*X^6 := by
    have hx : X ≤ X^6 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by omega : 1 ≤ 6)
    simpa only [one_mul] using mul_le_mul hK3 hx hX0 (pow_nonneg hK0 3)
  have hZ : C+δ ≤ 211*K^3*X^5 := by nlinarith only [hCX,hδX,hXX5]
  have hZG : (C+δ)*G ≤ 211*K^3*X^6 := by
    exact (mul_le_mul hZ hGX hG (by positivity)).trans_eq (by ring)
  have hZGB : (C+δ)*G+B ≤ 212*K^3*X^6 := by nlinarith only [hZG,hBX,hXX6]
  have hZGBP : ((C+δ)*G+B)*P ≤ 212*K^3*X^7 := by
    exact (mul_le_mul hZGB hPX hP (by positivity)).trans_eq (by ring)
  have hfirst : 64*((C+δ)*G+B)*P ≤ 13568*K^3*X^7 := by nlinarith only [hZGBP]
  have hZB : (C+δ)*B ≤ 211*K^3*X^6 := by
    exact (mul_le_mul hZ hBX hB (by positivity)).trans_eq (by ring)
  have hsecond : 64*(C+δ)*B/ρ ≤ 324096*K^5*X^9 := by
    have he : 64*(C+δ)*B/ρ=64*((C+δ)*B)*(1/ρ) := by ring
    rw [he]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hZB (by norm_num)) hρX
      (by positivity) (by positivity)).trans_eq (by ring)
  have hK5 : 1 ≤ K^5 := by simpa only [pow_zero] using pow_le_pow_right₀ hK (by omega : 0 ≤ 5)
  have hX9 : 1 ≤ X^9 := by simpa only [pow_zero] using pow_le_pow_right₀ hX (by omega : 0 ≤ 9)
  have hunit : 1 ≤ K^5*X^9 := by
    simpa only [one_mul] using mul_le_mul hK5 hX9 (by norm_num : (0 : ℝ) ≤ 1) (pow_nonneg hK0 5)
  have hmon : K^3*X^7 ≤ K^5*X^9 := mul_le_mul
    (pow_le_pow_right₀ hK (by omega : 3 ≤ 5)) (pow_le_pow_right₀ hX (by omega : 7 ≤ 9))
    (pow_nonneg hX0 7) (pow_nonneg hK0 5)
  nlinarith only [hfirst,hsecond,hunit,hmon]

#print axioms spline_height_threshold_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

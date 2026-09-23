import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapConvolution

/-! # Weighted top coefficients of the complete four-by-four Hankel determinant -/
namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

/-- A degree bound together with its coefficient, allowing a vanishing top coefficient. -/
def evenCompactGapTop (p : Polynomial ℝ) (n : ℕ) (c : ℝ) : Prop :=
  p.natDegree ≤ n ∧ p.coeff n = c

namespace evenCompactGapTop

 theorem add {p q : Polynomial ℝ} {n : ℕ} {a b : ℝ}
    (hp : evenCompactGapTop p n a) (hq : evenCompactGapTop q n b) :
    evenCompactGapTop (p+q) n (a+b) := by
  exact ⟨Polynomial.natDegree_add_le_of_degree_le hp.1 hq.1,
    by rw [Polynomial.coeff_add, hp.2, hq.2]⟩

 theorem sub {p q : Polynomial ℝ} {n : ℕ} {a b : ℝ}
    (hp : evenCompactGapTop p n a) (hq : evenCompactGapTop q n b) :
    evenCompactGapTop (p-q) n (a-b) := by
  exact ⟨by simpa only [max_self] using Polynomial.natDegree_sub_le_of_le hp.1 hq.1,
    by rw [Polynomial.coeff_sub, hp.2, hq.2]⟩

 theorem neg {p : Polynomial ℝ} {n : ℕ} {a : ℝ}
    (hp : evenCompactGapTop p n a) : evenCompactGapTop (-p) n (-a) := by
  exact ⟨Polynomial.natDegree_neg_le_of_le hp.1,
    by rw [Polynomial.coeff_neg, hp.2]⟩

 theorem mul {p q : Polynomial ℝ} {n m : ℕ} {a b : ℝ}
    (hp : evenCompactGapTop p n a) (hq : evenCompactGapTop q m b) :
    evenCompactGapTop (p*q) (n+m) (a*b) := by
  exact ⟨Polynomial.natDegree_mul_le_of_le hp.1 hq.1,
    by rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hp.1 hq.1, hp.2, hq.2]⟩

 theorem pow {p : Polynomial ℝ} {n : ℕ} {a : ℝ}
    (hp : evenCompactGapTop p n a) (k : ℕ) :
    evenCompactGapTop (p^k) (k*n) (a^k) := by
  exact ⟨Polynomial.natDegree_pow_le_of_le k hp.1,
    by rw [Polynomial.coeff_pow_of_natDegree_le hp.1, hp.2]⟩

 theorem constant (a : ℝ) : evenCompactGapTop (Polynomial.C a) 0 a := by
  simp [evenCompactGapTop]

/-- Weighted degree 2,3,...,8 turns the top determinant coefficient into the scalar determinant. -/
theorem hankel (a b c d e f g : Polynomial ℝ) (a' b' c' d' e' f' g' : ℝ)
    (ha : evenCompactGapTop a 2 a') (hb : evenCompactGapTop b 3 b')
    (hc : evenCompactGapTop c 4 c') (hd : evenCompactGapTop d 5 d')
    (he : evenCompactGapTop e 6 e') (hf : evenCompactGapTop f 7 f')
    (hg : evenCompactGapTop g 8 g') :
    evenCompactGapTop (hankelFourDet a b c d e f g) 20
      (hankelFourDet a' b' c' d' e' f' g') := by
  have htwo : evenCompactGapTop (2 : Polynomial ℝ) 0 2 := by
    norm_num [evenCompactGapTop]
  have hhead : evenCompactGapTop (a*c*e-a*d^(2 : ℕ)-b^(2 : ℕ)*e+2*b*c*d-c^(3 : ℕ)) 12
      (a'*c'*e'-a'*d'^(2 : ℕ)-b'^(2 : ℕ)*e'+2*b'*c'*d'-c'^(3 : ℕ)) :=
    sub (add (sub (sub (mul (mul ha hc) he) (mul ha (pow hd 2)))
      (mul (pow (n := 3) hb 2) he)) (mul (mul (mul htwo hb) hc) hd)) (pow hc 3)
  have h1 := mul (sub (mul hc he) (pow hd 2)) (pow hd 2)
  have h2 := mul (mul (mul htwo (sub (mul hc hd) (mul (n := 3) (m := 6) hb he))) hd) he
  have h3 := mul (mul (mul htwo (sub (mul (n := 3) (m := 5) hb hd) (pow (n := 4) hc 2))) hd) hf
  have h4 := mul (sub (mul ha he) (pow (n := 4) hc 2)) (pow he 2)
  have h5 := mul (mul (mul htwo (sub (mul hb hc) (mul (n := 2) (m := 5) ha hd))) he) hf
  have h6 := mul (sub (mul ha hc) (pow (n := 3) hb 2)) (pow hf 2)
  exact sub (mul hhead hg) (add (add (add (add (add h1 h2) h3) h4) h5) h6)

end evenCompactGapTop
end
end HTGeometry

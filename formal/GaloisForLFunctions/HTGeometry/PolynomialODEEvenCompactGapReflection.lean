import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapConvolution
import Mathlib.Algebra.Polynomial.Reverse

/-! # Weighted reflection of the complete four-by-four determinant -/
namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

/-- A bounded polynomial together with its exact reflection at the stated degree. -/
def evenCompactGapReflection (p : Polynomial ℝ) (n : ℕ) (q : Polynomial ℝ) : Prop :=
  p.natDegree ≤ n ∧ Polynomial.reflect n p = q

namespace evenCompactGapReflection

theorem add {p q a b : Polynomial ℝ} {n : ℕ}
    (hp : evenCompactGapReflection p n a) (hq : evenCompactGapReflection q n b) :
    evenCompactGapReflection (p+q) n (a+b) := by
  exact ⟨Polynomial.natDegree_add_le_of_degree_le hp.1 hq.1,
    by rw [Polynomial.reflect_add, hp.2, hq.2]⟩

theorem sub {p q a b : Polynomial ℝ} {n : ℕ}
    (hp : evenCompactGapReflection p n a) (hq : evenCompactGapReflection q n b) :
    evenCompactGapReflection (p-q) n (a-b) := by
  exact ⟨by simpa only [max_self] using Polynomial.natDegree_sub_le_of_le hp.1 hq.1,
    by rw [Polynomial.reflect_sub, hp.2, hq.2]⟩

theorem neg {p a : Polynomial ℝ} {n : ℕ}
    (hp : evenCompactGapReflection p n a) : evenCompactGapReflection (-p) n (-a) := by
  exact ⟨Polynomial.natDegree_neg_le_of_le hp.1,
    by rw [Polynomial.reflect_neg, hp.2]⟩

theorem mul {p q a b : Polynomial ℝ} {n m : ℕ}
    (hp : evenCompactGapReflection p n a) (hq : evenCompactGapReflection q m b) :
    evenCompactGapReflection (p*q) (n+m) (a*b) := by
  exact ⟨Polynomial.natDegree_mul_le_of_le hp.1 hq.1,
    by rw [Polynomial.reflect_mul p q hp.1 hq.1, hp.2, hq.2]⟩

theorem constant (a : ℝ) : evenCompactGapReflection (Polynomial.C a) 0 (Polynomial.C a) := by
  simp [evenCompactGapReflection, Polynomial.reflect_C]

theorem pow {p a : Polynomial ℝ} {n : ℕ}
    (hp : evenCompactGapReflection p n a) (k : ℕ) :
    evenCompactGapReflection (p^k) (k*n) (a^k) := by
  induction k with
  | zero => simpa using constant (1 : ℝ)
  | succ k ih => simpa only [pow_succ, Nat.succ_mul] using mul ih hp

/-- Weighted degree 2,3,...,8 turns the polynomial reflection into entrywise weighted reflection. -/
theorem hankel (a b c d e f g : Polynomial ℝ) (a' b' c' d' e' f' g' : Polynomial ℝ)
    (ha : evenCompactGapReflection a 2 a') (hb : evenCompactGapReflection b 3 b')
    (hc : evenCompactGapReflection c 4 c') (hd : evenCompactGapReflection d 5 d')
    (he : evenCompactGapReflection e 6 e') (hf : evenCompactGapReflection f 7 f')
    (hg : evenCompactGapReflection g 8 g') :
    evenCompactGapReflection (hankelFourDet a b c d e f g) 20
      (hankelFourDet a' b' c' d' e' f' g') := by
  have htwo : evenCompactGapReflection (2 : Polynomial ℝ) 0 2 := by
    simpa only [Polynomial.C_ofNat] using constant (2 : ℝ)
  have hhead : evenCompactGapReflection (a*c*e-a*d^2-b^2*e+2*b*c*d-c^3) 12
      (a'*c'*e'-a'*d'^2-b'^2*e'+2*b'*c'*d'-c'^3) :=
    sub (add (sub (sub (mul (mul ha hc) he) (mul ha (pow hd 2)))
      (mul (pow (n := 3) hb 2) he)) (mul (mul (mul htwo hb) hc) hd)) (pow hc 3)
  have h1 := mul (sub (mul hc he) (pow hd 2)) (pow hd 2)
  have h2 := mul (mul (mul htwo (sub (mul hc hd) (mul (n := 3) (m := 6) hb he))) hd) he
  have h3 := mul (mul (mul htwo (sub (mul (n := 3) (m := 5) hb hd) (pow (n := 4) hc 2))) hd) hf
  have h4 := mul (sub (mul ha he) (pow (n := 4) hc 2)) (pow he 2)
  have h5 := mul (mul (mul htwo (sub (mul hb hc) (mul (n := 2) (m := 5) ha hd))) he) hf
  have h6 := mul (sub (mul ha hc) (pow (n := 3) hb 2)) (pow hf 2)
  exact sub (mul hhead hg) (add (add (add (add (add h1 h2) h3) h4) h5) h6)

end evenCompactGapReflection
end
end HTGeometry

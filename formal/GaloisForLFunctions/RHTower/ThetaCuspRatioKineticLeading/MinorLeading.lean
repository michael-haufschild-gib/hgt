import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticLeading.ReflectionHeads

/-!
# Rank-one cancellation in the integer third minor

The third minor is `-H(R₂,R₄,R₆,R₈,R₁₀)` for the symmetric Hankel cubic
`H(a,b,c,d,e) = ace - ad² - b²e + 2bcd - c³`.  Reverse each reflected moment about its kinetic
degree bound and divide by `12^n`: `Q_n = 12^{-n} J^n R_n(1/J)` has constant coefficient
`q = -12y` for every index and linear coefficient
`F_n = u(4(n-1)y² - 2(n²-n+3)y) + (8/3)u y² δ_{n,2}`.

For arbitrary elements of a commutative ring
`H(q+xa, q+xb, q+xc, q+xd, q+xe) = x² q M(a,…,e) + x³ H(a,…,e)` with the rank-one residual
`M = (c-2b+a)(e-2c+a) - (d-b-c+a)²`.  Applied to the complete quotients `Q_n = q + x·divX Q_n`
this splits the reversed source determinant exactly into a quadratic residual and a cubic
remainder.  Consequently the kinetic degree of the third minor is at most `16` and

`[J^16] integerThirdMinor = -512·12^18 u² y⁴`.

The residual entries `F'_{a,b} = F_{2a+2b+2} - F_{2a+2} - F_{2b+2} + F_2` equal
`(8/3)u y² - 16 u y ab` for all positive indices, so the residual pairing of any two finite
weight vectors depends only on their zeroth and first index moments, and is indefinite.
-/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial Finset

/-! ## The Hankel cubic and its rank-one shift -/

/-- The symmetric Hankel cubic, the determinant of `[[a,b,c],[b,c,d],[c,d,e]]`. -/
def hankelCubic {R : Type*} [CommRing R] (a b c d e : R) : R :=
  a*c*e-a*d^2-b^2*e+2*b*c*d-c^3

/-- The rank-one residual minor. -/
def hankelResidual {R : Type*} [CommRing R] (a b c d e : R) : R :=
  (c-2*b+a)*(e-2*c+a)-(d-b-c+a)^2

/-- **Exact rank-one shift.**  Over any commutative ring,
`H(q+xa,…,q+xe) = x² q M(a,…,e) + x³ H(a,…,e)`. -/
theorem hankelCubic_shift {R : Type*} [CommRing R] (q x a b c d e : R) :
    hankelCubic (q+x*a) (q+x*b) (q+x*c) (q+x*d) (q+x*e) =
      x^2*q*hankelResidual a b c d e+x^3*hankelCubic a b c d e := by
  unfold hankelCubic hankelResidual
  ring

theorem integerThirdMinor_eq_neg_hankel :
    integerThirdMinor = -hankelCubic (integerReflection 2) (integerReflection 4)
      (integerReflection 6) (integerReflection 8) (integerReflection 10) := by
  unfold integerThirdMinor integerSignedMoment hankelCubic
  norm_num
  ring

/-! ## Normalized reversed reflections -/

/-- `Q_n = 12^{-n} J^n R_n(1/J)`. -/
def reversedReflection (n : ℕ) : Polynomial KCoeff :=
  Polynomial.C (C ((12:ℂ)^n)⁻¹)*Polynomial.reflect n (kineticEquiv (integerReflection n))

theorem reflect_integerReflection (n : ℕ) :
    Polynomial.reflect n (kineticEquiv (integerReflection n)) =
      Polynomial.C (C ((12:ℂ)^n))*reversedReflection n := by
  unfold reversedReflection
  rw [← mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel₀ (pow_ne_zero n (by norm_num)), map_one,
    map_one, one_mul]

private theorem C12_pow_inv_mul (n : ℕ) (x : KCoeff) :
    C ((12:ℂ)^n)⁻¹*((12:KCoeff)^n*x) = x := by
  rw [← mul_assoc, show (12:KCoeff)^n = C ((12:ℂ)^n) by rw [map_pow, map_ofNat], ← map_mul,
    inv_mul_cancel₀ (pow_ne_zero n (by norm_num)), map_one, one_mul]

/-- The constant coefficient of every normalized reversal is `-12y`. -/
theorem reversedReflection_coeff_zero {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    (reversedReflection n).coeff 0 = -12*kineticYC := by
  rw [reversedReflection, Polynomial.coeff_C_mul, Polynomial.coeff_reflect, Polynomial.revAt_le
    (by omega), Nat.sub_zero, integerReflection_kinetic_top_even hn he,
    show -(12:KCoeff)^(n+1)*kineticYC = (12:KCoeff)^n*(-12*kineticYC) by ring]
  exact C12_pow_inv_mul n _

/-- The linear coefficient `F_n`. -/
def reversedLinear (n : ℕ) : KCoeff :=
  kineticU*(4*((n:KCoeff)-1)*kineticYC^2-2*((n:KCoeff)^2-n+3)*kineticYC)+
    (if n = 2 then C (8/3)*kineticU*kineticYC^2 else 0)

theorem reversedReflection_coeff_one {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    (reversedReflection n).coeff 1 = reversedLinear n := by
  rw [reversedReflection, Polynomial.coeff_C_mul, Polynomial.coeff_reflect, Polynomial.revAt_le
    (by omega)]
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · have h2 : n = 2 := by obtain ⟨k, hk⟩ := he; omega
    subst h2
    rw [show 2 - 1 = 1 by rfl, integerReflection_two_kinetic_subtop]
    unfold reversedLinear
    rw [if_pos rfl]
    have hC : (C ((12:ℂ)^2)⁻¹ : KCoeff) = C (1/144 : ℂ) := by norm_num
    rw [hC]
    have e1 : (C (1/144 : ℂ) : KCoeff) * (960:KCoeff) = 4*(2-1)+C (8/3) := by
      rw [show (960:KCoeff) = C 960 by rw [map_ofNat], ← map_mul, show (4:KCoeff)*(2-1) = C 4 by
        rw [map_ofNat]; ring, ← map_add]; congr 1; norm_num
    have e2 : (C (1/144 : ℂ) : KCoeff) * (1440:KCoeff) = 2*(2^2-2+3) := by
      rw [show (1440:KCoeff) = C 1440 by rw [map_ofNat], ← map_mul, show (2:KCoeff)*(2^2-2+3) = C 10 by
        rw [map_ofNat]; ring]; congr 1; norm_num
    push_cast
    linear_combination kineticU*kineticYC^2*e1 - kineticU*kineticYC*e2
  · rw [integerReflection_kinetic_subtop_even h4 he]
    unfold reversedLinear
    rw [if_neg (by omega), add_zero,
      show kineticU*12^(n-1)*(48*((n:KCoeff)-1)*kineticYC^2-24*((n:KCoeff)^2-n+3)*kineticYC) =
        (12:KCoeff)^n*(kineticU*(4*((n:KCoeff)-1)*kineticYC^2-2*((n:KCoeff)^2-n+3)*kineticYC)) by
        rw [show (12:KCoeff)^n = 12^(n-1)*12 by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]]
        ring]
    exact C12_pow_inv_mul n _

/-! ## Reversal of the Hankel cubic -/

theorem hankelCubic_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b c d e : R) :
    φ (hankelCubic a b c d e) = hankelCubic (φ a) (φ b) (φ c) (φ d) (φ e) := by
  simp [hankelCubic, map_ofNat]

theorem hankelResidual_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b c d e : R) :
    φ (hankelResidual a b c d e) = hankelResidual (φ a) (φ b) (φ c) (φ d) (φ e) := by
  simp [hankelResidual, map_ofNat]

private theorem reflect_triple {f g h : Polynomial KCoeff} {F G H : ℕ} (hf : f.natDegree ≤ F)
    (hg : g.natDegree ≤ G) (hh : h.natDegree ≤ H) :
    Polynomial.reflect (F+G+H) (f*g*h) =
      Polynomial.reflect F f*Polynomial.reflect G g*Polynomial.reflect H h := by
  rw [Polynomial.reflect_mul _ _ (Polynomial.natDegree_mul_le_of_le hf hg) hh,
    Polynomial.reflect_mul _ _ hf hg]

/-- Reversal at total weight `18` commutes with the weighted Hankel cubic. -/
theorem reflect_hankelCubic {a b c d e : Polynomial KCoeff} (ha : a.natDegree ≤ 2)
    (hb : b.natDegree ≤ 4) (hc : c.natDegree ≤ 6) (hd : d.natDegree ≤ 8) (he : e.natDegree ≤ 10) :
    Polynomial.reflect 18 (hankelCubic a b c d e) =
      hankelCubic (Polynomial.reflect 2 a) (Polynomial.reflect 4 b) (Polynomial.reflect 6 c)
        (Polynomial.reflect 8 d) (Polynomial.reflect 10 e) := by
  unfold hankelCubic
  have t1 := reflect_triple ha hc he
  have t2 := reflect_triple ha hd hd
  have t3 := reflect_triple hb hb he
  have t4 := reflect_triple hb hc hd
  have t5 := reflect_triple hc hc hc
  norm_num at t1 t2 t3 t4 t5
  have h2 : Polynomial.reflect 18 (2*b*c*d) = 2*Polynomial.reflect 18 (b*c*d) := by
    rw [show (2:Polynomial KCoeff)*b*c*d = Polynomial.C 2*(b*c*d) by rw [map_ofNat]; ring,
      Polynomial.reflect_C_mul, map_ofNat]
  simp only [Polynomial.reflect_sub, Polynomial.reflect_add, pow_two, pow_three, ← mul_assoc, h2,
    t1, t2, t3, t4, t5]

theorem natDegree_hankelCubic_le {a b c d e : Polynomial KCoeff} (ha : a.natDegree ≤ 2)
    (hb : b.natDegree ≤ 4) (hc : c.natDegree ≤ 6) (hd : d.natDegree ≤ 8) (he : e.natDegree ≤ 10) :
    (hankelCubic a b c d e).natDegree ≤ 18 := by
  have hform : hankelCubic a b c d e =
      a*c*e - a*d*d - b*b*e + Polynomial.C 2*(b*c*d) - c*c*c := by
    unfold hankelCubic; rw [map_ofNat]; ring
  have m3 : ∀ {f g h : Polynomial KCoeff} {F G H : ℕ}, f.natDegree ≤ F → g.natDegree ≤ G →
      h.natDegree ≤ H → F+G+H = 18 → (f*g*h).natDegree ≤ 18 := fun hf hg hh hs =>
    hs ▸ Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le hf hg) hh
  rw [hform]
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (m3 hc hc hc rfl))
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_
    ((Polynomial.natDegree_C_mul_le 2 _).trans (m3 hb hc hd rfl)))
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (m3 hb hb he rfl))
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le (m3 ha hc he rfl) (m3 ha hd hd rfl))

/-! ## The third minor -/

private theorem deg2 : (kineticEquiv (integerReflection 2)).natDegree ≤ 2 :=
  integerReflection_kinetic_natDegree 2
private theorem deg4 : (kineticEquiv (integerReflection 4)).natDegree ≤ 4 :=
  integerReflection_kinetic_natDegree 4
private theorem deg6 : (kineticEquiv (integerReflection 6)).natDegree ≤ 6 :=
  integerReflection_kinetic_natDegree 6
private theorem deg8 : (kineticEquiv (integerReflection 8)).natDegree ≤ 8 :=
  integerReflection_kinetic_natDegree 8
private theorem deg10 : (kineticEquiv (integerReflection 10)).natDegree ≤ 10 :=
  integerReflection_kinetic_natDegree 10

theorem kineticEquiv_integerThirdMinor :
    kineticEquiv integerThirdMinor = -hankelCubic (kineticEquiv (integerReflection 2))
      (kineticEquiv (integerReflection 4)) (kineticEquiv (integerReflection 6))
      (kineticEquiv (integerReflection 8)) (kineticEquiv (integerReflection 10)) := by
  rw [integerThirdMinor_eq_neg_hankel, map_neg]
  congr 1
  exact hankelCubic_map kineticEquiv.toRingHom _ _ _ _ _

/-- The reversed third minor is `-12^18 H(Q₂,…,Q₁₀)`. -/
theorem reflect_integerThirdMinor :
    Polynomial.reflect 18 (kineticEquiv integerThirdMinor) =
      -(Polynomial.C (C (12:ℂ)) : Polynomial KCoeff)^18*hankelCubic (reversedReflection 2) (reversedReflection 4)
        (reversedReflection 6) (reversedReflection 8) (reversedReflection 10) := by
  rw [kineticEquiv_integerThirdMinor, Polynomial.reflect_neg,
    reflect_hankelCubic deg2 deg4 deg6 deg8 deg10, reflect_integerReflection,
    reflect_integerReflection, reflect_integerReflection, reflect_integerReflection,
    reflect_integerReflection]
  simp only [map_pow]
  unfold hankelCubic
  ring

/-- Every normalized reversal is its constant `-12y` plus `J` times its complete quotient. -/
theorem reversedReflection_split {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    reversedReflection n = Polynomial.C (-12*kineticYC) +
      Polynomial.X*(reversedReflection n).divX := by
  rw [← reversedReflection_coeff_zero hn he, add_comm]
  exact (Polynomial.X_mul_divX_add _).symm

/-- **Exact quadratic-plus-cubic decomposition** of the reversed source minor, with every complete
quotient retained. -/
theorem reversedMinor_decomposition :
    hankelCubic (reversedReflection 2) (reversedReflection 4) (reversedReflection 6)
        (reversedReflection 8) (reversedReflection 10) =
      Polynomial.X^2*Polynomial.C (-12*kineticYC)*hankelResidual (reversedReflection 2).divX
          (reversedReflection 4).divX (reversedReflection 6).divX (reversedReflection 8).divX
          (reversedReflection 10).divX +
        Polynomial.X^3*hankelCubic (reversedReflection 2).divX (reversedReflection 4).divX
          (reversedReflection 6).divX (reversedReflection 8).divX (reversedReflection 10).divX := by
  conv_lhs => rw [reversedReflection_split (n := 2) le_rfl (by decide),
    reversedReflection_split (n := 4) (by norm_num) (by decide),
    reversedReflection_split (n := 6) (by norm_num) (by decide),
    reversedReflection_split (n := 8) (by norm_num) (by decide),
    reversedReflection_split (n := 10) (by norm_num) (by decide)]
  exact hankelCubic_shift _ _ _ _ _ _ _

/-- The residual at the linear coefficients: `M(F₂,…,F₁₀) = -16·(8/3)·u² y³`. -/
theorem hankelResidual_reversedLinear :
    hankelResidual (reversedLinear 2) (reversedLinear 4) (reversedLinear 6) (reversedLinear 8)
      (reversedLinear 10) = -16*C (8/3)*kineticU^2*kineticYC^3 := by
  unfold hankelResidual reversedLinear
  norm_num
  ring

private theorem coeff_zero_divX_reversed {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    Polynomial.eval 0 (reversedReflection n).divX = reversedLinear n := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX, zero_add,
    reversedReflection_coeff_one hn he]

/-- **Kinetic degree and leading coefficient of the integer third minor.**
`deg_J ≤ 16` and `[J^16] integerThirdMinor = -512·12^18 u² y⁴`. -/
theorem integerThirdMinor_kinetic_leading :
    (kineticEquiv integerThirdMinor).natDegree ≤ 16 ∧
      (kineticEquiv integerThirdMinor).coeff 16 = -512*12^18*kineticU^2*kineticYC^4 := by
  have hR := reflect_integerThirdMinor
  rw [reversedMinor_decomposition] at hR
  have hc : ∀ k ≤ 18, (kineticEquiv integerThirdMinor).coeff k =
      (Polynomial.reflect 18 (kineticEquiv integerThirdMinor)).coeff (18 - k) := by
    intro k hk
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le (by omega), Nat.sub_sub_self hk]
  have hres : (hankelResidual (reversedReflection 2).divX (reversedReflection 4).divX
      (reversedReflection 6).divX (reversedReflection 8).divX
      (reversedReflection 10).divX).coeff 0 = -16*C (8/3)*kineticU^2*kineticYC^3 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom, hankelResidual_map]
    simp only [Polynomial.coe_evalRingHom]
    rw [coeff_zero_divX_reversed (n := 2) le_rfl (by decide),
      coeff_zero_divX_reversed (n := 4) (by norm_num) (by decide),
      coeff_zero_divX_reversed (n := 6) (by norm_num) (by decide),
      coeff_zero_divX_reversed (n := 8) (by norm_num) (by decide),
      coeff_zero_divX_reversed (n := 10) (by norm_num) (by decide), hankelResidual_reversedLinear]
  set M := hankelResidual (reversedReflection 2).divX (reversedReflection 4).divX
      (reversedReflection 6).divX (reversedReflection 8).divX (reversedReflection 10).divX with hM
  set H := hankelCubic (reversedReflection 2).divX (reversedReflection 4).divX
      (reversedReflection 6).divX (reversedReflection 8).divX (reversedReflection 10).divX with hH
  have hR' : Polynomial.reflect 18 (kineticEquiv integerThirdMinor) =
      Polynomial.X^2*(Polynomial.C (-(12:KCoeff)^18*(-12*kineticYC))*M) +
        Polynomial.X^3*(Polynomial.C (-(12:KCoeff)^18)*H) := by
    rw [hR]; simp only [map_neg, map_pow, map_mul, map_ofNat]; ring
  have hcoef : ∀ d, (Polynomial.reflect 18 (kineticEquiv integerThirdMinor)).coeff d =
      (if 2 ≤ d then (-(12:KCoeff)^18*(-12*kineticYC))*M.coeff (d-2) else 0) +
        (if 3 ≤ d then (-(12:KCoeff)^18)*H.coeff (d-3) else 0) := by
    intro d
    rw [hR', Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul',
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  have h18 : (kineticEquiv integerThirdMinor).coeff 18 = 0 := by
    rw [hc 18 le_rfl, hcoef]; simp
  have h17 : (kineticEquiv integerThirdMinor).coeff 17 = 0 := by
    rw [hc 17 (by norm_num), hcoef]; simp
  have h16 : (kineticEquiv integerThirdMinor).coeff 16 =
      -12^18*((-12*kineticYC)*(-16*C (8/3)*kineticU^2*kineticYC^3)) := by
    rw [hc 16 (by norm_num), hcoef]
    simp only [show 18 - 16 = 2 by rfl, le_refl, if_true, Nat.sub_self, show ¬ (3 ≤ 2) by norm_num,
      if_false, add_zero, hres]
    ring
  refine ⟨?_, ?_⟩
  · have h := natDegree_hankelCubic_le deg2 deg4 deg6 deg8 deg10
    rw [kineticEquiv_integerThirdMinor, Polynomial.natDegree_neg] at ⊢
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rcases Nat.lt_or_ge 18 N with h' | h'
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h h')
    · have : N = 17 ∨ N = 18 := by omega
      have h17' := h17; have h18' := h18
      rw [kineticEquiv_integerThirdMinor, Polynomial.coeff_neg, neg_eq_zero] at h17' h18'
      rcases this with rfl | rfl
      · exact h17'
      · exact h18'
  · rw [h16]
    have h83 : C (8/3 : ℂ) * (3 : KCoeff) = 8 := by
      rw [show (3:KCoeff) = C 3 by rw [map_ofNat], ← map_mul, show (8:KCoeff) = C 8 by
        rw [map_ofNat]]; congr 1; norm_num
    linear_combination (-(12:KCoeff)^18*64*kineticU^2*kineticYC^4)*h83

/-! ## The residual pairing -/

/-- Double differences of the linear coefficients, `F'_{a,b}`. -/
def residualEntry (a b : ℕ) : KCoeff :=
  reversedLinear (2*a+2*b+2)-reversedLinear (2*a+2)-reversedLinear (2*b+2)+reversedLinear 2

/-- `F'_{a,b}` is the double difference of the actual reversed source coefficients. -/
theorem residualEntry_eq_source (a b : ℕ) :
    residualEntry a b = (reversedReflection (2*a+2*b+2)).coeff 1-(reversedReflection (2*a+2)).coeff 1-
      (reversedReflection (2*b+2)).coeff 1+(reversedReflection 2).coeff 1 := by
  have ev : ∀ m : ℕ, Even (2*m+2) := fun m => ⟨m+1, by ring⟩
  rw [residualEntry, reversedReflection_coeff_one (by omega) ⟨a+b+1, by ring⟩,
    reversedReflection_coeff_one (by omega) (ev a), reversedReflection_coeff_one (by omega) (ev b),
    reversedReflection_coeff_one le_rfl (by decide)]

/-- **Residual entries** for all positive indices: `F'_{a,b} = (8/3)u y² - 16 u y ab`. -/
theorem residualEntry_closed {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    residualEntry a b = C (8/3)*kineticU*kineticYC^2-16*kineticU*kineticYC*(a:KCoeff)*(b:KCoeff) := by
  unfold residualEntry reversedLinear
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  push_cast
  ring

/-- **Two-moment law.**  For arbitrary finite sets of positive indices and arbitrary weights the
residual pairing depends only on the zeroth and first index moments. -/
theorem residual_pairing (S T : Finset ℕ) (hS : ∀ a ∈ S, 1 ≤ a) (hT : ∀ b ∈ T, 1 ≤ b)
    (A B : ℕ → KCoeff) :
    ∑ a ∈ S, ∑ b ∈ T, A a*B b*residualEntry a b =
      C (8/3)*kineticU*kineticYC^2*(∑ a ∈ S, A a)*(∑ b ∈ T, B b)-
        16*kineticU*kineticYC*(∑ a ∈ S, (a:KCoeff)*A a)*(∑ b ∈ T, (b:KCoeff)*B b) := by
  set c := C (8/3)*kineticU*kineticYC^2
  set d := 16*kineticU*kineticYC
  have h : ∀ a ∈ S, ∑ b ∈ T, A a*B b*residualEntry a b =
      ∑ b ∈ T, (c*(A a*B b)-d*(((a:KCoeff)*A a)*((b:KCoeff)*B b))) := by
    intro a ha
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [residualEntry_closed (hS a ha) (hT b hb)]; ring
  rw [Finset.sum_congr rfl h, mul_assoc c, mul_assoc d, Finset.sum_mul_sum, Finset.sum_mul_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- The residual quadratic form on the first two indices. -/
theorem residual_quadratic_form (x z : KCoeff) :
    x*x*residualEntry 1 1+x*z*residualEntry 1 2+z*x*residualEntry 2 1+z*z*residualEntry 2 2 =
      C (8/3)*kineticU*kineticYC^2*(x+z)^2-16*kineticU*kineticYC*(x+2*z)^2 := by
  rw [residualEntry_closed le_rfl le_rfl, residualEntry_closed le_rfl (by norm_num),
    residualEntry_closed (by norm_num) le_rfl, residualEntry_closed (by norm_num) (by norm_num)]
  push_cast; ring

/-- The two source directions `(1,-1)` and `(2,-1)`. -/
theorem residual_directions :
    C (8/3)*kineticU*kineticYC^2*((1:KCoeff)+(-1))^2-16*kineticU*kineticYC*((1:KCoeff)+2*(-1))^2 =
        -16*kineticU*kineticYC ∧
      C (8/3)*kineticU*kineticYC^2*((2:KCoeff)+(-1))^2-16*kineticU*kineticYC*((2:KCoeff)+2*(-1))^2 =
        C (8/3)*kineticU*kineticYC^2 := by
  constructor <;> ring

/-- **Indefiniteness.**  At every real point with `u ≠ 0` and `y > 0` the two directions have
values of opposite strict sign. -/
theorem residual_indefinite {u k : ℝ} (hu : u ≠ 0) (hy : 0 < 3*k+1) :
    let pt : Fin 2 → ℂ := ![(u:ℂ), (k:ℂ)]
    eval pt (-16*kineticU*kineticYC) = ((-16*u*(3*k+1) : ℝ) : ℂ) ∧
      eval pt (C (8/3)*kineticU*kineticYC^2) = ((8/3*u*(3*k+1)^2 : ℝ) : ℂ) ∧
      (-16*u*(3*k+1))*(8/3*u*(3*k+1)^2) < 0 := by
  refine ⟨by simp [kineticU, kineticYC], by simp [kineticU, kineticYC], ?_⟩
  have hu2 : 0 < u^2 := by positivity
  nlinarith [mul_pos hu2 (pow_pos hy 3)]

/-- The normalized residual `E_{a,b} = u((4/3)ab - (2/9)y)`, with `F'_{a,b} = -12y E_{a,b}`. -/
def normalizedResidual (a b : ℕ) : KCoeff := kineticU*(C (4/3)*(a:KCoeff)*(b:KCoeff)-C (2/9)*kineticYC)

theorem residualEntry_eq_normalized {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    residualEntry a b = -12*kineticYC*normalizedResidual a b := by
  rw [residualEntry_closed ha hb, normalizedResidual]
  have h1 : (12:KCoeff)*C (4/3) = 16 := by
    rw [show (12:KCoeff) = C 12 by rw [map_ofNat], ← map_mul, show (16:KCoeff) = C 16 by
      rw [map_ofNat]]; congr 1; norm_num
  have h2 : (12:KCoeff)*C (2/9) = C (8/3) := by
    rw [show (12:KCoeff) = C 12 by rw [map_ofNat], ← map_mul]; congr 1; norm_num
  linear_combination (kineticU*kineticYC*(a:KCoeff)*(b:KCoeff))*h1 - (kineticU*kineticYC^2)*h2

/-- `det E = -(8/27) u² y` on the first two indices. -/
theorem normalizedResidual_det :
    normalizedResidual 1 1*normalizedResidual 2 2-normalizedResidual 1 2*normalizedResidual 2 1 =
      -C (8/27)*kineticU^2*kineticYC := by
  unfold normalizedResidual
  have h1 : (C (4/3:ℂ) : KCoeff)*C (2/9) = C (8/27) := by rw [← map_mul]; congr 1; norm_num
  push_cast
  linear_combination (-kineticU^2*kineticYC*(1+4-2-2))*h1

end
end HTGeometry.ThetaRatioSource

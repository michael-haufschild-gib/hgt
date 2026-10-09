import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticLeading.KineticCoefficients
import GaloisForLFunctions.HTGeometry.MicroSpectrumMomentCollapse

/-!
# Top two kinetic coefficients of every reflected moment

For the reflected moments `R_n = Σ_i C(n,i)(-1)^{n-i} P_i P_{n-i}` the kinetic degree is at most
`n`.  For every even `n ≥ 2`

`[J^n] R_n = -12^{n+1} y`,

the two endpoint terms carrying the exceptional value `a_0 = 2y - 3`.  The subleading coefficient is

`[J^{n-1}] R_n = u·12^{n-1}(48(n-1)y² - 24(n²-n+3)y)` for even `n ≥ 4`,
`[J] R_2 = u(960y² - 1440y)`,

the exceptional first jet `b_1` and the exceptional `a_0` both contributing.
-/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial Finset

/-! ## Second coefficient of a product -/

/-- Subleading coefficient below a degree bound `d`, zero when `d = 0`. -/
def subTop (p : Polynomial KCoeff) (d : ℕ) : KCoeff := if d = 0 then 0 else p.coeff (d-1)

theorem coeff_mul_subTop {f g : Polynomial KCoeff} {df dg : ℕ} (hf : f.natDegree ≤ df)
    (hg : g.natDegree ≤ dg) (hd : 1 ≤ df + dg) :
    (f * g).coeff (df + dg - 1) = f.coeff df * subTop g dg + subTop f df * g.coeff dg := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have key : ∀ k ∈ range (df + dg - 1).succ, f.coeff k * g.coeff (df + dg - 1 - k) =
      (if k = df then f.coeff df * subTop g dg else 0) +
        (if k + 1 = df then subTop f df * g.coeff dg else 0) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    by_cases h1 : k = df
    · subst h1
      have hdg : dg ≠ 0 := by omega
      simp [subTop, hdg, show k + dg - 1 - k = dg - 1 by omega]
    · by_cases h2 : k + 1 = df
      · subst h2
        simp [subTop]
      · simp only [h1, h2, if_false, add_zero]
        rcases Nat.lt_or_gt_of_ne h1 with hlt | hgt
        · have : dg < df + dg - 1 - k := by omega
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hg this), mul_zero]
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hf hgt), zero_mul]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_ite_eq']
  rcases Nat.eq_zero_or_pos df with h0 | h0
  · subst h0
    have hz : ∀ k ∈ range (0 + dg - 1).succ, (if k + 1 = 0 then subTop f 0 * g.coeff dg else 0) = 0 :=
      fun k _ => by simp
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
    simp [subTop]
  · have hz : ∀ k ∈ range (df + dg - 1).succ,
        (if k + 1 = df then subTop f df * g.coeff dg else 0) =
          (if k = df - 1 then subTop f df * g.coeff dg else 0) := by
      intro k _
      by_cases hk : k = df - 1
      · simp [hk, show df - 1 + 1 = df by omega]
      · simp [hk, show k + 1 ≠ df by omega]
    rw [Finset.sum_congr rfl hz, Finset.sum_ite_eq']
    have hm : df - 1 ∈ range (df + dg - 1).succ := by simp; omega
    simp only [hm, if_true]
    by_cases hdg : dg = 0
    · subst hdg
      simp [subTop]
    · simp [show df < (df + dg - 1).succ by omega]

/-! ## Reflected moments -/

theorem kineticEquiv_integerReflection (n : ℕ) :
    kineticEquiv (integerReflection n) =
      ∑ i ∈ range (n+1), ((n.choose i : Polynomial KCoeff)*(-1)^(n-i))*
        (kineticEquiv (integerJet i)*kineticEquiv (integerJet (n-i))) := by
  simp [integerReflection, map_sum, mul_assoc]

theorem integerReflection_kinetic_natDegree (n : ℕ) :
    (kineticEquiv (integerReflection n)).natDegree ≤ n := by
  rw [kineticEquiv_integerReflection]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i hi => ?_)
  have hi : i ≤ n := by simp at hi; omega
  refine (Polynomial.natDegree_mul_le).trans ?_
  have h1 : ((n.choose i : Polynomial KCoeff)*(-1)^(n-i)).natDegree = 0 := by
    rw [show ((n.choose i : Polynomial KCoeff)*(-1)^(n-i)) =
      Polynomial.C ((n.choose i : KCoeff)*(-1)^(n-i)) by simp]
    exact Polynomial.natDegree_C _
  rw [h1, zero_add]
  refine Polynomial.natDegree_mul_le_of_le (integerJet_kinetic_head i).1
    (integerJet_kinetic_head (n-i)).1 |>.trans (by omega)

theorem integerReflection_kinetic_top (n : ℕ) :
    (kineticEquiv (integerReflection n)).coeff n =
      ∑ i ∈ range (n+1), ((n.choose i : KCoeff)*(-1)^(n-i))*(headA i*headA (n-i)) := by
  rw [kineticEquiv_integerReflection, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi : i ≤ n := by simp at hi; omega
  rw [show ((n.choose i : Polynomial KCoeff)*(-1)^(n-i)) =
    Polynomial.C ((n.choose i : KCoeff)*(-1)^(n-i)) by simp, Polynomial.coeff_C_mul]
  congr 1
  have h := Polynomial.coeff_mul_add_eq_of_natDegree_le (integerJet_kinetic_head i).1
    (integerJet_kinetic_head (n-i)).1
  rw [show i + (n - i) = n by omega] at h
  rw [h, (integerJet_kinetic_head i).2, (integerJet_kinetic_head (n-i)).2]

/-- `B'_k`: the subleading coefficient of `P_k`, zero for `k = 0`. -/
def subHeadB (k : ℕ) : KCoeff := if k = 0 then 0 else headB k

theorem integerJet_subTop (k : ℕ) : subTop (kineticEquiv (integerJet k)) k = subHeadB k := by
  unfold subTop subHeadB
  rcases k with _ | k
  · simp
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    exact integerJet_kinetic_subhead k

theorem integerReflection_kinetic_subtop {n : ℕ} (hn : 1 ≤ n) :
    (kineticEquiv (integerReflection n)).coeff (n-1) =
      ∑ i ∈ range (n+1), ((n.choose i : KCoeff)*(-1)^(n-i))*
        (headA i*subHeadB (n-i)+subHeadB i*headA (n-i)) := by
  rw [kineticEquiv_integerReflection, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi : i ≤ n := by simp at hi; omega
  rw [show ((n.choose i : Polynomial KCoeff)*(-1)^(n-i)) =
    Polynomial.C ((n.choose i : KCoeff)*(-1)^(n-i)) by simp, Polynomial.coeff_C_mul]
  congr 1
  have h := coeff_mul_subTop (integerJet_kinetic_head i).1 (integerJet_kinetic_head (n-i)).1
    (by omega)
  rw [show i + (n - i) - 1 = n - 1 by omega] at h
  rw [h, (integerJet_kinetic_head i).2, (integerJet_kinetic_head (n-i)).2, integerJet_subTop,
    integerJet_subTop]

/-! ## Closed forms -/

/-- Alternating binomial moments of order below `n` vanish. -/
theorem alt_moment_zero {n j : ℕ} (h : j < n) :
    ∑ i ∈ range (n+1), ((n.choose i : KCoeff)*(-1)^(n-i))*(i:KCoeff)^j = 0 := by
  have := GaloisForLFunctions.HTGeometry.alternating_binomial_sum_pow_eq_zero (R := KCoeff) h
  rw [← this]
  refine Finset.sum_congr rfl (fun i _ => by ring)

theorem headA_closed (i : ℕ) : headA i = 2*12^i*kineticYC - (if i = 0 then 3 else 0) := by
  cases i <;> simp [headA]

/-- The jet quadratic `q(i) = -8 i y² + (4i²+6i+12) y`. -/
def jetQ (i : ℕ) : KCoeff := -8*(i:KCoeff)*kineticYC^2+(4*(i:KCoeff)^2+6*(i:KCoeff)+12)*kineticYC

theorem subHeadB_closed (i : ℕ) :
    subHeadB i = if i = 0 then 0 else kineticU*12^(i-1)*(jetQ i - (if i = 1 then 15 else 0)) := by
  unfold subHeadB headB jetQ
  split_ifs <;> ring

/-- **Leading reflected coefficient.**  `[J^n] R_n = -12^{n+1} y` for every even `n ≥ 2`. -/
theorem integerReflection_kinetic_top_even {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    (kineticEquiv (integerReflection n)).coeff n = -12^(n+1)*kineticYC := by
  rw [integerReflection_kinetic_top]
  have hterm : ∀ i ∈ range (n+1), ((n.choose i : KCoeff)*(-1)^(n-i))*(headA i*headA (n-i)) =
      ((n.choose i : KCoeff)*(-1)^(n-i))*(4*12^n*kineticYC^2) -
        (if i = n then 6*12^n*kineticYC else 0) -
        (if i = 0 then 6*12^n*kineticYC else 0) := by
    intro i hi
    have hi : i ≤ n := by simp at hi; omega
    rw [headA_closed, headA_closed]
    by_cases h0 : i = 0
    · subst h0
      simp [show n ≠ 0 by omega, show (0:ℕ) ≠ n by omega, he.neg_one_pow]
      ring
    · by_cases hn' : i = n
      · subst hn'
        simp [h0]
        ring
      · have h1 : n - i ≠ 0 := by omega
        simp only [h0, hn', h1, if_false, sub_zero]
        rw [show (12:KCoeff)^n = 12^i*12^(n-i) by rw [← pow_add]; congr 1; omega]
        ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', ← Finset.sum_mul]
  have h0 := alt_moment_zero (n := n) (j := 0) (by omega)
  simp only [pow_zero, mul_one] at h0
  simp [h0, show n ∈ range (n+1) by simp]
  ring

private theorem subtop_term {n i : ℕ} (hn : 2 ≤ n) (hi : i ≤ n) :
    subHeadB i*headA (n-i) =
      2*kineticU*12^(n-1)*kineticYC*jetQ i - (if i = 1 then 30*kineticU*12^(n-1)*kineticYC else 0) -
        (if i = 0 then 24*kineticU*12^(n-1)*kineticYC^2 else 0) -
        (if i = n then 3*kineticU*12^(n-1)*jetQ n else 0) := by
  rw [subHeadB_closed, headA_closed]
  by_cases h0 : i = 0
  · subst h0
    simp [show (0:ℕ) ≠ 1 by omega, show (0:ℕ) ≠ n by omega, show n ≠ 0 by omega, jetQ]
    ring
  · by_cases hn' : i = n
    · subst hn'
      simp [h0, show i ≠ 1 by omega]
      ring
    · by_cases h1 : i = 1
      · subst h1
        simp [show n - 1 ≠ 0 by omega, show (1:ℕ) ≠ n by omega]
        ring
      · have h2 : n - i ≠ 0 := by omega
        simp only [h0, hn', h1, h2, if_false, sub_zero]
        rw [show (12:KCoeff)^(n-1) = 12^(i-1)*12^(n-i) by rw [← pow_add]; congr 1; omega]
        ring

private theorem jetQ_moment {n : ℕ} (hn : 3 ≤ n) :
    ∑ i ∈ range (n+1), ((n.choose i : KCoeff)*(-1)^(n-i))*jetQ i = 0 := by
  have m0 := alt_moment_zero (n := n) (j := 0) (by omega)
  have m1 := alt_moment_zero (n := n) (j := 1) (by omega)
  have m2 := alt_moment_zero (n := n) (j := 2) (by omega)
  have e : ∀ i ∈ range (n+1), ((n.choose i : KCoeff)*(-1)^(n-i))*jetQ i =
      (-8*kineticYC^2+6*kineticYC)*(((n.choose i : KCoeff)*(-1)^(n-i))*(i:KCoeff)^1) +
      4*kineticYC*(((n.choose i : KCoeff)*(-1)^(n-i))*(i:KCoeff)^2) +
      12*kineticYC*(((n.choose i : KCoeff)*(-1)^(n-i))*(i:KCoeff)^0) := by
    intro i _; unfold jetQ; ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, m0, m1, m2]
  ring

/-- **Subleading reflected coefficient** for every even `n ≥ 4`:
`[J^{n-1}] R_n = u·12^{n-1}(48(n-1)y² - 24(n²-n+3)y)`. -/
theorem integerReflection_kinetic_subtop_even {n : ℕ} (hn : 4 ≤ n) (he : Even n) :
    (kineticEquiv (integerReflection n)).coeff (n-1) =
      kineticU*12^(n-1)*(48*((n:KCoeff)-1)*kineticYC^2-24*((n:KCoeff)^2-n+3)*kineticYC) := by
  rw [integerReflection_kinetic_subtop (by omega)]
  have hsym : ∑ i ∈ range (n+1), ((n.choose i : KCoeff)*(-1)^(n-i))*(headA i*subHeadB (n-i)) =
      ∑ i ∈ range (n+1), ((n.choose i : KCoeff)*(-1)^(n-i))*(subHeadB i*headA (n-i)) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi : i ≤ n := by simp at hi; omega
    have hs : (-1:KCoeff)^i = (-1)^(n-i) := by
      have h1 : (-1:KCoeff)^(n-i) * (-1)^i = 1 := by
        rw [← pow_add, Nat.sub_add_cancel hi, he.neg_one_pow]
      have h2 : (-1:KCoeff)^i * (-1)^i = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
      calc (-1:KCoeff)^i = (-1)^i * ((-1)^(n-i) * (-1)^i) := by rw [h1, mul_one]
        _ = (-1)^(n-i) * ((-1)^i*(-1)^i) := by ring
        _ = (-1)^(n-i) := by rw [h2, mul_one]
    rw [show n + 1 - 1 - i = n - i by omega, show n - (n - i) = i by omega, Nat.choose_symm hi, hs]
    ring
  have hsplit : ∀ i ∈ range (n+1), ((n.choose i : KCoeff)*(-1)^(n-i))*
      (headA i*subHeadB (n-i)+subHeadB i*headA (n-i)) =
      ((n.choose i : KCoeff)*(-1)^(n-i))*(headA i*subHeadB (n-i)) +
        ((n.choose i : KCoeff)*(-1)^(n-i))*(subHeadB i*headA (n-i)) := fun i _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hsym, ← two_mul]
  have hterm : ∀ i ∈ range (n+1), ((n.choose i : KCoeff)*(-1)^(n-i))*(subHeadB i*headA (n-i)) =
      (2*kineticU*12^(n-1)*kineticYC)*(((n.choose i : KCoeff)*(-1)^(n-i))*jetQ i) -
        (if i = 1 then ((n.choose i : KCoeff)*(-1)^(n-i))*(30*kineticU*12^(n-1)*kineticYC) else 0) -
        (if i = 0 then ((n.choose i : KCoeff)*(-1)^(n-i))*(24*kineticU*12^(n-1)*kineticYC^2) else 0) -
        (if i = n then ((n.choose i : KCoeff)*(-1)^(n-i))*(3*kineticU*12^(n-1)*jetQ n) else 0) := by
    intro i hi
    have hi : i ≤ n := by simp at hi; omega
    rw [subtop_term (by omega) hi]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, jetQ_moment (by omega),
    Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  have hodd : (-1:KCoeff)^(n-1) = -1 := by
    rw [show n - 1 = 2*(n/2 - 1) + 1 by obtain ⟨k, hk⟩ := he; omega, pow_succ, pow_mul]; simp
  simp [show (1:ℕ) < n + 1 by omega, he.neg_one_pow, hodd, jetQ]
  ring

/-- `[J] R_2 = u(960y² - 1440y)`: the exceptional first moment. -/
theorem integerReflection_two_kinetic_subtop :
    (kineticEquiv (integerReflection 2)).coeff 1 = kineticU*(960*kineticYC^2-1440*kineticYC) := by
  rw [show (1:ℕ) = 2 - 1 by rfl, integerReflection_kinetic_subtop (by norm_num)]
  simp [Finset.sum_range_succ, headA, subHeadB, headB]
  ring

end
end HTGeometry.ThetaRatioSource

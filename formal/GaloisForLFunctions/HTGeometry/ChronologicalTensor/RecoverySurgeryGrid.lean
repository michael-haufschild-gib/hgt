import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Tactic

/-!
# A polynomial cut preserving every lower Chebyshev grid

The degree `n+2` perturbation stays strictly below its cutoff on every
lower-degree Chebyshev grid, while exceeding absolute value one at its
selected degree-`n+2` node. Rational-angle separation and the finite cosine
expansion of the Lagrange cardinal polynomial give uniform estimates.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Real Polynomial

theorem recoveryGrid_cos_chord (n : ℕ) (hn : 0 < n) :
    Real.cos (Real.pi / n) ≤ 1 - 2 / (n : ℝ)^(2 : ℕ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha0 : 0 ≤ Real.pi / n := by positivity
  have ha1 : Real.pi / n ≤ Real.pi := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith [Real.pi_pos]
  have h := Real.cos_le_one_sub_mul_cos_sq
    (x := Real.pi / n) (by simpa only [abs_of_nonneg ha0] using ha1)
  convert h using 1
  field_simp

theorem recoveryGrid_abs_cos_remainder (a n : ℕ) (hn : 0 < n) :
    |Real.cos ((a : ℝ)*Real.pi/n)| =
      |Real.cos (((a % n : ℕ) : ℝ)*Real.pi/n)| := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hh : ((a % n : ℕ) : ℝ) + (n : ℝ)*((a/n : ℕ) : ℝ) = a := by
    exact_mod_cast Nat.mod_add_div a n
  have he : (a : ℝ)*Real.pi/n =
      ((a % n : ℕ) : ℝ)*Real.pi/n + ((a/n : ℕ) : ℝ)*Real.pi := by
    rw [← hh]
    field_simp
  rw [he,Real.cos_add_nat_mul_pi,abs_mul,abs_neg_one_pow,one_mul]

theorem recoveryGrid_abs_cos_interior (r n : ℕ) (hr : 0 < r) (hrn : r < n) :
    |Real.cos ((r : ℝ)*Real.pi/n)| ≤ 1 - 2/(n : ℝ)^(2 : ℕ) := by
  have hn : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrle : (r : ℝ)+1 ≤ n := by exact_mod_cast hrn
  have hx0 : 0 ≤ (r : ℝ)*Real.pi/n := by positivity
  have hx1 : (r : ℝ)*Real.pi/n ≤ Real.pi := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith [Real.pi_pos]
  have ha0 : 0 ≤ Real.pi/n := by positivity
  have hax : Real.pi/n ≤ (r : ℝ)*Real.pi/n := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hn0)
    nlinarith [Real.pi_pos]
  have hay : Real.pi/n ≤ Real.pi - (r : ℝ)*Real.pi/n := by
    apply (le_sub_iff_add_le).mpr
    rw [← add_div]
    apply (div_le_iff₀ hn0).mpr
    nlinarith [Real.pi_pos]
  have hp := Real.cos_le_cos_of_nonneg_of_le_pi ha0 hx1 hax
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi ha0
    (show Real.pi - (r : ℝ)*Real.pi/n ≤ Real.pi by linarith) hay
  rw [Real.cos_pi_sub] at hm
  have h := recoveryGrid_cos_chord n hn
  rw [abs_le]
  constructor <;> linarith

theorem recoveryGrid_abs_cos_gap (a n : ℕ) :
    |Real.cos ((a : ℝ)*Real.pi/n)| = 1 ∨
      |Real.cos ((a : ℝ)*Real.pi/n)| ≤ 1 - 2/(n : ℝ)^(2 : ℕ) := by
  by_cases hn : n=0
  · subst n
    simp
  have hn0 : 0<n := Nat.pos_of_ne_zero hn
  rw [recoveryGrid_abs_cos_remainder a n hn0]
  by_cases hr : a % n=0
  · left
    simp [hr]
  · right
    exact recoveryGrid_abs_cos_interior (a%n) n (Nat.pos_of_ne_zero hr) (Nat.mod_lt a hn0)

theorem recoveryGrid_eval_gap (m n i : ℕ) (hn : 0 < n) (hnm : n ≤ m) :
    |(Chebyshev.T ℝ (m : ℤ)).eval (Chebyshev.node n i)| = 1 ∨
      |(Chebyshev.T ℝ (m : ℤ)).eval (Chebyshev.node n i)| ≤
        1 - 2 / (m : ℝ)^(2 : ℕ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have he : (Chebyshev.T ℝ (m : ℤ)).eval (Chebyshev.node n i) =
      Real.cos (((m*i : ℕ) : ℝ)*Real.pi/n) := by
    rw [Chebyshev.node, Chebyshev.T_real_cos]
    congr 1
    push_cast
    ring
  rw [he]
  rcases recoveryGrid_abs_cos_gap (m*i) n with h | h
  · exact Or.inl h
  · right
    have hd : 2/(m : ℝ)^(2 : ℕ) ≤ 2/(n : ℝ)^(2 : ℕ) :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hn0)
        (by nlinarith)
    linarith

theorem recoveryGrid_distinguished_node_absent (m n i : ℕ)
    (hn : 0 < n) (hnm : n < m) (hi : i ≤ n) :
    Chebyshev.node n i ≠ Chebyshev.node m 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_trans hn hnm)
  have hin : (i : ℝ) ≤ n := by exact_mod_cast hi
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (lt_trans hn hnm)
  intro he
  simp only [Chebyshev.node, Nat.cast_one, one_mul] at he
  have ha : (i : ℝ)*Real.pi/n = Real.pi/m := by
    apply Real.injOn_cos _ _ he
    · constructor
      · positivity
      · apply (div_le_iff₀ hn0).mpr
        nlinarith [Real.pi_pos]
    · constructor
      · positivity
      · apply (div_le_iff₀ hm0).mpr
        nlinarith [Real.pi_pos]
  have heq : i*m=n := by
    have hreal : (i : ℝ)*m=n := by
      field_simp at ha
      nlinarith [Real.pi_pos]
    exact_mod_cast hreal
  have hi0 : 0 < i := by
    by_contra h
    have : i=0 := by omega
    subst i
    simp at heq
    omega
  have : m ≤ i*m := by
    calc
      m = 1*m := by simp
      _ ≤ i*m := Nat.mul_le_mul_right m hi0
  omega

theorem recoveryGrid_shared_or_gap (m n i : ℕ)
    (hn : 0 < n) (hnm : n < m) (hi : i ≤ n) :
    (∃ j ≤ m, j ≠ 1 ∧ Chebyshev.node n i = Chebyshev.node m j) ∨
      |(Chebyshev.T ℝ (m : ℤ)).eval (Chebyshev.node n i)| ≤
        1 - 2/(m : ℝ)^(2 : ℕ) := by
  rcases recoveryGrid_eval_gap m n i hn (le_of_lt hnm) with he | hg
  · left
    obtain ⟨j, hj, heq⟩ :=
      (Chebyshev.abs_eval_T_real_eq_one_iff (Nat.ne_of_gt (lt_trans hn hnm))
        (Chebyshev.node n i)).mp he
    refine ⟨j, hj, ?_, heq⟩
    intro hj1
    subst j
    exact recoveryGrid_distinguished_node_absent m n i hn hnm hi heq
  · exact Or.inr hg

def recoveryCardinal (n : ℕ) : ℝ[X] :=
  Lagrange.basis (Finset.range (n+3)) (Chebyshev.node (n+2)) 1

def recoverySurgeryAlpha (n : ℕ) : ℝ :=
  -2*(n+2 : ℝ)^(2 : ℕ) / (2*(n+2 : ℝ)-Chebyshev.node (n+2) 1)

def recoverySurgeryEpsilon (n : ℕ) : ℝ := 1/(16*(n+2 : ℝ)^(3 : ℕ))

def recoverySurgeryHeight (n : ℕ) : ℝ := 1-recoverySurgeryEpsilon n/2

def recoverySurgeryPolynomial (n : ℕ) : ℝ[X] :=
  C (1-recoverySurgeryEpsilon n)*Chebyshev.T ℝ ((n+2 : ℕ) : ℤ) +
    C (recoverySurgeryEpsilon n*recoverySurgeryAlpha n)*recoveryCardinal n

theorem recoveryCardinal_self (n : ℕ) :
    (recoveryCardinal n).eval (Chebyshev.node (n+2) 1) = 1 := by
  apply Lagrange.eval_basis_self
  · exact (Chebyshev.strictAntiOn_node (n+2)).injOn
  · simp only [Finset.mem_range]
    omega

theorem recoveryCardinal_node (n j : ℕ) (hj : j ≤ n+2) (hj1 : j ≠ 1) :
    (recoveryCardinal n).eval (Chebyshev.node (n+2) j) = 0 := by
  exact Lagrange.eval_basis_of_ne hj1.symm (Finset.mem_range.mpr (by omega))

theorem recoveryCardinal_degree (n : ℕ) :
    (recoveryCardinal n).natDegree = n+2 := by
  rw [recoveryCardinal, Lagrange.natDegree_basis
    (Chebyshev.strictAntiOn_node (n+2)).injOn
    (show 1 ∈ Finset.range (n+3) by simp only [Finset.mem_range]; omega), Finset.card_range]
  omega

theorem recoverySurgeryAlpha_lt_neg_one (n : ℕ) :
    recoverySurgeryAlpha n < -1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hx := Chebyshev.node_mem_Icc (n := n+2) (i := 1)
  have hd : 0 < 2*(n+2 : ℝ)-Chebyshev.node (n+2) 1 := by linarith [hx.2]
  rw [recoverySurgeryAlpha, div_lt_iff₀ hd]
  nlinarith [hx.1]

theorem recoverySurgeryAlpha_abs_le (n : ℕ) :
    |recoverySurgeryAlpha n| ≤ 2*(n+2 : ℝ) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hx := Chebyshev.node_mem_Icc (n := n+2) (i := 1)
  have hd : 0 < 2*(n+2 : ℝ)-Chebyshev.node (n+2) 1 := by linarith [hx.2]
  have ha := recoverySurgeryAlpha_lt_neg_one n
  rw [abs_of_neg (show recoverySurgeryAlpha n < 0 by linarith), recoverySurgeryAlpha,
    ← neg_div, neg_mul, neg_neg, div_le_iff₀ hd]
  nlinarith [mul_nonneg (show 0 ≤ (n+2 : ℝ) by positivity)
    (show 0 ≤ (n+2 : ℝ)-Chebyshev.node (n+2) 1 by linarith [hx.2])]

theorem recoverySurgeryEpsilon_pos (n : ℕ) : 0 < recoverySurgeryEpsilon n := by
  unfold recoverySurgeryEpsilon
  positivity

theorem recoverySurgeryEpsilon_lt_one (n : ℕ) : recoverySurgeryEpsilon n < 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold recoverySurgeryEpsilon
  apply (div_lt_one (by positivity)).mpr
  nlinarith [sq_nonneg (n : ℝ), pow_nonneg hn 3]

theorem recoverySurgeryPolynomial_distinguished (n : ℕ) :
    (recoverySurgeryPolynomial n).eval (Chebyshev.node (n+2) 1) < -1 := by
  have he : (Chebyshev.T ℝ ((n+2 : ℕ) : ℤ)).eval (Chebyshev.node (n+2) 1) = -1 := by
    simpa using Chebyshev.eval_T_real_node
      (show 1 ∈ Finset.Iic (n+2) by simp only [Finset.mem_Iic]; omega)
  simp only [recoverySurgeryPolynomial, eval_add, eval_mul, eval_C,
    recoveryCardinal_self, he, mul_one]
  nlinarith [recoverySurgeryAlpha_lt_neg_one n, recoverySurgeryEpsilon_pos n]

theorem recoverySurgeryPolynomial_shared (n j : ℕ) (hj : j ≤ n+2) (hj1 : j ≠ 1) :
    |(recoverySurgeryPolynomial n).eval (Chebyshev.node (n+2) j)| =
      1-recoverySurgeryEpsilon n := by
  simp only [recoverySurgeryPolynomial, eval_add, eval_mul, eval_C,
    recoveryCardinal_node n j hj hj1, mul_zero, add_zero,
    Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr hj), abs_mul, abs_neg_one_pow,
    mul_one, abs_of_pos (sub_pos.mpr (recoverySurgeryEpsilon_lt_one n))]

theorem recoverySurgeryPolynomial_degree (n : ℕ) :
    (recoverySurgeryPolynomial n).natDegree ≤ n+2 := by
  apply natDegree_add_le_of_degree_le
  · have hd : (Chebyshev.T ℝ ((n+2 : ℕ) : ℤ)).natDegree = n+2 := by
      simpa only [Int.natAbs_natCast] using Chebyshev.natDegree_T ℝ ((n+2 : ℕ) : ℤ)
    exact (natDegree_C_mul_le _ _).trans (le_of_eq hd)
  · exact (natDegree_C_mul_le _ _).trans (le_of_eq (recoveryCardinal_degree n))

def recoveryCosineKernel (m : ℕ) (t : ℝ) : ℝ :=
  (∑ k ∈ Finset.range m, Real.cos (k*t)) + (Real.cos (m*t)-1)/2

theorem recoveryCosineKernel_step (m : ℕ) (t : ℝ) :
    recoveryCosineKernel (m+1) t = recoveryCosineKernel m t +
      (Real.cos (m*t)+Real.cos ((m+1 : ℕ)*t))/2 := by
  simp only [recoveryCosineKernel, Finset.sum_range_succ]
  ring

theorem recoveryCosineKernel_sine (m : ℕ) (t : ℝ) :
    2*Real.sin (t/2)*recoveryCosineKernel m t =
      Real.sin (m*t)*Real.cos (t/2) := by
  have hstep (a : ℝ) :
      Real.sin (t/2)*(Real.cos a+Real.cos (a+t)) =
        (Real.sin (a+t)-Real.sin a)*Real.cos (t/2) := by
    rw [Real.cos_add_cos, Real.sin_sub_sin]
    have h1 : (a-(a+t))/2 = -(t/2) := by ring
    have h2 : (a+t-a)/2 = t/2 := by ring
    have h3 : (a+(a+t))/2 = (a+t+a)/2 := by ring
    rw [h1, h2, h3, Real.cos_neg]
    ring
  induction m with
  | zero => simp [recoveryCosineKernel]
  | succ m ih =>
    rw [recoveryCosineKernel_step]
    push_cast
    have hs := hstep ((m : ℝ)*t)
    have he : ((m : ℝ)+1)*t = m*t+t := by ring
    rw [he]
    nlinarith

theorem recoveryCosineKernel_zero (m : ℕ) : recoveryCosineKernel m 0 = m := by
  simp [recoveryCosineKernel]

theorem recoveryCosineKernel_neg (m : ℕ) (t : ℝ) :
    recoveryCosineKernel m (-t) = recoveryCosineKernel m t := by
  simp [recoveryCosineKernel]

theorem recoveryCosineKernel_grid_zero (m q : ℕ) (hm : 0 < m)
    (hq : 0 < q) (hqm : q < 2*m) :
    recoveryCosineKernel m ((q : ℝ)*Real.pi/m) = 0 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqmR : (q : ℝ) < 2*m := by exact_mod_cast hqm
  have ha0 : 0 < ((q : ℝ)*Real.pi/m)/2 := by positivity
  have haπ : ((q : ℝ)*Real.pi/m)/2 < Real.pi := by
    rw [div_lt_iff₀ (show (0 : ℝ)<2 by positivity), div_lt_iff₀ hm0]
    nlinarith [Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi ha0 haπ
  have h := recoveryCosineKernel_sine m ((q : ℝ)*Real.pi/m)
  have he : (m : ℝ)*((q : ℝ)*Real.pi/m) = q*Real.pi := by field_simp
  rw [he, Real.sin_nat_mul_pi, zero_mul] at h
  nlinarith

theorem recoveryCosineKernel_pair (m : ℕ) (a t : ℝ) :
    recoveryCosineKernel m (t-a)+recoveryCosineKernel m (t+a) =
      2*(∑ k ∈ Finset.range m, Real.cos (k*a)*Real.cos (k*t)) +
        Real.cos (m*a)*Real.cos (m*t)-1 := by
  have he (r : ℝ) : Real.cos (r*(t-a))+Real.cos (r*(t+a)) =
      2*Real.cos (r*a)*Real.cos (r*t) := by
    rw [mul_sub, mul_add, Real.cos_sub, Real.cos_add]
    ring
  have hs : (∑ k ∈ Finset.range m, Real.cos (k*(t-a))) +
      (∑ k ∈ Finset.range m, Real.cos (k*(t+a))) =
        2*(∑ k ∈ Finset.range m, Real.cos (k*a)*Real.cos (k*t)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    nlinarith [he k]
  unfold recoveryCosineKernel
  nlinarith [he m]

def recoveryCosinePolynomial (n : ℕ) (a : ℝ) : ℝ[X] :=
  C (1/(n+2 : ℝ)) * (1 + C 2 *
    (∑ k ∈ Finset.range (n+1), C (Real.cos (((k+1 : ℕ) : ℝ)*a)) *
      Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)) +
    C (Real.cos (((n+2 : ℕ) : ℝ)*a)) * Chebyshev.T ℝ ((n+2 : ℕ) : ℤ))

theorem recoveryCosinePolynomial_degree (n : ℕ) (a : ℝ) :
    (recoveryCosinePolynomial n a).natDegree ≤ n+2 := by
  unfold recoveryCosinePolynomial
  refine (natDegree_C_mul_le _ _).trans ?_
  apply natDegree_add_le_of_degree_le
  · apply natDegree_add_le_of_degree_le
    · simp only [natDegree_one]; omega
    · refine (natDegree_C_mul_le _ _).trans ?_
      apply natDegree_sum_le_of_forall_le
      intro k hk
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [Chebyshev.natDegree_T, Int.natAbs_natCast]
      simp only [Finset.mem_range] at hk
      omega
  · refine (natDegree_C_mul_le _ _).trans ?_
    rw [Chebyshev.natDegree_T, Int.natAbs_natCast]

theorem recoveryCosinePolynomial_bound (n : ℕ) (a x : ℝ) (hx : |x| ≤ 1) :
    |(recoveryCosinePolynomial n a).eval x| ≤ 2 := by
  have ht (k : ℕ) :
      |Real.cos ((k : ℝ)*a) * (Chebyshev.T ℝ (k : ℤ)).eval x| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_cos_le_one _) (Chebyshev.abs_eval_T_real_le_one _ hx)
      (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
  have hs : |∑ k ∈ Finset.range (n+1), Real.cos (((k+1 : ℕ) : ℝ)*a) *
      (Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)).eval x| ≤ (n+1 : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (n+1),
          |Real.cos (((k+1 : ℕ) : ℝ)*a) * (Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)).eval x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range (n+1), (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => ht (k+1))
      _ = n+1 := by simp
  have hn : (0 : ℝ) < n+2 := by positivity
  have hε : 0 < 1/(n+2 : ℝ) := by positivity
  simp only [recoveryCosinePolynomial, eval_mul, eval_add, eval_C, eval_one,
    eval_finsetSum, abs_mul, abs_of_pos hε]
  have hb : |1+2*(∑ k ∈ Finset.range (n+1), Real.cos (((k+1 : ℕ) : ℝ)*a) *
      (Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)).eval x) +
        Real.cos (((n+2 : ℕ) : ℝ)*a)*(Chebyshev.T ℝ ((n+2 : ℕ) : ℤ)).eval x| ≤
      2*(n+2 : ℝ) := by
    calc
      _ ≤ |1+2*(∑ k ∈ Finset.range (n+1), Real.cos (((k+1 : ℕ) : ℝ)*a) *
          (Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)).eval x)| +
            |Real.cos (((n+2 : ℕ) : ℝ)*a)*(Chebyshev.T ℝ ((n+2 : ℕ) : ℤ)).eval x| :=
        abs_add_le _ _
      _ ≤ 1+2*(n+1 : ℝ)+1 := by
        have h := abs_add_le (1 : ℝ) (2*(∑ k ∈ Finset.range (n+1),
          Real.cos (((k+1 : ℕ) : ℝ)*a)*(Chebyshev.T ℝ ((k+1 : ℕ) : ℤ)).eval x))
        rw [abs_one, abs_mul, abs_of_pos (show (0 : ℝ)<2 by positivity)] at h
        linarith [ht (n+2)]
      _ = _ := by ring
  calc
    _ ≤ (1/(n+2 : ℝ))*(2*(n+2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (le_of_lt hε)
    _ = 2 := by field_simp

theorem recoveryCosinePolynomial_eval_cos (n : ℕ) (a t : ℝ) :
    (recoveryCosinePolynomial n a).eval (Real.cos t) =
      (recoveryCosineKernel (n+2) (t-a)+recoveryCosineKernel (n+2) (t+a))/(n+2 : ℝ) := by
  have hs : (∑ k ∈ Finset.range (n+2), Real.cos (k*a)*Real.cos (k*t)) =
      1 + ∑ k ∈ Finset.range (n+1),
        Real.cos (((k+1 : ℕ) : ℝ)*a)*Real.cos (((k+1 : ℕ) : ℝ)*t) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, one_mul]
    ring
  rw [recoveryCosineKernel_pair, hs]
  simp only [recoveryCosinePolynomial, eval_mul, eval_add, eval_C, eval_one,
    eval_finsetSum, Chebyshev.T_real_cos, Int.cast_natCast]
  ring

theorem recoveryCosinePolynomial_node (n j : ℕ) (hj : j ≤ n+2) :
    (recoveryCosinePolynomial n (Real.pi/(n+2 : ℝ))).eval (Chebyshev.node (n+2) j) =
      if j=1 then 1 else 0 := by
  simp only [Chebyshev.node, Nat.cast_add, Nat.cast_ofNat]
  rw [recoveryCosinePolynomial_eval_cos]
  have hb (q : ℕ) (hq : 0 < q) (hqm : q < 2*(n+2)) :
      recoveryCosineKernel (n+2) ((q : ℝ)*Real.pi/(n+2 : ℝ)) = 0 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      recoveryCosineKernel_grid_zero (n+2) q (by omega) hq hqm
  by_cases hj1 : j=1
  · subst j
    simp only [Nat.cast_one, one_mul, sub_self, recoveryCosineKernel_zero, ite_true]
    have he : Real.pi/(n+2 : ℝ)+Real.pi/(n+2 : ℝ) =
        (2 : ℝ)*Real.pi/(n+2 : ℝ) := by ring
    have h2 := hb 2 (by omega) (by omega)
    simp only [Nat.cast_ofNat] at h2
    rw [he, h2]
    push_cast
    field_simp
    simp
  rw [if_neg hj1]
  by_cases hj0 : j=0
  · subst j
    simp only [Nat.cast_zero, zero_mul, zero_div, zero_sub, zero_add,
      recoveryCosineKernel_neg]
    have h := hb 1 (by omega) (by omega)
    simp only [Nat.cast_one, one_mul] at h
    rw [h]
    simp
  have hjge : 1 ≤ j := by omega
  have he1 : (j : ℝ)*Real.pi/(n+2 : ℝ)-Real.pi/(n+2 : ℝ) =
      ((j-1 : ℕ) : ℝ)*Real.pi/(n+2 : ℝ) := by
    rw [Nat.cast_sub hjge, Nat.cast_one]
    ring
  have he2 : (j : ℝ)*Real.pi/(n+2 : ℝ)+Real.pi/(n+2 : ℝ) =
      ((j+1 : ℕ) : ℝ)*Real.pi/(n+2 : ℝ) := by
    push_cast
    ring
  rw [he1, he2, hb (j-1) (by omega) (by omega), hb (j+1) (by omega) (by omega)]
  simp

theorem recoveryCardinal_cosine_expansion (n : ℕ) :
    recoveryCardinal n = recoveryCosinePolynomial n (Real.pi/(n+2 : ℝ)) := by
  apply eq_of_degrees_lt_of_eval_index_eq (Finset.range (n+3))
    (Chebyshev.strictAntiOn_node (n+2)).injOn
  · rw [Finset.card_range]
    apply (degree_le_of_natDegree_le (le_of_eq (recoveryCardinal_degree n))).trans_lt
    exact_mod_cast (show n+2<n+3 by omega)
  · rw [Finset.card_range]
    apply (degree_le_of_natDegree_le (recoveryCosinePolynomial_degree n _)).trans_lt
    exact_mod_cast (show n+2<n+3 by omega)
  · intro j hj
    have hjle : j ≤ n+2 := by simp only [Finset.mem_range] at hj; omega
    rw [recoveryCosinePolynomial_node n j hjle]
    by_cases hj1 : j=1
    · subst j
      rw [if_pos rfl, recoveryCardinal_self]
    · rw [if_neg hj1, recoveryCardinal_node n j hjle hj1]

theorem recoveryCardinal_bound (n : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    |(recoveryCardinal n).eval x| ≤ 2 := by
  rw [recoveryCardinal_cosine_expansion]
  exact recoveryCosinePolynomial_bound n _ x hx

theorem recoverySurgeryPolynomial_difference (n : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    |(recoverySurgeryPolynomial n).eval x -
      (Chebyshev.T ℝ ((n+2 : ℕ) : ℤ)).eval x| ≤
        recoverySurgeryEpsilon n*(4*(n+2 : ℝ)+1) := by
  have he : (recoverySurgeryPolynomial n).eval x -
      (Chebyshev.T ℝ ((n+2 : ℕ) : ℤ)).eval x = recoverySurgeryEpsilon n *
        (recoverySurgeryAlpha n*(recoveryCardinal n).eval x -
          (Chebyshev.T ℝ ((n+2 : ℕ) : ℤ)).eval x) := by
    simp only [recoverySurgeryPolynomial, eval_add, eval_mul, eval_C]
    ring
  rw [he, abs_mul, abs_of_pos (recoverySurgeryEpsilon_pos n)]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (recoverySurgeryEpsilon_pos n))
  calc
    _ ≤ |recoverySurgeryAlpha n*(recoveryCardinal n).eval x| +
        |(Chebyshev.T ℝ ((n+2 : ℕ) : ℤ)).eval x| := abs_sub _ _
    _ ≤ 2*(n+2 : ℝ)*2+1 := by
      rw [abs_mul]
      exact add_le_add
        (mul_le_mul (recoverySurgeryAlpha_abs_le n) (recoveryCardinal_bound n x hx)
          (abs_nonneg _) (by positivity)) (Chebyshev.abs_eval_T_real_le_one _ hx)
    _ = _ := by ring

theorem recoverySurgeryPolynomial_bound (n : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    |(recoverySurgeryPolynomial n).eval x| ≤
      1+recoverySurgeryEpsilon n*(4*(n+2 : ℝ)+1) := by
  have he := abs_add_le
    ((recoverySurgeryPolynomial n).eval x-(Chebyshev.T ℝ ((n+2 : ℕ) : ℤ)).eval x)
    ((Chebyshev.T ℝ ((n+2 : ℕ) : ℤ)).eval x)
  rw [sub_add_cancel] at he
  linarith [recoverySurgeryPolynomial_difference n x hx,
    Chebyshev.abs_eval_T_real_le_one ((n+2 : ℕ) : ℤ) hx]

theorem recoverySurgery_margin (n : ℕ) :
    recoverySurgeryEpsilon n*(4*(n+2 : ℝ)+1)+1-2/(n+2 : ℝ)^(2 : ℕ) <
      recoverySurgeryHeight n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have he : 2/(n+2 : ℝ)^(2 : ℕ) = recoverySurgeryEpsilon n*(32*(n+2 : ℝ)) := by
    unfold recoverySurgeryEpsilon
    field_simp
    ring
  have hp : 0 < recoverySurgeryEpsilon n*(32*(n+2 : ℝ)-(4*(n+2 : ℝ)+1)-1/2) :=
    mul_pos (recoverySurgeryEpsilon_pos n) (by linarith)
  rw [he, recoverySurgeryHeight]
  nlinarith

/-- The explicit polynomial cut protects every lower-degree alternation grid. -/
theorem recoverySurgery_lower_grid (n : ℕ) (l : Fin (n+1)) (i : Fin (l.val+2)) :
    |(recoverySurgeryPolynomial n).eval (Chebyshev.node (l.val+1) i.val)| <
      recoverySurgeryHeight n := by
  have hl : l.val+1 < n+2 := by have := l.isLt; omega
  have hi : i.val ≤ l.val+1 := by have := i.isLt; omega
  rcases recoveryGrid_shared_or_gap (n+2) (l.val+1) i.val (by omega) hl hi with hs | hg
  · obtain ⟨j, hj, hj1, he⟩ := hs
    rw [he, recoverySurgeryPolynomial_shared n j hj hj1, recoverySurgeryHeight]
    linarith [recoverySurgeryEpsilon_pos n]
  · have hx : |Chebyshev.node (l.val+1) i.val| ≤ 1 :=
      abs_le.mpr Chebyshev.node_mem_Icc
    have hd := recoverySurgeryPolynomial_difference n _ hx
    have ha := abs_add_le
      ((recoverySurgeryPolynomial n).eval (Chebyshev.node (l.val+1) i.val) -
        (Chebyshev.T ℝ ((n+2 : ℕ) : ℤ)).eval (Chebyshev.node (l.val+1) i.val))
      ((Chebyshev.T ℝ ((n+2 : ℕ) : ℤ)).eval (Chebyshev.node (l.val+1) i.val))
    rw [sub_add_cancel] at ha
    simp only [Nat.cast_add, Nat.cast_ofNat] at hg hd ha
    linarith [recoverySurgery_margin n]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor

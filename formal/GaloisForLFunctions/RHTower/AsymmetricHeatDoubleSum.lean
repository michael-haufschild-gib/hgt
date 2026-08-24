import GaloisForLFunctions.RHTower.HeatDoubleSum
import GaloisForLFunctions.RHTower.ZetaRealBound

/-!
# Asymmetric additive-heat double sums

The reflected bi-heat completion uses complementary Dirichlet orders, so one factor can lie below
the separate `L²` threshold `Re(s) = 1 / 2`.  Absolute convergence only needs both real parts to
be nonnegative and their sum to exceed one.  Splitting the lattice into its two triangular halves
exposes a shifted `p`-series in the smaller index and a Gaussian series in the difference.
-/

open Complex

namespace RHTower

/-- Parametrize the upper and strict lower triangular halves of `ℕ × ℕ`. -/
def upperLowerNatPairEquiv : (ℕ × ℕ) ⊕ (ℕ × ℕ) ≃ ℕ × ℕ where
  toFun
    | Sum.inl p => (p.1 + p.2, p.1)
    | Sum.inr p => (p.1, p.1 + p.2 + 1)
  invFun p :=
    if p.2 ≤ p.1 then Sum.inl (p.2, p.1 - p.2)
    else Sum.inr (p.1, p.2 - p.1 - 1)
  left_inv p := by
    rcases p with ⟨n, k⟩ | ⟨n, k⟩
    · simp
    · simp
      omega
  right_inv p := by
    rcases p with ⟨m, n⟩
    by_cases h : n ≤ m
    · simp [h]
    · simp [h]
      omega

/-- Shifted negative real powers are summable above exponent one. -/
theorem summable_nat_add_one_rpow_neg {c : ℝ} (hc : 1 < c) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-c) := by
  refine (GaloisForLFunctions.RHTower.summable_one_div_nat_add_one_rpow hc).congr fun n => ?_
  rw [Real.rpow_neg (by positivity)]
  simp only [one_div]

/-- Pair of independent Dirichlet orders against the additive Gaussian. -/
noncomputable def asymmetricHeatPairTerm (a b : ℂ) (x : ℝ) (p : ℕ × ℕ) : ℂ :=
  (((p.1 : ℝ) + 1 : ℝ) : ℂ) ^ (-a) * (((p.2 : ℝ) + 1 : ℝ) : ℂ) ^ (-b) *
    ((heatCoeff x ((p.1 : ℤ) - (p.2 : ℤ)) : ℝ) : ℂ)

theorem norm_asymmetricHeatPairTerm (a b : ℂ) (x : ℝ) (p : ℕ × ℕ) :
    ‖asymmetricHeatPairTerm a b x p‖ =
      ((p.1 : ℝ) + 1) ^ (-a.re) * ((p.2 : ℝ) + 1) ^ (-b.re) *
        heatCoeff x ((p.1 : ℤ) - (p.2 : ℤ)) := by
  rw [asymmetricHeatPairTerm, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < (p.1 : ℝ) + 1),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < (p.2 : ℝ) + 1),
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (heatCoeff_pos x _), Complex.neg_re,
    Complex.neg_re]

/-- Product majorant after triangular reindexing. -/
noncomputable def asymmetricHeatPairMajorant (a b : ℂ) (x : ℝ) :
    (ℕ × ℕ) ⊕ (ℕ × ℕ) → ℝ
  | Sum.inl p => ((p.1 : ℝ) + 1) ^ (-(a.re + b.re)) * heatCoeff x (p.2 : ℤ)
  | Sum.inr p => ((p.1 : ℝ) + 1) ^ (-(a.re + b.re)) * heatCoeff x (-((p.2 : ℤ) + 1))

theorem summable_asymmetricHeatPairMajorant {a b : ℂ} (hab : 1 < a.re + b.re)
    {x : ℝ} (hx : 0 < x) : Summable (asymmetricHeatPairMajorant a b x) := by
  apply Summable.sum
  · change Summable (fun p : ℕ × ℕ =>
      ((p.1 : ℝ) + 1) ^ (-(a.re + b.re)) * heatCoeff x (p.2 : ℤ))
    exact (summable_nat_add_one_rpow_neg hab).mul_of_nonneg
      ((summable_heatCoeff hx).comp_injective Int.ofNat_injective)
      (fun _ => Real.rpow_nonneg (by positivity) _) (fun _ => (heatCoeff_pos x _).le)
  · have hinj : Function.Injective (fun k : ℕ => -((k : ℤ) + 1)) := by
      intro m n h
      have h' : (m : ℤ) + 1 = (n : ℤ) + 1 := neg_injective h
      have h'' : (m : ℤ) = (n : ℤ) := add_right_cancel h'
      exact_mod_cast h''
    change Summable (fun p : ℕ × ℕ =>
      ((p.1 : ℝ) + 1) ^ (-(a.re + b.re)) * heatCoeff x (-((p.2 : ℤ) + 1)))
    exact (summable_nat_add_one_rpow_neg hab).mul_of_nonneg
      ((summable_heatCoeff hx).comp_injective hinj)
      (fun _ => Real.rpow_nonneg (by positivity) _) (fun _ => (heatCoeff_pos x _).le)

theorem norm_asymmetricHeatPairTerm_comp_equiv_le {a b : ℂ} (ha : 0 ≤ a.re)
    (hb : 0 ≤ b.re) (x : ℝ) (q : (ℕ × ℕ) ⊕ (ℕ × ℕ)) :
    ‖asymmetricHeatPairTerm a b x (upperLowerNatPairEquiv q)‖ ≤
      asymmetricHeatPairMajorant a b x q := by
  rcases q with ⟨n, k⟩ | ⟨n, k⟩
  · rw [norm_asymmetricHeatPairTerm]
    change (((n + k : ℕ) : ℝ) + 1) ^ (-a.re) * ((n : ℝ) + 1) ^ (-b.re) *
        heatCoeff x (((n + k : ℕ) : ℤ) - (n : ℤ)) ≤
      ((n : ℝ) + 1) ^ (-(a.re + b.re)) * heatCoeff x (k : ℤ)
    rw [show ((n + k : ℕ) : ℤ) - (n : ℤ) = (k : ℤ) by push_cast; ring]
    have hbase : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle : (n : ℝ) + 1 ≤ ((n + k : ℕ) : ℝ) + 1 := by
      have hnk : n + 1 ≤ n + k + 1 := by omega
      exact_mod_cast hnk
    have hpow : (((n + k : ℕ) : ℝ) + 1) ^ (-a.re) ≤ ((n : ℝ) + 1) ^ (-a.re) :=
      Real.rpow_le_rpow_of_nonpos hbase hle (by linarith)
    have hrpow : ((n : ℝ) + 1) ^ (-(a.re + b.re)) =
        ((n : ℝ) + 1) ^ (-a.re) * ((n : ℝ) + 1) ^ (-b.re) := by
      rw [← Real.rpow_add hbase]
      congr 1
      ring
    rw [hrpow]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) _))
      (heatCoeff_pos x _).le
  · rw [norm_asymmetricHeatPairTerm]
    change ((n : ℝ) + 1) ^ (-a.re) * (((n + k + 1 : ℕ) : ℝ) + 1) ^ (-b.re) *
        heatCoeff x ((n : ℤ) - ((n + k + 1 : ℕ) : ℤ)) ≤
      ((n : ℝ) + 1) ^ (-(a.re + b.re)) * heatCoeff x (-((k : ℤ) + 1))
    rw [show (n : ℤ) - ((n + k + 1 : ℕ) : ℤ) = -((k : ℤ) + 1) by push_cast; ring]
    have hbase : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle : (n : ℝ) + 1 ≤ ((n + k + 1 : ℕ) : ℝ) + 1 := by
      have hnk : n + 1 ≤ n + k + 1 + 1 := by omega
      exact_mod_cast hnk
    have hpow : (((n + k + 1 : ℕ) : ℝ) + 1) ^ (-b.re) ≤ ((n : ℝ) + 1) ^ (-b.re) :=
      Real.rpow_le_rpow_of_nonpos hbase hle (by linarith)
    have hrpow : ((n : ℝ) + 1) ^ (-(a.re + b.re)) =
        ((n : ℝ) + 1) ^ (-a.re) * ((n : ℝ) + 1) ^ (-b.re) := by
      rw [← Real.rpow_add hbase]
      congr 1
      ring
    rw [hrpow]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow
        (Real.rpow_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) _))
      (heatCoeff_pos x _).le

/-- Absolute convergence of the asymmetric additive-heat pair on the sharp positive total-order
strip.  Neither factor separately needs to lie in `L²`. -/
theorem summable_asymmetricHeatPairTerm {a b : ℂ} (ha : 0 ≤ a.re) (hb : 0 ≤ b.re)
    (hab : 1 < a.re + b.re) {x : ℝ} (hx : 0 < x) :
    Summable (asymmetricHeatPairTerm a b x) := by
  apply (upperLowerNatPairEquiv.summable_iff).mp
  exact Summable.of_norm_bounded (summable_asymmetricHeatPairMajorant hab hx)
    (norm_asymmetricHeatPairTerm_comp_equiv_le ha hb x)

/-- Closed parameter space for the symmetrically regulated reflected bi-heat pairing. -/
structure ReflectedBiHeatRegulator where
  z : ℂ
  epsilon : ℂ
  x : ℝ
  z_re_pos : 0 < z.re
  z_re_lt_one : z.re < 1
  epsilon_re_pos : 0 < epsilon.re
  x_pos : 0 < x

/-- The paper's reflected pair, with complementary orders symmetrically shifted by `epsilon / 2`. -/
noncomputable def reflectedBiHeatPairTerm (P : ReflectedBiHeatRegulator) (p : ℕ × ℕ) : ℂ :=
  asymmetricHeatPairTerm (P.z + P.epsilon / 2) (1 - P.z + P.epsilon / 2) P.x p

/-- **Regulated reflected bi-heat convergence.** Every admissible regulator gives an absolutely
summable reflected pair, including when either factor lies below the separate `L²` threshold. -/
theorem reflectedBiHeatPairTerm_summable :
    ∀ P : ReflectedBiHeatRegulator, Summable (reflectedBiHeatPairTerm P) := by
  intro P
  apply summable_asymmetricHeatPairTerm
  · norm_num [Complex.div_re]
    linarith [P.z_re_pos, P.epsilon_re_pos]
  · norm_num [Complex.div_re]
    linarith [P.z_re_lt_one, P.epsilon_re_pos]
  · norm_num [Complex.div_re]
    linarith [P.epsilon_re_pos]
  · exact P.x_pos

end RHTower

import GaloisForLFunctions.HTGeometry.HyperbolicDiagonalSummability

/-! # Exact shift law for the hyperbolic Fredholm product

Shifting the hyperbolic coupling by one spacing telescopes all interior
factors. The surviving boundary ratio gives a quadratic exponential law on
the integer coupling lattice.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter
open scoped Topology

def hyperbolicFredholmProduct (a b : ℝ) : ℝ := ∏' n, hyperbolicFredholmFactor a b n

theorem hasProd_hyperbolicFredholmFactor {a : ℝ} (ha : 0 < a) (b : ℝ) :
    HasProd (hyperbolicFredholmFactor a b) (hyperbolicFredholmProduct a b) :=
  (multipliable_hyperbolicFredholmFactor ha b).hasProd

theorem hyperbolicFredholmProduct_zero (a : ℝ) : hyperbolicFredholmProduct a 0 = 1 := by
  simp [hyperbolicFredholmProduct, hyperbolicFredholmFactor]

theorem cosh_add_div_exp (x c : ℝ) :
    Real.cosh (x + c) / Real.exp x =
      (Real.exp c + Real.exp (-c) * Real.exp (-2 * x)) / 2 := by
  rw [Real.cosh_eq, neg_add, Real.exp_add, Real.exp_add,
    show -2 * x = -(x + x) by ring, Real.exp_neg (x + x), Real.exp_add, Real.exp_neg x]
  field_simp [Real.exp_ne_zero]

theorem tendsto_cosh_add_div_exp {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Tendsto (fun n : ℕ => Real.cosh (n * a + c) / Real.exp (n * a))
      atTop (𝓝 (Real.exp c / 2)) := by
  have h0 := (Real.summable_exp_nat_mul_iff.mpr
    (by linarith : -2 * a < 0)).tendsto_atTop_zero
  have h := ((tendsto_const_nhds (x := Real.exp c)).add
    (h0.const_mul (Real.exp (-c)))).div_const 2
  simp only [mul_zero, add_zero] at h
  refine h.congr' (Eventually.of_forall fun n => ?_)
  change (Real.exp c + Real.exp (-c) * Real.exp ((n : ℝ) * (-2 * a))) / 2 =
    Real.cosh (n * a + c) / Real.exp (n * a)
  rw [cosh_add_div_exp, show (n : ℝ) * (-2 * a) = -2 * (n * a) by ring]

theorem tendsto_cosh_add_ratio {a : ℝ} (ha : 0 < a) (c d : ℝ) :
    Tendsto (fun n : ℕ => Real.cosh (n * a + c) / Real.cosh (n * a + d))
      atTop (𝓝 (Real.exp (c - d))) := by
  have h := (tendsto_cosh_add_div_exp ha c).div (tendsto_cosh_add_div_exp ha d)
    (by positivity : Real.exp d / 2 ≠ 0)
  have hc : (Real.exp c / 2) / (Real.exp d / 2) = Real.exp (c - d) := by
    rw [Real.exp_sub]
    field_simp
  rw [hc] at h
  refine h.congr' (Eventually.of_forall fun n => ?_)
  change (Real.cosh (n * a + c) / Real.exp (n * a)) /
      (Real.cosh (n * a + d) / Real.exp (n * a)) =
    Real.cosh (n * a + c) / Real.cosh (n * a + d)
  field_simp [Real.exp_ne_zero, ne_of_gt (Real.cosh_pos _)]

theorem hyperbolicFredholmFactor_prod_shift (a b : ℝ) (K : ℕ) :
    (∏ n ∈ Finset.range K, hyperbolicFredholmFactor a (b + a) n) *
        Real.cosh b * Real.cosh ((K : ℝ) * a - a - b) =
      (∏ n ∈ Finset.range K, hyperbolicFredholmFactor a b n) *
        Real.cosh (a + b) * Real.cosh ((K : ℝ) * a + b) := by
  induction K with
  | zero =>
      simp only [Finset.range_zero, Finset.prod_empty, Nat.cast_zero, zero_mul,
        one_mul, zero_sub, zero_add]
      rw [show -a - b = -(a + b) by ring, Real.cosh_neg]
      ring
  | succ K ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ,
        hyperbolicFredholmFactor_eq_cosh, hyperbolicFredholmFactor_eq_cosh]
      have h₁ : ((K + 1 : ℕ) : ℝ) * a - a - b = (K : ℝ) * a - b := by push_cast; ring
      have h₂ : ((K + 1 : ℕ) : ℝ) * a + b = (K : ℝ) * a + b + a := by push_cast; ring
      rw [h₁, h₂, show (K : ℝ) * a + (b + a) = (K : ℝ) * a + b + a by ring,
        show (K : ℝ) * a - (b + a) = (K : ℝ) * a - a - b by ring]
      calc
        _ = ((∏ n ∈ Finset.range K, hyperbolicFredholmFactor a (b + a) n) *
              Real.cosh b * Real.cosh ((K : ℝ) * a - a - b)) *
            (Real.cosh ((K : ℝ) * a + b + a) * Real.cosh ((K : ℝ) * a - b) /
              Real.cosh ((K : ℝ) * a) ^ 2) := by ring
        _ = _ := by rw [ih]; ring

theorem hyperbolicFredholmProduct_shift {a : ℝ} (ha : 0 < a) (b : ℝ) :
    hyperbolicFredholmProduct a (b + a) * Real.cosh b =
      Real.exp (a + 2 * b) * Real.cosh (a + b) * hyperbolicFredholmProduct a b := by
  have hp := (hasProd_hyperbolicFredholmFactor ha (b + a)).tendsto_prod_nat
  have hq := (hasProd_hyperbolicFredholmFactor ha b).tendsto_prod_nat
  have hr := tendsto_cosh_add_ratio ha b (-a - b)
  have hr' : Tendsto (fun K : ℕ => Real.cosh ((K : ℝ) * a + b) /
      Real.cosh ((K : ℝ) * a - a - b)) atTop (𝓝 (Real.exp (a + 2 * b))) := by
    rw [show b - (-a - b) = a + 2 * b by ring] at hr
    refine hr.congr' (Eventually.of_forall fun K => ?_)
    congr 2
    ring
  have he (K : ℕ) :
      (∏ n ∈ Finset.range K, hyperbolicFredholmFactor a (b + a) n) * Real.cosh b =
      (∏ n ∈ Finset.range K, hyperbolicFredholmFactor a b n) * Real.cosh (a + b) *
        (Real.cosh ((K : ℝ) * a + b) / Real.cosh ((K : ℝ) * a - a - b)) := by
    rw [← mul_div_assoc]
    exact (eq_div_iff (ne_of_gt (Real.cosh_pos ((K : ℝ) * a - a - b)))).mpr
      (hyperbolicFredholmFactor_prod_shift a b K)
  have hh := tendsto_nhds_unique (hp.mul_const (Real.cosh b))
    (((hq.mul_const (Real.cosh (a + b))).mul hr').congr' (Eventually.of_forall fun K => (he K).symm))
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hh

theorem hyperbolicFredholmProduct_nat_mul {a : ℝ} (ha : 0 < a) (m : ℕ) :
    hyperbolicFredholmProduct a (m * a) = Real.cosh (m * a) * Real.exp ((m : ℝ) ^ 2 * a) := by
  induction m with
  | zero => simp [hyperbolicFredholmProduct_zero]
  | succ m ih =>
      have h := hyperbolicFredholmProduct_shift ha ((m : ℝ) * a)
      rw [ih] at h
      have hm : ((m + 1 : ℕ) : ℝ) * a = (m : ℝ) * a + a := by push_cast; ring
      rw [hm]
      apply mul_right_cancel₀ (ne_of_gt (Real.cosh_pos ((m : ℝ) * a)))
      rw [h]
      have he : Real.exp (a + 2 * ((m : ℝ) * a)) * Real.exp ((m : ℝ) ^ 2 * a) =
          Real.exp (((m + 1 : ℕ) : ℝ) ^ 2 * a) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [show a + (m : ℝ) * a = (m : ℝ) * a + a by ring]
      calc
        _ = Real.cosh ((m : ℝ) * a + a) *
            (Real.exp (a + 2 * ((m : ℝ) * a)) * Real.exp ((m : ℝ) ^ 2 * a)) *
              Real.cosh ((m : ℝ) * a) := by ring
        _ = _ := by rw [he]

end
end GaloisForLFunctions.HTGeometry

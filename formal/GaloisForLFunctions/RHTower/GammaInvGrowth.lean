import GaloisForLFunctions.HTGeometry.GammaWeierstrass
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Explicit order-one growth of reciprocal Gamma

The Weierstrass product is split at `ceil ‖s‖ + 1`.  Its initial block is controlled by the
harmonic estimate, while the regularized tail is controlled by a telescoping reciprocal-square
series.  This gives a global, premise-free growth bound for `Gamma⁻¹`.
-/

open Complex Real Filter Topology Finset
open scoped BigOperators

noncomputable section

namespace HilbertSchmidt

private theorem hasSum_reciprocal_telescope (m : ℕ) (hm : 1 ≤ m) :
    HasSum (fun k : ℕ =>
      1 / ((m + k : ℕ) : ℝ) - 1 / ((m + k + 1 : ℕ) : ℝ)) (1 / (m : ℝ)) := by
  have hnonneg : ∀ k : ℕ, 0 ≤
      1 / ((m + k : ℕ) : ℝ) - 1 / ((m + k + 1 : ℕ) : ℝ) := by
    intro k
    have hmk : (0 : ℝ) < (m + k : ℕ) := by positivity
    have hle : ((m + k : ℕ) : ℝ) ≤ (m + k + 1 : ℕ) := by norm_num
    linarith [one_div_le_one_div_of_le hmk hle]
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2
  have hsum : ∀ n : ℕ,
      ∑ k ∈ Finset.range n,
          (1 / ((m + k : ℕ) : ℝ) - 1 / ((m + k + 1 : ℕ) : ℝ)) =
        1 / (m : ℝ) - 1 / ((m + n : ℕ) : ℝ) := by
    intro n
    simpa [Nat.add_assoc] using
      Finset.sum_range_sub' (fun k : ℕ => 1 / ((m + k : ℕ) : ℝ)) n
  have ht : Tendsto (fun n : ℕ => 1 / ((m + n : ℕ) : ℝ)) atTop (nhds 0) := by
    have hcast : Tendsto (fun n : ℕ => ((m + n : ℕ) : ℝ)) atTop atTop := by
      have hn : Tendsto (fun n : ℕ => n + m) atTop atTop := tendsto_add_atTop_nat m
      have hc :=
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hn
      convert hc using 1
      funext n
      simp [Function.comp_apply, Nat.cast_add, add_comm]
    exact tendsto_const_nhds.div_atTop hcast
  have hc : Tendsto (fun _ : ℕ => (1 / (m : ℝ))) atTop (nhds (1 / (m : ℝ))) :=
    tendsto_const_nhds
  simpa only [hsum, sub_zero] using hc.sub ht

/-- The reciprocal-square tail beginning after `m` is at most `1/m`. -/
theorem tsum_reciprocal_square_tail_le {m : ℕ} (hm : 1 ≤ m) :
    ∑' k : ℕ, 1 / (((m + k : ℕ) : ℝ) + 1) ^ 2 ≤ 1 / (m : ℝ) := by
  let f : ℕ → ℝ := fun k => 1 / (((m + k : ℕ) : ℝ) + 1) ^ 2
  let g : ℕ → ℝ := fun k =>
    1 / ((m + k : ℕ) : ℝ) - 1 / ((m + k + 1 : ℕ) : ℝ)
  have hgHas : HasSum g (1 / (m : ℝ)) := hasSum_reciprocal_telescope m hm
  have hfSum : Summable f := by
    have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa [f, add_comm, add_left_comm, add_assoc] using
      (summable_nat_add_iff (m + 1)).2 hp
  have hfg : ∀ k, f k ≤ g k := by
    intro k
    dsimp [f, g]
    push_cast
    let a : ℝ := (m : ℝ) + k
    have ha : 0 < a := by dsimp [a]; positivity
    have ha1 : 0 < a + 1 := by dsimp [a]; positivity
    have hid : 1 / a - 1 / (a + 1) = 1 / (a * (a + 1)) := by
      field_simp [ha.ne', ha1.ne', mul_ne_zero ha.ne' ha1.ne']
      ring
    change 1 / (a + 1) ^ 2 ≤ 1 / a - 1 / (a + 1)
    rw [hid]
    apply one_div_le_one_div_of_le (mul_pos ha ha1)
    nlinarith
  exact (hfSum.tsum_le_tsum hfg hgHas.summable).trans_eq hgHas.tsum_eq

/-- The regularized factor in the reciprocal-Gamma Weierstrass product. -/
def gammaWeierstrassFactor (s : ℂ) (k : ℕ) : ℂ :=
  (1 + s / ((k : ℂ) + 1)) * Complex.exp (-(s / ((k : ℂ) + 1)))

private theorem norm_regularized_exp_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(1 + w) * Complex.exp (-w) - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
  have hnx : ‖(-w)‖ ≤ 1 := by rwa [norm_neg]
  have hdecomp : (1 + w) * Complex.exp (-w) - 1
      = (Complex.exp (-w) - 1 - (-w)) - (-w) * (Complex.exp (-w) - 1) := by ring
  rw [hdecomp]
  calc
    ‖(Complex.exp (-w) - 1 - (-w)) - (-w) * (Complex.exp (-w) - 1)‖
        ≤ ‖Complex.exp (-w) - 1 - (-w)‖ + ‖(-w) * (Complex.exp (-w) - 1)‖ :=
          norm_sub_le _ _
    _ ≤ ‖(-w)‖ ^ 2 + ‖(-w)‖ * (2 * ‖(-w)‖) := by
      gcongr
      · exact Complex.norm_exp_sub_one_sub_id_le hnx
      · rw [norm_mul]
        gcongr
        exact Complex.norm_exp_sub_one_le hnx
    _ = 3 * ‖w‖ ^ 2 := by rw [norm_neg]; ring

private theorem norm_gammaWeierstrassFactor_le_initial (s : ℂ) (k : ℕ) :
    ‖gammaWeierstrassFactor s k‖ ≤
      (1 + ‖s‖) * Real.exp (‖s‖ / ((k : ℝ) + 1)) := by
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hden : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    rw [Complex.norm_def]
    convert Real.sqrt_sq hkpos.le using 1
    norm_num [Complex.normSq]
    ring_nf
  have hdiv : ‖s / ((k : ℂ) + 1)‖ = ‖s‖ / ((k : ℝ) + 1) := by
    rw [norm_div, hden]
  have hsum : ‖1 + s / ((k : ℂ) + 1)‖ ≤ 1 + ‖s‖ := by
    calc
      ‖1 + s / ((k : ℂ) + 1)‖ ≤ 1 + ‖s / ((k : ℂ) + 1)‖ := by
        simpa using norm_add_le (1 : ℂ) (s / ((k : ℂ) + 1))
      _ = 1 + ‖s‖ / ((k : ℝ) + 1) := by rw [hdiv]
      _ ≤ 1 + ‖s‖ := by
        gcongr
        exact div_le_self (norm_nonneg s) (by linarith)
  have hexp : ‖Complex.exp (-(s / ((k : ℂ) + 1)))‖ ≤
      Real.exp (‖s‖ / ((k : ℝ) + 1)) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    exact (Complex.re_le_norm _).trans_eq (by rw [norm_neg, hdiv])
  rw [gammaWeierstrassFactor, norm_mul]
  exact mul_le_mul hsum hexp (norm_nonneg _) (by positivity)

private theorem norm_gammaWeierstrassFactor_le_tail {s : ℂ} {k : ℕ}
    (hk : ⌈‖s‖⌉₊ ≤ k) :
    ‖gammaWeierstrassFactor s k‖ ≤
      Real.exp (3 * ‖s‖ ^ 2 / ((k : ℝ) + 1) ^ 2) := by
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hden : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    rw [Complex.norm_def]
    convert Real.sqrt_sq hkpos.le using 1
    norm_num [Complex.normSq]
    ring_nf
  let w := s / ((k : ℂ) + 1)
  have hwn : ‖w‖ = ‖s‖ / ((k : ℝ) + 1) := by dsimp [w]; rw [norm_div, hden]
  have hw : ‖w‖ ≤ 1 := by
    rw [hwn, div_le_one hkpos]
    calc
      ‖s‖ ≤ (⌈‖s‖⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (k : ℝ) := by exact_mod_cast hk
      _ ≤ (k : ℝ) + 1 := by linarith
  calc
    ‖gammaWeierstrassFactor s k‖
        ≤ 1 + ‖gammaWeierstrassFactor s k - 1‖ := by
          have := norm_add_le (1 : ℂ) (gammaWeierstrassFactor s k - 1)
          simpa [add_sub_cancel] using this
    _ ≤ 1 + 3 * ‖w‖ ^ 2 := by
      gcongr
      exact norm_regularized_exp_sub_one_le hw
    _ ≤ Real.exp (3 * ‖s‖ ^ 2 / ((k : ℝ) + 1) ^ 2) := by
      rw [hwn, div_pow]
      have h := Real.add_one_le_exp (3 * ‖s‖ ^ 2 / ((k : ℝ) + 1) ^ 2)
      ring_nf at h ⊢
      exact h

private theorem prod_gammaWeierstrassFactor_norm_le_initial
    (s : ℂ) {n m : ℕ} (hnm : n ≤ m) :
    (∏ k ∈ Finset.range n, ‖gammaWeierstrassFactor s k‖) ≤
      (1 + ‖s‖) ^ m * Real.exp (‖s‖ * (1 + Real.log m)) := by
  have hpoint : ∀ k ∈ Finset.range n,
      ‖gammaWeierstrassFactor s k‖ ≤
        (1 + ‖s‖) * Real.exp (‖s‖ / ((k : ℝ) + 1)) := by
    intro k _
    exact norm_gammaWeierstrassFactor_le_initial s k
  have hprod := Finset.prod_le_prod
    (fun k (_hk : k ∈ Finset.range n) => norm_nonneg (gammaWeierstrassFactor s k)) hpoint
  calc
    ∏ k ∈ Finset.range n, ‖gammaWeierstrassFactor s k‖
        ≤ ∏ k ∈ Finset.range n,
            ((1 + ‖s‖) * Real.exp (‖s‖ / ((k : ℝ) + 1))) := hprod
    _ = (1 + ‖s‖) ^ n *
        Real.exp (‖s‖ * (harmonic n : ℝ)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Real.exp_sum]
      congr 2
      simp_rw [div_eq_mul_inv]
      rw [← Finset.mul_sum (Finset.range n) (fun x : ℕ => ((x : ℝ) + 1)⁻¹) ‖s‖]
      congr 1
      simp [harmonic]
    _ ≤ (1 + ‖s‖) ^ m * Real.exp (‖s‖ * (harmonic m : ℝ)) := by
      have hp : (1 + ‖s‖) ^ n ≤ (1 + ‖s‖) ^ m :=
        pow_le_pow_right₀ (by linarith [norm_nonneg s]) hnm
      have hh : (harmonic n : ℝ) ≤ (harmonic m : ℝ) := by
        have hsum : (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) ≤
            ∑ k ∈ Finset.range m, 1 / ((k : ℝ) + 1) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
          intro k _ _
          positivity
        simpa [harmonic] using hsum
      have he : Real.exp (‖s‖ * (harmonic n : ℝ)) ≤
          Real.exp (‖s‖ * (harmonic m : ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hh (norm_nonneg s))
      exact mul_le_mul hp he (Real.exp_pos _).le (pow_nonneg (by positivity) _)
    _ ≤ (1 + ‖s‖) ^ m * Real.exp (‖s‖ * (1 + Real.log m)) := by
      gcongr
      exact harmonic_le_one_add_log m

private theorem prod_gammaWeierstrassFactor_norm_le_tail
    (s : ℂ) {n m : ℕ} (hmceil : ⌈‖s‖⌉₊ ≤ m) (hm : 1 ≤ m) :
    (∏ j ∈ Finset.range n, ‖gammaWeierstrassFactor s (m + j)‖) ≤
      Real.exp (3 * ‖s‖ ^ 2 / (m : ℝ)) := by
  let q : ℕ → ℝ := fun j => 1 / (((m + j : ℕ) : ℝ) + 1) ^ 2
  have hq0 : ∀ j, 0 ≤ q j := fun j => by dsimp [q]; positivity
  have hqsum : Summable q := by
    have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa [q, add_comm, add_left_comm, add_assoc] using
      (summable_nat_add_iff (m + 1)).2 hp
  have hqtsum : ∑' j, q j ≤ 1 / (m : ℝ) := by
    exact tsum_reciprocal_square_tail_le hm
  have hpoint : ∀ j ∈ Finset.range n,
      ‖gammaWeierstrassFactor s (m + j)‖ ≤ Real.exp (3 * ‖s‖ ^ 2 * q j) := by
    intro j _
    have htail := norm_gammaWeierstrassFactor_le_tail
      (s := s) (k := m + j) (hmceil.trans (Nat.le_add_right m j))
    dsimp [q]
    convert htail using 1
    ring_nf
  have hprod := Finset.prod_le_prod
    (fun j (_hj : j ∈ Finset.range n) => norm_nonneg (gammaWeierstrassFactor s (m + j))) hpoint
  calc
    ∏ j ∈ Finset.range n, ‖gammaWeierstrassFactor s (m + j)‖
        ≤ ∏ j ∈ Finset.range n, Real.exp (3 * ‖s‖ ^ 2 * q j) := hprod
    _ = Real.exp (3 * ‖s‖ ^ 2 * ∑ j ∈ Finset.range n, q j) := by
      rw [← Real.exp_sum, ← Finset.mul_sum]
    _ ≤ Real.exp (3 * ‖s‖ ^ 2 * ∑' j, q j) := by
      apply Real.exp_le_exp.mpr
      gcongr
      exact hqsum.sum_le_tsum (Finset.range n) (fun i _ => hq0 i)
    _ ≤ Real.exp (3 * ‖s‖ ^ 2 / (m : ℝ)) := by
      apply Real.exp_le_exp.mpr
      calc
        3 * ‖s‖ ^ 2 * ∑' j, q j ≤ 3 * ‖s‖ ^ 2 * (1 / (m : ℝ)) := by
          gcongr
        _ = 3 * ‖s‖ ^ 2 / (m : ℝ) := by ring

/-- Natural splitting depth for the reciprocal-Gamma Weierstrass product. -/
def gammaGrowthIndex (s : ℂ) : ℕ := ⌈‖s‖⌉₊ + 1

/-- The regularized Weierstrass product has an explicit order-one envelope. -/
theorem norm_tprod_gammaWeierstrassFactor_le (s : ℂ) :
    ‖∏' k : ℕ, gammaWeierstrassFactor s k‖ ≤
      (1 + ‖s‖) ^ (gammaGrowthIndex s) *
        Real.exp
          (‖s‖ * (1 + Real.log (gammaGrowthIndex s)) + 3 * ‖s‖) := by
  let m := gammaGrowthIndex s
  have hm1 : 1 ≤ m := by dsimp [m, gammaGrowthIndex]; omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
  have hmceil : ⌈‖s‖⌉₊ ≤ m := by dsimp [m, gammaGrowthIndex]; omega
  have hrm : ‖s‖ ≤ (m : ℝ) :=
    (Nat.le_ceil ‖s‖).trans (by exact_mod_cast hmceil)
  have hrdiv : ‖s‖ ^ 2 / (m : ℝ) ≤ ‖s‖ := by
    rw [div_le_iff₀ hmpos]
    nlinarith [norm_nonneg s]
  have hmult : Multipliable (gammaWeierstrassFactor s) := by
    rw [show gammaWeierstrassFactor s =
        (fun k : ℕ => (1 + s / ((k : ℂ) + 1)) *
          Complex.exp (-(s / ((k : ℂ) + 1)))) by
      funext k
      rfl]
    exact multipliable_weierstrassFactor s
  rw [hmult.norm_tprod]
  apply hmult.norm.tprod_le_of_prod_range_le
  intro n
  by_cases hnm : n ≤ m
  · have hi := prod_gammaWeierstrassFactor_norm_le_initial s hnm
    exact hi.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (le_add_of_nonneg_right (by positivity : 0 ≤ 3 * ‖s‖)))
      (by positivity))
  · have hmn : m ≤ n := Nat.le_of_not_ge hnm
    have hi := prod_gammaWeierstrassFactor_norm_le_initial s (le_refl m)
    have ht := prod_gammaWeierstrassFactor_norm_le_tail s
      (n := n - m) hmceil hm1
    rw [← Nat.add_sub_of_le hmn, Finset.prod_range_add]
    calc
      (∏ x ∈ Finset.range m, ‖gammaWeierstrassFactor s x‖) *
          ∏ x ∈ Finset.range (n - m), ‖gammaWeierstrassFactor s (m + x)‖
          ≤ ((1 + ‖s‖) ^ m * Real.exp (‖s‖ * (1 + Real.log m))) *
              Real.exp (3 * ‖s‖ ^ 2 / (m : ℝ)) :=
            mul_le_mul hi ht (by positivity) (by positivity)
      _ ≤ (1 + ‖s‖) ^ m *
          Real.exp (‖s‖ * (1 + Real.log m) + 3 * ‖s‖) := by
        rw [mul_assoc, ← Real.exp_add]
        gcongr
        calc
          3 * ‖s‖ ^ 2 / (m : ℝ) = 3 * (‖s‖ ^ 2 / (m : ℝ)) := by ring
          _ ≤ 3 * ‖s‖ :=
            mul_le_mul_of_nonneg_left hrdiv (by norm_num : (0 : ℝ) ≤ 3)
      _ = (1 + ‖s‖) ^ (gammaGrowthIndex s) *
          Real.exp
            (‖s‖ * (1 + Real.log (gammaGrowthIndex s)) + 3 * ‖s‖) := rfl

/-- Global reciprocal-Gamma bound with an explicit order-one Weierstrass envelope. -/
theorem norm_Gamma_inv_le_weierstrass_envelope (s : ℂ) :
    ‖(Complex.Gamma s)⁻¹‖ ≤
      ‖s‖ * Real.exp (‖Real.eulerMascheroniConstant‖ * ‖s‖) *
        ((1 + ‖s‖) ^ (gammaGrowthIndex s) *
          Real.exp
            (‖s‖ * (1 + Real.log (gammaGrowthIndex s)) + 3 * ‖s‖)) := by
  by_cases hs : ∀ m : ℕ, s ≠ -m
  · rw [Gamma_inv_weierstrass s hs]
    have hgammaExp :
        ‖Complex.exp ((Real.eulerMascheroniConstant : ℂ) * s)‖ ≤
          Real.exp (‖Real.eulerMascheroniConstant‖ * ‖s‖) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      exact (Complex.re_le_norm _).trans
        (by rw [norm_mul, Complex.norm_real])
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hgammaExp (norm_nonneg s))
      (norm_tprod_gammaWeierstrassFactor_le s) (norm_nonneg _)
      (mul_nonneg (norm_nonneg s) (Real.exp_pos _).le)
  · push Not at hs
    obtain ⟨m, rfl⟩ := hs
    rw [Complex.Gamma_neg_nat_eq_zero, inv_zero, norm_zero]
    positivity

end HilbertSchmidt

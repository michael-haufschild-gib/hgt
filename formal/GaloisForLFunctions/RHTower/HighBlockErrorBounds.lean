import GaloisForLFunctions.RHTower.HighBlockAsymptotics

/-!
# High-block law: every error term of the block estimate as a clean power

At the parameters `x = √(a/2π)`, `L = ⌈a^{51/100}⌉`, `N = ⌊U^{1/20}⌋`, `J = ⌈a^{3/10}U^{1/20}⌉`,
with `20 ≤ a ≤ v ≤ 2a`, `v ≤ U`, `0 < d ≤ ¼`, `d log U ≤ 2R`:

* `‖Tail‖ ≤ C_t (1 + 3^{201}(2π)^{101}) a^{−1}`;
* `‖Pole‖ ≤ e · e^{−a²}`;
* `‖χ‖² ≤ e · e^{4R}` and `(τ/2π)^{2d} ≤ e^{4R}`;
* `E_dir ≤ 9 e^{4R} C`, `E_dual ≤ C_v² C` (from the sharp-energy input);
* the freezing error `≤ (11/3) A_f e^{2R} a^{−17/400} U^{−1/20}`;
* `J · 8LN(1+log LN) ≤ 32 U^{91/100} log U`.
-/

open Complex Set Finset Filter Topology

namespace RHTower

noncomputable section

/-- `x = √(a/2π)` squared. -/
theorem hbX_sq {a : ℝ} (ha : 0 ≤ a) : hbX a ^ 2 = a / (2 * Real.pi) := by
  unfold hbX
  rw [Real.sq_sqrt (by positivity)]

theorem hbX_ge_one {a : ℝ} (ha : 20 ≤ a) : 1 ≤ hbX a := by
  unfold hbX
  rw [Real.one_le_sqrt]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_le_four]

theorem hbX_rpow_le {a : ℝ} (ha : 0 ≤ a) {p : ℝ} (hp : 0 ≤ p) :
    hbX a ^ p ≤ a ^ (p / 2) := by
  have h1 : hbX a ≤ a ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact hbX_le_sqrt ha
  calc hbX a ^ p ≤ (a ^ ((1 : ℝ) / 2)) ^ p :=
        Real.rpow_le_rpow (hbX_pos' ha) h1 hp
    _ = a ^ (p / 2) := by rw [← Real.rpow_mul ha]; ring_nf
where hbX_pos' {a : ℝ} (_ha : 0 ≤ a) : 0 ≤ hbX a := Real.sqrt_nonneg _

/-- **The tail on a block.** -/
theorem hbTail_le {Ct : ℝ} (hCt : ∀ (d x τ : ℝ), 0 < d → d ≤ 1 / 4 → 0 < x → ∀ L : ℕ, 1 ≤ L →
      ‖highBlockAFETail d x τ L‖ ≤
        Ct * (x ^ (200 : ℝ) * ((L : ℝ) ^ (1 - (1 / 2 - d + 200)) / ((1 / 2 - d + 200) - 1)) +
          (1 + |τ|) ^ (((200 : ℕ) : ℝ) + 1 / 2) * x ^ (-(1 / 2 - d + 200)) *
            ((L : ℝ) ^ (-((200 : ℕ) : ℝ)) / 200)))
    (hCt0 : 0 ≤ Ct) {d a τ : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (ha : 20 ≤ a) (hτa : a ≤ τ)
    (hτv : τ ≤ 2 * a) :
    ‖highBlockAFETail d (hbX a) τ (hbL a)‖ ≤
      Ct * (1 + 3 ^ (201 : ℕ) * (2 * Real.pi) ^ (101 : ℕ)) * a ^ (-(1 : ℝ)) := by
  have ha0 : 0 < a := by linarith
  have ha1 : 1 ≤ a := by linarith
  have hx := hbX_pos ha0
  have hx1 := hbX_ge_one ha
  have hL1 : 1 ≤ hbL a := hbL_pos ha1
  have hL1' : (1 : ℝ) ≤ (hbL a : ℝ) := one_le_hbL_real ha1
  have hLge : a ^ ((51 : ℝ) / 100) ≤ (hbL a : ℝ) := hbL_ge
  have ha51 : 0 < a ^ ((51 : ℝ) / 100) := by positivity
  have h := hCt d (hbX a) τ hd hd4 hx (hbL a) hL1
  refine h.trans ?_
  -- first term ≤ a^{-1}
  have hT1 : hbX a ^ (200 : ℝ) *
      ((hbL a : ℝ) ^ (1 - (1 / 2 - d + 200)) / ((1 / 2 - d + 200) - 1)) ≤ a ^ (-(1 : ℝ)) := by
    have hx200 : hbX a ^ (200 : ℝ) ≤ a ^ (100 : ℝ) := by
      have := hbX_rpow_le ha0.le (p := 200) (by norm_num)
      rwa [show (200 : ℝ) / 2 = 100 by norm_num] at this
    have hLexp : (hbL a : ℝ) ^ (1 - (1 / 2 - d + 200)) ≤ (hbL a : ℝ) ^ (-(199 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hL1' (by linarith)
    have hL199 : (hbL a : ℝ) ^ (-(199 : ℝ)) ≤ (a ^ ((51 : ℝ) / 100)) ^ (-(199 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos ha51 hLge (by norm_num)
    have hden : 1 ≤ (1 / 2 - d + 200) - 1 := by linarith
    have hpow : (a ^ ((51 : ℝ) / 100)) ^ (-(199 : ℝ)) = a ^ (-((10149 : ℝ) / 100)) := by
      rw [← Real.rpow_mul ha0.le]
      norm_num
    calc hbX a ^ (200 : ℝ) * ((hbL a : ℝ) ^ (1 - (1 / 2 - d + 200)) / ((1 / 2 - d + 200) - 1))
        ≤ a ^ (100 : ℝ) * (a ^ (-((10149 : ℝ) / 100)) / 1) := by
          gcongr
          · exact hLexp.trans (hL199.trans_eq hpow)
      _ = a ^ ((100 : ℝ) + -((10149 : ℝ) / 100)) := by
          rw [div_one, ← Real.rpow_add ha0]
      _ ≤ a ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le ha1 (by norm_num)
  -- second term ≤ 3^(201 : ℕ) (2π)^(101 : ℕ) a^{-1}
  have hT2 : (1 + |τ|) ^ (((200 : ℕ) : ℝ) + 1 / 2) * hbX a ^ (-(1 / 2 - d + 200)) *
      ((hbL a : ℝ) ^ (-((200 : ℕ) : ℝ)) / 200) ≤
      3 ^ (201 : ℕ) * (2 * Real.pi) ^ (101 : ℕ) * a ^ (-(1 : ℝ)) := by
    have hτ0 : 0 ≤ τ := by linarith
    have h1τ : 1 + |τ| ≤ 3 * a := by rw [abs_of_nonneg hτ0]; linarith
    have hA : (1 + |τ|) ^ (((200 : ℕ) : ℝ) + 1 / 2) ≤ (3 * a) ^ (((200 : ℕ) : ℝ) + 1 / 2) :=
      Real.rpow_le_rpow (by positivity) h1τ (by positivity)
    have hA' : (3 * a) ^ (((200 : ℕ) : ℝ) + 1 / 2) ≤ 3 ^ (201 : ℕ) * a ^ (((200 : ℕ) : ℝ) + 1 / 2) := by
      rw [Real.mul_rpow (by norm_num) ha0.le]
      gcongr
      calc (3 : ℝ) ^ (((200 : ℕ) : ℝ) + 1 / 2) ≤ 3 ^ ((201 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; norm_num)
        _ = 3 ^ (201 : ℕ) := Real.rpow_natCast _ _
    have hB : hbX a ^ (-(1 / 2 - d + 200)) ≤ hbX a ^ (-((801 : ℝ) / 4)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hB' : hbX a ^ (-((801 : ℝ) / 4)) ≤ (2 * Real.pi) ^ (101 : ℕ) * a ^ (-((801 : ℝ) / 8)) := by
      have hsq : hbX a ^ (-((801 : ℝ) / 4)) = (hbX a ^ (2 : ℕ)) ^ (-((801 : ℝ) / 8)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
        norm_num
      rw [hsq, hbX_sq ha0.le, Real.div_rpow ha0.le (by positivity), Real.rpow_neg ha0.le,
        Real.rpow_neg (by positivity), div_eq_mul_inv, inv_inv]
      have h2π : (2 * Real.pi) ^ ((801 : ℝ) / 8) ≤ (2 * Real.pi) ^ (101 : ℕ) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by norm_num)
      calc (a ^ ((801 : ℝ) / 8))⁻¹ * (2 * Real.pi) ^ ((801 : ℝ) / 8)
          ≤ (a ^ ((801 : ℝ) / 8))⁻¹ * (2 * Real.pi) ^ (101 : ℕ) :=
            mul_le_mul_of_nonneg_left h2π (by positivity)
        _ = (2 * Real.pi) ^ (101 : ℕ) * (a ^ ((801 : ℝ) / 8))⁻¹ := by ring
    have hC : (hbL a : ℝ) ^ (-((200 : ℕ) : ℝ)) / 200 ≤ a ^ (-(102 : ℝ)) := by
      have h1 : (hbL a : ℝ) ^ (-((200 : ℕ) : ℝ)) ≤ (a ^ ((51 : ℝ) / 100)) ^ (-((200 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ha51 hLge (by norm_num)
      have h2 : (a ^ ((51 : ℝ) / 100)) ^ (-((200 : ℕ) : ℝ)) = a ^ (-(102 : ℝ)) := by
        rw [← Real.rpow_mul ha0.le]
        norm_num
      have h3 : 0 ≤ a ^ (-(102 : ℝ)) := by positivity
      calc (hbL a : ℝ) ^ (-((200 : ℕ) : ℝ)) / 200 ≤ a ^ (-(102 : ℝ)) / 200 := by
            gcongr
            exact h1.trans_eq h2
        _ ≤ a ^ (-(102 : ℝ)) := by
            rw [div_le_iff₀ (by norm_num)]
            linarith
    have hexp : a ^ (((200 : ℕ) : ℝ) + 1 / 2) * a ^ (-((801 : ℝ) / 8)) * a ^ (-(102 : ℝ)) ≤
        a ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add ha0, ← Real.rpow_add ha0]
      exact Real.rpow_le_rpow_of_exponent_le ha1 (by push_cast; norm_num)
    calc (1 + |τ|) ^ (((200 : ℕ) : ℝ) + 1 / 2) * hbX a ^ (-(1 / 2 - d + 200)) *
          ((hbL a : ℝ) ^ (-((200 : ℕ) : ℝ)) / 200)
        ≤ (3 ^ (201 : ℕ) * a ^ (((200 : ℕ) : ℝ) + 1 / 2)) *
          ((2 * Real.pi) ^ (101 : ℕ) * a ^ (-((801 : ℝ) / 8))) * a ^ (-(102 : ℝ)) := by
          gcongr
          · exact hA.trans hA'
          · exact hB.trans hB'
      _ = 3 ^ (201 : ℕ) * (2 * Real.pi) ^ (101 : ℕ) *
          (a ^ (((200 : ℕ) : ℝ) + 1 / 2) * a ^ (-((801 : ℝ) / 8)) * a ^ (-(102 : ℝ))) := by ring
      _ ≤ 3 ^ (201 : ℕ) * (2 * Real.pi) ^ (101 : ℕ) * a ^ (-(1 : ℝ)) := by
          gcongr
  calc Ct * (hbX a ^ (200 : ℝ) *
        ((hbL a : ℝ) ^ (1 - (1 / 2 - d + 200)) / ((1 / 2 - d + 200) - 1)) +
        (1 + |τ|) ^ (((200 : ℕ) : ℝ) + 1 / 2) * hbX a ^ (-(1 / 2 - d + 200)) *
          ((hbL a : ℝ) ^ (-((200 : ℕ) : ℝ)) / 200))
      ≤ Ct * (a ^ (-(1 : ℝ)) + 3 ^ (201 : ℕ) * (2 * Real.pi) ^ (101 : ℕ) * a ^ (-(1 : ℝ))) := by
        gcongr
    _ = Ct * (1 + 3 ^ (201 : ℕ) * (2 * Real.pi) ^ (101 : ℕ)) * a ^ (-(1 : ℝ)) := by ring

/-- **The pole on a block.** -/
theorem hbPole_le {d a τ : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (ha : 20 ≤ a) (hτa : a ≤ τ) :
    ‖smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) (hbX a)‖ ≤
      Real.exp 1 * Real.exp (-(a ^ 2)) := by
  have ha0 : 0 < a := by linarith
  have ha1 : 1 ≤ a := by linarith
  have hτ1 : 1 ≤ τ := by linarith
  have hx := hbX_pos ha0
  refine (norm_smoothAFEZetaShiftedPoleResidue_displaced_le_highBlockFreezing hd.le hd4 hx hτ1).trans ?_
  have hxpow : hbX a ^ (1 / 2 + d) ≤ a := by
    calc hbX a ^ (1 / 2 + d) ≤ a ^ ((1 / 2 + d) / 2) := hbX_rpow_le ha0.le (by linarith)
      _ ≤ a ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
      _ = a := Real.rpow_one a
  have hexp : Real.exp (-(τ ^ 2)) ≤ Real.exp (-(a ^ 2)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc hbX a ^ (1 / 2 + d) * Real.exp 1 * Real.exp (-(τ ^ 2)) / τ
      ≤ a * Real.exp 1 * Real.exp (-(a ^ 2)) / a := by gcongr
    _ = Real.exp 1 * Real.exp (-(a ^ 2)) := by field_simp

/-- **The `χ`-weights on a block.** -/
theorem hbChi_le {d U τ R : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hdU : d * Real.log U ≤ 2 * R)
    (hU : 1 ≤ U) (hτ : 4 ≤ τ) (hτU : τ ≤ U) :
    ‖zetaChi (displacedLinePt d τ)‖ ^ 2 ≤ Real.exp 1 * Real.exp (4 * R) ∧
      chiModulusWeight (2 * d) τ ≤ Real.exp (4 * R) := by
  have hτ0 : 0 < τ := by linarith
  have hU2d : U ^ (2 * d) ≤ Real.exp (4 * R) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hw : chiModulusWeight (2 * d) τ ≤ Real.exp (4 * R) := by
    unfold chiModulusWeight
    calc (τ / (2 * Real.pi)) ^ (2 * d) ≤ U ^ (2 * d) := by
          apply Real.rpow_le_rpow (by positivity) _ (by linarith)
          calc τ / (2 * Real.pi) ≤ τ := by
                rw [div_le_iff₀ (by positivity)]
                nlinarith [Real.pi_gt_three]
            _ ≤ U := hτU
      _ ≤ Real.exp (4 * R) := hU2d
  refine ⟨?_, hw⟩
  obtain ⟨e, he, heq⟩ := exists_normSq_zetaChi_displacedLinePt_eq_weight_mul_exp hd.le hd4 hτ0
  rw [heq]
  have hee : e ≤ 1 := by
    refine (le_abs_self e).trans (he.trans ?_)
    have h1 : Real.pi / τ ≤ Real.pi / 4 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hτ
    have h2 : 5 / τ ^ 2 ≤ 5 / 4 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hτ 2)
    have h3 : 0 ≤ Real.pi / τ + 5 / τ ^ 2 := by positivity
    calc 2 * d * (Real.pi / τ + 5 / τ ^ 2) ≤ 2 * (1 / 4) * (Real.pi / 4 + 5 / 4 ^ 2) := by
          apply mul_le_mul (by linarith) (by linarith) h3 (by norm_num)
      _ ≤ 1 := by nlinarith [Real.pi_le_four]
  calc chiModulusWeight (2 * d) τ * Real.exp e ≤ Real.exp (4 * R) * Real.exp 1 := by
        gcongr
        all_goals exact Real.exp_le_exp.mpr hee
    _ = Real.exp 1 * Real.exp (4 * R) := mul_comm _ _

/-- **The direct energy on a block.** -/
theorem hbEdir_le {C d a U R : ℝ} (hC0 : 0 ≤ C) (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hdU : d * Real.log U ≤ 2 * R) (ha : 20 ≤ a) (hLU : (hbL a : ℝ) + 1 ≤ U) {N : ℕ}
    (b : Fin N → ℂ)
    (hC : ∀ u ∈ Finset.range (hbL a),
      ∑ r : Fin (hbL a * N), ‖Sieve.dirConv (hbL a) N (sharpHead criticalHeadCoeff (hbL a) u) b r‖ ^ 2 ≤ C) :
    ∑ r : Fin (hbL a * N),
        ‖Sieve.dirConv (hbL a) N (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff 0 d (hbX a) n) b r‖ ^ 2 ≤
      9 * Real.exp (4 * R) * C := by
  have ha0 : 0 < a := by linarith
  have h := sum_normSq_dirConv_direct_le_sharp hd.le (hbX_pos ha0) (hbL a) N b hC0 hC
  refine h.trans ?_
  have hU1 : 1 ≤ U := by linarith [one_le_hbL_real (by linarith : (1 : ℝ) ≤ a)]
  have hL : ((hbL a : ℝ) + 1) ^ d ≤ U ^ d :=
    Real.rpow_le_rpow (by positivity) hLU hd.le
  have hUd : U ^ d ≤ Real.exp (2 * R) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsq : (3 * ((hbL a : ℝ) + 1) ^ d) ^ 2 ≤ 9 * Real.exp (4 * R) := by
    calc (3 * ((hbL a : ℝ) + 1) ^ d) ^ 2 ≤ (3 * Real.exp (2 * R)) ^ 2 := by
          gcongr
          exact hL.trans hUd
      _ = 9 * Real.exp (4 * R) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          norm_num
          ring_nf
  exact mul_le_mul_of_nonneg_right hsq hC0

/-- **`J · MV` on a block.** -/
theorem hbJMV_le {a U : ℝ} (ha : 1 ≤ a) (haU : a ≤ U) (hU : Real.exp 2 ≤ U)
    (hLNU : 2 * U ^ ((56 : ℝ) / 100) * Real.exp 1 ≤ U) :
    (hbJ a U : ℝ) * (8 * ((hbL a * hbN U : ℕ) : ℝ) * (1 + Real.log ((hbL a * hbN U : ℕ) : ℝ))) ≤
      32 * U ^ ((91 : ℝ) / 100) * Real.log U := by
  have hU1 : 1 ≤ U := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hU0 : 0 < U := by linarith
  have ha0 : 0 < a := by linarith
  have hone : ∀ p : ℝ, 0 ≤ p → (1 : ℝ) ≤ U ^ p := fun p hp => by
    calc (1 : ℝ) = U ^ (0 : ℝ) := (Real.rpow_zero U).symm
      _ ≤ U ^ p := Real.rpow_le_rpow_of_exponent_le hU1 hp
  have hJ : (hbJ a U : ℝ) ≤ 2 * U ^ ((7 : ℝ) / 20) := by
    refine (hbJ_le ha0.le hU0.le).trans ?_
    have h1 : a ^ ((3 : ℝ) / 10) ≤ U ^ ((3 : ℝ) / 10) :=
      Real.rpow_le_rpow ha0.le haU (by norm_num)
    have h2 : U ^ ((3 : ℝ) / 10) * U ^ ((1 : ℝ) / 20) = U ^ ((7 : ℝ) / 20) := by
      rw [← Real.rpow_add hU0]; norm_num
    have h3 := hone ((7 : ℝ) / 20) (by norm_num)
    have h4 : a ^ ((3 : ℝ) / 10) * U ^ ((1 : ℝ) / 20) ≤ U ^ ((7 : ℝ) / 20) := by
      rw [← h2]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    linarith
  have hLN : ((hbL a * hbN U : ℕ) : ℝ) ≤ 2 * U ^ ((56 : ℝ) / 100) := by
    push_cast
    have hL : (hbL a : ℝ) ≤ 2 * U ^ ((51 : ℝ) / 100) := by
      refine (hbL_le ha0.le).trans ?_
      have h1 : a ^ ((51 : ℝ) / 100) ≤ U ^ ((51 : ℝ) / 100) :=
        Real.rpow_le_rpow ha0.le haU (by norm_num)
      have h3 := hone ((51 : ℝ) / 100) (by norm_num)
      linarith
    have hN : (hbN U : ℝ) ≤ U ^ ((1 : ℝ) / 20) := hbN_le hU0.le
    have h2 : U ^ ((51 : ℝ) / 100) * U ^ ((1 : ℝ) / 20) = U ^ ((56 : ℝ) / 100) := by
      rw [← Real.rpow_add hU0]; norm_num
    calc (hbL a : ℝ) * (hbN U : ℝ) ≤ (2 * U ^ ((51 : ℝ) / 100)) * U ^ ((1 : ℝ) / 20) :=
          mul_le_mul hL hN (Nat.cast_nonneg _) (by positivity)
      _ = 2 * U ^ ((56 : ℝ) / 100) := by rw [mul_assoc, h2]
  have hLN1 : (1 : ℝ) ≤ ((hbL a * hbN U : ℕ) : ℝ) := by
    have hL1 := hbL_pos ha
    have hN1 : 1 ≤ hbN U := by
      unfold hbN
      exact Nat.le_floor (by rw [Nat.cast_one]; exact hone _ (by norm_num))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hlog : 1 + Real.log ((hbL a * hbN U : ℕ) : ℝ) ≤ Real.log U := by
    have h1 : Real.log ((hbL a * hbN U : ℕ) : ℝ) ≤ Real.log (2 * U ^ ((56 : ℝ) / 100)) :=
      Real.log_le_log (by linarith) hLN
    have h2 : Real.log (2 * U ^ ((56 : ℝ) / 100) * Real.exp 1) ≤ Real.log U :=
      Real.log_le_log (by positivity) hLNU
    rw [Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp] at h2
    linarith
  have hlogLN0 : 0 ≤ 1 + Real.log ((hbL a * hbN U : ℕ) : ℝ) := by
    have := Real.log_nonneg hLN1
    linarith
  calc (hbJ a U : ℝ) * (8 * ((hbL a * hbN U : ℕ) : ℝ) * (1 + Real.log ((hbL a * hbN U : ℕ) : ℝ)))
      ≤ (2 * U ^ ((7 : ℝ) / 20)) * (8 * (2 * U ^ ((56 : ℝ) / 100)) * Real.log U) := by
        gcongr
    _ = 32 * (U ^ ((7 : ℝ) / 20) * U ^ ((56 : ℝ) / 100)) * Real.log U := by ring
    _ = 32 * U ^ ((91 : ℝ) / 100) * Real.log U := by
        rw [← Real.rpow_add hU0]; norm_num

/-- **The freezing error on a sub-block.** -/
theorem hbFreeze_le {Af : ℝ}
    (hAf : ∀ d : ℝ, 0 < d → d ≤ 1 / 4 → ∀ x : ℝ, 0 < x → ∀ T τ : ℝ, 4 ≤ T → T ≤ τ →
      ∀ L : ℕ, ‖highBlockDualHead d x τ L - highBlockDualHeadFrozen d x T τ L‖ ≤
        Af * (τ - T) * T ^ (-(d + 1 / 4 + 1)) * x ^ (d + 1 / 4) *
          ∑ n ∈ Finset.range L, ((n + 1 : ℝ)) ^ (-(1 / 4 : ℝ)))
    (hAf0 : 0 ≤ Af) {d a v U R T τ : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hdU : d * Real.log U ≤ 2 * R) (ha : 20 ≤ a) (hav : a ≤ v) (hv2 : v ≤ 2 * a) (hvU : v ≤ U)
    (hTa : a ≤ T) (hTτ : T ≤ τ) (hτv : τ ≤ v) (hh : τ - T ≤ (v - a) / hbJ a U) :
    ‖highBlockDualHead d (hbX a) τ (hbL a) - highBlockDualHeadFrozen d (hbX a) T τ (hbL a)‖ ≤
      (11 / 3) * Af * Real.exp (2 * R) * a ^ (-((17 : ℝ) / 400)) * U ^ (-((1 : ℝ) / 20)) := by
  have ha0 : 0 < a := by linarith
  have ha1 : 1 ≤ a := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hU0 : 0 < U := by linarith
  have hx := hbX_pos ha0
  have hT4 : 4 ≤ T := by linarith
  have h := hAf d hd hd4 (hbX a) hx T τ hT4 hTτ (hbL a)
  refine h.trans ?_
  -- (τ − T) ≤ a^{7/10} U^{-1/20}
  have hJpos : 0 < a ^ ((3 : ℝ) / 10) * U ^ ((1 : ℝ) / 20) := by positivity
  have hJge := (hbJ_ge : a ^ ((3 : ℝ) / 10) * U ^ ((1 : ℝ) / 20) ≤ (hbJ a U : ℝ))
  have hJpos' : (0 : ℝ) < hbJ a U := lt_of_lt_of_le hJpos hJge
  have hh1 : τ - T ≤ a ^ ((7 : ℝ) / 10) * U ^ (-((1 : ℝ) / 20)) := by
    refine hh.trans ?_
    calc (v - a) / (hbJ a U : ℝ) ≤ a / (a ^ ((3 : ℝ) / 10) * U ^ ((1 : ℝ) / 20)) := by
          apply div_le_div₀ ha0.le (by linarith) hJpos hJge
      _ = a ^ ((7 : ℝ) / 10) * U ^ (-((1 : ℝ) / 20)) := by
          rw [Real.rpow_neg hU0.le, show (7 : ℝ) / 10 = 1 - 3 / 10 by norm_num, Real.rpow_sub ha0,
            Real.rpow_one]
          field_simp
  -- T^{-(d+5/4)} ≤ a^{-5/4}
  have hT1 : T ^ (-(d + 1 / 4 + 1)) ≤ a ^ (-((5 : ℝ) / 4)) := by
    calc T ^ (-(d + 1 / 4 + 1)) ≤ a ^ (-(d + 1 / 4 + 1)) :=
          Real.rpow_le_rpow_of_nonpos ha0 hTa (by linarith)
      _ ≤ a ^ (-((5 : ℝ) / 4)) := Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
  -- x^{d+1/4} ≤ e^{2R} a^{1/8}
  have hx2 : hbX a ^ (d + 1 / 4) ≤ Real.exp (2 * R) * a ^ ((1 : ℝ) / 8) := by
    rw [Real.rpow_add hx]
    have hxa : hbX a ≤ U := (hbX_le ha1).trans (hav.trans hvU)
    have h1 : hbX a ^ d ≤ U ^ d := Real.rpow_le_rpow hx.le hxa hd.le
    have h2 : U ^ d ≤ Real.exp (2 * R) := by
      rw [Real.rpow_def_of_pos hU0]
      apply Real.exp_le_exp.mpr
      nlinarith
    have h3 : hbX a ^ ((1 : ℝ) / 4) ≤ a ^ ((1 : ℝ) / 8) := by
      have := hbX_rpow_le ha0.le (p := (1 : ℝ) / 4) (by norm_num)
      rwa [show (1 : ℝ) / 4 / 2 = 1 / 8 by norm_num] at this
    exact mul_le_mul (h1.trans h2) h3 (by positivity) (by positivity)
  -- Σ (n+1)^{-1/4} ≤ (11/3) a^{153/400}
  have hS : ∑ n ∈ Finset.range (hbL a), ((n + 1 : ℝ)) ^ (-(1 / 4 : ℝ)) ≤
      (11 / 3) * a ^ ((153 : ℝ) / 400) := by
    refine (sum_rpow_neg_quarter_le (hbL a)).trans ?_
    have hL : (hbL a : ℝ) ≤ 2 * a ^ ((51 : ℝ) / 100) := by
      refine (hbL_le ha0.le).trans ?_
      have : (1 : ℝ) ≤ a ^ ((51 : ℝ) / 100) := by
        calc (1 : ℝ) = a ^ (0 : ℝ) := (Real.rpow_zero a).symm
          _ ≤ a ^ ((51 : ℝ) / 100) := Real.rpow_le_rpow_of_exponent_le ha1 (by norm_num)
      linarith
    have hL34 : (hbL a : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 * a ^ ((153 : ℝ) / 400) := by
      calc (hbL a : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 * a ^ ((51 : ℝ) / 100)) ^ ((3 : ℝ) / 4) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hL (by norm_num)
        _ = 2 ^ ((3 : ℝ) / 4) * (a ^ ((51 : ℝ) / 100)) ^ ((3 : ℝ) / 4) :=
            Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 2 * a ^ ((153 : ℝ) / 400) := by
            rw [← Real.rpow_mul ha0.le]
            norm_num
            gcongr
            calc (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
    have hone : (1 : ℝ) ≤ a ^ ((153 : ℝ) / 400) := by
      calc (1 : ℝ) = a ^ (0 : ℝ) := (Real.rpow_zero a).symm
        _ ≤ a ^ ((153 : ℝ) / 400) := Real.rpow_le_rpow_of_exponent_le ha1 (by norm_num)
    linarith
  -- assemble
  have hτT0 : 0 ≤ τ - T := by linarith
  have hS0 : 0 ≤ ∑ n ∈ Finset.range (hbL a), ((n + 1 : ℝ)) ^ (-(1 / 4 : ℝ)) :=
    Finset.sum_nonneg fun _ _ => by positivity
  calc Af * (τ - T) * T ^ (-(d + 1 / 4 + 1)) * hbX a ^ (d + 1 / 4) *
        ∑ n ∈ Finset.range (hbL a), ((n + 1 : ℝ)) ^ (-(1 / 4 : ℝ))
      ≤ Af * (a ^ ((7 : ℝ) / 10) * U ^ (-((1 : ℝ) / 20))) * a ^ (-((5 : ℝ) / 4)) *
          (Real.exp (2 * R) * a ^ ((1 : ℝ) / 8)) * ((11 / 3) * a ^ ((153 : ℝ) / 400)) := by
        gcongr
    _ = (11 / 3) * Af * Real.exp (2 * R) *
          (a ^ ((7 : ℝ) / 10) * a ^ (-((5 : ℝ) / 4)) * a ^ ((1 : ℝ) / 8) * a ^ ((153 : ℝ) / 400)) *
          U ^ (-((1 : ℝ) / 20)) := by ring
    _ = (11 / 3) * Af * Real.exp (2 * R) * a ^ (-((17 : ℝ) / 400)) * U ^ (-((1 : ℝ) / 20)) := by
        rw [← Real.rpow_add ha0, ← Real.rpow_add ha0, ← Real.rpow_add ha0]
        norm_num

end

end RHTower

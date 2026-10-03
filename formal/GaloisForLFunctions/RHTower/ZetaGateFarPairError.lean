import GaloisForLFunctions.RHTower.ZetaGateFarLeftLine
import GaloisForLFunctions.RHTower.ZetaGateRectanglePairError

/-!
# The pair error of the product approximate functional equation for mollifiers up to `u^43`

With the left lines on `Re w = −7` (`ZetaGateFarLeftLine`, `j = 3`), the direct off-diagonal
integrated by parts `100` times and the dual off-diagonal split at `Y₀ = u^{102}` with `500`
oscillation steps and `150` shift steps, the pair error of the block twisted moment with
`x = u^100`, taper `η = u^95`, block start `p = u^100` and coefficients up to `N ≤ u^43` is at most
`(q − p + 2u^95)(pairStarFar + 2^{14}K₂(1+(p−u^95))^{2d})/u^98` (`norm_pairError_le_param_far`):

* the smoothed diagonal gives `K₁(x/c)^{−7} ≤ K₁u^{−98}` for `c ≤ u^86`;
* the dual diagonal gives `K₂(cx)^7(1+L)^{−(14−2d)} ≤ 2^{14}K₂u^{1302−1400}(1+L)^{2d}`;
* the direct off-diagonal is `u^{5100−9500+4300} = u^{−100}`;
* the dual off-diagonal is `u^{21500+25602−47200} = u^{−98}` (oscillation) and
  `u^{15100−15198} = u^{−98}` (shift); the residue term is `O(u^{−300})`.

Summed over the `N² ≤ u^86` pairs the error is `O(u^{−12})` per unit window mass.  The only real
constraint is the per-step oscillation saving `η^{−2}·hk·Y₀ = u^{2m+102−190}`, which allows
`m < 44`.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset Filter
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

theorem farDepth_three : farDepth 3 = 7 := by norm_num [farDepth]

/-! ## Sizes of the pair parameters -/

/-- `(x/c)^{−7} ≤ 1/u^{98}` for `x = u^{100}`, `1 ≤ c ≤ u^{86}`. -/
theorem rpow_x_div_c_le_far {u c : ℝ} (hu : 1 ≤ u) (hc1 : 1 ≤ c) (hc : c ≤ u ^ 86) :
    (u ^ 100 / c) ^ (-(7 : ℝ)) ≤ 1 / u ^ 98 := by
  have hu0 : 0 < u := by linarith
  have h1 : u ^ 14 ≤ u ^ 100 / c := by
    rw [le_div_iff₀ (by linarith)]
    calc u ^ 14 * c ≤ u ^ 14 * u ^ 86 := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = u ^ 100 := by ring
  calc (u ^ 100 / c) ^ (-(7 : ℝ)) ≤ (u ^ 14) ^ (-(7 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
    _ = 1 / u ^ 98 := by
        rw [Real.rpow_neg (by positivity), show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast, ← pow_mul, one_div]

/-- `(c x)^7 ≤ u^{1302}` for `x = u^{100}`, `0 ≤ c ≤ u^{86}`. -/
theorem rpow_c_mul_x_le_far {u c : ℝ} (hu : 1 ≤ u) (hc0 : 0 ≤ c) (hc : c ≤ u ^ 86) :
    (c * u ^ 100) ^ (7 : ℝ) ≤ u ^ 1302 := by
  have hu0 : 0 < u := by linarith
  rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc (c * u ^ 100) ^ 7 ≤ (u ^ 86 * u ^ 100) ^ 7 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hc (by positivity)) 7
    _ = u ^ 1302 := by ring

/-- `(1+L)^{−(14−2d)} ≤ (2^{14}/u^{1400})(1+L)^{2d}` for `L ≥ u^{100}/2`. -/
theorem rpow_one_add_L_le_far {u L : ℝ} (hu : 1 ≤ u) (hL : u ^ 100 / 2 ≤ L) (d : ℝ) :
    (1 + L) ^ (-(2 * (7 : ℝ) - 2 * d)) ≤ (2 ^ 14 / u ^ 1400) * (1 + L) ^ (2 * d) := by
  have hu0 : 0 < u := by linarith
  have hL0 : 0 < 1 + L := by
    have : 0 < u ^ 100 / 2 := by positivity
    linarith
  have hsplit : (1 + L) ^ (-(2 * (7 : ℝ) - 2 * d))
      = (1 + L) ^ (-((14 : ℕ) : ℝ)) * (1 + L) ^ (2 * d) := by
    rw [← Real.rpow_add hL0]
    congr 1
    push_cast
    ring
  rw [hsplit]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hL0.le _)
  have hge : u ^ 100 / 2 ≤ 1 + L := by linarith
  rw [Real.rpow_neg hL0.le, Real.rpow_natCast]
  have h1 : (u ^ 100 / 2) ^ 14 ≤ (1 + L) ^ 14 := pow_le_pow_left₀ (by positivity) hge 14
  have h2 : ((1 + L) ^ 14)⁻¹ ≤ ((u ^ 100 / 2) ^ 14)⁻¹ := inv_anti₀ (by positivity) h1
  refine h2.trans (le_of_eq ?_)
  rw [div_pow, ← pow_mul]
  field_simp

/-! ## The window integral of the dual remainder -/

theorem norm_integral_window_dualLeft_le_gen {d c x p q η : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hc : 0 < c) (hx : 0 < x) (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) {K₂ a b : ℝ}
    (hK₂0 : 0 ≤ K₂) (hb : 0 ≤ b)
    (hK₂ : ∀ τ : ℝ, 4 ≤ |τ| → ‖dualLeft d c x τ‖ ≤ K₂ * (c * x) ^ a * (1 + |τ|) ^ (-b)) :
    ‖∫ t, blockWindowC p q η t * dualLeft d c x t‖
      ≤ (q - p + 2 * η) * (K₂ * (c * x) ^ a * (1 + (p - η)) ^ (-b)) := by
  have hsub : Set.Icc (p - η) (q + η) ⊆ Set.Icc (-(q + η)) (q + η) := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  set M : ℝ := K₂ * (c * x) ^ a * (1 + (p - η)) ^ (-b) with hM
  have hpη : 0 < 1 + (p - η) := by linarith
  have hM0 : 0 ≤ M := by positivity
  have hint : Integrable (fun t => blockWindowC p q η t * dualLeft d c x t) :=
    integrable_window_mul hη ((continuousOn_dualLeft hd hd8 hc hx (q + η)).mono hsub)
  have hpt : ∀ t, ‖blockWindowC p q η t * dualLeft d c x t‖ ≤ ‖blockWindowC p q η t‖ * M := by
    intro t
    rw [norm_mul]
    by_cases ht : t ∈ Set.Icc (p - η) (q + η)
    · have h4t : 4 ≤ |t| := le_trans (by linarith [ht.1]) (le_abs_self t)
      refine mul_le_mul_of_nonneg_left ((hK₂ t h4t).trans ?_) (norm_nonneg _)
      rw [hM]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h1 : 1 + (p - η) ≤ 1 + |t| := by
        have := le_abs_self t
        linarith [ht.1]
      exact Real.rpow_le_rpow_of_nonpos hpη h1 (by linarith)
    · rw [blockWindowC_eq_zero hη ht, norm_zero, zero_mul, zero_mul]
  calc ‖∫ t, blockWindowC p q η t * dualLeft d c x t‖
      ≤ ∫ t, ‖blockWindowC p q η t * dualLeft d c x t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖blockWindowC p q η t‖ * M :=
        integral_mono hint.norm ((integrable_blockWindowC hη).norm.mul_const _) hpt
    _ = (∫ t, ‖blockWindowC p q η t‖) * M := integral_mul_const _ _
    _ ≤ (q - p + 2 * η) * M :=
        mul_le_mul_of_nonneg_right (integral_norm_blockWindowC_le hη hpq) hM0

/-- **The pair error bound with general left-line remainders.** -/
theorem norm_pairError_le_gen {d x p q η : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hx1 : 1 ≤ x)
    (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) {g h' k' h k : ℕ} (hg : 0 < g) (hh' : 0 < h')
    (hk' : 0 < k') (hhg : h = g * h') (hkg : k = g * k') {K₁ K₂ a₁ a b : ℝ} (hK₁0 : 0 ≤ K₁)
    (hK₂0 : 0 ≤ K₂) (hb : 0 ≤ b)
    (hK₁ : ‖smoothLeft (1 / 2 - d) ((h' * k' : ℕ) : ℝ) x‖
      ≤ K₁ * (x / ((h' * k' : ℕ) : ℝ)) ^ (-a₁))
    (hK₂ : ∀ τ : ℝ, 4 ≤ |τ| → ‖dualLeft d ((h' * k' : ℕ) : ℝ) x τ‖
      ≤ K₂ * (((h' * k' : ℕ) : ℝ) * x) ^ a * (1 + |τ|) ^ (-b)) :
    ‖pairError d x p q η h' k' h k‖
      ≤ (∑' P : ℕ × ℕ, directOffDiagTerm (1 / 2 - d) x p q η h k P)
        + (∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P)
        + ((h : ℝ) * k) ^ (-(1 / 2 - d))
          * (((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 - d))
              * (K₁ * (x / ((h' * k' : ℕ) : ℝ)) ^ (-a₁)) * (q - p + 2 * η)
            + ((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 + d))
              * ((q - p + 2 * η) * (K₂ * (((h' * k' : ℕ) : ℝ) * x) ^ a
                * (1 + (p - η)) ^ (-b))))
        + (q - p + 2 * η) * (((h : ℝ) * k) ^ (-(1 / 2 - d))
          * (18 * Real.exp 1 * x * Real.exp (-((p - η) ^ 2)))) := by
  have hd4 : d ≤ 1 / 4 := by linarith
  have hx : 0 < x := by linarith
  have hh : 0 < h := by rw [hhg]; positivity
  have hk : 0 < k := by rw [hkg]; positivity
  have hc : (0 : ℝ) < ((h' * k' : ℕ) : ℝ) := by positivity
  unfold pairError
  have e1 := norm_tsum_compl_directTerm_le hd hd4 hx hη hpq hg hhg hkg hh hk
  have e2 := norm_tsum_compl_dualTerm_le hd hd4 hx hη hL hpq hg hhg hkg hh hk
  have e3 : ‖((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
      * (((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 - d)) : ℝ) : ℂ)
          * smoothLeft (1 / 2 - d) ((h' * k' : ℕ) : ℝ) x * (∫ t, blockWindowC p q η t)
        + ((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 + d)) : ℝ) : ℂ)
          * ∫ t, blockWindowC p q η t * dualLeft d ((h' * k' : ℕ) : ℝ) x t)‖
      ≤ ((h : ℝ) * k) ^ (-(1 / 2 - d))
          * (((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 - d))
              * (K₁ * (x / ((h' * k' : ℕ) : ℝ)) ^ (-a₁)) * (q - p + 2 * η)
            + ((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 + d))
              * ((q - p + 2 * η) * (K₂ * (((h' * k' : ℕ) : ℝ) * x) ^ a
                * (1 + (p - η)) ^ (-b)))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hK₁ (by positivity))
        (norm_integral_blockWindowC_le hη hpq) (norm_nonneg _) (by positivity)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left
        (norm_integral_window_dualLeft_le_gen hd hd8 hc hx hη hL hpq hK₂0 hb hK₂) (by positivity)
  have e4 := norm_residueTerm_le hd hd4 hx1 hη hL hpq hh hk
  calc ‖_ + _ + _ - residueTerm d x p q η h k‖
      ≤ ‖_ + _ + _‖ + ‖residueTerm d x p q η h k‖ := norm_sub_le _ _
    _ ≤ ‖_ + _‖ + ‖_‖ + ‖residueTerm d x p q η h k‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖_‖ + ‖_‖ + ‖_‖ + ‖residueTerm d x p q η h k‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ _ := by
        gcongr

/-! ## The direct off-diagonal with `100` integrations by parts -/

theorem tsum_directOffDiagTerm_le_param_far {d u p q : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hu : 1 ≤ u) (hpq : p ≤ q) {N h k : ℕ} (hN : (N : ℝ) ≤ u ^ 43) (hh : h ∈ Finset.Icc 1 N)
    (hk : k ∈ Finset.Icc 1 N) {CA : ℝ} (hCA0 : 0 ≤ CA)
    (hCA : ∀ {y : ℝ}, 0 < y → ‖smoothAFECutoff y‖ ≤ CA * y ^ (-(51 : ℝ))) :
    ∑' P : ℕ × ℕ, directOffDiagTerm (1 / 2 - d) (u ^ 100) p q (u ^ 95) h k P
      ≤ (q - p + 2 * u ^ 95)
        * ((blockWindowConst 100 * CA * 2 ^ 100
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2) / u ^ 100) := by
  have hh0 : 0 < h := (Finset.mem_Icc.mp hh).1
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  have hu0 : 0 < u := by linarith
  have hbnd := tsum_directOffDiagTerm_le 100 hCA0 hCA (σ₀ := 1 / 2 - d) (x := u ^ 100) (p := p)
    (q := q) (η := u ^ 95) (by push_cast; linarith) (by positivity) (by positivity) hpq hh0 hk0
  have h50 : ((100 : ℕ) : ℝ) / 2 = 50 := by norm_num
  rw [h50] at hbnd
  refine hbnd.trans ?_
  have e1 : ((h : ℝ) * k) ^ (50 - (1 / 2 - d)) ≤ u ^ 4300 := by
    have := mul_cast_rpow_le_u_pow_of_le hu hN hh hk (s := 50 - (1 / 2 - d)) 50
      (by push_cast; linarith)
    rwa [show 2 * 43 * 50 = 4300 by norm_num] at this
  have hZ0 := tsum_succ_rpow_neg_nonneg (51 + (1 / 2 - d) - 50)
  have e2 : (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(51 + (1 / 2 - d) - 50))) ^ 2
      ≤ (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hZ0 (tsum_succ_rpow_neg_le (by norm_num) (by linarith only [hd8])) 2
  have hD0 : 0 ≤ directOffDiagConst 100 CA 51 (u ^ 100) p q (u ^ 95) :=
    directOffDiagConst_nonneg 100 hCA0 (by positivity) (by positivity) hpq
  calc directOffDiagConst 100 CA 51 (u ^ 100) p q (u ^ 95) * ((h : ℝ) * k) ^ (50 - (1 / 2 - d))
        * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(51 + (1 / 2 - d) - 50))) ^ 2
      ≤ directOffDiagConst 100 CA 51 (u ^ 100) p q (u ^ 95) * u ^ 4300
        * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2 := by
        gcongr
    _ = (q - p + 2 * u ^ 95)
        * ((blockWindowConst 100 * CA * 2 ^ 100
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2) / u ^ 100) := by
        unfold directOffDiagConst
        rw [show (u ^ 100) ^ (51 : ℝ) = u ^ 5100 by
          rw [show (51 : ℝ) = ((51 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul]]
        field_simp
        try ring

/-! ## The dual off-diagonal with `500` oscillation steps -/

/-- The jet constant `Σ_j C(K,j) bwc_j (K−j)! 132^{K−j}`, kept irreducible so that no tactic
expands the sum. -/
@[irreducible] def jetStarK (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), (Nat.choose K j : ℝ) * blockWindowConst j
    * ((K - j).factorial * (132 : ℝ) ^ (K - j))

theorem jetStarK_nonneg (K : ℕ) : 0 ≤ jetStarK K := by
  unfold jetStarK
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (by positivity) (blockWindowConst_nonneg j)) (by positivity)

theorem windowCarrierJetConst_le_paramK (K : ℕ) {u L : ℝ} (hu : 1 ≤ u) (hL : u ^ 100 / 2 ≤ L) :
    windowCarrierJetConst K (u ^ 95) L (u ^ 5) ≤ jetStarK K / u ^ (95 * K) := by
  have hu0 : 0 < u := by linarith
  have hL0 : 0 < L := by
    have : 0 < u ^ 100 / 2 := by positivity
    linarith
  unfold windowCarrierJetConst jetStarK
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjK : j ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hbase : 33 * (1 + |u ^ 5|) / L ≤ 132 / u ^ 95 := by
    rw [abs_of_pos (by positivity)]
    have h1 : 1 + u ^ 5 ≤ 2 * u ^ 5 := by
      have : 1 ≤ u ^ 5 := one_le_pow₀ hu
      linarith
    calc 33 * (1 + u ^ 5) / L ≤ 33 * (2 * u ^ 5) / (u ^ 100 / 2) :=
          div_le_div₀ (by positivity) (by nlinarith) (by positivity) hL
      _ = 132 / u ^ 95 := by
          field_simp
          ring
  have hpow : (33 * (1 + |u ^ 5|) / L) ^ (K - j) ≤ (132 / u ^ 95) ^ (K - j) :=
    pow_le_pow_left₀ (by positivity) hbase _
  have hb0 := blockWindowConst_nonneg j
  calc (Nat.choose K j : ℝ) * (blockWindowConst j / (u ^ 95) ^ j)
        * (((K - j).factorial : ℝ) * (33 * (1 + |u ^ 5|) / L) ^ (K - j))
      ≤ (Nat.choose K j : ℝ) * (blockWindowConst j / (u ^ 95) ^ j)
        * (((K - j).factorial : ℝ) * (132 / u ^ 95) ^ (K - j)) := by
        gcongr
    _ = (Nat.choose K j : ℝ) * blockWindowConst j
        * (((K - j).factorial : ℝ) * (132 : ℝ) ^ (K - j)) / u ^ (95 * K) := by
        rw [div_pow]
        have : (u ^ 95) ^ j * (u ^ 95) ^ (K - j) = u ^ (95 * K) := by
          rw [← pow_add, Nat.add_sub_cancel' hjK, ← pow_mul]
        field_simp
        rw [← this]
        ring

/-- `4750!` as a real constant, kept irreducible so that no tactic evaluates the factorial. -/
@[irreducible] def fact4750 : ℝ := (Nat.factorial 4750 : ℝ)

theorem fact4750_eq : fact4750 = (Nat.factorial 4750 : ℝ) := by
  unfold fact4750
  rfl

theorem fact4750_nonneg : 0 ≤ fact4750 := by
  rw [fact4750_eq]
  exact Nat.cast_nonneg _

/-- The absolute constant of the oscillation part of the far dual envelope. -/
def oscStarFar (C₁ : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * Real.exp 1
    * (jetStarK 500 * (Real.exp 8 * 625) * Real.sqrt Real.pi * 2 ^ 500
      + C₁ * 256 * (Real.exp 16 * (fact4750 * 2 ^ 4750) * Real.sqrt (4 * Real.pi)))

theorem oscStarFar_nonneg {C₁ : ℝ} (hC₁ : 0 ≤ C₁) : 0 ≤ oscStarFar C₁ := by
  unfold oscStarFar
  have := jetStarK_nonneg 500
  have := fact4750_nonneg
  positivity

/-- `e^{−(u^5)²/2} ≤ 4750! 2^{4750} / u^{47500}`. -/
theorem exp_neg_sq_u_pow_five_le_far {u : ℝ} (hu0 : 0 < u) :
    Real.exp (-((u ^ 5) ^ 2) / 2) ≤ fact4750 * 2 ^ 4750 / u ^ 47500 := by
  have hy : 0 < (u ^ 5) ^ 2 / 2 := by positivity
  have h := exp_neg_le_factorial_div hy 4750
  rw [show -((u ^ 5) ^ 2) / 2 = -((u ^ 5) ^ 2 / 2) by ring]
  refine h.trans (le_of_eq ?_)
  rw [← fact4750_eq, div_pow, ← pow_mul, ← pow_mul]
  rw [div_div_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]

/-- The algebra of the far oscillation constant. -/
theorem oscFar_algebra {u : ℝ} (hu0 : 0 < u) (J F C₁ : ℝ) :
    (u ^ 100)⁻¹ * ((J / u ^ (95 * 500)) * (Real.exp 8 * (625 * u ^ 400)) * Real.sqrt Real.pi
        * 2 ^ 500)
      + (u ^ 100)⁻¹ * (C₁ * (256 * u ^ 400) * (Real.exp 16 * (F / u ^ 47500)
        * Real.sqrt (4 * Real.pi)))
    = (J * (Real.exp 8 * 625) * Real.sqrt Real.pi * 2 ^ 500
        + C₁ * 256 * (Real.exp 16 * F * Real.sqrt (4 * Real.pi))) / u ^ 47200 := by
  rw [show 95 * 500 = 47500 by norm_num]
  field_simp

theorem dualOffDiagOscConstV_le_param_far {u p q C₁ : ℝ} (hu : 2 ≤ u) (hp : p = u ^ 100)
    (hpq : p ≤ q) (hq : q ≤ 2 * u ^ 100) (hC₁ : 0 ≤ C₁) :
    dualOffDiagOscConstV 500 C₁ (u ^ 100) p q (u ^ 95) (u ^ 5)
      ≤ (q - p + 2 * u ^ 95) * (oscStarFar C₁ / u ^ 47200) := by
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have h95 : u ^ 95 ≤ u ^ 100 / 2 := by
    have h5 : 2 ≤ u ^ 5 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 5)
    have : u ^ 100 = u ^ 95 * u ^ 5 := by ring
    rw [this]
    nlinarith [pow_pos hu0 95]
  have hL : u ^ 100 / 2 ≤ p - u ^ 95 := by rw [hp]; linarith
  have hlen : 0 ≤ q - p + 2 * u ^ 95 := by
    have := pow_pos hu0 95
    linarith
  have hq0 : 0 ≤ q := by
    have := pow_pos hu0 100
    rw [hp] at hpq
    linarith
  have hpow4 : (1 + (q + u ^ 95) + u ^ 5) ^ 4 ≤ 625 * u ^ 400 := by
    have h1 : (1 : ℝ) ≤ u ^ 100 := one_le_pow₀ hu1
    have h5 : u ^ 5 ≤ u ^ 100 := u_pow_le_u_pow hu1 (by norm_num)
    have h95' : u ^ 95 ≤ u ^ 100 := u_pow_le_u_pow hu1 (by norm_num)
    have hsum : 1 + (q + u ^ 95) + u ^ 5 ≤ 5 * u ^ 100 := by linarith
    calc (1 + (q + u ^ 95) + u ^ 5) ^ 4 ≤ (5 * u ^ 100) ^ 4 :=
          pow_le_pow_left₀ (by linarith [pow_pos hu0 95, pow_pos hu0 5]) hsum 4
      _ = 625 * u ^ 400 := by ring
  have hpow4' : (1 + (q + u ^ 95)) ^ 4 ≤ 256 * u ^ 400 := by
    have h1 : (1 : ℝ) ≤ u ^ 100 := one_le_pow₀ hu1
    have h95' : u ^ 95 ≤ u ^ 100 := u_pow_le_u_pow hu1 (by norm_num)
    have hsum : 1 + (q + u ^ 95) ≤ 4 * u ^ 100 := by linarith
    calc (1 + (q + u ^ 95)) ^ 4 ≤ (4 * u ^ 100) ^ 4 :=
          pow_le_pow_left₀ (by linarith [pow_pos hu0 95]) hsum 4
      _ = 256 * u ^ 400 := by ring
  have hjs := jetStarK_nonneg 500
  have hf := fact4750_nonneg
  -- nonnegativity facts, before any large power enters the context
  have hE8 : 0 ≤ Real.exp 8 * (1 + (q + u ^ 95) + u ^ 5) ^ 4 := by positivity
  have hE16 : 0 ≤ Real.exp 16 * Real.exp (-((u ^ 5) ^ 2) / 2) := by positivity
  have hJq : 0 ≤ jetStarK 500 / u ^ (95 * 500) := by positivity
  have hsq : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hsq4 : 0 ≤ Real.sqrt (4 * Real.pi) := Real.sqrt_nonneg _
  have h2K : (0 : ℝ) ≤ 2 ^ 500 := by positivity
  have hC4 : 0 ≤ C₁ * (1 + (q + u ^ 95)) ^ 4 := by positivity
  have hcoef : 0 ≤ (1 / (2 * Real.pi)) * ((u ^ 100)⁻¹ * Real.exp 1 * (q - p + 2 * u ^ 95)) := by
    have : 0 ≤ (u ^ 100)⁻¹ * Real.exp 1 * (q - p + 2 * u ^ 95) :=
      mul_nonneg (by positivity) hlen
    positivity
  have key : ∀ X Y : ℝ, (1 / (2 * Real.pi)) * ((u ^ 100)⁻¹ * Real.exp 1 * (q - p + 2 * u ^ 95))
      * (X + Y) = (q - p + 2 * u ^ 95) * ((1 / (2 * Real.pi)) * Real.exp 1
        * ((u ^ 100)⁻¹ * X + (u ^ 100)⁻¹ * Y)) := fun X Y => by ring
  unfold dualOffDiagOscConstV
  have hA : windowCarrierJetConst 500 (u ^ 95) (p - u ^ 95) (u ^ 5)
        * (Real.exp 8 * (1 + (q + u ^ 95) + u ^ 5) ^ 4) * Real.sqrt Real.pi * 2 ^ 500
      ≤ (jetStarK 500 / u ^ (95 * 500)) * (Real.exp 8 * (625 * u ^ 400)) * Real.sqrt Real.pi
          * 2 ^ 500 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul (windowCarrierJetConst_le_paramK 500 hu1 hL)
        (mul_le_mul_of_nonneg_left hpow4 (Real.exp_pos 8).le) hE8 hJq) hsq) h2K
  have hB : C₁ * (1 + (q + u ^ 95)) ^ 4
        * (Real.exp 16 * Real.exp (-((u ^ 5) ^ 2) / 2) * Real.sqrt (4 * Real.pi))
      ≤ C₁ * (256 * u ^ 400)
        * (Real.exp 16 * (fact4750 * 2 ^ 4750 / u ^ 47500) * Real.sqrt (4 * Real.pi)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hpow4' hC₁)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (exp_neg_sq_u_pow_five_le_far hu0) (Real.exp_pos 16).le) hsq4)
      (mul_nonneg hE16 hsq4) (mul_nonneg hC₁ (by positivity))
  calc (1 / (2 * Real.pi)) * ((u ^ 100)⁻¹ * Real.exp 1 * (q - p + 2 * u ^ 95))
        * (windowCarrierJetConst 500 (u ^ 95) (p - u ^ 95) (u ^ 5)
            * (Real.exp 8 * (1 + (q + u ^ 95) + u ^ 5) ^ 4) * Real.sqrt Real.pi * 2 ^ 500
          + C₁ * (1 + (q + u ^ 95)) ^ 4
            * (Real.exp 16 * Real.exp (-((u ^ 5) ^ 2) / 2) * Real.sqrt (4 * Real.pi)))
      ≤ (1 / (2 * Real.pi)) * ((u ^ 100)⁻¹ * Real.exp 1 * (q - p + 2 * u ^ 95))
        * ((jetStarK 500 / u ^ (95 * 500)) * (Real.exp 8 * (625 * u ^ 400)) * Real.sqrt Real.pi
            * 2 ^ 500
          + C₁ * (256 * u ^ 400)
            * (Real.exp 16 * (fact4750 * 2 ^ 4750 / u ^ 47500)
              * Real.sqrt (4 * Real.pi))) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) hcoef
    _ = (q - p + 2 * u ^ 95) * ((1 / (2 * Real.pi)) * Real.exp 1
          * ((u ^ 100)⁻¹ * ((jetStarK 500 / u ^ (95 * 500)) * (Real.exp 8 * (625 * u ^ 400))
              * Real.sqrt Real.pi * 2 ^ 500)
            + (u ^ 100)⁻¹ * (C₁ * (256 * u ^ 400)
              * (Real.exp 16 * (fact4750 * 2 ^ 4750 / u ^ 47500)
                * Real.sqrt (4 * Real.pi))))) :=
        key _ _
    _ = (q - p + 2 * u ^ 95) * (oscStarFar C₁ / u ^ 47200) := by
        rw [oscFar_algebra hu0 (jetStarK 500) (fact4750 * 2 ^ 4750) C₁]
        unfold oscStarFar
        generalize (2 : ℝ) ^ 500 = T
        generalize fact4750 * (2 : ℝ) ^ 4750 = F
        ring

/-- The algebra of the far shift constant. -/
theorem shiftFar_algebra {u : ℝ} (hu0 : 0 < u) (W C c : ℝ) :
    W * (C * (c * u ^ 30100) * (1 / u ^ 15000)) = W * (C * c * u ^ 15100) := by
  field_simp

theorem dualOffDiagShiftConst_le_param_far {d u p q C₂ : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hu : 1 ≤ u) (hp : p = u ^ 100) (hpq : p ≤ q) (hq : q ≤ 2 * u ^ 100) (hC₂ : 0 ≤ C₂) :
    dualOffDiagShiftConst 150 C₂ d (u ^ 100) p q (u ^ 95)
      ≤ (q - p + 2 * u ^ 95) * (C₂ * 4 ^ 301 * u ^ 15100) := by
  have hu0 : 0 < u := by linarith
  have hlen : 0 ≤ q - p + 2 * u ^ 95 := by
    have := pow_pos hu0 95
    linarith
  have hq0 : 0 ≤ q := by
    have := pow_pos hu0 100
    rw [hp] at hpq
    linarith
  unfold dualOffDiagShiftConst
  have h1 : (1 : ℝ) ≤ u ^ 100 := one_le_pow₀ hu
  have h95' : u ^ 95 ≤ u ^ 100 := u_pow_le_u_pow hu (by norm_num)
  have hsum : 1 + (q + u ^ 95) ≤ 4 * u ^ 100 := by linarith
  have hbase : 0 ≤ 1 + (q + u ^ 95) := by linarith [pow_pos hu0 95]
  have hrp : 0 ≤ (u ^ 100) ^ (-(1 / 2 - d + (150 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hc0 : 0 ≤ C₂ * ((4 : ℝ) ^ 301 * u ^ 30100) := by positivity
  have hexp : -(1 / 2 - d + (150 : ℕ) : ℝ) ≤ -((150 : ℕ) : ℝ) := by
    push_cast; linarith only [hd8]
  have hpow : (1 + (q + u ^ 95)) ^ (2 * ((150 : ℕ) + 1 / 2 : ℝ)) ≤ 4 ^ 301 * u ^ 30100 := by
    rw [show (2 * ((150 : ℕ) + 1 / 2 : ℝ)) = ((301 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (1 + (q + u ^ 95)) ^ 301 ≤ (4 * u ^ 100) ^ 301 := pow_le_pow_left₀ hbase hsum 301
      _ = 4 ^ 301 * u ^ 30100 := by rw [mul_pow, ← pow_mul]
  have hx : (u ^ 100) ^ (-(1 / 2 - d + (150 : ℕ) : ℝ)) ≤ 1 / u ^ 15000 := by
    calc (u ^ 100) ^ (-(1 / 2 - d + (150 : ℕ) : ℝ)) ≤ (u ^ 100) ^ (-((150 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le h1 hexp
      _ = 1 / u ^ 15000 := by
          rw [Real.rpow_neg (le_trans zero_le_one h1), Real.rpow_natCast, ← pow_mul, one_div]
  calc (q - p + 2 * u ^ 95) * (C₂ * (1 + (q + u ^ 95)) ^ (2 * ((150 : ℕ) + 1 / 2 : ℝ))
        * (u ^ 100) ^ (-(1 / 2 - d + (150 : ℕ) : ℝ)))
      ≤ (q - p + 2 * u ^ 95) * (C₂ * (4 ^ 301 * u ^ 30100) * (1 / u ^ 15000)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hpow hC₂) hx hrp hc0)
          hlen
    _ = (q - p + 2 * u ^ 95) * (C₂ * 4 ^ 301 * u ^ 15100) := shiftFar_algebra hu0 _ _ _

/-- The absolute constant of the far dual envelope. -/
def dualStarFar (C₁ C₂ : ℝ) : ℝ :=
  oscStarFar C₁ * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ))) ^ 2
    + C₂ * 4 ^ 301 * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2

theorem dualStarFar_nonneg {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    0 ≤ dualStarFar C₁ C₂ := by
  unfold dualStarFar
  have := oscStarFar_nonneg hC₁
  positivity

/-- The algebra of the far dual envelope. -/
theorem dualFar_algebra {u : ℝ} (hu0 : 0 < u) (W A B Z₁ Z₂ : ℝ) :
    W * (A / u ^ 47200) * u ^ 21500 * u ^ 25602 * Z₁ + W * (B * u ^ 15100) * 1
        * (1 / u ^ 15198) * Z₂
      = W * ((A * Z₁ + B * Z₂) / u ^ 98) := by
  field_simp

theorem tsum_dualOffDiagTerm_le_param_far {d u p q : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hu : 2 ≤ u) (hp : p = u ^ 100) (hpq : p ≤ q) (hq : q ≤ 2 * u ^ 100) {N h k : ℕ}
    (hN : (N : ℝ) ≤ u ^ 43) (hh : h ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) {C₁ C₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : ∀ (d x p q η Y₀ V : ℝ) (h k : ℕ), 0 < d → d ≤ 1 / 4 →
      0 < x → 0 < η → 4 ≤ p - η → p ≤ q → 0 < Y₀ → 0 ≤ V → 2 * V ≤ p - η → 0 < h → 0 < k →
      ∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P
        ≤ dualOffDiagOscConstV 500 C₁ x p q η V
              * ((h : ℝ) * k) ^ (((500 : ℕ) : ℝ) / 2 - 1 / 2 + d)
              * Y₀ ^ (((500 : ℕ) : ℝ) / 2 + 1) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
          + dualOffDiagShiftConst 150 C₂ d x p q η * ((h : ℝ) * k) ^ (-(1 / 2 - d))
              * Y₀ ^ (-(((150 : ℕ) : ℝ) - 1)) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2) :
    ∑' P : ℕ × ℕ, dualOffDiagTerm d (u ^ 100) p q (u ^ 95) h k P
      ≤ (q - p + 2 * u ^ 95) * (dualStarFar C₁ C₂ / u ^ 98) := by
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hh0 : 0 < h := (Finset.mem_Icc.mp hh).1
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  have h95 : u ^ 95 ≤ u ^ 100 / 2 := by
    have h5 : 2 ≤ u ^ 5 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 5)
    have : u ^ 100 = u ^ 95 * u ^ 5 := by ring
    rw [this]
    nlinarith [pow_pos hu0 95]
  have h4 : (4 : ℝ) ≤ p - u ^ 95 := by
    have : (2 : ℝ) ^ 100 ≤ u ^ 100 := pow_le_pow_left₀ (by norm_num) hu 100
    have h2 : (8 : ℝ) ≤ u ^ 100 / 2 := by
      have : (16 : ℝ) ≤ (2 : ℝ) ^ 100 := by norm_num
      linarith
    rw [hp]
    linarith
  have hV : 2 * u ^ 5 ≤ p - u ^ 95 := by
    have h5 : u ^ 5 ≤ u ^ 100 / 4 := by
      have : u ^ 100 = u ^ 5 * u ^ 95 := by ring
      have h95' : (4 : ℝ) ≤ u ^ 95 :=
        le_trans (by norm_num) (le_trans (pow_le_pow_left₀ (by norm_num) hu 95) le_rfl)
      rw [this]
      nlinarith [pow_pos hu0 5]
    rw [hp]
    linarith
  -- nonnegativity facts, before any large power enters the context
  have hsk : 0 ≤ ((h : ℝ) * k) ^ (((500 : ℕ) : ℝ) / 2 - 1 / 2 + d) := by positivity
  have hsk' : 0 ≤ ((h : ℝ) * k) ^ (-(1 / 2 - d)) := by positivity
  have hZ0 := tsum_succ_rpow_neg_nonneg (5 / 2 + d)
  have hZ1 : 0 ≤ (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2 := sq_nonneg _
  have hZ2 := sq_nonneg (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ)))
  have e5 : (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
      ≤ (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hZ0 (tsum_succ_rpow_neg_le (by norm_num) (by linarith only [hd])) 2
  have e3 : ((h : ℝ) * k) ^ (-(1 / 2 - d)) ≤ 1 := mul_cast_rpow_neg_le_one hh0 hk0 (by linarith)
  have hos := oscStarFar_nonneg hC₁
  have hlen : 0 ≤ q - p + 2 * u ^ 95 := by
    have := pow_pos hu0 95
    linarith
  have hO1 : 0 ≤ (q - p + 2 * u ^ 95) * (oscStarFar C₁ / u ^ 47200) :=
    mul_nonneg hlen (div_nonneg hos (by positivity))
  have hU25 : (0 : ℝ) ≤ u ^ 25602 := by positivity
  have hO3 : 0 ≤ (q - p + 2 * u ^ 95) * (oscStarFar C₁ / u ^ 47200) * u ^ 21500 * u ^ 25602 :=
    mul_nonneg (mul_nonneg hO1 (by positivity)) hU25
  have hS1 : 0 ≤ (q - p + 2 * u ^ 95) * (C₂ * 4 ^ 301 * u ^ 15100) :=
    mul_nonneg hlen (by positivity)
  have hY1 : (0 : ℝ) ≤ 1 / u ^ 15198 := by positivity
  have hOsc0 := dualOffDiagOscConstV_nonneg 500 hC₁ (x := u ^ 100) (by positivity)
    (by positivity) h4 hpq (V := u ^ 5) (by positivity)
  have hSh0 := dualOffDiagShiftConst_nonneg 150 (C := C₂) (d := d) (x := u ^ 100) hC₂
    (by positivity) (by positivity) h4 hpq
  have hP1 : 0 ≤ dualOffDiagOscConstV 500 C₁ (u ^ 100) p q (u ^ 95) (u ^ 5)
      * ((h : ℝ) * k) ^ (((500 : ℕ) : ℝ) / 2 - 1 / 2 + d) := mul_nonneg hOsc0 hsk
  have hP2 : 0 ≤ dualOffDiagShiftConst 150 C₂ d (u ^ 100) p q (u ^ 95)
      * ((h : ℝ) * k) ^ (-(1 / 2 - d)) := mul_nonneg hSh0 hsk'
  -- the split bound and the large-power facts
  have hb := hsplit d (u ^ 100) p q (u ^ 95) (u ^ 102) (u ^ 5) h k hd (by linarith only [hd8])
    (by positivity) (by positivity) h4 hpq (by positivity) (by positivity) hV hh0 hk0
  have e1 : ((h : ℝ) * k) ^ (((500 : ℕ) : ℝ) / 2 - 1 / 2 + d) ≤ u ^ 21500 := by
    have := mul_cast_rpow_le_u_pow_of_le hu1 hN hh hk (s := ((500 : ℕ) : ℝ) / 2 - 1 / 2 + d) 250
      (by push_cast; linarith only [hd8])
    rwa [show 2 * 43 * 250 = 21500 by norm_num] at this
  have e2 : (u ^ 102) ^ (((500 : ℕ) : ℝ) / 2 + 1) = u ^ 25602 := by
    rw [show (((500 : ℕ) : ℝ) / 2 + 1) = ((251 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ← pow_mul]
  have e4 : (u ^ 102) ^ (-(((150 : ℕ) : ℝ) - 1)) = 1 / u ^ 15198 := by
    rw [show (-(((150 : ℕ) : ℝ) - 1)) = -((149 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (by positivity), Real.rpow_natCast, ← pow_mul, one_div]
  rw [e2, e4] at hb
  refine hb.trans ?_
  have hosc := dualOffDiagOscConstV_le_param_far hu hp hpq hq hC₁
  have hsh := dualOffDiagShiftConst_le_param_far hd hd8 hu1 hp hpq hq hC₂
  calc dualOffDiagOscConstV 500 C₁ (u ^ 100) p q (u ^ 95) (u ^ 5)
          * ((h : ℝ) * k) ^ (((500 : ℕ) : ℝ) / 2 - 1 / 2 + d) * u ^ 25602
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
        + dualOffDiagShiftConst 150 C₂ d (u ^ 100) p q (u ^ 95) * ((h : ℝ) * k) ^ (-(1 / 2 - d))
          * (1 / u ^ 15198) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2
      ≤ ((q - p + 2 * u ^ 95) * (oscStarFar C₁ / u ^ 47200)) * u ^ 21500 * u ^ 25602
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ))) ^ 2
        + ((q - p + 2 * u ^ 95) * (C₂ * 4 ^ 301 * u ^ 15100)) * 1
          * (1 / u ^ 15198) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2 :=
        add_le_add
          (mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul hosc e1 hsk hO1) hU25) e5 hZ1 hO3)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul hsh e3 hsk' hS1) hY1) hZ2)
    _ = (q - p + 2 * u ^ 95) * (dualStarFar C₁ C₂ / u ^ 98) := by
        unfold dualStarFar
        exact dualFar_algebra hu0 _ _ _ _ _

/-! ## The pair error for mollifiers up to `u^43` -/

/-- The absolute pair constant with the far envelopes. -/
def pairStarFar (CA C₁ C₂ K₁ : ℝ) : ℝ :=
  blockWindowConst 100 * CA * 2 ^ 100 * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2
    + dualStarFar C₁ C₂ + K₁ + 576 * Real.exp 1

theorem pairStarFar_nonneg {CA C₁ C₂ K₁ : ℝ} (hCA : 0 ≤ CA) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hK₁ : 0 ≤ K₁) : 0 ≤ pairStarFar CA C₁ C₂ K₁ := by
  unfold pairStarFar
  have := dualStarFar_nonneg hC₁ hC₂
  have := blockWindowConst_nonneg 100
  positivity

/-- **The pair error with the block parameters, mollifiers up to `u^43`.** -/
theorem norm_pairError_le_param_far {d u p q : ℝ} (hd : 0 < d) (hd20 : d ≤ 1 / 20)
    (hu : 2 ≤ u) (hp : p = u ^ 100) (hpq : p ≤ q) (hq : q ≤ 2 * u ^ 100) {N h k : ℕ}
    (hN : (N : ℝ) ≤ u ^ 43) (hh : h ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N)
    {CA C₁ C₂ K₁ K₂ : ℝ} (hCA0 : 0 ≤ CA)
    (hCA : ∀ {y : ℝ}, 0 < y → ‖smoothAFECutoff y‖ ≤ CA * y ^ (-(51 : ℝ)))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : ∀ (d x p q η Y₀ V : ℝ) (h k : ℕ), 0 < d → d ≤ 1 / 4 →
      0 < x → 0 < η → 4 ≤ p - η → p ≤ q → 0 < Y₀ → 0 ≤ V → 2 * V ≤ p - η → 0 < h → 0 < k →
      ∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P
        ≤ dualOffDiagOscConstV 500 C₁ x p q η V
              * ((h : ℝ) * k) ^ (((500 : ℕ) : ℝ) / 2 - 1 / 2 + d)
              * Y₀ ^ (((500 : ℕ) : ℝ) / 2 + 1) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
          + dualOffDiagShiftConst 150 C₂ d x p q η * ((h : ℝ) * k) ^ (-(1 / 2 - d))
              * Y₀ ^ (-(((150 : ℕ) : ℝ) - 1)) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2)
    (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hK₁ : ∀ σ₀ c x : ℝ, 9 / 20 ≤ σ₀ → σ₀ ≤ 1 / 2 → 0 < c → 0 < x →
      ‖smoothLeft σ₀ c x‖ ≤ K₁ * (x / c) ^ (-farDepth 3))
    (hK₂ : ∀ d c x τ : ℝ, 0 < d → d ≤ 1 / 20 → 0 < c → 0 < x → 1 ≤ c * x → 4 ≤ |τ| →
      ‖dualLeft d c x τ‖ ≤ K₂ * (c * x) ^ farDepth 3 * (1 + |τ|) ^ (-(2 * farDepth 3 - 2 * d))) :
    ‖pairError d (u ^ 100) p q (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
      ≤ (q - p + 2 * u ^ 95)
        * ((pairStarFar CA C₁ C₂ K₁ + 2 ^ 14 * K₂ * (1 + (p - u ^ 95)) ^ (2 * d)) / u ^ 98) := by
  rw [farDepth_three] at hK₁ hK₂
  have hd8 : d ≤ 1 / 8 := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hh0 : 0 < h := (Finset.mem_Icc.mp hh).1
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  obtain ⟨hg, hh', hk', hcop, hhg, hkg⟩ := gcd_facts hh0 hk0
  have h95 : u ^ 95 ≤ u ^ 100 / 2 := by
    have h5 : 2 ≤ u ^ 5 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 5)
    have : u ^ 100 = u ^ 95 * u ^ 5 := by ring
    rw [this]
    nlinarith [pow_pos hu0 95]
  have hL : u ^ 100 / 2 ≤ p - u ^ 95 := by rw [hp]; linarith
  have h4 : (4 : ℝ) ≤ p - u ^ 95 := by
    have : (2 : ℝ) ^ 100 ≤ u ^ 100 := pow_le_pow_left₀ (by norm_num) hu 100
    have h2 : (8 : ℝ) ≤ u ^ 100 / 2 := by
      have : (16 : ℝ) ≤ (2 : ℝ) ^ 100 := by norm_num
      linarith
    linarith
  have hlen : 0 ≤ q - p + 2 * u ^ 95 := by
    have := pow_pos hu0 95
    linarith
  have hx1 : (1 : ℝ) ≤ u ^ 100 := one_le_pow₀ hu1
  -- the reduced product
  have hcpos : (0 : ℝ) < ((reducedProd h k : ℕ) : ℝ) := by linarith [one_le_reducedProd hh0 hk0]
  have hc1 := one_le_reducedProd hh0 hk0
  have hcu : ((reducedProd h k : ℕ) : ℝ) ≤ u ^ 86 :=
    (reducedProd_le h k).trans (mul_le_u_pow_of_le hu1 hN hh hk)
  have hcx : 1 ≤ ((reducedProd h k : ℕ) : ℝ) * u ^ 100 := by nlinarith
  have hred : ((h / Nat.gcd h k) * (k / Nat.gcd h k) : ℕ) = reducedProd h k := rfl
  have hbound := norm_pairError_le_gen hd hd8 hx1 (by positivity) h4 hpq hg hh' hk' hhg hkg
    hK₁0 hK₂0 (b := 2 * (7 : ℝ) - 2 * d) (by linarith)
    (hK₁ (1 / 2 - d) _ (u ^ 100) (by linarith) (by linarith) (by rw [hred]; exact hcpos)
      (by positivity))
    (fun τ hτ => hK₂ d _ (u ^ 100) τ hd hd20 (by rw [hred]; exact hcpos) (by positivity)
      (by rw [hred]; exact hcx) hτ)
  rw [hred] at hbound
  refine hbound.trans ?_
  -- the pieces
  have e1 := tsum_directOffDiagTerm_le_param_far hd hd8 hu1 hpq hN hh hk hCA0 hCA
  have e2 := tsum_dualOffDiagTerm_le_param_far hd hd8 hu hp hpq hq hN hh hk hC₁ hC₂ hsplit
  have e3 : ((h : ℝ) * k) ^ (-(1 / 2 - d)) ≤ 1 :=
    mul_cast_rpow_neg_le_one hh0 hk0 (by linarith only [hd8])
  have e4 : ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 - d)) ≤ 1 := by
    calc ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 - d)) ≤ ((reducedProd h k : ℕ) : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hc1 (by linarith only [hd8])
      _ = 1 := Real.rpow_zero _
  have e5 : ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 + d)) ≤ 1 := by
    calc ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 + d)) ≤ ((reducedProd h k : ℕ) : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hc1 (by linarith only [hd])
      _ = 1 := Real.rpow_zero _
  have e6 := rpow_x_div_c_le_far hu1 hc1 hcu
  have e7 := rpow_c_mul_x_le_far hu1 hcpos.le hcu
  have e8 := rpow_one_add_L_le_far hu1 hL d
  have e9 := exp_neg_sq_le_param hu1 hL
  have hZ := sq_nonneg (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ)))
  have hbw := blockWindowConst_nonneg 100
  have hDS := dualStarFar_nonneg hC₁ hC₂
  have hLpow : 0 ≤ (1 + (p - u ^ 95)) ^ (2 * d) := Real.rpow_nonneg (by linarith only [h4]) _
  have hps := pairStarFar_nonneg hCA0 hC₁ hC₂ hK₁0
  set W : ℝ := q - p + 2 * u ^ 95 with hW
  -- assemble
  calc _ ≤ W
        * ((blockWindowConst 100 * CA * 2 ^ 100
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2) / u ^ 100)
        + W * (dualStarFar C₁ C₂ / u ^ 98)
        + 1 * (1 * (K₁ * (1 / u ^ 98)) * W
            + 1 * (W * (K₂ * u ^ 1302
              * ((2 ^ 14 / u ^ 1400) * (1 + (p - u ^ 95)) ^ (2 * d)))))
        + W * (1 * (18 * Real.exp 1 * u ^ 100 * (32 / u ^ 400))) := by
        gcongr
    _ = W
        * ((blockWindowConst 100 * CA * 2 ^ 100
            * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2) * (1 / u ^ 100)
          + dualStarFar C₁ C₂ * (1 / u ^ 98) + K₁ * (1 / u ^ 98)
          + 2 ^ 14 * K₂ * (1 + (p - u ^ 95)) ^ (2 * d) * (u ^ 1302 / u ^ 1400)
          + 576 * Real.exp 1 * (u ^ 100 / u ^ 400)) := by
        field_simp
        try ring
    _ ≤ W
        * ((blockWindowConst 100 * CA * 2 ^ 100
            * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2) * (1 / u ^ 98)
          + dualStarFar C₁ C₂ * (1 / u ^ 98) + K₁ * (1 / u ^ 98)
          + 2 ^ 14 * K₂ * (1 + (p - u ^ 95)) ^ (2 * d) * (1 / u ^ 98)
          + 576 * Real.exp 1 * (1 / u ^ 98)) := by
        have f1 : 1 / u ^ 100 ≤ 1 / u ^ 98 := one_div_u_pow_le hu1 (by norm_num)
        have f3 : u ^ 1302 / u ^ 1400 = 1 / u ^ 98 := by field_simp; try ring
        have f4 : u ^ 100 / u ^ 400 ≤ 1 / u ^ 98 := by
          rw [show u ^ 100 / u ^ 400 = 1 / u ^ 300 by field_simp; try ring]
          exact one_div_u_pow_le hu1 (by norm_num)
        rw [f3]
        gcongr
    _ = W
        * ((pairStarFar CA C₁ C₂ K₁ + 2 ^ 14 * K₂ * (1 + (p - u ^ 95)) ^ (2 * d)) / u ^ 98) := by
        unfold pairStarFar
        ring

end RHTower.ZetaGateProductAFE

end

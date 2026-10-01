import GaloisForLFunctions.RHTower.ZetaGateDeepLeftLine
import GaloisForLFunctions.RHTower.ZetaGateProductAFEHighBlockPieces

/-!
# The pair error of the product approximate functional equation for mollifiers up to `u^13`

With the left-line remainders on `Re w = −9/20` (`ZetaGateDeepLeftLine`) the pair error of the
block twisted moment with `x = u^100`, window taper `η = u^95`, block start `p = u^100` and
coefficients up to `N ≤ u^13` is at most `(q − p + 2u^95)(pairStar + 2K₂(1+(p−u^95))^{2d})/u^33`
(`norm_pairError_le_param_deep`):

* the smoothed-diagonal remainder gives `K₁(x/c)^{−9/20} ≤ K₁ u^{−33}` for `c ≤ u^26`;
* the dual-diagonal remainder gives `K₂(cx)^{9/20}(1+L)^{−(9/10−2d)} ≤ 2K₂ u^{57−90}(1+L)^{2d}`;
* the direct and dual off-diagonal sums, with `(hk)^{19} ≤ u^{494}` and `(hk)^{10} ≤ u^{260}`, are
  `O(u^{−1116})` and `O(u^{−130})`; the residue term is `O(u^{−300})`.

Summed over the `N² ≤ u^26` pairs the error is `O(u^{−7})` per unit window mass.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset Filter
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-! ## Sizes of the pair parameters -/

theorem mul_le_u_pow_of_le {u : ℝ} (hu : 1 ≤ u) {N h k m : ℕ} (hN : (N : ℝ) ≤ u ^ m)
    (hh : h ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) :
    (h : ℝ) * k ≤ u ^ (2 * m) := by
  have hh' : (h : ℝ) ≤ u ^ m := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hh).2) hN
  have hk' : (k : ℝ) ≤ u ^ m := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hk).2) hN
  calc (h : ℝ) * k ≤ u ^ m * u ^ m := mul_le_mul hh' hk' (Nat.cast_nonneg _) (by positivity)
    _ = u ^ (2 * m) := by ring

theorem mul_cast_rpow_le_u_pow_of_le {u : ℝ} (hu : 1 ≤ u) {N h k m : ℕ} (hN : (N : ℝ) ≤ u ^ m)
    (hh : h ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) {s : ℝ} (n : ℕ) (hs : s ≤ n) :
    ((h : ℝ) * k) ^ s ≤ u ^ (2 * m * n) := by
  have h1 := one_le_mul_cast (Finset.mem_Icc.mp hh).1 (Finset.mem_Icc.mp hk).1
  calc ((h : ℝ) * k) ^ s ≤ ((h : ℝ) * k) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hs
    _ = ((h : ℝ) * k) ^ n := Real.rpow_natCast _ n
    _ ≤ (u ^ (2 * m)) ^ n := pow_le_pow_left₀ (by positivity) (mul_le_u_pow_of_le hu hN hh hk) n
    _ = u ^ (2 * m * n) := by rw [← pow_mul]

/-- `(x/c)^{−9/20} ≤ 1/u^{33}` for `x = u^{100}`, `1 ≤ c ≤ u^{26}`. -/
theorem rpow_x_div_c_le_deep {u c : ℝ} (hu : 1 ≤ u) (hc1 : 1 ≤ c) (hc : c ≤ u ^ 26) :
    (u ^ 100 / c) ^ (-(9 / 20 : ℝ)) ≤ 1 / u ^ 33 := by
  have hu0 : 0 < u := by linarith
  have h1 : u ^ 74 ≤ u ^ 100 / c := by
    rw [le_div_iff₀ (by linarith)]
    calc u ^ 74 * c ≤ u ^ 74 * u ^ 26 := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = u ^ 100 := by ring
  calc (u ^ 100 / c) ^ (-(9 / 20 : ℝ)) ≤ (u ^ 74) ^ (-(9 / 20 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
    _ = u ^ (-(333 / 10 : ℝ)) := by
        rw [← Real.rpow_natCast u 74, ← Real.rpow_mul hu0.le]
        norm_num
    _ ≤ u ^ (-(33 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
    _ = 1 / u ^ 33 := by
        rw [Real.rpow_neg hu0.le, one_div]
        norm_cast

/-- `(c x)^{9/20} ≤ u^{57}` for `x = u^{100}`, `0 ≤ c ≤ u^{26}`. -/
theorem rpow_c_mul_x_le_deep {u c : ℝ} (hu : 1 ≤ u) (hc0 : 0 ≤ c) (hc : c ≤ u ^ 26) :
    (c * u ^ 100) ^ (9 / 20 : ℝ) ≤ u ^ 57 := by
  have hu0 : 0 < u := by linarith
  calc (c * u ^ 100) ^ (9 / 20 : ℝ) ≤ (u ^ 26 * u ^ 100) ^ (9 / 20 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right hc (by positivity))
          (by norm_num)
    _ = u ^ (567 / 10 : ℝ) := by
        rw [← pow_add, ← Real.rpow_natCast u (26 + 100), ← Real.rpow_mul hu0.le]
        norm_num
    _ ≤ u ^ (57 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
    _ = u ^ 57 := by norm_cast

/-- `(1+L)^{−(9/10−2d)} ≤ (2/u^{90})(1+L)^{2d}` for `L ≥ u^{100}/2`. -/
theorem rpow_one_add_L_le_deep {u L : ℝ} (hu : 1 ≤ u) (hL : u ^ 100 / 2 ≤ L) (d : ℝ) :
    (1 + L) ^ (-(9 / 10 - 2 * d)) ≤ (2 / u ^ 90) * (1 + L) ^ (2 * d) := by
  have hu0 : 0 < u := by linarith
  have hL0 : 0 < 1 + L := by
    have : 0 < u ^ 100 / 2 := by positivity
    linarith
  have hsplit : (1 + L) ^ (-(9 / 10 - 2 * d)) = (1 + L) ^ (-(9 / 10 : ℝ)) * (1 + L) ^ (2 * d) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  rw [hsplit]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hL0.le _)
  have hge : u ^ 100 / 2 ≤ 1 + L := by linarith
  have hpow : (u ^ 100 / 2) ^ (-(9 / 10 : ℝ)) = 2 ^ (9 / 10 : ℝ) * u ^ (-(90 : ℝ)) := by
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast u 100,
      ← Real.rpow_mul hu0.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
    norm_num
    ring
  calc (1 + L) ^ (-(9 / 10 : ℝ)) ≤ (u ^ 100 / 2) ^ (-(9 / 10 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hge (by norm_num)
    _ = 2 ^ (9 / 10 : ℝ) * u ^ (-(90 : ℝ)) := hpow
    _ ≤ 2 * u ^ (-(90 : ℝ)) := by
        have h2 : (2 : ℝ) ^ (9 / 10 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        rw [Real.rpow_one] at h2
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 2 / u ^ 90 := by
        rw [Real.rpow_neg hu0.le, div_eq_mul_inv]
        norm_cast

/-! ## The window integral of the dual remainder -/

theorem norm_integral_window_dualLeft_le_deep {d c x p q η : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hc : 0 < c) (hx : 0 < x) (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) {K₂ : ℝ} (hK₂0 : 0 ≤ K₂)
    (hK₂ : ∀ τ : ℝ, ‖dualLeft d c x τ‖ ≤ K₂ * (c * x) ^ (9 / 20 : ℝ) * (1 + |τ|) ^ (-(9 / 10 - 2 * d))) :
    ‖∫ t, blockWindowC p q η t * dualLeft d c x t‖
      ≤ (q - p + 2 * η) * (K₂ * (c * x) ^ (9 / 20 : ℝ) * (1 + (p - η)) ^ (-(9 / 10 - 2 * d))) := by
  have hsub : Set.Icc (p - η) (q + η) ⊆ Set.Icc (-(q + η)) (q + η) := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  set M : ℝ := K₂ * (c * x) ^ (9 / 20 : ℝ) * (1 + (p - η)) ^ (-(9 / 10 - 2 * d)) with hM
  have hpη : 0 < 1 + (p - η) := by linarith
  have hM0 : 0 ≤ M := by positivity
  have hint : Integrable (fun t => blockWindowC p q η t * dualLeft d c x t) :=
    integrable_window_mul hη ((continuousOn_dualLeft hd hd8 hc hx (q + η)).mono hsub)
  have hpt : ∀ t, ‖blockWindowC p q η t * dualLeft d c x t‖ ≤ ‖blockWindowC p q η t‖ * M := by
    intro t
    rw [norm_mul]
    by_cases ht : t ∈ Set.Icc (p - η) (q + η)
    · refine mul_le_mul_of_nonneg_left ((hK₂ t).trans ?_) (norm_nonneg _)
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


/-- **The pair error bound with the deep left-line remainders.** -/
theorem norm_pairError_le_deep {d x p q η : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hx1 : 1 ≤ x) (hη : 0 < η)
    (hL : 4 ≤ p - η) (hpq : p ≤ q) {g h' k' h k : ℕ} (hg : 0 < g) (hh' : 0 < h') (hk' : 0 < k')
    (hhg : h = g * h') (hkg : k = g * k') {K₁ K₂ : ℝ} (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hK₁ : ‖smoothLeft (1 / 2 - d) ((h' * k' : ℕ) : ℝ) x‖
      ≤ K₁ * (x / ((h' * k' : ℕ) : ℝ)) ^ (-(9 / 20 : ℝ)))
    (hK₂ : ∀ τ : ℝ, ‖dualLeft d ((h' * k' : ℕ) : ℝ) x τ‖
      ≤ K₂ * (((h' * k' : ℕ) : ℝ) * x) ^ (9 / 20 : ℝ) * (1 + |τ|) ^ (-(9 / 10 - 2 * d))) :
    ‖pairError d x p q η h' k' h k‖
      ≤ (∑' P : ℕ × ℕ, directOffDiagTerm (1 / 2 - d) x p q η h k P)
        + (∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P)
        + ((h : ℝ) * k) ^ (-(1 / 2 - d))
          * (((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 - d))
              * (K₁ * (x / ((h' * k' : ℕ) : ℝ)) ^ (-(9 / 20 : ℝ))) * (q - p + 2 * η)
            + ((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 + d))
              * ((q - p + 2 * η) * (K₂ * (((h' * k' : ℕ) : ℝ) * x) ^ (9 / 20 : ℝ)
                * (1 + (p - η)) ^ (-(9 / 10 - 2 * d)))))
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
              * (K₁ * (x / ((h' * k' : ℕ) : ℝ)) ^ (-(9 / 20 : ℝ))) * (q - p + 2 * η)
            + ((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 + d))
              * ((q - p + 2 * η) * (K₂ * (((h' * k' : ℕ) : ℝ) * x) ^ (9 / 20 : ℝ)
                * (1 + (p - η)) ^ (-(9 / 10 - 2 * d))))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hK₁ (by positivity))
        (norm_integral_blockWindowC_le hη hpq) (norm_nonneg _) (by positivity)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left
        (norm_integral_window_dualLeft_le_deep hd hd8 hc hx hη hL hpq hK₂0 hK₂) (by positivity)
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

/-! ## The off-diagonal sums for mollifiers up to `u^13` -/

theorem tsum_directOffDiagTerm_le_param_deep {d u p q : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hu : 1 ≤ u)
    (hpq : p ≤ q) {N h k : ℕ} (hN : (N : ℝ) ≤ u ^ 13) (hh : h ∈ Finset.Icc 1 N)
    (hk : k ∈ Finset.Icc 1 N) {CA : ℝ} (hCA0 : 0 ≤ CA)
    (hCA : ∀ {y : ℝ}, 0 < y → ‖smoothAFECutoff y‖ ≤ CA * y ^ (-(20 : ℝ))) :
    ∑' P : ℕ × ℕ, directOffDiagTerm (1 / 2 - d) (u ^ 100) p q (u ^ 95) h k P
      ≤ (q - p + 2 * u ^ 95)
        * ((blockWindowConst 38 * CA * 2 ^ 38
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2) / u ^ 1116) := by
  have hh0 : 0 < h := (Finset.mem_Icc.mp hh).1
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  have hu0 : 0 < u := by linarith
  have hbnd := tsum_directOffDiagTerm_le 38 hCA0 hCA (σ₀ := 1 / 2 - d) (x := u ^ 100) (p := p)
    (q := q) (η := u ^ 95) (by push_cast; linarith) (by positivity) (by positivity) hpq hh0 hk0
  have h19 : ((38 : ℕ) : ℝ) / 2 = 19 := by norm_num
  rw [h19] at hbnd
  refine hbnd.trans ?_
  have e1 : ((h : ℝ) * k) ^ (19 - (1 / 2 - d)) ≤ u ^ 494 := by
    have := mul_cast_rpow_le_u_pow_of_le hu hN hh hk (s := 19 - (1 / 2 - d)) 19 (by push_cast; linarith)
    simpa using this
  have hZ0 := tsum_succ_rpow_neg_nonneg (20 + (1 / 2 - d) - 19)
  have e2 : (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(20 + (1 / 2 - d) - 19))) ^ 2
      ≤ (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hZ0 (tsum_succ_rpow_neg_le (by norm_num) (by linarith)) 2
  have hD0 : 0 ≤ directOffDiagConst 38 CA 20 (u ^ 100) p q (u ^ 95) :=
    directOffDiagConst_nonneg 38 hCA0 (by positivity) (by positivity) hpq
  have hlen : 0 ≤ q - p + 2 * u ^ 95 := by positivity
  calc directOffDiagConst 38 CA 20 (u ^ 100) p q (u ^ 95) * ((h : ℝ) * k) ^ (19 - (1 / 2 - d))
        * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(20 + (1 / 2 - d) - 19))) ^ 2
      ≤ directOffDiagConst 38 CA 20 (u ^ 100) p q (u ^ 95) * u ^ 494
        * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2 := by
        gcongr
    _ = (q - p + 2 * u ^ 95)
        * ((blockWindowConst 38 * CA * 2 ^ 38
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2) / u ^ 1116) := by
        unfold directOffDiagConst
        rw [show (u ^ 100) ^ (20 : ℝ) = u ^ 2000 by
          rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul]]
        field_simp
        try ring


theorem tsum_dualOffDiagTerm_le_param_deep {d u p q : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hu : 2 ≤ u)
    (hp : p = u ^ 100) (hpq : p ≤ q) (hq : q ≤ 2 * u ^ 100) {N h k : ℕ} (hN : (N : ℝ) ≤ u ^ 13)
    (hh : h ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : ∀ (d x p q η Y₀ V : ℝ) (h k : ℕ), 0 < d → d ≤ 1 / 4 →
      0 < x → 0 < η → 4 ≤ p - η → p ≤ q → 0 < Y₀ → 0 ≤ V → 2 * V ≤ p - η → 0 < h → 0 < k →
      ∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P
        ≤ dualOffDiagOscConstV 20 C₁ x p q η V * ((h : ℝ) * k) ^ (((20 : ℕ) : ℝ) / 2 - 1 / 2 + d)
              * Y₀ ^ (((20 : ℕ) : ℝ) / 2 + 1) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
          + dualOffDiagShiftConst 40 C₂ d x p q η * ((h : ℝ) * k) ^ (-(1 / 2 - d))
              * Y₀ ^ (-(((40 : ℕ) : ℝ) - 1)) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2) :
    ∑' P : ℕ × ℕ, dualOffDiagTerm d (u ^ 100) p q (u ^ 95) h k P
      ≤ (q - p + 2 * u ^ 95) * (dualStar C₁ C₂ / u ^ 130) := by
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hh0 : 0 < h := (Finset.mem_Icc.mp hh).1
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
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
  have hV : 2 * u ^ 5 ≤ p - u ^ 95 := by
    have h5 : u ^ 5 ≤ u ^ 100 / 4 := by
      have : u ^ 100 = u ^ 5 * u ^ 95 := by ring
      have h95' : (4 : ℝ) ≤ u ^ 95 :=
        le_trans (by norm_num) (le_trans (pow_le_pow_left₀ (by norm_num) hu 95) le_rfl)
      rw [this]
      nlinarith [pow_pos hu0 5]
    linarith
  have hlen : 0 ≤ q - p + 2 * u ^ 95 := by
    have := pow_pos hu0 95
    linarith
  have hb := hsplit d (u ^ 100) p q (u ^ 95) (u ^ 110) (u ^ 5) h k hd (by linarith)
    (by positivity) (by positivity) h4 hpq (by positivity) (by positivity) hV hh0 hk0
  refine hb.trans ?_
  have hOsc := dualOffDiagOscConstV_le_param hu hp hpq hq hC₁
  have hSh := dualOffDiagShiftConst_le_param hd hd8 hu1 hp hpq hq hC₂
  have hOsc0 := dualOffDiagOscConstV_nonneg 20 hC₁ (x := u ^ 100) (by positivity) (by positivity)
    h4 hpq (V := u ^ 5) (by positivity)
  have hSh0 := dualOffDiagShiftConst_nonneg 40 (C := C₂) (d := d) (x := u ^ 100) hC₂ (by positivity)
    (by positivity) h4 hpq
  have e1 : ((h : ℝ) * k) ^ (((20 : ℕ) : ℝ) / 2 - 1 / 2 + d) ≤ u ^ 260 := by
    have := mul_cast_rpow_le_u_pow_of_le hu1 hN hh hk (s := ((20 : ℕ) : ℝ) / 2 - 1 / 2 + d) 10
      (by push_cast; linarith)
    simpa using this
  have e2 : (u ^ 110) ^ (((20 : ℕ) : ℝ) / 2 + 1) = u ^ 1210 := by
    rw [show (((20 : ℕ) : ℝ) / 2 + 1) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul]
    try norm_num
  have e3 : ((h : ℝ) * k) ^ (-(1 / 2 - d)) ≤ 1 := mul_cast_rpow_neg_le_one hh0 hk0 (by linarith)
  have e4 : (u ^ 110) ^ (-(((40 : ℕ) : ℝ) - 1)) = 1 / u ^ 4290 := by
    rw [show (-(((40 : ℕ) : ℝ) - 1)) = -((39 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_natCast, ← pow_mul]
    norm_num
  have hZ0 := tsum_succ_rpow_neg_nonneg (5 / 2 + d)
  have e5 : (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
      ≤ (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hZ0 (tsum_succ_rpow_neg_le (by norm_num) (by linarith)) 2
  have hZ2 := sq_nonneg (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ)))
  have hZ5 := sq_nonneg (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
  have hos := oscStar_nonneg hC₁
  rw [e2, e4]
  set W : ℝ := q - p + 2 * u ^ 95 with hW
  calc dualOffDiagOscConstV 20 C₁ (u ^ 100) p q (u ^ 95) (u ^ 5)
          * ((h : ℝ) * k) ^ (((20 : ℕ) : ℝ) / 2 - 1 / 2 + d) * u ^ 1210
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
        + dualOffDiagShiftConst 40 C₂ d (u ^ 100) p q (u ^ 95) * ((h : ℝ) * k) ^ (-(1 / 2 - d))
          * (1 / u ^ 4290) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2
      ≤ ((q - p + 2 * u ^ 95) * (oscStar C₁ / u ^ 1600)) * u ^ 260 * u ^ 1210
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ))) ^ 2
        + ((q - p + 2 * u ^ 95) * (C₂ * 4 ^ 81 * u ^ 4100)) * 1
          * (1 / u ^ 4290) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2 := by
        gcongr
    _ = W * (oscStar C₁ * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ))) ^ 2
          * (u ^ 260 * u ^ 1210 / u ^ 1600)
        + C₂ * 4 ^ 81 * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2 * (u ^ 4100 / u ^ 4290)) := by
        field_simp
        try ring
    _ ≤ W * (oscStar C₁ * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ))) ^ 2
          * (1 / u ^ 130)
        + C₂ * 4 ^ 81 * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2 * (1 / u ^ 130)) := by
        have f1 : u ^ 260 * u ^ 1210 / u ^ 1600 = 1 / u ^ 130 := by
          field_simp
          try ring
        have f2 : u ^ 4100 / u ^ 4290 ≤ 1 / u ^ 130 := by
          rw [show u ^ 4100 / u ^ 4290 = 1 / u ^ 190 by field_simp; try ring]
          exact one_div_u_pow_le hu1 (by norm_num)
        rw [f1]
        gcongr
    _ = W * (dualStar C₁ C₂ / u ^ 130) := by
        unfold dualStar
        ring


/-- **The pair error with the block parameters and the deep left-line remainders.** -/
theorem norm_pairError_le_param_deep {d u p q : ℝ} (hd : 0 < d) (hd20 : d ≤ 1 / 20) (hu : 2 ≤ u)
    (hp : p = u ^ 100) (hpq : p ≤ q) (hq : q ≤ 2 * u ^ 100) {N h k : ℕ} (hN : (N : ℝ) ≤ u ^ 13)
    (hh : h ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) {CA C₁ C₂ K₁ K₂ : ℝ} (hCA0 : 0 ≤ CA)
    (hCA : ∀ {y : ℝ}, 0 < y → ‖smoothAFECutoff y‖ ≤ CA * y ^ (-(20 : ℝ)))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : ∀ (d x p q η Y₀ V : ℝ) (h k : ℕ), 0 < d → d ≤ 1 / 4 →
      0 < x → 0 < η → 4 ≤ p - η → p ≤ q → 0 < Y₀ → 0 ≤ V → 2 * V ≤ p - η → 0 < h → 0 < k →
      ∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P
        ≤ dualOffDiagOscConstV 20 C₁ x p q η V * ((h : ℝ) * k) ^ (((20 : ℕ) : ℝ) / 2 - 1 / 2 + d)
              * Y₀ ^ (((20 : ℕ) : ℝ) / 2 + 1) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
          + dualOffDiagShiftConst 40 C₂ d x p q η * ((h : ℝ) * k) ^ (-(1 / 2 - d))
              * Y₀ ^ (-(((40 : ℕ) : ℝ) - 1)) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2)
    (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hK₁ : ∀ σ₀ c x : ℝ, 9 / 20 ≤ σ₀ → σ₀ ≤ 1 / 2 → 0 < c → 0 < x →
      ‖smoothLeft σ₀ c x‖ ≤ K₁ * (x / c) ^ (-(9 / 20 : ℝ)))
    (hK₂ : ∀ d c x τ : ℝ, 0 < d → d ≤ 1 / 20 → 0 < c → 0 < x →
      ‖dualLeft d c x τ‖ ≤ K₂ * (c * x) ^ (9 / 20 : ℝ) * (1 + |τ|) ^ (-(9 / 10 - 2 * d))) :
    ‖pairError d (u ^ 100) p q (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
      ≤ (q - p + 2 * u ^ 95)
        * ((pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (p - u ^ 95)) ^ (2 * d)) / u ^ 33) := by
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
  have hcu : ((reducedProd h k : ℕ) : ℝ) ≤ u ^ 26 :=
    (reducedProd_le h k).trans (mul_le_u_pow_of_le hu1 hN hh hk)
  have hred : ((h / Nat.gcd h k) * (k / Nat.gcd h k) : ℕ) = reducedProd h k := rfl
  have hbound := norm_pairError_le_deep hd hd8 hx1 (by positivity) h4 hpq hg hh' hk' hhg hkg hK₁0 hK₂0
    (hK₁ (1 / 2 - d) _ (u ^ 100) (by linarith) (by linarith) (by rw [hred]; exact hcpos)
      (by positivity))
    (fun τ => hK₂ d _ (u ^ 100) τ hd hd20 (by rw [hred]; exact hcpos) (by positivity))
  rw [hred] at hbound
  refine hbound.trans ?_
  -- the pieces
  have e1 := tsum_directOffDiagTerm_le_param_deep hd hd8 hu1 hpq hN hh hk hCA0 hCA
  have e2 := tsum_dualOffDiagTerm_le_param_deep hd hd8 hu hp hpq hq hN hh hk hC₁ hC₂ hsplit
  have e3 : ((h : ℝ) * k) ^ (-(1 / 2 - d)) ≤ 1 := mul_cast_rpow_neg_le_one hh0 hk0 (by linarith)
  have e4 : ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 - d)) ≤ 1 := by
    calc ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 - d)) ≤ ((reducedProd h k : ℕ) : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hc1 (by linarith)
      _ = 1 := Real.rpow_zero _
  have e5 : ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 + d)) ≤ 1 := by
    calc ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 + d)) ≤ ((reducedProd h k : ℕ) : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hc1 (by linarith)
      _ = 1 := Real.rpow_zero _
  have e6 := rpow_x_div_c_le_deep hu1 hc1 hcu
  have e7 := rpow_c_mul_x_le_deep hu1 hcpos.le hcu
  have e8 := rpow_one_add_L_le_deep hu1 hL d
  have e9 := exp_neg_sq_le_param hu1 hL
  have hZ := sq_nonneg (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ)))
  have hbw := blockWindowConst_nonneg 38
  have hDS := dualStar_nonneg hC₁ hC₂
  have hLpow : 0 ≤ (1 + (p - u ^ 95)) ^ (2 * d) := Real.rpow_nonneg (by linarith) _
  have hps := pairStar_nonneg hCA0 hC₁ hC₂ hK₁0
  set W : ℝ := q - p + 2 * u ^ 95 with hW
  -- assemble
  calc _ ≤ W
        * ((blockWindowConst 38 * CA * 2 ^ 38
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2) / u ^ 1116)
        + W * (dualStar C₁ C₂ / u ^ 130)
        + 1 * (1 * (K₁ * (1 / u ^ 33)) * W
            + 1 * (W * (K₂ * u ^ 57
              * ((2 / u ^ 90) * (1 + (p - u ^ 95)) ^ (2 * d)))))
        + W * (1 * (18 * Real.exp 1 * u ^ 100 * (32 / u ^ 400))) := by
        gcongr
    _ = W
        * ((blockWindowConst 38 * CA * 2 ^ 38
            * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2) * (1 / u ^ 1116)
          + dualStar C₁ C₂ * (1 / u ^ 130) + K₁ * (1 / u ^ 33)
          + 2 * K₂ * (1 + (p - u ^ 95)) ^ (2 * d) * (u ^ 57 / u ^ 90)
          + 576 * Real.exp 1 * (u ^ 100 / u ^ 400)) := by
        field_simp
        try ring
    _ ≤ W
        * ((blockWindowConst 38 * CA * 2 ^ 38
            * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2) * (1 / u ^ 33)
          + dualStar C₁ C₂ * (1 / u ^ 33) + K₁ * (1 / u ^ 33)
          + 2 * K₂ * (1 + (p - u ^ 95)) ^ (2 * d) * (1 / u ^ 33)
          + 576 * Real.exp 1 * (1 / u ^ 33)) := by
        have f1 : 1 / u ^ 1116 ≤ 1 / u ^ 33 := one_div_u_pow_le hu1 (by norm_num)
        have f2 : 1 / u ^ 130 ≤ 1 / u ^ 33 := one_div_u_pow_le hu1 (by norm_num)
        have f3 : u ^ 57 / u ^ 90 = 1 / u ^ 33 := by field_simp; try ring
        have f4 : u ^ 100 / u ^ 400 ≤ 1 / u ^ 33 := by
          rw [show u ^ 100 / u ^ 400 = 1 / u ^ 300 by field_simp; try ring]
          exact one_div_u_pow_le hu1 (by norm_num)
        rw [f3]
        gcongr
    _ = W
        * ((pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (p - u ^ 95)) ^ (2 * d)) / u ^ 33) := by
        unfold pairStar
        ring

end RHTower.ZetaGateProductAFE

end

import GaloisForLFunctions.HTGeometry.GammaJetShapeRatios

/-!
# The projective boundary shape with integer exponents

Equation (3) of the projective boundary law reads `F(s) = c·Γ(s)^k·s^a·(log s)^b·(1+o(1))` with
`k, a, b ∈ ℤ`.  The corpus's `gammaJetShape` carries natural exponents, which is what a *polynomial*
in the jets produces; a quotient of two such elements — a general element of the field — needs the
integer form, since the exponents subtract.

This file defines that shape, relates it to the natural one, and proves the three dominance limits in
the order of eq. (26): a smaller `Γ`-exponent dominates; at equal `Γ`-exponent a larger `s`-exponent
dominates; at equal `Γ`- and `s`-exponents a larger `log`-exponent dominates.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {σ : ℝ}

/-- The boundary shape of eq. (3) with integer exponents: `Γ^k·s^a·(log s)^b` on a vertical line. -/
noncomputable def gammaShapeZ (σ : ℝ) (k a b : ℤ) (t : ℝ) : ℂ :=
  gammaLine σ t ^ k * (((σ : ℂ) + (t : ℂ) * Complex.I) ^ a * vertLog t ^ b)

theorem eventually_gammaShapeZ_ne_zero (hσ : 0 < σ) (k a b : ℤ) :
    ∀ᶠ t : ℝ in atTop, gammaShapeZ σ k a b t ≠ 0 := by
  filter_upwards [eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ] with t hL hs
  rw [gammaShapeZ]
  exact mul_ne_zero (zpow_ne_zero _ (gammaLine_ne_zero hσ t))
    (mul_ne_zero (zpow_ne_zero _ hs) (zpow_ne_zero _ hL))

/-- The natural-exponent shape is the integer shape at the corresponding exponents. -/
theorem gammaJetShape_eq_gammaShapeZ (u a dP b : ℕ) :
    ∀ᶠ t : ℝ in atTop,
      gammaJetShape σ u a dP b t = gammaShapeZ σ (u : ℤ) ((dP : ℤ) - (b : ℤ)) (a : ℤ) t := by
  filter_upwards [eventually_vertical_ne_zero σ] with t hs
  rw [gammaJetShape, gammaShapeZ, polyJetShape, zpow_sub₀ hs, zpow_natCast, zpow_natCast,
    zpow_natCast, zpow_natCast]
  field_simp

/-- Quotients of integer shapes are integer shapes. -/
theorem gammaShapeZ_div (hσ : 0 < σ) (k₁ a₁ b₁ k₂ a₂ b₂ : ℤ) :
    ∀ᶠ t : ℝ in atTop,
      gammaShapeZ σ k₁ a₁ b₁ t / gammaShapeZ σ k₂ a₂ b₂ t
        = gammaShapeZ σ (k₁ - k₂) (a₁ - a₂) (b₁ - b₂) t := by
  filter_upwards [eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ] with t hL hs
  have hΓ : gammaLine σ t ≠ 0 := gammaLine_ne_zero hσ t
  rw [gammaShapeZ, gammaShapeZ, gammaShapeZ, zpow_sub₀ hΓ, zpow_sub₀ hs, zpow_sub₀ hL]
  field_simp

/-- A function bounded below by `1` and above by a power has polynomial growth at every integer
power. -/
theorem hasPolyGrowthLine_zpow {f : ℝ → ℂ} {C : ℝ} {M : ℕ} (hC : 0 ≤ C)
    (hle : ∀ᶠ t : ℝ in atTop, ‖f t‖ ≤ C * t ^ M) (hge : ∀ᶠ t : ℝ in atTop, 1 ≤ ‖f t‖) (n : ℤ) :
    HasPolyGrowthLine (fun t : ℝ => f t ^ n) := by
  by_cases hn : 0 ≤ n
  · refine ⟨M * n.toNat, C ^ n.toNat, by positivity, ?_⟩
    filter_upwards [hle, hge, eventually_ge_atTop (1 : ℝ)] with t hb hg ht
    have hz : n = (n.toNat : ℤ) := (Int.toNat_of_nonneg hn).symm
    rw [hz, zpow_natCast, norm_pow]
    calc ‖f t‖ ^ n.toNat ≤ (C * t ^ M) ^ n.toNat :=
          pow_le_pow_left₀ (norm_nonneg _) hb _
      _ = C ^ n.toNat * t ^ (M * n.toNat) := by
          rw [mul_pow, ← pow_mul]
  · refine ⟨0, 1, zero_le_one, ?_⟩
    filter_upwards [hge, eventually_ge_atTop (1 : ℝ)] with t hg ht
    have hnorm : ‖f t ^ n‖ = ‖f t‖ ^ n := by rw [norm_zpow]
    rw [hnorm, pow_zero, mul_one]
    calc ‖f t‖ ^ n ≤ ‖f t‖ ^ (0 : ℤ) := zpow_le_zpow_right₀ hg (by omega)
      _ = 1 := zpow_zero _

theorem hasPolyGrowthLine_zpow_vertical (hσ : 0 ≤ σ) (a : ℤ) :
    HasPolyGrowthLine (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ a) := by
  refine hasPolyGrowthLine_zpow (C := 1 + σ) (M := 1) (by linarith) ?_ ?_ a
  · filter_upwards [eventually_norm_vertical_le hσ] with t ht
    simpa using ht
  · exact (tendsto_norm_vertical σ).eventually_ge_atTop 1

theorem hasPolyGrowthLine_zpow_vertLog (b : ℤ) :
    HasPolyGrowthLine (fun t : ℝ => vertLog t ^ b) := by
  refine hasPolyGrowthLine_zpow (C := 1 + Real.pi / 2) (M := 1) (by positivity) ?_ ?_ b
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have h := norm_vertLog_le ht
    have hlog : Real.log t ≤ t := Real.log_le_sub_one_of_pos (by linarith) |>.trans (by linarith)
    have hpi : 0 < Real.pi := Real.pi_pos
    calc ‖vertLog t‖ ≤ Real.log t + Real.pi / 2 := h
      _ ≤ t + (Real.pi / 2) * t := by nlinarith
      _ = (1 + Real.pi / 2) * t ^ 1 := by ring
  · exact tendsto_norm_vertLog.eventually_ge_atTop 1

/-- The product of two functions of polynomial growth has polynomial growth. -/
theorem HasPolyGrowthLine.mul {f g : ℝ → ℂ} (hf : HasPolyGrowthLine f)
    (hg : HasPolyGrowthLine g) : HasPolyGrowthLine (fun t => f t * g t) := by
  obtain ⟨M, C, hC, hfb⟩ := hf
  obtain ⟨N, D, hD, hgb⟩ := hg
  refine ⟨M + N, C * D, by positivity, ?_⟩
  filter_upwards [hfb, hgb, eventually_ge_atTop (0 : ℝ)] with t hf' hg' ht
  calc ‖f t * g t‖ = ‖f t‖ * ‖g t‖ := norm_mul _ _
    _ ≤ (C * t ^ M) * (D * t ^ N) :=
        mul_le_mul hf' hg' (norm_nonneg _) (by positivity)
    _ = C * D * t ^ (M + N) := by rw [pow_add]; ring

/-- A positive power of `Γ` sends the whole shape to zero. -/
theorem tendsto_gammaShapeZ_zero_of_gamma_pos (hσ : 0 < σ) {k : ℤ} (hk : 0 < k) (a b : ℤ) :
    Tendsto (gammaShapeZ σ k a b) atTop (nhds 0) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = (m : ℤ) + 1 :=
    ⟨(k - 1).toNat, by omega⟩
  have hgrow : HasPolyGrowthLine
      (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ a * vertLog t ^ b) :=
    HasPolyGrowthLine.mul (hasPolyGrowthLine_zpow_vertical (le_of_lt hσ) a)
      (hasPolyGrowthLine_zpow_vertLog b)
  have h := tendsto_gammaLine_pow_mul hσ hgrow m
  refine h.congr fun t => ?_
  rw [gammaShapeZ, hm, zpow_add₀ (gammaLine_ne_zero hσ t), zpow_natCast, zpow_one, pow_succ]

/-- At Gamma exponent zero a negative argument exponent sends the shape to zero. -/
theorem tendsto_gammaShapeZ_zero_of_arg_neg (hσ : 0 < σ) {a : ℤ} (ha : a < 0) (b : ℤ) :
    Tendsto (gammaShapeZ σ 0 a b) atTop (nhds 0) := by
  obtain ⟨p, hp⟩ : ∃ p : ℕ, a = -((p : ℤ) + 1) := ⟨(-a - 1).toNat, by omega⟩
  by_cases hb : b ≤ 0
  · -- the logarithm factor is bounded, the argument factor vanishes
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound : ∀ᶠ t : ℝ in atTop,
        ‖gammaShapeZ σ 0 a b t‖ ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ a‖ := by
      filter_upwards [tendsto_norm_vertLog.eventually_ge_atTop 1] with t hL
      have hLb : ‖vertLog t ^ b‖ ≤ 1 := by
        rw [norm_zpow]
        calc ‖vertLog t‖ ^ b ≤ ‖vertLog t‖ ^ (0 : ℤ) := zpow_le_zpow_right₀ hL hb
          _ = 1 := zpow_zero _
      rw [gammaShapeZ, zpow_zero, one_mul, norm_mul]
      calc ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ a‖ * ‖vertLog t ^ b‖
          ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ a‖ * 1 :=
            mul_le_mul_of_nonneg_left hLb (norm_nonneg _)
        _ = ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ a‖ := mul_one _
    have hlim : Tendsto
        (fun t : ℝ => ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ a‖) atTop (nhds 0) := by
      have h1 : Tendsto
          (fun t : ℝ => (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (p + 1))⁻¹) atTop (nhds 0) :=
        ((tendsto_pow_atTop (Nat.succ_ne_zero p)).comp (tendsto_norm_vertical σ)).inv_tendsto_atTop
      refine h1.congr fun t => ?_
      rw [norm_zpow, hp, zpow_neg,
        show ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact squeeze_zero' (by filter_upwards with t using norm_nonneg _) hbound hlim
  · -- a positive power of the logarithm still loses to one power of the argument
    obtain ⟨q, hq⟩ : ∃ q : ℕ, b = (q : ℤ) := ⟨b.toNat, by omega⟩
    have h := tendsto_vertLog_pow_div_vertical_pow (σ := σ) hσ q (p := p + 1) (Nat.succ_pos p)
    refine h.congr fun t => ?_
    rw [gammaShapeZ, zpow_zero, one_mul, hp, hq, zpow_neg,
      show ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      div_eq_mul_inv]
    ring

/-- At Gamma and argument exponent zero a negative logarithm exponent sends the shape to zero. -/
theorem tendsto_gammaShapeZ_zero_of_log_neg {b : ℤ} (hb : b < 0) :
    Tendsto (gammaShapeZ σ 0 0 b) atTop (nhds 0) := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ, b = -((q : ℤ) + 1) := ⟨(-b - 1).toNat, by omega⟩
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun t : ℝ => (‖vertLog t‖ ^ (q + 1))⁻¹) atTop (nhds 0) :=
    (tendsto_pow_atTop (Nat.succ_ne_zero q) |>.comp tendsto_norm_vertLog).inv_tendsto_atTop
  refine hlim.congr fun t => ?_
  rw [gammaShapeZ, zpow_zero, zpow_zero, one_mul, one_mul, norm_zpow, hq, zpow_neg,
    show ((q : ℤ) + 1) = ((q + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

/-- **The dominance order of eq. (26).**  A shape whose datum is strictly subordinate — larger
`Γ`-exponent, or equal `Γ`-exponent and smaller argument exponent, or both equal and smaller
logarithm exponent — vanishes against the dominant one. -/
theorem tendsto_gammaShapeZ_ratio_zero (hσ : 0 < σ) {k₁ a₁ b₁ k₂ a₂ b₂ : ℤ}
    (h : k₂ < k₁ ∨ (k₁ = k₂ ∧ a₁ < a₂) ∨ (k₁ = k₂ ∧ a₁ = a₂ ∧ b₁ < b₂)) :
    Tendsto (fun t : ℝ => gammaShapeZ σ k₁ a₁ b₁ t / gammaShapeZ σ k₂ a₂ b₂ t) atTop (nhds 0) := by
  have hzero : Tendsto (gammaShapeZ σ (k₁ - k₂) (a₁ - a₂) (b₁ - b₂)) atTop (nhds 0) := by
    rcases h with hk | ⟨hk, ha⟩ | ⟨hk, ha, hb⟩
    · exact tendsto_gammaShapeZ_zero_of_gamma_pos hσ (by omega) _ _
    · rw [show k₁ - k₂ = 0 by omega]
      exact tendsto_gammaShapeZ_zero_of_arg_neg hσ (by omega) _
    · rw [show k₁ - k₂ = 0 by omega, show a₁ - a₂ = 0 by omega]
      exact tendsto_gammaShapeZ_zero_of_log_neg (by omega)
  refine hzero.congr' ?_
  filter_upwards [gammaShapeZ_div hσ k₁ a₁ b₁ k₂ a₂ b₂] with t ht
  exact ht.symm

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {σ : ℝ}

/-- Shifting the argument exponent multiplies the shape by that power of the argument. -/
theorem gammaShapeZ_arg_add (k a b Δ : ℤ) :
    ∀ᶠ t : ℝ in atTop,
      gammaShapeZ σ k (a + Δ) b t
        = gammaShapeZ σ k a b t * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ Δ := by
  filter_upwards [eventually_vertical_ne_zero σ] with t hs
  rw [gammaShapeZ, gammaShapeZ, zpow_add₀ hs]
  ring

/-- **A finite family of integer data has a dominant member** in the order of eq. (26): smaller
`Γ`-exponent dominates, then larger argument exponent, then larger logarithm exponent. -/
theorem exists_dominant_shapeZ_index {N : ℕ} (hN : 0 < N) (k a b : Fin N → ℤ) :
    ∃ β : Fin N, ∀ α : Fin N,
      (k α = k β ∧ a α = a β ∧ b α = b β)
        ∨ (k β < k α ∨ (k α = k β ∧ a α < a β) ∨ (k α = k β ∧ a α = a β ∧ b α < b β)) := by
  classical
  have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hN)
  obtain ⟨β, -, hβ⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N))
    (fun α => (toLex (k α, toLex (-a α, -b α)) : ℤ ×ₗ (ℤ ×ₗ ℤ))) hne
  refine ⟨β, fun α => ?_⟩
  have hle := hβ α (Finset.mem_univ α)
  rw [Prod.Lex.le_iff] at hle
  rcases hle with hlt | ⟨heq, hle2⟩
  · have h1 : k β < k α := hlt
    exact Or.inr (Or.inl h1)
  · have h1 : k β = k α := heq
    rw [Prod.Lex.le_iff] at hle2
    rcases hle2 with hlt2 | ⟨heq2, hle3⟩
    · have h2 : -a β < -a α := hlt2
      exact Or.inr (Or.inr (Or.inl ⟨h1.symm, by omega⟩))
    · have h2 : -a β = -a α := heq2
      have h3 : -b β ≤ -b α := hle3
      rcases lt_or_eq_of_le h3 with hlt3 | heq3
      · exact Or.inr (Or.inr (Or.inr ⟨h1.symm, by omega, by omega⟩))
      · exact Or.inl ⟨h1.symm, by omega, by omega⟩

end

end GaloisForLFunctions.HTGeometry

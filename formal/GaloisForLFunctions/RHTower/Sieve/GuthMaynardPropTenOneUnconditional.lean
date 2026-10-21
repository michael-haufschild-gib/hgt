import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropTenOneMajorant
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSevenTwo

set_option autoImplicit false

/-!
# Guth–Maynard Proposition 10.1: `S₃ ⪅ T² |W|^{3/2} + T N |W|^{1/2} E(W)^{1/2}`

Guth–Maynard (arXiv 2405.20552) Proposition 10.1: for a real CGL bump `w`, `0 < ε ≤ 1`,
`2 ≤ T`, `T^ε ≤ N ≤ T` and every `1`-separated `W ⊂ [0, T]`,

`|S₃| = |Σ_{m ∈ ℤ³, m₁m₂m₃ ≠ 0} I_m|
   ≤ C T^{5ε} (T² |W|^{3/2} + T N |W|^{1/2} E(W)^{1/2}) + C T^{-100}`.

Proof. Proposition 7.2 (`prop72`) expands `S₃` into the dyadic block sum of the smoothed cubic
terms `Ĩ_m` with the bumps `innerBump (2 T^{ε/2})`, `outerBump` and `M ≤ T^{1+ε}/N`. The majorant
`f = innerBump 21 · R̃²` of `GuthMaynardPropTenOneMajorant` discharges every data hypothesis of
the assembly `guthMaynard_prop101`: it is continuous, compactly supported, nonnegative, equals
`R̃²` on `[-20, 20]`, has mass `≪ T^{ε/2} |W|`, square mass `≪ T^{ε} E(W)` and Fourier decay
`ξ² |f̂(ξ)| ≤ A₀ T^{5ε/2} T² sup f ≤ A₀ T³ sup f` for `ε ≤ 2/5`. Since `ε` is arbitrary, this is
`S₃ ⪅ T² |W|^{3/2} + T N |W|^{1/2} E(W)^{1/2}`.

The restriction `ε ≤ 1/4` of the core statement is removed by applying it at `min ε (1/4)`.
-/

open MeasureTheory Set
open scoped FourierTransform

namespace RHTower.GuthMaynard

noncomputable section

/-- **Proposition 10.1 for small `ε`.** The `T^{5ε/2}` loss of the Fourier decay must fit under
the `T³` of Proposition 9.1, which forces `ε ≤ 2/5`; `ε ≤ 1/4` is used. -/
theorem prop101_of_le_quarter (w : CGLRealSmoothBump) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    ∃ C, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ), 2 ≤ T → 1 ≤ N → N ≤ T → T ^ ε ≤ N →
      (∀ t ∈ W, t ∈ Icc 0 T) → IsSeparated 1 W →
      ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖
        ≤ C * T ^ (5 * ε) * (T ^ 2 * W.card * √(W.card : ℝ)
            + T * N * √(W.card : ℝ) * √(additiveEnergy W : ℝ)) + C * T ^ (-100 : ℝ) := by
  obtain ⟨C₇, hC₇0, h72⟩ := prop72 w hε (by linarith)
  obtain ⟨A₀, hA₀0, hdecay⟩ := exists_fourier_decay_propTenOneMajorant
  obtain ⟨K, hK0, h101⟩ := guthMaynard_prop101 (δ := ε) hε hA₀0
  obtain ⟨c₇, hc₇⟩ : ∃ c₇, c₇ = max C₇ 1 := ⟨_, rfl⟩
  have hc₇1 : 1 ≤ c₇ := hc₇ ▸ le_max_right _ _
  have hc₇0 : 0 ≤ c₇ := by linarith
  have hC₇c₇ : C₇ ≤ c₇ := hc₇ ▸ le_max_left _ _
  have hwc0 : 0 ≤ windowConstant := windowConstant_nonneg
  have hbase : 0 ≤ c₇ * K *
      (c₇ ^ 2 * (8 * windowConstant) + c₇ * (8 * √windowConstant)) :=
    mul_nonneg (mul_nonneg hc₇0 hK0)
      (add_nonneg (mul_nonneg (sq_nonneg _) (by linarith))
        (mul_nonneg hc₇0 (by positivity)))
  refine ⟨max (c₇ * K * (c₇ ^ 2 * (8 * windowConstant) + c₇ * (8 * √windowConstant))) c₇,
    le_trans hc₇0 (le_max_right _ _), fun T N W hT hN hNT hTεN hW hsep => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨M₁, M, hM₁, hM₁M, hMT, hS⟩ := h72 T N W hT hN hNT hTεN hW hsep
  -- the width `η = T^{ε/2}` of the inner bump
  obtain ⟨η, hηdef⟩ : ∃ η, η = T ^ (ε / 2) := ⟨_, rfl⟩
  rw [← hηdef] at hS
  have hpow : ∀ n : ℕ, η ^ n = T ^ (ε / 2 * (n : ℝ)) := fun n => by
    rw [hηdef, Real.rpow_mul hT0.le, Real.rpow_natCast]
  have hη1 : 1 ≤ η := hηdef ▸ Real.one_le_rpow hT1 (by positivity)
  have hη0 : 0 < η := by linarith
  have hηsq : η ^ 2 = T ^ ε := by rw [hpow 2]; congr 1; push_cast; ring
  have hη10 : η ^ 10 = T ^ (5 * ε) := by rw [hpow 10]; congr 1; push_cast; ring
  -- the smoothing scale `B = NM`
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM₁.trans hM₁M
  have hB1 : (1 : ℝ) ≤ N * M := by nlinarith
  have hNM0 : (0 : ℝ) < N * M := by linarith
  have hNMT : N * (M : ℝ) ≤ T ^ (1 + ε) := by
    rw [le_div_iff₀ hN0] at hMT
    linarith
  have he : T ^ (1 + ε) = η ^ 2 * T := by
    rw [hηsq, Real.rpow_add hT0, Real.rpow_one]; ring
  have hNMη : N * (M : ℝ) ≤ η ^ 2 * T := he ▸ hNMT
  have hNMc₇ : N * (M : ℝ) ≤ c₇ * T ^ (1 + ε) := by
    have hTpos : (0 : ℝ) < T ^ (1 + ε) := by positivity
    nlinarith
  -- the data hypotheses of the assembly
  have hsup0 : 0 ≤ ⨆ x, propTenOneMajorant η (N * M) W x :=
    le_trans (propTenOneMajorant_nonneg hNM0.le W 1)
      (le_ciSup ((continuous_propTenOneMajorant hη0 (N * M) W).bddAbove_range_of_hasCompactSupport
        (hasCompactSupport_propTenOneMajorant η (N * M) W)) 1)
  have hη5 : η ^ 5 ≤ T := by
    rw [hpow 5]
    calc T ^ (ε / 2 * ((5 : ℕ) : ℝ)) ≤ T ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by push_cast; linarith)
      _ = T := Real.rpow_one T
  have hdecT : ∀ ξ : ℝ, ξ ^ 2 * ‖𝓕 (complexify (propTenOneMajorant η (N * M) W)) ξ‖
      ≤ A₀ * T ^ 3 * ⨆ x, propTenOneMajorant η (N * M) W x := by
    intro ξ
    refine (hdecay T η (N * M) W hT1 hη1 hB1 hNMη hW ξ).trans ?_
    calc A₀ * η ^ 5 * T ^ 2 * ⨆ x, propTenOneMajorant η (N * M) W x
        ≤ A₀ * T * T ^ 2 * ⨆ x, propTenOneMajorant η (N * M) W x :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hη5 hA₀0) (sq_nonneg T)) hsup0
      _ = A₀ * T ^ 3 * ⨆ x, propTenOneMajorant η (N * M) W x := by ring
  have hmaj : ∀ u, |u| ≤ 20 →
      smoothedLagSum (innerBump (2 * η)) outerBump N M W u ^ 2
        ≤ propTenOneMajorant η (N * M) W u :=
    fun u hu => smoothedLagSum_sq_le_propTenOneMajorant hη0 hNM0.le W hu
  have hbox : ∀ m ∈ dyadicFrequencyBlock M₁ M, InPropSevenTwoBox M₁ M m :=
    fun _ hm => mem_dyadicFrequencyBlock.mp hm
  have hsum : 0 ≤ (N ^ 2 / M) * ∑ m ∈ dyadicFrequencyBlock M₁ M,
      smoothedCubicTerm (innerBump (2 * η)) outerBump N M W m.1 m.2.1 m.2.2 :=
    mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ => smoothedCubicTerm_nonneg _ _ _ _ _ _ _ _)
  have hS' : ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖
      ≤ c₇ * T ^ ε * (N ^ 2 / M) * ∑ m ∈ dyadicFrequencyBlock M₁ M,
          smoothedCubicTerm (innerBump (2 * η)) outerBump N M W m.1 m.2.1 m.2.2
        + c₇ * T ^ (-100 : ℝ) := by
    have hTε : 0 ≤ T ^ ε := by positivity
    have hT100 : 0 ≤ T ^ (-100 : ℝ) := by positivity
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₇c₇ hTε) hsum
    have h2 := mul_le_mul_of_nonneg_right hC₇c₇ hT100
    simp only [mul_assoc] at hS h1 ⊢
    linarith
  have hmain := h101 ε T N c₇ (8 * η * windowConstant) (64 * η ^ 2 * windowConstant) M₁ M
    (innerBump (2 * η)) outerBump (propTenOneMajorant η (N * M) W) W
    (dyadicFrequencyBlock M₁ M) ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖
    hε.le hT1 hN0 hc₇0 (mul_nonneg (by linarith) hwc0) (mul_nonneg (by positivity) hwc0)
    hM₁ hM₁M hNMc₇ (isSmoothingPair_innerBump_outerBump (by linarith)) hsep hbox
    (continuous_propTenOneMajorant hη0 (N * M) W)
    (hasCompactSupport_propTenOneMajorant η (N * M) W)
    (fun u => propTenOneMajorant_nonneg hNM0.le W u) hmaj hdecT
    (integral_propTenOneMajorant_le hη0 hNM0 hsep) (integral_sq_propTenOneMajorant_le hη0 hNM0 W)
    hS'
  refine hmain.trans ?_
  -- the exponent bookkeeping: `T^{ε/2} · T^ε · (T^ε)³ = η⁹ ≤ η¹⁰ = T^{5ε}`
  have hsqrt : √(64 * η ^ 2 * windowConstant) = 8 * η * √windowConstant := by
    rw [show 64 * η ^ 2 * windowConstant = (8 * η) ^ 2 * windowConstant by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
  have hT5 : (0 : ℝ) ≤ T ^ (5 * ε) := Real.rpow_nonneg hT0.le _
  have hcoef : c₇ * K * (c₇ ^ 2 * (8 * η * windowConstant)
          + c₇ * √(64 * η ^ 2 * windowConstant)) * T ^ ε * (T ^ ε) ^ 3
      ≤ max (c₇ * K * (c₇ ^ 2 * (8 * windowConstant) + c₇ * (8 * √windowConstant))) c₇
        * T ^ (5 * ε) := by
    calc c₇ * K * (c₇ ^ 2 * (8 * η * windowConstant)
            + c₇ * √(64 * η ^ 2 * windowConstant)) * T ^ ε * (T ^ ε) ^ 3
        = c₇ * K * (c₇ ^ 2 * (8 * windowConstant) + c₇ * (8 * √windowConstant)) * η ^ 9 := by
          rw [hsqrt, ← hηsq]; ring
      _ ≤ c₇ * K * (c₇ ^ 2 * (8 * windowConstant) + c₇ * (8 * √windowConstant)) * η ^ 10 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hη1 (by norm_num)) hbase
      _ = c₇ * K * (c₇ ^ 2 * (8 * windowConstant) + c₇ * (8 * √windowConstant))
            * T ^ (5 * ε) := by rw [hη10]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hT5
  have hZ0 : (0 : ℝ) ≤ T ^ 2 * W.card * √(W.card : ℝ)
      + T * N * √(W.card : ℝ) * √(additiveEnergy W : ℝ) :=
    add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg (mul_nonneg hT0.le hN0.le) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  have hT100 : (0 : ℝ) ≤ T ^ (-100 : ℝ) := Real.rpow_nonneg hT0.le _
  have e1 := mul_le_mul_of_nonneg_right hcoef hZ0
  have e2 := mul_le_mul_of_nonneg_right
    (le_max_right (c₇ * K * (c₇ ^ 2 * (8 * windowConstant) + c₇ * (8 * √windowConstant))) c₇)
    hT100
  linarith

/-- **Guth–Maynard Proposition 10.1 (`S₃ ⪅ T² |W|^{3/2} + T N |W|^{1/2} E(W)^{1/2}`).** For a real
CGL bump `w` and every `ε > 0` there is `C ≥ 0` such that for `2 ≤ T`, `1 ≤ N ≤ T`, `T^ε ≤ N` and
every `1`-separated `W ⊂ [0, T]`:
`‖S₃‖ ≤ C T^{5ε} (T² |W|^{3/2} + T N |W|^{1/2} E(W)^{1/2}) + C T^{-100}`. -/
theorem prop101 (w : CGLRealSmoothBump) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ), 2 ≤ T → 1 ≤ N → N ≤ T → T ^ ε ≤ N →
      (∀ t ∈ W, t ∈ Icc 0 T) → IsSeparated 1 W →
      ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖
        ≤ C * T ^ (5 * ε) * (T ^ 2 * W.card * √(W.card : ℝ)
            + T * N * √(W.card : ℝ) * √(additiveEnergy W : ℝ)) + C * T ^ (-100 : ℝ) := by
  obtain ⟨C, hC0, h⟩ := prop101_of_le_quarter w (ε := min ε (1 / 4))
    (lt_min hε (by norm_num)) (min_le_right _ _)
  refine ⟨C, hC0, fun T N W hT hN hNT hTεN hW hsep => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hmin : T ^ min ε (1 / 4) ≤ N :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hT1 (min_le_left _ _)) hTεN
  refine (h T N W hT hN hNT hmin hW hsep).trans ?_
  have hZ0 : (0 : ℝ) ≤ T ^ 2 * W.card * √(W.card : ℝ)
      + T * N * √(W.card : ℝ) * √(additiveEnergy W : ℝ) :=
    add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg (mul_nonneg hT0.le hN0.le) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  have hexp : T ^ (5 * min ε (1 / 4)) ≤ T ^ (5 * ε) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by
      have := min_le_left ε (1 / 4 : ℝ)
      linarith)
  have e1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hC0) hZ0
  linarith

end

end RHTower.GuthMaynard

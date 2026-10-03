import GaloisForLFunctions.HTGeometry.EulerHellingerAnomalyConservation

/-!
# The theta lift of the relative anomaly, and the spectral floor of the transport

The Hellinger Gram `K` is positive and trace class with `Tr K = ` the primitive collision budget.
With the theta Mellin-six flux `Φ = diag(w_n)` put `T_6 = Φ ⊗ C`, `T_H = Φ ⊗ K` and
`Δ_rel = T_H - T_6`; then `Δ_rel = Φ ⊗ D` entrywise, `Tr T_H = Tr T_6 = ` budget and `Tr Δ_rel = 0`
(**(EHGM.25)–(EHGM.27)**).

The transport preserves the Euler spectral floor (**(EHGM.28)**): every Euler clock satisfies
`λ_i ≥ log 2 > 1/2`, and `M h_λ = f_λ` with `f_λ(t) = √(864/115) λ^{3/2} t (e^{-λt} - e^{-2λt})`,
whose exact exponential rate is `λ`: `e^{μt} f_λ(t) → 0` for `μ < λ` and `→ ∞` for `μ > λ`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local notation "ℓ²E" => lp (fun _ : EulerLabel => ℂ) 2
local notation "ℓ²HE" => lp (fun _ : ℕ × EulerLabel => ℂ) 2

/-- **(EHGM.10)** `K ≥ 0`, `K ∈ 𝒮₁`, `Tr K = ‖K‖₁ = ` budget. -/
theorem hellingerGram_traceClass :
    hellingerGram.IsPositive ∧ MemSchattenClass 1 hellingerGram ∧
      hellingerGram.opTrace = (routePPrimitiveCollisionCubicTraceBudget : ℂ) ∧
      traceNorm ℓ²E hellingerGram = routePPrimitiveCollisionCubicTraceBudget := by
  obtain ⟨hpos, hS, htr⟩ := rightGram_traceClass summable_norm_sq_hellingerFrame
  simp_rw [norm_sq_hellingerFrame] at htr
  refine ⟨hpos, hS, htr, ?_⟩
  exact (traceNorm_eq_re_opTrace_of_isPositive hS hpos).trans (by rw [htr, Complex.ofReal_re]; rfl)

/-! ## The theta lift -/

/-- The joint Hellinger frame `√(w_n s_i) e_n ⊗ f_{λ_i}`. -/
def thetaHellingerFrame (a : ℕ × EulerLabel) : lp (fun _ : ℕ => HalfLineL2) 2 :=
  ((Real.sqrt (PrimeHodgeHistory.w a.1 * xiGammaEulerPrimitiveCubicLogMomentWeight a.2) : ℝ) : ℂ) •
    lp.single 2 a.1 (hellingerVector (xiGammaEulerPrimitiveLogFrequency_pos a.2))

theorem norm_sq_thetaHellingerFrame (a : ℕ × EulerLabel) :
    ‖thetaHellingerFrame a‖ ^ 2 =
      PrimeHodgeHistory.w a.1 * xiGammaEulerPrimitiveCubicLogMomentWeight a.2 := by
  rw [thetaHellingerFrame, norm_smul, lp.norm_single (by norm_num), norm_hellingerVector, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (mul_nonneg (PrimeHodgeHistory.w_pos _).le
      (xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg _))]

theorem summable_norm_sq_thetaHellingerFrame : Summable fun a => ‖thetaHellingerFrame a‖ ^ 2 := by
  simp_rw [norm_sq_thetaHellingerFrame]
  exact summable_thetaCapacityWeight

/-- **(EHGM.25)** `T_H = Φ ⊗ K`. -/
def thetaHellinger : ℓ²HE →L[ℂ] ℓ²HE :=
  ContinuousLinearMap.adjoint
      (squareSummableSynthesis thetaHellingerFrame summable_norm_sq_thetaHellingerFrame) ∘L
    squareSummableSynthesis thetaHellingerFrame summable_norm_sq_thetaHellingerFrame

theorem inner_single_hellingerGram (i j : EulerLabel) :
    ⟪(lp.single 2 i (1 : ℂ) : ℓ²E), hellingerGram (lp.single 2 j 1)⟫_ℂ =
      ⟪hellingerFrame i, hellingerFrame j⟫_ℂ := by
  rw [hellingerGram, hellingerSynthesis, inner_single_rightGram_single]

/-- **(EHGM.25)** `T_H((n,i),(m,j)) = δ_{nm} w_n K(i,j)`. -/
theorem inner_single_thetaHellinger (a b : ℕ × EulerLabel) :
    ⟪(lp.single 2 a (1 : ℂ) : ℓ²HE), thetaHellinger (lp.single 2 b 1)⟫_ℂ =
      if a.1 = b.1 then (PrimeHodgeHistory.w a.1 : ℂ) *
        ⟪(lp.single 2 a.2 (1 : ℂ) : ℓ²E), hellingerGram (lp.single 2 b.2 1)⟫_ℂ else 0 := by
  obtain ⟨n, i⟩ := a
  obtain ⟨m, j⟩ := b
  rw [thetaHellinger, inner_single_rightGram_single, thetaHellingerFrame, thetaHellingerFrame,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, lp.inner_single_left,
    inner_single_hellingerGram, hellingerFrame, hellingerFrame, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  by_cases h : n = m
  · subst h
    rw [lp.single_apply_self, if_pos rfl, Real.sqrt_mul (PrimeHodgeHistory.w_pos n).le,
      Real.sqrt_mul (PrimeHodgeHistory.w_pos n).le]
    have hw : ((Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ) * ((Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ) =
        (PrimeHodgeHistory.w n : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt (PrimeHodgeHistory.w_pos n).le
    push_cast
    linear_combination (((Real.sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight i) : ℝ) : ℂ) *
      ((Real.sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight j) : ℝ) : ℂ) *
        ⟪hellingerVector (xiGammaEulerPrimitiveLogFrequency_pos i),
          hellingerVector (xiGammaEulerPrimitiveLogFrequency_pos j)⟫_ℂ) * hw
  · rw [lp.single_apply_ne _ _ _ h, if_neg h, inner_zero_right, mul_zero, mul_zero]

/-- **(EHGM.26)** `T_H ≥ 0`, `T_H ∈ 𝒮₁`, `Tr T_H = ` budget. -/
theorem thetaHellinger_traceClass :
    thetaHellinger.IsPositive ∧ MemSchattenClass 1 thetaHellinger ∧
      thetaHellinger.opTrace = (routePPrimitiveCollisionCubicTraceBudget : ℂ) := by
  obtain ⟨hpos, hS, htr⟩ := rightGram_traceClass summable_norm_sq_thetaHellingerFrame
  simp_rw [norm_sq_thetaHellingerFrame] at htr
  rw [tsum_thetaCapacityWeight] at htr
  exact ⟨hpos, hS, htr⟩

/-- **(EHGM.25)** The relative theta anomaly `Δ_rel = T_H - T_6`. -/
def relativeThetaAnomaly : ℓ²HE →L[ℂ] ℓ²HE := thetaHellinger - thetaCapacity

/-- **(EHGM.27)** `T_6 = T_H - Δ_rel`. -/
theorem thetaCapacity_eq_sub : thetaCapacity = thetaHellinger - relativeThetaAnomaly := by
  rw [relativeThetaAnomaly, sub_sub_cancel]

/-- **(EHGM.25)** `Δ_rel((n,i),(m,j)) = δ_{nm} w_n D(i,j)`: `Δ_rel = Φ ⊗ D`. -/
theorem inner_single_relativeThetaAnomaly (a b : ℕ × EulerLabel) :
    ⟪(lp.single 2 a (1 : ℂ) : ℓ²HE), relativeThetaAnomaly (lp.single 2 b 1)⟫_ℂ =
      if a.1 = b.1 then (PrimeHodgeHistory.w a.1 : ℂ) *
        ⟪(lp.single 2 a.2 (1 : ℂ) : ℓ²E), relativeAnomaly (lp.single 2 b.2 1)⟫_ℂ else 0 := by
  have hK := congrArg (fun T : ℓ²E →L[ℂ] ℓ²E =>
    ⟪(lp.single 2 a.2 (1 : ℂ) : ℓ²E), T (lp.single 2 b.2 1)⟫_ℂ) hellingerGram_eq_add
  simp only [add_apply, inner_add_right] at hK
  rw [relativeThetaAnomaly, sub_apply, inner_sub_right, inner_single_thetaHellinger,
    inner_single_thetaCapacity]
  split_ifs
  · rw [hK, ← (inner_single_capacityGram a.2 b.2).2, ← (inner_single_capacityGram a.2 b.2).1]
    ring
  · ring

/-- **(EHGM.26)** `Δ_rel ∈ 𝒮₁` with `Tr Δ_rel = 0`. -/
theorem relativeThetaAnomaly_traceClass :
    MemSchattenClass 1 relativeThetaAnomaly ∧ relativeThetaAnomaly.opTrace = 0 := by
  have hS : MemSchattenClass 1 relativeThetaAnomaly := by
    rw [relativeThetaAnomaly, sub_eq_add_neg]
    exact thetaHellinger_traceClass.2.1.one_add
      (by simpa using memSchattenClass_one_smul thetaCapacity_traceClass.2.1 (-1 : ℂ))
  refine ⟨hS, ?_⟩
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one hS (HilbertSchmidt.lpBasis _)]
  have hdiag : ∀ a : ℕ × EulerLabel, ⟪HilbertSchmidt.lpBasis _ a,
      relativeThetaAnomaly (HilbertSchmidt.lpBasis _ a)⟫_ℂ = 0 := fun a => by
    rw [HilbertSchmidt.lpBasis_apply, inner_single_relativeThetaAnomaly, if_pos rfl,
      relativeAnomaly_diagonal, mul_zero]
  simp_rw [hdiag, tsum_zero]

/-! ## The spectral floor -/

/-- **(EHGM.28)** Every Euler clock is at least `log 2 > 1/2`. -/
theorem half_lt_log_two_le_eulerClock (i : EulerLabel) :
    1 / 2 < Real.log 2 ∧ Real.log 2 ≤ xiGammaEulerPrimitiveLogFrequency i := by
  refine ⟨by have := Real.log_two_gt_d9; linarith, ?_⟩
  rw [xiGammaEulerPrimitiveLogFrequency_eq]
  have h2 : Real.log 2 ≤ Real.log (i.1 : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast i.1.property.two_le)
  have hl := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  nlinarith [(Nat.cast_nonneg i.2 : (0 : ℝ) ≤ i.2)]

/-- The Hellinger profile `f_λ(t) = √(864/115) λ^{3/2} t (e^{-λt} - e^{-2λt})`. -/
def hellingerProfile (lam t : ℝ) : ℝ :=
  Real.sqrt (864 / 115) * lam ^ (3 / 2 : ℝ) * t * (Real.exp (-(lam * t)) - Real.exp (-(2 * lam * t)))

/-- **(EHGM.3)** `f_λ` has the explicit profile. -/
theorem hellingerVector_ae {lam : ℝ} (hlam : 0 < lam) :
    (hellingerVector hlam : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      fun t => (hellingerProfile lam t : ℂ) := by
  have h2 : (0 : ℝ) < 2 * lam := by positivity
  rw [hellingerVector]
  filter_upwards [Lp.coeFn_smul ((Real.sqrt (216 / 115) : ℝ) : ℂ)
      (gammaCoherentVector 3 hlam - (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) • gammaCoherentVector 3 h2),
    Lp.coeFn_sub (gammaCoherentVector 3 hlam)
      ((((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) • gammaCoherentVector 3 h2),
    Lp.coeFn_smul (((2 : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) (gammaCoherentVector 3 h2),
    gammaCoherentVector_ae 3 hlam, gammaCoherentVector_ae 3 h2] with t e1 e2 e3 e4 e5
  rw [e1, Pi.smul_apply, e2, Pi.sub_apply, e3, Pi.smul_apply, e4, e5, smul_eq_mul, smul_eq_mul,
    gammaCoherentProfile_three hlam, gammaCoherentProfile_three h2, hellingerProfile,
    Real.mul_rpow (by norm_num) hlam.le]
  have hc : (2 : ℝ) ^ (-(3 / 2 : ℝ)) * (2 : ℝ) ^ (3 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  have h864 : Real.sqrt (864 / 115) = 2 * Real.sqrt (216 / 115) := by
    rw [show (864 / 115 : ℝ) = 2 ^ 2 * (216 / 115) by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [h864]
  norm_cast
  linear_combination (-(2 * Real.sqrt (216 / 115) * lam ^ (3 / 2 : ℝ) * t *
    Real.exp (-(2 * lam * t)))) * hc

/-- **(EHGM.28)** The exact exponential rate of `f_λ` is `λ`: `e^{μt} f_λ(t) → 0` for `μ < λ`. -/
theorem tendsto_exp_mul_hellingerProfile_of_lt {lam μ : ℝ} (hlam : 0 < lam) (hμ : μ < lam) :
    Tendsto (fun t => Real.exp (μ * t) * hellingerProfile lam t) atTop (𝓝 0) := by
  have hε : 0 < lam - μ := sub_pos.2 hμ
  have h1 : Tendsto (fun t : ℝ => t * Real.exp (-(lam - μ) * t)) atTop (𝓝 0) := by
    have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h := (this.comp (tendsto_id.const_mul_atTop hε))
    have h' := h.const_mul (1 / (lam - μ))
    simp only [mul_zero] at h'
    refine h'.congr fun t => ?_
    simp only [Function.comp, id, pow_one]
    field_simp
  have h2 : Tendsto (fun t : ℝ => 1 - Real.exp (-(lam * t))) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hlam)))
  have h3 := (h1.mul h2).const_mul (Real.sqrt (864 / 115) * lam ^ (3 / 2 : ℝ))
  simp only [mul_zero, zero_mul] at h3
  refine h3.congr fun t => ?_
  unfold hellingerProfile
  have e1 : Real.exp (μ * t) * Real.exp (-(lam * t)) = Real.exp (-(lam - μ) * t) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (μ * t) * Real.exp (-(2 * lam * t)) =
      Real.exp (-(lam - μ) * t) * Real.exp (-(lam * t)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  calc Real.sqrt (864 / 115) * lam ^ (3 / 2 : ℝ) * (t * Real.exp (-(lam - μ) * t) *
        (1 - Real.exp (-(lam * t))))
      = Real.sqrt (864 / 115) * lam ^ (3 / 2 : ℝ) * t *
          (Real.exp (μ * t) * Real.exp (-(lam * t)) - Real.exp (μ * t) * Real.exp (-(2 * lam * t))) := by
        rw [e1, e2]; ring
    _ = _ := by ring

/-- **(EHGM.28)** `e^{μt} f_λ(t) → ∞` for `μ > λ`. -/
theorem tendsto_exp_mul_hellingerProfile_of_gt {lam μ : ℝ} (hlam : 0 < lam) (hμ : lam < μ) :
    Tendsto (fun t => Real.exp (μ * t) * hellingerProfile lam t) atTop atTop := by
  have hε : 0 < μ - lam := sub_pos.2 hμ
  have hC : 0 < Real.sqrt (864 / 115) * lam ^ (3 / 2 : ℝ) := by positivity
  have h1 : Tendsto (fun t : ℝ => t * Real.exp ((μ - lam) * t)) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hε))
  have h2 : Tendsto (fun t : ℝ => 1 - Real.exp (-(lam * t))) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hlam)))
  rw [sub_zero] at h2
  have h3 := (h1.atTop_mul_pos one_pos h2).const_mul_atTop hC
  refine h3.congr fun t => ?_
  unfold hellingerProfile
  have e1 : Real.exp (μ * t) * Real.exp (-(lam * t)) = Real.exp ((μ - lam) * t) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (μ * t) * Real.exp (-(2 * lam * t)) =
      Real.exp ((μ - lam) * t) * Real.exp (-(lam * t)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  calc Real.sqrt (864 / 115) * lam ^ (3 / 2 : ℝ) * (t * Real.exp ((μ - lam) * t) *
        (1 - Real.exp (-(lam * t))))
      = Real.sqrt (864 / 115) * lam ^ (3 / 2 : ℝ) * t *
          (Real.exp (μ * t) * Real.exp (-(lam * t)) - Real.exp (μ * t) * Real.exp (-(2 * lam * t))) := by
        rw [e1, e2]; ring
    _ = _ := by ring

/-- **(EHGM.28) The transport preserves the Euler spectral floor.**  The image `M (W_6 e_i)` of every
Euler source column is `√s_i f_{λ_i}`, which decays faster than `e^{-at}` for every `a < log 2`; in
particular for every rate `a ≤ 1/2`. -/
theorem ehgmTransport_preserves_spectral_floor (i : EulerLabel) {a : ℝ} (ha : a < Real.log 2) :
    ehgmTransport (capacitySynthesis (lp.single 2 i 1)) = hellingerFrame i ∧
      Tendsto (fun t => Real.exp (a * t) *
        hellingerProfile (xiGammaEulerPrimitiveLogFrequency i) t) atTop (𝓝 0) := by
  refine ⟨?_, tendsto_exp_mul_hellingerProfile_of_lt (xiGammaEulerPrimitiveLogFrequency_pos i)
    (ha.trans_le (half_lt_log_two_le_eulerClock i).2)⟩
  rw [capacitySynthesis, squareSummableSynthesis_single, one_smul, capacityFrame, map_smul,
    ehgmTransport_sixth, hellingerFrame]

/-- **(EHGM.28) `M` is not the Xi landing.**  A profile `g` with an exponential rate below
`log 2`, i.e. `e^{μt} g(t) → ∞` for some `μ < log 2` (in particular every rate `0 < a < 1/2`), is
never eventually a multiple of a transported Euler column `f_{λ_i}`. -/
theorem not_eventuallyEq_hellingerProfile_of_slow_rate (i : EulerLabel) {g : ℝ → ℝ} {μ : ℝ}
    (hμ : μ < Real.log 2) (hg : Tendsto (fun t => Real.exp (μ * t) * g t) atTop atTop) (c : ℝ) :
    ¬ (g =ᶠ[atTop] fun t => c * hellingerProfile (xiGammaEulerPrimitiveLogFrequency i) t) := by
  intro h
  have h0 := (tendsto_exp_mul_hellingerProfile_of_lt (xiGammaEulerPrimitiveLogFrequency_pos i)
    (hμ.trans_le (half_lt_log_two_le_eulerClock i).2)).const_mul c
  rw [mul_zero] at h0
  have h1 : Tendsto (fun t => Real.exp (μ * t) * g t) atTop (𝓝 0) := by
    refine h0.congr' ?_
    filter_upwards [h] with t ht
    rw [ht]
    ring
  exact not_tendsto_nhds_of_tendsto_atTop hg 0 h1

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.RHTower.GaussChannelOperator
import GaloisForLFunctions.RHTower.GaussOnePrimeReducedDefectEnergy

/-!
# Actual depth-one residue of the one-prime Gauss defect

The general Gauss-channel singular-value theorem was previously stated only for depths `m ≥ 2`.
At depth one the same column argument closes after a sharper one-step class budget: the principal
step applied to the constant vector grows more slowly than every positive power.  The existing
positive-operator diagonal comparison then transfers the exact Fourier-diagonal logarithmic mean
to the literal singular values of the actual channel operator.

Combining this with the exact reduced-defect identity gives the measurable weak-trace-class law for
`Eₚ*Eₚ` itself, not a diagonal proxy.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions ContinuousLinearMap
open GaloisForLFunctions.RHTower
open scoped ENNReal NNReal

noncomputable section

/-! ## The depth-one principal-step bound -/

set_option maxHeartbeats 2000000 in
/-- At depth one the principal step on the constant Fourier vector has sub-power growth. -/
theorem exists_norm_gaussPrincipalStep_pow_one_le (k : Fin 1) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ I : ℕ, 2 ≤ I →
      ‖(gaussPrincipalStepBlock (le_refl 1) k p hp (I : ℤ) ^ 1)
          (fourierLp 2 (0 : ℤ))‖ ≤ C * (1 + (I : ℝ)) ^ ρ := by
  obtain ⟨K, hK, hKb⟩ :=
    exists_norm_gaussSampleValue_pow_ratio_bound (le_refl 1) k p
  set c₀ : ℝ := min (ρ / 4) (1 / 4) with hc₀def
  set ε : ℝ := min (ρ / 8) (1 / 8) with hεdef
  have hc₀0 : 0 < c₀ := lt_min (by linarith) (by norm_num)
  have hc₀ρ : c₀ ≤ ρ / 4 := min_le_left _ _
  have hc₀quarter : c₀ ≤ 1 / 4 := min_le_right _ _
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hερ : ε ≤ ρ / 8 := min_le_left _ _
  have hεeighth : ε ≤ 1 / 8 := min_le_right _ _
  obtain ⟨A₀, B₀, hA₀, hB₀, hclass₀⟩ :=
    exists_gaussClass_principalStep_pow (le_refl 1) k p hp hK hKb
      hc₀0 hε0 0 (by norm_num; linarith) (by norm_num)
  have hcm : c₀ + 1 / (2 * ((1 : ℕ) : ℝ)) < 1 := by
    norm_num
    linarith
  obtain ⟨A₁, B₁, hA₁, hB₁, hinner⟩ :=
    exists_gaussClass_principalStepInner (le_refl 1) k p hp hK hKb
      (θ := 1) (c := c₀) (ε := ε) hc₀0 hcm (by norm_num) hε0
      (by nlinarith) A₀ B₀ hA₀ hB₀
  set θ : ℝ := 1 - 2 * ε with hθdef
  set c : ℝ := c₀ + 1 with hcdef
  have hθhalf : (1 : ℝ) / 2 < θ := by
    rw [hθdef]
    nlinarith
  have hchalf : (1 : ℝ) / 2 < c := by
    rw [hcdef]
    linarith
  have hbudget : 2 * c - 2 * θ ≤ 2 * ρ := by
    rw [hcdef, hθdef]
    nlinarith
  set W : ℝ := Real.sqrt (2 * (A₁ ^ 2 * intNatAbsPowTotal (2 * θ))
    + 2 * (B₁ ^ 2 * intNatAbsPowTotal (2 * c))) with hWdef
  refine ⟨Real.sqrt (p : ℝ) * W, by positivity, fun I hI => ?_⟩
  set X : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussShiftedBlockDiag (le_refl 1) k p (I : ℤ)
      (gaussPrimeScaleInvSqBlock hp
        (gaussShiftedBlockOf (le_refl 1) k p (I : ℤ)
          (gaussPrimeScaleBlock hp (fourierLp 2 (0 : ℤ))))) with hXdef
  have hbaseClass := hclass₀ I hI
  have hbaseClass' : TwoPieceAmplitude A₀ 1 (B₀ / (1 + (I : ℝ)) ^ (1 : ℝ)) c₀ I
      (fun j => fourierCoeff
        (((gaussPrincipalStepBlock (le_refl 1) k p hp (I : ℤ) ^ 0)
          (fourierLp 2 (0 : ℤ)) : AddCircle (1 : ℝ) → ℂ)) j) := by
    simpa using hbaseClass
  have hXclass : TwoPieceAmplitude A₁ θ (B₁ / (1 + (I : ℝ)) ^ θ) c I
      (fun j => fourierCoeff ((X : AddCircle (1 : ℝ) → ℂ)) j) := by
    have h := hinner I hI
      ((gaussPrincipalStepBlock (le_refl 1) k p hp (I : ℤ) ^ 0)
        (fourierLp 2 (0 : ℤ))) hbaseClass'
    simpa [X, θ, c] using h
  have hXnorm : ‖X‖ ≤ W * (1 + (I : ℝ)) ^ ρ := by
    simpa [W] using
      (norm_le_of_tiedTwoPieceAmplitude hA₁ hB₁ hθhalf hchalf hρ.le hbudget hXclass)
  have houter : ‖gaussPrimeScaleBlock hp X‖ ≤ Real.sqrt (p : ℝ) * ‖X‖ := by
    refine le_trans ((gaussPrimeScaleBlock hp).le_opNorm X) ?_
    exact mul_le_mul_of_nonneg_right (norm_gaussPrimeScaleBlock_le hp) (norm_nonneg X)
  rw [pow_one, gaussPrincipalStepBlock_apply]
  change ‖gaussPrimeScaleBlock hp X‖ ≤ _
  exact houter.trans (by
    have := mul_le_mul_of_nonneg_left hXnorm (Real.sqrt_nonneg (p : ℝ))
    nlinarith)

/-! ## Depth-one column decay -/

set_option maxHeartbeats 1000000 in
/-- The actual depth-one Gauss block has columns `O(|n|⁻¹⁺ρ)` for every `ρ > 0`. -/
theorem exists_norm_gaussQuasiInnerG_one_fourierLp_le (k : Fin 1) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, n ≠ 0 →
      ‖(gaussQuasiInnerG (le_refl 1) k p ^ 1) (fourierLp 2 n)‖
        ≤ C * ((n.natAbs : ℝ)) ^ (-1 + ρ) := by
  set ρ' : ℝ := min ρ 1 with hρ'def
  have hρ'0 : 0 < ρ' := lt_min hρ one_pos
  have hρ'1 : ρ' ≤ 1 := min_le_right _ _
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    exists_norm_gaussSampleValue_pow_mul_natAbs_le (le_refl 1) k p
  obtain ⟨C₂, hC₂0, hC₂⟩ :=
    exists_norm_gaussPrincipalStep_pow_one_le k p hp hρ'0
  set G := gaussQuasiInnerG (le_refl 1) k p with hGdef
  refine ⟨max ‖G‖ (2 * (p : ℝ) * C₁ * C₂), le_max_of_le_left (norm_nonneg G),
    fun n hn => ?_⟩
  have hbasis : ‖(fourierLp 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))‖ = 1 := by
    rw [show (fourierLp 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) =
      (fourierBasis (T := (1 : ℝ))) n by rw [coe_fourierBasis]]
    exact (fourierBasis (T := (1 : ℝ))).orthonormal.1 n
  have hnat1 : 1 ≤ n.natAbs := by omega
  have hnatR : (1 : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hnat1
  have hnatpos : (0 : ℝ) < (n.natAbs : ℝ) := by linarith
  by_cases hsmall : n.natAbs < 2
  · have hn1 : n.natAbs = 1 := by omega
    have hpow : ((n.natAbs : ℝ)) ^ (-1 + ρ) = 1 := by rw [hn1]; norm_num
    rw [hpow, mul_one, pow_one]
    refine le_trans ?_ (le_max_left _ _)
    have h := G.le_opNorm (fourierLp 2 n)
    rw [hbasis, mul_one] at h
    exact h
  · push Not at hsmall
    rw [norm_gaussQuasiInnerG_pow_fourierLp_natAbs (le_refl 1) k p 1 n]
    have hnz : ((n.natAbs : ℤ)) ≠ 0 := by omega
    have hstep := norm_gaussQuasiInnerG_pow_fourierLp_le
      (le_refl 1) k p hp hnz 1
    have hR := hC₂ n.natAbs hsmall
    have hd := hC₁ ((n.natAbs : ℤ)) hnz
    have hdabs : (((n.natAbs : ℤ)).natAbs : ℝ) = (n.natAbs : ℝ) := by norm_num
    rw [hdabs] at hd
    have hd2 : ‖gaussSampleValue k p ((n.natAbs : ℤ))‖ ^ 2
        ≤ C₁ / (n.natAbs : ℝ) := by
      rw [le_div_iff₀ hnatpos]
      norm_num at hd ⊢
      exact hd
    have hone : (1 : ℝ) + (n.natAbs : ℝ) ≤ 2 * (n.natAbs : ℝ) := by linarith
    have hbnd : (1 + (n.natAbs : ℝ)) ^ ρ' ≤ 2 * ((n.natAbs : ℝ)) ^ ρ' := by
      have h1 : (1 + (n.natAbs : ℝ)) ^ ρ' ≤ (2 * (n.natAbs : ℝ)) ^ ρ' :=
        Real.rpow_le_rpow (by positivity) hone hρ'0.le
      have h2 : (2 * (n.natAbs : ℝ)) ^ ρ' =
          (2 : ℝ) ^ ρ' * ((n.natAbs : ℝ)) ^ ρ' :=
        Real.mul_rpow (by norm_num) hnatpos.le
      have h3 : (2 : ℝ) ^ ρ' ≤ 2 := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hρ'1
        rwa [Real.rpow_one] at h
      have h4 : (0 : ℝ) ≤ ((n.natAbs : ℝ)) ^ ρ' := Real.rpow_nonneg hnatpos.le _
      nlinarith [h1, h2.le, h2.ge, h3, h4]
    have hchain : ‖(gaussQuasiInnerG (le_refl 1) k p ^ 1)
        (fourierLp 2 ((n.natAbs : ℤ)))‖
        ≤ (p : ℝ) * (C₁ / (n.natAbs : ℝ)) *
          (C₂ * (2 * ((n.natAbs : ℝ)) ^ ρ')) := by
      refine le_trans hstep ?_
      norm_num only [pow_one]
      have hA : (p : ℝ) * ‖gaussSampleValue k p ((n.natAbs : ℤ))‖ ^ 2
          ≤ (p : ℝ) * (C₁ / (n.natAbs : ℝ)) :=
        mul_le_mul_of_nonneg_left hd2 (by positivity)
      have hB : ‖gaussPrincipalStepBlock (le_refl 1) k p hp ((n.natAbs : ℤ))
          (fourierLp 2 (0 : ℤ))‖ ≤ C₂ * (2 * ((n.natAbs : ℝ)) ^ ρ') := by
        refine le_trans hR ?_
        exact mul_le_mul_of_nonneg_left hbnd hC₂0
      have hAn : 0 ≤ (p : ℝ) * ‖gaussSampleValue k p ((n.natAbs : ℤ))‖ ^ 2 := by positivity
      have hBn : 0 ≤ ‖gaussPrincipalStepBlock (le_refl 1) k p hp ((n.natAbs : ℤ))
          (fourierLp 2 (0 : ℤ))‖ := norm_nonneg _
      nlinarith [hA, hB, hAn, hBn]
    refine le_trans hchain ?_
    have hpowid : (C₁ / (n.natAbs : ℝ)) * ((n.natAbs : ℝ)) ^ ρ'
        = C₁ * ((n.natAbs : ℝ)) ^ (-1 + ρ') := by
      rw [Real.rpow_add hnatpos (-1) ρ', Real.rpow_neg_one]
      field_simp
    have hmono : ((n.natAbs : ℝ)) ^ (-1 + ρ')
        ≤ ((n.natAbs : ℝ)) ^ (-1 + ρ) :=
      Real.rpow_le_rpow_of_exponent_le hnatR (by linarith)
    have hfinal : (p : ℝ) * (C₁ / (n.natAbs : ℝ)) *
        (C₂ * (2 * ((n.natAbs : ℝ)) ^ ρ'))
        = (2 * (p : ℝ) * C₁ * C₂) * ((n.natAbs : ℝ)) ^ (-1 + ρ') := by
      calc
        (p : ℝ) * (C₁ / (n.natAbs : ℝ)) *
            (C₂ * (2 * ((n.natAbs : ℝ)) ^ ρ'))
            = 2 * (p : ℝ) * C₂ *
              ((C₁ / (n.natAbs : ℝ)) * ((n.natAbs : ℝ)) ^ ρ') := by ring
        _ = (2 * (p : ℝ) * C₁ * C₂) * ((n.natAbs : ℝ)) ^ (-1 + ρ') := by
          rw [hpowid]
          ring
    rw [hfinal]
    calc
      (2 * (p : ℝ) * C₁ * C₂) * ((n.natAbs : ℝ)) ^ (-1 + ρ')
          ≤ (2 * (p : ℝ) * C₁ * C₂) * ((n.natAbs : ℝ)) ^ (-1 + ρ) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
      _ ≤ max ‖G‖ (2 * (p : ℝ) * C₁ * C₂) *
          ((n.natAbs : ℝ)) ^ (-1 + ρ) := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The scaled one-prime channel inherits the depth-one column decay. -/
theorem exists_norm_gaussChannelOperator_one_fourierBasis_le (k : Fin 1) (p : Nat.Primes)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, n ≠ 0 →
      ‖gaussChannelOperator (le_refl 1) k p ((fourierBasis (T := (1 : ℝ))) n)‖
        ≤ C * ((n.natAbs : ℝ)) ^ (-1 + ρ) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  obtain ⟨C, hC0, hC⟩ := exists_norm_gaussQuasiInnerG_one_fourierLp_le k p hp hρ
  refine ⟨gaussLocalFactorWeight 1 p * (gaussArchScale 1 ^ 2) * C,
    mul_nonneg (mul_nonneg (gaussLocalFactorWeight_pos 1 p).le (sq_nonneg _)) hC0,
    fun n hn => ?_⟩
  rw [show ((fourierBasis (T := (1 : ℝ))) n) =
      (fourierLp 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) by rw [coe_fourierBasis],
    norm_gaussChannelOperator_fourierLp (le_refl 1) k p n]
  norm_num only [pow_one]
  have hscale : 0 ≤ gaussLocalFactorWeight 1 p * (gaussArchScale 1 ^ 2) :=
    mul_nonneg (gaussLocalFactorWeight_pos 1 p).le (sq_nonneg _)
  calc
    gaussLocalFactorWeight 1 p * (gaussArchScale 1 ^ 2) *
        ‖gaussQuasiInnerG (le_refl 1) k p (fourierLp 2 n)‖
        ≤ gaussLocalFactorWeight 1 p * (gaussArchScale 1 ^ 2) *
          (C * ((n.natAbs : ℝ)) ^ (-1 + ρ)) :=
      mul_le_mul_of_nonneg_left (by simpa using hC n hn) hscale
    _ = gaussLocalFactorWeight 1 p * (gaussArchScale 1 ^ 2) * C *
        ((n.natAbs : ℝ)) ^ (-1 + ρ) := by ring

/-! ## Fourier and singular-value logarithmic means -/

set_option maxHeartbeats 1000000 in
/-- The symmetric Fourier diagonal of the actual depth-one channel has the arithmetic residue. -/
theorem tendsto_gaussChannelOperator_one_band_logMean (k : Fin 1) (p : Nat.Primes) :
    Tendsto (fun M : ℕ =>
      (∑ j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        RCLike.re (inner ℂ ((fourierBasis (T := (1 : ℝ))) j)
          (gaussChannelOperator (le_refl 1) k p
            ((fourierBasis (T := (1 : ℝ))) j)) : ℂ)) / Real.log (M : ℝ))
      atTop (nhds (gaussChannelResidue 1 p)) := by
  set g : ℤ → ℂ := fun j =>
    inner ℂ (fourierLp 2 j)
      ((gaussQuasiInnerGFull (le_refl 1) k p ^ 1) (fourierLp 2 j)) with hgdef
  set f : ℤ → ℝ := fun j =>
    RCLike.re (inner ℂ ((fourierBasis (T := (1 : ℝ))) j)
      (gaussChannelOperator (le_refl 1) k p ((fourierBasis (T := (1 : ℝ))) j)) : ℂ) with hfdef
  have hfval : ∀ j : ℤ, f j = gaussLocalFactorWeight 1 p * (g j).re := by
    intro j
    have hb : ((fourierBasis (T := (1 : ℝ))) j) =
        (fourierLp 2 j : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) := by
      rw [coe_fourierBasis]
    rw [hfdef]
    simp only [hb]
    rw [inner_gaussChannelOperator_fourierLp (le_refl 1) k p j]
    exact Complex.re_ofReal_mul (gaussLocalFactorWeight 1 p) (g j)
  have hbase := tendsto_gaussLocalDiagonal_logResidue k p
  have hre : Tendsto (fun N : ℕ =>
      (((gaussLocalFactorWeight 1 p : ℝ) : ℂ) *
        ((∑ n ∈ Finset.range N, (g ((n : ℤ) + 1) + g (-((n : ℤ) + 1)))) /
          (Real.log (N : ℝ) : ℂ))).re) atTop (nhds (gaussChannelResidue 1 p)) := by
    exact (Complex.continuous_re.tendsto _).comp hbase
  have hsimp : ∀ N : ℕ,
      (((gaussLocalFactorWeight 1 p : ℝ) : ℂ) *
        ((∑ n ∈ Finset.range N, (g ((n : ℤ) + 1) + g (-((n : ℤ) + 1)))) /
          (Real.log (N : ℝ) : ℂ))).re
        = (∑ n ∈ Finset.range N, (f ((n : ℤ) + 1) + f (-((n : ℤ) + 1)))) /
            Real.log (N : ℝ) := by
    intro N
    have hdiv : ((∑ n ∈ Finset.range N, (g ((n : ℤ) + 1) + g (-((n : ℤ) + 1)))) /
        (Real.log (N : ℝ) : ℂ)).re
        = (∑ n ∈ Finset.range N, (g ((n : ℤ) + 1) + g (-((n : ℤ) + 1)))).re /
          Real.log (N : ℝ) := by
      rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm, Complex.re_ofReal_mul]
      ring
    have hterm : ∀ n ∈ Finset.range N,
        (g ((n : ℤ) + 1) + g (-((n : ℤ) + 1))).re =
          (g ((n : ℤ) + 1)).re + (g (-((n : ℤ) + 1))).re :=
      fun n _ => Complex.add_re _ _
    have hsum : (∑ n ∈ Finset.range N, (f ((n : ℤ) + 1) + f (-((n : ℤ) + 1)))) =
        gaussLocalFactorWeight 1 p *
          ∑ x ∈ Finset.range N, ((g ((x : ℤ) + 1)).re + (g (-((x : ℤ) + 1))).re) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hfval, hfval]
      ring
    rw [Complex.re_ofReal_mul, hdiv, Complex.re_sum, Finset.sum_congr rfl hterm, hsum]
    ring
  have hmid : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, (f ((n : ℤ) + 1) + f (-((n : ℤ) + 1)))) /
        Real.log (N : ℝ)) atTop (nhds (gaussChannelResidue 1 p)) :=
    hre.congr fun N => hsimp N
  have hzero : Tendsto (fun N : ℕ => f 0 / Real.log (N : ℝ)) atTop (nhds 0) :=
    ContinuousLinearMap.tendsto_const_div_log_natCast (f 0)
  have hsum := hzero.add hmid
  rw [zero_add] at hsum
  refine hsum.congr fun N => ?_
  rw [← add_div, ← sum_Icc_eq_zero_add_sum_range f N]

/-- Literal singular values of the actual depth-one channel have the same logarithmic mean. -/
theorem tendsto_sum_singVal_gaussChannelOperator_one (k : Fin 1) (p : Nat.Primes) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, singVal (gaussChannelOperator (le_refl 1) k p) n) /
        Real.log (N : ℝ)) atTop (nhds (gaussChannelResidue 1 p)) := by
  refine ContinuousLinearMap.tendsto_sum_singVal_div_log_of_diagonal
    (fourierBasis (T := (1 : ℝ)))
    (isCompactOperator_gaussChannelOperator (le_refl 1) k p)
    (gaussChannelOperator_nonneg (le_refl 1) k p)
    (tendsto_gaussChannelOperator_one_band_logMean k p) (fun δ hδ => ?_)
  exact exists_norm_gaussChannelOperator_one_fourierBasis_le k p hδ

/-- The actual depth-one channel lies in the Dixmier ideal. -/
theorem isDixmier_gaussChannelOperator_one (k : Fin 1) (p : Nat.Primes) :
    ContinuousLinearMap.IsDixmier (gaussChannelOperator (le_refl 1) k p) :=
  isDixmier_of_tendsto_logMean (tendsto_sum_singVal_gaussChannelOperator_one k p)

set_option maxHeartbeats 1000000 in
/-- The actual depth-one channel is measurable with the exact arithmetic residue. -/
theorem hasSchattenLogResidue_gaussChannelOperator_one (k : Fin 1) (p : Nat.Primes) :
    HasSchattenLogResidue 1 (gaussChannelOperator (le_refl 1) k p)
      (gaussChannelResidue 1 p) := by
  have hcpt := isCompactOperator_gaussChannelOperator (le_refl 1) k p
  have hbase := tendsto_sum_singVal_gaussChannelOperator_one k p
  have hstep : Tendsto (fun N : ℕ =>
      Real.log (((N + 1 : ℕ) : ℕ) : ℝ) / Real.log (N : ℝ)) atTop (nhds 1) := by
    refine ContinuousLinearMap.tendsto_log_div_log_of_bounds (f := fun N : ℕ => N + 1)
      (α := 1) (β := Real.log 2) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
      have h := Real.log_le_log hNpos hle
      have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hle : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        push_cast
        linarith
      have h := Real.log_le_log (by positivity) hle
      rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)] at h
      linarith
  have hinv : Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) / Real.log (((N : ℝ)) + 1)) atTop (nhds 1) := by
    have h := hstep.inv₀ one_ne_zero
    rw [inv_one] at h
    refine h.congr fun N => ?_
    rw [inv_div]
    push_cast
    rfl
  have hprod := hbase.mul hinv
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlogpos : (0 : ℝ) < Real.log (N : ℝ) := by
    refine Real.log_pos ?_
    exact_mod_cast (show 1 < N by omega)
  have hsp : schattenPowerPartialSum 1 (gaussChannelOperator (le_refl 1) k p) N =
      ∑ n ∈ Finset.range N, singVal (gaussChannelOperator (le_refl 1) k p) n := by
    rw [schattenPowerPartialSum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Real.rpow_one, approxNumber_eq_singVal hcpt n]
  rw [hsp]
  field_simp

/-- Positive residue excludes trace class for the literal depth-one channel. -/
theorem gaussChannelOperator_one_not_memSchattenClass (k : Fin 1) (p : Nat.Primes) :
    ¬ MemSchattenClass 1 (gaussChannelOperator (le_refl 1) k p) :=
  (hasSchattenLogResidue_gaussChannelOperator_one k p).not_memSchattenClass
    (gaussChannelResidue_pos (le_refl 1) p)

/-! ## Transfer to the reduced one-prime defect -/

/-- The literal reduced defect energy is measurable with the arithmetic residue. -/
theorem hasSchattenLogResidue_gaussOnePrimeReducedDefect_modulusSq
    (p : Nat.Primes) :
    HasSchattenLogResidue 1
      (adjoint (gaussOnePrimeReducedDefect p) ∘L gaussOnePrimeReducedDefect p)
      (gaussChannelResidue 1 p) := by
  rw [gaussOnePrimeReducedDefect_modulusSq]
  exact hasSchattenLogResidue_gaussChannelOperator_one (0 : Fin 1) p

/-- The literal reduced defect energy is in the Dixmier ideal. -/
theorem isDixmier_gaussOnePrimeReducedDefect_modulusSq (p : Nat.Primes) :
    ContinuousLinearMap.IsDixmier
      (adjoint (gaussOnePrimeReducedDefect p) ∘L gaussOnePrimeReducedDefect p) := by
  rw [gaussOnePrimeReducedDefect_modulusSq]
  exact isDixmier_gaussChannelOperator_one (0 : Fin 1) p

/-- The literal reduced defect energy is not trace class. -/
theorem gaussOnePrimeReducedDefect_modulusSq_not_memSchattenClass (p : Nat.Primes) :
    ¬ MemSchattenClass 1
      (adjoint (gaussOnePrimeReducedDefect p) ∘L gaussOnePrimeReducedDefect p) := by
  rw [gaussOnePrimeReducedDefect_modulusSq]
  exact gaussChannelOperator_one_not_memSchattenClass (0 : Fin 1) p

end

end RHTower

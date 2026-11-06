import GaloisForLFunctions.CompletedArithmeticForms.ThePrefixSchurCostIsThePrefixResidual
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PolynomialConductorComplementCoercivityAndSharpenedOverlap
import GaloisForLFunctions.TransMetzlerWeilPositivity.TransMetzlerYoungOptimization
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TelescopedConductorSplitAndOneNinthWeilPositivity
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.Conductor.CoprimeFourierOrder

/-!
# The Schur debit is paid on growing blocks and full tails

The plateau Schur complement `S = D − BᵀA⁻¹B` has two payments.

**Growing conductor blocks.** The residual form `S(tail z) = zᵀWz − rᵀA⁻¹r`, with `A⁻¹ ≤ 20`, turns the debit
into the prefix mass of the conductor residuals, of order `(log N)^{−13/32}`. The whole block keeps half of the
conductor floor `a e^{−Bc}`, uniformly over `M ≥ M₀`, `log M ≤ √log N`, `c ≤ b log log N` and
conductors up to `(log N)^{1/32}` (`exists_plateauPrefixSchur_floor_on_growing_blocks`).

**Full tails.** Choosing the prefix `p = −A⁻¹By` kills the residual, so `S(y) = xᵀWx` for an extension
`x` of `y`. A full-space floor of `W` therefore passes to the Schur complement on every tail
(`dotProduct_prefixSchur_ge_of_floor`). This is what the certified plateau floor pays
(`eventually_plateauPrefixSchur_floor_on_full_tail`). Above the certified boundary the full tail payment
is the positivity of `W` itself.
-/

noncomputable section

open Matrix Finset Filter Topology MeasureTheory
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CompletedArithmeticForms

open TransMetzlerWeilPositivity SpacingScaleHarmonicAnalysis
  CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-! ### Full tails -/

/-- **A full-space floor passes to the Schur complement on every tail.** -/
theorem dotProduct_prefixSchur_ge_of_floor {M N : ℕ} (hMN : M ≤ N) {c e : ℝ} (he : 0 ≤ e)
    (hA : (plateauPrefixBlock hMN c).PosDef)
    (hfloor : ∀ x : PrimeHorizonIndex N → ℝ,
      e * (x ⬝ᵥ x) ≤ x ⬝ᵥ completeWeilMatrix transMetzlerProfile c N *ᵥ x)
    (y : HorizonTail M N → ℝ) :
    e * (y ⬝ᵥ y) ≤ y ⬝ᵥ plateauPrefixSchur hMN c *ᵥ y := by
  obtain ⟨A, hAd⟩ : ∃ A, A = plateauPrefixBlock hMN c := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = plateauMixedBlock hMN c := ⟨_, rfl⟩
  have hunit : IsUnit A.det := by
    rw [hAd]
    exact isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  obtain ⟨p, hpd⟩ : ∃ p, p = -(A⁻¹ *ᵥ (B *ᵥ y)) := ⟨_, rfl⟩
  let x : PrimeHorizonIndex N → ℝ := Sum.elim p y ∘ (horizonPrefixSplit hMN).symm
  have hxsplit : x ∘ horizonPrefixSplit hMN = Sum.elim p y := by
    funext i
    simp only [x, Function.comp, Equiv.symm_apply_apply]
  have hpre : prefixPart hMN x = p := by
    funext j
    exact congrFun hxsplit (Sum.inl j)
  have htail : tailPart (M := M) x = y := by
    funext j
    exact congrFun hxsplit (Sum.inr j)
  -- the residual vanishes on the prefix
  have hres : prefixPart hMN (completeWeilMatrix transMetzlerProfile c N *ᵥ x) = 0 := by
    rw [prefixPart_mulVec, hpre, htail, ← hAd, ← hBd, hpd, mulVec_neg, mulVec_mulVec,
      Matrix.mul_nonsing_inv A hunit, one_mulVec, neg_add_cancel]
  have hS := prefixSchur_tail_eq hMN hA x
  rw [htail, hres, zero_dotProduct, sub_zero] at hS
  rw [hS]
  refine le_trans ?_ (hfloor x)
  refine mul_le_mul_of_nonneg_left ?_ he
  have hsum : x ⬝ᵥ x = p ⬝ᵥ p + y ⬝ᵥ y := by
    simp only [dotProduct]
    rw [← Equiv.sum_comp (horizonPrefixSplit hMN) fun i => x i * x i, Fintype.sum_sum_type]
    have h1 (j : PrimeHorizonIndex M) :
        x (horizonPrefixSplit hMN (Sum.inl j)) = p j := congrFun hxsplit (Sum.inl j)
    have h2 (j : HorizonTail M N) :
        x (horizonPrefixSplit hMN (Sum.inr j)) = y j := congrFun hxsplit (Sum.inr j)
    simp only [h1, h2]
  rw [hsum]
  have hp : 0 ≤ p ⬝ᵥ p := sum_nonneg fun i _ => mul_self_nonneg _
  linarith only [hp]

/-- **The Schur debit on the full tail below the certified plateau boundary.** -/
theorem eventually_plateauPrefixSchur_floor_on_full_tail {c : ℝ} (hc : 1 ≤ c)
    (hcb : c ≤ transMetzlerCertifiedBoundary) {ε : ℝ} (hε : 0 < ε)
    (hεc : ε ≤ transMetzlerOptimizedOverlapFloor c) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ N : ℕ in atTop, ∀ hMN : M ≤ N, c * M ≤ N → ∀ y : HorizonTail M N → ℝ,
      (transMetzlerOptimizedOverlapFloor c - ε) * (y ⬝ᵥ y) ≤
        y ⬝ᵥ plateauPrefixSchur hMN c *ᵥ y := by
  filter_upwards [eventually_plateauPrefixBlock_posDef] with M hM
  filter_upwards [eventually_completeWeilMatrix_young_floor_to_boundary hc hcb ε hε] with N hN hMN hcMN y
  have hc0 : 0 < c := by linarith only [hc]
  refine dotProduct_prefixSchur_ge_of_floor hMN (by linarith only [hεc]) (hM N hMN c hc0 hcMN) ?_ y
  intro x
  have h := hN (WithLp.toLp 2 x)
  have hnorm : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (PrimeHorizonIndex N))‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, sq]
  rw [hnorm] at h
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, star_trivial] using h

/-! ### Growing conductor blocks -/

/-- The complete action on a conductor combination, coordinate by coordinate. -/
private theorem completeWeil_mulVec_sum (c : ℝ) {Q N : ℕ} (a : ℕ → ℝ) (i : PrimeHorizonIndex N) :
    (completeWeilMatrix transMetzlerProfile c N *ᵥ
        (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N).ofLp) i =
      ∑ m ∈ Icc 1 Q, a m * (completeWeilMatrix transMetzlerProfile c N *ᵥ
        (normalizedRamanujanHorizonVector m N).ofLp) i := by
  have he : (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N).ofLp =
      ∑ m ∈ Icc 1 Q, a m • (normalizedRamanujanHorizonVector m N).ofLp := by
    funext j
    simp [Finset.sum_apply]
  rw [he, Matrix.mulVec_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]

/-- The pole-gauge mode has square at most `m / j`. -/
private theorem ramanujanPoleProfile_sq_le {m j : ℕ} (hm : 0 < m) :
    ramanujanPoleProfile m j ^ 2 ≤ (m : ℝ) * (1 / (j : ℝ)) := by
  have htot : (0 : ℝ) < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  have hcoef := BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m j
  have hmode : normalizedRamanujanMode m j ^ 2 ≤ (m : ℝ) := by
    rw [normalizedRamanujanMode_eq_coefficient hm, div_pow, Real.sq_sqrt htot.le]
    have hsq : BezoutValuationIncidence.ramanujanLagCoefficient m j ^ 2 ≤ (m.totient : ℝ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hcoef 2
    have htm : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
    refine (div_le_iff₀ htot).mpr (hsq.trans ?_)
    nlinarith only [htm, htot]
  rw [ramanujanPoleProfile, div_pow, Real.sq_sqrt (Nat.cast_nonneg j), mul_one_div]
  exact div_le_div_of_nonneg_right hmode (Nat.cast_nonneg j)

/-- The mass of a mode on the prefix is at most `m (1 + log M)`. -/
private theorem sum_ramanujanPoleProfile_sq_le {m M : ℕ} (hm : 0 < m) (hM : 1 ≤ M) :
    ∑ j : PrimeHorizonIndex M, ramanujanPoleProfile m j ^ 2 ≤ (m : ℝ) * (1 + Real.log M) := by
  have h1 : ∑ j : PrimeHorizonIndex M, ramanujanPoleProfile m j ^ 2 ≤
      ∑ j : PrimeHorizonIndex M, (m : ℝ) * (1 / ((j : ℕ) : ℝ)) :=
    Finset.sum_le_sum fun j _ => ramanujanPoleProfile_sq_le hm
  refine h1.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m)
  have h2 : ∑ j : PrimeHorizonIndex M, (1 / ((j : ℕ) : ℝ)) = ∑ j ∈ Icc 1 M, (1 / (j : ℝ)) :=
    Finset.sum_coe_sort (Icc 1 M) fun j => 1 / (j : ℝ)
  rw [h2]
  exact RHTower.sum_Icc_one_div_le hM

/-- **The Schur complement keeps the conductor floor on growing blocks.** Half of the conductor floor
survives uniformly in the prefix `M`, the overlap `c ≤ b log log N`, and the conductor bound
`Q ≤ (log N)^{1/32}`. -/
theorem exists_plateauPrefixSchur_floor_on_growing_blocks :
    ∃ (B a b : ℝ) (M₀ : ℕ), 0 < B ∧ 0 < a ∧ 0 < b ∧
      ∀ᶠ N : ℕ in atTop, ∀ M, M₀ ≤ M → ∀ hMN : M ≤ N, ∀ c : ℝ, 1 ≤ c →
        c ≤ b * Real.log (Real.log (N : ℝ)) → c * M ≤ N →
        Real.log M ≤ Real.log (N : ℝ) ^ (1 / 2 : ℝ) →
        ∀ Q : ℕ, (Q : ℝ) ≤ Real.log (N : ℝ) ^ (1 / 32 : ℝ) → ∀ z ∈ conductorSubspace Q N,
          (a / 2 * Real.exp (-B * c)) * ‖z‖ ^ 2 ≤
            tailPart z.ofLp ⬝ᵥ plateauPrefixSchur hMN c *ᵥ tailPart z.ofLp := by
  have hφ := contDiff_transMetzlerProfile
  have hsupp : ∀ x, x ∉ Set.Icc (0 : ℝ) 1 → transMetzlerProfile x = 0 :=
    fun _ hx => transMetzlerProfile_eq_zero hx
  have hmass := integral_transMetzlerProfile_sq_pos
  obtain ⟨B, hB, hfloorAll⟩ := exists_universal_loglog_overlap_coercivity
  obtain ⟨a₀, ha₀, hfloor⟩ := hfloorAll transMetzlerProfile hφ hsupp hmass
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    (eventually_plateauPrefixBlock_posDef.and eventually_plateauPrefix_inverse_quadratic_le)
  obtain ⟨K, hK, hresAll⟩ := exists_completeWeil_linear_conductor_residual_variable_rate hφ hsupp hmass
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = min 1 (1 / (64 * B)) := ⟨_, rfl⟩
  have hb : 0 < b := by rw [hbd]; positivity
  have hb1 : b ≤ 1 := by rw [hbd]; exact min_le_left _ _
  have hbB : B * b ≤ 1 / 64 := by
    have h : b ≤ 1 / (64 * B) := by rw [hbd]; exact min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_left h hB.le
    refine h2.trans_eq ?_
    field_simp
  refine ⟨B, a₀, b, max M₀ 1, hB, ha₀, hb, ?_⟩
  obtain ⟨F, hFd⟩ : ∃ F, F = |completeWeilSelfFinitePart transMetzlerProfile 1| := ⟨_, rfl⟩
  have hF0 : 0 ≤ F := by rw [hFd]; exact abs_nonneg _
  obtain ⟨D₀, hD₀d⟩ : ∃ D₀, D₀ = 1764 + 486 * K := ⟨_, rfl⟩
  have hD₀ : 0 < D₀ := by rw [hD₀d]; positivity
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hξlim : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (1 / 256 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hLlim
  have hα : 2 * B * b < 1 := by nlinarith only [hbB]
  filter_upwards [hfloor (1 / 4) (by norm_num) (by norm_num) b hb hα,
    hresAll (1 / 32) (by norm_num) 64 (by norm_num),
    hξlim.eventually_ge_atTop (2 + F + 80 * D₀ / a₀),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1
      (by norm_num : (0 : ℝ) < 1 / 256) 1),
    eventually_log_nat_le_rpow_36_one_ninth,
    hLlim.eventually_ge_atTop 2000,
    eventually_ge_atTop 1]
    with N hfl hres hξbig hpoly hLX hL2000 hN1' M hMM₀ hMN c hc1 hcb hcMN hlogM Q hQ z hz
  -- the scale `ξ = L^{1/256}`
  obtain ⟨L, hLd⟩ : ∃ L, L = Real.log (N : ℝ) := ⟨_, rfl⟩
  rw [← hLd] at hfl hres hξbig hpoly hLX hL2000 hcb hlogM hQ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hN0 : (0 : ℝ) < N := by linarith only [hN1]
  have hL0 : 0 < L := by linarith only [hL2000]
  have hL1 : 1 ≤ L := by linarith only [hL2000]
  obtain ⟨ξ, hξd⟩ : ∃ ξ, ξ = L ^ (1 / 256 : ℝ) := ⟨_, rfl⟩
  rw [← hξd] at hξbig
  have hξ2 : 2 ≤ ξ := by
    have h : 0 ≤ 80 * D₀ / a₀ := by positivity
    linarith only [hξbig, hF0, h]
  have hξ1 : 1 ≤ ξ := by linarith only [hξ2]
  have hξ0 : 0 < ξ := by linarith only [hξ2]
  have hpow (k : ℕ) : L ^ ((k : ℝ) / 256) = ξ ^ k := by
    rw [hξd, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1
    ring
  have hLξ : L = ξ ^ 256 := by
    have h := hpow 256
    norm_num at h
    exact h
  have hξ8 : L ^ (1 / 32 : ℝ) = ξ ^ 8 := by
    rw [← hpow 8]
    norm_num
  have hξ128 : L ^ (1 / 2 : ℝ) = ξ ^ 128 := by
    rw [← hpow 128]
    norm_num
  have hξ4 : L ^ (1 / ((64 : ℕ) : ℝ)) = ξ ^ 4 := by
    rw [← hpow 4]
    norm_num
  rw [hξ8] at hQ
  rw [hξ128] at hlogM
  have hlogL : Real.log L ≤ ξ := by
    have h : 1 + Real.log L ≤ L ^ (1 / 256 : ℝ) := by simpa only [one_mul, pow_one] using hpoly
    rw [← hξd] at h
    linarith only [h]
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hc0 : 0 < c := by linarith only [hc1]
  have hcξ : c ≤ ξ := by
    refine hcb.trans (le_trans ?_ hlogL)
    exact mul_le_of_le_one_left hlogL0 hb1
  -- the floor at the overlap
  have hexpfloor : 1 / ξ ^ 4 ≤ Real.exp (-B * c) := by
    have h1 : B * c ≤ (1 / 64) * Real.log L := by
      calc B * c ≤ B * (b * Real.log L) := mul_le_mul_of_nonneg_left hcb hB.le
        _ = (B * b) * Real.log L := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hbB hlogL0
    have h2 : ξ ^ 4 = Real.exp ((1 / 64) * Real.log L) := by
      rw [← hpow 4, Real.rpow_def_of_pos hL0]
      congr 1
      ring
    rw [h2, one_div, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith only [h1])
  -- the conductor block
  obtain ⟨Q', hQ'⟩ : ∃ Q', Q' = max Q 2 := ⟨_, rfl⟩
  have hQQ' : Q ≤ Q' := by rw [hQ']; exact le_max_left _ _
  have hQ'2 : 2 ≤ Q' := by rw [hQ']; exact le_max_right _ _
  have hξ8ge : (2 : ℝ) ≤ ξ ^ 8 := hξ2.trans (le_self_pow₀ hξ1 (by norm_num))
  have hQ'ξ : (Q' : ℝ) ≤ ξ ^ 8 := by
    rw [hQ']
    push_cast
    exact max_le hQ hξ8ge
  have hQ'0 : (0 : ℝ) < Q' := by exact_mod_cast (show 0 < Q' by omega)
  have hlogξ : Real.log ξ ≤ ξ := (Real.log_le_sub_one_of_pos hξ0).trans (by linarith only)
  have hL18 : L ^ 18 ≤ (N : ℝ) := by
    have hX0 : 0 ≤ (N : ℝ) ^ (1 / 36 : ℝ) := Real.rpow_nonneg hN0.le _
    calc L ^ 18 ≤ ((N : ℝ) ^ (1 / 36 : ℝ)) ^ 18 := pow_le_pow_left₀ hL0.le hLX 18
      _ = (N : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
          norm_num
      _ ≤ N := by
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hξ8L : ξ ^ 8 ≤ L := by
    rw [hLξ]
    exact pow_le_pow_right₀ hξ1 (by norm_num)
  have hQ'L : (Q' : ℝ) ≤ L := hQ'ξ.trans hξ8L
  have hcL : c ≤ L := hcξ.trans ((le_self_pow₀ hξ1 (by norm_num)).trans hξ8L)
  have hQQN : Q' * Q' ≤ N := by
    have h : (Q' : ℝ) * Q' ≤ N := by
      have h1 : (Q' : ℝ) * Q' ≤ L * L := mul_le_mul hQ'L hQ'L hQ'0.le hL0.le
      have h2 : L * L ≤ L ^ 18 := by
        rw [← sq]
        exact pow_le_pow_right₀ hL1 (by norm_num)
      linarith only [h1, h2, hL18]
    exact_mod_cast h
  have hlogQ' : Real.log (Q' : ℝ) ≤ 8 * ξ := by
    have h := Real.log_le_log hQ'0 hQ'ξ
    rw [Real.log_pow] at h
    push_cast at h
    linarith only [h, hlogξ]
  have hlogN : 4 * Real.log (Q' : ℝ) + 18 ≤ L := by
    have hξ256 : 256 * ξ ^ 2 ≤ L := by
      have hsq : ξ ^ 2 * ξ ^ 8 ≤ ξ ^ 256 := by
        rw [← pow_add]
        exact pow_le_pow_right₀ hξ1 (by norm_num)
      have hξ8big : (256 : ℝ) ≤ ξ ^ 8 := by
        calc (256 : ℝ) = 2 ^ 8 := by norm_num
          _ ≤ ξ ^ 8 := pow_le_pow_left₀ (by norm_num) hξ2 8
      rw [hLξ]
      nlinarith only [hsq, hξ8big, sq_nonneg ξ]
    have hξ24 : ξ ≤ ξ ^ 2 := le_self_pow₀ hξ1 (by norm_num)
    have hξsq : (4 : ℝ) ≤ ξ ^ 2 := by nlinarith only [hξ2]
    linarith only [hlogQ', hξ256, hξ24, hξsq]
  have hcN4 : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) := by
    have he : Real.exp 1 + 3 ≤ 6 := by linarith only [Real.exp_one_lt_d9]
    have h1 : (Real.exp 1 + 3) ^ 2 ≤ 36 := by
      have := pow_le_pow_left₀ (by positivity) he 2
      linarith only [this]
    have hc2 : c ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hc0.le hcL 2
    have hbig : 144 * L ^ 2 ≤ L ^ 18 := by
      have hL3 : L ^ 2 * L ^ 3 ≤ L ^ 18 := by
        rw [← pow_add]
        exact pow_le_pow_right₀ hL1 (by norm_num)
      have hL144 : (144 : ℝ) ≤ L ^ 3 := by
        have : L ≤ L ^ 3 := le_self_pow₀ hL1 (by norm_num)
        linarith only [this, hL2000]
      nlinarith only [hL3, hL144, sq_nonneg L]
    calc 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ 4 * 36 * L ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hc2 (sq_nonneg _) (by norm_num)
      _ = 144 * L ^ 2 := by ring
      _ ≤ L ^ 18 := hbig
      _ ≤ N := hL18
  -- the floor on the block
  have hQfloor : Q' ≤ ⌊L ^ (1 / 4 : ℝ)⌋₊ := by
    apply Nat.le_floor
    refine hQ'ξ.trans ?_
    rw [← hpow 8]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hzQ' : z ∈ conductorSubspace Q' N := conductorSubspace_mono hQQ' N hz
  have hfl' := hfl c hc1 hcb z (conductorSubspace_mono hQfloor N hzQ')
  have henergy : completeWeilEnergy transMetzlerProfile c N z =
      z.ofLp ⬝ᵥ completeWeilMatrix transMetzlerProfile c N *ᵥ z.ofLp := by
    unfold completeWeilEnergy
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, star_trivial]
  rw [henergy] at hfl'
  obtain ⟨hApos, hAinv⟩ := hM₀ M ((le_max_left _ _).trans hMM₀)
  have hA := hApos N hMN c hc0 hcMN
  rw [prefixSchur_tail_eq hMN hA z.ofLp]
  obtain ⟨r, hrd⟩ : ∃ r, r = prefixPart hMN (completeWeilMatrix transMetzlerProfile c N *ᵥ z.ofLp) :=
    ⟨_, rfl⟩
  rw [← hrd]
  have hinv := (hAinv N hMN c hc0 hcMN r).2
  -- the residual of a conductor vector on the prefix
  obtain ⟨a, -, hza⟩ := (mem_conductorSubspace_iff (M := Q') (N := N) (x := z)).mp hzQ'
  have hriesz := (half_and_three_halves_riesz_of_four_log_le hQ'2 hQQN (by rw [← hLd]; exact hlogN) a).1
  rw [← hza] at hriesz
  let E : ℕ → ℝ := completedConductorEnergy transMetzlerProfile c
  let C : ℕ → ℝ := fun m => ∑ j : PrimeHorizonIndex M, ramanujanPoleProfile m j ^ 2
  let resid : ℕ → ℝ := fun m =>
    ‖Matrix.toEuclideanLin (completeWeilMatrix transMetzlerProfile c N)
        (normalizedRamanujanHorizonVector m N) -
      completedConductorEnergy transMetzlerProfile c m • normalizedRamanujanHorizonVector m N‖
  let H : ℝ := ∑ m ∈ Icc 1 Q', (2 * E m ^ 2 * (C m * L⁻¹) + 2 * resid m ^ 2)
  have hrr : r ⬝ᵥ r ≤ (∑ m ∈ Icc 1 Q', a m ^ 2) * H := by
    have hcoord : ∀ j : PrimeHorizonIndex M, r j = ∑ m ∈ Icc 1 Q', a m *
        (completeWeilMatrix transMetzlerProfile c N *ᵥ
          (normalizedRamanujanHorizonVector m N).ofLp) (horizonPrefixMap hMN j) := by
      intro j
      rw [hrd, hza]
      exact completeWeil_mulVec_sum c a _
    have hrow : ∀ m ∈ Icc 1 Q', ∑ j : PrimeHorizonIndex M,
        ((completeWeilMatrix transMetzlerProfile c N *ᵥ
          (normalizedRamanujanHorizonVector m N).ofLp) (horizonPrefixMap hMN j)) ^ 2 ≤
        2 * E m ^ 2 * (C m * L⁻¹) + 2 * resid m ^ 2 := by
      intro m _
      obtain ⟨res, hres'⟩ : ∃ res, res = Matrix.toEuclideanLin
          (completeWeilMatrix transMetzlerProfile c N) (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy transMetzlerProfile c m •
              normalizedRamanujanHorizonVector m N := ⟨_, rfl⟩
      have hpt : ∀ i : PrimeHorizonIndex N,
          (completeWeilMatrix transMetzlerProfile c N *ᵥ
            (normalizedRamanujanHorizonVector m N).ofLp) i =
            E m * (normalizedRamanujanHorizonVector m N).ofLp i + res.ofLp i := by
        intro i
        have h := congrArg (fun v : EuclideanSpace ℝ (PrimeHorizonIndex N) => v.ofLp i) hres'
        simp only [Matrix.toLpLin_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h
        simp only [E]
        linarith only [h]
      have hvec : ∀ j : PrimeHorizonIndex M,
          ((normalizedRamanujanHorizonVector m N).ofLp (horizonPrefixMap hMN j)) ^ 2 =
            ramanujanPoleProfile m j ^ 2 * L⁻¹ := by
        intro j
        have h1 : (normalizedRamanujanHorizonVector m N).ofLp (horizonPrefixMap hMN j) =
            (Real.sqrt L)⁻¹ * ramanujanPoleProfile m j := by
          rw [hLd]
          simp [normalizedRamanujanHorizonVector, ramanujanHorizonVector, horizonPrefixMap]
        rw [h1, mul_pow, inv_pow, Real.sq_sqrt hL0.le]
        ring
      have hresn : ∑ j : PrimeHorizonIndex M, (res.ofLp (horizonPrefixMap hMN j)) ^ 2 ≤
          resid m ^ 2 := by
        have hnorm : resid m ^ 2 = ∑ i : PrimeHorizonIndex N, (res.ofLp i) ^ 2 := by
          simp only [resid]
          rw [← hres', EuclideanSpace.real_norm_sq_eq]
        rw [hnorm]
        have hinj : Function.Injective (horizonPrefixMap hMN) := fun i j h => by
          have hv : (horizonPrefixMap hMN i).val = (horizonPrefixMap hMN j).val := congrArg _ h
          exact Subtype.ext hv
        rw [← Finset.sum_image (f := fun i => (res.ofLp i) ^ 2)
          (s := (Finset.univ : Finset (PrimeHorizonIndex M))) (g := horizonPrefixMap hMN)
          (fun i _ j _ h => hinj h)]
        exact Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
      calc ∑ j : PrimeHorizonIndex M, ((completeWeilMatrix transMetzlerProfile c N *ᵥ
              (normalizedRamanujanHorizonVector m N).ofLp) (horizonPrefixMap hMN j)) ^ 2
          ≤ ∑ j : PrimeHorizonIndex M, (2 * E m ^ 2 *
              ((normalizedRamanujanHorizonVector m N).ofLp (horizonPrefixMap hMN j)) ^ 2 +
              2 * (res.ofLp (horizonPrefixMap hMN j)) ^ 2) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [hpt]
            nlinarith only [sq_nonneg (E m * (normalizedRamanujanHorizonVector m N).ofLp
              (horizonPrefixMap hMN j) - res.ofLp (horizonPrefixMap hMN j))]
        _ = 2 * E m ^ 2 * (C m * L⁻¹) +
              2 * ∑ j : PrimeHorizonIndex M, (res.ofLp (horizonPrefixMap hMN j)) ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
            congr 2
            simp only [hvec, C, Finset.sum_mul]
        _ ≤ _ := by linarith only [hresn]
    have hdot : r ⬝ᵥ r = ∑ j : PrimeHorizonIndex M, r j ^ 2 := by
      simp only [dotProduct, sq]
    rw [hdot]
    calc ∑ j : PrimeHorizonIndex M, r j ^ 2
        ≤ ∑ j : PrimeHorizonIndex M, ((∑ m ∈ Icc 1 Q', a m ^ 2) *
            ∑ m ∈ Icc 1 Q', ((completeWeilMatrix transMetzlerProfile c N *ᵥ
              (normalizedRamanujanHorizonVector m N).ofLp) (horizonPrefixMap hMN j)) ^ 2) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [hcoord]
          exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ m ∈ Icc 1 Q', a m ^ 2) * ∑ m ∈ Icc 1 Q', ∑ j : PrimeHorizonIndex M,
            ((completeWeilMatrix transMetzlerProfile c N *ᵥ
              (normalizedRamanujanHorizonVector m N).ofLp) (horizonPrefixMap hMN j)) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  -- each conductor costs at most `m D₀ / ξ^120`
  have hξ120 : 0 < ξ ^ 120 := by positivity
  have hterm : ∀ m ∈ Icc 1 Q', 2 * E m ^ 2 * (C m * L⁻¹) + 2 * resid m ^ 2 ≤
      (m : ℝ) * (D₀ / ξ ^ 120) := by
    intro m hm
    obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hmξ : (m : ℝ) ≤ ξ ^ 8 := (show (m : ℝ) ≤ Q' by exact_mod_cast hmQ).trans hQ'ξ
    have hlogm : Real.log (m : ℝ) ≤ 8 * ξ := by
      have h := Real.log_le_log hm0 hmξ
      rw [Real.log_pow] at h
      push_cast at h
      linarith only [h, hlogξ]
    have hlogm0 : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
    -- the conductor energy
    have hEup := completedConductorEnergy_le_of_one_le hφ hsupp hmass hc1 (m := m) hm1
    have hElow := RenormalizedArithmeticPotentialTheory.log_conductor_sub_log_overlap_le_completedEnergy
      hφ hsupp hmass hc0 (m := m) hm1
    have hc4 : c ^ 4 ≤ ξ ^ 4 := pow_le_pow_left₀ hc0.le hcξ 4
    have hξ14 : ξ ≤ ξ ^ 4 := le_self_pow₀ hξ1 (by norm_num)
    have hF4 : F ≤ ξ ^ 4 := by
      have h : 0 ≤ 80 * D₀ / a₀ := by positivity
      linarith only [hξbig, h, hξ14]
    have hlogc : Real.log c ≤ ξ :=
      (Real.log_le_sub_one_of_pos hc0).trans (by linarith only [hcξ])
    have hEabs : |E m| ≤ 21 * ξ ^ 4 := by
      rw [abs_le]
      constructor
      · have hmin : -F ≤ min 0 (completeWeilSelfFinitePart transMetzlerProfile 1) := by
          rw [hFd]
          exact le_min (neg_nonpos.mpr (abs_nonneg _)) (neg_abs_le _)
        change _ ≤ completedConductorEnergy transMetzlerProfile c m
        linarith only [hElow, hmin, hlogm0, hlogc, hF4, hξ14, pow_pos hξ0 4]
      · change completedConductorEnergy transMetzlerProfile c m ≤ _
        rw [← hFd] at hEup
        linarith only [hEup, hlogm, hc4, hF4, hξ14, pow_pos hξ0 4]
    have hE2 : E m ^ 2 ≤ 441 * ξ ^ 8 := by
      rw [← sq_abs]
      calc |E m| ^ 2 ≤ (21 * ξ ^ 4) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hEabs 2
        _ = 441 * ξ ^ 8 := by ring
    -- the prefix mass of the mode
    have hM1 : 1 ≤ M := (le_max_right _ _).trans hMM₀
    have hCle : C m ≤ (m : ℝ) * (1 + Real.log M) := sum_ramanujanPoleProfile_sq_le hm1 hM1
    have hξ128 : 1 ≤ ξ ^ 128 := one_le_pow₀ hξ1
    have hξ1280 : 0 < ξ ^ 128 := by positivity
    have hLinv : L⁻¹ = 1 / ξ ^ 256 := by rw [hLξ, one_div]
    have hCL : C m * L⁻¹ ≤ (m : ℝ) * (2 / ξ ^ 128) := by
      have hlogM1 : 1 + Real.log M ≤ 2 * ξ ^ 128 := by linarith only [hlogM, hξ128]
      have h1 : C m ≤ (m : ℝ) * (2 * ξ ^ 128) :=
        hCle.trans (mul_le_mul_of_nonneg_left hlogM1 hm0.le)
      have hinv0 : 0 ≤ L⁻¹ := (inv_pos.mpr hL0).le
      have h2 := mul_le_mul_of_nonneg_right h1 hinv0
      refine h2.trans_eq ?_
      rw [hLinv, show (256 : ℕ) = 128 + 128 by norm_num, pow_add]
      field_simp
    have hCnn : 0 ≤ C m * L⁻¹ :=
      mul_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (inv_pos.mpr hL0).le
    have hfirst : 2 * E m ^ 2 * (C m * L⁻¹) ≤ (m : ℝ) * (1764 / ξ ^ 120) := by
      calc 2 * E m ^ 2 * (C m * L⁻¹) ≤ 2 * (441 * ξ ^ 8) * ((m : ℝ) * (2 / ξ ^ 128)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hE2 (by norm_num)) hCL hCnn (by positivity)
        _ = _ := by
            rw [show (128 : ℕ) = 120 + 8 by norm_num, pow_add]
            field_simp
            ring
    -- the residual of the mode
    have hr := hres m hm1 (by rw [hξ8]; exact hmξ) c hc1 hcN4
    rw [hξ4] at hr
    change resid m ^ 2 ≤ _ at hr
    have hc3 : c ^ 3 ≤ ξ ^ 3 := pow_le_pow_left₀ hc0.le hcξ 3
    have hc5 : c ^ 5 ≤ ξ ^ 10 :=
      (pow_le_pow_left₀ hc0.le hcξ 5).trans (pow_le_pow_right₀ hξ1 (by norm_num))
    have hc10 : c ^ 10 ≤ ξ ^ 10 := pow_le_pow_left₀ hc0.le hcξ 10
    have hLN : (L / N) ^ 2 ≤ 1 / L := by
      have h2 : L * L ≤ N := by
        have h3 : L * L ≤ L ^ 18 := by
          rw [← sq]
          exact pow_le_pow_right₀ hL1 (by norm_num)
        exact h3.trans hL18
      have h4 : L / N ≤ 1 / L := by
        rw [div_le_div_iff₀ hN0 hL0]
        linarith only [h2]
      have h5 : 0 ≤ L / N := by positivity
      have hone : 1 / L ≤ 1 := (div_le_one hL0).mpr hL1
      have h6 := pow_le_pow_left₀ h5 h4 2
      have hL1inv : 0 ≤ 1 / L := by positivity
      nlinarith only [h6, hone, hL1inv]
    have hrate : c ^ 5 / L + c ^ 10 * (L / N) ^ 2 + c ^ 3 * ξ ^ 4 / L ≤ 3 * (ξ ^ 10 / L) := by
      have h1 : c ^ 5 / L ≤ ξ ^ 10 / L := div_le_div_of_nonneg_right hc5 hL0.le
      have h2 : c ^ 10 * (L / N) ^ 2 ≤ ξ ^ 10 / L := by
        have := mul_le_mul hc10 hLN (sq_nonneg _) (by positivity)
        refine this.trans_eq ?_
        ring
      have h3 : c ^ 3 * ξ ^ 4 / L ≤ ξ ^ 10 / L := by
        refine div_le_div_of_nonneg_right ?_ hL0.le
        have := mul_le_mul_of_nonneg_right hc3 (pow_nonneg hξ0.le 4)
        refine this.trans ?_
        rw [← pow_add]
        exact pow_le_pow_right₀ hξ1 (by norm_num)
      linarith only [h1, h2, h3]
    have hlog1 : (1 + Real.log m) ^ 2 ≤ 81 * ξ ^ 2 := by
      have h1 : 1 + Real.log (m : ℝ) ≤ 9 * ξ := by linarith only [hlogm, hξ1]
      calc (1 + Real.log (m : ℝ)) ^ 2 ≤ (9 * ξ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        _ = 81 * ξ ^ 2 := by ring
    have hsecond : resid m ^ 2 ≤ (m : ℝ) * (243 * K / ξ ^ 120) := by
      refine hr.trans ?_
      have hrate0 : 0 ≤ c ^ 5 / L + c ^ 10 * (L / N) ^ 2 + c ^ 3 * ξ ^ 4 / L := by positivity
      have hmm : (m : ℝ) * (1 + Real.log m) ^ 2 ≤ (m : ℝ) * (81 * ξ ^ 2) :=
        mul_le_mul_of_nonneg_left hlog1 hm0.le
      have hprod : K * ((m : ℝ) * (1 + Real.log m) ^ 2) *
          (c ^ 5 / L + c ^ 10 * (L / N) ^ 2 + c ^ 3 * ξ ^ 4 / L) ≤
          K * ((m : ℝ) * (81 * ξ ^ 2)) * (3 * (ξ ^ 10 / L)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmm hK.le) hrate hrate0 (by positivity)
      refine hprod.trans ?_
      have hξpow : ξ ^ 2 * (ξ ^ 10 / L) ≤ 1 / ξ ^ 120 := by
        have e : ξ ^ 2 * (ξ ^ 10 / L) = 1 / ξ ^ 244 := by
          rw [hLξ, show (256 : ℕ) = 2 + 10 + 244 by norm_num, pow_add, pow_add]
          field_simp
        rw [e]
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hξ1 (by norm_num))
      have hfinal := mul_le_mul_of_nonneg_left hξpow
        (show 0 ≤ 243 * K * (m : ℝ) by positivity)
      calc K * ((m : ℝ) * (81 * ξ ^ 2)) * (3 * (ξ ^ 10 / L))
          = 243 * K * (m : ℝ) * (ξ ^ 2 * (ξ ^ 10 / L)) := by ring
        _ ≤ 243 * K * (m : ℝ) * (1 / ξ ^ 120) := hfinal
        _ = _ := by ring
    have hsum : (m : ℝ) * (1764 / ξ ^ 120) + 2 * ((m : ℝ) * (243 * K / ξ ^ 120)) =
        (m : ℝ) * (D₀ / ξ ^ 120) := by
      rw [hD₀d]
      ring
    linarith only [hfirst, hsecond, hsum]
  -- the total prefix mass
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun m _ => by
    have hC0 : 0 ≤ C m := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hLinv : 0 ≤ L⁻¹ := (inv_pos.mpr hL0).le
    positivity
  have hHle : H ≤ D₀ / ξ ^ 104 := by
    have h1 : H ≤ ∑ m ∈ Icc 1 Q', (m : ℝ) * (D₀ / ξ ^ 120) := Finset.sum_le_sum hterm
    have h2 : ∑ m ∈ Icc 1 Q', (m : ℝ) ≤ (Q' : ℝ) * Q' := by
      have hb : ∀ m ∈ Icc 1 Q', (m : ℝ) ≤ Q' := fun m hm => by
        exact_mod_cast (mem_Icc.mp hm).2
      have h3 := Finset.sum_le_card_nsmul _ _ _ hb
      simpa only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] using h3
    have hQ2 : (Q' : ℝ) * Q' ≤ ξ ^ 16 := by
      have h3 := mul_le_mul hQ'ξ hQ'ξ hQ'0.le (by positivity)
      refine h3.trans_eq ?_
      ring
    rw [← Finset.sum_mul] at h1
    have hcoef0 : 0 ≤ D₀ / ξ ^ 120 := by positivity
    have h4 := mul_le_mul_of_nonneg_right (h2.trans hQ2) hcoef0
    refine h1.trans (h4.trans_eq ?_)
    rw [show (120 : ℕ) = 16 + 104 by norm_num, pow_add]
    field_simp
  have hA2 : ∑ m ∈ Icc 1 Q', a m ^ 2 ≤ 2 * ‖z‖ ^ 2 := by linarith only [hriesz]
  have hz2 : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
  have hrr2 : r ⬝ᵥ r ≤ 2 * ‖z‖ ^ 2 * (D₀ / ξ ^ 104) :=
    hrr.trans (mul_le_mul hA2 hHle hH0 (by positivity))
  -- the floor pays the debit
  have hdebit : 40 * (D₀ / ξ ^ 104) ≤ a₀ / 2 * Real.exp (-B * c) := by
    have h80 : 80 * D₀ ≤ a₀ * ξ ^ 100 := by
      have h : 80 * D₀ / a₀ ≤ ξ := by
        have hnn : 0 ≤ F := hF0
        linarith only [hξbig, hnn]
      have h2 := (div_le_iff₀ ha₀).mp h
      have h3 : ξ ≤ ξ ^ 100 := le_self_pow₀ hξ1 (by norm_num)
      have h4 := mul_le_mul_of_nonneg_left h3 ha₀.le
      linarith only [h2, h4]
    have hstep : 40 * (D₀ / ξ ^ 104) ≤ a₀ / 2 * (1 / ξ ^ 4) := by
      rw [show (104 : ℕ) = 100 + 4 by norm_num, pow_add]
      have hξ4pos : 0 < ξ ^ 4 := by positivity
      have hξ100pos : 0 < ξ ^ 100 := by positivity
      rw [show 40 * (D₀ / (ξ ^ 100 * ξ ^ 4)) = (40 * D₀ / ξ ^ 100) * (1 / ξ ^ 4) by
        field_simp]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [div_le_iff₀ hξ100pos]
      linarith only [h80]
    exact hstep.trans (mul_le_mul_of_nonneg_left hexpfloor (by positivity))
  have hinv' : r ⬝ᵥ (plateauPrefixBlock hMN c)⁻¹ *ᵥ r ≤ (a₀ / 2 * Real.exp (-B * c)) * ‖z‖ ^ 2 := by
    refine hinv.trans ?_
    calc 20 * (r ⬝ᵥ r) ≤ 20 * (2 * ‖z‖ ^ 2 * (D₀ / ξ ^ 104)) := by gcongr
      _ = (40 * (D₀ / ξ ^ 104)) * ‖z‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdebit hz2
  have hsplitfloor : (a₀ * Real.exp (-B * c)) * ‖z‖ ^ 2 =
      (a₀ / 2 * Real.exp (-B * c)) * ‖z‖ ^ 2 + (a₀ / 2 * Real.exp (-B * c)) * ‖z‖ ^ 2 := by ring
  linarith only [hfl', hinv', hsplitfloor]

end GaloisForLFunctions.CompletedArithmeticForms

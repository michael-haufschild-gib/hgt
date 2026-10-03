import GaloisForLFunctions.HTGeometry.PrimeHodgeSquareCommutatorGrowth
import GaloisForLFunctions.HTGeometry.HilbertSchmidtHeatFlowDerivative
import GaloisForLFunctions.HTGeometry.TraceClassQuantumCorner
import GaloisForLFunctions.RHTower.PrimeLogCongruenceIdealExit
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import GaloisForLFunctions.RHTower.DirectSubunitEscapeCapacityFusion

/-!
# The prime-log congruence orbit: ideal exit and cubic jet

Let `𝖳_d` be the prime–Hodge integral–nuclear defect on `ℓ²(ℕ × Primes)` and
`P_{-u} e_{(n,p)} = p^u e_{(n,p)}` the inverse prime heat.  The congruence `P_{-u}𝖳_dP_{-u}` has the
matrix `p^u q^u 𝖳_d((n,p),(m,q))`.

* **(PLCIE.3)** It is the matrix of a trace-class operator exactly when `u < d`: for `u < d` it is
  `κ_{d,u} 𝖳_{d-u}` with `κ_{d,u} = (d/(d-u)) U_{d-u}/U_d > 0`, and a trace-class operator has a
  summable diagonal, which forces `Σ_p p^{2u} w_d(p) < ∞`, i.e. `u < d`.  Hence
  `d = sup{u ≥ 0 : P_{-u}𝖳_dP_{-u} is trace class}`.
* Every finite-prime compression is trace class for every `u`, and compressions at different times
  differ by the invertible diagonal gauge `p^{u-u'}`.
* **(PLCIE.5)** The forward orbit `u ↦ P_u𝖳_dP_u` on `[0, ∞)` is three times differentiable in
  operator norm (with Hilbert–Schmidt convergent difference quotients) and
  `d³/du³ (P_u𝖳_dP_u)|_{u=0} = -S_Λ³(𝖳_d) = -8 Φ ⊗ |b_d⟩⟨b_d|`.
-/

open Filter Topology Set
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower GaloisForLFunctions

local notation "ℍ" => PrimeHodgeHistoryHilbert

variable {d u : ℝ}

/-! ## Matrix entries -/

theorem inner_single_primeHodgeHistoryDefectOperator (hd : 0 < d) (a b : PrimeHodgeHistoryIndex) :
    ⟪(lp.single 2 a (1 : ℂ) : ℍ), primeHodgeHistoryDefectOperator hd (lp.single 2 b 1)⟫_ℂ =
      primeHodgeHistoryDefectKernel d (a, b) := by
  rw [primeHodgeHistoryDefectOperator, lp.inner_single_left, HilbertSchmidt.toOperator_single]
  simp

/-- A kernel is trace class if it is the matrix of a Schatten-one operator. -/
def IsTraceClassKernel (K : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex → ℂ) : Prop :=
  ∃ X : ℍ →L[ℂ] ℍ, MemSchattenClass 1 X ∧
    ∀ a b, ⟪(lp.single 2 a (1 : ℂ) : ℍ), X (lp.single 2 b 1)⟫_ℂ = K (a, b)

/-- The matrix of the congruence `P_{-u}𝖳_dP_{-u}`. -/
def congruenceKernel (d u : ℝ) (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) : ℂ :=
  ((((ab.1.2 : ℝ) ^ u * (ab.2.2 : ℝ) ^ u : ℝ)) : ℂ) * primeHodgeHistoryDefectKernel d ab

/-! ## Before the exit: a rescaled aperture -/

/-- The congruence ratio `κ_{d,u} = (d/(d-u)) U_{d-u}/U_d`. -/
def congruenceRatio (d u : ℝ) : ℝ :=
  d / (d - u) * (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (d - u) /
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)

theorem congruenceRatio_pos (hd : 0 < d) (hu : u < d) : 0 < congruenceRatio d u :=
  mul_pos (div_pos hd (sub_pos.2 hu))
    (div_pos (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos (sub_pos.2 hu))
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd))

/-- **(PLCIE.1), normalized.**  `p^{2u} μ_d(p) = κ_{d,u} μ_{d-u}(p)` for `u < d`. -/
theorem rpow_mul_primeFormationLaw (hd : 0 < d) (hu : u < d) (p : Nat.Primes) :
    (p : ℝ) ^ (2 * u) * primeFormationLaw d p = congruenceRatio d u * primeFormationLaw (d - u) p := by
  have h := primeLogCongruenceWeight_eq_rescaled_transport hd hu p
  rw [primeLogCongruenceWeight] at h
  have hU := (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).ne'
  have hU' := (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos (sub_pos.2 hu)).ne'
  rw [primeFormationLaw, primeFormationLaw, congruenceRatio, ← mul_div_assoc, h]
  field_simp

theorem rpow_mul_stokesEntry (hd : 0 < d) (hu : u < d) (p q : Nat.Primes) :
    (p : ℝ) ^ u * (q : ℝ) ^ u * stokesEntry d p q = congruenceRatio d u * stokesEntry (d - u) p q := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hsq : ∀ x : ℝ, 0 ≤ x → x ^ (2 * u) = (x ^ u) ^ 2 := fun x hx => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    ring_nf
  have hκ := congruenceRatio_pos hd hu
  have hμp := (primeFormationLaw_pos hd p).le
  have hμq := (primeFormationLaw_pos hd q).le
  have hμp' := (primeFormationLaw_pos (sub_pos.2 hu) p).le
  have hμq' := (primeFormationLaw_pos (sub_pos.2 hu) q).le
  have hkey : (p : ℝ) ^ u * (q : ℝ) ^ u *
      Real.sqrt (primeFormationLaw d p * primeFormationLaw d q) =
      congruenceRatio d u * Real.sqrt (primeFormationLaw (d - u) p * primeFormationLaw (d - u) q) := by
    have e1 : (p : ℝ) ^ u * (q : ℝ) ^ u * Real.sqrt (primeFormationLaw d p * primeFormationLaw d q) =
        Real.sqrt ((p : ℝ) ^ (2 * u) * primeFormationLaw d p *
          ((q : ℝ) ^ (2 * u) * primeFormationLaw d q)) := by
      rw [hsq _ hp0, hsq _ hq0, show ((p : ℝ) ^ u) ^ 2 * primeFormationLaw d p *
          (((q : ℝ) ^ u) ^ 2 * primeFormationLaw d q) =
          ((p : ℝ) ^ u * (q : ℝ) ^ u) ^ 2 * (primeFormationLaw d p * primeFormationLaw d q) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg (Real.rpow_nonneg hp0 _)
          (Real.rpow_nonneg hq0 _))]
    rw [e1, rpow_mul_primeFormationLaw hd hu p, rpow_mul_primeFormationLaw hd hu q,
      show congruenceRatio d u * primeFormationLaw (d - u) p *
          (congruenceRatio d u * primeFormationLaw (d - u) q) =
          congruenceRatio d u ^ 2 * (primeFormationLaw (d - u) p * primeFormationLaw (d - u) q) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ.le]
  rw [stokesEntry, stokesEntry, ← mul_assoc, hkey, mul_assoc]

/-- Before the exit the congruence is a positive multiple of the defect at aperture `d - u`. -/
theorem congruenceKernel_eq_smul (hd : 0 < d) (hu : u < d) :
    congruenceKernel d u = (congruenceRatio d u : ℂ) • primeHodgeHistoryDefectKernel (d - u) := by
  funext ab
  obtain ⟨⟨n, p⟩, ⟨m, q⟩⟩ := ab
  simp only [congruenceKernel, Pi.smul_apply, smul_eq_mul, primeHodgeHistoryDefectKernel]
  split_ifs
  · rw [normalizedStokesPrimeKernel_eq_stokesEntry hd,
      normalizedStokesPrimeKernel_eq_stokesEntry (sub_pos.2 hu)]
    have h := rpow_mul_stokesEntry hd hu p q
    calc (((p : ℝ) ^ u * (q : ℝ) ^ u : ℝ) : ℂ) * ((PrimeHodgeHistory.w n : ℂ) * (stokesEntry d p q : ℂ))
        = ((PrimeHodgeHistory.w n * ((p : ℝ) ^ u * (q : ℝ) ^ u * stokesEntry d p q) : ℝ) : ℂ) := by
          push_cast
          ring
      _ = _ := by
          rw [h]
          push_cast
          ring
  · simp

/-! ## (PLCIE.3) The trace-ideal exit -/

theorem isTraceClassKernel_congruence_of_lt (hd : 0 < d) (hu : u < d) :
    IsTraceClassKernel (congruenceKernel d u) := by
  refine ⟨(congruenceRatio d u : ℂ) • primeHodgeHistoryDefectOperator (sub_pos.2 hu),
    memSchattenClass_one_smul (primeHodgeHistoryDefectOperator_memSchattenClass_one (sub_pos.2 hu)) _,
    fun a b => ?_⟩
  rw [congruenceKernel_eq_smul hd hu, smul_apply, inner_smul_right,
    inner_single_primeHodgeHistoryDefectOperator, Pi.smul_apply, smul_eq_mul]

theorem congruenceKernel_diagonal (hd : 0 < d) (p : Nat.Primes) :
    congruenceKernel d u ((0, p), (0, p)) =
      (((PrimeHodgeHistory.w 0 / gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d) *
        primeLogCongruenceWeight d u p : ℝ) : ℂ) := by
  rw [congruenceKernel, primeHodgeHistoryDefectKernel, if_pos rfl,
    normalizedStokesPrimeKernel_diagonal hd, primeLogCongruenceWeight]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  rw [show (2 * u) = u + u by ring, Real.rpow_add hp]
  push_cast
  ring

theorem lt_of_isTraceClassKernel_congruence (hd : 0 < d) (hu0 : 0 ≤ u)
    (h : IsTraceClassKernel (congruenceKernel d u)) : u < d := by
  obtain ⟨X, hX, hXe⟩ := h
  have hsum := RHTower.MemSchattenClass.one_summable_inner_diag_basis hX
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex)
  simp_rw [HilbertSchmidt.lpBasis_apply, hXe] at hsum
  have h0 := hsum.comp_injective (Prod.mk_right_injective (0 : ℕ))
  have hreal : Summable fun p : Nat.Primes =>
      (PrimeHodgeHistory.w 0 / gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d) *
        primeLogCongruenceWeight d u p := by
    refine Complex.summable_ofReal.1 (h0.congr fun p => ?_)
    simp only [Function.comp]
    exact congruenceKernel_diagonal hd p
  have hc : PrimeHodgeHistory.w 0 / gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d ≠ 0 :=
    (div_pos (PrimeHodgeHistory.w_pos 0) (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd)).ne'
  exact (summable_primeLogCongruenceWeight_iff hd hu0).1 ((summable_mul_left_iff hc).1 hreal)

/-- **(PLCIE.2)–(PLCIE.3), operator form.**  `P_{-u}𝖳_dP_{-u}` is trace class iff `u < d`. -/
theorem isTraceClassKernel_congruence_iff (hd : 0 < d) (hu0 : 0 ≤ u) :
    IsTraceClassKernel (congruenceKernel d u) ↔ u < d :=
  ⟨lt_of_isTraceClassKernel_congruence hd hu0, isTraceClassKernel_congruence_of_lt hd⟩

/-- **(PLCIE.3)** `d = sup{u ≥ 0 : P_{-u}𝖳_dP_{-u} is trace class}`. -/
theorem sSup_traceClass_congruence (hd : 0 < d) :
    sSup {u : ℝ | 0 ≤ u ∧ IsTraceClassKernel (congruenceKernel d u)} = d := by
  have hset : {u : ℝ | 0 ≤ u ∧ IsTraceClassKernel (congruenceKernel d u)} = Ico 0 d := by
    ext u
    simp only [mem_setOf_eq, mem_Ico]
    exact ⟨fun h => ⟨h.1, (isTraceClassKernel_congruence_iff hd h.1).1 h.2⟩,
      fun h => ⟨h.1, (isTraceClassKernel_congruence_iff hd h.1).2 h.2⟩⟩
  rw [hset, csSup_Ico hd]

/-! ## Finite-prime compressions -/

/-- The finite gauge symbol `1_F(p) p^u`. -/
def finiteGaugeSymbol (F : Finset Nat.Primes) (u : ℝ) (a : PrimeHodgeHistoryIndex) : ℂ :=
  if a.2 ∈ F then (((a.2 : ℝ) ^ u : ℝ) : ℂ) else 0

theorem norm_finiteGaugeSymbol_le (F : Finset Nat.Primes) (u : ℝ) (a : PrimeHodgeHistoryIndex) :
    ‖finiteGaugeSymbol F u a‖ ≤ ∑ p ∈ F, (p : ℝ) ^ u := by
  unfold finiteGaugeSymbol
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact Finset.single_le_sum (f := fun p : Nat.Primes => (p : ℝ) ^ u)
      (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) h
  · rw [norm_zero]
    exact Finset.sum_nonneg fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- The compression `1_F P_{-u}`. -/
def finiteGauge (F : Finset Nat.Primes) (u : ℝ) : ℍ →L[ℂ] ℍ :=
  lpDiagonalCLM (finiteGaugeSymbol F u)
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (norm_finiteGaugeSymbol_le F u)

theorem adjoint_finiteGauge (F : Finset Nat.Primes) (u : ℝ) :
    ContinuousLinearMap.adjoint (finiteGauge F u) = finiteGauge F u := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun a => ?_
  have hc : starRingEnd ℂ (finiteGaugeSymbol F u a) = finiteGaugeSymbol F u a := by
    unfold finiteGaugeSymbol
    split_ifs <;> simp
  rw [show ((finiteGauge F u x : ℍ) : PrimeHodgeHistoryIndex → ℂ) a = finiteGaugeSymbol F u a * x a
      from rfl, show ((finiteGauge F u y : ℍ) : PrimeHodgeHistoryIndex → ℂ) a =
      finiteGaugeSymbol F u a * y a from rfl, RCLike.inner_apply, RCLike.inner_apply, map_mul, hc]
  ring

/-- The matrix of the finite compression `1_F P_{-u}𝖳_dP_{-u} 1_F`. -/
def compressedCongruenceKernel (F : Finset Nat.Primes) (d u : ℝ)
    (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) : ℂ :=
  if ab.1.2 ∈ F ∧ ab.2.2 ∈ F then congruenceKernel d u ab else 0

/-- **Finite stages never exit.**  Every finite-prime compression is trace class for every `u`. -/
theorem isTraceClassKernel_compressedCongruence (hd : 0 < d) (F : Finset Nat.Primes) (u : ℝ) :
    IsTraceClassKernel (compressedCongruenceKernel F d u) := by
  refine ⟨(finiteGauge F u ∘L primeHodgeHistoryDefectOperator hd) ∘L
      ContinuousLinearMap.adjoint (finiteGauge F u),
    memSchattenClass_one_sandwich _ (primeHodgeHistoryDefectOperator_memSchattenClass_one hd),
    fun a b => ?_⟩
  rw [adjoint_finiteGauge, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, finiteGauge,
    lpDiagonalCLM_single, lp.inner_single_left, lpDiagonalCLM_apply,
    show (lp.single 2 b (finiteGaugeSymbol F u b) : ℍ) =
      finiteGaugeSymbol F u b • lp.single 2 b 1 by rw [← lp.single_smul, smul_eq_mul, mul_one],
    map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have he : (primeHodgeHistoryDefectOperator hd (lp.single 2 b (1 : ℂ)) : PrimeHodgeHistoryIndex → ℂ) a =
      primeHodgeHistoryDefectKernel d (a, b) := HilbertSchmidt.toOperator_single _ a b
  rw [he, compressedCongruenceKernel, congruenceKernel]
  unfold finiteGaugeSymbol
  by_cases ha : a.2 ∈ F <;> by_cases hb : b.2 ∈ F <;> simp [ha, hb]
  ring

/-- **The gauge crossing.**  Compressions at times `u` and `u'` differ by the invertible diagonal
gauge `p^{u-u'}`. -/
theorem compressedCongruenceKernel_gauge (F : Finset Nat.Primes) (d u u' : ℝ)
    (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) :
    compressedCongruenceKernel F d u ab =
      (((ab.1.2 : ℝ) ^ (u - u') : ℝ) : ℂ) * compressedCongruenceKernel F d u' ab *
        (((ab.2.2 : ℝ) ^ (u - u') : ℝ) : ℂ) := by
  have hp : (0 : ℝ) < (ab.1.2 : ℝ) := by exact_mod_cast ab.1.2.property.pos
  have hq : (0 : ℝ) < (ab.2.2 : ℝ) := by exact_mod_cast ab.2.2.property.pos
  unfold compressedCongruenceKernel congruenceKernel
  split_ifs
  · rw [show u = (u - u') + u' by ring, Real.rpow_add hp, Real.rpow_add hq]
    simp only [sub_add_cancel]
    push_cast
    ring
  · ring

theorem rpow_gauge_pos (p : Nat.Primes) (t : ℝ) : 0 < ((p : ℝ) ^ t) :=
  Real.rpow_pos_of_pos (by exact_mod_cast p.property.pos) t

/-! ## (PLCIE.4) The exit ray -/

/-- **(PLCIE.4), projective form.**  The exit density `log(p) w_{d,d}(p) = 8d log²p/p` lies on the
ray of the Xi formation metric anomaly `(115/(864a⁴)) log²p/p` of a strict-right Xi copy: the two
prime sequences are proportional with a prime-independent positive factor. -/
theorem exit_density_eq_smul_formationMetricAnomaly (hd : 0 < d) (q : XiRightZeroCopy) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : Nat.Primes,
      Real.log (p : ℝ) * primeLogCongruenceWeight d d p =
        c * xiWardCubicFormationMetricAnomalyTraceWeight q p := by
  have ha := xiRightCenteredZero_re_pos q
  refine ⟨8 * d * (864 * (xiRightCenteredZero q).re ^ 4 / 115), by positivity, fun p => ?_⟩
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  rw [log_mul_primeLogCongruenceWeight_exit_eq hd, xiWardCubicFormationMetricAnomalyTraceWeight,
    gammaSewnSynchronizedRecoveryQuadraticCost_singleton]
  field_simp
  ring

/-! ## (PLCIE.5) The cubic jet of the forward orbit -/

/-- The rate `λ_a + λ_b` of the forward congruence. -/
def congruenceRate (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) : ℝ :=
  Real.log (ab.1.2 : ℝ) + Real.log (ab.2.2 : ℝ)

theorem one_le_congruenceRate (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) :
    1 ≤ congruenceRate ab := by
  have h2 : ∀ p : Nat.Primes, Real.log 2 ≤ Real.log (p : ℝ) := fun p =>
    Real.log_le_log (by norm_num) (by exact_mod_cast p.property.two_le)
  have := Real.log_two_gt_d9
  have h1 := h2 ab.1.2
  have h3 := h2 ab.2.2
  unfold congruenceRate
  linarith

theorem congruenceRate_nonneg (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) :
    0 ≤ congruenceRate ab :=
  zero_le_one.trans (one_le_congruenceRate ab)

theorem sq_rate_pow_mul_norm_le (hd : 0 < d) {k : ℕ} (hk : k ≤ 3)
    (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) :
    (congruenceRate ab ^ k * ‖primeHodgeHistoryDefectKernel d ab‖) ^ 2 ≤
      historyBirthMass d ab.1 * historyBirthMass d ab.2 := by
  have hnn : ∀ np, 0 ≤ historyBirthMass d np := fun np =>
    mul_nonneg (mul_nonneg (by norm_num) (PrimeHodgeHistory.w_pos _).le) (sq_nonneg _)
  obtain ⟨⟨n, p⟩, ⟨m, q⟩⟩ := ab
  by_cases hnm : n = m
  · subst hnm
    have hw := (PrimeHodgeHistory.w_pos n).le
    have hs1 : 1 ≤ congruenceRate ((n, p), (n, q)) := one_le_congruenceRate _
    have hclock := congrArg norm (primeHodgeCubicClock_normalizedStokesKernel hd p q)
    rw [norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (add_pos (primeClock_pos p) (primeClock_pos q)).le, norm_mul,
      norm_mul, norm_star] at hclock
    have hpow : congruenceRate ((n, p), (n, q)) ^ k ≤ congruenceRate ((n, p), (n, q)) ^ 3 :=
      pow_le_pow_right₀ hs1 hk
    have hA := norm_nonneg (normalizedStokesPrimeKernel d (p, q))
    have hbound : congruenceRate ((n, p), (n, q)) ^ k *
        ‖primeHodgeHistoryDefectKernel d ((n, p), (n, q))‖ ≤
        PrimeHodgeHistory.w n * (8 * ‖primeHodgeCubicBirthVector d p‖ *
          ‖primeHodgeCubicBirthVector d q‖) := by
      rw [primeHodgeHistoryDefectKernel, if_pos rfl, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hw]
      calc congruenceRate ((n, p), (n, q)) ^ k * (PrimeHodgeHistory.w n *
            ‖normalizedStokesPrimeKernel d (p, q)‖)
          ≤ congruenceRate ((n, p), (n, q)) ^ 3 * (PrimeHodgeHistory.w n *
            ‖normalizedStokesPrimeKernel d (p, q)‖) :=
            mul_le_mul_of_nonneg_right hpow (mul_nonneg hw hA)
        _ = PrimeHodgeHistory.w n * ((Real.log (p : ℝ) + Real.log (q : ℝ)) ^ 3 *
            ‖normalizedStokesPrimeKernel d (p, q)‖) := by
            rw [congruenceRate]
            ring
        _ = _ := by
            rw [hclock]
            norm_num
    calc (congruenceRate ((n, p), (n, q)) ^ k *
          ‖primeHodgeHistoryDefectKernel d ((n, p), (n, q))‖) ^ 2
        ≤ (PrimeHodgeHistory.w n * (8 * ‖primeHodgeCubicBirthVector d p‖ *
          ‖primeHodgeCubicBirthVector d q‖)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _)) hbound 2
      _ = historyBirthMass d (n, p) * historyBirthMass d (n, q) := by
          rw [historyBirthMass, historyBirthMass]
          ring
  · rw [primeHodgeHistoryDefectKernel, if_neg hnm, norm_zero, mul_zero, zero_pow two_ne_zero]
    exact mul_nonneg (hnn _) (hnn _)

theorem summable_rate_pow_mul_norm (hd : 0 < d) {k : ℕ} (hk : k ≤ 3) :
    Summable fun ab => (congruenceRate ab ^ k * ‖primeHodgeHistoryDefectKernel d ab‖) ^ 2 := by
  have hB := summable_historyBirthMass hd
  have hnn : ∀ np, 0 ≤ historyBirthMass d np := fun np =>
    mul_nonneg (mul_nonneg (by norm_num) (PrimeHodgeHistory.w_pos _).le) (sq_nonneg _)
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (sq_rate_pow_mul_norm_le hd hk)
    (hB.mul_of_nonneg hB hnn hnn)

/-- The forward prime heat `P_u = e^{-u⁺Λ}`. -/
def historyPrimeHeat (u : ℝ) : ℍ →L[ℂ] ℍ :=
  lpDiagonalCLM (fun a : PrimeHodgeHistoryIndex =>
      ((Real.exp (-(max u 0 * Real.log (a.2 : ℝ))) : ℝ) : ℂ)) zero_le_one fun a => by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (le_max_right u 0) (Real.log_nonneg (by exact_mod_cast a.2.property.one_lt.le))

/-- The forward congruence orbit `u ↦ P_u𝖳_dP_u`, as a heat flow of the defect kernel. -/
def congruenceOrbit (d : ℝ) : ℝ → ℍ →L[ℂ] ℍ :=
  HilbertSchmidt.heatFlowOperator congruenceRate (primeHodgeHistoryDefectKernel d) 0

/-- On `[0, ∞)` the orbit is `P_u𝖳_dP_u`. -/
theorem congruenceOrbit_eq (hd : 0 < d) (u : ℝ) :
    congruenceOrbit d u = historyPrimeHeat u ∘L primeHodgeHistoryDefectOperator hd ∘L historyPrimeHeat u := by
  rw [congruenceOrbit, HilbertSchmidt.heatFlowOperator_eq (HilbertSchmidt.isHS_heatFlowKernel
    congruenceRate_nonneg (summable_rate_pow_mul_norm hd (k := 0) (by norm_num)) u)]
  refine ContinuousLinearMap.ext fun f => lp.ext (funext fun a => ?_)
  rw [HilbertSchmidt.toOperator_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    historyPrimeHeat, lpDiagonalCLM_apply, primeHodgeHistoryDefectOperator,
    HilbertSchmidt.toOperator_apply, ← tsum_mul_left]
  refine tsum_congr fun b => ?_
  rw [lpDiagonalCLM_apply, HilbertSchmidt.heatFlowKernel, congruenceRate]
  have he : Real.exp (-(max u 0 * (Real.log (a.2 : ℝ) + Real.log (b.2 : ℝ)))) =
      Real.exp (-(max u 0 * Real.log (a.2 : ℝ))) * Real.exp (-(max u 0 * Real.log (b.2 : ℝ))) := by
    rw [← Real.exp_add]
    ring_nf
  rw [he]
  push_cast
  ring

/-- **(PLCIE.5) The cubic jet.**  `d³/du³ (P_u𝖳_dP_u)|_{u=0} = -S_Λ³(𝖳_d) = -8 Φ ⊗ |b_d⟩⟨b_d|`,
the third derivative taken in operator norm on `[0, ∞)`. -/
theorem iteratedDerivWithin_three_congruenceOrbit (hd : 0 < d) :
    iteratedDerivWithin 3 (congruenceOrbit d) (Ici 0) 0 =
        -(jointCubicSylvesterTerm hd (m := 3) le_rfl +
          (3 : ℂ) • jointCubicSylvesterTerm hd (m := 2) (by norm_num) +
          (3 : ℂ) • jointCubicSylvesterTerm hd (m := 1) (by norm_num) +
          jointCubicSylvesterTerm hd (m := 0) (by norm_num)) ∧
      iteratedDerivWithin 3 (congruenceOrbit d) (Ici 0) 0 = -(8 : ℂ) • historyCubicBirthOperator hd := by
  have hjet : iteratedDerivWithin 3 (congruenceOrbit d) (Ici 0) 0 =
      -(8 : ℂ) • historyCubicBirthOperator hd := by
    rw [congruenceOrbit, HilbertSchmidt.iteratedDerivWithin_heatFlowOperator congruenceRate_nonneg 3
      (fun j hj => summable_rate_pow_mul_norm hd hj) 0 self_mem_Ici,
      HilbertSchmidt.heatFlowOperator_eq (HilbertSchmidt.isHS_heatFlowKernel congruenceRate_nonneg
        (summable_rate_pow_mul_norm hd (k := 3) le_rfl) 0), historyCubicBirthOperator,
      ← toOperator_smul_kernel]
    refine HilbertSchmidt.toOperator_congr _ _ (funext fun ab => ?_)
    have hb := primeHodgeHistoryCubicClockCore_eq_birth hd ab
    rw [primeHodgeHistoryCubicClockCore, primeHodgeHistoryCubicClock] at hb
    rw [HilbertSchmidt.heatFlowKernel, Pi.smul_apply, smul_eq_mul, max_self, zero_mul, neg_zero,
      Real.exp_zero, mul_one, congruenceRate,
      show (-(Real.log (ab.1.2 : ℝ) + Real.log (ab.2.2 : ℝ))) ^ 3 =
        -((Real.log (ab.1.2 : ℝ) + Real.log (ab.2.2 : ℝ)) ^ 3) by ring,
      Complex.ofReal_neg, Complex.ofReal_pow, neg_mul, hb]
    ring
  refine ⟨?_, hjet⟩
  rw [hjet, jointCubicSylvester_law hd, neg_smul]

end GaloisForLFunctions.HTGeometry

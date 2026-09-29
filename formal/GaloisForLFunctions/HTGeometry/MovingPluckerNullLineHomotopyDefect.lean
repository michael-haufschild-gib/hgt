import GaloisForLFunctions.HTGeometry.PhysicalOverlapSingularGaugeNondescent
import GaloisForLFunctions.HTGeometry.ThetaCompletedPluckerSandwich
import GaloisForLFunctions.HTGeometry.ConstitutiveToeplitzDefectIndex
import GaloisForLFunctions.HTGeometry.CountableSeparableInteractionOperatorLaw

/-!
# The moving Plücker null-line integral–nuclear homotopy defect

Fix primes `p < q`.  With the physical packet mass `P_e` and the theta first-exit law `w_e`, put
`g_e = √(w_e/P_e)`, `a_e = (g_e/g_{e+1})² = w_e P_{e+1}/(w_{e+1} P_e)` and `α_e = √a_e`; since
`π_e = F P_e/Z`, `g_e = √(F/Z) s_e` and `α_e = s_e/s_{e+1}`.

* `a_e = 1 - 2/e + O(e⁻²)`, so `0 < inf α ≤ sup α < ∞`.
* On `K = ℓ²(ℕ)` (basis `ε_e`), the completion-conjugated shift `C ε_e = α_e ε_{e+1}`, which is
  `G⁻¹ V G` coordinatewise, is bounded, bounded below and injective, has closed range `ε_0^⊥`, and
  `ind C = -1`.
* `T = C*C - CC*` is the self-adjoint Schatten-one diagonal `(a_0, a_1 - a_0, a_2 - a_1, …)`;
  `Tr(Q_N T Q_N) = a_N` and `Tr T = 1 = -ind C`, while `C*C` and `CC*` are not trace class.
* Embedding `ε_e ↦ (e, u_e)` with `u_e` the unit Stokes-gap null vector of the physical Plücker
  block, `T` has depth blocks `(a_e - a_{e-1}) u_e u_eᵀ`; the zeroth block has all entries nonzero
  (prime mixing) and `T` is not a history diagonal tensored with a fixed packet matrix.
* `a_e - a_{e-1} > 0` for all large `e`, so negative directions of `T` lie in a finite history
  head; `g_{N+1}/g_0 = ∏_{e≤N} a_e^{-1/2}`.
-/

open Filter Topology Set Asymptotics
open scoped ENNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower _root_.RHTower.HedenmalmThetaSource

/-! ## The completion transport -/

section Transport

variable (p q : Nat.Primes)

/-- The completion gauge `g_e = √(w_e/P_e)`. -/
def completionGauge (e : ℕ) : ℝ :=
  Real.sqrt (thetaCuspMellinSixFlux e / gammaSewnCriticalPrimeDepthPacket_Partition e p q)

/-- **(MPNLIH.1).**  The transport square `a_e = w_e P_{e+1}/(w_{e+1} P_e)`. -/
def completionTransport (e : ℕ) : ℝ :=
  thetaCuspMellinSixFlux e * gammaSewnCriticalPrimeDepthPacket_Partition (e + 1) p q /
    (thetaCuspMellinSixFlux (e + 1) * gammaSewnCriticalPrimeDepthPacket_Partition e p q)

/-- The shift weight `α_e = √a_e`. -/
def completionShiftWeight (e : ℕ) : ℝ := Real.sqrt (completionTransport p q e)

variable {p q} (hpq : (p : ℕ) < (q : ℕ))
include hpq

theorem completionGauge_pos (e : ℕ) : 0 < completionGauge p q e :=
  Real.sqrt_pos.2 (div_pos (thetaCuspMellinSixFlux_pos e)
    (gammaSewnCriticalPrimeDepthPacket_Partition_pos hpq))

theorem completionTransport_pos (e : ℕ) : 0 < completionTransport p q e := by
  have h1 := gammaSewnCriticalPrimeDepthPacket_Partition_pos (e := e) hpq
  have h2 := gammaSewnCriticalPrimeDepthPacket_Partition_pos (e := e + 1) hpq
  have h3 := thetaCuspMellinSixFlux_pos e
  have h4 := thetaCuspMellinSixFlux_pos (e + 1)
  unfold completionTransport
  positivity

theorem completionShiftWeight_pos (e : ℕ) : 0 < completionShiftWeight p q e :=
  Real.sqrt_pos.2 (completionTransport_pos hpq e)

theorem completionShiftWeight_sq (e : ℕ) :
    completionShiftWeight p q e * completionShiftWeight p q e = completionTransport p q e :=
  Real.mul_self_sqrt (completionTransport_pos hpq e).le

/-- `a_e = (g_e/g_{e+1})²`. -/
theorem completionTransport_eq_sq (e : ℕ) :
    completionTransport p q e = (completionGauge p q e / completionGauge p q (e + 1)) ^ 2 := by
  have h1 := gammaSewnCriticalPrimeDepthPacket_Partition_pos (e := e) hpq
  have h2 := gammaSewnCriticalPrimeDepthPacket_Partition_pos (e := e + 1) hpq
  have h3 := thetaCuspMellinSixFlux_pos e
  have h4 := thetaCuspMellinSixFlux_pos (e + 1)
  rw [div_pow, completionGauge, completionGauge, Real.sq_sqrt (div_pos h3 h1).le,
    Real.sq_sqrt (div_pos h4 h2).le, completionTransport]
  field_simp

/-- `α_e = g_e/g_{e+1}`. -/
theorem completionShiftWeight_eq (e : ℕ) :
    completionShiftWeight p q e = completionGauge p q e / completionGauge p q (e + 1) := by
  rw [completionShiftWeight, completionTransport_eq_sq hpq,
    Real.sqrt_sq (div_pos (completionGauge_pos hpq e) (completionGauge_pos hpq (e + 1))).le]

/-- The global normalizer cancels: `g_e = √(F/Z) s_e`. -/
theorem completionGauge_eq (e : ℕ) :
    completionGauge p q e =
      Real.sqrt (pluckerFisherClock p q / pluckerDepthTotal p q) * formationHalfDensity p q e := by
  have hF := pluckerFisherClock_pos p q
  have hZ := pluckerDepthTotal_pos hpq
  have hP := (gammaSewnCriticalPrimeDepthPacket_Partition_pos (e := e) hpq).ne'
  rw [completionGauge, formationHalfDensity, ← Real.sqrt_mul (div_pos hF hZ).le]
  congr 1
  simp only [pluckerDepthLaw, pluckerDepthWeight_eq]
  field_simp

/-- `α_e = s_e/s_{e+1}`: the shift is the inverse formation connection. -/
theorem completionShiftWeight_eq_formation (e : ℕ) :
    completionShiftWeight p q e =
      formationHalfDensity p q e / formationHalfDensity p q (e + 1) := by
  rw [completionShiftWeight_eq hpq, completionGauge_eq hpq, completionGauge_eq hpq,
    mul_div_mul_left _ _ (Real.sqrt_pos.2 (div_pos (pluckerFisherClock_pos p q)
      (pluckerDepthTotal_pos hpq))).ne']

/-- **(MPNLIH, (3)).**  `a_e = 1 - 2/e + O(e⁻²)`. -/
theorem isBigO_completionTransport_sub :
    (fun e : ℕ => completionTransport p q e - (1 - 2 / (e : ℝ))) =O[atTop]
      (fun e : ℕ => ((e : ℝ) ^ 2)⁻¹) := by
  have hP := isBigO_partition_ratio hpq
  have hfac : (fun e : ℕ => (2 * (e : ℝ) + 11) / (2 * e + 3)) =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    IsBigO.of_bound 4 (Eventually.of_forall fun e => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, mul_one, abs_of_pos (by positivity),
        div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg e : (0 : ℝ) ≤ e)])
  have hmain : (fun e : ℕ => -60 / ((e : ℝ) * (2 * e + 3))) =O[atTop]
      (fun e : ℕ => ((e : ℝ) ^ 2)⁻¹) := by
    refine IsBigO.of_bound 30 ?_
    filter_upwards [eventually_ne_atTop 0] with e he
    have hepos : (0 : ℝ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos (by positivity : (0 : ℝ) < (e : ℝ) * (2 * e + 3)),
      abs_of_pos (by positivity : (0 : ℝ) < ((e : ℝ) ^ 2)⁻¹)]
    calc |(60 : ℝ)| / ((e : ℝ) * (2 * e + 3)) ≤ 60 / ((e : ℝ) * (2 * e)) := by
          rw [abs_of_pos (by norm_num : (0 : ℝ) < 60)]
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
      _ = 30 * ((e : ℝ) ^ 2)⁻¹ := by field_simp; ring
  have hsum := hmain.add ((hP.mul hfac).trans (by simp only [mul_one]; exact isBigO_refl _ _))
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_atTop 0] with e he
  have hepos : (0 : ℝ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)
  have hP0 := (gammaSewnCriticalPrimeDepthPacket_Partition_pos (e := e) hpq).ne'
  have hw0 := (thetaCuspMellinSixFlux_pos e).ne'
  have hw1 := (thetaCuspMellinSixFlux_pos (e + 1)).ne'
  have hw : thetaCuspMellinSixFlux e / thetaCuspMellinSixFlux (e + 1) =
      (2 * (e : ℝ) + 11) / (2 * e + 3) := by
    rw [← inv_div, thetaCuspMellinSixFlux_succ_div, inv_div]
  have ha : completionTransport p q e =
      gammaSewnCriticalPrimeDepthPacket_Partition (e + 1) p q /
        gammaSewnCriticalPrimeDepthPacket_Partition e p q * ((2 * (e : ℝ) + 11) / (2 * e + 3)) := by
    rw [← hw, completionTransport]
    field_simp
  rw [ha]
  field_simp
  ring

/-- `a_e → 1`. -/
theorem tendsto_completionTransport :
    Tendsto (completionTransport p q) atTop (𝓝 1) := by
  have hinv2 : Tendsto (fun e : ℕ => ((e : ℝ) ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
  have h0 := (isBigO_completionTransport_sub hpq).trans_tendsto hinv2
  have h1 : Tendsto (fun e : ℕ => 1 - 2 / (e : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_const_div_atTop_nhds_zero_nat 2)
  simpa using h0.add h1

theorem tendsto_completionShiftWeight :
    Tendsto (completionShiftWeight p q) atTop (𝓝 1) := by
  have h := (tendsto_completionTransport hpq).sqrt
  rw [Real.sqrt_one] at h
  exact h

theorem bddAbove_completionShiftWeight : BddAbove (range (completionShiftWeight p q)) :=
  (tendsto_completionShiftWeight hpq).bddAbove_range

theorem bddAbove_inv_completionShiftWeight :
    BddAbove (range fun e => (completionShiftWeight p q e)⁻¹) :=
  ((tendsto_completionShiftWeight hpq).inv₀ one_ne_zero).bddAbove_range

end Transport

/-! ## The completion-conjugated shift -/

section Shift

variable {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ))

/-- An upper bound for `α`. -/
def completionShiftUpper : ℝ := (bddAbove_completionShiftWeight hpq).choose

/-- An upper bound for `α⁻¹`. -/
def completionShiftInverseUpper : ℝ := (bddAbove_inv_completionShiftWeight hpq).choose

theorem norm_completionShiftWeight_le (e : ℕ) :
    ‖((completionShiftWeight p q e : ℝ) : ℂ)‖ ≤ completionShiftUpper hpq := by
  rw [Complex.norm_real, Real.norm_of_nonneg (completionShiftWeight_pos hpq e).le]
  exact (bddAbove_completionShiftWeight hpq).choose_spec ⟨e, rfl⟩

theorem norm_inv_completionShiftWeight_le (e : ℕ) :
    ‖(((completionShiftWeight p q e)⁻¹ : ℝ) : ℂ)‖ ≤ completionShiftInverseUpper hpq := by
  rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (completionShiftWeight_pos hpq e).le)]
  exact (bddAbove_inv_completionShiftWeight hpq).choose_spec ⟨e, rfl⟩

/-- The diagonal `diag(α_e)`. -/
def completionShiftDiagonal : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  _root_.HTGeometry.ellTwoDiagonal (fun e => ((completionShiftWeight p q e : ℝ) : ℂ))
    (norm_completionShiftWeight_le hpq)

/-- The diagonal `diag(α_e⁻¹)`. -/
def completionShiftInverseDiagonal : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  _root_.HTGeometry.ellTwoDiagonal (fun e => (((completionShiftWeight p q e)⁻¹ : ℝ) : ℂ))
    (norm_inv_completionShiftWeight_le hpq)

/-- **(MPNLIH.3).**  The completion-conjugated formation shift `C ε_e = α_e ε_{e+1}`. -/
def completionShift : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  shiftOp 1 ∘L completionShiftDiagonal hpq

/-- The bounded backward transport `L = diag(α⁻¹) V*`. -/
def completionShiftLeftInverse : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  completionShiftInverseDiagonal hpq ∘L backOp 1

theorem completionShift_apply_succ (x : ToeplitzSpace) (e : ℕ) :
    (completionShift hpq x : ℕ → ℂ) (e + 1) =
      ((completionShiftWeight p q e : ℝ) : ℂ) * (x : ℕ → ℂ) e := by
  rw [completionShift, ContinuousLinearMap.comp_apply, shiftOp_apply, shiftFun_add,
    completionShiftDiagonal, _root_.HTGeometry.ellTwoDiagonal_apply]

theorem completionShift_apply_zero (x : ToeplitzSpace) :
    (completionShift hpq x : ℕ → ℂ) 0 = 0 := by
  rw [completionShift, ContinuousLinearMap.comp_apply, shiftOp_apply, shiftFun_of_lt (by omega)]

theorem completionShift_single (e : ℕ) :
    completionShift hpq (lp.single 2 e 1) =
      ((completionShiftWeight p q e : ℝ) : ℂ) • (lp.single 2 (e + 1) 1 : ToeplitzSpace) := by
  ext k
  rcases k with _ | k
  · rw [completionShift_apply_zero, lp.coeFn_smul, Pi.smul_apply,
      lp.single_apply_ne _ _ _ (by omega : (0 : ℕ) ≠ e + 1), smul_zero]
  · rw [completionShift_apply_succ]
    simp only [lp.single_apply, Pi.single_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases h : k = e
    · subst k
      simp
    · have hs : k + 1 ≠ e + 1 := by omega
      simp [h]

/-- **(MPNLIH.4).**  Coordinatewise `C = G⁻¹ V G`: `(Cx)_{e+1} = g_{e+1}⁻¹ g_e x_e`. -/
theorem completionShift_apply_succ_gauge (x : ToeplitzSpace) (e : ℕ) :
    (completionShift hpq x : ℕ → ℂ) (e + 1) =
      ((completionGauge p q (e + 1))⁻¹ : ℂ) * ((completionGauge p q e : ℂ) * (x : ℕ → ℂ) e) := by
  have hg := (completionGauge_pos hpq (e + 1)).ne'
  rw [completionShift_apply_succ, completionShiftWeight_eq hpq, Complex.ofReal_div]
  field_simp

theorem completionShiftLeftInverse_comp :
    completionShiftLeftInverse hpq ∘L completionShift hpq =
      ContinuousLinearMap.id ℂ ToeplitzSpace := by
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun k => ?_)
  have hα := (completionShiftWeight_pos hpq k).ne'
  change (((completionShiftWeight p q k)⁻¹ : ℝ) : ℂ) * (completionShift hpq x : ℕ → ℂ) (k + 1) =
    (x : ℕ → ℂ) k
  rw [completionShift_apply_succ, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hα,
    Complex.ofReal_one, one_mul]

theorem completionShiftDiagonal_comp_inverse :
    completionShiftDiagonal hpq ∘L completionShiftInverseDiagonal hpq =
      ContinuousLinearMap.id ℂ ToeplitzSpace := by
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun k => ?_)
  have hα := (completionShiftWeight_pos hpq k).ne'
  change ((completionShiftWeight p q k : ℝ) : ℂ) *
      ((((completionShiftWeight p q k)⁻¹ : ℝ) : ℂ) * (x : ℕ → ℂ) k) = (x : ℕ → ℂ) k
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hα, Complex.ofReal_one, one_mul]

/-- `C` is injective. -/
theorem ker_completionShift : LinearMap.ker (completionShift hpq).toLinearMap = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have h := congrArg (fun A : ToeplitzSpace →L[ℂ] ToeplitzSpace => A x)
    (completionShiftLeftInverse_comp hpq)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
  have hx' : completionShift hpq x = 0 := hx
  rw [hx', map_zero] at h
  exact h.symm

/-- The range of `C` is `ε_0^⊥ = {y : y_0 = 0}`. -/
theorem mem_range_completionShift_iff (y : ToeplitzSpace) :
    y ∈ LinearMap.range (completionShift hpq).toLinearMap ↔ (y : ℕ → ℂ) 0 = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact completionShift_apply_zero hpq x
  · intro hy
    refine ⟨completionShiftLeftInverse hpq y, lp.ext (funext fun k => ?_)⟩
    rcases k with _ | k
    · change (completionShift hpq _ : ℕ → ℂ) 0 = _
      rw [completionShift_apply_zero, hy]
    · change (completionShift hpq _ : ℕ → ℂ) (k + 1) = _
      have hα := (completionShiftWeight_pos hpq k).ne'
      rw [completionShift_apply_succ]
      change ((completionShiftWeight p q k : ℝ) : ℂ) *
          ((((completionShiftWeight p q k)⁻¹ : ℝ) : ℂ) * (y : ℕ → ℂ) (k + 1)) = _
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hα, Complex.ofReal_one, one_mul]

/-- `C` has closed range. -/
theorem isClosed_range_completionShift :
    IsClosed (LinearMap.range (completionShift hpq).toLinearMap : Set ToeplitzSpace) := by
  have hset : (LinearMap.range (completionShift hpq).toLinearMap : Set ToeplitzSpace) =
      {y | ⟪(lp.single 2 0 (1 : ℂ) : ToeplitzSpace), y⟫_ℂ = 0} := by
    ext y
    rw [SetLike.mem_coe, mem_range_completionShift_iff, Set.mem_setOf_eq, lp.inner_single_left]
    simp
  rw [hset]
  exact isClosed_eq (continuous_const.inner continuous_id) continuous_const

theorem range_completionShift_eq_shift :
    LinearMap.range (completionShift hpq).toLinearMap =
      LinearMap.range (shiftOp 1).toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨completionShiftDiagonal hpq x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨completionShiftInverseDiagonal hpq x, ?_⟩
    change shiftOp 1 (completionShiftDiagonal hpq (completionShiftInverseDiagonal hpq x)) =
      shiftOp 1 x
    have h := congrArg (fun A : ToeplitzSpace →L[ℂ] ToeplitzSpace => A x)
      (completionShiftDiagonal_comp_inverse hpq)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    rw [h]

/-- The Fredholm index of `C`, through algebraic kernel and cokernel. -/
def completionShiftIndex : ℤ :=
  (Module.finrank ℂ (LinearMap.ker (completionShift hpq).toLinearMap) : ℤ) -
    (Module.finrank ℂ (ToeplitzSpace ⧸ LinearMap.range (completionShift hpq).toLinearMap) : ℤ)

/-- **(MPNLIH.5).**  `ind C = -1`: the kernel is trivial and the cokernel is a line. -/
theorem completionShiftIndex_eq : completionShiftIndex hpq = -1 := by
  rw [completionShiftIndex, ker_completionShift, range_completionShift_eq_shift,
    finrank_coker_shiftOp, finrank_bot]
  norm_num

theorem finrank_coker_completionShift :
    Module.finrank ℂ (ToeplitzSpace ⧸ LinearMap.range (completionShift hpq).toLinearMap) = 1 := by
  rw [range_completionShift_eq_shift, finrank_coker_shiftOp]

/-- `C` is bounded below. -/
theorem exists_completionShift_bounded_below :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖completionShift hpq x‖ := by
  set L := completionShiftLeftInverse hpq
  refine ⟨(‖L‖ + 1)⁻¹, by positivity, fun x => ?_⟩
  have h := congrArg (fun A : ToeplitzSpace →L[ℂ] ToeplitzSpace => A x)
    (completionShiftLeftInverse_comp hpq)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
  have hle : ‖x‖ ≤ ‖L‖ * ‖completionShift hpq x‖ := by
    calc ‖x‖ = ‖L (completionShift hpq x)‖ := by rw [h]
      _ ≤ ‖L‖ * ‖completionShift hpq x‖ := L.le_opNorm _
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (completionShift hpq x)]

theorem adjoint_completionShift :
    ContinuousLinearMap.adjoint (completionShift hpq) =
      completionShiftDiagonal hpq ∘L backOp 1 := by
  rw [completionShift, ContinuousLinearMap.adjoint_comp, adjoint_shiftOp, completionShiftDiagonal,
    _root_.HTGeometry.adjoint_ellTwoDiagonal]
  congr 1
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun k => ?_)
  rw [_root_.HTGeometry.ellTwoDiagonal_apply, _root_.HTGeometry.ellTwoDiagonal_apply,
    Complex.conj_ofReal]

theorem adjoint_completionShift_apply (x : ToeplitzSpace) (k : ℕ) :
    (ContinuousLinearMap.adjoint (completionShift hpq) x : ℕ → ℂ) k =
      ((completionShiftWeight p q k : ℝ) : ℂ) * (x : ℕ → ℂ) (k + 1) := by
  rw [adjoint_completionShift]
  rfl

/-- `C*C = diag(a_e)`. -/
theorem adjoint_comp_completionShift_apply (x : ToeplitzSpace) (k : ℕ) :
    ((ContinuousLinearMap.adjoint (completionShift hpq) ∘L completionShift hpq) x : ℕ → ℂ) k =
      ((completionTransport p q k : ℝ) : ℂ) * (x : ℕ → ℂ) k := by
  rw [ContinuousLinearMap.comp_apply, adjoint_completionShift_apply, completionShift_apply_succ,
    ← mul_assoc, ← Complex.ofReal_mul, completionShiftWeight_sq hpq]

/-- `CC* = diag(0, a_0, a_1, …)`. -/
theorem completionShift_comp_adjoint_apply_zero (x : ToeplitzSpace) :
    ((completionShift hpq ∘L ContinuousLinearMap.adjoint (completionShift hpq)) x : ℕ → ℂ) 0 =
      0 := by
  rw [ContinuousLinearMap.comp_apply, completionShift_apply_zero]

theorem completionShift_comp_adjoint_apply_succ (x : ToeplitzSpace) (k : ℕ) :
    ((completionShift hpq ∘L ContinuousLinearMap.adjoint (completionShift hpq)) x : ℕ → ℂ)
        (k + 1) = ((completionTransport p q k : ℝ) : ℂ) * (x : ℕ → ℂ) (k + 1) := by
  rw [ContinuousLinearMap.comp_apply, completionShift_apply_succ, adjoint_completionShift_apply,
    ← mul_assoc, ← Complex.ofReal_mul, completionShiftWeight_sq hpq]

end Shift

/-! ## The self-commutator -/

section Commutator

variable {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ))

/-- **(MPNLIH.6).**  The homotopy defect `T = C*C - CC*`. -/
def completionSelfCommutator : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  ContinuousLinearMap.adjoint (completionShift hpq) ∘L completionShift hpq -
    completionShift hpq ∘L ContinuousLinearMap.adjoint (completionShift hpq)

/-- The boundary curvature `(a_0, a_1 - a_0, a_2 - a_1, …)`. -/
def completionBoundaryCurvature (p q : Nat.Primes) : ℕ → ℝ
  | 0 => completionTransport p q 0
  | e + 1 => completionTransport p q (e + 1) - completionTransport p q e

theorem completionBoundaryCurvature_succ (e : ℕ) :
    completionBoundaryCurvature p q (e + 1) =
      completionTransport p q (e + 1) - completionTransport p q e := rfl

include hpq

/-- The boundary curvature satisfies `a_e - a_{e-1} = O(e⁻²)`. -/
theorem isBigO_completionBoundaryCurvature_succ :
    (fun e : ℕ => completionBoundaryCurvature p q (e + 1)) =O[atTop]
      (fun e : ℕ => ((e : ℝ) ^ 2)⁻¹) := by
  have hA := isBigO_completionTransport_sub hpq
  have hA1 : (fun e : ℕ => completionTransport p q (e + 1) - (1 - 2 / ((e : ℝ) + 1))) =O[atTop]
      (fun e : ℕ => ((e : ℝ) ^ 2)⁻¹) := by
    have h := hA.comp_tendsto (tendsto_add_atTop_nat 1)
    refine (h.congr_left fun e => by simp [Function.comp]).trans ?_
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ne_atTop 0] with e he
    have hepos : (0 : ℝ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)
    simp only [Function.comp, Nat.cast_add, Nat.cast_one, Real.norm_eq_abs, one_mul]
    rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hepos.le (by linarith) 2)
  have h3 : (fun e : ℕ => 2 / (e : ℝ) - 2 / ((e : ℝ) + 1)) =O[atTop]
      (fun e : ℕ => ((e : ℝ) ^ 2)⁻¹) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ne_atTop 0] with e he
    have hepos : (0 : ℝ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)
    have hid : 2 / (e : ℝ) - 2 / ((e : ℝ) + 1) = 2 / ((e : ℝ) * (e + 1)) := by
      field_simp
      ring
    rw [hid, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity),
      abs_of_pos (by positivity)]
    calc 2 / ((e : ℝ) * (e + 1)) ≤ 2 / ((e : ℝ) * e) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
      _ = 2 * ((e : ℝ) ^ 2)⁻¹ := by field_simp
  refine ((hA1.sub hA).add h3).congr (fun e => ?_) (fun _ => rfl)
  rw [completionBoundaryCurvature_succ]
  ring

theorem summable_abs_completionBoundaryCurvature :
    Summable fun e => |completionBoundaryCurvature p q e| := by
  refine (summable_nat_add_iff 1).1 ?_
  have h := summable_of_isBigO_nat (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
    (isBigO_completionBoundaryCurvature_succ hpq).norm_left
  simpa [Real.norm_eq_abs] using h

theorem summable_completionBoundaryCurvature : Summable (completionBoundaryCurvature p q) :=
  (summable_abs_completionBoundaryCurvature hpq).of_abs

/-- **(MPNLIH.7).**  `T` is the diagonal `(a_0, a_1 - a_0, …)`. -/
theorem completionSelfCommutator_eq :
    completionSelfCommutator hpq =
      realSummableDiagonalOperator (completionBoundaryCurvature p q)
        (summable_abs_completionBoundaryCurvature hpq) := by
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun k => ?_)
  rw [realSummableDiagonalOperator_apply]
  change ((ContinuousLinearMap.adjoint (completionShift hpq) ∘L completionShift hpq) x :
      ℕ → ℂ) k - ((completionShift hpq ∘L ContinuousLinearMap.adjoint (completionShift hpq)) x :
      ℕ → ℂ) k = _
  rcases k with _ | k
  · rw [adjoint_comp_completionShift_apply, completionShift_comp_adjoint_apply_zero, sub_zero]
    rfl
  · rw [adjoint_comp_completionShift_apply, completionShift_comp_adjoint_apply_succ,
      completionBoundaryCurvature_succ, Complex.ofReal_sub]
    ring

/-- `T` is nuclear. -/
theorem completionSelfCommutator_memSchattenClass_one :
    MemSchattenClass 1 (completionSelfCommutator hpq) := by
  rw [completionSelfCommutator_eq]
  exact realSummableDiagonalOperator_memSchattenClass_one _ _

/-- `T` is self-adjoint. -/
theorem completionSelfCommutator_isSelfAdjoint : IsSelfAdjoint (completionSelfCommutator hpq) := by
  rw [completionSelfCommutator_eq]
  exact realSummableDiagonalOperator_isSelfAdjoint _ _

theorem completionSelfCommutator_single (e : ℕ) :
    completionSelfCommutator hpq (lp.single 2 e 1) =
      ((completionBoundaryCurvature p q e : ℝ) : ℂ) • (lp.single 2 e 1 : ToeplitzSpace) := by
  rw [completionSelfCommutator_eq]
  refine lp.ext (funext fun k => ?_)
  rw [realSummableDiagonalOperator_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases h : k = e
  · subst h
    rfl
  · rw [lp.single_apply_ne _ _ _ h, mul_zero, mul_zero]

omit hpq in
/-- The trace of an absolutely summable real diagonal on `ℓ²(ℕ)` is the sum of its entries. -/
theorem opTrace_realSummableDiagonalOperator_nat (w : ℕ → ℝ) (hw : Summable fun e => |w e|) :
    (realSummableDiagonalOperator w hw).opTrace = ((∑' e, w e : ℝ) : ℂ) := by
  have hS := realSummableDiagonalOperator_memSchattenClass_one w hw
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one hS (HilbertSchmidt.lpBasis ℕ),
    Complex.ofReal_tsum]
  refine tsum_congr fun e => ?_
  rw [HilbertSchmidt.lpBasis_apply, lp.inner_single_left, realSummableDiagonalOperator_apply,
    lp.single_apply_self]
  simp

omit hpq in
theorem sum_range_completionBoundaryCurvature (N : ℕ) :
    ∑ e ∈ Finset.range (N + 1), completionBoundaryCurvature p q e = completionTransport p q N := by
  induction N with
  | zero => rw [Finset.sum_range_one]; rfl
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, completionBoundaryCurvature_succ]
    ring

theorem hasSum_completionBoundaryCurvature : HasSum (completionBoundaryCurvature p q) 1 := by
  refine ((summable_completionBoundaryCurvature hpq).hasSum_iff_tendsto_nat).2 ?_
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  simpa only [sum_range_completionBoundaryCurvature] using tendsto_completionTransport hpq

/-- **(MPNLIH.9).**  `Tr T = 1 = -ind C`. -/
theorem opTrace_completionSelfCommutator :
    (completionSelfCommutator hpq).opTrace = 1 ∧
      ((-completionShiftIndex hpq : ℤ) : ℂ) = (completionSelfCommutator hpq).opTrace := by
  have h1 : (completionSelfCommutator hpq).opTrace = 1 := by
    rw [completionSelfCommutator_eq, opTrace_realSummableDiagonalOperator_nat,
      (hasSum_completionBoundaryCurvature hpq).tsum_eq, Complex.ofReal_one]
  refine ⟨h1, ?_⟩
  rw [h1, completionShiftIndex_eq]
  norm_num

omit hpq in
/-- The projection `Q_N` onto the histories `0, …, N`. -/
def historyHeadProjection (N : ℕ) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  _root_.HTGeometry.ellTwoDiagonal (fun e => if e ≤ N then (1 : ℂ) else 0) (C := 1)
    (fun e => by split_ifs <;> simp)

omit hpq in
theorem summable_abs_head (b : ℕ → ℝ) (N : ℕ) :
    Summable fun e => |if e ≤ N then b e else 0| :=
  summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun e he => by
    rw [Finset.mem_range, not_lt] at he
    rw [if_neg (by omega), abs_zero]

theorem historyHeadProjection_sandwich (N : ℕ) :
    historyHeadProjection N ∘L completionSelfCommutator hpq ∘L historyHeadProjection N =
      realSummableDiagonalOperator (fun e => if e ≤ N then completionBoundaryCurvature p q e else 0)
        (summable_abs_head _ N) := by
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun k => ?_)
  rw [realSummableDiagonalOperator_apply]
  change (if k ≤ N then (1 : ℂ) else 0) * (completionSelfCommutator hpq
    (historyHeadProjection N x) : ℕ → ℂ) k = _
  rw [completionSelfCommutator_eq, realSummableDiagonalOperator_apply]
  change (if k ≤ N then (1 : ℂ) else 0) * (((completionBoundaryCurvature p q k : ℝ) : ℂ) *
    ((if k ≤ N then (1 : ℂ) else 0) * (x : ℕ → ℂ) k)) = _
  split_ifs <;> simp

/-- **(MPNLIH.8).**  `Tr(Q_N T Q_N) = a_N`. -/
theorem opTrace_historyHeadProjection_sandwich (N : ℕ) :
    (historyHeadProjection N ∘L completionSelfCommutator hpq ∘L historyHeadProjection N).opTrace =
      ((completionTransport p q N : ℝ) : ℂ) := by
  rw [historyHeadProjection_sandwich, opTrace_realSummableDiagonalOperator_nat,
    tsum_eq_sum (s := Finset.range (N + 1)) (fun e he => by
      rw [Finset.mem_range, not_lt] at he
      rw [if_neg (by omega)]), ← sum_range_completionBoundaryCurvature]
  congr 1
  refine Finset.sum_congr rfl fun e he => ?_
  rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp he))]

/-- The chiral Laplacians `C*C` and `CC*` are not trace class; only their difference is. -/
theorem chiralLaplacians_not_memSchattenClass_one :
    ¬ MemSchattenClass 1 (ContinuousLinearMap.adjoint (completionShift hpq) ∘L
        completionShift hpq) ∧
      ¬ MemSchattenClass 1 (completionShift hpq ∘L
        ContinuousLinearMap.adjoint (completionShift hpq)) := by
  have hlim := tendsto_completionTransport hpq
  have hdiag : ∀ (A : ToeplitzSpace →L[ℂ] ToeplitzSpace) (e : ℕ),
      ⟪HilbertSchmidt.lpBasis ℕ e, A (HilbertSchmidt.lpBasis ℕ e)⟫_ℂ =
        (A (lp.single 2 e 1) : ℕ → ℂ) e := fun A e => by
    rw [HilbertSchmidt.lpBasis_apply, lp.inner_single_left]
    simp
  constructor
  · intro h
    have hs := h.one_summable_inner_diag_basis (HilbertSchmidt.lpBasis ℕ)
    simp_rw [hdiag, adjoint_comp_completionShift_apply, lp.single_apply_self, mul_one] at hs
    have h0 := (Complex.summable_ofReal.1 hs).tendsto_atTop_zero
    exact one_ne_zero (tendsto_nhds_unique hlim h0)
  · intro h
    have hs := h.one_summable_inner_diag_basis (HilbertSchmidt.lpBasis ℕ)
    simp_rw [hdiag] at hs
    have hs1 := (summable_nat_add_iff 1).2 hs
    simp_rw [completionShift_comp_adjoint_apply_succ, lp.single_apply_self, mul_one] at hs1
    have h0 := (Complex.summable_ofReal.1 hs1).tendsto_atTop_zero
    exact one_ne_zero (tendsto_nhds_unique hlim h0)

/-- **(MPNLIH.13).**  `g_{N+1}/g_0 = ∏_{e≤N} a_e^{-1/2}`. -/
theorem completionGauge_succ_div_zero (N : ℕ) :
    completionGauge p q (N + 1) / completionGauge p q 0 =
      ∏ e ∈ Finset.range (N + 1), (Real.sqrt (completionTransport p q e))⁻¹ := by
  have hstep : ∀ e, (Real.sqrt (completionTransport p q e))⁻¹ =
      completionGauge p q (e + 1) / completionGauge p q e := fun e => by
    rw [← completionShiftWeight, completionShiftWeight_eq hpq, inv_div]
  induction N with
  | zero => simp [hstep]
  | succ N ih =>
    rw [Finset.prod_range_succ, ← ih, hstep]
    field_simp [(completionGauge_pos hpq 0).ne', (completionGauge_pos hpq (N + 1)).ne']

end Commutator

/-! ## Eventual positivity of the boundary curvature -/

section Positivity

variable (p q : Nat.Primes)

/-- The transport profile `Φ` with `a_e = Φ(1/e)`. -/
def completionTransportProfile (t : ℝ) : ℝ :=
  pluckerPartitionProfile p q (t / (1 + t)) * thetaExitProfile t /
    ((1 + t) ^ 2 * pluckerPartitionProfile p q t * thetaExitProfile (t / (1 + t)))

variable {p q} (hpq : (p : ℕ) < (q : ℕ))
include hpq

theorem pluckerPartitionProfile_zero_pos : 0 < pluckerPartitionProfile p q 0 := by
  rw [pluckerPartitionProfile_zero]
  exact pluckerOrderConstant_pos hpq

theorem completionTransport_eq_profile {e : ℕ} (he : e ≠ 0) :
    completionTransport p q e = completionTransportProfile p q (e : ℝ)⁻¹ := by
  have hepos : (0 : ℝ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)
  have hP : ∀ k : ℕ, k ≠ 0 → gammaSewnCriticalPrimeDepthPacket_Partition k p q =
      pluckerPartitionProfile p q (k : ℝ)⁻¹ / (k : ℝ) ^ 6 := fun k hk => by
    rw [← pow_six_mul_partition_eq_profile p q hk]
    field_simp
  have hW : ∀ k : ℕ, k ≠ 0 → thetaCuspMellinSixFlux k = thetaExitProfile (k : ℝ)⁻¹ / (k : ℝ) ^ 4 :=
    fun k hk => by
      rw [← pow_four_mul_thetaFlux_eq_profile hk]
      field_simp
  have hPr : ∀ k : ℕ, k ≠ 0 → pluckerPartitionProfile p q (k : ℝ)⁻¹ ≠ 0 := fun k hk => by
    rw [← pow_six_mul_partition_eq_profile p q hk]
    exact mul_ne_zero (pow_ne_zero 6 (Nat.cast_ne_zero.mpr hk))
      (gammaSewnCriticalPrimeDepthPacket_Partition_pos hpq).ne'
  have hWr : ∀ k : ℕ, k ≠ 0 → thetaExitProfile (k : ℝ)⁻¹ ≠ 0 := fun k hk => by
    rw [← pow_four_mul_thetaFlux_eq_profile hk]
    exact mul_ne_zero (pow_ne_zero 4 (Nat.cast_ne_zero.mpr hk)) (thetaCuspMellinSixFlux_pos k).ne'
  have hs : (e : ℝ)⁻¹ / (1 + (e : ℝ)⁻¹) = (((e + 1 : ℕ) : ℝ))⁻¹ := by
    push_cast
    field_simp
  have h1 := hPr e he
  have h2 := hPr (e + 1) (Nat.succ_ne_zero e)
  have h3 := hWr e he
  have h4 := hWr (e + 1) (Nat.succ_ne_zero e)
  rw [completionTransport, completionTransportProfile, hs, hP e he, hP (e + 1) (Nat.succ_ne_zero e),
    hW e he, hW (e + 1) (Nat.succ_ne_zero e)]
  push_cast at h2 h4 ⊢
  field_simp

omit hpq in
theorem contDiffAt_completionTransportProfile_of (hP0 : pluckerPartitionProfile p q 0 ≠ 0) :
    ContDiffAt ℝ 1 (completionTransportProfile p q) 0 := by
  have hg : ContDiffAt ℝ 1 (fun t : ℝ => t / (1 + t)) 0 :=
    contDiffAt_id.div (contDiffAt_const.add contDiffAt_id) (by norm_num)
  have hPg : ContDiffAt ℝ 1 (fun t : ℝ => pluckerPartitionProfile p q (t / (1 + t))) 0 :=
    ContDiffAt.comp (g := pluckerPartitionProfile p q) (f := fun t : ℝ => t / (1 + t)) 0
      (by simpa using contDiffAt_pluckerPartitionProfile p q) hg
  have hWg : ContDiffAt ℝ 1 (fun t : ℝ => thetaExitProfile (t / (1 + t))) 0 :=
    ContDiffAt.comp (g := thetaExitProfile) (f := fun t : ℝ => t / (1 + t)) 0
      (by simpa using contDiffAt_thetaExitProfile) hg
  have hden : (1 + (0 : ℝ)) ^ 2 * pluckerPartitionProfile p q 0 *
      thetaExitProfile (0 / (1 + 0)) ≠ 0 := by
    rw [zero_div, thetaExitProfile_zero]
    norm_num
    exact hP0
  unfold completionTransportProfile
  exact ContDiffAt.div
    (f := fun t => pluckerPartitionProfile p q (t / (1 + t)) * thetaExitProfile t)
    (g := fun t => (1 + t) ^ 2 * pluckerPartitionProfile p q t * thetaExitProfile (t / (1 + t)))
    (hPg.mul contDiffAt_thetaExitProfile)
    ((((contDiffAt_const.add contDiffAt_id).pow 2).mul
      (contDiffAt_pluckerPartitionProfile p q)).mul hWg) hden

theorem completionTransportProfile_zero : completionTransportProfile p q 0 = 1 := by
  have h1 := (pluckerPartitionProfile_zero_pos hpq).ne'
  have h2 : thetaExitProfile 0 ≠ 0 := by rw [thetaExitProfile_zero]; norm_num
  simp only [completionTransportProfile, zero_div, add_zero, one_pow, one_mul]
  exact div_self (mul_ne_zero h1 h2)

/-- `e (a_e - 1) → -2`. -/
theorem tendsto_mul_completionTransport_sub_one :
    Tendsto (fun e : ℕ => (e : ℝ) * (completionTransport p q e - 1)) atTop (𝓝 (-2)) := by
  have hinv : Tendsto (fun e : ℕ => (e : ℝ) * ((e : ℝ) ^ 2)⁻¹) atTop (𝓝 0) := by
    refine tendsto_inv_atTop_nhds_zero_nat.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with e he
    have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he
    field_simp
  have h0 := ((isBigO_refl (fun e : ℕ => (e : ℝ)) atTop).mul
    (isBigO_completionTransport_sub hpq)).trans_tendsto hinv
  have h := h0.sub (tendsto_const_nhds (x := (2 : ℝ)))
  rw [zero_sub] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with e he
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he
  field_simp
  ring

/-- `Φ'(0) = -2`. -/
theorem deriv_completionTransportProfile_zero :
    deriv (completionTransportProfile p q) 0 = -2 := by
  have hΦ := contDiffAt_completionTransportProfile_of (pluckerPartitionProfile_zero_pos hpq).ne'
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1
    (hΦ.differentiableAt one_ne_zero).hasDerivAt
  have hinv : Tendsto (fun e : ℕ => ((e : ℝ))⁻¹) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_inv_atTop_nhds_zero_nat,
      (eventually_ne_atTop 0).mono fun e he => inv_ne_zero (Nat.cast_ne_zero.mpr he)⟩
  have h1 := hslope.comp hinv
  refine tendsto_nhds_unique h1 ((tendsto_mul_completionTransport_sub_one hpq).congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with e he
  simp only [Function.comp, zero_add, inv_inv, smul_eq_mul]
  rw [completionTransport_eq_profile hpq he, completionTransportProfile_zero hpq]

/-- **(MPNLIH.10a).**  `a_e < a_{e+1}` for all large `e`. -/
theorem eventually_completionTransport_lt_succ :
    ∀ᶠ e : ℕ in atTop, completionTransport p q e < completionTransport p q (e + 1) := by
  have hΦ := contDiffAt_completionTransportProfile_of (pluckerPartitionProfile_zero_pos hpq).ne'
  have hstrict := hΦ.hasStrictDerivAt one_ne_zero
  rw [deriv_completionTransportProfile_zero hpq] at hstrict
  have ho := (hasStrictDerivAt_iff_hasStrictFDerivAt.1 hstrict).isLittleO
  have hb := ho.def (c := 1) one_pos
  have hpair : Tendsto (fun e : ℕ => (((e : ℝ))⁻¹, ((e : ℝ) + 1)⁻¹)) atTop (𝓝 ((0 : ℝ), (0 : ℝ))) :=
    tendsto_inv_atTop_nhds_zero_nat.prodMk_nhds
      ((tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr fun e => by simp)
  filter_upwards [hpair.eventually hb, eventually_ne_atTop 0] with e he he0
  have hepos : (0 : ℝ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he0)
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Real.norm_eq_abs,
    one_mul] at he
  have hd : 0 < (e : ℝ)⁻¹ - ((e : ℝ) + 1)⁻¹ := sub_pos.2 (inv_strictAnti₀ hepos (by linarith))
  rw [abs_of_pos hd] at he
  have hlt : completionTransportProfile p q (e : ℝ)⁻¹ <
      completionTransportProfile p q ((e : ℝ) + 1)⁻¹ := by
    have := (abs_le.1 he).2
    linarith
  rw [completionTransport_eq_profile hpq he0,
    completionTransport_eq_profile hpq (Nat.succ_ne_zero e)]
  push_cast
  exact hlt

/-- **(MPNLIH.10a).**  There is `E` with `a_e - a_{e-1} > 0` for every `e ≥ E`. -/
theorem exists_completionBoundaryCurvature_pos :
    ∃ E : ℕ, ∀ e ≥ E, 0 < completionBoundaryCurvature p q e := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_completionTransport_lt_succ hpq)
  refine ⟨N + 1, fun e he => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  rw [completionBoundaryCurvature_succ]
  exact sub_pos.2 (hN k (by omega))

/-- Negative spectral directions of `T` lie in a finite history head. -/
theorem exists_head_re_inner_completionSelfCommutator_nonneg :
    ∃ E : ℕ, ∀ x : ToeplitzSpace, (∀ e < E, (x : ℕ → ℂ) e = 0) →
      0 ≤ (⟪x, completionSelfCommutator hpq x⟫_ℂ).re := by
  obtain ⟨E, hE⟩ := exists_completionBoundaryCurvature_pos hpq
  refine ⟨E, fun x hx => ?_⟩
  rw [lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner _ _)]
  refine tsum_nonneg fun e => ?_
  rw [completionSelfCommutator_eq, realSummableDiagonalOperator_apply, RCLike.inner_apply]
  by_cases he : e < E
  · rw [hx e he]
    simp
  · have hc : ((completionBoundaryCurvature p q e : ℝ) : ℂ) * (x : ℕ → ℂ) e *
        (starRingEnd ℂ) ((x : ℕ → ℂ) e) =
        ((completionBoundaryCurvature p q e * ‖(x : ℕ → ℂ) e‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_assoc, Complex.mul_conj']
      push_cast
      ring
    rw [hc, Complex.ofReal_re]
    exact mul_nonneg (hE e (not_lt.1 he)).le (by positivity)

end Positivity

/-! ## The literal embedding on moving null lines -/

section Literal

variable (p q : Nat.Primes)

theorem pluckerSpectralKernelVector_pos (e : ℕ) (i : Fin 4) :
    0 < gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q i :=
  inv_pos.2 (Real.sqrt_pos.2 (gammaSewnCriticalPrimeDepthPacket_node_pos e p q i))

/-- `‖v_e‖`. -/
def nullLineNorm (e : ℕ) : ℝ :=
  Real.sqrt (∑ i, gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q i ^ 2)

/-- **(MPNLIH.2).**  The unit null vector `u_e = v_e/‖v_e‖`. -/
def nullLineVector (e : ℕ) (i : Fin 4) : ℝ :=
  gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q i / nullLineNorm p q e

theorem nullLineNorm_pos (e : ℕ) : 0 < nullLineNorm p q e :=
  Real.sqrt_pos.2 (Finset.sum_pos (fun i _ => pow_pos (pluckerSpectralKernelVector_pos p q e i) 2)
    Finset.univ_nonempty)

theorem nullLineVector_pos (e : ℕ) (i : Fin 4) : 0 < nullLineVector p q e i :=
  div_pos (pluckerSpectralKernelVector_pos p q e i) (nullLineNorm_pos p q e)

theorem sum_nullLineVector_sq (e : ℕ) : ∑ i, nullLineVector p q e i ^ 2 = 1 := by
  simp only [nullLineVector, div_pow]
  rw [← Finset.sum_div, nullLineNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    div_self (ne_of_gt (Finset.sum_pos
      (fun i _ => pow_pos (pluckerSpectralKernelVector_pos p q e i) 2) Finset.univ_nonempty))]

/-- `u_e` spans the null line of the physical Plücker block. -/
theorem mulVec_nullLineVector {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) (e : ℕ) :
    (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q).mulVec (nullLineVector p q e) =
      0 := by
  have h : nullLineVector p q e = (nullLineNorm p q e)⁻¹ •
      gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q := by
    funext i
    simp [nullLineVector, div_eq_inv_mul]
  rw [h, Matrix.mulVec_smul,
    gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector_mulVec_eq_zero hpq, smul_zero]

/-- The coordinates of `x ↦ (u_e x_e)_e`. -/
def nullLineEmbeddingFun (x : ℕ → ℂ) : ℕ × Fin 4 → ℂ :=
  fun z => (nullLineVector p q z.1 z.2 : ℂ) * x z.1

theorem sum_norm_sq_nullLineEmbeddingFun (x : ℕ → ℂ) (e : ℕ) :
    ∑ i, ‖nullLineEmbeddingFun p q x (e, i)‖ ^ 2 = ‖x e‖ ^ 2 := by
  simp only [nullLineEmbeddingFun, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs]
  rw [← Finset.sum_mul, sum_nullLineVector_sq, one_mul]

theorem memℓp_nullLineEmbeddingFun (x : ToeplitzSpace) :
    Memℓp (nullLineEmbeddingFun p q x) 2 := by
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff h2]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  refine (summable_prod_of_nonneg fun _ => by positivity).2 ⟨fun _ => Summable.of_finite, ?_⟩
  simpa [tsum_fintype, sum_norm_sq_nullLineEmbeddingFun] using HilbertSchmidt.summable_coe_sq x

theorem norm_nullLineEmbeddingFun (x : ToeplitzSpace) :
    ‖(⟨nullLineEmbeddingFun p q x, memℓp_nullLineEmbeddingFun p q x⟩ :
      DiagonalL2 (ℕ × Fin 4))‖ = ‖x‖ := by
  have hsq : ‖(⟨nullLineEmbeddingFun p q x, memℓp_nullLineEmbeddingFun p q x⟩ :
      DiagonalL2 (ℕ × Fin 4))‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq, HilbertSchmidt.lp_norm_sq_eq,
      (HilbertSchmidt.summable_coe_sq (⟨nullLineEmbeddingFun p q x,
        memℓp_nullLineEmbeddingFun p q x⟩ : DiagonalL2 (ℕ × Fin 4))).tsum_prod]
    refine tsum_congr fun e => ?_
    rw [tsum_fintype]
    exact sum_norm_sq_nullLineEmbeddingFun p q x e
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

/-- The literal isometric embedding `J : K → ℓ²(ℕ × Fin 4)`, `J ε_e = (e, u_e)`. -/
def nullLineEmbedding : ToeplitzSpace →L[ℂ] DiagonalL2 (ℕ × Fin 4) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨nullLineEmbeddingFun p q x, memℓp_nullLineEmbeddingFun p q x⟩
      map_add' := fun x y => by
        apply lp.ext
        funext z
        change nullLineEmbeddingFun p q ⇑(x + y) z =
          nullLineEmbeddingFun p q ⇑x z + nullLineEmbeddingFun p q ⇑y z
        simp only [nullLineEmbeddingFun, lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c x => by
        apply lp.ext
        funext z
        change nullLineEmbeddingFun p q ⇑(c • x) z = c * nullLineEmbeddingFun p q ⇑x z
        simp only [nullLineEmbeddingFun, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        ring }
    1 (fun x => by rw [one_mul]; exact (norm_nullLineEmbeddingFun p q x).le)

theorem nullLineEmbedding_apply (x : ToeplitzSpace) (z : ℕ × Fin 4) :
    (nullLineEmbedding p q x : ℕ × Fin 4 → ℂ) z =
      (nullLineVector p q z.1 z.2 : ℂ) * (x : ℕ → ℂ) z.1 := rfl

theorem norm_nullLineEmbedding_apply (x : ToeplitzSpace) : ‖nullLineEmbedding p q x‖ = ‖x‖ :=
  norm_nullLineEmbeddingFun p q x

theorem adjoint_nullLineEmbedding_single (e : ℕ) (i : Fin 4) :
    ContinuousLinearMap.adjoint (nullLineEmbedding p q)
        (lp.single 2 (e, i) (1 : ℂ) : DiagonalL2 (ℕ × Fin 4)) =
      (nullLineVector p q e i : ℂ) • (lp.single 2 e (1 : ℂ) : ToeplitzSpace) := by
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right, lp.inner_single_right, inner_smul_right,
    lp.inner_single_right, nullLineEmbedding_apply]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

variable {p q} (hpq : (p : ℕ) < (q : ℕ))

/-- **(MPNLIH.10).**  `T` in the literal embedding: `J T J*` on `ℓ²(ℕ × Fin 4)`. -/
def literalNullLineDefect : DiagonalL2 (ℕ × Fin 4) →L[ℂ] DiagonalL2 (ℕ × Fin 4) :=
  nullLineEmbedding p q ∘L completionSelfCommutator hpq ∘L
    ContinuousLinearMap.adjoint (nullLineEmbedding p q)

/-- **(MPNLIH.10).**  The depth blocks of `J T J*` are `(a_e - a_{e-1}) u_e u_eᵀ`. -/
theorem inner_single_literalNullLineDefect_single (e : ℕ) (i : Fin 4) (e' : ℕ) (j : Fin 4) :
    ⟪(lp.single 2 (e, i) (1 : ℂ) : DiagonalL2 (ℕ × Fin 4)),
        literalNullLineDefect hpq (lp.single 2 (e', j) 1)⟫_ℂ =
      if e = e' then ((completionBoundaryCurvature p q e * nullLineVector p q e i *
        nullLineVector p q e j : ℝ) : ℂ) else 0 := by
  rw [literalNullLineDefect, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_left, adjoint_nullLineEmbedding_single,
    adjoint_nullLineEmbedding_single, map_smul, completionSelfCommutator_single,
    inner_smul_left, inner_smul_right, inner_smul_right, lp.inner_single_left]
  split_ifs with h
  · subst h
    rw [lp.single_apply_self]
    simp only [RCLike.inner_apply, map_one, mul_one, Complex.conj_ofReal]
    push_cast
    ring
  · rw [lp.single_apply_ne _ _ _ h]
    simp

/-- **Prime mixing.**  Every entry of the zeroth block, in particular each entry joining a `p`
cell to a `q` cell, is nonzero. -/
theorem literalNullLineDefect_zero_block_ne_zero (i j : Fin 4) :
    ⟪(lp.single 2 (0, i) (1 : ℂ) : DiagonalL2 (ℕ × Fin 4)),
        literalNullLineDefect hpq (lp.single 2 (0, j) 1)⟫_ℂ ≠ 0 := by
  rw [inner_single_literalNullLineDefect_single, if_pos rfl, Complex.ofReal_ne_zero]
  exact (mul_pos (mul_pos (completionTransport_pos hpq 0) (nullLineVector_pos p q 0 i))
    (nullLineVector_pos p q 0 j)).ne'

/-- **(MPNLIH, 5).**  `J T J*` is not a history diagonal tensored with a fixed nonzero packet
matrix. -/
theorem literalNullLineDefect_not_separable :
    ¬ ∃ (d : ℕ → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ), ∀ (e : ℕ) (i j : Fin 4),
      ⟪(lp.single 2 (e, i) (1 : ℂ) : DiagonalL2 (ℕ × Fin 4)),
          literalNullLineDefect hpq (lp.single 2 (e, j) 1)⟫_ℂ = d e * A i j := by
  rintro ⟨d, A, hA⟩
  obtain ⟨E, hE⟩ := exists_completionBoundaryCurvature_pos hpq
  set e := E + 1
  have hbe := hE e (by omega)
  have hb0 := completionTransport_pos hpq 0
  have hblock : ∀ k i j, d k * A i j = ((completionBoundaryCurvature p q k *
      nullLineVector p q k i * nullLineVector p q k j : ℝ) : ℂ) := fun k i j => by
    rw [← hA, inner_single_literalNullLineDefect_single, if_pos rfl]
  have h00 := hblock 0 0 0
  have h10 := hblock 0 1 0
  have he00 := hblock e 0 0
  have he10 := hblock e 1 0
  set u := nullLineVector p q
  have key : ((completionBoundaryCurvature p q 0 * completionBoundaryCurvature p q e *
      u 0 0 * u e 0 * (u 0 0 * u e 1 - u 0 1 * u e 0) : ℝ) : ℂ) = 0 := by
    push_cast at h00 h10 he00 he10 ⊢
    linear_combination (-(d e * A 1 0)) * h00 + (-(↑(completionBoundaryCurvature p q 0) *
      ↑(u 0 0) * ↑(u 0 0))) * he10 + (d e * A 0 0) * h10 +
      (↑(completionBoundaryCurvature p q 0) * ↑(u 0 1) * ↑(u 0 0)) * he00
  rw [Complex.ofReal_eq_zero] at key
  have hb0' : 0 < completionBoundaryCurvature p q 0 := hb0
  have hcross : u 0 0 * u e 1 = u 0 1 * u e 0 := by
    have hne : completionBoundaryCurvature p q 0 * completionBoundaryCurvature p q e *
        u 0 0 * u e 0 ≠ 0 := (mul_pos (mul_pos (mul_pos hb0' hbe) (nullLineVector_pos p q 0 0))
          (nullLineVector_pos p q e 0)).ne'
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left hne)
  have hv : ∀ k : ℕ, ∀ i : Fin 4, u k i =
      gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector k p q i / nullLineNorm p q k :=
    fun k i => rfl
  rw [hv, hv, hv, hv, pluckerSpectralKernelVector_eq, pluckerSpectralKernelVector_eq] at hcross
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hcross
  have hI := gammaSewnMobiusApertureStokesInverseTilt_pos (s := 1 / 2) (by norm_num) p
  have hn0 := nullLineNorm_pos p q 0
  have hne := nullLineNorm_pos p q e
  field_simp at hcross
  have heR : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast (show 1 ≤ e by omega)
  push_cast at hcross
  nlinarith [mul_pos hI hI]

end Literal

/-! ## The moving null-line homotopy defect theorem -/

/-- **(MPNLIH.12).**  Five readings of one unit: `(6-4)/2`, the formation residue, `lim a_N`,
`-ind C` and `Tr T`. -/
theorem movingNullLine_unit_readings {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    formationCharge 6 4 = 1 ∧
      HasFormationResidue (formationHalfDensity p q) 1 ∧
      Tendsto (completionTransport p q) atTop (𝓝 1) ∧
      ((-completionShiftIndex hpq : ℤ) : ℂ) = 1 ∧
      (completionSelfCommutator hpq).opTrace = 1 := by
  obtain ⟨hres, hq⟩ := hasFormationResidue_formationHalfDensity hpq
  obtain ⟨hT, hind⟩ := opTrace_completionSelfCommutator hpq
  exact ⟨hq, hq ▸ hres, tendsto_completionTransport hpq, hind.trans hT, hT⟩

/-- The first physical prime edge `(2, 3)`. -/
theorem two_lt_three_primes :
    ((⟨2, Nat.prime_two⟩ : Nat.Primes) : ℕ) < ((⟨3, Nat.prime_three⟩ : Nat.Primes) : ℕ) := by
  norm_num

/-- **(MPNLIH.11).**  The fixed-edge realization `T = T_{(2,3)}`. -/
def firstEdgeMovingNullLineDefect : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  completionSelfCommutator two_lt_three_primes

theorem firstEdgeMovingNullLineDefect_opTrace : firstEdgeMovingNullLineDefect.opTrace = 1 :=
  (opTrace_completionSelfCommutator two_lt_three_primes).1

/-- **Theorem MPNLIH.**  For primes `p < q`: `C ε_e = α_e ε_{e+1}` is bounded, bounded below and
injective with closed range `ε_0^⊥` and `ind C = -1`; `T = C*C - CC*` is self-adjoint, nuclear and
diagonal with entries `(a_0, a_1 - a_0, …)`; `Tr(Q_N T Q_N) = a_N`, `Tr T = 1 = -ind C`; the chiral
Laplacians are not nuclear; in the literal embedding the depth blocks are
`(a_e - a_{e-1}) u_e u_eᵀ`, the zeroth block is fully prime-mixed and the operator is not
history-diagonal ⊗ fixed packet; and `a_e - a_{e-1} > 0` for large `e`. -/
theorem moving_plucker_null_line_homotopy_defect {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    LinearMap.ker (completionShift hpq).toLinearMap = ⊥ ∧
    (∀ y, y ∈ LinearMap.range (completionShift hpq).toLinearMap ↔ (y : ℕ → ℂ) 0 = 0) ∧
    IsClosed (LinearMap.range (completionShift hpq).toLinearMap : Set ToeplitzSpace) ∧
    completionShiftIndex hpq = -1 ∧
    (∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖completionShift hpq x‖) ∧
    completionSelfCommutator hpq = realSummableDiagonalOperator (completionBoundaryCurvature p q)
      (summable_abs_completionBoundaryCurvature hpq) ∧
    IsSelfAdjoint (completionSelfCommutator hpq) ∧
    MemSchattenClass 1 (completionSelfCommutator hpq) ∧
    (∀ N, (historyHeadProjection N ∘L completionSelfCommutator hpq ∘L
      historyHeadProjection N).opTrace = ((completionTransport p q N : ℝ) : ℂ)) ∧
    (completionSelfCommutator hpq).opTrace = 1 ∧
    ((-completionShiftIndex hpq : ℤ) : ℂ) = (completionSelfCommutator hpq).opTrace ∧
    (¬ MemSchattenClass 1 (ContinuousLinearMap.adjoint (completionShift hpq) ∘L
        completionShift hpq) ∧
      ¬ MemSchattenClass 1 (completionShift hpq ∘L
        ContinuousLinearMap.adjoint (completionShift hpq))) ∧
    (∀ e i e' j, ⟪(lp.single 2 (e, i) (1 : ℂ) : DiagonalL2 (ℕ × Fin 4)),
        literalNullLineDefect hpq (lp.single 2 (e', j) 1)⟫_ℂ =
      if e = e' then ((completionBoundaryCurvature p q e * nullLineVector p q e i *
        nullLineVector p q e j : ℝ) : ℂ) else 0) ∧
    (∀ i j : Fin 4, ⟪(lp.single 2 (0, i) (1 : ℂ) : DiagonalL2 (ℕ × Fin 4)),
        literalNullLineDefect hpq (lp.single 2 (0, j) 1)⟫_ℂ ≠ 0) ∧
    (¬ ∃ (d : ℕ → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ), ∀ (e : ℕ) (i j : Fin 4),
      ⟪(lp.single 2 (e, i) (1 : ℂ) : DiagonalL2 (ℕ × Fin 4)),
          literalNullLineDefect hpq (lp.single 2 (e, j) 1)⟫_ℂ = d e * A i j) ∧
    ∃ E : ℕ, ∀ e ≥ E, 0 < completionBoundaryCurvature p q e :=
  ⟨ker_completionShift hpq, mem_range_completionShift_iff hpq, isClosed_range_completionShift hpq,
    completionShiftIndex_eq hpq, exists_completionShift_bounded_below hpq,
    completionSelfCommutator_eq hpq, completionSelfCommutator_isSelfAdjoint hpq,
    completionSelfCommutator_memSchattenClass_one hpq,
    opTrace_historyHeadProjection_sandwich hpq, (opTrace_completionSelfCommutator hpq).1,
    (opTrace_completionSelfCommutator hpq).2, chiralLaplacians_not_memSchattenClass_one hpq,
    inner_single_literalNullLineDefect_single hpq, literalNullLineDefect_zero_block_ne_zero hpq,
    literalNullLineDefect_not_separable hpq, exists_completionBoundaryCurvature_pos hpq⟩

end GaloisForLFunctions.HTGeometry

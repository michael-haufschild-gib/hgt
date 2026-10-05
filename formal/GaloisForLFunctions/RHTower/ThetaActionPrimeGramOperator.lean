import GaloisForLFunctions.RHTower.MertensClockDefectTraceClass
import GaloisForLFunctions.RHTower.ThetaCdfActionClock
import GaloisForLFunctions.RHTower.TraceNorm
import GaloisForLFunctions.RHTower.PerronLaplaceKernel

/-!
# The theta-clock prime Gram operator

Replace the Mertens clock `x_p = log log p` of the prime Poisson Gram operator
`K(p,q) = (pq)^{-1/2} sech²((x_p − x_q)/2)` by the theta CDF action `Φ_p`:

`K_Φ(p,q) = (pq)^{-1/2} sech²((Φ_p − Φ_q)/2)`.

The sharp action clock `Φ_p = log log p − log π + O(log log p/log p)` places the theta step clock
`φ_Φ = Φ_p + log π + B` on the prime cell `I_p` within `O(e^{-y/2})` of the identity.  The
clock-defect trace-class theorem then shows that `K_Φ` is bounded and positive, that `K_Φ − K` is
trace class with trace zero, and that `K_Φ` has essential spectrum `[0, 4]`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RHTower

open GaloisForLFunctions.HTGeometry HedenmalmThetaSource

noncomputable section

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2
local notation "L²₊" => Lp ℂ 2 halfLineMeasure

/-! ## The prime calibration of the theta action -/

theorem log_pos_of_prime {p : ℕ} (hp : p.Prime) : 0 < Real.log p :=
  Real.log_pos (by exact_mod_cast hp.one_lt)

theorem exp_log_log_of_prime {p : ℕ} (hp : p.Prime) : Real.exp (Real.log (Real.log p)) = Real.log p :=
  Real.exp_log (log_pos_of_prime hp)

/-- **Prime calibration**: `Φ_p = x_p − log π + O((1 + x_p) e^{-x_p})`, `x_p = log log p`. -/
theorem exists_abs_cdfAction_prime_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ p : ℕ, p.Prime → N₀ ≤ p →
      |cdfAction p - (Real.log (Real.log p) - Real.log Real.pi)| ≤
        C * ((1 + Real.log (Real.log p)) * Real.exp (-Real.log (Real.log p))) := by
  obtain ⟨C, hC, N₀, hN₀⟩ := exists_abs_cdfAction_sub_loglog_le
  refine ⟨C, hC, N₀, fun p hp hpN => (hN₀ p hpN).trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hC
  rw [Real.exp_neg, exp_log_log_of_prime hp, div_eq_mul_inv]
  have := log_pos_of_prime hp
  have : 0 ≤ (Real.log p)⁻¹ := by positivity
  nlinarith

/-- The cell offset `Φ_p + log π − log log p` is `O(e^{-x_p/2})` uniformly over primes. -/
theorem exists_abs_cdfAction_prime_offset_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p : ℕ, p.Prime →
      |cdfAction p + Real.log Real.pi - Real.log (Real.log p)| ≤
        A * Real.exp (-(Real.log (Real.log p) / 2)) := by
  obtain ⟨C, hC, N₀, hN₀⟩ := exists_abs_cdfAction_sub_loglog_le
  set N₁ := N₀ + 3
  set K₁ := ∑ n ∈ Finset.range N₁, |cdfAction n + Real.log Real.pi - Real.log (Real.log n)|
  have hK₁ : 0 ≤ K₁ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨C + K₁ * Real.exp (Real.log (Real.log N₁) / 2), by positivity, fun p hp => ?_⟩
  have hlp := log_pos_of_prime hp
  set x := Real.log (Real.log p)
  have hE : 0 ≤ Real.exp (-(x / 2)) := (Real.exp_pos _).le
  by_cases hpN : N₁ ≤ p
  · -- the clock range
    have h := hN₀ p (by omega)
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
    have hlog1 : 1 ≤ Real.log p := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hx0 : 0 ≤ x := Real.log_nonneg hlog1
    have hrat : x / Real.log p ≤ Real.exp (-(x / 2)) := by
      have hlx : Real.log p = Real.exp x := (exp_log_log_of_prime hp).symm
      rw [hlx, div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
      have := le_exp_half hx0
      calc x ≤ Real.exp (x / 2) := this
        _ = Real.exp (-(x / 2) + x) := by ring_nf
    have h' : |cdfAction p + Real.log Real.pi - x| ≤ C * Real.exp (-(x / 2)) := by
      rw [show cdfAction p + Real.log Real.pi - x = cdfAction p - (x - Real.log Real.pi) by ring]
      exact h.trans (mul_le_mul_of_nonneg_left hrat hC)
    refine h'.trans ?_
    have : 0 ≤ K₁ * Real.exp (Real.log (Real.log N₁) / 2) * Real.exp (-(x / 2)) := by positivity
    nlinarith
  · -- the finitely many small primes
    push Not at hpN
    have hsmall : |cdfAction p + Real.log Real.pi - x| ≤ K₁ :=
      Finset.single_le_sum (f := fun n : ℕ => |cdfAction n + Real.log Real.pi - Real.log (Real.log n)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.2 hpN)
    have hxN : x ≤ Real.log (Real.log N₁) := by
      have hpN' : (p : ℝ) ≤ N₁ := by exact_mod_cast hpN.le
      exact Real.log_le_log hlp (Real.log_le_log (by exact_mod_cast hp.pos) hpN')
    have hone : 1 ≤ Real.exp (Real.log (Real.log N₁) / 2) * Real.exp (-(x / 2)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    have : K₁ ≤ K₁ * (Real.exp (Real.log (Real.log N₁) / 2) * Real.exp (-(x / 2))) := by
      nlinarith
    nlinarith

/-! ## The theta step clock -/

/-- The theta step clock `φ_Φ(y) = Φ_p + log π + B` on the prime cell `I_p`. -/
def thetaStepClock (y : ℝ) : ℝ :=
  cdfAction (primeCellIndex y) + Real.log Real.pi + Sieve.meisselMertensConst

theorem measurable_thetaStepClock : Measurable thetaStepClock :=
  (measurable_from_nat (f := fun m : ℕ =>
    cdfAction m + Real.log Real.pi + Sieve.meisselMertensConst)).comp measurable_primeCellIndex

theorem thetaStepClock_of_mem {p : ℕ} (hp : p.Prime) {y : ℝ} (hy : y ∈ primeCell p) :
    thetaStepClock y = cdfAction p + Real.log Real.pi + Sieve.meisselMertensConst := by
  rw [thetaStepClock, primeCellIndex_eq hp hy]

/-- **The theta clock estimate**: `|φ_Φ(y) − y| ≤ D e^{-y/2}` for `y ≥ 0`. -/
theorem exists_abs_thetaStepClock_sub_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y, 0 ≤ y → |thetaStepClock y - y| ≤ D * Real.exp (-(y / 2)) := by
  obtain ⟨A, hA, hAp⟩ := exists_abs_cdfAction_prime_offset_le
  set E := mertensClockConst
  set B := Sieve.meisselMertensConst
  have hE := mertensClockConst_nonneg
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c₂ := Real.exp (-(Real.log (Real.log 2) / 2))
  refine ⟨(A + E * c₂) * Real.exp ((B + E / Real.log 2) / 2), by positivity, fun y hy => ?_⟩
  obtain ⟨hp, hmem⟩ := primeCellIndex_spec hy
  set p := primeCellIndex y
  have hlp := log_pos_of_prime hp
  set x := Real.log (Real.log p)
  have hlogp2 : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have hx2 : Real.log (Real.log 2) ≤ x := Real.log_le_log hlog2 hlogp2
  have hM := abs_mertensStepClock_sub_le_div_log hp hmem
  rw [mertensStepClock_of_mem hp hmem] at hM
  have hoff := hAp p hp
  -- `E/log p ≤ E c₂ e^{-x/2}`
  have hEl : E / Real.log p ≤ E * c₂ * Real.exp (-(x / 2)) := by
    have hlx : Real.log p = Real.exp x := (exp_log_log_of_prime hp).symm
    have hc : Real.exp (-(x / 2)) ≤ c₂ := Real.exp_le_exp.mpr (by linarith)
    rw [hlx, div_eq_mul_inv, ← Real.exp_neg, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hE
    calc Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ c₂ * Real.exp (-(x / 2)) := mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
  -- `y ≤ x + B + E/log 2`
  have hyx : y ≤ x + B + E / Real.log 2 := by
    have h1 := (abs_le.1 hM).1
    have h2 : E / Real.log p ≤ E / Real.log 2 := div_le_div_of_nonneg_left hE hlog2 hlogp2
    linarith
  have hexp : Real.exp (-(x / 2)) ≤ Real.exp ((B + E / Real.log 2) / 2) * Real.exp (-(y / 2)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hsplit : thetaStepClock y - y =
      (cdfAction p + Real.log Real.pi - x) + (x + B - y) := by
    rw [thetaStepClock_of_mem hp hmem]; ring
  rw [hsplit]
  calc |(cdfAction p + Real.log Real.pi - x) + (x + B - y)|
      ≤ |cdfAction p + Real.log Real.pi - x| + |x + B - y| := abs_add_le _ _
    _ ≤ A * Real.exp (-(x / 2)) + E * c₂ * Real.exp (-(x / 2)) := add_le_add hoff (hM.trans hEl)
    _ = (A + E * c₂) * Real.exp (-(x / 2)) := by ring
    _ ≤ (A + E * c₂) * (Real.exp ((B + E / Real.log 2) / 2) * Real.exp (-(y / 2))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

/-- The decay constant of the theta clock. -/
def thetaClockConst : ℝ := Classical.choose exists_abs_thetaStepClock_sub_le

theorem thetaClockConst_nonneg : 0 ≤ thetaClockConst :=
  (Classical.choose_spec exists_abs_thetaStepClock_sub_le).1

theorem abs_thetaStepClock_sub_le {y : ℝ} (hy : 0 ≤ y) :
    |thetaStepClock y - y| ≤ thetaClockConst * Real.exp (-(y / 2)) :=
  (Classical.choose_spec exists_abs_thetaStepClock_sub_le).2 y hy

/-- **The theta half-line clock**: `φ_Φ` on `[0, ∞)`, continued by the identity. -/
def thetaHalfLineClock : HalfLineClock where
  toFun y := if 0 ≤ y then thetaStepClock y else y
  measurable := Measurable.ite measurableSet_Ici measurable_thetaStepClock measurable_id
  eq_of_neg hy := if_neg (not_le.mpr hy)
  D := thetaClockConst
  D_nonneg := thetaClockConst_nonneg
  abs_sub_le {y} hy := by
    simp only [if_pos hy]
    exact abs_thetaStepClock_sub_le hy

theorem thetaHalfLineClock_of_mem {p : ℕ} (hp : p.Prime) {y : ℝ} (hy : y ∈ primeCell p) :
    thetaHalfLineClock.toFun y = cdfAction p + Real.log Real.pi + Sieve.meisselMertensConst := by
  show (if 0 ≤ y then thetaStepClock y else y) = _
  rw [if_pos (show (0 : ℝ) ≤ y from primeCell_subset_Ici p hy), thetaStepClock_of_mem hp hy]

/-! ## The step operators -/

/-- The Schur kernel `h(ψ(y) − ψ(z))` of a half-line clock, `h = sech²(·/2)`. -/
def halfLineClockSechKernel (ψ : HalfLineClock) : SchurKernel halfLineMeasure where
  toFun y z := (sechSqHalf (ψ.toFun y - ψ.toFun z) : ℂ)
  measurable := Complex.measurable_ofReal.comp
    (measurable_sechSqHalf.comp ((ψ.measurable.comp measurable_fst).sub
      (ψ.measurable.comp measurable_snd)))
  bound := Real.toNNReal (4 * Real.exp (1 * (2 * ψ.D)) * (2 / 1))
  row y := (setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_clock_kernel_le (by norm_num) one_pos abs_sechSqHalf_le ψ.abs_sub_le_const y)
  col z := (setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_clock_kernel_le' (by norm_num) one_pos abs_sechSqHalf_le ψ.abs_sub_le_const z)

/-- The theta step operator `A_Φ`, kernel `h(φ_Φ(y) − φ_Φ(z))`. -/
def thetaStepSechOp : L²₊ →L[ℂ] L²₊ := (halfLineClockSechKernel thetaHalfLineClock).op

/-- **The theta-clock prime Gram operator** `K_Φ = U* A_Φ U`. -/
def thetaPrimeGramOp : ℓ²P →L[ℂ] ℓ²P := primeCellOp.adjoint ∘L thetaStepSechOp ∘L primeCellOp

theorem thetaStepSechKernel_toFun_of_mem {p q : Nat.Primes} {y z : ℝ} (hy : y ∈ primeCell p)
    (hz : z ∈ primeCell q) :
    (halfLineClockSechKernel thetaHalfLineClock).toFun y z =
      (sechSqHalf (cdfAction (p : ℕ) - cdfAction (q : ℕ)) : ℂ) := by
  change ((sechSqHalf (thetaHalfLineClock.toFun y - thetaHalfLineClock.toFun z) : ℝ) : ℂ) = _
  rw [thetaHalfLineClock_of_mem p.prop hy, thetaHalfLineClock_of_mem q.prop hz]
  congr 2
  ring

/-- **The matrix of `K_Φ`**: `⟨δ_p, K_Φ δ_q⟩ = (pq)^{-1/2} h(Φ_p − Φ_q)`. -/
theorem hasLpMatrix_thetaPrimeGramOp :
    HasLpMatrix thetaPrimeGramOp fun p q =>
      ((sechSqHalf (cdfAction (p : ℕ) - cdfAction (q : ℕ)) /
        (Real.sqrt (p : ℕ) * Real.sqrt (q : ℕ)) : ℝ) : ℂ) := by
  intro p q
  rw [coord_eq_inner, thetaPrimeGramOp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply, primeCellOp_lpBasisVec,
    primeCellOp_lpBasisVec, thetaStepSechOp,
    inner_primeCellVec_op_of_const _ fun y hy z hz => thetaStepSechKernel_toFun_of_mem hy hz]
  push_cast
  ring

theorem isSelfAdjoint_thetaStepSechOp : IsSelfAdjoint thetaStepSechOp :=
  SchurKernel.isSelfAdjoint_op _ fun y z => by
    change (starRingEnd ℂ) ((sechSqHalf (thetaHalfLineClock.toFun z - thetaHalfLineClock.toFun y) : ℝ) : ℂ) =
      ((sechSqHalf (thetaHalfLineClock.toFun y - thetaHalfLineClock.toFun z) : ℝ) : ℂ)
    rw [Complex.conj_ofReal, ← neg_sub, sechSqHalf_neg]

theorem re_inner_thetaStepSechOp_nonneg (f : L²₊) : 0 ≤ (inner ℂ f (thetaStepSechOp f)).re :=
  SchurKernel.re_inner_op_nonneg_of_sechSqHalf _ thetaHalfLineClock.measurable (fun _ _ => rfl) f

theorem isSelfAdjoint_thetaPrimeGramOp : IsSelfAdjoint thetaPrimeGramOp :=
  isSelfAdjoint_thetaStepSechOp.adjoint_conj primeCellOp

theorem re_inner_thetaPrimeGramOp_nonneg (f : ℓ²P) : 0 ≤ (inner ℂ f (thetaPrimeGramOp f)).re := by
  rw [thetaPrimeGramOp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply]
  exact re_inner_thetaStepSechOp_nonneg _

/-- **`K_Φ` is a bounded positive operator.** -/
theorem isPositive_thetaPrimeGramOp : thetaPrimeGramOp.IsPositive :=
  isPositive_of_re_inner_nonneg isSelfAdjoint_thetaPrimeGramOp re_inner_thetaPrimeGramOp_nonneg

/-! ## The trace-class comparison -/

theorem sub_thetaStepSechKernel_toFun (y z : ℝ) :
    (SchurKernel.sub (halfLineClockSechKernel thetaHalfLineClock) wienerHopfSechKernel).toFun y z =
      ((sechSqHalfProfile.g (thetaHalfLineClock.toFun y - thetaHalfLineClock.toFun z) -
        sechSqHalfProfile.g (y - z) : ℝ) : ℂ) := by
  show ((sechSqHalf (thetaHalfLineClock.toFun y - thetaHalfLineClock.toFun z) : ℝ) : ℂ) -
    ((sechSqHalf (y - z) : ℝ) : ℂ) = _
  push_cast; rfl

/-- **`A_Φ − W` is trace class with zero trace.** -/
theorem memSchattenClass_one_thetaStepSechOp_sub :
    MemSchattenClass 1 (thetaStepSechOp - wienerHopfSechOp) := by
  rw [thetaStepSechOp, wienerHopfSechOp, ← SchurKernel.sub_op]
  exact sechSqHalfProfile.memSchattenClass_one_op thetaHalfLineClock _ sub_thetaStepSechKernel_toFun

theorem opTrace_thetaStepSechOp_sub :
    ContinuousLinearMap.opTrace (thetaStepSechOp - wienerHopfSechOp) = 0 := by
  rw [thetaStepSechOp, wienerHopfSechOp, ← SchurKernel.sub_op]
  exact sechSqHalfProfile.opTrace_op thetaHalfLineClock _ sub_thetaStepSechKernel_toFun

/-- The step-operator difference `A_Φ − A`. -/
theorem memSchattenClass_one_thetaStepSechOp_sub_mertensStepSechOp :
    MemSchattenClass 1 (thetaStepSechOp - mertensStepSechOp) := by
  have h1 := memSchattenClass_one_thetaStepSechOp_sub
  have h2 := memSchattenClass_one_smul memSchattenClass_one_mertensStepSechOp_sub (-1)
  have h := memSchattenClass_one_add (h1.isCompactOperator one_pos) (h2.isCompactOperator one_pos) h1 h2
  have e : thetaStepSechOp - wienerHopfSechOp + (-1 : ℂ) • (mertensStepSechOp - wienerHopfSechOp) =
      thetaStepSechOp - mertensStepSechOp := by
    rw [neg_one_smul]; abel
  rwa [e] at h

/-- The compression `K_Φ − K = U*(A_Φ − A)U`. -/
theorem thetaPrimeGramOp_sub_poissonPrimeOp :
    thetaPrimeGramOp - poissonPrimeOp =
      primeCellOp.adjoint ∘L (thetaStepSechOp - mertensStepSechOp) ∘L primeCellOp := by
  rw [thetaPrimeGramOp, poissonPrimeOp, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

/-- A trace-class factorization of `K_Φ − K` through Hilbert–Schmidt maps. -/
theorem exists_hs_factorization_thetaPrimeGramOp_sub :
    ∃ (S : L²₊ →L[ℂ] ℓ²P) (V : ℓ²P →L[ℂ] L²₊), S.IsHilbertSchmidt ∧ V.IsHilbertSchmidt ∧
      thetaPrimeGramOp - poissonPrimeOp = S ∘L V := by
  obtain ⟨S, V, hS, hV, hfac⟩ := memSchattenClass_one_thetaStepSechOp_sub_mertensStepSechOp.one_isTraceClass
  refine ⟨primeCellOp.adjoint ∘L S, V ∘L primeCellOp, hS.comp_left _, hV.comp_right _, ?_⟩
  rw [thetaPrimeGramOp_sub_poissonPrimeOp, hfac]
  rfl

/-- **`K_Φ − K` is trace class.** -/
theorem memSchattenClass_one_thetaPrimeGramOp_sub :
    MemSchattenClass 1 (thetaPrimeGramOp - poissonPrimeOp) := by
  obtain ⟨S, V, hS, hV, hfac⟩ := exists_hs_factorization_thetaPrimeGramOp_sub
  rw [hfac]
  exact memSchattenClass_one_comp hS hV

/-- The canonical Hilbert basis of `ℓ²(primes)`. -/
def primeHilbertBasis : HilbertBasis Nat.Primes ℂ ℓ²P := ⟨LinearIsometryEquiv.refl ℂ ℓ²P⟩

theorem primeHilbertBasis_apply (p : Nat.Primes) : primeHilbertBasis p = lpBasisVec p := by
  classical
  rw [← HilbertBasis.repr_symm_single]
  rfl

theorem inner_lpBasisVec_thetaPrimeGramOp_sub_self (p : Nat.Primes) :
    inner ℂ (lpBasisVec p) ((thetaPrimeGramOp - poissonPrimeOp) (lpBasisVec p)) = 0 := by
  rw [sub_apply, inner_sub_right, ← coord_eq_inner, ← coord_eq_inner,
    hasLpMatrix_thetaPrimeGramOp p p, hasLpMatrix_poissonPrimeOp p p]
  show ((sechSqHalf (cdfAction ((p : ℕ) : ℤ) - cdfAction ((p : ℕ) : ℤ)) /
      (Real.sqrt (p : ℕ) * Real.sqrt (p : ℕ)) : ℝ) : ℂ) - ((stcPrimePoissonKernel p p : ℝ) : ℂ) = 0
  rw [stcPrimePoissonKernel_eq_sechSqHalf, sub_self, sub_self, sub_eq_zero]

/-- **`Tr(K_Φ − K) = 0`**: both prime matrices have diagonal `h(0)/p`. -/
theorem opTrace_thetaPrimeGramOp_sub :
    ContinuousLinearMap.opTrace (thetaPrimeGramOp - poissonPrimeOp) = 0 := by
  obtain ⟨S, V, hS, hV, hfac⟩ := exists_hs_factorization_thetaPrimeGramOp_sub
  rw [hfac, ContinuousLinearMap.opTrace_comp_eq_tsum_basis hS hV primeHilbertBasis, ← hfac]
  refine (tsum_congr fun p => ?_).trans tsum_zero
  rw [primeHilbertBasis_apply]
  exact inner_lpBasisVec_thetaPrimeGramOp_sub_self p

/-- **`σ_ess(K_Φ) = [0, 4]`.** -/
theorem weylEssentialSpectrum_thetaPrimeGramOp :
    weylEssentialSpectrum thetaPrimeGramOp = weylIntervalZeroFour := by
  rw [weylEssentialSpectrum_eq_of_isCompactOperator
    (memSchattenClass_one_thetaPrimeGramOp_sub.isCompactOperator one_pos),
    weylEssentialSpectrum_poissonPrimeOp]

end

end RHTower

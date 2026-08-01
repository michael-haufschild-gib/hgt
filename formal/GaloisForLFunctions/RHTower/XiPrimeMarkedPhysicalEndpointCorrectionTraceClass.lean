import GaloisForLFunctions.RHTower.XiPhysicalEndpointValuationCorrectionOddShuttle
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten

/-!
# Trace-class physical-endpoint correction on the marked prime Hilbert space

The valuation-resolved correction from unit--double refinement to the physical ordinary-prime
endpoint is absolutely summable before any height is chosen.  Dressing each correction frequency
by the square-summable physical prime endpoint vector therefore gives an absolutely nuclear series
of rank-one operators on `ℓ²(Nat.Primes)`.

This constructs an actual source-defined, phase-preserving Schatten-1 correction for Route K.
It does not make the non-absolutely-summable completed seam kernel trace class and does not assert
the global centered-Xi determinant identity.
-/

open scoped BigOperators InnerProductSpace

namespace RHTower

noncomputable section

/-- Marked ordinary-prime Hilbert space used by the Route K correction. -/
abbrev RouteKPrimeHilbert := lp (fun _ : Nat.Primes => ℂ) 2

private theorem summable_routeKPhysicalEndpointWeight_sq :
    Summable (fun p : Nat.Primes => physicalPrimeEndpointWeight p ^ 2) := by
  have hnat := summable_abs_log_natCast_pow_mul_rpow_neg 2 2 (by norm_num)
  have hnat' : Summable (fun n : ℕ => (Real.log n / (n : ℝ)) ^ 2) := by
    apply hnat.congr
    intro n
    rcases n with _ | n
    · simp
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hlog : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by norm_num)
    rw [abs_of_nonneg hlog, Real.rpow_neg hn.le]
    rw [show ((n + 1 : ℕ) : ℝ) ^ (2 : ℝ) =
        ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) by
      exact Real.rpow_natCast _ 2]
    field_simp
  have hprime : Summable (fun p : Nat.Primes =>
      (Real.log (p : ℝ) / (p : ℝ)) ^ 2) :=
    hnat'.comp_injective Subtype.val_injective
  exact hprime.congr fun p => by
    rw [physicalPrimeEndpointWeight]

/-- Prime-power frequency retained by one valuation-correction atom. -/
def routeKPhysicalEndpointCorrectionFrequency
    (pe : Nat.Primes × ℕ) : ℝ :=
  ((pe.2 + 1 : ℕ) : ℝ) * Real.log (pe.1 : ℝ)

/-- Physical prime endpoint vector with one source prime-power phase. -/
def routeKPhysicalEndpointCorrectionPhaseVector
    (pe : Nat.Primes × ℕ) : RouteKPrimeHilbert :=
  ⟨fun p => (physicalPrimeEndpointWeight p : ℂ) *
      Complex.exp
        (((-routeKPhysicalEndpointCorrectionFrequency pe *
          Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I),
    HilbertSchmidt.memℓp_of_sq
      (summable_routeKPhysicalEndpointWeight_sq.congr fun p => by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, sq_abs])⟩

@[simp] theorem routeKPhysicalEndpointCorrectionPhaseVector_apply
    (pe : Nat.Primes × ℕ) (p : Nat.Primes) :
    routeKPhysicalEndpointCorrectionPhaseVector pe p =
      (physicalPrimeEndpointWeight p : ℂ) *
        Complex.exp
          (((-routeKPhysicalEndpointCorrectionFrequency pe *
            Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I) := rfl

/-- Every phase vector has the same finite physical endpoint energy. -/
theorem norm_sq_routeKPhysicalEndpointCorrectionPhaseVector
    (pe : Nat.Primes × ℕ) :
    ‖routeKPhysicalEndpointCorrectionPhaseVector pe‖ ^ 2 =
      ∑' p : Nat.Primes, physicalPrimeEndpointWeight p ^ 2 := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  apply tsum_congr
  intro p
  rw [routeKPhysicalEndpointCorrectionPhaseVector_apply, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- Clocked real coefficient of one valuation-resolved endpoint correction atom. -/
def routeKPhysicalEndpointCorrectionCoefficient
    (pe : Nat.Primes × ℕ) : ℝ :=
  Real.log (pe.1 : ℝ) *
    xiPhysicalEndpointValuationCorrection pe.1 pe.2

theorem summable_abs_routeKPhysicalEndpointCorrectionCoefficient :
    Summable (fun pe : Nat.Primes × ℕ =>
      |routeKPhysicalEndpointCorrectionCoefficient pe|) := by
  simpa [routeKPhysicalEndpointCorrectionCoefficient] using
    summable_abs_clocked_xiPhysicalEndpointValuationCorrection

/-- One source-frequency rank-one correction on marked prime space. -/
def routeKPhysicalEndpointCorrectionRankOne
    (pe : Nat.Primes × ℕ) : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  (routeKPhysicalEndpointCorrectionCoefficient pe : ℂ) •
    InnerProductSpace.rankOne ℂ
      (routeKPhysicalEndpointCorrectionPhaseVector pe)
      (routeKPhysicalEndpointCorrectionPhaseVector pe)

theorem routeKPhysicalEndpointCorrectionRankOne_hasRankLE
    (pe : Nat.Primes × ℕ) :
    HasRankLE (routeKPhysicalEndpointCorrectionRankOne pe) 1 := by
  apply hasRankLE_smul
  simpa using hasRankLE_sum_range_rankOne
    (fun _ : ℕ => routeKPhysicalEndpointCorrectionPhaseVector pe)
    (fun _ : ℕ => routeKPhysicalEndpointCorrectionPhaseVector pe) 1

/-- Each valuation-correction atom is self-adjoint because its coefficient is real and its two
rank-one vectors agree. -/
theorem routeKPhysicalEndpointCorrectionRankOne_isSelfAdjoint
    (pe : Nat.Primes × ℕ) :
    IsSelfAdjoint (routeKPhysicalEndpointCorrectionRankOne pe) := by
  rw [routeKPhysicalEndpointCorrectionRankOne]
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  change star ((routeKPhysicalEndpointCorrectionCoefficient pe : ℂ) •
    InnerProductSpace.rankOne ℂ
      (routeKPhysicalEndpointCorrectionPhaseVector pe)
      (routeKPhysicalEndpointCorrectionPhaseVector pe)) = _
  rw [star_smul]
  change star (routeKPhysicalEndpointCorrectionCoefficient pe : ℂ) •
      ContinuousLinearMap.adjoint
        (InnerProductSpace.rankOne ℂ
          (routeKPhysicalEndpointCorrectionPhaseVector pe)
          (routeKPhysicalEndpointCorrectionPhaseVector pe)) = _
  rw [InnerProductSpace.adjoint_rankOne]
  simp

/-- Exact nuclear norm budget of one source-frequency term. -/
theorem norm_routeKPhysicalEndpointCorrectionRankOne
    (pe : Nat.Primes × ℕ) :
    ‖routeKPhysicalEndpointCorrectionRankOne pe‖ =
      |routeKPhysicalEndpointCorrectionCoefficient pe| *
        (∑' p : Nat.Primes, physicalPrimeEndpointWeight p ^ 2) := by
  rw [routeKPhysicalEndpointCorrectionRankOne, norm_smul,
    InnerProductSpace.norm_rankOne, Complex.norm_real, Real.norm_eq_abs,
    ← pow_two,
    norm_sq_routeKPhysicalEndpointCorrectionPhaseVector]

theorem summable_norm_routeKPhysicalEndpointCorrectionRankOne :
    Summable (fun pe : Nat.Primes × ℕ =>
      ‖routeKPhysicalEndpointCorrectionRankOne pe‖) := by
  rw [show (fun pe : Nat.Primes × ℕ =>
      ‖routeKPhysicalEndpointCorrectionRankOne pe‖) =
      fun pe => |routeKPhysicalEndpointCorrectionCoefficient pe| *
        (∑' p : Nat.Primes, physicalPrimeEndpointWeight p ^ 2) by
    funext pe
    exact norm_routeKPhysicalEndpointCorrectionRankOne pe]
  exact summable_abs_routeKPhysicalEndpointCorrectionCoefficient.mul_right _

/-- Absolutely convergent source-built endpoint correction operator. -/
def routeKPhysicalEndpointCorrectionOperator :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  ∑' pe : Nat.Primes × ℕ, routeKPhysicalEndpointCorrectionRankOne pe

/-- **Actual Route K trace-class survivor.** The valuation correction is Schatten-1 on the marked
ordinary-prime Hilbert space, with all prime-power phases retained. -/
theorem routeKPhysicalEndpointCorrectionOperator_memSchattenClass_one :
    MemSchattenClass 1 routeKPhysicalEndpointCorrectionOperator := by
  exact memSchattenClass_one_tsum_rankOneTerms_of_summable_norm
    routeKPhysicalEndpointCorrectionRankOne
    routeKPhysicalEndpointCorrectionRankOne_hasRankLE
    summable_norm_routeKPhysicalEndpointCorrectionRankOne

/-- The full absolutely nuclear correction remains self-adjoint after summing all source
frequencies. -/
theorem routeKPhysicalEndpointCorrectionOperator_isSelfAdjoint :
    IsSelfAdjoint routeKPhysicalEndpointCorrectionOperator := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  change star (∑' pe : Nat.Primes × ℕ,
    routeKPhysicalEndpointCorrectionRankOne pe) = _
  rw [tsum_star]
  apply tsum_congr
  intro pe
  exact routeKPhysicalEndpointCorrectionRankOne_isSelfAdjoint pe

/-! ## Exact marked-prime matrix incidence -/

/-- Canonical marked-prime basis vector. -/
def routeKPrimeBasis (p : Nat.Primes) : RouteKPrimeHilbert :=
  lp.single 2 p (1 : ℂ)

theorem inner_routeKPrimeBasis_phase
    (pe : Nat.Primes × ℕ) (p : Nat.Primes) :
    inner ℂ (routeKPrimeBasis p)
      (routeKPhysicalEndpointCorrectionPhaseVector pe) =
      routeKPhysicalEndpointCorrectionPhaseVector pe p := by
  simp [routeKPrimeBasis, lp.inner_single_left]

theorem inner_phase_routeKPrimeBasis
    (pe : Nat.Primes × ℕ) (q : Nat.Primes) :
    inner ℂ (routeKPhysicalEndpointCorrectionPhaseVector pe)
      (routeKPrimeBasis q) =
      star (routeKPhysicalEndpointCorrectionPhaseVector pe q) := by
  simp [routeKPrimeBasis, lp.inner_single_right]

private theorem star_exp_ofReal_mul_I (a : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((a : ℂ) * Complex.I)) =
      Complex.exp ((-a : ℝ) * Complex.I) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

private theorem star_weight_mul_exp_ofReal_mul_I (w a : ℝ) :
    star ((w : ℂ) * Complex.exp ((a : ℂ) * Complex.I)) =
      (w : ℂ) * Complex.exp ((-a : ℝ) * Complex.I) := by
  change (starRingEnd ℂ) ((w : ℂ) * Complex.exp ((a : ℂ) * Complex.I)) = _
  rw [map_mul, Complex.conj_ofReal, star_exp_ofReal_mul_I]

/-- Exact matrix entry of one correction frequency. -/
theorem routeKPhysicalEndpointCorrectionRankOne_matrix
    (pe : Nat.Primes × ℕ) (p q : Nat.Primes) :
    inner ℂ (routeKPrimeBasis p)
        (routeKPhysicalEndpointCorrectionRankOne pe (routeKPrimeBasis q)) =
      (routeKPhysicalEndpointCorrectionCoefficient pe : ℂ) *
        (physicalPrimeEndpointWeight p : ℂ) *
          (physicalPrimeEndpointWeight q : ℂ) *
            Complex.exp
              (((-routeKPhysicalEndpointCorrectionFrequency pe *
                (Real.log (p : ℝ) - Real.log (q : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  rw [routeKPhysicalEndpointCorrectionRankOne,
    smul_apply, InnerProductSpace.rankOne_apply]
  rw [inner_smul_right (routeKPrimeBasis p)
    ((inner ℂ (routeKPhysicalEndpointCorrectionPhaseVector pe)
      (routeKPrimeBasis q)) •
        routeKPhysicalEndpointCorrectionPhaseVector pe)
    (routeKPhysicalEndpointCorrectionCoefficient pe : ℂ)]
  rw [inner_smul_right (routeKPrimeBasis p)
    (routeKPhysicalEndpointCorrectionPhaseVector pe)
    (inner ℂ (routeKPhysicalEndpointCorrectionPhaseVector pe)
      (routeKPrimeBasis q))]
  rw [inner_routeKPrimeBasis_phase,
    inner_phase_routeKPrimeBasis,
    routeKPhysicalEndpointCorrectionPhaseVector_apply,
    routeKPhysicalEndpointCorrectionPhaseVector_apply]
  rw [star_weight_mul_exp_ofReal_mul_I]
  calc
    _ = (routeKPhysicalEndpointCorrectionCoefficient pe : ℂ) *
          (physicalPrimeEndpointWeight p : ℂ) *
            (physicalPrimeEndpointWeight q : ℂ) *
              (Complex.exp
                  (((routeKPhysicalEndpointCorrectionFrequency pe *
                    Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I) *
                Complex.exp
                  (((-routeKPhysicalEndpointCorrectionFrequency pe *
                    Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I)) := by ring_nf
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- The correction-kernel atom is exactly the frequency used by the rank-one series. -/
theorem routeKPhysicalEndpointCorrectionKernelTerm_eq
    (pe : Nat.Primes × ℕ) (t : ℝ) :
    xiPhysicalEndpointValuationCorrectionKernelTerm t pe =
      (routeKPhysicalEndpointCorrectionCoefficient pe : ℂ) *
        Complex.exp
          (((-routeKPhysicalEndpointCorrectionFrequency pe * t : ℝ) : ℂ) *
            Complex.I) := by
  rw [xiPhysicalEndpointValuationCorrectionKernelTerm,
    routeKPhysicalEndpointCorrectionCoefficient,
    routeKPhysicalEndpointCorrectionFrequency]
  congr 2 <;> apply Complex.ext <;> norm_num

/-- **Exact source incidence.** Matrix coefficients of the trace-class operator are precisely the
physical pair dressing of the absolutely convergent valuation-correction kernel at logarithmic
prime ratios. -/
theorem routeKPhysicalEndpointCorrectionOperator_matrix
    (p q : Nat.Primes) :
    inner ℂ (routeKPrimeBasis p)
        (routeKPhysicalEndpointCorrectionOperator (routeKPrimeBasis q)) =
      (physicalPrimeEndpointWeight p : ℂ) *
        (physicalPrimeEndpointWeight q : ℂ) *
          xiPhysicalEndpointValuationCorrectionKernel
            (Real.log (p : ℝ) - Real.log (q : ℝ)) := by
  let L : (RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert) →L[ℂ] ℂ :=
    (innerSL ℂ (routeKPrimeBasis p)).comp
      (ContinuousLinearMap.apply ℂ RouteKPrimeHilbert (routeKPrimeBasis q))
  have hsumOp : Summable routeKPhysicalEndpointCorrectionRankOne :=
    Summable.of_norm summable_norm_routeKPhysicalEndpointCorrectionRankOne
  have hmap := L.map_tsum hsumOp
  change inner ℂ (routeKPrimeBasis p)
      ((∑' pe, routeKPhysicalEndpointCorrectionRankOne pe)
        (routeKPrimeBasis q)) = _
  rw [show inner ℂ (routeKPrimeBasis p)
      ((∑' pe, routeKPhysicalEndpointCorrectionRankOne pe)
        (routeKPrimeBasis q)) =
      ∑' pe, inner ℂ (routeKPrimeBasis p)
        (routeKPhysicalEndpointCorrectionRankOne pe (routeKPrimeBasis q)) by
    simpa [L] using hmap]
  rw [xiPhysicalEndpointValuationCorrectionKernel, ← tsum_mul_left]
  apply tsum_congr
  intro pe
  rw [routeKPhysicalEndpointCorrectionRankOne_matrix,
    routeKPhysicalEndpointCorrectionKernelTerm_eq]
  ring

end

end RHTower

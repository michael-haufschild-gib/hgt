import GaloisForLFunctions.HTGeometry.MeromorphicGermTameSymbol
import GaloisForLFunctions.HTGeometry.MilnorKDegTwoSymbol
import GaloisForLFunctions.RHTower.PrimeRotationXiSourceTransport

/-!
# The relative K2 boundary of the actual Xi transport

Pair the meromorphic Xi correction `Xi(s)/Xi(s+t)` with the prime exponential unit in Milnor K2.
The concrete tame boundary retains the signed analytic divisor. At the two points of an isolated
Xi dipole, its product is exactly the prime Weyl phase with the full analytic multiplicity.

This constructs the relative source class and its nontrivial boundary. It does not identify it
with a rotation K0 class, prove trace integrality for such a class, or supply an RH implication.
-/

open Filter Topology GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

private theorem centered_meromorphicAt {f : ℂ → ℂ} (rho : ℂ) (hf : MeromorphicAt f rho) :
    MeromorphicAt (fun z => f (rho + z)) 0 := by
  have hf' : MeromorphicAt f (rho + 0) := by simpa using hf
  exact hf'.comp_analyticAt (analyticAt_const.add analyticAt_id)

private theorem centered_meromorphicOrderAt (f : ℂ → ℂ) (rho : ℂ) :
    meromorphicOrderAt (fun z => f (rho + z)) 0 = meromorphicOrderAt f rho := by
  have hd : deriv (fun z : ℂ => rho + z) 0 = 1 :=
    ((hasDerivAt_id (0 : ℂ)).const_add rho).deriv
  simpa only [Function.comp_def, add_zero] using
    (meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) (g := fun z : ℂ => rho + z) (x := 0)
      (analyticAt_const.add analyticAt_id) (by rw [hd]; exact one_ne_zero))

private theorem primeEulerCentered_analytic (p : Nat.Primes) (rho : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => Complex.exp (-((Real.log p : ℝ) : ℂ) * (rho + z))) 0 := by
  fun_prop

private theorem primeEulerCentered_order (p : Nat.Primes) (rho : ℂ) :
    meromorphicOrderAt
      (fun z : ℂ => Complex.exp (-((Real.log p : ℝ) : ℂ) * (rho + z))) 0 = 0 := by
  have ho : analyticOrderAt
      (fun z : ℂ => Complex.exp (-((Real.log p : ℝ) : ℂ) * (rho + z))) 0 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (Complex.exp_ne_zero _))
  rw [(primeEulerCentered_analytic p rho).meromorphicOrderAt_eq, ho]
  rfl

/-- The native prime unit in the meromorphic germ field, centered at the named point. -/
def primeEulerMeroGermUnit (p : Nat.Primes) (rho : ℂ) : MeroGermˣ :=
  meroGermUnitOf
    (fun z => Complex.exp (-((Real.log p : ℝ) : ℂ) * (rho + z)))
    (primeEulerCentered_analytic p rho).meromorphicAt
    (by rw [primeEulerCentered_order]; exact WithTop.coe_ne_top)

theorem primeEulerMeroGermUnit_hasLimit (p : Nat.Primes) (rho : ℂ) :
    (primeEulerMeroGermUnit p rho : MeroGerm).HasLimit
      (Complex.exp (-((Real.log p : ℝ) : ℂ) * rho)) := by
  apply (MeroGerm.hasLimit_ofMero_iff (primeEulerCentered_analytic p rho).meromorphicAt _).mpr
  simpa only [add_zero] using
    (primeEulerCentered_analytic p rho).continuousAt.continuousWithinAt.tendsto

private theorem xiTranslationGauge_centered_order (t rho : ℂ) :
    meromorphicOrderAt (fun z => xiTranslationGauge t (rho + z)) 0 =
      (((analyticOrderAt xi rho).toNat : ℤ) -
        ((analyticOrderAt xi (rho + t)).toNat : ℤ) : WithTop ℤ) := by
  rw [centered_meromorphicOrderAt, xiTranslationGauge_order]

/-- The actual meromorphic Xi cocycle, as a unit of the germ field at a named point. -/
def xiTranslationGermUnit (t rho : ℂ) : MeroGermˣ :=
  meroGermUnitOf (fun z => xiTranslationGauge t (rho + z))
    (centered_meromorphicAt rho (xiTranslationGauge_meromorphicAt t rho))
    (by rw [xiTranslationGauge_centered_order]; exact WithTop.coe_ne_top)

theorem xiTranslationGermUnit_order (t rho : ℂ) :
    meroGermUnitOrder (xiTranslationGermUnit t rho) =
      ((analyticOrderAt xi rho).toNat : ℤ) -
        ((analyticOrderAt xi (rho + t)).toNat : ℤ) := by
  apply WithTop.coe_injective
  rw [xiTranslationGermUnit, meroGermUnitOf_order, xiTranslationGauge_centered_order]
  push_cast
  rfl

/-- A source-defined relative K2 symbol pairing the prime unit with the Xi transport. -/
def xiPrimeRelativeK2Class (p : Nat.Primes) (t rho : ℂ) : MilnorKDeg MeroGerm 2 :=
  milnorClassDeg MeroGerm 2 ⟨[primeEulerMeroGermUnit p rho, xiTranslationGermUnit t rho], rfl⟩

/-- Exact local boundary: multiplicity enters through the actual meromorphic order. -/
theorem xiPrimeRelativeK2Class_boundary (p : Nat.Primes) (t rho : ℂ) :
    meroGermTameBoundaryValue (xiPrimeRelativeK2Class p t rho) =
      Complex.exp (-((Real.log p : ℝ) : ℂ) * rho) ^
        (((analyticOrderAt xi rho).toNat : ℤ) -
          ((analyticOrderAt xi (rho + t)).toNat : ℤ)) := by
  rw [xiPrimeRelativeK2Class,
    meroGermTameBoundaryValue_symbol_of_limit _ _ (Complex.exp_ne_zero _)
      (primeEulerMeroGermUnit_hasLimit p rho), xiTranslationGermUnit_order]

/-- The two relative source symbols of a transported local Xi divisor. -/
def xiPrimeDipoleK2Class (p : Nat.Primes) (t rho : ℂ) : MilnorKDeg MeroGerm 2 :=
  xiPrimeRelativeK2Class p t rho + xiPrimeRelativeK2Class p t (rho - t)

/-- The dipole boundary retains precisely the original multiplicity-weighted Weyl multiplier. -/
theorem xiPrimeDipoleK2Class_boundary (p : Nat.Primes) (rho : ℂ) :
    ∃ epsilon > 0, ∀ t : ℂ, t ≠ 0 → ‖t‖ < epsilon →
      meroGermTameBoundaryValue (xiPrimeDipoleK2Class p t rho) =
        Complex.exp (-((Real.log p : ℝ) : ℂ) * t) ^ (analyticOrderAt xi rho).toNat := by
  obtain ⟨epsilon, hepsilon, he⟩ := xiTranslationGauge_isolated_dipole rho
  refine ⟨epsilon, hepsilon, fun t ht hnorm => ?_⟩
  obtain ⟨hp, hm, _, _⟩ := he t ht hnorm
  rw [xiPrimeDipoleK2Class, meroGermTameBoundaryValue_add,
    xiPrimeRelativeK2Class_boundary, xiPrimeRelativeK2Class_boundary, sub_add_cancel,
    analyticOrderAt_eq_zero.mpr (Or.inr hp), analyticOrderAt_eq_zero.mpr (Or.inr hm)]
  simp only [ENat.toNat_zero, Nat.cast_zero, sub_zero, zero_sub, zpow_natCast, zpow_neg]
  rw [← div_eq_mul_inv, ← div_pow, ← Complex.exp_sub]
  congr 2
  ring

/-- Arbitrarily small native clocks give an actual relative K2 boundary equal to the prime phase. -/
theorem xiPrimeDipoleK2Class_clock_boundary (p : Nat.Primes) (rho : ℂ) :
    ∃ q : ℕ, 0 < q ∧
      meroGermTameBoundaryValue (xiPrimeDipoleK2Class p (primeAlgebraicClockStep q) rho) =
        primeAlgebraicWeylDeterminantPhase p (analyticOrderAt xi rho).toNat q := by
  obtain ⟨epsilon, hepsilon, he⟩ := xiPrimeDipoleK2Class_boundary p rho
  obtain ⟨q, hq, hnorm⟩ := exists_primeAlgebraicClockStep_norm_lt hepsilon
  have hstep : primeAlgebraicClockStep q ≠ 0 := by
    apply norm_pos_iff.mp
    rw [norm_primeAlgebraicClockStep]
    exact one_div_pos.mpr (by exact_mod_cast hq)
  exact ⟨q, hq, (he _ hstep hnorm).trans (primeAlgebraicWeylMultiplier_pow_eq_phase p _ q)⟩

/-- At every genuine Xi zero the actual small-clock relative class has transcendental boundary
    and is nonzero. No algebraic or trivial boundary descent is assumed. -/
theorem xiPrimeDipoleK2Class_nonzero (p : Nat.Primes) {rho : ℂ} (hrho : xi rho = 0) :
    ∃ q : ℕ, 0 < q ∧
      Transcendental ℚ
        (meroGermTameBoundaryValue (xiPrimeDipoleK2Class p (primeAlgebraicClockStep q) rho)) ∧
      xiPrimeDipoleK2Class p (primeAlgebraicClockStep q) rho ≠ 0 := by
  obtain ⟨q, hq, he⟩ := xiPrimeDipoleK2Class_clock_boundary p rho
  have htrans : Transcendental ℚ
      (meroGermTameBoundaryValue (xiPrimeDipoleK2Class p (primeAlgebraicClockStep q) rho)) := by
    rw [he]
    exact primeAlgebraicWeylDeterminantPhase_transcendental p
      (xi_order_toNat_ne_zero hrho) (Nat.ne_of_gt hq)
  refine ⟨q, hq, htrans, ?_⟩
  intro hz
  rw [hz, meroGermTameBoundaryValue_zero] at htrans
  exact htrans (by simpa using isAlgebraic_natComplex 1)

/-! ## Exact source composition and its K2 correction -/

private theorem xiCentered_analytic (rho : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => xi (rho + z)) 0 := by
  have hxi : AnalyticAt ℂ xi (rho + 0) :=
    xi_analyticOnNhd_univ _ (Set.mem_univ _)
  exact hxi.comp (f := fun z : ℂ => rho + z) (analyticAt_const.add analyticAt_id)

private theorem xiCentered_order (rho : ℂ) :
    meromorphicOrderAt (fun z : ℂ => xi (rho + z)) 0 =
      ((analyticOrderAt xi rho).toNat : ℤ) := by
  rw [centered_meromorphicOrderAt,
    (xi_analyticOnNhd_univ rho (Set.mem_univ _)).meromorphicOrderAt_eq,
    ← ENat.coe_toNat (xi_order_ne_top rho)]
  rfl

/-- The literal Xi germ, which is invertible in the meromorphic field even at its divisor. -/
def xiMeroGermUnit (rho : ℂ) : MeroGermˣ :=
  meroGermUnitOf (fun z => xi (rho + z)) (xiCentered_analytic rho).meromorphicAt
    (by rw [xiCentered_order]; exact WithTop.coe_ne_top)

/-- The transport is the exact ratio of the two literal source germs. -/
theorem xiTranslationGermUnit_eq_ratio (t rho : ℂ) :
    xiTranslationGermUnit t rho = xiMeroGermUnit rho * (xiMeroGermUnit (rho + t))⁻¹ := by
  apply Units.ext
  change ofMero (fun z => xiTranslationGauge t (rho + z))
      (centered_meromorphicAt rho (xiTranslationGauge_meromorphicAt t rho)) =
    ofMero (fun z => xi (rho + z)) (xiCentered_analytic rho).meromorphicAt *
      (ofMero (fun z => xi (rho + t + z)) (xiCentered_analytic (rho + t)).meromorphicAt)⁻¹
  rw [ofMero_inv, ofMero_mul, ofMero_eq_iff]
  exact Eventually.of_forall fun z => by
    simp [xiTranslationGauge, div_eq_mul_inv, add_comm, add_left_comm]

/-- The meromorphic source unit satisfies exact composition, with its moving center retained. -/
theorem xiTranslationGermUnit_cocycle (t u rho : ℂ) :
    xiTranslationGermUnit (t + u) rho =
      xiTranslationGermUnit t rho * xiTranslationGermUnit u (rho + t) := by
  rw [xiTranslationGermUnit_eq_ratio, xiTranslationGermUnit_eq_ratio,
    xiTranslationGermUnit_eq_ratio, add_assoc]
  group

/-- The constant prime clock multiplier, embedded as an actual meromorphic unit. -/
def primeClockScalarGermUnit (p : Nat.Primes) (t : ℂ) : MeroGermˣ :=
  milnorUnitMap constGerm
    (Units.mk0 (Complex.exp (-((Real.log p : ℝ) : ℂ) * t)) (Complex.exp_ne_zero _))

theorem primeClockScalarGermUnit_hasLimit (p : Nat.Primes) (t : ℂ) :
    (primeClockScalarGermUnit p t : MeroGerm).HasLimit
      (Complex.exp (-((Real.log p : ℝ) : ℂ) * t)) :=
  MeroGerm.hasLimit_const _

/-- Moving the center multiplies the prime germ by the native Weyl scalar. -/
theorem primeEulerMeroGermUnit_shift (p : Nat.Primes) (t rho : ℂ) :
    primeEulerMeroGermUnit p (rho + t) =
      primeClockScalarGermUnit p t * primeEulerMeroGermUnit p rho := by
  apply Units.ext
  change ofMero (fun z => Complex.exp (-((Real.log p : ℝ) : ℂ) * (rho + t + z)))
      (primeEulerCentered_analytic p (rho + t)).meromorphicAt =
    ofMero (fun _ => Complex.exp (-((Real.log p : ℝ) : ℂ) * t))
      (MeromorphicAt.const _ 0) *
      ofMero (fun z => Complex.exp (-((Real.log p : ℝ) : ℂ) * (rho + z)))
        (primeEulerCentered_analytic p rho).meromorphicAt
  rw [ofMero_mul, ofMero_eq_iff]
  refine Eventually.of_forall fun z => ?_
  change Complex.exp _ = Complex.exp _ * Complex.exp _
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Exact relative K2 composition. The prime clock supplies a nontrivial correction, which
    cannot be discarded when gluing the moving local source classes. -/
theorem xiPrimeRelativeK2Class_cocycle (p : Nat.Primes) (t u rho : ℂ) :
    xiPrimeRelativeK2Class p (t + u) rho +
        milnorSym2 MeroGerm (primeClockScalarGermUnit p t)
          (xiTranslationGermUnit u (rho + t)) =
      xiPrimeRelativeK2Class p t rho + xiPrimeRelativeK2Class p u (rho + t) := by
  change milnorSym2 MeroGerm _ _ + _ = milnorSym2 MeroGerm _ _ + milnorSym2 MeroGerm _ _
  rw [xiTranslationGermUnit_cocycle, milnorSym2_mul_right,
    primeEulerMeroGermUnit_shift, milnorSym2_mul_left]
  abel

/-- The gluing correction itself has an exact multiplicity-weighted boundary. -/
theorem xiPrimeRelativeK2Class_cocycle_correction_boundary
    (p : Nat.Primes) (t u rho : ℂ) :
    meroGermTameBoundaryValue
        (milnorSym2 MeroGerm (primeClockScalarGermUnit p t)
          (xiTranslationGermUnit u (rho + t))) =
      Complex.exp (-((Real.log p : ℝ) : ℂ) * t) ^
        (((analyticOrderAt xi (rho + t)).toNat : ℤ) -
          ((analyticOrderAt xi (rho + t + u)).toNat : ℤ)) := by
  rw [milnorSym2, meroGermTameBoundaryValue_symbol_of_limit _ _ (Complex.exp_ne_zero _)
    (primeClockScalarGermUnit_hasLimit p t), xiTranslationGermUnit_order]

/-! ## Untwisting transfers all dipole charge to the clock correction -/

theorem xiMeroGermUnit_order (rho : ℂ) :
    meroGermUnitOrder (xiMeroGermUnit rho) = ((analyticOrderAt xi rho).toNat : ℤ) := by
  apply WithTop.coe_injective
  rw [xiMeroGermUnit, meroGermUnitOf_order, xiCentered_order]

/-- The literal local Xi/prime K2 potential. -/
def xiPrimeK2Potential (p : Nat.Primes) (rho : ℂ) : MilnorKDeg MeroGerm 2 :=
  milnorSym2 MeroGerm (primeEulerMeroGermUnit p rho) (xiMeroGermUnit rho)

/-- The clock correction associated with the source at its transported center. -/
def xiPrimeK2ClockCorrection (p : Nat.Primes) (t rho : ℂ) : MilnorKDeg MeroGerm 2 :=
  milnorSym2 MeroGerm (primeClockScalarGermUnit p t) (xiMeroGermUnit (rho + t))

/-- Exact decomposition into a strict coboundary and the retained prime clock correction. -/
theorem xiPrimeRelativeK2Class_decomposition (p : Nat.Primes) (t rho : ℂ) :
    xiPrimeRelativeK2Class p t rho =
      xiPrimeK2Potential p rho - xiPrimeK2Potential p (rho + t) +
        xiPrimeK2ClockCorrection p t rho := by
  change milnorSym2 MeroGerm _ _ =
    milnorSym2 MeroGerm _ _ - milnorSym2 MeroGerm _ _ + milnorSym2 MeroGerm _ _
  rw [xiTranslationGermUnit_eq_ratio, milnorSym2_mul_right, milnorSym2_inv_right,
    primeEulerMeroGermUnit_shift, milnorSym2_mul_left]
  abel

/-- Untwisting the source classes removes precisely the clock correction. -/
def xiPrimeK2UntwistedTransport (p : Nat.Primes) (t rho : ℂ) : MilnorKDeg MeroGerm 2 :=
  xiPrimeRelativeK2Class p t rho - xiPrimeK2ClockCorrection p t rho

theorem xiPrimeK2UntwistedTransport_eq (p : Nat.Primes) (t rho : ℂ) :
    xiPrimeK2UntwistedTransport p t rho =
      xiPrimeK2Potential p rho - xiPrimeK2Potential p (rho + t) := by
  rw [xiPrimeK2UntwistedTransport, xiPrimeRelativeK2Class_decomposition, add_sub_cancel_right]

/-- The explicitly untwisted transport obeys the ordinary translation cocycle. -/
theorem xiPrimeK2UntwistedTransport_cocycle (p : Nat.Primes) (t u rho : ℂ) :
    xiPrimeK2UntwistedTransport p (t + u) rho =
      xiPrimeK2UntwistedTransport p t rho + xiPrimeK2UntwistedTransport p u (rho + t) := by
  simp only [xiPrimeK2UntwistedTransport_eq, add_assoc]
  abel

theorem xiPrimeK2Potential_boundary (p : Nat.Primes) (rho : ℂ) :
    meroGermTameBoundaryValue (xiPrimeK2Potential p rho) =
      Complex.exp (-((Real.log p : ℝ) : ℂ) * rho) ^ (analyticOrderAt xi rho).toNat := by
  rw [xiPrimeK2Potential, milnorSym2,
    meroGermTameBoundaryValue_symbol_of_limit _ _ (Complex.exp_ne_zero _)
      (primeEulerMeroGermUnit_hasLimit p rho), xiMeroGermUnit_order, zpow_natCast]

theorem xiPrimeK2ClockCorrection_boundary (p : Nat.Primes) (t rho : ℂ) :
    meroGermTameBoundaryValue (xiPrimeK2ClockCorrection p t rho) =
      Complex.exp (-((Real.log p : ℝ) : ℂ) * t) ^ (analyticOrderAt xi (rho + t)).toNat := by
  rw [xiPrimeK2ClockCorrection, milnorSym2,
    meroGermTameBoundaryValue_symbol_of_limit _ _ (Complex.exp_ne_zero _)
      (primeClockScalarGermUnit_hasLimit p t), xiMeroGermUnit_order, zpow_natCast]

/-- Exact charge transfer: untwisting makes the isolated dipole boundary trivial, while the
    removed clock correction retains the full multiplicity-weighted prime phase. -/
theorem xiPrimeK2_dipole_charge_transfer (p : Nat.Primes) (rho : ℂ) :
    ∃ epsilon > 0, ∀ t : ℂ, t ≠ 0 → ‖t‖ < epsilon →
      meroGermTameBoundaryValue
        (xiPrimeK2UntwistedTransport p t rho +
          xiPrimeK2UntwistedTransport p t (rho - t)) = 1 ∧
      meroGermTameBoundaryValue
        (xiPrimeK2ClockCorrection p t rho +
          xiPrimeK2ClockCorrection p t (rho - t)) =
        Complex.exp (-((Real.log p : ℝ) : ℂ) * t) ^ (analyticOrderAt xi rho).toNat := by
  obtain ⟨epsilon, hepsilon, he⟩ := xiTranslationGauge_isolated_dipole rho
  refine ⟨epsilon, hepsilon, fun t ht hnorm => ?_⟩
  obtain ⟨hp, hm, _, _⟩ := he t ht hnorm
  constructor
  · rw [xiPrimeK2UntwistedTransport_eq, xiPrimeK2UntwistedTransport_eq, sub_add_cancel]
    have htel : xiPrimeK2Potential p rho - xiPrimeK2Potential p (rho + t) +
        (xiPrimeK2Potential p (rho - t) - xiPrimeK2Potential p rho) =
        xiPrimeK2Potential p (rho - t) - xiPrimeK2Potential p (rho + t) := by abel
    rw [htel, meroGermTameBoundaryValue_sub, xiPrimeK2Potential_boundary,
      xiPrimeK2Potential_boundary, analyticOrderAt_eq_zero.mpr (Or.inr hp),
      analyticOrderAt_eq_zero.mpr (Or.inr hm)]
    simp
  · rw [meroGermTameBoundaryValue_add, xiPrimeK2ClockCorrection_boundary,
      xiPrimeK2ClockCorrection_boundary, sub_add_cancel,
      analyticOrderAt_eq_zero.mpr (Or.inr hp)]
    simp

end
end RHTower

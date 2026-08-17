import GaloisForLFunctions.HTGeometry.PrimeDirichletAnalyticTransfer
import GaloisForLFunctions.HTGeometry.HelsonPhaseTailIndependence

/-!
# Analytic shift–jet independence for an arbitrary unimodular phase

The signed prime carriers already carry the whole transfer: a prime-supported arithmetic function
with bounded coefficients is summable on `Re s > 1`, its shifted rotated jets are the prime columns
of the shift–jet palette, tail independence of those columns is algebraic independence of the
arithmetic functions, and the upper-end germ realization is a faithful algebra map.

Every step of that chain uses only the boundedness of the coefficients, so it applies verbatim to a
carrier whose prime coefficients are an arbitrary unimodular phase.  The tail independence of the
palette is the one place where the signed case used the finiteness of the coefficient range, and for
a phase that never vanishes it is supplied instead by the common-weight argument.

The conclusion is the analytic form of the independence theorem for a Helson phase: for one source
and any finite palette of shifts with distinct real parts, the shifted derivatives are algebraically
independent — as germs, and over the finite-prime rational coefficient field.
-/

open ArithmeticFunction

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Reindexing a coefficient family along an equivalence preserves tail independence. -/
theorem tailCoefficientIndependent_comp_equiv {I I' P : Type*} [Fintype I] [Fintype I']
    (e : I' ≃ I) {a : I → P → ℂ} (h : TailCoefficientIndependent a) :
    TailCoefficientIndependent (fun i' => a (e i')) := by
  intro c hc
  have hset : {p : P | ∑ i, c (e.symm i) * a i p ≠ 0}
      = {p : P | ∑ i', c i' * a (e i') p ≠ 0} := by
    ext p
    have : ∑ i, c (e.symm i) * a i p = ∑ i', c i' * a (e i') p := by
      refine (Fintype.sum_equiv e _ _ ?_).symm
      intro i'
      simp
    simp [this]
  have h0 : (fun i => c (e.symm i)) = 0 := h _ (by rw [hset]; exact hc)
  funext i'
  have hi := congrFun h0 (e i')
  simpa using hi

/-- The prime carrier of a phase. -/
def phasePrimeArithmeticFunction (w : Nat.Primes → ℂ) : ArithmeticFunction ℂ :=
  arithmeticOfPrimeColumn w

/-- A unimodular phase gives a coefficientwise bounded carrier. -/
theorem norm_phasePrimeArithmeticFunction_le_one {w : Nat.Primes → ℂ}
    (hw : ∀ p, ‖w p‖ ≤ 1) (n : ℕ) : ‖phasePrimeArithmeticFunction w n‖ ≤ 1 := by
  by_cases hn : n.Prime
  · rw [show phasePrimeArithmeticFunction w n = w ⟨n, hn⟩ from
      arithmeticOfPrimeColumn_apply_prime w ⟨n, hn⟩]
    exact hw _
  · rw [show phasePrimeArithmeticFunction w n = 0 by
      simp [phasePrimeArithmeticFunction, arithmeticOfPrimeColumn, hn]]
    simp

/-- A phase carrier inside the translation-stable finite-abscissa algebra. -/
def phasePrimeFiniteAbscissa (w : Nat.Primes → ℂ) (hw : ∀ p, ‖w p‖ ≤ 1) :
    finiteAbscissaArithmeticSubalgebra := by
  refine ⟨phasePrimeArithmeticFunction w, 1, ?_⟩
  intro y hy
  refine LSeriesSummable_of_bounded_of_one_lt_re
    (m := 1) (fun n _ => norm_phasePrimeArithmeticFunction_le_one hw n) ?_
  simpa using hy

@[simp]
theorem phasePrimeFiniteAbscissa_coe (w : Nat.Primes → ℂ) (hw : ∀ p, ‖w p‖ ≤ 1) :
    (phasePrimeFiniteAbscissa w hw).1 = phasePrimeArithmeticFunction w := rfl

/-- The shifted order-`k` analytic derivative carrier of a phase. -/
def phasePrimeShiftedRotatedJet (w : Nat.Primes → ℂ) (hw : ∀ p, ‖w p‖ ≤ 1) (a : ℂ) (k : ℕ) :
    finiteAbscissaArithmeticSubalgebra :=
  finiteAbscissaDirichletShift a
    ((finiteAbscissaRotatedDeriv^[k]) (phasePrimeFiniteAbscissa w hw))

theorem phasePrimeShiftedRotatedJet_apply (w : Nat.Primes → ℂ) (hw : ∀ p, ‖w p‖ ≤ 1)
    (a : ℂ) (k n : ℕ) :
    (phasePrimeShiftedRotatedJet w hw a k).1 n =
      cpowWeight a n * (Complex.I * (Real.log n : ℂ)) ^ k * phasePrimeArithmeticFunction w n := by
  rw [phasePrimeShiftedRotatedJet, finiteAbscissaDirichletShift_apply,
    finiteAbscissaRotatedDeriv_iterate_apply]
  change cpowWeight a n *
      ((Complex.I * (Real.log n : ℂ)) ^ k * phasePrimeArithmeticFunction w n) = _
  ring

/-- A shifted rotated jet of a phase is the corresponding prime column of the shift–jet palette. -/
theorem phasePrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn
    (w : Nat.Primes → ℂ) (hw : ∀ p, ‖w p‖ ≤ 1) (a : ℂ) (k : ℕ) :
    (phasePrimeShiftedRotatedJet w hw a k).1 =
      arithmeticOfPrimeColumn
        (fun p => w p * primeShiftFactor a p * rotatedPrimeLogClock p ^ k) := by
  ext n
  by_cases hn : n.Prime
  · rw [phasePrimeShiftedRotatedJet_apply,
      show phasePrimeArithmeticFunction w n = w ⟨n, hn⟩ from
        arithmeticOfPrimeColumn_apply_prime w ⟨n, hn⟩,
      show arithmeticOfPrimeColumn
          (fun p => w p * primeShiftFactor a p * rotatedPrimeLogClock p ^ k) n =
          w ⟨n, hn⟩ * primeShiftFactor a ⟨n, hn⟩ * rotatedPrimeLogClock ⟨n, hn⟩ ^ k from
        arithmeticOfPrimeColumn_apply_prime
          (fun p => w p * primeShiftFactor a p * rotatedPrimeLogClock p ^ k) ⟨n, hn⟩]
    rw [show cpowWeight a n = primeShiftFactor a ⟨n, hn⟩ from
      cpowWeight_prime_eq_primeShiftFactor a ⟨n, hn⟩]
    simp only [rotatedPrimeLogClock, primeLogClock]
    ring
  · rw [phasePrimeShiftedRotatedJet_apply]
    simp [phasePrimeArithmeticFunction, arithmeticOfPrimeColumn, hn]

/-- **The shift–jet palette of a nowhere-vanishing phase has full coefficient-tail rank.** -/
theorem phasePrimeShiftedRotatedJet_tailIndependent {A : Type*} [Fintype A] [DecidableEq A]
    (w : Nat.Primes → ℂ) (hw0 : ∀ p, w p ≠ 0) (alpha : A → ℂ)
    (hdistinct : Function.Injective fun a => (alpha a).re) (m : ℕ) :
    TailCoefficientIndependent
      (fun ak : A × Fin (m + 1) => fun p =>
        w p * primeShiftFactor (alpha ak.1) p * rotatedPrimeLogClock p ^ (ak.2 : ℕ)) := by
  classical
  have hbase := tailCoefficientIndependent_phaseShiftJet (J := Unit) w hw0 alpha hdistinct m
  have hre := tailCoefficientIndependent_comp_equiv
    (e := (Equiv.punitProd (A × Fin (m + 1))).symm) hbase
  have hu : ∀ ak : A × Fin (m + 1), (Complex.I ^ (ak.2 : ℕ)) ≠ 0 :=
    fun ak => pow_ne_zero _ Complex.I_ne_zero
  have hscaled := tailCoefficientIndependent_scale_columns _ (fun ak => Complex.I ^ (ak.2 : ℕ))
    hu hre
  convert hscaled using 1
  funext ak p
  simp only [coefficientShiftJet, rotatedPrimeLogClock, mul_pow, Equiv.punitProd_symm_apply]
  ring

/-- Every finite shifted derivative rectangle of a phase carrier is algebraically independent. -/
theorem phasePrimeShiftedRotatedJets_algebraicIndependent {A : Type*} [Fintype A] [DecidableEq A]
    (w : Nat.Primes → ℂ) (hw0 : ∀ p, w p ≠ 0) (hw : ∀ p, ‖w p‖ ≤ 1) (alpha : A → ℂ)
    (hdistinct : Function.Injective fun a => (alpha a).re) (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun ak : A × Fin (m + 1) => phasePrimeShiftedRotatedJet w hw (alpha ak.1) ak.2) := by
  classical
  have hcoeff := phasePrimeShiftedRotatedJet_tailIndependent w hw0 alpha hdistinct m
  have hraw := algebraicIndependent_arithmeticColumns_of_tailIndependent _ hcoeff
  let incl : finiteAbscissaArithmeticSubalgebra →ₐ[ℂ] ArithmeticFunction ℂ :=
    finiteAbscissaArithmeticSubalgebra.val
  have hincl : Function.Injective incl := fun x y hxy => Subtype.ext hxy
  apply (AlgHom.algebraicIndependent_iff incl hincl).mp
  convert hraw using 1
  funext ak
  exact phasePrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn w hw (alpha ak.1) ak.2

/-- **Analytic form.**  The shifted derivative rectangle of a Helson phase is algebraically
independent as a family of actual analytic upper-end germs. -/
theorem phasePrimeShiftedUpperEndGerm_jets_algebraicIndependent {A : Type*} [Fintype A]
    [DecidableEq A] (w : Nat.Primes → ℂ) (hw0 : ∀ p, w p ≠ 0) (hw : ∀ p, ‖w p‖ ≤ 1)
    (alpha : A → ℂ) (hdistinct : Function.Injective fun a => (alpha a).re) (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun ak : A × Fin (m + 1) =>
        finiteAbscissaLSeriesToUpperEndGerm
          (phasePrimeShiftedRotatedJet w hw (alpha ak.1) ak.2)) :=
  (phasePrimeShiftedRotatedJets_algebraicIndependent w hw0 hw alpha hdistinct m).map'
    finiteAbscissaLSeriesToUpperEndGerm_injective

/-- The same rectangle stays independent over the intrinsic finite-prime coefficient field. -/
theorem phasePrimeShiftedRotatedJets_algebraicIndependent_over_finitePrimeCoefficientField
    {A : Type*} [Fintype A] [DecidableEq A]
    (w : Nat.Primes → ℂ) (hw0 : ∀ p, w p ≠ 0) (hw : ∀ p, ‖w p‖ ≤ 1) (alpha : A → ℂ)
    (hdistinct : Function.Injective fun a => (alpha a).re) (m : ℕ) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun ak : A × Fin (m + 1) =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (phasePrimeShiftedRotatedJet w hw (alpha ak.1) ak.2).1) := by
  classical
  have hcoeff := phasePrimeShiftedRotatedJet_tailIndependent w hw0 alpha hdistinct m
  have hraw :=
    algebraicIndependent_fractionPrimeColumns_over_finitePrimeCoefficientField _ hcoeff
  convert hraw using 1
  funext ak
  congr 1
  exact phasePrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn w hw (alpha ak.1) ak.2

/-- **Pong's conclusion for a Helson phase, over the card's `E_fin(s)`.**  Every finite shifted
derivative rectangle of the prime carrier of a unimodular phase is algebraically independent over
the finite-prime rational coefficient field. -/
theorem phasePrimeShiftedRotatedJets_algebraicIndependent_over_finitePrimeRationalCoefficientField
    {A : Type*} [Fintype A] [DecidableEq A]
    (w : Nat.Primes → ℂ) (hw0 : ∀ p, w p ≠ 0) (hw : ∀ p, ‖w p‖ ≤ 1) (alpha : A → ℂ)
    (hdistinct : Function.Injective fun a => (alpha a).re) (m : ℕ) :
    AlgebraicIndependent finitePrimeRationalCoefficientField
      (fun ak : A × Fin (m + 1) =>
        algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
          (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (phasePrimeShiftedRotatedJet w hw (alpha ak.1) ak.2).1)) :=
  algebraicIndependent_constants_over_finitePrimeRationalCoefficientField _
    (phasePrimeShiftedRotatedJets_algebraicIndependent_over_finitePrimeCoefficientField
      w hw0 hw alpha hdistinct m)

end GaloisForLFunctions.HTGeometry

end

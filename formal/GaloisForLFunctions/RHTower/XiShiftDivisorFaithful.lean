import GaloisForLFunctions.RHTower.XiShiftDivisorPrimeSymbol
import GaloisForLFunctions.RHTower.RayCompleteTranslationFaithful

/-!
# The completed-Xi prime source has trivial shift-divisor annihilator

The Dirichlet symbol of a finite shift divisor evaluated at `n` is exactly the translation character
of the divisor at the frequency `log n`.  Ray-complete translation faithfulness on the prime-log
rays therefore says that a divisor whose symbol vanishes at every prime power is zero.

Combined with Dirichlet-series injectivity this gives the value-relation statement: on the Euler
half-plane the corrected completed logarithmic derivative `logDeriv xi - logDeriv archFactor`
satisfies no nontrivial linear relation with constant complex coefficients among its translates by
shifts of nonnegative real part.  The annihilator submodule of the corrected completed-Xi value is
trivial, so distinct shift divisors give distinct values.
-/

namespace RHTower

open Complex Filter

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Dirichlet symbol of a shift divisor at `n` is its translation character at the frequency
`log n`. -/
theorem shiftDivisorSymbol_eq_translationChar (w : ℂ →₀ ℂ) {n : ℕ} (hn : n ≠ 0) :
    shiftDivisorSymbol w n =
      GaloisForLFunctions.RHTower.translationChar (Real.log n)
        (AddMonoidAlgebra.ofCoeff w) := by
  have hn' : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hlog : Complex.log ((n : ℕ) : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [GaloisForLFunctions.RHTower.translationChar_apply, shiftDivisorSymbol, Finsupp.sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.cpow_def_of_ne_zero hn', hlog,
    show ((Real.log n : ℝ) : ℂ) * (-a) = -((Real.log n : ℝ) : ℂ) * a by ring]

/-- **Divisor faithfulness.** A finite shift divisor whose Dirichlet symbol vanishes at every prime
power is the zero divisor. -/
theorem shiftDivisor_eq_zero_of_symbol_prime_pow {w : ℂ →₀ ℂ}
    (h : ∀ p : ℕ, p.Prime → ∀ m : ℕ, 1 ≤ m → shiftDivisorSymbol w (p ^ m) = 0) :
    w = 0 := by
  have hP : (AddMonoidAlgebra.ofCoeff w : AddMonoidAlgebra ℂ ℂ) = 0 := by
    apply GaloisForLFunctions.RHTower.euler_translation_faithful
    intro p hp m hm
    have hpm : (p ^ m : ℕ) ≠ 0 := pow_ne_zero m hp.ne_zero
    have hval := h p hp m hm
    rw [shiftDivisorSymbol_eq_translationChar w hpm] at hval
    rwa [show Real.log ((p ^ m : ℕ) : ℝ) = (m : ℝ) * Real.log p by
      rw [Nat.cast_pow, Real.log_pow]] at hval
  simpa using congrArg AddMonoidAlgebra.coeff hP

/-- **Faithfulness of the divisor twist on the von Mangoldt stream.** -/
theorem shiftDivisorStream_vonMangoldt_eq_zero_iff (w : ℂ →₀ ℂ) :
    (∀ n : ℕ, shiftDivisorStream w
        (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) n = 0) ↔ w = 0 := by
  constructor
  · intro hstream
    apply shiftDivisor_eq_zero_of_symbol_prime_pow
    intro p hp m hm
    have hz := hstream (p ^ m)
    rw [shiftDivisorStream,
      ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp] at hz
    have hlogne : ((Real.log p : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    exact (mul_eq_zero.mp hz).resolve_right hlogne
  · rintro rfl
    intro n
    simp [shiftDivisorStream, shiftDivisorSymbol]

/-- The absolute-convergence abscissa of a nonnegative-shift divisor twist of the von Mangoldt
stream is finite. -/
theorem abscissaOfAbsConv_shiftDivisorStream_vonMangoldt_lt_top {w : ℂ →₀ ℂ}
    (hw : ∀ a ∈ w.support, 0 ≤ a.re) :
    LSeries.abscissaOfAbsConv
        (shiftDivisorStream w fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) < ⊤ := by
  refine lt_of_le_of_lt
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) ?_)
    (EReal.coe_lt_top 1)
  intro y hy
  refine LSeriesSummable_shiftDivisorStream w _ _ fun a ha => ?_
  refine ArithmeticFunction.LSeriesSummable_vonMangoldt ?_
  have := hw a ha
  rw [Complex.add_re, Complex.ofReal_re]
  linarith

/-- **Trivial annihilator of the corrected completed-Xi value.** A shift divisor with shifts of
nonnegative real part annihilates the corrected completed-Xi value on the Euler half-plane exactly
when it is the zero divisor. -/
theorem xiShiftDivisorPrimeValue_eq_zero_iff {w : ℂ →₀ ℂ}
    (hw : ∀ a ∈ w.support, 0 ≤ a.re) :
    (∀ s : ℂ, 1 < s.re → xiShiftDivisorPrimeValue w s = 0) ↔ w = 0 := by
  constructor
  · intro hzero
    refine (shiftDivisorStream_vonMangoldt_eq_zero_iff w).mp fun n => ?_
    by_cases hn : n = 0
    · simp [hn, shiftDivisorStream]
    · have hsummable0 : ∀ y : ℝ, LSeriesSummable (0 : ℕ → ℂ) ((y : ℝ) : ℂ) := by
        intro y
        have hterm : LSeries.term (0 : ℕ → ℂ) ((y : ℝ) : ℂ) = fun _ => 0 := by
          funext k
          simp [LSeries.term]
        unfold LSeriesSummable
        rw [hterm]
        exact summable_zero
      have habs0 : LSeries.abscissaOfAbsConv (0 : ℕ → ℂ) < ⊤ :=
        lt_of_le_of_lt
          (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
            fun y _ => hsummable0 y)
          (EReal.coe_lt_top 1)
      have hLzero : ∀ y : ℝ, LSeries (0 : ℕ → ℂ) ((y : ℝ) : ℂ) = 0 :=
        fun y => congrFun LSeries_zero ((y : ℝ) : ℂ)
      have heq : (fun x : ℝ => LSeries
            (shiftDivisorStream w fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (x : ℂ))
          =ᶠ[atTop] fun x : ℝ => LSeries (0 : ℕ → ℂ) (x : ℂ) := by
        filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
        have hxre : 1 < ((x : ℝ) : ℂ).re := by simpa using hx
        have hval := hzero ((x : ℝ) : ℂ) hxre
        rw [xiShiftDivisorPrimeValue_eq_lSeries w hw hxre] at hval
        rw [hLzero x]
        linear_combination -hval
      simpa using LSeries.eq_of_LSeries_eventually_eq
        (abscissaOfAbsConv_shiftDivisorStream_vonMangoldt_lt_top hw) habs0 heq hn
  · rintro rfl
    intro s _
    simp [xiShiftDivisorPrimeValue, xiShiftDivisorLogDeriv, xiShiftDivisorArchimedeanCorrection]

/-- **No constant-coefficient difference relation for the completed prime source.** If a finite
family of complex shifts with nonnegative real part and complex coefficients annihilates
`logDeriv xi - logDeriv archFactor` throughout the Euler half-plane, every coefficient vanishes. -/
theorem shiftDivisor_eq_zero_of_completedPrimeSource_relation {w : ℂ →₀ ℂ}
    (hw : ∀ a ∈ w.support, 0 ≤ a.re)
    (hrel : ∀ s : ℂ, 1 < s.re →
      (w.sum fun a m => m * (logDeriv xi (s + a) - logDeriv archFactor (s + a))) = 0) :
    w = 0 := by
  refine (xiShiftDivisorPrimeValue_eq_zero_iff hw).mp fun s hs => ?_
  rw [xiShiftDivisorPrimeValue, xiShiftDivisorLogDeriv, xiShiftDivisorArchimedeanCorrection,
    ← shiftDivisorValue_fun_sub]
  exact hrel s hs

/-! ## Independence of complex translates -/

/-- Divisor of a finite weighted family of complex shifts. -/
def familyShiftDivisor {d : ℕ} (a c : Fin d → ℂ) : ℂ →₀ ℂ :=
  ∑ i, Finsupp.single (a i) (c i)

theorem familyShiftDivisor_apply_of_injective {d : ℕ} {a c : Fin d → ℂ}
    (hinj : Function.Injective a) (j : Fin d) :
    familyShiftDivisor a c (a j) = c j := by
  classical
  rw [familyShiftDivisor, Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have : a i ≠ a j := fun h => hij (hinj h)
    simp [this]
  · simp

theorem familyShiftDivisor_support_subset {d : ℕ} {a c : Fin d → ℂ} :
    (familyShiftDivisor a c).support ⊆ Finset.univ.image a := by
  classical
  refine (Finsupp.support_finsetSum).trans ?_
  refine Finset.biUnion_subset.mpr fun i _ => ?_
  refine (Finsupp.support_single_subset).trans ?_
  simp

theorem shiftDivisorValue_familyShiftDivisor {d : ℕ} (a c : Fin d → ℂ) (f : ℂ → ℂ) (s : ℂ) :
    shiftDivisorValue (familyShiftDivisor a c) f s = ∑ i, c i * f (s + a i) := by
  rw [familyShiftDivisor, shiftDivisorValue_finset_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [shiftDivisorValue_single]

/-- **Independence of the completed prime source under complex translation.** Distinct complex
shifts of nonnegative real part give linearly independent corrected completed logarithmic
derivatives on the Euler half-plane. -/
theorem completedPrimeSource_translate_independent {d : ℕ} {a c : Fin d → ℂ}
    (hinj : Function.Injective a) (hre : ∀ i, 0 ≤ (a i).re)
    (hrel : ∀ s : ℂ, 1 < s.re →
      ∑ i, c i * (logDeriv xi (s + a i) - logDeriv archFactor (s + a i)) = 0)
    (j : Fin d) : c j = 0 := by
  classical
  have hsupp : ∀ x ∈ (familyShiftDivisor a c).support, 0 ≤ x.re := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (familyShiftDivisor_support_subset hx)
    exact hre i
  have hzero : familyShiftDivisor a c = 0 := by
    refine shiftDivisor_eq_zero_of_completedPrimeSource_relation hsupp fun s hs => ?_
    have := hrel s hs
    rwa [← shiftDivisorValue_familyShiftDivisor a c
      (fun z => logDeriv xi z - logDeriv archFactor z) s] at this
  have := familyShiftDivisor_apply_of_injective (a := a) (c := c) hinj j
  rw [hzero] at this
  simpa using this.symm

/-- Distinct nonnegative-shift divisors have distinct corrected completed-Xi values. -/
theorem xiShiftDivisorPrimeValue_injective {v w : ℂ →₀ ℂ}
    (hv : ∀ a ∈ (v - w).support, 0 ≤ a.re)
    (h : ∀ s : ℂ, 1 < s.re → xiShiftDivisorPrimeValue v s = xiShiftDivisorPrimeValue w s) :
    v = w := by
  have hzero : v - w = 0 := by
    refine (xiShiftDivisorPrimeValue_eq_zero_iff hv).mp fun s hs => ?_
    rw [xiShiftDivisorPrimeValue, xiShiftDivisorLogDeriv, xiShiftDivisorArchimedeanCorrection,
      shiftDivisorValue_sub, shiftDivisorValue_sub]
    have := h s hs
    rw [xiShiftDivisorPrimeValue, xiShiftDivisorPrimeValue, xiShiftDivisorLogDeriv,
      xiShiftDivisorLogDeriv, xiShiftDivisorArchimedeanCorrection,
      xiShiftDivisorArchimedeanCorrection] at this
    linear_combination this
  exact sub_eq_zero.mp hzero

end

end RHTower

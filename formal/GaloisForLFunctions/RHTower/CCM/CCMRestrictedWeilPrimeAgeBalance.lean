import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleEntrySlopes

/-!
# Entry tangents and the common hyperbolic loss of Weil prime atoms

Both parity corrections are their initial tangent minus one identical positive
post-entry remainder. The remainder sinh(t)-t is evaluated as the hyperbolic
Green response to a linear source. Odd entry gain alone therefore omits a
strictly positive loss at every later radius of a genuine prime power.
-/

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The hyperbolic remainder beyond linear transport from an entry. -/
def ccmWeilPoleAgeKernel (t : ℝ) : ℝ := Real.sinh t-t

/-- Exact nonnegativity of the hyperbolic aging remainder after entry. -/
theorem ccmWeilPoleAgeKernel_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ ccmWeilPoleAgeKernel t := by
  exact sub_nonneg.mpr (Real.self_le_sinh_iff.mpr ht)

/-- The aging remainder is strictly positive exactly at positive elapsed aperture. -/
theorem ccmWeilPoleAgeKernel_pos_iff (t : ℝ) : 0 < ccmWeilPoleAgeKernel t ↔ 0 < t := by
  exact sub_pos.trans Real.self_lt_sinh_iff

/-- The aging kernel is the exact hyperbolic Green response to a linear source. -/
theorem ccmWeilPoleAgeKernel_eq_green_integral (t : ℝ) :
    ccmWeilPoleAgeKernel t = ∫ u in (0:ℝ)..t, Real.sinh (t-u)*u := by
  have hd (u : ℝ) : HasDerivAt (fun v => -v*Real.cosh (t-v)-Real.sinh (t-v))
      (Real.sinh (t-u)*u) u := by
    have h := (hasDerivAt_id u).const_sub t
    convert! (((hasDerivAt_id u).neg.mul h.cosh).sub h.sinh) using 1
    simp only [id_eq,Pi.neg_apply]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hd u) ((Real.continuous_sinh.comp (continuous_const.sub continuous_id)).mul continuous_id |>.intervalIntegrable 0 t)
  simpa [ccmWeilPoleAgeKernel,sub_eq_add_neg,add_comm] using hi.symm

/-- Nonnegative initial slope of a new odd prime-power energy contribution. -/
def ccmWeilOddPrimeEntrySlope (n : ℕ) : ℝ :=
  4*ArithmeticFunction.vonMangoldt n*(1-Real.exp (-(Real.log n/2)))^(2 : ℕ)

/-- Magnitude of the nonpositive initial slope of the new even contribution. -/
def ccmWeilEvenPrimeEntrySlopeMagnitude (n : ℕ) : ℝ :=
  4*ArithmeticFunction.vonMangoldt n*(1+Real.exp (-(Real.log n/2)))^(2 : ℕ)

/-- Common post-entry loss in both parity corrections. -/
def ccmWeilPrimeAgeLoss (n : ℕ) (s : ℝ) : ℝ :=
  8*ArithmeticFunction.vonMangoldt n*Real.exp (-(Real.log n/2))*
    ccmWeilPoleAgeKernel (s-Real.log n/2)

private theorem halfLog_exp (n : ℕ) (hn : 2 ≤ n) :
    Real.exp (2*(Real.log n/2)) = n := by
  rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
  exact Real.exp_log (by exact_mod_cast (by omega : 0 < n))

private theorem halfLog_inv (n : ℕ) (hn : 2 ≤ n) :
    1/(n:ℝ) = Real.exp (-(Real.log n/2))^(2 : ℕ) := by
  conv_lhs => rw [← halfLog_exp n hn]
  rw [one_div,← Real.exp_neg,← Real.exp_nat_mul]
  congr 1
  ring

private theorem diagonal_difference (n : ℕ) (hn : 2 ≤ n) (s : ℝ) :
    Real.exp s/n-Real.exp (-s) =
      2*Real.exp (-(Real.log n/2))*Real.sinh (s-Real.log n/2) := by
  conv_lhs => rw [← halfLog_exp n hn]
  rw [← Real.exp_sub]
  symm
  calc
    _ = Real.exp (-(Real.log n/2))*Real.exp (s-Real.log n/2)-
        Real.exp (-(Real.log n/2))*Real.exp (-(s-Real.log n/2)) := by
      rw [Real.sinh_eq]
      ring
    _ = _ := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1 <;> congr 1 <;> ring

/-- The odd contribution is its positive entry tangent minus the common age loss. -/
theorem ccmWeilOddPrimeAtom_eq_tangent_sub_age (n : ℕ) (hn : 2 ≤ n) (s : ℝ) :
    2*(-ccmWeilPolePrimeDiagonalAtom n s+ccmWeilPolePrimeCrossAtom n s) =
      ccmWeilOddPrimeEntrySlope n*(s-Real.log n/2)-ccmWeilPrimeAgeLoss n s := by
  unfold ccmWeilPolePrimeDiagonalAtom ccmWeilPolePrimeCrossAtom
    ccmWeilOddPrimeEntrySlope ccmWeilPrimeAgeLoss ccmWeilPoleAgeKernel
  rw [diagonal_difference n hn,halfLog_inv n hn]
  ring

/-- The even contribution is its negative entry tangent minus exactly the same age loss. -/
theorem ccmWeilEvenPrimeAtom_eq_tangent_sub_age (n : ℕ) (hn : 2 ≤ n) (s : ℝ) :
    2*(-ccmWeilPolePrimeDiagonalAtom n s-ccmWeilPolePrimeCrossAtom n s) =
      -ccmWeilEvenPrimeEntrySlopeMagnitude n*(s-Real.log n/2)-ccmWeilPrimeAgeLoss n s := by
  unfold ccmWeilPolePrimeDiagonalAtom ccmWeilPolePrimeCrossAtom
    ccmWeilEvenPrimeEntrySlopeMagnitude ccmWeilPrimeAgeLoss ccmWeilPoleAgeKernel
  rw [diagonal_difference n hn,halfLog_inv n hn]
  ring

/-- The odd atom is its entry impulse propagated by sinh, minus its exact Green forcing. -/
theorem ccmWeilOddPrimeAtom_eq_green_balance (n : ℕ) (hn : 2 ≤ n) (s : ℝ) :
    2*(-ccmWeilPolePrimeDiagonalAtom n s+ccmWeilPolePrimeCrossAtom n s) =
      ccmWeilOddPrimeEntrySlope n*Real.sinh (s-Real.log n/2)-
        4*ArithmeticFunction.vonMangoldt n*(1+1/(n:ℝ))*ccmWeilPoleAgeKernel (s-Real.log n/2) := by
  rw [ccmWeilOddPrimeAtom_eq_tangent_sub_age n hn]
  unfold ccmWeilOddPrimeEntrySlope ccmWeilPrimeAgeLoss ccmWeilPoleAgeKernel
  rw [halfLog_inv n hn]
  ring

/-- Both initial tangent magnitudes are nonnegative for every arithmetic index. -/
theorem ccmWeilPrimeEntrySlopes_nonneg (n : ℕ) :
    0 ≤ ccmWeilOddPrimeEntrySlope n ∧ 0 ≤ ccmWeilEvenPrimeEntrySlopeMagnitude n := by
  have hm := ArithmeticFunction.vonMangoldt_nonneg (n:=n)
  constructor <;> dsimp [ccmWeilOddPrimeEntrySlope,ccmWeilEvenPrimeEntrySlopeMagnitude] <;> positivity

/-- The shared loss is nonnegative at every radius after entry. -/
theorem ccmWeilPrimeAgeLoss_nonneg (n : ℕ) {s : ℝ} (hs : Real.log n/2 ≤ s) :
    0 ≤ ccmWeilPrimeAgeLoss n s := by
  have hm := ArithmeticFunction.vonMangoldt_nonneg (n:=n)
  have hk := ccmWeilPoleAgeKernel_nonneg (sub_nonneg.mpr hs)
  unfold ccmWeilPrimeAgeLoss
  positivity

/-- Every genuine prime power has a strictly positive shared loss at every later radius. -/
theorem ccmWeilPrimeAgeLoss_pos {n : ℕ} (hn : IsPrimePow n) {s : ℝ}
    (hs : Real.log n/2 < s) : 0 < ccmWeilPrimeAgeLoss n s := by
  have hm := ArithmeticFunction.vonMangoldt_pos_iff.mpr hn
  have hk := (ccmWeilPoleAgeKernel_pos_iff _).mpr (sub_pos.mpr hs)
  unfold ccmWeilPrimeAgeLoss
  positivity

end RHTower

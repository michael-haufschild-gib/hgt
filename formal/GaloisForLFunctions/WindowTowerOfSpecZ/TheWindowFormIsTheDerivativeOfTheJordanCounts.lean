import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowDirichletAlgebra
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheJordanLimitCountsProjectiveSpace

/-!
# Weil's window form is the derivative of the Jordan counts

Jordan's totient `J_k(m) = Σ_{d ∣ m} μ(m/d) d^k` (ADT `jordanTotient`) counts the primitive vectors
of `(ℤ/m)^k`; equivalently `J_k(m) = φ(m)·#ℙ^{k−1}(ℤ/m)` (AHD). These are the Tate pieces of the
degeneration of the complete Weil family: point counts of punctured affine space over residue rings.

As arithmetic functions, `J_k = ζ_{(−k)} * μ` where `ζ_{(−k)}(n) = n^k` is the Tate twist of the zeta
function (`jordanFun_eq`), so on a window `ρ_A(J_k) = ρ_A(ζ_{(−k)}) ρ_A(μ)` is the window ratio
"`ζ(s − k)/ζ(s)`": the Tate-twisted window zeta operator divided by the window zeta operator.

* **Dimension zero** (`jordanFun_zero`): `J_0 = 1`, so `ρ_A(J_0)` is the identity.
* **The derivative at dimension zero is von Mangoldt** (`hasDerivAt_jordanTotient_zero`):
  `∂_k J_k(m)|_{k=0} = Σ_{d∣m} μ(m/d) log d = Λ(m)`.
* **The Tate pieces** (`jordanTotient_eq_card_projPoints`, `jordanTotient_eq_card_primVec`): at
  `k = β + 1` the coefficients are `φ(m)#ℙ^β(ℤ/m)`; the operators `ρ_A(J_{β+1})` preserve
  positivity (`windowRepFun_jordan_nonneg`).
* **Weil's window form is a first-order jet of the Tate function** (`weilQuad_eq_tateJet`): with
  `τ_H(k) = ⟨ρ_A(J_k)H, H⟩` (`tateFunction`),
  `Q(H) = Ω(0) τ_H(0) − 2 τ_H′(0) + J_∞(H) + ½⟨c,H⟩² − ½⟨s,H⟩²`
  (`tateFunction_zero`, `hasDerivAt_tateFunction`). The values of `τ_H` at the positive integers are
  the Tate pieces of the window test; Weil's arithmetic term is its derivative at dimension zero.

The coefficientwise derivative is the window form of the shifted Jordan–Euler law
`∂_ω c_ω(n)|_{ω=0} = 2Λ(n)` (RHTower `hasDerivAt_suzukiShiftedCoefficient`, with
`c_ω(n) = n^{−ω} J_{2ω}(n)`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole
open ArithmeticDegenerationTheory ArithmeticHodgeTheoryOfDegenerations

/-! ### The Jordan family as arithmetic functions -/

/-- Jordan's totient `J_k` as an arithmetic function. -/
def jordanFun (k : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => jordanTotient k m, by simp [jordanTotient]⟩

theorem jordanFun_apply (k : ℝ) (m : ℕ) : jordanFun k m = jordanTotient k m := rfl

/-- `J_k = ζ_{(−k)} * μ`: the Tate-twisted zeta function divided by zeta. -/
theorem jordanFun_eq (k : ℝ) :
    jordanFun k = tateTwist (-k) (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
  ext m
  rw [jordanFun_apply, jordanTotient, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b =>
      tateTwist (-k) (ArithmeticFunction.zeta : ArithmeticFunction ℝ) a *
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) b)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  rw [tateTwist_apply, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hd0,
    ArithmeticFunction.intCoe_apply, neg_neg, Nat.cast_one, one_mul, mul_comm]

/-- **Dimension zero**: `J_0 = 1`. -/
theorem jordanFun_zero : jordanFun 0 = 1 := by
  rw [jordanFun_eq, neg_zero]
  have : tateTwist 0 (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
    ext n; rw [tateTwist_apply, neg_zero, Real.rpow_zero, mul_one]
  rw [this, ArithmeticFunction.coe_zeta_mul_coe_moebius]

/-- **The derivative of Jordan's totient at dimension zero is von Mangoldt**:
`∂_k J_k(m)|_{k=0} = Σ_{d∣m} μ(m/d) log d = Λ(m)`. -/
theorem hasDerivAt_jordanTotient_zero (m : ℕ) :
    HasDerivAt (fun k => jordanTotient k m) (ArithmeticFunction.vonMangoldt m) 0 := by
  have hterm : ∀ d ∈ m.divisors, HasDerivAt
      (fun k => (ArithmeticFunction.moebius (m / d) : ℝ) * (d : ℝ) ^ k)
      ((ArithmeticFunction.moebius (m / d) : ℝ) * ((d : ℝ) ^ (0 : ℝ) * Real.log d)) 0 :=
    fun d hd => ((Real.hasStrictDerivAt_const_rpow
      (by exact_mod_cast Nat.pos_of_mem_divisors hd) 0).hasDerivAt).const_mul _
  have h := HasDerivAt.fun_sum hterm
  simp only [Real.rpow_zero, one_mul] at h
  convert h using 1
  rw [← ArithmeticFunction.log_mul_moebius_eq_vonMangoldt, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => ArithmeticFunction.log a *
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) b)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [ArithmeticFunction.log_apply, ArithmeticFunction.intCoe_apply, mul_comm]

/-! ### The Tate pieces -/

/-- **Tate pieces are point counts of projective space**: `J_{β+1}(m) = φ(m)·#ℙ^β(ℤ/m)`. -/
theorem jordanTotient_eq_card_projPoints (β : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    jordanTotient (β + 1 : ℕ) m = (Nat.card (ProjPoints (β + 1) m) : ℝ) * m.totient :=
  (natCard_projPoints_mul_totient (Nat.succ_pos β) hm).symm

/-- `J_{β+1}(m)` counts the primitive vectors of `(ℤ/m)^{β+1}`. -/
theorem jordanTotient_eq_card_primVec (β : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    jordanTotient (β + 1 : ℕ) m = Nat.card (PrimVec (β + 1) m) :=
  (natCard_primVec_eq_jordanTotient (Nat.succ_pos β) m hm).symm

theorem jordanTotient_succ_nonneg (β : ℕ) (m : ℕ) : 0 ≤ jordanTotient (β + 1 : ℕ) m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [jordanTotient]
  · rw [jordanTotient_eq_card_primVec β hm]; exact Nat.cast_nonneg _

/-- **The Tate operators preserve positivity**: `ρ_A(J_{β+1})` maps nonnegative functions to
nonnegative functions. -/
theorem windowRepFun_jordan_nonneg (A : ℝ) (β : ℕ) {H : ℝ → ℝ} (hH : ∀ u, 0 ≤ H u) (u : ℝ) :
    0 ≤ windowRepFun A (jordanFun (β + 1 : ℕ)) H u := by
  refine Finset.sum_nonneg fun n _ => mul_nonneg (div_nonneg (jordanTotient_succ_nonneg β n)
    (Real.sqrt_nonneg _)) ?_
  rcases le_or_gt u 0 with h | h
  · rw [windowShift_apply_of_le _ h]; exact hH _
  · rw [windowShift_apply_of_pos _ h]

/-! ### The Tate function of a window test -/

/-- The **Tate function** `τ_H(k) = ⟨ρ_A(J_k)H, H⟩` of a window function. -/
def tateFunction (A : ℝ) (H : ℝ → ℝ) (k : ℝ) : ℝ :=
  ∫ u, windowRepFun A (jordanFun k) H u * H u

/-- The Tate function is a finite exponential sum in the dimension. -/
theorem tateFunction_eq {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) (k : ℝ) :
    tateFunction A H k = ∑ n ∈ Finset.Icc 1 (windowLevel A),
      jordanTotient k n / Real.sqrt n * ∫ u, H u * H (u + Real.log n) := by
  have hmem := mem_windowSupported_of_isWindowTest hH
  have hint : ∀ n ∈ Finset.Icc 1 (windowLevel A), Integrable fun u =>
      (jordanFun k n / Real.sqrt n) * (windowShift (Real.log n) H u * H u) := fun n _ => by
    refine Integrable.const_mul ?_ _
    simp_rw [windowShift_mul_self hmem]
    refine (integrable_mul_shift hH.continuous hH.hasCompactSupport (-Real.log n)).congr
      (Eventually.of_forall fun u => ?_)
    simp only [sub_eq_add_neg]
    ring
  rw [tateFunction]
  simp_rw [windowRepFun, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_windowShift_mul hmem, jordanFun_apply]

/-- At dimension zero the Tate function is the squared norm. -/
theorem tateFunction_zero {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    tateFunction A H 0 = ∫ u, H u ^ 2 := by
  rw [tateFunction, jordanFun_zero, windowRepFun_one (mem_windowSupported_of_isWindowTest hH)]
  simp_rw [sq]

/-- **The derivative of the Tate function at dimension zero is the arithmetic pairing**
`τ_H′(0) = ⟨ρ_A(Λ)H, H⟩`. -/
theorem hasDerivAt_tateFunction {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    HasDerivAt (tateFunction A H)
      (∫ u, windowRepFun A ArithmeticFunction.vonMangoldt H u * H u) 0 := by
  have h : HasDerivAt (fun k => ∑ n ∈ Finset.Icc 1 (windowLevel A),
      jordanTotient k n / Real.sqrt n * ∫ u, H u * H (u + Real.log n))
      (∑ n ∈ Finset.Icc 1 (windowLevel A), ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        ∫ u, H u * H (u + Real.log n)) 0 :=
    HasDerivAt.fun_sum fun n _ =>
      (((hasDerivAt_jordanTotient_zero n).div_const _).mul_const _)
  have hfun : tateFunction A H = fun k => ∑ n ∈ Finset.Icc 1 (windowLevel A),
      jordanTotient k n / Real.sqrt n * ∫ u, H u * H (u + Real.log n) :=
    funext (tateFunction_eq hH)
  rw [hfun]
  convert h using 1
  have hmem := mem_windowSupported_of_isWindowTest hH
  have hint : ∀ n ∈ Finset.Icc 1 (windowLevel A), Integrable fun u =>
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (windowShift (Real.log n) H u * H u) := fun n _ => by
    refine Integrable.const_mul ?_ _
    simp_rw [windowShift_mul_self hmem]
    refine (integrable_mul_shift hH.continuous hH.hasCompactSupport (-Real.log n)).congr
      (Eventually.of_forall fun u => ?_)
    simp only [sub_eq_add_neg]
    ring
  simp_rw [windowRepFun, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_windowShift_mul hmem]

/-- At the positive integers the Tate function reads the projective point counts:
`τ_H(β + 1) = Σ_{m ≤ e^A} φ(m)#ℙ^β(ℤ/m) m^{−1/2} ∫ H(u)H(u + log m)`. -/
theorem tateFunction_succ {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) (β : ℕ) :
    tateFunction A H (β + 1 : ℕ) = ∑ m ∈ Finset.Icc 1 (windowLevel A),
      (Nat.card (ProjPoints (β + 1) m) : ℝ) * m.totient / Real.sqrt m *
        ∫ u, H u * H (u + Real.log m) := by
  rw [tateFunction_eq hH]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [jordanTotient_eq_card_projPoints β (Finset.mem_Icc.mp hm).1]

/-- **Weil's window form is a first-order jet of the Tate function**:
`Q(H) = Ω(0) τ_H(0) − 2 τ_H′(0) + J_∞(H) + ½⟨c,H⟩² − ½⟨s,H⟩²`. -/
theorem weilQuad_eq_tateJet {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    weilQuad H = EF.gammaBracket 0 * tateFunction A H 0 - 2 * deriv (tateFunction A H) 0 +
      levyJump H + (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2) := by
  rw [weilQuad_eq_windowRep hH, tateFunction_zero hH, (hasDerivAt_tateFunction hH).deriv]
  ring

end GaloisForLFunctions.WindowTowerOfSpecZ

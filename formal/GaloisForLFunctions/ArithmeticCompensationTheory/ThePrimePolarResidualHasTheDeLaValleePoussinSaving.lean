import GaloisForLFunctions.ArithmeticIncidencePositivity.LagChebyshevAbelSummation
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs

/-!
# The compensated prime–polar residual has the de la Vallée Poussin saving

The prime side of the critical ledger and its polar counterpart cancel before any square is
taken: for every `C¹` lag weight `h` vanishing from `S` on,

`Σ_n Λ(n) h(log n) − ∫_{s>0} (e^s + 1) h(s) ds = ∫_0^S E(s) h′(s) ds`,

with the two-pole Chebyshev defect `E(s) = e^s + s − 1 − ψ(e^s)`
(`ArithmeticIncidencePositivity.sum_vonMangoldt_sub_polar_eq_chebyshev`), and on the translate of a
compact test this is the ledger's own pairing
(`ArithmeticIncidencePositivity.primeShift_sub_polarDensity_eq_chebyshev`). This file gives the
residual its aperture exponent, uniformly over the expanding test class:

* `exists_abs_chebyshevTwoPoleDefect_mul_exp_le`: for every weight `e^{−θs}`, `0 ≤ θ ≤ ½`,
  `sup_{0 ≤ s ≤ S} |E(s)| e^{−θs} ≤ K e^{(1−θ)S} exp(−c√S)`: the prime number theorem with the de la
  Vallée Poussin error above a fixed scale, and a constant below it;
* `exists_abs_sum_vonMangoldt_sub_polar_le`: the residual of every lag weight of aperture `S` is
  at most `K e^S exp(−c√S) ∫_0^S |h′|`;
* `exists_abs_primeShift_sub_polar_le`: on the translate `x` of a `C¹` test supported in `[−r, r]`,
  `S = 2r + |x|`, the residual is at most `K e^{S/2} exp(−c√S) (2‖F′‖₁ + ‖F‖₁)`.

The constants `c, K, S₀` are universal. Against the trivial exponent `e^{S/2}` of the ledger
(`|E(s)| ≤ Ce^s`) the saving is exactly the prime number theorem's; an exponent `e^{θS}` with
`θ < ½` is classically equivalent to a zero-free strip, and is not claimed here.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.ArithmeticIncidencePositivity

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-- The lag Chebyshev function is `ψ(e^s)`. -/
theorem lagChebyshev_eq_psi (s : ℝ) : lagChebyshev s = Chebyshev.psi (Real.exp s) := by
  rw [lagChebyshev, Chebyshev.psi, ← Finset.Ioc_insert_left (Nat.zero_le _),
    Finset.sum_insert (by simp)]
  simp

/-- **The two-pole defect at the de la Vallée Poussin rate, with an exponential weight.** -/
theorem exists_abs_chebyshevTwoPoleDefect_mul_exp_le :
    ∃ c > 0, ∃ K : ℝ, 0 ≤ K ∧ ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S, S₀ ≤ S → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 2 →
      ∀ s ∈ Icc (0 : ℝ) S, |chebyshevTwoPoleDefect s| * Real.exp (-θ * s) ≤
        K * Real.exp ((1 - θ) * S) * Real.exp (-c * Real.sqrt S) := by
  obtain ⟨C, c, hc, hC, hev⟩ := RHTower.exists_psi_error_eventually
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  set s₁ := max (max (Real.log X) 4) (4 * c ^ 2)
  have hs₁4 : 4 ≤ s₁ := (le_max_right _ _).trans (le_max_left _ _)
  have hs₁c : 4 * c ^ 2 ≤ s₁ := le_max_right _ _
  have hs₁X : Real.log X ≤ s₁ := (le_max_left _ _).trans (le_max_left _ _)
  set B₁ := Real.exp s₁ + (s₁ + 1) + Chebyshev.psi (Real.exp s₁)
  have hB₁ : 0 ≤ B₁ := by have := Chebyshev.psi_nonneg (Real.exp s₁); positivity
  refine ⟨c, hc, C + 1 + B₁, by positivity, s₁, by linarith, fun S hS θ hθ0 hθ1 s hs => ?_⟩
  obtain ⟨hs0, hsS⟩ := hs
  have hS0 : 0 ≤ S := by linarith
  -- `c√t ≤ t/2` as soon as `t ≥ 4c²`
  have hsqrt : ∀ t, 4 * c ^ 2 ≤ t → c * Real.sqrt t ≤ t / 2 := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (by positivity) ht
    have h1 : 2 * c ≤ Real.sqrt t := Real.le_sqrt_of_sq_le (by nlinarith)
    have h2 := Real.mul_self_sqrt ht0
    nlinarith [Real.sqrt_nonneg t]
  have hSc := hsqrt S (hs₁c.trans hS)
  have hgS : 1 ≤ Real.exp ((1 - θ) * S) * Real.exp (-c * Real.sqrt S) := by
    rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
  have hE : chebyshevTwoPoleDefect s = (Real.exp s - Chebyshev.psi (Real.exp s)) + (s - 1) := by
    rw [chebyshevTwoPoleDefect_eq_error_add, chebyshevError, lagChebyshev_eq_psi]
  have hw : Real.exp (-θ * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  rcases le_or_gt s s₁ with hss | hss
  · -- below the fixed scale the defect is bounded
    have hbd : |chebyshevTwoPoleDefect s| ≤ B₁ := by
      rw [hE]
      have h1 : Real.exp s ≤ Real.exp s₁ := Real.exp_le_exp.mpr hss
      have h2 : Chebyshev.psi (Real.exp s) ≤ Chebyshev.psi (Real.exp s₁) :=
        Chebyshev.psi_mono h1
      have h3 := Chebyshev.psi_nonneg (Real.exp s)
      have h4 := Real.exp_pos s
      rw [abs_le]; constructor <;> nlinarith
    calc |chebyshevTwoPoleDefect s| * Real.exp (-θ * s) ≤ B₁ * 1 :=
          mul_le_mul hbd hw (Real.exp_pos _).le hB₁
      _ ≤ B₁ * (Real.exp ((1 - θ) * S) * Real.exp (-c * Real.sqrt S)) :=
          mul_le_mul_of_nonneg_left hgS hB₁
      _ ≤ (C + 1 + B₁) * Real.exp ((1 - θ) * S) * Real.exp (-c * Real.sqrt S) := by
          have := Real.exp_pos ((1 - θ) * S); have := Real.exp_pos (-c * Real.sqrt S)
          nlinarith [mul_pos (Real.exp_pos ((1 - θ) * S)) (Real.exp_pos (-c * Real.sqrt S))]
  · -- above it, the prime number theorem
    have hs1 : s₁ ≤ s := hss.le
    have hXs : X ≤ Real.exp s := by
      calc X ≤ max X 1 := le_max_left _ _
        _ = Real.exp (Real.log (max X 1)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp s := Real.exp_le_exp.mpr (by
            rcases le_or_gt X 1 with hX1 | hX1
            · rw [max_eq_right hX1, Real.log_one]; linarith
            · rw [max_eq_left hX1.le]; linarith)
    have hpnt := hX (Real.exp s) hXs
    rw [Real.log_exp, abs_sub_comm] at hpnt
    have hlin : |s - 1| ≤ Real.exp s * Real.exp (-c * Real.sqrt s) := by
      have h1 : s + 1 ≤ Real.exp (s / 2) := by
        have := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ s / 2)
        nlinarith
      have h2 : Real.exp (s / 2) ≤ Real.exp s * Real.exp (-c * Real.sqrt s) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [hsqrt s (hs₁c.trans hs1)])
      rw [abs_le]; constructor <;> linarith
    have hpt : |chebyshevTwoPoleDefect s| ≤ (C + 1) * (Real.exp s * Real.exp (-c * Real.sqrt s)) := by
      rw [hE]
      calc |(Real.exp s - Chebyshev.psi (Real.exp s)) + (s - 1)|
          ≤ |Real.exp s - Chebyshev.psi (Real.exp s)| + |s - 1| := abs_add_le _ _
        _ ≤ C * (Real.exp s * Real.exp (-c * Real.sqrt s)) +
            Real.exp s * Real.exp (-c * Real.sqrt s) := add_le_add hpnt hlin
        _ = (C + 1) * (Real.exp s * Real.exp (-c * Real.sqrt s)) := by ring
    -- the weight `e^{(1−θ)t − c√t}` increases on `t ≥ 4c²`
    have hmono : (1 - θ) * s - c * Real.sqrt s ≤ (1 - θ) * S - c * Real.sqrt S := by
      have ha : 2 * c ≤ Real.sqrt s := Real.le_sqrt_of_sq_le (by nlinarith)
      have hab : Real.sqrt s ≤ Real.sqrt S := Real.sqrt_le_sqrt hsS
      have hsa := Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ s)
      have hSb := Real.mul_self_sqrt hS0
      nlinarith [mul_nonneg (sub_nonneg.mpr hab) (by nlinarith : (0 : ℝ) ≤
        (1 - θ) * (Real.sqrt s + Real.sqrt S) - c)]
    calc |chebyshevTwoPoleDefect s| * Real.exp (-θ * s)
        ≤ (C + 1) * (Real.exp s * Real.exp (-c * Real.sqrt s)) * Real.exp (-θ * s) :=
          mul_le_mul_of_nonneg_right hpt (Real.exp_pos _).le
      _ = (C + 1) * Real.exp ((1 - θ) * s - c * Real.sqrt s) := by
          rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ (C + 1) * Real.exp ((1 - θ) * S - c * Real.sqrt S) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmono) (by positivity)
      _ ≤ (C + 1 + B₁) * Real.exp ((1 - θ) * S) * Real.exp (-c * Real.sqrt S) := by
          rw [mul_assoc, ← Real.exp_add, show (1 - θ) * S + -c * Real.sqrt S =
            (1 - θ) * S - c * Real.sqrt S by ring]
          exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- **The compensated residual of every lag weight.** With universal `c, K, S₀`, every `C¹` weight
vanishing from `S ≥ S₀` on has prime–polar residual at most `K e^S exp(−c√S) ∫_0^S |h′|`. -/
theorem exists_abs_sum_vonMangoldt_sub_polar_le :
    ∃ c > 0, ∃ K : ℝ, 0 ≤ K ∧ ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ S, S₀ ≤ S → ∀ h : ℝ → ℝ, ContDiff ℝ 1 h →
      (∀ s, S ≤ s → h s = 0) → ∀ N : ℕ, Real.exp S ≤ N →
      |(∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * h (Real.log n)) -
          ∫ s in Ioi (0 : ℝ), (Real.exp s + 1) * h s| ≤
        K * Real.exp S * Real.exp (-c * Real.sqrt S) * ∫ s in Ioc (0 : ℝ) S, |deriv h s| := by
  obtain ⟨c, hc, K, hK, S₀, hS₀, hE⟩ := exists_abs_chebyshevTwoPoleDefect_mul_exp_le
  refine ⟨c, hc, K, hK, S₀, hS₀, fun S hS h hh hvan N hN => ?_⟩
  have hS0 : 0 < S := by linarith
  set M := K * Real.exp S * Real.exp (-c * Real.sqrt S)
  have hM : ∀ s ∈ Ioc (0 : ℝ) S, |chebyshevTwoPoleDefect s| ≤ M := fun s hs => by
    have := hE S hS 0 le_rfl (by norm_num) s ⟨hs.1.le, hs.2⟩
    simpa [M] using this
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  rw [sum_vonMangoldt_sub_polar_eq_chebyshev hh hS0 hvan hN,
    integral_chebyshev_mul_deriv_eq_Ioc hh hS0 hvan hN, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on ?_ ?_ measurableSet_Ioc
    fun s hs => ?_)
  · exact ((integrableOn_Ioi_chebyshevTwoPoleDefect_mul_deriv hh hS0 hvan hN).mono_set
      fun t ht => ht.1).abs
  · exact (continuous_const.mul hdc.abs).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hM s hs) (abs_nonneg _)

/-- **The compensated residual of the ledger, on every translate.** With universal `c, K, S₀`, for
every `C¹` test supported in `[−r, r]` and every translate `x` with `S = 2r + |x| ≥ S₀`, the prime
atoms `Σ Λ(n) 2n^{−1/2} F(x + log n)` and the polar density `∫ 4cosh(s/2) F(x + s)` differ by at most
`K e^{S/2} exp(−c√S) (2‖F′‖₁ + ‖F‖₁)`. -/
theorem exists_abs_primeShift_sub_polar_le :
    ∃ c > 0, ∃ K : ℝ, 0 ≤ K ∧ ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → ∀ r : ℝ, 0 < r →
      (∀ y, r < |y| → F y = 0) → ∀ x : ℝ, S₀ ≤ 2 * r + |x| → ∀ N : ℕ,
      Real.exp (2 * r + |x|) ≤ N →
      |(∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
            (2 * (Real.sqrt n)⁻¹ * F (x + Real.log n))) -
          ∫ s in Ioi (0 : ℝ), 4 * Real.cosh (s / 2) * F (x + s)| ≤
        K * Real.exp ((2 * r + |x|) / 2) * Real.exp (-c * Real.sqrt (2 * r + |x|)) *
          (2 * ∫ y, |deriv F y| + ∫ y, |F y|) := by
  obtain ⟨c, hc, K, hK, S₀, hS₀, hE⟩ := exists_abs_chebyshevTwoPoleDefect_mul_exp_le
  refine ⟨c, hc, K, hK, S₀, hS₀, fun F hF r hr hsupp x hS N hN => ?_⟩
  set S := 2 * r + |x| with hSdef
  have hS0 : 0 < S := by have := abs_nonneg x; linarith
  set M := K * Real.exp (S / 2) * Real.exp (-c * Real.sqrt S)
  have hM0 : 0 ≤ M := by positivity
  have hM : ∀ s ∈ Ioc (0 : ℝ) S, |chebyshevTwoPoleDefect s| * Real.exp (-s / 2) ≤ M := by
    intro s hs
    have := hE S hS (1 / 2) (by norm_num) le_rfl s ⟨hs.1.le, hs.2⟩
    simp only [M]
    rw [show -s / 2 = -(1 / 2) * s by ring, show S / 2 = (1 - 1 / 2) * S by ring]
    exact this
  have hFc : HasCompactSupport F :=
    HasCompactSupport.intro (isCompact_Icc (a := -r) (b := r)) fun y hy => hsupp y (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
      rcases hy with hy | hy
      · linarith [neg_le_abs y]
      · linarith [le_abs_self y])
  have hdc : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hFi : Integrable F := hF.continuous.integrable_of_hasCompactSupport hFc
  have hdi : Integrable (deriv F) := hdc.integrable_of_hasCompactSupport hFc.deriv
  have hvan : ∀ s, S ≤ s → shiftLagWeight F x s = 0 :=
    fun s hs => shiftLagWeight_eq_zero hr hsupp x hs
  have hsl := contDiff_shiftLagWeight hF x
  rw [primeShift_sub_polarDensity_eq_chebyshev hF hr hsupp x hN]
  have hderiv : ∀ s, shiftLagWeightDeriv F x s = deriv (shiftLagWeight F x) s :=
    fun s => (deriv_shiftLagWeight hF x s).symm
  simp only [hderiv]
  rw [integral_chebyshev_mul_deriv_eq_Ioc hsl hS0 hvan hN]
  simp only [← hderiv]
  -- the majorant `M (2|F′(x+s)| + |F(x+s)|)`
  set G : ℝ → ℝ := fun s => M * (2 * |deriv F (x + s)| + |F (x + s)|)
  have hGi : Integrable G := by
    have h1 : Integrable fun s => |deriv F (x + s)| := (hdi.comp_add_left x).abs
    have h2 : Integrable fun s => |F (x + s)| := (hFi.comp_add_left x).abs
    exact ((h1.const_mul 2).add h2).const_mul M
  have hGint : (∫ s, G s) = M * (2 * ∫ y, |deriv F y| + ∫ y, |F y|) := by
    have h1 : Integrable fun s => |deriv F (x + s)| := (hdi.comp_add_left x).abs
    have h2 : Integrable fun s => |F (x + s)| := (hFi.comp_add_left x).abs
    have e1 : (∫ s, |deriv F (x + s)|) = ∫ y, |deriv F y| :=
      integral_add_left_eq_self (fun y => |deriv F y|) x
    have e2 : (∫ s, |F (x + s)|) = ∫ y, |F y| := integral_add_left_eq_self (fun y => |F y|) x
    simp only [G]
    rw [integral_const_mul, integral_add (h1.const_mul 2) h2, integral_const_mul, e1, e2]
  have hint : IntegrableOn (fun s => chebyshevTwoPoleDefect s * shiftLagWeightDeriv F x s)
      (Ioc (0 : ℝ) S) := by
    have h := (integrableOn_Ioi_chebyshevTwoPoleDefect_mul_deriv hsl hS0 hvan hN).mono_set
      (fun t (ht : t ∈ Ioc (0 : ℝ) S) => ht.1)
    exact h.congr_fun (fun s _ => by rw [hderiv]) measurableSet_Ioc
  calc |∫ s in Ioc (0 : ℝ) S, chebyshevTwoPoleDefect s * shiftLagWeightDeriv F x s|
      ≤ ∫ s in Ioc (0 : ℝ) S, |chebyshevTwoPoleDefect s * shiftLagWeightDeriv F x s| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ s in Ioc (0 : ℝ) S, G s := by
        refine setIntegral_mono_on hint.abs hGi.integrableOn measurableSet_Ioc fun s hs => ?_
        rw [shiftLagWeightDeriv, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos (Real.exp_pos _)]
        have hd : |deriv F (x + s) - F (x + s) / 2| ≤ |deriv F (x + s)| + |F (x + s)| / 2 := by
          refine (abs_sub _ _).trans ?_
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have hm := hM s hs
        calc |chebyshevTwoPoleDefect s| * (2 * Real.exp (-s / 2) * |deriv F (x + s) - F (x + s) / 2|)
            = |chebyshevTwoPoleDefect s| * Real.exp (-s / 2) *
                (2 * |deriv F (x + s) - F (x + s) / 2|) := by ring
          _ ≤ M * (2 * (|deriv F (x + s)| + |F (x + s)| / 2)) :=
              mul_le_mul hm (by linarith) (by positivity) hM0
          _ = G s := by simp only [G]; ring
    _ ≤ ∫ s, G s := setIntegral_le_integral hGi (Eventually.of_forall fun s => by
        simp only [G]; positivity)
    _ = M * (2 * ∫ y, |deriv F y| + ∫ y, |F y|) := hGint

end GaloisForLFunctions.ArithmeticCompensationTheory

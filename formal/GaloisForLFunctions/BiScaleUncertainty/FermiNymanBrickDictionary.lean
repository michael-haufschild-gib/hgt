import GaloisForLFunctions.BiScaleUncertainty.DyadicBlockEnergyDiscreteDeviation
import GaloisForLFunctions.BiScaleUncertainty.LocalToGlobalTailStabilityAndWitnessIndicatorPairing

/-!
# The Fermi–Nyman generators as dyadic bricks of the field

The Fermi–Nyman–Beurling generators `φ_a(t) = {1/(at)} − 2{1/(2at)}` live on `(0, 1]`.  Under the
exponential change of variables `t = e^{−u}` the Hilbert space `L²((0,1], dt)` becomes the gauge
space of the field,

`∫_0^1 ‖F(t)‖² dt = ∫_0^∞ ‖e^{−u/2} F(e^{−u})‖² du`,

and on the bulk `u < log(2a)` the generator is minus the dyadic block indicator,

`φ_a(e^{−u}) = −1_{[log a, log 2a)}(u)`

(the step-brick law of the parallel FZZ-P programme).  The field reads the gauge-lifted brick through
the signed prime–polar measure as the dyadic Chebyshev difference,

`pairing N (e^{t/2} 1_{(log a, log 2a]}) = ψ(2a) − ψ(a) − a − log 2`.

Thus the Nyman–Beurling approximation problem of FZZ-P (approximate the Haar target by generator
combinations in `L²(0,1)`) is, in the field's coordinates, the approximation of a gauge brick by dyadic
block bricks plus origin tails (`u ≥ log 2a`), and the generators pair with `ν_N` to exactly the
coarse dyadic block discrepancies of the renewal chain.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators CompactlySupported Real

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar RHTower
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

/-! ## The exponential change of variables -/

theorem image_exp_neg_Ici : (fun u : ℝ => Real.exp (-u)) '' Ici 0 = Ioc 0 1 := by
  ext x
  simp only [mem_image, mem_Ici, mem_Ioc]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨Real.exp_pos _, Real.exp_le_one_iff.2 (by linarith)⟩
  · rintro ⟨hx0, hx1⟩
    refine ⟨-Real.log x, ?_, by rw [neg_neg, Real.exp_log hx0]⟩
    simp only [neg_nonneg]
    exact Real.log_nonpos hx0.le hx1

/-- `∫_0^1 F(t) dt = ∫_0^∞ e^{−u} F(e^{−u}) du`. -/
theorem integral_Ioc_zero_one_eq_integral_exp_neg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℝ → E) :
    (∫ t in Ioc (0 : ℝ) 1, F t) = ∫ u in Ici (0 : ℝ), Real.exp (-u) • F (Real.exp (-u)) := by
  rw [← image_exp_neg_Ici, integral_image_eq_integral_abs_deriv_smul measurableSet_Ici
    (fun u _ => ((hasDerivAt_neg u).exp).hasDerivWithinAt)
    (fun u _ v _ h => neg_inj.1 (Real.exp_injective h)) F]
  refine setIntegral_congr_fun measurableSet_Ici fun u _ => ?_
  show |Real.exp (-u) * -1| • F (Real.exp (-u)) = Real.exp (-u) • F (Real.exp (-u))
  rw [abs_mul, abs_neg, abs_one, mul_one, abs_of_pos (Real.exp_pos _)]

/-- **`L²(0,1]` is the gauge space:** `∫_0^1 ‖F‖² = ∫_0^∞ ‖e^{−u/2} F(e^{−u})‖²`. -/
theorem integral_norm_sq_Ioc_eq_gauge (F : ℝ → ℂ) :
    (∫ t in Ioc (0 : ℝ) 1, ‖F t‖ ^ 2) =
      ∫ u in Ici (0 : ℝ), ‖(Real.exp (-u / 2) : ℂ) * F (Real.exp (-u))‖ ^ 2 := by
  rw [integral_Ioc_zero_one_eq_integral_exp_neg (fun t => ‖F t‖ ^ 2)]
  refine setIntegral_congr_fun measurableSet_Ici fun u _ => ?_
  show Real.exp (-u) • ‖F (Real.exp (-u))‖ ^ 2 =
    ‖(Real.exp (-u / 2) : ℂ) * F (Real.exp (-u))‖ ^ 2
  rw [smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mul_pow, sq (Real.exp (-u / 2)), ← Real.exp_add]
  congr 2
  ring

/-! ## The generator bulk as a dyadic block -/

/-- **The Fermi–Nyman generator in log coordinates:** on the bulk `u < log(2a)`,
`φ_a(e^{−u}) = −1_{[log a, log 2a)}(u)`. -/
theorem fermiNymanGen_exp_neg_bulk (a : ℕ) {u : ℝ}
    (hu : u < Real.log (2 * ((a + 1 : ℕ) : ℝ))) :
    _root_.RHTower.fermiNymanGen ((a + 1 : ℕ) : ℝ) (Real.exp (-u)) =
      -(Ico (Real.log ((a + 1 : ℕ) : ℝ)) (Real.log (2 * ((a + 1 : ℕ) : ℝ)))).indicator
        (fun _ => (1 : ℂ)) u := by
  have ha : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by positivity
  have h2a : (0 : ℝ) < 2 * ((a + 1 : ℕ) : ℝ) := by positivity
  have h := fermiNymanGen_nat_eq_neg_indicator_on_bulk a (Real.exp (-u))
  have hmem : Real.exp (-u) ∈ Ioi (1 / (2 * ((a + 1 : ℕ) : ℝ))) := by
    show 1 / (2 * ((a + 1 : ℕ) : ℝ)) < Real.exp (-u)
    rw [one_div, ← Real.exp_log (inv_pos.2 h2a), Real.log_inv]
    exact Real.exp_lt_exp.2 (by linarith)
  rw [Set.indicator_of_mem hmem] at h
  rw [h]
  congr 1
  by_cases hmem2 : Real.exp (-u) ∈ Ioc (1 / (2 * ((a + 1 : ℕ) : ℝ))) (1 / ((a + 1 : ℕ) : ℝ))
  · rw [Set.indicator_of_mem hmem2, Set.indicator_of_mem]
    refine ⟨?_, hu⟩
    have := hmem2.2
    rw [one_div, ← Real.exp_log (inv_pos.2 ha), Real.log_inv, Real.exp_le_exp] at this
    linarith
  · rw [Set.indicator_of_notMem hmem2, Set.indicator_of_notMem]
    intro hu2
    apply hmem2
    refine ⟨hmem, ?_⟩
    rw [one_div, ← Real.exp_log (inv_pos.2 ha), Real.log_inv, Real.exp_le_exp]
    linarith [hu2.1]

/-! ## The field's reading of a gauge-lifted brick -/

theorem polarRectangle_sub_eq_indicator {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (t : ℝ) :
    polarRectangle b t - polarRectangle a t =
      Real.exp (t / 2) * (Ioc a b).indicator (fun _ => (1 : ℝ)) t := by
  unfold polarRectangle
  by_cases hb : t ∈ Icc 0 b
  · by_cases ha' : t ∈ Icc 0 a
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem ha',
        Set.indicator_of_notMem (show t ∉ Ioc a b from fun h => absurd ha'.2 (not_le.2 h.1))]
      ring
    · have hta : a < t := by
        by_contra hcon
        exact ha' ⟨hb.1, not_lt.1 hcon⟩
      rw [Set.indicator_of_mem hb, Set.indicator_of_notMem ha',
        Set.indicator_of_mem (show t ∈ Ioc a b from ⟨hta, hb.2⟩)]
      ring
  · have hna : t ∉ Icc 0 a := fun h => hb ⟨h.1, h.2.trans hab⟩
    have hnab : t ∉ Ioc a b := fun h => hb ⟨ha.trans h.1.le, h.2⟩
    rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hna, Set.indicator_of_notMem hnab]
    ring

/-- **The gauge-lifted brick reads the Chebyshev error increment:**
`pairing N (e^{t/2} 1_{(a,b]}) = (ψ(e^b) − e^b) − (ψ(e^a) − e^a) − (b − a)`. -/
theorem pairing_exp_half_mul_indicator_Ioc (N : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbL : b ≤ cutoff N) :
    pairing N (fun t => Real.exp (t / 2) * (Ioc a b).indicator (fun _ => (1 : ℝ)) t) =
      logError b - logError a - (b - a) := by
  have h := pairing_polarRectangle_sub N ha hab hbL
  rw [show (fun t => polarRectangle b t - polarRectangle a t) =
      fun t => Real.exp (t / 2) * (Ioc a b).indicator (fun _ => (1 : ℝ)) t from
      funext (polarRectangle_sub_eq_indicator ha hab)] at h
  rw [h, blockResponse_eq]
  have he : Real.exp (b / 2) * Real.exp (-b / 2) = 1 := by
    rw [← Real.exp_add, show b / 2 + -b / 2 = 0 by ring, Real.exp_zero]
  linear_combination (logError b - logError a - (b - a)) * he

/-- **The dyadic brick of `a` reads `ψ(2a) − ψ(a) − a − log 2`.** -/
theorem pairing_dyadicBrick (N : ℕ) {a : ℕ} (ha : 1 ≤ a)
    (hL : Real.log (2 * (a : ℝ)) ≤ cutoff N) :
    pairing N (fun t => Real.exp (t / 2) *
        (Ioc (Real.log (a : ℝ)) (Real.log (2 * (a : ℝ)))).indicator (fun _ => (1 : ℝ)) t) =
      Chebyshev.psi (2 * (a : ℝ)) - Chebyshev.psi (a : ℝ) - a - Real.log 2 := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  rw [pairing_exp_half_mul_indicator_Ioc N (Real.log_nonneg (by exact_mod_cast ha))
    (Real.log_le_log ha0 (by linarith)) hL]
  unfold logError
  rw [Real.exp_log ha0, Real.exp_log (by positivity), Real.log_mul (by norm_num) ha0.ne']
  ring

/-- The dyadic brick reading is the gauge-lifted chain input: with `X = 2^k`,
`pairing N (e^{t/2} 1_{(log X, log 2X]}) = √(2X) · r_k`. -/
theorem pairing_dyadicBrick_eq_sqrt_mul_chainInput (N : ℕ) {k : ℕ}
    (hk : (k + 1) * Real.log 2 ≤ cutoff N) :
    pairing N (fun t => Real.exp (t / 2) *
        (Ioc (Real.log (((2 ^ k : ℕ) : ℝ))) (Real.log (2 * ((2 ^ k : ℕ) : ℝ)))).indicator
          (fun _ => (1 : ℝ)) t) =
      Real.exp (((k : ℝ) + 1) * Real.log 2 / 2) * chainInput (Real.log 2) k := by
  have hX : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hX0 : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have e1 : Real.exp ((k : ℝ) * Real.log 2) = ((2 ^ k : ℕ) : ℝ) := by
    rw [log_two_pow, Real.exp_log hX0]
  have e2 : Real.exp (((k : ℝ) + 1) * Real.log 2) = 2 * ((2 ^ k : ℕ) : ℝ) := by
    rw [log_two_pow_succ, Real.exp_log (by positivity)]
    push_cast; ring
  have hL : Real.log (2 * ((2 ^ k : ℕ) : ℝ)) ≤ cutoff N := by
    rw [← e2, Real.log_exp]; exact hk
  rw [pairing_dyadicBrick N hX hL]
  unfold chainInput blockResponse
  rw [e1, e2]
  have he : Real.exp (((k : ℝ) + 1) * Real.log 2 / 2) *
      Real.exp (-(((k : ℝ) + 1) * Real.log 2) / 2) = 1 := by
    rw [← Real.exp_add, show ((k : ℝ) + 1) * Real.log 2 / 2 + -(((k : ℝ) + 1) * Real.log 2) / 2 = 0
      by ring, Real.exp_zero]
  linear_combination (-(Chebyshev.psi (2 * ((2 ^ k : ℕ) : ℝ)) - Chebyshev.psi ((2 ^ k : ℕ) : ℝ) -
    (2 * ((2 ^ k : ℕ) : ℝ) - ((2 ^ k : ℕ) : ℝ)) -
    (((k : ℝ) + 1) * Real.log 2 - (k : ℝ) * Real.log 2))) * he

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

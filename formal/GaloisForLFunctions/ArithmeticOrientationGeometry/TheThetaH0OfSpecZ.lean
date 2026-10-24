import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Normed.Group.Tannery
import GaloisForLFunctions.ArithmeticOrientationGeometry.ScalingDataAndWeilPlanes

/-!
# The theta `h⁰` of `Spec ℤ` and its Riemann–Roch

The review asks for an `h⁰` defined from arithmetic, not from the sign of the form, with a
Riemann–Roch theorem proved independently. On the base `Spec ℤ` this exists: it is the
`h⁰` of Arakelov divisors of van der Geer–Schoof, the logarithm of the number of lattice points
of `ℤ` counted with Gaussian weight. The scale group acts on Arakelov divisors by translating the
degree.

* **The arithmetic `h⁰`** (`arithH0`). For the Arakelov divisor of degree `d`,
  `h⁰(d) = log Σ_{n ∈ ℤ} e^{−π n² e^{−2d}}`: the lattice `ℤ ⊂ ℝ` with metric scaled by `e^{−d}`.
* **Riemann–Roch** (`arithH0_riemannRoch`): `h⁰(d) − h⁰(−d) = d`, from Poisson summation for the
  Gaussian (`Real.tsum_exp_neg_mul_int_sq`). No positivity of any form is used.
* **Effectivity and vanishing** (`arithH0_pos`, `arithH0_strictMono`, `tendsto_arithH0_atBot`,
  `tendsto_arithH0_sub_atTop`). `h⁰` is positive and strictly increasing; it tends to `0` as
  `d → −∞` (no sections of very negative degree) and `h⁰(d) − d → 0` as `d → ∞`
  (Riemann–Roch asymptotics).
* **The generating function is `Λ(s)`** (`completedRiemannZeta_eq_mellin_arithH0`). For `Re s > 1`,
  `π^{−s/2}Γ(s/2)ζ(s)` is half the Mellin transform at `s/2` of `e^{h⁰} − 1` in the variable
  `t = e^{−2d}`: the completed zeta function is the generating function of `h⁰` along the scale
  line, and its functional equation is this Riemann–Roch.
* **The pole plane** (`poleH0`, `poleH0_riemannRoch`). On every polar surface the fibre class
  `D = aH + bV` (`a, b > 0`) gets `h⁰(D) = h⁰(log a) + h⁰(log b)`, and with
  `D^∨ = a⁻¹H + b⁻¹V`: `h⁰(D) − h⁰(D^∨) = log(D²/2)`. The self-intersection enters only through
  its logarithm.

The theorem is the Riemann–Roch of the base, where Weil uses the Riemann–Roch of the curve; it
yields the functional equation and holds equally for every datum with one. The Hodge index needs
Riemann–Roch on the surface, for classes with a test component, and that is not supplied here.
-/

noncomputable section

open Real Filter Topology

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri

/-! ### The theta sum -/

/-- The theta sum `θ(u) = Σ_{n ∈ ℤ} e^{−π u n²}`. -/
def thetaSum (u : ℝ) : ℝ := ∑' n : ℤ, Real.exp (-π * u * (n : ℝ) ^ 2)

theorem hasSum_thetaSum {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℤ => Real.exp (-π * u * (n : ℝ) ^ 2)) (HurwitzZeta.evenKernel 0 u) := by
  have h := HurwitzZeta.hasSum_int_evenKernel 0 hu
  refine h.congr_fun fun n => ?_
  simp only [add_zero]
  ring_nf

theorem summable_thetaSum {u : ℝ} (hu : 0 < u) :
    Summable fun n : ℤ => Real.exp (-π * u * (n : ℝ) ^ 2) :=
  (hasSum_thetaSum hu).summable

/-- The theta sum is Mathlib's even Hurwitz kernel at `0`. -/
theorem thetaSum_eq_evenKernel {u : ℝ} (hu : 0 < u) :
    thetaSum u = HurwitzZeta.evenKernel 0 u :=
  (hasSum_thetaSum hu).tsum_eq

/-- **The theta transformation**, Poisson summation for the Gaussian: `θ(u) = u^{−1/2} θ(1/u)`. -/
theorem thetaSum_inv {u : ℝ} (hu : 0 < u) : thetaSum u = (u ^ (1 / 2 : ℝ))⁻¹ * thetaSum u⁻¹ := by
  rw [thetaSum, Real.tsum_exp_neg_mul_int_sq hu, one_div, thetaSum]
  congr 1

theorem one_le_thetaSum {u : ℝ} (hu : 0 < u) : 1 ≤ thetaSum u :=
  calc (1 : ℝ) = Real.exp (-π * u * ((0 : ℤ) : ℝ) ^ 2) := by simp
    _ ≤ thetaSum u := (summable_thetaSum hu).le_tsum 0 fun j _ => (Real.exp_pos _).le

theorem thetaSum_pos {u : ℝ} (hu : 0 < u) : 0 < thetaSum u :=
  lt_of_lt_of_le one_pos (one_le_thetaSum hu)

/-- The theta sum is strictly decreasing. -/
theorem thetaSum_lt_thetaSum {u v : ℝ} (hu : 0 < u) (huv : u < v) : thetaSum v < thetaSum u := by
  refine (summable_thetaSum (hu.trans huv)).tsum_lt_tsum (i := 1) (fun n => ?_) ?_
    (summable_thetaSum hu)
  · have h0 : 0 ≤ π * (n : ℝ) ^ 2 * (v - u) :=
      mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) (sub_nonneg.mpr huv.le)
    exact Real.exp_le_exp.mpr (by nlinarith)
  · have h1 : 0 < π * (v - u) := mul_pos Real.pi_pos (sub_pos.mpr huv)
    simp only [Int.cast_one, one_pow, mul_one]
    exact Real.exp_lt_exp.mpr (by nlinarith)

/-- **Tannery**: `θ(u) → 1` as `u → ∞`. -/
theorem tendsto_thetaSum_atTop : Tendsto thetaSum atTop (𝓝 1) := by
  classical
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun u (n : ℤ) => Real.exp (-π * u * (n : ℝ) ^ 2))
    (g := fun n : ℤ => if n = 0 then 1 else 0)
    (bound := fun n : ℤ => Real.exp (-π * 1 * (n : ℝ) ^ 2)) (summable_thetaSum one_pos)
    (fun n => ?_) ?_
  · rw [tsum_ite_eq] at h
    exact h
  · by_cases hn : n = 0
    · simp only [hn, if_pos, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, Real.exp_zero]
      exact tendsto_const_nhds
    · rw [if_neg hn]
      have hn2 : 0 < (n : ℝ) ^ 2 := by positivity
      have hlin : Tendsto (fun u : ℝ => -π * u * (n : ℝ) ^ 2) atTop atBot := by
        have : Tendsto (fun u : ℝ => u * (π * (n : ℝ) ^ 2)) atTop atTop :=
          tendsto_id.atTop_mul_const (by positivity)
        refine (tendsto_neg_atTop_atBot.comp this).congr fun u => ?_
        simp only [Function.comp]
        ring
      exact Real.tendsto_exp_atBot.comp hlin
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu n
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h0 : 0 ≤ π * (n : ℝ) ^ 2 * (u - 1) :=
      mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) (sub_nonneg.mpr hu)
    exact Real.exp_le_exp.mpr (by nlinarith)

/-! ### The arithmetic `h⁰` -/

/-- **The arithmetic `h⁰` of the Arakelov divisor of degree `d` on `Spec ℤ`.** -/
def arithH0 (d : ℝ) : ℝ := Real.log (thetaSum (Real.exp (-2 * d)))

theorem exp_arithH0 (d : ℝ) : Real.exp (arithH0 d) = thetaSum (Real.exp (-2 * d)) :=
  Real.exp_log (thetaSum_pos (Real.exp_pos _))

/-- **Riemann–Roch for `Spec ℤ`**: `h⁰(d) − h⁰(−d) = d`. -/
theorem arithH0_riemannRoch (d : ℝ) : arithH0 d - arithH0 (-d) = d := by
  have hu : 0 < Real.exp (-2 * d) := Real.exp_pos _
  have hroot : (Real.exp (-2 * d) ^ (1 / 2 : ℝ))⁻¹ = Real.exp d := by
    rw [← Real.exp_mul, ← Real.exp_neg]
    congr 1
    ring
  have hinv : (Real.exp (-2 * d))⁻¹ = Real.exp (-2 * -d) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [arithH0, arithH0, thetaSum_inv hu, hroot, hinv,
    Real.log_mul (Real.exp_pos d).ne' (thetaSum_pos (Real.exp_pos _)).ne', Real.log_exp]
  ring

/-- `h⁰` is positive: the zero section is always there. -/
theorem arithH0_pos (d : ℝ) : 0 < arithH0 d := by
  have h1 := one_le_thetaSum (Real.exp_pos (-2 * d))
  have h2 : thetaSum (Real.exp (-2 * d)) ≠ 1 := by
    have := thetaSum_lt_thetaSum (Real.exp_pos (-2 * d))
      (show Real.exp (-2 * d) < Real.exp (-2 * d) + 1 by linarith)
    linarith [one_le_thetaSum (show 0 < Real.exp (-2 * d) + 1 by positivity)]
  exact Real.log_pos (lt_of_le_of_ne h1 (Ne.symm h2))

/-- `h⁰` is strictly increasing in the degree. -/
theorem arithH0_strictMono : StrictMono arithH0 := by
  intro d d' h
  refine Real.log_lt_log (thetaSum_pos (Real.exp_pos _)) ?_
  exact thetaSum_lt_thetaSum (Real.exp_pos _) (Real.exp_lt_exp.mpr (by linarith))

/-- **Vanishing in very negative degree**: `h⁰(d) → 0` as `d → −∞`. -/
theorem tendsto_arithH0_atBot : Tendsto arithH0 atBot (𝓝 0) := by
  have hexp : Tendsto (fun d : ℝ => Real.exp (-2 * d)) atBot atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    have : Tendsto (fun d : ℝ => d * (-2)) atBot atTop :=
      tendsto_id.atBot_mul_const_of_neg (by norm_num)
    exact this.congr fun d => mul_comm _ _
  have hlog : Tendsto Real.log (𝓝 1) (𝓝 0) := by
    simpa using (Real.continuousAt_log one_ne_zero).tendsto
  exact hlog.comp (tendsto_thetaSum_atTop.comp hexp)

/-- **Riemann–Roch asymptotics**: `h⁰(d) − d → 0` as `d → ∞`. -/
theorem tendsto_arithH0_sub_atTop : Tendsto (fun d => arithH0 d - d) atTop (𝓝 0) := by
  have h : (fun d => arithH0 d - d) = fun d => arithH0 (-d) := by
    funext d
    linarith [arithH0_riemannRoch d]
  rw [h]
  exact tendsto_arithH0_atBot.comp tendsto_neg_atTop_atBot

/-! ### The generating function of `h⁰` -/

/-- **The completed zeta function is the generating function of `h⁰`.** For `Re s > 1`,
`Λ(s) = π^{−s/2}Γ(s/2)ζ(s)` is half the Mellin transform at `s/2` of `e^{h⁰(−(log t)/2)} − 1`. -/
theorem completedRiemannZeta_eq_mellin_arithH0 {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s =
      mellin (fun t : ℝ => ((Real.exp (arithH0 (-Real.log t / 2)) : ℝ) : ℂ) - 1) (s / 2) / 2 := by
  have hs2 : 1 / 2 < (s / 2).re := by
    rw [Complex.div_ofNat_re]; linarith
  have hM := ((HurwitzZeta.hurwitzEvenFEPair 0).hasMellin hs2).2
  have hfun : ∀ t ∈ Set.Ioi (0 : ℝ), (HurwitzZeta.hurwitzEvenFEPair 0).f t -
      (HurwitzZeta.hurwitzEvenFEPair 0).f₀ = ((Real.exp (arithH0 (-Real.log t / 2)) : ℝ) : ℂ) - 1 := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have he : Real.exp (-2 * (-Real.log t / 2)) = t := by
      rw [show -2 * (-Real.log t / 2) = Real.log t by ring, Real.exp_log ht']
    show ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - (if (0 : UnitAddCircle) = 0 then 1 else 0) = _
    rw [if_pos rfl, exp_arithH0, he, thetaSum_eq_evenKernel ht']
  rw [completedRiemannZeta, HurwitzZeta.completedHurwitzZetaEven, ← hM]
  congr 1
  unfold mellin
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  dsimp only
  rw [hfun t ht]

/-! ### The pole plane -/

/-- The arithmetic `h⁰` of the fibre class `aH + bV`, `a, b > 0`: the sum of the `h⁰` of the
fibre degrees `log a` and `log b`. -/
def poleH0 (a b : ℝ) : ℝ := arithH0 (Real.log a) + arithH0 (Real.log b)

/-- **Riemann–Roch on the pole plane.** On every polar surface, for `D = aH + bV` with `a, b > 0`
and `D^∨ = a⁻¹H + b⁻¹V`: `h⁰(D) − h⁰(D^∨) = log(D²/2)`. -/
theorem poleH0_riemannRoch {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    poleH0 a b - poleH0 a⁻¹ b⁻¹ = Real.log (S.pair (a • S.H + b • S.V) (a • S.H + b • S.V) / 2) := by
  have hsq : S.pair (a • S.H + b • S.V) (a • S.H + b • S.V) = 2 * (a * b) := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_H_H, S.pair_V_V, S.pair_H_V, S.pair_comm S.V S.H]
    ring
  rw [hsq, mul_div_cancel_left₀ _ two_ne_zero, Real.log_mul ha.ne' hb.ne', poleH0, poleH0,
    Real.log_inv, Real.log_inv]
  linarith [arithH0_riemannRoch (Real.log a), arithH0_riemannRoch (Real.log b)]

end GaloisForLFunctions.ArithmeticOrientationGeometry

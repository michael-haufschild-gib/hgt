import GaloisForLFunctions.ArithmeticCriticalityTheory.ReflectedPrimeMassAsymptotics
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateSpanPlateauLaw
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateKernelBounds

/-!
# The pole-free Weil operator: the Doob source of every gauge

For a test profile `M` and its gauge `ω = M/Φ` put

    𝒲M(x) = Σ_n Λ(n) n^{−1/2} (M(x + log n) + M(x − log n))
              − ∫_0^∞ [2ν(u) M(x) − ω(u)(M(x+u) + M(x−u))] du + (γ + log π) M(x)

(`poleFreeWeilOperator`), `ω(u) = e^{−u/2}/(1 − e^{−2u})`, `ν(u) = e^{−2u}/(1 − e^{−2u})`. The harmonic
identity of Riemann's kernel reads `𝒲Φ = cosh(x/2)` (`poleFreeWeilOperator_riemannKernelReal`).

* **Exact source** (`twoSidedGenerator_profileGauge_sub_potential`). Whenever the prime sum and the
  archimedean integral of `M` converge at `x`,

      (𝓛_D ω)(x) − Φ(x) cosh(x/2) ω(x) = −Φ(x) 𝒲M(x).

  The harmonic identity absorbs the potential exactly: the Doob source of any gauge is `−Φ` times the
  pole-free Weil operator of its test profile.
* **Folding** (`foldedGenerator_eq_twoSidedGenerator_abs`). On `x ≥ 0` the folded generator of `ω` is
  the two-sided generator of `ω(|·|)`, so the folded source is `−Φ 𝒲(M(|·|))`
  (`foldedGenerator_profileGauge_sub_potential`): every reflected point is read with a plus sign.
* **Every positive profile fails at infinity**
  (`exists_infinity_window_profileGauge_foldedGenerator_lt_potential`). If `M ≥ 0` on `[0, ∞)`,
  `M(y₀) > 0` for some `y₀ > 0`, and `M`, `M'` are `O(e^{−8|y|})`, then `ω = M/Φ` is a strict folded
  subsolution on a half line `[X, ∞)`. In `𝒲(M(|·|))(x)` every prime term is nonnegative and only the
  archimedean second difference can be negative; it is local and `O(e^{−8x})`
  (`integral_profileArchTerm_abs_le`). A prime power `n` with `log n` just below `x − y₀` reads the
  profile back near `y₀` with weight `Λ(n) n^{−1/2} ≥ log 2 · e^{−(x − y₀)/2}`. The prime number
  theorem supplies such `n` for every large `x`; without it, each prime `p` alone forces failure at
  `x = log p + y₀` (`profileGauge_foldedGenerator_lt_potential_at_prime_shift`).

So the failure at infinity holds for every positive profile of exponential decay, not only on the
span of the shifted ground states: once the harmonic identity has absorbed the potential, the
obstruction is the positivity of the reflected prime atoms. Positive even profiles are strict
two-sided subsolutions on a half line
(`exists_infinity_window_even_profileGauge_twoSidedGenerator_lt_potential`).
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The operator -/

/-- The symmetrized archimedean integrand of a profile, `2ν(u)M(x) − ω(u)(M(x+u) + M(x−u))`;
for `M = Φ` it is `symArchTerm`. -/
def profileArchTerm (M : ℝ → ℝ) (x u : ℝ) : ℝ :=
  2 * archDiagonalDensity u * M x - archLevyDensity u * (M (x + u) + M (x - u))

/-- The symmetric prime shift sum `Σ_n Λ(n) n^{−1/2} (M(x + log n) + M(x − log n))`. -/
def profilePrimeSum (M : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * (M (x + Real.log n) + M (x - Real.log n))

/-- **The pole-free Weil operator** `𝒲M = (prime shift sum) − ∫_0^∞ profileArchTerm + (γ + log π) M`. -/
def poleFreeWeilOperator (M : ℝ → ℝ) (x : ℝ) : ℝ :=
  profilePrimeSum M x - (∫ u in Ioi (0 : ℝ), profileArchTerm M x u) + 2 * archConstantReal * M x

/-- The harmonic identity of Riemann's kernel: `𝒲Φ = cosh(x/2)`. -/
theorem poleFreeWeilOperator_riemannKernelReal (x : ℝ) :
    poleFreeWeilOperator riemannKernelReal x = Real.cosh (x / 2) := by
  have h := theta_harmonic_identity x
  change primeKernelSum x - (∫ u in Ioi (0 : ℝ), symArchTerm x u) +
    2 * archConstantReal * riemannKernelReal x = _
  linarith

/-! ### The exact source of a gauge -/

/-- The two-sided shift generator of `ω = M/Φ` in test coordinates. -/
theorem twoSidedShiftGenerator_profileGauge (M : ℝ → ℝ) (t x : ℝ) :
    twoSidedShiftGenerator (fun y => M y / riemannKernelReal y) t x =
      M x * (riemannKernelReal (x + t) + riemannKernelReal (x - t)) -
        riemannKernelReal x * (M (x + t) + M (x - t)) := by
  unfold twoSidedShiftGenerator
  have h0 := (riemannKernelReal_pos x).ne'
  have h1 := (riemannKernelReal_pos (x + t)).ne'
  have h2 := (riemannKernelReal_pos (x - t)).ne'
  field_simp
  ring

/-- **Exact source of every gauge.** If the prime shift sum of `M` converges at `x` and its
archimedean integrand is integrable, then `(𝓛_D ω)(x) − Φ(x) cosh(x/2) ω(x) = −Φ(x) 𝒲M(x)` for
`ω = M/Φ`. -/
theorem twoSidedGenerator_profileGauge_sub_potential {M : ℝ → ℝ} {x : ℝ}
    (hP : Summable fun n : ℕ => vonMangoldtAtom n * (M (x + Real.log n) + M (x - Real.log n)))
    (hA : IntegrableOn (profileArchTerm M x) (Ioi 0)) :
    twoSidedGenerator (fun y => M y / riemannKernelReal y) x -
        riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x) =
      -(riemannKernelReal x * poleFreeWeilOperator M x) := by
  have harch : (∫ u in Ioi (0 : ℝ), archLevyDensity u *
      twoSidedShiftGenerator (fun y => M y / riemannKernelReal y) u x) =
      -(M x * (∫ u in Ioi (0 : ℝ), symArchTerm x u) -
        riemannKernelReal x * ∫ u in Ioi (0 : ℝ), profileArchTerm M x u) := by
    have h1 : (∫ u in Ioi (0 : ℝ), archLevyDensity u *
        twoSidedShiftGenerator (fun y => M y / riemannKernelReal y) u x) =
        ∫ u in Ioi (0 : ℝ), -(M x * symArchTerm x u - riemannKernelReal x * profileArchTerm M x u) :=
      setIntegral_congr_fun measurableSet_Ioi fun u _ => by
        rw [twoSidedShiftGenerator_profileGauge]
        unfold symArchTerm profileArchTerm
        ring
    have hS : IntegrableOn (fun u => M x * symArchTerm x u) (Ioi 0) :=
      (integrableOn_symArchTerm x).const_mul _
    have hT : IntegrableOn (fun u => riemannKernelReal x * profileArchTerm M x u) (Ioi 0) :=
      hA.const_mul _
    rw [h1, integral_neg, integral_sub hS hT, integral_const_mul, integral_const_mul]
  have hprime : (∑' n : ℕ, vonMangoldtAtom n *
      twoSidedShiftGenerator (fun y => M y / riemannKernelReal y) (Real.log n) x) =
      M x * primeKernelSum x - riemannKernelReal x * profilePrimeSum M x := by
    have e : (fun n : ℕ => vonMangoldtAtom n *
        twoSidedShiftGenerator (fun y => M y / riemannKernelReal y) (Real.log n) x) =
        fun n => M x * (vonMangoldtAtom n * (riemannKernelReal (x + Real.log n) +
          riemannKernelReal (x - Real.log n))) - riemannKernelReal x *
          (vonMangoldtAtom n * (M (x + Real.log n) + M (x - Real.log n))) := by
      funext n
      rw [twoSidedShiftGenerator_profileGauge]
      ring
    rw [e, ((summable_primeKernelSum x).mul_left _).tsum_sub (hP.mul_left _), tsum_mul_left,
      tsum_mul_left]
    rfl
  have hpot : riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x) =
      Real.cosh (x / 2) * M x := by
    have := (riemannKernelReal_pos x).ne'
    field_simp
  unfold twoSidedGenerator poleFreeWeilOperator
  rw [harch, hprime, theta_harmonic_identity x, hpot]
  ring

/-- On `x ≥ 0` the folded generator of `ω` is the two-sided generator of `ω(|·|)`. -/
theorem foldedGenerator_eq_twoSidedGenerator_abs (ω : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    foldedGenerator ω x = twoSidedGenerator (fun y => ω |y|) x := by
  have key : ∀ t, 0 ≤ t →
      foldedShiftGenerator ω t x = twoSidedShiftGenerator (fun y => ω |y|) t x := by
    intro t ht
    unfold foldedShiftGenerator twoSidedShiftGenerator
    simp only [abs_of_nonneg hx, abs_of_nonneg (by linarith : 0 ≤ x + t)]
  unfold foldedGenerator twoSidedGenerator
  congr 1
  · exact setIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [key t (le_of_lt ht)]
  · exact tsum_congr fun n => by rw [key _ (Real.log_natCast_nonneg n)]

/-- **Exact folded source.** For `x ≥ 0`, `(𝓛_N ω)(x) − Φ(x) cosh(x/2) ω(x) = −Φ(x) 𝒲(M(|·|))(x)`
for `ω = M/Φ`. -/
theorem foldedGenerator_profileGauge_sub_potential {M : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (hP : Summable fun n : ℕ => vonMangoldtAtom n * (M (|x + Real.log n|) + M (|x - Real.log n|)))
    (hA : IntegrableOn (profileArchTerm (fun y => M (|y|)) x) (Ioi 0)) :
    foldedGenerator (fun y => M y / riemannKernelReal y) x -
        riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x) =
      -(riemannKernelReal x * poleFreeWeilOperator (fun y => M (|y|)) x) := by
  have e : (fun y => (fun y => M y / riemannKernelReal y) |y|) =
      fun y => (fun y => M (|y|)) y / riemannKernelReal y := by
    funext y
    simp only [riemannKernelReal_abs']
  rw [foldedGenerator_eq_twoSidedGenerator_abs _ hx, e]
  have h := twoSidedGenerator_profileGauge_sub_potential (M := fun y => M (|y|)) (x := x) hP hA
  rw [abs_of_nonneg hx] at h
  exact h

/-! ### Profiles of exponential decay -/

theorem archDiagonalDensity_eq (u : ℝ) :
    archDiagonalDensity u = archLevyDensity u * Real.exp (-(3 / 2 * u)) := by
  unfold archDiagonalDensity archLevyDensity
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  ring

theorem archDiagonalDensity_le {u : ℝ} (hu : 0 < u) : archDiagonalDensity u ≤ archLevyDensity u := by
  rw [archDiagonalDensity_eq]
  exact mul_le_of_le_one_right (archLevyDensity_pos hu).le
    (Real.exp_le_one_iff.mpr (by linarith))

/-- The archimedean integrand of a Lipschitz profile is `O(u ω(u))`: the singular parts of the
two densities cancel against the second difference. -/
theorem abs_profileArchTerm_le {f : ℝ → ℝ} {K : ℝ} (hf : ∀ a b, |f a - f b| ≤ K * |a - b|)
    (x : ℝ) {u : ℝ} (hu : 0 < u) :
    |profileArchTerm f x u| ≤ (2 * K + 3 * |f x|) * (archLevyDensity u * u) := by
  have hω := archLevyDensity_pos hu
  have e : profileArchTerm f x u = -(archLevyDensity u * ((f (x + u) - f x) + (f (x - u) - f x) +
      2 * (1 - Real.exp (-(3 / 2 * u))) * f x)) := by
    unfold profileArchTerm
    rw [archDiagonalDensity_eq]
    ring
  have h1 := hf (x + u) x
  have h2 := hf (x - u) x
  rw [show x + u - x = u by ring, abs_of_pos hu] at h1
  rw [show x - u - x = -u by ring, abs_neg, abs_of_pos hu] at h2
  have h3 : 1 - Real.exp (-(3 / 2 * u)) ≤ 3 / 2 * u := by
    have := Real.add_one_le_exp (-(3 / 2 * u))
    linarith
  have h4 : 0 ≤ 1 - Real.exp (-(3 / 2 * u)) := by
    have := Real.exp_le_one_iff.mpr (by linarith : -(3 / 2 * u) ≤ 0)
    linarith
  have hin : |(f (x + u) - f x) + (f (x - u) - f x) + 2 * (1 - Real.exp (-(3 / 2 * u))) * f x| ≤
      (2 * K + 3 * |f x|) * u := by
    have h5 : |2 * (1 - Real.exp (-(3 / 2 * u))) * f x| ≤ 3 * u * |f x| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg h4]
      nlinarith [abs_nonneg (f x)]
    calc _ ≤ |f (x + u) - f x| + |f (x - u) - f x| + |2 * (1 - Real.exp (-(3 / 2 * u))) * f x| :=
          abs_add_three _ _ _
      _ ≤ K * u + K * u + 3 * u * |f x| := by linarith
      _ = _ := by ring
  rw [e, abs_neg, abs_mul, abs_of_pos hω]
  calc archLevyDensity u * |(f (x + u) - f x) + (f (x - u) - f x) +
        2 * (1 - Real.exp (-(3 / 2 * u))) * f x|
      ≤ archLevyDensity u * ((2 * K + 3 * |f x|) * u) := mul_le_mul_of_nonneg_left hin hω.le
    _ = _ := by ring

theorem integrableOn_profileArchTerm {f : ℝ → ℝ} {K : ℝ} (hfc : Continuous f)
    (hf : ∀ a b, |f a - f b| ≤ K * |a - b|) (x : ℝ) :
    IntegrableOn (profileArchTerm f x) (Ioi 0) := by
  refine (integrableOn_archLevyDensity_mul_id.const_mul (2 * K + 3 * |f x|)).mono' ?_ ?_
  · have hfm := hfc.measurable
    have : Measurable (profileArchTerm f x) := by
      unfold profileArchTerm archDiagonalDensity
      exact ((measurable_const.mul (by fun_prop)).mul measurable_const).sub
        (measurable_archLevyDensity.mul ((hfm.comp (measurable_const.add measurable_id)).add
          (hfm.comp (measurable_const.sub measurable_id))))
    exact this.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs]
    exact abs_profileArchTerm_le hf x hu

theorem summable_atom_mul_profileShift {f : ℝ → ℝ} {C : ℝ}
    (hdec : ∀ y, |f y| ≤ C * Real.exp (-(8 * |y|))) (x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * (f (x + Real.log n) + f (x - Real.log n)) := by
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (hdec 0)
    rwa [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
  refine Summable.of_norm_bounded
    (summable_atom_mul_exp_neg_eight_log.mul_left (2 * C * Real.exp (8 * |x|))) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg n)]
  have h1 := (hdec (x + Real.log n)).trans
    (mul_le_mul_of_nonneg_left (exp_neg_eight_mul_abs_add_log_le x n) hC0)
  have hab : |x - Real.log n| = |-x + Real.log n| := by rw [← abs_neg]; ring_nf
  have h2 := (hdec (x - Real.log n)).trans (by
    rw [hab]
    exact mul_le_mul_of_nonneg_left (exp_neg_eight_mul_abs_add_log_le (-x) n) hC0)
  rw [abs_neg] at h2
  have hsum := abs_add_le (f (x + Real.log n)) (f (x - Real.log n))
  have hatom := vonMangoldtAtom_nonneg n
  calc vonMangoldtAtom n * |f (x + Real.log n) + f (x - Real.log n)|
      ≤ vonMangoldtAtom n * (2 * (C * (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))))) :=
        mul_le_mul_of_nonneg_left (by linarith) hatom
    _ = _ := by ring

/-- A profile whose derivative is `O(e^{−8|y|})` is Lipschitz on `[x − 1, x + 1]` with constant
`C e^{−8(x−1)}` for `x ≥ 1`. -/
theorem abs_sub_le_of_deriv_decay {M : ℝ → ℝ} {C : ℝ} (hM : Differentiable ℝ M)
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|))) {x a b : ℝ}
    (ha : a ∈ Icc (x - 1) (x + 1)) (hb : b ∈ Icc (x - 1) (x + 1)) :
    |M b - M a| ≤ C * Real.exp (-(8 * (x - 1))) * |b - a| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := M) (s := Icc (x - 1) (x + 1))
    (C := C * Real.exp (-(8 * (x - 1)))) (fun y _ => hM y) (fun y hy => ?_) (convex_Icc _ _) ha hb
  · simpa only [Real.norm_eq_abs] using h
  · rw [Real.norm_eq_abs]
    refine (hdec' y).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ?_)
    · have : x - 1 ≤ |y| := le_trans hy.1 (le_abs_self y)
      linarith
    · have := (abs_nonneg _).trans (hdec' y)
      exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)

/-- **The archimedean part is local.** For a nonnegative profile on `[0, ∞)` with
`|M|, |M'| ≤ Ce^{−8|y|}` and `x ≥ 1`, the archimedean integral of `M(|·|)` at `x` is at most
`2C(e⁸ + 1) J e^{−8x}`, `J = ∫_0^∞ ω(u) u du`. -/
theorem integral_profileArchTerm_abs_le {M : ℝ → ℝ} {C : ℝ} (hM : Differentiable ℝ M)
    (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|)))
    (hnn : ∀ y, 0 ≤ y → 0 ≤ M y) {x : ℝ} (hx : 1 ≤ x) :
    (∫ u in Ioi (0 : ℝ), profileArchTerm (fun y => M (|y|)) x u) ≤
      2 * C * (Real.exp 8 + 1) * (∫ u in Ioi (0 : ℝ), archLevyDensity u * u) *
        Real.exp (-(8 * x)) := by
  have hx0 : 0 ≤ x := by linarith
  have hMx : M x ≤ C * Real.exp (-(8 * x)) := by
    have := (le_abs_self _).trans (hdec x)
    rwa [abs_of_nonneg hx0] at this
  have hMx0 := hnn x hx0
  have hK : C * Real.exp (-(8 * (x - 1))) = C * Real.exp 8 * Real.exp (-(8 * x)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hLip : ∀ a b, |M (|a|) - M (|b|)| ≤ C * |a - b| := by
    intro a b
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := M) (s := univ) (C := C)
      (fun y _ => hM y) (fun y _ => by
        rw [Real.norm_eq_abs]
        refine (hdec' y).trans (mul_le_of_le_one_right ?_ ?_)
        · have := (abs_nonneg _).trans (hdec' y)
          exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
        · exact Real.exp_le_one_iff.mpr (by linarith [abs_nonneg y]))
      convex_univ (mem_univ |b|) (mem_univ |a|)
    simp only [Real.norm_eq_abs] at h
    have hC0 : 0 ≤ C := by
      have := (abs_nonneg _).trans (hdec 0)
      rwa [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
    exact h.trans (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub a b) hC0)
  have hint := integrableOn_profileArchTerm (f := fun y => M (|y|))
    (hM.continuous.comp continuous_abs) hLip x
  set B := 2 * C * (Real.exp 8 + 1) * Real.exp (-(8 * x)) with hB
  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      profileArchTerm (fun y => M (|y|)) x u ≤ B * (archLevyDensity u * u) := by
    intro u hu
    have hu0 : 0 < u := hu
    have hω := archLevyDensity_pos hu0
    have hν := archDiagonalDensity_le hu0
    have hνx : 2 * archDiagonalDensity u * M x ≤ 2 * archLevyDensity u * M x := by nlinarith
    unfold profileArchTerm
    simp only [abs_of_nonneg hx0]
    rcases le_or_gt u 1 with hu1 | hu1
    · have hxp : 0 ≤ x + u := by linarith
      have hxm : 0 ≤ x - u := by linarith
      rw [abs_of_nonneg hxp, abs_of_nonneg hxm]
      have hmem : x ∈ Icc (x - 1) (x + 1) := ⟨by linarith, by linarith⟩
      have e1 := abs_sub_le_of_deriv_decay hM hdec' hmem
        (⟨by linarith, by linarith⟩ : x + u ∈ Icc (x - 1) (x + 1))
      have e2 := abs_sub_le_of_deriv_decay hM hdec' hmem
        (⟨by linarith, by linarith⟩ : x - u ∈ Icc (x - 1) (x + 1))
      rw [show x + u - x = u by ring, abs_of_pos hu0, hK] at e1
      rw [show x - u - x = -u by ring, abs_neg, abs_of_pos hu0, hK] at e2
      have l1 := neg_abs_le (M (x + u) - M x)
      have l2 := neg_abs_le (M (x - u) - M x)
      have hJ : archLevyDensity u * (2 * M x - M (x + u) - M (x - u)) ≤
          archLevyDensity u * (2 * (C * Real.exp 8 * Real.exp (-(8 * x))) * u) :=
        mul_le_mul_of_nonneg_left (by linarith) hω.le
      have hexp : 0 ≤ C * Real.exp (-(8 * x)) := le_trans hMx0 hMx
      have hfin : archLevyDensity u * (2 * (C * Real.exp 8 * Real.exp (-(8 * x))) * u) ≤
          B * (archLevyDensity u * u) := by
        rw [hB]
        have : 0 ≤ archLevyDensity u * u := by positivity
        nlinarith
      nlinarith
    · have hp := hnn |x + u| (abs_nonneg _)
      have hm := hnn |x - u| (abs_nonneg _)
      have hexp : 0 ≤ C * Real.exp (-(8 * x)) := le_trans hMx0 hMx
      have h1 : 2 * archLevyDensity u * M x ≤ B * (archLevyDensity u * u) := by
        rw [hB]
        have hωu : archLevyDensity u ≤ archLevyDensity u * u := by nlinarith
        have h8 : 0 ≤ Real.exp 8 * (C * Real.exp (-(8 * x))) := by positivity
        nlinarith
      nlinarith [mul_nonneg hω.le (add_nonneg hp hm)]
  have hrhs : IntegrableOn (fun u => B * (archLevyDensity u * u)) (Ioi 0) :=
    integrableOn_archLevyDensity_mul_id.const_mul B
  calc (∫ u in Ioi (0 : ℝ), profileArchTerm (fun y => M (|y|)) x u)
      ≤ ∫ u in Ioi (0 : ℝ), B * (archLevyDensity u * u) :=
        setIntegral_mono_on hint hrhs measurableSet_Ioi hpt
    _ = _ := by rw [integral_const_mul, hB]; ring

/-- **Lower bound by a single reflected atom.** For `x ≥ 1` and every `n`,
`𝒲(M(|·|))(x) ≥ Λ(n) n^{−1/2} M(|x − log n|) − 2C(e⁸ + 1) J e^{−8x}`. -/
theorem poleFreeWeilOperator_abs_ge {M : ℝ → ℝ} {C : ℝ} (hM : Differentiable ℝ M)
    (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|)))
    (hnn : ∀ y, 0 ≤ y → 0 ≤ M y) {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    vonMangoldtAtom n * M (|x - Real.log n|) -
        2 * C * (Real.exp 8 + 1) * (∫ u in Ioi (0 : ℝ), archLevyDensity u * u) *
          Real.exp (-(8 * x)) ≤
      poleFreeWeilOperator (fun y => M (|y|)) x := by
  have hdecA : ∀ y, |M (|y|)| ≤ C * Real.exp (-(8 * |y|)) := fun y => by
    simpa only [abs_abs] using hdec |y|
  have hS := summable_atom_mul_profileShift hdecA x
  have hterm : vonMangoldtAtom n * M (|x - Real.log n|) ≤ profilePrimeSum (fun y => M (|y|)) x := by
    have hle := hS.le_tsum n fun m _ =>
      mul_nonneg (vonMangoldtAtom_nonneg m) (add_nonneg (hnn _ (abs_nonneg _)) (hnn _ (abs_nonneg _)))
    have hp := hnn |x + Real.log n| (abs_nonneg _)
    have ha := vonMangoldtAtom_nonneg n
    unfold profilePrimeSum
    nlinarith
  have hA := integral_profileArchTerm_abs_le hM hdec hdec' hnn hx
  have hc : 0 < archConstantReal := by
    unfold archConstantReal
    have := Real.one_half_lt_eulerMascheroniConstant
    have := Real.log_pos (by linarith [Real.pi_gt_three] : (1 : ℝ) < Real.pi)
    linarith
  have hMx := hnn |x| (abs_nonneg _)
  unfold poleFreeWeilOperator
  nlinarith [mul_nonneg hc.le hMx]

/-! ### Failure at infinity -/

theorem log_two_le_vonMangoldt_of_pos {n : ℕ} (h : 0 < (ArithmeticFunction.vonMangoldt n : ℝ)) :
    Real.log 2 ≤ ArithmeticFunction.vonMangoldt n := by
  rw [ArithmeticFunction.vonMangoldt_apply] at h ⊢
  split_ifs with hpp
  · exact Real.log_le_log (by norm_num) (by exact_mod_cast (Nat.minFac_prime hpp.ne_one).two_le)
  · rw [if_neg hpp] at h
    exact absurd h (lt_irrefl 0)

/-- **Prime powers in every multiplicative window** (prime number theorem). For every `δ > 0`, every
large `y` has some `n ∈ (y, e^δ y]` with `Λ(n) > 0`. -/
theorem exists_vonMangoldt_pos_mem_window {δ : ℝ} (hδ : 0 < δ) :
    ∃ Y : ℝ, ∀ y, Y ≤ y → ∃ n : ℕ, y < n ∧ (n : ℝ) ≤ Real.exp δ * y ∧
      0 < (ArithmeticFunction.vonMangoldt n : ℝ) := by
  set r := Real.exp δ with hr
  have hr1 : 1 < r := Real.one_lt_exp_iff.mpr hδ
  have hlo : (1 + r) / (2 * r) < (3 * r + 1) / (4 * r) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hlo1 : (3 * r + 1) / (4 * r) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hb1 : 1 < (1 + r) / 2 := by linarith
  have hev := tendsto_psiSum_div.eventually
    (Ioo_mem_nhds hlo1 hb1)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  refine ⟨max T 1, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) hy
  have hyT : T ≤ y := le_trans (le_max_left _ _) hy
  have hy0 : 0 < y := by linarith
  have hryT : T ≤ r * y := le_trans hyT (by nlinarith)
  have h1 := (hT (r * y) hryT).1
  have h2 := (hT y hyT).2
  rw [lt_div_iff₀ (by positivity)] at h1
  rw [div_lt_iff₀ hy0] at h2
  have hgt : psiSum y < psiSum (r * y) := by
    have : (1 + r) / 2 * y < (3 * r + 1) / (4 * r) * (r * y) := by
      rw [show (3 * r + 1) / (4 * r) * (r * y) = (3 * r + 1) / 4 * y by
        field_simp]
      nlinarith
    linarith
  by_contra hno
  simp only [not_exists, not_and, not_lt] at hno
  apply absurd hgt
  apply not_lt.mpr (le_of_eq _)
  unfold psiSum
  symm
  refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor (by nlinarith)))
    fun k hk hk' => ?_
  have hk1 : (k : ℝ) ≤ r * y := (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Icc.mp hk).2
  have hk2 : y < k := by
    refine Nat.lt_of_floor_lt ?_
    by_contra hle
    exact hk' (Finset.mem_Icc.mpr ⟨Nat.zero_le _, not_lt.mp hle⟩)
  exact le_antisymm (hno k hk2 hk1) ArithmeticFunction.vonMangoldt_nonneg

/-- **Every positive profile is a strict folded subsolution at infinity.** If `M` is differentiable,
`|M|, |M'| ≤ C e^{−8|y|}`, `M ≥ 0` on `[0, ∞)` and `M(y₀) > 0` for some `y₀ > 0`, then the gauge
`ω = M/Φ` satisfies `(𝓛_N ω)(x) < Φ(x) cosh(x/2) ω(x)` for all `x` in a half line `[X, ∞)`. -/
theorem exists_infinity_window_profileGauge_foldedGenerator_lt_potential {M : ℝ → ℝ} {C : ℝ}
    (hM : Differentiable ℝ M) (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|)))
    (hnn : ∀ y, 0 ≤ y → 0 ≤ M y) {y₀ : ℝ} (hy₀ : 0 < y₀) (hM₀ : 0 < M y₀) :
    ∃ X : ℝ, ∀ x, X ≤ x →
      foldedGenerator (fun y => M y / riemannKernelReal y) x <
        riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x) := by
  -- `M > M(y₀)/2` on `(y₀ − δ, y₀ + δ)`
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp (hM.continuous.continuousAt (x := y₀))
    (M y₀ / 2) (by linarith)
  have hnear : ∀ y, y₀ ≤ y → y < y₀ + δ → M y₀ / 2 < M y := fun y h1 h2 => by
    have := hball (show dist y y₀ < δ by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
    rw [Real.dist_eq] at this
    linarith [neg_abs_le (M y - M y₀)]
  obtain ⟨Y, hY⟩ := exists_vonMangoldt_pos_mem_window (half_pos hδ)
  set J := ∫ u in Ioi (0 : ℝ), archLevyDensity u * u with hJdef
  set B := 2 * C * (Real.exp 8 + 1) * J with hBdef
  set c₀ := Real.log 2 * (M y₀ / 2) * Real.exp (y₀ / 2) with hc₀
  have hc₀pos : 0 < c₀ := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  refine ⟨max (max 1 (y₀ + δ / 2 + Real.log (max Y 1))) (B / c₀), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxY : y₀ + δ / 2 + Real.log (max Y 1) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxB : B / c₀ ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 ≤ x := by linarith
  -- the window
  set y := Real.exp (x - y₀ - δ / 2) with hy
  have hyY : max Y 1 ≤ y := by
    rw [hy, ← Real.exp_log (lt_of_lt_of_le one_pos (le_max_right Y 1))]
    exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨n, hn1, hn2, hΛ⟩ := hY y (le_trans (le_max_left _ _) hyY)
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) hyY
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog1 : x - y₀ - δ / 2 < Real.log n := by
    rw [← Real.log_exp (x - y₀ - δ / 2)]
    exact Real.log_lt_log (Real.exp_pos _) hn1
  have hlog2 : Real.log n ≤ x - y₀ := by
    have := Real.log_le_log hn0 hn2
    rwa [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp,
      show δ / 2 + (x - y₀ - δ / 2) = x - y₀ by ring] at this
  have hdist : |x - Real.log n| = x - Real.log n := abs_of_nonneg (by linarith)
  have hMn : M y₀ / 2 < M (|x - Real.log n|) := by
    rw [hdist]
    exact hnear _ (by linarith) (by linarith)
  -- the reflected atom
  have hn2' : 2 ≤ n := by
    have : (1 : ℝ) < n := by linarith
    exact_mod_cast this
  have hatom : Real.log 2 * Real.exp (-((x - y₀) / 2)) ≤ vonMangoldtAtom n := by
    unfold vonMangoldtAtom
    rw [if_pos hn2']
    have hsq : Real.sqrt n ≤ Real.exp ((x - y₀) / 2) := by
      rw [show Real.exp ((x - y₀) / 2) = Real.sqrt (Real.exp (x - y₀)) by
        rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; ring_nf]
      exact Real.sqrt_le_sqrt (by
        have := Real.exp_log hn0
        rw [← this]; exact Real.exp_le_exp.mpr hlog2)
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (Real.sqrt_pos.mpr hn0)]
    exact mul_le_mul (log_two_le_vonMangoldt_of_pos hΛ) hsq (Real.sqrt_nonneg _)
      (le_trans (Real.log_nonneg (by norm_num)) (log_two_le_vonMangoldt_of_pos hΛ))
  have hW := poleFreeWeilOperator_abs_ge hM hdec hdec' hnn hx1 n
  rw [← hJdef, ← hBdef] at hW
  -- positivity of the Weil operator
  have hpos : 0 < poleFreeWeilOperator (fun y => M (|y|)) x := by
    have hprod : c₀ * Real.exp (-(x / 2)) ≤ vonMangoldtAtom n * M (|x - Real.log n|) := by
      have h1 : c₀ * Real.exp (-(x / 2)) =
          (Real.log 2 * Real.exp (-((x - y₀) / 2))) * (M y₀ / 2) := by
        rw [hc₀, show -((x - y₀) / 2) = y₀ / 2 + -(x / 2) by ring, Real.exp_add]
        ring
      rw [h1]
      exact mul_le_mul hatom hMn.le (by linarith) (vonMangoldtAtom_nonneg n)
    have hsmall : B * Real.exp (-(8 * x)) < c₀ * Real.exp (-(x / 2)) := by
      have hsplit : Real.exp (-(8 * x)) = Real.exp (-(x / 2)) * Real.exp (-(15 / 2 * x)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hlin : 15 / 2 * x + 1 ≤ Real.exp (15 / 2 * x) := Real.add_one_le_exp _
      have hBc : B < c₀ * (15 / 2 * x + 1) := by
        rw [div_le_iff₀ hc₀pos] at hxB
        nlinarith
      have hBexp : B * Real.exp (-(15 / 2 * x)) < c₀ := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
        nlinarith
      rw [hsplit, show B * (Real.exp (-(x / 2)) * Real.exp (-(15 / 2 * x))) =
        (B * Real.exp (-(15 / 2 * x))) * Real.exp (-(x / 2)) by ring]
      exact mul_lt_mul_of_pos_right hBexp (Real.exp_pos _)
    linarith
  -- the folded source
  have hdecA : ∀ y, |M (|y|)| ≤ C * Real.exp (-(8 * |y|)) := fun y => by
    simpa only [abs_abs] using hdec |y|
  have hP := summable_atom_mul_profileShift hdecA x
  have hLip : ∀ a b, |M (|a|) - M (|b|)| ≤ C * |a - b| := by
    intro a b
    have hC0 : 0 ≤ C := by
      have := (abs_nonneg _).trans (hdec 0)
      rwa [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := M) (s := univ) (C := C)
      (fun y _ => hM y) (fun y _ => by
        rw [Real.norm_eq_abs]
        exact (hdec' y).trans (mul_le_of_le_one_right hC0
          (Real.exp_le_one_iff.mpr (by linarith [abs_nonneg y]))))
      convex_univ (mem_univ |b|) (mem_univ |a|)
    simp only [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub a b) hC0)
  have hA := integrableOn_profileArchTerm (f := fun y => M (|y|)) (hM.continuous.comp continuous_abs)
    hLip x
  have hsrc := foldedGenerator_profileGauge_sub_potential hx0 hP hA
  have hΦ := riemannKernelReal_pos x
  nlinarith [mul_pos hΦ hpos]

/-- **Without the prime number theorem: every large prime forces failure.** Under the hypotheses of
`exists_infinity_window_profileGauge_foldedGenerator_lt_potential`, the gauge `M/Φ` is a strict
folded subsolution at `log p + y₀` for every prime `p ≥ N`: the reflected atom of `p` reads the
profile back at `y₀`. -/
theorem profileGauge_foldedGenerator_lt_potential_at_prime_shift {M : ℝ → ℝ} {C : ℝ}
    (hM : Differentiable ℝ M) (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|)))
    (hnn : ∀ y, 0 ≤ y → 0 ≤ M y) {y₀ : ℝ} (hy₀ : 0 < y₀) (hM₀ : 0 < M y₀) :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p →
      foldedGenerator (fun y => M y / riemannKernelReal y) (Real.log p + y₀) <
        riemannKernelReal (Real.log p + y₀) * Real.cosh ((Real.log p + y₀) / 2) *
          (M (Real.log p + y₀) / riemannKernelReal (Real.log p + y₀)) := by
  set J := ∫ u in Ioi (0 : ℝ), archLevyDensity u * u with hJdef
  set B := 2 * C * (Real.exp 8 + 1) * J with hBdef
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  refine ⟨max 3 (⌈B / (Real.log 2 * M y₀)⌉₊ + 1), fun p hp hpN => ?_⟩
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast le_trans (le_max_left _ _) hpN
  have hpB : B / (Real.log 2 * M y₀) < p := by
    have h1 := Nat.le_ceil (B / (Real.log 2 * M y₀))
    have h2 : ((⌈B / (Real.log 2 * M y₀)⌉₊ + 1 : ℕ) : ℝ) ≤ p := by
      exact_mod_cast le_trans (le_max_right _ _) hpN
    push_cast at h2
    linarith
  have hp0 : (0 : ℝ) < p := by linarith
  set x := Real.log p + y₀ with hxdef
  have hlog3 : 1 < Real.log p := by
    have : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      norm_num at this ⊢
      linarith
    exact lt_of_lt_of_le this (Real.log_le_log (by norm_num) hp3)
  have hx1 : 1 ≤ x := by rw [hxdef]; linarith
  have hx0 : 0 ≤ x := by linarith
  have hW := poleFreeWeilOperator_abs_ge hM hdec hdec' hnn hx1 p
  rw [show x - Real.log p = y₀ by rw [hxdef]; ring, abs_of_pos hy₀, ← hJdef, ← hBdef] at hW
  have hatom : vonMangoldtAtom p = Real.log p / Real.sqrt p := by
    unfold vonMangoldtAtom
    rw [if_pos hp.two_le, ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hsq : Real.sqrt p ≤ p := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hsqpos : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hexp : Real.exp (-(8 * x)) ≤ 1 / ((p : ℝ) * p) := by
    have h1 : Real.exp (-(8 * x)) ≤ Real.exp (-(2 * Real.log p)) :=
      Real.exp_le_exp.mpr (by rw [hxdef]; linarith)
    have h2 : Real.exp (-(2 * Real.log p)) = 1 / ((p : ℝ) * p) := by
      rw [Real.exp_neg, show 2 * Real.log p = Real.log p + Real.log p by ring, Real.exp_add,
        Real.exp_log hp0]
      ring
    linarith
  have hpos : 0 < poleFreeWeilOperator (fun y => M (|y|)) x := by
    have hlogp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by linarith)
    have hB : B < Real.log 2 * M y₀ * p := by
      rw [div_lt_iff₀ (by positivity)] at hpB
      linarith
    have hgain : B * Real.exp (-(8 * x)) < Real.log p / Real.sqrt p * M y₀ := by
      have hB0 : B * Real.exp (-(8 * x)) ≤ max B 0 * (1 / ((p : ℝ) * p)) := by
        calc B * Real.exp (-(8 * x)) ≤ max B 0 * Real.exp (-(8 * x)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
          _ ≤ _ := mul_le_mul_of_nonneg_left hexp (le_max_right _ _)
      have hmax : max B 0 < Real.log 2 * M y₀ * p := max_lt hB (by positivity)
      have hfin : max B 0 * (1 / ((p : ℝ) * p)) < Real.log p / Real.sqrt p * M y₀ := by
        rw [div_mul_eq_mul_div, lt_div_iff₀ hsqpos]
        have h1 : max B 0 * (1 / ((p : ℝ) * p)) * Real.sqrt p ≤ max B 0 * (1 / (p : ℝ)) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hp0]
          nlinarith
        have h2 : max B 0 * (1 / (p : ℝ)) < Real.log p * M y₀ := by
          rw [mul_one_div, div_lt_iff₀ hp0]
          nlinarith
        linarith
      linarith
    have hl := hW
    rw [hatom] at hl
    linarith
  have hdecA : ∀ y, |M (|y|)| ≤ C * Real.exp (-(8 * |y|)) := fun y => by
    simpa only [abs_abs] using hdec |y|
  have hP := summable_atom_mul_profileShift hdecA x
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (hdec 0)
    rwa [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
  have hLip : ∀ a b, |M (|a|) - M (|b|)| ≤ C * |a - b| := by
    intro a b
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := M) (s := univ) (C := C)
      (fun y _ => hM y) (fun y _ => by
        rw [Real.norm_eq_abs]
        exact (hdec' y).trans (mul_le_of_le_one_right hC0
          (Real.exp_le_one_iff.mpr (by linarith [abs_nonneg y]))))
      convex_univ (mem_univ |b|) (mem_univ |a|)
    simp only [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub a b) hC0)
  have hA := integrableOn_profileArchTerm (f := fun y => M (|y|)) (hM.continuous.comp continuous_abs)
    hLip x
  have hsrc := foldedGenerator_profileGauge_sub_potential hx0 hP hA
  have hΦ := riemannKernelReal_pos x
  nlinarith [mul_pos hΦ hpos]

/-- **Positive even profiles are strict two-sided subsolutions at infinity.** For an even `M ≥ 0`
with `M(y₀) > 0` and `|M|, |M'| ≤ Ce^{−8|y|}`, `(𝓛_D ω)(x) < Φ(x) cosh(x/2) ω(x)` on a half line. -/
theorem exists_infinity_window_even_profileGauge_twoSidedGenerator_lt_potential {M : ℝ → ℝ} {C : ℝ}
    (hM : Differentiable ℝ M) (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))
    (hdec' : ∀ y, |deriv M y| ≤ C * Real.exp (-(8 * |y|))) (hev : ∀ y, M (-y) = M y)
    (hnn : ∀ y, 0 ≤ y → 0 ≤ M y) {y₀ : ℝ} (hy₀ : 0 < y₀) (hM₀ : 0 < M y₀) :
    ∃ X : ℝ, ∀ x, X ≤ x →
      twoSidedGenerator (fun y => M y / riemannKernelReal y) x <
        riemannKernelReal x * Real.cosh (x / 2) * (M x / riemannKernelReal x) := by
  obtain ⟨X, hX⟩ :=
    exists_infinity_window_profileGauge_foldedGenerator_lt_potential hM hdec hdec' hnn hy₀ hM₀
  refine ⟨max X 0, fun x hx => ?_⟩
  have h := hX x (le_trans (le_max_left _ _) hx)
  have habs : (fun y => (fun y => M y / riemannKernelReal y) |y|) =
      fun y => M y / riemannKernelReal y := by
    funext y
    rcases abs_cases y with ⟨hy, -⟩ | ⟨hy, -⟩ <;> simp only [hy, hev, riemannKernelReal_neg']
  rwa [foldedGenerator_eq_twoSidedGenerator_abs _ (le_trans (le_max_right _ _) hx), habs] at h

end GaloisForLFunctions.ArithmeticCriticalityTheory

end

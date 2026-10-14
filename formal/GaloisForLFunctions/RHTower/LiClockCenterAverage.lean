import GaloisForLFunctions.HTGeometry.HalfPlanePoissonBoundedReproduction
import GaloisForLFunctions.RHTower.LiSubexponentialCriterion
import GaloisForLFunctions.RHTower.XiCanonicalProduct

/-!
# The Li clock averaged over its center: depth-free detection of off-line zeros

For a spectral point `a = −i(ρ − ½)` of `ξ` and a center height `x`, the clock atom centered at
`½ + ix` is `1 − cos(t/(a − x))`.  Average it over the center with the Cauchy weight
`P₁(x) = 1/(π(1+x²))`:

`Ā_t(a) = ∫ P₁(x) Re(1 − cos(t/(a − x))) dx`.

* **Off the line** (`Im a ≠ 0`).  The atom is holomorphic and bounded in the center variable on the
  closed half-plane away from `a`, so Poisson reproduction gives `Ā_t(a) = Re(1 − cos(t/(a ∓ i)))`
  (`centerClockAverage_eq_of_im_neg`, `centerClockAverage_eq_of_im_pos`).  The averaged atom grows
  like `cosh(tκ)` with `κ = (|Im a| + 1)/|a ∓ i|² ≥ 1/(|a|+1)²`: the rate does not depend on the
  depth `|Im a|`.
* **On the line** (`Im a = 0`).  The singularity sits on the integration line and only the decaying
  exponential of `cos = (e^{iw}+e^{−iw})/2` survives: `Ā_t(a) = Re(1 − e^{it/(a−i)})`
  (`centerClockAverage_eq_of_im_eq_zero`; equivalently: if `X` is Cauchy then `1/(a−X)` is
  Cauchy).  Hence `0 ≤ Ā_t(a) ≤ t(t+2)/|a|²`, which also follows from `1 − cos y ≤ 4y²/(4+y²)`
  and the Poisson semigroup.  Off the line both exponentials survive, and the growing one carries
  the detection.

So for `A(t) = Σ_q Ā_t(a_q)` over all zero copies of `ξ`:

* RH ⟺ `A(n) ≥ 0` for every `n` (`riemannHypothesis_iff_liClockCenterAverage_nonneg`).
* Every off-line zero `q₀`, of any depth, forces `A(n) < −B e^{n/(2(|a_{q₀}|+1)²)}` for some `n`
  (`exists_liClockCenterAverage_lt_neg_exp`).
* Hence a lower bound `A(n) ≥ −C e^{n/(2(T+1)²)}` excludes every off-line zero with `|ρ − ½| ≤ T`:
  a window law in the height alone (`xiSpectralPoint_im_eq_zero_of_liClockCenterAverage_lower`).
* **The small-clock slope counts critical zeros.**  `A(t)/t → Σ_{critical} 1/(1+γ²)` as `t → 0⁺`
  (`tendsto_liClockCenterAverage_div`): near an on-line ordinate `1 − cos(t/(γ−x))` concentrates mass
  `πt`, while off-line atoms are `O(t²)`.  The full weight sum `Σ_q Im (a_q − i)⁻¹ = Σ_ρ Re 1/(ρ+½)`
  exceeds it by a weighted **number** of off-line copies, not by their depths; RH is equality
  (`riemannHypothesis_iff_liClockCriticalSlope_eq`).

Ordinate averaging of analytic kernels is abscissa translation (`XiHadamardPairCauchyAverage`), and
cannot separate an off-line zero from its absence.  The clock kernel is the exception: its essential
singularity sits on the line, so on-line atoms stay bounded while off-line atoms are translated.
-/

noncomputable section

open Complex MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-! ### Elementary bounds -/

/-- `‖cos w‖ ≤ e^{‖w‖}`. -/
private theorem norm_cos_le_exp_norm (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp ‖w‖ := by
  rw [Complex.cos]
  have h1 : ‖Complex.exp (w * I)‖ ≤ Real.exp ‖w‖ := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (by simp))
  have h2 : ‖Complex.exp (-w * I)‖ ≤ Real.exp ‖w‖ := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (by simp))
  rw [norm_div, Complex.norm_two]
  calc ‖Complex.exp (w * I) + Complex.exp (-w * I)‖ / 2
      ≤ (‖Complex.exp (w * I)‖ + ‖Complex.exp (-w * I)‖) / 2 := by
        gcongr; exact norm_add_le _ _
    _ ≤ (Real.exp ‖w‖ + Real.exp ‖w‖) / 2 := by gcongr
    _ = Real.exp ‖w‖ := by ring

/-- `1 − cos y ≤ 4y²/(4+y²)` for real `y`. -/
theorem one_sub_cos_le_four_mul_sq_div (y : ℝ) :
    1 - Real.cos y ≤ 4 * y ^ 2 / (4 + y ^ 2) := by
  have h1 : 1 - Real.cos y ≤ y ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := y)
    linarith
  have h2 : 1 - Real.cos y ≤ 2 := by linarith [Real.neg_one_le_cos y]
  have h0 : 0 ≤ 1 - Real.cos y := by linarith [Real.cos_le_one y]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg y]

/-! ### The averaged atom -/

/-- The clock atom of the spectral point `a` centered at height `x`. -/
def centerClockAtom (t : ℝ) (a : ℂ) (x : ℝ) : ℂ :=
  1 - Complex.cos ((t : ℂ) / (a - x))

/-- The Cauchy average over the center of one clock atom. -/
def centerClockAverage (t : ℝ) (a : ℂ) : ℝ :=
  ∫ x : ℝ, halfPlanePoisson 1 x * (centerClockAtom t a x).re

private theorem sub_ne_zero_of_im_neg {a z : ℂ} (ha : a.im < 0) (hz : 0 ≤ z.im) : a - z ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.zero_im] at this
  linarith

private theorem abs_im_le_norm_sub {a z : ℂ} (ha : a.im < 0) (hz : 0 ≤ z.im) :
    |a.im| ≤ ‖a - z‖ := by
  have h := Complex.abs_im_le_norm (a - z)
  simp only [Complex.sub_im] at h
  rw [abs_of_neg ha]
  rw [abs_of_neg (by linarith)] at h
  linarith

/-- Poisson reproduction for an atom whose spectral point lies below the axis. -/
theorem integral_halfPlanePoisson_mul_centerClockAtom_of_im_neg {a : ℂ} (ha : a.im < 0) (t : ℝ) :
    (∫ x : ℝ, (halfPlanePoisson 1 x : ℂ) * (1 - Complex.cos ((t : ℂ) / (a - x)))) =
      1 - Complex.cos ((t : ℂ) / (a - I)) := by
  have hdiff : ∀ z : ℂ, 0 ≤ z.im →
      DifferentiableAt ℂ (fun z : ℂ => 1 - Complex.cos ((t : ℂ) / (a - z))) z := by
    intro z hz
    have hne := sub_ne_zero_of_im_neg ha hz
    fun_prop (disch := exact hne)
  have hbd : ∀ z : ℂ, 0 ≤ z.im →
      ‖(fun z : ℂ => 1 - Complex.cos ((t : ℂ) / (a - z))) z‖ ≤ 1 + Real.exp (|t| / |a.im|) := by
    intro z hz
    have hne := sub_ne_zero_of_im_neg ha hz
    have hpos : 0 < |a.im| := abs_pos.mpr (ne_of_lt ha)
    have hq : ‖(t : ℂ) / (a - z)‖ ≤ |t| / |a.im| := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_div_of_nonneg_left (abs_nonneg t) hpos (abs_im_le_norm_sub ha hz)
    calc ‖1 - Complex.cos ((t : ℂ) / (a - z))‖
        ≤ ‖(1 : ℂ)‖ + ‖Complex.cos ((t : ℂ) / (a - z))‖ := norm_sub_le _ _
      _ ≤ 1 + Real.exp (|t| / |a.im|) := by
          rw [norm_one]
          gcongr
          exact (norm_cos_le_exp_norm _).trans (Real.exp_le_exp.mpr hq)
  exact integral_halfPlanePoisson_one_mul_eq_apply_I hdiff hbd

private theorem integrable_halfPlanePoisson_mul_centerClockAtom_of_im_neg {a : ℂ} (ha : a.im < 0)
    (t : ℝ) :
    Integrable (fun x : ℝ => (halfPlanePoisson 1 x : ℂ) * (1 - Complex.cos ((t : ℂ) / (a - x)))) := by
  have hP : Integrable (fun x : ℝ => (halfPlanePoisson 1 x : ℂ)) :=
    (integrable_halfPlanePoisson one_pos).ofReal
  have hpos : 0 < |a.im| := abs_pos.mpr (ne_of_lt ha)
  have hcont : Continuous (fun x : ℝ => 1 - Complex.cos ((t : ℂ) / (a - x))) := by
    have hne : ∀ x : ℝ, a - (x : ℂ) ≠ 0 := fun x => sub_ne_zero_of_im_neg ha (by simp)
    fun_prop (disch := exact hne _)
  refine (hP.bdd_mul (c := 1 + Real.exp (|t| / |a.im|)) hcont.aestronglyMeasurable ?_).congr ?_
  · refine Eventually.of_forall fun x => ?_
    have hq : ‖(t : ℂ) / (a - x)‖ ≤ |t| / |a.im| := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_div_of_nonneg_left (abs_nonneg t) hpos (abs_im_le_norm_sub ha (by simp))
    calc ‖1 - Complex.cos ((t : ℂ) / (a - x))‖
        ≤ ‖(1 : ℂ)‖ + ‖Complex.cos ((t : ℂ) / (a - x))‖ := norm_sub_le _ _
      _ ≤ 1 + Real.exp (|t| / |a.im|) := by
          rw [norm_one]
          gcongr
          exact (norm_cos_le_exp_norm _).trans (Real.exp_le_exp.mpr hq)
  · exact Eventually.of_forall fun x => mul_comm _ _

/-- **Off the line, below the axis.**  The averaged atom is the atom translated by `−i`. -/
theorem centerClockAverage_eq_of_im_neg {a : ℂ} (ha : a.im < 0) (t : ℝ) :
    centerClockAverage t a = (1 - Complex.cos ((t : ℂ) / (a - I))).re := by
  rw [← integral_halfPlanePoisson_mul_centerClockAtom_of_im_neg ha t, centerClockAverage]
  have hint := integrable_halfPlanePoisson_mul_centerClockAtom_of_im_neg ha t
  rw [show (∫ x : ℝ, (halfPlanePoisson 1 x : ℂ) * (1 - Complex.cos ((t : ℂ) / (a - x)))).re =
      RCLike.re (∫ x : ℝ, (halfPlanePoisson 1 x : ℂ) * (1 - Complex.cos ((t : ℂ) / (a - x))))
      from rfl, ← integral_re hint]
  congr 1
  funext x
  simp [centerClockAtom]

private theorem centerClockAtom_conj_re (t : ℝ) (a : ℂ) (x : ℝ) :
    (centerClockAtom t ((starRingEnd ℂ) a) x).re = (centerClockAtom t a x).re := by
  have h : centerClockAtom t ((starRingEnd ℂ) a) x = (starRingEnd ℂ) (centerClockAtom t a x) := by
    rw [centerClockAtom, centerClockAtom, map_sub, map_one, ← Complex.cos_conj, map_div₀,
      Complex.conj_ofReal, map_sub, Complex.conj_ofReal]
  rw [h, Complex.conj_re]

/-- **Off the line, above the axis.**  The averaged atom is the atom translated by `+i`. -/
theorem centerClockAverage_eq_of_im_pos {a : ℂ} (ha : 0 < a.im) (t : ℝ) :
    centerClockAverage t a = (1 - Complex.cos ((t : ℂ) / (a + I))).re := by
  have hc : ((starRingEnd ℂ) a).im < 0 := by simp [ha]
  have hav : centerClockAverage t a = centerClockAverage t ((starRingEnd ℂ) a) := by
    unfold centerClockAverage
    congr 1
    funext x
    rw [centerClockAtom_conj_re]
  rw [hav, centerClockAverage_eq_of_im_neg hc t]
  have h : 1 - Complex.cos ((t : ℂ) / ((starRingEnd ℂ) a - I)) =
      (starRingEnd ℂ) (1 - Complex.cos ((t : ℂ) / (a + I))) := by
    rw [map_sub, map_one, ← Complex.cos_conj, map_div₀, Complex.conj_ofReal, map_add,
      Complex.conj_I, ← sub_eq_add_neg]
  rw [h, Complex.conj_re]

/-- On the line the atom is real and nonnegative. -/
private theorem centerClockAtom_re_of_im_eq_zero {a : ℂ} (ha : a.im = 0) (t x : ℝ) :
    (centerClockAtom t a x).re = 1 - Real.cos (t / (a.re - x)) := by
  have hreal : a - (x : ℂ) = ((a.re - x : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [ha]
  have harg : (t : ℂ) / (a - x) = ((t / (a.re - x) : ℝ) : ℂ) := by
    rw [hreal, Complex.ofReal_div]
  rw [centerClockAtom, harg, ← Complex.ofReal_cos, Complex.sub_re, Complex.one_re,
    Complex.ofReal_re]

/-- **On the line**, the averaged atom is nonnegative. -/
theorem centerClockAverage_nonneg_of_im_eq_zero {a : ℂ} (ha : a.im = 0) (t : ℝ) :
    0 ≤ centerClockAverage t a := by
  refine integral_nonneg fun x => ?_
  rw [centerClockAtom_re_of_im_eq_zero ha]
  exact mul_nonneg (halfPlanePoisson_pos one_pos x).le (by linarith [Real.cos_le_one (t / (a.re - x))])

/-- The one-sided exponential is the Poisson reproduction of its boundary values even when the
essential singularity sits on the line: shift the singularity below the axis by `ε`, reproduce,
and let `ε → 0` by dominated convergence. -/
theorem integral_halfPlanePoisson_mul_exp_I_div_of_real (γ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : ℝ, (halfPlanePoisson 1 x : ℂ) * Complex.exp (I * t / ((γ : ℂ) - x))) =
      Complex.exp (I * t / ((γ : ℂ) - I)) := by
  -- the shifted family
  set Fε : ℝ → ℂ → ℂ := fun ε z => Complex.exp (I * t / ((γ : ℂ) - I * ε - z)) with hFε
  have hden : ∀ {ε : ℝ}, 0 < ε → ∀ z : ℂ, 0 ≤ z.im → (γ : ℂ) - I * ε - z ≠ 0 := by
    intro ε hε z hz h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hre_nonpos : ∀ {ε : ℝ}, 0 < ε → ∀ z : ℂ, 0 ≤ z.im →
      (I * t / ((γ : ℂ) - I * ε - z)).re ≤ 0 := by
    intro ε hε z hz
    set d : ℂ := (γ : ℂ) - I * ε - z with hd
    have hdne : d ≠ 0 := hden hε z hz
    have hdim : d.im = -ε - z.im := by rw [hd]; simp
    rw [Complex.div_re]
    have hnum : (I * (t : ℂ)).re * d.re + (I * (t : ℂ)).im * d.im = t * d.im := by
      simp
    have hns : 0 < Complex.normSq d := Complex.normSq_pos.mpr hdne
    rw [show (I * (t : ℂ)).re * d.re / Complex.normSq d + (I * (t : ℂ)).im * d.im / Complex.normSq d
        = ((I * (t : ℂ)).re * d.re + (I * (t : ℂ)).im * d.im) / Complex.normSq d by ring, hnum]
    apply div_nonpos_of_nonpos_of_nonneg _ hns.le
    rw [hdim]
    nlinarith
  have hrepr : ∀ {ε : ℝ}, 0 < ε →
      (∫ x : ℝ, (halfPlanePoisson 1 x : ℂ) * Fε ε x) = Fε ε I := by
    intro ε hε
    refine integral_halfPlanePoisson_one_mul_eq_apply_I (M := 1) (fun z hz => ?_) (fun z hz => ?_)
    · have := hden hε z hz
      simp only [hFε]
      fun_prop (disch := exact this)
    · simp only [hFε, Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr (hre_nonpos hε z hz)
  -- pass to the limit along `ε = 1/(n+1)`
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n => by rw [hεdef]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hP : Integrable (fun x : ℝ => (halfPlanePoisson 1 x : ℝ)) := integrable_halfPlanePoisson one_pos
  have hlhs : Tendsto (fun n => ∫ x : ℝ, (halfPlanePoisson 1 x : ℂ) * Fε (ε n) x) atTop
      (𝓝 (∫ x : ℝ, (halfPlanePoisson 1 x : ℂ) * Complex.exp (I * t / ((γ : ℂ) - x)))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => halfPlanePoisson 1 x) ?_ hP ?_ ?_
    · intro n
      have hc : Continuous (fun x : ℝ => (halfPlanePoisson 1 x : ℂ) * Fε (ε n) x) := by
        have hne : ∀ x : ℝ, (γ : ℂ) - I * (ε n) - (x : ℂ) ≠ 0 := fun x => hden (hεpos n) x (by simp)
        have hPc : Continuous (fun x : ℝ => halfPlanePoisson 1 x) := by
          unfold halfPlanePoisson; fun_prop (disch := intro x; positivity)
        simp only [hFε]
        fun_prop (disch := exact hne _)
      exact hc.aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (halfPlanePoisson_pos one_pos x)]
      have h1 : ‖Fε (ε n) x‖ ≤ 1 := by
        simp only [hFε, Complex.norm_exp]
        exact Real.exp_le_one_iff.mpr (hre_nonpos (hεpos n) x (by simp))
      nlinarith [halfPlanePoisson_pos one_pos x]
    · -- pointwise convergence off the singular point
      have hnull : ∀ᵐ x : ℝ, x ≠ γ := by
        have : (volume : Measure ℝ) {γ} = 0 := Real.volume_singleton
        exact measure_eq_zero_iff_ae_notMem.mp this |>.mono fun x hx => by simpa using hx
      filter_upwards [hnull] with x hx
      have hxne : (γ : ℂ) - (x : ℂ) ≠ 0 := by
        intro h; apply hx
        have := congrArg Complex.re h
        simp at this; linarith
      have hcont : ContinuousAt (fun e : ℝ => Complex.exp (I * t / ((γ : ℂ) - I * e - x))) 0 := by
        have : (γ : ℂ) - I * ((0 : ℝ) : ℂ) - (x : ℂ) ≠ 0 := by simpa using hxne
        fun_prop (disch := exact this)
      have hlim := hcont.tendsto.comp hεlim
      have hlim' : Tendsto (fun n => Fε (ε n) x) atTop (𝓝 (Complex.exp (I * t / ((γ : ℂ) - x)))) := by
        simpa [hFε, Function.comp_def] using hlim
      exact hlim'.const_mul _
  have hrhs : Tendsto (fun n => Fε (ε n) I) atTop (𝓝 (Complex.exp (I * t / ((γ : ℂ) - I)))) := by
    have hne : (γ : ℂ) - I * ((0 : ℝ) : ℂ) - I ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this
    have hcont : ContinuousAt (fun e : ℝ => Complex.exp (I * t / ((γ : ℂ) - I * e - I))) 0 := by
      fun_prop (disch := exact hne)
    have hlim := hcont.tendsto.comp hεlim
    simpa [hFε, Function.comp_def] using hlim
  have heq : (fun n => ∫ x : ℝ, (halfPlanePoisson 1 x : ℂ) * Fε (ε n) x) = fun n => Fε (ε n) I := by
    funext n; exact hrepr (hεpos n)
  rw [heq] at hlhs
  exact tendsto_nhds_unique hlhs hrhs

private theorem re_one_sub_exp_I_mul_ofReal (r : ℝ) :
    (1 - Complex.exp (I * (r : ℂ))).re = 1 - Real.cos r := by
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]

private theorem norm_exp_I_mul_ofReal (r : ℝ) : ‖Complex.exp (I * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

/-- **On the line, exactly.**  The averaged atom of a real spectral point keeps only the decaying
exponential: `Re(1 − e^{it/(a−i)}) = 1 − e^{−t/(1+a²)} cos(ta/(1+a²))`.  Off the line both
exponentials of `cos` survive (`centerClockAverage_eq_of_im_neg`). -/
theorem centerClockAverage_eq_of_im_eq_zero {a : ℂ} (ha : a.im = 0) {t : ℝ} (ht : 0 ≤ t) :
    centerClockAverage t a = (1 - Complex.exp (I * t / (a - I))).re := by
  have haγ : a = ((a.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [ha]
  have hpt : ∀ x : ℝ, (centerClockAtom t a x).re = (1 - Complex.exp (I * t / ((a.re : ℂ) - x))).re := by
    intro x
    rw [centerClockAtom_re_of_im_eq_zero ha]
    have harg : I * (t : ℂ) / ((a.re : ℂ) - x) = I * ((t / (a.re - x) : ℝ) : ℂ) := by
      push_cast; ring
    rw [harg, re_one_sub_exp_I_mul_ofReal]
  have hP : Integrable (fun x : ℝ => (halfPlanePoisson 1 x : ℂ)) :=
    (integrable_halfPlanePoisson one_pos).ofReal
  have hint : Integrable (fun x : ℝ =>
      (halfPlanePoisson 1 x : ℂ) * (1 - Complex.exp (I * t / ((a.re : ℂ) - x)))) := by
    have hmeas : AEStronglyMeasurable (fun x : ℝ => 1 - Complex.exp (I * t / ((a.re : ℂ) - x))) volume := by
      have : Measurable (fun x : ℝ => 1 - Complex.exp (I * t / ((a.re : ℂ) - x))) := by fun_prop
      exact this.aestronglyMeasurable
    refine (hP.bdd_mul (c := 2) hmeas ?_).congr (Eventually.of_forall fun x => mul_comm _ _)
    refine Eventually.of_forall fun x => ?_
    have hle : ‖Complex.exp (I * t / ((a.re : ℂ) - x))‖ ≤ 1 := by
      have : I * (t : ℂ) / ((a.re : ℂ) - x) = I * ((t / (a.re - x) : ℝ) : ℂ) := by push_cast; ring
      rw [this, norm_exp_I_mul_ofReal]
    calc ‖1 - Complex.exp (I * t / ((a.re : ℂ) - x))‖
        ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (I * t / ((a.re : ℂ) - x))‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hsplit : (∫ x : ℝ, (halfPlanePoisson 1 x : ℂ) * (1 - Complex.exp (I * t / ((a.re : ℂ) - x)))) =
      1 - Complex.exp (I * t / ((a.re : ℂ) - I)) := by
    have hexp : Integrable (fun x : ℝ =>
        (halfPlanePoisson 1 x : ℂ) * Complex.exp (I * t / ((a.re : ℂ) - x))) := by
      have hsub := hP.sub hint
      refine hsub.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]; ring
    rw [show (fun x : ℝ => (halfPlanePoisson 1 x : ℂ) * (1 - Complex.exp (I * t / ((a.re : ℂ) - x))))
        = fun x : ℝ => (halfPlanePoisson 1 x : ℂ) - (halfPlanePoisson 1 x : ℂ) *
          Complex.exp (I * t / ((a.re : ℂ) - x)) by funext x; ring,
      integral_sub hP hexp, integral_halfPlanePoisson_mul_exp_I_div_of_real a.re ht,
      integral_complex_ofReal, integral_halfPlanePoisson one_pos]
    simp
  unfold centerClockAverage
  simp_rw [hpt]
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [show (fun x : ℝ => halfPlanePoisson 1 x *
      (1 - Complex.exp (I * t / ((a.re : ℂ) - x))).re) =
      fun x : ℝ => ((halfPlanePoisson 1 x : ℂ) * (1 - Complex.exp (I * t / ((a.re : ℂ) - x)))).re by
    funext x; simp [Complex.mul_re], hre, hsplit, ← haγ]

/-- **On the line**, the averaged atom is at most `t(t+2)/|a|²`. -/
theorem centerClockAverage_le_of_im_eq_zero {a : ℂ} (ha : a.im = 0) (ha0 : a ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) : centerClockAverage t a ≤ t * (t + 2) / ‖a‖ ^ (2 : ℕ) := by
  have hnorm : ‖a‖ = |a.re| := by
    have : a = (a.re : ℂ) := by apply Complex.ext <;> simp [ha]
    rw [this, Complex.norm_real, Real.norm_eq_abs]; simp
  have hre0 : a.re ≠ 0 := by
    intro h; apply ha0; apply Complex.ext <;> simp [h, ha]
  have hsq : 0 < a.re ^ 2 := by positivity
  rcases eq_or_lt_of_le ht with h0 | htpos
  · -- `t = 0`: every atom vanishes
    subst h0
    have hz : centerClockAverage 0 a = 0 := by
      unfold centerClockAverage
      simp [centerClockAtom]
    rw [hz]
    simp
  -- the pointwise majorant
  set c : ℝ := t / 2 with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hmaj : ∀ x : ℝ, (centerClockAtom t a x).re ≤
      2 * Real.pi * t * halfPlanePoisson c (a.re - x) := by
    intro x
    rw [centerClockAtom_re_of_im_eq_zero ha]
    have hb := one_sub_cos_le_four_mul_sq_div (t / (a.re - x))
    rw [halfPlanePoisson]
    by_cases hx : a.re - x = 0
    · rw [hx, div_zero, Real.cos_zero, sub_self]
      positivity
    · have hpi : 0 < Real.pi := Real.pi_pos
      refine hb.trans (le_of_eq ?_)
      rw [hc]
      field_simp
      ring
  have hpi : 0 < Real.pi := Real.pi_pos
  have hP1 : Integrable (halfPlanePoisson 1) := integrable_halfPlanePoisson one_pos
  have hmeas : Measurable (fun x : ℝ => 1 - Real.cos (t / (a.re - x))) :=
    measurable_const.sub (Real.measurable_cos.comp
      (measurable_const.div (measurable_const.sub measurable_id)))
  have hatom : (fun x : ℝ => (centerClockAtom t a x).re) =
      fun x : ℝ => 1 - Real.cos (t / (a.re - x)) := by
    funext x; exact centerClockAtom_re_of_im_eq_zero ha t x
  have hlhs : Integrable (fun x : ℝ => halfPlanePoisson 1 x * (centerClockAtom t a x).re) := by
    simp only [centerClockAtom_re_of_im_eq_zero ha]
    refine (hP1.mul_const 2).mono'
      (hP1.aestronglyMeasurable.mul hmeas.aestronglyMeasurable) ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (halfPlanePoisson_pos one_pos x).le
      (by linarith [Real.cos_le_one (t / (a.re - x))]))]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.neg_one_le_cos (t / (a.re - x))])
      (halfPlanePoisson_pos one_pos x).le
  have hPc_le : ∀ y : ℝ, halfPlanePoisson c y ≤ 1 / (Real.pi * c) := by
    intro y
    rw [halfPlanePoisson, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg y, sq_nonneg c]
  have hconv_int : Integrable (fun x : ℝ => halfPlanePoisson c (a.re - x) * halfPlanePoisson 1 x) := by
    refine (hP1.const_mul (1 / (Real.pi * c))).mono' ?_ ?_
    · have hm : Measurable (fun x : ℝ => halfPlanePoisson c (a.re - x)) := by
        unfold halfPlanePoisson; fun_prop
      exact hm.aestronglyMeasurable.mul hP1.aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (halfPlanePoisson_pos hc0 _).le
        (halfPlanePoisson_pos one_pos x).le)]
      exact mul_le_mul_of_nonneg_right (hPc_le _) (halfPlanePoisson_pos one_pos x).le
  have hrhs : Integrable (fun x : ℝ =>
      halfPlanePoisson 1 x * (2 * Real.pi * t * halfPlanePoisson c (a.re - x))) := by
    refine (hconv_int.const_mul (2 * Real.pi * t)).congr (Eventually.of_forall fun x => ?_)
    ring
  have hmono : centerClockAverage t a ≤
      ∫ x : ℝ, halfPlanePoisson 1 x * (2 * Real.pi * t * halfPlanePoisson c (a.re - x)) :=
    integral_mono hlhs hrhs fun x =>
      mul_le_mul_of_nonneg_left (hmaj x) (halfPlanePoisson_pos one_pos x).le
  have hval : (∫ x : ℝ, halfPlanePoisson 1 x * (2 * Real.pi * t * halfPlanePoisson c (a.re - x))) =
      2 * Real.pi * t * halfPlanePoisson (c + 1) a.re := by
    rw [← halfPlanePoisson_convolution hc0 one_pos a.re, ← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hval] at hmono
  calc centerClockAverage t a ≤ 2 * Real.pi * t * halfPlanePoisson (c + 1) a.re := hmono
    _ = 2 * t * (c + 1) / ((c + 1) ^ (2 : ℕ) + a.re ^ (2 : ℕ)) := by
        rw [halfPlanePoisson]
        field_simp
    _ ≤ t * (t + 2) / ‖a‖ ^ (2 : ℕ) := by
        rw [hnorm, sq_abs, hc, div_le_div_iff₀ (by positivity) hsq]
        have : 0 ≤ t * (t + 2) * (t / 2 + 1) ^ (2 : ℕ) := by positivity
        nlinarith

/-! ### Off-line atoms are paired Li terms -/

/-- The reciprocal of the translated spectral point, oriented into the lower half-plane. -/
def centerClockShiftReciprocal (a : ℂ) : ℂ :=
  if a.im < 0 then -(a - I)⁻¹ else (a + I)⁻¹

/-- The paired-Li base attached to an off-line spectral point. -/
def centerClockLiBase (a : ℂ) : ℂ := Complex.exp (I * centerClockShiftReciprocal a)

/-- A paired Li term of an exponential base is a cosine defect. -/
theorem liTerm_exp_I_mul (u : ℂ) (n : ℕ) :
    liTerm (Complex.exp (I * u)) n = 2 * (1 - Complex.cos ((n : ℂ) * u)) := by
  rw [liTerm, ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.cos]
  have h1 : (n : ℂ) * (I * u) = (n : ℂ) * u * I := by ring
  have h2 : (n : ℂ) * -(I * u) = -((n : ℂ) * u) * I := by ring
  rw [h1, h2]
  ring

private theorem shift_norm_facts {a : ℂ} (ha : a.im ≠ 0) :
    let s : ℂ := if a.im < 0 then a - I else a + I
    1 ≤ |s.im| ∧ ‖a‖ ≤ ‖s‖ ∧ ‖s‖ ≤ ‖a‖ + 1 ∧ |s.im| = |a.im| + 1 := by
  intro s
  have hsre : s.re = a.re := by
    simp only [s]; split_ifs <;> simp
  have hsim : |s.im| = |a.im| + 1 := by
    simp only [s]
    split_ifs with h
    · simp only [Complex.sub_im, Complex.I_im]
      rw [abs_of_neg (by linarith), abs_of_neg h]; ring
    · have h' : 0 < a.im := lt_of_le_of_ne (not_lt.mp h) (Ne.symm ha)
      simp only [Complex.add_im, Complex.I_im]
      rw [abs_of_pos (by linarith), abs_of_pos h']
  refine ⟨by rw [hsim]; linarith [abs_nonneg a.im], ?_, ?_, hsim⟩
  · rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply, hsre]
    have h1 : a.im * a.im ≤ s.im * s.im := by
      have := mul_self_le_mul_self (abs_nonneg a.im) (show |a.im| ≤ |s.im| by rw [hsim]; linarith)
      simpa [abs_mul_abs_self] using this
    linarith
  · simp only [s]
    split_ifs
    · exact (norm_sub_le a I).trans (by rw [Complex.norm_I])
    · exact (norm_add_le a I).trans (by rw [Complex.norm_I])

/-- The oriented reciprocal lies strictly below the axis, with depth-free size control. -/
theorem centerClockShiftReciprocal_bounds {a : ℂ} (ha : a.im ≠ 0) :
    1 / (‖a‖ + 1) ^ (2 : ℕ) ≤ -(centerClockShiftReciprocal a).im ∧
      ‖centerClockShiftReciprocal a‖ ≤ 1 ∧
      ‖centerClockShiftReciprocal a‖ ^ (2 : ℕ) ≤ 1 / ‖a‖ ^ (2 : ℕ) := by
  obtain ⟨hs1, has, hsa, hsim⟩ := shift_norm_facts ha
  set s : ℂ := if a.im < 0 then a - I else a + I with hsdef
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le one_pos ((le_trans hs1 (Complex.abs_im_le_norm s)))
  have hnormu : ‖centerClockShiftReciprocal a‖ = ‖s‖⁻¹ := by
    rw [centerClockShiftReciprocal, hsdef]
    split_ifs <;> simp [norm_inv]
  have himu : -(centerClockShiftReciprocal a).im = |s.im| / ‖s‖ ^ (2 : ℕ) := by
    rw [centerClockShiftReciprocal, hsdef, ← Complex.normSq_eq_norm_sq]
    split_ifs with h
    · rw [Complex.neg_im, neg_neg, Complex.inv_im, Complex.sub_im, Complex.I_im,
        abs_of_neg (by linarith : a.im - 1 < 0)]
    · have h' : 0 < a.im := lt_of_le_of_ne (not_lt.mp h) (Ne.symm ha)
      rw [Complex.inv_im, Complex.add_im, Complex.I_im, abs_of_pos (by linarith), neg_div, neg_neg]
  refine ⟨?_, ?_, ?_⟩
  · rw [himu]
    have hpos : 0 < ‖s‖ ^ (2 : ℕ) := by positivity
    calc 1 / (‖a‖ + 1) ^ (2 : ℕ) ≤ 1 / ‖s‖ ^ (2 : ℕ) := by
          apply one_div_le_one_div_of_le hpos
          exact pow_le_pow_left₀ (norm_nonneg _) hsa 2
      _ ≤ |s.im| / ‖s‖ ^ (2 : ℕ) := div_le_div_of_nonneg_right hs1 hpos.le
  · rw [hnormu]
    exact inv_le_one_of_one_le₀ (le_trans hs1 (Complex.abs_im_le_norm s))
  · rw [hnormu, inv_pow]
    have hpos : 0 < ‖a‖ := norm_pos_iff.mpr (fun h0 => ha (by simp [h0]))
    rw [← one_div]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (norm_nonneg _) has 2)

/-- **Off-line atoms are half paired Li terms** of a base outside the unit circle. -/
theorem centerClockAverage_eq_half_liTerm {a : ℂ} (ha : a.im ≠ 0) (n : ℕ) :
    centerClockAverage n a = (liTerm (centerClockLiBase a) n).re / 2 := by
  rw [centerClockLiBase, liTerm_exp_I_mul]
  have hcos : Complex.cos ((n : ℂ) * centerClockShiftReciprocal a) =
      Complex.cos (((n : ℝ) : ℂ) / (if a.im < 0 then a - I else a + I)) := by
    rw [centerClockShiftReciprocal]
    split_ifs
    · rw [mul_neg, Complex.cos_neg, div_eq_mul_inv]; push_cast; ring_nf
    · rw [div_eq_mul_inv]; push_cast; ring_nf
  rw [hcos]
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · rw [centerClockAverage_eq_of_im_neg hneg, if_pos hneg]
    simp [Complex.mul_re]
  · rw [centerClockAverage_eq_of_im_pos hpos, if_neg (not_lt.mpr hpos.le)]
    simp [Complex.mul_re]

theorem one_le_norm_centerClockLiBase {a : ℂ} (ha : a.im ≠ 0) :
    1 ≤ ‖centerClockLiBase a‖ := by
  rw [centerClockLiBase, Complex.norm_exp]
  have h := (centerClockShiftReciprocal_bounds ha).1
  have hre : (I * centerClockShiftReciprocal a).re = -(centerClockShiftReciprocal a).im := by
    simp [Complex.mul_re]
  rw [hre]
  exact Real.one_le_exp (le_trans (by positivity) h)

theorem exp_le_norm_centerClockLiBase {a : ℂ} (ha : a.im ≠ 0) :
    Real.exp (1 / (‖a‖ + 1) ^ (2 : ℕ)) ≤ ‖centerClockLiBase a‖ := by
  rw [centerClockLiBase, Complex.norm_exp]
  have hre : (I * centerClockShiftReciprocal a).re = -(centerClockShiftReciprocal a).im := by
    simp [Complex.mul_re]
  rw [hre]
  exact Real.exp_le_exp.mpr (centerClockShiftReciprocal_bounds ha).1

theorem norm_centerClockLiBase_le {a : ℂ} (ha : a.im ≠ 0) :
    ‖centerClockLiBase a‖ ≤ Real.exp 1 := by
  rw [centerClockLiBase, Complex.norm_exp]
  refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
  rw [norm_mul, Complex.norm_I, one_mul]
  exact (centerClockShiftReciprocal_bounds ha).2.1

theorem norm_centerClockLiBase_sub_one_sq_le {a : ℂ} (ha : a.im ≠ 0) :
    ‖centerClockLiBase a - 1‖ ^ (2 : ℕ) ≤ 4 * (1 / ‖a‖ ^ (2 : ℕ)) := by
  obtain ⟨-, hu1, hu2⟩ := centerClockShiftReciprocal_bounds ha
  have hle : ‖I * centerClockShiftReciprocal a‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, one_mul]; exact hu1
  have h := Complex.norm_exp_sub_one_le hle
  rw [norm_mul, Complex.norm_I, one_mul] at h
  rw [centerClockLiBase]
  calc ‖Complex.exp (I * centerClockShiftReciprocal a) - 1‖ ^ (2 : ℕ)
      ≤ (2 * ‖centerClockShiftReciprocal a‖) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 4 * ‖centerClockShiftReciprocal a‖ ^ (2 : ℕ) := by ring
    _ ≤ 4 * (1 / ‖a‖ ^ (2 : ℕ)) := by gcongr

/-! ### The averaged clock of `ξ` -/

/-- **The center-averaged Li clock of `ξ`.** -/
def liClockCenterAverage (t : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, centerClockAverage t (xiSpectralPoint q)

private theorem xiSpectralPoint_im_eq_half_sub (q : XiZeroCopy) :
    (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
  rw [xiSpectralPoint]
  simp [Complex.mul_im]

private theorem xiSpectralPoint_im_eq_zero_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    (xiSpectralPoint q).im = 0 := by
  have h := (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH) _
    (xi_eq_zero_of_mem_divisor_support q.1)
  rw [xiSpectralPoint_im_eq_half_sub, h]
  norm_num

theorem exists_xiSpectralPoint_im_ne_zero_of_not_rh (h : ¬ RiemannHypothesis) :
    ∃ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half] at h
  push Not at h
  obtain ⟨ρ, hρ, hre⟩ := h
  let r : XiDivisorSupport := ⟨ρ, mem_xi_divisor_support_of_eq_zero hρ⟩
  have hpos := xi_divisor_pos_on_support r
  refine ⟨⟨r, ⟨0, Int.lt_toNat.mpr (by simpa using hpos)⟩⟩, ?_⟩
  rw [xiSpectralPoint_im_eq_half_sub]
  intro h0
  exact hre (by simp only [r] at h0; linarith)

/-- Under RH the averaged clock is nonnegative at every clock. -/
theorem liClockCenterAverage_nonneg_of_rh (hRH : RiemannHypothesis) (t : ℝ) :
    0 ≤ liClockCenterAverage t :=
  tsum_nonneg fun q =>
    centerClockAverage_nonneg_of_im_eq_zero (xiSpectralPoint_im_eq_zero_of_rh hRH q) t

/-- **Depth-free detection.**  Every off-line zero copy `q₀`, of any depth, forces the averaged clock
below `−B e^{n/(2(|a_{q₀}|+1)²)}` at some integer clock, for every `B`.  The exponent depends only on
the distance `|ρ₀ − ½|`, not on `|Re ρ₀ − ½|`. -/
theorem exists_liClockCenterAverage_lt_neg_exp {q₀ : XiZeroCopy}
    (hq₀ : (xiSpectralPoint q₀).im ≠ 0) (B : ℝ) :
    ∃ n : ℕ, liClockCenterAverage n <
      -(B * Real.exp (n / (2 * (‖xiSpectralPoint q₀‖ + 1) ^ (2 : ℕ)))) := by
  classical
  set Off : Set XiZeroCopy := {q | (xiSpectralPoint q).im ≠ 0} with hOff
  set S : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hS
  have hSsum := xiSpectralPoint_inv_sq_summable
  have hS0 : 0 ≤ S := tsum_nonneg fun q => by positivity
  set κ : ℝ := 1 / (2 * (‖xiSpectralPoint q₀‖ + 1) ^ (2 : ℕ)) with hκ
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  set ρ : ℝ := Real.exp κ with hρ
  have hρ1 : 1 < ρ := by
    have := Real.exp_lt_exp.mpr hκ0
    rwa [Real.exp_zero] at this
  have hρ0 : 0 ≤ ρ := (Real.exp_pos κ).le
  -- polynomial domination by `ρⁿ`
  have hr : |ρ⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr (lt_trans zero_lt_one hρ1))]
    exact inv_lt_one_of_one_lt₀ hρ1
  obtain ⟨M', hM'⟩ := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hr).bddAbove_range
  have hpoly : ∀ n : ℕ, (n : ℝ) * (n + 2) * S ≤ (3 * S * max M' 0) * ρ ^ n := by
    intro n
    have hb : (n : ℝ) ^ 2 * ρ⁻¹ ^ n ≤ max M' 0 := (hM' ⟨n, rfl⟩).trans (le_max_left _ _)
    have hρn : 0 < ρ ^ n := pow_pos (lt_trans zero_lt_one hρ1) n
    have hsq : (n : ℝ) ^ 2 ≤ max M' 0 * ρ ^ n := by
      have : (n : ℝ) ^ 2 = (n : ℝ) ^ 2 * ρ⁻¹ ^ n * ρ ^ n := by
        rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ (ne_of_gt (lt_trans zero_lt_one hρ1)),
          one_pow, mul_one]
      rw [this]
      exact mul_le_mul_of_nonneg_right hb hρn.le
    have hn2 : (n : ℝ) * (n + 2) ≤ 3 * (n : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ n ∨ (n : ℝ) = 0 := by
        rcases Nat.eq_zero_or_pos n with h | h
        · right; simp [h]
        · left; exact_mod_cast h
      rcases this with h | h
      · nlinarith
      · rw [h]; norm_num
    calc (n : ℝ) * (n + 2) * S ≤ 3 * (n : ℝ) ^ 2 * S := mul_le_mul_of_nonneg_right hn2 hS0
      _ ≤ 3 * (max M' 0 * ρ ^ n) * S := by gcongr
      _ = 3 * S * max M' 0 * ρ ^ n := by ring
  set K : ℝ := 3 * S * max M' 0 with hK
  -- the off-line family as a paired Li family
  let ι := {q : XiZeroCopy // (xiSpectralPoint q).im ≠ 0}
  let v : ι → ℂ := fun i => centerClockLiBase (xiSpectralPoint i.1)
  have hv : ∀ i : ι, 1 ≤ ‖v i‖ := fun i => one_le_norm_centerClockLiBase i.2
  have hMv : ∀ i : ι, ‖v i‖ ≤ Real.exp 1 := fun i => norm_centerClockLiBase_le i.2
  have hsum : Summable fun i : ι => (1 : ℝ) * ‖v i - 1‖ ^ (2 : ℕ) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      ((hSsum.subtype {q | (xiSpectralPoint q).im ≠ 0}).mul_left 4)
    rw [one_mul]
    exact norm_centerClockLiBase_sub_one_sq_le i.2
  have htop : 1 < ‖v ⟨q₀, hq₀⟩‖ := by
    refine lt_of_lt_of_le ?_ (exp_le_norm_centerClockLiBase hq₀)
    have := Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 / (‖xiSpectralPoint q₀‖ + 1) ^ (2 : ℕ) by positivity)
    rwa [Real.exp_zero] at this
  have hρW : ρ < ‖v ⟨q₀, hq₀⟩‖ := by
    refine lt_of_lt_of_le ?_ (exp_le_norm_centerClockLiBase hq₀)
    rw [hρ]
    apply Real.exp_lt_exp.mpr
    rw [hκ]
    have hpos : 0 < (‖xiSpectralPoint q₀‖ + 1) ^ (2 : ℕ) := by positivity
    rw [div_lt_div_iff₀ (by positivity) hpos]
    linarith
  obtain ⟨n, hn⟩ := exists_re_tsum_liTerm_lt_neg_pow (m := fun _ => (1 : ℝ)) (fun _ => le_rfl)
    hv hMv hsum htop hρ0 hρW (B := 2 * (B + K))
  refine ⟨n, ?_⟩
  -- split the averaged clock into on-line and off-line parts
  set f : XiZeroCopy → ℝ := fun q => centerClockAverage n (xiSpectralPoint q) with hf
  have hoff_eq : ∀ i : ι, f i.1 = (1 : ℝ) * (liTerm (v i) n).re / 2 := by
    intro i
    rw [one_mul]
    exact centerClockAverage_eq_half_liTerm i.2 n
  have hoff_sum : Summable fun i : ι => f i.1 := by
    have hs := summable_re_liTerm_of_one_le (m := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
      hv hMv hsum n
    refine (hs.div_const 2).congr fun i => ?_
    rw [hoff_eq]
  have hon_bd : ∀ q : {q : XiZeroCopy // ¬ (xiSpectralPoint q).im ≠ 0},
      0 ≤ f q.1 ∧ f q.1 ≤ (n : ℝ) * (n + 2) * (1 / ‖xiSpectralPoint q.1‖ ^ (2 : ℕ)) := by
    intro q
    have hq : (xiSpectralPoint q.1).im = 0 := not_not.mp q.2
    refine ⟨centerClockAverage_nonneg_of_im_eq_zero hq _, ?_⟩
    have := centerClockAverage_le_of_im_eq_zero hq (xiSpectralPoint_ne_zero q.1)
      (Nat.cast_nonneg n)
    calc f q.1 ≤ (n : ℝ) * (n + 2) / ‖xiSpectralPoint q.1‖ ^ (2 : ℕ) := this
      _ = (n : ℝ) * (n + 2) * (1 / ‖xiSpectralPoint q.1‖ ^ (2 : ℕ)) := by ring
  have hon_sum : Summable fun q : {q : XiZeroCopy // ¬ (xiSpectralPoint q).im ≠ 0} => f q.1 :=
    Summable.of_nonneg_of_le (fun q => (hon_bd q).1) (fun q => (hon_bd q).2)
      ((hSsum.subtype _).mul_left _)
  have hfsum : Summable f := by
    have := (summable_subtype_and_compl (s := Off) (f := f)).mp
    exact this ⟨hoff_sum, hon_sum⟩
  have hsplit := hfsum.tsum_subtype_add_tsum_subtype_compl Off
  have hon_le : (∑' q : {q : XiZeroCopy // ¬ (xiSpectralPoint q).im ≠ 0}, f q.1) ≤
      (n : ℝ) * (n + 2) * S := by
    calc (∑' q : {q : XiZeroCopy // ¬ (xiSpectralPoint q).im ≠ 0}, f q.1)
        ≤ ∑' q : {q : XiZeroCopy // ¬ (xiSpectralPoint q).im ≠ 0},
            (n : ℝ) * (n + 2) * (1 / ‖xiSpectralPoint q.1‖ ^ (2 : ℕ)) :=
          Summable.tsum_le_tsum (fun q => (hon_bd q).2) hon_sum ((hSsum.subtype _).mul_left _)
      _ = (n : ℝ) * (n + 2) * ∑' q : {q : XiZeroCopy // ¬ (xiSpectralPoint q).im ≠ 0},
            1 / ‖xiSpectralPoint q.1‖ ^ (2 : ℕ) := by
          rw [tsum_mul_left]
      _ ≤ (n : ℝ) * (n + 2) * S := by
          have hsub := Summable.tsum_subtype_le (fun q : XiZeroCopy => 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))
            {q : XiZeroCopy | ¬ (xiSpectralPoint q).im ≠ 0} (fun q => by positivity) hSsum
          exact mul_le_mul_of_nonneg_left hsub (by positivity)
  have hoff_val : (∑' i : ι, f i.1) = (∑' i : ι, (1 : ℝ) * (liTerm (v i) n).re) / 2 := by
    rw [← tsum_div_const]
    exact tsum_congr hoff_eq
  have hA : liClockCenterAverage n = (∑' i : ι, f i.1) +
      ∑' q : {q : XiZeroCopy // ¬ (xiSpectralPoint q).im ≠ 0}, f q.1 := by
    rw [liClockCenterAverage, ← hsplit]
    rfl
  have hexp : Real.exp (n / (2 * (‖xiSpectralPoint q₀‖ + 1) ^ (2 : ℕ))) = ρ ^ n := by
    rw [hρ, ← Real.exp_nat_mul, hκ]
    congr 1
    ring
  rw [hA, hoff_val, hexp]
  have hpn := hpoly n
  have hρn : 0 < ρ ^ n := pow_pos (lt_trans zero_lt_one hρ1) n
  nlinarith

/-- **The height-only window law.**  A lower bound `−C e^{n/(2(T+1)²)}` for the averaged clock at
every integer clock excludes every off-line zero copy with `|ρ − ½| ≤ T`, whatever its depth. -/
theorem xiSpectralPoint_im_eq_zero_of_liClockCenterAverage_lower {T C : ℝ}
    (h : ∀ n : ℕ, -(C * Real.exp (n / (2 * (T + 1) ^ (2 : ℕ)))) ≤ liClockCenterAverage n)
    {q : XiZeroCopy} (hq : ‖xiSpectralPoint q‖ ≤ T) : (xiSpectralPoint q).im = 0 := by
  by_contra hne
  obtain ⟨n, hn⟩ := exists_liClockCenterAverage_lt_neg_exp hne (max C 0)
  have hT : 0 ≤ T := (norm_nonneg _).trans hq
  have he : Real.exp (n / (2 * (T + 1) ^ (2 : ℕ))) ≤
      Real.exp (n / (2 * (‖xiSpectralPoint q‖ + 1) ^ (2 : ℕ))) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by positivity)
    have h1 : ‖xiSpectralPoint q‖ + 1 ≤ T + 1 := by linarith
    have h2 : (‖xiSpectralPoint q‖ + 1) ^ (2 : ℕ) ≤ (T + 1) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) h1 2
    linarith
  have hcmp : C * Real.exp (n / (2 * (T + 1) ^ (2 : ℕ))) ≤
      max C 0 * Real.exp (n / (2 * (‖xiSpectralPoint q‖ + 1) ^ (2 : ℕ))) :=
    calc C * Real.exp (n / (2 * (T + 1) ^ (2 : ℕ)))
        ≤ max C 0 * Real.exp (n / (2 * (T + 1) ^ (2 : ℕ))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max C 0 * Real.exp (n / (2 * (‖xiSpectralPoint q‖ + 1) ^ (2 : ℕ))) :=
          mul_le_mul_of_nonneg_left he (le_max_right _ _)
  linarith [h n]

/-- **RH is the nonnegativity of the center-averaged clock** at every integer clock. -/
theorem riemannHypothesis_iff_liClockCenterAverage_nonneg :
    RiemannHypothesis ↔ ∀ n : ℕ, 0 ≤ liClockCenterAverage n := by
  refine ⟨fun hRH n => liClockCenterAverage_nonneg_of_rh hRH n, fun h => ?_⟩
  by_contra hnot
  obtain ⟨q₀, hq₀⟩ := exists_xiSpectralPoint_im_ne_zero_of_not_rh hnot
  obtain ⟨n, hn⟩ := exists_liClockCenterAverage_lt_neg_exp hq₀ 0
  have := h n
  simp only [zero_mul, neg_zero] at hn
  linarith

/-- **RH is any subexponential lower bound for the center-averaged clock.** -/
theorem riemannHypothesis_iff_liClockCenterAverage_subexp :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, -(C * Real.exp (ε * n)) ≤ liClockCenterAverage n := by
  refine ⟨fun hRH ε _ => ⟨0, fun n => by simpa using liClockCenterAverage_nonneg_of_rh hRH n⟩,
    fun h => ?_⟩
  by_contra hnot
  obtain ⟨q₀, hq₀⟩ := exists_xiSpectralPoint_im_ne_zero_of_not_rh hnot
  set ε : ℝ := 1 / (4 * (‖xiSpectralPoint q₀‖ + 1) ^ (2 : ℕ)) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨C, hC⟩ := h ε hε0
  obtain ⟨n, hn⟩ := exists_liClockCenterAverage_lt_neg_exp hq₀ (max C 0)
  have h1 := hC n
  have hcmp : C * Real.exp (ε * n) ≤
      max C 0 * Real.exp (n / (2 * (‖xiSpectralPoint q₀‖ + 1) ^ (2 : ℕ))) := by
    have he : Real.exp (ε * n) ≤ Real.exp (n / (2 * (‖xiSpectralPoint q₀‖ + 1) ^ (2 : ℕ))) := by
      apply Real.exp_le_exp.mpr
      rw [hε]
      have hpos : 0 < (‖xiSpectralPoint q₀‖ + 1) ^ (2 : ℕ) := by positivity
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc C * Real.exp (ε * n) ≤ max C 0 * Real.exp (ε * n) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max C 0 * Real.exp (n / (2 * (‖xiSpectralPoint q₀‖ + 1) ^ (2 : ℕ))) :=
          mul_le_mul_of_nonneg_left he (le_max_right _ _)
  linarith

/-! ### The small-clock slope counts the critical zeros -/

/-- The Cauchy slope weight of a spectral point, `Im (a − i)⁻¹`; it is `1/(1 + a²)` for real `a`
and equals `Re 1/(ρ + ½)` for `a = −i(ρ − ½)`. -/
def centerClockSlopeWeight (a : ℂ) : ℝ := ((a - I)⁻¹).im

private theorem norm_one_sub_cos_le_sq {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖1 - Complex.cos z‖ ≤ ‖z‖ ^ (2 : ℕ) := by
  have hzI : ‖z * I‖ ≤ 1 := by rw [norm_mul, Complex.norm_I, mul_one]; exact hz
  have hzI' : ‖-z * I‖ ≤ 1 := by rw [norm_mul, norm_neg, Complex.norm_I, mul_one]; exact hz
  have h1 := Complex.norm_exp_sub_one_sub_id_le hzI
  have h2 := Complex.norm_exp_sub_one_sub_id_le hzI'
  have hcos : 1 - Complex.cos z = -((Complex.exp (z * I) - 1 - z * I) +
      (Complex.exp (-z * I) - 1 - -z * I)) / 2 := by
    rw [Complex.cos]; ring
  rw [hcos, norm_div, norm_neg, Complex.norm_two]
  have hn1 : ‖z * I‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, mul_one]
  have hn2 : ‖-z * I‖ = ‖z‖ := by rw [norm_mul, norm_neg, Complex.norm_I, mul_one]
  calc ‖(Complex.exp (z * I) - 1 - z * I) + (Complex.exp (-z * I) - 1 - -z * I)‖ / 2
      ≤ (‖Complex.exp (z * I) - 1 - z * I‖ + ‖Complex.exp (-z * I) - 1 - -z * I‖) / 2 := by
        gcongr; exact norm_add_le _ _
    _ ≤ (‖z * I‖ ^ (2 : ℕ) + ‖-z * I‖ ^ (2 : ℕ)) / 2 := by gcongr
    _ = ‖z‖ ^ (2 : ℕ) := by rw [hn1, hn2]; ring

/-- On the line the slope of the averaged atom at clock `0` is its Cauchy weight. -/
theorem tendsto_centerClockAverage_div_of_im_eq_zero {a : ℂ} (ha : a.im = 0) :
    Tendsto (fun t : ℝ => centerClockAverage t a / t) (𝓝[>] 0)
      (𝓝 (centerClockSlopeWeight a)) := by
  set c : ℂ := I * (a - I)⁻¹ with hc
  set g : ℝ → ℝ := fun t => (1 - Complex.exp ((t : ℂ) * c)).re with hg
  have hderivC : HasDerivAt (fun t : ℝ => 1 - Complex.exp ((t : ℂ) * c)) (-c) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * c) c 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const c
    have hexp := (Complex.hasDerivAt_exp ((0 : ℝ) * c)).comp (0 : ℝ) hlin
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] at hexp
    simpa using hexp.const_sub 1
  have hderiv : HasDerivAt g (-c).re 0 := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hderivC
    have hfun : (⇑Complex.reCLM ∘ fun t : ℝ => 1 - Complex.exp ((t : ℂ) * c)) = g := by
      funext t; simp [hg]
    rw [hfun, Complex.reCLM_apply] at h
    exact h
  have hval : (-c).re = centerClockSlopeWeight a := by
    rw [hc, centerClockSlopeWeight]
    simp [Complex.mul_re]
  have hg0 : g 0 = 0 := by simp [hg]
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hderiv
  simp only [zero_add, hg0, sub_zero, smul_eq_mul] at hslope
  have hslope' : Tendsto (fun t : ℝ => g t / t) (𝓝[>] 0) (𝓝 (centerClockSlopeWeight a)) := by
    rw [← hval]
    refine (hslope.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)).congr fun t => ?_
    rw [div_eq_inv_mul]
  refine hslope'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [centerClockAverage_eq_of_im_eq_zero ha (le_of_lt ht)]
  have : I * (t : ℂ) / (a - I) = (t : ℂ) * c := by rw [hc]; field_simp
  rw [hg, this]

/-- Off the line the slope of the averaged atom at clock `0` vanishes. -/
theorem tendsto_centerClockAverage_div_of_im_ne_zero {a : ℂ} (ha : a.im ≠ 0) :
    Tendsto (fun t : ℝ => centerClockAverage t a / t) (𝓝[>] 0) (𝓝 0) := by
  set s : ℂ := if a.im < 0 then a - I else a + I with hs
  have hform : ∀ t : ℝ, centerClockAverage t a = (1 - Complex.cos ((t : ℂ) * s⁻¹)).re := by
    intro t
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · rw [centerClockAverage_eq_of_im_neg hneg, hs, if_pos hneg, div_eq_mul_inv]
    · rw [centerClockAverage_eq_of_im_pos hpos, hs, if_neg (not_lt.mpr hpos.le), div_eq_mul_inv]
  set g : ℝ → ℝ := fun t => (1 - Complex.cos ((t : ℂ) * s⁻¹)).re with hg
  have hderivC : HasDerivAt (fun t : ℝ => 1 - Complex.cos ((t : ℂ) * s⁻¹)) 0 0 := by
    have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * s⁻¹) s⁻¹ 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const s⁻¹
    have hcos := (Complex.hasDerivAt_cos ((0 : ℝ) * s⁻¹)).comp (0 : ℝ) hlin
    simp only [Complex.ofReal_zero, zero_mul, Complex.sin_zero, neg_zero, zero_mul] at hcos
    simpa using hcos.const_sub 1
  have hderiv : HasDerivAt g 0 0 := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hderivC
    have hfun : (⇑Complex.reCLM ∘ fun t : ℝ => 1 - Complex.cos ((t : ℂ) * s⁻¹)) = g := by
      funext t; simp [hg]
    rw [hfun, map_zero] at h
    exact h
  have hg0 : g 0 = 0 := by simp [hg]
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hderiv
  simp only [zero_add, hg0, sub_zero, smul_eq_mul] at hslope
  refine (hslope.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)).congr fun t => ?_
  rw [hform, div_eq_inv_mul]

private theorem abs_im_xiSpectralPoint_lt_half (q : XiZeroCopy) :
    |(xiSpectralPoint q).im| < 1 / 2 := by
  rw [xiSpectralPoint_im_eq_half_sub]
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  rw [abs_lt]; constructor <;> linarith

/-- The slope weight is positive and at most `(3/2)/|a|²` for every zero copy. -/
private theorem centerClockSlopeWeight_bounds (q : XiZeroCopy) :
    0 < centerClockSlopeWeight (xiSpectralPoint q) ∧
      centerClockSlopeWeight (xiSpectralPoint q) ≤ 3 / 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  set a := xiSpectralPoint q with ha
  have him := abs_im_xiSpectralPoint_lt_half q
  rw [← ha] at him
  have hai := abs_lt.mp him
  have hne : a - I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hns : 0 < Complex.normSq (a - I) := Complex.normSq_pos.mpr hne
  have hw : centerClockSlopeWeight a = (1 - a.im) / Complex.normSq (a - I) := by
    rw [centerClockSlopeWeight, Complex.inv_im]
    simp only [Complex.sub_im, Complex.I_im]
    ring
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hcmp : ‖a‖ ^ (2 : ℕ) ≤ Complex.normSq (a - I) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.I_im]
    nlinarith
  refine ⟨by rw [hw]; exact div_pos (by linarith) hns, ?_⟩
  rw [hw]
  calc (1 - a.im) / Complex.normSq (a - I) ≤ (3 / 2) / Complex.normSq (a - I) :=
        div_le_div_of_nonneg_right (by linarith) hns.le
    _ ≤ (3 / 2) / ‖a‖ ^ (2 : ℕ) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hcmp
    _ = 3 / 2 * (1 / ‖a‖ ^ (2 : ℕ)) := by ring

/-- For clocks in `(0, 1]` every averaged atom has slope at most `3/|a|²`. -/
private theorem abs_centerClockAverage_div_le (q : XiZeroCopy) {t : ℝ} (ht : 0 < t)
    (ht1 : t ≤ 1) :
    ‖centerClockAverage t (xiSpectralPoint q) / t‖ ≤ 3 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  set a := xiSpectralPoint q with ha
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht, div_le_iff₀ ht]
  by_cases him : a.im = 0
  · have h0 := centerClockAverage_nonneg_of_im_eq_zero him t
    have h1 := centerClockAverage_le_of_im_eq_zero him (xiSpectralPoint_ne_zero q) ht.le
    rw [abs_of_nonneg h0]
    calc centerClockAverage t a ≤ t * (t + 2) / ‖a‖ ^ (2 : ℕ) := h1
      _ ≤ 3 * (1 / ‖a‖ ^ (2 : ℕ)) * t := by
          rw [div_eq_mul_one_div]
          have hp : 0 ≤ 1 / ‖a‖ ^ (2 : ℕ) := by positivity
          have htt : t * (t + 2) ≤ 3 * t := by nlinarith
          calc t * (t + 2) * (1 / ‖a‖ ^ (2 : ℕ)) ≤ 3 * t * (1 / ‖a‖ ^ (2 : ℕ)) :=
                mul_le_mul_of_nonneg_right htt hp
            _ = 3 * (1 / ‖a‖ ^ (2 : ℕ)) * t := by ring
  · obtain ⟨hs1, has, -, -⟩ := shift_norm_facts him
    set s : ℂ := if a.im < 0 then a - I else a + I with hs
    have hs0 : 0 < ‖s‖ := lt_of_lt_of_le one_pos (hs1.trans (Complex.abs_im_le_norm s))
    have hform : centerClockAverage t a = (1 - Complex.cos ((t : ℂ) * s⁻¹)).re := by
      rcases lt_or_gt_of_ne him with hneg | hpos
      · rw [centerClockAverage_eq_of_im_neg hneg, hs, if_pos hneg, div_eq_mul_inv]
      · rw [centerClockAverage_eq_of_im_pos hpos, hs, if_neg (not_lt.mpr hpos.le), div_eq_mul_inv]
    have hzn : ‖(t : ℂ) * s⁻¹‖ = t / ‖s‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, norm_inv, div_eq_mul_inv]
    have hz1 : ‖(t : ℂ) * s⁻¹‖ ≤ 1 := by
      rw [hzn, div_le_one hs0]
      exact ht1.trans (hs1.trans (Complex.abs_im_le_norm s))
    have hb := norm_one_sub_cos_le_sq hz1
    rw [hform]
    calc |(1 - Complex.cos ((t : ℂ) * s⁻¹)).re| ≤ ‖1 - Complex.cos ((t : ℂ) * s⁻¹)‖ :=
          Complex.abs_re_le_norm _
      _ ≤ (t / ‖s‖) ^ (2 : ℕ) := by rw [← hzn]; exact hb
      _ ≤ 3 * (1 / ‖a‖ ^ (2 : ℕ)) * t := by
          have hsa : ‖a‖ ^ (2 : ℕ) ≤ ‖s‖ ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) has 2
          rw [div_pow, div_le_iff₀ (by positivity)]
          have hka : 0 < ‖a‖ ^ (2 : ℕ) := by positivity
          rw [show 3 * (1 / ‖a‖ ^ (2 : ℕ)) * t * ‖s‖ ^ (2 : ℕ) =
              3 * t * (‖s‖ ^ (2 : ℕ) / ‖a‖ ^ (2 : ℕ)) by ring]
          have hratio : 1 ≤ ‖s‖ ^ (2 : ℕ) / ‖a‖ ^ (2 : ℕ) := by
            rw [le_div_iff₀ hka]; linarith
          nlinarith

/-- The critical-line part of the slope weights. -/
def liClockCriticalSlope : ℝ :=
  ∑' q : XiZeroCopy,
    if (xiSpectralPoint q).im = 0 then centerClockSlopeWeight (xiSpectralPoint q) else 0

/-- **The small-clock slope of the averaged clock counts the critical zeros.**
`A(t)/t → Σ_{critical copies} 1/(1 + γ²)` as `t → 0⁺`: off-line copies do not contribute, whatever
their depth. -/
theorem tendsto_liClockCenterAverage_div :
    Tendsto (fun t : ℝ => liClockCenterAverage t / t) (𝓝[>] 0) (𝓝 liClockCriticalSlope) := by
  have heq : (fun t : ℝ => liClockCenterAverage t / t) =
      fun t : ℝ => ∑' q : XiZeroCopy, centerClockAverage t (xiSpectralPoint q) / t := by
    funext t; rw [liClockCenterAverage, tsum_div_const]
  rw [heq, liClockCriticalSlope]
  refine tendsto_tsum_of_dominated_convergence
    (xiSpectralPoint_inv_sq_summable.mul_left 3) (fun q => ?_) ?_
  · by_cases him : (xiSpectralPoint q).im = 0
    · rw [if_pos him]; exact tendsto_centerClockAverage_div_of_im_eq_zero him
    · rw [if_neg him]; exact tendsto_centerClockAverage_div_of_im_ne_zero him
  · have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT one_pos
    filter_upwards [hmem] with t ht q
    exact abs_centerClockAverage_div_le q ht.1 ht.2

private theorem summable_centerClockSlopeWeight :
    Summable fun q : XiZeroCopy => centerClockSlopeWeight (xiSpectralPoint q) :=
  Summable.of_nonneg_of_le (fun q => (centerClockSlopeWeight_bounds q).1.le)
    (fun q => (centerClockSlopeWeight_bounds q).2)
    (xiSpectralPoint_inv_sq_summable.mul_left (3 / 2))

private theorem criticalSlopeTerm_nonneg_le (q : XiZeroCopy) :
    0 ≤ (if (xiSpectralPoint q).im = 0 then centerClockSlopeWeight (xiSpectralPoint q) else 0) ∧
      (if (xiSpectralPoint q).im = 0 then centerClockSlopeWeight (xiSpectralPoint q) else 0) ≤
        centerClockSlopeWeight (xiSpectralPoint q) := by
  have h := (centerClockSlopeWeight_bounds q).1
  by_cases him : (xiSpectralPoint q).im = 0
  · rw [if_pos him]; exact ⟨h.le, le_rfl⟩
  · rw [if_neg him]; exact ⟨le_rfl, h.le⟩

/-- **A single-number criterion with depth-free deficit.**  The critical slope equals the full
Cauchy weight sum `Σ_q Im (a_q − i)⁻¹` (which is `Σ_ρ Re 1/(ρ + ½)`) exactly under RH.  Otherwise
the deficit is the weighted number of off-line copies, each weighted by about `1/(1+γ²)`. -/
theorem riemannHypothesis_iff_liClockCriticalSlope_eq :
    RiemannHypothesis ↔
      liClockCriticalSlope = ∑' q : XiZeroCopy, centerClockSlopeWeight (xiSpectralPoint q) := by
  have hsumw := summable_centerClockSlopeWeight
  have hsumc : Summable fun q : XiZeroCopy =>
      if (xiSpectralPoint q).im = 0 then centerClockSlopeWeight (xiSpectralPoint q) else 0 :=
    Summable.of_nonneg_of_le (fun q => (criticalSlopeTerm_nonneg_le q).1)
      (fun q => (criticalSlopeTerm_nonneg_le q).2) hsumw
  constructor
  · intro hRH
    rw [liClockCriticalSlope]
    exact tsum_congr fun q => by rw [if_pos (xiSpectralPoint_im_eq_zero_of_rh hRH q)]
  · intro heq
    by_contra hnot
    obtain ⟨q₀, hq₀⟩ := exists_xiSpectralPoint_im_ne_zero_of_not_rh hnot
    have hsub := hsumw.tsum_sub hsumc
    have hdsum := hsumw.sub hsumc
    have hle := hdsum.le_tsum q₀ (fun q _ => sub_nonneg.mpr (criticalSlopeTerm_nonneg_le q).2)
    have hq₀v : (centerClockSlopeWeight (xiSpectralPoint q₀) -
        if (xiSpectralPoint q₀).im = 0 then centerClockSlopeWeight (xiSpectralPoint q₀) else 0) =
        centerClockSlopeWeight (xiSpectralPoint q₀) := by rw [if_neg hq₀, sub_zero]
    rw [hq₀v, hsub] at hle
    have hc : (∑' q : XiZeroCopy,
        if (xiSpectralPoint q).im = 0 then centerClockSlopeWeight (xiSpectralPoint q) else 0) =
        liClockCriticalSlope := rfl
    rw [hc, heq, sub_self] at hle
    linarith [(centerClockSlopeWeight_bounds q₀).1]

end RHTower

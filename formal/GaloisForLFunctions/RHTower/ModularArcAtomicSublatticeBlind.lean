import GaloisForLFunctions.RHTower.FinitePoissonDecayWitness

/-!
# Continuous pole-filtered modular arc witnesses and infinite sublattice blindness

In `ModularArcLineModelBlind`, the continuous modular arc witness `ν` (`exists_arcWitness`) produces a
line-model vector `h_ν = arcLineVector ν` whose derivative `h_ν' = arcLineDeriv ν` has vanishing Fourier
coefficients at **every** nonzero integer frequency `2π(n+1)`, while its log-scale profile
`B_ν(v) = e^{v/2} h_ν(e^v) = arcPoissonProfile ν v` is strictly positive definite on the critical line.
However, `B_ν(v)` decays only like `e^{−|v|/2}` due to the logarithmic edge (`ζ`-pole at `s = 1`).

On the other hand, `FinitePoissonDecayWitness` and `FinitePoissonBlindRigidity` established a sharp
finite-vs-infinite dichotomy: applying the 5-point atomic pole filter (`atomWeight b`, `atomShift b`) to
finitely many points of the upper half-plane yields decay-class witnesses (`O(e^{−3|v|/2})`) blind up to
any finite level `N`, whereas no finite superposition of Poisson vectors can be blind at all large
integers.

In this module we apply the 5-point atomic pole filter directly to a **continuous** finite measure `ν` on
the modular bottom arc:

`H_{b,ν}(x) = Σ_{j=0}^4 m_j(b) e^{−w_j/2} h_ν(x e^{−w_j})`  (`arcLineAtomicVector b ν`),

with derivative `arcLineAtomicDeriv b ν` and log-scale profile `arcLineAtomicProfile b ν`.

## Main results

1. **Full Weil decay-class properties for any symmetric finite measure `ν` (`ν.map arcNeg = ν`):**
   - `hasDerivAt_arcLineAtomicVector`: `HasDerivAt (arcLineAtomicVector b ν) (arcLineAtomicDeriv b ν x) x`.
   - `arcLineAtomicVector_neg_of_map_arcNeg`, `arcLineAtomicDeriv_neg_of_map_arcNeg`: `H_{b,ν}` is even
     and `H_{b,ν}'` is odd.
   - `arcLineAtomicVector_inv`: `H_{b,ν}(1/x) = |x| H_{b,ν}(x)` for `x ≠ 0`.
   - `exp_half_mul_arcLineAtomicVector`: `e^{v/2} H_{b,ν}(e^v) = arcLineAtomicProfile b ν v`.
   - `integral_atomicArcProfile_eq_two_mul_arcLineAtomicProfile` and `abs_arcLineAtomicProfile_le`:
     for `ν.map arcNeg = ν` and `b ≥ 0`,
     `|arcLineAtomicProfile b ν v| ≤ 5 · ν.real univ · atomMass b · e^{3b} · e^{−3|v|/2}`.
   - `integral_arcLineAtomicVector_eq_zero`: `∫ H_{b,ν}(x) dx = 0` for `b ≥ 0` and `ν.map arcNeg = ν`.
   - `integral_cos_mul_arcLineAtomicProfile` and `integral_cos_mul_arcLineAtomicProfile_pos`:
     `∫ cos(τv) arcLineAtomicProfile b ν v dv = (1 − cos(bτ)/cosh(b/2))² ∫ cos(τv) B_ν(v) dv > 0`.

2. **Exact sub-harmonic moment reduction and infinite sublattice blindness at `b = log k` (`k ≥ 1`):**
   - `integral_arcLineAtomicDeriv_mul_cos_eq_zero`: for any symmetric `ν` and any `c ∈ ℝ`,
     `∫ H_{b,ν}'(x) cos(cx) dx = 0`.
   - `integral_arcLineAtomicDeriv_log_mul_sin_eq_subharmonics`: when `b = log k` (`k ≥ 1`) and `ν` is
     integer-blind (`∀ n, ∫ h_ν'(t) sin(arcFreq n · t) dt = 0`), the three non-negative dilation shifts
     `0, log k, 2 log k` map every positive integer frequency `arcFreq n = 2π(n+1)` to the integer
     frequencies `2π(n+1)`, `2π(n+1)k`, and `2π(n+1)k²`, and therefore **vanish identically for all `n`**.
     The 5-term sine moment reduces purely to the two sub-harmonic shifts `−log k` and `−2 log k` at
     frequencies `arcFreq n / k` and `arcFreq n / k²`.
   - `integral_arcLineAtomicDeriv_log_mul_sin_mul_eq_single_subharmonic`: on the `k`-sublattice
     `arcFreq (k(m+1) − 1) = 2πk(m+1)`, the `−log k` shift also lands on the integer frequency
     `arcFreq m` and vanishes, leaving only the single `−2 log k` term.
   - `integral_arcLineAtomicDeriv_log_mul_sin_sq_mul_eq_zero`: on the infinite `k²`-sublattice
     `arcFreq (k²(m+1) − 1) = 2πk²(m+1)`, **all five dilation shifts land on positive integer
     frequencies and vanish identically for every `m ∈ ℕ`**.
   - `exists_logNat_decayClass_sublattice_witness`: for every integer `k ≥ 2`, there is a single fixed
     function in the full `O(e^{−3|v|/2})` Weil decay class (even, inversion-covariant, zero-mean,
     strictly positive definite on the critical line) that is simultaneously blind at the entire
     infinite arithmetic progression `2πk²(m+1)` (`m ∈ ℕ`) and has purely sub-harmonic residuals at all
     other positive integers.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Symmetry and regularity of the continuous arc line-model vector -/

theorem continuous_arcPointVector_arc (x : ℝ) :
    Continuous fun u : ArcParam => arcPointVector u x := by
  unfold arcPointVector modularArcHeight
  exact Continuous.rpow_const (by
    refine Continuous.div (by fun_prop) (by fun_prop) fun u => ?_
    exact (sub_sq_add_modularArcHeight_sq_pos u x).ne') fun _ => Or.inr (by norm_num)

theorem arcLineVector_eq_integral_arcPointVector (ν : Measure ArcParam) (x : ℝ) :
    arcLineVector ν x = ∫ u, arcPointVector u x ∂ν := rfl

theorem arcLineKernel_arcNeg (x : ℝ) (u : ArcParam) :
    arcLineKernel (-x) (arcNeg u) = -arcLineKernel x u := by
  simp only [arcLineKernel, arcNeg, modularArcHeight_neg]
  have e : (-x - -(u : ℝ)) ^ 2 + modularArcHeight u ^ 2 =
      (x - u) ^ 2 + modularArcHeight u ^ 2 := by ring
  rw [e]
  ring

/-- For a `u ↦ −u` symmetric measure `ν`, `arcLineVector ν` is even. -/
theorem arcLineVector_neg_of_map_arcNeg {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineVector ν (-x) = arcLineVector ν x := by
  simp_rw [arcLineVector_eq_integral_arcPointVector]
  conv_rhs => rw [← hν]
  rw [integral_map measurable_arcNeg.aemeasurable
    (continuous_arcPointVector_arc x).aestronglyMeasurable]
  exact integral_congr_ae (Eventually.of_forall fun u => (arcPointVector_arcNeg u x).symm)

/-- For a `u ↦ −u` symmetric measure `ν`, `arcLineDeriv ν` is odd. -/
theorem arcLineDeriv_neg_of_map_arcNeg {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineDeriv ν (-x) = -arcLineDeriv ν x := by
  have hker : ∀ y : ℝ, Continuous fun u : ArcParam => arcLineKernel y u := fun y =>
    continuous_arcLineKernel.comp (continuous_const.prodMk continuous_id)
  have hdef : ∀ y : ℝ, arcLineDeriv ν y = -∫ u, arcLineKernel y u ∂ν := fun _ => rfl
  rw [hdef (-x), hdef x, neg_neg, ← integral_neg]
  conv_rhs => rw [← hν]
  rw [integral_map measurable_arcNeg.aemeasurable (hker x).aestronglyMeasurable]
  exact integral_congr_ae (Eventually.of_forall fun u => by
    have := arcLineKernel_arcNeg (-x) u
    rw [neg_neg] at this
    exact this.symm)

/-- For a `u ↦ −u` symmetric finite measure `ν`, all cosine moments of `arcLineDeriv ν` vanish. -/
theorem integral_arcLineDeriv_mul_cos_eq_zero_of_map_arcNeg {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (c : ℝ) :
    ∫ x, arcLineDeriv ν x * Real.cos (c * x) = 0 := by
  have h := integral_neg_eq_self (fun x : ℝ => arcLineDeriv ν x * Real.cos (c * x)) volume
  have e : (fun x : ℝ => arcLineDeriv ν (-x) * Real.cos (c * -x)) =
      fun x => -(arcLineDeriv ν x * Real.cos (c * x)) := by
    funext x
    rw [arcLineDeriv_neg_of_map_arcNeg hν, mul_neg, Real.cos_neg, neg_mul]
  rw [e, integral_neg] at h
  linarith

theorem continuous_arcLineVector (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Continuous (arcLineVector ν) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_arcLineVector ν x).continuousAt

theorem arcPoissonProfile_neg (ν : Measure ArcParam) (v : ℝ) :
    arcPoissonProfile ν (-v) = arcPoissonProfile ν v := by
  simp only [arcPoissonProfile, Real.cosh_neg]

theorem continuous_arcPoissonProfile (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Continuous (arcPoissonProfile ν) := by
  have e : arcPoissonProfile ν = fun v => Real.exp (v / 2) * arcLineVector ν (Real.exp v) :=
    funext fun v => (exp_half_mul_arcLineVector ν v).symm
  rw [e]
  exact (by fun_prop : Continuous fun v : ℝ => Real.exp (v / 2)).mul
    ((continuous_arcLineVector ν).comp Real.continuous_exp)

theorem abs_arcPoissonProfile_le (ν : Measure ArcParam) [IsFiniteMeasure ν] (v : ℝ) :
    |arcPoissonProfile ν v| ≤ 2 * ν.real univ * Real.cosh v ^ (-(1 / 2) : ℝ) := by
  have hc : Continuous fun u : ArcParam => arcPoissonKernel u v :=
    continuous_arcPoissonKernel.comp (continuous_const.prodMk continuous_id)
  calc |arcPoissonProfile ν v|
      = |∫ u, arcPoissonKernel u v ∂ν| := rfl
    _ ≤ ∫ u, |arcPoissonKernel u v| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ _, 2 * Real.cosh v ^ (-(1 / 2) : ℝ) ∂ν :=
        integral_mono (integrable_of_continuous_arc hc).abs (integrable_const _)
          fun u => arcPoissonKernel_le u v
    _ = 2 * ν.real univ * Real.cosh v ^ (-(1 / 2) : ℝ) := by
        rw [integral_const, smul_eq_mul]; ring

theorem integrable_arcPoissonProfile (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcPoissonProfile ν) := by
  have hI := _root_.HTGeometry.integrable_cosh_rpow_neg (s := 1 / 2) (by norm_num)
  refine (hI.const_mul (2 * ν.real univ)).mono'
    (continuous_arcPoissonProfile ν).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs]
  have := abs_arcPoissonProfile_le ν v
  simpa [show (-(1 / 2) : ℝ) = -(1 / 2 : ℝ) by norm_num] using this

/-- For a symmetric finite measure `ν`, `∫ arcPairProfile u v dν = 2 · arcPoissonProfile ν v`. -/
theorem integral_arcPairProfile_eq_two_mul_arcPoissonProfile {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (v : ℝ) :
    ∫ u, arcPairProfile u v ∂ν = 2 * arcPoissonProfile ν v := by
  have c1 : Continuous fun u : ArcParam => arcPoissonKernel u v :=
    continuous_arcPoissonKernel.comp (continuous_const.prodMk continuous_id)
  have c2 : Continuous fun u : ArcParam => arcPoissonKernel (arcNeg u) v :=
    c1.comp continuous_arcNeg
  have e : ∀ u : ArcParam, arcPairProfile u v =
      arcPoissonKernel u v + arcPoissonKernel (arcNeg u) v := fun u => by
    unfold arcPairProfile arcPairVector
    rw [mul_add, exp_half_mul_arcPointVector, exp_half_mul_arcPointVector]
  simp_rw [e]
  rw [integral_add (integrable_of_continuous_arc c1) (integrable_of_continuous_arc c2)]
  have hmap : ∫ u, arcPoissonKernel (arcNeg u) v ∂ν = arcPoissonProfile ν v := by
    have := (integral_map measurable_arcNeg.aemeasurable c1.aestronglyMeasurable (μ := ν)).symm
    rw [hν] at this
    exact this
  rw [hmap]
  change arcPoissonProfile ν v + arcPoissonProfile ν v = 2 * arcPoissonProfile ν v
  ring

theorem abs_arcPoissonProfile_le_exp {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcPoissonProfile ν v| ≤ 5 * ν.real univ * Real.exp (-(|v| / 2)) := by
  have hc : Continuous fun u : ArcParam => arcPairProfile u v := by
    have e : (fun u : ArcParam => arcPairProfile u v) =
        fun u => arcPoissonKernel u v + arcPoissonKernel (arcNeg u) v := funext fun u => by
      unfold arcPairProfile arcPairVector
      rw [mul_add, exp_half_mul_arcPointVector, exp_half_mul_arcPointVector]
    rw [e]
    exact (continuous_arcPoissonKernel.comp (continuous_const.prodMk continuous_id)).add
      ((continuous_arcPoissonKernel.comp (continuous_const.prodMk continuous_id)).comp
        continuous_arcNeg)
  have h2 : 2 * |arcPoissonProfile ν v| ≤
      ν.real univ * (10 * Real.exp (-(|v| / 2))) := by
    calc 2 * |arcPoissonProfile ν v|
        = |2 * arcPoissonProfile ν v| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ = |∫ u, arcPairProfile u v ∂ν| := by
          rw [integral_arcPairProfile_eq_two_mul_arcPoissonProfile hν]
      _ ≤ ∫ u, |arcPairProfile u v| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ _, 10 * Real.exp (-(|v| / 2)) ∂ν :=
          integral_mono (integrable_of_continuous_arc hc).abs (integrable_const _)
            fun u => abs_arcPairProfile_le_exp u v
      _ = ν.real univ * (10 * Real.exp (-(|v| / 2))) := by
          rw [integral_const, smul_eq_mul]
  linarith

/-! ### Dilations of `arcLineVector` and `arcLineDeriv` -/

/-- The dilate `e^{−w/2} h_ν(x e^{−w})` of `arcLineVector ν`. -/
def dilatedArcLine (ν : Measure ArcParam) (w x : ℝ) : ℝ :=
  Real.exp (-(w / 2)) * arcLineVector ν (x * Real.exp (-w))

/-- Its derivative `e^{−3w/2} h_ν'(x e^{−w})`. -/
def dilatedArcLineDeriv (ν : Measure ArcParam) (w x : ℝ) : ℝ :=
  Real.exp (-(3 * w / 2)) * arcLineDeriv ν (x * Real.exp (-w))

theorem hasDerivAt_dilatedArcLine (ν : Measure ArcParam) [IsFiniteMeasure ν] (w x : ℝ) :
    HasDerivAt (dilatedArcLine ν w) (dilatedArcLineDeriv ν w x) x := by
  have hc : HasDerivAt (fun x' : ℝ => x' * Real.exp (-w)) (Real.exp (-w)) x := by
    simpa using (hasDerivAt_id x).mul_const (Real.exp (-w))
  have h := ((hasDerivAt_arcLineVector ν (x * Real.exp (-w))).comp x hc).const_mul
    (Real.exp (-(w / 2)))
  refine h.congr_deriv ?_
  have he : Real.exp (-(w / 2)) * Real.exp (-w) = Real.exp (-(3 * w / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold dilatedArcLineDeriv
  rw [← he]; ring

theorem dilatedArcLine_neg_of_map_arcNeg {ν : Measure ArcParam} (hν : ν.map arcNeg = ν)
    (w x : ℝ) :
    dilatedArcLine ν w (-x) = dilatedArcLine ν w x := by
  unfold dilatedArcLine
  rw [neg_mul, arcLineVector_neg_of_map_arcNeg hν]

theorem dilatedArcLineDeriv_neg_of_map_arcNeg {ν : Measure ArcParam} (hν : ν.map arcNeg = ν)
    (w x : ℝ) :
    dilatedArcLineDeriv ν w (-x) = -dilatedArcLineDeriv ν w x := by
  unfold dilatedArcLineDeriv
  rw [neg_mul, arcLineDeriv_neg_of_map_arcNeg hν, mul_neg]

theorem dilatedArcLine_inv (ν : Measure ArcParam) (w : ℝ) {x : ℝ} (hx : x ≠ 0) :
    dilatedArcLine ν w (1 / x) = |x| * dilatedArcLine ν (-w) x := by
  have hxe : x * Real.exp w ≠ 0 := mul_ne_zero hx (Real.exp_pos w).ne'
  have e1 : 1 / x * Real.exp (-w) = 1 / (x * Real.exp w) := by rw [Real.exp_neg]; field_simp
  unfold dilatedArcLine
  rw [e1, arcLineVector_inv ν hxe, abs_mul, abs_of_pos (Real.exp_pos w), neg_neg]
  have e2 : Real.exp (-(w / 2)) * Real.exp w = Real.exp (-(-w / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← e2]; ring

theorem exp_half_mul_dilatedArcLine (ν : Measure ArcParam) (w v : ℝ) :
    Real.exp (v / 2) * dilatedArcLine ν w (Real.exp v) = arcPoissonProfile ν (v - w) := by
  unfold dilatedArcLine
  have e1 : Real.exp v * Real.exp (-w) = Real.exp (v - w) := by rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (v / 2) * Real.exp (-(w / 2)) = Real.exp ((v - w) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1, ← mul_assoc, e2, exp_half_mul_arcLineVector]

theorem integrable_dilatedArcLineDeriv (ν : Measure ArcParam) [IsFiniteMeasure ν] (w : ℝ) :
    Integrable (dilatedArcLineDeriv ν w) :=
  ((integrable_arcLineDeriv ν).comp_mul_right' (Real.exp_pos (-w)).ne').const_mul
    (Real.exp (-(3 * w / 2)))

theorem integral_dilatedArcLineDeriv_mul_sin (ν : Measure ArcParam) (w : ℝ) (c : ℝ) :
    ∫ x, dilatedArcLineDeriv ν w x * Real.sin (c * x) =
      Real.exp (-(w / 2)) * ∫ t, arcLineDeriv ν t * Real.sin (c * Real.exp w * t) := by
  have e : (fun x => dilatedArcLineDeriv ν w x * Real.sin (c * x)) = fun x =>
      Real.exp (-(3 * w / 2)) * (arcLineDeriv ν (x * Real.exp (-w)) *
        Real.sin (c * Real.exp w * (x * Real.exp (-w)))) := by
    funext x
    have : c * Real.exp w * (x * Real.exp (-w)) = c * x := by rw [Real.exp_neg]; field_simp
    simp only [dilatedArcLineDeriv]; rw [this]; ring
  rw [e, integral_const_mul]
  have hcv := Measure.integral_comp_mul_right
    (fun t : ℝ => arcLineDeriv ν t * Real.sin (c * Real.exp w * t)) (Real.exp (-w))
  rw [hcv, abs_of_pos (inv_pos.mpr (Real.exp_pos _)), smul_eq_mul, ← Real.exp_neg, neg_neg]
  have : Real.exp (-(3 * w / 2)) * Real.exp w = Real.exp (-(w / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← mul_assoc, this]

/-! ### The continuous atomic pole-filtered arc line vector -/

/-- The 5-point pole-filtered line-model vector of a measure `ν` on the modular arc:
`H_{b,ν}(x) = Σ_{j=0}^4 m_j(b) e^{−w_j/2} h_ν(x e^{−w_j})`. -/
def arcLineAtomicVector (b : ℝ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  ∑ j, atomWeight b j * dilatedArcLine ν (atomShift b j) x

/-- Its derivative `H_{b,ν}'(x) = Σ_{j=0}^4 m_j(b) e^{−3w_j/2} h_ν'(x e^{−w_j})`. -/
def arcLineAtomicDeriv (b : ℝ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  ∑ j, atomWeight b j * dilatedArcLineDeriv ν (atomShift b j) x

/-- Its log-scale profile `Σ_{j=0}^4 m_j(b) B_ν(v − w_j)`. -/
def arcLineAtomicProfile (b : ℝ) (ν : Measure ArcParam) (v : ℝ) : ℝ :=
  ∑ j, atomWeight b j * arcPoissonProfile ν (v - atomShift b j)

theorem hasDerivAt_arcLineAtomicVector (b : ℝ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (x : ℝ) :
    HasDerivAt (arcLineAtomicVector b ν) (arcLineAtomicDeriv b ν x) x :=
  HasDerivAt.fun_sum fun j _ =>
    (hasDerivAt_dilatedArcLine ν (atomShift b j) x).const_mul (atomWeight b j)

theorem continuous_arcLineAtomicVector (b : ℝ) (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Continuous (arcLineAtomicVector b ν) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_arcLineAtomicVector b ν x).continuousAt

theorem arcLineAtomicVector_neg_of_map_arcNeg (b : ℝ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineAtomicVector b ν (-x) = arcLineAtomicVector b ν x :=
  Finset.sum_congr rfl fun j _ => by rw [dilatedArcLine_neg_of_map_arcNeg hν]

theorem arcLineAtomicDeriv_neg_of_map_arcNeg (b : ℝ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineAtomicDeriv b ν (-x) = -arcLineAtomicDeriv b ν x := by
  simp only [arcLineAtomicDeriv, dilatedArcLineDeriv_neg_of_map_arcNeg hν, mul_neg,
    Finset.sum_neg_distrib]

theorem arcLineAtomicVector_inv (b : ℝ) (ν : Measure ArcParam) {x : ℝ} (hx : x ≠ 0) :
    arcLineAtomicVector b ν (1 / x) = |x| * arcLineAtomicVector b ν x := by
  simp only [arcLineAtomicVector, Fin.sum_univ_five, atomWeight, atomShift,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, dilatedArcLine_inv ν _ hx,
    neg_neg, neg_zero]
  ring

theorem exp_half_mul_arcLineAtomicVector (b : ℝ) (ν : Measure ArcParam) (v : ℝ) :
    Real.exp (v / 2) * arcLineAtomicVector b ν (Real.exp v) = arcLineAtomicProfile b ν v := by
  unfold arcLineAtomicVector arcLineAtomicProfile
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [mul_left_comm, exp_half_mul_dilatedArcLine]

theorem continuous_arcLineAtomicProfile (b : ℝ) (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Continuous (arcLineAtomicProfile b ν) :=
  continuous_finsetSum _ fun j _ =>
    continuous_const.mul ((continuous_arcPoissonProfile ν).comp (by fun_prop))

theorem arcLineAtomicProfile_neg (b : ℝ) (ν : Measure ArcParam) (v : ℝ) :
    arcLineAtomicProfile b ν (-v) = arcLineAtomicProfile b ν v := by
  simp only [arcLineAtomicProfile, Fin.sum_univ_five, atomWeight, atomShift,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, sub_zero, sub_neg_eq_add]
  rw [arcPoissonProfile_neg, show -v - b = -(v + b) by ring, show -v + b = -(v - b) by ring,
    show -v - 2 * b = -(v + 2 * b) by ring, show -v + 2 * b = -(v - 2 * b) by ring,
    arcPoissonProfile_neg, arcPoissonProfile_neg, arcPoissonProfile_neg, arcPoissonProfile_neg]
  ring

/-- **Integral representation of the profile.** For a symmetric finite measure `ν`,
`∫ atomicArcProfile b u v dν = 2 · arcLineAtomicProfile b ν v`. -/
theorem integral_atomicArcProfile_eq_two_mul_arcLineAtomicProfile (b : ℝ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (v : ℝ) :
    ∫ u, atomicArcProfile b u v ∂ν = 2 * arcLineAtomicProfile b ν v := by
  have hc : ∀ w : ℝ, Continuous fun u : ArcParam => arcPairProfile u (v - w) := fun w => by
    have e : (fun u : ArcParam => arcPairProfile u (v - w)) =
        fun u => arcPoissonKernel u (v - w) + arcPoissonKernel (arcNeg u) (v - w) := funext fun u => by
      unfold arcPairProfile arcPairVector
      rw [mul_add, exp_half_mul_arcPointVector, exp_half_mul_arcPointVector]
    rw [e]
    exact (continuous_arcPoissonKernel.comp (continuous_const.prodMk continuous_id)).add
      ((continuous_arcPoissonKernel.comp (continuous_const.prodMk continuous_id)).comp
        continuous_arcNeg)
  simp_rw [atomicArcProfile_eq_sum]
  rw [integral_finsetSum _ fun j _ =>
    (integrable_of_continuous_arc (hc (atomShift b j))).const_mul _]
  unfold arcLineAtomicProfile
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_arcPairProfile_eq_two_mul_arcPoissonProfile hν]
  ring

/-- **Weil decay-class bound for the continuous pole-filtered arc profile.** -/
theorem abs_arcLineAtomicProfile_le {b : ℝ} (hb : 0 ≤ b) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineAtomicProfile b ν v| ≤
      5 * ν.real univ * atomMass b * Real.exp (3 * b) * Real.exp (-(3 * |v| / 2)) := by
  have hc : Continuous fun u : ArcParam => atomicArcProfile b u v := by
    have e : (fun u : ArcParam => atomicArcProfile b u v) =
        fun u => ∑ j, atomWeight b j * (arcPoissonKernel u (v - atomShift b j) +
          arcPoissonKernel (arcNeg u) (v - atomShift b j)) := funext fun u => by
      rw [atomicArcProfile_eq_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold arcPairProfile arcPairVector
      rw [mul_add, exp_half_mul_arcPointVector, exp_half_mul_arcPointVector]
    rw [e]
    exact continuous_finsetSum _ fun j _ => continuous_const.mul
      ((continuous_arcPoissonKernel.comp (continuous_const.prodMk continuous_id)).add
        ((continuous_arcPoissonKernel.comp (continuous_const.prodMk continuous_id)).comp
          continuous_arcNeg))
  have h2 : 2 * |arcLineAtomicProfile b ν v| ≤
      ν.real univ * (10 * atomMass b * Real.exp (3 * b) * Real.exp (-(3 * |v| / 2))) := by
    calc 2 * |arcLineAtomicProfile b ν v|
        = |2 * arcLineAtomicProfile b ν v| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ = |∫ u, atomicArcProfile b u v ∂ν| := by
          rw [integral_atomicArcProfile_eq_two_mul_arcLineAtomicProfile b hν v]
      _ ≤ ∫ u, |atomicArcProfile b u v| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ _, 10 * atomMass b * Real.exp (3 * b) * Real.exp (-(3 * |v| / 2)) ∂ν :=
          integral_mono (integrable_of_continuous_arc hc).abs (integrable_const _)
            fun u => abs_atomicArcProfile_le hb u v
      _ = ν.real univ * (10 * atomMass b * Real.exp (3 * b) * Real.exp (-(3 * |v| / 2))) := by
          rw [integral_const, smul_eq_mul]
  linarith

theorem arcLineAtomicVector_zero (b : ℝ) (ν : Measure ArcParam) :
    arcLineAtomicVector b ν 0 = 0 := by
  have h := atomWeight_edge_sum b (-(1 / 2)) (Or.inr rfl)
  have key : ∀ w, dilatedArcLine ν w 0 = Real.exp (-(1 / 2) * w) * arcLineVector ν 0 := fun w => by
    simp only [dilatedArcLine, zero_mul]; congr 2; ring
  unfold arcLineAtomicVector
  simp_rw [key, ← mul_assoc]
  rw [← Finset.sum_mul, h, zero_mul]

theorem abs_arcLineAtomicVector_le {b : ℝ} (hb : 0 ≤ b) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (x : ℝ) :
    |arcLineAtomicVector b ν x| ≤
      2 * (5 * ν.real univ * atomMass b * Real.exp (3 * b)) * (1 + x ^ 2)⁻¹ :=
  abs_le_of_logProfile_decay
    (by have := atomMass_nonneg b; have := measureReal_nonneg (μ := ν) (s := univ); positivity)
    (arcLineAtomicVector_neg_of_map_arcNeg b hν)
    (arcLineAtomicVector_zero b ν)
    (fun v => by rw [exp_half_mul_arcLineAtomicVector]; exact abs_arcLineAtomicProfile_le hb hν v) x

theorem integrable_arcLineAtomicVector {b : ℝ} (hb : 0 ≤ b) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Integrable (arcLineAtomicVector b ν) :=
  (integrable_inv_one_add_sq.const_mul _).mono'
    (continuous_arcLineAtomicVector b ν).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_arcLineAtomicVector_le hb hν x)

theorem integrable_arcLineAtomicDeriv (b : ℝ) (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcLineAtomicDeriv b ν) :=
  integrable_finsetSum _ fun j _ =>
    (integrable_dilatedArcLineDeriv ν (atomShift b j)).const_mul (atomWeight b j)

/-! ### Zero mean and strict positive definiteness on the critical line -/

theorem integrable_exp_mul_arcPoissonProfile {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    Integrable fun v => Real.exp (l * v) * arcPoissonProfile ν v := by
  have hκ : 0 < 1 / 2 - l := by linarith
  refine ((integrable_rexp_neg_mul_abs hκ).const_mul (5 * ν.real univ)).mono'
    ((by fun_prop : Continuous fun v : ℝ => Real.exp (l * v)).mul
      (continuous_arcPoissonProfile ν)).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |Real.exp (l * v)| * |arcPoissonProfile ν v|
      ≤ Real.exp (l * |v|) * (5 * ν.real univ * Real.exp (-(|v| / 2))) :=
        mul_le_mul (abs_exp_mul_le hl0) (abs_arcPoissonProfile_le_exp hν v) (abs_nonneg _)
          (Real.exp_pos _).le
    _ = 5 * ν.real univ * Real.exp (-((1 / 2 - l) * |v|)) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

theorem abs_integral_exp_mul_arcPoissonProfile_le {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    |∫ v, Real.exp (l * v) * arcPoissonProfile ν v| ≤ 10 * ν.real univ / (1 / 2 - l) := by
  have hκ : 0 < 1 / 2 - l := by linarith
  refine abs_integral_le_integral_abs.trans ?_
  calc ∫ v, |Real.exp (l * v) * arcPoissonProfile ν v|
      ≤ ∫ v, 5 * ν.real univ * Real.exp (-((1 / 2 - l) * |v|)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          ((integrable_rexp_neg_mul_abs hκ).const_mul (5 * ν.real univ))
          (Eventually.of_forall fun v => ?_)
        dsimp only
        rw [abs_mul]
        calc |Real.exp (l * v)| * |arcPoissonProfile ν v|
            ≤ Real.exp (l * |v|) * (5 * ν.real univ * Real.exp (-(|v| / 2))) :=
              mul_le_mul (abs_exp_mul_le hl0) (abs_arcPoissonProfile_le_exp hν v) (abs_nonneg _)
                (Real.exp_pos _).le
          _ = 5 * ν.real univ * Real.exp (-((1 / 2 - l) * |v|)) := by
              rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    _ = 10 * ν.real univ / (1 / 2 - l) := by
        rw [integral_const_mul, integral_rexp_neg_mul_abs hκ]; ring

theorem integral_exp_mul_arcPoissonProfile_sub (ν : Measure ArcParam) (l w : ℝ) :
    ∫ v, Real.exp (l * v) * arcPoissonProfile ν (v - w) =
      Real.exp (l * w) * ∫ v, Real.exp (l * v) * arcPoissonProfile ν v := by
  rw [← integral_add_right_eq_self (μ := volume)
    (fun v => Real.exp (l * v) * arcPoissonProfile ν (v - w)) w, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [add_sub_cancel_right, show l * (v + w) = l * w + l * v by ring, Real.exp_add]; ring

/-- **Zero mean of the continuous pole-filtered arc vector.** -/
theorem integral_arcLineAtomicVector_eq_zero {b : ℝ} (hb : 0 ≤ b) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    ∫ x, arcLineAtomicVector b ν x = 0 := by
  have heven : ∀ x, arcLineAtomicVector b ν |x| = arcLineAtomicVector b ν x := fun x => by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, arcLineAtomicVector_neg_of_map_arcNeg b hν]
  have h1 : ∫ x, arcLineAtomicVector b ν x = 2 * ∫ x in Ioi 0, arcLineAtomicVector b ν x := by
    rw [← integral_comp_abs (f := arcLineAtomicVector b ν)]
    exact integral_congr_ae (Eventually.of_forall fun x => (heven x).symm)
  rw [h1, setIntegral_Ioi_eq_integral_exp_mul]
  have h2 : ∀ v, Real.exp v * arcLineAtomicVector b ν (Real.exp v) =
      Real.exp (v / 2) * arcLineAtomicProfile b ν v := fun v => by
    rw [← exp_half_mul_arcLineAtomicVector, ← mul_assoc, ← Real.exp_add]; ring_nf
  simp_rw [h2]
  rw [integral_exp_half_mul_eq_zero_of_tilt (continuous_arcLineAtomicProfile b ν)
    (abs_arcLineAtomicProfile_le hb hν) (D := 10 * ν.real univ * b ^ 2) ?_, mul_zero]
  intro l hl0 hl
  have hi : ∀ w, Integrable fun v => Real.exp (l * v) * arcPoissonProfile ν (v - w) := fun w => by
    have h := (integrable_exp_mul_arcPoissonProfile hν hl0 hl).comp_sub_right w
    refine (h.const_mul (Real.exp (l * w))).congr (Eventually.of_forall fun v => ?_)
    simp only
    rw [show l * v = l * w + l * (v - w) by ring, Real.exp_add]; ring
  have e : ∀ v, Real.exp (l * v) * arcLineAtomicProfile b ν v =
      ∑ j, atomWeight b j * (Real.exp (l * v) * arcPoissonProfile ν (v - atomShift b j)) :=
    fun v => by
      unfold arcLineAtomicProfile
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun j _ => (hi _).const_mul _]
  simp_rw [integral_const_mul, integral_exp_mul_arcPoissonProfile_sub]
  have hsum : ∑ j, atomWeight b j * (Real.exp (l * atomShift b j) *
      ∫ v, Real.exp (l * v) * arcPoissonProfile ν v) =
      (1 - Real.cosh (l * b) / Real.cosh (b / 2)) ^ 2 *
        ∫ v, Real.exp (l * v) * arcPoissonProfile ν v := by
    rw [← atomicWeight_exp]
    simp only [Fin.sum_univ_five, atomWeight, atomShift, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, mul_zero, Real.exp_zero]
    ring
  rw [hsum, abs_mul, abs_of_nonneg (sq_nonneg _)]
  obtain ⟨hlo, hhi⟩ := one_sub_cosh_div_le hb hl0 hl.le
  have hQ := abs_integral_exp_mul_arcPoissonProfile_le hν hl0 hl
  have hκ : 0 < 1 / 2 - l := by linarith
  calc (1 - Real.cosh (l * b) / Real.cosh (b / 2)) ^ 2 *
        |∫ v, Real.exp (l * v) * arcPoissonProfile ν v|
      ≤ (b * (1 / 2 - l)) ^ 2 * (10 * ν.real univ / (1 / 2 - l)) :=
        mul_le_mul (pow_le_pow_left₀ hlo hhi 2) hQ (abs_nonneg _) (sq_nonneg _)
    _ = 10 * ν.real univ * b ^ 2 * (1 / 2 - l) := by field_simp

theorem integrable_cos_mul_arcPoissonProfile_sub (ν : Measure ArcParam) [IsFiniteMeasure ν]
    (τ w : ℝ) :
    Integrable fun v => Real.cos (τ * v) * arcPoissonProfile ν (v - w) :=
  ((integrable_arcPoissonProfile ν).comp_sub_right w).bdd_mul (by fun_prop)
    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

theorem integral_cos_mul_arcPoissonProfile_shift (ν : Measure ArcParam) [IsFiniteMeasure ν]
    (τ w : ℝ) :
    ∫ v, Real.cos (τ * v) * arcPoissonProfile ν (v - w) =
      Real.cos (τ * w) * ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v := by
  have hQ := integrable_arcPoissonProfile ν
  have hc : Integrable fun v => Real.cos (τ * v) * arcPoissonProfile ν v :=
    hQ.bdd_mul (by fun_prop) (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hs : Integrable fun v => Real.sin (τ * v) * arcPoissonProfile ν v :=
    hQ.bdd_mul (by fun_prop) (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hodd : ∫ v, Real.sin (τ * v) * arcPoissonProfile ν v = 0 := by
    have h := integral_neg_eq_self (fun v => Real.sin (τ * v) * arcPoissonProfile ν v) volume
    have e : (fun v => Real.sin (τ * -v) * arcPoissonProfile ν (-v)) =
        fun v => -(Real.sin (τ * v) * arcPoissonProfile ν v) := by
      funext v; rw [arcPoissonProfile_neg, mul_neg, Real.sin_neg]; ring
    rw [e, integral_neg] at h
    linarith
  rw [← integral_add_right_eq_self (μ := volume)
    (fun v => Real.cos (τ * v) * arcPoissonProfile ν (v - w)) w]
  have e : ∀ v, Real.cos (τ * (v + w)) * arcPoissonProfile ν (v + w - w) =
      Real.cos (τ * w) * (Real.cos (τ * v) * arcPoissonProfile ν v) -
        Real.sin (τ * w) * (Real.sin (τ * v) * arcPoissonProfile ν v) := by
    intro v
    rw [add_sub_cancel_right, mul_add, Real.cos_add]; ring
  simp_rw [e]
  rw [integral_sub (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul, hodd,
    mul_zero, sub_zero]

/-- **Exact critical-line spectral factorization.** -/
theorem integral_cos_mul_arcLineAtomicProfile (b : ℝ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * arcLineAtomicProfile b ν v =
      (1 - Real.cos (b * τ) / Real.cosh (b / 2)) ^ 2 *
        ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v := by
  have hi := integrable_cos_mul_arcPoissonProfile_sub ν τ
  have e : ∀ v, Real.cos (τ * v) * arcLineAtomicProfile b ν v =
      ∑ j, atomWeight b j * (Real.cos (τ * v) * arcPoissonProfile ν (v - atomShift b j)) :=
    fun v => by
      unfold arcLineAtomicProfile
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun j _ => (hi _).const_mul _]
  simp_rw [integral_const_mul, integral_cos_mul_arcPoissonProfile_shift]
  rw [← atomWeight_cos_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Strict positive definiteness of the continuous pole-filtered arc profile.** -/
theorem integral_cos_mul_arcLineAtomicProfile_pos {b : ℝ} (hb : 0 < b)
    (ν : Measure ArcParam) [IsFiniteMeasure ν]
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (τ : ℝ) :
    0 < ∫ v, Real.cos (τ * v) * arcLineAtomicProfile b ν v := by
  rw [integral_cos_mul_arcLineAtomicProfile]
  refine mul_pos ?_ (hpd τ)
  have h1 : Real.cos (b * τ) / Real.cosh (b / 2) < 1 := by
    have hC : 1 < Real.cosh (b / 2) := Real.one_lt_cosh.mpr (by positivity)
    rw [div_lt_one (by positivity)]
    linarith [Real.cos_le_one (b * τ)]
  have := sub_pos.mpr h1
  positivity

/-! ### Fourier moments and integer-dilation (`b = log k`) sublattice blindness -/

/-- For a symmetric finite measure `ν`, all cosine moments of `arcLineAtomicDeriv b ν` vanish. -/
theorem integral_arcLineAtomicDeriv_mul_cos_eq_zero (b : ℝ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (c : ℝ) :
    ∫ x, arcLineAtomicDeriv b ν x * Real.cos (c * x) = 0 := by
  have h := integral_neg_eq_self (fun x : ℝ => arcLineAtomicDeriv b ν x * Real.cos (c * x)) volume
  have e : (fun x : ℝ => arcLineAtomicDeriv b ν (-x) * Real.cos (c * -x)) =
      fun x => -(arcLineAtomicDeriv b ν x * Real.cos (c * x)) := by
    funext x
    rw [arcLineAtomicDeriv_neg_of_map_arcNeg b hν, mul_neg, Real.cos_neg, neg_mul]
  rw [e, integral_neg] at h
  linarith

/-- **Sine moments of `arcLineAtomicDeriv b ν`.** -/
theorem integral_arcLineAtomicDeriv_mul_sin (b : ℝ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (c : ℝ) :
    ∫ x, arcLineAtomicDeriv b ν x * Real.sin (c * x) =
      ∑ j, atomWeight b j * (Real.exp (-(atomShift b j / 2)) *
        ∫ t, arcLineDeriv ν t * Real.sin (c * Real.exp (atomShift b j) * t)) := by
  have hi : ∀ w, Integrable fun x => dilatedArcLineDeriv ν w x * Real.sin (c * x) := fun w =>
    (integrable_dilatedArcLineDeriv ν w).mul_bdd (by fun_prop)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have e : ∀ x, arcLineAtomicDeriv b ν x * Real.sin (c * x) =
      ∑ j, atomWeight b j * (dilatedArcLineDeriv ν (atomShift b j) x * Real.sin (c * x)) :=
    fun x => by
      unfold arcLineAtomicDeriv
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun j _ => (hi _).const_mul _]
  exact Finset.sum_congr rfl fun j _ => by
    rw [integral_const_mul, integral_dilatedArcLineDeriv_mul_sin]

/-- Scaling an integer frequency `arcFreq n = 2π(n+1)` by a positive integer `k ≥ 1` yields the
integer frequency `arcFreq ((n + 1) * k - 1)`. -/
theorem arcFreq_mul_nat {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    arcFreq n * (k : ℝ) = arcFreq ((n + 1) * k - 1) := by
  have h1 : 1 ≤ (n + 1) * k := Nat.mul_pos (Nat.succ_pos n) hk
  unfold arcFreq
  rw [Nat.cast_sub h1]
  push_cast
  ring

/-- **Sub-harmonic reduction at `b = log k`.** When `b = log k` (`k ≥ 1`) and `ν` is blind at all
positive integer frequencies `arcFreq n`, the three non-negative shifts `0, log k, 2 log k` land on
integer frequencies and vanish identically for every `n ∈ ℕ`, reducing the 5-term sine moment
purely to the two negative-shift (sub-harmonic) terms at `arcFreq n / k` and `arcFreq n / k²`. -/
theorem integral_arcLineAtomicDeriv_log_mul_sin_eq_subharmonics
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    ∫ x, arcLineAtomicDeriv (Real.log k) ν x * Real.sin (arcFreq n * x) =
      atomW1 (Real.log k) * (Real.sqrt k *
        ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n / k * t)) +
      atomW2 (Real.log k) * ((k : ℝ) *
        ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n / (k : ℝ) ^ 2 * t)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  rw [integral_arcLineAtomicDeriv_mul_sin]
  simp only [Fin.sum_univ_five, atomWeight, atomShift, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons]
  -- `j = 0`: shift `0`, frequency `arcFreq n`
  have hz0 : ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * Real.exp 0 * t) = 0 := by
    rw [Real.exp_zero, mul_one]; exact hblind n
  -- `j = 1`: shift `log k`, frequency `arcFreq n * k = arcFreq ((n + 1) * k - 1)`
  have hz1 : ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * Real.exp (Real.log k) * t) = 0 := by
    rw [Real.exp_log hkpos, arcFreq_mul_nat hk n]
    exact hblind _
  -- `j = 3`: shift `2 log k`, frequency `arcFreq n * k² = arcFreq ((n + 1) * k² - 1)`
  have hz3 : ∫ t, arcLineDeriv ν t *
      Real.sin (arcFreq n * Real.exp (2 * Real.log k) * t) = 0 := by
    have he2 : Real.exp (2 * Real.log k) = ((k ^ 2 : ℕ) : ℝ) := by
      rw [show (2 : ℝ) * Real.log k = ((2 : ℕ) : ℝ) * Real.log k by norm_num, Real.exp_nat_mul,
        Real.exp_log hkpos]
      push_cast; rfl
    have hk2 : 1 ≤ k ^ 2 := by nlinarith
    rw [he2, arcFreq_mul_nat hk2 n]
    exact hblind _
  -- `j = 2`: shift `-log k`
  have hneg1 : Real.exp (-(-Real.log k / 2)) = Real.sqrt k := by
    rw [neg_div, neg_neg, Real.exp_half, Real.exp_log hkpos]
  have hfreq1 : arcFreq n * Real.exp (-Real.log k) = arcFreq n / k := by
    rw [Real.exp_neg, Real.exp_log hkpos, div_eq_mul_inv]
  -- `j = 4`: shift `-2 log k`
  have hneg2 : Real.exp (-(-(2 * Real.log k) / 2)) = (k : ℝ) := by
    rw [show -(-(2 * Real.log k) / 2) = Real.log k by ring, Real.exp_log hkpos]
  have hfreq2 : arcFreq n * Real.exp (-(2 * Real.log k)) = arcFreq n / (k : ℝ) ^ 2 := by
    rw [Real.exp_neg, show (2 : ℝ) * Real.log k = ((2 : ℕ) : ℝ) * Real.log k by norm_num,
      Real.exp_nat_mul, Real.exp_log hkpos, div_eq_mul_inv]
  rw [hz0, hz1, hz3, hneg1, hfreq1, hneg2, hfreq2]
  ring

/-- **Single-term reduction on the `k`-sublattice.** At frequencies `2π k(m+1) = arcFreq (k*(m+1)-1)`,
the `−log k` sub-harmonic lands on `arcFreq m` and vanishes, leaving only the single `−2 log k`
sub-harmonic at `arcFreq m / k`. -/
theorem integral_arcLineAtomicDeriv_log_mul_sin_mul_eq_single_subharmonic
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    ∫ x, arcLineAtomicDeriv (Real.log k) ν x *
        Real.sin (arcFreq (k * (m + 1) - 1) * x) =
      atomW2 (Real.log k) * ((k : ℝ) *
        ∫ t, arcLineDeriv ν t * Real.sin (arcFreq m / k * t)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hmul : arcFreq (k * (m + 1) - 1) = arcFreq m * k := by
    rw [Nat.mul_comm k (m + 1), ← arcFreq_mul_nat hk m]
  rw [integral_arcLineAtomicDeriv_log_mul_sin_eq_subharmonics hblind hk, hmul,
    mul_div_cancel_right₀ _ hkpos.ne', hblind m, mul_zero, mul_zero, zero_add]
  have hdiv2 : arcFreq m * (k : ℝ) / (k : ℝ) ^ 2 = arcFreq m / k := by
    have := hkpos.ne'
    field_simp
  rw [hdiv2]

/-- **Exact blindness on the infinite `k²`-sublattice.** At every frequency
`2π k²(m+1) = arcFreq (k²*(m+1)-1)` (`m ∈ ℕ`), all five dilation shifts land on positive integer
frequencies and vanish identically. -/
theorem integral_arcLineAtomicDeriv_log_mul_sin_sq_mul_eq_zero
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    ∫ x, arcLineAtomicDeriv (Real.log k) ν x *
        Real.sin (arcFreq (k ^ 2 * (m + 1) - 1) * x) = 0 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have heq : k ^ 2 * (m + 1) - 1 = k * (k * (m + 1) - 1 + 1) - 1 := by
    have h1 : 1 ≤ k * (m + 1) := Nat.mul_pos hk (Nat.succ_pos m)
    rw [Nat.sub_add_cancel h1]
    ring_nf
  rw [heq, integral_arcLineAtomicDeriv_log_mul_sin_mul_eq_single_subharmonic hblind hk]
  have hdiv : arcFreq (k * (m + 1) - 1) / (k : ℝ) = arcFreq m := by
    rw [Nat.mul_comm k (m + 1), ← arcFreq_mul_nat hk m, mul_div_cancel_right₀ _ hkpos.ne']
  rw [hdiv, hblind m, mul_zero, mul_zero]

/-! ### The unconditional continuous decay-class sublattice witness theorem -/

/-- **Unconditional continuous decay-class witness with infinite sublattice blindness.**
For every integer `k ≥ 2`, the pole-filtered modular arc witness `h = arcLineAtomicVector (log k) ν`
is a single fixed function in the full `O(e^{−3|v|/2})` Weil decay class (even, inversion-covariant,
integrable with zero mean, strictly positive definite on the critical line) whose derivative `h'` has
vanishing cosine moments at all real frequencies, purely sub-harmonic sine moments at all positive
integers, and **exact sine blindness along the entire infinite arithmetic progression
`2π k²(m+1)` (`m ∈ ℕ`)**. -/
theorem exists_logNat_decayClass_sublattice_witness {k : ℕ} (hk : 2 ≤ k) :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ x, HasDerivAt (arcLineAtomicVector (Real.log k) ν)
        (arcLineAtomicDeriv (Real.log k) ν x) x) ∧
      Integrable (arcLineAtomicVector (Real.log k) ν) ∧
      Integrable (arcLineAtomicDeriv (Real.log k) ν) ∧
      (∀ x, arcLineAtomicVector (Real.log k) ν (-x) = arcLineAtomicVector (Real.log k) ν x) ∧
      (∀ x, arcLineAtomicDeriv (Real.log k) ν (-x) = -arcLineAtomicDeriv (Real.log k) ν x) ∧
      (∀ x, x ≠ 0 → arcLineAtomicVector (Real.log k) ν (1 / x) =
        |x| * arcLineAtomicVector (Real.log k) ν x) ∧
      ∫ x, arcLineAtomicVector (Real.log k) ν x = 0 ∧
      (∃ C, 0 < C ∧ ∀ v,
        |Real.exp (v / 2) * arcLineAtomicVector (Real.log k) ν (Real.exp v)| ≤
          C * Real.exp (-(3 * |v| / 2))) ∧
      (∀ c : ℝ, ∫ x, arcLineAtomicDeriv (Real.log k) ν x * Real.cos (c * x) = 0) ∧
      (∀ n : ℕ, ∫ x, arcLineAtomicDeriv (Real.log k) ν x * Real.sin (arcFreq n * x) =
        atomW1 (Real.log k) * (Real.sqrt k *
          ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n / k * t)) +
        atomW2 (Real.log k) * ((k : ℝ) *
          ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n / (k : ℝ) ^ 2 * t))) ∧
      (∀ m : ℕ, ∫ x, arcLineAtomicDeriv (Real.log k) ν x *
          Real.sin (arcFreq (k * (m + 1) - 1) * x) =
        atomW2 (Real.log k) * ((k : ℝ) *
          ∫ t, arcLineDeriv ν t * Real.sin (arcFreq m / k * t))) ∧
      (∀ m : ℕ, ∫ x, arcLineAtomicDeriv (Real.log k) ν x *
          Real.sin (arcFreq (k ^ 2 * (m + 1) - 1) * x) = 0) ∧
      ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) *
        (Real.exp (v / 2) * arcLineAtomicVector (Real.log k) ν (Real.exp v)) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hk1 : 1 ≤ k := by omega
  have hkgt1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le one_lt_two hk)
  have hb : 0 < Real.log k := Real.log_pos hkgt1
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym,
    hasDerivAt_arcLineAtomicVector (Real.log k) ν,
    integrable_arcLineAtomicVector hb.le hsym,
    integrable_arcLineAtomicDeriv (Real.log k) ν,
    arcLineAtomicVector_neg_of_map_arcNeg (Real.log k) hsym,
    arcLineAtomicDeriv_neg_of_map_arcNeg (Real.log k) hsym,
    fun x hx => arcLineAtomicVector_inv (Real.log k) ν hx,
    integral_arcLineAtomicVector_eq_zero hb.le hsym,
    ⟨5 * ν.real univ * atomMass (Real.log k) * Real.exp (3 * Real.log k) + 1, ?_, fun v => ?_⟩,
    integral_arcLineAtomicDeriv_mul_cos_eq_zero (Real.log k) hsym,
    integral_arcLineAtomicDeriv_log_mul_sin_eq_subharmonics hblind hk1,
    integral_arcLineAtomicDeriv_log_mul_sin_mul_eq_single_subharmonic hblind hk1,
    integral_arcLineAtomicDeriv_log_mul_sin_sq_mul_eq_zero hblind hk1,
    fun τ => ?_⟩
  · have := measureReal_nonneg (μ := ν) (s := univ)
    have := atomMass_nonneg (Real.log k)
    positivity
  · rw [exp_half_mul_arcLineAtomicVector]
    calc |arcLineAtomicProfile (Real.log k) ν v|
        ≤ 5 * ν.real univ * atomMass (Real.log k) * Real.exp (3 * Real.log k) *
            Real.exp (-(3 * |v| / 2)) := abs_arcLineAtomicProfile_le hb.le hsym v
      _ ≤ (5 * ν.real univ * atomMass (Real.log k) * Real.exp (3 * Real.log k) + 1) *
            Real.exp (-(3 * |v| / 2)) := by
          gcongr; linarith
  · simp_rw [exp_half_mul_arcLineAtomicVector]
    exact integral_cos_mul_arcLineAtomicProfile_pos hb ν hpd τ

end

end RHTower

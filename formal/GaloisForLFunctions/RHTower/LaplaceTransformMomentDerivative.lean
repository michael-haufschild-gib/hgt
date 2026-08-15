import GaloisForLFunctions.RHTower.LandauAbscissaRigidity

/-!
# The Laplace transform of a nonnegative measure differentiates into its moments

Right of the abscissa the transform is a genuine Bochner integral, and it may be differentiated
under the integral sign: the dominating function for the derivative is `u e^{-b u}`, which is
itself dominated by `δ^{-1} e^{-b' u}` for any `b' < b`, because `x ≤ e^{x}` gives
`u e^{-δ u} ≤ δ^{-1}`.  Since every exponential kernel strictly right of the abscissa is
integrable, the domination closes and

`d/dσ ∫ e^{-σu} dν = −∫ u e^{-σu} dν`.

Iterating, the `k`-th derivative at a real point is `(−1)^k` times the `k`-th Laplace moment.  This
is the bridge between the analytic side of Landau's theorem and the `ℝ≥0∞` moment identity already
owned: a transform analytic on a disc about a real point has a convergent Taylor series there, whose
coefficients are exactly the moments, so the moment series converges — and past the distance to the
abscissa it cannot.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The Laplace transform as a Bochner integral. -/
def laplaceReal (ν : Measure ℝ) (σ : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), Real.exp (-σ * u) ∂ν

/-- The `k`-th moment as a Bochner integral. -/
def laplaceMomentReal (ν : Measure ℝ) (a : ℝ) (k : ℕ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-a * u) ∂ν

/-- **The exponential kernel is integrable strictly right of the abscissa.** -/
theorem integrableOn_exp_neg_of_gt_abscissa {ν : Measure ℝ} {c σ : ℝ} (hc : IsAbscissa ν c)
    (hσ : c < σ) :
    IntegrableOn (fun u : ℝ => Real.exp (-σ * u)) (Ioi (0 : ℝ)) ν := by
  constructor
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · have hfin : laplaceMass ν σ ≠ ⊤ := hc.1 σ hσ
    have hcongr : (∫⁻ u in Ioi (0 : ℝ), ‖Real.exp (-σ * u)‖ₑ ∂ν) = laplaceMass ν σ := by
      rw [laplaceMass]
      refine lintegral_congr fun u => ?_
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [HasFiniteIntegral, hcongr]
    exact lt_top_iff_ne_top.mpr hfin

/-- The elementary bound `u e^{-δu} ≤ δ⁻¹`, from `x ≤ e^x`. -/
theorem mul_exp_neg_le {δ u : ℝ} (hδ : 0 < δ) :
    u * Real.exp (-δ * u) ≤ δ⁻¹ := by
  have hx : δ * u ≤ Real.exp (δ * u) := by
    have := Real.add_one_le_exp (δ * u)
    linarith
  have hpos : (0 : ℝ) < Real.exp (δ * u) := Real.exp_pos _
  have hneg : Real.exp (-δ * u) = (Real.exp (δ * u))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hneg, mul_inv_le_iff₀ hpos, inv_mul_eq_div, le_div_iff₀ hδ]
  nlinarith [hx, hpos]

/-- **The first-moment kernel is integrable strictly right of the abscissa.** -/
theorem integrableOn_mul_exp_neg_of_gt_abscissa {ν : Measure ℝ} {c b : ℝ} (hc : IsAbscissa ν c)
    (hb : c < b) :
    IntegrableOn (fun u : ℝ => u * Real.exp (-b * u)) (Ioi (0 : ℝ)) ν := by
  set b' : ℝ := (c + b) / 2 with hb'
  have hcb' : c < b' := by rw [hb']; linarith
  have hb'b : b' < b := by rw [hb']; linarith
  set δ : ℝ := b - b' with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hbase : IntegrableOn (fun u : ℝ => Real.exp (-b' * u)) (Ioi (0 : ℝ)) ν :=
    integrableOn_exp_neg_of_gt_abscissa hc hcb'
  have hmaj : IntegrableOn (fun u : ℝ => δ⁻¹ * Real.exp (-b' * u)) (Ioi (0 : ℝ)) ν :=
    hbase.const_mul _
  refine Integrable.mono' hmaj
    ((continuous_id.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
  have hsplit : Real.exp (-b * u) = Real.exp (-δ * u) * Real.exp (-b' * u) := by
    rw [← Real.exp_add]
    congr 1
    rw [hδ]
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ u * Real.exp (-b * u)), hsplit,
    ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_exp_neg_le hδ0) (Real.exp_pos _).le

/-- **The transform differentiates into the negative first moment.** -/
theorem hasDerivAt_laplaceReal {ν : Measure ℝ} {c a : ℝ} (hc : IsAbscissa ν c) (ha : c < a) :
    HasDerivAt (laplaceReal ν) (-laplaceMomentReal ν a 1) a := by
  set ε : ℝ := (a - c) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set s : Set ℝ := Ioo (a - ε) (a + ε) with hs
  have hsnhds : s ∈ 𝓝 a := Ioo_mem_nhds (by linarith) (by linarith)
  have hlow : c < a - ε := by rw [hε]; linarith
  -- the dominating function
  have hbound : IntegrableOn (fun u : ℝ => u * Real.exp (-(a - ε) * u)) (Ioi (0 : ℝ)) ν :=
    integrableOn_mul_exp_neg_of_gt_abscissa hc hlow
  have hmeasF : ∀ᶠ x : ℝ in 𝓝 a,
      AEStronglyMeasurable (fun u : ℝ => Real.exp (-x * u)) (ν.restrict (Ioi (0 : ℝ))) := by
    filter_upwards with x
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hInt : Integrable (fun u : ℝ => Real.exp (-a * u)) (ν.restrict (Ioi (0 : ℝ))) :=
    integrableOn_exp_neg_of_gt_abscissa hc ha
  have hmeasF' : AEStronglyMeasurable (fun u : ℝ => -(u * Real.exp (-a * u)))
      (ν.restrict (Ioi (0 : ℝ))) :=
    ((continuous_id.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).neg).aestronglyMeasurable
  have hdom : ∀ᵐ u ∂(ν.restrict (Ioi (0 : ℝ))), ∀ x ∈ s,
      ‖-(u * Real.exp (-x * u))‖ ≤ u * Real.exp (-(a - ε) * u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu x hx
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    have hxlow : a - ε ≤ x := le_of_lt (hs ▸ hx).1
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ hu0
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hu0, hxlow]
  have hderiv : ∀ᵐ u ∂(ν.restrict (Ioi (0 : ℝ))), ∀ x ∈ s,
      HasDerivAt (fun y : ℝ => Real.exp (-y * u)) (-(u * Real.exp (-x * u))) x := by
    filter_upwards with u x _
    have h1 : HasDerivAt (fun y : ℝ => -y * u) (-u) x := by
      have h0 : HasDerivAt (fun y : ℝ => (-u) * y) ((-u) * 1) x := (hasDerivAt_id x).const_mul (-u)
      refine h0.congr_deriv (by ring) |>.congr_of_eventuallyEq ?_
      filter_upwards with y
      ring
    have := h1.exp
    refine this.congr_deriv ?_
    ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun x u => Real.exp (-x * u))
    (F' := fun x u => -(u * Real.exp (-x * u))) (bound := fun u => u * Real.exp (-(a - ε) * u))
    hsnhds hmeasF hInt hmeasF' hdom hbound hderiv
  have hval : (∫ u in Ioi (0 : ℝ), -(u * Real.exp (-a * u)) ∂ν) = -laplaceMomentReal ν a 1 := by
    rw [integral_neg, laplaceMomentReal]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp
  rw [← hval]
  exact hmain.2

/-! ## The whole moment tower -/

/-- The power bound `u^n e^{-δu} ≤ n!/δ^n`, from `x^n/n! ≤ e^x`. -/
theorem pow_mul_exp_neg_le {δ u : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u) (n : ℕ) :
    u ^ n * Real.exp (-δ * u) ≤ (n.factorial : ℝ) / δ ^ n := by
  have hx : (δ * u) ^ n / (n.factorial : ℝ) ≤ Real.exp (δ * u) :=
    Real.pow_div_factorial_le_exp (δ * u) (by positivity) n
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hpos : (0 : ℝ) < Real.exp (δ * u) := Real.exp_pos _
  have hneg : Real.exp (-δ * u) = (Real.exp (δ * u))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hsplit : (δ * u) ^ n = δ ^ n * u ^ n := mul_pow δ u n
  rw [hsplit] at hx
  have hδn : (0 : ℝ) < δ ^ n := pow_pos hδ n
  have hkey : δ ^ n * u ^ n ≤ (n.factorial : ℝ) * Real.exp (δ * u) := by
    rw [div_le_iff₀ hfac] at hx
    linarith [hx]
  rw [hneg, mul_inv_le_iff₀ hpos]
  calc u ^ n = (δ ^ n * u ^ n) / δ ^ n := by field_simp
    _ ≤ ((n.factorial : ℝ) * Real.exp (δ * u)) / δ ^ n := by gcongr
    _ = (n.factorial : ℝ) / δ ^ n * Real.exp (δ * u) := by ring

/-- **Every moment kernel is integrable strictly right of the abscissa.** -/
theorem integrableOn_pow_mul_exp_neg_of_gt_abscissa {ν : Measure ℝ} {c b : ℝ}
    (hc : IsAbscissa ν c) (hb : c < b) (n : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-b * u)) (Ioi (0 : ℝ)) ν := by
  set b' : ℝ := (c + b) / 2 with hb'
  have hcb' : c < b' := by rw [hb']; linarith
  have hb'b : b' < b := by rw [hb']; linarith
  set δ : ℝ := b - b' with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hbase : IntegrableOn (fun u : ℝ => Real.exp (-b' * u)) (Ioi (0 : ℝ)) ν :=
    integrableOn_exp_neg_of_gt_abscissa hc hcb'
  have hmaj : IntegrableOn
      (fun u : ℝ => ((n.factorial : ℝ) / δ ^ n) * Real.exp (-b' * u)) (Ioi (0 : ℝ)) ν :=
    hbase.const_mul _
  refine Integrable.mono' hmaj
    (((continuous_pow n).mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
  have hsplit : Real.exp (-b * u) = Real.exp (-δ * u) * Real.exp (-b' * u) := by
    rw [← Real.exp_add]
    congr 1
    rw [hδ]
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ n * Real.exp (-b * u)),
    hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (pow_mul_exp_neg_le hδ0 hu0 n) (Real.exp_pos _).le

/-- **Each moment differentiates into the next.** -/
theorem hasDerivAt_laplaceMomentReal {ν : Measure ℝ} {c a : ℝ} (hc : IsAbscissa ν c) (ha : c < a)
    (n : ℕ) :
    HasDerivAt (fun σ : ℝ => laplaceMomentReal ν σ n) (-laplaceMomentReal ν a (n + 1)) a := by
  set ε : ℝ := (a - c) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set s : Set ℝ := Ioo (a - ε) (a + ε) with hs
  have hsnhds : s ∈ 𝓝 a := Ioo_mem_nhds (by linarith) (by linarith)
  have hlow : c < a - ε := by rw [hε]; linarith
  have hbound : IntegrableOn (fun u : ℝ => u ^ (n + 1) * Real.exp (-(a - ε) * u))
      (Ioi (0 : ℝ)) ν := integrableOn_pow_mul_exp_neg_of_gt_abscissa hc hlow (n + 1)
  have hmeasF : ∀ᶠ x : ℝ in 𝓝 a,
      AEStronglyMeasurable (fun u : ℝ => u ^ n * Real.exp (-x * u))
        (ν.restrict (Ioi (0 : ℝ))) := by
    filter_upwards with x
    exact (((continuous_pow n).mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)))).aestronglyMeasurable
  have hInt : Integrable (fun u : ℝ => u ^ n * Real.exp (-a * u)) (ν.restrict (Ioi (0 : ℝ))) :=
    integrableOn_pow_mul_exp_neg_of_gt_abscissa hc ha n
  have hmeasF' : AEStronglyMeasurable (fun u : ℝ => -(u ^ (n + 1) * Real.exp (-a * u)))
      (ν.restrict (Ioi (0 : ℝ))) :=
    ((((continuous_pow (n + 1)).mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)))).neg).aestronglyMeasurable
  have hdom : ∀ᵐ u ∂(ν.restrict (Ioi (0 : ℝ))), ∀ x ∈ s,
      ‖-(u ^ (n + 1) * Real.exp (-x * u))‖ ≤ u ^ (n + 1) * Real.exp (-(a - ε) * u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu x hx
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    have hxlow : a - ε ≤ x := le_of_lt (hs ▸ hx).1
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hu0, hxlow]
  have hderiv : ∀ᵐ u ∂(ν.restrict (Ioi (0 : ℝ))), ∀ x ∈ s,
      HasDerivAt (fun y : ℝ => u ^ n * Real.exp (-y * u))
        (-(u ^ (n + 1) * Real.exp (-x * u))) x := by
    filter_upwards with u x _
    have h1 : HasDerivAt (fun y : ℝ => -y * u) (-u) x := by
      have h0 : HasDerivAt (fun y : ℝ => (-u) * y) ((-u) * 1) x := (hasDerivAt_id x).const_mul (-u)
      refine h0.congr_deriv (by ring) |>.congr_of_eventuallyEq ?_
      filter_upwards with y
      ring
    have hexp := h1.exp
    have hscaled := hexp.const_mul (u ^ n)
    refine hscaled.congr_deriv ?_
    rw [pow_succ]
    ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x u => u ^ n * Real.exp (-x * u))
    (F' := fun x u => -(u ^ (n + 1) * Real.exp (-x * u)))
    (bound := fun u => u ^ (n + 1) * Real.exp (-(a - ε) * u))
    hsnhds hmeasF hInt hmeasF' hdom hbound hderiv
  have hval : (∫ u in Ioi (0 : ℝ), -(u ^ (n + 1) * Real.exp (-a * u)) ∂ν)
      = -laplaceMomentReal ν a (n + 1) := by
    rw [integral_neg, laplaceMomentReal]
  rw [← hval]
  exact hmain.2

/-- **The moment tower is the derivative tower.**  The `k`-th derivative of the transform at a real
point right of the abscissa is `(−1)^k` times the `k`-th moment. -/
theorem iteratedDeriv_laplaceReal {ν : Measure ℝ} {c : ℝ} (hc : IsAbscissa ν c) :
    ∀ (k : ℕ) (a : ℝ), c < a →
      iteratedDeriv k (laplaceReal ν) a = (-1 : ℝ) ^ k * laplaceMomentReal ν a k := by
  intro k
  induction k with
  | zero =>
    intro a _
    rw [iteratedDeriv_zero, laplaceReal, laplaceMomentReal]
    simp
  | succ n ih =>
    intro a ha
    have hfun : Set.EqOn (iteratedDeriv n (laplaceReal ν))
        (fun σ : ℝ => (-1 : ℝ) ^ n * laplaceMomentReal ν σ n) (Ioi c) := by
      intro σ hσ
      exact ih σ hσ
    have hopen : IsOpen (Ioi c) := isOpen_Ioi
    have hmem : a ∈ Ioi c := ha
    have hd : HasDerivAt (fun σ : ℝ => (-1 : ℝ) ^ n * laplaceMomentReal ν σ n)
        ((-1 : ℝ) ^ n * (-laplaceMomentReal ν a (n + 1))) a :=
      (hasDerivAt_laplaceMomentReal hc ha n).const_mul _
    have hd' : HasDerivAt (iteratedDeriv n (laplaceReal ν))
        ((-1 : ℝ) ^ n * (-laplaceMomentReal ν a (n + 1))) a :=
      hd.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) hfun)
    rw [iteratedDeriv_succ, hd'.deriv]
    ring

/-! ## Landau's theorem -/

theorem laplaceMomentReal_nonneg {ν : Measure ℝ} (a : ℝ) (k : ℕ) :
    0 ≤ laplaceMomentReal ν a k := by
  rw [laplaceMomentReal]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
  positivity

/-- Right of the abscissa the extended-real moment is the Bochner moment. -/
theorem laplaceMoment_eq_ofReal {ν : Measure ℝ} {c a : ℝ} (hc : IsAbscissa ν c) (ha : c < a)
    (k : ℕ) :
    laplaceMoment ν a k = ENNReal.ofReal (laplaceMomentReal ν a k) := by
  have hint : IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-a * u)) (Ioi (0 : ℝ)) ν :=
    integrableOn_pow_mul_exp_neg_of_gt_abscissa hc ha k
  have hnn : 0 ≤ᵐ[ν.restrict (Ioi (0 : ℝ))] fun u : ℝ => u ^ k * Real.exp (-a * u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    positivity
  rw [laplaceMoment, laplaceMomentReal, ← ofReal_integral_eq_lintegral_ofReal hint hnn]

/-- **Landau's theorem.**  The transform of a nonnegative measure has no convergent Taylor
expansion at a real point with radius exceeding the distance to the abscissa: the moment series
past that radius diverges. -/
theorem not_summable_moment_beyond_abscissa {ν : Measure ℝ} {c a t : ℝ} (hc : IsAbscissa ν c)
    (ha : c < a) (ht : 0 ≤ t) (hgt : a - c < t)
    (h : Summable fun k : ℕ => t ^ k / (k.factorial : ℝ) * laplaceMomentReal ν a k) : False := by
  have hnn : ∀ k : ℕ, 0 ≤ t ^ k / (k.factorial : ℝ) * laplaceMomentReal ν a k := by
    intro k
    have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have := laplaceMomentReal_nonneg (ν := ν) a k
    positivity
  have hsum : (∑' k : ℕ, ENNReal.ofReal (t ^ k / (k.factorial : ℝ) * laplaceMomentReal ν a k))
      = ENNReal.ofReal (∑' k : ℕ, t ^ k / (k.factorial : ℝ) * laplaceMomentReal ν a k) :=
    (ENNReal.ofReal_tsum_of_nonneg hnn h).symm
  have hcongr : (∑' k : ℕ, ENNReal.ofReal (t ^ k / (k.factorial : ℝ)) * laplaceMoment ν a k)
      = ∑' k : ℕ, ENNReal.ofReal (t ^ k / (k.factorial : ℝ) * laplaceMomentReal ν a k) := by
    refine tsum_congr fun k => ?_
    have hfac : (0 : ℝ) ≤ t ^ k / (k.factorial : ℝ) := by
      have : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
      positivity
    rw [laplaceMoment_eq_ofReal hc ha k, ← ENNReal.ofReal_mul hfac]
  have hfinite : (∑' k : ℕ, ENNReal.ofReal (t ^ k / (k.factorial : ℝ)) * laplaceMoment ν a k)
      ≠ ⊤ := by
    rw [hcongr, hsum]
    exact ENNReal.ofReal_ne_top
  exact hfinite (moments_eq_top_of_gt_abscissaDist hc ht hgt)

/-- **Landau's theorem in derivative form.**  Since the `k`-th derivative of the transform at a real
point is `(−1)^k` times the `k`-th moment, a convergent Taylor series at a point right of the
abscissa cannot have radius exceeding the distance to it. -/
theorem not_summable_iteratedDeriv_beyond_abscissa {ν : Measure ℝ} {c a t : ℝ}
    (hc : IsAbscissa ν c) (ha : c < a) (ht : 0 ≤ t) (hgt : a - c < t)
    (h : Summable fun k : ℕ =>
      t ^ k / (k.factorial : ℝ) * |iteratedDeriv k (laplaceReal ν) a|) : False := by
  refine not_summable_moment_beyond_abscissa hc ha ht hgt (h.congr fun k => ?_)
  rw [iteratedDeriv_laplaceReal hc k a ha, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (laplaceMomentReal_nonneg a k)]

end GaloisForLFunctions.RHTower

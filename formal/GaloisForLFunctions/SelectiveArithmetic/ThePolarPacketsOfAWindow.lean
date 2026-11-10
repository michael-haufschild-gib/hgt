import GaloisForLFunctions.SelectiveArithmetic.TheMassOfAConductorPaysEveryDominatedContact

/-!
# The polar packets of a window

The contact operator of the primes on a window `[−a, a]` has, on average, the kernel
`e^{|u−v|/2} = 2 cosh(u/2) cosh(v/2) − 2 sinh(u/2) sinh(v/2) − e^{−|u−v|/2}`: a positive square on
`cosh(u/2)`, a negative square on `sinh(u/2)`, and a bounded remainder. The two *polar packets* are
these profiles, cut off smoothly at distance `δ` from the ends of the window:

`E(u) = cosh(u/2) χ(u)`,  `O(u) = sinh(u/2) χ(u)`,  `χ = 1` on `[−a + δ, a − δ]`, `χ = 0` off
`(−a, a)`.

* **Mass and derivative energy** (`integral_evenPolar_sq_le`, `integral_deriv_evenPolar_sq_le`, and
  the same for `O`): `∫ E² ≤ a + sinh a` and `∫ E'² ≤ (½ + 2S/δ)² (a + sinh a)`, with `S` a bound of
  the derivative of the smooth step.
* **The ends of the even packet correlate** (`packetAutocorr_evenPolar_ge`): at a lag
  `0 ≤ y ≤ 2a − 2δ`, `(E ⋆ Ẽ)(y) ≥ ¼ e^{y/2} (2a − 2δ − y)`.
* **The two correlations add up to the polar kernel** (`packetAutocorr_oddPolar_le`):
  `E(u)E(u+y) + O(u)O(u+y) = cosh(u + y/2) χ(u) χ(u+y)`, hence
  `(O ⋆ Õ)(y) ≤ 2a e^{a − y/2} − (E ⋆ Ẽ)(y)`: where the even packet correlates with itself, the odd
  packet anticorrelates.
-/

open Filter Topology MeasureTheory Set
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ

/-! ### The smooth step and the cutoff of a window -/

/-- The derivative of the smooth step is bounded. -/
theorem exists_abs_deriv_smoothTransition_le :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ S := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · have := hC x hx
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · have h0 : deriv Real.smoothTransition x = 0 := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [Iio_mem_nhds h] with y hy
          exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
        rw [he.deriv_eq, deriv_const]
      · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
          filter_upwards [Ioi_mem_nhds h] with y hy
          exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
        rw [he.deriv_eq, deriv_const]
    rw [h0, abs_zero]
    exact le_max_right _ _

/-- The cutoff of the window `[−a, a]` with margin `δ`: `1` on `[−a + δ, a − δ]`, `0` off
`(−a, a)`. -/
def cutoff (a δ u : ℝ) : ℝ :=
  Real.smoothTransition ((a - u) / δ) * Real.smoothTransition ((a + u) / δ)

theorem contDiff_cutoff (a δ : ℝ) : ContDiff ℝ 3 (cutoff a δ) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const δ)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.add contDiff_id).div_const δ))

theorem cutoff_nonneg (a δ u : ℝ) : 0 ≤ cutoff a δ u :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem cutoff_le_one (a δ u : ℝ) : cutoff a δ u ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem cutoff_eq_one {a δ u : ℝ} (hδ : 0 < δ) (hu : |u| ≤ a - δ) : cutoff a δ u = 1 := by
  have h := abs_le.mp hu
  rw [cutoff, Real.smoothTransition.one_of_one_le ((one_le_div hδ).mpr (by linarith [h.2])),
    Real.smoothTransition.one_of_one_le ((one_le_div hδ).mpr (by linarith [h.1])), mul_one]

theorem cutoff_eq_zero {a δ u : ℝ} (hδ : 0 < δ) (hu : a ≤ |u|) : cutoff a δ u = 0 := by
  rcases le_abs.mp hu with h | h
  · rw [cutoff, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le), zero_mul]
  · rw [cutoff, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith : a + u ≤ 0) hδ.le), mul_zero]

theorem abs_lt_of_cutoff_ne_zero {a δ u : ℝ} (hδ : 0 < δ) (hu : cutoff a δ u ≠ 0) : |u| < a :=
  lt_of_not_ge fun h => hu (cutoff_eq_zero hδ h)

/-- The derivative of the cutoff is at most `2S/δ`. -/
theorem abs_deriv_cutoff_le {S : ℝ} (hS : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ S) {δ : ℝ}
    (hδ : 0 < δ) (a u : ℝ) : |deriv (cutoff a δ) u| ≤ 2 * S / δ := by
  have hs : ∀ x : ℝ, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
    fun x => ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt
  have h1 : HasDerivAt (fun v : ℝ => (a - v) / δ) (-1 / δ) u :=
    ((hasDerivAt_id' u).const_sub a).div_const δ
  have h2 : HasDerivAt (fun v : ℝ => (a + v) / δ) (1 / δ) u :=
    ((hasDerivAt_id' u).const_add a).div_const δ
  have hA : HasDerivAt (Real.smoothTransition ∘ fun v : ℝ => (a - v) / δ)
      (deriv Real.smoothTransition ((a - u) / δ) * (-1 / δ)) u :=
    HasDerivAt.comp (h₂ := Real.smoothTransition) (h := fun v : ℝ => (a - v) / δ) u (hs _) h1
  have hB : HasDerivAt (Real.smoothTransition ∘ fun v : ℝ => (a + v) / δ)
      (deriv Real.smoothTransition ((a + u) / δ) * (1 / δ)) u :=
    HasDerivAt.comp (h₂ := Real.smoothTransition) (h := fun v : ℝ => (a + v) / δ) u (hs _) h2
  have hprod : HasDerivAt (cutoff a δ)
      (deriv Real.smoothTransition ((a - u) / δ) * (-1 / δ) *
          Real.smoothTransition ((a + u) / δ) +
        Real.smoothTransition ((a - u) / δ) *
          (deriv Real.smoothTransition ((a + u) / δ) * (1 / δ))) u :=
    hA.mul hB
  rw [hprod.deriv]
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS 0)
  have e1 : |deriv Real.smoothTransition ((a - u) / δ) * (-1 / δ) *
      Real.smoothTransition ((a + u) / δ)| ≤ S / δ := by
    rw [abs_mul, abs_mul, abs_div, abs_neg, abs_one, abs_of_pos hδ,
      abs_of_nonneg (Real.smoothTransition.nonneg _)]
    calc |deriv Real.smoothTransition ((a - u) / δ)| * (1 / δ) *
          Real.smoothTransition ((a + u) / δ)
        ≤ S * (1 / δ) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hS _) (by positivity))
            (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) (by positivity)
      _ = S / δ := by ring
  have e2 : |Real.smoothTransition ((a - u) / δ) *
      (deriv Real.smoothTransition ((a + u) / δ) * (1 / δ))| ≤ S / δ := by
    rw [abs_mul, abs_mul, abs_div, abs_one, abs_of_pos hδ,
      abs_of_nonneg (Real.smoothTransition.nonneg _)]
    calc Real.smoothTransition ((a - u) / δ) *
          (|deriv Real.smoothTransition ((a + u) / δ)| * (1 / δ))
        ≤ 1 * (S * (1 / δ)) :=
          mul_le_mul (Real.smoothTransition.le_one _)
            (mul_le_mul_of_nonneg_right (hS _) (by positivity)) (by positivity) zero_le_one
      _ = S / δ := by ring
  calc _ ≤ S / δ + S / δ := (abs_add_le _ _).trans (add_le_add e1 e2)
    _ = 2 * S / δ := by ring

/-! ### Hyperbolic bounds -/

theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  have h1 := Real.sinh_lt_cosh x
  have h2 := Real.sinh_lt_cosh (-x)
  rw [Real.sinh_neg, Real.cosh_neg] at h2
  exact abs_le.mpr ⟨by linarith, h1.le⟩

theorem cosh_le_exp_of_abs_le {x b : ℝ} (h : |x| ≤ b) : Real.cosh x ≤ Real.exp b := by
  have h' := abs_le.mp h
  have h1 : Real.exp x ≤ Real.exp b := Real.exp_le_exp.mpr h'.2
  have h2 : Real.exp (-x) ≤ Real.exp b := Real.exp_le_exp.mpr (by linarith [h'.1])
  rw [Real.cosh_eq]
  linarith

theorem half_exp_le_cosh (x : ℝ) : Real.exp x / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  linarith [Real.exp_pos (-x)]

theorem half_exp_neg_le_cosh (x : ℝ) : Real.exp (-x) / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  linarith [Real.exp_pos x]

/-- `∫_{−a}^{a} cosh²(u/2) du = a + sinh a`. -/
theorem integral_cosh_half_sq {a : ℝ} (ha : 0 ≤ a) :
    ∫ u in Icc (-a) a, Real.cosh (u / 2) ^ 2 = a + Real.sinh a := by
  have hd : ∀ u : ℝ, HasDerivAt (fun v : ℝ => (v + Real.sinh v) / 2)
      ((1 + Real.cosh u) / 2) u := fun u =>
    ((hasDerivAt_id u).add (Real.hasDerivAt_sinh u)).div_const 2
  have hpt : ∀ u : ℝ, Real.cosh (u / 2) ^ 2 = (1 + Real.cosh u) / 2 := fun u => by
    have h1 := Real.cosh_two_mul (u / 2)
    have h2 := Real.cosh_sq (u / 2)
    rw [show 2 * (u / 2) = u by ring] at h1
    linarith
  have hcont : Continuous fun u : ℝ => (1 + Real.cosh u) / 2 := by fun_prop
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  simp_rw [hpt]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hcont.intervalIntegrable _ _), Real.sinh_neg]
  ring

/-- A continuous function bounded by `K cosh(u/2)` and vanishing off `[−a, a]` has square
integral at most `K² (a + sinh a)`. -/
theorem integral_sq_le_of_abs_le_cosh {g : ℝ → ℝ} (hg : Continuous g) {a K : ℝ} (ha : 0 ≤ a)
    (hb : ∀ u, |g u| ≤ K * Real.cosh (u / 2)) (h0 : ∀ u, a < |u| → g u = 0) :
    ∫ u, g u ^ 2 ≤ K ^ 2 * (a + Real.sinh a) := by
  have hzero : ∀ u, u ∉ Icc (-a) a → g u ^ 2 = 0 := fun u hu => by
    have : a < |u| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl h)
    rw [h0 u this]
    norm_num
  have hcosh : Continuous fun u : ℝ => K ^ 2 * Real.cosh (u / 2) ^ 2 := by fun_prop
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← integral_cosh_half_sq ha,
    ← integral_const_mul]
  refine setIntegral_mono_on (hg.pow 2).integrableOn_Icc hcosh.integrableOn_Icc
    measurableSet_Icc fun u _ => ?_
  have h := hb u
  have hK : 0 ≤ K * Real.cosh (u / 2) := (abs_nonneg _).trans h
  calc g u ^ 2 = |g u| ^ 2 := (sq_abs _).symm
    _ ≤ (K * Real.cosh (u / 2)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = K ^ 2 * Real.cosh (u / 2) ^ 2 := mul_pow _ _ _

/-! ### The two polar packets -/

/-- The even polar packet `cosh(u/2) χ(u)`. -/
def evenPolar (a δ u : ℝ) : ℝ := Real.cosh (u / 2) * cutoff a δ u

/-- The odd polar packet `sinh(u/2) χ(u)`. -/
def oddPolar (a δ u : ℝ) : ℝ := Real.sinh (u / 2) * cutoff a δ u

theorem contDiff_evenPolar (a δ : ℝ) : ContDiff ℝ 3 (evenPolar a δ) :=
  (Real.contDiff_cosh.comp (contDiff_id.div_const 2)).mul (contDiff_cutoff a δ)

theorem contDiff_oddPolar (a δ : ℝ) : ContDiff ℝ 3 (oddPolar a δ) :=
  (Real.contDiff_sinh.comp (contDiff_id.div_const 2)).mul (contDiff_cutoff a δ)

theorem evenPolar_nonneg (a δ u : ℝ) : 0 ≤ evenPolar a δ u :=
  mul_nonneg (Real.cosh_pos _).le (cutoff_nonneg a δ u)

theorem evenPolar_eq_zero {a δ u : ℝ} (hδ : 0 < δ) (hu : a ≤ |u|) : evenPolar a δ u = 0 := by
  rw [evenPolar, cutoff_eq_zero hδ hu, mul_zero]

theorem oddPolar_eq_zero {a δ u : ℝ} (hδ : 0 < δ) (hu : a ≤ |u|) : oddPolar a δ u = 0 := by
  rw [oddPolar, cutoff_eq_zero hδ hu, mul_zero]

theorem evenPolar_eq {a δ u : ℝ} (hδ : 0 < δ) (hu : |u| ≤ a - δ) :
    evenPolar a δ u = Real.cosh (u / 2) := by
  rw [evenPolar, cutoff_eq_one hδ hu, mul_one]

theorem abs_evenPolar_le (a δ u : ℝ) : |evenPolar a δ u| ≤ 1 * Real.cosh (u / 2) := by
  rw [abs_of_nonneg (evenPolar_nonneg a δ u), one_mul]
  exact mul_le_of_le_one_right (Real.cosh_pos _).le (cutoff_le_one a δ u)

theorem abs_oddPolar_le (a δ u : ℝ) : |oddPolar a δ u| ≤ 1 * Real.cosh (u / 2) := by
  rw [oddPolar, abs_mul, abs_of_nonneg (cutoff_nonneg a δ u), one_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (cutoff_le_one a δ u)).trans (abs_sinh_le_cosh _)

theorem hasCompactSupport_evenPolar {a δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (evenPolar a δ) :=
  HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu =>
    evenPolar_eq_zero hδ (by
      rw [mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · exact le_abs.mpr (Or.inr (by linarith))
      · exact le_abs.mpr (Or.inl h.le))

theorem hasCompactSupport_oddPolar {a δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (oddPolar a δ) :=
  HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu =>
    oddPolar_eq_zero hδ (by
      rw [mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · exact le_abs.mpr (Or.inr (by linarith))
      · exact le_abs.mpr (Or.inl h.le))

/-- A packet vanishing off `(−a, a)` has its topological support in `[−a, a]`. -/
theorem tsupport_ofReal_subset_of_eq_zero {f : ℝ → ℝ} {a : ℝ} (h0 : ∀ u, a ≤ |u| → f u = 0) :
    tsupport (fun u => (f u : ℂ)) ⊆ Icc (-a) a := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hxI
  have hx' : a ≤ |x| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hxI
    rcases hxI with h | h
    · exact le_abs.mpr (Or.inr (by linarith))
    · exact le_abs.mpr (Or.inl h.le)
  exact hx (by
    show ((f x : ℝ) : ℂ) = 0
    rw [h0 x hx', Complex.ofReal_zero])

/-! ### Mass and derivative energy -/

theorem integral_evenPolar_sq_le {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    ∫ u, evenPolar a δ u ^ 2 ≤ a + Real.sinh a := by
  have h := integral_sq_le_of_abs_le_cosh (contDiff_evenPolar a δ).continuous ha
    (abs_evenPolar_le a δ) fun u hu => evenPolar_eq_zero hδ hu.le
  rwa [one_pow, one_mul] at h

theorem integral_oddPolar_sq_le {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    ∫ u, oddPolar a δ u ^ 2 ≤ a + Real.sinh a := by
  have h := integral_sq_le_of_abs_le_cosh (contDiff_oddPolar a δ).continuous ha
    (abs_oddPolar_le a δ) fun u hu => oddPolar_eq_zero hδ hu.le
  rwa [one_pow, one_mul] at h

/-- The derivative of a function vanishing off `[−a, a]` vanishes off `[−a, a]`. -/
theorem deriv_eq_zero_of_abs_gt {g : ℝ → ℝ} {a : ℝ} (h0 : ∀ u, a ≤ |u| → g u = 0) {u : ℝ}
    (hu : a < |u|) : deriv g u = 0 := by
  have hopen : IsOpen {v : ℝ | a < |v|} := isOpen_lt continuous_const continuous_abs
  have he : g =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hu] with v hv
    exact h0 v (le_of_lt hv)
  rw [he.deriv_eq, deriv_const]

theorem abs_deriv_evenPolar_le {S : ℝ} (hS : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ S)
    {δ : ℝ} (hδ : 0 < δ) (a u : ℝ) :
    |deriv (evenPolar a δ) u| ≤ (1 / 2 + 2 * S / δ) * Real.cosh (u / 2) := by
  have hc : HasDerivAt (fun v : ℝ => Real.cosh (v / 2)) (Real.sinh (u / 2) * (1 / 2)) u :=
    ((hasDerivAt_id' u).div_const 2).cosh
  have hχ : HasDerivAt (cutoff a δ) (deriv (cutoff a δ) u) u :=
    ((contDiff_cutoff a δ).differentiable (by norm_num) u).hasDerivAt
  have hprod : HasDerivAt (evenPolar a δ)
      (Real.sinh (u / 2) * (1 / 2) * cutoff a δ u + Real.cosh (u / 2) * deriv (cutoff a δ) u) u :=
    hc.mul hχ
  rw [hprod.deriv]
  have hcosh := (Real.cosh_pos (u / 2)).le
  have e1 : |Real.sinh (u / 2) * (1 / 2) * cutoff a δ u| ≤ 1 / 2 * Real.cosh (u / 2) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (cutoff_nonneg a δ u),
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc |Real.sinh (u / 2)| * (1 / 2) * cutoff a δ u
        ≤ Real.cosh (u / 2) * (1 / 2) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (abs_sinh_le_cosh _) (by norm_num))
            (cutoff_le_one a δ u) (cutoff_nonneg a δ u) (by positivity)
      _ = 1 / 2 * Real.cosh (u / 2) := by ring
  have e2 : |Real.cosh (u / 2) * deriv (cutoff a δ) u| ≤ 2 * S / δ * Real.cosh (u / 2) := by
    rw [abs_mul, abs_of_nonneg hcosh, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_deriv_cutoff_le hS hδ a u) hcosh
  calc _ ≤ 1 / 2 * Real.cosh (u / 2) + 2 * S / δ * Real.cosh (u / 2) :=
        (abs_add_le _ _).trans (add_le_add e1 e2)
    _ = (1 / 2 + 2 * S / δ) * Real.cosh (u / 2) := by ring

theorem abs_deriv_oddPolar_le {S : ℝ} (hS : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ S)
    {δ : ℝ} (hδ : 0 < δ) (a u : ℝ) :
    |deriv (oddPolar a δ) u| ≤ (1 / 2 + 2 * S / δ) * Real.cosh (u / 2) := by
  have hc : HasDerivAt (fun v : ℝ => Real.sinh (v / 2)) (Real.cosh (u / 2) * (1 / 2)) u :=
    ((hasDerivAt_id' u).div_const 2).sinh
  have hχ : HasDerivAt (cutoff a δ) (deriv (cutoff a δ) u) u :=
    ((contDiff_cutoff a δ).differentiable (by norm_num) u).hasDerivAt
  have hprod : HasDerivAt (oddPolar a δ)
      (Real.cosh (u / 2) * (1 / 2) * cutoff a δ u + Real.sinh (u / 2) * deriv (cutoff a δ) u) u :=
    hc.mul hχ
  rw [hprod.deriv]
  have hcosh := (Real.cosh_pos (u / 2)).le
  have e1 : |Real.cosh (u / 2) * (1 / 2) * cutoff a δ u| ≤ 1 / 2 * Real.cosh (u / 2) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (cutoff_nonneg a δ u),
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg hcosh]
    calc Real.cosh (u / 2) * (1 / 2) * cutoff a δ u
        ≤ Real.cosh (u / 2) * (1 / 2) * 1 :=
          mul_le_mul_of_nonneg_left (cutoff_le_one a δ u) (by positivity)
      _ = 1 / 2 * Real.cosh (u / 2) := by ring
  have e2 : |Real.sinh (u / 2) * deriv (cutoff a δ) u| ≤ 2 * S / δ * Real.cosh (u / 2) := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul (abs_deriv_cutoff_le hS hδ a u) (abs_sinh_le_cosh _) (abs_nonneg _)
      ((abs_nonneg _).trans (abs_deriv_cutoff_le hS hδ a u))
  calc _ ≤ 1 / 2 * Real.cosh (u / 2) + 2 * S / δ * Real.cosh (u / 2) :=
        (abs_add_le _ _).trans (add_le_add e1 e2)
    _ = (1 / 2 + 2 * S / δ) * Real.cosh (u / 2) := by ring

theorem integral_deriv_evenPolar_sq_le {S : ℝ}
    (hS : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ S) {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    ∫ u, deriv (evenPolar a δ) u ^ 2 ≤ (1 / 2 + 2 * S / δ) ^ 2 * (a + Real.sinh a) :=
  integral_sq_le_of_abs_le_cosh ((contDiff_evenPolar a δ).continuous_deriv (by norm_num)) ha
    (abs_deriv_evenPolar_le hS hδ a)
    fun _ hu => deriv_eq_zero_of_abs_gt (fun _ hv => evenPolar_eq_zero hδ hv) hu

theorem integral_deriv_oddPolar_sq_le {S : ℝ}
    (hS : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ S) {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    ∫ u, deriv (oddPolar a δ) u ^ 2 ≤ (1 / 2 + 2 * S / δ) ^ 2 * (a + Real.sinh a) :=
  integral_sq_le_of_abs_le_cosh ((contDiff_oddPolar a δ).continuous_deriv (by norm_num)) ha
    (abs_deriv_oddPolar_le hS hδ a)
    fun _ hu => deriv_eq_zero_of_abs_gt (fun _ hv => oddPolar_eq_zero hδ hv) hu

/-! ### Correlations -/

/-- The autocorrelation of a packet is at most its mass. -/
theorem abs_packetAutocorr_le {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : ℝ) : |packetAutocorr f x| ≤ ∫ u, f u ^ 2 := by
  have hsq : Integrable fun u => f u * f u :=
    (hf.mul hf).integrable_of_hasCompactSupport hfc.mul_right
  have hsq' : Integrable fun u => f (u + x) * f (u + x) := hsq.comp_add_right x
  have hprod : Integrable fun u => f u * f (u + x) :=
    (hf.mul (hf.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hfc.mul_right
  have hshift : ∫ u, f (u + x) * f (u + x) = ∫ u, f u * f u :=
    integral_add_right_eq_self (fun u => f u * f u) x
  have hmass : ∫ u, f u ^ 2 = ∫ u, f u * f u :=
    integral_congr_ae (Eventually.of_forall fun u => sq (f u))
  rw [hmass]
  calc |packetAutocorr f x| ≤ ∫ u, |f u * f (u + x)| := abs_integral_le_integral_abs
    _ ≤ ∫ u, (f u * f u + f (u + x) * f (u + x)) / 2 := by
        refine integral_mono hprod.abs ((hsq.add hsq').div_const 2) fun u => ?_
        show |f u * f (u + x)| ≤ (f u * f u + f (u + x) * f (u + x)) / 2
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (f u - f (u + x)), sq_nonneg (f u + f (u + x))]
    _ = ∫ u, f u * f u := by
        rw [integral_div, integral_add hsq hsq', hshift]
        ring

theorem integrable_evenPolar_mul {a δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    Integrable fun u => evenPolar a δ u * evenPolar a δ (u + y) :=
  ((contDiff_evenPolar a δ).continuous.mul ((contDiff_evenPolar a δ).continuous.comp
    (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hasCompactSupport_evenPolar hδ).mul_right

theorem integrable_oddPolar_mul {a δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    Integrable fun u => oddPolar a δ u * oddPolar a δ (u + y) :=
  ((contDiff_oddPolar a δ).continuous.mul ((contDiff_oddPolar a δ).continuous.comp
    (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hasCompactSupport_oddPolar hδ).mul_right

theorem packetAutocorr_evenPolar_nonneg (a δ y : ℝ) : 0 ≤ packetAutocorr (evenPolar a δ) y :=
  integral_nonneg fun _ => mul_nonneg (evenPolar_nonneg a δ _) (evenPolar_nonneg a δ _)

/-- **The ends of the even polar packet correlate.** For `0 ≤ y ≤ 2a − 2δ`:
`(E ⋆ Ẽ)(y) ≥ ¼ e^{y/2} (2a − 2δ − y)`. -/
theorem packetAutocorr_evenPolar_ge {a δ : ℝ} (hδ : 0 < δ) {y : ℝ} (hy : 0 ≤ y)
    (hya : y + 2 * δ ≤ 2 * a) :
    Real.exp (y / 2) / 4 * (2 * a - 2 * δ - y) ≤ packetAutocorr (evenPolar a δ) y := by
  have hg : ∫ u, (Icc (-a + δ) (a - δ - y)).indicator (fun _ => Real.exp (y / 2) / 4) u =
      Real.exp (y / 2) / 4 * (2 * a - 2 * δ - y) := by
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  rw [← hg, packetAutocorr]
  refine integral_mono (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc)
    (integrable_evenPolar_mul hδ y) fun u => ?_
  by_cases hu : u ∈ Icc (-a + δ) (a - δ - y)
  · rw [Set.indicator_of_mem hu]
    have h1 : |u| ≤ a - δ := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h2 : |u + y| ≤ a - δ := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rw [evenPolar_eq hδ h1, evenPolar_eq hδ h2]
    have e : Real.exp (y / 2) = Real.exp (-(u / 2)) * Real.exp ((u + y) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have c1 := half_exp_neg_le_cosh (u / 2)
    have c2 := half_exp_le_cosh ((u + y) / 2)
    have p1 := Real.exp_pos (-(u / 2))
    have p2 := Real.exp_pos ((u + y) / 2)
    rw [e]
    nlinarith [mul_le_mul c1 c2 (by positivity) (Real.cosh_pos (u / 2)).le]
  · rw [Set.indicator_of_notMem hu]
    exact mul_nonneg (evenPolar_nonneg a δ _) (evenPolar_nonneg a δ _)

/-- **The correlations of the two polar packets add up to the polar kernel.** At every lag `y`:
`(O ⋆ Õ)(y) ≤ 2a e^{a − y/2} − (E ⋆ Ẽ)(y)`. -/
theorem packetAutocorr_oddPolar_le {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (y : ℝ) :
    packetAutocorr (oddPolar a δ) y ≤
      2 * a * Real.exp (a - y / 2) - packetAutocorr (evenPolar a δ) y := by
  have hg : ∫ u, (Icc (-a) a).indicator (fun _ => Real.exp (a - y / 2)) u =
      2 * a * Real.exp (a - y / 2) := by
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  have hsum : packetAutocorr (oddPolar a δ) y + packetAutocorr (evenPolar a δ) y ≤
      2 * a * Real.exp (a - y / 2) := by
    rw [← hg, packetAutocorr, packetAutocorr,
      ← integral_add (integrable_oddPolar_mul hδ y) (integrable_evenPolar_mul hδ y)]
    refine integral_mono ((integrable_oddPolar_mul hδ y).add (integrable_evenPolar_mul hδ y))
      (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc) fun u => ?_
    have hkey : oddPolar a δ u * oddPolar a δ (u + y) +
        evenPolar a δ u * evenPolar a δ (u + y) =
        Real.cosh (u + y / 2) * (cutoff a δ u * cutoff a δ (u + y)) := by
      have hc := Real.cosh_add (u / 2) ((u + y) / 2)
      rw [show u / 2 + (u + y) / 2 = u + y / 2 by ring] at hc
      rw [oddPolar, oddPolar, evenPolar, evenPolar, hc]
      ring
    show oddPolar a δ u * oddPolar a δ (u + y) + evenPolar a δ u * evenPolar a δ (u + y) ≤ _
    rw [hkey]
    by_cases hz : cutoff a δ u * cutoff a δ (u + y) = 0
    · rw [hz, mul_zero]
      exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) u
    · have h1 := abs_lt.mp (abs_lt_of_cutoff_ne_zero hδ (left_ne_zero_of_mul hz))
      have h2 := abs_lt.mp (abs_lt_of_cutoff_ne_zero hδ (right_ne_zero_of_mul hz))
      have hmem : u ∈ Set.Icc (-a) a := ⟨h1.1.le, h1.2.le⟩
      rw [Set.indicator_of_mem hmem]
      have hcosh : Real.cosh (u + y / 2) ≤ Real.exp (a - y / 2) :=
        cosh_le_exp_of_abs_le (abs_le.mpr ⟨by linarith [h1.1], by linarith [h2.2]⟩)
      have hχ : cutoff a δ u * cutoff a δ (u + y) ≤ 1 :=
        mul_le_one₀ (cutoff_le_one a δ u) (cutoff_nonneg a δ _) (cutoff_le_one a δ _)
      calc Real.cosh (u + y / 2) * (cutoff a δ u * cutoff a δ (u + y))
          ≤ Real.exp (a - y / 2) * 1 :=
            mul_le_mul hcosh hχ (mul_nonneg (cutoff_nonneg a δ _) (cutoff_nonneg a δ _))
              (Real.exp_pos _).le
        _ = Real.exp (a - y / 2) := mul_one _
  linarith

end GaloisForLFunctions.SelectiveArithmetic

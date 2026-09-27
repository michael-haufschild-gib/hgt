import GaloisForLFunctions.RHTower.HedenmalmCompactSourceEigenmode
import GaloisForLFunctions.HTGeometry.PontryaginNeutralEigenvectorBound

/-!
# A rank-two boundary defect with infinitely many off-real source modes

Fix `0 < a < 1/2`, `A > 0` with `cosh A = 1/(2a)`, and `L > 2A`.  With `h(x) = e^{-x⁴}` the
three-bump density

`g(x) = h(x) + a h(x - L) + a h(x + L)`

is positive, even, smooth and dominated by every Gaussian.  Its Fourier transform factors as
`F(z) = H(z)(1 + 2a cos(Lz))`, so it vanishes at `z_n^± = ((2n+1)π ± iA)/L` with
`0 < Im z_n^+ < 1/2`.

The quartic tail envelope `g(y) ≤ g(x) e^{-4(x-L)³(y-x)}` (`L + 1 ≤ x ≤ y`) gives

* finite reciprocal-tail energy, so the source inverse `B = i M_q C` is Hilbert--Schmidt;
* a bound `|u_z| ≤ C g` for the source mode at every zero with `|Im z| ≤ 1`, so each `z_n^+` gives
  a nonzero `L²` eigenvector of `B` with eigenvalue `-1/z_n^+` in the upper half-plane.

The metric `D = M_{1/q}` is bounded, positive and injective and `D B - B† D = i P` with `P` the
rank-two pinned boundary operator.  Nevertheless, a self-adjoint operator on a space whose form is
positive definite on a subspace of codimension `κ` can carry at most `κ` of the eigenvalues
`-1/z_n^+`: a rank-two local defect does not bound the number of off-real source modes.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace UniversalBoundaryCountermodel

open HedenmalmQuantile HedenmalmPrimeTranslation HedenmalmHilbertSchmidt HedenmalmCompactSource

/-! ### Parameters -/

/-- The parameters `0 < a < 1/2`, `A > 0` with `cosh A = 1/(2a)`, and `L > 2A`. -/
structure Params where
  a : ℝ
  A : ℝ
  L : ℝ
  a_pos : 0 < a
  a_lt : a < 1 / 2
  A_pos : 0 < A
  cosh_A : Real.cosh A = 1 / (2 * a)
  L_gt : 2 * A < L

/-- Every `0 < a < 1/2` and `L > 2 arcosh(1/(2a))` give admissible parameters. -/
theorem exists_params {a L : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (hL : 2 * Real.arcosh (1 / (2 * a)) < L) : ∃ P : Params, P.a = a ∧ P.L = L := by
  have h1 : 1 < 1 / (2 * a) := by rw [lt_div_iff₀ (by positivity)]; linarith
  exact ⟨⟨a, Real.arcosh (1 / (2 * a)), L, ha, ha2, Real.arcosh_pos h1,
    Real.cosh_arcosh h1.le, hL⟩, rfl, rfl⟩

variable (P : Params)

theorem Params.L_pos : 0 < P.L := by linarith [P.A_pos, P.L_gt]

/-! ### The quartic profile -/

/-- The quartic profile `h(x) = e^{-x⁴}`. -/
def quarticProfile (x : ℝ) : ℝ := Real.exp (-x ^ 4)

theorem quarticProfile_pos (x : ℝ) : 0 < quarticProfile x := Real.exp_pos _

theorem quarticProfile_le_one (x : ℝ) : quarticProfile x ≤ 1 :=
  Real.exp_le_one_iff.mpr (by nlinarith [pow_two_nonneg (x ^ 2)])

theorem quarticProfile_neg (x : ℝ) : quarticProfile (-x) = quarticProfile x := by
  simp [quarticProfile, Even.neg_pow (by decide : Even 4)]

theorem continuous_quarticProfile : Continuous quarticProfile := by
  unfold quarticProfile; fun_prop

theorem contDiff_quarticProfile : ContDiff ℝ ⊤ quarticProfile := by
  unfold quarticProfile; fun_prop

/-- `e^{-y⁴} ≤ e^{c²} e^{-2c y²}`. -/
theorem quarticProfile_le_gaussian (c y : ℝ) :
    quarticProfile y ≤ Real.exp (c ^ 2) * Real.exp (-(2 * c) * y ^ 2) := by
  rw [quarticProfile, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (y ^ 2 - c)])

/-! ### The three-bump density -/

/-- The density `g = h + a h(· - L) + a h(· + L)`. -/
def density (x : ℝ) : ℝ :=
  quarticProfile x + P.a * quarticProfile (x - P.L) + P.a * quarticProfile (x + P.L)

theorem density_pos (x : ℝ) : 0 < density P x := by
  have := P.a_pos
  unfold density
  have h1 := quarticProfile_pos x
  have h2 := quarticProfile_pos (x - P.L)
  have h3 := quarticProfile_pos (x + P.L)
  positivity

theorem density_neg (x : ℝ) : density P (-x) = density P x := by
  unfold density
  rw [quarticProfile_neg, show -x - P.L = -(x + P.L) by ring, quarticProfile_neg,
    show -x + P.L = -(x - P.L) by ring, quarticProfile_neg]
  ring

theorem continuous_density : Continuous (density P) := by
  unfold density
  have := continuous_quarticProfile
  fun_prop

theorem contDiff_density : ContDiff ℝ ⊤ (density P) := by
  unfold density
  have h := contDiff_quarticProfile
  exact (h.add (contDiff_const.mul (h.comp (contDiff_id.sub contDiff_const)))).add
    (contDiff_const.mul (h.comp (contDiff_id.add contDiff_const)))

theorem density_le (x : ℝ) : density P x ≤ 1 + 2 * P.a := by
  have := P.a_pos
  unfold density
  nlinarith [quarticProfile_le_one x, quarticProfile_le_one (x - P.L),
    quarticProfile_le_one (x + P.L)]

/-- **Super-Gaussian tails.** For every `c ≥ 0`, `g(x) ≤ (1 + 2a) e^{c² + 2cL²} e^{-c x²}`. -/
theorem density_le_gaussian {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    density P x ≤ (1 + 2 * P.a) * Real.exp (c ^ 2 + 2 * c * P.L ^ 2) * Real.exp (-c * x ^ 2) := by
  have ha := P.a_pos
  have hshift : ∀ s : ℝ, |s| ≤ P.L → quarticProfile (x - s) ≤
      Real.exp (c ^ 2 + 2 * c * P.L ^ 2) * Real.exp (-c * x ^ 2) := by
    intro s hs
    refine (quarticProfile_le_gaussian c (x - s)).trans ?_
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hs2 : s ^ 2 ≤ P.L ^ 2 := by
      have := abs_le.mp hs; nlinarith [abs_nonneg s, sq_abs s]
    nlinarith [sq_nonneg (x - 2 * s), mul_nonneg hc (sq_nonneg (x - 2 * s)), mul_le_mul_of_nonneg_left hs2 hc]
  have h0 := hshift 0 (by simp [P.L_pos.le])
  have h1 := hshift P.L (by rw [abs_of_pos P.L_pos])
  have h2 := hshift (-P.L) (by rw [abs_neg, abs_of_pos P.L_pos])
  rw [sub_zero] at h0
  rw [sub_neg_eq_add] at h2
  unfold density
  nlinarith

/-- `g(x) e^{bx}` is integrable for every real `b`. -/
theorem integrable_density_mul_exp (b : ℝ) :
    Integrable (fun x => density P x * Real.exp (b * x)) := by
  set K := (1 + 2 * P.a) * Real.exp (1 ^ 2 + 2 * 1 * P.L ^ 2)
  have hK : 0 ≤ K := by have := P.a_pos; positivity
  have hdom : Integrable (fun x : ℝ => K * Real.exp (b ^ 2 / 2) * Real.exp (-(1 / 2) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
  refine hdom.mono' ((continuous_density P).mul (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have hg := density_le_gaussian P zero_le_one x
  have hpos := (density_pos P x).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpos (Real.exp_pos _).le)]
  calc density P x * Real.exp (b * x)
      ≤ K * Real.exp (-1 * x ^ 2) * Real.exp (b * x) :=
        mul_le_mul_of_nonneg_right hg (Real.exp_pos _).le
    _ = K * (Real.exp (-1 * x ^ 2 + b * x)) := by rw [Real.exp_add]; ring
    _ ≤ K * (Real.exp (b ^ 2 / 2 + -(1 / 2) * x ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK
        nlinarith [sq_nonneg (x - b)]
    _ = K * Real.exp (b ^ 2 / 2) * Real.exp (-(1 / 2) * x ^ 2) := by rw [Real.exp_add]; ring

theorem integrable_density : Integrable (density P) := by
  simpa using integrable_density_mul_exp P 0

/-- The three-bump source. -/
def source : PositiveDensitySource where
  k := density P
  continuous_k := continuous_density P
  pos_k := density_pos P
  integrable_k := integrable_density P

theorem source_k : (source P).k = density P := rfl

theorem hasShiftedTail_source (z : ℂ) : HasShiftedTail (source P) z :=
  integrable_density_mul_exp P (-z.im)

/-! ### The Fourier transform and its zeros -/

/-- The quartic Fourier transform `H(z) = ∫ e^{-x⁴} e^{izx} dx`. -/
def quarticTransform (z : ℂ) : ℂ := ∫ x, (quarticProfile x : ℂ) * sourceChar z x

/-- `e^{-x⁴} e^{bx}` is integrable. -/
theorem integrable_quarticProfile_mul_exp (b : ℝ) :
    Integrable fun x => quarticProfile x * Real.exp (b * x) := by
  have hdom : Integrable (fun x : ℝ => Real.exp (1 + b ^ 2 / 4) * Real.exp (-1 * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul _
  refine hdom.mono' ((continuous_quarticProfile.mul (by fun_prop)).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (quarticProfile_pos x).le (Real.exp_pos _).le)]
  calc quarticProfile x * Real.exp (b * x)
      ≤ Real.exp (1 ^ 2) * Real.exp (-(2 * 1) * x ^ 2) * Real.exp (b * x) :=
        mul_le_mul_of_nonneg_right (quarticProfile_le_gaussian 1 x) (Real.exp_pos _).le
    _ = Real.exp (1 + (-2 * x ^ 2 + b * x)) := by rw [Real.exp_add, Real.exp_add]; ring_nf
    _ ≤ Real.exp (1 + b ^ 2 / 4 + -1 * x ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (x - b / 2)])
    _ = Real.exp (1 + b ^ 2 / 4) * Real.exp (-1 * x ^ 2) := by rw [Real.exp_add]

theorem integrable_quarticProfile_sourceChar (z : ℂ) :
    Integrable fun x => (quarticProfile x : ℂ) * sourceChar z x := by
  refine (integrable_quarticProfile_mul_exp (-z.im)).mono'
    ((Complex.continuous_ofReal.comp continuous_quarticProfile).mul
      (continuous_sourceChar z)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (quarticProfile_pos x),
    norm_sourceChar]

theorem sourceChar_add_mul (z : ℂ) (x y : ℝ) :
    sourceChar z (x + y) = sourceChar z x * sourceChar z y := by
  rw [sourceChar, sourceChar, sourceChar, ← Complex.exp_add]
  push_cast
  ring_nf

/-- **(1)** `F(z) = H(z)(1 + 2a cos(Lz))`. -/
theorem xiC_source (z : ℂ) :
    xiC (source P) z = quarticTransform z * (1 + 2 * P.a * Complex.cos (P.L * z)) := by
  have hH := integrable_quarticProfile_sourceChar z
  have hshift : ∀ s : ℝ, (∫ x, (quarticProfile (x - s) : ℂ) * sourceChar z x) =
      quarticTransform z * sourceChar z s := by
    intro s
    have e : ∀ x : ℝ, (quarticProfile (x - s) : ℂ) * sourceChar z x =
        (fun y => (quarticProfile y : ℂ) * sourceChar z y * sourceChar z s) (x - s) := by
      intro x
      simp only
      rw [mul_assoc, ← sourceChar_add_mul, sub_add_cancel]
    simp_rw [e]
    rw [integral_sub_right_eq_self (fun y => (quarticProfile y : ℂ) * sourceChar z y *
      sourceChar z s) s, integral_mul_const]
    rfl
  have hint : ∀ s : ℝ, Integrable fun x => (quarticProfile (x - s) : ℂ) * sourceChar z x := by
    intro s
    have := (hH.comp_sub_right s).mul_const (sourceChar z s)
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only
    rw [mul_assoc, ← sourceChar_add_mul, sub_add_cancel]
  have hsplit : (fun x => ((source P).k x : ℂ) * sourceChar z x) = fun x =>
      (quarticProfile x : ℂ) * sourceChar z x +
        (P.a : ℂ) * ((quarticProfile (x - P.L) : ℂ) * sourceChar z x) +
        (P.a : ℂ) * ((quarticProfile (x - (-P.L)) : ℂ) * sourceChar z x) := by
    funext x
    rw [source_k, density, sub_neg_eq_add]
    push_cast
    ring
  rw [xiC, hsplit, integral_add (f := fun x => (quarticProfile x : ℂ) * sourceChar z x +
      (P.a : ℂ) * ((quarticProfile (x - P.L) : ℂ) * sourceChar z x))
      (hH.add ((hint P.L).const_mul _)) ((hint (-P.L)).const_mul _),
    integral_add hH ((hint P.L).const_mul _), integral_const_mul, integral_const_mul, hshift,
    hshift]
  change quarticTransform z + _ + _ = _
  rw [Complex.cos, sourceChar, sourceChar]
  have e1 : Complex.I * z * ((P.L : ℝ) : ℂ) = ((P.L : ℂ) * z) * Complex.I := by ring
  have e2 : Complex.I * z * (((-P.L : ℝ)) : ℂ) = -((P.L : ℂ) * z) * Complex.I := by
    push_cast; ring
  rw [e1, e2]
  ring

/-- The upper zeros `z_n^+ = ((2n+1)π + iA)/L`. -/
def upperZero (n : ℤ) : ℂ := ((2 * n + 1) * Real.pi + P.A * Complex.I) / P.L

/-- The lower zeros `z_n^- = ((2n+1)π - iA)/L`. -/
def lowerZero (n : ℤ) : ℂ := ((2 * n + 1) * Real.pi - P.A * Complex.I) / P.L

theorem cos_odd_pi_add (n : ℤ) (w : ℂ) :
    Complex.cos ((2 * n + 1) * Real.pi + w) = -Complex.cos w := by
  have : ((2 * n + 1) * Real.pi + w : ℂ) = w + Real.pi + n * (2 * Real.pi) := by ring
  rw [this, Complex.cos_add_int_mul_two_pi, Complex.cos_add_pi]

theorem one_add_cos_eq_zero (s : ℂ) (hs : s = 1 ∨ s = -1) (n : ℤ) :
    1 + 2 * P.a * Complex.cos ((2 * n + 1) * Real.pi + s * P.A * Complex.I) = 0 := by
  rw [cos_odd_pi_add]
  have hcos : Complex.cos (s * P.A * Complex.I) = (Real.cosh P.A : ℂ) := by
    rcases hs with rfl | rfl
    · rw [one_mul, Complex.cos_mul_I, Complex.ofReal_cosh]
    · rw [neg_one_mul, neg_mul, Complex.cos_neg, Complex.cos_mul_I, Complex.ofReal_cosh]
  rw [hcos, P.cosh_A]
  have ha : (P.a : ℂ) ≠ 0 := by exact_mod_cast P.a_pos.ne'
  push_cast
  field_simp
  ring

/-- **(2)** `F(z_n^+) = 0`. -/
theorem xiC_upperZero (n : ℤ) : xiC (source P) (upperZero P n) = 0 := by
  rw [xiC_source]
  have hL : (P.L : ℂ) ≠ 0 := by exact_mod_cast P.L_pos.ne'
  have e : (P.L : ℂ) * upperZero P n = (2 * n + 1) * Real.pi + 1 * P.A * Complex.I := by
    rw [upperZero]; field_simp
  rw [e, one_add_cos_eq_zero P 1 (Or.inl rfl), mul_zero]

/-- **(2)** `F(z_n^-) = 0`. -/
theorem xiC_lowerZero (n : ℤ) : xiC (source P) (lowerZero P n) = 0 := by
  rw [xiC_source]
  have hL : (P.L : ℂ) ≠ 0 := by exact_mod_cast P.L_pos.ne'
  have e : (P.L : ℂ) * lowerZero P n = (2 * n + 1) * Real.pi + (-1) * P.A * Complex.I := by
    rw [lowerZero]; field_simp; ring
  rw [e, one_add_cos_eq_zero P (-1) (Or.inr rfl), mul_zero]

theorem upperZero_re (n : ℤ) : (upperZero P n).re = (2 * n + 1) * Real.pi / P.L := by
  rw [upperZero, Complex.div_ofReal_re]
  simp

theorem upperZero_im (n : ℤ) : (upperZero P n).im = P.A / P.L := by
  rw [upperZero, Complex.div_ofReal_im]
  simp

/-- **(2)** `0 < Im z_n^+ < 1/2`. -/
theorem upperZero_im_mem (n : ℤ) : 0 < (upperZero P n).im ∧ (upperZero P n).im < 1 / 2 := by
  rw [upperZero_im]
  have hL := P.L_pos
  refine ⟨div_pos P.A_pos hL, ?_⟩
  rw [div_lt_iff₀ hL]
  linarith [P.L_gt]

theorem upperZero_ne_zero (n : ℤ) : upperZero P n ≠ 0 := by
  intro h
  have := (upperZero_im_mem P n).1
  rw [h, Complex.zero_im] at this
  exact lt_irrefl _ this

theorem upperZero_injective : Function.Injective (upperZero P) := by
  intro m n h
  have h1 := congrArg Complex.re h
  rw [upperZero_re, upperZero_re, div_left_inj' P.L_pos.ne'] at h1
  have h2 := mul_right_cancel₀ Real.pi_pos.ne' h1
  exact_mod_cast (by linarith : (m : ℝ) = n)

/-- The eigenvalues `-1/z_n^+` lie in the upper half-plane. -/
theorem neg_inv_upperZero_im_pos (n : ℤ) : 0 < (-(upperZero P n)⁻¹).im := by
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_pos (upperZero_im_mem P n).1 (Complex.normSq_pos.mpr (upperZero_ne_zero P n))

theorem neg_inv_upperZero_injective : Function.Injective fun n => -(upperZero P n)⁻¹ := by
  intro m n h
  exact upperZero_injective P (inv_injective (neg_injective h))

/-! ### The quartic tail envelope -/

theorem quartic_increment {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    4 * u ^ 3 * (v - u) ≤ v ^ 4 - u ^ 4 := by
  have hd : 0 ≤ v - u := sub_nonneg.mpr huv
  have h1 : 0 ≤ u ^ 2 * (v - u) ^ 2 := by positivity
  have h2 : 0 ≤ u * (v - u) ^ 3 := by positivity
  have h3 : 0 ≤ (v - u) ^ 4 := by positivity
  nlinarith [h1, h2, h3]

theorem quarticProfile_tail {L x y s : ℝ} (hs : s ≤ L) (hx : L + 1 ≤ x) (hxy : x ≤ y) :
    quarticProfile (y - s) ≤ quarticProfile (x - s) * Real.exp (-(4 * (x - L) ^ 3 * (y - x))) := by
  rw [quarticProfile, quarticProfile, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hu : 0 ≤ x - s := by linarith
  have h1 := quartic_increment hu (by linarith : x - s ≤ y - s)
  have h2 : (x - L) ^ 3 ≤ (x - s) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have h3 : 0 ≤ y - x := by linarith
  nlinarith [mul_le_mul_of_nonneg_right h2 h3]

/-- **Tail envelope.** For `L + 1 ≤ x ≤ y`, `g(y) ≤ g(x) e^{-4(x-L)³(y-x)}`. -/
theorem density_tail {x y : ℝ} (hx : P.L + 1 ≤ x) (hxy : x ≤ y) :
    density P y ≤ density P x * Real.exp (-(4 * (x - P.L) ^ 3 * (y - x))) := by
  have ha := P.a_pos
  have hL := P.L_pos
  have t0 := quarticProfile_tail (s := 0) hL.le hx hxy
  have t1 := quarticProfile_tail (s := P.L) le_rfl hx hxy
  have t2 := quarticProfile_tail (s := -P.L) (by linarith) hx hxy
  simp only [sub_zero, sub_neg_eq_add] at t0 t2
  unfold density
  nlinarith [mul_le_mul_of_nonneg_left t1 ha.le, mul_le_mul_of_nonneg_left t2 ha.le]

theorem integral_exp_tail {x c : ℝ} (hc : 0 < c) :
    ∫ y in Ioi x, Real.exp (-(c * (y - x))) = 1 / c := by
  have e : ∀ y, Real.exp (-(c * (y - x))) = Real.exp (c * x) * Real.exp ((-c) * y) := by
    intro y; rw [← Real.exp_add]; ring_nf
  simp_rw [e]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) x, mul_div_assoc', mul_neg,
    neg_div_neg_eq, ← Real.exp_add, show c * x + -c * x = 0 by ring, Real.exp_zero]

theorem integrableOn_exp_tail {x c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun y => Real.exp (-(c * (y - x)))) (Ioi x) := by
  refine IntegrableOn.congr_fun ((integrableOn_exp_mul_Ioi (by linarith : -c < 0) x).const_mul
    (Real.exp (c * x))) (fun y _ => ?_) measurableSet_Ioi
  rw [← Real.exp_add]; ring_nf

theorem integrable_density_mul_exp_sub (c x : ℝ) :
    Integrable (fun y => density P y * Real.exp (c * (y - x))) := by
  refine ((integrable_density_mul_exp P c).const_mul (Real.exp (-(c * x)))).congr
    (ae_of_all _ fun y => ?_)
  simp only
  rw [mul_left_comm, ← Real.exp_add]; ring_nf

/-- The right tail integral: `∫_{y > x} g(y) e^{c(y-x)} dy ≤ g(x)/(4(x-L)³ - c)`. -/
theorem density_tail_integral {x c : ℝ} (hx : P.L + 1 ≤ x) (hc : c < 4 * (x - P.L) ^ 3) :
    ∫ y in Ioi x, density P y * Real.exp (c * (y - x)) ≤
      density P x / (4 * (x - P.L) ^ 3 - c) := by
  set r := 4 * (x - P.L) ^ 3
  have hrc : 0 < r - c := by linarith
  calc ∫ y in Ioi x, density P y * Real.exp (c * (y - x))
      ≤ ∫ y in Ioi x, density P x * Real.exp (-((r - c) * (y - x))) := by
        refine setIntegral_mono_on (integrable_density_mul_exp_sub P c x).integrableOn
          ((integrableOn_exp_tail hrc).const_mul _) measurableSet_Ioi fun y hy => ?_
        have hty := density_tail P hx (le_of_lt hy)
        calc density P y * Real.exp (c * (y - x))
            ≤ density P x * Real.exp (-(r * (y - x))) * Real.exp (c * (y - x)) :=
              mul_le_mul_of_nonneg_right hty (Real.exp_pos _).le
          _ = density P x * Real.exp (-((r - c) * (y - x))) := by
              rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ = density P x / (r - c) := by rw [integral_const_mul, integral_exp_tail hrc, mul_one_div]

/-- The left tail integral, by evenness. -/
theorem density_tail_integral_left {x c : ℝ} (hx : x ≤ -(P.L + 1))
    (hc : c < 4 * (-x - P.L) ^ 3) :
    ∫ y in Iic x, density P y * Real.exp (c * (x - y)) ≤
      density P x / (4 * (-x - P.L) ^ 3 - c) := by
  have e := integral_comp_neg_Iic x (fun y => density P y * Real.exp (c * (y - -x)))
  have e2 : (fun y => density P (-y) * Real.exp (c * (-y - -x))) =
      fun y => density P y * Real.exp (c * (x - y)) := by
    funext y; rw [density_neg]; ring_nf
  rw [e2] at e
  rw [e]
  have h := density_tail_integral P (x := -x) (c := c) (by linarith) hc
  rwa [density_neg] at h

/-- Complementary tail masses. -/
theorem setIntegral_Iic_add_Ioi_real {f : ℝ → ℝ} (hf : Integrable f) (x : ℝ) :
    (∫ y in Iic x, f y) + ∫ y in Ioi x, f y = ∫ y, f y := by
  rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hf.integrableOn
    hf.integrableOn, Iic_union_Ioi, setIntegral_univ]

theorem four_le_rate {x : ℝ} (hx : P.L + 1 ≤ x) : 4 ≤ 4 * (x - P.L) ^ 3 := by
  have : 1 ≤ (x - P.L) ^ 3 := one_le_pow₀ (by linarith)
  linarith

/-! ### Finite reciprocal-tail energy -/

theorem tailEnergyDensity_nonneg (x : ℝ) : 0 ≤ tailEnergyDensity (source P) x := by
  have h := (source P).cdfFun_mem_Ioo x
  unfold tailEnergyDensity
  exact div_nonneg (mul_nonneg h.1.le (by linarith [h.2])) ((source P).pos_k x).le

theorem one_sub_cdfFun_eq (x : ℝ) :
    1 - (source P).cdfFun x = (∫ y in Ioi x, density P y) / (source P).mass := by
  have hsum := setIntegral_Iic_add_Ioi_real (integrable_density P) x
  have hM : (source P).mass ≠ 0 := (source P).mass_ne_zero
  rw [PositiveDensitySource.cdfFun, eq_div_iff hM, sub_mul, one_mul, div_mul_cancel₀ _ hM]
  change (source P).mass - ∫ y in Iic x, density P y = _
  rw [show (source P).mass = ∫ y, density P y from rfl, ← hsum]
  ring

theorem tailEnergyDensity_le_right {x : ℝ} (hx : P.L + 1 ≤ x) :
    tailEnergyDensity (source P) x ≤ 1 / ((source P).mass * (4 * (x - P.L) ^ 3)) := by
  have hG := (source P).cdfFun_mem_Ioo x
  have hM := (source P).mass_pos
  have hk := density_pos P x
  have hr : 0 < 4 * (x - P.L) ^ 3 := by linarith [four_le_rate P hx]
  have htail := density_tail_integral P (c := 0) hx hr
  simp only [zero_mul, Real.exp_zero, mul_one, sub_zero] at htail
  unfold tailEnergyDensity
  rw [one_sub_cdfFun_eq, source_k]
  rw [div_le_div_iff₀ hk (by positivity)]
  have hI : (∫ y in Ioi x, density P y) ≤ density P x / (4 * (x - P.L) ^ 3) := htail
  have hI0 : 0 ≤ ∫ y in Ioi x, density P y :=
    setIntegral_nonneg measurableSet_Ioi fun y _ => (density_pos P y).le
  rw [le_div_iff₀ hr] at hI
  have hGle : (source P).cdfFun x * ((∫ y in Ioi x, density P y) / (source P).mass) ≤
      (∫ y in Ioi x, density P y) / (source P).mass :=
    mul_le_of_le_one_left (div_nonneg hI0 hM.le) hG.2.le
  calc (source P).cdfFun x * ((∫ y in Ioi x, density P y) / (source P).mass) *
        ((source P).mass * (4 * (x - P.L) ^ 3))
      ≤ (∫ y in Ioi x, density P y) / (source P).mass * ((source P).mass * (4 * (x - P.L) ^ 3)) :=
        mul_le_mul_of_nonneg_right hGle (by positivity)
    _ = (∫ y in Ioi x, density P y) * (4 * (x - P.L) ^ 3) := by field_simp
    _ ≤ 1 * density P x := by linarith

theorem tailEnergyDensity_le_left {x : ℝ} (hx : x ≤ -(P.L + 1)) :
    tailEnergyDensity (source P) x ≤ 1 / ((source P).mass * (4 * (-x - P.L) ^ 3)) := by
  have hG := (source P).cdfFun_mem_Ioo x
  have hM := (source P).mass_pos
  have hk := density_pos P x
  have hr : 0 < 4 * (-x - P.L) ^ 3 := by linarith [four_le_rate P (x := -x) (by linarith)]
  have htail := density_tail_integral_left P (c := 0) hx hr
  simp only [zero_mul, Real.exp_zero, mul_one, sub_zero] at htail
  unfold tailEnergyDensity
  rw [source_k, div_le_div_iff₀ hk (by positivity)]
  have hI : (∫ y in Iic x, density P y) ≤ density P x / (4 * (-x - P.L) ^ 3) := htail
  rw [le_div_iff₀ hr] at hI
  have hcdf : (source P).cdfFun x = (∫ y in Iic x, density P y) / (source P).mass := rfl
  have hGle : (source P).cdfFun x * (1 - (source P).cdfFun x) ≤ (source P).cdfFun x :=
    mul_le_of_le_one_right hG.1.le (by linarith [hG.1])
  calc (source P).cdfFun x * (1 - (source P).cdfFun x) * ((source P).mass * (4 * (-x - P.L) ^ 3))
      ≤ (source P).cdfFun x * ((source P).mass * (4 * (-x - P.L) ^ 3)) :=
        mul_le_mul_of_nonneg_right hGle (by positivity)
    _ = (∫ y in Iic x, density P y) * (4 * (-x - P.L) ^ 3) := by rw [hcdf]; field_simp
    _ ≤ 1 * density P x := by linarith

theorem continuous_tailEnergyDensity : Continuous (tailEnergyDensity (source P)) := by
  unfold tailEnergyDensity
  exact ((source P).continuous_cdfFun.mul (continuous_const.sub (source P).continuous_cdfFun)).div
    (source P).continuous_k fun x => ((source P).pos_k x).ne'

theorem rate_inv_le {x : ℝ} (hx : P.L + 1 ≤ x) :
    1 / ((source P).mass * (4 * (x - P.L) ^ 3)) ≤
      (P.L + 1) ^ 3 / (4 * (source P).mass) * x ^ (-3 : ℝ) := by
  have hM := (source P).mass_pos
  have hL := P.L_pos
  have hx0 : 0 < x := by linarith
  have hxL : x / (P.L + 1) ≤ x - P.L := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h3 : (x / (P.L + 1)) ^ 3 ≤ (x - P.L) ^ 3 := pow_le_pow_left₀ (by positivity) hxL 3
  rw [Real.rpow_neg hx0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hL1 : 0 < P.L + 1 := by linarith
  have h3' : x ^ 3 ≤ (P.L + 1) ^ 3 * (x - P.L) ^ 3 := by
    rw [div_pow, div_le_iff₀ (by positivity)] at h3; linarith
  have hxL3 : 0 < (x - P.L) ^ 3 := pow_pos (by linarith) 3
  have e : (P.L + 1) ^ 3 / (4 * (source P).mass) * (x ^ 3)⁻¹ =
      (P.L + 1) ^ 3 / (4 * (source P).mass * x ^ 3) := by field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h3', hM]

/-- **(4)** The reciprocal-tail energy of the three-bump source is finite. -/
theorem integrable_tailEnergyDensity : Integrable (tailEnergyDensity (source P)) := by
  set c := P.L + 1
  have hc : 0 < c := by linarith [P.L_pos]
  set K := (P.L + 1) ^ 3 / (4 * (source P).mass)
  have hright : IntegrableOn (tailEnergyDensity (source P)) (Ioi c) := by
    refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hc).const_mul K).mono'
      (continuous_tailEnergyDensity P).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (tailEnergyDensity_nonneg P x)]
    exact (tailEnergyDensity_le_right P (le_of_lt hx)).trans (rate_inv_le P (le_of_lt hx))
  have hleft : IntegrableOn (tailEnergyDensity (source P)) (Iio (-c)) := by
    have h0 : IntegrableOn (fun t : ℝ => K * t ^ (-3 : ℝ)) (Ioi c) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hc).const_mul K
    have h := h0.comp_neg
    rw [Set.neg_Ioi] at h
    refine h.mono' (continuous_tailEnergyDensity P).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (tailEnergyDensity_nonneg P x)]
    have hx' : x ≤ -(P.L + 1) := le_of_lt hx
    refine (tailEnergyDensity_le_left P hx').trans ?_
    exact rate_inv_le P (x := -x) (by linarith)
  have hmid : IntegrableOn (tailEnergyDensity (source P)) (Icc (-c) c) :=
    (continuous_tailEnergyDensity P).integrableOn_Icc
  have hunion : Iio (-c) ∪ (Icc (-c) c ∪ Ioi c) = univ := by
    ext x; simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    by_cases h1 : x < -c
    · exact Or.inl h1
    · by_cases h2 : c < x
      · exact Or.inr (Or.inr h2)
      · exact Or.inr (Or.inl ⟨not_lt.mp h1, not_lt.mp h2⟩)
  rw [← integrableOn_univ, ← hunion]
  exact hleft.union (hmid.union hright)

theorem hasFiniteKernelEnergy_source : HasFiniteKernelEnergy (source P) :=
  hasFiniteKernelEnergy_of_integrable (source P) (integrable_tailEnergyDensity P)

/-- **(3)** The source inverse of the countermodel. -/
def sourceInverseOp : Lp ℂ 2 unitIntervalMeasure →L[ℂ] Lp ℂ 2 unitIntervalMeasure :=
  compactSourceInverse (source P) (hasFiniteKernelEnergy_source P)

/-- **(3)** It is Hilbert--Schmidt, hence compact. -/
theorem sourceInverseOp_hilbertSchmidt :
    ContinuousLinearMap.IsHilbertSchmidt (sourceInverseOp P) ∧
      IsCompactOperator (sourceInverseOp P) :=
  ⟨isHilbertSchmidt_compactSourceInverse _ _, isCompactOperator_compactSourceInverse _ _⟩

/-- **(4)** The Hilbert--Schmidt energy identity `∫₀¹ q² t(1-t) = M ∫ G(1-G)/g`. -/
theorem sourceInverseOp_energy :
    (∫ t in Ioo (0 : ℝ) 1, quantileSpeed (source P) t ^ 2 * (t * (1 - t))) =
      (source P).mass * ∫ x, tailEnergyDensity (source P) x :=
  integral_quantileSpeed_sq_slice (source P)

/-! ### The metric and its rank-two defect -/

theorem norm_metricSymbol_source_le (t : ℝ) :
    ‖metricSymbol (source P) t‖ ≤ (1 + 2 * P.a) / (source P).mass :=
  norm_metricSymbol_le (source P) (density_le P) t

theorem metricBound_nonneg : 0 ≤ (1 + 2 * P.a) / (source P).mass := by
  have := P.a_pos; have := (source P).mass_pos; positivity

/-- The canonical metric `D = M_{1/q}`. -/
def metricOp : Lp ℂ 2 unitIntervalMeasure →L[ℂ] Lp ℂ 2 unitIntervalMeasure :=
  metricOperator (source P) (metricBound_nonneg P) (norm_metricSymbol_source_le P)

/-- **(5)** `D` is bounded, self-adjoint, positive and injective, and `D B - B† D = i P` with the
rank-two pinned boundary operator `P`. -/
theorem metricOp_commutator :
    (metricOp P).adjoint = metricOp P ∧
      (∀ f, 0 ≤ (inner ℂ (metricOp P f) f : ℂ).re) ∧
      Function.Injective (metricOp P) ∧
      metricOp P * sourceInverseOp P -
          ContinuousLinearMap.adjoint (sourceInverseOp P) * metricOp P =
        Complex.I • pinnedBoundaryCLM :=
  ⟨adjoint_metricOperator _ _ _, re_inner_metricOperator_nonneg _ _ _,
    metricOperator_injective _ _ _,
    metricOperator_commutator_compactSourceInverse _ _ _ _⟩

/-- **(5)** `P` has rank two, `P 1 = -v` and `P v = -1/12` for `v(t) = t - 1/2`, with one
positive and one negative direction. -/
theorem boundaryDefect_rankTwo :
    Module.finrank ℂ (LinearMap.range pinnedBoundaryCLM.toLinearMap) = 2 ∧
      pinnedBoundaryCLM pinnedOne = -pinnedCenter ∧
      pinnedBoundaryCLM pinnedCenter = -(1 / 12 : ℂ) • pinnedOne ∧
      inner ℂ (pinnedBoundaryCLM pinnedPositiveMode) pinnedPositiveMode = (1 : ℂ) / 6 ∧
      inner ℂ (pinnedBoundaryCLM pinnedNegativeMode) pinnedNegativeMode = -(1 : ℂ) / 6 :=
  ⟨finrank_range_pinnedBoundaryCLM, pinnedBoundaryCLM_pinnedOne_eq_neg_center,
    pinnedBoundaryCLM_pinnedCenter, pinnedBoundaryCLM_exact_rankTwo_mixed_inertia.2.2.1,
    pinnedBoundaryCLM_exact_rankTwo_mixed_inertia.2.2.2⟩

/-! ### Source modes at the zeros -/

theorem continuous_sourceModeU (z : ℂ) : Continuous (sourceModeU (source P) z) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_sourceModeU (source P) (hasShiftedTail_source P z) x).continuousAt

theorem norm_sourceModeU_eq (z : ℂ) (x : ℝ) :
    ‖sourceModeU (source P) z x‖ = Real.exp (z.im * x) * ‖sourceModeI (source P) z x‖ := by
  rw [sourceModeU, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_setIntegral_k_sourceChar_le (z : ℂ) (s : Set ℝ) :
    ‖∫ y in s, ((source P).k y : ℂ) * sourceChar z y‖ ≤
      ∫ y in s, density P y * Real.exp (-z.im * y) := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, source_k, abs_of_pos (density_pos P y),
    norm_sourceChar]

/-- Right tail of the mode at a zero: `|u_z(x)| ≤ g(x)` for `x ≥ L + 1`. -/
theorem norm_sourceModeU_le_right {z : ℂ} (hz : |z.im| ≤ 1) (hzero : xiC (source P) z = 0)
    {x : ℝ} (hx : P.L + 1 ≤ x) : ‖sourceModeU (source P) z x‖ ≤ density P x := by
  have hf := integrable_k_sourceChar (source P) (hasShiftedTail_source P z)
  have hI : sourceModeI (source P) z x = -∫ y in Ioi x, ((source P).k y : ℂ) * sourceChar z y := by
    have h := HedenmalmFredholmRange.setIntegral_Iic_add_Ioi hf x
    change _ = xiC (source P) z at h
    rw [hzero] at h
    rw [sourceModeI]
    linear_combination h
  rw [norm_sourceModeU_eq, hI, norm_neg]
  have hmono : Real.exp (z.im * x) * ∫ y in Ioi x, density P y * Real.exp (-z.im * y) ≤
      ∫ y in Ioi x, density P y * Real.exp (|z.im| * (y - x)) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on ((integrable_density_mul_exp P (-z.im)).const_mul _).integrableOn
      (integrable_density_mul_exp_sub P _ x).integrableOn measurableSet_Ioi fun y hy => ?_
    rw [mul_left_comm, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (density_pos P y).le
    have hyx : 0 ≤ y - x := by linarith [mem_Ioi.mp hy]
    nlinarith [mul_le_mul_of_nonneg_right (neg_le_abs z.im) hyx]
  have hr := four_le_rate P hx
  calc Real.exp (z.im * x) * ‖∫ y in Ioi x, ((source P).k y : ℂ) * sourceChar z y‖
      ≤ Real.exp (z.im * x) * ∫ y in Ioi x, density P y * Real.exp (-z.im * y) :=
        mul_le_mul_of_nonneg_left (norm_setIntegral_k_sourceChar_le P z _) (Real.exp_pos _).le
    _ ≤ ∫ y in Ioi x, density P y * Real.exp (|z.im| * (y - x)) := hmono
    _ ≤ density P x / (4 * (x - P.L) ^ 3 - |z.im|) :=
        density_tail_integral P hx (by linarith)
    _ ≤ density P x := div_le_self (density_pos P x).le (by linarith)

/-- Left tail of the mode: `|u_z(x)| ≤ g(x)` for `x ≤ -(L + 1)`. -/
theorem norm_sourceModeU_le_left {z : ℂ} (hz : |z.im| ≤ 1) {x : ℝ} (hx : x ≤ -(P.L + 1)) :
    ‖sourceModeU (source P) z x‖ ≤ density P x := by
  rw [norm_sourceModeU_eq, sourceModeI]
  have hint : Integrable (fun y => density P y * Real.exp (|z.im| * (x - y))) :=
    (integrable_density_mul_exp_sub P (-|z.im|) x).congr (ae_of_all _ fun y => by
      simp only; ring_nf)
  have hmono : Real.exp (z.im * x) * ∫ y in Iic x, density P y * Real.exp (-z.im * y) ≤
      ∫ y in Iic x, density P y * Real.exp (|z.im| * (x - y)) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on ((integrable_density_mul_exp P (-z.im)).const_mul _).integrableOn
      hint.integrableOn measurableSet_Iic fun y hy => ?_
    rw [mul_left_comm, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (density_pos P y).le
    have hxy : 0 ≤ x - y := by linarith [mem_Iic.mp hy]
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self z.im) hxy]
  have hr := four_le_rate P (x := -x) (by linarith)
  calc Real.exp (z.im * x) * ‖∫ y in Iic x, ((source P).k y : ℂ) * sourceChar z y‖
      ≤ Real.exp (z.im * x) * ∫ y in Iic x, density P y * Real.exp (-z.im * y) :=
        mul_le_mul_of_nonneg_left (norm_setIntegral_k_sourceChar_le P z _) (Real.exp_pos _).le
    _ ≤ ∫ y in Iic x, density P y * Real.exp (|z.im| * (x - y)) := hmono
    _ ≤ density P x / (4 * (-x - P.L) ^ 3 - |z.im|) :=
        density_tail_integral_left P hx (by linarith)
    _ ≤ density P x := div_le_self (density_pos P x).le (by linarith)

/-- **Mode envelope.** At a zero with `|Im z| ≤ 1`, `|u_z| ≤ C g` on the whole line. -/
theorem exists_norm_sourceModeU_le {z : ℂ} (hz : |z.im| ≤ 1) (hzero : xiC (source P) z = 0) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖sourceModeU (source P) z x‖ ≤ C * density P x := by
  set c := P.L + 1
  have hc : 0 < c := by linarith [P.L_pos]
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := -c) (b := c)).exists_bound_of_continuousOn
    (continuous_sourceModeU P z).continuousOn
  obtain ⟨x₀, -, hmin⟩ := (isCompact_Icc (a := -c) (b := c)).exists_isMinOn
    (nonempty_Icc.mpr (by linarith)) (continuous_density P).continuousOn
  have hm : 0 < density P x₀ := density_pos P x₀
  refine ⟨max 1 (C₁ / density P x₀), le_max_of_le_left zero_le_one, fun x => ?_⟩
  have hk := density_pos P x
  by_cases hr : c ≤ x
  · exact (norm_sourceModeU_le_right P hz hzero hr).trans
      (le_mul_of_one_le_left hk.le (le_max_left _ _))
  by_cases hl : x ≤ -c
  · exact (norm_sourceModeU_le_left P hz hl).trans
      (le_mul_of_one_le_left hk.le (le_max_left _ _))
  have hxI : x ∈ Icc (-c) c := ⟨(not_le.mp hl).le, (not_le.mp hr).le⟩
  have h1 := hC₁ x hxI
  have h2 : density P x₀ ≤ density P x := isMinOn_iff.mp hmin x hxI
  have hC1 : 0 ≤ C₁ := (norm_nonneg _).trans h1
  calc ‖sourceModeU (source P) z x‖ ≤ C₁ := h1
    _ = C₁ / density P x₀ * density P x₀ := by field_simp
    _ ≤ C₁ / density P x₀ * density P x :=
        mul_le_mul_of_nonneg_left h2 (div_nonneg hC1 hm.le)
    _ ≤ max 1 (C₁ / density P x₀) * density P x :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hk.le

theorem tendsto_density (l : Filter ℝ) (hl : Tendsto (fun x : ℝ => x ^ 2) l atTop) :
    Tendsto (density P) l (𝓝 0) := by
  set K := (1 + 2 * P.a) * Real.exp (1 ^ 2 + 2 * 1 * P.L ^ 2)
  have hexp : Tendsto (fun x : ℝ => K * Real.exp (-1 * x ^ 2)) l (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => -1 * x ^ 2) l atBot :=
      (tendsto_neg_atTop_atBot.comp hl).congr fun x => by simp only [Function.comp_apply]; ring
    simpa using (Real.tendsto_exp_atBot.comp h).const_mul K
  exact squeeze_zero (fun x => (density_pos P x).le) (fun x => density_le_gaussian P zero_le_one x)
    hexp

theorem tendsto_sq_atTop : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
  tendsto_pow_atTop two_ne_zero

theorem tendsto_sq_atBot : Tendsto (fun x : ℝ => x ^ 2) atBot atTop := by
  exact ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_neg_atBot_atTop).congr fun x => by
    simp only [Function.comp_apply, neg_sq]

theorem tendsto_sourceModeU {z : ℂ} (hz : |z.im| ≤ 1) (hzero : xiC (source P) z = 0) :
    Tendsto (sourceModeU (source P) z) atBot (𝓝 0) ∧
      Tendsto (sourceModeU (source P) z) atTop (𝓝 0) := by
  obtain ⟨C, -, hC⟩ := exists_norm_sourceModeU_le P hz hzero
  refine ⟨squeeze_zero_norm hC ?_, squeeze_zero_norm hC ?_⟩
  · simpa using (tendsto_density P atBot (tendsto_sq_atBot)).const_mul C
  · simpa using (tendsto_density P atTop (tendsto_sq_atTop)).const_mul C

theorem integrable_sourceModeU {z : ℂ} (hz : |z.im| ≤ 1) (hzero : xiC (source P) z = 0) :
    Integrable (sourceModeU (source P) z) := by
  obtain ⟨C, -, hC⟩ := exists_norm_sourceModeU_le P hz hzero
  exact ((integrable_density P).const_mul C).mono'
    (continuous_sourceModeU P z).aestronglyMeasurable (ae_of_all _ hC)

theorem integrable_sourceModeF {z : ℂ} (hz : |z.im| ≤ 1) (hzero : xiC (source P) z = 0) :
    Integrable (sourceModeF (source P) z) :=
  ((integrable_sourceModeU P hz hzero).const_mul (-z)).congr
    (ae_of_all _ fun x => (sourceModeF_eq (source P) x).symm)

/-- `∫ f_z = M`: integrate the mode equation across the line. -/
theorem integral_sourceModeF {z : ℂ} (hz0 : z ≠ 0) (hz : |z.im| ≤ 1)
    (hzero : xiC (source P) z = 0) :
    (∫ x, sourceModeF (source P) z x) = ((source P).mass : ℂ) := by
  have hIz : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz0
  have hu := integrable_sourceModeU P hz hzero
  have hkC : Integrable fun x : ℝ => (((source P).k x : ℝ) : ℂ) := (source P).integrable_k.ofReal
  have hderiv : ∀ x : ℝ, HasDerivAt (sourceModeU (source P) z)
      (-(Complex.I * z) * sourceModeU (source P) z x - Complex.I * (((source P).k x : ℝ) : ℂ)) x :=
    hasDerivAt_sourceModeU (source P) (hasShiftedTail_source P z)
  have hint : Integrable fun x : ℝ => -(Complex.I * z) * sourceModeU (source P) z x
      - Complex.I * (((source P).k x : ℝ) : ℂ) := (hu.const_mul _).sub (hkC.const_mul _)
  obtain ⟨hbot, htop⟩ := tendsto_sourceModeU P hz hzero
  have h0 := integral_of_hasDerivAt_of_tendsto hderiv hint hbot htop
  rw [sub_zero, integral_sub (hu.const_mul _) (hkC.const_mul _), integral_const_mul,
    integral_const_mul] at h0
  have hmass : (∫ x : ℝ, (((source P).k x : ℝ) : ℂ)) = (((source P).mass : ℝ) : ℂ) := by
    rw [integral_complex_ofReal]; rfl
  rw [hmass] at h0
  have hJ : (∫ x, sourceModeU (source P) z x) = -((source P).mass : ℂ) / z := by
    rw [eq_div_iff hz0]
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have := congrArg (fun w => Complex.I * w) h0
    simp only [mul_zero] at this
    linear_combination this + ((∫ x, sourceModeU (source P) z x) * z + ((source P).mass : ℂ)) * hI
  have h : (∫ x, sourceModeF (source P) z x) = -z * ∫ x, sourceModeU (source P) z x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => sourceModeF_eq (source P) x)
  rw [h, hJ]
  field_simp

/-- The mode lies in the weighted source space `L²(ℝ, g⁻¹ dx)`. -/
theorem memLp_sourceModeF {z : ℂ} (hz : |z.im| ≤ 1) (hzero : xiC (source P) z = 0) :
    MemLp (sourceModeF (source P) z) 2
      ((volume : Measure ℝ).withDensity (realDensity (sourceWeight (source P)))) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_sourceModeU_le P hz hzero
  refine (memLp_two_withDensity_iff (measurable_sourceWeight (source P))
    (sourceWeight_pos (source P))).mpr ?_
  have hcont : Continuous fun x =>
      sqrtWeight (sourceWeight (source P)) x * sourceModeF (source P) z x := by
    have hw : Continuous (sourceWeight (source P)) := by
      unfold sourceWeight
      exact (source P).continuous_k.inv₀ fun x => ((source P).pos_k x).ne'
    have hsw : Continuous (sqrtWeight (sourceWeight (source P))) := by
      unfold sqrtWeight
      exact Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hw)
    unfold sourceModeF
    exact hsw.mul (continuous_const.mul (continuous_sourceModeU P z))
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr ?_
  refine ((integrable_density P).const_mul (‖z‖ ^ 2 * C ^ 2)).mono'
    (hcont.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hk := density_pos P x
  have hu2 : ‖sourceModeU (source P) z x‖ ^ 2 ≤ (C * density P x) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, sqrtWeight, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (sourceWeight_pos (source P) x).le, sourceModeF, norm_mul, norm_neg, mul_pow,
    sourceWeight, source_k]
  calc (density P x)⁻¹ * (‖z‖ ^ 2 * ‖sourceModeU (source P) z x‖ ^ 2)
      ≤ (density P x)⁻¹ * (‖z‖ ^ 2 * (C * density P x) ^ 2) := by gcongr
    _ = ‖z‖ ^ 2 * C ^ 2 * density P x := by field_simp

/-- **(6) Divisor eigenvectors.** Every zero `z ≠ 0` of `F` with `|Im z| ≤ 1` gives a nonzero
eigenvector of `B` in `L²(0,1)` with eigenvalue `-1/z`. -/
theorem sourceInverseOp_eigen {z : ℂ} (hz0 : z ≠ 0) (hz : |z.im| ≤ 1)
    (hzero : xiC (source P) z = 0) :
    divisorEigenvector (source P) (memLp_sourceModeF P hz hzero) ≠ 0 ∧
      sourceInverseOp P (divisorEigenvector (source P) (memLp_sourceModeF P hz hzero)) =
        (-z⁻¹) • divisorEigenvector (source P) (memLp_sourceModeF P hz hzero) :=
  ⟨divisorEigenvector_ne_zero _ _ (integral_sourceModeF P hz0 hz hzero),
    compactSourceInverse_divisorEigenvector _ _ hz0 (hasShiftedTail_source P z) _
      (integrable_sourceModeF P hz hzero) (tendsto_sourceModeU P hz hzero).1
      (integral_sourceModeF P hz0 hz hzero)⟩

theorem abs_upperZero_im_le (n : ℤ) : |(upperZero P n).im| ≤ 1 := by
  obtain ⟨h1, h2⟩ := upperZero_im_mem P n
  rw [abs_of_pos h1]; linarith

/-- The eigenvector attached to `z_n^+`. -/
def upperEigenvector (n : ℤ) : Lp ℂ 2 unitIntervalMeasure :=
  divisorEigenvector (source P) (memLp_sourceModeF P (abs_upperZero_im_le P n) (xiC_upperZero P n))

/-- **(6)** Each `z_n^+` gives a nonzero eigenvector with eigenvalue `-1/z_n^+`, which lies in the
upper half-plane; the eigenvalues are pairwise distinct. -/
theorem upperEigenvector_spec (n : ℤ) :
    upperEigenvector P n ≠ 0 ∧
      sourceInverseOp P (upperEigenvector P n) = (-(upperZero P n)⁻¹) • upperEigenvector P n ∧
      0 < (-(upperZero P n)⁻¹).im :=
  ⟨(sourceInverseOp_eigen P (upperZero_ne_zero P n) (abs_upperZero_im_le P n)
      (xiC_upperZero P n)).1,
    (sourceInverseOp_eigen P (upperZero_ne_zero P n) (abs_upperZero_im_le P n)
      (xiC_upperZero P n)).2,
    neg_inv_upperZero_im_pos P n⟩

/-! ### No finite-index realization -/

/-- **Index bound.** A `B`-self-adjoint operator `T` on a space whose form is positive definite on
the kernel of `π : V → ℂ^κ` (a Pontryagin space of negative index `κ`) can carry at most `κ` of
the eigenvalues `-1/z_n^+`. -/
theorem realization_card_le {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) {κ : ℕ} (π : V →ₗ[ℂ] (Fin κ → ℂ))
    (hπ : ∀ v, π v = 0 → v ≠ 0 → 0 < (B v v).re) (T : V →ₗ[ℂ] V)
    (hT : ∀ x y, B (T x) y = B x (T y)) {N : ℕ} (w : Fin N → V) (hw0 : ∀ i, w i ≠ 0)
    (hTw : ∀ i, T (w i) = (-(upperZero P (i : ℕ))⁻¹) • w i) : N ≤ κ :=
  card_upper_eigenvalues_le B π hπ T hT (fun i => -(upperZero P (i : ℕ))⁻¹)
    (fun i j h => Fin.ext (by exact_mod_cast neg_inv_upperZero_injective P h))
    (fun i => neg_inv_upperZero_im_pos P _) w hw0 hTw

/-- **No finite-index realization of the divisor.** No such `T` carries all eigenvalues
`-1/z_n^+`, `n ∈ ℕ`. -/
theorem no_finite_index_realization {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) {κ : ℕ} (π : V →ₗ[ℂ] (Fin κ → ℂ))
    (hπ : ∀ v, π v = 0 → v ≠ 0 → 0 < (B v v).re) (T : V →ₗ[ℂ] V)
    (hT : ∀ x y, B (T x) y = B x (T y)) :
    ¬ ∃ w : ℕ → V, (∀ n, w n ≠ 0) ∧ ∀ n : ℕ, T (w n) = (-(upperZero P n)⁻¹) • w n := by
  rintro ⟨w, hw0, hTw⟩
  have := realization_card_le P B π hπ T hT (N := κ + 1) (fun i => w i) (fun i => hw0 i)
    fun i => hTw i
  omega

end UniversalBoundaryCountermodel

end

end RHTower

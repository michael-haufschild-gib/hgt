import GaloisForLFunctions.RHTower.CCMParityTopLayerProjection
import GaloisForLFunctions.RHTower.CCMParityQuartetEvenFloor

/-!
# Growing transforms of interval sources as half-line pairings

Let `g` be a real square-integrable function vanishing for `|x| ≥ a` (`RealIntervalSource a g`) and let
`σ = t + iδ`. Reflecting about `a` (`s = a − x`) gives the exact identity

`ĝ(−σ) = ∫ g(x) e^{−iσx} dx = e^{−iσa} ⟨g(a − ·), ψ⟩`, `ψ(s) = e^{−(δ − it)s}`
(`testTransform_neg_eq_exp_mul_halfLinePairing`).

So the growing transforms at the top layer are pairings of the reflected source with the Cauchy
model functions, and `Σ_j M_j Re ĝ(−σ_j)² = e^{2δa} T(θ(a))[g(a − ·)]` with `θ_j(a) = −2t_j a`
(`sum_re_testTransform_sq_eq`).

For a source of parity `s = ±1` the zero-sum term at `σ` splits over the real and imaginary parts:
`Re(f̂(−σ) conj f̂(−σ̄)) = s (Re f̂₁(−σ)² + Re f̂₂(−σ)²)` (`re_zeroSumTerm_parity`).

**Even halving** (`halfLineForm_reflect_ge_of_even`). For even `g` the reflected function splits
into its part on `(0, a]` (mass `‖g‖²/2`, the half `x ≥ 0`) and its part on `(a, 2a)` whose
pairings are `O(e^{−δa})`. Hence

`T(θ)[g(a − ·)] ≥ −(max(λ_max(θ + π𝟙), 0)/2 + (3/(2δ)) e^{−δa} Σ_j |M_j|) ‖g‖²`.
-/

open Matrix Complex Filter Topology MeasureTheory Set
open RHTower.CCMParityQuartet GaloisForLFunctions.HTGeometry

namespace RHTower.CCMParityCauchy

noncomputable section

variable {m : ℕ}

/-! ## Cauchy–Schwarz for an arbitrary measure -/

theorem norm_integral_mul_sq_le_of_memLp {μ : Measure ℝ} {F H : ℝ → ℂ} (hF : MemLp F 2 μ)
    (hH : MemLp H 2 μ) :
    ‖∫ x, F x * H x ∂μ‖ ^ 2 ≤ (∫ x, ‖F x‖ ^ 2 ∂μ) * ∫ x, ‖H x‖ ^ 2 ∂μ := by
  have hF' : MemLp F (ENNReal.ofReal 2) μ := by simpa using hF
  have hH' : MemLp H (ENNReal.ofReal 2) μ := by simpa using hH
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hF' hH'
  have h1 : ‖∫ x, F x * H x ∂μ‖ ≤ ∫ x, ‖F x‖ * ‖H x‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    simp only [norm_mul]
  have hA : 0 ≤ ∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ := integral_nonneg fun _ => by positivity
  have hB : 0 ≤ ∫ x, ‖H x‖ ^ (2 : ℝ) ∂μ := integral_nonneg fun _ => by positivity
  have hrpow : ∀ g : ℝ → ℂ, (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) = ∫ x, ‖g x‖ ^ 2 ∂μ := fun g => by
    congr 1
    funext x
    exact Real.rpow_two _
  have hsq : (∫ x, ‖F x‖ * ‖H x‖ ∂μ) ^ 2 ≤
      ((∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) * (∫ x, ‖H x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (integral_nonneg fun _ => by positivity) hcs 2
  rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hA, Real.sq_sqrt hB,
    hrpow F, hrpow H] at hsq
  calc ‖∫ x, F x * H x ∂μ‖ ^ 2 ≤ (∫ x, ‖F x‖ * ‖H x‖ ∂μ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := hsq

/-! ## Reflection about a point -/

theorem setIntegral_Ioi_zero_eq_Iio {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ)
    (F : ℝ → E) : ∫ s in Ioi (0 : ℝ), F s = ∫ x in Iio a, F (a - x) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Iio]
  have h := integral_sub_left_eq_self ((Ioi (0 : ℝ)).indicator F) volume a
  rw [← h]
  congr 1
  funext x
  by_cases hx : x < a
  · rw [indicator_of_mem (show a - x ∈ Ioi (0 : ℝ) from sub_pos.mpr hx),
      indicator_of_mem (show x ∈ Iio a from hx)]
  · rw [indicator_of_notMem (show a - x ∉ Ioi (0 : ℝ) by simp only [mem_Ioi]; linarith),
      indicator_of_notMem (show x ∉ Iio a from hx)]

/-! ## Interval sources -/

/-- A real square-integrable function vanishing for `|x| ≥ a`. -/
structure RealIntervalSource (a : ℝ) (g : ℝ → ℝ) : Prop where
  memLp : MemLp g 2
  vanish : ∀ x, a ≤ |x| → g x = 0

theorem RealIntervalSource.integrable_mul_exp {a : ℝ} {g : ℝ → ℝ} (hg : RealIntervalSource a g) (c : ℂ) :
    Integrable fun x : ℝ => (g x : ℂ) * Complex.exp (c * x) := by
  have hH : MemLp ((Icc (-a) a).indicator fun x : ℝ => Complex.exp (c * x)) 2 :=
    memLp_indicator_Icc (by fun_prop) a
  have hprod := (hg.memLp.ofReal (K := ℂ)).integrable_mul hH
  refine hprod.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  by_cases hx : x ∈ Icc (-a) a
  · simp [indicator_of_mem hx]
  · rw [indicator_of_notMem hx]
    have hxa : a ≤ |x| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · exact le_trans (by linarith) (neg_le_abs x)
      · exact (h.le.trans (le_abs_self x))
    rw [hg.vanish x hxa]
    simp

theorem RealIntervalSource.memLp_reflect {a : ℝ} {g : ℝ → ℝ} (hg : RealIntervalSource a g) :
    MemLp (fun s => g (a - s)) 2 (volume.restrict (Ioi 0)) :=
  (hg.memLp.comp_measurePreserving (Measure.measurePreserving_sub_left volume a)).restrict _

/-- **The growing transform is a half-line pairing of the reflected source.** -/
theorem testTransform_neg_eq_exp_mul_halfLinePairing {a : ℝ} {g : ℝ → ℝ}
    (hg : RealIntervalSource a g) (δ : ℝ) (t : Fin m → ℝ) (j : Fin m) :
    testTransform (fun x => (g x : ℂ)) (-((t j : ℂ) + δ * I)) =
      Complex.exp (-(I * ((t j : ℂ) + δ * I)) * a) *
        halfLinePairing δ t (fun s => g (a - s)) j := by
  have hP : halfLinePairing δ t (fun s => g (a - s)) j =
      Complex.exp (-((δ : ℂ) - I * t j) * a) *
        testTransform (fun x => (g x : ℂ)) (-((t j : ℂ) + δ * I)) := by
    unfold halfLinePairing testTransform
    rw [setIntegral_Ioi_zero_eq_Iio a]
    simp only [sub_sub_cancel]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      have hxa : a ≤ x := not_lt.mp hx
      rw [hg.vanish x (hxa.trans (le_abs_self x))]
      simp, ← integral_const_mul]
    congr 1
    funext x
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hP, ← mul_assoc, ← Complex.exp_add]
  have : -(I * ((t j : ℂ) + δ * I)) * a + -((δ : ℂ) - I * t j) * a = 0 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [this, Complex.exp_zero, one_mul]

/-- The aperture phase: `e^{−2iσ_j a} = e^{2δa} e^{iθ_j(a)}`, `θ_j(a) = −2t_j a`. -/
theorem exp_neg_two_mul_I_top (δ a tj : ℝ) :
    Complex.exp (-(I * ((tj : ℂ) + δ * I)) * a) ^ 2 =
      ((Real.exp (2 * δ * a) : ℝ) : ℂ) * Complex.exp (((-2 * tj * a : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_nat_mul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The top-layer growing sum is the half-line form at the aperture phases.** -/
theorem sum_re_testTransform_sq_eq {a : ℝ} {g : ℝ → ℝ} (hg : RealIntervalSource a g)
    (δ : ℝ) (t M : Fin m → ℝ) :
    ∑ j, M j * ((testTransform (fun x => (g x : ℂ)) (-((t j : ℂ) + δ * I))) ^ 2).re =
      Real.exp (2 * δ * a) *
        halfLineForm δ t M (fun j => -2 * t j * a) (fun s => g (a - s)) := by
  unfold halfLineForm
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [testTransform_neg_eq_exp_mul_halfLinePairing hg, mul_pow, exp_neg_two_mul_I_top]
  rw [show (M j : ℂ) * Complex.exp (((-2 * t j * a : ℝ) : ℂ) * I) *
      halfLinePairing δ t (fun s => g (a - s)) j ^ 2 =
    (M j : ℂ) * (Complex.exp (((-2 * t j * a : ℝ) : ℂ) * I) *
      halfLinePairing δ t (fun s => g (a - s)) j ^ 2) by ring]
  rw [show ((Real.exp (2 * δ * a) : ℝ) : ℂ) * Complex.exp (((-2 * t j * a : ℝ) : ℂ) * I) *
      halfLinePairing δ t (fun s => g (a - s)) j ^ 2 =
    ((Real.exp (2 * δ * a) : ℝ) : ℂ) * (Complex.exp (((-2 * t j * a : ℝ) : ℂ) * I) *
      halfLinePairing δ t (fun s => g (a - s)) j ^ 2) by ring]
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

/-! ## The parity split of a zero-sum term -/

theorem testTransform_add_I_mul {f g : ℝ → ℂ} (w : ℂ)
    (hf : Integrable fun x : ℝ => f x * Complex.exp (I * w * x))
    (hg : Integrable fun x : ℝ => g x * Complex.exp (I * w * x)) :
    testTransform (fun x => f x + I * g x) w = testTransform f w + I * testTransform g w := by
  unfold testTransform
  rw [← integral_const_mul, ← integral_add hf (hg.const_mul I)]
  congr 1
  funext x
  ring

/-- **Parity split.** For a source of parity `s = ±1` with square-integrable real and imaginary
parts vanishing off `(−A, A)`,
`Re(f̂(−σ) conj f̂(−σ̄)) = s (Re f̂₁(−σ)² + Re f̂₂(−σ)²)`. -/
theorem re_zeroSumTerm_parity {A : ℝ} {f : ℝ → ℂ} {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hpar : ∀ x, f (-x) = (s : ℂ) * f x) (h1 : RealIntervalSource A fun x => (f x).re)
    (h2 : RealIntervalSource A fun x => (f x).im) (σ : ℂ) :
    (zeroSumTerm f σ).re =
      s * ((testTransform (fun x => (((f x).re : ℝ) : ℂ)) (-σ)) ^ 2).re +
        s * ((testTransform (fun x => (((f x).im : ℝ) : ℂ)) (-σ)) ^ 2).re := by
  have hs2 : (s : ℂ) * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  set f₁ : ℝ → ℂ := fun x => (((f x).re : ℝ) : ℂ) with hf₁
  set f₂ : ℝ → ℂ := fun x => (((f x).im : ℝ) : ℂ) with hf₂
  have hsplit : f = fun x => f₁ x + I * f₂ x := by
    funext x
    simp only [hf₁, hf₂]
    rw [mul_comm]
    exact (Complex.re_add_im (f x)).symm
  have hT : ∀ w : ℂ, testTransform f w = testTransform f₁ w + I * testTransform f₂ w := by
    intro w
    conv_lhs => rw [hsplit]
    exact testTransform_add_I_mul w (h1.integrable_mul_exp _) (h2.integrable_mul_exp _)
  -- parity of the components
  have hpar₁ : ∀ x, f₁ (-x) = (s : ℂ) * f₁ x := by
    intro x
    simp only [hf₁, hpar x]
    rw [show ((s : ℂ) * f x).re = s * (f x).re by simp [Complex.mul_re]]
    push_cast; ring
  have hpar₂ : ∀ x, f₂ (-x) = (s : ℂ) * f₂ x := by
    intro x
    simp only [hf₂, hpar x]
    rw [show ((s : ℂ) * f x).im = s * (f x).im by simp [Complex.mul_im]]
    push_cast; ring
  -- `conj f̂_k(−σ̄) = s f̂_k(−σ)`
  have hconj : ∀ (g : ℝ → ℂ), (∀ x, (starRingEnd ℂ) (g x) = g x) →
      (∀ x, g (-x) = (s : ℂ) * g x) →
      (starRingEnd ℂ) (testTransform g (-(starRingEnd ℂ) σ)) = (s : ℂ) * testTransform g (-σ) := by
    intro g hreal hg
    rw [← testTransform_conj]
    have hfun : (fun x => (starRingEnd ℂ) (g x)) = g := funext hreal
    rw [hfun, testTransform_neg_of_reflect hg σ, ← mul_assoc, hs2, one_mul]
  have hreal₁ : ∀ x, (starRingEnd ℂ) (f₁ x) = f₁ x := fun x => Complex.conj_ofReal _
  have hreal₂ : ∀ x, (starRingEnd ℂ) (f₂ x) = f₂ x := fun x => Complex.conj_ofReal _
  have hc₁ := hconj f₁ hreal₁ hpar₁
  have hc₂ := hconj f₂ hreal₂ hpar₂
  unfold zeroSumTerm
  rw [hT, hT, map_add, map_mul, Complex.conj_I, hc₁, hc₂]
  set A₁ := testTransform f₁ (-σ)
  set A₂ := testTransform f₂ (-σ)
  have : (A₁ + I * A₂) * ((s : ℂ) * A₁ + -I * ((s : ℂ) * A₂)) =
      ((s : ℝ) : ℂ) * A₁ ^ 2 + ((s : ℝ) : ℂ) * A₂ ^ 2 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [this, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]

/-! ## Half-line pairings: linearity and size -/

theorem halfLinePairing_add {δ : ℝ} (hδ : 0 < δ) (t : Fin m → ℝ) {v w : ℝ → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioi 0))) (hw : MemLp w 2 (volume.restrict (Ioi 0)))
    (j : Fin m) :
    halfLinePairing δ t (v + w) j = halfLinePairing δ t v j + halfLinePairing δ t w j := by
  have hp : 0 < ((δ : ℂ) - I * t j).re := by simp [hδ]
  unfold halfLinePairing
  rw [← integral_add (integrableOn_mul_exp_neg hv hp) (integrableOn_mul_exp_neg hw hp)]
  congr 1
  funext s
  simp only [Pi.add_apply]
  push_cast
  ring

theorem integral_norm_sq_exp_Ioi {δ : ℝ} (hδ : 0 < δ) (tj c : ℝ) :
    ∫ s in Ioi c, ‖Complex.exp (-((δ : ℂ) - I * tj) * s)‖ ^ 2 =
      Real.exp (-(2 * δ) * c) / (2 * δ) := by
  have hfun : ∀ s : ℝ, ‖Complex.exp (-((δ : ℂ) - I * tj) * s)‖ ^ 2 = Real.exp (-(2 * δ) * s) := by
    intro s
    rw [Complex.norm_exp, ← Real.exp_nat_mul]
    congr 1
    simp [Complex.mul_re]
    ring
  simp_rw [hfun]
  rw [integral_exp_mul_Ioi (by linarith) c]
  field_simp

theorem memLp_exp_Ioi_restrict {δ : ℝ} (hδ : 0 < δ) (tj : ℝ) :
    MemLp (fun s : ℝ => Complex.exp (-((δ : ℂ) - I * tj) * s)) 2 (volume.restrict (Ioi 0)) :=
  memLp_exp_neg_Ioi (by simp [hδ])

/-- `|⟨v, ψ_j⟩|² ≤ (∫_0^∞ v²)/(2δ)`. -/
theorem norm_halfLinePairing_sq_le {δ : ℝ} (hδ : 0 < δ) (t : Fin m → ℝ) {v : ℝ → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioi 0))) (j : Fin m) :
    ‖halfLinePairing δ t v j‖ ^ 2 ≤ (∫ s in Ioi (0 : ℝ), v s ^ 2) * (1 / (2 * δ)) := by
  have h := norm_integral_mul_sq_le_of_memLp (hv.ofReal (K := ℂ)) (memLp_exp_Ioi_restrict hδ (t j))
  unfold halfLinePairing
  refine h.trans (le_of_eq ?_)
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp [Complex.norm_real, sq_abs]
  · rw [integral_norm_sq_exp_Ioi hδ (t j) 0]
    simp

/-- A function vanishing on `(0, c]` has pairings `O(e^{−δc})`. -/
theorem norm_halfLinePairing_sq_le_of_vanish {δ : ℝ} (hδ : 0 < δ) (t : Fin m → ℝ) {v : ℝ → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioi 0))) {c : ℝ} (hc : 0 ≤ c)
    (hvan : ∀ s ∈ Ioc 0 c, v s = 0) (j : Fin m) :
    ‖halfLinePairing δ t v j‖ ^ 2 ≤
      (∫ s in Ioi (0 : ℝ), v s ^ 2) * (Real.exp (-(2 * δ) * c) / (2 * δ)) := by
  set ψ : ℝ → ℂ := fun s => Complex.exp (-((δ : ℂ) - I * t j) * s) with hψ
  have hH : MemLp ((Ioi c).indicator ψ) 2 (volume.restrict (Ioi 0)) :=
    (memLp_exp_Ioi_restrict hδ (t j)).indicator measurableSet_Ioi
  have h := norm_integral_mul_sq_le_of_memLp (hv.ofReal (K := ℂ)) hH
  have heq : halfLinePairing δ t v j =
      ∫ s in Ioi (0 : ℝ), (v s : ℂ) * (Ioi c).indicator ψ s := by
    unfold halfLinePairing
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    by_cases hsc : s ∈ Ioi c
    · rw [indicator_of_mem hsc]
    · rw [indicator_of_notMem hsc, hvan s ⟨hs, not_lt.mp hsc⟩]
      simp
  rw [heq]
  refine h.trans (le_of_eq ?_)
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp [Complex.norm_real, sq_abs]
  · have hfun : (fun s => ‖(Ioi c).indicator ψ s‖ ^ 2) =
        (Ioi c).indicator (fun s => ‖ψ s‖ ^ 2) := by
      funext s
      by_cases hs : s ∈ Ioi c <;> simp [hs]
    rw [hfun, setIntegral_indicator measurableSet_Ioi,
      show Ioi (0 : ℝ) ∩ Ioi c = Ioi c by
        ext s; simp only [mem_inter_iff, mem_Ioi]; constructor
        · exact fun h => h.2
        · exact fun h => ⟨by linarith, h⟩]
    exact integral_norm_sq_exp_Ioi hδ (t j) c

/-- **Perturbation of the half-line form.** -/
theorem abs_halfLineForm_add_sub_le {δ : ℝ} (hδ : 0 < δ) (t M θ : Fin m → ℝ) {v w : ℝ → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioi 0))) (hw : MemLp w 2 (volume.restrict (Ioi 0))) :
    |halfLineForm δ t M θ (v + w) - halfLineForm δ t M θ v| ≤
      ∑ j, |M j| * (‖halfLinePairing δ t w j‖ *
        (2 * ‖halfLinePairing δ t v j‖ + ‖halfLinePairing δ t w j‖)) := by
  unfold halfLineForm
  rw [← Complex.sub_re, ← Finset.sum_sub_distrib]
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
  rw [halfLinePairing_add hδ t hv hw]
  set p := halfLinePairing δ t v j
  set q := halfLinePairing δ t w j
  have : (M j : ℂ) * Complex.exp ((θ j : ℂ) * I) * (p + q) ^ 2 -
      (M j : ℂ) * Complex.exp ((θ j : ℂ) * I) * p ^ 2 =
      (M j : ℂ) * Complex.exp ((θ j : ℂ) * I) * (q * (2 * p + q)) := by ring
  rw [this, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  gcongr
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_ofNat]

/-! ## The even half -/

theorem integral_sq_reflect_Iic {a : ℝ} {g : ℝ → ℝ} (hg : RealIntervalSource a g) :
    ∫ s in Ioi (0 : ℝ), ((Iic a).indicator (fun s => g (a - s)) s) ^ 2 =
      ∫ x in Ioi (0 : ℝ), g x ^ 2 := by
  rw [setIntegral_Ioi_zero_eq_Iio a]
  have hfun : ∀ x, ((Iic a).indicator (fun s => g (a - s)) (a - x)) ^ 2 =
      (Ici 0).indicator (fun x => g x ^ 2) x := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [indicator_of_mem (show a - x ∈ Iic a by simp only [mem_Iic]; linarith),
        indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx), sub_sub_cancel]
    · rw [indicator_of_notMem (show a - x ∉ Iic a by simp only [mem_Iic]; push Not at hx; linarith),
        indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx)]
      simp
  simp_rw [hfun]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    have hxa : a ≤ x := not_lt.mp hx
    by_cases h0 : 0 ≤ x
    · rw [indicator_of_mem (show x ∈ Ici (0 : ℝ) from h0), hg.vanish x (hxa.trans (le_abs_self x))]
      simp
    · rw [indicator_of_notMem (show x ∉ Ici (0 : ℝ) from h0)]]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem integral_sq_eq_two_mul_Ioi_of_even {g : ℝ → ℝ} (hg : MemLp g 2) (heven : ∀ x, g (-x) = g x) :
    ∫ x, g x ^ 2 = 2 * ∫ x in Ioi (0 : ℝ), g x ^ 2 := by
  have hint : Integrable fun x => g x ^ 2 := hg.integrable_sq
  rw [← integral_add_compl measurableSet_Ioi hint, compl_Ioi]
  have h := integral_comp_neg_Iic (0 : ℝ) (fun x => g x ^ 2)
  simp only [heven, neg_zero] at h
  rw [h]
  ring

theorem integral_sq_reflect {a : ℝ} {g : ℝ → ℝ} (hg : RealIntervalSource a g) :
    ∫ s in Ioi (0 : ℝ), g (a - s) ^ 2 = ∫ x, g x ^ 2 := by
  rw [setIntegral_Ioi_zero_eq_Iio a]
  simp only [sub_sub_cancel]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    have hxa : a ≤ x := not_lt.mp hx
    rw [hg.vanish x (hxa.trans (le_abs_self x))]
    simp

/-- **The even floor of the reflected form.** -/
theorem halfLineForm_reflect_ge_of_even {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ)
    {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℝ} (hg : RealIntervalSource a g) (heven : ∀ x, g (-x) = g x) :
    -((max (ccmLambdaMax δ t M (halfTurn θ)) 0 / 2 +
        3 / (2 * δ) * Real.exp (-(δ * a)) * ∑ j, |M j|) * ∫ x, g x ^ 2) ≤
      halfLineForm δ t M θ (fun s => g (a - s)) := by
  set N := ∫ x, g x ^ 2 with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => sq_nonneg _
  set v : ℝ → ℝ := fun s => g (a - s) with hv
  set vn : ℝ → ℝ := (Iic a).indicator v with hvn
  set vf : ℝ → ℝ := (Ioi a).indicator v with hvf
  have hvm : MemLp v 2 (volume.restrict (Ioi 0)) := hg.memLp_reflect
  have hvnm : MemLp vn 2 (volume.restrict (Ioi 0)) := hvm.indicator measurableSet_Iic
  have hvfm : MemLp vf 2 (volume.restrict (Ioi 0)) := hvm.indicator measurableSet_Ioi
  have hsum : vn + vf = v := by
    funext s
    simp only [Pi.add_apply, hvn, hvf]
    rw [← compl_Iic]
    exact indicator_self_add_compl_apply _ _ _
  -- masses
  have hNn : ∫ s in Ioi (0 : ℝ), vn s ^ 2 = N / 2 := by
    rw [integral_sq_reflect_Iic hg, hN, integral_sq_eq_two_mul_Ioi_of_even hg.memLp heven]
    ring
  have hNf : ∫ s in Ioi (0 : ℝ), vf s ^ 2 ≤ N := by
    rw [hN, ← integral_sq_reflect hg]
    refine setIntegral_mono_on hvfm.integrable_sq hvm.integrable_sq measurableSet_Ioi
      fun s _ => ?_
    simp only [hvf]
    by_cases hs : s ∈ Ioi a
    · rw [indicator_of_mem hs]
    · rw [indicator_of_notMem hs]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg _
  -- pairings
  have hPn : ∀ j, ‖halfLinePairing δ t vn j‖ ^ 2 ≤ N * (1 / (2 * δ)) := by
    intro j
    refine (norm_halfLinePairing_sq_le hδ t hvnm j).trans ?_
    rw [hNn]
    have : 0 ≤ 1 / (2 * δ) := by positivity
    nlinarith
  have hPf : ∀ j, ‖halfLinePairing δ t vf j‖ ^ 2 ≤ N * (Real.exp (-(2 * δ) * a) / (2 * δ)) := by
    intro j
    refine (norm_halfLinePairing_sq_le_of_vanish hδ t hvfm ha (fun s hs => ?_) j).trans ?_
    · simp only [hvf]
      rw [indicator_of_notMem (show s ∉ Ioi a by simp only [mem_Ioi, not_lt]; exact hs.2)]
    · exact mul_le_mul_of_nonneg_right hNf (by positivity)
  -- the near part
  have hnear := halfLineForm_ge hδ ht htpos hm M θ hvnm
  rw [hNn] at hnear
  -- the far part
  have hpert := abs_halfLineForm_add_sub_le hδ t M θ hvnm hvfm
  rw [hsum] at hpert
  set E := Real.exp (-(δ * a)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hE2 : Real.exp (-(2 * δ) * a) = E ^ 2 := by
    rw [hE, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hterm : ∀ j, ‖halfLinePairing δ t vf j‖ *
      (2 * ‖halfLinePairing δ t vn j‖ + ‖halfLinePairing δ t vf j‖) ≤ 3 / (2 * δ) * E * N := by
    intro j
    set x := ‖halfLinePairing δ t vf j‖
    set y := ‖halfLinePairing δ t vn j‖
    have hx := hPf j
    have hy := hPn j
    rw [hE2] at hx
    have hx0 : 0 ≤ x := norm_nonneg _
    have hy0 : 0 ≤ y := norm_nonneg _
    have hk : 0 < 1 / (2 * δ) := by positivity
    -- `2xy ≤ x²/E + E y²`
    have hamgm : 2 * x * y ≤ x ^ 2 / E + E * y ^ 2 := by
      rw [div_add' _ _ _ hE0.ne', le_div_iff₀ hE0]
      nlinarith [sq_nonneg (x - E * y)]
    have h1 : x ^ 2 / E ≤ N * (1 / (2 * δ)) * E := by
      rw [div_le_iff₀ hE0]
      calc x ^ 2 ≤ N * (E ^ 2 / (2 * δ)) := hx
        _ = N * (1 / (2 * δ)) * E * E := by ring
    have h2 : E * y ^ 2 ≤ E * (N * (1 / (2 * δ))) := mul_le_mul_of_nonneg_left hy hE0.le
    have h3 : x ^ 2 ≤ N * (1 / (2 * δ)) * E := by
      calc x ^ 2 ≤ N * (E ^ 2 / (2 * δ)) := hx
        _ = N * (1 / (2 * δ)) * E * E := by ring
        _ ≤ N * (1 / (2 * δ)) * E * 1 := by
          apply mul_le_mul_of_nonneg_left hE1; positivity
        _ = N * (1 / (2 * δ)) * E := mul_one _
    calc x * (2 * y + x) = 2 * x * y + x ^ 2 := by ring
      _ ≤ (N * (1 / (2 * δ)) * E + E * (N * (1 / (2 * δ)))) + N * (1 / (2 * δ)) * E := by
        linarith
      _ = 3 / (2 * δ) * E * N := by ring
  have hpert' : |halfLineForm δ t M θ v - halfLineForm δ t M θ vn| ≤
      3 / (2 * δ) * E * (∑ j, |M j|) * N := by
    refine hpert.trans ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have := mul_le_mul_of_nonneg_left (hterm j) (abs_nonneg (M j))
    linarith
  rw [abs_le] at hpert'
  have hmax0 : 0 ≤ max (ccmLambdaMax δ t M (halfTurn θ)) 0 := le_max_right _ _
  nlinarith [hpert'.1]

end

end RHTower.CCMParityCauchy

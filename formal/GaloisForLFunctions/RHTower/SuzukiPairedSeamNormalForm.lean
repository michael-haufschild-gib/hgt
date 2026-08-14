import GaloisForLFunctions.RHTower.SuzukiLogisticCoupling

/-!
# The exact paired normal form of a logarithmic seam

At the seam point `e^{-L}` the fixed-window logarithmic jump

`(J₀u)(x) = ∫_{-1}^{1} [u(x) - u(y)] / |x - y| dy`

splits into three physical pieces: the near same-side window `(0, e^{-L})`, the far same-side
window `(e^{-L}, 1)`, and the opposite window `(-1, 0)`.  The exponential charts
`y = e^{-L}e^{-s}`, `y = e^{-L}e^{s}` and `y = -e^{-v}` turn them into

`∫₀^∞ [F₊(L) - F₊(L+s)]/(e^s - 1) ds`,
`∫₀^L [F₊(L) - F₊(L-s)] e^s/(e^s - 1) ds`,
`∫₀^∞ [F₊(L) - F₋(v)]/(1 + e^{v-L}) dv`,

where `F₊(L) = u(e^{-L}) - u(0)` and `F₋(L) = u(-e^{-L}) - u(0)` are the two oriented seam germs.
Splitting `e^s/(e^s-1) = 1 + 1/(e^s-1)` and evaluating the scalar cutoff integral gives the exact
normal form

`(J₀u)(e^{-L}) = [2L + q(L)] F₊(L) - ∫₀^L F₊ + (R F₊)(L) - (C F₋)(L)`,  `q(L) = log(1+e^{-L})`,

in which the only cross-orientation term is the Carleman block `C`.  Its `L`-derivative is the
logistic coupling, so the paired seam has a bounded off-diagonal block on the whole Gamma strip.
-/

open Set MeasureTheory Filter Topology

namespace RHTower

noncomputable section

/-! ## The two oriented seam germs -/

/-- The right seam germ `F₊(L) = u(e^{-L}) - u(0)`. -/
def seamRight (u : ℝ → ℝ) (L : ℝ) : ℝ := u (Real.exp (-L)) - u 0

/-- The left seam germ `F₋(L) = u(-e^{-L}) - u(0)`. -/
def seamLeft (u : ℝ → ℝ) (L : ℝ) : ℝ := u (-Real.exp (-L)) - u 0

theorem seamRight_comp_neg (u : ℝ → ℝ) (L : ℝ) :
    seamRight (fun x => u (-x)) L = seamLeft u L := by
  rw [seamRight, seamLeft, neg_zero]

theorem seamLeft_comp_neg (u : ℝ → ℝ) (L : ℝ) :
    seamLeft (fun x => u (-x)) L = seamRight u L := by
  rw [seamRight, seamLeft, neg_zero, neg_neg]

/-! ## The three window pieces -/

/-- The near same-side window `(0, e^{-L})`. -/
def jumpNear (u : ℝ → ℝ) (L : ℝ) : ℝ :=
  ∫ y in Ioo 0 (Real.exp (-L)), (u (Real.exp (-L)) - u y) / (Real.exp (-L) - y)

/-- The far same-side window `(e^{-L}, 1)`. -/
def jumpFar (u : ℝ → ℝ) (L : ℝ) : ℝ :=
  ∫ y in Ioo (Real.exp (-L)) 1, (u (Real.exp (-L)) - u y) / (y - Real.exp (-L))

/-- The opposite window `(-1, 0)`. -/
def jumpOpposite (u : ℝ → ℝ) (L : ℝ) : ℝ :=
  ∫ y in Ioo (-1) 0, (u (Real.exp (-L)) - u y) / (Real.exp (-L) - y)

/-- **`(2)`: the fixed-window logarithmic jump at the right seam point**, read through the
difference cancellation as the sum of its three physical windows. -/
def logJumpRight (u : ℝ → ℝ) (L : ℝ) : ℝ :=
  jumpNear u L + jumpFar u L + jumpOpposite u L

/-- The logarithmic jump at the left seam point, obtained by reflecting the window. -/
def logJumpLeft (u : ℝ → ℝ) (L : ℝ) : ℝ := logJumpRight (fun x => u (-x)) L

/-! ## The seam operators -/

/-- **`(3)`: the same-side difference operator `R`.** -/
def seamR (F : ℝ → ℝ) (L : ℝ) : ℝ :=
  (∫ s in Ioi (0:ℝ), (F L - F (L + s)) / (Real.exp s - 1))
    + ∫ s in Ioo (0:ℝ) L, (F L - F (L - s)) / (Real.exp s - 1)

/-- **`(3)`: the Carleman cross operator `C`.** -/
def seamC (F : ℝ → ℝ) (L : ℝ) : ℝ := ∫ v in Ioi (0:ℝ), F v * carlemanCutoffFactor L v

/-- **`(5)`: the exponentially small seam scalar.** -/
def seamScalar (L : ℝ) : ℝ := Real.log (1 + Real.exp (-L))

/-! ## The three exponential charts -/

theorem exp_neg_log_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.exp (-Real.log (a / b)) = b / a := by
  rw [← Real.log_inv, Real.exp_log (by positivity), inv_div]

theorem image_nearChart (L : ℝ) :
    (fun s : ℝ => Real.exp (-L) * Real.exp (-s)) '' Ioi (0:ℝ) = Ioo 0 (Real.exp (-L)) := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs0 : (0:ℝ) < s := hs
    refine ⟨by positivity, ?_⟩
    have h1 : Real.exp (-s) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    nlinarith [Real.exp_pos (-L), Real.exp_pos (-s)]
  · rintro ⟨h0, h1⟩
    have hy : (0:ℝ) < y := h0
    have hr : (0:ℝ) < Real.exp (-L) := Real.exp_pos _
    refine ⟨Real.log (Real.exp (-L) / y), ?_, ?_⟩
    · show (0:ℝ) < Real.log (Real.exp (-L) / y)
      exact Real.log_pos ((one_lt_div hy).mpr h1)
    · show Real.exp (-L) * Real.exp (-Real.log (Real.exp (-L) / y)) = y
      rw [exp_neg_log_div hr hy]
      field_simp

theorem image_farChart (L : ℝ) :
    (fun s : ℝ => Real.exp (-L) * Real.exp s) '' Ioo (0:ℝ) L = Ioo (Real.exp (-L)) 1 := by
  have hr : (0:ℝ) < Real.exp (-L) := Real.exp_pos _
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    constructor
    · have h1 : (1:ℝ) < Real.exp s := by
        rw [show (1:ℝ) = Real.exp 0 by simp]
        exact Real.exp_lt_exp.mpr hs.1
      nlinarith
    · have h2 : Real.exp s < Real.exp L := Real.exp_lt_exp.mpr hs.2
      have h3 : Real.exp (-L) * Real.exp L = 1 := by
        rw [← Real.exp_add]
        simp
      nlinarith
  · rintro ⟨h0, h1⟩
    have hy : (0:ℝ) < y := lt_trans hr h0
    refine ⟨Real.log (y / Real.exp (-L)), ⟨?_, ?_⟩, ?_⟩
    · show (0:ℝ) < Real.log (y / Real.exp (-L))
      exact Real.log_pos ((one_lt_div hr).mpr h0)
    · show Real.log (y / Real.exp (-L)) < L
      have hlt : y / Real.exp (-L) < Real.exp L := by
        rw [div_lt_iff₀ hr, ← Real.exp_add]
        simpa using h1
      have hlog := Real.log_lt_log (div_pos hy hr) hlt
      rwa [Real.log_exp] at hlog
    · show Real.exp (-L) * Real.exp (Real.log (y / Real.exp (-L))) = y
      rw [Real.exp_log (div_pos hy hr)]
      field_simp

theorem image_oppositeChart :
    (fun v : ℝ => -Real.exp (-v)) '' Ioi (0:ℝ) = Ioo (-1) 0 := by
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv0 : (0:ℝ) < v := hv
    have h1 : Real.exp (-v) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    exact ⟨by linarith, by linarith [Real.exp_pos (-v)]⟩
  · rintro ⟨h0, h1⟩
    have hneg : (0:ℝ) < -y := by linarith
    refine ⟨-Real.log (-y), ?_, ?_⟩
    · show (0:ℝ) < -Real.log (-y)
      have hlog : Real.log (-y) < 0 := Real.log_neg hneg (by linarith)
      linarith
    · show -Real.exp (-(-Real.log (-y))) = y
      rw [neg_neg, Real.exp_log hneg]
      ring

/-! ## The chart identities -/

/-- **`(9)`: the near same-side window in the physical chart.** -/
theorem jumpNear_eq (u : ℝ → ℝ) (L : ℝ) :
    jumpNear u L
      = ∫ s in Ioi (0:ℝ), (seamRight u L - seamRight u (L + s)) / (Real.exp s - 1) := by
  have hderiv : ∀ s ∈ Ioi (0:ℝ),
      HasDerivWithinAt (fun t : ℝ => Real.exp (-L) * Real.exp (-t))
        (-(Real.exp (-L) * Real.exp (-s))) (Ioi (0:ℝ)) s := by
    intro s _
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-s)) s := by
      have h := (hasDerivAt_neg s).exp
      simpa using h
    have hval : Real.exp (-L) * -Real.exp (-s) = -(Real.exp (-L) * Real.exp (-s)) := by ring
    rw [← hval]
    exact (hexp.const_mul (Real.exp (-L))).hasDerivWithinAt
  have hinj : InjOn (fun s : ℝ => Real.exp (-L) * Real.exp (-s)) (Ioi (0:ℝ)) := by
    intro a _ b _ hab
    have hab' : Real.exp (-L) * Real.exp (-a) = Real.exp (-L) * Real.exp (-b) := hab
    have hcancel : Real.exp (-a) = Real.exp (-b) :=
      mul_left_cancel₀ (ne_of_gt (Real.exp_pos (-L))) hab'
    have hneg := Real.exp_injective hcancel
    linarith
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun y => (u (Real.exp (-L)) - u y) / (Real.exp (-L) - y))
  rw [image_nearChart] at h
  rw [jumpNear, h]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : (0:ℝ) < s := hs
  have hr : (0:ℝ) < Real.exp (-L) := Real.exp_pos _
  have hes : (0:ℝ) < Real.exp (-s) := Real.exp_pos _
  have hone : Real.exp (-s) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hprod : Real.exp (-L) * Real.exp (-s) = Real.exp (-(L + s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hnum : u (Real.exp (-L)) - u (Real.exp (-L) * Real.exp (-s))
      = seamRight u L - seamRight u (L + s) := by
    rw [seamRight, seamRight, hprod]
    ring
  have habs : |(-(Real.exp (-L) * Real.exp (-s)))| = Real.exp (-L) * Real.exp (-s) := by
    rw [abs_neg, abs_of_pos (by positivity)]
  have hespos : (0:ℝ) < Real.exp s := Real.exp_pos s
  have hexpne : Real.exp s - 1 ≠ 0 := by
    have : (1:ℝ) < Real.exp s := by
      rw [show (1:ℝ) = Real.exp 0 by simp]
      exact Real.exp_lt_exp.mpr hs0
    linarith
  have hrne : Real.exp (-L) ≠ 0 := ne_of_gt hr
  have hinv : Real.exp (-s) = (Real.exp s)⁻¹ := Real.exp_neg s
  show |(-(Real.exp (-L) * Real.exp (-s)))| •
      ((u (Real.exp (-L)) - u (Real.exp (-L) * Real.exp (-s)))
        / (Real.exp (-L) - Real.exp (-L) * Real.exp (-s)))
    = (seamRight u L - seamRight u (L + s)) / (Real.exp s - 1)
  rw [smul_eq_mul, habs, hnum, hinv]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  field_simp

/-- **`(10)`, unsplit: the far same-side window in the physical chart.** -/
theorem jumpFar_eq (u : ℝ → ℝ) (L : ℝ) :
    jumpFar u L
      = ∫ s in Ioo (0:ℝ) L,
          (seamRight u L - seamRight u (L - s)) * (Real.exp s / (Real.exp s - 1)) := by
  have hderiv : ∀ s ∈ Ioo (0:ℝ) L,
      HasDerivWithinAt (fun t : ℝ => Real.exp (-L) * Real.exp t)
        (Real.exp (-L) * Real.exp s) (Ioo (0:ℝ) L) s := by
    intro s _
    exact ((Real.hasDerivAt_exp s).const_mul (Real.exp (-L))).hasDerivWithinAt
  have hinj : InjOn (fun s : ℝ => Real.exp (-L) * Real.exp s) (Ioo (0:ℝ) L) := by
    intro a _ b _ hab
    have hab' : Real.exp (-L) * Real.exp a = Real.exp (-L) * Real.exp b := hab
    exact Real.exp_injective (mul_left_cancel₀ (ne_of_gt (Real.exp_pos (-L))) hab')
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun y => (u (Real.exp (-L)) - u y) / (y - Real.exp (-L)))
  rw [image_farChart] at h
  rw [jumpFar, h]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  have hs0 : (0:ℝ) < s := hs.1
  have hr : (0:ℝ) < Real.exp (-L) := Real.exp_pos _
  have hexpne : Real.exp s - 1 ≠ 0 := by
    have : (1:ℝ) < Real.exp s := by
      rw [show (1:ℝ) = Real.exp 0 by simp]
      exact Real.exp_lt_exp.mpr hs0
    linarith
  have hprod : Real.exp (-L) * Real.exp s = Real.exp (-(L - s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hnum : u (Real.exp (-L)) - u (Real.exp (-L) * Real.exp s)
      = seamRight u L - seamRight u (L - s) := by
    rw [seamRight, seamRight, hprod]
    ring
  have habs : |Real.exp (-L) * Real.exp s| = Real.exp (-L) * Real.exp s := by
    rw [abs_of_pos (by positivity)]
  show |Real.exp (-L) * Real.exp s| •
      ((u (Real.exp (-L)) - u (Real.exp (-L) * Real.exp s))
        / (Real.exp (-L) * Real.exp s - Real.exp (-L)))
    = (seamRight u L - seamRight u (L - s)) * (Real.exp s / (Real.exp s - 1))
  rw [smul_eq_mul, habs, hnum,
    show Real.exp (-L) * Real.exp s - Real.exp (-L)
      = Real.exp (-L) * (Real.exp s - 1) by ring]
  field_simp

/-- **`(12)`: the opposite window in the physical chart.** -/
theorem jumpOpposite_eq (u : ℝ → ℝ) (L : ℝ) :
    jumpOpposite u L
      = ∫ v in Ioi (0:ℝ), (seamRight u L - seamLeft u v) * carlemanCutoffFactor L v := by
  have hderiv : ∀ v ∈ Ioi (0:ℝ),
      HasDerivWithinAt (fun t : ℝ => -Real.exp (-t)) (Real.exp (-v)) (Ioi (0:ℝ)) v := by
    intro v _
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-v)) v := by
      have h := (hasDerivAt_neg v).exp
      simpa using h
    have hval : -(-Real.exp (-v)) = Real.exp (-v) := by ring
    rw [← hval]
    exact hexp.neg.hasDerivWithinAt
  have hinj : InjOn (fun v : ℝ => -Real.exp (-v)) (Ioi (0:ℝ)) := by
    intro a _ b _ hab
    have hab' : -Real.exp (-a) = -Real.exp (-b) := hab
    have hcancel : Real.exp (-a) = Real.exp (-b) := neg_injective hab'
    have hneg := Real.exp_injective hcancel
    linarith
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun y => (u (Real.exp (-L)) - u y) / (Real.exp (-L) - y))
  rw [image_oppositeChart] at h
  rw [jumpOpposite, h]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv0 : (0:ℝ) < v := hv
  have hr : (0:ℝ) < Real.exp (-L) := Real.exp_pos _
  have hev : (0:ℝ) < Real.exp (-v) := Real.exp_pos _
  have hnum : u (Real.exp (-L)) - u (-Real.exp (-v)) = seamRight u L - seamLeft u v := by
    rw [seamRight, seamLeft]
    ring
  have habs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos hev
  have hden : Real.exp (-L) - -Real.exp (-v) = Real.exp (-L) + Real.exp (-v) := by ring
  have hfactor : Real.exp (-v) / (Real.exp (-L) + Real.exp (-v)) = carlemanCutoffFactor L v := by
    rw [carlemanCutoffFactor, Real.exp_neg, Real.exp_neg, Real.exp_sub]
    have h1 : Real.exp L ≠ 0 := ne_of_gt (Real.exp_pos _)
    have h2 : Real.exp v ≠ 0 := ne_of_gt (Real.exp_pos _)
    field_simp
    ring
  show |Real.exp (-v)| •
      ((u (Real.exp (-L)) - u (-Real.exp (-v))) / (Real.exp (-L) - -Real.exp (-v)))
    = (seamRight u L - seamLeft u v) * carlemanCutoffFactor L v
  rw [smul_eq_mul, habs, hnum, hden, ← hfactor]
  ring

/-! ## Integrability of the cutoff factor -/

/-- The Carleman cutoff factor is integrable on the physical ray. -/
theorem integrableOn_carlemanCutoffFactor (L : ℝ) :
    IntegrableOn (carlemanCutoffFactor L) (Ioi (0:ℝ)) volume :=
  integrableOn_Ioi_deriv_of_nonneg
    (hasDerivAt_carlemanScalarPrimitive L 0).continuousAt.continuousWithinAt
    (fun v _ => hasDerivAt_carlemanScalarPrimitive L v)
    (fun v _ => (carlemanCutoffFactor_pos L v).le)
    (tendsto_carlemanScalarPrimitive L)

/-! ## The two splittings -/

/-- **`(10)`, split: the Volterra--Gamma form of the far same-side window.** -/
theorem jumpFar_split (u : ℝ → ℝ) {L : ℝ} (hL : 0 < L)
    (hgerm : IntegrableOn (seamRight u) (Ioo (0:ℝ) L) volume)
    (hdiff : IntegrableOn
      (fun s => (seamRight u L - seamRight u (L - s)) / (Real.exp s - 1))
      (Ioo (0:ℝ) L) volume) :
    jumpFar u L
      = L * seamRight u L - (∫ t in Ioo (0:ℝ) L, seamRight u t)
        + ∫ s in Ioo (0:ℝ) L, (seamRight u L - seamRight u (L - s)) / (Real.exp s - 1) := by
  have hrefl : (∫ s in Ioo (0:ℝ) L, seamRight u (L - s)) = ∫ t in Ioo (0:ℝ) L, seamRight u t := by
    have h1 : (∫ s in Ioo (0:ℝ) L, seamRight u (L - s))
        = ∫ s in (0:ℝ)..L, seamRight u (L - s) := by
      rw [intervalIntegral.integral_of_le hL.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have h2 : (∫ s in (0:ℝ)..L, seamRight u (L - s)) = ∫ t in (L - L)..(L - 0), seamRight u t :=
      intervalIntegral.integral_comp_sub_left (seamRight u) L
    have h3 : (∫ t in (L - L)..(L - 0), seamRight u t) = ∫ t in Ioo (0:ℝ) L, seamRight u t := by
      rw [show L - L = (0:ℝ) by ring, show L - 0 = L by ring,
        intervalIntegral.integral_of_le hL.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [h1, h2, h3]
  have hshift : IntegrableOn (fun s => seamRight u (L - s)) (Ioo (0:ℝ) L) volume := by
    have hpre : (fun s : ℝ => L - s) ⁻¹' (Ioo (0:ℝ) L) = Ioo (0:ℝ) L := by
      ext s
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
    have hmp := (Measure.measurePreserving_sub_left (volume : Measure ℝ) L).restrict_preimage
      (s := Ioo (0:ℝ) L) measurableSet_Ioo
    rw [hpre] at hmp
    exact (hmp.integrable_comp hgerm.aestronglyMeasurable).mpr hgerm
  have hconstInt : IntegrableOn (fun _ : ℝ => seamRight u L) (Ioo (0:ℝ) L) volume :=
    integrableOn_const (by simp [Real.volume_Ioo])
  have hsub : IntegrableOn (fun s => seamRight u L - seamRight u (L - s)) (Ioo (0:ℝ) L) volume :=
    hconstInt.sub hshift
  have hsplit : jumpFar u L
      = (∫ s in Ioo (0:ℝ) L, (seamRight u L - seamRight u (L - s)))
        + ∫ s in Ioo (0:ℝ) L, (seamRight u L - seamRight u (L - s)) / (Real.exp s - 1) := by
    rw [jumpFar_eq u L, ← integral_add hsub hdiff]
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    have hs0 : (0:ℝ) < s := hs.1
    have hexpne : Real.exp s - 1 ≠ 0 := by
      have : (1:ℝ) < Real.exp s := by
        rw [show (1:ℝ) = Real.exp 0 by simp]
        exact Real.exp_lt_exp.mpr hs0
      linarith
    show (seamRight u L - seamRight u (L - s)) * (Real.exp s / (Real.exp s - 1))
      = (seamRight u L - seamRight u (L - s))
        + (seamRight u L - seamRight u (L - s)) / (Real.exp s - 1)
    field_simp
    ring
  have hconst : (∫ s in Ioo (0:ℝ) L, (seamRight u L - seamRight u (L - s)))
      = L * seamRight u L - ∫ t in Ioo (0:ℝ) L, seamRight u t := by
    rw [integral_sub hconstInt hshift, hrefl, MeasureTheory.setIntegral_const,
      Real.volume_real_Ioo, smul_eq_mul, sub_zero, max_eq_left hL.le]
  rw [hsplit, hconst]

/-- **`(14)`: the opposite window is the scalar seam term minus the Carleman cross block.** -/
theorem jumpOpposite_split (u : ℝ → ℝ) (L : ℝ)
    (hcross : IntegrableOn (fun v => seamLeft u v * carlemanCutoffFactor L v)
      (Ioi (0:ℝ)) volume) :
    jumpOpposite u L = (L + seamScalar L) * seamRight u L - seamC (seamLeft u) L := by
  have hconst : IntegrableOn (fun v => seamRight u L * carlemanCutoffFactor L v)
      (Ioi (0:ℝ)) volume := (integrableOn_carlemanCutoffFactor L).const_mul _
  rw [jumpOpposite_eq u L]
  have hsplit : (∫ v in Ioi (0:ℝ), (seamRight u L - seamLeft u v) * carlemanCutoffFactor L v)
      = (∫ v in Ioi (0:ℝ), seamRight u L * carlemanCutoffFactor L v)
        - ∫ v in Ioi (0:ℝ), seamLeft u v * carlemanCutoffFactor L v := by
    rw [← integral_sub hconst hcross]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    show (seamRight u L - seamLeft u v) * carlemanCutoffFactor L v
      = seamRight u L * carlemanCutoffFactor L v - seamLeft u v * carlemanCutoffFactor L v
    ring
  rw [hsplit, MeasureTheory.integral_const_mul, integral_Ioi_carlemanCutoffFactor, seamC,
    seamScalar]
  ring

/-! ## The paired normal form -/

/-- **`(4+)`: the exact normal form at the right seam point.** -/
theorem logJumpRight_eq (u : ℝ → ℝ) {L : ℝ} (hL : 0 < L)
    (hgerm : IntegrableOn (seamRight u) (Ioo (0:ℝ) L) volume)
    (hdiff : IntegrableOn
      (fun s => (seamRight u L - seamRight u (L - s)) / (Real.exp s - 1))
      (Ioo (0:ℝ) L) volume)
    (hcross : IntegrableOn (fun v => seamLeft u v * carlemanCutoffFactor L v)
      (Ioi (0:ℝ)) volume) :
    logJumpRight u L
      = (2 * L + seamScalar L) * seamRight u L - (∫ t in Ioo (0:ℝ) L, seamRight u t)
        + seamR (seamRight u) L - seamC (seamLeft u) L := by
  rw [logJumpRight, jumpNear_eq, jumpFar_split u hL hgerm hdiff, jumpOpposite_split u L hcross,
    seamR]
  ring

/-- **`(4-)`: the exact normal form at the left seam point**, obtained from `(4+)` by reflecting
the window. -/
theorem logJumpLeft_eq (u : ℝ → ℝ) {L : ℝ} (hL : 0 < L)
    (hgerm : IntegrableOn (seamLeft u) (Ioo (0:ℝ) L) volume)
    (hdiff : IntegrableOn
      (fun s => (seamLeft u L - seamLeft u (L - s)) / (Real.exp s - 1))
      (Ioo (0:ℝ) L) volume)
    (hcross : IntegrableOn (fun v => seamRight u v * carlemanCutoffFactor L v)
      (Ioi (0:ℝ)) volume) :
    logJumpLeft u L
      = (2 * L + seamScalar L) * seamLeft u L - (∫ t in Ioo (0:ℝ) L, seamLeft u t)
        + seamR (seamLeft u) L - seamC (seamRight u) L := by
  have hgerm' : IntegrableOn (seamRight fun x => u (-x)) (Ioo (0:ℝ) L) volume := by
    have : (seamRight fun x => u (-x)) = seamLeft u := by
      funext t
      exact seamRight_comp_neg u t
    rwa [this]
  have hdiff' : IntegrableOn
      (fun s => (seamRight (fun x => u (-x)) L - seamRight (fun x => u (-x)) (L - s))
        / (Real.exp s - 1)) (Ioo (0:ℝ) L) volume := by
    have : (fun s => (seamRight (fun x => u (-x)) L - seamRight (fun x => u (-x)) (L - s))
        / (Real.exp s - 1))
        = fun s => (seamLeft u L - seamLeft u (L - s)) / (Real.exp s - 1) := by
      funext s
      rw [seamRight_comp_neg, seamRight_comp_neg]
    rwa [this]
  have hcross' : IntegrableOn
      (fun v => seamLeft (fun x => u (-x)) v * carlemanCutoffFactor L v) (Ioi (0:ℝ)) volume := by
    have : (fun v => seamLeft (fun x => u (-x)) v * carlemanCutoffFactor L v)
        = fun v => seamRight u v * carlemanCutoffFactor L v := by
      funext v
      rw [seamLeft_comp_neg]
    rwa [this]
  have h := logJumpRight_eq (fun x => u (-x)) hL hgerm' hdiff' hcross'
  rw [logJumpLeft, h]
  have h1 : (seamRight fun x => u (-x)) = seamLeft u := by
    funext t
    exact seamRight_comp_neg u t
  have h2 : (seamLeft fun x => u (-x)) = seamRight u := by
    funext t
    exact seamLeft_comp_neg u t
  rw [h1, h2]

/-- **`(8)`: at a physical endpoint the opposite orientation is the zero exterior**, so the
paired normal form loses its cross block and nothing arbitrary remains. -/
theorem logJumpRight_eq_of_zero_exterior (u : ℝ → ℝ) {L : ℝ} (hL : 0 < L)
    (hzero : ∀ x : ℝ, x ≤ 0 → u x = 0)
    (hgerm : IntegrableOn (seamRight u) (Ioo (0:ℝ) L) volume)
    (hdiff : IntegrableOn
      (fun s => (seamRight u L - seamRight u (L - s)) / (Real.exp s - 1))
      (Ioo (0:ℝ) L) volume) :
    logJumpRight u L
      = (2 * L + seamScalar L) * seamRight u L - (∫ t in Ioo (0:ℝ) L, seamRight u t)
        + seamR (seamRight u) L := by
  have hleft : seamLeft u = fun _ => (0:ℝ) := by
    funext v
    rw [seamLeft, hzero _ (by linarith [Real.exp_pos (-v)]), hzero 0 le_rfl, sub_zero]
  have hcross : IntegrableOn (fun v => seamLeft u v * carlemanCutoffFactor L v)
      (Ioi (0:ℝ)) volume := by
    rw [hleft]
    simp
  have h := logJumpRight_eq u hL hgerm hdiff hcross
  rw [h, seamC, hleft]
  simp

/-! ## The differentiated cross block -/

/-- **`(6)`: the `L`-derivative of the Carleman cross block is the logistic coupling.**  The
profile is bounded, so the logistic majorant dominates the differentiated integrand uniformly on
a ball, and differentiation under the integral sign applies. -/
theorem hasDerivAt_seamC {F : ℝ → ℝ} (hFm : Measurable F) {C : ℝ} (hFb : ∀ v, |F v| ≤ C)
    (L : ℝ) :
    HasDerivAt (seamC F) (∫ v in Ioi (0:ℝ), F v * logisticKernel (v - L)) L := by
  have hC : 0 ≤ C := le_trans (abs_nonneg (F 0)) (hFb 0)
  set μ : Measure ℝ := volume.restrict (Ioi (0:ℝ)) with hμ
  set G : ℝ → ℝ → ℝ := fun M v => F v * carlemanCutoffFactor M v with hG
  set G' : ℝ → ℝ → ℝ := fun M v => F v * logisticKernel (v - M) with hG'
  have hballmem : Metric.ball L 1 ∈ 𝓝 L := Metric.ball_mem_nhds L one_pos
  have hmeasG : ∀ M : ℝ, AEStronglyMeasurable (G M) μ := by
    intro M
    refine Measurable.aestronglyMeasurable ?_
    have : Measurable fun v : ℝ => carlemanCutoffFactor M v := by
      have : Measurable fun v : ℝ => (1 + Real.exp (v - M))⁻¹ := by fun_prop
      simpa [carlemanCutoffFactor] using this
    exact hFm.mul this
  have hmeasG' : ∀ M : ℝ, AEStronglyMeasurable (G' M) μ := by
    intro M
    refine Measurable.aestronglyMeasurable ?_
    exact hFm.mul (continuous_logisticKernel.measurable.comp (measurable_id.sub_const M))
  have hint : Integrable (G L) μ := by
    refine Integrable.mono' ((integrableOn_carlemanCutoffFactor L).const_mul C)
      (hmeasG L) (Filter.Eventually.of_forall fun v => ?_)
    have h1 : |F v * carlemanCutoffFactor L v| = |F v| * carlemanCutoffFactor L v := by
      rw [abs_mul, abs_of_pos (carlemanCutoffFactor_pos L v)]
    rw [Real.norm_eq_abs, h1]
    exact mul_le_mul_of_nonneg_right (hFb v) (carlemanCutoffFactor_pos L v).le
  set bound : ℝ → ℝ := fun v => C * (Real.exp 1 * Real.exp (-|v - L|)) with hbound
  have hboundint : Integrable bound μ := by
    have hbase : Integrable (fun v : ℝ => Real.exp (-(1:ℝ) * |v - L|)) volume := by
      have h := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 (r := (1:ℝ)) one_pos
      have h1 : Integrable (fun v : ℝ => Real.exp (-(1:ℝ) * |v|)) volume := by
        simpa using h
      have := h1.comp_sub_right L
      simpa using this
    have : Integrable (fun v : ℝ => C * (Real.exp 1 * Real.exp (-|v - L|))) volume := by
      have hcongr : (fun v : ℝ => Real.exp (-(1:ℝ) * |v - L|))
          = fun v : ℝ => Real.exp (-|v - L|) := by
        funext v
        congr 1
        ring
      rw [hcongr] at hbase
      exact (hbase.const_mul (Real.exp 1)).const_mul C
    exact this.restrict
  have hderivbound : ∀ᵐ v ∂μ, ∀ M ∈ Metric.ball L 1, ‖G' M v‖ ≤ bound v := by
    refine Filter.Eventually.of_forall fun v => ?_
    intro M hM
    have hMdist : |M - L| < 1 := by
      have := Metric.mem_ball.mp hM
      rwa [Real.dist_eq] at this
    have hk : logisticKernel (v - M) ≤ Real.exp (-|v - M|) :=
      logisticKernel_le_exp_neg_abs (v - M)
    have htri : |v - L| - |M - L| ≤ |v - M| := by
      have : |v - L| ≤ |v - M| + |M - L| := by
        have := abs_add_le (v - M) (M - L)
        simpa using this
      linarith
    have hexp : Real.exp (-|v - M|) ≤ Real.exp 1 * Real.exp (-|v - L|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    have habs : ‖G' M v‖ = |F v| * logisticKernel (v - M) := by
      rw [hG']
      show ‖F v * logisticKernel (v - M)‖ = |F v| * logisticKernel (v - M)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (logisticKernel_pos _)]
    rw [habs, hbound]
    calc |F v| * logisticKernel (v - M)
        ≤ C * (Real.exp 1 * Real.exp (-|v - L|)) := by
          apply mul_le_mul (hFb v) (le_trans hk hexp) (logisticKernel_pos _).le hC
      _ = C * (Real.exp 1 * Real.exp (-|v - L|)) := rfl
  have hdiff : ∀ᵐ v ∂μ, ∀ M ∈ Metric.ball L 1, HasDerivAt (fun M => G M v) (G' M v) M := by
    refine Filter.Eventually.of_forall fun v => ?_
    intro M _
    exact (hasDerivAt_carlemanCutoffFactor_left v M).const_mul (F v)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := G) (F' := G') (x₀ := L)
    (bound := bound) (μ := μ) hballmem
    (Filter.Eventually.of_forall fun M => hmeasG M) hint (hmeasG' L) hderivbound hboundint hdiff
  exact h.2

/-! ## The differentiated paired system -/

theorem hasDerivAt_seamScalar (L : ℝ) :
    HasDerivAt seamScalar (-(Real.exp (-L) / (1 + Real.exp (-L)))) L := by
  have hpos : (0:ℝ) < 1 + Real.exp (-L) := by
    have := Real.exp_pos (-L)
    linarith
  have hexp : HasDerivAt (fun M : ℝ => Real.exp (-M)) (-Real.exp (-L)) L := by
    have h := (hasDerivAt_neg L).exp
    simpa using h
  have hbase : HasDerivAt (fun M : ℝ => 1 + Real.exp (-M)) (-Real.exp (-L)) L := by
    simpa using hexp.const_add (1:ℝ)
  have hlog := hbase.log (ne_of_gt hpos)
  have hfun : seamScalar = fun M : ℝ => Real.log (1 + Real.exp (-M)) := by
    funext M
    rw [seamScalar]
  rw [hfun]
  have hval : -Real.exp (-L) / (1 + Real.exp (-L))
      = -(Real.exp (-L) / (1 + Real.exp (-L))) := by ring
  rw [← hval]
  exact hlog

/-- The running Volterra primitive of a seam germ. -/
theorem hasDerivAt_seamPrimitive {F : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hint : IntervalIntegrable F volume 0 L) (hmeas : StronglyMeasurableAtFilter F (𝓝 L))
    (hcont : ContinuousAt F L) :
    HasDerivAt (fun M => ∫ t in Ioo (0:ℝ) M, F t) (F L) L := by
  have hbase : HasDerivAt (fun M => ∫ t in (0:ℝ)..M, F t) (F L) L :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds hL] with M hM
  rw [intervalIntegral.integral_of_le hM.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- The right-hand side of the paired normal form, as a function of the cutoff scale. -/
def normalFormRight (Fp Fm : ℝ → ℝ) (L : ℝ) : ℝ :=
  (2 * L + seamScalar L) * Fp L - (∫ t in Ioo (0:ℝ) L, Fp t) + seamR Fp L - seamC Fm L

/-- **`(19+)`: the differentiated paired normal equation.**  The diagonal contributes
`[2L+q]F' + [1+q']F`, the same-side block contributes `(R F)'`, and the cross block contributes
exactly the logistic coupling `-K F₋`. -/
theorem hasDerivAt_normalFormRight {Fp Fm : ℝ → ℝ} {c r C : ℝ} {L : ℝ} (hL : 0 < L)
    (hFp : HasDerivAt Fp c L) (hint : IntervalIntegrable Fp volume 0 L)
    (hmeas : StronglyMeasurableAtFilter Fp (𝓝 L)) (hR : HasDerivAt (seamR Fp) r L)
    (hFmm : Measurable Fm) (hFmb : ∀ v, |Fm v| ≤ C) :
    HasDerivAt (normalFormRight Fp Fm)
      ((2 * L + seamScalar L) * c + (1 - Real.exp (-L) / (1 + Real.exp (-L))) * Fp L + r
        - ∫ v in Ioi (0:ℝ), Fm v * logisticKernel (v - L)) L := by
  have hq := hasDerivAt_seamScalar L
  have hlin : HasDerivAt (fun M : ℝ => 2 * M + seamScalar M)
      (2 + -(Real.exp (-L) / (1 + Real.exp (-L)))) L := by
    have h2 : HasDerivAt (fun M : ℝ => 2 * M) 2 L := by
      simpa using (hasDerivAt_id' L).const_mul (2:ℝ)
    exact h2.add hq
  have hprod := hlin.mul hFp
  have hprim := hasDerivAt_seamPrimitive hL hint hmeas hFp.continuousAt
  have hC := hasDerivAt_seamC hFmm hFmb L
  have hsum := ((hprod.sub hprim).add hR).sub hC
  have hval : (2 + -(Real.exp (-L) / (1 + Real.exp (-L)))) * Fp L + (2 * L + seamScalar L) * c
        - Fp L + r - ∫ v in Ioi (0:ℝ), Fm v * logisticKernel (v - L)
      = (2 * L + seamScalar L) * c + (1 - Real.exp (-L) / (1 + Real.exp (-L))) * Fp L + r
        - ∫ v in Ioi (0:ℝ), Fm v * logisticKernel (v - L) := by ring
  have hfun : normalFormRight Fp Fm
      = fun M => (2 * M + seamScalar M) * Fp M - (∫ t in Ioo (0:ℝ) M, Fp t)
        + seamR Fp M - seamC Fm M := by
    funext M
    rw [normalFormRight]
  rw [hfun, ← hval]
  exact hsum

end

end RHTower

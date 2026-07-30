/-
Ramification of the incidence carrier on the critical line: seam critical points are the
emission ports.

For a pencil of carriers real on the line, the incidence carrier `ι = −Λ₂/Λ₁` restricts to
a real-analytic function of the height parameter on the seam.  Its critical points are the
ports: a height `τ₀` is a critical point of the real seam restriction exactly when the
holomorphic derivative of `ι` vanishes at `linePt τ₀`, which is exactly when the on-line
pencil member whose ratio is the incidence value there has a zero of order at least two at
`linePt τ₀` — a multiple on-line zero, the emission-port class of the seam ledger.

The mechanism is the same rotation the seam ledger uses: the line's tangent is `i`, so the
real seam derivative is `i · ι'(linePt τ₀)`, and reality forces it to be real; it vanishes
exactly when `ι'` does.  The member factors as `Λ₁·(r − ι)` through the anchor, so its
double-zero locus is the critical locus of `ι` at the fiber value `r`.
-/
import GaloisForLFunctions.RHTower.IncidenceCarrier
import Mathlib.Analysis.Analytic.Order

namespace RHTower

open Complex Metric

/-- The seam restriction of the incidence carrier: its real value along the critical
line as a function of height. -/
noncomputable def seamIncidence (Λ₁ Λ₂ : ℂ → ℂ) (τ : ℝ) : ℝ :=
  (incidence Λ₁ Λ₂ (linePt τ)).re

/-- **The seam incidence is real-analytic.**  Where the anchor `Λ₁` does not vanish, the
incidence carrier is holomorphic; composed with the real-analytic line map and projected to
the real axis it is a real-analytic function of height. -/
theorem seamIncidence_analyticAt {Λ₁ Λ₂ : ℂ → ℂ} {τ₀ : ℝ}
    (h1 : AnalyticAt ℂ Λ₁ (linePt τ₀)) (h2 : AnalyticAt ℂ Λ₂ (linePt τ₀))
    (h0 : Λ₁ (linePt τ₀) ≠ 0) :
    AnalyticAt ℝ (seamIncidence Λ₁ Λ₂) τ₀ := by
  have hlp : AnalyticAt ℝ linePt τ₀ := by
    unfold linePt
    exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt τ₀).mul analyticAt_const)
  have hiota : AnalyticAt ℂ (incidence Λ₁ Λ₂) (linePt τ₀) := by
    unfold incidence
    exact h2.neg.div h1 h0
  have hcomp : AnalyticAt ℝ (fun τ : ℝ => incidence Λ₁ Λ₂ (linePt τ)) τ₀ :=
    hiota.restrictScalars.comp hlp
  exact (Complex.reCLM.analyticAt _).comp hcomp

/-- The incidence carrier's holomorphic derivative along the line, in terms of the two
carrier derivatives. -/
private noncomputable def iotaDeriv (Λ₁ Λ₂ : ℂ → ℂ) (d₁ d₂ : ℂ) (z₀ : ℂ) : ℂ :=
  (-d₂ * Λ₁ z₀ - -Λ₂ z₀ * d₁) / Λ₁ z₀ ^ 2

private theorem hasDerivAt_incidence {Λ₁ Λ₂ : ℂ → ℂ} {d₁ d₂ : ℂ} {z₀ : ℂ}
    (hd₁ : HasDerivAt Λ₁ d₁ z₀) (hd₂ : HasDerivAt Λ₂ d₂ z₀) (h0 : Λ₁ z₀ ≠ 0) :
    HasDerivAt (incidence Λ₁ Λ₂) (iotaDeriv Λ₁ Λ₂ d₁ d₂ z₀) z₀ := by
  unfold incidence iotaDeriv
  exact hd₂.neg.div hd₁ h0

/-- The pencil member with ratio `r` has holomorphic derivative `r·d₁ + d₂`. -/
private theorem hasDerivAt_pencil {Λ₁ Λ₂ : ℂ → ℂ} {d₁ d₂ : ℂ} {z₀ : ℂ} (r : ℂ)
    (hd₁ : HasDerivAt Λ₁ d₁ z₀) (hd₂ : HasDerivAt Λ₂ d₂ z₀) :
    HasDerivAt (pencil Λ₁ Λ₂ r 1) (r * d₁ + 1 * d₂) z₀ := by
  unfold pencil
  exact (hd₁.const_mul r).add (hd₂.const_mul 1)

/-- **The member derivative is the anchor times the incidence derivative.**  At the fiber
value `r = ι(z₀)`, the on-line member `Λ₁·(r − ι)` has derivative `−Λ₁(z₀)·ι'(z₀)`, so its
critical points at the fiber are exactly the critical points of `ι`. -/
private theorem pencil_deriv_eq_neg_anchor_mul_iotaDeriv {Λ₁ Λ₂ : ℂ → ℂ} {d₁ d₂ z₀ r : ℂ}
    (h0 : Λ₁ z₀ ≠ 0) (hratio : Λ₂ z₀ = -r * Λ₁ z₀) :
    r * d₁ + 1 * d₂ = -Λ₁ z₀ * iotaDeriv Λ₁ Λ₂ d₁ d₂ z₀ := by
  unfold iotaDeriv
  rw [hratio]
  field_simp
  ring

/-- The incidence value at a nonvanishing-anchor point pins the member ratio: `ι(z₀) = r`
iff `Λ₂ z₀ = −r·Λ₁ z₀`. -/
private theorem incidence_eq_iff_ratio {Λ₁ Λ₂ : ℂ → ℂ} {z₀ r : ℂ} (h0 : Λ₁ z₀ ≠ 0) :
    incidence Λ₁ Λ₂ z₀ = r ↔ Λ₂ z₀ = -r * Λ₁ z₀ := by
  unfold incidence
  rw [div_eq_iff h0]
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-- **The seam derivative rotates the incidence derivative.**  On the line the real seam
restriction has derivative `Re(i·ι'(linePt τ₀))`; reality of the incidence values forces
`i·ι'` to be real, so the seam derivative vanishes exactly when `ι'` does. -/
theorem seam_deriv_eq_zero_iff_incidence_deriv_zero {Λ₁ Λ₂ : ℂ → ℂ} {d₁ d₂ : ℂ} {τ₀ : ℝ}
    (hd₁ : HasDerivAt Λ₁ d₁ (linePt τ₀)) (hd₂ : HasDerivAt Λ₂ d₂ (linePt τ₀))
    (h0 : Λ₁ (linePt τ₀) ≠ 0)
    (hr1 : ∀ τ, (Λ₁ (linePt τ)).im = 0) (hr2 : ∀ τ, (Λ₂ (linePt τ)).im = 0) :
    deriv (seamIncidence Λ₁ Λ₂) τ₀ = 0 ↔ iotaDeriv Λ₁ Λ₂ d₁ d₂ (linePt τ₀) = 0 := by
  -- the complex seam curve and its derivative
  have hfc : HasDerivAt (fun τ : ℝ => incidence Λ₁ Λ₂ (linePt τ))
      (iotaDeriv Λ₁ Λ₂ d₁ d₂ (linePt τ₀) * I) τ₀ :=
    HasDerivAt.comp τ₀ (hasDerivAt_incidence hd₁ hd₂ h0) (hasDerivAt_linePt τ₀)
  -- reality of the incidence values on the line
  have hreal : ∀ τ, (incidence Λ₁ Λ₂ (linePt τ)).im = 0 := fun τ =>
    incidence_im_eq_zero_on_line (hr1 τ) (hr2 τ)
  -- the complex seam derivative is real
  have hderiv_im : (iotaDeriv Λ₁ Λ₂ d₁ d₂ (linePt τ₀) * I).im = 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => (incidence Λ₁ Λ₂ (linePt τ)).im)
        (iotaDeriv Λ₁ Λ₂ d₁ d₂ (linePt τ₀) * I).im τ₀ := by
      have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt τ₀ hfc
      simpa using! this
    have h2 : HasDerivAt (fun τ : ℝ => (incidence Λ₁ Λ₂ (linePt τ)).im) 0 τ₀ := by
      have he : (fun τ : ℝ => (incidence Λ₁ Λ₂ (linePt τ)).im) = fun _ => (0 : ℝ) := by
        funext τ; exact hreal τ
      rw [he]; exact hasDerivAt_const _ _
    exact h1.unique h2
  -- the real seam function's derivative is the real part
  have hseam : HasDerivAt (seamIncidence Λ₁ Λ₂)
      (iotaDeriv Λ₁ Λ₂ d₁ d₂ (linePt τ₀) * I).re τ₀ := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ₀ hfc
    simpa [seamIncidence] using! this
  rw [hseam.deriv]
  constructor
  · intro h
    have hzero : iotaDeriv Λ₁ Λ₂ d₁ d₂ (linePt τ₀) * I = 0 := Complex.ext h hderiv_im
    have : iotaDeriv Λ₁ Λ₂ d₁ d₂ (linePt τ₀) * I * (-I) = 0 := by rw [hzero]; ring
    simpa [mul_assoc, Complex.I_mul_I] using this
  · intro h
    rw [h]; simp

/-- **The port criterion.**  The on-line pencil member whose ratio is the incidence value at
`linePt τ₀` has a zero of order at least two there — a multiple on-line zero — exactly when
the incidence derivative vanishes.  Both are the ramification of `ι` at the fiber. -/
theorem member_order_ge_two_iff_incidence_deriv_zero {Λ₁ Λ₂ : ℂ → ℂ} {d₁ d₂ : ℂ} {τ₀ : ℝ}
    (ha1 : AnalyticAt ℂ Λ₁ (linePt τ₀)) (ha2 : AnalyticAt ℂ Λ₂ (linePt τ₀))
    (hd₁ : HasDerivAt Λ₁ d₁ (linePt τ₀)) (hd₂ : HasDerivAt Λ₂ d₂ (linePt τ₀))
    (h0 : Λ₁ (linePt τ₀) ≠ 0) :
    (2 : ℕ∞) ≤ analyticOrderAt
        (pencil Λ₁ Λ₂ (incidence Λ₁ Λ₂ (linePt τ₀)) 1) (linePt τ₀) ↔
      iotaDeriv Λ₁ Λ₂ d₁ d₂ (linePt τ₀) = 0 := by
  set z₀ := linePt τ₀ with hz₀
  set r := incidence Λ₁ Λ₂ z₀ with hr
  have hratio : Λ₂ z₀ = -r * Λ₁ z₀ := (incidence_eq_iff_ratio h0).mp rfl
  -- the member is analytic
  have hpan : AnalyticAt ℂ (pencil Λ₁ Λ₂ r 1) z₀ := by
    unfold pencil
    exact (analyticAt_const.mul ha1).add (analyticAt_const.mul ha2)
  -- value of the member at z₀ is zero
  have hval : pencil Λ₁ Λ₂ r 1 z₀ = 0 := by
    unfold pencil
    rw [hratio]; ring
  -- derivative of the member
  have hpder : HasDerivAt (pencil Λ₁ Λ₂ r 1) (r * d₁ + 1 * d₂) z₀ :=
    hasDerivAt_pencil r hd₁ hd₂
  have hderiv_eq : deriv (pencil Λ₁ Λ₂ r 1) z₀ = r * d₁ + 1 * d₂ := hpder.deriv
  -- order ≥ 2 ↔ value 0 ∧ deriv 0
  have hord : (2 : ℕ∞) ≤ analyticOrderAt (pencil Λ₁ Λ₂ r 1) z₀ ↔
      pencil Λ₁ Λ₂ r 1 z₀ = 0 ∧ deriv (pencil Λ₁ Λ₂ r 1) z₀ = 0 := by
    rw [show (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) from rfl,
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hpan]
    constructor
    · intro h
      exact ⟨by have := h 0 (by norm_num); simpa [iteratedDeriv_zero] using this,
        by have := h 1 (by norm_num); simpa [iteratedDeriv_one] using this⟩
    · rintro ⟨hv, hd⟩ i hi
      interval_cases i
      · simpa [iteratedDeriv_zero] using hv
      · simpa [iteratedDeriv_one] using hd
  have hpdeq : r * d₁ + 1 * d₂ = -Λ₁ z₀ * iotaDeriv Λ₁ Λ₂ d₁ d₂ z₀ :=
    pencil_deriv_eq_neg_anchor_mul_iotaDeriv h0 hratio
  rw [hord, hderiv_eq, hval]
  simp only [true_and]
  rw [hpdeq]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (by simpa using h0)
  · intro h
    rw [h, mul_zero]

/-- **Ports are the seam critical points.**  For a pencil of carriers real on the line with
nonvanishing anchor, a height is a critical point of the real seam restriction of the
incidence carrier exactly when the on-line member through it has a multiple zero — the
emission-port class of the seam ledger.  The transversal event structure degenerates
precisely where the incidence carrier ramifies. -/
theorem seam_critical_iff_port {Λ₁ Λ₂ : ℂ → ℂ} {d₁ d₂ : ℂ} {τ₀ : ℝ}
    (ha1 : AnalyticAt ℂ Λ₁ (linePt τ₀)) (ha2 : AnalyticAt ℂ Λ₂ (linePt τ₀))
    (hd₁ : HasDerivAt Λ₁ d₁ (linePt τ₀)) (hd₂ : HasDerivAt Λ₂ d₂ (linePt τ₀))
    (h0 : Λ₁ (linePt τ₀) ≠ 0)
    (hr1 : ∀ τ, (Λ₁ (linePt τ)).im = 0) (hr2 : ∀ τ, (Λ₂ (linePt τ)).im = 0) :
    deriv (seamIncidence Λ₁ Λ₂) τ₀ = 0 ↔
      (2 : ℕ∞) ≤ analyticOrderAt
        (pencil Λ₁ Λ₂ (incidence Λ₁ Λ₂ (linePt τ₀)) 1) (linePt τ₀) := by
  rw [seam_deriv_eq_zero_iff_incidence_deriv_zero hd₁ hd₂ h0 hr1 hr2,
    member_order_ge_two_iff_incidence_deriv_zero ha1 ha2 hd₁ hd₂ h0]

end RHTower

namespace RHTower

open Complex Metric

/-- **The simple-port criterion.**  The on-line member whose ratio is the incidence value has
a zero of order exactly two — a simple, nondegenerate multiple zero — precisely when the
incidence derivative vanishes while the member's second derivative does not.  Order exactly two
is the generic port: two event branches merge transversally, the two-coloring degenerating with
a nonvanishing Hessian. -/
theorem member_order_eq_two_iff_incidence_deriv_zero {Λ₁ Λ₂ : ℂ → ℂ} {d₁ d₂ : ℂ} {τ₀ : ℝ}
    (ha1 : AnalyticAt ℂ Λ₁ (linePt τ₀)) (ha2 : AnalyticAt ℂ Λ₂ (linePt τ₀))
    (hd₁ : HasDerivAt Λ₁ d₁ (linePt τ₀)) (hd₂ : HasDerivAt Λ₂ d₂ (linePt τ₀))
    (h0 : Λ₁ (linePt τ₀) ≠ 0) :
    analyticOrderAt (pencil Λ₁ Λ₂ (incidence Λ₁ Λ₂ (linePt τ₀)) 1) (linePt τ₀) = 2 ↔
      iotaDeriv Λ₁ Λ₂ d₁ d₂ (linePt τ₀) = 0 ∧
        iteratedDeriv 2 (pencil Λ₁ Λ₂ (incidence Λ₁ Λ₂ (linePt τ₀)) 1) (linePt τ₀) ≠ 0 := by
  set z₀ := linePt τ₀ with hz₀
  set r := incidence Λ₁ Λ₂ z₀ with hr
  have hratio : Λ₂ z₀ = -r * Λ₁ z₀ := (incidence_eq_iff_ratio h0).mp rfl
  have hpan : AnalyticAt ℂ (pencil Λ₁ Λ₂ r 1) z₀ := by
    unfold pencil
    exact (analyticAt_const.mul ha1).add (analyticAt_const.mul ha2)
  have hval : pencil Λ₁ Λ₂ r 1 z₀ = 0 := by
    unfold pencil; rw [hratio]; ring
  have hpder : HasDerivAt (pencil Λ₁ Λ₂ r 1) (r * d₁ + 1 * d₂) z₀ :=
    hasDerivAt_pencil r hd₁ hd₂
  have hderiv_eq : deriv (pencil Λ₁ Λ₂ r 1) z₀ = r * d₁ + 1 * d₂ := hpder.deriv
  have hpdeq : r * d₁ + 1 * d₂ = -Λ₁ z₀ * iotaDeriv Λ₁ Λ₂ d₁ d₂ z₀ :=
    pencil_deriv_eq_neg_anchor_mul_iotaDeriv h0 hratio
  have hge2 : (2 : ℕ∞) ≤ analyticOrderAt (pencil Λ₁ Λ₂ r 1) z₀ ↔
      iotaDeriv Λ₁ Λ₂ d₁ d₂ z₀ = 0 :=
    member_order_ge_two_iff_incidence_deriv_zero ha1 ha2 hd₁ hd₂ h0
  have hge3 : (3 : ℕ∞) ≤ analyticOrderAt (pencil Λ₁ Λ₂ r 1) z₀ ↔
      iotaDeriv Λ₁ Λ₂ d₁ d₂ z₀ = 0 ∧
        iteratedDeriv 2 (pencil Λ₁ Λ₂ r 1) z₀ = 0 := by
    rw [show (3 : ℕ∞) = ((3 : ℕ) : ℕ∞) from rfl,
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hpan]
    constructor
    · intro h
      refine ⟨?_, by simpa using h 2 (by norm_num)⟩
      have hd := h 1 (by norm_num)
      rw [iteratedDeriv_one, hderiv_eq, hpdeq] at hd
      exact (mul_eq_zero.mp hd).resolve_left (by simpa using h0)
    · rintro ⟨hι, hd2⟩ i hi
      interval_cases i
      · simpa [iteratedDeriv_zero] using hval
      · rw [iteratedDeriv_one, hderiv_eq, hpdeq, hι, mul_zero]
      · simpa using hd2
  have hsplit : analyticOrderAt (pencil Λ₁ Λ₂ r 1) z₀ = 2 ↔
      2 ≤ analyticOrderAt (pencil Λ₁ Λ₂ r 1) z₀ ∧
        ¬ 3 ≤ analyticOrderAt (pencil Λ₁ Λ₂ r 1) z₀ := by
    constructor
    · rintro h; rw [h]; exact ⟨le_refl 2, by decide⟩
    · rintro ⟨h1, h2⟩
      exact le_antisymm (Order.le_of_lt_succ (not_le.mp h2)) h1
  rw [hsplit, hge2, hge3]
  constructor
  · rintro ⟨hι, hn3⟩
    exact ⟨hι, fun hd2 => hn3 ⟨hι, hd2⟩⟩
  · rintro ⟨hι, hd2⟩
    exact ⟨hι, fun h => hd2 h.2⟩

/-- **Simple ports are the simple seam critical points.**  A height is a critical point of the
real seam restriction with the member's on-line Hessian nonvanishing exactly when the on-line
member through it has a zero of order exactly two: the generic, nondegenerate emission port. -/
theorem seam_simple_port_iff {Λ₁ Λ₂ : ℂ → ℂ} {d₁ d₂ : ℂ} {τ₀ : ℝ}
    (ha1 : AnalyticAt ℂ Λ₁ (linePt τ₀)) (ha2 : AnalyticAt ℂ Λ₂ (linePt τ₀))
    (hd₁ : HasDerivAt Λ₁ d₁ (linePt τ₀)) (hd₂ : HasDerivAt Λ₂ d₂ (linePt τ₀))
    (h0 : Λ₁ (linePt τ₀) ≠ 0)
    (hr1 : ∀ τ, (Λ₁ (linePt τ)).im = 0) (hr2 : ∀ τ, (Λ₂ (linePt τ)).im = 0) :
    (deriv (seamIncidence Λ₁ Λ₂) τ₀ = 0 ∧
        iteratedDeriv 2 (pencil Λ₁ Λ₂ (incidence Λ₁ Λ₂ (linePt τ₀)) 1) (linePt τ₀) ≠ 0) ↔
      analyticOrderAt (pencil Λ₁ Λ₂ (incidence Λ₁ Λ₂ (linePt τ₀)) 1) (linePt τ₀) = 2 := by
  rw [seam_deriv_eq_zero_iff_incidence_deriv_zero hd₁ hd₂ h0 hr1 hr2,
    member_order_eq_two_iff_incidence_deriv_zero ha1 ha2 hd₁ hd₂ h0]

end RHTower

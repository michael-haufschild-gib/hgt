import GaloisForLFunctions.BiScaleUncertainty.HyperbolicShiftCommutatorAndParityIntertwining
import GaloisForLFunctions.BiScaleUncertainty.DisjointCollarCliqueDivergenceAndTuransProblem

/-!
# $\mathrm{SO}^+(1,1)$ Lorentz Boost Representation, Minkowski Light-Cone Geometry & Exact Krein Defect Calculus

This module establishes the Lie-group and quadratic-form foundations of the hyperbolic multiplier
calculus (`coshMultiplier` and `sinhMultiplier`) together with the exact $L^2$ defect identities for
the Krein chord and doubling inequalities.

## Main Results

1. **The $\mathrm{SO}^+(1, 1)$ Lorentz Boost Representation (§1):**
   - For every boost rapidity $\alpha \in \mathbb{R}$, the multiplier pair
     $(C_\alpha f)(u) = \cosh(\alpha u) f(u)$ and $(S_\alpha f)(u) = \sinh(\alpha u) f(u)$
     forms a representation of the orthochronous Lorentz group $\mathrm{SO}^+(1, 1)$:
     $$C_{\alpha + \beta} f = C_\alpha (C_\beta f) + S_\alpha (S_\beta f), \qquad
       S_{\alpha + \beta} f = C_\alpha (S_\beta f) + S_\alpha (C_\beta f),$$
     with Lorentz metric identity $C_\alpha (C_\alpha f) - S_\alpha (S_\alpha f) = f$ and exact
     inverse boost $\alpha \mapsto -\alpha$.

2. **Non-Commutative Weyl Boost–Translation Commutation Relations (§2):**
   - Under the translation operator $(T_x f)(u) = f(u + x)$, the hyperbolic doublet
     $(C_\alpha f, S_\alpha f)$ transforms by the Lorentz boost matrix
     $\begin{pmatrix} \cosh(\alpha x) & \sinh(\alpha x) \\ \sinh(\alpha x) & \cosh(\alpha x) \end{pmatrix}$:
     $$T_x (C_\alpha f) = \cosh(\alpha x) \, C_\alpha (T_x f) + \sinh(\alpha x) \, S_\alpha (T_x f),$$
     $$T_x (S_\alpha f) = \sinh(\alpha x) \, C_\alpha (T_x f) + \cosh(\alpha x) \, S_\alpha (T_x f),$$
     yielding explicit non-commutative commutators $[T_x, C_\alpha]$ and $[T_x, S_\alpha]$.

3. **Scale-Invariant Hyperbolic Casimir Invariant & Minkowski Light-Cone Law (§3):**
   - The **Hyperbolic Casimir Invariant**
     $$\mathcal{C}_\alpha(f, x) := \frac{h_{C_\alpha f}(x) - h_{S_\alpha f}(x)}{\cosh(\alpha x)}$$
     equals $h_f(x)$ for every $\alpha \in \mathbb{R}$ (`hyperbolicCasimirInvariant_eq_autocorr`)
     and is therefore strictly invariant under all Lorentz boosts
     (`hyperbolicCasimirInvariant_rapidity_invariant`).
   - **Minkowski Light-Cone Identity (`autocorr_coshMultiplier_sq_sub_sinhMultiplier_sq`):**
     The Minkowski quadratic form of the autocorrelation doublet factors as
     $$h_{C_\alpha f}(x)^2 - h_{S_\alpha f}(x)^2
       = \cosh(\alpha x) \, h_f(x) \, \bigl(h_{C_\alpha f}(x) + h_{S_\alpha f}(x)\bigr).$$
   - **Exact Zero-Grid Null-Cone Equivalence (`↔`)
     (`autocorr_eq_zero_iff_coshMultiplier_eq_sinhMultiplier` & `minkowski_lightCone_eq_zero_iff`):**
     For every rapidity $\alpha \in \mathbb{R}$,
     $$h_f(x) = 0 \iff h_{C_\alpha f}(x) = h_{S_\alpha f}(x),$$
     and $h_{C_\alpha f}(x)^2 - h_{S_\alpha f}(x)^2 = 0 \iff h_f(x) = 0 \vee
     h_{C_\alpha f}(x) + h_{S_\alpha f}(x) = 0$, while at the origin $x = 0$ the Minkowski form
     satisfies the timelike lower bound $h_{C_\alpha f}(0)^2 - h_{S_\alpha f}(0)^2 \ge h_f(0)^2$.

4. **Exact $L^2$ Defect Identities for the Krein Chord, Doubling & Increment Laws (§4):**
   - **Peter–Paul Chord Defect Identity (`autocorr_chord_peter_paul_defect_eq_integral`):**
     $$(1 + t)\bigl(h_f(0) - h_f(x)\bigr) + \left(1 + \frac{1}{t}\right)\bigl(h_f(0) - h_f(y)\bigr)
       - \bigl(h_f(0) - h_f(x + y)\bigr)
       = \frac{1}{2t} \int_{\mathbb{R}} \Bigl(t\bigl(f(u) - f(u + x)\bigr) -
         \bigl(f(u + x) - f(u + x + y)\bigr)\Bigr)^2 \, du.$$
   - **Krein Doubling Second-Difference Identity (`autocorr_krein_doubling_defect_eq_integral`):**
     $$4\bigl(h_f(0) - h_f(x)\bigr) - \bigl(h_f(0) - h_f(2x)\bigr)
       = \frac{1}{2} \int_{\mathbb{R}} \bigl(f(u) - 2 f(u + x) + f(u + 2x)\bigr)^2 \, du.$$
   - **Krein Increment Defect Identity (`autocorr_krein_increment_defect_eq_integral`):**
     $$2\bigl(h_f(0) - h_f(x - y)\bigr) - 2t\bigl(h_f(x) - h_f(y)\bigr) + t^2 h_f(0)
       = \int_{\mathbb{R}} \bigl(f(u + x) - f(u + y) - t f(u)\bigr)^2 \, du.$$
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

set_option autoImplicit false

/-! ## §1. The $\mathrm{SO}^+(1, 1)$ Lorentz Boost Representation -/

@[simp]
theorem coshMultiplier_zero (f : ℝ → ℝ) :
    coshMultiplier 0 f = f := by
  funext u
  simp [coshMultiplier]

@[simp]
theorem sinhMultiplier_zero (f : ℝ → ℝ) :
    sinhMultiplier 0 f = fun _ => 0 := by
  funext u
  simp [sinhMultiplier]

@[simp]
theorem coshMultiplier_neg (α : ℝ) (f : ℝ → ℝ) :
    coshMultiplier (-α) f = coshMultiplier α f := by
  funext u
  unfold coshMultiplier
  rw [neg_mul, Real.cosh_neg]

@[simp]
theorem sinhMultiplier_neg (α : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    sinhMultiplier (-α) f u = -sinhMultiplier α f u := by
  unfold sinhMultiplier
  rw [neg_mul, Real.sinh_neg, neg_mul]

/-- **$\mathrm{SO}^+(1, 1)$ Boost Addition Law for `coshMultiplier`:**
$$C_{\alpha + \beta} f(u) = C_\alpha (C_\beta f)(u) + S_\alpha (S_\beta f)(u).$$ -/
theorem coshMultiplier_add (α β : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    coshMultiplier (α + β) f u =
      coshMultiplier α (coshMultiplier β f) u +
        sinhMultiplier α (sinhMultiplier β f) u := by
  unfold coshMultiplier sinhMultiplier
  have hadd : (α + β) * u = α * u + β * u := by ring
  rw [hadd, Real.cosh_add]
  ring

/-- **$\mathrm{SO}^+(1, 1)$ Boost Addition Law for `sinhMultiplier`:**
$$S_{\alpha + \beta} f(u) = C_\alpha (S_\beta f)(u) + S_\alpha (C_\beta f)(u).$$ -/
theorem sinhMultiplier_add (α β : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    sinhMultiplier (α + β) f u =
      coshMultiplier α (sinhMultiplier β f) u +
        sinhMultiplier α (coshMultiplier β f) u := by
  unfold coshMultiplier sinhMultiplier
  have hadd : (α + β) * u = α * u + β * u := by ring
  rw [hadd, Real.sinh_add]
  ring

/-- **$\mathrm{SO}^+(1, 1)$ Lorentz Metric Operator Identity:**
$$C_\alpha (C_\alpha f)(u) - S_\alpha (S_\alpha f)(u) = f(u).$$ -/
theorem coshMultiplier_comp_self_sub_sinhMultiplier_comp_self (α : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    coshMultiplier α (coshMultiplier α f) u -
        sinhMultiplier α (sinhMultiplier α f) u = f u := by
  unfold coshMultiplier sinhMultiplier
  have h := Real.cosh_sq_sub_sinh_sq (α * u)
  calc
    Real.cosh (α * u) * (Real.cosh (α * u) * f u) -
        Real.sinh (α * u) * (Real.sinh (α * u) * f u)
      = (Real.cosh (α * u) ^ 2 - Real.sinh (α * u) ^ 2) * f u := by ring
    _ = 1 * f u := by rw [h]
    _ = f u := one_mul _

/-- **Hyperbolic Boost Inversion (Diagonal Component):**
$$C_{-\alpha}(C_\alpha f)(u) + S_{-\alpha}(S_\alpha f)(u) = f(u).$$ -/
theorem lorentzBoost_inverse_cosh (α : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    coshMultiplier (-α) (coshMultiplier α f) u +
        sinhMultiplier (-α) (sinhMultiplier α f) u = f u := by
  have h := coshMultiplier_add (-α) α f u
  rw [neg_add_cancel, coshMultiplier_zero] at h
  exact h.symm

/-- **Hyperbolic Boost Inversion (Off-Diagonal Component):**
$$C_{-\alpha}(S_\alpha f)(u) + S_{-\alpha}(C_\alpha f)(u) = 0.$$ -/
theorem lorentzBoost_inverse_sinh (α : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    coshMultiplier (-α) (sinhMultiplier α f) u +
        sinhMultiplier (-α) (coshMultiplier α f) u = 0 := by
  have h := sinhMultiplier_add (-α) α f u
  rw [neg_add_cancel, sinhMultiplier_zero] at h
  exact h.symm

/-! ## §2. Non-Commutative Weyl Boost–Translation Commutation Relations -/

/-- The additive translation operator `(shiftOp x f)(u) = f(u + x)`. -/
def shiftOp (x : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  f (u + x)

@[simp]
theorem shiftOp_zero (f : ℝ → ℝ) :
    shiftOp 0 f = f := by
  funext u
  simp [shiftOp]

theorem shiftOp_add (x y : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    shiftOp (x + y) f u = shiftOp x (shiftOp y f) u := by
  unfold shiftOp
  ring_nf

/-- **Weyl Boost–Translation Intertwining Law for `coshMultiplier`:**
$$T_x (C_\alpha f)(u) = \cosh(\alpha x) \, C_\alpha (T_x f)(u) + \sinh(\alpha x) \, S_\alpha (T_x f)(u).$$ -/
theorem shiftOp_coshMultiplier (α x : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    shiftOp x (coshMultiplier α f) u =
      Real.cosh (α * x) * coshMultiplier α (shiftOp x f) u +
        Real.sinh (α * x) * sinhMultiplier α (shiftOp x f) u := by
  unfold shiftOp coshMultiplier sinhMultiplier
  have hadd : α * (u + x) = α * u + α * x := by ring
  rw [hadd, Real.cosh_add]
  ring

/-- **Weyl Boost–Translation Intertwining Law for `sinhMultiplier`:**
$$T_x (S_\alpha f)(u) = \sinh(\alpha x) \, C_\alpha (T_x f)(u) + \cosh(\alpha x) \, S_\alpha (T_x f)(u).$$ -/
theorem shiftOp_sinhMultiplier (α x : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    shiftOp x (sinhMultiplier α f) u =
      Real.sinh (α * x) * coshMultiplier α (shiftOp x f) u +
        Real.cosh (α * x) * sinhMultiplier α (shiftOp x f) u := by
  unfold shiftOp coshMultiplier sinhMultiplier
  have hadd : α * (u + x) = α * u + α * x := by ring
  rw [hadd, Real.sinh_add]
  ring

/-- **Non-Commutative Commutator $[T_x, C_\alpha]$:**
$$(T_x C_\alpha - C_\alpha T_x) f(u)
  = (\cosh(\alpha x) - 1) \, C_\alpha (T_x f)(u) + \sinh(\alpha x) \, S_\alpha (T_x f)(u).$$ -/
theorem commutator_shiftOp_coshMultiplier (α x : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    shiftOp x (coshMultiplier α f) u - coshMultiplier α (shiftOp x f) u =
      (Real.cosh (α * x) - 1) * coshMultiplier α (shiftOp x f) u +
        Real.sinh (α * x) * sinhMultiplier α (shiftOp x f) u := by
  rw [shiftOp_coshMultiplier]
  ring

/-- **Non-Commutative Commutator $[T_x, S_\alpha]$:**
$$(T_x S_\alpha - S_\alpha T_x) f(u)
  = \sinh(\alpha x) \, C_\alpha (T_x f)(u) + (\cosh(\alpha x) - 1) \, S_\alpha (T_x f)(u).$$ -/
theorem commutator_shiftOp_sinhMultiplier (α x : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    shiftOp x (sinhMultiplier α f) u - sinhMultiplier α (shiftOp x f) u =
      Real.sinh (α * x) * coshMultiplier α (shiftOp x f) u +
        (Real.cosh (α * x) - 1) * sinhMultiplier α (shiftOp x f) u := by
  rw [shiftOp_sinhMultiplier]
  ring

/-! ## §3. Scale-Invariant Hyperbolic Casimir Invariant & Minkowski Light-Cone Law -/

/-- The **Hyperbolic Casimir Invariant** of a source `f` at rapidity `α` and shift `x`:
$$\mathcal{C}_\alpha(f, x) := \frac{h_{C_\alpha f}(x) - h_{S_\alpha f}(x)}{\cosh(\alpha x)}.$$ -/
def hyperbolicCasimirInvariant (α : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (autocorr (coshMultiplier α f) x - autocorr (sinhMultiplier α f) x) / Real.cosh (α * x)

/-- **Exact Evaluation of the Hyperbolic Casimir Invariant:**
For every continuous compactly supported `f : ℝ → ℝ` and all `α, x ∈ ℝ`,
$$\mathcal{C}_\alpha(f, x) = \operatorname{autocorr}(f, x).$$ -/
theorem hyperbolicCasimirInvariant_eq_autocorr {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α x : ℝ) :
    hyperbolicCasimirInvariant α f x = autocorr f x := by
  unfold hyperbolicCasimirInvariant
  rw [autocorr_coshMultiplier_sub_sinhMultiplier hf hfc α x,
    mul_div_cancel_left₀ _ (Real.cosh_pos _).ne']

/-- **Rapidity Invariance of the Hyperbolic Casimir Invariant:**
For any two boost rapidities `α, β ∈ ℝ`,
$$\mathcal{C}_\alpha(f, x) = \mathcal{C}_\beta(f, x).$$ -/
theorem hyperbolicCasimirInvariant_rapidity_invariant {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α β x : ℝ) :
    hyperbolicCasimirInvariant α f x = hyperbolicCasimirInvariant β f x := by
  rw [hyperbolicCasimirInvariant_eq_autocorr hf hfc α x,
    hyperbolicCasimirInvariant_eq_autocorr hf hfc β x]

/-- **The Minkowski Light-Cone Identity for Hyperbolic Autocorrelation Doublets:**
For every continuous compactly supported `f : ℝ → ℝ` and all `α, x ∈ ℝ`,
$$h_{C_\alpha f}(x)^2 - h_{S_\alpha f}(x)^2
  = \cosh(\alpha x) \, h_f(x) \, \bigl(h_{C_\alpha f}(x) + h_{S_\alpha f}(x)\bigr).$$ -/
theorem autocorr_coshMultiplier_sq_sub_sinhMultiplier_sq {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α x : ℝ) :
    autocorr (coshMultiplier α f) x ^ 2 - autocorr (sinhMultiplier α f) x ^ 2 =
      Real.cosh (α * x) * autocorr f x *
        (autocorr (coshMultiplier α f) x + autocorr (sinhMultiplier α f) x) := by
  have hdiff := autocorr_coshMultiplier_sub_sinhMultiplier hf hfc α x
  calc
    autocorr (coshMultiplier α f) x ^ 2 - autocorr (sinhMultiplier α f) x ^ 2
      = (autocorr (coshMultiplier α f) x - autocorr (sinhMultiplier α f) x) *
          (autocorr (coshMultiplier α f) x + autocorr (sinhMultiplier α f) x) := by ring
    _ = Real.cosh (α * x) * autocorr f x *
          (autocorr (coshMultiplier α f) x + autocorr (sinhMultiplier α f) x) := by
        rw [hdiff]

/-- **Exact Zero-Grid Coincidence Equivalence (`↔`):**
For every continuous compactly supported `f : ℝ → ℝ` and every boost rapidity `α ∈ ℝ`,
a shift `x` is a zero of `autocorr f` if and only if the `cosh`- and `sinh`-multiplier
autocorrelations coincide at `x`:
$$h_f(x) = 0 \iff h_{C_\alpha f}(x) = h_{S_\alpha f}(x).$$ -/
theorem autocorr_eq_zero_iff_coshMultiplier_eq_sinhMultiplier {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α x : ℝ) :
    autocorr f x = 0 ↔
      autocorr (coshMultiplier α f) x = autocorr (sinhMultiplier α f) x := by
  constructor
  · exact autocorr_coshMultiplier_eq_sinhMultiplier_of_zero hf hfc α
  · intro heq
    rw [← hyperbolicCasimirInvariant_eq_autocorr hf hfc α x]
    unfold hyperbolicCasimirInvariant
    rw [heq, sub_self, zero_div]

/-- **Exact Minkowski Null-Cone Characterization (`↔`):**
For every continuous compactly supported `f : ℝ → ℝ` and all `α, x ∈ ℝ`, the autocorrelation
doublet $(h_{C_\alpha f}(x), h_{S_\alpha f}(x))$ lies on the Minkowski null light-cone if and only
if either $h_f(x) = 0$ (the future-null branch $h_{C_\alpha f}(x) = h_{S_\alpha f}(x)$) or
$h_{C_\alpha f}(x) + h_{S_\alpha f}(x) = 0$ (the past-null branch):
$$h_{C_\alpha f}(x)^2 - h_{S_\alpha f}(x)^2 = 0
  \iff h_f(x) = 0 \;\lor\; h_{C_\alpha f}(x) + h_{S_\alpha f}(x) = 0.$$ -/
theorem minkowski_lightCone_eq_zero_iff {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α x : ℝ) :
    autocorr (coshMultiplier α f) x ^ 2 - autocorr (sinhMultiplier α f) x ^ 2 = 0 ↔
      autocorr f x = 0 ∨
        autocorr (coshMultiplier α f) x + autocorr (sinhMultiplier α f) x = 0 := by
  rw [autocorr_coshMultiplier_sq_sub_sinhMultiplier_sq hf hfc α x, mul_eq_zero, mul_eq_zero]
  have hcosh : Real.cosh (α * x) ≠ 0 := (Real.cosh_pos _).ne'
  simp [hcosh]

/-- **Timelike Origin Lower Bound on the Minkowski Quadratic Form:**
At $x = 0$, the Minkowski quadratic form of the autocorrelation doublet satisfies
$$h_{C_\alpha f}(0)^2 - h_{S_\alpha f}(0)^2
  = h_f(0) \bigl(h_f(0) + 2 h_{S_\alpha f}(0)\bigr) \ge h_f(0)^2.$$ -/
theorem minkowski_lightCone_origin_ge_sq {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α : ℝ) :
    autocorr f 0 ^ 2 ≤
      autocorr (coshMultiplier α f) 0 ^ 2 - autocorr (sinhMultiplier α f) 0 ^ 2 := by
  have h0 := autocorr_coshMultiplier_zero_eq hf hfc α
  have hf0 : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have hs0 : 0 ≤ autocorr (sinhMultiplier α f) 0 := autocorr_zero_nonneg (sinhMultiplier α f)
  rw [h0]
  nlinarith

/-! ## §4. Exact $L^2$ Defect Identities for the Krein Chord, Doubling & Increment Laws -/

/-- **Exact $L^2$ Defect Identity for the Peter–Paul Chord Inequality:**
For any continuous compactly supported `f : ℝ → ℝ`, shifts `x, y ∈ ℝ`, and parameter `t > 0`,
$$(1 + t)\bigl(h_f(0) - h_f(x)\bigr) + \left(1 + \frac{1}{t}\right)\bigl(h_f(0) - h_f(y)\bigr)
  - \bigl(h_f(0) - h_f(x + y)\bigr)
  = \frac{1}{2t} \int_{\mathbb{R}} \Bigl(t\bigl(f(u) - f(u + x)\bigr) -
    \bigl(f(u + x) - f(u + (x + y))\bigr)\Bigr)^2 \, du.$$ -/
theorem autocorr_chord_peter_paul_defect_eq_integral {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f) (x y : ℝ) {t : ℝ} (ht : t ≠ 0) :
    (1 + t) * (autocorr f 0 - autocorr f x) +
        (1 + 1 / t) * (autocorr f 0 - autocorr f y) -
        (autocorr f 0 - autocorr f (x + y)) =
      (1 / (2 * t)) * ∫ u, (t * (f u - f (u + x)) - (f (u + x) - f (u + (x + y)))) ^ 2 := by
  set A : ℝ → ℝ := fun u => f u - f (u + x)
  set B : ℝ → ℝ := fun u => f (u + x) - f (u + (x + y))
  have hAc : Continuous A := hf.sub (hf.comp (continuous_add_const x))
  have hAcs : HasCompactSupport A := hfc.sub (hasCompactSupport_comp_add hfc x)
  have hBc : Continuous B :=
    (hf.comp (continuous_add_const x)).sub (hf.comp (continuous_add_const (x + y)))
  have hBcs : HasCompactSupport B :=
    (hasCompactSupport_comp_add hfc x).sub (hasCompactSupport_comp_add hfc (x + y))
  have hiA : Integrable (fun u => A u ^ 2) := integrable_sq hAc hAcs
  have hiB : Integrable (fun u => B u ^ 2) := integrable_sq hBc hBcs
  have hiAB : Integrable (fun u => (A u + B u) ^ 2) :=
    integrable_sq (hAc.add hBc) (hAcs.add hBcs)
  have hpt : ∀ u : ℝ,
      (t * A u - B u) ^ 2 =
        t * ((1 + t) * A u ^ 2 + (1 + 1 / t) * B u ^ 2 - (A u + B u) ^ 2) := by
    intro u
    field_simp [ht]
    ring
  change _ = (1 / (2 * t)) * ∫ u, (t * A u - B u) ^ 2
  simp_rw [hpt]
  have e1 : (∫ u, ((1 + t) * A u ^ 2 + (1 + 1 / t) * B u ^ 2 - (A u + B u) ^ 2)) =
      (∫ u, ((1 + t) * A u ^ 2 + (1 + 1 / t) * B u ^ 2)) - ∫ u, (A u + B u) ^ 2 :=
    integral_sub ((hiA.const_mul (1 + t)).add (hiB.const_mul (1 + 1 / t))) hiAB
  have e2 : (∫ u, ((1 + t) * A u ^ 2 + (1 + 1 / t) * B u ^ 2)) =
      (∫ u, (1 + t) * A u ^ 2) + ∫ u, (1 + 1 / t) * B u ^ 2 :=
    integral_add (hiA.const_mul (1 + t)) (hiB.const_mul (1 + 1 / t))
  rw [integral_const_mul, e1, e2, integral_const_mul, integral_const_mul]
  have hsum : (fun u => (A u + B u) ^ 2) = fun u => (f u - f (u + (x + y))) ^ 2 := by
    funext u; simp only [A, B]; ring
  have hAint : (∫ u, A u ^ 2) = 2 * (autocorr f 0 - autocorr f x) :=
    integral_sub_shift_sq hfc hf x
  have hBint : (∫ u, B u ^ 2) = 2 * (autocorr f 0 - autocorr f y) := by
    have := integral_shift_sub_shift_sq hfc hf x (x + y)
    simpa [B, show x - (x + y) = -y by ring, autocorr_neg] using this
  rw [hsum, integral_sub_shift_sq hfc hf (x + y), hAint, hBint]
  field_simp [ht]

/-- **Exact $L^2$ Second-Difference Identity for the Krein Doubling Law:**
For any continuous compactly supported `f : ℝ → ℝ` and shift `x ∈ ℝ`,
$$4\bigl(h_f(0) - h_f(x)\bigr) - \bigl(h_f(0) - h_f(2x)\bigr)
  = \frac{1}{2} \int_{\mathbb{R}} \bigl(f(u) - 2 f(u + x) + f(u + 2x)\bigr)^2 \, du.$$ -/
theorem autocorr_krein_doubling_defect_eq_integral {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f) (x : ℝ) :
    4 * (autocorr f 0 - autocorr f x) - (autocorr f 0 - autocorr f (2 * x)) =
      (1 / 2 : ℝ) * ∫ u, (f u - 2 * f (u + x) + f (u + 2 * x)) ^ 2 := by
  have hpp := autocorr_chord_peter_paul_defect_eq_integral hfc hf x x one_ne_zero
  have h2x : x + x = 2 * x := by ring
  have hint :
      (fun u => (1 * (f u - f (u + x)) - (f (u + x) - f (u + (x + x)))) ^ 2) =
        fun u => (f u - 2 * f (u + x) + f (u + 2 * x)) ^ 2 := by
    funext u
    rw [h2x]
    ring
  rw [hint, h2x] at hpp
  linarith

/-- **Exact $L^2$ Defect Identity for Krein's Positive-Definite Increment Quadratic Form:**
For any continuous compactly supported `f : ℝ → ℝ` and real numbers `x, y, t ∈ ℝ`,
$$2\bigl(h_f(0) - h_f(x - y)\bigr) - 2t\bigl(h_f(x) - h_f(y)\bigr) + t^2 h_f(0)
  = \int_{\mathbb{R}} \bigl(f(u + x) - f(u + y) - t f(u)\bigr)^2 \, du.$$ -/
theorem autocorr_krein_increment_defect_eq_integral {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f) (x y t : ℝ) :
    2 * (autocorr f 0 - autocorr f (x - y)) -
        2 * t * (autocorr f x - autocorr f y) + t ^ 2 * autocorr f 0 =
      ∫ u, (f (u + x) - f (u + y) - t * f u) ^ 2 := by
  set D : ℝ → ℝ := fun u => f (u + x) - f (u + y)
  have hDc : Continuous D :=
    (hf.comp (continuous_add_const x)).sub (hf.comp (continuous_add_const y))
  have hDcs : HasCompactSupport D :=
    (hasCompactSupport_comp_add hfc x).sub (hasCompactSupport_comp_add hfc y)
  have hiD2 : Integrable (fun u => D u ^ 2) := integrable_sq hDc hDcs
  have hif2 : Integrable (fun u => f u ^ 2) := integrable_sq hf hfc
  have hifx : Integrable (fun u => f u * f (u + x)) := integrable_mul_shift hf hfc x
  have hify : Integrable (fun u => f u * f (u + y)) := integrable_mul_shift hf hfc y
  have hiDf : Integrable (fun u => f u * D u) := by
    have hrew : (fun u => f u * D u) = fun u => f u * f (u + x) - f u * f (u + y) := by
      funext u; simp only [D]; ring
    rw [hrew]
    exact hifx.sub hify
  have hexpand : (fun u => (D u - t * f u) ^ 2) =
      fun u => (D u ^ 2 - 2 * t * (f u * D u)) + t ^ 2 * f u ^ 2 := by
    funext u; ring
  have e1 : (∫ u, ((D u ^ 2 - 2 * t * (f u * D u)) + t ^ 2 * f u ^ 2)) =
      (∫ u, (D u ^ 2 - 2 * t * (f u * D u))) + ∫ u, t ^ 2 * f u ^ 2 :=
    integral_add (hiD2.sub (hiDf.const_mul (2 * t))) (hif2.const_mul (t ^ 2))
  have e2 : (∫ u, (D u ^ 2 - 2 * t * (f u * D u))) =
      (∫ u, D u ^ 2) - ∫ u, 2 * t * (f u * D u) :=
    integral_sub hiD2 (hiDf.const_mul (2 * t))
  change _ = ∫ u, (D u - t * f u) ^ 2
  rw [hexpand, e1, e2, integral_const_mul, integral_const_mul]
  have hDint : (∫ u, D u ^ 2) = 2 * (autocorr f 0 - autocorr f (x - y)) :=
    integral_shift_sub_shift_sq hfc hf x y
  have hDfint : (∫ u, f u * D u) = autocorr f x - autocorr f y := by
    have hrew : (fun u => f u * D u) = fun u => f u * f (u + x) - f u * f (u + y) := by
      funext u; simp only [D]; ring
    rw [hrew, integral_sub hifx hify]
    rfl
  rw [hDint, hDfint, integral_sq_eq_autocorr_zero]

end

end GaloisForLFunctions.BiScaleUncertainty

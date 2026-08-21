import GaloisForLFunctions.HTGeometry.TriangularIntervalFubini
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The inverse Neumann Laplacian on a symmetric interval

On `(-a,a)` the differentiation operator `D = i d/dx` with Dirichlet boundary conditions maps
`H_0^1(-a,a)` bijectively onto the mean-zero space `L_0^2(-a,a)`, and for `u = Dv` the `L²` mass of
the primitive `v` is the quadratic form of a compact positive integral operator.  Two kernels
represent that form:

* the prefix Gram kernel `a - max(x,y)`, coming from writing `v` as a prefix integral of `u`;
* the Neumann Green kernel

  `N(x,y) = (x² + y²)/(4a) - |x - y|/2 + a/6`,

  the integral kernel of `(-Δ_N)^{-1}`, where `-Δ_N = D D^*` is the Neumann Laplacian.

The two kernels differ by the separable expression `φ(x) + φ(y)`, so their quadratic forms agree on
mean-zero data; this is the equality of forms

`‖v‖_{L²}² = ⟨(a - max(·,·)) u, u⟩ = ⟨N u, u⟩`.

The operator with kernel `N` is exactly the inverse Neumann Laplacian: for mean-zero `u` the
function `x ↦ ∫ N(x,y) u(y) dy` has derivative `-v(x)` at every interior point, so its second
derivative is `-u` and its first derivative vanishes at both endpoints — the Neumann boundary
condition.  Its range lies again in the mean-zero space, because every `N(x,·)` has vanishing
integral.

Only interval integrability of the datum is assumed; every `L²` function on a bounded interval is
interval integrable, so the statements below apply verbatim to `L_0^2(-a,a)`.
-/

open MeasureTheory Set intervalIntegral
open scoped ComplexConjugate

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## Conjugation of interval-integrable data -/

theorem integrable_conj_of_integrable {μ : Measure ℝ} {f : ℝ → ℂ} (h : Integrable f μ) :
    Integrable (fun x => conj (f x)) μ := by
  refine h.norm.mono'
    (Complex.continuous_conj.comp_aestronglyMeasurable h.aestronglyMeasurable) ?_
  filter_upwards with x
  simp

theorem intervalIntegrable_conj {f : ℝ → ℂ} {a b : ℝ} {μ : Measure ℝ}
    (h : IntervalIntegrable f μ a b) :
    IntervalIntegrable (fun x => conj (f x)) μ a b :=
  ⟨integrable_conj_of_integrable h.1, integrable_conj_of_integrable h.2⟩

theorem intervalIntegral_conj {f : ℝ → ℂ} (a b : ℝ) :
    (∫ x in a..b, conj (f x)) = conj (∫ x in a..b, f x) := by
  simp [intervalIntegral, integral_conj]

/-! ## The two kernels -/

/-- The Neumann Green kernel `N(x,y) = (x² + y²)/(4a) - |x - y|/2 + a/6` of `(-Δ_N)^{-1}` on
`(-a,a)`. -/
def suzukiNeumannGreenKernel (a x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2) / (4 * a) - |x - y| / 2 + a / 6

/-- The prefix Gram kernel `a - max(x,y)`: the Gram kernel of the map sending `u` to its prefix
integral. -/
def suzukiPrefixGramKernel (a x y : ℝ) : ℝ := a - max x y

/-- The separable profile by which the two kernels differ. -/
def suzukiNeumannSplitProfile (a t : ℝ) : ℝ := t ^ 2 / (4 * a) + t / 2 - 5 * a / 12

theorem suzukiNeumannGreenKernel_symm (a x y : ℝ) :
    suzukiNeumannGreenKernel a x y = suzukiNeumannGreenKernel a y x := by
  unfold suzukiNeumannGreenKernel
  rw [abs_sub_comm]
  ring

theorem suzukiPrefixGramKernel_symm (a x y : ℝ) :
    suzukiPrefixGramKernel a x y = suzukiPrefixGramKernel a y x := by
  unfold suzukiPrefixGramKernel
  rw [max_comm]

theorem continuous_suzukiNeumannGreenKernel (a x : ℝ) :
    Continuous fun y => suzukiNeumannGreenKernel a x y := by
  unfold suzukiNeumannGreenKernel
  fun_prop

theorem continuous_suzukiPrefixGramKernel (a x : ℝ) :
    Continuous fun y => suzukiPrefixGramKernel a x y := by
  unfold suzukiPrefixGramKernel
  fun_prop

theorem max_eq_half_add_abs_sub (x y : ℝ) : max x y = (x + y + |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring

/-- **The two kernels differ by a separable term.**  `N(x,y) - (a - max(x,y)) = φ(x) + φ(y)`.
No positivity or nonvanishing assumption on `a` is needed. -/
theorem suzukiNeumannGreenKernel_sub_prefixGramKernel (a x y : ℝ) :
    suzukiNeumannGreenKernel a x y - suzukiPrefixGramKernel a x y
      = suzukiNeumannSplitProfile a x + suzukiNeumannSplitProfile a y := by
  unfold suzukiNeumannGreenKernel suzukiPrefixGramKernel suzukiNeumannSplitProfile
  rw [max_eq_half_add_abs_sub]
  ring

/-! ## The prefix primitive -/

/-- The prefix primitive `v(x) = ∫_{-a}^x u(t) dt`, i.e. the inverse of `d/dx` on
`H_0^1(-a,a)`. -/
def suzukiPrefixPrimitive (a : ℝ) (u : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t in (-a)..x, u t

@[simp]
theorem suzukiPrefixPrimitive_left (a : ℝ) (u : ℝ → ℂ) :
    suzukiPrefixPrimitive a u (-a) = 0 := by
  simp [suzukiPrefixPrimitive]

/-- The prefix primitive vanishes at the right endpoint exactly on mean-zero data: this is the
Dirichlet boundary condition `v(a) = 0`. -/
theorem suzukiPrefixPrimitive_right (a : ℝ) (u : ℝ → ℂ)
    (hmean : (∫ y in (-a)..a, u y) = 0) :
    suzukiPrefixPrimitive a u a = 0 := hmean

theorem integrableOn_uIcc_of_intervalIntegrable {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a) :
    IntegrableOn u (uIcc (-a) a) volume := by
  have hle : -a ≤ a := by linarith
  rw [uIcc_of_le hle]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mp hu

theorem continuousOn_suzukiPrefixPrimitive {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a) :
    ContinuousOn (suzukiPrefixPrimitive a u) (uIcc (-a) a) :=
  continuousOn_primitive_interval (integrableOn_uIcc_of_intervalIntegrable ha hu)

theorem intervalIntegrable_suzukiPrefixPrimitive {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a) :
    IntervalIntegrable (suzukiPrefixPrimitive a u) volume (-a) a :=
  (continuousOn_suzukiPrefixPrimitive ha hu).intervalIntegrable

/-! ## The prefix Gram kernel integrates the primitive over the upper tail -/

theorem intervalIntegrable_prefixGramKernel_mul {a p q : ℝ} {u : ℝ → ℂ} (x : ℝ)
    (hu : IntervalIntegrable u volume p q) :
    IntervalIntegrable (fun y => ((suzukiPrefixGramKernel a x y : ℝ) : ℂ) * u y) volume p q :=
  hu.continuousOn_mul
    (Complex.continuous_ofReal.comp (continuous_suzukiPrefixGramKernel a x)).continuousOn

/-- Against mean-free-free data the prefix Gram kernel produces the tail integral of the prefix
primitive:  `∫_{-a}^a (a - max(x,y)) u(y) dy = ∫_x^a v(t) dt`.  This is the Fubini identity
behind `‖v‖² = ⟨K̃_a u, u⟩`. -/
theorem intervalIntegral_prefixGramKernel_mul {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a) {x : ℝ} (hx : x ∈ Icc (-a) a) :
    (∫ y in (-a)..a, ((suzukiPrefixGramKernel a x y : ℝ) : ℂ) * u y)
      = ∫ t in x..a, suzukiPrefixPrimitive a u t := by
  obtain ⟨hx1, hx2⟩ := hx
  have hle : (-a : ℝ) ≤ a := by linarith
  have hu1 : IntervalIntegrable u volume (-a) x :=
    hu.mono_set (by rw [uIcc_of_le hx1, uIcc_of_le hle]; exact Icc_subset_Icc le_rfl hx2)
  have hu2 : IntervalIntegrable u volume x a :=
    hu.mono_set (by rw [uIcc_of_le hx2, uIcc_of_le hle]; exact Icc_subset_Icc hx1 le_rfl)
  have hKu1 := intervalIntegrable_prefixGramKernel_mul (a := a) (u := u) x hu1
  have hKu2 := intervalIntegrable_prefixGramKernel_mul (a := a) (u := u) x hu2
  have hsplit :
      (∫ y in (-a)..x, ((suzukiPrefixGramKernel a x y : ℝ) : ℂ) * u y) +
          ∫ y in x..a, ((suzukiPrefixGramKernel a x y : ℝ) : ℂ) * u y
        = ∫ y in (-a)..a, ((suzukiPrefixGramKernel a x y : ℝ) : ℂ) * u y :=
    intervalIntegral.integral_add_adjacent_intervals hKu1 hKu2
  -- lower piece: the kernel is the constant `a - x`
  have hlow :
      (∫ y in (-a)..x, ((suzukiPrefixGramKernel a x y : ℝ) : ℂ) * u y)
        = ((a - x : ℝ) : ℂ) * suzukiPrefixPrimitive a u x := by
    rw [suzukiPrefixPrimitive, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro y hy
    rw [uIcc_of_le hx1] at hy
    have hmax : max x y = x := max_eq_left hy.2
    simp [suzukiPrefixGramKernel, hmax]
  -- upper piece: the kernel is `a - y`
  have hup :
      (∫ y in x..a, ((suzukiPrefixGramKernel a x y : ℝ) : ℂ) * u y)
        = ∫ y in x..a, u y * ((a - y : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr ?_
    intro y hy
    rw [uIcc_of_le hx2] at hy
    have hmax : max x y = y := max_eq_right hy.1
    simp [suzukiPrefixGramKernel, hmax, mul_comm]
  -- the right-hand side, decomposed along `x`
  have hv : ∀ t ∈ uIcc x a,
      suzukiPrefixPrimitive a u t = suzukiPrefixPrimitive a u x + ∫ s in x..t, u s := by
    intro t ht
    rw [uIcc_of_le hx2] at ht
    have hut : IntervalIntegrable u volume x t :=
      hu2.mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le hx2]; exact Icc_subset_Icc le_rfl ht.2)
    exact (intervalIntegral.integral_add_adjacent_intervals hu1 hut).symm
  have hcontTail : ContinuousOn (fun t => ∫ s in x..t, u s) (uIcc x a) :=
    continuousOn_primitive_interval
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hx2).mp hu2 |>.mono_set
        (by rw [uIcc_of_le hx2]))
  have hrhs :
      (∫ t in x..a, suzukiPrefixPrimitive a u t)
        = ((a - x : ℝ) : ℂ) * suzukiPrefixPrimitive a u x
            + ∫ t in x..a, ∫ s in x..t, u s := by
    rw [intervalIntegral.integral_congr hv,
      intervalIntegral.integral_add (intervalIntegrable_const)
        hcontTail.intervalIntegrable,
      intervalIntegral.integral_const]
    simp [Complex.real_smul]
  have hswap :
      (∫ s in x..a, u s * ∫ t in s..a, (1 : ℂ)) = ∫ t in x..a, (∫ s in x..t, u s) * 1 :=
    intervalIntegral_triangle_swap hx2 hu2 intervalIntegrable_const
  have hone : ∀ s : ℝ, (∫ t in s..a, (1 : ℂ)) = ((a - s : ℝ) : ℂ) := by
    intro s
    rw [intervalIntegral.integral_const]
    simp [Complex.real_smul]
  simp only [hone, mul_one] at hswap
  rw [← hsplit, hlow, hup, hrhs, hswap]

/-- The upper tail integral of the Dirichlet primitive is continuous on the aperture. -/
theorem continuousOn_tail_suzukiPrefixPrimitive {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a) :
    ContinuousOn (fun x => ∫ t in x..a, suzukiPrefixPrimitive a u t) (uIcc (-a) a) := by
  have hle : (-a : ℝ) ≤ a := by linarith
  have hprim : ContinuousOn (fun x => ∫ t in (-a)..x, suzukiPrefixPrimitive a u t)
      (uIcc (-a) a) :=
    continuousOn_primitive_interval
      (integrableOn_uIcc_of_intervalIntegrable ha
        (intervalIntegrable_suzukiPrefixPrimitive ha hu))
  have hsplit : ∀ x ∈ uIcc (-a) a,
      (∫ t in x..a, suzukiPrefixPrimitive a u t)
        = (∫ t in (-a)..a, suzukiPrefixPrimitive a u t)
            - ∫ t in (-a)..x, suzukiPrefixPrimitive a u t := by
    intro x hx
    rw [uIcc_of_le hle] at hx
    have h1 : IntervalIntegrable (suzukiPrefixPrimitive a u) volume (-a) x :=
      (intervalIntegrable_suzukiPrefixPrimitive ha hu).mono_set
        (by rw [uIcc_of_le hx.1, uIcc_of_le hle]; exact Icc_subset_Icc le_rfl hx.2)
    have h2 : IntervalIntegrable (suzukiPrefixPrimitive a u) volume x a :=
      (intervalIntegrable_suzukiPrefixPrimitive ha hu).mono_set
        (by rw [uIcc_of_le hx.2, uIcc_of_le hle]; exact Icc_subset_Icc hx.1 le_rfl)
    rw [eq_sub_iff_add_eq, add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals h1 h2
  exact (continuousOn_const.sub hprim).congr hsplit

theorem intervalIntegrable_tail_suzukiPrefixPrimitive {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a) :
    IntervalIntegrable (fun x => ∫ t in x..a, suzukiPrefixPrimitive a u t) volume (-a) a :=
  (continuousOn_tail_suzukiPrefixPrimitive ha hu).intervalIntegrable

/-- The prefix Gram operator, as a function of the outer variable, is continuous on the
aperture. -/
theorem continuousOn_prefixGram_operator {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a) :
    ContinuousOn (fun x => ∫ y in (-a)..a, ((suzukiPrefixGramKernel a x y : ℝ) : ℂ) * u y)
      (uIcc (-a) a) := by
  have hle : (-a : ℝ) ≤ a := by linarith
  refine (continuousOn_tail_suzukiPrefixPrimitive ha hu).congr ?_
  intro x hx
  rw [uIcc_of_le hle] at hx
  exact intervalIntegral_prefixGramKernel_mul ha hu hx

/-- **The prefix Gram form is the `L²` mass of the primitive.**  For `u = Dv` with
`v ∈ H_0^1(-a,a)`, `‖v‖_{L²}² = ⟨K̃_a u, u⟩` with `K̃_a` the integral operator of kernel
`a - max(x,y)`. -/
theorem intervalIntegral_prefixGram_form_eq_primitive_energy {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a) :
    (∫ x in (-a)..a,
        (∫ y in (-a)..a, ((suzukiPrefixGramKernel a x y : ℝ) : ℂ) * u y) * conj (u x))
      = ∫ t in (-a)..a,
          suzukiPrefixPrimitive a u t * conj (suzukiPrefixPrimitive a u t) := by
  have hle : (-a : ℝ) ≤ a := by linarith
  have hcongr :
      (∫ x in (-a)..a,
          (∫ y in (-a)..a, ((suzukiPrefixGramKernel a x y : ℝ) : ℂ) * u y) * conj (u x))
        = ∫ x in (-a)..a, conj (u x) * ∫ t in x..a, suzukiPrefixPrimitive a u t := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [uIcc_of_le hle] at hx
    dsimp only
    rw [intervalIntegral_prefixGramKernel_mul ha hu hx, mul_comm]
  rw [hcongr,
    intervalIntegral_triangle_swap hle (F := fun x => conj (u x))
      (G := suzukiPrefixPrimitive a u) (intervalIntegrable_conj hu)
      (intervalIntegrable_suzukiPrefixPrimitive ha hu)]
  refine intervalIntegral.integral_congr ?_
  intro t _
  dsimp only
  rw [intervalIntegral_conj]
  exact mul_comm _ _

/-! ## Passing to the Neumann Green kernel -/

theorem intervalIntegrable_neumannGreenKernel_mul {a p q : ℝ} {u : ℝ → ℂ} (x : ℝ)
    (hu : IntervalIntegrable u volume p q) :
    IntervalIntegrable (fun y => ((suzukiNeumannGreenKernel a x y : ℝ) : ℂ) * u y) volume p q :=
  hu.continuousOn_mul
    (Complex.continuous_ofReal.comp (continuous_suzukiNeumannGreenKernel a x)).continuousOn

theorem intervalIntegrable_splitProfile_mul {a p q : ℝ} {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume p q) :
    IntervalIntegrable (fun y => ((suzukiNeumannSplitProfile a y : ℝ) : ℂ) * u y) volume p q := by
  refine hu.continuousOn_mul (Complex.continuous_ofReal.comp ?_).continuousOn
  unfold suzukiNeumannSplitProfile
  fun_prop

/-- The constant by which the Neumann Green operator and the prefix Gram operator differ on
mean-zero data. -/
def suzukiNeumannSplitConstant (a : ℝ) (u : ℝ → ℂ) : ℂ :=
  ∫ y in (-a)..a, ((suzukiNeumannSplitProfile a y : ℝ) : ℂ) * u y

/-- **On mean-zero data the two operators differ by a constant.** -/
theorem intervalIntegral_neumannGreenKernel_mul_eq {a : ℝ} {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a)
    (hmean : (∫ y in (-a)..a, u y) = 0) (x : ℝ) :
    (∫ y in (-a)..a, ((suzukiNeumannGreenKernel a x y : ℝ) : ℂ) * u y)
      = (∫ y in (-a)..a, ((suzukiPrefixGramKernel a x y : ℝ) : ℂ) * u y)
          + suzukiNeumannSplitConstant a u := by
  have hdecomp : ∀ y : ℝ,
      ((suzukiNeumannGreenKernel a x y : ℝ) : ℂ) * u y
        = ((suzukiPrefixGramKernel a x y : ℝ) : ℂ) * u y
            + (((suzukiNeumannSplitProfile a x : ℝ) : ℂ) * u y
              + ((suzukiNeumannSplitProfile a y : ℝ) : ℂ) * u y) := by
    intro y
    have h := suzukiNeumannGreenKernel_sub_prefixGramKernel a x y
    have h' : suzukiNeumannGreenKernel a x y
        = suzukiPrefixGramKernel a x y
            + (suzukiNeumannSplitProfile a x + suzukiNeumannSplitProfile a y) := by linarith
    rw [h']
    push_cast
    ring
  simp only [hdecomp]
  rw [intervalIntegral.integral_add (intervalIntegrable_prefixGramKernel_mul x hu)
      ((hu.const_mul _).add (intervalIntegrable_splitProfile_mul hu)),
    intervalIntegral.integral_add (hu.const_mul _) (intervalIntegrable_splitProfile_mul hu),
    intervalIntegral.integral_const_mul, hmean]
  simp [suzukiNeumannSplitConstant]

/-- **Equality of the two quadratic forms on mean-zero data.**  The Neumann Green kernel and the
prefix Gram kernel induce the same quadratic form on `L_0^2(-a,a)`. -/
theorem intervalIntegral_neumannGreen_form_eq_prefixGram_form {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a)
    (hmean : (∫ y in (-a)..a, u y) = 0) :
    (∫ x in (-a)..a,
        (∫ y in (-a)..a, ((suzukiNeumannGreenKernel a x y : ℝ) : ℂ) * u y) * conj (u x))
      = ∫ x in (-a)..a,
          (∫ y in (-a)..a, ((suzukiPrefixGramKernel a x y : ℝ) : ℂ) * u y) * conj (u x) := by
  have hle : (-a : ℝ) ≤ a := by linarith
  have hGram : IntervalIntegrable
      (fun x => (∫ y in (-a)..a, ((suzukiPrefixGramKernel a x y : ℝ) : ℂ) * u y) * conj (u x))
      volume (-a) a :=
    (intervalIntegrable_conj hu).continuousOn_mul (continuousOn_prefixGram_operator ha hu)
  have hstep : ∀ x : ℝ,
      (∫ y in (-a)..a, ((suzukiNeumannGreenKernel a x y : ℝ) : ℂ) * u y) * conj (u x)
        = (∫ y in (-a)..a, ((suzukiPrefixGramKernel a x y : ℝ) : ℂ) * u y) * conj (u x)
            + suzukiNeumannSplitConstant a u * conj (u x) := by
    intro x
    rw [intervalIntegral_neumannGreenKernel_mul_eq hu hmean x, add_mul]
  simp only [hstep]
  rw [intervalIntegral.integral_add hGram ((intervalIntegrable_conj hu).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral_conj, hmean]
  simp

/-- **Suzuki, equation (8.2).**  For `u = Dv` mean-zero on `(-a,a)`, the `L²` mass of the
Dirichlet primitive `v` is the quadratic form of the inverse Neumann Laplacian:

`‖v‖_{L²}² = ⟨K̃_a u, u⟩ = ⟨(-Δ_N)^{-1} u, u⟩`. -/
theorem suzuki_equation_802 {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a)
    (hmean : (∫ y in (-a)..a, u y) = 0) :
    (∫ t in (-a)..a, suzukiPrefixPrimitive a u t * conj (suzukiPrefixPrimitive a u t))
      = ∫ x in (-a)..a,
          (∫ y in (-a)..a, ((suzukiNeumannGreenKernel a x y : ℝ) : ℂ) * u y) * conj (u x) := by
  rw [intervalIntegral_neumannGreen_form_eq_prefixGram_form ha hu hmean,
    intervalIntegral_prefixGram_form_eq_primitive_energy ha hu]

/-! ## Positivity of the form -/

/-- The inverse Neumann Laplacian form of mean-zero data is the (nonnegative real) `L²` mass of
the Dirichlet primitive. -/
theorem suzuki_neumannGreen_form_eq_ofReal {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a)
    (hmean : (∫ y in (-a)..a, u y) = 0) :
    (∫ x in (-a)..a,
        (∫ y in (-a)..a, ((suzukiNeumannGreenKernel a x y : ℝ) : ℂ) * u y) * conj (u x))
      = ((∫ t in (-a)..a, ‖suzukiPrefixPrimitive a u t‖ ^ 2 : ℝ) : ℂ) := by
  rw [← suzuki_equation_802 ha hu hmean, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr ?_
  intro t _
  dsimp only
  rw [Complex.mul_conj]
  norm_cast
  simp [Complex.normSq_eq_norm_sq]

/-- **The inverse Neumann Laplacian is a positive operator on mean-zero data.** -/
theorem suzuki_neumannGreen_form_nonneg {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a)
    (hmean : (∫ y in (-a)..a, u y) = 0) :
    0 ≤ (∫ x in (-a)..a,
        (∫ y in (-a)..a, ((suzukiNeumannGreenKernel a x y : ℝ) : ℂ) * u y) * conj (u x)).re := by
  rw [suzuki_neumannGreen_form_eq_ofReal ha hu hmean, Complex.ofReal_re]
  exact intervalIntegral.integral_nonneg (by linarith) fun t _ => by positivity

/-! ## Every slice of the Neumann Green kernel has vanishing mean -/

theorem intervalIntegral_abs_sub {a x : ℝ} (hx : x ∈ Icc (-a) a) :
    (∫ y in (-a)..a, |x - y|) = ((x + a) ^ 2 + (a - x) ^ 2) / 2 := by
  obtain ⟨hx1, hx2⟩ := hx
  have hlow : (∫ y in (-a)..x, |x - y|) = (x + a) ^ 2 / 2 := by
    rw [show (∫ y in (-a)..x, |x - y|) = ∫ y in (-a)..x, (x - y) from
      intervalIntegral.integral_congr (fun y hy => by
        rw [uIcc_of_le hx1] at hy
        exact abs_of_nonneg (by linarith [hy.2]))]
    simp only [intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_id), intervalIntegral.integral_const,
      _root_.integral_id, smul_eq_mul]
    ring
  have hup : (∫ y in x..a, |x - y|) = (a - x) ^ 2 / 2 := by
    rw [show (∫ y in x..a, |x - y|) = ∫ y in x..a, (y - x) from
      intervalIntegral.integral_congr (fun y hy => by
        rw [uIcc_of_le hx2] at hy
        rw [abs_sub_comm]
        exact abs_of_nonneg (by linarith [hy.1]))]
    simp only [intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_id)
      intervalIntegrable_const, intervalIntegral.integral_const,
      _root_.integral_id, smul_eq_mul]
    ring
  have hI1 : IntervalIntegrable (fun y => |x - y|) volume (-a) x :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hI2 : IntervalIntegrable (fun y => |x - y|) volume x a :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, hlow, hup]
  ring

/-- **Each slice of the Neumann Green kernel has vanishing mean.**  The constant `a/6` is
exactly what makes `∫_{-a}^a N(x,y) dy = 0`, so the operator annihilates constants and, by
symmetry of `N`, maps `L^2(-a,a)` into the mean-zero subspace. -/
theorem intervalIntegral_suzukiNeumannGreenKernel_right {a : ℝ} (ha : 0 < a) {x : ℝ}
    (hx : x ∈ Icc (-a) a) :
    (∫ y in (-a)..a, suzukiNeumannGreenKernel a x y) = 0 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hne : (4 : ℝ) * a ≠ 0 := by positivity
  have hsq : IntervalIntegrable (fun y : ℝ => y ^ 2) volume (-a) a :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have habs : IntervalIntegrable (fun y : ℝ => |x - y|) volume (-a) a :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hsplit : ∀ y : ℝ,
      suzukiNeumannGreenKernel a x y
        = (x ^ 2 / (4 * a) + a / 6) + (y ^ 2 / (4 * a) - |x - y| / 2) := by
    intro y
    unfold suzukiNeumannGreenKernel
    field_simp
    ring
  have hsqval : (∫ y in (-a)..a, y ^ 2) = 2 * a ^ 3 / 3 := by
    rw [integral_pow]
    norm_num
    ring
  simp only [hsplit]
  rw [intervalIntegral.integral_add intervalIntegrable_const
      ((hsq.div_const _).sub (habs.div_const _)),
    intervalIntegral.integral_sub (hsq.div_const _) (habs.div_const _),
    intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_const, hsqval, intervalIntegral_abs_sub hx]
  field_simp
  ring_nf
  field_simp
  ring

/-! ## The Neumann Green operator solves `-w'' = u` with Neumann boundary conditions -/

/-- The integral operator `(-Δ_N)^{-1}` with the Neumann Green kernel. -/
def suzukiNeumannGreenOperator (a : ℝ) (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in (-a)..a, ((suzukiNeumannGreenKernel a x y : ℝ) : ℂ) * u y

/-- On the aperture, the Neumann Green operator is a constant plus the upper tail integral of the
Dirichlet primitive. -/
theorem suzukiNeumannGreenOperator_eq_tail {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a)
    (hmean : (∫ y in (-a)..a, u y) = 0) {x : ℝ} (hx : x ∈ Icc (-a) a) :
    suzukiNeumannGreenOperator a u x
      = suzukiNeumannSplitConstant a u + ∫ t in x..a, suzukiPrefixPrimitive a u t := by
  rw [suzukiNeumannGreenOperator, intervalIntegral_neumannGreenKernel_mul_eq hu hmean x,
    intervalIntegral_prefixGramKernel_mul ha hu hx, add_comm]

/-- **First derivative of the inverse Neumann Laplacian.**  On mean-zero data,
`(K_a u)'(x) = -v(x)` at every interior point, where `v` is the Dirichlet primitive of `u`. -/
theorem hasDerivAt_suzukiNeumannGreenOperator {a : ℝ} (ha : 0 < a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a)
    (hmean : (∫ y in (-a)..a, u y) = 0) {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (suzukiNeumannGreenOperator a u) (-(suzukiPrefixPrimitive a u x)) x := by
  have hle : (-a : ℝ) ≤ a := by linarith
  have hIcc : Icc (-a) a ∈ nhds x := Icc_mem_nhds hx.1 hx.2
  have hcontOn : ContinuousOn (suzukiPrefixPrimitive a u) (Icc (-a) a) := by
    have h := continuousOn_suzukiPrefixPrimitive ha.le hu
    rwa [uIcc_of_le hle] at h
  have hcontAt : ContinuousAt (suzukiPrefixPrimitive a u) x := hcontOn.continuousAt hIcc
  have hmeasAt : StronglyMeasurableAtFilter (suzukiPrefixPrimitive a u) (nhds x) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hcontOn.mono Ioo_subset_Icc_self) x hx
  have hII : IntervalIntegrable (suzukiPrefixPrimitive a u) volume x a :=
    (intervalIntegrable_suzukiPrefixPrimitive ha.le hu).mono_set
      (by rw [uIcc_of_le hx.2.le, uIcc_of_le hle]; exact Icc_subset_Icc hx.1.le le_rfl)
  have htail : HasDerivAt (fun p => ∫ t in p..a, suzukiPrefixPrimitive a u t)
      (-(suzukiPrefixPrimitive a u x)) x :=
    intervalIntegral.integral_hasDerivAt_left hII hmeasAt hcontAt
  have heq : suzukiNeumannGreenOperator a u =ᶠ[nhds x]
      fun p => suzukiNeumannSplitConstant a u + ∫ t in p..a, suzukiPrefixPrimitive a u t := by
    filter_upwards [hIcc] with p hp
    exact suzukiNeumannGreenOperator_eq_tail ha.le hu hmean hp
  exact (htail.const_add _).congr_of_eventuallyEq heq

theorem deriv_suzukiNeumannGreenOperator {a : ℝ} (ha : 0 < a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a)
    (hmean : (∫ y in (-a)..a, u y) = 0) {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    deriv (suzukiNeumannGreenOperator a u) x = -(suzukiPrefixPrimitive a u x) :=
  (hasDerivAt_suzukiNeumannGreenOperator ha hu hmean hx).deriv

/-- **The Neumann boundary condition at the left endpoint.** -/
theorem tendsto_deriv_suzukiNeumannGreenOperator_left {a : ℝ} (ha : 0 < a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a)
    (hmean : (∫ y in (-a)..a, u y) = 0) :
    Filter.Tendsto (deriv (suzukiNeumannGreenOperator a u))
      (nhdsWithin (-a) (Ioo (-a) a)) (nhds 0) := by
  have hle : (-a : ℝ) ≤ a := by linarith
  have hcontOn : ContinuousOn (suzukiPrefixPrimitive a u) (Icc (-a) a) := by
    have h := continuousOn_suzukiPrefixPrimitive ha.le hu
    rwa [uIcc_of_le hle] at h
  have hwithin : ContinuousWithinAt (suzukiPrefixPrimitive a u) (Ioo (-a) a) (-a) :=
    (hcontOn (-a) (left_mem_Icc.mpr hle)).mono Ioo_subset_Icc_self
  have hlim : Filter.Tendsto (fun x => -(suzukiPrefixPrimitive a u x))
      (nhdsWithin (-a) (Ioo (-a) a)) (nhds 0) := by
    have := hwithin.tendsto.neg
    rwa [suzukiPrefixPrimitive_left, neg_zero] at this
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (deriv_suzukiNeumannGreenOperator ha hu hmean hx).symm

/-- **The Neumann boundary condition at the right endpoint.** -/
theorem tendsto_deriv_suzukiNeumannGreenOperator_right {a : ℝ} (ha : 0 < a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a)
    (hmean : (∫ y in (-a)..a, u y) = 0) :
    Filter.Tendsto (deriv (suzukiNeumannGreenOperator a u))
      (nhdsWithin a (Ioo (-a) a)) (nhds 0) := by
  have hle : (-a : ℝ) ≤ a := by linarith
  have hcontOn : ContinuousOn (suzukiPrefixPrimitive a u) (Icc (-a) a) := by
    have h := continuousOn_suzukiPrefixPrimitive ha.le hu
    rwa [uIcc_of_le hle] at h
  have hwithin : ContinuousWithinAt (suzukiPrefixPrimitive a u) (Ioo (-a) a) a :=
    (hcontOn a (right_mem_Icc.mpr hle)).mono Ioo_subset_Icc_self
  have hlim : Filter.Tendsto (fun x => -(suzukiPrefixPrimitive a u x))
      (nhdsWithin a (Ioo (-a) a)) (nhds 0) := by
    have := hwithin.tendsto.neg
    rwa [suzukiPrefixPrimitive_right a u hmean, neg_zero] at this
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (deriv_suzukiNeumannGreenOperator ha hu hmean hx).symm

/-- **Second derivative of the inverse Neumann Laplacian.**  At every interior point where the
mean-zero datum is continuous, `(K_a u)'' = -u`; together with the two boundary limits this is the
statement that `K_a` inverts the Neumann Laplacian `-Δ_N`. -/
theorem hasDerivAt_deriv_suzukiNeumannGreenOperator {a : ℝ} (ha : 0 < a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a)
    (hmean : (∫ y in (-a)..a, u y) = 0) {x : ℝ} (hx : x ∈ Ioo (-a) a)
    (hcont : ContinuousAt u x) :
    HasDerivAt (deriv (suzukiNeumannGreenOperator a u)) (-(u x)) x := by
  have hle : (-a : ℝ) ≤ a := by linarith
  have hII : IntervalIntegrable u volume (-a) x :=
    hu.mono_set (by rw [uIcc_of_le hx.1.le, uIcc_of_le hle]; exact Icc_subset_Icc le_rfl hx.2.le)
  have hmeasAt : StronglyMeasurableAtFilter u (nhds x) volume := by
    refine ⟨Ioo (-a) a, Ioo_mem_nhds hx.1 hx.2, ?_⟩
    exact hu.1.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl)
  have hprim : HasDerivAt (suzukiPrefixPrimitive a u) (u x) x :=
    intervalIntegral.integral_hasDerivAt_right hII hmeasAt hcont
  have heq : deriv (suzukiNeumannGreenOperator a u)
      =ᶠ[nhds x] fun p => -(suzukiPrefixPrimitive a u p) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with p hp
    exact deriv_suzukiNeumannGreenOperator ha hu hmean hp
  exact hprim.neg.congr_of_eventuallyEq heq

/-! ## The inverse Neumann Laplacian preserves the mean-zero subspace -/

/-- The quadratic profile obtained by integrating `t ↦ t + a` from `s` to `a`. -/
def suzukiNeumannTailProfile (a s : ℝ) : ℝ := (3 * a ^ 2 - 2 * a * s - s ^ 2) / 2

theorem intervalIntegral_linear_tail (a s : ℝ) :
    (∫ t in s..a, ((t + a : ℝ) : ℂ)) = ((suzukiNeumannTailProfile a s : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_ofReal]
  congr 1
  rw [intervalIntegral.integral_add intervalIntegral.intervalIntegrable_id
      intervalIntegrable_const, _root_.integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul, suzukiNeumannTailProfile]
  ring

theorem suzukiNeumannSplitProfile_tail_identity {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    2 * a * suzukiNeumannSplitProfile a y + suzukiNeumannTailProfile a y = 2 * a ^ 2 / 3 := by
  unfold suzukiNeumannSplitProfile suzukiNeumannTailProfile
  field_simp
  ring

/-- **The inverse Neumann Laplacian maps `L_0^2(-a,a)` into itself.** -/
theorem intervalIntegral_suzukiNeumannGreenOperator_eq_zero {a : ℝ} (ha : 0 < a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a) (hmean : (∫ y in (-a)..a, u y) = 0) :
    (∫ x in (-a)..a, suzukiNeumannGreenOperator a u x) = 0 := by
  have hle : (-a : ℝ) ≤ a := by linarith
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hv := intervalIntegrable_suzukiPrefixPrimitive ha.le hu
  have hlin : IntervalIntegrable (fun t : ℝ => ((t + a : ℝ) : ℂ)) volume (-a) a :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hprofile : IntervalIntegrable
      (fun y => ((suzukiNeumannTailProfile a y : ℝ) : ℂ) * u y) volume (-a) a := by
    refine hu.continuousOn_mul (Complex.continuous_ofReal.comp ?_).continuousOn
    unfold suzukiNeumannTailProfile
    fun_prop
  have hsplitMul : IntervalIntegrable
      (fun y => ((2 * a * suzukiNeumannSplitProfile a y : ℝ) : ℂ) * u y) volume (-a) a := by
    refine hu.continuousOn_mul (Complex.continuous_ofReal.comp ?_).continuousOn
    unfold suzukiNeumannSplitProfile
    fun_prop
  have h1 : (∫ x in (-a)..a, suzukiNeumannGreenOperator a u x)
      = ∫ x in (-a)..a,
          (suzukiNeumannSplitConstant a u + ∫ t in x..a, suzukiPrefixPrimitive a u t) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [uIcc_of_le hle] at hx
    exact suzukiNeumannGreenOperator_eq_tail ha.le hu hmean hx
  have h2 : (∫ x in (-a)..a, ∫ t in x..a, suzukiPrefixPrimitive a u t)
      = ∫ t in (-a)..a, ((t + a : ℝ) : ℂ) * suzukiPrefixPrimitive a u t := by
    have hswap := intervalIntegral_triangle_swap hle (F := fun _ : ℝ => (1 : ℂ))
      (G := suzukiPrefixPrimitive a u) intervalIntegrable_const hv
    simp only [one_mul] at hswap
    rw [hswap]
    refine intervalIntegral.integral_congr ?_
    intro t _
    dsimp only
    rw [intervalIntegral.integral_const, Complex.real_smul]
    push_cast
    ring
  have h3 : (∫ t in (-a)..a, ((t + a : ℝ) : ℂ) * suzukiPrefixPrimitive a u t)
      = ∫ s in (-a)..a, ((suzukiNeumannTailProfile a s : ℝ) : ℂ) * u s := by
    have hswap := intervalIntegral_triangle_swap hle (F := u)
      (G := fun t : ℝ => ((t + a : ℝ) : ℂ)) hu hlin
    simp only [intervalIntegral_linear_tail] at hswap
    rw [show (∫ t in (-a)..a, ((t + a : ℝ) : ℂ) * suzukiPrefixPrimitive a u t)
        = ∫ t in (-a)..a, (∫ s in (-a)..t, u s) * ((t + a : ℝ) : ℂ) from
      intervalIntegral.integral_congr (fun t _ => mul_comm _ _)]
    rw [← hswap]
    exact intervalIntegral.integral_congr (fun s _ => mul_comm _ _)
  have hconst : (a - -a) • suzukiNeumannSplitConstant a u
      = ∫ y in (-a)..a, ((2 * a * suzukiNeumannSplitProfile a y : ℝ) : ℂ) * u y := by
    rw [suzukiNeumannSplitConstant, ← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    rw [Complex.real_smul]
    push_cast
    ring
  rw [h1, intervalIntegral.integral_add intervalIntegrable_const
      (intervalIntegrable_tail_suzukiPrefixPrimitive ha.le hu),
    intervalIntegral.integral_const, hconst, h2, h3,
    ← intervalIntegral.integral_add hsplitMul hprofile]
  rw [show (∫ y in (-a)..a,
      (((2 * a * suzukiNeumannSplitProfile a y : ℝ) : ℂ) * u y
        + ((suzukiNeumannTailProfile a y : ℝ) : ℂ) * u y))
      = ∫ y in (-a)..a, ((2 * a ^ 2 / 3 : ℝ) : ℂ) * u y from by
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    rw [← add_mul, ← Complex.ofReal_add, suzukiNeumannSplitProfile_tail_identity ha0 y]]
  rw [intervalIntegral.integral_const_mul, hmean, mul_zero]


/-! ## `D : H_0^1(-a,a) → L_0^2(-a,a)` is a bijection -/

/-- **Surjectivity.**  Every mean-zero datum is the derivative of a function vanishing at both
endpoints, namely its own prefix primitive. -/
theorem suzukiPrefixPrimitive_hasDerivAt_and_vanishes {a : ℝ} (ha : 0 < a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a)
    (hmean : (∫ y in (-a)..a, u y) = 0) :
    suzukiPrefixPrimitive a u (-a) = 0 ∧ suzukiPrefixPrimitive a u a = 0 ∧
      ∀ x ∈ Ioo (-a) a, ContinuousAt u x →
        HasDerivAt (suzukiPrefixPrimitive a u) (u x) x := by
  refine ⟨suzukiPrefixPrimitive_left a u, suzukiPrefixPrimitive_right a u hmean, ?_⟩
  intro x hx hcont
  have hle : (-a : ℝ) ≤ a := by linarith
  have hII : IntervalIntegrable u volume (-a) x :=
    hu.mono_set (by rw [uIcc_of_le hx.1.le, uIcc_of_le hle]; exact Icc_subset_Icc le_rfl hx.2.le)
  have hmeasAt : StronglyMeasurableAtFilter u (nhds x) volume := by
    refine ⟨Ioo (-a) a, Ioo_mem_nhds hx.1 hx.2, ?_⟩
    exact hu.1.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl)
  exact intervalIntegral.integral_hasDerivAt_right hII hmeasAt hcont

/-- **The range of `D` lies in the mean-zero space.**  If `v` vanishes at both endpoints and has
derivative `u` on the aperture, then `u` has vanishing mean. -/
theorem intervalIntegral_eq_zero_of_dirichlet {a : ℝ} {v u : ℝ → ℂ}
    (hderiv : ∀ x ∈ uIcc (-a) a, HasDerivAt v (u x) x)
    (hu : IntervalIntegrable u volume (-a) a)
    (hleft : v (-a) = 0) (hright : v a = 0) :
    (∫ y in (-a)..a, u y) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hu, hleft, hright, sub_zero]


/-! ## The generalized eigenvalue reformulation -/

/-- The quadratic form of the inverse Neumann Laplacian. -/
def suzukiNeumannGreenForm (a : ℝ) (u : ℝ → ℂ) : ℂ :=
  ∫ x in (-a)..a, suzukiNeumannGreenOperator a u x * conj (u x)

theorem suzukiNeumannGreenForm_eq_primitive_energy {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a)
    (hmean : (∫ y in (-a)..a, u y) = 0) :
    suzukiNeumannGreenForm a u
      = ((∫ t in (-a)..a, ‖suzukiPrefixPrimitive a u t‖ ^ 2 : ℝ) : ℂ) :=
  suzuki_neumannGreen_form_eq_ofReal ha hu hmean

/-- **Suzuki, equation (8.4).**  For `u = Dv` mean-zero, the Rayleigh quotient of any localized
Weil-form value over the `L²` mass of the Dirichlet primitive `v` is the generalized Rayleigh
quotient of that value against the inverse Neumann Laplacian.  Combined with
`⟨G_a u, u⟩ = Q_W^a(v)`, this is Suzuki's reformulation of the spectral problem for `A_a` as the
generalized eigenvalue problem `G_a u = λ K_a u`. -/
theorem suzuki_equation_804 {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume (-a) a)
    (hmean : (∫ y in (-a)..a, u y) = 0) (Q : ℂ) :
    Q / ((∫ t in (-a)..a, ‖suzukiPrefixPrimitive a u t‖ ^ 2 : ℝ) : ℂ)
      = Q / suzukiNeumannGreenForm a u := by
  rw [suzukiNeumannGreenForm_eq_primitive_energy ha hu hmean]

end RHTower

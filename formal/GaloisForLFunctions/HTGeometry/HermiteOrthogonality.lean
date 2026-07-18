import GaloisForLFunctions.HTGeometry.HermiteFourierEigen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Module

/-!
# Orthogonality of the Hermite functions

The Hermite functions are pairwise orthogonal in `L²(ℝ)`.  The proof here is the oscillator
argument, carried out entirely with the creation and annihilation operators

```text
A = 2π M − D,        B = 2π M + D,        M f = x·f,   D f = f',
```

and needs no explicit Gaussian integral.  Three facts drive it:

* **Adjointness.**  For the bilinear pairing `⟨f, g⟩ = ∫ f·g`, integration by parts on the line
  gives `⟨A f, g⟩ = ⟨f, B g⟩`; the boundary terms vanish because Schwartz functions decay.
* **The commutator.**  `B A − A B = 4π`, which is `[D, M] = 1` in disguise.
* **The vacuum.**  `B` annihilates the Gaussian, since `(2πx + d/dx) e^{−πx²} = 0`.

From the last two, induction gives the lowering relation `B h_{n+1} = 2(n+1) h_n`, and then
adjointness turns `⟨h_m, h_n⟩` with `m > n` into a multiple of `⟨h_{m−1}, h_{n−1}⟩`, which
descends to `⟨h_{m−n}, h_0⟩ = 0`.

Because the Hermite functions are real-valued, the bilinear pairing agrees with the `L²` inner
product on them, so the orthogonality transfers verbatim to `L²`.  Together with the Fourier
eigenrelation this makes the Hermite family an orthogonal system of Fourier eigenvectors — the
input a variational trial-space argument needs.
-/

open scoped Real FourierTransform SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## Pointwise products and the bilinear pairing -/

/-- The pointwise product of two Schwartz functions, again a Schwartz function. -/
def mulS (f g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) := SchwartzMap.smulLeftCLM ℂ (f : ℝ → ℂ) g

@[simp] theorem mulS_apply (f g : 𝓢(ℝ, ℂ)) (x : ℝ) : mulS f g x = f x * g x := by
  rw [mulS, SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth, smul_eq_mul]

theorem mulS_comm (f g : 𝓢(ℝ, ℂ)) : mulS f g = mulS g f := by
  apply SchwartzMap.ext
  intro x
  rw [mulS_apply, mulS_apply, mul_comm]

theorem mulS_smul_right (c : ℂ) (f g : 𝓢(ℝ, ℂ)) : mulS f (c • g) = c • mulS f g :=
  map_smul _ _ _

/-- The bilinear pairing `⟨f, g⟩ = ∫ f·g`, with no complex conjugation. -/
def schwartzPair (f g : 𝓢(ℝ, ℂ)) : ℂ := SchwartzMap.integralCLM ℂ volume (mulS f g)

theorem schwartzPair_def (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair f g = SchwartzMap.integralCLM ℂ volume (mulS f g) := rfl

theorem schwartzPair_eq_integral (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair f g = ∫ x : ℝ, f x * g x := by
  rw [schwartzPair_def, SchwartzMap.integralCLM_apply]
  simp only [mulS_apply]

theorem schwartzPair_comm (f g : 𝓢(ℝ, ℂ)) : schwartzPair f g = schwartzPair g f := by
  rw [schwartzPair_def, schwartzPair_def, mulS_comm]

theorem schwartzPair_smul_right (c : ℂ) (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair f (c • g) = c * schwartzPair f g := by
  rw [schwartzPair_def, mulS_smul_right, map_smul, schwartzPair_def, smul_eq_mul]

theorem schwartzPair_zero_right (f : 𝓢(ℝ, ℂ)) : schwartzPair f 0 = 0 := by
  rw [schwartzPair_def, show mulS f 0 = 0 from map_zero _, map_zero]

/-! ## The annihilation operator -/

/-- The **annihilation operator** `B f = 2πx·f + f'`. -/
def annihilationCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := (2 * (π : ℂ)) • mulXCLM + derivSCLM

theorem annihilationCLM_eq (f : 𝓢(ℝ, ℂ)) :
    annihilationCLM f = (2 * (π : ℂ)) • mulXCLM f + derivSCLM f := rfl

@[simp] theorem annihilationCLM_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    annihilationCLM f x = 2 * (π : ℂ) * (x : ℂ) * f x + deriv (f : ℝ → ℂ) x := by
  rw [annihilationCLM_eq]
  simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, mulXCLM_apply, derivSCLM_apply,
    smul_eq_mul]
  ring

/-! ## The three structural facts -/

/-- **The commutator of differentiation and coordinate multiplication is the identity.** -/
theorem derivSCLM_mulXCLM (f : 𝓢(ℝ, ℂ)) :
    derivSCLM (mulXCLM f) = f + mulXCLM (derivSCLM f) := by
  apply SchwartzMap.ext
  intro x
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  have h2 := f.hasDerivAt x
  have h3 : HasDerivAt (fun y : ℝ => (y : ℂ) * f y)
      (1 * f x + (x : ℂ) * deriv (f : ℝ → ℂ) x) x := h1.mul h2
  rw [derivSCLM_apply, coe_mulXCLM, h3.deriv, SchwartzMap.add_apply, mulXCLM_apply,
    derivSCLM_apply]
  ring

/-- **The oscillator commutation relation** `B A − A B = 4π`. -/
theorem annihilationCLM_creationCLM_sub (f : 𝓢(ℝ, ℂ)) :
    annihilationCLM (creationCLM f) - creationCLM (annihilationCLM f) = (4 * (π : ℂ)) • f := by
  rw [annihilationCLM_eq, creationCLM_eq, creationCLM_eq (annihilationCLM f), annihilationCLM_eq]
  simp only [map_sub, map_add, map_smul, derivSCLM_mulXCLM]
  module

/-- **The annihilation operator kills the Gaussian.** -/
theorem annihilationCLM_gaussianSchwartz : annihilationCLM gaussianSchwartz = 0 := by
  apply SchwartzMap.ext
  intro x
  have hr : HasDerivAt (fun y : ℝ => ((gaussReal y : ℝ) : ℂ))
      (((-(2 * π * x) * gaussReal x : ℝ) : ℂ)) x := (hasDerivAt_gaussReal x).ofReal_comp
  have hc : deriv (gaussianSchwartz : ℝ → ℂ) x = ((-(2 * π * x) * gaussReal x : ℝ) : ℂ) := hr.deriv
  rw [annihilationCLM_apply, hc, SchwartzMap.zero_apply, gaussianSchwartz_apply]
  push_cast
  ring

theorem annihilationCLM_hermiteSchwartz_zero : annihilationCLM (hermiteSchwartz 0) = 0 := by
  rw [hermiteSchwartz_zero]
  exact annihilationCLM_gaussianSchwartz

/-! ## The lowering relation -/

theorem two_pi_ne_zero : (2 * (π : ℂ)) ≠ 0 := by
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero, false_or]
  exact Real.pi_ne_zero

/-- The creation operator raises the Hermite index, up to the normalizing scalar. -/
theorem creationCLM_hermiteSchwartz (n : ℕ) :
    creationCLM (hermiteSchwartz n) = (2 * (π : ℂ)) • hermiteSchwartz (n + 1) := by
  rw [hermiteSchwartz_succ_eq, smul_smul, mul_inv_cancel₀ two_pi_ne_zero, one_smul]

/-- Commuting `B` past one application of `A` on a Hermite function. -/
theorem annihilationCLM_hermiteSchwartz_succ_eq (n : ℕ) :
    annihilationCLM (hermiteSchwartz (n + 1))
      = (2 * (π : ℂ))⁻¹ • (creationCLM (annihilationCLM (hermiteSchwartz n))
          + (4 * (π : ℂ)) • hermiteSchwartz n) := by
  rw [hermiteSchwartz_succ_eq, map_smul]
  congr 1
  have h := annihilationCLM_creationCLM_sub (hermiteSchwartz n)
  rw [sub_eq_iff_eq_add] at h
  rw [h, add_comm]

/-- **The annihilation operator lowers the Hermite index:** `B h_{n+1} = 2(n+1) h_n`. -/
theorem annihilationCLM_hermiteSchwartz (n : ℕ) :
    annihilationCLM (hermiteSchwartz (n + 1)) = (2 * ((n : ℂ) + 1)) • hermiteSchwartz n := by
  induction n with
  | zero =>
    rw [annihilationCLM_hermiteSchwartz_succ_eq, annihilationCLM_hermiteSchwartz_zero, map_zero,
      zero_add, smul_smul]
    congr 1
    field_simp
    norm_num
  | succ n ih =>
    rw [annihilationCLM_hermiteSchwartz_succ_eq, ih, map_smul, creationCLM_hermiteSchwartz,
      smul_smul, ← add_smul, smul_smul]
    congr 1
    push_cast
    field_simp
    ring

/-! ## Adjointness and orthogonality -/

/-- **Adjointness of the creation and annihilation operators** for the bilinear pairing.  This is
integration by parts; the boundary terms vanish by Schwartz decay. -/
theorem schwartzPair_creationCLM (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair (creationCLM f) g = schwartzPair f (annihilationCLM g) := by
  have hkey : mulS (creationCLM f) g
      = mulS f (annihilationCLM g) - (mulS (derivSCLM f) g + mulS f (derivSCLM g)) := by
    apply SchwartzMap.ext
    intro x
    simp only [mulS_apply, creationCLM_apply, annihilationCLM_apply, SchwartzMap.sub_apply,
      SchwartzMap.add_apply, derivSCLM_apply]
    ring
  have h1 : schwartzPair (derivSCLM f) g = ∫ x : ℝ, deriv (f : ℝ → ℂ) x * g x := by
    rw [schwartzPair_eq_integral]
    simp only [derivSCLM_apply]
  have h2 : schwartzPair f (derivSCLM g) = ∫ x : ℝ, f x * deriv (g : ℝ → ℂ) x := by
    rw [schwartzPair_eq_integral]
    simp only [derivSCLM_apply]
  have hibp : ∫ x : ℝ, f x * deriv (g : ℝ → ℂ) x = -∫ x : ℝ, deriv (f : ℝ → ℂ) x * g x :=
    SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul f g
  rw [schwartzPair_def, hkey, map_sub, map_add, ← schwartzPair_def, ← schwartzPair_def,
    ← schwartzPair_def, h1, h2, hibp]
  ring

/-- **The Hermite functions are pairwise orthogonal for the bilinear pairing**, in the form that
the index gap is positive. -/
theorem schwartzPair_hermiteSchwartz_gap (k : ℕ) :
    ∀ n : ℕ, schwartzPair (hermiteSchwartz (n + k + 1)) (hermiteSchwartz n) = 0 := by
  intro n
  induction n with
  | zero =>
    have hraise : hermiteSchwartz (0 + k + 1)
        = (2 * (π : ℂ))⁻¹ • creationCLM (hermiteSchwartz (0 + k)) := hermiteSchwartz_succ_eq _
    rw [hraise, schwartzPair_comm, schwartzPair_smul_right, schwartzPair_comm,
      schwartzPair_creationCLM, annihilationCLM_hermiteSchwartz_zero, schwartzPair_zero_right,
      mul_zero]
  | succ n ih =>
    have hraise : hermiteSchwartz (n + 1 + k + 1)
        = (2 * (π : ℂ))⁻¹ • creationCLM (hermiteSchwartz (n + 1 + k)) := hermiteSchwartz_succ_eq _
    have hindex : n + 1 + k = n + k + 1 := by omega
    rw [hraise, schwartzPair_comm, schwartzPair_smul_right, schwartzPair_comm,
      schwartzPair_creationCLM, annihilationCLM_hermiteSchwartz, schwartzPair_smul_right,
      hindex, ih, mul_zero, mul_zero]

/-- **Orthogonality of the Hermite functions for the bilinear pairing.** -/
theorem schwartzPair_hermiteSchwartz_eq_zero {m n : ℕ} (h : m ≠ n) :
    schwartzPair (hermiteSchwartz m) (hermiteSchwartz n) = 0 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hk : n = m + (n - m - 1) + 1 := by omega
    rw [schwartzPair_comm, hk]
    exact schwartzPair_hermiteSchwartz_gap (n - m - 1) m
  · have hk : m = n + (m - n - 1) + 1 := by omega
    rw [hk]
    exact schwartzPair_hermiteSchwartz_gap (m - n - 1) n

/-! ## Transport to the `L²` inner product -/

/-- The Hermite functions are real-valued. -/
theorem conj_hermiteSchwartz (n : ℕ) (x : ℝ) :
    (starRingEnd ℂ) (hermiteSchwartz n x) = hermiteSchwartz n x := by
  rw [hermiteSchwartz_apply]
  exact Complex.conj_ofReal _

/-- On the Hermite family the `L²` inner product is the bilinear pairing, since the functions are
real-valued. -/
theorem inner_hermiteSchwartz_toLp (m n : ℕ) :
    inner ℂ ((hermiteSchwartz m).toLp 2 volume) ((hermiteSchwartz n).toLp 2 volume)
      = schwartzPair (hermiteSchwartz m) (hermiteSchwartz n) := by
  rw [MeasureTheory.L2.inner_def, schwartzPair_eq_integral]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [SchwartzMap.coeFn_toLp (hermiteSchwartz m) 2 volume,
    SchwartzMap.coeFn_toLp (hermiteSchwartz n) 2 volume] with x hx hy
  rw [hx, hy, RCLike.inner_apply, conj_hermiteSchwartz, mul_comm]

/-- **The Hermite functions are an orthogonal system in `L²(ℝ)`.**  With the Fourier eigenrelation
this exhibits an orthogonal family of Fourier eigenvectors. -/
theorem inner_hermiteSchwartz_toLp_eq_zero {m n : ℕ} (h : m ≠ n) :
    inner ℂ ((hermiteSchwartz m).toLp 2 volume) ((hermiteSchwartz n).toLp 2 volume) = 0 := by
  rw [inner_hermiteSchwartz_toLp]
  exact schwartzPair_hermiteSchwartz_eq_zero h

/-! ## Nonvanishing, and the orthonormal system -/

theorem schwartzPair_smul_left (c : ℂ) (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair (c • f) g = c * schwartzPair f g := by
  rw [schwartzPair_comm, schwartzPair_smul_right, schwartzPair_comm]

/-- The Gaussian's self-pairing is the Gauss integral of `e^{−2πx²}`. -/
theorem schwartzPair_gaussianSchwartz_self :
    schwartzPair gaussianSchwartz gaussianSchwartz = ((Real.sqrt (π / (2 * π)) : ℝ) : ℂ) := by
  rw [schwartzPair_eq_integral]
  have hfun : (fun x : ℝ => gaussianSchwartz x * gaussianSchwartz x)
      = fun x : ℝ => ((Real.exp (-(2 * π) * x ^ 2) : ℝ) : ℂ) := by
    funext x
    rw [gaussianSchwartz_apply]
    norm_cast
    unfold gaussReal
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun, integral_complex_ofReal, integral_gaussian]

theorem schwartzPair_gaussianSchwartz_self_ne_zero :
    schwartzPair gaussianSchwartz gaussianSchwartz ≠ 0 := by
  rw [schwartzPair_gaussianSchwartz_self]
  have h : (0 : ℝ) < Real.sqrt (π / (2 * π)) := by
    rw [Real.sqrt_pos]
    positivity
  exact Complex.ofReal_ne_zero.mpr h.ne'

theorem pi_ne_zero_complex : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

/-- The self-pairings satisfy the oscillator recursion `⟨h_{n+1}, h_{n+1}⟩ = ((n+1)/π)⟨h_n, h_n⟩`,
obtained by moving one creation operator across the pairing and lowering it back. -/
theorem schwartzPair_hermiteSchwartz_self_succ (n : ℕ) :
    schwartzPair (hermiteSchwartz (n + 1)) (hermiteSchwartz (n + 1))
      = ((n : ℂ) + 1) / (π : ℂ) * schwartzPair (hermiteSchwartz n) (hermiteSchwartz n) := by
  nth_rewrite 1 [hermiteSchwartz_succ_eq]
  rw [schwartzPair_smul_left, schwartzPair_creationCLM, annihilationCLM_hermiteSchwartz,
    schwartzPair_smul_right]
  field_simp

theorem schwartzPair_hermiteSchwartz_self_ne_zero (n : ℕ) :
    schwartzPair (hermiteSchwartz n) (hermiteSchwartz n) ≠ 0 := by
  induction n with
  | zero =>
    rw [hermiteSchwartz_zero]
    exact schwartzPair_gaussianSchwartz_self_ne_zero
  | succ n ih =>
    rw [schwartzPair_hermiteSchwartz_self_succ]
    refine mul_ne_zero (div_ne_zero ?_ pi_ne_zero_complex) ih
    have h : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    push_cast at h
    exact h

/-- No Hermite function vanishes in `L²`. -/
theorem hermiteSchwartz_toLp_ne_zero (n : ℕ) :
    (hermiteSchwartz n).toLp 2 volume ≠ 0 := by
  intro hzero
  have h := inner_hermiteSchwartz_toLp n n
  rw [hzero, inner_zero_left] at h
  exact schwartzPair_hermiteSchwartz_self_ne_zero n h.symm

/-- **The normalized Hermite functions are an orthonormal family in `L²(ℝ)`.**  Combined with
`fourier_hermiteSchwartz_toLp` this is an orthonormal family of eigenvectors of the `L²` Fourier
transform, the input a variational trial-space argument consumes. -/
theorem orthonormal_hermiteSchwartz_toLp :
    Orthonormal ℂ (fun n : ℕ =>
      ((‖(hermiteSchwartz n).toLp 2 volume‖ : ℂ))⁻¹ • (hermiteSchwartz n).toLp 2 volume) := by
  constructor
  · intro n
    exact norm_smul_inv_norm (hermiteSchwartz_toLp_ne_zero n)
  · intro m n hmn
    simp only [inner_smul_left, inner_smul_right, inner_hermiteSchwartz_toLp_eq_zero hmn,
      mul_zero]

end GaloisForLFunctions

end

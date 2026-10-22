import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The equivariant Tate exponential sequence and the rationalized Kummer class

On the suspension cover the exponential map carries the suspension parameter in its exponent:
`E_u(α) = exp(2πi α / u)`.  Its kernel is the lattice `uℤ`, which is the Tate local system, and it
is onto the invertible functions, so the exponential sequence is exact.  The factor `u⁻¹` is forced:
a family `exp(2πi c(u) α)` is invariant under the simultaneous scaling of the suspension parameter
and of the weight-one coefficient exactly when `c(u) = c(1)/u`.

Rationalizing the unit group makes the twist and the Frobenius power cancel: on `ℚ ⊗ M` the class
of `q • m` against the Tate fibre `q⁻¹` is the class of `m`.  The kernel of the rationalization is
exactly the torsion, so on a field the kernel of the rationalized Kummer class is exactly the roots
of unity.

* `deningerTateExp_eq_one_iff` : the kernel of the exponential is the Tate lattice `uℤ`.
* `deningerTateExp_surjective`, `deningerTateExp_exact` : the exponential sequence.
* `deningerTateWeight_forced` : the `u⁻¹` factor is forced by equivariance.
* `deningerRationalTwist_cancel` : Frobenius power and Tate twist cancel.
* `deningerRationalization_eq_zero_iff`, `deningerKummerKernel_isTorsion` : injectivity modulo
  torsion.
-/

namespace RHTower

open scoped TensorProduct

section ExponentialSequence

/-- The equivariant exponential of the suspension cover, with the forced `u⁻¹` in the exponent. -/
noncomputable def deningerTateExp (u : ℝ) (α : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * α / (u : ℂ))

theorem deningerTateExp_add (u : ℝ) (α β : ℂ) :
    deningerTateExp u (α + β) = deningerTateExp u α * deningerTateExp u β := by
  rw [deningerTateExp, deningerTateExp, deningerTateExp, ← Complex.exp_add]
  congr 1
  ring

theorem deningerTateExp_ne_zero (u : ℝ) (α : ℂ) : deningerTateExp u α ≠ 0 :=
  Complex.exp_ne_zero _

theorem deningerTwoPiI_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
  exact_mod_cast Real.pi_ne_zero

/-- **The kernel of the exponential is the Tate lattice.**  It is the lattice `uℤ`, which carries
the weight-one action of the positive rationals. -/
theorem deningerTateExp_eq_one_iff {u : ℝ} (hu : u ≠ 0) (α : ℂ) :
    deningerTateExp u α = 1 ↔ ∃ n : ℤ, α = (n : ℂ) * (u : ℂ) := by
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  rw [deningerTateExp, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [div_eq_iff hu'] at hn
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) * α
        = (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * (u : ℂ)) := by
      rw [hn]
      ring
    exact mul_left_cancel₀ deningerTwoPiI_ne_zero h2
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have hdiv : ((n : ℂ) * (u : ℂ)) / (u : ℂ) = (n : ℂ) := by
      field_simp
    rw [mul_div_assoc, hdiv]
    ring

/-- **The exponential is onto the invertible functions.** -/
theorem deningerTateExp_surjective {u : ℝ} (hu : u ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    ∃ α : ℂ, deningerTateExp u α = z := by
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  refine ⟨Complex.log z * (u : ℂ) / (2 * (Real.pi : ℂ) * Complex.I), ?_⟩
  rw [deningerTateExp]
  have hrw : 2 * (Real.pi : ℂ) * Complex.I *
      (Complex.log z * (u : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) / (u : ℂ)
      = Complex.log z := by
    field_simp
  rw [hrw, Complex.exp_log hz]

/-- **The exponential sequence.**  The Tate lattice is exactly the set of coefficients with trivial
exponential. -/
theorem deningerTateExp_exact {u : ℝ} (hu : u ≠ 0) :
    Function.Exact (fun n : ℤ => (n : ℂ) * (u : ℂ)) (fun α : ℂ => deningerTateExp u α - 1) := by
  intro α
  constructor
  · intro hα
    rw [sub_eq_zero] at hα
    obtain ⟨n, hn⟩ := (deningerTateExp_eq_one_iff hu α).mp hα
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, rfl⟩
    rw [sub_eq_zero]
    exact (deningerTateExp_eq_one_iff hu _).mpr ⟨n, rfl⟩

/-- **Equivariance.**  Scaling the suspension parameter and the weight-one coefficient by the same
positive rational leaves the exponential unchanged. -/
theorem deningerTateExp_equivariant {q u : ℝ} (hq : q ≠ 0) (hu : u ≠ 0) (α : ℂ) :
    deningerTateExp (q * u) ((q : ℂ) * α) = deningerTateExp u α := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have _hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  rw [deningerTateExp, deningerTateExp]
  congr 1
  have hcast : ((q * u : ℝ) : ℂ) = (q : ℂ) * (u : ℂ) := by
    push_cast
    ring
  rw [hcast, show 2 * (Real.pi : ℂ) * Complex.I * ((q : ℂ) * α)
      = (q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * α) from by ring,
    mul_div_mul_left _ _ hq']

/-- An exponential character determines its linear coefficient. -/
theorem deningerExpScalar_injective {A B : ℂ}
    (h : ∀ α : ℂ, Complex.exp (A * α) = Complex.exp (B * α)) : A = B := by
  by_contra hne
  have hsub : A - B ≠ 0 := sub_ne_zero.mpr hne
  have hone := h (A - B)⁻¹
  have hcalc : Complex.exp ((A - B) * (A - B)⁻¹) = 1 := by
    rw [sub_mul, Complex.exp_sub, hone, div_self (Complex.exp_ne_zero _)]
  rw [mul_inv_cancel₀ hsub] at hcalc
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hcalc
  have hcongr := congrArg Complex.re hn
  simp at hcongr

/-- **The weight is forced.**  A family of exponential characters invariant under the simultaneous
scaling of the suspension parameter and the coefficient has exponent `c(1)/u`; in particular the
`u⁻¹` of the equivariant exponential is not an optional normalization. -/
theorem deningerTateWeight_forced {c : ℝ → ℝ}
    (h : ∀ (q u : ℝ), 0 < q → 0 < u → ∀ α : ℂ,
      Complex.exp ((c (q * u) : ℂ) * ((q : ℂ) * α)) = Complex.exp ((c u : ℂ) * α))
    {u : ℝ} (hu : 0 < u) : c u = c 1 / u := by
  have key : ∀ (q v : ℝ), 0 < q → 0 < v → c (q * v) * q = c v := by
    intro q v hq hv
    have hfun : ∀ α : ℂ, Complex.exp (((c (q * v) * q : ℝ) : ℂ) * α)
        = Complex.exp (((c v : ℝ) : ℂ) * α) := by
      intro α
      have := h q v hq hv α
      rw [← this]
      congr 1
      push_cast
      ring
    have := deningerExpScalar_injective hfun
    exact_mod_cast this
  have h1 := key u 1 hu one_pos
  rw [mul_one] at h1
  rw [eq_div_iff (ne_of_gt hu)]
  exact h1

end ExponentialSequence

section Rationalization

variable {M : Type*} [AddCommGroup M]

/-- **The Frobenius power and the Tate twist cancel.**  On the rationalization, the `q`-th power of
a unit paired with the Tate fibre `q⁻¹` is the original class. -/
theorem deningerRationalTwist_cancel (q : ℤ) (hq : q ≠ 0) (m : M) :
    (((q : ℚ)⁻¹ : ℚ) ⊗ₜ[ℤ] (q • m) : ℚ ⊗[ℤ] M) = (1 : ℚ) ⊗ₜ[ℤ] m := by
  have hq' : (q : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hq
  rw [← TensorProduct.smul_tmul]
  congr 1
  rw [zsmul_eq_mul]
  field_simp

/-- The rationalization of a module is its localization at the nonzero integers. -/
theorem deningerRationalization_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1) := by
  rw [isLocalizedModule_iff_isBaseChange (S := nonZeroDivisors ℤ) (A := ℚ)]
  exact TensorProduct.isBaseChange ℤ M ℚ

/-- **The kernel of the rationalization is the torsion.** -/
theorem deningerRationalization_eq_zero_iff (m : M) :
    ((1 : ℚ) ⊗ₜ[ℤ] m : ℚ ⊗[ℤ] M) = 0 ↔ ∃ n : ℤ, n ≠ 0 ∧ n • m = 0 := by
  haveI := deningerRationalization_isLocalizedModule (M := M)
  have h := IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1)
    (m := m)
  constructor
  · intro hm
    obtain ⟨s, hs⟩ := h.mp hm
    exact ⟨(s : ℤ), nonZeroDivisors.ne_zero s.2, hs⟩
  · rintro ⟨n, hn, hnm⟩
    refine h.mpr ⟨⟨n, ?_⟩, hnm⟩
    exact mem_nonZeroDivisors_of_ne_zero hn

end Rationalization

section KummerKernel

variable {K : Type*} [Field K]

/-- **Injectivity modulo torsion.**  A unit whose rationalized Kummer class vanishes is a root of
unity, so the kernel of the class map is contained in the roots of unity. -/
theorem deningerKummerKernel_isTorsion (x : Kˣ)
    (h : ((1 : ℚ) ⊗ₜ[ℤ] (Additive.ofMul x) : ℚ ⊗[ℤ] Additive Kˣ) = 0) :
    ∃ n : ℤ, n ≠ 0 ∧ x ^ n = 1 := by
  obtain ⟨n, hn, hnx⟩ := (deningerRationalization_eq_zero_iff (Additive.ofMul x)).mp h
  exact ⟨n, hn, hnx⟩

/-- Conversely every root of unity has vanishing rationalized Kummer class. -/
theorem deningerKummerKernel_of_root (x : Kˣ) {n : ℤ} (hn : n ≠ 0) (hx : x ^ n = 1) :
    ((1 : ℚ) ⊗ₜ[ℤ] (Additive.ofMul x) : ℚ ⊗[ℤ] Additive Kˣ) = 0 := by
  refine (deningerRationalization_eq_zero_iff (Additive.ofMul x)).mpr ⟨n, hn, ?_⟩
  exact hx

end KummerKernel

end RHTower

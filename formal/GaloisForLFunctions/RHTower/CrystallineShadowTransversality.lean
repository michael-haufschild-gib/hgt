import Mathlib

/-!
# Finite crystalline transversality

The shadow density of a finite multi-splitting is

`ρ(x) = 4 ∑_j cos(γ_j x) (cosh(t_j x) − 1)`,

the exact amount an explicit formula's prime side would have to absorb.  When every splitting is
genuine, `t_j ≠ 0`, this density is not identically zero, so the shadow has a nonzero absolutely
continuous part and cannot be atomic.  Hence the finite-splitting strata meet the crystalline locus
only at `t = 0`.

The certificate is local rather than spectral: at any `x` small enough that every `γ_j x` stays
inside the first quarter period, all cosines are positive and every `cosh(t_j x) − 1` is strictly
positive, so the whole sum is.  No linear independence of exponentials is needed.
-/

namespace RHTower

open Real

/-- The shadow density of a finite multi-splitting. -/
noncomputable def shadowDensity {ι : Type*} [Fintype ι] (gam t : ι → ℝ) (x : ℝ) : ℝ :=
  4 * ∑ j, Real.cos (gam j * x) * (Real.cosh (t j * x) - 1)

theorem shadowDensity_zero {ι : Type*} [Fintype ι] (gam t : ι → ℝ) :
    shadowDensity gam t 0 = 0 := by
  simp [shadowDensity]

/-- **Θ3.2, finite transversality.**  A finite multi-splitting with every displacement nonzero has
a shadow density that is somewhere strictly positive; in particular it is not identically zero, so
the shadow is not atomic. -/
theorem shadowDensity_pos_of_ne_zero {ι : Type*} [Fintype ι] [Nonempty ι]
    (gam t : ι → ℝ) (hgam : ∀ j, 0 ≤ gam j) (ht : ∀ j, t j ≠ 0) :
    ∃ x : ℝ, 0 < x ∧ 0 < shadowDensity gam t x := by
  classical
  set M : ℝ := 1 + ∑ j, gam j with hM
  have hMpos : 0 < M := by
    have : (0 : ℝ) ≤ ∑ j, gam j := Finset.sum_nonneg (fun j _ => hgam j)
    rw [hM]
    linarith
  refine ⟨1 / M, by positivity, ?_⟩
  have hxpos : (0 : ℝ) < 1 / M := by positivity
  have hbound : ∀ j, gam j * (1 / M) ≤ 1 := by
    intro j
    have hle : gam j ≤ M := by
      have hsingle : gam j ≤ ∑ k, gam k :=
        Finset.single_le_sum (f := gam) (fun k _ => hgam k) (Finset.mem_univ j)
      rw [hM]
      linarith
    rw [mul_one_div, div_le_one hMpos]
    exact hle
  have hpi : (1 : ℝ) < π / 2 := by
    have := Real.pi_gt_three
    linarith
  refine lt_of_lt_of_le ?_ (le_of_eq rfl)
  rw [shadowDensity]
  have hterm : ∀ j : ι, 0 < Real.cos (gam j * (1 / M)) * (Real.cosh (t j * (1 / M)) - 1) := by
    intro j
    have hcos : 0 < Real.cos (gam j * (1 / M)) := by
      refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
      · have hnn : 0 ≤ gam j * (1 / M) := mul_nonneg (hgam j) hxpos.le
        linarith [hpi]
      · exact lt_of_le_of_lt (hbound j) hpi
    have hne : t j * (1 / M) ≠ 0 := mul_ne_zero (ht j) (ne_of_gt hxpos)
    have hcosh : 1 < Real.cosh (t j * (1 / M)) := Real.one_lt_cosh.mpr hne
    have : 0 < Real.cosh (t j * (1 / M)) - 1 := by linarith
    exact mul_pos hcos this
  have hsum : 0 < ∑ j, Real.cos (gam j * (1 / M)) * (Real.cosh (t j * (1 / M)) - 1) :=
    Finset.sum_pos (fun j _ => hterm j) Finset.univ_nonempty
  linarith

/-- **Θ3.2, contrapositive form.**  The shadow density of a genuine finite multi-splitting is not
the zero function, so no finite off-line displacement is compatible with an atomic arithmetic
side. -/
theorem shadowDensity_ne_zero_fun {ι : Type*} [Fintype ι] [Nonempty ι]
    (gam t : ι → ℝ) (hgam : ∀ j, 0 ≤ gam j) (ht : ∀ j, t j ≠ 0) :
    shadowDensity gam t ≠ fun _ => 0 := by
  obtain ⟨x, _, hx⟩ := shadowDensity_pos_of_ne_zero gam t hgam ht
  intro hzero
  have : shadowDensity gam t x = 0 := by rw [hzero]
  linarith

end RHTower

namespace RHTower

open Complex

/-! ## The shadow kernel identity -/

/-- **Θ3.1, kernel identity.**  The four splitting exponentials of one displaced conjugate pair
sum to the shadow kernel: the quadruple `{1/2 ± t ± iγ}` contributes `4 cos(γx) cosh(tx)` to the
explicit-formula integrand.  Subtracting the undisplaced value `4 cos(γx)` leaves the shadow
density of `Θ3.1`. -/
theorem quadrupleExp_eq (g t x : ℂ) :
    Complex.exp ((t + g * Complex.I) * x) + Complex.exp ((t - g * Complex.I) * x)
        + Complex.exp ((-t + g * Complex.I) * x) + Complex.exp ((-t - g * Complex.I) * x)
      = 4 * Complex.cos (g * x) * Complex.cosh (t * x) := by
  have e1 : Complex.exp ((t + g * Complex.I) * x)
      = Complex.exp (t * x) * Complex.exp (g * x * Complex.I) := by
    rw [← Complex.exp_add]; ring_nf
  have e2 : Complex.exp ((t - g * Complex.I) * x)
      = Complex.exp (t * x) * Complex.exp (-(g * x) * Complex.I) := by
    rw [← Complex.exp_add]; ring_nf
  have e3 : Complex.exp ((-t + g * Complex.I) * x)
      = Complex.exp (-(t * x)) * Complex.exp (g * x * Complex.I) := by
    rw [← Complex.exp_add]; ring_nf
  have e4 : Complex.exp ((-t - g * Complex.I) * x)
      = Complex.exp (-(t * x)) * Complex.exp (-(g * x) * Complex.I) := by
    rw [← Complex.exp_add]; ring_nf
  rw [e1, e2, e3, e4, Complex.cos, Complex.cosh]
  ring_nf

/-- **Θ3.1, shadow form.**  The displaced quadruple minus its undisplaced value is exactly the
shadow kernel `4 cos(γx)(cosh(tx) − 1)`. -/
theorem quadrupleExp_sub_undisplaced (g t x : ℂ) :
    (Complex.exp ((t + g * Complex.I) * x) + Complex.exp ((t - g * Complex.I) * x)
        + Complex.exp ((-t + g * Complex.I) * x) + Complex.exp ((-t - g * Complex.I) * x))
      - 4 * Complex.cos (g * x)
      = 4 * Complex.cos (g * x) * (Complex.cosh (t * x) - 1) := by
  rw [quadrupleExp_eq]
  ring

end RHTower

import GaloisForLFunctions.HTGeometry.BohrConvolution

/-!
# The Fejér kernel on an arithmetic frequency progression

The Bochner–Fejér construction convolves an almost-periodic function against a **nonnegative**
trigonometric kernel of mean one.  On the arithmetic progression `βℤ` that kernel is the classical
Fejér kernel, realized here as `|D_N|²/(N+1)` with `D_N(u) = ∑_{k ≤ N} e^{ikβu}`:

* it is a nonnegative real (`fejerKernel_nonneg`), being a squared modulus;
* it is a trigonometric polynomial with frequencies in `βℤ` (`fejerKernel_eq_sum`);
* its mean is exactly one (`bohrMean_fejerKernel`), because only the diagonal terms have zero
  frequency.

Convolving `f` against it therefore produces the Fejér mean of the Bohr–Fourier series of `f` along
`βℤ` (`bohrMean_translate_mul_fejerKernel`).  The remaining analytic step of the approximation theorem
is the uniform convergence of these Fejér means.
-/

open Filter Topology ComplexConjugate

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- The Dirichlet sum `D_N(u) = ∑_{k ≤ N} e^{ikβu}` on the progression `βℤ`. -/
noncomputable def fejerSum (β : ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1), expChar ((k : ℝ) * β) u

/-- The Fejér kernel `|D_N|²/(N+1)` on the progression `βℤ`. -/
noncomputable def fejerKernel (β : ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  ((N : ℂ) + 1)⁻¹ * (fejerSum β N u * conj (fejerSum β N u))

theorem conj_expChar (a u : ℝ) : conj (expChar a u) = expChar (-a) u := by
  simp only [expChar, ← Complex.exp_conj]
  congr 1
  simp

/-- The Fejér kernel is a nonnegative real. -/
theorem fejerKernel_eq_ofReal (β : ℝ) (N : ℕ) (u : ℝ) :
    fejerKernel β N u = (((‖fejerSum β N u‖ ^ (2 : ℕ) / ((N : ℝ) + 1) : ℝ)) : ℂ) := by
  rw [fejerKernel, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  field_simp

theorem fejerKernel_nonneg (β : ℝ) (N : ℕ) (u : ℝ) :
    0 ≤ (‖fejerSum β N u‖ ^ (2 : ℕ) / ((N : ℝ) + 1)) := by
  positivity

/-- The Fejér kernel expanded as a trigonometric polynomial with frequencies in `βℤ`. -/
theorem fejerKernel_eq_sum (β : ℝ) (N : ℕ) (u : ℝ) :
    fejerKernel β N u
      = ∑ p ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
          ((N : ℂ) + 1)⁻¹ * expChar (((p.1 : ℝ) - (p.2 : ℝ)) * β) u := by
  classical
  have hconj : conj (fejerSum β N u)
      = ∑ k ∈ Finset.range (N + 1), expChar (-((k : ℝ) * β)) u := by
    rw [fejerSum, map_sum]
    exact Finset.sum_congr rfl fun k _ => conj_expChar _ _
  rw [fejerKernel, hconj, fejerSum, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [expChar_add]
  congr 2
  ring

/-- The Fejér kernel is continuous. -/
theorem continuous_fejerKernel (β : ℝ) (N : ℕ) : Continuous (fejerKernel β N) := by
  have h : fejerKernel β N = fun u => ∑ p ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
      ((N : ℂ) + 1)⁻¹ * expChar (((p.1 : ℝ) - (p.2 : ℝ)) * β) u :=
    funext fun u => fejerKernel_eq_sum β N u
  rw [h]
  exact continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_expChar _)

/-- **The Fejér kernel has mean one.**  Only the diagonal terms carry zero frequency. -/
theorem bohrMean_fejerKernel {β : ℝ} (hβ : β ≠ 0) (N : ℕ) :
    bohrMean (fejerKernel β N) = 1 := by
  classical
  have h : fejerKernel β N = fun u => ∑ p ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
      ((N : ℂ) + 1)⁻¹ * expChar (((p.1 : ℝ) - (p.2 : ℝ)) * β) u :=
    funext fun u => fejerKernel_eq_sum β N u
  rw [h, bohrMean_sum_expChar (Finset.range (N + 1) ×ˢ Finset.range (N + 1))
    (fun _ : ℕ × ℕ => ((N : ℂ) + 1)⁻¹)
    (fun p : ℕ × ℕ => ((p.1 : ℝ) - (p.2 : ℝ)) * β), Finset.sum_product]
  have hinner : ∀ j ∈ Finset.range (N + 1),
      (∑ k ∈ Finset.range (N + 1),
        if ((j : ℝ) - (k : ℝ)) * β = 0 then ((N : ℂ) + 1)⁻¹ else 0)
        = ((N : ℂ) + 1)⁻¹ := by
    intro j hj
    have hstep : ∀ k ∈ Finset.range (N + 1),
        (if ((j : ℝ) - (k : ℝ)) * β = 0 then ((N : ℂ) + 1)⁻¹ else 0)
          = if k = j then ((N : ℂ) + 1)⁻¹ else 0 := by
      intro k _
      by_cases hk : k = j
      · rw [if_pos hk, if_pos (by rw [hk]; ring)]
      · rw [if_neg hk, if_neg]
        intro hz
        rcases mul_eq_zero.mp hz with h1 | h2
        · exact hk (by
            have : (j : ℝ) = (k : ℝ) := by linarith [sub_eq_zero.mp h1]
            exact_mod_cast this.symm)
        · exact hβ h2
    rw [Finset.sum_congr rfl hstep,
      Finset.sum_ite_eq' (Finset.range (N + 1)) j (fun _ => ((N : ℂ) + 1)⁻¹), if_pos hj]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hne : ((N : ℂ) + 1) ≠ 0 := by
    intro hz
    have : ((N : ℝ) + 1 : ℂ) = 0 := by push_cast at hz ⊢; exact hz
    have hR : ((N : ℝ) + 1) = 0 := by exact_mod_cast this
    have : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    linarith
  push_cast
  field_simp

/-- **The Fejér mean of the Bohr–Fourier series.**  Convolving `f` against the Fejér kernel of the
progression `βℤ` returns the trigonometric polynomial whose coefficients are the Bohr coefficients of
`f` at the frequencies `(j−k)β`, weighted by `1/(N+1)`. -/
theorem bohrMean_translate_mul_fejerKernel {f : ℝ → ℂ} (hfc : Continuous f)
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) (β : ℝ) (N : ℕ) (t : ℝ) :
    bohrMean (fun u => f (u + t) * fejerKernel β N u)
      = ∑ p ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
          (((N : ℂ) + 1)⁻¹ *
              bohrCoefficient f (-(((p.1 : ℝ) - (p.2 : ℝ)) * β))) *
            expChar (-(((p.1 : ℝ) - (p.2 : ℝ)) * β)) t := by
  classical
  have h : (fun u => f (u + t) * fejerKernel β N u)
      = fun u => f (u + t) * ∑ p ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
          ((N : ℂ) + 1)⁻¹ * bohrChar (-(((p.1 : ℝ) - (p.2 : ℝ)) * β)) u := by
    funext u
    rw [fejerKernel_eq_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [expChar_eq_bohrChar]
  rw [h, bohrMean_translate_mul_trigKernel (Finset.range (N + 1) ×ˢ Finset.range (N + 1))
    (fun _ : ℕ × ℕ => ((N : ℂ) + 1)⁻¹)
    (fun p : ℕ × ℕ => -(((p.1 : ℝ) - (p.2 : ℝ)) * β)) hfc hfa t]

end

end GaloisForLFunctions

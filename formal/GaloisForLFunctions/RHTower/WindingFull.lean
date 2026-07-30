/-
The argument principle for a general analytic function on a disc.

Combining the divisor computation (`windingNumber_divisor`) with the vanishing of the winding of a
nonvanishing factor (`windingNumber_nonvanishing_disc`, via a branch of logarithm on the simply
connected disc): if `f = (∏ᵢ (z − ρᵢ)^{mᵢ})·g` on a disc `ball c R`, with the `ρᵢ` strictly inside a
sub-circle of radius `r < R` and `g` continuous and nowhere zero on the disc, then the winding number
of `f` around that circle is the total enclosed order `Σᵢ mᵢ` (`windingNumber_argument_principle`).

This is the topological argument principle in exactly the factored form of `box_charge_eq_deckRed`:
the deck charge of the boundary circle, `wCharge (2^k) (Σᵢ mᵢ)` (`loopCharge_argument_principle`),
is the winding number's reduction — the winding realisation of the multi-zero deck charge for a
general analytic `f`, not merely a polynomial.
-/
import GaloisForLFunctions.RHTower.WindingDivisor

open Complex Set Metric

namespace RHTower

/-- An open ball is simply connected (it is convex, hence contractible). -/
theorem isSimplyConnected_ball (c : ℂ) {R : ℝ} (hR : 0 < R) :
    IsSimplyConnected (Metric.ball c R) := by
  haveI : ContractibleSpace ↥(Metric.ball c R) :=
    (convex_ball c R).contractibleSpace (nonempty_ball.mpr hR)
  apply SimplyConnectedSpace.ofContractible

/-- The circle of radius `r < R` lies inside `ball c R`. -/
theorem circle_mem_ball {c : ℂ} {r R : ℝ} (hrR : r < R) (hr : 0 ≤ r) (θ : ℝ) :
    (c + ↑r * exp (I * ↑θ)) ∈ Metric.ball c R := by
  rw [Metric.mem_ball, dist_eq_norm, show (c + ↑r * exp (I * ↑θ)) - c = ↑r * exp (I * ↑θ) by ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im]
  simpa using hrR

/-- **A nowhere-zero factor on the disc contributes no winding.**  If `g` is continuous and nowhere
zero on `ball c R`, then `g` restricted to any interior circle winds `0`: it has a single-valued
branch of logarithm on the simply connected disc. -/
theorem windingNumber_nonvanishing_disc {g : ℂ → ℂ} {c : ℂ} {r R : ℝ}
    (hrR : r < R) (hr : 0 ≤ r)
    (hgc : ContinuousOn g (Metric.ball c R)) (hg0 : ∀ z ∈ Metric.ball c R, g z ≠ 0) :
    windingNumber (fun θ => g (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi) = 0 := by
  have hcirc : ∀ θ : ℝ, (c + ↑r * exp (I * ↑θ)) ∈ Metric.ball c R :=
    fun θ => circle_mem_ball hrR hr θ
  obtain ⟨G, hGc, hGe⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    (isSimplyConnected_ball c (hr.trans_lt hrR)) isOpen_ball hgc
    (by rintro ⟨z, hz, hgz⟩; exact hg0 z hz hgz)
  set circ : ℝ → ℂ := fun θ => c + ↑r * exp (I * ↑θ) with hcircdef
  have hcircc : Continuous circ := by fun_prop
  have hccl : circ (2 * Real.pi) = circ 0 := by
    rw [hcircdef]; simp only
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      show (I * (((2 : ℝ) * Real.pi : ℝ) : ℂ)) = (2 * (Real.pi : ℂ) * I) by push_cast; ring,
      Complex.exp_two_pi_mul_I]
  have hL : IsLoop (fun θ => g (circ θ)) 0 (2 * Real.pi) :=
    ⟨hgc.comp_continuous hcircc hcirc, fun θ => hg0 _ (hcirc θ), by
      show g (circ 0) = g (circ (2 * Real.pi)); rw [hccl]⟩
  rw [windingNumber_eq_zero_iff hL (hGc.comp_continuous hcircc hcirc) (fun θ => hGe (hcirc θ))]
  show G (circ (2 * Real.pi)) = G (circ 0)
  rw [hccl]

/-- The product of enclosed linear-factor powers is a loop. -/
theorem isLoop_divisor {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ) (c : ℂ) {r : ℝ}
    (hr : 0 < r) (hin : ∀ i ∈ s, ‖ρ i - c‖ < r) :
    IsLoop (fun θ => ∏ i ∈ s, ((c + ↑r * exp (I * ↑θ)) - ρ i) ^ m i) 0 (2 * Real.pi) := by
  refine ⟨continuous_finsetProd s (fun i hi =>
      ((isLoop_linear_enclosing hr (hin i hi)).continuous).pow (m i)), fun θ => ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr
      (fun i hi => pow_ne_zero _ ((isLoop_linear_enclosing hr (hin i hi)).nonzero θ))
  · refine Finset.prod_congr rfl (fun i hi => ?_)
    have h := (isLoop_linear_enclosing hr (hin i hi)).closed
    rw [h]

/-- **The argument principle.**  For `f = (∏ᵢ (z − ρᵢ)^{mᵢ})·g` on `ball c R`, with all `ρᵢ` strictly
inside the circle of radius `r < R` and `g` continuous and nowhere zero on the disc, the winding
number of `f` around that circle is the total enclosed order `Σᵢ mᵢ`. -/
theorem windingNumber_argument_principle {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ)
    {f g : ℂ → ℂ} {c : ℂ} {r R : ℝ} (hrR : r < R) (hr : 0 < r)
    (hin : ∀ i ∈ s, ‖ρ i - c‖ < r)
    (hgc : ContinuousOn g (Metric.ball c R)) (hg0 : ∀ z ∈ Metric.ball c R, g z ≠ 0)
    (hfact : ∀ z ∈ Metric.ball c R, f z = (∏ i ∈ s, (z - ρ i) ^ m i) * g z) :
    windingNumber (fun θ => f (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi) = ∑ i ∈ s, (m i : ℤ) := by
  have hcirc : ∀ θ : ℝ, (c + ↑r * exp (I * ↑θ)) ∈ Metric.ball c R :=
    fun θ => circle_mem_ball hrR hr.le θ
  have hccl : (c + ↑r * exp (I * ((0 : ℝ) : ℂ)))
      = (c + ↑r * exp (I * (((2 : ℝ) * Real.pi : ℝ) : ℂ))) := by
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      show (I * (((2 : ℝ) * Real.pi : ℝ) : ℂ)) = (2 * (Real.pi : ℂ) * I) by push_cast; ring,
      Complex.exp_two_pi_mul_I]
  have hLg : IsLoop (fun θ : ℝ => g (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi) :=
    ⟨hgc.comp_continuous (by fun_prop) hcirc, fun θ => hg0 _ (hcirc θ), by
      show g (c + ↑r * exp (I * ((0 : ℝ) : ℂ))) = g (c + ↑r * exp (I * (((2 : ℝ) * Real.pi : ℝ) : ℂ)))
      rw [hccl]⟩
  have hfeq : (fun θ : ℝ => f (c + ↑r * exp (I * ↑θ)))
      = (fun θ : ℝ => (∏ i ∈ s, ((c + ↑r * exp (I * ↑θ)) - ρ i) ^ m i)
          * g (c + ↑r * exp (I * ↑θ))) := by
    funext θ; exact hfact _ (hcirc θ)
  rw [hfeq, windingNumber_mul (isLoop_divisor s ρ m c hr hin) hLg,
    windingNumber_divisor s ρ m c r hr hin,
    windingNumber_nonvanishing_disc hrR hr.le hgc hg0, add_zero]

/-- **The deck charge of the boundary circle is the enclosed order, for a general analytic `f`.**
`wCharge (2^k) (Σᵢ mᵢ)` — the winding realisation of the multi-zero deck charge in the factored form
of `box_charge_eq_deckRed`. -/
theorem loopCharge_argument_principle {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ)
    {f g : ℂ → ℂ} {c : ℂ} {r R : ℝ} (hrR : r < R) (hr : 0 < r)
    (hin : ∀ i ∈ s, ‖ρ i - c‖ < r)
    (hgc : ContinuousOn g (Metric.ball c R)) (hg0 : ∀ z ∈ Metric.ball c R, g z ≠ 0)
    (hfact : ∀ z ∈ Metric.ball c R, f z = (∏ i ∈ s, (z - ρ i) ^ m i) * g z) (k : ℕ) :
    loopCharge k (fun θ => f (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi)
      = wCharge (2 ^ k) (∑ i ∈ s, (m i : ℤ)) := by
  rw [loopCharge, windingNumber_argument_principle s ρ m hrR hr hin hgc hg0 hfact]

end RHTower

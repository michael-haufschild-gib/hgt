import GaloisForLFunctions.RHTower.XiTwoPortProducerTransport
import GaloisForLFunctions.RHTower.EntireWeightedLittlewoodLeftClosure

/-!
# The Littlewood transport identity of the two-port producer

Let `B_h(s) = ξ(s) + ξ(s − 2h)` and `c = ½ + h`. Zeros of `B_h` right of `Re s = c` are the defects
of `cos(hD)Ξ` (`s = c + iz`, `Re s − c = −Im z`). Zeros of `ξ` right of `c` are the zeros deeper
than `h`.

**Theorem** (`twoPort_littlewood_transport`). On a rectangle `[c, d] × [T₁, T₂]` on whose right and
horizontal edges `B_h` and `ξ` do not vanish,

  `2π (Σ_{B_h = 0} m (Re s − c) − Σ_{ξ = 0} m (Re s − c)) = W(B_h) − W(ξ)`,

where `W` is the weighted Littlewood boundary functional (`weightedLittlewoodBoundary`). Zeros on the
left edge are allowed and carry weight zero.

On the left edge `‖B_h(c + it)‖ = 2|Re ξ(c + it)|` (`norm_twoPort_line`). So the left-edge part of
`W(B_h) − W(ξ)` is the *phase deficit* `∫ log |2 cos arg ξ(c + it)| dt`, and the identity reads:
the height moment of the producer's defects minus the excess moment of the deep zeros equals the
phase deficit of `ξ` along `Re s = ½ + h`, up to the right and horizontal edges. Under RH both
moments vanish, so the phase deficit is balanced by the edges at every depth.
-/

open Complex Set MeasureTheory

namespace RHTower

noncomputable section

theorem norm_twoPort_line (h t : ℝ) :
    ‖twoPort h (((1 / 2 + h : ℝ) : ℂ) + t * I)‖ =
      2 * |(xi (((1 / 2 + h : ℝ) : ℂ) + t * I)).re| := by
  rw [twoPort_line, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos two_pos]

/-- **The Littlewood transport identity.** -/
theorem twoPort_littlewood_transport {h d T₁ T₂ : ℝ} (hcd : 1 / 2 + h < d) (hT : T₁ < T₂)
    (hBbot : ∀ x ∈ uIcc (1 / 2 + h) d, twoPort h ((x : ℂ) + T₁ * I) ≠ 0)
    (hBtop : ∀ x ∈ uIcc (1 / 2 + h) d, twoPort h ((x : ℂ) + T₂ * I) ≠ 0)
    (hBright : ∀ t ∈ uIcc T₁ T₂, twoPort h ((d : ℂ) + t * I) ≠ 0)
    (hξbot : ∀ x ∈ uIcc (1 / 2 + h) d, xi ((x : ℂ) + T₁ * I) ≠ 0)
    (hξtop : ∀ x ∈ uIcc (1 / 2 + h) d, xi ((x : ℂ) + T₂ * I) ≠ 0)
    (hξright : ∀ t ∈ uIcc T₁ T₂, xi ((d : ℂ) + t * I) ≠ 0) :
    ∃ ZB Zξ : Finset ℂ,
      (∀ z : ℂ, z ∈ ZB ↔ z ∈ (uIcc (1 / 2 + h) d ×ℂ uIcc T₁ T₂) ∧ twoPort h z = 0) ∧
      (∀ z : ℂ, z ∈ Zξ ↔ z ∈ (uIcc (1 / 2 + h) d ×ℂ uIcc T₁ T₂) ∧ xi z = 0) ∧
      2 * Real.pi *
          ((∑ w ∈ ZB, ((analyticOrderAt (twoPort h) w).toNat : ℝ) * (w.re - (1 / 2 + h))) -
            ∑ w ∈ Zξ, ((analyticOrderAt xi w).toNat : ℝ) * (w.re - (1 / 2 + h))) =
        weightedLittlewoodBoundary (twoPort h) (1 / 2 + h) d T₁ T₂ -
          weightedLittlewoodBoundary xi (1 / 2 + h) d T₁ T₂ := by
  have hT' : T₁ ∈ uIcc T₁ T₂ := left_mem_uIcc
  obtain ⟨ZB, hZB, idB⟩ := exists_entire_weighted_littlewood_rectangle_allow_left_zeros
    (analyticOnNhd_twoPort h) ⟨_, hBright T₁ hT'⟩ hcd hT hBbot hBtop hBright
  obtain ⟨Zξ, hZξ, idξ⟩ := exists_entire_weighted_littlewood_rectangle_allow_left_zeros
    xi_analyticOnNhd_univ ⟨_, hξright T₁ hT'⟩ hcd hT hξbot hξtop hξright
  refine ⟨ZB, Zξ, hZB, hZξ, ?_⟩
  rw [mul_sub, idB, idξ]

/-- **The left edge is the phase deficit.** The left-edge term of `W(B_h) − W(ξ)` is
`∫ (log 2|Re ξ(c + it)| − log ‖ξ(c + it)‖) dt`, the integral of `log |2 cos arg ξ|`. -/
theorem weightedLittlewoodBoundary_twoPort_left (h T₁ T₂ : ℝ) :
    (∫ t in T₁..T₂, Real.log ‖twoPort h ((((1 / 2 + h : ℝ) : ℂ)) + t * I)‖) =
      ∫ t in T₁..T₂, Real.log (2 * |(xi (((1 / 2 + h : ℝ) : ℂ) + t * I)).re|) := by
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [norm_twoPort_line]

end

end RHTower

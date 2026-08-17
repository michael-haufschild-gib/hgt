import GaloisForLFunctions.RHTower.SuzukiExplicitScrewRegularKernel

/-!
# The endpoint window of the regular screw kernel

Rescaling the regular screw kernel at the endpoint of the aperture leaves an exact two-term
expression,

`e^{-a} K(2a - u) = e^{-u/2} - e^{-6a + 5u/2} / (1 - e^{-4a + 2u})`,

whose first term is the limiting Laplace density and whose second term is exponentially small,
uniformly for `u` in a fixed window.  This is the reason the archimedean endpoint compression
converges to its rank-one Laplace limit in Hilbert–Schmidt norm and not merely strongly.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **`(280)`: the exact endpoint rescaling of the regular screw kernel.** -/
theorem exp_neg_mul_screwRegularKernel {a u : ℝ} (h : u < 2 * a) :
    Real.exp (-a) * screwRegularKernel (2 * a - u)
      = Real.exp (-u / 2)
        - Real.exp (-6 * a + 5 * u / 2) / (1 - Real.exp (-4 * a + 2 * u)) := by
  have ht : (0 : ℝ) < 2 * a - u := by linarith
  have hden : (1 : ℝ) - Real.exp (-(2 * (2 * a - u))) ≠ 0 :=
    ne_of_gt (one_sub_exp_neg_two_mul_pos ht)
  have hrw : -(2 * (2 * a - u)) = -4 * a + 2 * u := by ring
  have h1 : Real.exp (-a) * Real.exp ((2 * a - u) / 2) = Real.exp (-u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-a) * Real.exp (-(5 * (2 * a - u) / 2))
      = Real.exp (-6 * a + 5 * u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [screwRegularKernel, mul_sub, h1, mul_div_assoc', h2, hrw]

/-- The correction term is dominated by an exponentially small quantity, uniformly on a window. -/
theorem abs_screwEndpointCorrection_le {a u L T : ℝ} (hT : 0 < T)
    (huL : u ≤ 2 * L) (h : T ≤ 2 * a - u) :
    |Real.exp (-6 * a + 5 * u / 2) / (1 - Real.exp (-4 * a + 2 * u))|
      ≤ Real.exp (-6 * a + 5 * L) / (1 - Real.exp (-2 * T)) := by
  have hexpT : Real.exp (-2 * T) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hdenT : (0 : ℝ) < 1 - Real.exp (-2 * T) := by linarith
  have hle : Real.exp (-4 * a + 2 * u) ≤ Real.exp (-2 * T) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hden : (0 : ℝ) < 1 - Real.exp (-4 * a + 2 * u) := by linarith
  have hnum : Real.exp (-6 * a + 5 * u / 2) ≤ Real.exp (-6 * a + 5 * L) := by
    apply Real.exp_le_exp.mpr
    linarith
  rw [abs_of_pos (by positivity)]
  exact div_le_div₀ (by positivity) hnum hdenT (by linarith)

/-- **The endpoint kernel converges to the Laplace density with an exponentially small uniform
error.** -/
theorem abs_exp_neg_mul_screwRegularKernel_sub_le {a u L T : ℝ} (hT : 0 < T)
    (huL : u ≤ 2 * L) (h : T ≤ 2 * a - u) :
    |Real.exp (-a) * screwRegularKernel (2 * a - u) - Real.exp (-u / 2)|
      ≤ Real.exp (-6 * a + 5 * L) / (1 - Real.exp (-2 * T)) := by
  have hlt : u < 2 * a := by linarith
  rw [exp_neg_mul_screwRegularKernel hlt]
  have hsimp : Real.exp (-u / 2)
      - Real.exp (-6 * a + 5 * u / 2) / (1 - Real.exp (-4 * a + 2 * u))
      - Real.exp (-u / 2)
      = -(Real.exp (-6 * a + 5 * u / 2) / (1 - Real.exp (-4 * a + 2 * u))) := by ring
  rw [hsimp, abs_neg]
  exact abs_screwEndpointCorrection_le hT huL h

end GaloisForLFunctions.RHTower

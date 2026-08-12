import GaloisForLFunctions.RHTower.Sieve.RouteTZetaParameters

/-!
# Canonical Route-T zeta growth

All free receiver parameters are now chosen from the height.  The only remaining size condition is
that the degree-nine start exponent lies below the ordinary cubic zeta truncation exponent.
-/

namespace RHTower.Sieve

open Complex

noncomputable section

/-- **Canonical left-edge growth.**  At width `D⁻¹(V+1)⁻⁹`, zeta is bounded by a polynomial head,
one absolute constant per dyadic block, and the two exact Euler--Maclaurin tails. -/
theorem norm_riemannZeta_le_routeT_canonical
    {t : ℝ} (ht8 : 8 * Real.pi ≤ t)
    (hdepth : routeTGlobalExponent (routeTGlobalShell t) + 1 ≤ topExponent t) :
    ‖riemannZeta ((routeTStripAbscissa (routeTGlobalShell t) : ℂ) +
        Complex.I * (t : ℂ))‖ ≤
      2 + (routeTStripDenominator * (routeTGlobalShell t + 1) ^ 9 : ℕ) +
        (routeTGlobalBlocks t : ℝ) * 6912 +
      (((2 ^ topExponent t : ℕ) : ℝ) ^
          (1 - routeTStripAbscissa (routeTGlobalShell t))) /
        ‖(routeTStripAbscissa (routeTGlobalShell t) : ℂ) +
          Complex.I * (t : ℂ) - 1‖ +
      ‖(routeTStripAbscissa (routeTGlobalShell t) : ℂ) +
          Complex.I * (t : ℂ)‖ *
        ((((2 ^ topExponent t : ℕ) : ℝ) ^
          (-routeTStripAbscissa (routeTGlobalShell t))) /
            routeTStripAbscissa (routeTGlobalShell t)) := by
  let V := routeTGlobalShell t
  let A := routeTGlobalStart V
  let R := routeTGlobalBlocks t
  let σ := routeTStripAbscissa V
  have ht : 1 < t := by
    have hπ := Real.pi_gt_three
    nlinarith
  have hmain := norm_riemannZeta_le_routeT_uniform
    (A := A) (V := V) (R := R) (σ := σ) (t := t)
    (routeTGlobalStart_two_le V)
    (routeTStripAbscissa_pos V) (routeTStripAbscissa_lt_one V) ht
    (routeTGlobalStart_size V)
    (by simpa only [A, V] using routeTGlobalHeight_upper ht)
    (routeTGlobalStart_factorial V)
    (by simpa only [A, R, V] using routeTGlobalTruncation_low ht8 hdepth)
    (by
      rw [one_sub_routeTStripAbscissa]
      exact routeTStripWidth_route_condition (routeTGlobalShell_pos t))
    (by
      rw [one_sub_routeTStripAbscissa]
      exact routeTStripWidth_derivative_condition V)
  have htrunc := routeTGlobalTruncation_eq (t := t) (by omega)
  have hhead := routeTGlobalHead_le V
  dsimp only [A, R, σ] at hmain
  rw [htrunc] at hmain
  dsimp only [V] at hmain hhead ⊢
  linarith

end

end RHTower.Sieve

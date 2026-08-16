import GaloisForLFunctions.RHTower.XiMassShellPrimeMass
import GaloisForLFunctions.RHTower.XiMassBesselConeTail

/-!
# The exterior tail beyond a shifted shell

Using the square-root-gain envelope `(17.7)` instead of the plain one, and cutting at
`e^{κu+L}` instead of `e^{κu}`, the exterior true-prime tail acquires both the stationary-phase
factor `u^{-1/2}` and the geometric gain `e^{-(a-1/2)L}`:

`∑_{log p > κu+L} (log p) p^{-1/2} |F_u(log p)| ≤ C u^{-1/2} e^{-η_κ u} e^{-(a-1/2)L}`.

This is the estimate that makes the first shell dominate the rest of the annulus.
-/

open Complex Filter Finset MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- The exterior atom majorant with the square-root gain and a shifted cutoff. -/
theorem norm_xiMassCenteredPrimeAtom_exteriorSqrt_le {a sigma kappa u L : ℝ} {p : ℕ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 < u) (hL : 0 ≤ L)
    (hp : p.Prime) (hcone : Real.exp (kappa * u + L) < (p : ℝ)) :
    ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) p‖
      ≤ xiMassBesselExteriorSqrtConstant a sigma kappa / Real.sqrt u
          * Real.exp (-(xiMassBesselConeExponent a kappa * u))
          * Real.exp ((a - 1 / 2) * (kappa * u))
        * (Real.log p * (p : ℝ) ^ (-(1 + (a - 1 / 2)))) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  set h : ℝ := Real.log p with hh
  have hhpos : 0 < h := Real.log_pos hp1
  have hcone' : kappa * u ≤ h := by
    have hlog := Real.log_lt_log (Real.exp_pos (kappa * u + L)) hcone
    rw [Real.log_exp] at hlog
    linarith
  have hF := norm_stripFourier_xiMass_le_besselExteriorSqrt
    (a := a) (sigma := sigma) (kappa := kappa) (u := u) (h := h)
    ha0 hsigma hkappa hu hcone'
  have hnorm : ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) p‖
      = (Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)))
        * ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)‖ := by
    rw [xiMassCenteredPrimeAtom, norm_mul, norm_lseriesTerm_vonMangoldt_prime hp]
  have hweight0 : (0 : ℝ) ≤ Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (Real.log_nonneg hp1.le) (Real.rpow_pos_of_pos hp0 _).le
  have hstep : ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) p‖
      ≤ (Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)))
        * (xiMassBesselExteriorSqrtConstant a sigma kappa / Real.sqrt u
          * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hF hweight0
  refine hstep.trans ?_
  have hexpo := xiMassBessel_exterior_exponent_le (a := a) (kappa := kappa) (u := u) (h := h)
    ha hkappa hu.le hcone'
  have hhalf : (p : ℝ) ^ (-(1 / 2 : ℝ)) = Real.exp (-(h / 2)) := by
    rw [Real.rpow_def_of_pos hp0, ← hh]
    congr 1
    ring
  have hpow : (p : ℝ) ^ (-(1 + (a - 1 / 2))) = Real.exp (-((1 + (a - 1 / 2)) * h)) := by
    rw [Real.rpow_def_of_pos hp0, ← hh]
    congr 1
    ring
  rw [hhalf, hpow]
  have hexpprod : Real.exp (-(h / 2)) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))
      ≤ Real.exp (-(xiMassBesselConeExponent a kappa * u))
        * Real.exp ((a - 1 / 2) * (kappa * u)) * Real.exp (-((1 + (a - 1 / 2)) * h)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1.le
  have hC : 0 ≤ xiMassBesselExteriorSqrtConstant a sigma kappa / Real.sqrt u := by
    have := xiMassBesselExteriorSqrtConstant_nonneg (a := a) (sigma := sigma) ha0 hkappa
    positivity
  calc Real.log p * Real.exp (-(h / 2))
        * (xiMassBesselExteriorSqrtConstant a sigma kappa / Real.sqrt u
          * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))))
      = xiMassBesselExteriorSqrtConstant a sigma kappa / Real.sqrt u
        * (Real.log p * (Real.exp (-(h / 2))
          * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))))) := by ring
    _ ≤ xiMassBesselExteriorSqrtConstant a sigma kappa / Real.sqrt u
        * (Real.log p * (Real.exp (-(xiMassBesselConeExponent a kappa * u))
            * Real.exp ((a - 1 / 2) * (kappa * u)) * Real.exp (-((1 + (a - 1 / 2)) * h)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpprod hlogp) hC
    _ = xiMassBesselExteriorSqrtConstant a sigma kappa / Real.sqrt u
          * Real.exp (-(xiMassBesselConeExponent a kappa * u))
          * Real.exp ((a - 1 / 2) * (kappa * u))
        * (Real.log p * Real.exp (-((1 + (a - 1 / 2)) * h))) := by ring

/-- The total exterior tail constant with the square-root gain. -/
def xiMassBesselExteriorSqrtTailConstant (a sigma kappa : ℝ) : ℝ :=
  xiMassBesselExteriorSqrtConstant a sigma kappa
    * ((2 : ℝ) ^ (a - 1 / 2) * primeLogRpowTailConstant (a - 1 / 2))

/-- **The shifted exterior prime tail.** -/
theorem sum_norm_xiMassCenteredPrimeAtom_exteriorSqrt_le {a sigma kappa u L : ℝ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 < u) (hL : 0 ≤ L)
    (N : ℕ) :
    ∑ p ∈ (Nat.primesBelow (N + 1)).filter
        (fun p : ℕ => Real.exp (kappa * u + L) < (p : ℝ)),
        ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) p‖
      ≤ xiMassBesselExteriorSqrtTailConstant a sigma kappa / Real.sqrt u
        * Real.exp (-(xiMassBesselConeExponent a kappa * u))
        * Real.exp (-((a - 1 / 2) * L)) := by
  classical
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hδ : (0 : ℝ) < a - 1 / 2 := by linarith
  have hA0 : (0 : ℝ) ≤ xiMassBesselExteriorSqrtConstant a sigma kappa / Real.sqrt u
      * Real.exp (-(xiMassBesselConeExponent a kappa * u))
      * Real.exp ((a - 1 / 2) * (kappa * u)) := by
    have := xiMassBesselExteriorSqrtConstant_nonneg (a := a) (sigma := sigma) ha0 hkappa
    positivity
  have hterm : ∀ p ∈ (Nat.primesBelow (N + 1)).filter
      (fun p : ℕ => Real.exp (kappa * u + L) < (p : ℝ)),
      ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) p‖
        ≤ (xiMassBesselExteriorSqrtConstant a sigma kappa / Real.sqrt u
            * Real.exp (-(xiMassBesselConeExponent a kappa * u))
            * Real.exp ((a - 1 / 2) * (kappa * u)))
          * (Real.log p * (p : ℝ) ^ (-(1 + (a - 1 / 2)))) := by
    intro p hp
    obtain ⟨hpmem, hgt⟩ := Finset.mem_filter.mp hp
    exact norm_xiMassCenteredPrimeAtom_exteriorSqrt_le ha hsigma hkappa hu hL
      (Nat.mem_primesBelow.mp hpmem).2 hgt
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hX : (1 : ℝ) ≤ Real.exp (kappa * u + L) :=
    Real.one_le_exp (by nlinarith [hu, hL, hkappa0])
  have htail := sum_prime_log_rpow_tail_le (δ := a - 1 / 2)
    (X := Real.exp (kappa * u + L)) hδ hX N
  have hstep := mul_le_mul_of_nonneg_left htail hA0
  refine hstep.trans (le_of_eq ?_)
  have hXpow : (Real.exp (kappa * u + L)) ^ (-(a - 1 / 2))
      = Real.exp (-((a - 1 / 2) * (kappa * u))) * Real.exp (-((a - 1 / 2) * L)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
    congr 1
    ring
  rw [hXpow, xiMassBesselExteriorSqrtTailConstant]
  have hcancel : Real.exp ((a - 1 / 2) * (kappa * u)) * Real.exp (-((a - 1 / 2) * (kappa * u)))
      = 1 := by
    rw [← Real.exp_add]
    simp
  calc (xiMassBesselExteriorSqrtConstant a sigma kappa / Real.sqrt u
        * Real.exp (-(xiMassBesselConeExponent a kappa * u))
        * Real.exp ((a - 1 / 2) * (kappa * u)))
      * ((2 : ℝ) ^ (a - 1 / 2) * primeLogRpowTailConstant (a - 1 / 2)
        * (Real.exp (-((a - 1 / 2) * (kappa * u))) * Real.exp (-((a - 1 / 2) * L))))
      = (xiMassBesselExteriorSqrtConstant a sigma kappa
            * ((2 : ℝ) ^ (a - 1 / 2) * primeLogRpowTailConstant (a - 1 / 2)) / Real.sqrt u
          * Real.exp (-(xiMassBesselConeExponent a kappa * u))
          * Real.exp (-((a - 1 / 2) * L)))
        * (Real.exp ((a - 1 / 2) * (kappa * u))
          * Real.exp (-((a - 1 / 2) * (kappa * u)))) := by ring
    _ = xiMassBesselExteriorSqrtConstant a sigma kappa
          * ((2 : ℝ) ^ (a - 1 / 2) * primeLogRpowTailConstant (a - 1 / 2)) / Real.sqrt u
        * Real.exp (-(xiMassBesselConeExponent a kappa * u))
        * Real.exp (-((a - 1 / 2) * L)) := by
        rw [hcancel, mul_one]

end

end RHTower

import GaloisForLFunctions.RHTower.XiMassBesselConeEnvelope
import GaloisForLFunctions.RHTower.PrimeLogRpowTail
import GaloisForLFunctions.RHTower.XiMassTruePrimeCoboundaryBridge
import GaloisForLFunctions.RHTower.XiMassPrimePowerVerticalIdeal

/-!
# The exterior prime tail of the Bessel cone

Outside the slope-`κ` cone the true-prime mass is controlled by one Chebyshev tail.  Two exact
inequalities combine.

The first is purely geometric: for `h ≥ κu ≥ 0` and `κ > 1`,

`h − κu + √(κ²−1)·u ≤ √(h² − u²)`,

with equality at `h = κu`.  Multiplying by `a` and rearranging turns the Bessel exponent
`h/2 − a√(h²−u²)` into `−η_κ u − (a−1/2)(h − κu)` where `η_κ = a√(κ²−1) − κ/2`.

The second is Chebyshev's `∑_{p ≤ x} log p ≤ x log 4` in its dyadic tail form: the residual
Dirichlet exponent `a − 1/2` is strictly positive, so the tail of `(log p) p^{-1/2-a}` above
`e^{κu}` cancels the factor `e^{(a-1/2)κu}` exactly.

The result is that the exterior true-prime mass is at most `C e^{-η_κ u}`.  The balance slope
`κ_B = a/√(a²−1/4)` is exactly where `η_κ` vanishes, so every slope at or above it gives a
uniformly bounded exterior tail — and therefore a cone equivalent to RH.
-/

open Complex Finset MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## The exterior exponent -/

/-- The Bessel cone exponent `η_κ = a√(κ²−1) − κ/2`. -/
def xiMassBesselConeExponent (a kappa : ℝ) : ℝ :=
  a * Real.sqrt (kappa ^ 2 - 1) - kappa / 2

/-- The cone exponent is nonnegative exactly from the sharp balance slope on. -/
theorem xiMassBesselConeExponent_nonneg {a kappa : ℝ} (ha : 1 / 2 < a) (hkappa : 1 < kappa)
    (hsharp : xiMassSpacelikeSharpSlope a ≤ kappa) :
    0 ≤ xiMassBesselConeExponent a kappa := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hden : (0 : ℝ) < a ^ 2 - 1 / 4 := by nlinarith
  have hk : (0 : ℝ) < Real.sqrt (a ^ 2 - 1 / 4) := Real.sqrt_pos.2 hden
  have hksq : Real.sqrt (a ^ 2 - 1 / 4) ^ 2 = a ^ 2 - 1 / 4 := Real.sq_sqrt hden.le
  have hslope : a / Real.sqrt (a ^ 2 - 1 / 4) ≤ kappa := by
    simpa only [xiMassSpacelikeSharpSlope] using hsharp
  have hmul : a ≤ kappa * Real.sqrt (a ^ 2 - 1 / 4) := by
    rw [div_le_iff₀ hk] at hslope
    exact hslope
  have hkappa2 : (0 : ℝ) ≤ kappa ^ 2 - 1 := by nlinarith
  have hsq : Real.sqrt (kappa ^ 2 - 1) ^ 2 = kappa ^ 2 - 1 := Real.sq_sqrt hkappa2
  have hsnn : 0 ≤ Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_nonneg _
  have hkey : (kappa / 2) ^ 2 ≤ (a * Real.sqrt (kappa ^ 2 - 1)) ^ 2 := by
    have hexp : (a * Real.sqrt (kappa ^ 2 - 1)) ^ 2 = a ^ 2 * (kappa ^ 2 - 1) := by
      rw [mul_pow, hsq]
    rw [hexp]
    nlinarith [hksq, hmul, sq_nonneg (kappa * Real.sqrt (a ^ 2 - 1 / 4) - a)]
  rw [xiMassBesselConeExponent, sub_nonneg]
  nlinarith [mul_nonneg ha0.le hsnn]

/-- **The exterior cone geometry.**  On a slope-`κ` cone the spacelike gap dominates the shifted
height. -/
theorem sub_add_sqrt_le_sqrt_gap {kappa u h : ℝ} (hkappa : 1 < kappa) (hu : 0 ≤ u)
    (hcone : kappa * u ≤ h) :
    h - kappa * u + Real.sqrt (kappa ^ 2 - 1) * u ≤ Real.sqrt (h ^ 2 - u ^ 2) := by
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hkappa2 : (0 : ℝ) ≤ kappa ^ 2 - 1 := by nlinarith
  have hs : Real.sqrt (kappa ^ 2 - 1) ^ 2 = kappa ^ 2 - 1 := Real.sq_sqrt hkappa2
  have hsnn : 0 ≤ Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_nonneg _
  have hsk : Real.sqrt (kappa ^ 2 - 1) < kappa := by nlinarith
  have huh : u ≤ h := le_trans (by nlinarith) hcone
  have hgap : 0 ≤ h ^ 2 - u ^ 2 := by nlinarith
  have hL : 0 ≤ h - kappa * u + Real.sqrt (kappa ^ 2 - 1) * u := by
    have := mul_nonneg hsnn hu
    linarith
  have hsqgap : Real.sqrt (h ^ 2 - u ^ 2) ^ 2 = h ^ 2 - u ^ 2 := Real.sq_sqrt hgap
  have hsq : (h - kappa * u + Real.sqrt (kappa ^ 2 - 1) * u) ^ 2 ≤ h ^ 2 - u ^ 2 := by
    have hfactor : h ^ 2 - u ^ 2 - (h - kappa * u + Real.sqrt (kappa ^ 2 - 1) * u) ^ 2
        = 2 * u * (h - kappa * u) * (kappa - Real.sqrt (kappa ^ 2 - 1)) := by
      have hexp : (h - kappa * u + Real.sqrt (kappa ^ 2 - 1) * u) ^ 2
          = (h - kappa * u) ^ 2
            + 2 * (h - kappa * u) * (Real.sqrt (kappa ^ 2 - 1) * u)
            + (kappa ^ 2 - 1) * u ^ 2 := by
        have : (Real.sqrt (kappa ^ 2 - 1) * u) ^ 2 = (kappa ^ 2 - 1) * u ^ 2 := by
          rw [mul_pow, hs]
        nlinarith [this]
      rw [hexp]
      ring
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * u) (by linarith : (0:ℝ) ≤ h - kappa * u))
      (by linarith : (0:ℝ) ≤ kappa - Real.sqrt (kappa ^ 2 - 1))]
  nlinarith [Real.sqrt_nonneg (h ^ 2 - u ^ 2)]

/-- **(17.13) The exterior exponent inequality.** -/
theorem xiMassBessel_exterior_exponent_le {a kappa u h : ℝ} (ha : 1 / 2 < a) (hkappa : 1 < kappa)
    (hu : 0 ≤ u) (hcone : kappa * u ≤ h) :
    h / 2 - a * Real.sqrt (h ^ 2 - u ^ 2)
      ≤ -(xiMassBesselConeExponent a kappa * u) - (a - 1 / 2) * (h - kappa * u) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hgeom := sub_add_sqrt_le_sqrt_gap hkappa hu hcone
  have hscaled := mul_le_mul_of_nonneg_left hgeom ha0.le
  rw [xiMassBesselConeExponent]
  nlinarith

/-! ## The exterior prime atoms -/

theorem norm_lseriesTerm_vonMangoldt_prime {p : ℕ} (hp : p.Prime) :
    ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 / 2 : ℂ) p‖
      = Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have h := xiMassPrimePowerCriticalWeight_eq ⟨p, hp⟩ 0
  rw [xiMassPrimePowerCriticalWeight] at h
  norm_num at h
  rw [h]

/-- The exterior atom majorant: the Chebyshev-summable Dirichlet weight times two exponentials. -/
theorem norm_xiMassCenteredPrimeAtom_exterior_le {a sigma kappa u : ℝ} {p : ℕ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 ≤ u)
    (hp : p.Prime) (hcone : Real.exp (kappa * u) < (p : ℝ)) :
    ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) p‖
      ≤ xiMassBesselExteriorConstant a sigma kappa
          * Real.exp (-(xiMassBesselConeExponent a kappa * u))
          * Real.exp ((a - 1 / 2) * (kappa * u))
        * (Real.log p * (p : ℝ) ^ (-(1 + (a - 1 / 2)))) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  set h : ℝ := Real.log p with hh
  have hhpos : 0 < h := Real.log_pos hp1
  have hcone' : kappa * u ≤ h := by
    have := Real.log_lt_log (Real.exp_pos (kappa * u)) hcone
    rw [Real.log_exp] at this
    exact this.le
  have hF := norm_stripFourier_xiMass_le_besselExterior
    (a := a) (sigma := sigma) (kappa := kappa) (u := u) (h := h)
    ha0 hsigma hkappa hu hhpos hcone'
  have hnorm : ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) p‖
      = (Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)))
        * ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)‖ := by
    rw [xiMassCenteredPrimeAtom, norm_mul, norm_lseriesTerm_vonMangoldt_prime hp]
  have hweight0 : (0 : ℝ) ≤ Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (Real.log_nonneg hp1.le) (Real.rpow_pos_of_pos hp0 _).le
  have hstep : ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) p‖
      ≤ (Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)))
        * (xiMassBesselExteriorConstant a sigma kappa
          * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hF hweight0
  refine hstep.trans ?_
  have hexpo := xiMassBessel_exterior_exponent_le (a := a) (kappa := kappa) (u := u) (h := h)
    ha hkappa hu hcone'
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
  have hC : 0 ≤ xiMassBesselExteriorConstant a sigma kappa :=
    xiMassBesselExteriorConstant_nonneg ha0 hsigma hkappa
  calc Real.log p * Real.exp (-(h / 2))
        * (xiMassBesselExteriorConstant a sigma kappa
          * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))))
      = xiMassBesselExteriorConstant a sigma kappa
        * (Real.log p * (Real.exp (-(h / 2)) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))))) := by
        ring
    _ ≤ xiMassBesselExteriorConstant a sigma kappa
        * (Real.log p * (Real.exp (-(xiMassBesselConeExponent a kappa * u))
            * Real.exp ((a - 1 / 2) * (kappa * u)) * Real.exp (-((1 + (a - 1 / 2)) * h)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpprod hlogp) hC
    _ = xiMassBesselExteriorConstant a sigma kappa
          * Real.exp (-(xiMassBesselConeExponent a kappa * u))
          * Real.exp ((a - 1 / 2) * (kappa * u))
        * (Real.log p * Real.exp (-((1 + (a - 1 / 2)) * h))) := by ring

/-- The total exterior tail constant. -/
def xiMassBesselExteriorTailConstant (a sigma kappa : ℝ) : ℝ :=
  xiMassBesselExteriorConstant a sigma kappa * ((2 : ℝ) ^ (a - 1 / 2)
    * primeLogRpowTailConstant (a - 1 / 2))

/-- **(17.11) The exterior prime tail.**  Every finite piece of the true-prime mass outside the
slope-`κ` cone is bounded by `C e^{-η_κ u}`. -/
theorem sum_norm_xiMassCenteredPrimeAtom_exterior_le {a sigma kappa u : ℝ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 ≤ u) (N : ℕ) :
    ∑ p ∈ (Nat.primesBelow (N + 1)).filter (fun p : ℕ => Real.exp (kappa * u) < (p : ℝ)),
        ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) p‖
      ≤ xiMassBesselExteriorTailConstant a sigma kappa
        * Real.exp (-(xiMassBesselConeExponent a kappa * u)) := by
  classical
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  set δ : ℝ := a - 1 / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set A : ℝ := xiMassBesselExteriorConstant a sigma kappa
    * Real.exp (-(xiMassBesselConeExponent a kappa * u))
    * Real.exp (δ * (kappa * u)) with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (mul_nonneg (xiMassBesselExteriorConstant_nonneg ha0 hsigma hkappa)
      (Real.exp_nonneg _)) (Real.exp_nonneg _)
  have hterm : ∀ p ∈ (Nat.primesBelow (N + 1)).filter
      (fun p : ℕ => Real.exp (kappa * u) < (p : ℝ)),
      ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) p‖
        ≤ A * (Real.log p * (p : ℝ) ^ (-(1 + δ))) := by
    intro p hp
    obtain ⟨hpmem, hgt⟩ := Finset.mem_filter.mp hp
    exact norm_xiMassCenteredPrimeAtom_exterior_le ha hsigma hkappa hu
      (Nat.mem_primesBelow.mp hpmem).2 hgt
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hX : (1 : ℝ) ≤ Real.exp (kappa * u) :=
    Real.one_le_exp (mul_nonneg hkappa0.le hu)
  have htail := sum_prime_log_rpow_tail_le (δ := δ) (X := Real.exp (kappa * u)) hδ hX N
  have hstep := mul_le_mul_of_nonneg_left htail hA0
  refine hstep.trans (le_of_eq ?_)
  have hXpow : (Real.exp (kappa * u)) ^ (-δ) = Real.exp (-(δ * (kappa * u))) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  rw [hXpow, hA, xiMassBesselExteriorTailConstant, ← hδdef]
  have hcancel : Real.exp (δ * (kappa * u)) * Real.exp (-(δ * (kappa * u))) = 1 := by
    rw [← Real.exp_add, show δ * (kappa * u) + -(δ * (kappa * u)) = 0 from by ring, Real.exp_zero]
  linear_combination (xiMassBesselExteriorConstant a sigma kappa
    * Real.exp (-(xiMassBesselConeExponent a kappa * u))
    * ((2 : ℝ) ^ δ * primeLogRpowTailConstant δ)) * hcancel


/-! ## The closed sharp Bessel cone -/

/-- The cone height realized by a prescribed slope. -/
theorem xiMassConeDepthOfSlope_height {kappa : ℝ} (hkappa : 1 < kappa) (u : ℝ) :
    xiMassConeDepthOfSlope kappa * u / (xiMassConeDepthOfSlope kappa - 1 / 2) = kappa * u := by
  rw [← div_mul_eq_mul_div, xiMassConeDepthOfSlope_slope hkappa]

/-- **(17.11) Uniform prime-annulus cancellation between two slopes.**  Enlarging the cone slope
changes the true-prime cone by at most the exterior Chebyshev tail. -/
theorem norm_xiMassCriticalTruePrimeCone_slope_difference_le {a sigma kappa kappa' u : ℝ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hkk : kappa ≤ kappa')
    (hu : 0 ≤ u) :
    ‖xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa') u
        - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u‖
      ≤ xiMassBesselExteriorTailConstant a sigma kappa
        * Real.exp (-(xiMassBesselConeExponent a kappa * u)) := by
  classical
  have hkappa' : 1 < kappa' := lt_of_lt_of_le hkappa hkk
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ⌊Real.exp (kappa * u)⌋₊ = M := ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : ℕ, ⌊Real.exp (kappa' * u)⌋₊ = M' := ⟨_, rfl⟩
  have hMM' : M ≤ M' := by
    rw [← hM, ← hM']
    exact Nat.floor_mono (Real.exp_le_exp.2 (by nlinarith))
  have hfloorlt : Real.exp (kappa * u) < (M : ℝ) + 1 := by
    rw [← hM]
    exact Nat.lt_floor_add_one _
  have hcone : xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u
      = ∑ k ∈ (Finset.range (M - 1)).filter (fun k => Nat.Prime (k + 2)),
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2) := by
    rw [xiMassCriticalTruePrimeCone_eq_finsetSum, xiMassConeDepthOfSlope_height hkappa, hM]
  have hcone' : xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa') u
      = ∑ k ∈ (Finset.range (M' - 1)).filter (fun k => Nat.Prime (k + 2)),
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2) := by
    rw [xiMassCriticalTruePrimeCone_eq_finsetSum, xiMassConeDepthOfSlope_height hkappa', hM']
  have hsub : (Finset.range (M - 1)).filter (fun k => Nat.Prime (k + 2))
      ⊆ (Finset.range (M' - 1)).filter (fun k => Nat.Prime (k + 2)) := by
    intro x hx
    obtain ⟨hxr, hxp⟩ := Finset.mem_filter.mp hx
    have hxlt : x < M - 1 := Finset.mem_range.mp hxr
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hxp⟩
  have hdiff : xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa') u
      - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u
      = ∑ k ∈ (Finset.range (M' - 1)).filter (fun k => Nat.Prime (k + 2))
          \ (Finset.range (M - 1)).filter (fun k => Nat.Prime (k + 2)),
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2) := by
    rw [hcone, hcone', ← Finset.sum_sdiff hsub]
    ring
  rw [hdiff]
  refine le_trans (norm_sum_le _ _) ?_
  have hinj : ∀ x ∈ (Finset.range (M' - 1)).filter (fun k => Nat.Prime (k + 2))
      \ (Finset.range (M - 1)).filter (fun k => Nat.Prime (k + 2)),
      ∀ y ∈ (Finset.range (M' - 1)).filter (fun k => Nat.Prime (k + 2))
      \ (Finset.range (M - 1)).filter (fun k => Nat.Prime (k + 2)),
      x + 2 = y + 2 → x = y := by
    intro x _ y _ hxy
    omega
  have himage : ∑ n ∈ ((Finset.range (M' - 1)).filter (fun k => Nat.Prime (k + 2))
        \ (Finset.range (M - 1)).filter (fun k => Nat.Prime (k + 2))).image (fun k => k + 2),
        ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) n‖
      = ∑ k ∈ (Finset.range (M' - 1)).filter (fun k => Nat.Prime (k + 2))
          \ (Finset.range (M - 1)).filter (fun k => Nat.Prime (k + 2)),
          ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)‖ :=
    Finset.sum_image hinj
  have hsubT : ((Finset.range (M' - 1)).filter (fun k => Nat.Prime (k + 2))
        \ (Finset.range (M - 1)).filter (fun k => Nat.Prime (k + 2))).image (fun k => k + 2)
      ⊆ (Nat.primesBelow (M' + 1)).filter (fun p : ℕ => Real.exp (kappa * u) < (p : ℝ)) := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hkS', hkS⟩ := Finset.mem_sdiff.mp hk
    obtain ⟨hkrange, hkprime⟩ := Finset.mem_filter.mp hkS'
    have hkr : k < M' - 1 := Finset.mem_range.mp hkrange
    have hnotrange : ¬ k < M - 1 := by
      intro hlt
      exact hkS (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hkprime⟩)
    refine Finset.mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hkprime⟩, ?_⟩
    have hge : M + 1 ≤ k + 2 := by omega
    have hgeR : ((M : ℝ) + 1) ≤ ((k : ℝ) + 2) := by exact_mod_cast hge
    have hcast : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    linarith
  have hnn : ∀ n ∈ (Nat.primesBelow (M' + 1)).filter
      (fun p : ℕ => Real.exp (kappa * u) < (p : ℝ)),
      n ∉ ((Finset.range (M' - 1)).filter (fun k => Nat.Prime (k + 2))
        \ (Finset.range (M - 1)).filter (fun k => Nat.Prime (k + 2))).image (fun k => k + 2) →
      0 ≤ ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) n‖ := fun n _ _ => norm_nonneg _
  rw [← himage]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubT hnn) ?_
  exact sum_norm_xiMassCenteredPrimeAtom_exterior_le ha hsigma hkappa hu M'

/-- The line-bound property of the slope-`κ` Bessel cone. -/
def XiMassCriticalBesselConeLineBound (a sigma kappa : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u‖ ≤ C

/-- **(17.12) The closed sharp Bessel cone criterion.**  For every slope at or above the Bessel
balance slope `κ_B = a/√(a²−1/4)`, RH is equivalent to uniform boundedness of the true-prime cone
of that slope.  The balance slope is strictly below the strip slope `a/(a−1/2)`, so this is a
strictly smaller cone than the strip-shift one. -/
theorem riemannHypothesis_iff_xiMassCriticalBesselConeLineBound {a c sigma kappa : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa)
    (hsharp : xiMassSpacelikeSharpSlope a ≤ kappa) :
    RiemannHypothesis ↔ XiMassCriticalBesselConeLineBound a sigma kappa := by
  have ha : 1 / 2 < a := lt_trans hhalf hca
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hstrip : (0 : ℝ) < a - 1 / 2 := by linarith
  set kappa' : ℝ := max kappa (a / (a - 1 / 2)) + 1 with hkappa'def
  have hkk : kappa ≤ kappa' := by
    rw [hkappa'def]
    have := le_max_left kappa (a / (a - 1 / 2))
    linarith
  have hkappa' : 1 < kappa' := lt_of_lt_of_le hkappa hkk
  have hslopelt : a / (a - 1 / 2) < kappa' := by
    rw [hkappa'def]
    have := le_max_right kappa (a / (a - 1 / 2))
    linarith
  set d' : ℝ := xiMassConeDepthOfSlope kappa' with hd'
  have hd'half : 1 / 2 < d' := xiMassConeDepthOfSlope_half_lt hkappa'
  have hd'a : d' < a := (xiMassConeDepthOfSlope_lt_iff ha hkappa').2 hslopelt
  have heta : 0 ≤ xiMassBesselConeExponent a kappa :=
    xiMassBesselConeExponent_nonneg ha hkappa hsharp
  have hB0 : 0 ≤ xiMassBesselExteriorTailConstant a sigma kappa := by
    rw [xiMassBesselExteriorTailConstant]
    have h1 : 0 ≤ xiMassBesselExteriorConstant a sigma kappa :=
      xiMassBesselExteriorConstant_nonneg ha0 hsigma hkappa
    have h2 : 0 ≤ primeLogRpowTailConstant (a - 1 / 2) :=
      primeLogRpowTailConstant_nonneg hstrip
    have h3 : (0 : ℝ) < (2 : ℝ) ^ (a - 1 / 2) := Real.rpow_pos_of_pos (by norm_num) _
    exact mul_nonneg h1 (mul_nonneg h3.le h2)
  have hdiff : ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalTruePrimeCone a sigma d' u
        - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u‖
        ≤ xiMassBesselExteriorTailConstant a sigma kappa := by
    intro u hu
    refine le_trans (norm_xiMassCriticalTruePrimeCone_slope_difference_le
      ha hsigma hkappa hkk hu) ?_
    have hexp : Real.exp (-(xiMassBesselConeExponent a kappa * u)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    nlinarith
  rw [riemannHypothesis_iff_xiMassCriticalTruePrimeConeLineBound hhalf hca hsigma hd'half hd'a]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + xiMassBesselExteriorTailConstant a sigma kappa, fun u hu => ?_⟩
    have hsolve : xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u
        = xiMassCriticalTruePrimeCone a sigma d' u
          - (xiMassCriticalTruePrimeCone a sigma d' u
              - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u) := by
      ring
    rw [hsolve]
    exact (norm_sub_le _ _).trans (add_le_add (hC u hu) (hdiff u hu))
  · rintro ⟨C, hC⟩
    refine ⟨C + xiMassBesselExteriorTailConstant a sigma kappa, fun u hu => ?_⟩
    have hsolve : xiMassCriticalTruePrimeCone a sigma d' u
        = xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u
          + (xiMassCriticalTruePrimeCone a sigma d' u
              - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u) := by
      ring
    rw [hsolve]
    exact (norm_add_le _ _).trans (add_le_add (hC u hu) (hdiff u hu))

end

end RHTower

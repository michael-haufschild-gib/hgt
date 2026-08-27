import GaloisForLFunctions.RHTower.XiPhysicalEndpointValuationCompletionCofinalInvariance

/-!
# Fixed-width completed endpoint energy is unconditionally bounded

The completed unit--double refinement kernel samples Xi seam flux only at the frequency
`x - y`.  On a fixed logarithmic prime window, this frequency stays in a compact interval
independent of the translated scale.  Existing unconditional line-one and line-two seam bounds
therefore give a uniform kernel bound.  Combining it with the Mertens bound for physical endpoint
mass and the aperture Hilbert-distance bound proves an absolute, scale-free energy estimate.

The valuation correction is already a uniformly bounded perturbation, so the fully completed
physical endpoint energy has unconditional upper and lower cofinal bounds on every fixed-width
packet.  Consequently, bare fixed-width two-sided boundedness cannot be the missing RH-strength
condition.  The positive survivor is the explicit compact-frequency Dirichlet-form estimate below.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The unit--double completed response has an unconditional polynomial frequency bound. -/
theorem exists_norm_xiUnitDoubleCompletedOffDiagonalResponseKernel_global_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ,
      ‖xiUnitDoubleCompletedOffDiagonalResponseKernel x y‖ ≤
        C * (1 + |x - y|) ^ 9 := by
  obtain ⟨C₁, hC₁, hlineOne⟩ :=
    exists_norm_seamFluxCochain_boundary_global_le
  obtain ⟨C₂, hC₂, hlineTwo⟩ :=
    exists_norm_seamFluxCochain_lineTwo_global_le
  refine ⟨C₁ + 2 * C₂, add_nonneg hC₁ (mul_nonneg (by norm_num) hC₂), ?_⟩
  intro x y
  rw [xiUnitDoubleCompletedOffDiagonalResponseKernel_eq_seamFlux]
  calc
    ‖2 * seamFluxCochain ((2 : ℂ) + ((x - y : ℝ) : ℂ) * Complex.I) -
        seamFluxCochain ((1 : ℂ) + ((x - y : ℝ) : ℂ) * Complex.I)‖ ≤
        2 * ‖seamFluxCochain ((2 : ℂ) + ((x - y : ℝ) : ℂ) * Complex.I)‖ +
          ‖seamFluxCochain ((1 : ℂ) + ((x - y : ℝ) : ℂ) * Complex.I)‖ := by
      simpa using norm_sub_le
        (2 * seamFluxCochain ((2 : ℂ) + ((x - y : ℝ) : ℂ) * Complex.I))
        (seamFluxCochain ((1 : ℂ) + ((x - y : ℝ) : ℂ) * Complex.I))
    _ ≤ 2 * (C₂ * (1 + |x - y|) ^ 9) +
        C₁ * (1 + |x - y|) ^ 9 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hlineTwo (x - y)) (by norm_num))
        (hlineOne (x - y))
    _ = (C₁ + 2 * C₂) * (1 + |x - y|) ^ 9 := by ring

/-- Two primes in one logarithmic window have log-ratio bounded by the window width. -/
theorem abs_primeLog_sub_le_of_mem_xiPhysicalPrimeLogWindowPacket
    {H T : ℝ} {p q : Nat.Primes}
    (hp : p ∈ xiPhysicalPrimeLogWindowPacket H T)
    (hq : q ∈ xiPhysicalPrimeLogWindowPacket H T) :
    |Real.log (p : ℝ) - Real.log (q : ℝ)| ≤ T - H := by
  rw [mem_xiPhysicalPrimeLogWindowPacket_iff_log] at hp hq
  rw [abs_le]
  constructor <;> linarith

/-- Abstract finite-packet law: a uniform bound for the sampled refinement kernel controls the
whole signed Dirichlet energy by four aperture lengths times squared endpoint mass. -/
theorem abs_xiUnitDoubleCompletedRefinementApertureDirichletEnergy_le_of_kernelBound
    (P : Finset Nat.Primes) {A K : ℝ} (hA : 0 < A) (hK : 0 ≤ K)
    (hkernel : ∀ p ∈ P, ∀ q ∈ P,
      |xiUnitDoubleCompletedPrimeRatioRealKernel p q| ≤ K)
    (m k : ℝ) :
    |xiUnitDoubleCompletedRefinementApertureDirichletEnergy P A m k| ≤
      4 * A * K * xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 := by
  rw [xiUnitDoubleCompletedRefinementApertureDirichletEnergy_eq_kernel_distance]
  calc
    |∑ p ∈ P, ∑ q ∈ P,
        physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
          (-xiUnitDoubleCompletedPrimeRatioRealKernel p q) *
            xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2| ≤
      ∑ p ∈ P, ∑ q ∈ P,
        |physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
          (-xiUnitDoubleCompletedPrimeRatioRealKernel p q) *
            xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun p _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ p ∈ P, ∑ q ∈ P,
        4 * A * K *
          (physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q) := by
      refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
      have hwp : 0 ≤ physicalPrimeEndpointWeight p :=
        (physicalPrimeEndpointWeight_pos p).le
      have hwq : 0 ≤ physicalPrimeEndpointWeight q :=
        (physicalPrimeEndpointWeight_pos q).le
      have hk := hkernel p hp q hq
      have hd := xiPhysicalPrimeLogApertureHilbertDistance_sq_le_four_mul hA m k p q
      rw [abs_mul,
        abs_of_nonneg (sq_nonneg
          (xiPhysicalPrimeLogApertureHilbertDistance A m k p q)),
        abs_mul, abs_mul, abs_neg,
        abs_of_nonneg hwp, abs_of_nonneg hwq]
      let w := physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q
      have hw : 0 ≤ w := mul_nonneg hwp hwq
      calc
        w * |xiUnitDoubleCompletedPrimeRatioRealKernel p q| *
            xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2 ≤
          w * K * xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hk hw) (sq_nonneg _)
        _ ≤ w * K * (4 * A) :=
          mul_le_mul_of_nonneg_left hd (mul_nonneg hw hK)
        _ = 4 * A * K * w := by ring
    _ = 4 * A * K * xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 := by
      rw [xiPhysicalPrimeLogEndpointTotalWeight, sq, Finset.sum_mul_sum]
      simp_rw [Finset.mul_sum]

/-- Explicit scale-free bound for refinement energy on one translated fixed-width packet. -/
theorem abs_xiUnitDoubleCompletedRefinementApertureDirichletEnergy_supportPacket_le
    {C : ℝ} (hC : 0 ≤ C)
    (hglobal : ∀ x y : ℝ,
      ‖xiUnitDoubleCompletedOffDiagonalResponseKernel x y‖ ≤
        C * (1 + |x - y|) ^ 9)
    {A m c : ℝ} (hA : 0 < A) (hc : 0 ≤ c)
    (hlow : 2 ≤ Real.exp (m - A)) :
    |xiUnitDoubleCompletedRefinementApertureDirichletEnergy
        (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c)| ≤
      4 * A * (C * (1 + (A + c)) ^ 9) *
        (A + c + primeLogWindowConst) ^ 2 := by
  let P := xiPhysicalPrimeLogWindowPacket (m - A) (m + c)
  let K := C * (1 + (A + c)) ^ 9
  have hwidth : 0 ≤ A + c := by linarith
  have hK : 0 ≤ K := mul_nonneg hC (pow_nonneg (by linarith) 9)
  have hkernel : ∀ p ∈ P, ∀ q ∈ P,
      |xiUnitDoubleCompletedPrimeRatioRealKernel p q| ≤ K := by
    intro p hp q hq
    have hfreq : |Real.log (p : ℝ) - Real.log (q : ℝ)| ≤ A + c := by
      simpa [P, add_comm] using
        abs_primeLog_sub_le_of_mem_xiPhysicalPrimeLogWindowPacket hp hq
    have hre : |xiUnitDoubleCompletedPrimeRatioRealKernel p q| ≤
        ‖xiUnitDoubleCompletedOffDiagonalResponseKernel
          (Real.log (p : ℝ)) (Real.log (q : ℝ))‖ := by
      exact Complex.abs_re_le_norm _
    have hraw := hglobal (Real.log (p : ℝ)) (Real.log (q : ℝ))
    have hpow :
        (1 + |Real.log (p : ℝ) - Real.log (q : ℝ)|) ^ 9 ≤
          (1 + (A + c)) ^ 9 := by
      exact pow_le_pow_left₀ (by positivity) (by linarith) 9
    calc
      |xiUnitDoubleCompletedPrimeRatioRealKernel p q| ≤
          ‖xiUnitDoubleCompletedOffDiagonalResponseKernel
            (Real.log (p : ℝ)) (Real.log (q : ℝ))‖ := hre
      _ ≤ C * (1 + |Real.log (p : ℝ) - Real.log (q : ℝ)|) ^ 9 := hraw
      _ ≤ C * (1 + (A + c)) ^ 9 := mul_le_mul_of_nonneg_left hpow hC
      _ = K := rfl
  have hbase :=
    abs_xiUnitDoubleCompletedRefinementApertureDirichletEnergy_le_of_kernelBound
      P hA hK hkernel m (m + c)
  have hW : 0 ≤ xiPhysicalPrimeLogEndpointTotalWeight P :=
    xiPhysicalPrimeLogEndpointTotalWeight_nonneg P
  have hWle : xiPhysicalPrimeLogEndpointTotalWeight P ≤
      A + c + primeLogWindowConst := by
    simpa [P] using
      xiPhysicalPrimeLogWindowPacket_totalWeight_le_fixedWidth hA hc hlow
  have hB : 0 ≤ A + c + primeLogWindowConst := hW.trans hWle
  have hsquare : xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 ≤
      (A + c + primeLogWindowConst) ^ 2 :=
    (sq_le_sq₀ hW hB).2 hWle
  have hcoef : 0 ≤ 4 * A * K :=
    mul_nonneg (mul_nonneg (by norm_num) hA.le) hK
  exact hbase.trans (mul_le_mul_of_nonneg_left hsquare hcoef)

/-- Refinement energy is absolutely and uniformly bounded under scale translation for every fixed
positive aperture and fixed nonnegative forward width. -/
theorem exists_uniform_abs_xiUnitDoubleCompletedRefinementApertureDirichletEnergy_fixedWidth
    {A c : ℝ} (hA : 0 < A) (hc : 0 ≤ c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℝ, 2 ≤ Real.exp (m - A) →
      |xiUnitDoubleCompletedRefinementApertureDirichletEnergy
        (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c)| ≤ B := by
  obtain ⟨C, hC, hglobal⟩ :=
    exists_norm_xiUnitDoubleCompletedOffDiagonalResponseKernel_global_le
  let B := 4 * A * (C * (1 + (A + c)) ^ 9) *
    (A + c + primeLogWindowConst) ^ 2
  have hwidth : 0 ≤ A + c := by linarith
  have hmass : 0 ≤ A + c + primeLogWindowConst :=
    add_nonneg hwidth primeLogWindowConst_nonneg
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro m hlow
  exact abs_xiUnitDoubleCompletedRefinementApertureDirichletEnergy_supportPacket_le
    hC hglobal hA hc hlow

/-- Valuation completion preserves the absolute fixed-width bound, not merely one-sided
boundedness. -/
theorem exists_uniform_abs_xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_fixedWidth
    {A c : ℝ} (hA : 0 < A) (hc : 0 ≤ c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℝ, 2 ≤ Real.exp (m - A) →
      |xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy
        (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c)| ≤ B := by
  obtain ⟨B, hB, href⟩ :=
    exists_uniform_abs_xiUnitDoubleCompletedRefinementApertureDirichletEnergy_fixedWidth hA hc
  let K := 4 * A * routeKPhysicalEndpointCorrectionMass *
    (A + c + primeLogWindowConst) ^ 2
  have hwidth : 0 ≤ A + c := by linarith
  have hmass : 0 ≤ A + c + primeLogWindowConst :=
    add_nonneg hwidth primeLogWindowConst_nonneg
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hA.le)
        routeKPhysicalEndpointCorrectionMass_nonneg)
      (sq_nonneg _)
  refine ⟨B + K, add_nonneg hB hK, ?_⟩
  intro m hlow
  have hsplit :=
    xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_eq_refinement_add_correction
      (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c)
  have hrefm := href m hlow
  have hcorr :=
    abs_xiPhysicalEndpointValuationCorrectionApertureDirichletEnergy_supportPacket_le
      hA hc hlow
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hrefm hcorr)

/-- **Fixed-width no-go.** Bare cofinal upper and lower bounds for completed physical endpoint
energy hold unconditionally for every fixed width, so neither condition can distinguish RH. -/
theorem physicalEndpointCompletedFixedWidthEnergy_twoSidedBound :
    ∀ A c : ℝ, 0 < A → 0 ≤ c →
      (∃ B : ℝ, ∀ m : ℝ, 2 ≤ Real.exp (m - A) →
        xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy
          (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c) ≤ B) ∧
      (∃ B : ℝ, ∀ m : ℝ, 2 ≤ Real.exp (m - A) →
        B ≤ xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy
          (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c)) := by
  intro A c hA hc
  obtain ⟨B, _hB, hbound⟩ :=
    exists_uniform_abs_xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_fixedWidth
      hA hc
  constructor
  · refine ⟨B, ?_⟩
    intro m hlow
    exact (le_abs_self _).trans (hbound m hlow)
  · refine ⟨-B, ?_⟩
    intro m hlow
    exact neg_le_of_abs_le (hbound m hlow)

/-- Premise-free unit-window absolute boundedness capstone. -/
theorem unitPhysicalEndpointCompletedFixedWindowEnergyUniformAbsoluteBound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℝ, 2 ≤ Real.exp (m - 1) →
      |xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy
        (xiPhysicalPrimeLogWindowPacket (m - 1) (m + 1)) 1 m (m + 1)| ≤ B := by
  exact exists_uniform_abs_xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_fixedWidth
    (A := 1) (c := 1) (by norm_num) (by norm_num)

/-- Premise-free unit-window two-sided no-go capstone. -/
theorem unitPhysicalEndpointCompletedFixedWindowEnergyTwoSidedBound :
    (∃ B : ℝ, ∀ m : ℝ, 2 ≤ Real.exp (m - 1) →
      xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy
        (xiPhysicalPrimeLogWindowPacket (m - 1) (m + 1)) 1 m (m + 1) ≤ B) ∧
    (∃ B : ℝ, ∀ m : ℝ, 2 ≤ Real.exp (m - 1) →
      B ≤ xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy
        (xiPhysicalPrimeLogWindowPacket (m - 1) (m + 1)) 1 m (m + 1)) := by
  exact physicalEndpointCompletedFixedWidthEnergy_twoSidedBound 1 1 (by norm_num) (by norm_num)

end

end RHTower

import GaloisForLFunctions.RHTower.XiPrimeSeamCofinalAnchoredCommutator
import GaloisForLFunctions.RHTower.SoninCalkinNormBound

/-!
# Cofinal charge-scale essential-norm decay suffices for RH

Exact compactness of the anchored two-prime Euler compression commutator is stronger than the
top-down argument needs.  The finite prime Gram shell estimates recover the full off-diagonal
orientation coefficient from the commutator's Calkin distance:

`|u_2 - u_q| <= sqrt (2*q) * essentialNorm [T_u, T_1]`.

Consequently it is enough, on each Xi divisor fibre, to make the right-hand side arbitrarily
small along arbitrarily large primes.  The unconditional decay of the `q`-seam then kills the
fixed first-prime seam and closes RH.

The same estimate is stated for the finite rational-Hurwitz reflection seams, with all Hurwitz
values shifted into their half-plane of absolute convergence.  Thus the remaining target is a
quantitative source approximation, not an exact compactness identity.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-! ## Quantitative finite-prime Calkin recovery -/

/-- The positive-Euler rescaling divides an orientation coefficient by the geometric mean of
its two prime scales. -/
theorem norm_finiteEulerGramRescale_orientationMatrix
    {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (u : Fin n → ℂ) (k l : Fin n) :
    ‖finiteEulerGramRescale (fun i ↦ (p i : ℝ))
        (finiteEulerOrientationMatrix u) l k‖ =
      ‖u l - u k‖ / (Real.sqrt (p l) * Real.sqrt (p k)) := by
  simp only [finiteEulerGramRescale, finiteEulerOrientationMatrix, norm_mul,
    norm_star, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (Real.sqrt_pos.2 (by exact_mod_cast (hp l).pos)),
    abs_of_pos (Real.sqrt_pos.2 (by exact_mod_cast (hp k).pos))]
  field_simp

/-- Every off-diagonal orientation difference, after its forced positive-Euler normalization,
is bounded by the essential norm of the concrete Hardy--Titchmarsh source Gram. -/
theorem norm_orientationDifference_div_sqrt_le_essentialNorm
    {n : ℕ} {a : ℝ} (ha : 0 < a) (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (u : Fin n → ℂ) (k l : Fin n) (hkl : k ≠ l) :
    ‖u l - u k‖ / (Real.sqrt (p l) * Real.sqrt (p k)) ≤
      essentialNorm
        (finiteArchimedeanEulerOrientationGram a (fun i ↦ (p i : ℝ)) u) := by
  let r : Fin n → ℝ := fun i ↦ (p i : ℝ)
  let hr : ∀ i, 1 < r i := fun i ↦ by
    change (1 : ℝ) < (p i : ℝ)
    exact_mod_cast (hp i).one_lt
  let A := finiteEulerOrientationMatrix u
  let D := finiteEvenDilationGramCombination a r hr (finiteEulerGramRescale r A)
  have hlower : ‖finiteEulerGramRescale r A l k‖ ≤ essentialNorm D := by
    apply le_essentialNorm
    intro K hK
    exact norm_matrixEntry_le_norm_finitePrimeEvenDilationGram_sub_compact
      a ha p hp hinj (finiteEulerGramRescale r A) k l hkl K hK
  have hsource :
      essentialNorm
          (finiteArchimedeanEulerOrientationGram a r u) =
        essentialNorm D := by
    unfold finiteArchimedeanEulerOrientationGram
    rw [finiteArchimedeanPrimeEulerGramCombination_eq_unitaryPush a r hr A,
      essentialNorm_unitaryPush]
    rw [finiteEvenPositiveEulerGramCombination_eq_dilation]
    rfl
  have hrescale : ‖finiteEulerGramRescale r A l k‖ =
      ‖u l - u k‖ / (Real.sqrt (p l) * Real.sqrt (p k)) := by
    simpa [r, A] using norm_finiteEulerGramRescale_orientationMatrix p hp u k l
  rw [← hrescale]
  simpa [r] using hlower.trans_eq hsource.symm

/-- Negation does not change Calkin distance. -/
theorem essentialNorm_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) : essentialNorm (-T) = essentialNorm T := by
  simpa using essentialNorm_smul (-1 : ℂ) T

/-- A compact operator has zero essential norm. -/
theorem essentialNorm_eq_zero_of_isCompactOperator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T : E →L[ℂ] E} (hT : IsCompactOperator T) :
    essentialNorm T = 0 := by
  apply le_antisymm
  · simpa using essentialNorm_le T T hT
  · exact essentialNorm_nonneg T

/-! ## The anchored quantitative source and value interfaces -/

/-- The recovered first-prime orientation defect is bounded by the charge-scale essential norm
of the anchored compressed source commutator.  The factor is exactly `sqrt (2*q)`. -/
theorem norm_primeSeamDifference_le_scaledEssentialNorm_anchoredCommutator
    {a : ℝ} (ha : 0 < a) {rho : ℂ} {q : ℕ}
    (hq : q.Prime) (hq2 : 2 < q) :
    ‖orbitwiseNatPrimeSeamCharge 2 rho - orbitwiseNatPrimeSeamCharge q rho‖ ≤
      Real.sqrt (2 * q : ℕ) *
        essentialNorm (firstPrimeAnchoredEulerCompressionCommutator a rho q) := by
  let p := firstPrimeAnchoredPacket q
  let u : Fin 2 → ℂ := fun i ↦ orbitwiseNatPrimeSeamCharge (p i) rho
  have hp : ∀ i, (p i).Prime := firstPrimeAnchoredPacket_prime hq
  have hinj : Function.Injective p := firstPrimeAnchoredPacket_injective hq2
  have hlower := norm_orientationDifference_div_sqrt_le_essentialNorm
    ha p hp hinj u (1 : Fin 2) (0 : Fin 2) (by decide)
  have horientation :=
    finiteArchimedeanEulerOrientationGram_eq_neg_compression_commutator
      a (fun i ↦ (p i : ℝ))
        (fun i ↦ by
          change (1 : ℝ) < (p i : ℝ)
          exact_mod_cast (hp i).one_lt) u
  have hEN :
      essentialNorm
          (finiteArchimedeanEulerOrientationGram a (fun i ↦ (p i : ℝ)) u) =
        essentialNorm (firstPrimeAnchoredEulerCompressionCommutator a rho q) := by
    rw [horientation, essentialNorm_neg]
    rfl
  rw [hEN] at hlower
  have hden : 0 < Real.sqrt 2 * Real.sqrt q := mul_pos (by positivity)
    (Real.sqrt_pos.2 (by exact_mod_cast hq.pos))
  have hmul := (div_le_iff₀ hden).mp hlower
  have hproduct : Real.sqrt (2 * q : ℕ) = Real.sqrt 2 * Real.sqrt q := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
  rw [hproduct]
  simpa [p, u, firstPrimeAnchoredPacket, mul_comm] using hmul

/-- **Positive off-line Calkin floor.**  At an off-critical strip point, all sufficiently large
prime partners have charge-scale essential norm bounded below by half the fixed first-prime seam.
Thus the `1/sqrt(2*q)` positive-Euler attenuation cannot by itself satisfy the decay criterion. -/
theorem eventually_half_norm_firstPrimeSeamCharge_lt_scaledEssentialNorm_of_re_ne_half
    {a : ℝ} (ha : 0 < a) {rho : ℂ}
    (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hoff : rho.re ≠ 1 / 2) :
    ∃ N : ℕ, ∀ q : ℕ, q.Prime → max N 2 < q →
      ‖orbitwiseFirstPrimeSeamCharge rho‖ / 2 <
        Real.sqrt (2 * q : ℕ) *
          essentialNorm (firstPrimeAnchoredEulerCompressionCommutator a rho q) := by
  let c := orbitwiseNatPrimeSeamCharge 2 rho
  have hcne : c ≠ 0 := by
    simpa [c, orbitwiseNatPrimeSeamCharge_two_eq_firstPrime] using
      (orbitwiseFirstPrimeSeamCharge_eq_zero_iff rho).not.mpr hoff
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hcne
  have hlim := tendsto_orbitwiseNatPrimeSeamCharge hstrip
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) (‖c‖ / 2) (half_pos hcpos)
  refine ⟨N, fun q hq hNq ↦ ?_⟩
  have hq2 : 2 < q := (le_max_right N 2).trans_lt hNq
  have hqN : N ≤ q := (le_max_left N 2).trans (le_of_lt hNq)
  have hqsmall : ‖orbitwiseNatPrimeSeamCharge q rho‖ < ‖c‖ / 2 := by
    simpa [dist_eq_norm] using hN q hqN
  have htri : ‖c‖ ≤
      ‖c - orbitwiseNatPrimeSeamCharge q rho‖ +
        ‖orbitwiseNatPrimeSeamCharge q rho‖ := by
    simpa using norm_add_le
      (c - orbitwiseNatPrimeSeamCharge q rho)
      (orbitwiseNatPrimeSeamCharge q rho)
  have hdiff : ‖c‖ / 2 < ‖c - orbitwiseNatPrimeSeamCharge q rho‖ := by
    linarith
  have hlower :=
    norm_primeSeamDifference_le_scaledEssentialNorm_anchoredCommutator
      ha hq hq2 (rho := rho)
  have hfinal : ‖c‖ / 2 <
      Real.sqrt (2 * q : ℕ) *
        essentialNorm (firstPrimeAnchoredEulerCompressionCommutator a rho q) :=
    hdiff.trans_le (by simpa [c] using hlower)
  simpa [c, orbitwiseNatPrimeSeamCharge_two_eq_firstPrime] using hfinal

/-- Quantitative value form: the same essential norm controls the difference of the two finite
rational-Hurwitz reflection seams in the absolute-convergence half-plane. -/
theorem norm_rationalHurwitzFiberReflectionSeamDifference_le_scaledEssentialNorm
    {a : ℝ} (ha : 0 < a) {rho : ℂ} {q : ℕ}
    (hq : q.Prime) (hq2 : 2 < q)
    (hstrip : 0 < rho.re ∧ rho.re < 1) :
    ‖rationalHurwitzFiberReflectionSeam 2 rho -
        rationalHurwitzFiberReflectionSeam q rho‖ ≤
      Real.sqrt (2 * q : ℕ) *
        essentialNorm (firstPrimeAnchoredEulerCompressionCommutator a rho q) := by
  rw [rationalHurwitzFiberReflectionSeam_eq_primeSeamCharge
      (n := 2) (by norm_num) hstrip,
    rationalHurwitzFiberReflectionSeam_eq_primeSeamCharge
      (n := q) hq.pos hstrip]
  exact norm_primeSeamDifference_le_scaledEssentialNorm_anchoredCommutator
    ha hq hq2

/-! ## Cofinal decay and RH -/

/-- On every Xi divisor fibre, the charge-scale essential norm of the anchored commutator can be
made arbitrarily small at arbitrarily large partner primes. -/
def XiCofinalFirstPrimeEulerCompressionEssentialNormDecay (a : ℝ) : Prop :=
  ∀ (rho : XiDivisorSupport) (ε : ℝ), 0 < ε → ∀ N : ℕ, ∃ q : ℕ,
    q.Prime ∧ max N 2 < q ∧
      Real.sqrt (2 * q : ℕ) *
        essentialNorm
          (firstPrimeAnchoredEulerCompressionCommutator a (rho : ℂ) q) < ε

/-- Cofinal charge-scale essential-norm decay on one strip fibre kills the first-prime seam. -/
theorem firstPrimeSeamCharge_eq_zero_of_cofinal_anchored_essentialNorm_decay
    {a : ℝ} (ha : 0 < a) {rho : ℂ}
    (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ q : ℕ,
      q.Prime ∧ max N 2 < q ∧
        Real.sqrt (2 * q : ℕ) *
          essentialNorm
            (firstPrimeAnchoredEulerCompressionCommutator a rho q) < ε) :
    orbitwiseFirstPrimeSeamCharge rho = 0 := by
  rw [← orbitwiseNatPrimeSeamCharge_two_eq_firstPrime]
  by_contra hne
  let c := orbitwiseNatPrimeSeamCharge 2 rho
  have hd : 0 < dist c 0 := dist_pos.mpr hne
  have hlim := tendsto_orbitwiseNatPrimeSeamCharge hstrip
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) (dist c 0 / 2) (half_pos hd)
  obtain ⟨q, hq, hNq, hsmall⟩ := hdecay (dist c 0 / 2) (half_pos hd) N
  have hq2 : 2 < q := (le_max_right N 2).trans_lt hNq
  have hqN : N ≤ q := (le_max_left N 2).trans (le_of_lt hNq)
  have hqsmall : dist (orbitwiseNatPrimeSeamCharge q rho) 0 < dist c 0 / 2 :=
    hN q hqN
  have hlower :=
    norm_primeSeamDifference_le_scaledEssentialNorm_anchoredCommutator
      ha hq hq2 (rho := rho)
  have hdiff : dist c (orbitwiseNatPrimeSeamCharge q rho) < dist c 0 / 2 := by
    rw [Complex.dist_eq]
    exact hlower.trans_lt hsmall
  have htri := dist_triangle c (orbitwiseNatPrimeSeamCharge q rho) 0
  linarith

/-- Exact cofinal compactness implies the relaxed charge-scale essential-norm decay condition. -/
theorem xiCofinalFirstPrimeEulerCompressionEssentialNormDecay_of_essentiallyCommuting
    {a : ℝ}
    (hcompact : XiCofinalFirstPrimeEulerCompressionEssentiallyCommuting a) :
    XiCofinalFirstPrimeEulerCompressionEssentialNormDecay a := by
  intro rho ε hε N
  obtain ⟨q, hq, hNq, hcompactq⟩ := hcompact rho N
  refine ⟨q, hq, hNq, ?_⟩
  rw [essentialNorm_eq_zero_of_isCompactOperator hcompactq, mul_zero]
  exact hε

/-- **Cofinal scaled essential-norm criterion.**  It is enough that the normalized Calkin
distance tend to zero along some cofinal prime subnet separately on every Xi divisor fibre. -/
theorem xiCofinalFirstPrimeEulerCompressionEssentialNormDecay_iff_riemannHypothesis
    (a : ℝ) (ha : 0 < a) :
    XiCofinalFirstPrimeEulerCompressionEssentialNormDecay a ↔
      RiemannHypothesis := by
  constructor
  · intro hsource
    apply riemannHypothesis_of_xiPrimeSeamChargesCoherent
    apply xiPrimeSeamChargesCoherent_iff_firstPrimeSeamChargesVanish.mpr
    intro rho
    exact firstPrimeSeamCharge_eq_zero_of_cofinal_anchored_essentialNorm_decay
      ha (xi_divisor_support_re_mem_open_unit rho) (hsource rho)
  · intro hRH
    apply xiCofinalFirstPrimeEulerCompressionEssentialNormDecay_of_essentiallyCommuting
    exact (xiCofinalFirstPrimeEulerCompressionEssentiallyCommuting_iff_riemannHypothesis
      a ha).mpr hRH

end

end RHTower

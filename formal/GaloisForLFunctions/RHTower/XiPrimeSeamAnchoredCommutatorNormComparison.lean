import GaloisForLFunctions.RHTower.XiPrimeSeamCalkinGram
import GaloisForLFunctions.RHTower.XiPrimeSeamCofinalAnchoredEssentialNormDecay

/-!
# The anchored Euler commutator norm is faithful to one prime-seam difference

For the two-prime packet `{2, q}`, the finite Euler orientation Gram is exactly the sum of the
two ordered seam-weighted quadratic corners.  The essential norm triangle inequality, the exact
essential norm of each ordered corner, and finite Gram Calkin injectivity therefore give

`cornerNorm <= commutatorNorm <= 2 * cornerNorm`.

After multiplying by the forced positive-Euler scale `sqrt (2*q)`, the corner norm is exactly the
charge difference `|u_2-u_q|`.  Hence the scaled commutator norm and the raw finite value defect
are uniformly equivalent, with constants one and two.  This positively classifies the proposed
commutator-decay source condition: it is a faithful Calkin coordinate for the orientation charge,
not an independent mechanism capable of making that charge vanish.
-/

open Complex

namespace RHTower

noncomputable section

/-- On an anchored two-prime packet, only the two off-diagonal orientation corners survive. -/
theorem anchored_orientationGram_eq_pairCalkinCorners
    (a : ℝ) (rho : ℂ) (q : ℕ) :
    finiteArchimedeanEulerOrientationGram a
        (fun i ↦ (firstPrimeAnchoredPacket q i : ℝ))
        (fun i ↦ orbitwiseNatPrimeSeamCharge
          (firstPrimeAnchoredPacket q i) rho) =
      orbitwisePrimeSeamCalkinGramCorner a 2 q rho +
        orbitwisePrimeSeamCalkinGramCorner a q 2 rho := by
  classical
  simp [finiteArchimedeanEulerOrientationGram,
    finiteArchimedeanPrimeEulerGramCombination,
    finiteEulerOrientationMatrix, firstPrimeAnchoredPacket,
    orbitwisePrimeSeamCalkinGramCorner, Fin.sum_univ_two]

/-- The essential norm of the anchored commutator is at most twice that of either ordered
seam-weighted corner. -/
theorem essentialNorm_anchoredCommutator_le_two_mul_corner
    {a : ℝ} (ha : 0 < a) {rho : ℂ} {q : ℕ}
    (hq : q.Prime) :
    essentialNorm (firstPrimeAnchoredEulerCompressionCommutator a rho q) ≤
      2 * essentialNorm (orbitwisePrimeSeamCalkinGramCorner a 2 q rho) := by
  let p := firstPrimeAnchoredPacket q
  let u : Fin 2 → ℂ := fun i ↦ orbitwiseNatPrimeSeamCharge (p i) rho
  have hp : ∀ i, (p i).Prime := firstPrimeAnchoredPacket_prime hq
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
  have hpair := anchored_orientationGram_eq_pairCalkinCorners a rho q
  have htri := essentialNorm_add_le
    (orbitwisePrimeSeamCalkinGramCorner a 2 q rho)
    (orbitwisePrimeSeamCalkinGramCorner a q 2 rho)
  calc
    essentialNorm (firstPrimeAnchoredEulerCompressionCommutator a rho q) =
        essentialNorm
          (finiteArchimedeanEulerOrientationGram a (fun i ↦ (p i : ℝ)) u) := hEN.symm
    _ = essentialNorm
        (orbitwisePrimeSeamCalkinGramCorner a 2 q rho +
          orbitwisePrimeSeamCalkinGramCorner a q 2 rho) := by
            rw [hpair]
    _ ≤ essentialNorm (orbitwisePrimeSeamCalkinGramCorner a 2 q rho) +
          essentialNorm (orbitwisePrimeSeamCalkinGramCorner a q 2 rho) := htri
    _ = 2 * essentialNorm (orbitwisePrimeSeamCalkinGramCorner a 2 q rho) := by
      rw [essentialNorm_orbitwisePrimeSeamCalkinGramCorner
          a 2 q rho ha (by norm_num) hq,
        essentialNorm_orbitwisePrimeSeamCalkinGramCorner
          a q 2 rho ha hq (by norm_num), norm_sub_rev]
      ring

/-- Finite prime Gram injectivity supplies the reverse comparison: one ordered seam corner cannot
have larger essential norm than the complete anchored commutator. -/
theorem essentialNorm_corner_le_anchoredCommutator
    {a : ℝ} (ha : 0 < a) {rho : ℂ} {q : ℕ}
    (hq : q.Prime) (hq2 : 2 < q) :
    essentialNorm (orbitwisePrimeSeamCalkinGramCorner a 2 q rho) ≤
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
  calc
    essentialNorm (orbitwisePrimeSeamCalkinGramCorner a 2 q rho) =
        ‖orbitwiseNatPrimeSeamCharge 2 rho -
          orbitwiseNatPrimeSeamCharge q rho‖ *
            (Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ))⁻¹ :=
      essentialNorm_orbitwisePrimeSeamCalkinGramCorner
        a 2 q rho ha (by norm_num) hq
    _ = ‖orbitwiseNatPrimeSeamCharge 2 rho -
          orbitwiseNatPrimeSeamCharge q rho‖ /
            (Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ)) := by
      rw [div_eq_mul_inv]
    _ ≤ essentialNorm (firstPrimeAnchoredEulerCompressionCommutator a rho q) := by
      simpa [p, u, firstPrimeAnchoredPacket] using hlower

/-- The forced charge scaling cancels the exact positive-Euler essential norm of one ordered
corner, recovering precisely the raw two-prime value defect. -/
theorem scaledEssentialNorm_corner_eq_seamDifference
    {a : ℝ} (ha : 0 < a) {rho : ℂ} {q : ℕ}
    (hq : q.Prime) :
    Real.sqrt (2 * q : ℕ) *
        essentialNorm (orbitwisePrimeSeamCalkinGramCorner a 2 q rho) =
      ‖orbitwiseNatPrimeSeamCharge 2 rho -
        orbitwiseNatPrimeSeamCharge q rho‖ := by
  rw [essentialNorm_orbitwisePrimeSeamCalkinGramCorner
    a 2 q rho ha (by norm_num) hq]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hproduct : Real.sqrt (2 * q : ℕ) =
      Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
  rw [hproduct]
  field_simp
  ring_nf

/-- **Uniform norm equivalence.**  The charge-scale essential norm of the complete anchored
commutator lies between one and two times the raw prime-seam difference. -/
theorem scaledEssentialNorm_anchoredCommutator_between_seamDifference
    {a : ℝ} (ha : 0 < a) {rho : ℂ} {q : ℕ}
    (hq : q.Prime) (hq2 : 2 < q) :
    ‖orbitwiseNatPrimeSeamCharge 2 rho -
        orbitwiseNatPrimeSeamCharge q rho‖ ≤
        Real.sqrt (2 * q : ℕ) *
          essentialNorm (firstPrimeAnchoredEulerCompressionCommutator a rho q) ∧
      Real.sqrt (2 * q : ℕ) *
          essentialNorm (firstPrimeAnchoredEulerCompressionCommutator a rho q) ≤
        2 * ‖orbitwiseNatPrimeSeamCharge 2 rho -
          orbitwiseNatPrimeSeamCharge q rho‖ := by
  constructor
  · exact norm_primeSeamDifference_le_scaledEssentialNorm_anchoredCommutator
      ha hq hq2
  · have hupper := essentialNorm_anchoredCommutator_le_two_mul_corner
      ha hq (rho := rho)
    have hscale : 0 ≤ Real.sqrt (2 * q : ℕ) := Real.sqrt_nonneg _
    calc
      Real.sqrt (2 * q : ℕ) *
          essentialNorm (firstPrimeAnchoredEulerCompressionCommutator a rho q) ≤
        Real.sqrt (2 * q : ℕ) *
          (2 * essentialNorm (orbitwisePrimeSeamCalkinGramCorner a 2 q rho)) :=
        mul_le_mul_of_nonneg_left hupper hscale
      _ = 2 * (Real.sqrt (2 * q : ℕ) *
          essentialNorm (orbitwisePrimeSeamCalkinGramCorner a 2 q rho)) := by ring
      _ = 2 * ‖orbitwiseNatPrimeSeamCharge 2 rho -
          orbitwiseNatPrimeSeamCharge q rho‖ := by
        rw [scaledEssentialNorm_corner_eq_seamDifference ha hq]

end

end RHTower

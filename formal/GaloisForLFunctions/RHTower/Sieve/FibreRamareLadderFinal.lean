import GaloisForLFunctions.RHTower.Sieve.RamareBilinearKernelBound
import GaloisForLFunctions.RHTower.Sieve.FibreRamareBilinearBridge
import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetFromAnnulus

/-!
# The Route E fibre mean square, paid by the Ramaré ladder

The fibre capstone reduces the mean square to the kernel-weighted bilinear mean square; the ladder
supplies the affine majorant of that mean square from two sup bounds — the prime polynomial away
from zero frequency, the cofactor polynomial near it.  Unlike the `ω_P`-weighted route, the cofactor
here is the exact Ramaré one, so no Turán–Kubilius variance enters and nothing is divided by the
harmonic mass of the prime range.
-/

namespace RHTower.Sieve

open Finset MeasureTheory ArithmeticFunction

noncomputable section

/-- The prime-polynomial bound of a ladder step off the low window. -/
def ladderPrimeSup (Q η ρ : ℝ) (j : ℕ) : ℝ := ρ * (Q * (1 + η) ^ j)

/-- The cofactor bound of a ladder step on the low window. -/
def ladderCofactorSup (M : ℕ) (Q η s : ℝ) (j : ℕ) : ℝ := s * ((M : ℝ) / (Q * (1 + η) ^ j))

/-- The trivial prime-polynomial bound of a ladder step. -/
def ladderPrimeCard (P : Finset ℕ) (Q η : ℝ) (j : ℕ) : ℝ :=
  ((geomBlock P Q (1 + η) j).card : ℝ)

/-- **The affine majorant of the Ramaré bilinear mean square, from the two sup bounds.** -/
theorem integral_normSq_ramareBilinear_ladder_affine {P : Finset ℕ} (M : ℕ)
    {Q η w₀ G T₀ ρ s : ℝ} (hQ : 1 < Q) (hη : 0 ≤ η) (hG : 1 ≤ G) (_hGT₀ : G ≤ T₀)
    (hw₀ : 0 ≤ w₀) (hwG : w₀ ≤ G) {L : ℕ} (hL : 1 ≤ L) (hρ : 0 ≤ ρ) (hs : 0 ≤ s)
    (hPprime : ∀ q ∈ P, q.Prime) (hPge : ∀ p ∈ P, Q ≤ (p : ℝ))
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    (hV : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-T₀) T₀ \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ ladderPrimeSup Q η ρ j)
    (hU : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖
        ≤ ladderCofactorSup M Q η s j) :
    ∀ T : ℝ, G ≤ T → T ≤ T₀ →
      (∫ w in Set.Icc (-T) T, ‖ramareBilinear P M w‖ ^ (2 : ℕ))
        ≤ ramareLadderSlope M L Q η (ladderPrimeSup Q η ρ) * T
          + ramareLadderConst M L Q η w₀ (ladderPrimeSup Q η ρ) (ladderCofactorSup M Q η s)
              (ladderPrimeCard P Q η) := by
  intro T hGT hTT₀
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ
  have hT1 : (1 : ℝ) ≤ T := le_trans hG hGT
  have hwT : w₀ ≤ T := le_trans hwG hGT
  have hVpos : ∀ j, 0 ≤ ladderPrimeSup Q η ρ j := by
    intro j
    have : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    rw [ladderPrimeSup]
    positivity
  have hUpos : ∀ j, 0 ≤ ladderCofactorSup M Q η s j := by
    intro j
    have : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    rw [ladderCofactorSup]
    positivity
  have hVlowpos : ∀ j, 0 ≤ ladderPrimeCard P Q η j := fun j => Nat.cast_nonneg _
  have hVT : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-T) T \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ ladderPrimeSup Q η ρ j := by
    intro j hj w hw
    refine hV j hj w ⟨?_, hw.2⟩
    have hwT' : w ∈ Set.Icc (-T) T := hw.1
    rw [Set.mem_Icc] at hwT' ⊢
    exact ⟨by linarith [hwT'.1], by linarith [hwT'.2]⟩
  have hlowP : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ ladderPrimeCard P Q η j := by
    intro j _ w _
    exact norm_primeBlockPoly_le_card _ w
  exact integral_normSq_ramareBilinear_affine_le M hQ hη hT1 hw₀ hwT hL hPprime hPge hP
    (ladderPrimeSup Q η ρ) (ladderCofactorSup M Q η s) (ladderPrimeCard P Q η)
    hVpos hUpos hVlowpos hVT hlowP hU

/-- **The Route E fibre mean square, fully paid by the Ramaré ladder.** -/
theorem sum_sq_fibreSum_moebius_le_ramareLadder_final {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h)
    (hhx : h ≤ Real.sqrt x) {z r : ℕ} (hz : 2 ≤ z) (hr : Even r) {lam : ℝ} (hlam : 1 ≤ lam)
    {M L : ℕ} {Q η w₀ G T₀ ρ s : ℝ} (hM : M = ⌊Real.sqrt x + h⌋₊)
    (hδ : 0 < fibreWidth x h)
    (hQ : 1 < Q) (hη : 0 ≤ η) (hG : 1 ≤ G) (hGT₀ : G ≤ T₀) (hw₀ : 0 ≤ w₀) (hwG : w₀ ≤ G)
    (hL : 1 ≤ L) (hρ : 0 ≤ ρ) (hs : 0 ≤ s)
    (hPge : ∀ p ∈ Nat.primesLE z, Q ≤ (p : ℝ))
    (hP : ∀ p ∈ Nat.primesLE z, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    (hV : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-T₀) T₀ \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock (Nat.primesLE z) Q (1 + η) j) w‖ ≤ ladderPrimeSup Q η ρ j)
    (hU : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly (ramareCofactorCoeff (Nat.primesLE z)) (geomCofactorBlock M Q η j) w‖
        ≤ ladderCofactorSup M Q η s j) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ (2 : ℕ)
      ≤ 16 * Real.sqrt x
          * (2 * (fibreWidth x h) ^ (2 : ℕ)
              * (ramareLadderSlope M L Q η (ladderPrimeSup Q η ρ) * G
                + ramareLadderConst M L Q η w₀ (ladderPrimeSup Q η ρ)
                    (ladderCofactorSup M Q η s) (ladderPrimeCard (Nat.primesLE z) Q η))
            + (4 * (ramareLadderSlope M L Q η (ladderPrimeSup Q η ρ)
                    + 5 * Real.pi / 2 * (M : ℝ)
                    + 5 * Real.exp 1 / 2 * (M : ℝ) * (M : ℝ) / T₀)
                / (Real.pi ^ (2 : ℕ) * G)
              + 4 * ramareLadderConst M L Q η w₀ (ladderPrimeSup Q η ρ)
                    (ladderCofactorSup M Q η s) (ladderPrimeCard (Nat.primesLE z) Q η)
                / (3 * Real.pi ^ (2 : ℕ) * G ^ (2 : ℕ))))
        + 204 * (Real.sqrt x + 1)
        + 2 * ((outerBlock x h).card : ℝ) * (fibreRamareSieveError h z r lam) ^ (2 : ℕ) := by
  classical
  have hPprime : ∀ q ∈ Nat.primesLE z, q.Prime := fun q hq => Nat.prime_of_mem_primesLE hq
  have hmid := integral_normSq_ramareBilinear_ladder_affine (P := Nat.primesLE z) M hQ hη hG
    hGT₀ hw₀ hwG hL hρ hs hPprime hPge hP hV hU
  have hhead := hmid G le_rfl hGT₀
  have hslope0 : 0 ≤ ramareLadderSlope M L Q η (ladderPrimeSup Q η ρ) :=
    ramareLadderSlope_nonneg hQ hη _
  have hconst0 : 0 ≤ ramareLadderConst M L Q η w₀ (ladderPrimeSup Q η ρ)
      (ladderCofactorSup M Q η s) (ladderPrimeCard (Nat.primesLE z) Q η) :=
    ramareLadderConst_nonneg hQ hη hw₀ _ _ _
  have hkern := integral_kernel_normSq_ramareBilinear_le (P := Nat.primesLE z) (M := M)
    (δ := fibreWidth x h) hPprime hδ hG hGT₀ hslope0 hconst0 hhead hmid
  have hbridge := sum_sq_fibreSum_moebius_le_ramareBilinear_ladder hx hh0 hhx hz hr hlam
  rw [← hM] at hbridge
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hmul := mul_le_mul_of_nonneg_left hkern (by positivity : (0 : ℝ) ≤ 16 * Real.sqrt x)
  linarith [hbridge, hmul]

end

end RHTower.Sieve

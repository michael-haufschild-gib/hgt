import GaloisForLFunctions.RHTower.Sieve.RamareBilinearKernelBound
import GaloisForLFunctions.RHTower.Sieve.FibreRamareBilinearBridge
import GaloisForLFunctions.RHTower.Sieve.RamareAffinePartitioned

/-!
# The Route E fibre mean square, paid by a partitioned Ramaré ladder

`Sieve/FibreRamareLadderFinal` pays the ladder with two sup bounds: the prime polynomial away from
zero frequency, the cofactor polynomial near it.  A pointwise prime bound on the whole annulus is
too strong — the phases of a short prime block align somewhere in every long window.  The
partitioned form replaces it by a measurable frequency set `S`: on `S` the prime polynomial is
small pointwise, and off `S` only the cofactor is bounded pointwise while the prime polynomial is
paid in mean square.  Everything else in the chain — the Gallagher kernel step and the fibre
bridge — is unchanged, because both are parametric in the slope and the constant.
-/

namespace RHTower.Sieve

open Finset MeasureTheory ArithmeticFunction

noncomputable section

/-- **The Route E fibre mean square, paid by a partitioned Ramaré ladder.** -/
theorem sum_sq_fibreSum_moebius_le_ramarePartitioned_final {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h)
    (hhx : h ≤ Real.sqrt x) {z r : ℕ} (hz : 2 ≤ z) (hr : Even r) {lam : ℝ} (hlam : 1 ≤ lam)
    {M L : ℕ} {Q η w₀ G T₀ Dslope Dconst : ℝ} (hM : M = ⌊Real.sqrt x + h⌋₊)
    (hδ : 0 < fibreWidth x h)
    (hQ : 1 < Q) (hη : 0 ≤ η) (hG : 1 ≤ G) (hGT₀ : G ≤ T₀) (hw₀ : 0 ≤ w₀) (hwG : w₀ ≤ G)
    (hL : 1 ≤ L) (hDs : 0 ≤ Dslope) (hDc : 0 ≤ Dconst)
    (hP : ∀ p ∈ Nat.primesLE z, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    (hDfct : ∀ W : ℝ, 1 ≤ W → W ≤ T₀ →
      (∫ w in Set.Icc (-W) W, ‖ramareLadderError (Nat.primesLE z) M Q η L w‖ ^ (2 : ℕ))
        ≤ Dslope * W + Dconst)
    {S : Set ℝ} (hSm : MeasurableSet S)
    (V U Vlow Us J : ℕ → ℝ) (hV : ∀ j, 0 ≤ V j) (hU : ∀ j, 0 ≤ U j) (hVlow : ∀ j, 0 ≤ Vlow j)
    (hJ0 : ∀ j, 0 ≤ J j)
    (hann : ∀ j ∈ Finset.range L, ∀ w ∈ S \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock (Nat.primesLE z) Q (1 + η) j) w‖ ≤ V j)
    (hcof : ∀ j ∈ Finset.range L, ∀ w ∈ (Set.Icc (-T₀) T₀ \ S) \ Set.Icc (-w₀) w₀,
      ‖logPoly (ramareCofactorCoeff (Nat.primesLE z)) (geomCofactorBlock M Q η j) w‖ ≤ Us j)
    (hJ : ∀ j ∈ Finset.range L,
      (∫ w in (Set.Icc (-T₀) T₀ \ S) \ Set.Icc (-w₀) w₀,
        ‖primeBlockPoly (geomBlock (Nat.primesLE z) Q (1 + η) j) w‖ ^ (2 : ℕ)) ≤ J j)
    (hlowP : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock (Nat.primesLE z) Q (1 + η) j) w‖ ≤ Vlow j)
    (hlowC : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly (ramareCofactorCoeff (Nat.primesLE z)) (geomCofactorBlock M Q η j) w‖ ≤ U j) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ (2 : ℕ)
      ≤ 16 * Real.sqrt x
          * (2 * (fibreWidth x h) ^ (2 : ℕ)
              * (ramarePartSlope M L Q η V Dslope * G
                + ramarePartConst M L Q η w₀ V U Vlow Us J Dconst)
            + (4 * (ramarePartSlope M L Q η V Dslope
                    + 5 * Real.pi / 2 * (M : ℝ)
                    + 5 * Real.exp 1 / 2 * (M : ℝ) * (M : ℝ) / T₀)
                / (Real.pi ^ (2 : ℕ) * G)
              + 4 * ramarePartConst M L Q η w₀ V U Vlow Us J Dconst
                / (3 * Real.pi ^ (2 : ℕ) * G ^ (2 : ℕ))))
        + 204 * (Real.sqrt x + 1)
        + 2 * ((outerBlock x h).card : ℝ) * (fibreRamareSieveError h z r lam) ^ (2 : ℕ) := by
  classical
  have hPprime : ∀ q ∈ Nat.primesLE z, q.Prime := fun q hq => Nat.prime_of_mem_primesLE hq
  have hmid := integral_normSq_ramareBilinear_affine_partitioned_le (P := Nat.primesLE z) M hQ hη
    hw₀ hL hP hDfct hSm V U Vlow Us J hV hU hVlow hann hcof hJ hlowP hlowC
  have hmid' : ∀ T : ℝ, G ≤ T → T ≤ T₀ →
      (∫ w in Set.Icc (-T) T, ‖ramareBilinear (Nat.primesLE z) M w‖ ^ (2 : ℕ))
        ≤ ramarePartSlope M L Q η V Dslope * T
          + ramarePartConst M L Q η w₀ V U Vlow Us J Dconst := by
    intro T hGT hTT₀
    exact hmid T (le_trans hG hGT) (le_trans hwG hGT) hTT₀
  have hhead := hmid' G le_rfl hGT₀
  have hslope0 : 0 ≤ ramarePartSlope M L Q η V Dslope :=
    ramarePartSlope_nonneg M L Q η V hDs
  have hconst0 : 0 ≤ ramarePartConst M L Q η w₀ V U Vlow Us J Dconst :=
    ramarePartConst_nonneg M L Q η hw₀ V U Vlow Us J hJ0 hDc
  have hkern := integral_kernel_normSq_ramareBilinear_le (P := Nat.primesLE z) (M := M)
    (δ := fibreWidth x h) hPprime hδ hG hGT₀ hslope0 hconst0 hhead hmid'
  have hbridge := sum_sq_fibreSum_moebius_le_ramareBilinear_ladder hx hh0 hhx hz hr hlam
  rw [← hM] at hbridge
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hmul := mul_le_mul_of_nonneg_left hkern (by positivity : (0 : ℝ) ≤ 16 * Real.sqrt x)
  linarith [hbridge, hmul]

end

end RHTower.Sieve

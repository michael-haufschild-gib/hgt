import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheRobustIndexOfTheFiniteComb
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheRobustCombDirectionsTransferToStepPackets

/-!
# The robust comb index creates no extra right zeros

Block averaging maps every negative subspace with a fixed mass margin
injectively into the nested-window Weil Gram. Simultaneous smoothing then
bounds its dimension by the number of distinct right zeros.
-/

noncomputable section

open Finset Filter Topology Matrix Zeta23

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open HTGeometry AbsoluteGeometryOfSpecZ ArithmeticCastelnuovoSeveri

/-- Complex block averages, as a linear map. -/
def complexBlockMean (N B J : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun c j := Complex.ofReal ((B : ℝ)⁻¹) *
    ∑ n ∈ (Ioc N (N + B * J)).filter (fun n => blockIndex N B n = j), c n
  map_add' c d := by
    ext j
    simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' a c := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

theorem complexBlockMean_re (N B J : ℕ) (c : ℕ → ℂ) (j : ℕ) :
    (complexBlockMean N B J c j).re = blockMean N B J (fun n => (c n).re) j := by
  simp only [complexBlockMean, LinearMap.coe_mk, AddHom.coe_mk, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_sum, zero_mul, sub_zero,
    blockMean, div_eq_mul_inv, mul_comm]

theorem complexBlockMean_im (N B J : ℕ) (c : ℕ → ℂ) (j : ℕ) :
    (complexBlockMean N B J c j).im = blockMean N B J (fun n => (c n).im) j := by
  simp only [complexBlockMean, LinearMap.coe_mk, AddHom.coe_mk, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.im_sum, zero_mul, add_zero,
    blockMean, div_eq_mul_inv, mul_comm]

/-- The summation-by-parts map from complex block values to nested windows. -/
def complexNestedCoeff (J : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (Fin (J + 1) → ℂ) where
  toFun c j := (if (j : ℕ) = 0 then 0 else c ((j : ℕ) - 1)) -
    if (j : ℕ) < J then c j else 0
  map_add' c d := by
    ext j
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' a c := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem complexNestedCoeff_re (J : ℕ) (c : ℕ → ℂ) (j : Fin (J + 1)) :
    (complexNestedCoeff J c j).re = nestedCoeff J (fun n => (c n).re) j := by
  simp only [complexNestedCoeff, LinearMap.coe_mk, AddHom.coe_mk, nestedCoeff, lowerValue,
    Complex.sub_re]
  split_ifs <;> simp

theorem complexNestedCoeff_im (J : ℕ) (c : ℕ → ℂ) (j : Fin (J + 1)) :
    (complexNestedCoeff J c j).im = nestedCoeff J (fun n => (c n).im) j := by
  simp only [complexNestedCoeff, LinearMap.coe_mk, AddHom.coe_mk, nestedCoeff, lowerValue,
    Complex.sub_im]
  split_ifs <;> simp

/-- The finite nested Gram on block coefficients is exactly the sum of
the two real step-packet forms. -/
theorem hermQuad_complexNestedCoeff {R J Q : ℕ} (hR : 1 ≤ R) (c : ℕ → ℂ) :
    hermQuad (packetFormGram Q
      (fun j : Fin (J + 1) => flatPacket (R : ℝ) ((R + (j : ℕ) : ℕ) : ℝ)))
        (complexNestedCoeff J c) =
      packetForm Q (stepPacket R J (fun n => (c n).re)) +
        packetForm Q (stepPacket R J (fun n => (c n).im)) := by
  have hx : ∀ j : Fin (J + 1), R ≤ R + (j : ℕ) ∧ R + (j : ℕ) ≤ R + J := by
    intro j
    constructor
    · exact Nat.le_add_right _ _
    · have := j.isLt
      omega
  rw [hermQuad_packetFormGram_nested hR _ hx]
  simp only [complexNestedCoeff_re, complexNestedCoeff_im]
  have hpacket (σ : ℕ → ℝ) :
      (fun u => ∑ j : Fin (J + 1), nestedCoeff J σ j *
        flatPacket (R : ℝ) ((R + (j : ℕ) : ℕ) : ℝ) u) =
        stepPacket R J σ := by
    rw [stepPacket_eq_nested hR J σ]
    funext u
    exact Fin.sum_univ_eq_sum_range
      (fun j => nestedCoeff J σ j * flatPacket (R : ℝ) ((R + j : ℕ) : ℝ) u) (J + 1)
  rw [hpacket, hpacket]

/-- Every robust finite-comb negative subspace eventually has dimension
at most the number of distinct zeta zeros strictly right of the line. -/
theorem eventually_robustCombIndex_le_rightZeros (K : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      robustCombIndex (Ioc N (N + 3 * K * N)) η ≤ (rightZeros zetaZeroConfig).encard := by
  obtain ⟨R, hR, hev⟩ := exists_block_transfer_to_stepPacket K hη
  filter_upwards [hev] with N hN
  let J := (6 * K + 1) * R
  let S := Ioc N (N + 3 * K * N)
  let A : (S → ℂ) →ₗ[ℂ] (Fin (J + 1) → ℂ) :=
    (complexNestedCoeff J).comp
      ((complexBlockMean (R * (N / R)) (N / R) J).comp (combExtension S))
  let H := packetFormGram (6 * K + 2)
    (fun j : Fin (J + 1) => flatPacket (R : ℝ) ((R + (j : ℕ) : ℕ) : ℝ))
  have htransfer : robustCombIndex S η ≤ (hermNegIndex H : ℕ∞) := by
    apply robustCombIndex_le_of_linear_transfer H A
    intro c hc
    have hp_re : (fun n => if n ∈ S then (combExtension S c n).re else 0) =
        fun n => (combExtension S c n).re := by
      funext n
      by_cases hn : n ∈ S <;> simp [combExtension, hn]
    have hp_im : (fun n => if n ∈ S then (combExtension S c n).im else 0) =
        fun n => (combExtension S c n).im := by
      funext n
      by_cases hn : n ∈ S <;> simp [combExtension, hn]
    have hr := hN.2 (fun n => (combExtension S c n).re)
    have hi := hN.2 (fun n => (combExtension S c n).im)
    change (N / R : ℕ) * packetForm (6 * K + 2)
      (stepPacket R J (blockMean (R * (N / R)) (N / R) J
        (fun n => if n ∈ S then (combExtension S c n).re else 0))) ≤ _ at hr
    change (N / R : ℕ) * packetForm (6 * K + 2)
      (stepPacket R J (blockMean (R * (N / R)) (N / R) J
        (fun n => if n ∈ S then (combExtension S c n).im else 0))) ≤ _ at hi
    rw [hp_re] at hr
    rw [hp_im] at hi
    have hm := combExtension_mass S c
    have hsum : (N / R : ℕ) * hermQuad H (A c) < 0 := by
      change (N / R : ℕ) * hermQuad H
        (complexNestedCoeff J (complexBlockMean (R * (N / R)) (N / R) J
          (combExtension S c))) < 0
      rw [hermQuad_complexNestedCoeff hR]
      simp only [complexBlockMean_re, complexBlockMean_im]
      change combForm S (fun n => (combExtension S c n).re) +
        combForm S (fun n => (combExtension S c n).im) + η * ∑ i, ‖c i‖ ^ 2 < 0 at hc
      rw [← hm] at hc
      nlinarith only [hr, hi, hc]
    by_contra hnonneg
    exact (not_lt_of_ge (mul_nonneg (Nat.cast_nonneg (N / R))
      (le_of_not_gt hnonneg))) hsum
  apply htransfer.trans
  apply negIndex_nested_packetFormGram_le_rightZeros hR (by omega)
    (fun j : Fin (J + 1) => R + (j : ℕ)) (X := R + J)
  · intro j
    have := j.isLt
    constructor <;> omega
  · dsimp [J]
    exact le_of_eq (by ring)

end GaloisForLFunctions.HodgeTheoryOfAFixedPart

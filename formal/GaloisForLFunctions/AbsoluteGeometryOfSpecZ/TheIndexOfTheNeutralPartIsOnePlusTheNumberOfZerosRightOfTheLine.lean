import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePoleAddsOneNegativeSquareToTheBlockMatrixOfAWindow
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheRobustCombIndexCountsRightZeros

/-!
# The index of the neutral part is one plus the number of zeros right of the line

The index law of the step-packet matrices at finite scale, over all windows `(R, R + J]`:

* the block matrix of a window has `r` negative squares on some window iff there are at least
  `r` zeros right of the critical line (`exists_le_hermNegIndex_blockWindow_iff`);
* its neutral part has `r` negative squares on some window iff `r` is at most one plus the
  number of zeros right of the line (`exists_le_hermNegIndex_neutralWindow_iff`).

So the neutral part of the step-packet matrices has the index of Weil's form of the zeros minus
the poles: the pole `s = 1` and the zeros right of the line.

* **Upper bounds.** A step packet is a bounded packet, and bounded packets create no negative
  square beyond the zeros right of the line; the form of the block matrix is the form of the
  nested Gram matrix on the nested coefficients (`hermNegIndex_blockWindow_le_rightZeros`). The
  index of the neutral part exceeds that of the block matrix by at most one.
* **Attainment.** A negative direction of the comb with a mass margin survives the block means
  as a negative step packet, and the robust index of the comb counts the zeros right of the
  line (`exists_le_hermNegIndex_blockWindow`). The pole adds one negative square.
-/

open Finset Filter Topology Matrix Zeta23
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The form of the block matrix of a window on complex block values is the sum of the two real
step-packet forms. -/
theorem hermQuad_blockWindow_restrict {R : ℕ} (hR : 1 ≤ R) (Q J : ℕ) (c : ℕ → ℂ) :
    hermQuad ((blockWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ)
        (fun i : Fin J => c i) =
      packetForm Q (stepPacket R J fun n => (c n).re) +
        packetForm Q (stepPacket R J fun n => (c n).im) := by
  rw [HeckeKreinToeplitz.hermQuad_map_ofReal, dotProduct_mulVec_eq_sum,
    dotProduct_mulVec_eq_sum, blockWindow,
    sum_fin_windowMatrix_coe (blockMatrix Q) R J (fun n => (c n).re),
    sum_fin_windowMatrix_coe (blockMatrix Q) R J (fun n => (c n).im),
    packetForm_stepPacket_eq_sum_blockMatrix hR, packetForm_stepPacket_eq_sum_blockMatrix hR]

/-- Complex block values of a window, extended by zero. -/
def complexExtend (J : ℕ) : (Fin J → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun c n := if h : n < J then c ⟨n, h⟩ else 0
  map_add' c d := by
    ext n
    by_cases hn : n < J <;> simp [hn]
  map_smul' a c := by
    ext n
    by_cases hn : n < J <;> simp [hn]

theorem complexExtend_coe {J : ℕ} (c : Fin J → ℂ) (i : Fin J) : complexExtend J c i = c i :=
  dif_pos i.2

/-- **The block matrix of a window has at most as many negative squares as there are zeros
right of the line.** -/
theorem hermNegIndex_blockWindow_le_rightZeros {Q R J : ℕ} (hR : 1 ≤ R) (hQ : R + J ≤ Q * R) :
    (hermNegIndex ((blockWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) : ℕ∞) ≤
      (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard := by
  have hQ1 : 1 ≤ Q := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · subst h
      omega
    · exact h
  -- the form of the block matrix is the form of the nested Gram matrix
  have hle : hermNegIndex ((blockWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤
      hermNegIndex (packetFormGram Q
        (fun j : Fin (J + 1) => flatPacket (R : ℝ) ((R + (j : ℕ) : ℕ) : ℝ))) := by
    refine HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_eq _ _
      ((HodgeTheoryOfAFixedPart.complexNestedCoeff J).comp (complexExtend J)) fun c => ?_
    show hermQuad _ (HodgeTheoryOfAFixedPart.complexNestedCoeff J (complexExtend J c)) = _
    rw [HodgeTheoryOfAFixedPart.hermQuad_complexNestedCoeff hR,
      ← hermQuad_blockWindow_restrict hR]
    congr 1
    funext i
    exact complexExtend_coe c i
  refine (ENat.coe_le_coe.mpr hle).trans ?_
  apply negIndex_nested_packetFormGram_le_rightZeros hR hQ1
    (fun j : Fin (J + 1) => R + (j : ℕ)) (X := R + J)
  · intro j
    have := j.isLt
    constructor <;> omega
  · exact hQ

/-- **The block matrices attain the number of zeros right of the line.** -/
theorem exists_le_hermNegIndex_blockWindow {r : ℕ}
    (hr : (r : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard) :
    ∃ Q R J : ℕ, 1 ≤ R ∧ R + J ≤ Q * R ∧
      r ≤ hermNegIndex ((blockWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) := by
  obtain ⟨K, -, η, hη, hev⟩ :=
    (HodgeTheoryOfAFixedPart.nat_le_rightZeros_iff_eventual_robustCombIndex r).mp hr
  obtain ⟨R, hR, hev₂⟩ := HodgeTheoryOfAFixedPart.exists_block_transfer_to_stepPacket K hη
  obtain ⟨N, hN, hN₂⟩ := (hev.and hev₂).exists
  refine ⟨6 * K + 2, R, (6 * K + 1) * R, hR, le_of_eq (by ring), ?_⟩
  -- the block means carry the robust negative directions of the comb to step packets
  have htransfer : HodgeTheoryOfAFixedPart.robustCombIndex (Ioc N (N + 3 * K * N)) η ≤
      (hermNegIndex ((blockWindow (6 * K + 2) R ((6 * K + 1) * R)).map (↑) :
        Matrix (Fin ((6 * K + 1) * R)) (Fin ((6 * K + 1) * R)) ℂ) : ℕ∞) := by
    apply HodgeTheoryOfAFixedPart.robustCombIndex_le_of_linear_transfer _
      ((LinearMap.funLeft ℂ ℂ (fun i : Fin ((6 * K + 1) * R) => (i : ℕ))).comp
        ((HodgeTheoryOfAFixedPart.complexBlockMean (R * (N / R)) (N / R)
          ((6 * K + 1) * R)).comp
          (HodgeTheoryOfAFixedPart.combExtension (Ioc N (N + 3 * K * N)))))
    intro c hc
    have hp_re : (fun n => if n ∈ Ioc N (N + 3 * K * N) then
        (HodgeTheoryOfAFixedPart.combExtension (Ioc N (N + 3 * K * N)) c n).re else 0) =
        fun n => (HodgeTheoryOfAFixedPart.combExtension (Ioc N (N + 3 * K * N)) c n).re := by
      funext n
      by_cases hn : n ∈ Ioc N (N + 3 * K * N)
      · rw [if_pos hn]
      · rw [if_neg hn]
        show (0 : ℝ) = (if h : n ∈ Ioc N (N + 3 * K * N) then c ⟨n, h⟩ else 0).re
        rw [dif_neg hn, Complex.zero_re]
    have hp_im : (fun n => if n ∈ Ioc N (N + 3 * K * N) then
        (HodgeTheoryOfAFixedPart.combExtension (Ioc N (N + 3 * K * N)) c n).im else 0) =
        fun n => (HodgeTheoryOfAFixedPart.combExtension (Ioc N (N + 3 * K * N)) c n).im := by
      funext n
      by_cases hn : n ∈ Ioc N (N + 3 * K * N)
      · rw [if_pos hn]
      · rw [if_neg hn]
        show (0 : ℝ) = (if h : n ∈ Ioc N (N + 3 * K * N) then c ⟨n, h⟩ else 0).im
        rw [dif_neg hn, Complex.zero_im]
    have hre := hN₂.2 fun n =>
      (HodgeTheoryOfAFixedPart.combExtension (Ioc N (N + 3 * K * N)) c n).re
    have him := hN₂.2 fun n =>
      (HodgeTheoryOfAFixedPart.combExtension (Ioc N (N + 3 * K * N)) c n).im
    rw [hp_re] at hre
    rw [hp_im] at him
    have hm := HodgeTheoryOfAFixedPart.combExtension_mass (Ioc N (N + 3 * K * N)) c
    have hsum : (N / R : ℕ) * hermQuad ((blockWindow (6 * K + 2) R ((6 * K + 1) * R)).map (↑) :
        Matrix (Fin ((6 * K + 1) * R)) (Fin ((6 * K + 1) * R)) ℂ)
        (fun i : Fin ((6 * K + 1) * R) =>
          HodgeTheoryOfAFixedPart.complexBlockMean (R * (N / R)) (N / R) ((6 * K + 1) * R)
            (HodgeTheoryOfAFixedPart.combExtension (Ioc N (N + 3 * K * N)) c) i) < 0 := by
      rw [hermQuad_blockWindow_restrict hR]
      simp only [HodgeTheoryOfAFixedPart.complexBlockMean_re,
        HodgeTheoryOfAFixedPart.complexBlockMean_im]
      have hc' : HodgeTheoryOfAFixedPart.combForm (Ioc N (N + 3 * K * N))
            (fun n => (HodgeTheoryOfAFixedPart.combExtension (Ioc N (N + 3 * K * N)) c n).re) +
          HodgeTheoryOfAFixedPart.combForm (Ioc N (N + 3 * K * N))
            (fun n => (HodgeTheoryOfAFixedPart.combExtension (Ioc N (N + 3 * K * N)) c n).im) +
          η * ∑ i, ‖c i‖ ^ 2 < 0 := hc
      rw [← hm] at hc'
      nlinarith only [hre, him, hc']
    by_contra hnonneg
    exact (not_lt_of_ge (mul_nonneg (Nat.cast_nonneg (N / R)) (le_of_not_gt hnonneg))) hsum
  exact_mod_cast hN.trans htransfer

/-- **The index law of the block matrices.** Some window has a block matrix with `r` negative
squares iff there are at least `r` zeros right of the critical line. -/
theorem exists_le_hermNegIndex_blockWindow_iff (r : ℕ) :
    (∃ Q R J : ℕ, 1 ≤ R ∧ R + J ≤ Q * R ∧
        r ≤ hermNegIndex ((blockWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ)) ↔
      (r : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard := by
  constructor
  · rintro ⟨Q, R, J, hR, hQ, hr⟩
    exact (ENat.coe_le_coe.mpr hr).trans (hermNegIndex_blockWindow_le_rightZeros hR hQ)
  · exact exists_le_hermNegIndex_blockWindow

/-- **The index law of the neutral part.** Some window has a neutral part with `r` negative
squares iff `r` is at most one plus the number of zeros right of the critical line. -/
theorem exists_le_hermNegIndex_neutralWindow_iff (r : ℕ) :
    (∃ Q R J : ℕ, 1 ≤ R ∧ R + J ≤ Q * R ∧
        r ≤ hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ)) ↔
      (r : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard + 1 := by
  constructor
  · rintro ⟨Q, R, J, hR, hQ, hr⟩
    have h1 := hermNegIndex_neutralWindow_le_blockWindow_add_one Q R J
    have h2 := hermNegIndex_blockWindow_le_rightZeros hR hQ
    calc (r : ℕ∞) ≤ ((hermNegIndex ((blockWindow Q R J).map (↑) :
          Matrix (Fin J) (Fin J) ℂ) + 1 : ℕ) : ℕ∞) := ENat.coe_le_coe.mpr (hr.trans h1)
      _ = (hermNegIndex ((blockWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) : ℕ∞) + 1 := by
          push_cast
          rfl
      _ ≤ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard + 1 :=
          add_le_add h2 le_rfl
  · intro hr
    rcases Nat.eq_zero_or_pos r with rfl | hpos
    · exact ⟨1, 1, 0, le_rfl, le_rfl, Nat.zero_le _⟩
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      have hr' : (r' : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard := by
        have h : ((r' : ℕ∞) + 1) ≤
            (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard + 1 := by
          exact_mod_cast hr
        exact (ENat.add_le_add_iff_right (ENat.one_ne_top)).mp h
      obtain ⟨Q, R, J, hR, hQ, hidx⟩ := exists_le_hermNegIndex_blockWindow hr'
      obtain ⟨M, hM, hpole⟩ := exists_hermNegIndex_blockWindow_add_one_le hR hQ
      exact ⟨M + M, 1, M + M - 1, le_rfl, by omega, (Nat.add_le_add_right hidx 1).trans hpole⟩

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

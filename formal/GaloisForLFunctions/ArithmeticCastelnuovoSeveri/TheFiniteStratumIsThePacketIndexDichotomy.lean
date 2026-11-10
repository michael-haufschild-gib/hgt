import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectIsCyclic
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheIndexExit
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheHodgeIndexOfThePairingOfTheDegreePoints
import GaloisForLFunctions.HTGeometry.ExponentialKernelAlternatingInertia

/-!
# The finite stratum is the packet-index dichotomy

The supremum of the negative indices of the comb defect on real compactly supported
packets counts the distinct zeros right of the critical line. Complex tests do not enlarge
this supremum: splitting each test into its real and imaginary parts expresses its Gram
matrix as a compression of a real packet Gram matrix.

Consequently, the assertion that finitely many off-line zeros force RH is equivalent to
the packet index being zero or infinite.
-/

open Complex Matrix
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.ArithmeticOrientationGeometry

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The negative index of the comb defect, over all finite real packet families. -/
def realPacketNegIndex : ℕ∞ :=
  ⨆ (n : ℕ) (f : Fin n → ℝ → ℝ) (_ : ∀ i, ContDiff ℝ 2 (f i))
    (_ : ∀ i, HasCompactSupport (f i)),
    (hermNegIndex (weilGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
      (fun i u => (f i u : ℂ))) : ℕ∞)

/-- Splitting complex tests into real and imaginary parts never decreases the available
negative index. The larger family consists of real packets. -/
theorem exists_real_packets_negIndex_ge {n : ℕ} (f : Fin n → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    ∃ (m : ℕ) (g : Fin m → ℝ → ℝ), (∀ i, ContDiff ℝ 2 (g i)) ∧
      (∀ i, HasCompactSupport (g i)) ∧
      hermNegIndex (zeroGram zetaZeroConfig f) ≤
        hermNegIndex (weilGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
          (fun i u => (g i u : ℂ))) := by
  classical
  let g : Fin n × Fin 2 → ℝ → ℝ := fun j u =>
    if j.2 = 0 then (f j.1 u).re else (f j.1 u).im
  have hg : ∀ j, ContDiff ℝ 2 (g j) := by
    intro j
    dsimp only [g]
    split_ifs
    · exact Complex.reCLM.contDiff.comp (hf j.1)
    · exact Complex.imCLM.contDiff.comp (hf j.1)
  have hgc : ∀ j, HasCompactSupport (g j) := by
    intro j
    dsimp only [g]
    split_ifs
    · exact (hfc j.1).comp_left rfl
    · exact (hfc j.1).comp_left rfl
  let t : Fin n × Fin 2 → testSpace := fun j =>
    ⟨fun u => (g j u : ℂ), contDiff_ofReal_packet (hg j),
      hasCompactSupport_ofReal_packet (hgc j)⟩
  let C : Matrix (Fin n) (Fin n × Fin 2) ℂ := fun i j =>
    if j.1 = i then if j.2 = 0 then 1 else I else 0
  have hcomb : (fun i => ((∑ j, C i j • t j : testSpace) : ℝ → ℂ)) = f := by
    funext i u
    simp [C, t, g, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.re_add_im]
  have hmat := zeroGram_comb zetaZeroConfig temperedConfig_zetaZeroConfig t C
  rw [hcomb] at hmat
  have hle : hermNegIndex (zeroGram zetaZeroConfig f) ≤
      hermNegIndex (zeroGram zetaZeroConfig (fun j u => (g j u : ℂ))) := by
    rw [hmat]
    exact hermNegIndex_mul_mul_conjTranspose_le C _
  let e := (Fintype.equivFin (Fin n × Fin 2)).symm
  refine ⟨Fintype.card (Fin n × Fin 2), fun i => g (e i),
    fun i => hg (e i), fun i => hgc (e i), ?_⟩
  rw [weilGram_eq_zeroGram _ (fun i => contDiff_ofReal_packet (hg (e i)))
    (fun i => hasCompactSupport_ofReal_packet (hgc (e i)))]
  change hermNegIndex (zeroGram zetaZeroConfig f) ≤
    hermNegIndex ((zeroGram zetaZeroConfig (fun j u => (g j u : ℂ))).submatrix e e)
  rw [hermNegIndex_submatrix_equiv]
  exact hle

/-- Real packets attain the full Pontryagin index, including an infinite index. -/
theorem realPacketNegIndex_eq_rightZeros :
    realPacketNegIndex = (rightZeros zetaZeroConfig).encard := by
  apply le_antisymm
  · refine iSup_le fun n => iSup_le fun f => iSup_le fun hf => iSup_le fun hfc => ?_
    exact negIndex_defect_packets_le hf hfc
  · apply ENat.forall_natCast_le_iff_le.mp
    intro n hn
    obtain ⟨f, hf, hfc, hneg⟩ :=
      (pontryagin_law zetaZeroConfig temperedConfig_zetaZeroConfig n).mpr hn
    obtain ⟨m, g, hg, hgc, hle⟩ := exists_real_packets_negIndex_ge f hf hfc
    exact (ENat.coe_le_coe.mpr (hneg.trans hle)).trans
      (le_iSup_of_le m (le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le hgc le_rfl))))

/-- The finite-stratum implication is exactly the zero-or-infinite packet-index law. -/
theorem finiteOffLine_imp_rh_iff_packetIndex_zero_or_infinite :
    (_root_.RHTower.BacklundConverse.FiniteOffLine → RiemannHypothesis) ↔
      realPacketNegIndex = 0 ∨ realPacketNegIndex = ⊤ := by
  rw [realPacketNegIndex_eq_rightZeros]
  constructor
  · intro h
    rcases (rightZeros zetaZeroConfig).finite_or_infinite with hfin | hinf
    · left
      rw [rightZeros_zeta_eq_empty_iff.mpr
        (h (rightZeros_zeta_finite_iff_finiteOffLine.mp hfin)), Set.encard_empty]
    · exact Or.inr hinf.encard_eq
  · intro h hfin
    rcases h with hzero | hinf
    · exact rightZeros_zeta_eq_empty_iff.mp (Set.encard_eq_zero.mp hzero)
    · exact False.elim ((rightZeros_zeta_finite_iff_finiteOffLine.mpr hfin).encard_lt_top.ne hinf)

#print axioms realPacketNegIndex_eq_rightZeros
#print axioms finiteOffLine_imp_rh_iff_packetIndex_zero_or_infinite

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

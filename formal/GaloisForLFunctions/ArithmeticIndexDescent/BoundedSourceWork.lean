import GaloisForLFunctions.ArithmeticIndexDescent.TheArithmeticSourcePaysTheIndex

/-!
# Bounded source work and finite off-line support

Every row of the multiplicity-weighted angular kernel is summable, since its
horizontal displacement is at most one and the Cauchy height weight is summable.
Critical zeros do not interact transversally. Consequently finitely many off-line
zeros give finite total copied energy, even with all critical zeros and all
multiplicities retained. Conversely, finite copied energy bounds the distinct-zero
energy and therefore forces finite off-line support.
-/

open Filter Finset RHTower
open GaloisForLFunctions.ArithmeticElectrostatics
open scoped ENNReal Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- Angular interaction between analytic-multiplicity copies, including coincident copies. -/
def copyAngularTerm (p q : XiZeroCopy) : ℝ :=
  transverseAngular (xiSignedDepth p - xiSignedDepth q) (xiZeroHeight p - xiZeroHeight q)

theorem copyAngularTerm_nonneg (p q : XiZeroCopy) : 0 ≤ copyAngularTerm p q :=
  transverseAngular_nonneg _ _

theorem copyAngularTerm_comm (p q : XiZeroCopy) : copyAngularTerm p q = copyAngularTerm q p := by
  unfold copyAngularTerm transverseAngular
  rw [sq_sub_comm (xiSignedDepth p), sq_sub_comm (xiZeroHeight p)]

/-- Strip confinement provides a summable bound for each full interaction row. -/
theorem copyAngularTerm_le_cauchyWeight (p q : XiZeroCopy) :
    copyAngularTerm p q ≤ 1 / (1 + (xiZeroHeight p - xiZeroHeight q) ^ 2) := by
  let a := xiSignedDepth p - xiSignedDepth q
  let b := xiZeroHeight p - xiZeroHeight q
  have ha : a ^ 2 ≤ 1 := by
    have h := xiSignedDepth_pair_bound p q
    dsimp only [a]
    nlinarith only [h, sq_nonneg (xiSignedDepth p + xiSignedDepth q)]
  change a ^ 2 / (a ^ 2 + b ^ 2) ≤ 1 / (1 + b ^ 2)
  by_cases hd : a ^ 2 + b ^ 2 = 0
  · rw [hd, div_zero]
    positivity
  · have hden : 0 < a ^ 2 + b ^ 2 :=
      lt_of_le_of_ne (add_nonneg (sq_nonneg a) (sq_nonneg b)) (Ne.symm hd)
    rw [div_le_div_iff₀ hden (by positivity)]
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg b)]

theorem summable_copyAngularTerm (p : XiZeroCopy) : Summable (copyAngularTerm p) :=
  Summable.of_nonneg_of_le (copyAngularTerm_nonneg p) (copyAngularTerm_le_cauchyWeight p)
    (summable_xiZeroWeight (xiZeroHeight p))

/-- Total angular energy seen by one multiplicity copy. -/
def copyAngularEnergy (p : XiZeroCopy) : ℝ := ∑' q, copyAngularTerm p q

theorem ofReal_copyAngularEnergy (p : XiZeroCopy) :
    ENNReal.ofReal (copyAngularEnergy p) = ∑' q, ENNReal.ofReal (copyAngularTerm p q) :=
  ENNReal.ofReal_tsum_of_nonneg (copyAngularTerm_nonneg p) (summable_copyAngularTerm p)

theorem xiCopyTransverseEnergy_eq_half_rowSum :
    xiCopyTransverseEnergy = (∑' p, ENNReal.ofReal (copyAngularEnergy p)) / 2 := by
  unfold xiCopyTransverseEnergy
  simp_rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp only [ENNReal.ofReal_ofNat, div_eq_mul_inv, ENNReal.tsum_mul_right]
  congr 1
  rw [ENNReal.tsum_prod]
  exact tsum_congr fun p => (ofReal_copyAngularEnergy p).symm

theorem copyAngularTerm_eq_zero_of_critical {p q : XiZeroCopy}
    (hp : (p.1 : ℂ).re = 1 / 2) (hq : (q.1 : ℂ).re = 1 / 2) :
    copyAngularTerm p q = 0 := by
  simp only [copyAngularTerm, transverseAngular, xiSignedDepth, hp, hq,
    sub_self, zero_pow (by decide : 2 ≠ 0), zero_div]

/-- Finitely many support points carry finitely many analytic-multiplicity copies. -/
theorem offLineCopies_finite_of_offLineSupport_finite (h : offLineSupport.Finite) :
    offLineCopies.Finite := by
  classical
  refine (h.biUnion (fun ρ _ =>
    (Set.finite_range (fun i : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) =>
      (⟨ρ, i⟩ : XiZeroCopy))))).subset ?_
  intro q hq
  exact Set.mem_biUnion (show q.1 ∈ offLineSupport from hq) ⟨q.2, rfl⟩

/-- Finite copied energy is exactly finite off-line support; multiplicities do not change finiteness. -/
theorem xiCopyTransverseEnergy_lt_top_iff :
    xiCopyTransverseEnergy < ⊤ ↔ offLineSupport.Finite := by
  constructor
  · intro h
    exact divisorTransverseEnergy_lt_top_iff.mp
      (divisorTransverseEnergy_le_xiCopyTransverseEnergy.trans_lt h)
  · intro h
    classical
    have hfin := offLineCopies_finite_of_offLineSupport_finite h
    let F := hfin.toFinset
    have hcritical {p : XiZeroCopy} (hp : p ∉ F) : (p.1 : ℂ).re = 1 / 2 := by
      have hnot : p ∉ offLineCopies := (hfin.mem_toFinset).not.mp hp
      simpa only [offLineCopies, Set.mem_setOf_eq, not_not] using hnot
    have hrow (p : XiZeroCopy) : ENNReal.ofReal (copyAngularEnergy p) ≤
        (if p ∈ F then ENNReal.ofReal (copyAngularEnergy p) else 0) +
          ∑ q ∈ F, ENNReal.ofReal (copyAngularTerm p q) := by
      by_cases hp : p ∈ F
      · rw [if_pos hp]
        exact le_self_add
      · rw [if_neg hp, zero_add]
        have heq : copyAngularEnergy p = ∑ q ∈ F, copyAngularTerm p q :=
          tsum_eq_sum fun q hq => copyAngularTerm_eq_zero_of_critical
            (hcritical hp) (hcritical hq)
        rw [heq, ENNReal.ofReal_sum_of_nonneg fun q _ => copyAngularTerm_nonneg p q]
    have hsum : (∑' p, ENNReal.ofReal (copyAngularEnergy p)) ≤
        2 * ∑ p ∈ F, ENNReal.ofReal (copyAngularEnergy p) := by
      calc
        _ ≤ ∑' p, ((if p ∈ F then ENNReal.ofReal (copyAngularEnergy p) else 0) +
            ∑ q ∈ F, ENNReal.ofReal (copyAngularTerm p q)) := ENNReal.tsum_le_tsum hrow
        _ = (∑' p, if p ∈ F then ENNReal.ofReal (copyAngularEnergy p) else 0) +
            ∑' p, ∑ q ∈ F, ENNReal.ofReal (copyAngularTerm p q) := ENNReal.tsum_add
        _ = (∑ p ∈ F, ENNReal.ofReal (copyAngularEnergy p)) +
            ∑ q ∈ F, ∑' p, ENNReal.ofReal (copyAngularTerm p q) := by
          congr 1
          · exact (tsum_eq_sum fun p hp => if_neg hp).trans
              (sum_congr rfl fun p hp => if_pos hp)
          · exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable
        _ = (∑ p ∈ F, ENNReal.ofReal (copyAngularEnergy p)) +
            ∑ q ∈ F, ENNReal.ofReal (copyAngularEnergy q) := by
          congr 1
          refine sum_congr rfl fun q _ => ?_
          rw [ofReal_copyAngularEnergy]
          exact tsum_congr fun p => congrArg ENNReal.ofReal (copyAngularTerm_comm p q)
        _ = _ := by rw [two_mul]
    rw [xiCopyTransverseEnergy_eq_half_rowSum]
    refine ENNReal.div_lt_top (ne_top_of_le_ne_top ?_ hsum) two_ne_zero
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top)

/-- Eventual boundedness of the actual damped work is precisely finite off-line support. -/
theorem eventually_bounded_dampedSourceWork_iff :
    (∃ B : ℝ, ∀ᶠ n : ℕ in atTop, xiDampedSourceWork ((n : ℝ) + 4) ≤ B) ↔
      offLineSupport.Finite := by
  constructor
  · rintro ⟨B, hB⟩
    have hle : xiCopyTransverseEnergy ≤ ENNReal.ofReal B :=
      le_of_tendsto xiDampedSourceWork_tendsto_energy
        (hB.mono fun _ hn => ENNReal.ofReal_le_ofReal hn)
    exact xiCopyTransverseEnergy_lt_top_iff.mp (hle.trans_lt ENNReal.ofReal_lt_top)
  · intro hfin
    have hE := xiCopyTransverseEnergy_lt_top_iff.mpr hfin
    obtain ⟨B, hB⟩ := ENNReal.exists_nat_gt hE.ne
    refine ⟨(B : ℝ), ?_⟩
    filter_upwards [xiDampedSourceWork_tendsto_energy.eventually (gt_mem_nhds hB)] with n hn
    have h := ENNReal.toReal_mono (by simp : (B : ℝ≥0∞) ≠ ⊤) hn.le
    have hR : (4 : ℝ) ≤ (n : ℝ) + 4 := by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith only [hn0]
    have hnonneg : 0 ≤ xiDampedSourceWork ((n : ℝ) + 4) := xiDampedSourceWork_nonneg hR
    simpa only [ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_natCast] using h

/-- Infinite off-line support is exactly divergence of the damped source work to infinity. -/
theorem dampedSourceWork_tendsto_top_iff :
    Tendsto (fun n : ℕ => ENNReal.ofReal (xiDampedSourceWork ((n : ℝ) + 4))) atTop
      (𝓝 ⊤) ↔ offLineSupport.Infinite := by
  have htop : xiCopyTransverseEnergy = ⊤ ↔ offLineSupport.Infinite := by
    rw [← not_lt_top_iff, xiCopyTransverseEnergy_lt_top_iff]
    rfl
  constructor
  · intro h
    exact htop.mp (tendsto_nhds_unique xiDampedSourceWork_tendsto_energy h)
  · intro h
    simpa only [htop.mpr h] using xiDampedSourceWork_tendsto_energy

end GaloisForLFunctions.ArithmeticIndexDescent

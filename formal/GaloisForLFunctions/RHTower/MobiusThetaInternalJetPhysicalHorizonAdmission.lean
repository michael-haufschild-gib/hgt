import GaloisForLFunctions.RHTower.MobiusThetaInternalJetPhysicalGraph

/-!
# Physical horizon admission for every Möbius--theta internal jet

The internally promoted Möbius--theta exponent codiagonal was previously known to converge
strongly in physical `L²`.  Strong convergence alone does not put the complete coface field in
the Hilbert horizon used by the Hellinger--Hodge descent.

This module proves the source-side strengthening.  For every internal jet order, the complete
sequence of physical exponent cofaces is absolutely summable, hence square summable, in `L²`.
It therefore defines a literal point of `ℓ²(ℕ; L²)`.  Its codiagonal is exactly the physical
theta-jet source, and Plancherel lands that codiagonal on the corresponding Xi jet.

No divisor, zero enumeration, target residue, or externally chosen horizon weight occurs.
-/

open Complex Filter MeasureTheory ArithmeticFunction
open scoped BigOperators Topology Moebius FourierTransform

noncomputable section
namespace RHTower

/-- Geometric source estimate for every internally promoted post-head channel. -/
theorem norm_mobiusThetaInternalJetPrimeNormalTailTerm_le_geometricMajorant
    (k : ℕ) {p m : ℕ} (hp : 1 ≤ p) (hm : 3 ≤ m) (j : ℕ) :
    ‖mobiusThetaInternalJetPrimeNormalTailTerm k p m j‖ ≤
      (((p : ℝ) / (p + 1 : ℕ)) ^ (((m : ℝ) - 3) / 2)) *
        mobiusThetaInternalJetPrimeNormalMajorant k p j := by
  rw [norm_mobiusThetaInternalJetPrimeNormalTailTerm,
    mobiusThetaPrimeNormalWeight, abs_mul]
  have hmu : |(μ (p + j + 1) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p + j + 1)
  let r : ℝ := (p : ℝ) / (p + j + 1 : ℕ)
  let q : ℝ := (p : ℝ) / (p + 1 : ℕ)
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hrq : r ≤ q := by
    dsimp [r, q]
    exact (div_le_div_iff_of_pos_left
      (by exact_mod_cast hp) (by positivity) (by positivity)).2
      (by exact_mod_cast (by omega : p + 1 ≤ p + j + 1))
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hexp : 0 ≤ ((m : ℝ) - 3) / 2 := by linarith
  have hrpow : r ^ ((m : ℝ) / 2) =
      r ^ (3 / 2 : ℝ) * r ^ (((m : ℝ) - 3) / 2) := by
    rw [← Real.rpow_add hrpos]
    congr 1
    ring
  have hbase : r ^ (((m : ℝ) - 3) / 2) ≤
      q ^ (((m : ℝ) - 3) / 2) :=
    Real.rpow_le_rpow hrpos.le hrq hexp
  rw [abs_of_nonneg (Real.rpow_nonneg hrpos.le _)]
  change |(μ (p + j + 1) : ℝ)| * r ^ ((m : ℝ) / 2) *
      ‖xiThetaInternalJetSourceL2 k‖ ≤
    q ^ (((m : ℝ) - 3) / 2) *
      (r ^ (3 / 2 : ℝ) * ‖xiThetaInternalJetSourceL2 k‖)
  rw [hrpow]
  calc
    |(μ (p + j + 1) : ℝ)| *
          (r ^ (3 / 2 : ℝ) * r ^ (((m : ℝ) - 3) / 2)) *
          ‖xiThetaInternalJetSourceL2 k‖ ≤
        1 * (r ^ (3 / 2 : ℝ) * r ^ (((m : ℝ) - 3) / 2)) *
          ‖xiThetaInternalJetSourceL2 k‖ := by
      gcongr
    _ ≤ q ^ (((m : ℝ) - 3) / 2) *
          (r ^ (3 / 2 : ℝ) * ‖xiThetaInternalJetSourceL2 k‖) := by
      rw [one_mul]
      calc
        r ^ (3 / 2 : ℝ) * r ^ (((m : ℝ) - 3) / 2) *
              ‖xiThetaInternalJetSourceL2 k‖ =
            r ^ (((m : ℝ) - 3) / 2) *
              (r ^ (3 / 2 : ℝ) * ‖xiThetaInternalJetSourceL2 k‖) := by ring
        _ ≤ q ^ (((m : ℝ) - 3) / 2) *
              (r ^ (3 / 2 : ℝ) * ‖xiThetaInternalJetSourceL2 k‖) := by
          exact mul_le_mul_of_nonneg_right hbase
            (mul_nonneg (Real.rpow_nonneg hrpos.le _) (norm_nonneg _))

private theorem summable_prime_one_geometricHalf_internalJet :
    Summable (fun j : ℕ => ((1 / 2 : ℝ) ^ ((j : ℝ) / 2))) := by
  have hbase_nonneg : 0 ≤ (1 / 2 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have hbase_lt : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  have hgeom := summable_geometric_of_lt_one hbase_nonneg hbase_lt
  convert hgeom using 1
  funext j
  rw [← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  ring

private theorem summable_norm_mobiusThetaInternalJetPrimeNormalTail_three
    (k : ℕ) :
    Summable (fun j : ℕ =>
      ‖∑' q : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k 1 (j + 3) q‖) := by
  let C : ℝ := ∑' q : ℕ, mobiusThetaInternalJetPrimeNormalMajorant k 1 q
  have hmajor : Summable
      (fun j : ℕ => (1 / 2 : ℝ) ^ ((j : ℝ) / 2) * C) :=
    summable_prime_one_geometricHalf_internalJet.mul_right C
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hmajor
  have hterms : Summable (fun q : ℕ =>
      ‖mobiusThetaInternalJetPrimeNormalTailTerm k 1 (j + 3) q‖) :=
    (summable_mobiusThetaInternalJetPrimeNormalMajorant k 1).of_norm_bounded
      (fun q => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact norm_mobiusThetaInternalJetPrimeNormalTailTerm_le_majorant
          k (by omega) (by omega) q)
  calc
    ‖∑' q : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k 1 (j + 3) q‖ ≤
        ∑' q : ℕ,
          ‖mobiusThetaInternalJetPrimeNormalTailTerm k 1 (j + 3) q‖ :=
      norm_tsum_le_tsum_norm hterms
    _ ≤ ∑' q : ℕ,
        (1 / 2 : ℝ) ^ ((j : ℝ) / 2) *
          mobiusThetaInternalJetPrimeNormalMajorant k 1 q := by
      apply hterms.tsum_le_tsum
      · intro q
        simpa [Nat.cast_add] using
          (norm_mobiusThetaInternalJetPrimeNormalTailTerm_le_geometricMajorant
            k (p := 1) (m := j + 3) (by omega) (by omega) q)
      · exact (summable_mobiusThetaInternalJetPrimeNormalMajorant k 1).mul_left _
    _ = (1 / 2 : ℝ) ^ ((j : ℝ) / 2) * C := by
      rw [tsum_mul_left]

private theorem
    mobiusThetaInternalJetCompletePhysicalChannel_three_succ_eq_tail_sub
    (k j : ℕ) :
    mobiusThetaInternalJetCompletePhysicalChannel k 3 (j + 1) =
      (∑' q : ℕ,
        mobiusThetaInternalJetPrimeNormalTailTerm k 1 (j + 4) q) -
      (∑' q : ℕ,
        mobiusThetaInternalJetPrimeNormalTailTerm k 1 (j + 3) q) := by
  simp only [mobiusThetaInternalJetCompletePhysicalChannel,
    mobiusThetaInternalJetDirectPhysicalRung,
    mobiusThetaInternalJetPrimeNormalResidual]
  rw [show 3 + j + 1 = j + 4 by omega,
    show 3 + j = j + 3 by omega]
  norm_num

/-- Every internal Xi-jet order has an absolutely summable physical exponent-coface field. -/
theorem summable_norm_mobiusThetaInternalJetCompletePhysicalChannel_three
    (k : ℕ) :
    Summable (fun j : ℕ =>
      ‖mobiusThetaInternalJetCompletePhysicalChannel k 3 j‖) := by
  let T : ℕ → MobiusThetaSourceL2 := fun j =>
    ∑' q : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k 1 (j + 3) q
  have hT : Summable (fun j : ℕ => ‖T j‖) :=
    summable_norm_mobiusThetaInternalJetPrimeNormalTail_three k
  have hTshift : Summable (fun j : ℕ => ‖T (j + 1)‖) :=
    (_root_.summable_nat_add_iff 1).2 hT
  have hupper : Summable (fun j : ℕ => ‖T (j + 1)‖ + ‖T j‖) :=
    hTshift.add hT
  have hsucc : Summable (fun j : ℕ =>
      ‖mobiusThetaInternalJetCompletePhysicalChannel k 3 (j + 1)‖) := by
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hupper
    rw [mobiusThetaInternalJetCompletePhysicalChannel_three_succ_eq_tail_sub]
    exact norm_sub_le _ _
  exact (_root_.summable_nat_add_iff 1).1 hsucc

theorem summable_mobiusThetaInternalJetCompletePhysicalChannel_three
    (k : ℕ) :
    Summable (mobiusThetaInternalJetCompletePhysicalChannel k 3) :=
  Summable.of_norm
    (summable_norm_mobiusThetaInternalJetCompletePhysicalChannel_three k)

/-- Absolute source codiagonal: summing all physical cofaces gives the actual internal theta jet. -/
theorem tsum_mobiusThetaInternalJetCompletePhysicalChannel_three
    (k : ℕ) :
    (∑' j : ℕ, mobiusThetaInternalJetCompletePhysicalChannel k 3 j) =
      xiThetaInternalJetSourceL2 k := by
  have hsum :=
    (summable_mobiusThetaInternalJetCompletePhysicalChannel_three k).hasSum.tendsto_sum_nat
  have hsumSucc := hsum.comp (tendsto_add_atTop_nat 1)
  have hphysical :=
    tendsto_sum_range_mobiusThetaInternalJetCompletePhysicalChannel k 3
  exact tendsto_nhds_unique hsumSucc hphysical

/-- Absolute summability forces square summability of the physical coface norms. -/
theorem summable_norm_sq_mobiusThetaInternalJetCompletePhysicalChannel_three
    (k : ℕ) :
    Summable (fun j : ℕ =>
      ‖mobiusThetaInternalJetCompletePhysicalChannel k 3 j‖ ^ 2) := by
  let a : ℕ → ℝ := fun j =>
    ‖mobiusThetaInternalJetCompletePhysicalChannel k 3 j‖
  have ha : Summable a :=
    summable_norm_mobiusThetaInternalJetCompletePhysicalChannel_three k
  have hev : ∀ᶠ j : ℕ in atTop, a j < 1 :=
    ha.tendsto_atTop_zero.eventually_lt_const zero_lt_one
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hashift : Summable (fun j : ℕ => a (j + N)) :=
    (_root_.summable_nat_add_iff N).2 ha
  have hsqshift : Summable (fun j : ℕ => (a (j + N)) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) hashift
    have hlt : a (j + N) < 1 := hN (j + N) (by omega)
    have hnonneg : 0 ≤ a (j + N) := norm_nonneg _
    nlinarith
  exact (_root_.summable_nat_add_iff N).1 hsqshift

/-- Literal all-order physical Hellinger horizon.  Its coordinates are the actual exponent
cofaces, and its `ℓ²` admission follows from source norms rather than an external grade. -/
def mobiusThetaInternalJetPhysicalHorizon
    (k : ℕ) : lp (fun _ : ℕ => MobiusThetaSourceL2) 2 :=
  ⟨(mobiusThetaInternalJetCompletePhysicalChannel k 3 :
      PreLp (fun _ : ℕ => MobiusThetaSourceL2)), by
    change Memℓp (mobiusThetaInternalJetCompletePhysicalChannel k 3) 2
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      summable_norm_sq_mobiusThetaInternalJetCompletePhysicalChannel_three k⟩

@[simp] theorem mobiusThetaInternalJetPhysicalHorizon_apply
    (k j : ℕ) :
    mobiusThetaInternalJetPhysicalHorizon k j =
      mobiusThetaInternalJetCompletePhysicalChannel k 3 j :=
  rfl

/-- The admitted horizon codiagonal lands exactly on the physical internal theta jet. -/
theorem tsum_mobiusThetaInternalJetPhysicalHorizon
    (k : ℕ) :
    (∑' j : ℕ, mobiusThetaInternalJetPhysicalHorizon k j) =
      xiThetaInternalJetSourceL2 k :=
  tsum_mobiusThetaInternalJetCompletePhysicalChannel_three k

/-- Plancherel sends the exact physical horizon codiagonal to the `L²` Xi-jet source. -/
theorem fourier_tsum_mobiusThetaInternalJetPhysicalHorizon
    (k : ℕ) :
    𝓕 (∑' j : ℕ, mobiusThetaInternalJetPhysicalHorizon k j) =
      xiThetaInternalJetFourierSourceL2 k := by
  rw [tsum_mobiusThetaInternalJetPhysicalHorizon,
    fourier_xiThetaInternalJetSourceL2]

end RHTower

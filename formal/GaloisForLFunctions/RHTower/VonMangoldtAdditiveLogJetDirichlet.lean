import GaloisForLFunctions.RHTower.VonMangoldtGammaAllDepthCauchy
import GaloisForLFunctions.RHTower.EulerFisherCurvature

/-!
# Von Mangoldt additive log-jet Dirichlet completion

The resolved-prime diagonal energy of a positive logarithmic Mellin jet diverges.  This
module constructs a canonical off-diagonal repair internal to the integral source:
put the source conductance `Λ(n) / n` on the successor edge `n → n + 1` and apply the
discrete derivative before taking the Hilbert norm.  Every logarithmic jet then has finite
energy, the mixed entries are absolutely summable, and every finite all-order section is a
genuine Hilbert-space Gram matrix.

This is a positive source completion, not by itself an RH criterion.  The remaining
source-producing theorem is a Gamma/polar discrete Green identity identifying the relevant
boundary Schur complement with the normalized prime--archimedean central moments.
-/

open Filter

namespace RHTower

noncomputable section

def vonMangoldtAdditiveLogJet (r n : ℕ) : ℝ := Real.log n ^ r

def vonMangoldtAdditiveLogJetDifference (r n : ℕ) : ℝ :=
  vonMangoldtAdditiveLogJet r (n + 1) - vonMangoldtAdditiveLogJet r n

def vonMangoldtAdditiveLogJetEnergy (r n : ℕ) : ℝ :=
  finiteVonMangoldtRealWeight n * vonMangoldtAdditiveLogJetDifference r n ^ 2

lemma log_natCast_succ_sub_log_natCast_le_inv
    (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n + 1 : ℝ) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hs0 : (0 : ℝ) < n + 1 := by positivity
  calc
    Real.log (n + 1 : ℝ) - Real.log (n : ℝ) =
        Real.log ((n + 1 : ℝ) / (n : ℝ)) := by
      rw [Real.log_div hs0.ne' hn0.ne']
    _ ≤ (n + 1 : ℝ) / (n : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hs0 hn0)
    _ = 1 / (n : ℝ) := by field_simp; ring

lemma abs_vonMangoldtAdditiveLogJetDifference_le
    (r n : ℕ) (hn : 1 ≤ n) :
    |vonMangoldtAdditiveLogJetDifference r n| ≤
      (r : ℝ) * Real.log (n + 1 : ℝ) ^ (r - 1) / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hns : (n : ℝ) ≤ (n + 1 : ℝ) := by norm_num
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlogs : 0 ≤ Real.log (n + 1 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hns0 : (0 : ℝ) < n + 1 := by linarith
  have hlogle : Real.log (n : ℝ) ≤ Real.log (n + 1 : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hn0 hns0 hns
  have hdiff : 0 ≤ Real.log (n + 1 : ℝ) - Real.log (n : ℝ) := sub_nonneg.mpr hlogle
  have hpow := abs_pow_sub_pow_le
    (a := Real.log (n + 1 : ℝ)) (b := Real.log (n : ℝ)) r
  rw [abs_of_nonneg hlogs, abs_of_nonneg hlogn, max_eq_left hlogle,
    abs_of_nonneg hdiff] at hpow
  rw [vonMangoldtAdditiveLogJetDifference, vonMangoldtAdditiveLogJet]
  simp only [Nat.cast_add, Nat.cast_one]
  calc
    |Real.log (n + 1 : ℝ) ^ r - Real.log (n : ℝ) ^ r| ≤
        (Real.log (n + 1 : ℝ) - Real.log (n : ℝ)) * (r : ℝ) *
          Real.log (n + 1 : ℝ) ^ (r - 1) := hpow
    _ ≤ (1 / (n : ℝ)) * (r : ℝ) *
          Real.log (n + 1 : ℝ) ^ (r - 1) := by
      gcongr
      exact log_natCast_succ_sub_log_natCast_le_inv n hn
    _ = (r : ℝ) * Real.log (n + 1 : ℝ) ^ (r - 1) / (n : ℝ) := by ring

lemma vonMangoldtAdditiveLogJetEnergy_nonneg (r n : ℕ) :
    0 ≤ vonMangoldtAdditiveLogJetEnergy r n := by
  exact mul_nonneg (finiteVonMangoldtRealWeight_nonneg n) (sq_nonneg _)

lemma vonMangoldtAdditiveLogJetEnergy_le_majorant
    (r n : ℕ) (hr : 1 ≤ r) (hn : 2 ≤ n) :
    vonMangoldtAdditiveLogJetEnergy r n ≤
      8 * (r : ℝ) ^ 2 * |Real.log (n + 1 : ℝ)| ^ (2 * r - 1) *
        (n + 1 : ℝ) ^ (-3 : ℝ) := by
  have hn1 : 1 ≤ n := le_trans (by omega) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
  have hns0 : (0 : ℝ) < n + 1 := by positivity
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hlogs : 0 ≤ Real.log (n + 1 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hlogle : Real.log (n : ℝ) ≤ Real.log (n + 1 : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn hn0 hns0 (by norm_num)
  have hvm : finiteVonMangoldtRealWeight n ≤ Real.log (n : ℝ) / (n : ℝ) := by
    rw [finiteVonMangoldtRealWeight]
    exact div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log hn0.le
  have hdiff := abs_vonMangoldtAdditiveLogJetDifference_le r n hn1
  have hdiffsq : vonMangoldtAdditiveLogJetDifference r n ^ 2 ≤
      ((r : ℝ) * Real.log (n + 1 : ℝ) ^ (r - 1) / (n : ℝ)) ^ 2 := by
    rw [← sq_abs (vonMangoldtAdditiveLogJetDifference r n)]
    exact sq_le_sq₀ (abs_nonneg _) (by positivity) |>.2 hdiff
  have hbase : vonMangoldtAdditiveLogJetEnergy r n ≤
      (Real.log (n : ℝ) / (n : ℝ)) *
        ((r : ℝ) * Real.log (n + 1 : ℝ) ^ (r - 1) / (n : ℝ)) ^ 2 := by
    rw [vonMangoldtAdditiveLogJetEnergy]
    exact mul_le_mul hvm hdiffsq (sq_nonneg _) (div_nonneg hlogn hn0.le)
  calc
    vonMangoldtAdditiveLogJetEnergy r n ≤
        (Real.log (n : ℝ) / (n : ℝ)) *
          ((r : ℝ) * Real.log (n + 1 : ℝ) ^ (r - 1) / (n : ℝ)) ^ 2 := hbase
    _ ≤ (r : ℝ) ^ 2 * Real.log (n + 1 : ℝ) ^ (2 * r - 1) /
          (n : ℝ) ^ 3 := by
      have hfactor : 0 ≤ Real.log (n + 1 : ℝ) ^ (2 * (r - 1)) := by positivity
      have hprod : Real.log (n : ℝ) * Real.log (n + 1 : ℝ) ^ (2 * (r - 1)) ≤
          Real.log (n + 1 : ℝ) * Real.log (n + 1 : ℝ) ^ (2 * (r - 1)) :=
        mul_le_mul_of_nonneg_right hlogle hfactor
      rw [show 2 * r - 1 = 1 + 2 * (r - 1) by omega, pow_add, pow_mul]
      calc
        (Real.log (n : ℝ) / (n : ℝ)) *
            ((r : ℝ) * Real.log (n + 1 : ℝ) ^ (r - 1) / (n : ℝ)) ^ 2 =
            (r : ℝ) ^ 2 *
              (Real.log (n : ℝ) * Real.log (n + 1 : ℝ) ^ (2 * (r - 1))) /
                (n : ℝ) ^ 3 := by ring
        _ ≤ (r : ℝ) ^ 2 *
              (Real.log (n + 1 : ℝ) * Real.log (n + 1 : ℝ) ^ (2 * (r - 1))) /
                (n : ℝ) ^ 3 := by gcongr
        _ = _ := by ring
    _ ≤ 8 * (r : ℝ) ^ 2 * Real.log (n + 1 : ℝ) ^ (2 * r - 1) /
          (n + 1 : ℝ) ^ 3 := by
      have htwoNat : n + 1 ≤ 2 * n := by omega
      have htwo : (n + 1 : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast htwoNat
      have hpow : (n + 1 : ℝ) ^ 3 ≤ 8 * (n : ℝ) ^ 3 := by
        calc
          (n + 1 : ℝ) ^ 3 ≤ (2 * (n : ℝ)) ^ 3 :=
            pow_le_pow_left₀ (by positivity) htwo 3
          _ = 8 * (n : ℝ) ^ 3 := by ring
      have hnum : 0 ≤ (r : ℝ) ^ 2 * Real.log (n + 1 : ℝ) ^ (2 * r - 1) := by positivity
      have hinv : 1 / (n : ℝ) ^ 3 ≤ 8 / (n + 1 : ℝ) ^ 3 := by
        rw [div_le_div_iff₀ (by positivity : 0 < (n : ℝ) ^ 3)
          (by positivity : 0 < (n + 1 : ℝ) ^ 3)]
        simpa only [one_mul] using hpow
      calc
        (r : ℝ) ^ 2 * Real.log (n + 1 : ℝ) ^ (2 * r - 1) / (n : ℝ) ^ 3 =
            ((r : ℝ) ^ 2 * Real.log (n + 1 : ℝ) ^ (2 * r - 1)) *
              (1 / (n : ℝ) ^ 3) := by ring
        _ ≤ ((r : ℝ) ^ 2 * Real.log (n + 1 : ℝ) ^ (2 * r - 1)) *
              (8 / (n + 1 : ℝ) ^ 3) := mul_le_mul_of_nonneg_left hinv hnum
        _ = _ := by ring
    _ = 8 * (r : ℝ) ^ 2 * |Real.log (n + 1 : ℝ)| ^ (2 * r - 1) *
          (n + 1 : ℝ) ^ (-3 : ℝ) := by
      rw [abs_of_nonneg hlogs, Real.rpow_neg (le_of_lt hns0)]
      have hp : (n + 1 : ℝ) ^ (3 : ℝ) = (n + 1 : ℝ) ^ (3 : ℕ) :=
        Real.rpow_natCast _ 3
      rw [hp, div_eq_mul_inv]

theorem summable_vonMangoldtAdditiveLogJetEnergy (r : ℕ) :
    Summable (vonMangoldtAdditiveLogJetEnergy r) := by
  rcases r with _ | r
  · apply summable_zero.congr
    intro n
    simp [vonMangoldtAdditiveLogJetEnergy, vonMangoldtAdditiveLogJetDifference,
      vonMangoldtAdditiveLogJet]
  · let m : ℕ := 2 * (r + 1) - 1
    let C : ℝ := 8 * ((r + 1 : ℕ) : ℝ) ^ 2
    have hs0 : Summable (fun n : ℕ =>
        |Real.log (n + 1 : ℝ)| ^ m * (n + 1 : ℝ) ^ (-3 : ℝ)) := by
      simpa [Function.comp_def, Nat.cast_succ] using
        (summable_abs_log_natCast_pow_mul_rpow_neg m 3 (by norm_num)).comp_injective
          Nat.succ_injective
    have hmajor : Summable (fun n : ℕ =>
        8 * ((r + 1 : ℕ) : ℝ) ^ 2 * |Real.log (n + 1 : ℝ)| ^ (2 * (r + 1) - 1) *
          (n + 1 : ℝ) ^ (-3 : ℝ)) := by
      simpa only [m, C, mul_assoc] using hs0.mul_left C
    apply (summable_nat_add_iff (f := vonMangoldtAdditiveLogJetEnergy (r + 1)) 2).mp
    apply Summable.of_nonneg_of_le
    · intro n
      exact vonMangoldtAdditiveLogJetEnergy_nonneg (r + 1) (n + 2)
    · intro n
      exact vonMangoldtAdditiveLogJetEnergy_le_majorant (r + 1) (n + 2)
        (by omega) (by omega)
    · exact hmajor.comp_injective (fun a b h => Nat.add_right_cancel h)

/-- The source-weighted edge feature on the integral successor graph. -/
def vonMangoldtAdditiveLogJetFeature (r n : ℕ) : ℝ :=
  Real.sqrt (finiteVonMangoldtRealWeight n) *
    vonMangoldtAdditiveLogJetDifference r n

theorem vonMangoldtAdditiveLogJetFeature_sq (r n : ℕ) :
    vonMangoldtAdditiveLogJetFeature r n ^ 2 =
      vonMangoldtAdditiveLogJetEnergy r n := by
  rw [vonMangoldtAdditiveLogJetFeature, vonMangoldtAdditiveLogJetEnergy, mul_pow,
    Real.sq_sqrt (finiteVonMangoldtRealWeight_nonneg n)]

theorem summable_sq_vonMangoldtAdditiveLogJetFeature (r : ℕ) :
    Summable (fun n => vonMangoldtAdditiveLogJetFeature r n ^ 2) := by
  exact (summable_vonMangoldtAdditiveLogJetEnergy r).congr
    (fun n => (vonMangoldtAdditiveLogJetFeature_sq r n).symm)

theorem memℓp_two_vonMangoldtAdditiveLogJetFeature (r : ℕ) :
    Memℓp (vonMangoldtAdditiveLogJetFeature r) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  simpa [Real.norm_eq_abs, sq_abs] using
    summable_sq_vonMangoldtAdditiveLogJetFeature r

/-- The canonical all-prime integral-successor Dirichlet vector of logarithmic order `r`. -/
def vonMangoldtAdditiveLogJetVector (r : ℕ) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨vonMangoldtAdditiveLogJetFeature r,
    memℓp_two_vonMangoldtAdditiveLogJetFeature r⟩

theorem summable_vonMangoldtAdditiveLogJetFeature_mul (r s : ℕ) :
    Summable (fun n =>
      vonMangoldtAdditiveLogJetFeature r n *
        vonMangoldtAdditiveLogJetFeature s n) := by
  apply Summable.of_norm_bounded
    (summable_vonMangoldtAdditiveLogJetEnergy r |>.add
      (summable_vonMangoldtAdditiveLogJetEnergy s))
  intro n
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |vonMangoldtAdditiveLogJetFeature r n| *
        |vonMangoldtAdditiveLogJetFeature s n| ≤
        |vonMangoldtAdditiveLogJetFeature r n| ^ 2 +
          |vonMangoldtAdditiveLogJetFeature s n| ^ 2 := by
      nlinarith [sq_nonneg
        (|vonMangoldtAdditiveLogJetFeature r n| -
          |vonMangoldtAdditiveLogJetFeature s n|)]
    _ = vonMangoldtAdditiveLogJetEnergy r n +
        vonMangoldtAdditiveLogJetEnergy s n := by
      rw [sq_abs, sq_abs, vonMangoldtAdditiveLogJetFeature_sq,
        vonMangoldtAdditiveLogJetFeature_sq]

/-- The finite all-order source Gram section of the successor Dirichlet completion. -/
def vonMangoldtAdditiveLogJetGram (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.gram ℝ (fun r : Fin N => vonMangoldtAdditiveLogJetVector r)

theorem vonMangoldtAdditiveLogJetGram_posSemidef (N : ℕ) :
    (vonMangoldtAdditiveLogJetGram N).PosSemidef :=
  Matrix.posSemidef_gram ℝ _

theorem vonMangoldtAdditiveLogJetGram_apply
    (N : ℕ) (r s : Fin N) :
    vonMangoldtAdditiveLogJetGram N r s =
      ∑' n, vonMangoldtAdditiveLogJetFeature r n *
        vonMangoldtAdditiveLogJetFeature s n := by
  rw [vonMangoldtAdditiveLogJetGram, Matrix.gram_apply, lp.inner_eq_tsum]
  simp [vonMangoldtAdditiveLogJetVector, mul_comm]

theorem vonMangoldtAdditiveLogJetGram_diagonal
    (N : ℕ) (r : Fin N) :
    vonMangoldtAdditiveLogJetGram N r r =
      ∑' n, vonMangoldtAdditiveLogJetEnergy r n := by
  rw [vonMangoldtAdditiveLogJetGram_apply]
  apply tsum_congr
  intro n
  rw [← vonMangoldtAdditiveLogJetFeature_sq]
  ring

end

end RHTower

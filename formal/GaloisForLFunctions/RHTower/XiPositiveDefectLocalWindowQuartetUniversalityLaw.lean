import GaloisForLFunctions.RHTower.XiHeightAdaptivePositiveDefectCensusUniversalityLaw
import GaloisForLFunctions.RHTower.CofinalWindowDataRH

/-!
# Xi positive-defect local window-quartet universality

The height-adaptive positive-defect theorem currently exhausts natural heights and returns RH.
Before that exhaustion, one modular collision already empties its own Xi box.  Combining that
local arithmetic fact with the four exact window classifications activates every analytic window
interface at the same height, without passing through global RH.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

/-- The complete collection of exact zero-free window interfaces at one height. -/
def XiPositiveDefectLocalWindowCertificate (T : ℝ) : Prop :=
  boxZeros T = ∅ ∧
    WindowLinePackage T ∧
    SecondMomentOrthogonalSavingOuterPowerWindowData T ∧
    AnchorMassOuterPowerWindowData T ∧
    IntegralLedgerOuterPowerWindowData T

/-- **Xi positive-defect local window-quartet universality law.**  One modular collision whose
modulus exceeds a positive defect's bound empties the Xi box at that exact height and activates all
four zero-free window interfaces there.  No cofinal exhaustion or global RH conversion is used. -/
theorem xiPositiveDefectSingleCollision_windowCertificateUniversality
    (upper lower defect : ℝ → ℕ) {n k : ℕ} {bound : ℝ}
    (hdecomp :
      upper (n : ℝ) = lower (n : ℝ) + defect (n : ℝ))
    (hdetect :
      (boxFinset (n : ℝ)).Nonempty → 0 < defect (n : ℝ))
    (hbound : (defect (n : ℝ) : ℝ) ≤ bound)
    (hkLarge : bound < (2 ^ k : ℕ))
    (hcollision :
      (upper (n : ℝ) : ZMod (2 ^ k)) =
        (lower (n : ℝ) : ZMod (2 ^ k))) :
    XiPositiveDefectLocalWindowCertificate (n : ℝ) := by
  have hmod :
      upper (n : ℝ) ≡ lower (n : ℝ) [MOD 2 ^ k] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hcollision
  have hdvd : 2 ^ k ∣ defect (n : ℝ) := by
    rw [hdecomp] at hmod
    have hmod' :
        lower (n : ℝ) + defect (n : ℝ) ≡
          lower (n : ℝ) + 0 [MOD 2 ^ k] := by
      simpa using hmod
    exact Nat.modEq_zero_iff_dvd.mp
      (Nat.ModEq.add_left_cancel Nat.ModEq.rfl hmod')
  have hdefectLtReal :
      (defect (n : ℝ) : ℝ) < ((2 ^ k : ℕ) : ℝ) :=
    hbound.trans_lt hkLarge
  have hdefectLt : defect (n : ℝ) < 2 ^ k := by
    exact_mod_cast hdefectLtReal
  have hfinEmpty : boxFinset (n : ℝ) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    have hpositive : 0 < defect (n : ℝ) :=
      hdetect ⟨z, hz⟩
    have hmodLe : 2 ^ k ≤ defect (n : ℝ) :=
      Nat.le_of_dvd hpositive hdvd
    omega
  have hempty : boxZeros (n : ℝ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hzfin : z ∈ boxFinset (n : ℝ) :=
      mem_boxFinset.mpr hz
    rw [hfinEmpty] at hzfin
    exact Finset.notMem_empty z hzfin
  exact
    ⟨hempty,
      (windowLinePackage_iff_boxZeros_empty _).2 hempty,
      (secondMomentOrthogonalSavingOuterPowerWindowData_iff_boxZeros_empty _).2 hempty,
      (anchorMassOuterPowerWindowData_iff_boxZeros_empty _).2 hempty,
      (integralLedgerOuterPowerWindowData_iff_boxZeros_empty _).2 hempty⟩

/-- A global height-adaptive collision supplies the local five-part certificate at every positive
natural height; this retains the exact height information hidden by its RH corollary. -/
theorem xiNatHeightAdaptivePositiveDefectCollision_localWindowCertificates
    (bound : ℕ → ℝ) (upper lower defect : ℝ → ℕ)
    (hdecomp : ∀ T, upper T = lower T + defect T)
    (hdetect : ∀ T, (boxFinset T).Nonempty → 0 < defect T)
    (hbound : ∀ n : ℕ, 1 ≤ n → (defect (n : ℝ) : ℝ) ≤ bound n)
    (hcollision :
      XiNatHeightAdaptivePositiveDefectCollision bound upper lower) :
    ∀ n : ℕ, 1 ≤ n →
      XiPositiveDefectLocalWindowCertificate (n : ℝ) := by
  intro n hn
  obtain ⟨k, hkLarge, hcensus⟩ := hcollision n hn
  exact xiPositiveDefectSingleCollision_windowCertificateUniversality
    upper lower defect (hdecomp _) (hdetect _) (hbound n hn)
      hkLarge hcensus

end

end RHTower

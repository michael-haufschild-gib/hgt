import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskySexticJostDealiasing

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-!
# Exact charge-decay Jost alias spectrum

For charge-decay rung `k`, negative-helicity hypergeometric Jost incidence in the
open Xi strip is a finite packet of exactly `2k+1` equally spaced tilts.  Its
overtone window is `4k+3,...,6k+3`; theta reflection reverses this window and
negates tilt.  Consequently only the sextic rung `k=0` has a single strip
incidence.  This classifies every reciprocal-Gamma alias, not merely the first
off-axis example.
-/

def d4ThetaHawkingChargeDecayAliasOvertone (k : ℕ) (j : Fin (2 * k + 1)) : ℕ :=
  4 * k + 3 + j

def d4ThetaHawkingChargeDecayAliasTilt (k : ℕ) (j : Fin (2 * k + 1)) : ℝ :=
  ((k : ℝ) - (j : ℕ)) / (2 * ((k + 1 : ℕ) : ℝ))

def d4ThetaHawkingChargeDecayAliasPoint
    (k : ℕ) (j : Fin (2 * k + 1)) (x : ℝ) : ℂ :=
  (x : ℂ) + Complex.I * (d4ThetaHawkingChargeDecayAliasTilt k j : ℂ)

def d4ThetaHawkingChargeDecayAliasMirror
    (k : ℕ) (j : Fin (2 * k + 1)) : Fin (2 * k + 1) :=
  ⟨2 * k - j, by omega⟩

theorem d4ThetaHawkingChargeDecayAliasMirror_involutive
    (k : ℕ) (j : Fin (2 * k + 1)) :
    d4ThetaHawkingChargeDecayAliasMirror k
        (d4ThetaHawkingChargeDecayAliasMirror k j) = j := by
  apply Fin.ext
  simp [d4ThetaHawkingChargeDecayAliasMirror]
  omega

theorem d4ThetaHawkingChargeDecayAliasTilt_mirror
    (k : ℕ) (j : Fin (2 * k + 1)) :
    d4ThetaHawkingChargeDecayAliasTilt k
        (d4ThetaHawkingChargeDecayAliasMirror k j) =
      -d4ThetaHawkingChargeDecayAliasTilt k j := by
  unfold d4ThetaHawkingChargeDecayAliasTilt
    d4ThetaHawkingChargeDecayAliasMirror
  have hj : (j : ℕ) ≤ 2 * k := by omega
  have hden : (2 * ((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hden]
  rw [Nat.cast_sub hj]
  push_cast
  ring

theorem d4ThetaHawkingChargeDecayAliasMirror_fixed_iff
    (k : ℕ) (j : Fin (2 * k + 1)) :
    d4ThetaHawkingChargeDecayAliasMirror k j = j ↔ (j : ℕ) = k := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp [d4ThetaHawkingChargeDecayAliasMirror] at hv
    have hj : (j : ℕ) ≤ 2 * k := by omega
    omega
  · intro h
    apply Fin.ext
    simp [d4ThetaHawkingChargeDecayAliasMirror]
    omega

theorem d4ThetaHawkingChargeDecayAliasTilt_eq_zero_iff
    (k : ℕ) (j : Fin (2 * k + 1)) :
    d4ThetaHawkingChargeDecayAliasTilt k j = 0 ↔ (j : ℕ) = k := by
  unfold d4ThetaHawkingChargeDecayAliasTilt
  have hden : (2 * ((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  constructor
  · intro h
    field_simp [hden] at h
    norm_num at h
    have hcast : (k : ℝ) = ((j : ℕ) : ℝ) := sub_eq_zero.mp h
    exact_mod_cast hcast.symm
  · intro h
    rw [h]
    simp

lemma d4ThetaHawkingChargeDecayAliasPoint_im
    (k : ℕ) (j : Fin (2 * k + 1)) (x : ℝ) :
    (d4ThetaHawkingChargeDecayAliasPoint k j x).im =
      d4ThetaHawkingChargeDecayAliasTilt k j := by
  simp [d4ThetaHawkingChargeDecayAliasPoint]

theorem d4ThetaHawkingChargeDecayAliasPoint_mem_strip
    (k : ℕ) (j : Fin (2 * k + 1)) (x : ℝ) :
    -1 / 2 < (d4ThetaHawkingChargeDecayAliasPoint k j x).im ∧
      (d4ThetaHawkingChargeDecayAliasPoint k j x).im < 1 / 2 := by
  rw [d4ThetaHawkingChargeDecayAliasPoint_im]
  unfold d4ThetaHawkingChargeDecayAliasTilt
  have hj : (j : ℕ) ≤ 2 * k := by omega
  have hjR : (((j : ℕ) : ℝ)) ≤ 2 * (k : ℝ) := by exact_mod_cast hj
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk : (0 : ℝ) < 2 * ((k + 1 : ℕ) : ℝ) := by positivity
  rw [div_lt_iff₀ hk, lt_div_iff₀ hk]
  constructor <;> push_cast <;> nlinarith

theorem d4ThetaHawkingChargeDecayAlias_frequency_eq
    (k : ℕ) (j : Fin (2 * k + 1)) (x : ℝ) :
    d4ThetaHawkingChargeDecayInputFrequency k
        (d4ThetaHawkingChargeDecayAliasPoint k j x) =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus
        (d4ThetaHawkingChargeDecayAliasOvertone k j)
        (d4ThetaCuspHawkingQuadraticDealiasedLift
          (d4ThetaHawkingChargeDecayAliasPoint k j x)) := by
  rw [← sub_eq_zero]
  change d4ThetaHawkingChargeMinusTwoFundamentalFrequency
      (d4ThetaHawkingChargeDecayDirectMultiplicity k)
      (d4ThetaHawkingChargeDecayAliasPoint k j x) - _ = 0
  rw [d4ThetaHawkingChargeMinusTwoFundamentalFrequency_sub_qnmMinus]
  rw [d4ThetaHawkingChargeDecayAliasPoint_im]
  simp [d4ThetaHawkingChargeDecayDirectMultiplicity,
    d4ThetaHawkingChargeDecayAliasOvertone,
    d4ThetaHawkingChargeDecayAliasTilt]
  have hk : (k : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  field_simp [hk]
  ring

theorem d4ThetaHawkingChargeDecayAlias_jost_eq_zero
    (k : ℕ) (j : Fin (2 * k + 1)) (x : ℝ) :
    d4ThetaHawkingChargeDecayNegativeJost k
        (d4ThetaHawkingChargeDecayAliasPoint k j x) = 0 := by
  unfold d4ThetaHawkingChargeDecayNegativeJost
  rw [d4ThetaHawkingChargeDecayAlias_frequency_eq]
  exact thetaCuspHawkingHypergeometricJostMinus_qnm_zero _ _

theorem d4ThetaHawkingChargeDecayAliasPoint_injective
    (k : ℕ) (x : ℝ) :
    Function.Injective (fun j : Fin (2 * k + 1) =>
      d4ThetaHawkingChargeDecayAliasPoint k j x) := by
  intro i j h
  have him := congrArg Complex.im h
  rw [d4ThetaHawkingChargeDecayAliasPoint_im,
    d4ThetaHawkingChargeDecayAliasPoint_im] at him
  unfold d4ThetaHawkingChargeDecayAliasTilt at him
  apply Fin.ext
  have hk : (0 : ℝ) < 2 * ((k + 1 : ℕ) : ℝ) := by positivity
  have hkne : (2 * ((k + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hk
  field_simp [hkne] at him
  have hij : ((i : ℕ) : ℝ) = (j : ℕ) := by
    linarith
  exact_mod_cast hij

theorem card_d4ThetaHawkingChargeDecayAliasOvertoneWindow (k : ℕ) :
    (Finset.Icc (4 * k + 3) (6 * k + 3)).card = 2 * k + 1 := by
  simp
  omega

theorem card_d4ThetaHawkingChargeDecayAliasOvertoneWindow_eq_one_iff (k : ℕ) :
    (Finset.Icc (4 * k + 3) (6 * k + 3)).card = 1 ↔ k = 0 := by
  rw [card_d4ThetaHawkingChargeDecayAliasOvertoneWindow]
  omega

theorem d4ThetaHawkingChargeDecayNegativeJost_eq_zero_iff_aliasWindow
    (k : ℕ) (z : ℂ) (hzlo : -1 / 2 < z.im) (hzhi : z.im < 1 / 2) :
    d4ThetaHawkingChargeDecayNegativeJost k z = 0 ↔
      ∃ m : ℕ,
        4 * k + 3 ≤ m ∧ m ≤ 6 * k + 3 ∧
          z.im =
            (((5 * k + 3 : ℕ) : ℝ) - (m : ℝ)) /
              (2 * ((k + 1 : ℕ) : ℝ)) := by
  unfold d4ThetaHawkingChargeDecayNegativeJost
    thetaCuspHawkingHypergeometricJostMinus
  rw [d4ThetaHawkingChargeDecayInput_radialB]
  constructor
  · intro hzero
    unfold GaloisForLFunctions.reciprocalGammaEntire at hzero
    rw [inv_eq_zero, Complex.Gamma_eq_zero_iff] at hzero
    obtain ⟨m, hm⟩ := hzero
    have hre := congrArg Complex.re hm
    simp [d4ThetaHawkingChargeDecayTargetOvertone] at hre
    have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hscale : (0 : ℝ) < 2 * ((k + 1 : ℕ) : ℝ) := by positivity
    have hzloScaled := mul_lt_mul_of_pos_left hzlo hscale
    have hzhiScaled := mul_lt_mul_of_pos_left hzhi hscale
    have hmloR : ((4 * k + 2 : ℕ) : ℝ) < (m : ℝ) := by
      push_cast
      nlinarith
    have hmhiR : (m : ℝ) < ((6 * k + 4 : ℕ) : ℝ) := by
      push_cast
      nlinarith
    have hmlo : 4 * k + 3 ≤ m := by
      have : 4 * k + 2 < m := by exact_mod_cast hmloR
      omega
    have hmhi : m ≤ 6 * k + 3 := by
      have : m < 6 * k + 4 := by exact_mod_cast hmhiR
      omega
    refine ⟨m, hmlo, hmhi, ?_⟩
    apply (eq_div_iff (by positivity : (2 * ((k + 1 : ℕ) : ℝ)) ≠ 0)).2
    push_cast
    nlinarith
  · rintro ⟨m, _hmlo, _hmhi, him⟩
    unfold GaloisForLFunctions.reciprocalGammaEntire
    rw [inv_eq_zero, Complex.Gamma_eq_zero_iff]
    refine ⟨m, ?_⟩
    rw [him]
    simp [d4ThetaHawkingChargeDecayTargetOvertone]
    have hk : (k : ℂ) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero k
    field_simp [hk]
    ring

end

end RHTower

import GaloisForLFunctions.RHTower.DiagonalEllTwoOperator
import GaloisForLFunctions.RHTower.WeakSchattenResidue

open Filter Topology

/-!
# Gamma-six shell Green principal ideal

This file constructs the actual diagonal shell Green operator whose shell `m`
has multiplicity `5 * 6^m` and eigenvalue `6^(-m)`.  The sorted coordinate
model uses `Nat.log 6 (n + 216)`, because the shells start at `m = 3` and

`sum_{j=3}^{m-1} 5 * 6^j = 6^m - 216`.

The approximation numbers are therefore exact, not asymptotic.  The operator
lies in weak Schatten `S_{1,∞}` but not Schatten `S₁`; every complete shell has
trace mass exactly five.  Its positive powers give a concrete operator model
of the projective critical-edge ideal.  Both reflected powers belong to that
ideal exactly at horizontal rate zero.

The Wold coordinate embedding is also literal: `n ↦ 6*n + 1080` is
multiplication by six after restoring the `216` offset, and it scales the
principal Green eigenvalue by `1/6`.

All results are unconditional.  This module constructs the nonzero source
principal class and its strict two-orientation domain; it does not assert that
a completed-Xi comparison carries the full corrected Möbius remainder into
this domain.
-/

namespace RHTower

noncomputable section

def deningerGammaSixShellDepth (n : ℕ) : ℕ := Nat.log 6 (n + 216)

def deningerGammaSixShellEigenvalue (n : ℕ) : ℝ := (1 / 6 : ℝ) ^ deningerGammaSixShellDepth n

theorem deningerGammaSixShellDepth_mono : Monotone deningerGammaSixShellDepth := by
  intro i j hij
  exact Nat.log_mono_right (Nat.add_le_add_right hij 216)

theorem deningerGammaSixShellEigenvalue_nonneg (n : ℕ) : 0 ≤ deningerGammaSixShellEigenvalue n := by
  rw [deningerGammaSixShellEigenvalue]
  positivity

theorem deningerGammaSixShellEigenvalue_antitone : Antitone deningerGammaSixShellEigenvalue := by
  intro i j hij
  exact pow_le_pow_of_le_one (by positivity) (by norm_num)
    (deningerGammaSixShellDepth_mono hij)

theorem deningerGammaSixShellDepth_eq_of_shell {m n : ℕ}
    (hlo : 6 ^ m ≤ n + 216) (hi : n + 216 < 6 ^ (m + 1)) :
    deningerGammaSixShellDepth n = m := by
  exact Nat.log_eq_of_pow_le_of_lt_pow hlo hi

theorem deningerGammaSixShellEigenvalue_lower (n : ℕ) :
    1 / ((n : ℝ) + 216) ≤ deningerGammaSixShellEigenvalue n := by
  let d := deningerGammaSixShellDepth n
  have hpowNat : 6 ^ d ≤ n + 216 :=
    Nat.pow_log_le_self 6 (by omega)
  have hpow : (6 : ℝ) ^ d ≤ (n : ℝ) + 216 := by
    exact_mod_cast hpowNat
  change 1 / ((n : ℝ) + 216) ≤ (1 / 6 : ℝ) ^ d
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) hpow

theorem deningerGammaSixShellEigenvalue_upper (n : ℕ) :
    deningerGammaSixShellEigenvalue n ≤ 6 / ((n : ℝ) + 216) := by
  let d := deningerGammaSixShellDepth n
  have hltNat : n + 216 < 6 ^ (d + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) (n + 216)
  have hleNat : n + 216 ≤ 6 * 6 ^ d := by
    rw [Nat.pow_succ] at hltNat
    omega
  have hle : (n : ℝ) + 216 ≤ 6 * (6 : ℝ) ^ d := by
    exact_mod_cast hleNat
  change (1 / 6 : ℝ) ^ d ≤ 6 / ((n : ℝ) + 216)
  rw [one_div_pow]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (6 : ℝ) ^ d)
    (by positivity : (0 : ℝ) < (n : ℝ) + 216)]
  simpa [mul_comm] using hle

theorem deningerGammaSixShellEigenvalue_upper_harmonic (n : ℕ) :
    deningerGammaSixShellEigenvalue n ≤ 6 / ((n : ℝ) + 1) := by
  exact (deningerGammaSixShellEigenvalue_upper n).trans
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith))

theorem not_summable_deningerGammaSixShellEigenvalue : ¬ Summable deningerGammaSixShellEigenvalue := by
  intro hsum
  have hlower : Summable (fun n : ℕ => 1 / ((n : ℝ) + 216)) :=
    hsum.of_nonneg_of_le (fun n => by positivity) deningerGammaSixShellEigenvalue_lower
  have hshift : Summable (fun n : ℕ => 1 / |(n : ℝ) + 216| ^ (1 : ℝ)) := by
    apply hlower.congr
    intro n
    rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 216),
      Real.rpow_one]
  have : (1 : ℝ) < 1 :=
    (Real.summable_one_div_nat_add_rpow 216 1).mp hshift
  norm_num at this

abbrev DeningerGammaSixPositiveExponent := {p : ℝ // 0 < p}

def deningerGammaSixShellPowerWeight (p : DeningerGammaSixPositiveExponent) (n : ℕ) : ℝ :=
  deningerGammaSixShellEigenvalue n ^ (p : ℝ)

theorem deningerGammaSixShellPowerWeight_nonneg (p : DeningerGammaSixPositiveExponent) (n : ℕ) :
    0 ≤ deningerGammaSixShellPowerWeight p n := Real.rpow_nonneg (deningerGammaSixShellEigenvalue_nonneg n) _

theorem deningerGammaSixShellPowerWeight_antitone (p : DeningerGammaSixPositiveExponent) :
    Antitone (deningerGammaSixShellPowerWeight p) := by
  intro i j hij
  exact Real.rpow_le_rpow (deningerGammaSixShellEigenvalue_nonneg j) (deningerGammaSixShellEigenvalue_antitone hij) p.property.le

def deningerGammaSixShellPowerOperator (p : DeningerGammaSixPositiveExponent) : EllTwo →L[ℂ] EllTwo :=
  antitoneDiagonalOperator (deningerGammaSixShellPowerWeight p)
    (deningerGammaSixShellPowerWeight_nonneg p) (fun {_ _} h => deningerGammaSixShellPowerWeight_antitone p h)

theorem approxNumber_deningerGammaSixShellPowerOperator (p : DeningerGammaSixPositiveExponent) (n : ℕ) :
    approxNumber (deningerGammaSixShellPowerOperator p) n = deningerGammaSixShellPowerWeight p n := by
  exact approxNumber_antitoneDiagonalOperator_eq _
    (deningerGammaSixShellPowerWeight_nonneg p) (fun {_ _} h => deningerGammaSixShellPowerWeight_antitone p h) n

theorem memSchattenClass_one_deningerGammaSixShellPowerOperator_iff (p : DeningerGammaSixPositiveExponent) :
    MemSchattenClass 1 (deningerGammaSixShellPowerOperator p) ↔
      Summable (deningerGammaSixShellPowerWeight p) := by
  unfold MemSchattenClass
  simp_rw [approxNumber_deningerGammaSixShellPowerOperator, Real.rpow_one]

theorem summable_deningerGammaSixShellPowerWeight_of_one_lt
    (p : DeningerGammaSixPositiveExponent) (hp : 1 < (p : ℝ)) :
    Summable (deningerGammaSixShellPowerWeight p) := by
  have hbase : Summable (fun n : ℕ =>
      6 ^ (p : ℝ) / |(n : ℝ) + 216| ^ (p : ℝ)) := by
    have hs := (Real.summable_one_div_nat_add_rpow 216 (p : ℝ)).2 hp
    simpa only [mul_one_div] using hs.mul_left (6 ^ (p : ℝ))
  apply hbase.of_nonneg_of_le (deningerGammaSixShellPowerWeight_nonneg p)
  intro n
  have hu := deningerGammaSixShellEigenvalue_upper n
  have hpow := Real.rpow_le_rpow (deningerGammaSixShellEigenvalue_nonneg n) hu p.property.le
  calc
    deningerGammaSixShellPowerWeight p n ≤ (6 / ((n : ℝ) + 216)) ^ (p : ℝ) := hpow
    _ = 6 ^ (p : ℝ) / |(n : ℝ) + 216| ^ (p : ℝ) := by
      rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 216),
        Real.div_rpow (by norm_num : (0 : ℝ) ≤ 6) (by positivity)]

theorem deningerGammaSixShellPowerOperator_memSchattenClass_one_of_one_lt
    (p : DeningerGammaSixPositiveExponent) (hp : 1 < (p : ℝ)) :
    MemSchattenClass 1 (deningerGammaSixShellPowerOperator p) :=
  (memSchattenClass_one_deningerGammaSixShellPowerOperator_iff p).2
    (summable_deningerGammaSixShellPowerWeight_of_one_lt p hp)

def deningerGammaSixOneExponent : DeningerGammaSixPositiveExponent := ⟨1, by norm_num⟩

theorem deningerGammaSixShellPowerWeight_one : deningerGammaSixShellPowerWeight deningerGammaSixOneExponent = deningerGammaSixShellEigenvalue := by
  funext n
  simp [deningerGammaSixShellPowerWeight, deningerGammaSixOneExponent]

theorem deningerGammaSixShellPowerOperator_not_memSchattenClass_one :
    ¬ MemSchattenClass 1 (deningerGammaSixShellPowerOperator deningerGammaSixOneExponent) := by
  rw [memSchattenClass_one_deningerGammaSixShellPowerOperator_iff, deningerGammaSixShellPowerWeight_one]
  exact not_summable_deningerGammaSixShellEigenvalue

def deningerGammaSixShellPrincipalOperator : EllTwo →L[ℂ] EllTwo :=
  deningerGammaSixShellPowerOperator deningerGammaSixOneExponent

theorem deningerGammaSixShellPrincipalOperator_weak :
    MemWeakSchattenClass 1 deningerGammaSixShellPrincipalOperator := by
  refine ⟨6, by norm_num, fun n => ?_⟩
  rw [deningerGammaSixShellPrincipalOperator, approxNumber_deningerGammaSixShellPowerOperator,
    deningerGammaSixShellPowerWeight_one, Real.rpow_one]
  exact deningerGammaSixShellEigenvalue_upper_harmonic n

theorem deningerGammaSixShellPrincipalOperator_not_traceClass :
    ¬ MemSchattenClass 1 deningerGammaSixShellPrincipalOperator :=
  deningerGammaSixShellPowerOperator_not_memSchattenClass_one

/-- **Exact source principal-class witness.**  The Gamma-six shell Green
operator represents a nonzero weak trace class modulo ordinary trace class. -/
theorem deningerGammaSixShellPrincipalClass_nonzero :
    MemWeakSchattenClass 1 deningerGammaSixShellPrincipalOperator ∧
      ¬ MemSchattenClass 1 deningerGammaSixShellPrincipalOperator :=
  ⟨deningerGammaSixShellPrincipalOperator_weak,
    deningerGammaSixShellPrincipalOperator_not_traceClass⟩

def DeningerGammaSixProjectiveTraceDomain (alpha : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ p : DeningerGammaSixPositiveExponent,
      (p : ℝ) = alpha + epsilon ∧
        MemSchattenClass 1 (deningerGammaSixShellPowerOperator p)

theorem DeningerGammaSixProjectiveTraceDomain_iff (alpha : ℝ) :
    DeningerGammaSixProjectiveTraceDomain alpha ↔ 1 ≤ alpha := by
  constructor
  · intro h
    by_contra hn
    have ha : alpha < 1 := lt_of_not_ge hn
    obtain ⟨p, hp, hmem⟩ := h (1 - alpha) (sub_pos.mpr ha)
    have hpOne : p = deningerGammaSixOneExponent := by
      apply Subtype.ext
      dsimp [deningerGammaSixOneExponent]
      linarith
    subst p
    exact deningerGammaSixShellPowerOperator_not_memSchattenClass_one hmem
  · intro ha epsilon hepsilon
    let p : DeningerGammaSixPositiveExponent :=
      ⟨alpha + epsilon, by linarith⟩
    refine ⟨p, rfl, deningerGammaSixShellPowerOperator_memSchattenClass_one_of_one_lt p ?_⟩
    dsimp [p]
    linarith

def DeningerGammaSixForwardEdgeInDomain (delta : ℝ) : Prop :=
  DeningerGammaSixProjectiveTraceDomain (1 - delta)

def DeningerGammaSixReflectedEdgeInDomain (delta : ℝ) : Prop :=
  DeningerGammaSixProjectiveTraceDomain (1 + delta)

theorem DeningerGammaSixForwardEdgeInDomain_iff (delta : ℝ) :
    DeningerGammaSixForwardEdgeInDomain delta ↔ delta ≤ 0 := by
  change DeningerGammaSixProjectiveTraceDomain (1 - delta) ↔ delta ≤ 0
  rw [DeningerGammaSixProjectiveTraceDomain_iff]
  constructor <;> intro h <;> linarith

theorem DeningerGammaSixReflectedEdgeInDomain_iff (delta : ℝ) :
    DeningerGammaSixReflectedEdgeInDomain delta ↔ 0 ≤ delta := by
  change DeningerGammaSixProjectiveTraceDomain (1 + delta) ↔ 0 ≤ delta
  rw [DeningerGammaSixProjectiveTraceDomain_iff]
  constructor <;> intro h <;> linarith

theorem DeningerGammaSixBothEdgesInDomain_iff (delta : ℝ) :
    DeningerGammaSixForwardEdgeInDomain delta ∧ DeningerGammaSixReflectedEdgeInDomain delta ↔ delta = 0 := by
  rw [DeningerGammaSixForwardEdgeInDomain_iff, DeningerGammaSixReflectedEdgeInDomain_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 h2
  · rintro rfl
    exact ⟨le_rfl, le_rfl⟩

def deningerGammaSixWoldCoordinate (n : ℕ) : ℕ := 6 * n + 1080

theorem deningerGammaSixShellDepth_wold (n : ℕ) :
    deningerGammaSixShellDepth (deningerGammaSixWoldCoordinate n) = deningerGammaSixShellDepth n + 1 := by
  rw [deningerGammaSixShellDepth, deningerGammaSixShellDepth, deningerGammaSixWoldCoordinate]
  have harg : 6 * n + 1080 + 216 = (n + 216) * 6 := by omega
  rw [harg, Nat.log_mul_base (by norm_num) (by omega)]

theorem deningerGammaSixShellEigenvalue_wold (n : ℕ) :
    deningerGammaSixShellEigenvalue (deningerGammaSixWoldCoordinate n) = (1 / 6 : ℝ) * deningerGammaSixShellEigenvalue n := by
  rw [deningerGammaSixShellEigenvalue, deningerGammaSixShellEigenvalue, deningerGammaSixShellDepth_wold, pow_succ]
  ring

def deningerGammaSixShellCoordinates (m : ℕ) : Finset ℕ :=
  Finset.Ico (6 ^ m - 216) (6 ^ (m + 1) - 216)

theorem deningerGammaSix_pow_three_le {m : ℕ} (hm : 3 ≤ m) : 216 ≤ 6 ^ m := by
  calc
    216 = 6 ^ 3 := by norm_num
    _ ≤ 6 ^ m := Nat.pow_le_pow_right (by norm_num) hm

theorem deningerGammaSixShellCoordinates_card {m : ℕ} (hm : 3 ≤ m) :
    (deningerGammaSixShellCoordinates m).card = 5 * 6 ^ m := by
  rw [deningerGammaSixShellCoordinates, Nat.card_Ico]
  have hlo := deningerGammaSix_pow_three_le hm
  have hhi : 216 ≤ 6 ^ (m + 1) := hlo.trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m))
  rw [Nat.pow_succ]
  omega

theorem deningerGammaSixShellEigenvalue_eq_on_shell {m n : ℕ} (hm : 3 ≤ m)
    (hn : n ∈ deningerGammaSixShellCoordinates m) :
    deningerGammaSixShellEigenvalue n = (1 / 6 : ℝ) ^ m := by
  rw [deningerGammaSixShellCoordinates, Finset.mem_Ico] at hn
  have hloPow := deningerGammaSix_pow_three_le hm
  have hhiPow : 216 ≤ 6 ^ (m + 1) := hloPow.trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m))
  rw [deningerGammaSixShellEigenvalue]
  congr 1
  apply deningerGammaSixShellDepth_eq_of_shell
  · omega
  · omega

theorem deningerGammaSixShellTraceMass_eq_five {m : ℕ} (hm : 3 ≤ m) :
    ∑ n ∈ deningerGammaSixShellCoordinates m, deningerGammaSixShellEigenvalue n = 5 := by
  calc
    ∑ n ∈ deningerGammaSixShellCoordinates m, deningerGammaSixShellEigenvalue n =
        ∑ _n ∈ deningerGammaSixShellCoordinates m, (1 / 6 : ℝ) ^ m := by
      apply Finset.sum_congr rfl
      intro n hn
      exact deningerGammaSixShellEigenvalue_eq_on_shell hm hn
    _ = ((deningerGammaSixShellCoordinates m).card : ℝ) * (1 / 6 : ℝ) ^ m := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = 5 := by
      rw [deningerGammaSixShellCoordinates_card hm]
      push_cast
      rw [one_div_pow]
      field_simp

end

end RHTower

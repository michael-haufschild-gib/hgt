import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownAggregateCofactorReceiver
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownSelectedFactorFrequencySplit
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownWindowRelevantDichotomy

/-!
# Simultaneous selected factors for all active degree-three boxes

Every active window-relevant box has a factor of length at least the eighth root of the physical
lower edge.  The choices are made simultaneously over the finite box type.  If a chosen factor is
Möbius, its literal dyadic length remains below the Heath--Brown cutoff.
-/

namespace RHTower.Sieve

open Finset Filter

noncomputable section

/-- The eighth-root factor lower bound converts a fixed ambient eighth-power cutoff into a
uniform lower bound for every selected dyadic exponent. -/
theorem exponent_le_of_eight_pow_le_of_rpow_oneEighth_le
    {a q0 q : ℕ} (hlarge : 2 ^ (8 * q0) ≤ a)
    (hfactor : (a : ℝ) ^ (1 / 8 : ℝ) ≤ (((2 ^ q : ℕ) : ℝ))) :
    q0 ≤ q := by
  have hcast : (((2 ^ (8 * q0) : ℕ) : ℝ)) ≤ (a : ℝ) := by
    exact_mod_cast hlarge
  have hrpow := Real.rpow_le_rpow
    (by positivity : (0 : ℝ) ≤ ((2 ^ (8 * q0) : ℕ) : ℝ))
    hcast (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hroot : (((2 ^ q0 : ℕ) : ℝ)) ≤ (a : ℝ) ^ (1 / 8 : ℝ) := by
    calc
      (((2 ^ q0 : ℕ) : ℝ)) = (2 : ℝ) ^ (q0 : ℕ) := by norm_num
      _ = (2 : ℝ) ^ (q0 : ℝ) := (Real.rpow_natCast 2 q0).symm
      _ = (2 : ℝ) ^ (((8 * q0 : ℕ) : ℝ) * (1 / 8 : ℝ)) := by
        congr 1
        push_cast
        ring
      _ = ((2 : ℝ) ^ ((8 * q0 : ℕ) : ℝ)) ^ (1 / 8 : ℝ) := by
        rw [Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2)]
      _ = (((2 : ℝ) ^ (8 * q0 : ℕ))) ^ (1 / 8 : ℝ) := by
        rw [Real.rpow_natCast]
      _ = (((2 ^ (8 * q0) : ℕ) : ℝ)) ^ (1 / 8 : ℝ) := by norm_num
      _ ≤ (a : ℝ) ^ (1 / 8 : ℝ) := hrpow
  have hpowsReal : (((2 ^ q0 : ℕ) : ℝ)) ≤ (((2 ^ q : ℕ) : ℝ)) :=
    hroot.trans hfactor
  have hpowsNat : 2 ^ q0 ≤ 2 ^ q := by exact_mod_cast hpowsReal
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hpowsNat

/-- Simultaneous literal factor selection for every box occurring in the active aggregate. -/
theorem exists_activeBox_selectedFactor
    {L X : ℕ} {T0 t a : ℝ} (hL : 1 ≤ L) (ha : (64 : ℝ) ^ 8 ≤ a) :
    ∃ j : (box : HeathBrownBoxChoice L X 3) →
        HeathBrownBoxFactorIndex 3 box.m,
      ∀ box ∈ menonHeathBrownActiveBoxes L X T0 t a,
        1 ≤ heathBrownBoxFactorExponent box.a box.b box.q (j box) ∧
        a ^ (1 / 8 : ℝ) ≤
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q (j box) : ℕ) : ℝ)) ∧
        (heathBrownBoxFactorKind 3 box.m (j box) = .moebius →
          2 ^ heathBrownBoxFactorExponent box.a box.b box.q (j box) ≤ L) := by
  classical
  have hchoice : ∀ box : HeathBrownBoxChoice L X 3,
      ∃ i : HeathBrownBoxFactorIndex 3 box.m,
        box ∈ menonHeathBrownActiveBoxes L X T0 t a →
          1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i ∧
          a ^ (1 / 8 : ℝ) ≤
            (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ∧

          (heathBrownBoxFactorKind 3 box.m i = .moebius →
            2 ^ heathBrownBoxFactorExponent box.a box.b box.q i ≤ L) := by
    intro box
    by_cases hactive : box ∈ menonHeathBrownActiveBoxes L X T0 t a
    · have hrelevant : IsHeathBrownBoxWindowRelevant a X 3 box := by
        have := hactive
        simp only [menonHeathBrownActiveBoxes, Finset.mem_filter, Finset.mem_univ,
          true_and] at this
        exact this.2
      have ha1 : 1 < a := (by norm_num : (1 : ℝ) < 64 ^ 8).trans_le ha
      have hwidth := windowRelevant_heathBrownBox_coreLower_gt hrelevant
      have hdiv : a / 64 <
          (groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) := by
        norm_num at hwidth ⊢
        exact hwidth
      have hedge : a ^ (7 / 8 : ℝ) ≤
          (groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) :=
        (rpow_sevenEighth_le_div_sixtyFour_of_pow_eight_le ha).trans hdiv.le
      rcases exists_heathBrown_three_medium_or_long_zeta_log_cutoff
          box hL ha1 hedge with hmedium | hlong
      · obtain ⟨i, hlo, hiL⟩ := hmedium
        refine ⟨i, fun _ => ⟨i.property, hlo, ?_⟩⟩
        intro _hkind
        exact_mod_cast hiL
      · obtain ⟨i, hlo, _hLi, hkind⟩ := hlong
        refine ⟨i, fun _ => ⟨i.property, hlo, ?_⟩⟩
        intro hmoebius
        rcases hkind with hzeta | hlog
        · rw [hmoebius] at hzeta
          contradiction
        · rw [hmoebius] at hlog
          contradiction
    · let fallback : HeathBrownBoxFactorIndex 3 box.m := Sum.inr (Sum.inr Unit.unit)
      exact ⟨fallback, fun hmem => (hactive hmem).elim⟩
  choose j hj using hchoice
  exact ⟨j, fun box hbox => hj box hbox⟩

/-- Once the physical lower edge is large enough, every simultaneously selected active-box
factor lies beyond any prescribed dyadic exponent. -/
theorem eventually_activeBox_selectedFactor_exponent_ge (q0 : ℕ) :
    ∀ᶠ a : ℕ in atTop,
      ∀ {L X : ℕ} {T0 t : ℝ} (j : (box : HeathBrownBoxChoice L X 3) →
        HeathBrownBoxFactorIndex 3 box.m),
      (∀ box ∈ menonHeathBrownActiveBoxes L X T0 t (a : ℝ),
        (a : ℝ) ^ (1 / 8 : ℝ) ≤
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q (j box) : ℕ) : ℝ))) →
      ∀ box ∈ menonHeathBrownActiveBoxes L X T0 t (a : ℝ),
        q0 ≤ heathBrownBoxFactorExponent box.a box.b box.q (j box) := by
  filter_upwards [Filter.eventually_ge_atTop (2 ^ (8 * q0))] with a ha
  intro L X T0 t j hfactor box hbox
  exact exponent_le_of_eight_pow_le_of_rpow_oneEighth_le ha (hfactor box hbox)

end

end RHTower.Sieve

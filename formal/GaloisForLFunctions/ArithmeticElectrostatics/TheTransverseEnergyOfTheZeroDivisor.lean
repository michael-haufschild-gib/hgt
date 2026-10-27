import GaloisForLFunctions.RHTower.AngularEnergyQuantization
import GaloisForLFunctions.RHTower.TransverseAttainment

/-!
# The transverse energy of the zero divisor

Put a unit charge at each distinct zero of `ξ`. The **transverse energy** of the divisor is

  `𝓔 = ½ Σ_{ρ ≠ ρ'} (Re ρ − Re ρ')²/|ρ − ρ'|² ∈ [0, ∞]`,

half the sum of the angular energies of the zeros (`RHTower.angularEnergy`). It is the
electrostatic energy whose gradient is the transverse force of the marginality identity.

* **Vanishing and gap** (`divisorTransverseEnergy_eq_zero_iff`,
  `riemannHypothesis_iff_divisorTransverseEnergy_lt_one`): `𝓔 = 0` iff RH, and `𝓔 < 1` iff RH; every
  finite set of off-line zeros has at most `2𝓔` elements (`card_le_two_mul_divisorTransverseEnergy`),
  because each off-line zero carries the unit quantum of its reflection pair.
* **Finiteness is the finite off-line index** (`divisorTransverseEnergy_lt_top_iff`): `𝓔 < ∞` iff
  only finitely many zeros are off the line. An infinite off-line set has infinite energy; a finite
  one has energy at most twice the angular energy of its own zeros, since a pair of critical zeros
  contributes nothing.
* **Work equals energy** (`tsum_angularEnergy_eq_two_mul_work`,
  `divisorTransverseEnergy_eq_ofReal_work`): when the off-line set is finite, the energy is the work
  `Σ_{ρ off-line} (Re ρ − ½) F(ρ)` of the transverse force `F` against the displacement. Each pair
  term splits as `δ_j F_{jk} + δ_k F_{kj}`, and only the finitely many off-line displacements are
  nonzero.

So RH has three electrostatic forms of increasing strength — zero energy, energy below one quantum,
and, at finite off-line index, total outward work below one — and the finite off-line index (a
classical problem weaker than RH) is exactly finiteness of the transverse energy.
-/

open Finset RHTower
open scoped ENNReal

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

/-- The **transverse energy** of the zero divisor, with a unit charge at each distinct zero. -/
def divisorTransverseEnergy : ℝ≥0∞ :=
  (∑' j : XiDivisorSupport, ENNReal.ofReal (angularEnergy j)) / 2

/-- The displacement of a zero from the critical line. -/
def displacement (j : XiDivisorSupport) : ℝ := (j : ℂ).re - 1 / 2

theorem two_mul_divisorTransverseEnergy :
    2 * divisorTransverseEnergy = ∑' j : XiDivisorSupport, ENNReal.ofReal (angularEnergy j) :=
  ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- The angular term is symmetric. -/
theorem angularEnergyTerm_comm (j k : XiDivisorSupport) :
    angularEnergyTerm j k = angularEnergyTerm k j := by
  unfold angularEnergyTerm
  by_cases h : k = j
  · subst h; rfl
  · rw [if_neg h, if_neg fun h' => h h'.symm,
      show Complex.normSq ((k : ℂ) - j) = Complex.normSq ((j : ℂ) - k) by
        rw [← Complex.normSq_neg, neg_sub]]
    ring

/-- Two critical zeros do not interact transversally. -/
theorem angularEnergyTerm_eq_zero_of_critical {j k : XiDivisorSupport}
    (hj : (j : ℂ).re = 1 / 2) (hk : (k : ℂ).re = 1 / 2) : angularEnergyTerm j k = 0 := by
  unfold angularEnergyTerm
  split_ifs
  · rfl
  · rw [hj, hk]; simp

theorem not_mem_offLineSupport_iff {j : XiDivisorSupport} :
    j ∉ offLineSupport ↔ (j : ℂ).re = 1 / 2 := by
  simp [offLineSupport]

/-! ### Vanishing, quantization and the gap -/

/-- **Zero energy is RH.** -/
theorem divisorTransverseEnergy_eq_zero_iff : divisorTransverseEnergy = 0 ↔ RiemannHypothesis := by
  rw [divisorTransverseEnergy, ENNReal.div_eq_zero_iff, or_iff_left ENNReal.ofNat_ne_top,
    ENNReal.tsum_eq_zero, riemannHypothesis_iff_forall_angularEnergy_eq_zero]
  refine forall_congr' fun j => ?_
  rw [ENNReal.ofReal_eq_zero]
  exact ⟨fun h => le_antisymm h (angularEnergy_nonneg j), le_of_eq⟩

/-- **Quantization**: a finite set of off-line zeros has at most twice the energy many elements. -/
theorem card_le_two_mul_divisorTransverseEnergy {s : Finset XiDivisorSupport}
    (hs : ∀ j ∈ s, (j : ℂ).re ≠ 1 / 2) : (s.card : ℝ≥0∞) ≤ 2 * divisorTransverseEnergy := by
  rw [two_mul_divisorTransverseEnergy]
  calc (s.card : ℝ≥0∞) = ∑ _j ∈ s, (1 : ℝ≥0∞) := by simp
    _ ≤ ∑ j ∈ s, ENNReal.ofReal (angularEnergy j) := sum_le_sum fun j hj => by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (one_le_angularEnergy (hs j hj))
    _ ≤ _ := ENNReal.sum_le_tsum s

/-- **The gap**: off the critical line the energy is at least one quantum. -/
theorem one_le_divisorTransverseEnergy {j : XiDivisorSupport} (hj : (j : ℂ).re ≠ 1 / 2) :
    1 ≤ divisorTransverseEnergy := by
  have hpj : (supportPartner j : ℂ).re ≠ 1 / 2 := by
    rw [supportPartner_re]; intro hc; exact hj (by linarith)
  have hne : supportPartner j ≠ j := fun hc => hj ((supportPartner_eq_self_iff j).mp hc)
  have h2 := card_le_two_mul_divisorTransverseEnergy (s := {j, supportPartner j})
    (by simp only [mem_insert, mem_singleton]; rintro k (rfl | rfl) <;> assumption)
  rw [card_pair hne.symm, two_mul_divisorTransverseEnergy] at h2
  rw [divisorTransverseEnergy, ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero)
    (Or.inl ENNReal.ofNat_ne_top), one_mul]
  exact_mod_cast h2

/-- **RH is energy below one quantum.** -/
theorem riemannHypothesis_iff_divisorTransverseEnergy_lt_one :
    RiemannHypothesis ↔ divisorTransverseEnergy < 1 := by
  constructor
  · intro h
    rw [divisorTransverseEnergy_eq_zero_iff.mpr h]
    exact zero_lt_one
  · intro hlt
    refine riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun j => ?_
    by_contra hj
    exact absurd (one_le_divisorTransverseEnergy hj) (not_le.mpr hlt)

/-! ### Finite energy is finite off-line index -/

/-- **Finite energy iff finitely many off-line zeros.** -/
theorem divisorTransverseEnergy_lt_top_iff :
    divisorTransverseEnergy < ⊤ ↔ offLineSupport.Finite := by
  constructor
  · intro hlt
    by_contra hinf
    have hle : ∀ n : ℕ, (n : ℝ≥0∞) ≤ 2 * divisorTransverseEnergy := fun n => by
      obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf n
      rw [← hcard]
      exact card_le_two_mul_divisorTransverseEnergy fun j hj => ht hj
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt
      (ENNReal.mul_lt_top (ENNReal.ofNat_lt_top (n := 2)) hlt).ne
    exact absurd (hle n) (not_le.mpr hn)
  · intro hfin
    set F := hfin.toFinset
    -- a critical zero only sees the finitely many off-line zeros
    have hbound : ∀ j, ENNReal.ofReal (angularEnergy j) ≤
        (if j ∈ F then ENNReal.ofReal (angularEnergy j) else 0) +
          ∑ k ∈ F, ENNReal.ofReal (angularEnergyTerm j k) := by
      intro j
      by_cases hj : j ∈ F
      · rw [if_pos hj]; exact le_self_add
      · rw [if_neg hj, zero_add]
        have hjre := not_mem_offLineSupport_iff.mp ((hfin.mem_toFinset).not.mp hj)
        have heq : angularEnergy j = ∑ k ∈ F, angularEnergyTerm j k :=
          tsum_eq_sum fun k hk => angularEnergyTerm_eq_zero_of_critical hjre
            (not_mem_offLineSupport_iff.mp ((hfin.mem_toFinset).not.mp hk))
        rw [heq, ENNReal.ofReal_sum_of_nonneg fun k _ => angularEnergyTerm_nonneg j k]
    have hsum : ∑' j, ENNReal.ofReal (angularEnergy j) ≤
        2 * ∑ k ∈ F, ENNReal.ofReal (angularEnergy k) := by
      calc ∑' j, ENNReal.ofReal (angularEnergy j)
          ≤ ∑' j, ((if j ∈ F then ENNReal.ofReal (angularEnergy j) else 0) +
              ∑ k ∈ F, ENNReal.ofReal (angularEnergyTerm j k)) := ENNReal.tsum_le_tsum hbound
        _ = ∑' j, (if j ∈ F then ENNReal.ofReal (angularEnergy j) else 0) +
              ∑' j, ∑ k ∈ F, ENNReal.ofReal (angularEnergyTerm j k) := ENNReal.tsum_add
        _ = ∑ j ∈ F, ENNReal.ofReal (angularEnergy j) +
              ∑ k ∈ F, ∑' j, ENNReal.ofReal (angularEnergyTerm j k) := by
            congr 1
            · exact (tsum_eq_sum fun j hj => if_neg hj).trans (sum_congr rfl fun j hj => if_pos hj)
            · exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable
        _ = ∑ j ∈ F, ENNReal.ofReal (angularEnergy j) +
              ∑ k ∈ F, ENNReal.ofReal (angularEnergy k) := by
            congr 1
            refine sum_congr rfl fun k _ => ?_
            rw [angularEnergy, ENNReal.ofReal_tsum_of_nonneg (angularEnergyTerm_nonneg k)
              (summable_angularEnergyTerm k)]
            exact tsum_congr fun j => by rw [angularEnergyTerm_comm]
        _ = 2 * ∑ k ∈ F, ENNReal.ofReal (angularEnergy k) := by rw [two_mul]
    rw [divisorTransverseEnergy]
    refine ENNReal.div_lt_top (ne_top_of_le_ne_top ?_ hsum) two_ne_zero
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top)

/-! ### Work equals energy at finite off-line index -/

/-- Each angular term is the work of the two transverse forces of the pair. -/
theorem angularEnergyTerm_eq_work (j k : XiDivisorSupport) :
    angularEnergyTerm j k =
      displacement j * transverseForceTerm j k + displacement k * transverseForceTerm k j := by
  unfold angularEnergyTerm transverseForceTerm displacement
  by_cases h : k = j
  · subst h; simp
  · rw [if_neg h, if_neg h, if_neg fun h' => h h'.symm,
      show Complex.normSq ((k : ℂ) - j) = Complex.normSq ((j : ℂ) - k) by
        rw [← Complex.normSq_neg, neg_sub]]
    ring

/-- **Work equals energy.** With finitely many off-line zeros the angular energies are summable and
their sum is twice the work `Σ_{ρ off-line} (Re ρ − ½) F(ρ)` of the transverse force. -/
theorem tsum_angularEnergy_eq_two_mul_work (hfin : offLineSupport.Finite) :
    Summable angularEnergy ∧
      ∑' j, angularEnergy j = 2 * ∑ j ∈ hfin.toFinset, displacement j * transverseForce j := by
  set F := hfin.toFinset
  have hdisp : ∀ k, k ∉ F → displacement k = 0 := fun k hk => by
    rw [displacement, not_mem_offLineSupport_iff.mp ((hfin.mem_toFinset).not.mp hk), sub_self]
  have hrow : ∀ j, angularEnergy j = displacement j * transverseForce j +
      ∑ k ∈ F, displacement k * transverseForceTerm k j := by
    intro j
    have h1 : Summable fun k => displacement j * transverseForceTerm j k :=
      (summable_transverseForceTerm j).mul_left _
    have h2 : Summable fun k => displacement k * transverseForceTerm k j :=
      summable_of_ne_finset_zero (s := F) fun k hk => by rw [hdisp k hk, zero_mul]
    rw [angularEnergy, transverseForce, tsum_congr (angularEnergyTerm_eq_work j), h1.tsum_add h2,
      tsum_mul_left, tsum_eq_sum (f := fun k => displacement k * transverseForceTerm k j) (s := F)
        fun k hk => by rw [hdisp k hk, zero_mul]]
  have hA : Summable fun j => displacement j * transverseForce j :=
    summable_of_ne_finset_zero (s := F) fun j hj => by rw [hdisp j hj, zero_mul]
  have hB : Summable fun j => ∑ k ∈ F, displacement k * transverseForceTerm k j :=
    summable_sum fun k _ => (summable_transverseForceTerm k).mul_left _
  refine ⟨(hA.add hB).congr fun j => (hrow j).symm, ?_⟩
  rw [tsum_congr hrow, hA.tsum_add hB,
    tsum_eq_sum (s := F) fun j hj => by rw [hdisp j hj, zero_mul],
    Summable.tsum_finsetSum fun k _ => (summable_transverseForceTerm k).mul_left _, two_mul]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [tsum_mul_left, transverseForce]

/-- The energy of a divisor with finitely many off-line zeros is their total outward work. -/
theorem divisorTransverseEnergy_eq_ofReal_work (hfin : offLineSupport.Finite) :
    divisorTransverseEnergy =
      ENNReal.ofReal (∑ j ∈ hfin.toFinset, displacement j * transverseForce j) := by
  obtain ⟨hs, heq⟩ := tsum_angularEnergy_eq_two_mul_work hfin
  have h2 : 2 * divisorTransverseEnergy =
      2 * ENNReal.ofReal (∑ j ∈ hfin.toFinset, displacement j * transverseForce j) := by
    rw [two_mul_divisorTransverseEnergy, ← ENNReal.ofReal_tsum_of_nonneg angularEnergy_nonneg hs,
      heq, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
  exact (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).mp h2

/-- **At finite off-line index, RH is total outward work below one.** -/
theorem riemannHypothesis_iff_work_lt_one (hfin : offLineSupport.Finite) :
    RiemannHypothesis ↔ ∑ j ∈ hfin.toFinset, displacement j * transverseForce j < 1 := by
  rw [riemannHypothesis_iff_divisorTransverseEnergy_lt_one,
    divisorTransverseEnergy_eq_ofReal_work hfin, ENNReal.ofReal_lt_one]

/-- At finite off-line index the outward work bounds the number of off-line zeros:
`#off-line ≤ 2 · work`. -/
theorem card_offLine_le_two_mul_work (hfin : offLineSupport.Finite) :
    (hfin.toFinset.card : ℝ) ≤ 2 * ∑ j ∈ hfin.toFinset, displacement j * transverseForce j := by
  obtain ⟨hs, heq⟩ := tsum_angularEnergy_eq_two_mul_work hfin
  rw [← heq]
  calc (hfin.toFinset.card : ℝ) = ∑ _j ∈ hfin.toFinset, (1 : ℝ) := by simp
    _ ≤ ∑ j ∈ hfin.toFinset, angularEnergy j := sum_le_sum fun j hj =>
        one_le_angularEnergy ((hfin.mem_toFinset).mp hj)
    _ ≤ ∑' j, angularEnergy j := hs.sum_le_tsum _ fun j _ => angularEnergy_nonneg j

end

end GaloisForLFunctions.ArithmeticElectrostatics

import GaloisForLFunctions.RHTower.CCMShiftCovariantPoleDivisorCapacity

/-!
# Every transverse divisor unit costs more than four units of trace slope

The initial trace slope of the shifted Hankel gap of a finite right-half divisor packet is the
squared `L²` norm of its anti-causal residue profile.  That norm is an explicit positive Cauchy form
in the divisor data, so it dominates its own diagonal, and each diagonal term of a zero at
transverse depth `a < 1/2` with multiplicity `m ≥ 1` exceeds `4m`.  The incoming pole at depth `1/2`
has energy exactly `4`, so a nonexpansive pole-to-divisor transfer admits no divisor unit at all.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set Filter Topology

noncomputable section

theorem complexConj_two : (starRingEnd ℂ) (2 : ℂ) = 2 := by
  apply Complex.ext <;> simp

/-- The `L²` energy of a divisor packet profile: the negative initial trace slope. -/
def divisorPacketEnergy {r : ℕ} (lam : Fin r → ℂ) (m : Fin r → ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), ‖divisorPacketProfile lam m t‖ ^ 2

/-- The positive Cauchy weight of a pair of divisor points. -/
def cauchyWeight (u v : ℂ) : ℝ :=
  (u.re + v.re) / ((u.re + v.re) ^ 2 + (u.im - v.im) ^ 2)

theorem cauchyWeight_pos {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) : 0 < cauchyWeight u v := by
  unfold cauchyWeight
  have hnum : 0 < u.re + v.re := by linarith
  have hden : 0 < (u.re + v.re) ^ 2 + (u.im - v.im) ^ 2 := by positivity
  positivity

theorem cauchyWeight_self (u : ℂ) (hu : 0 < u.re) : cauchyWeight u u = 1 / (2 * u.re) := by
  unfold cauchyWeight
  have h : (u.im - u.im) = 0 := by ring
  rw [h]
  have h2 : (u.re + u.re) ^ 2 + (0 : ℝ) ^ 2 = (2 * u.re) ^ 2 := by ring
  rw [h2]
  field_simp
  ring

theorem re_div_add_conj {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (c : ℝ) :
    (((c : ℂ)) / (u + (starRingEnd ℂ) v)).re = c * cauchyWeight u v := by
  have hne : u + (starRingEnd ℂ) v ≠ 0 := by
    intro h
    have hre : (u + (starRingEnd ℂ) v).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.conj_re] at hre
    linarith
  rw [div_eq_mul_inv, Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im, cauchyWeight]
  field_simp
  ring

/-! ## The exact energy -/

theorem ofReal_divisorPacketEnergy {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ}
    (hlam : ∀ j, 0 < (lam j).re) :
    ((divisorPacketEnergy lam m : ℝ) : ℂ) =
      ∑ j, ∑ k, (4 * (m j : ℂ) * (m k : ℂ)) / (lam j + (starRingEnd ℂ) (lam k)) := by
  have hre : ∀ j k : Fin r, 0 < (lam j + (starRingEnd ℂ) (lam k)).re := by
    intro j k
    simp only [Complex.add_re, Complex.conj_re]
    have := hlam j
    have := hlam k
    linarith
  have hpt : ∀ t : ℝ, ((‖divisorPacketProfile lam m t‖ ^ 2 : ℝ) : ℂ)
      = ∑ j, ∑ k, 4 * (m j : ℂ) * (m k : ℂ)
          * Complex.exp (-((lam j + (starRingEnd ℂ) (lam k)) * (t : ℂ))) := by
    intro t
    have hconj : (starRingEnd ℂ) (divisorPacketProfile lam m t)
        = 2 * ∑ k, (m k : ℂ) * Complex.exp (-((starRingEnd ℂ) (lam k) * (t : ℂ))) := by
      unfold divisorPacketProfile
      rw [map_mul, map_sum, complexConj_two]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, ← Complex.exp_conj]
      congr 1
      · simp
      · rw [map_neg, map_mul, Complex.conj_ofReal]
    have hsq : ((‖divisorPacketProfile lam m t‖ ^ 2 : ℝ) : ℂ)
        = divisorPacketProfile lam m t * (starRingEnd ℂ) (divisorPacketProfile lam m t) := by
      rw [Complex.mul_conj']
      push_cast
      ring
    rw [hsq, hconj]
    unfold divisorPacketProfile
    rw [show (2 * ∑ j, (m j : ℂ) * Complex.exp (-(lam j * (t : ℂ))))
        * (2 * ∑ k, (m k : ℂ) * Complex.exp (-((starRingEnd ℂ) (lam k) * (t : ℂ))))
        = 4 * ((∑ j, (m j : ℂ) * Complex.exp (-(lam j * (t : ℂ))))
          * ∑ k, (m k : ℂ) * Complex.exp (-((starRingEnd ℂ) (lam k) * (t : ℂ)))) from by ring]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hexp : Complex.exp (-(lam j * (t : ℂ)))
        * Complex.exp (-((starRingEnd ℂ) (lam k) * (t : ℂ)))
        = Complex.exp (-((lam j + (starRingEnd ℂ) (lam k)) * (t : ℂ))) := by
      rw [← Complex.exp_add]
      ring_nf
    linear_combination (4 * (m j : ℂ) * (m k : ℂ)) * hexp
  have hint : ∀ j k : Fin r, IntegrableOn
      (fun t : ℝ => 4 * (m j : ℂ) * (m k : ℂ)
        * Complex.exp (-((lam j + (starRingEnd ℂ) (lam k)) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume :=
    fun j k => (integrableOn_Ioi_cexp_neg_mul (hre j k)).const_mul _
  calc ((divisorPacketEnergy lam m : ℝ) : ℂ)
      = ∫ t in Ioi (0 : ℝ), ((‖divisorPacketProfile lam m t‖ ^ 2 : ℝ) : ℂ) :=
        (integral_complex_ofReal).symm
    _ = ∫ t in Ioi (0 : ℝ), ∑ j, ∑ k, 4 * (m j : ℂ) * (m k : ℂ)
          * Complex.exp (-((lam j + (starRingEnd ℂ) (lam k)) * (t : ℂ))) :=
        setIntegral_congr_fun measurableSet_Ioi fun t _ => hpt t
    _ = ∑ j, ∑ k, ∫ t in Ioi (0 : ℝ), 4 * (m j : ℂ) * (m k : ℂ)
          * Complex.exp (-((lam j + (starRingEnd ℂ) (lam k)) * (t : ℂ))) := by
        rw [integral_finsetSum _ fun j _ => (integrable_finsetSum _ fun k _ => hint j k)]
        exact Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun k _ => hint j k
    _ = ∑ j, ∑ k, (4 * (m j : ℂ) * (m k : ℂ)) / (lam j + (starRingEnd ℂ) (lam k)) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul, integral_Ioi_cexp_neg_mul (hre j k), div_eq_mul_inv]

/-- **Equation (7), first half.**  The energy is the explicit positive Cauchy form. -/
theorem divisorPacketEnergy_eq {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ}
    (hlam : ∀ j, 0 < (lam j).re) :
    divisorPacketEnergy lam m
      = ∑ j, ∑ k, 4 * (m j : ℝ) * (m k : ℝ) * cauchyWeight (lam j) (lam k) := by
  have h := congrArg Complex.re (ofReal_divisorPacketEnergy (m := m) hlam)
  rw [Complex.ofReal_re] at h
  rw [h, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcast : (4 * (m j : ℂ) * (m k : ℂ)) = (((4 * (m j : ℝ) * (m k : ℝ) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hcast, re_div_add_conj (hlam j) (hlam k)]

/-! ## The coercivity law -/

/-- **Equation (7), second half.**  The energy dominates its own diagonal. -/
theorem diagonal_le_divisorPacketEnergy {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ}
    (hlam : ∀ j, 0 < (lam j).re) :
    ∑ j, 2 * (m j : ℝ) ^ 2 / (lam j).re ≤ divisorPacketEnergy lam m := by
  rw [divisorPacketEnergy_eq hlam]
  refine Finset.sum_le_sum fun j _ => ?_
  have hdiag : 4 * (m j : ℝ) * (m j : ℝ) * cauchyWeight (lam j) (lam j)
      = 2 * (m j : ℝ) ^ 2 / (lam j).re := by
    rw [cauchyWeight_self _ (hlam j)]
    have hne : (lam j).re ≠ 0 := ne_of_gt (hlam j)
    field_simp
    ring
  rw [← hdiag]
  refine Finset.single_le_sum (f := fun k => 4 * (m j : ℝ) * (m k : ℝ)
    * cauchyWeight (lam j) (lam k)) (fun k _ => ?_) (Finset.mem_univ j)
  have := (cauchyWeight_pos (hlam j) (hlam k)).le
  positivity

/-- **Equation (6).**  Every transverse divisor unit costs strictly more than four units. -/
theorem four_mul_multiplicity_lt_divisorPacketEnergy {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ}
    (hlam : ∀ j, 0 < (lam j).re) (hstrip : ∀ j, (lam j).re < 1 / 2) (hm : ∀ j, 0 < m j)
    (j₀ : Fin r) :
    4 * ((divisorPacketMultiplicity m : ℕ) : ℝ) < divisorPacketEnergy lam m := by
  have hdiag := diagonal_le_divisorPacketEnergy (m := m) hlam
  have hterm : ∀ j : Fin r, 4 * (m j : ℝ) < 2 * (m j : ℝ) ^ 2 / (lam j).re := by
    intro j
    have ha := hlam j
    have hs := hstrip j
    have hm1 : (1 : ℝ) ≤ (m j : ℝ) := by exact_mod_cast hm j
    rw [lt_div_iff₀ ha]
    nlinarith
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨j₀, Finset.mem_univ j₀⟩
  have hsum : ∑ j, 4 * (m j : ℝ) < ∑ j, 2 * (m j : ℝ) ^ 2 / (lam j).re :=
    Finset.sum_lt_sum_of_nonempty hne fun j _ => hterm j
  have hcast : 4 * ((divisorPacketMultiplicity m : ℕ) : ℝ) = ∑ j, 4 * (m j : ℝ) := by
    unfold divisorPacketMultiplicity
    push_cast
    rw [Finset.mul_sum]
  rw [hcast]
  linarith

/-! ## The incoming pole saturates the unit cost -/

/-- The `L²` energy of the incoming pole profile. -/
def polePacketEnergy : ℝ := ∫ t in Ioi (0 : ℝ), ‖polePacketProfile t‖ ^ 2

/-- **Equation (11).**  The incoming pole at transverse depth `1/2` costs exactly four units. -/
theorem polePacketEnergy_eq_four : polePacketEnergy = 4 := by
  have hpt : ∀ t : ℝ, ((‖polePacketProfile t‖ ^ 2 : ℝ) : ℂ)
      = 4 * Complex.exp (-((1 : ℂ) * (t : ℂ))) := by
    intro t
    have hconj : (starRingEnd ℂ) (polePacketProfile t)
        = 2 * Complex.exp (-((1 / 2 : ℂ) * (t : ℂ))) := by
      unfold polePacketProfile
      rw [map_mul, ← Complex.exp_conj, complexConj_two, map_neg, map_mul, Complex.conj_ofReal,
        map_div₀, complexConj_two]
      simp
    have hsq : ((‖polePacketProfile t‖ ^ 2 : ℝ) : ℂ)
        = polePacketProfile t * (starRingEnd ℂ) (polePacketProfile t) := by
      rw [Complex.mul_conj']
      push_cast
      ring
    rw [hsq, hconj]
    unfold polePacketProfile
    have hexp : Complex.exp (-((1 / 2 : ℂ) * (t : ℂ))) * Complex.exp (-((1 / 2 : ℂ) * (t : ℂ)))
        = Complex.exp (-((1 : ℂ) * (t : ℂ))) := by
      rw [← Complex.exp_add]
      ring_nf
    linear_combination (4 : ℂ) * hexp
  have hone : (0 : ℝ) < (1 : ℂ).re := by norm_num
  have hcast : ((polePacketEnergy : ℝ) : ℂ) = 4 := by
    calc ((polePacketEnergy : ℝ) : ℂ)
        = ∫ t in Ioi (0 : ℝ), ((‖polePacketProfile t‖ ^ 2 : ℝ) : ℂ) :=
          (integral_complex_ofReal).symm
      _ = ∫ t in Ioi (0 : ℝ), 4 * Complex.exp (-((1 : ℂ) * (t : ℂ))) :=
          setIntegral_congr_fun measurableSet_Ioi fun t _ => hpt t
      _ = 4 := by
          rw [integral_const_mul, integral_Ioi_cexp_neg_mul hone]
          norm_num
  exact_mod_cast hcast

/-- **Equation (13).**  A nonexpansive pole-to-divisor transfer admits no divisor unit. -/
theorem divisorPacket_isEmpty_of_energy_le_pole {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ}
    (hlam : ∀ j, 0 < (lam j).re) (hstrip : ∀ j, (lam j).re < 1 / 2) (hm : ∀ j, 0 < m j)
    (hbudget : divisorPacketEnergy lam m ≤ polePacketEnergy) :
    r = 0 := by
  by_contra hr
  obtain ⟨j₀⟩ : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hr)
  have hlow := four_mul_multiplicity_lt_divisorPacketEnergy hlam hstrip hm j₀
  rw [polePacketEnergy_eq_four] at hbudget
  have hkappa : 1 ≤ ((divisorPacketMultiplicity m : ℕ) : ℝ) := by
    have : 1 ≤ divisorPacketMultiplicity m := by
      unfold divisorPacketMultiplicity
      calc 1 ≤ m j₀ := hm j₀
        _ ≤ ∑ j, m j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j₀)
    exact_mod_cast this
  linarith

end

end GaloisForLFunctions.RHTower

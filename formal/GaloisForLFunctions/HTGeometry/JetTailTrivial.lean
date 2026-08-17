import GaloisForLFunctions.HTGeometry.JetChainDescent
import GaloisForLFunctions.HTGeometry.JetShiftPropagation
import GaloisForLFunctions.HTGeometry.JetUniformStrip
import GaloisForLFunctions.HTGeometry.JetShiftLevelInduction

/-!
# No normalizing shift above jet level three

The descent chain closes at even levels, where the range condition `2t < N` of the chain and the
order crossing `t + 2 > N − t` share the integer `t = (N−1)/2` — that is, when `N = M − 1` is odd.
Odd levels are reduced to even ones by propagating the shift upwards one level, the first stripping
step of the propagated chain being supplied by the pinned top coefficient at the original level.  So
no level above three carries a normalizing shift once the levels below are known to carry none.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

omit [CharZero C] in
theorem invTower_zero : invTower (C := C) 0 = (jetRatio 2 : JetField C Unit) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hδ : deltaIter 1 ((JetField.jet ((), 1) : JetField C Unit)⁻¹)
      = -((JetField.jet ((), 1) : JetField C Unit))⁻¹ ^ 2 * (JetField.jet ((), 2)) := by
    rw [deltaIter_succ]
    have h := (JetField.jetDerivation (C := C) (ι := Unit)).leibniz_inv
      (JetField.jet ((), 1) : JetField C Unit)
    rw [JetField.jetDerivation_jet] at h
    simp only [smul_eq_mul] at h
    exact h
  rw [invTower, hδ, jetRatio, pow_zero, div_one]
  field_simp

/-- **No normalizing shift above level three.** -/
theorem no_zshift (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {M : ℕ} (hM : 4 ≤ M)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, M - 1 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {w : JetField C Unit} (hwz : IsWeightZero w)
    (hord : ∀ j : ℕ, M - 1 < j → JetField.pd ((), j) w = 0)
    (heq : substitutionDeriv R ^ M * jetSubstitution R hR w
      = substitutionDeriv R * w - substitutionShiftRatio R M) : False := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hρ0 : substitutionDeriv R ≠ 0 := hR
  rcases Nat.even_or_odd M with hpar | hpar
  · -- even level: the chain runs directly
    obtain ⟨T, hT⟩ : ∃ T, M = 2 * T + 2 := by
      obtain ⟨k, hk⟩ := hpar
      exact ⟨k - 1, by omega⟩
    have hT1 : 1 ≤ T := by omega
    have hNM : M - 1 = 2 * T + 1 := by omega
    have hfix' : ∀ g : JetField C Unit,
        (∀ j : ℕ, 2 * T + 1 < j → JetField.pd ((), j) g = 0) →
          jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e := by
      intro g hg hgf
      exact hfix g (fun j hj => hg j (by omega)) hgf
    have hord' : ∀ j : ℕ, 2 * T + 1 < j → JetField.pd ((), j) w = 0 :=
      fun j hj => hord j (by omega)
    have heq' : substitutionDeriv R ^ (2 * T + 1 + 1) * jetSubstitution R hR w
        = substitutionDeriv R * w - substitutionShiftRatio R (2 * T + 1 + 1) := by
      rw [show 2 * T + 1 + 1 = M from by omega]
      exact heq
    obtain ⟨-, hstripord, -⟩ := zshift_strip R hR (N := 2 * T + 1) (by omega) hfix' hwz hord' heq'
    refine no_zshift_of_odd R hR hT1 (Kf := 2 * T + 1) (by omega) (by omega) hfix' hwz heq' ?_
    intro j hj
    have hchain : chain (C := C) (2 * T + 1) w 1
        = w + ((2 * T + 1 + 1 : ℕ) : JetField C Unit) * (jetRatio 2 : JetField C Unit)
          * (jetRatio (2 * T + 1) : JetField C Unit) := by
      rw [chain, Finset.sum_range_one, chainTerm, invTower_zero, Nat.choose_one_right,
        Nat.sub_zero]
    rw [hchain]
    exact hstripord j (by omega)
  · -- odd level: propagate one level up
    obtain ⟨T, hT⟩ : ∃ T, M = 2 * T + 1 := by
      obtain ⟨k, hk⟩ := hpar
      exact ⟨k, by omega⟩
    have hT2 : 2 ≤ T := by omega
    have hfix' : ∀ g : JetField C Unit,
        (∀ j : ℕ, 2 * T < j → JetField.pd ((), j) g = 0) →
          jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e := by
      intro g hg hgf
      exact hfix g (fun j hj => hg j (by omega)) hgf
    have hordw : ∀ j : ℕ, M - 1 < j → JetField.pd ((), j) w = 0 := hord
    -- the pinned top coefficient at the original level
    have htop := topDescent_of_zshift R hR (N := M - 1) (by omega) (by
        intro g hg hgf
        exact hfix g hg hgf) hwz hordw (by
        rw [show M - 1 + 1 = M from by omega]
        exact heq)
    obtain ⟨htop1, -⟩ := htop
    -- propagate
    obtain ⟨hwz', hord', heq'⟩ := zshift_succ R hR (m := M - 1) (by omega) hwz hordw (by
      rw [show M - 1 + 1 = M from by omega]
      exact heq)
    set w' : JetField C Unit := jetNabla w
      + ((M - 1 : ℕ) : JetField C Unit) * (jetRatio 2 : JetField C Unit) * w
      - (jetRatio 2 : JetField C Unit) * (jetRatio (M - 1 + 1) : JetField C Unit) with hw'def
    -- the first strip of the propagated chain
    have hpdM : JetField.pd ((), M) w' = -(((M + 1 : ℕ) : JetField C Unit)
        * (jetRatio 2 : JetField C Unit)) / (JetField.jet ((), 1) : JetField C Unit) ^ M := by
      have hz2 : JetField.pd ((), M) (jetRatio 2 : JetField C Unit) = 0 :=
        pd_jetRatio_of_ne (by omega) (by omega)
      have hwM : JetField.pd ((), M) w = 0 := hordw M (by omega)
      have hnab : JetField.pd ((), M) (jetNabla w)
          = JetField.pd ((), M - 1) w / (JetField.jet ((), 1) : JetField C Unit) := by
        have hinv : JetField.pd ((), M) ((JetField.jet ((), 1) : JetField C Unit)⁻¹) = 0 :=
          pd_inv_eq_zero (JetField.pd_jet_of_ne (by
            simp only [ne_eq, Prod.mk.injEq, true_and]; omega))
        have hl := (JetField.pd ((), M) :
          Derivation C (JetField C Unit) (JetField C Unit)).leibniz
            (JetField.jetDerivation w) ((JetField.jet ((), 1) : JetField C Unit)⁻¹)
        simp only [smul_eq_mul] at hl
        obtain ⟨i, hi⟩ : ∃ i, M = i + 1 := ⟨M - 1, by omega⟩
        rw [jetNabla_apply, div_eq_mul_inv, hl, hinv, mul_zero, zero_add]
        rw [hi, ← JetField.deriv_eq, JetField.pd_deriv_succ, JetField.deriv_eq]
        rw [show i + 1 - 1 = i from by omega] at *
        rw [hordw (i + 1) (by omega), map_zero, zero_add, div_eq_mul_inv]
        ring
      have hzM : JetField.pd ((), M) (jetRatio (M - 1 + 1) : JetField C Unit)
          = 1 / (JetField.jet ((), 1) : JetField C Unit) ^ M := by
        rw [show M - 1 + 1 = M from by omega]
        exact pd_jetRatio_self (by omega)
      have hpdw : JetField.pd ((), M - 1) w
          = -(((M : ℕ) : JetField C Unit) * (jetRatio 2 : JetField C Unit))
            / (JetField.jet ((), 1) : JetField C Unit) ^ (M - 1) := by
        rw [eq_div_iff (pow_ne_zero _ hy1)]
        rw [topDescent] at htop1
        rw [show ((M - 1 + 1 : ℕ) : C) = ((M : ℕ) : C) from by
          congr 1
          omega] at htop1
        rw [map_natCast] at htop1
        linear_combination htop1
      have hl2 := (JetField.pd ((), M) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (((M - 1 : ℕ) : JetField C Unit) * (jetRatio 2 : JetField C Unit)) w
      have hl3 := (JetField.pd ((), M) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (jetRatio 2 : JetField C Unit) (jetRatio (M - 1 + 1) : JetField C Unit)
      simp only [smul_eq_mul] at hl2 hl3
      have hcz : JetField.pd ((), M) (((M - 1 : ℕ) : JetField C Unit)
          * (jetRatio 2 : JetField C Unit)) = 0 :=
        pd_mul_eq_zero (pd_natCast_eq_zero _ _) hz2
      rw [hw'def, map_sub, map_add, hnab, hl2, hl3, hwM, hz2, hcz, hpdw, hzM]
      have hsplit : (JetField.jet ((), 1) : JetField C Unit) ^ M
          = (JetField.jet ((), 1) : JetField C Unit) ^ (M - 1)
            * (JetField.jet ((), 1) : JetField C Unit) := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hsplit]
      field_simp
      push_cast
      ring
    have hbase : ∀ j : ℕ, 2 * T + 1 - 1 < j →
        JetField.pd ((), j) (chain (C := C) (2 * T + 1) w' 1) = 0 := by
      intro j hj
      have hchain : chain (C := C) (2 * T + 1) w' 1
          = w' + ((2 * T + 1 + 1 : ℕ) : JetField C Unit) * (jetRatio 2 : JetField C Unit)
            * (jetRatio (2 * T + 1) : JetField C Unit) := by
        rw [chain, Finset.sum_range_one, chainTerm, invTower_zero, Nat.choose_one_right,
          Nat.sub_zero]
      rw [hchain, map_add]
      rcases (by omega : j = M ∨ M < j) with heqj | hlt
      · rw [heqj]
        have hzj : JetField.pd ((), M) (jetRatio (2 * T + 1) : JetField C Unit)
            = 1 / (JetField.jet ((), 1) : JetField C Unit) ^ M := by
          rw [show (2 * T + 1 : ℕ) = M from by omega]
          exact pd_jetRatio_self (by omega)
        have hl := (JetField.pd ((), M) :
          Derivation C (JetField C Unit) (JetField C Unit)).leibniz
            (((2 * T + 1 + 1 : ℕ) : JetField C Unit) * (jetRatio 2 : JetField C Unit))
            (jetRatio (2 * T + 1) : JetField C Unit)
        simp only [smul_eq_mul] at hl
        rw [hl, hzj, pd_mul_eq_zero (pd_natCast_eq_zero _ _)
          (pd_jetRatio_of_ne (by omega) (by omega)), mul_zero, add_zero, hpdM,
          show (2 * T + 1 + 1 : ℕ) = M + 1 from by omega]
        field_simp
        ring
      · rw [hord' j (by omega), pd_mul_eq_zero (pd_mul_eq_zero (pd_natCast_eq_zero _ _)
          (pd_jetRatio_of_ne (by omega) (by omega)))
          (pd_jetRatio_of_ne (by omega) (by omega)), add_zero]
    refine no_zshift_of_odd R hR (T := T) (by omega) (Kf := 2 * T) (by omega) (by omega)
      hfix' hwz' ?_ hbase
    rw [show 2 * T + 1 + 1 = M - 1 + 1 + 1 from by omega]
    exact heq'

/-! ## The tail is trivial -/

theorem not_hasNormalizingShift_of_fix (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {M : ℕ}
    (hM : 4 ≤ M)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, M - 1 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    (h : HasNormalizingShift R hR (show 1 ≤ M by omega)) : False := by
  obtain ⟨w, hwz, hord, heq⟩ := exists_isWeightZero_zshift R hR (show 1 < M by omega) hfix h
  exact no_zshift R hR hM hfix hwz hord heq

theorem not_hasNormalizingShift_all (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (hbase : ∀ g : JetField C Unit, (∀ j : ℕ, 1 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    (h2 : ¬ HasNormalizingShift R hR (show (1 : ℕ) ≤ 2 by omega))
    (h3 : ¬ HasNormalizingShift R hR (show (1 : ℕ) ≤ 3 by omega)) :
    ∀ M : ℕ, ∀ hM : 2 ≤ M, ¬ HasNormalizingShift R hR (le_trans one_le_two hM) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
      intro hM h
      rcases (by omega : M = 2 ∨ M = 3 ∨ 4 ≤ M) with hM2 | hM3 | h4
      · subst hM2
        exact h2 h
      · subst hM3
        exact h3 h
      · refine not_hasNormalizingShift_of_fix R hR h4 ?_ h
        refine fixed_isConst_of_order_le R hR hbase (M - 1) ?_
        intro M' hM' hle
        exact ih M' (by omega) hM'

/-- **The orbifold tail is trivial.**  Once the levels one, two and three are excluded, every
`Φ_R`-fixed element of the free jet field is constant. -/
theorem fixed_isConst (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (hbase : ∀ g : JetField C Unit, (∀ j : ℕ, 1 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    (h2 : ¬ HasNormalizingShift R hR (show (1 : ℕ) ≤ 2 by omega))
    (h3 : ¬ HasNormalizingShift R hR (show (1 : ℕ) ≤ 3 by omega))
    (K : ℕ) {g : JetField C Unit}
    (hg : ∀ j : ℕ, K < j → JetField.pd ((), j) g = 0)
    (hgfix : jetSubstitution R hR g = g) :
    ∃ e : C, g = algebraMap C (JetField C Unit) e :=
  fixed_isConst_of_order_le R hR hbase K
    (fun M hM _ => not_hasNormalizingShift_all R hR hbase h2 h3 M hM) g hg hgfix

end

end GaloisForLFunctions.HTGeometry

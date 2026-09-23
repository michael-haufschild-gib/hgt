import GaloisForLFunctions.HTGeometry.JetShiftSubdiagonal

/-!
# The inverse tower

The iterated derivatives of `1/y₁` carry the whole level-free part of the descent.  Writing `δ` for
the jet derivation, the substitution acts on them by

`Φ(δ^k(1/y₁)) = δ^k(1/(R'(y₀)·y₁))`,

because `Φ` is a differential endomorphism and `Φ(y₁) = R'(y₀)·y₁`.  The normalised elements

`V_t := −δ^{t+1}(1/y₁)/y₁^t`

therefore satisfy `R'^{t+2}·Φ(V_t) = R'·V_t + Ê_t` with an explicit inhomogeneous term, are torus
invariant, and have jet order exactly `t + 2` with top descent `y₁^{t+2}·∂_{t+2}V_t = 1`: the
leading coefficient never degenerates.  The universal tower of the shift is the same construction
applied to the derivative factor, `T_r = δ^r(R'(y₀))/y₁^r`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- Iterated jet derivation. -/
def deltaIter : ℕ → JetField C Unit → JetField C Unit
  | 0, v => v
  | (k + 1), v => JetField.jetDerivation (deltaIter k v)

omit [CharZero C] in
theorem deltaIter_succ (k : ℕ) (v : JetField C Unit) :
    deltaIter (k + 1) v = JetField.jetDerivation (deltaIter k v) := rfl

theorem jetSubstitution_deltaIter (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) (k : ℕ)
    (v : JetField C Unit) :
    jetSubstitution R hR (deltaIter k v) = deltaIter k (jetSubstitution R hR v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [deltaIter_succ, deltaIter_succ, jetSubstitution_jetDerivation, ih]

/-! ## Order and top partial of an iterated derivative -/

omit [CharZero C] in
theorem pd_deltaIter_of_order_one {v : JetField C Unit}
    (hv : ∀ j : ℕ, 1 < j → JetField.pd ((), j) v = 0) (k : ℕ) :
    (∀ j : ℕ, k + 1 < j → JetField.pd ((), j) (deltaIter k v) = 0)
      ∧ JetField.pd ((), k + 1) (deltaIter k v) = JetField.pd ((), 1) v := by
  induction k with
  | zero => exact ⟨hv, rfl⟩
  | succ k ih =>
      obtain ⟨ihord, ihtop⟩ := ih
      constructor
      · intro j hj
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        rw [deltaIter_succ, ← JetField.deriv_eq, JetField.pd_deriv_succ, JetField.deriv_eq,
          ihord (i + 1) (by omega), ihord i (by omega), map_zero, add_zero]
      · rw [deltaIter_succ, ← JetField.deriv_eq, JetField.pd_deriv_succ, JetField.deriv_eq,
          ihord (k + 2) (by omega), map_zero, zero_add, ihtop]

/-! ## The shift tower as an iterated derivative -/

theorem shiftTower_mul_pow (R : RatFunc C) {r : ℕ} (hr : 1 ≤ r) :
    shiftTower R r * (JetField.jet ((), 1) : JetField C Unit) ^ r
      = deltaIter r (substitutionDeriv R) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  induction r, hr using Nat.le_induction with
  | base =>
      rw [pow_one, deltaIter_succ,
        show shiftTower R 1 = JetField.pd ((), 0) (substitutionDeriv R) from rfl]
      have hd : JetField.jetDerivation (deltaIter 0 (substitutionDeriv R))
          = (JetField.jet ((), 1) : JetField C Unit)
            * JetField.pd ((), 0) (substitutionDeriv R) :=
        jetDerivation_of_order_zero (fun k hk => pd_substitutionDeriv_eq_zero R hk)
      rw [hd]
      ring
  | succ r hr ih =>
      obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
      have hpow : JetField.jetDerivation ((JetField.jet ((), 1) : JetField C Unit) ^ (q + 1))
          = ((q + 1 : ℕ) : JetField C Unit)
            * (JetField.jet ((), 1) : JetField C Unit) ^ q
            * (JetField.jet ((), 2) : JetField C Unit) := by
        have h := (JetField.jetDerivation (C := C) (ι := Unit)).leibniz_pow
          (JetField.jet ((), 1) : JetField C Unit) (q + 1)
        simp only [smul_eq_mul, JetField.jetDerivation_jet, Nat.add_sub_cancel] at h
        rw [h]
        push_cast
        ring
      have hleib := (JetField.jetDerivation (C := C) (ι := Unit)).leibniz
        (shiftTower R (q + 1)) ((JetField.jet ((), 1) : JetField C Unit) ^ (q + 1))
      simp only [smul_eq_mul] at hleib
      rw [ih, hpow] at hleib
      have hnab : JetField.jetDerivation (shiftTower R (q + 1))
          = (JetField.jet ((), 1) : JetField C Unit) * jetNabla (shiftTower R (q + 1)) := by
        rw [jetNabla_apply]
        field_simp
      rw [hnab] at hleib
      have hrec : shiftTower R (q + 1 + 1)
          = jetNabla (shiftTower R (q + 1))
            + ((q + 1 : ℕ) : JetField C Unit) * (jetRatio 2 : JetField C Unit)
              * shiftTower R (q + 1) := shiftTower_add_two R q
      have hz2 : (jetRatio 2 : JetField C Unit)
          * (JetField.jet ((), 1) : JetField C Unit) ^ (2 : ℕ)
          = (JetField.jet ((), 2) : JetField C Unit) := by
        rw [jetRatio]
        field_simp
      rw [deltaIter_succ, hleib, hrec]
      have hsplit : (JetField.jet ((), 1) : JetField C Unit) ^ (q + 1 + 1)
          = (JetField.jet ((), 1) : JetField C Unit) ^ q
            * (JetField.jet ((), 1) : JetField C Unit) ^ (2 : ℕ) := by
        rw [← pow_add]
      rw [hsplit]
      linear_combination (((q + 1 : ℕ) : JetField C Unit)
        * (JetField.jet ((), 1) : JetField C Unit) ^ q
        * shiftTower R (q + 1)) * hz2

/-! ## The inverse tower -/

/-- The level-free tower of the descent. -/
def invTower (t : ℕ) : JetField C Unit :=
  -(deltaIter (t + 1) ((JetField.jet ((), 1) : JetField C Unit)⁻¹))
    / (JetField.jet ((), 1) : JetField C Unit) ^ t

/-- The inhomogeneous term of the level-free tower. -/
def invTowerDefect (R : RatFunc C) (t : ℕ) : JetField C Unit :=
  (substitutionDeriv R * deltaIter (t + 1) ((JetField.jet ((), 1) : JetField C Unit)⁻¹)
      - substitutionDeriv R ^ (2 : ℕ)
        * deltaIter (t + 1)
          (((JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R)⁻¹))
    / (JetField.jet ((), 1) : JetField C Unit) ^ t

/-- **The level-free tower solves the level-free relation.** -/
theorem jetSubstitution_invTower (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) (t : ℕ) :
    substitutionDeriv R ^ (t + 2) * jetSubstitution R hR (invTower (C := C) t)
      = substitutionDeriv R * invTower (C := C) t + invTowerDefect R t := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hρ0 : substitutionDeriv R ≠ 0 := hR
  have hΦ1 : jetSubstitution R hR (JetField.jet ((), 1) : JetField C Unit)
      = (JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R := by
    rw [jetSubstitution_jet, substitutionJet_one]
  have hΦinv : jetSubstitution R hR ((JetField.jet ((), 1) : JetField C Unit)⁻¹)
      = ((JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R)⁻¹ := by
    rw [map_inv₀, hΦ1]
  rw [invTower, invTowerDefect, map_div₀, map_neg, map_pow, hΦ1,
    jetSubstitution_deltaIter, hΦinv, mul_pow]
  field_simp
  ring

/-! ## Order and leading coefficient of the inverse tower -/

omit [CharZero C] in
theorem pd_jet_one_inv :
    JetField.pd ((), 1) ((JetField.jet ((), 1) : JetField C Unit)⁻¹)
      = -((JetField.jet ((), 1) : JetField C Unit))⁻¹ ^ (2 : ℕ) := by
  have h := (JetField.pd ((), 1) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz_inv
      (JetField.jet ((), 1) : JetField C Unit)
  rw [h, JetField.pd_jet_self]
  simp

omit [CharZero C] in
theorem pd_jet_one_inv_of_ne {j : ℕ} (hj : j ≠ 1) :
    JetField.pd ((), j) ((JetField.jet ((), 1) : JetField C Unit)⁻¹) = 0 :=
  pd_inv_eq_zero (JetField.pd_jet_of_ne (by
    simp only [ne_eq, Prod.mk.injEq, true_and]; exact hj))

omit [CharZero C] in
theorem pd_invTower_top (t : ℕ) :
    JetField.pd ((), t + 2) (invTower (C := C) t)
      = ((JetField.jet ((), 1) : JetField C Unit))⁻¹ ^ (2 : ℕ)
        / (JetField.jet ((), 1) : JetField C Unit) ^ t := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  obtain ⟨hord, htop⟩ := pd_deltaIter_of_order_one (C := C)
    (v := ((JetField.jet ((), 1) : JetField C Unit))⁻¹)
    (fun j hj => pd_jet_one_inv_of_ne (by omega)) (t + 1)
  have htop' : JetField.pd ((), t + 2)
      (deltaIter (t + 1) ((JetField.jet ((), 1) : JetField C Unit)⁻¹))
      = -((JetField.jet ((), 1) : JetField C Unit))⁻¹ ^ (2 : ℕ) := by
    rw [pd_jet_one_inv] at htop
    exact htop
  have hpowpd : JetField.pd ((), t + 2)
      ((JetField.jet ((), 1) : JetField C Unit) ^ t) = 0 :=
    pd_pow_eq_zero (JetField.pd_jet_of_ne (by
      simp only [ne_eq, Prod.mk.injEq, true_and]; omega)) t
  have hinvpd : JetField.pd ((), t + 2)
      (((JetField.jet ((), 1) : JetField C Unit) ^ t)⁻¹) = 0 :=
    pd_inv_eq_zero hpowpd
  have hleib := (JetField.pd ((), t + 2) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (-(deltaIter (t + 1) ((JetField.jet ((), 1) : JetField C Unit)⁻¹)))
      (((JetField.jet ((), 1) : JetField C Unit) ^ t)⁻¹)
  simp only [smul_eq_mul] at hleib
  rw [invTower, div_eq_mul_inv, hleib, hinvpd, mul_zero, zero_add, map_neg, htop']
  field_simp

omit [CharZero C] in
theorem pd_invTower_of_gt {t j : ℕ} (hj : t + 2 < j) :
    JetField.pd ((), j) (invTower (C := C) t) = 0 := by
  obtain ⟨hord, -⟩ := pd_deltaIter_of_order_one (C := C)
    (v := ((JetField.jet ((), 1) : JetField C Unit))⁻¹)
    (fun i hi => pd_jet_one_inv_of_ne (by omega)) (t + 1)
  have hpowpd : JetField.pd ((), j) ((JetField.jet ((), 1) : JetField C Unit) ^ t) = 0 :=
    pd_pow_eq_zero (JetField.pd_jet_of_ne (by
      simp only [ne_eq, Prod.mk.injEq, true_and]; omega)) t
  have hleib := (JetField.pd ((), j) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (-(deltaIter (t + 1) ((JetField.jet ((), 1) : JetField C Unit)⁻¹)))
      (((JetField.jet ((), 1) : JetField C Unit) ^ t)⁻¹)
  simp only [smul_eq_mul] at hleib
  rw [invTower, div_eq_mul_inv, hleib, pd_inv_eq_zero hpowpd, mul_zero, zero_add, map_neg,
    hord j (by omega), neg_zero, mul_zero]

omit [CharZero C] in
/-- **The leading coefficient of the level-free tower is one.** -/
theorem topDescent_invTower (t : ℕ) :
    topDescent (t + 2) (invTower (C := C) t) = 1 := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  rw [topDescent, pd_invTower_top]
  field_simp
  ring

/-! ## Torus invariance and the order of the defect -/

omit [CharZero C] in
theorem jetDerivation_algebraMap_mul (c : C) (u : JetField C Unit) :
    JetField.jetDerivation (algebraMap C (JetField C Unit) c * u)
      = algebraMap C (JetField C Unit) c * JetField.jetDerivation u := by
  have h := (JetField.jetDerivation (C := C) (ι := Unit)).leibniz
    (algebraMap C (JetField C Unit) c) u
  simp only [smul_eq_mul] at h
  rw [h, Derivation.map_algebraMap, mul_zero, add_zero]

omit [CharZero C] in
theorem weightScale_deltaIter {lam : C} (h : lam ≠ 0) (k : ℕ) (v : JetField C Unit) :
    weightScale h (deltaIter k v)
      = algebraMap C (JetField C Unit) lam ^ k * deltaIter k (weightScale h v) := by
  induction k with
  | zero => simp [deltaIter]
  | succ k ih =>
      have hstep : algebraMap C (JetField C Unit) lam
          * algebraMap C (JetField C Unit) (lam ^ k)
          = algebraMap C (JetField C Unit) (lam ^ (k + 1)) := by
        rw [← map_mul, ← pow_succ']
      rw [deltaIter_succ, weightScale_jetDerivation, ih, ← map_pow,
        jetDerivation_algebraMap_mul, ← deltaIter_succ, ← mul_assoc, hstep, ← map_pow]

theorem isWeightZero_invTower (t : ℕ) : IsWeightZero (invTower (C := C) t) := by
  have h2 : (2 : C) ≠ 0 := two_ne_zero
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hA : algebraMap C (JetField C Unit) (2 : C) ≠ 0 := by
    intro hh
    exact absurd ((algebraMap C (JetField C Unit)).injective (by rw [hh, map_zero])) h2
  have hinv : weightScale h2 ((JetField.jet ((), 1) : JetField C Unit)⁻¹)
      = (algebraMap C (JetField C Unit) (2 : C))⁻¹
        * ((JetField.jet ((), 1) : JetField C Unit))⁻¹ := by
    rw [map_inv₀, weightScale_jet, pow_one, mul_inv]
  show weightScale h2 (invTower (C := C) t) = invTower (C := C) t
  rw [invTower, map_div₀, map_neg, map_pow, weightScale_jet, pow_one,
    weightScale_deltaIter, hinv]
  have hcm : deltaIter (t + 1) ((algebraMap C (JetField C Unit) (2 : C))⁻¹
        * ((JetField.jet ((), 1) : JetField C Unit))⁻¹)
      = (algebraMap C (JetField C Unit) (2 : C))⁻¹
        * deltaIter (t + 1) (((JetField.jet ((), 1) : JetField C Unit))⁻¹) := by
    have hgen : ∀ k : ℕ, ∀ u : JetField C Unit,
        deltaIter k ((algebraMap C (JetField C Unit) (2 : C))⁻¹ * u)
          = (algebraMap C (JetField C Unit) (2 : C))⁻¹ * deltaIter k u := by
      intro k
      induction k with
      | zero => intro u; rfl
      | succ k ih =>
          intro u
          rw [deltaIter_succ, ih, ← map_inv₀, jetDerivation_algebraMap_mul, map_inv₀,
            ← deltaIter_succ]
    exact hgen (t + 1) _
  rw [hcm, mul_pow]
  field_simp
  ring

theorem pd_invTowerDefect_of_gt (R : RatFunc C) {t j : ℕ} (hj : t + 1 < j) :
    JetField.pd ((), j) (invTowerDefect R t) = 0 := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hord1 : ∀ i : ℕ, 1 < i →
      JetField.pd ((), i) ((JetField.jet ((), 1) : JetField C Unit)⁻¹) = 0 :=
    fun i hi => pd_jet_one_inv_of_ne (by omega)
  have hord2 : ∀ i : ℕ, 1 < i →
      JetField.pd ((), i)
        (((JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R)⁻¹) = 0 := by
    intro i hi
    refine pd_inv_eq_zero (pd_mul_eq_zero ?_ (pd_substitutionDeriv_eq_zero R (by omega)))
    exact JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)
  obtain ⟨hoA, htA⟩ := pd_deltaIter_of_order_one hord1 (t + 1)
  obtain ⟨hoB, htB⟩ := pd_deltaIter_of_order_one hord2 (t + 1)
  have hρpd : JetField.pd ((), j) (substitutionDeriv R) = 0 :=
    pd_substitutionDeriv_eq_zero R (by omega)
  have hpowpd : JetField.pd ((), j)
      (((JetField.jet ((), 1) : JetField C Unit) ^ t)⁻¹) = 0 :=
    pd_inv_eq_zero (pd_pow_eq_zero (JetField.pd_jet_of_ne (by
      simp only [ne_eq, Prod.mk.injEq, true_and]; omega)) t)
  have hnum : JetField.pd ((), j)
      (substitutionDeriv R * deltaIter (t + 1) ((JetField.jet ((), 1) : JetField C Unit)⁻¹)
        - substitutionDeriv R ^ (2 : ℕ)
          * deltaIter (t + 1)
            (((JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R)⁻¹)) = 0 := by
    have hl1 := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz
        (substitutionDeriv R) (deltaIter (t + 1) ((JetField.jet ((), 1) : JetField C Unit)⁻¹))
    have hl2 := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz
        (substitutionDeriv R ^ (2 : ℕ))
        (deltaIter (t + 1) (((JetField.jet ((), 1) : JetField C Unit)
          * substitutionDeriv R)⁻¹))
    simp only [smul_eq_mul] at hl1 hl2
    rw [map_sub, hl1, hl2, hρpd, pd_pow_eq_zero hρpd 2, mul_zero, mul_zero, add_zero, add_zero]
    rcases (by omega : j = t + 2 ∨ t + 2 < j) with heq | hgt
    · subst heq
      have hA : JetField.pd ((), t + 2)
          (deltaIter (t + 1) ((JetField.jet ((), 1) : JetField C Unit)⁻¹))
          = -((JetField.jet ((), 1) : JetField C Unit))⁻¹ ^ (2 : ℕ) := by
        rw [pd_jet_one_inv] at htA
        exact htA
      have hB : JetField.pd ((), t + 2)
          (deltaIter (t + 1) (((JetField.jet ((), 1) : JetField C Unit)
            * substitutionDeriv R)⁻¹))
          = -(((JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R)⁻¹ ^ (2 : ℕ))
            * substitutionDeriv R := by
        have hb := (JetField.pd ((), 1) :
          Derivation C (JetField C Unit) (JetField C Unit)).leibniz_inv
            ((JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R)
        have hb2 := (JetField.pd ((), 1) :
          Derivation C (JetField C Unit) (JetField C Unit)).leibniz
            (JetField.jet ((), 1) : JetField C Unit) (substitutionDeriv R)
        simp only [smul_eq_mul] at hb2
        rw [hb2, JetField.pd_jet_self, pd_substitutionDeriv_eq_zero R (by omega), mul_zero,
          zero_add, mul_one] at hb
        rw [hb] at htB
        simp only [smul_eq_mul] at htB
        exact htB
      rw [hA, hB]
      by_cases hρ0 : substitutionDeriv R = 0
      · rw [hρ0]
        ring
      · field_simp
        ring
    · rw [hoA j (by omega), hoB j (by omega), mul_zero, mul_zero, sub_zero]
  have hleib := (JetField.pd ((), j) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (substitutionDeriv R * deltaIter (t + 1) ((JetField.jet ((), 1) : JetField C Unit)⁻¹)
        - substitutionDeriv R ^ (2 : ℕ)
          * deltaIter (t + 1)
            (((JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R)⁻¹))
      (((JetField.jet ((), 1) : JetField C Unit) ^ t)⁻¹)
  simp only [smul_eq_mul] at hleib
  rw [invTowerDefect, div_eq_mul_inv, hleib, hnum, hpowpd, mul_zero, mul_zero, add_zero]

/-! ## The iterated Leibniz rule -/

omit [CharZero C] in
theorem deltaIter_leibniz (n : ℕ) (a b : JetField C Unit) :
    deltaIter n (a * b)
      = ∑ i ∈ Finset.range (n + 1), (((n.choose i : ℕ)) : JetField C Unit)
          * deltaIter i a * deltaIter (n - i) b := by
  induction n with
  | zero => simp [deltaIter]
  | succ n ih =>
      have hstep : ∀ i ∈ Finset.range (n + 1),
          JetField.jetDerivation ((((n.choose i : ℕ)) : JetField C Unit)
              * deltaIter i a * deltaIter (n - i) b)
            = (((n.choose i : ℕ)) : JetField C Unit)
                * deltaIter (i + 1) a * deltaIter (n - i) b
              + (((n.choose i : ℕ)) : JetField C Unit)
                * deltaIter i a * deltaIter (n - i + 1) b := by
        intro i _
        have hl1 := (JetField.jetDerivation (C := C) (ι := Unit)).leibniz
          ((((n.choose i : ℕ)) : JetField C Unit) * deltaIter i a) (deltaIter (n - i) b)
        have hl2 := (JetField.jetDerivation (C := C) (ι := Unit)).leibniz
          ((((n.choose i : ℕ)) : JetField C Unit)) (deltaIter i a)
        simp only [smul_eq_mul] at hl1 hl2
        have hc : JetField.jetDerivation ((((n.choose i : ℕ)) : JetField C Unit)) = 0 := by
          rw [show ((((n.choose i : ℕ)) : JetField C Unit))
              = algebraMap C (JetField C Unit) (((n.choose i : ℕ)) : C) from
            (map_natCast (algebraMap C (JetField C Unit)) (n.choose i)).symm,
            Derivation.map_algebraMap]
        rw [hl2, hc, mul_zero, add_zero] at hl1
        rw [hl1, deltaIter_succ, deltaIter_succ]
        ring
      rw [deltaIter_succ, ih, map_sum, Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
      -- the target, split off its bottom term
      rw [Finset.sum_range_succ' (fun i => (((((n + 1).choose i : ℕ))) : JetField C Unit)
        * deltaIter i a * deltaIter (n + 1 - i) b) (n + 1)]
      have hpascal : ∀ i ∈ Finset.range (n + 1),
          (((((n + 1).choose (i + 1) : ℕ))) : JetField C Unit)
              * deltaIter (i + 1) a * deltaIter (n + 1 - (i + 1)) b
            = (((n.choose i : ℕ)) : JetField C Unit)
                * deltaIter (i + 1) a * deltaIter (n - i) b
              + (((n.choose (i + 1) : ℕ)) : JetField C Unit)
                * deltaIter (i + 1) a * deltaIter (n - i) b := by
        intro i _
        rw [show n + 1 - (i + 1) = n - i from by omega, Nat.choose_succ_succ]
        push_cast
        ring
      rw [Finset.sum_congr rfl hpascal, Finset.sum_add_distrib]
      have hshift : ∑ i ∈ Finset.range (n + 1), (((n.choose (i + 1) : ℕ)) : JetField C Unit)
              * deltaIter (i + 1) a * deltaIter (n - i) b
            + (((((n + 1).choose 0 : ℕ))) : JetField C Unit)
              * deltaIter 0 a * deltaIter (n + 1 - 0) b
          = ∑ i ∈ Finset.range (n + 1), (((n.choose i : ℕ)) : JetField C Unit)
              * deltaIter i a * deltaIter (n - i + 1) b := by
        rw [Finset.sum_range_succ' (fun i => (((n.choose i : ℕ)) : JetField C Unit)
          * deltaIter i a * deltaIter (n - i + 1) b) n]
        rw [Finset.sum_range_succ (fun i => (((n.choose (i + 1) : ℕ)) : JetField C Unit)
          * deltaIter (i + 1) a * deltaIter (n - i) b) n]
        rw [Nat.choose_succ_self]
        have hcongr : ∀ i ∈ Finset.range n,
            (((n.choose (i + 1) : ℕ)) : JetField C Unit)
                * deltaIter (i + 1) a * deltaIter (n - i) b
              = (((n.choose (i + 1) : ℕ)) : JetField C Unit)
                * deltaIter (i + 1) a * deltaIter (n - (i + 1) + 1) b := by
          intro i hi
          rw [show n - (i + 1) + 1 = n - i from by
            have := Finset.mem_range.mp hi
            omega]
        rw [Finset.sum_congr rfl hcongr]
        simp
      rw [← hshift]
      ring

/-- **The Leibniz split of the inverse tower.**  Writing `1/y₁ = R'(y₀)·(1/(y₁·R'(y₀)))` and
expanding by the iterated Leibniz rule separates the two extreme terms from a middle sum whose
entries pair an iterated derivative of the derivative factor with one of the twisted inverse. -/
theorem deltaIter_inv_split (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) (t : ℕ) :
    deltaIter (t + 1) ((JetField.jet ((), 1) : JetField C Unit)⁻¹)
      = substitutionDeriv R
          * deltaIter (t + 1) (((JetField.jet ((), 1) : JetField C Unit)
            * substitutionDeriv R)⁻¹)
        + (∑ j ∈ Finset.range t, ((((t + 1).choose (j + 1) : ℕ)) : JetField C Unit)
            * deltaIter (j + 1) (substitutionDeriv R)
            * deltaIter (t - j) (((JetField.jet ((), 1) : JetField C Unit)
              * substitutionDeriv R)⁻¹))
        + deltaIter (t + 1) (substitutionDeriv R)
          * ((JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R)⁻¹ := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hprod : substitutionDeriv R
      * ((JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R)⁻¹
      = ((JetField.jet ((), 1) : JetField C Unit))⁻¹ := by
    field_simp
  rw [← hprod, deltaIter_leibniz]
  rw [Finset.sum_range_succ' (fun i => ((((t + 1).choose i : ℕ)) : JetField C Unit)
    * deltaIter i (substitutionDeriv R)
    * deltaIter (t + 1 - i) (((JetField.jet ((), 1) : JetField C Unit)
      * substitutionDeriv R)⁻¹)) (t + 1)]
  rw [Finset.sum_range_succ (fun j => ((((t + 1).choose (j + 1) : ℕ)) : JetField C Unit)
    * deltaIter (j + 1) (substitutionDeriv R)
    * deltaIter (t + 1 - (j + 1)) (((JetField.jet ((), 1) : JetField C Unit)
      * substitutionDeriv R)⁻¹)) t]
  have hcongr : ∀ j ∈ Finset.range t,
      ((((t + 1).choose (j + 1) : ℕ)) : JetField C Unit)
          * deltaIter (j + 1) (substitutionDeriv R)
          * deltaIter (t + 1 - (j + 1)) (((JetField.jet ((), 1) : JetField C Unit)
            * substitutionDeriv R)⁻¹)
        = ((((t + 1).choose (j + 1) : ℕ)) : JetField C Unit)
          * deltaIter (j + 1) (substitutionDeriv R)
          * deltaIter (t - j) (((JetField.jet ((), 1) : JetField C Unit)
            * substitutionDeriv R)⁻¹) := by
    intro j _
    rw [show t + 1 - (j + 1) = t - j from by omega]
  rw [Finset.sum_congr rfl hcongr]
  rw [show t + 1 - (t + 1) = 0 from by omega, Nat.choose_self, Nat.choose_zero_right,
    show t + 1 - 0 = t + 1 from by omega]
  simp only [Nat.cast_one, one_mul]
  rw [show deltaIter 0 (substitutionDeriv R) = substitutionDeriv R from rfl,
    show deltaIter 0 (((JetField.jet ((), 1) : JetField C Unit)
      * substitutionDeriv R)⁻¹)
      = ((JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R)⁻¹ from rfl]
  ring

omit [CharZero C] in
theorem invTower_add_defect_div (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) (u : ℕ) :
    invTower (C := C) u + invTowerDefect R u / substitutionDeriv R
      = -(substitutionDeriv R
          * deltaIter (u + 1) (((JetField.jet ((), 1) : JetField C Unit)
            * substitutionDeriv R)⁻¹))
        / (JetField.jet ((), 1) : JetField C Unit) ^ u := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  rw [invTower, invTowerDefect]
  field_simp
  ring

/-- **The defect recursion.**  The inhomogeneous term of the level-free tower is the next entry of
the shift tower minus a binomial convolution of the earlier entries — the identity that makes the
whole descent chain level-free. -/
theorem invTowerDefect_eq (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) (t : ℕ) :
    invTowerDefect R t
      = shiftTower R (t + 1)
        - ∑ j ∈ Finset.range t, ((((t + 1).choose (j + 1) : ℕ)) : JetField C Unit)
            * shiftTower R (j + 1)
            * (invTower (C := C) (t - 1 - j)
              + invTowerDefect R (t - 1 - j) / substitutionDeriv R) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hρ0 : substitutionDeriv R ≠ 0 := hR
  have hterm : ∀ j ∈ Finset.range t,
      ((((t + 1).choose (j + 1) : ℕ)) : JetField C Unit) * shiftTower R (j + 1)
          * (invTower (C := C) (t - 1 - j)
            + invTowerDefect R (t - 1 - j) / substitutionDeriv R)
        = -(substitutionDeriv R * (((((t + 1).choose (j + 1) : ℕ)) : JetField C Unit)
            * deltaIter (j + 1) (substitutionDeriv R)
            * deltaIter (t - j) (((JetField.jet ((), 1) : JetField C Unit)
              * substitutionDeriv R)⁻¹)))
          / (JetField.jet ((), 1) : JetField C Unit) ^ t := by
    intro j hj
    obtain ⟨q, hq⟩ : ∃ q, t = j + 1 + q := ⟨t - j - 1, by
      have := Finset.mem_range.mp hj
      omega⟩
    have h1 : t - 1 - j = q := by omega
    have h2 : t - j = q + 1 := by omega
    have hT : shiftTower R (j + 1)
        = deltaIter (j + 1) (substitutionDeriv R)
          / (JetField.jet ((), 1) : JetField C Unit) ^ (j + 1) := by
      rw [eq_div_iff (pow_ne_zero (j + 1) hy1)]
      exact shiftTower_mul_pow R (by omega)
    rw [h1, h2, invTower_add_defect_div R hR q, hT, hq]
    have hsplit : (JetField.jet ((), 1) : JetField C Unit) ^ (j + 1 + q)
        = (JetField.jet ((), 1) : JetField C Unit) ^ (j + 1)
          * (JetField.jet ((), 1) : JetField C Unit) ^ q := by
      rw [← pow_add]
    rw [hsplit]
    field_simp
  rw [Finset.sum_congr rfl hterm]
  have hTtop : shiftTower R (t + 1)
      = deltaIter (t + 1) (substitutionDeriv R)
        / (JetField.jet ((), 1) : JetField C Unit) ^ (t + 1) := by
    rw [eq_div_iff (pow_ne_zero (t + 1) hy1)]
    exact shiftTower_mul_pow R (by omega)
  have hsum : ∑ j ∈ Finset.range t,
        (-(substitutionDeriv R * (((((t + 1).choose (j + 1) : ℕ)) : JetField C Unit)
            * deltaIter (j + 1) (substitutionDeriv R)
            * deltaIter (t - j) (((JetField.jet ((), 1) : JetField C Unit)
              * substitutionDeriv R)⁻¹)))
          / (JetField.jet ((), 1) : JetField C Unit) ^ t)
      = -(substitutionDeriv R * (∑ j ∈ Finset.range t,
            ((((t + 1).choose (j + 1) : ℕ)) : JetField C Unit)
              * deltaIter (j + 1) (substitutionDeriv R)
              * deltaIter (t - j) (((JetField.jet ((), 1) : JetField C Unit)
                * substitutionDeriv R)⁻¹)))
        / (JetField.jet ((), 1) : JetField C Unit) ^ t := by
    rw [Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_neg_distrib]
  have hsplit := deltaIter_inv_split R hR t
  have hyρ : (JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R ≠ 0 :=
    mul_ne_zero hy1 hρ0
  have hinv : ((JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R)⁻¹
      * ((JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R) = 1 :=
    inv_mul_cancel₀ hyρ
  have hnum : substitutionDeriv R
        * deltaIter (t + 1) ((JetField.jet ((), 1) : JetField C Unit)⁻¹)
      - substitutionDeriv R ^ (2 : ℕ)
        * deltaIter (t + 1) (((JetField.jet ((), 1) : JetField C Unit)
          * substitutionDeriv R)⁻¹)
      = deltaIter (t + 1) (substitutionDeriv R) / (JetField.jet ((), 1) : JetField C Unit)
        + substitutionDeriv R * (∑ j ∈ Finset.range t,
            ((((t + 1).choose (j + 1) : ℕ)) : JetField C Unit)
              * deltaIter (j + 1) (substitutionDeriv R)
              * deltaIter (t - j) (((JetField.jet ((), 1) : JetField C Unit)
                * substitutionDeriv R)⁻¹)) := by
    refine mul_right_cancel₀ hy1 ?_
    rw [add_mul, div_mul_cancel₀ _ hy1]
    linear_combination (substitutionDeriv R * (JetField.jet ((), 1) : JetField C Unit)) * hsplit
      + deltaIter (t + 1) (substitutionDeriv R) * hinv
  rw [hsum, hTtop, invTowerDefect, hnum, neg_div, sub_neg_eq_add, add_div, div_div, ← pow_succ']

end

end GaloisForLFunctions.HTGeometry

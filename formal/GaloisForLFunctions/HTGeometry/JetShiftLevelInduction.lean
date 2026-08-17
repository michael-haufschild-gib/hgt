import GaloisForLFunctions.HTGeometry.JetFixedFieldShift
import GaloisForLFunctions.HTGeometry.JetLevelThreeDescent

/-!
# The inductive frame of the jet descent

Two ingredients that make the level-by-level descent an induction.

The first is the passage from "no normalizing shift below a level" to "every fixed element of that
jet order is constant": a nonconstant fixed element of order exactly `M` is a normalizing shift at
level `M`, so ruling those out one level at a time rules out all of them.

The second is the shape of the coefficient of the top coordinate in the sliced shift.  Both branches
of the slicing at level `N + 3` give the linear coefficient a relation

`Φ(w)·R'·y₁ = R'·w·y₁ − κ·σ₂ − μ·σ_{N+2}`

with `κ = N + 3` and `μ` twice the scalar attached to the quadratic coefficient.  The combination
`w + κ·y₂/y₁ + μ·y_{N+2}/y₁` is then fixed of order at most `N + 2`, hence constant, and the partial
in the top coordinate reads off the scalars: for `N ≥ 1` it forces `μ = 0`, so the quadratic branch
cannot occur above level three, and the linear branch determines the coefficient completely as
`c₀ − (N + 3)·y₂/y₁`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-! ## The ratios by the first jet coordinate -/

/-- The ratio of a jet coordinate by the first. -/
def jetOverOne (j : ℕ) : JetField C Unit :=
  (JetField.jet ((), j) : JetField C Unit) / (JetField.jet ((), 1) : JetField C Unit)

omit [CharZero C] in
theorem jetOverOne_mul (j : ℕ) :
    (jetOverOne j : JetField C Unit) * (JetField.jet ((), 1) : JetField C Unit)
      = JetField.jet ((), j) :=
  div_mul_cancel₀ _ (jet_ne_zero _)

omit [CharZero C] in
theorem pd_jetOverOne_mul {i j : ℕ} (hi : i ≠ 1) :
    JetField.pd ((), i) (jetOverOne j : JetField C Unit)
        * (JetField.jet ((), 1) : JetField C Unit)
      = JetField.pd ((), i) (JetField.jet ((), j) : JetField C Unit) := by
  have hleib := (JetField.pd ((), i) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (jetOverOne j : JetField C Unit) (JetField.jet ((), 1) : JetField C Unit)
  simp only [smul_eq_mul] at hleib
  rw [jetOverOne_mul] at hleib
  rw [hleib, JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)]
  ring

omit [CharZero C] in
theorem pd_jetOverOne_self {j : ℕ} (hj : j ≠ 1) :
    JetField.pd ((), j) (jetOverOne j : JetField C Unit)
      = 1 / (JetField.jet ((), 1) : JetField C Unit) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have h := pd_jetOverOne_mul (C := C) (i := j) (j := j) hj
  rw [JetField.pd_jet_self] at h
  field_simp
  linear_combination h

omit [CharZero C] in
theorem pd_jetOverOne_of_ne {i j : ℕ} (hi : i ≠ 1) (hij : i ≠ j) :
    JetField.pd ((), i) (jetOverOne j : JetField C Unit) = 0 := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have h := pd_jetOverOne_mul (C := C) (i := i) (j := j) hi
  rw [JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)] at h
  exact (mul_eq_zero.mp h).resolve_right hy1

/-- **The substitution on a ratio by the first jet coordinate.** -/
theorem jetSubstitution_jetOverOne (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) (j : ℕ) :
    jetSubstitution R hR (jetOverOne j : JetField C Unit)
        * (substitutionDeriv R * (JetField.jet ((), 1) : JetField C Unit))
      = substitutionDeriv R * (jetOverOne j : JetField C Unit)
          * (JetField.jet ((), 1) : JetField C Unit) + substitutionShift R j := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hΦ1 : jetSubstitution R hR (JetField.jet ((), 1) : JetField C Unit)
      = (JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R := by
    rw [jetSubstitution_jet, substitutionJet_one]
  have hΦj : jetSubstitution R hR (JetField.jet ((), j) : JetField C Unit)
      = substitutionDeriv R * (JetField.jet ((), j) : JetField C Unit) + substitutionShift R j := by
    rw [jetSubstitution_jet, substitutionJet_eq_affine]
  rw [jetOverOne, map_div₀, hΦ1, hΦj]
  field_simp

/-! ## The linear coefficient of the sliced shift -/

/-- **The linear coefficient of the sliced shift is constant up to two explicit ratios.** -/
theorem exists_const_of_double_shift (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {K : ℕ}
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, K < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {w : JetField C Unit} {n m : ℕ} (hw : ∀ j : ℕ, n < j → JetField.pd ((), j) w = 0)
    (hn : n ≤ K) (h2 : 2 ≤ K) (hmK : m ≤ K) {κ μ : C}
    (heq : jetSubstitution R hR w * substitutionDeriv R
          * (JetField.jet ((), 1) : JetField C Unit)
      = substitutionDeriv R * w * (JetField.jet ((), 1) : JetField C Unit)
        - algebraMap C (JetField C Unit) κ * substitutionShift R 2
        - algebraMap C (JetField C Unit) μ * substitutionShift R m) :
    ∃ c : C, w = algebraMap C (JetField C Unit) c
      - algebraMap C (JetField C Unit) κ * jetOverOne 2
      - algebraMap C (JetField C Unit) μ * jetOverOne m := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  set ρ : JetField C Unit := substitutionDeriv R with hρdef
  set κJ : JetField C Unit := algebraMap C (JetField C Unit) κ with hκdef
  set μJ : JetField C Unit := algebraMap C (JetField C Unit) μ with hμdef
  set g : JetField C Unit := w + κJ * jetOverOne 2 + μJ * jetOverOne m with hgdef
  have h2sub := jetSubstitution_jetOverOne R hR 2
  have hmsub := jetSubstitution_jetOverOne R hR m
  have hgfix : jetSubstitution R hR g = g := by
    have hcancel : (jetSubstitution R hR g - g) * (ρ * (JetField.jet ((), 1) : JetField C Unit))
        = 0 := by
      rw [hgdef, map_add, map_add, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes]
      linear_combination heq + κJ * h2sub + μJ * hmsub
    have hne : ρ * (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := mul_ne_zero hR hy1
    have hz := (mul_eq_zero.mp hcancel).resolve_right hne
    exact sub_eq_zero.mp hz
  have hgord : ∀ j : ℕ, K < j → JetField.pd ((), j) g = 0 := by
    intro j hj
    have hleib2 := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz κJ (jetOverOne 2)
    have hleibm := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz μJ (jetOverOne m)
    simp only [smul_eq_mul] at hleib2 hleibm
    rw [hgdef, map_add, map_add, hw j (by omega), hleib2, hleibm,
      show JetField.pd ((), j) κJ = 0 from by rw [hκdef, Derivation.map_algebraMap],
      show JetField.pd ((), j) μJ = 0 from by rw [hμdef, Derivation.map_algebraMap],
      pd_jetOverOne_of_ne (by omega) (by omega),
      pd_jetOverOne_of_ne (by omega) (by omega)]
    ring
  obtain ⟨c, hc⟩ := hfix g hgord hgfix
  exact ⟨c, by rw [← hc, hgdef]; ring⟩

/-! ## Reading off the scalars -/

/-- **Above level three the quadratic branch cannot occur.**  When the index of the second ratio is
at least three and exceeds the order of the coefficient, its scalar vanishes. -/
theorem mu_eq_zero_of_double_shift (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {K : ℕ}
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, K < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {w : JetField C Unit} {n m : ℕ} (hw : ∀ j : ℕ, n < j → JetField.pd ((), j) w = 0)
    (hn : n ≤ K) (h2 : 2 ≤ K) (hmK : m ≤ K) (hnm : n < m) (hm : 3 ≤ m) {κ μ : C}
    (heq : jetSubstitution R hR w * substitutionDeriv R
          * (JetField.jet ((), 1) : JetField C Unit)
      = substitutionDeriv R * w * (JetField.jet ((), 1) : JetField C Unit)
        - algebraMap C (JetField C Unit) κ * substitutionShift R 2
        - algebraMap C (JetField C Unit) μ * substitutionShift R m) :
    μ = 0 := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  obtain ⟨c, hc⟩ := exists_const_of_double_shift R hR hfix hw hn h2 hmK heq
  have hpd := congrArg (JetField.pd ((), m) : JetField C Unit → JetField C Unit) hc
  rw [hw m hnm, map_sub, map_sub, Derivation.map_algebraMap] at hpd
  have hleib2 := (JetField.pd ((), m) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (algebraMap C (JetField C Unit) κ) (jetOverOne 2)
  have hleibm := (JetField.pd ((), m) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (algebraMap C (JetField C Unit) μ) (jetOverOne m)
  simp only [smul_eq_mul] at hleib2 hleibm
  rw [hleib2, hleibm, Derivation.map_algebraMap, Derivation.map_algebraMap,
    pd_jetOverOne_of_ne (by omega) (by omega), pd_jetOverOne_self (by omega)] at hpd
  have hμ : algebraMap C (JetField C Unit) μ
      * (1 / (JetField.jet ((), 1) : JetField C Unit)) = 0 := by
    linear_combination hpd
  field_simp at hμ
  have hμ0 : algebraMap C (JetField C Unit) μ = 0 := by simpa using hμ
  exact (algebraMap C (JetField C Unit)).injective (by rw [hμ0, map_zero])

/-! ## From no normalizing shift to constancy of fixed elements -/

/-- **No normalizing shift below a level makes every fixed element of that jet order constant.** -/
theorem fixed_isConst_of_order_le (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (hbase : ∀ g : JetField C Unit, (∀ j : ℕ, 1 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e) :
    ∀ K : ℕ, (∀ (M : ℕ) (hM : 2 ≤ M), M ≤ K →
        ¬ HasNormalizingShift R hR (le_trans one_le_two hM)) →
      ∀ g : JetField C Unit, (∀ j : ℕ, K < j → JetField.pd ((), j) g = 0) →
        jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e := by
  intro K
  induction K with
  | zero =>
      intro _ g hg hgfix
      exact hbase g (fun j hj => hg j (by omega)) hgfix
  | succ K ih =>
      intro hno g hg hgfix
      by_cases hpd : JetField.pd ((), K + 1) g = 0
      · refine ih (fun M hM hMK => hno M hM (by omega)) g (fun j hj => ?_) hgfix
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hj) with heq | hlt
        · rw [← heq]; exact hpd
        · exact hg j (by omega)
      rcases Nat.lt_or_ge K 1 with hK | hK
      · have hK0 : K = 0 := by omega
        subst hK0
        obtain ⟨e, he⟩ := hbase g (fun j hj => hg j (by omega)) hgfix
        exact absurd (by rw [he]; exact Derivation.map_algebraMap _ e) hpd
      · exact absurd ((hasNormalizingShift_iff_exists_fixed R hR (show 2 ≤ K + 1 by omega)).mpr
          ⟨g, hg, hpd, hgfix⟩) (hno (K + 1) (by omega) (le_refl _))

end

end GaloisForLFunctions.HTGeometry

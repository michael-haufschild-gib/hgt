import GaloisForLFunctions.HTGeometry.JetOrderRelationSlicing
import GaloisForLFunctions.HTGeometry.JetLevelThreeDescent

/-!
# Tools for the jet descent at level four

Three ingredients the level-four descent needs beyond level three: the shift term at level four,
the coefficient relations of a twisted affine relation of degree at most three, and the reading of a
pure scaling relation of arbitrary exponent.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-! ## The shift term at level four -/

/-- **The shift term at level four.** -/
theorem substitutionShift_four (R : RatFunc C) :
    substitutionShift R 4
      = 4 * JetField.pd ((), 0) (substitutionDeriv R)
          * (JetField.jet ((), 1) : JetField C Unit) * (JetField.jet ((), 3) : JetField C Unit)
        + 3 * JetField.pd ((), 0) (substitutionDeriv R)
          * (JetField.jet ((), 2) : JetField C Unit) ^ 2
        + 6 * JetField.pd ((), 0) (JetField.pd ((), 0) (substitutionDeriv R))
          * (JetField.jet ((), 1) : JetField C Unit) ^ 2
          * (JetField.jet ((), 2) : JetField C Unit)
        + JetField.pd ((), 0)
            (JetField.pd ((), 0) (JetField.pd ((), 0) (substitutionDeriv R)))
          * (JetField.jet ((), 1) : JetField C Unit) ^ 4 := by
  set ρ : JetField C Unit := substitutionDeriv R with hρdef
  set ρ₁ : JetField C Unit := JetField.pd ((), 0) ρ with hρ₁def
  set ρ₂ : JetField C Unit := JetField.pd ((), 0) ρ₁ with hρ₂def
  set ρ₃ : JetField C Unit := JetField.pd ((), 0) ρ₂ with hρ₃def
  set δ := (JetField.jetDerivation : Derivation C (JetField C Unit) (JetField C Unit)) with hδdef
  have hjet : substitutionJet R 4 = δ (substitutionJet R 3) := by
    rw [substitutionJet, substitutionJet, show (4 : ℕ) = 3 + 1 from rfl, differentialJet_succ,
      JetField.deriv_eq, hδdef]
  have haff3 : substitutionJet R 3 = ρ * (JetField.jet ((), 3) : JetField C Unit)
      + (3 * ρ₁ * (JetField.jet ((), 1) : JetField C Unit)
          * (JetField.jet ((), 2) : JetField C Unit)
        + ρ₂ * (JetField.jet ((), 1) : JetField C Unit) ^ 3) := by
    rw [substitutionJet_eq_affine R 3, substitutionShift_three, hρdef, hρ₁def, hρ₂def]
  have hδρ : δ ρ = (JetField.jet ((), 1) : JetField C Unit) * ρ₁ :=
    jetDerivation_of_order_zero (fun k hk => pd_substitutionDeriv_eq_zero R hk)
  have hρ₁ord : ∀ k : ℕ, k ≠ 0 → JetField.pd ((), k) ρ₁ = 0 := by
    intro k hk
    rw [hρ₁def, pd_comm, pd_substitutionDeriv_eq_zero R hk, map_zero]
  have hδρ₁ : δ ρ₁ = (JetField.jet ((), 1) : JetField C Unit) * ρ₂ :=
    jetDerivation_of_order_zero hρ₁ord
  have hρ₂ord : ∀ k : ℕ, k ≠ 0 → JetField.pd ((), k) ρ₂ = 0 := by
    intro k hk
    rw [hρ₂def, pd_comm, hρ₁ord k hk, map_zero]
  have hδρ₂ : δ ρ₂ = (JetField.jet ((), 1) : JetField C Unit) * ρ₃ :=
    jetDerivation_of_order_zero hρ₂ord
  have hδ1 : δ (JetField.jet ((), 1) : JetField C Unit) = JetField.jet ((), 2) := by
    rw [hδdef]; exact JetField.jetDerivation_jet ((), 1)
  have hδ2 : δ (JetField.jet ((), 2) : JetField C Unit) = JetField.jet ((), 3) := by
    rw [hδdef]; exact JetField.jetDerivation_jet ((), 2)
  have hδ3 : δ (JetField.jet ((), 3) : JetField C Unit) = JetField.jet ((), 4) := by
    rw [hδdef]; exact JetField.jetDerivation_jet ((), 3)
  have hmul : ∀ a b : JetField C Unit, δ (a * b) = δ a * b + a * δ b := by
    intro a b
    have h := δ.leibniz a b
    simp only [smul_eq_mul] at h
    rw [h]; ring
  have hcube : δ ((JetField.jet ((), 1) : JetField C Unit) ^ 3)
      = 3 * (JetField.jet ((), 1) : JetField C Unit) ^ 2 * (JetField.jet ((), 2)) := by
    have h := δ.leibniz_pow (JetField.jet ((), 1) : JetField C Unit) 3
    simp only [smul_eq_mul, hδ1] at h
    rw [h]
    push_cast
    ring
  have hnat : ∀ n : ℕ, δ ((n : JetField C Unit)) = 0 := by
    intro n
    rw [show ((n : ℕ) : JetField C Unit) = algebraMap C (JetField C Unit) ((n : ℕ) : C) from by
      rw [map_natCast], Derivation.map_algebraMap]
  have h3 : δ (3 : JetField C Unit) = 0 := by
    have := hnat 3
    push_cast at this
    exact this
  rw [substitutionShift, hjet, haff3]
  simp only [map_add, hmul, hcube, hδρ, hδρ₁, hδρ₂, hδ1, hδ2, hδ3, h3]
  ring

/-! ## Coefficient relations in degree at most three -/

variable {K : Type*} [Field K]

omit [Field C] [CharZero C] in
theorem eq_cubic_of_natDegree_le_three {u : Polynomial K} (hu : u.natDegree ≤ 3) :
    u = Polynomial.C (u.coeff 3) * Polynomial.X ^ 3
      + Polynomial.C (u.coeff 2) * Polynomial.X ^ 2
      + Polynomial.C (u.coeff 1) * Polynomial.X + Polynomial.C (u.coeff 0) := by
  ext n
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;>
      simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_C, Polynomial.coeff_X]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    rw [if_neg (by omega : ¬(n = 3)), if_neg (by omega : ¬(n = 2)),
      if_neg (by omega : ¬(1 = n)), if_neg (by omega : ¬(n = 0))]
    ring

omit [Field C] [CharZero C] in
/-- **The four coefficient equations of a twisted affine relation in degree at most three.** -/
theorem coeff_eqs_of_twistComp_affine_deg_le_three (Φ : K →+* K) (ρ s c : K)
    {S : Polynomial K} {u : Polynomial K} (hu : u.natDegree ≤ 3)
    (hcu : twistComp Φ (Polynomial.C ρ * Polynomial.X + Polynomial.C s) u
      = Polynomial.C c * u - S) :
    Φ (u.coeff 3) * ρ ^ 3 = c * u.coeff 3 - S.coeff 3
      ∧ Φ (u.coeff 3) * (3 * ρ ^ 2 * s) + Φ (u.coeff 2) * ρ ^ 2
          = c * u.coeff 2 - S.coeff 2
      ∧ Φ (u.coeff 3) * (3 * ρ * s ^ 2) + Φ (u.coeff 2) * (2 * ρ * s)
            + Φ (u.coeff 1) * ρ
          = c * u.coeff 1 - S.coeff 1
      ∧ Φ (u.coeff 3) * s ^ 3 + Φ (u.coeff 2) * s ^ 2 + Φ (u.coeff 1) * s + Φ (u.coeff 0)
          = c * u.coeff 0 - S.coeff 0 := by
  set T : Polynomial K := Polynomial.C ρ * Polynomial.X + Polynomial.C s with hTdef
  have hexp : twistComp Φ T u
      = Polynomial.C (Φ (u.coeff 3)) * T ^ 3 + Polynomial.C (Φ (u.coeff 2)) * T ^ 2
        + Polynomial.C (Φ (u.coeff 1)) * T + Polynomial.C (Φ (u.coeff 0)) := by
    conv_lhs => rw [eq_cubic_of_natDegree_le_three hu]
    rw [twistComp_add, twistComp_add, twistComp_add, twistComp_C_mul_X_pow,
      twistComp_C_mul_X_pow]
    congr 1
    · congr 1
      have h1 : Polynomial.C (u.coeff 1) * Polynomial.X
          = Polynomial.C (u.coeff 1) * Polynomial.X ^ 1 := by rw [pow_one]
      rw [h1, twistComp_C_mul_X_pow, pow_one]
    · exact twistComp_C Φ T (u.coeff 0)
  have hTsq : T ^ 2 = Polynomial.C (ρ ^ 2) * Polynomial.X ^ 2
      + Polynomial.C (2 * ρ * s) * Polynomial.X + Polynomial.C (s ^ 2) := by
    rw [hTdef]
    simp only [map_pow, map_mul, map_ofNat]
    ring
  have hTcube : T ^ 3 = Polynomial.C (ρ ^ 3) * Polynomial.X ^ 3
      + Polynomial.C (3 * ρ ^ 2 * s) * Polynomial.X ^ 2
      + Polynomial.C (3 * ρ * s ^ 2) * Polynomial.X + Polynomial.C (s ^ 3) := by
    rw [hTdef]
    simp only [map_pow, map_mul, map_ofNat]
    ring
  rw [hexp, hTsq, hTcube, hTdef] at hcu
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun p : Polynomial K => p.coeff 3) hcu
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at h
    norm_num at h
    linear_combination h
  · have h := congrArg (fun p : Polynomial K => p.coeff 2) hcu
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at h
    norm_num at h
    linear_combination h
  · have h := congrArg (fun p : Polynomial K => p.coeff 1) hcu
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at h
    norm_num at h
    linear_combination h
  · have h := congrArg (fun p : Polynomial K => p.coeff 0) hcu
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at h
    norm_num at h
    linear_combination h

omit [Field C] [CharZero C] in
/-- **The affine cocycle of a shifted relation, with an arbitrary degree bound.** -/
theorem exists_cocycle_of_shift_polynomial_lt [CharZero K] (Φ : K →+* K) {ρ L : K} (hρ : ρ ≠ 0)
    {u S : Polynomial K} {a : ℕ} (hdeg : u.natDegree = a + 1) (ha : 2 ≤ a)
    (hSdeg : S.natDegree < a)
    (hcu : twistComp Φ (Polynomial.C ρ * Polynomial.X + Polynomial.C L) u
      = Polynomial.C ρ * u - S) :
    ∃ t : K, Φ t = ρ * t - L := by
  have hSa : S.coeff a = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hSa1 : S.coeff (a + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have h1 : (twistComp Φ (Polynomial.C ρ * Polynomial.X + Polynomial.C L) u).coeff a
      = ρ * u.coeff a := by
    rw [hcu, Polynomial.coeff_sub, Polynomial.coeff_C_mul, hSa, sub_zero]
  have h2 : (twistComp Φ (Polynomial.C ρ * Polynomial.X + Polynomial.C L) u).coeff (a + 1)
      = ρ * u.coeff (a + 1) := by
    rw [hcu, Polynomial.coeff_sub, Polynomial.coeff_C_mul, hSa1, sub_zero]
  have hcoc := twistComp_affine_cocycle_of_coeff Φ hρ hdeg h1 h2
  have hcast : ((a : K) + 1) ≠ 0 := by
    have h : ((a + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  refine ⟨(u.coeff a / u.coeff (a + 1)) / ((a : K) + 1), ?_⟩
  rw [map_div₀, map_add, map_natCast, map_one, hcoc]
  field_simp

/-! ## Pure scaling relations of arbitrary exponent -/

/-- **A pure scaling relation of arbitrary exponent forces a constant.** -/
theorem exists_const_of_scaling_eigen_pow (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {Kb j : ℕ} (hKb : 1 ≤ Kb)
    (hfix : ∀ g : JetField C Unit, (∀ i : ℕ, Kb < i → JetField.pd ((), i) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {w : JetField C Unit} {n : ℕ} (hn : n ≤ Kb)
    (hw : ∀ i : ℕ, n < i → JetField.pd ((), i) w = 0)
    (heq : jetSubstitution R hR w * substitutionDeriv R ^ j = w) :
    ∃ e : C, w * (JetField.jet ((), 1) : JetField C Unit) ^ j
      = algebraMap C (JetField C Unit) e := by
  refine hfix (w * (JetField.jet ((), 1) : JetField C Unit) ^ j) (fun i hi => ?_) ?_
  · have hpow : JetField.pd ((), i) ((JetField.jet ((), 1) : JetField C Unit) ^ j) = 0 := by
      have hl := (JetField.pd ((), i) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz_pow
          (JetField.jet ((), 1) : JetField C Unit) j
      rw [JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)] at hl
      simpa using hl
    have hleib := (JetField.pd ((), i) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz w
        ((JetField.jet ((), 1) : JetField C Unit) ^ j)
    simp only [smul_eq_mul] at hleib
    rw [hleib, hw i (by omega), hpow]
    ring
  · have hΦ1 : jetSubstitution R hR (JetField.jet ((), 1) : JetField C Unit)
        = (JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R := by
      rw [jetSubstitution_jet, substitutionJet_one]
    rw [map_mul, map_pow, hΦ1, mul_pow]
    linear_combination ((JetField.jet ((), 1) : JetField C Unit) ^ j) * heq

end

end GaloisForLFunctions.HTGeometry

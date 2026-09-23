import GaloisForLFunctions.HTGeometry.JetShiftLevelInduction

/-!
# The sliced shift above jet level three

At level `N + 3` the slicing of a normalizing shift leaves a polynomial of degree one or two in the
coordinate `y_{N+2}`, and comparing coefficients gives three relations.  The quadratic coefficient
satisfies a pure scaling relation, so its product with the first jet coordinate is a fixed element of
order at most `N + 1`, hence a constant `e`; feeding that into the linear relation produces

`Φ(w)·R'·y₁ = R'·w·y₁ − (N + 3)·σ₂ − 2e·σ_{N+2}`.

For `N ≥ 1` the two ratios `y₂/y₁` and `y_{N+2}/y₁` are distinct, and the partial in the top
coordinate forces `e = 0`: the quadratic branch cannot occur above level three.  What is left is the
linear branch, whose coefficient is then completely determined as `c₀ − (N + 3)·y₂/y₁`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- **A pure scaling relation of bounded order forces a constant.** -/
theorem exists_const_of_scaling_eigen_of_order (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {K : ℕ} (hK : 1 ≤ K)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, K < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {w : JetField C Unit} {n : ℕ} (hn : n ≤ K) (hw : ∀ j : ℕ, n < j → JetField.pd ((), j) w = 0)
    (heq : jetSubstitution R hR w * substitutionDeriv R = w) :
    ∃ e : C, w * (JetField.jet ((), 1) : JetField C Unit)
      = algebraMap C (JetField C Unit) e := by
  refine hfix (w * (JetField.jet ((), 1) : JetField C Unit)) (fun j hj => ?_) ?_
  · have hleib := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz w
        (JetField.jet ((), 1) : JetField C Unit)
    simp only [smul_eq_mul] at hleib
    rw [hleib, hw j (by omega),
      JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)]
    ring
  · have hΦ1 : jetSubstitution R hR (JetField.jet ((), 1) : JetField C Unit)
        = (JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R := by
      rw [jetSubstitution_jet, substitutionJet_one]
    rw [map_mul, hΦ1]
    linear_combination (JetField.jet ((), 1) : JetField C Unit) * heq

/-- **The three coefficient relations of the sliced shift at level `N + 3`.** -/
theorem branch_coefficient_relations (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) (N : ℕ)
    {u : Polynomial ↥(jetPrefixField C (N + 2))} {A B : ↥(jetPrefixField C (N + 2))}
    (hu : u.natDegree ≤ 2)
    (hcu : twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom
        (substitutionAffine R (show (1 : ℕ) ≤ N + 2 by omega)) u
      = Polynomial.C (substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)) * u
        - (Polynomial.C A * Polynomial.X + Polynomial.C B)) :
    jetSubstitution R hR (u.coeff 2 : JetField C Unit) * substitutionDeriv R ^ (2 : ℕ)
        = substitutionDeriv R * (u.coeff 2 : JetField C Unit)
      ∧ jetSubstitution R hR (u.coeff 2 : JetField C Unit)
            * (2 * substitutionDeriv R * substitutionShift R (N + 2))
          + jetSubstitution R hR (u.coeff 1 : JetField C Unit) * substitutionDeriv R
        = substitutionDeriv R * (u.coeff 1 : JetField C Unit) - (A : JetField C Unit)
      ∧ jetSubstitution R hR (u.coeff 2 : JetField C Unit) * substitutionShift R (N + 2) ^ (2 : ℕ)
            + jetSubstitution R hR (u.coeff 1 : JetField C Unit) * substitutionShift R (N + 2)
          + jetSubstitution R hR (u.coeff 0 : JetField C Unit)
        = substitutionDeriv R * (u.coeff 0 : JetField C Unit) - (B : JetField C Unit) := by
  set h2 : (1 : ℕ) ≤ N + 2 := by omega
  set ι := algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit) with hιdef
  rw [substitutionAffine] at hcu
  obtain ⟨e2, e1, e0⟩ := coeff_eqs_of_twistComp_affine_deg_le_two
    (jetSubstitutionPrefix R hR (N + 2)).toRingHom (substitutionDerivPrefix R h2)
    (substitutionShiftPrefix R h2) (substitutionDerivPrefix R h2) A B hu hcu
  have hρι : ι (substitutionDerivPrefix R h2) = substitutionDeriv R := rfl
  have hσι : ι (substitutionShiftPrefix R h2) = substitutionShift R (N + 2) := rfl
  have hΦι : ∀ z : ↥(jetPrefixField C (N + 2)),
      ι ((jetSubstitutionPrefix R hR (N + 2)).toRingHom z) = jetSubstitution R hR (ι z) :=
    fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · have hc := congrArg ι e2
    simp only [map_mul, map_pow, hΦι, hρι] at hc
    exact hc
  · have hc := congrArg ι e1
    simp only [map_mul, map_add, map_sub, map_ofNat, hΦι, hρι, hσι] at hc
    exact hc
  · have hc := congrArg ι e0
    simp only [map_mul, map_add, map_sub, map_pow, hΦι, hρι, hσι] at hc
    exact hc

/-- **Above level three the sliced shift is linear and its coefficient is determined.** -/
theorem branch_linear_above_three (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {N : ℕ}
    (hN : 1 ≤ N)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, N + 2 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {u : Polynomial ↥(jetPrefixField C (N + 2))} {A B : ↥(jetPrefixField C (N + 2))}
    (hdeg : u.natDegree = 1 ∨ u.natDegree = 2)
    (hAB : substitutionShift R (N + 3)
      = (A : JetField C Unit) * (JetField.jet ((), N + 2) : JetField C Unit)
        + (B : JetField C Unit))
    (hcu : twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom
        (substitutionAffine R (show (1 : ℕ) ≤ N + 2 by omega)) u
      = Polynomial.C (substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)) * u
        - (Polynomial.C A * Polynomial.X + Polynomial.C B)) :
    u.natDegree = 1 ∧ ∃ c₀ : C, (u.coeff 1 : JetField C Unit)
      = algebraMap C (JetField C Unit) c₀
        - algebraMap C (JetField C Unit) ((N + 3 : ℕ) : C) * jetOverOne 2 := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hu : u.natDegree ≤ 2 := by rcases hdeg with hd | hd <;> omega
  obtain ⟨E2, E1, _⟩ := branch_coefficient_relations R hR N hu hcu
  set ρ : JetField C Unit := substitutionDeriv R with hρdef
  set ρ₁ : JetField C Unit := JetField.pd ((), 0) ρ with hρ₁def
  have hord : ∀ (z : ↥(jetPrefixField C (N + 2))) (j : ℕ), N + 1 < j →
      JetField.pd ((), j) (z : JetField C Unit) = 0 := by
    intro z j hj
    exact (mem_jetPrefixField_iff (N + 2) _).mp z.2 j (by omega)
  have hAval : (A : JetField C Unit)
      = ((N + 3 : ℕ) : JetField C Unit) * (ρ₁ * (JetField.jet ((), 1) : JetField C Unit)) := by
    rw [coe_eq_pd_top_of_affine R N hAB, show N + 2 = (N + 1) + 1 from rfl,
      show N + 3 = (N + 1) + 2 from rfl, pd_top_substitutionShift_eq R (N + 1)]
  have hE2 : jetSubstitution R hR (u.coeff 2 : JetField C Unit) * ρ
      = (u.coeff 2 : JetField C Unit) := by
    refine mul_left_cancel₀ hR ?_
    linear_combination E2
  obtain ⟨e, he⟩ := exists_const_of_scaling_eigen_of_order R hR (by omega) hfix
    (n := N + 1) (by omega) (hord (u.coeff 2)) hE2
  have hσ2 : substitutionShift R 2
      = ρ₁ * (JetField.jet ((), 1) : JetField C Unit) ^ (2 : ℕ) := substitutionShift_two R
  have hdouble : jetSubstitution R hR (u.coeff 1 : JetField C Unit) * ρ
        * (JetField.jet ((), 1) : JetField C Unit)
      = ρ * (u.coeff 1 : JetField C Unit) * (JetField.jet ((), 1) : JetField C Unit)
        - algebraMap C (JetField C Unit) ((N + 3 : ℕ) : C) * substitutionShift R 2
        - algebraMap C (JetField C Unit) (2 * e) * substitutionShift R (N + 2) := by
    have hcast : algebraMap C (JetField C Unit) ((N + 3 : ℕ) : C)
        = ((N + 3 : ℕ) : JetField C Unit) := by
      rw [map_natCast]
    have hcast2 : algebraMap C (JetField C Unit) (2 * e)
        = 2 * algebraMap C (JetField C Unit) e := by
      rw [map_mul, map_ofNat]
    rw [hσ2, hcast, hcast2, ← he]
    rw [hAval] at E1
    linear_combination (JetField.jet ((), 1) : JetField C Unit) * E1
      - 2 * substitutionShift R (N + 2) * (JetField.jet ((), 1) : JetField C Unit) * hE2
  have hμ : (2 : C) * e = 0 :=
    mu_eq_zero_of_double_shift R hR hfix (hord (u.coeff 1)) (n := N + 1) (by omega) (by omega)
      (by omega) (by omega) (by omega) hdouble
  have he0 : e = 0 := by
    have htwo : (2 : C) ≠ 0 := two_ne_zero
    exact (mul_eq_zero.mp hμ).resolve_left htwo
  have hu2 : (u.coeff 2 : JetField C Unit) = 0 := by
    have : (u.coeff 2 : JetField C Unit) * (JetField.jet ((), 1) : JetField C Unit) = 0 := by
      rw [he, he0, map_zero]
    exact (mul_eq_zero.mp this).resolve_right hy1
  have hu2' : u.coeff 2 = 0 := Subtype.ext hu2
  refine ⟨?_, ?_⟩
  · rcases hdeg with hd | hd
    · exact hd
    · exfalso
      have hu0 : u ≠ 0 := by
        intro hz
        rw [hz, Polynomial.natDegree_zero] at hd
        exact absurd hd (by norm_num)
      have hne : u.coeff 2 ≠ 0 := by
        have hlc := Polynomial.leadingCoeff_ne_zero.mpr hu0
        rwa [Polynomial.leadingCoeff, hd] at hlc
      exact hne hu2'
  · obtain ⟨c₀, hc₀⟩ := exists_const_of_double_shift R hR hfix (hord (u.coeff 1))
      (n := N + 1) (by omega) (by omega) (by omega) hdouble
    refine ⟨c₀, ?_⟩
    rw [hc₀, he0, mul_zero, map_zero, zero_mul, sub_zero]

end

end GaloisForLFunctions.HTGeometry

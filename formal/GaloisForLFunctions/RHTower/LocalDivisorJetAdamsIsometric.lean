import GaloisForLFunctions.RHTower.LocalDivisorJetAdamsMonodromy

/-!
# Isometric and contractive source realizations of the local Adams packet

The power-map injection `k ↦ k^n` induces an isometry on the counting Hilbert space of positive
integers.  Its adjoint is the coefficient pullback `f(k) ↦ f(k^n)` and is contractive.  If the
actual local divisor-jet Adams packet embeds faithfully as eigenvectors of either the isometry or
this pullback, the first cotangent eigenvalue `n ≥ 2` is impossible.  A positive packet can contain
only the constant direction and its jet length is one.

This is a source-shaped strengthening of abstract power-bounded Adams rigidity.  The theorem does
not construct the missing completed prime--Gamma localization or its symplectic pairing.
-/

namespace RHTower

noncomputable section

/-- A nondegenerate alternating polarization carried directly by the local Adams packet. -/
def LocalAdamsSymplecticPolarization (m : ℕ) : Prop :=
  ∃ omega : LinearMap.BilinForm ℂ (Fin m → ℂ),
    omega.Nondegenerate ∧ omega.IsAlt

/-- A polarized local packet has even length. -/
theorem even_of_localAdamsSymplecticPolarization {m : ℕ}
    (h : LocalAdamsSymplecticPolarization m) : Even m := by
  obtain ⟨omega, hnd, halt⟩ := h
  have heven := even_finrank_of_nondegenerate_isAlt hnd halt
  simpa using heven

/-- **Isometric Adams reducedness.**  A faithful eigenpacket for the actual Adams weights inside
one source isometry has length one. -/
theorem adamsDilation_isometric_eigenpacket_forces_simple
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {m n : ℕ} (hm : 0 < m) (hn : 2 ≤ n)
    (v : Fin m → H) (hv : ∀ j, v j ≠ 0)
    (U : H →ₗᵢ[ℂ] H)
    (hU : ∀ j, U (v j) = ((n : ℂ) ^ (j : ℕ)) • v j) :
    m = 1 := by
  by_contra hne
  have hm2 : 2 ≤ m := by omega
  let j1 : Fin m := ⟨1, hm2⟩
  have hnorm := U.norm_map (v j1)
  rw [hU j1, norm_smul] at hnorm
  have hvpos : 0 < ‖v j1‖ := norm_pos_iff.mpr (hv j1)
  have hncomplex : ‖((n : ℂ) ^ (j1 : ℕ))‖ = (n : ℝ) := by
    simp [j1]
  rw [hncomplex] at hnorm
  have hnreal : (n : ℝ) = 1 := by nlinarith
  have : n = 1 := by exact_mod_cast hnreal
  omega

/-- **Contractive Adams reducedness.**  A faithful eigenpacket for the actual Adams weights inside
one source contraction has length one.  This is the precise abstract consequence applicable to
the adjoint of the source power-map isometry. -/
theorem adamsDilation_contractive_eigenpacket_forces_simple
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {m n : ℕ} (hm : 0 < m) (hn : 2 ≤ n)
    (v : Fin m → H) (hv : ∀ j, v j ≠ 0)
    (U : H →L[ℂ] H)
    (hcontract : ∀ x, ‖U x‖ ≤ ‖x‖)
    (hU : ∀ j, U (v j) = ((n : ℂ) ^ (j : ℕ)) • v j) :
    m = 1 := by
  by_contra hne
  have hm2 : 2 ≤ m := by omega
  let j1 : Fin m := ⟨1, hm2⟩
  have hnorm := hcontract (v j1)
  rw [hU j1, norm_smul] at hnorm
  have hvpos : 0 < ‖v j1‖ := norm_pos_iff.mpr (hv j1)
  have hncomplex : ‖((n : ℂ) ^ (j1 : ℕ))‖ = (n : ℝ) := by
    simp [j1]
  rw [hncomplex] at hnorm
  have hnle : (n : ℝ) ≤ 1 := by nlinarith
  have : n ≤ 1 := by exact_mod_cast hnle
  omega

/-- **Polarized isometric Adams route to RH.**  One completed source Hilbert space supplies a
faithful local Adams eigenpacket, while the source polarization supplies even local multiplicity.
The actual Adams cotangent weight makes the same positive multiplicity one. -/
theorem
    riemannHypothesis_of_rightSymplecticRealization_of_rightAdamsDilationIsometricEigenpacket
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (hsymplectic : ∀ rho ∈ rightHalf, xi rho = 0 → SymplecticRealization rho)
    (hiso : ∀ rho ∈ rightHalf, xi rho = 0 →
      ∃ n : ℕ, 2 ≤ n ∧
        ∃ v : Fin (analyticOrderAt xi rho).toNat → H,
          (∀ j, v j ≠ 0) ∧
          ∃ U : H →ₗᵢ[ℂ] H,
            ∀ j, U (v j) = ((n : ℂ) ^ (j : ℕ)) • v j) :
    RiemannHypothesis := by
  have hladder : RHLadder 1 := rhLadder_one_of_symplecticRealization hsymplectic
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  obtain ⟨n, hn, v, hv, U, hU⟩ := hiso rho hrho hzero
  have hmpos : 0 < (analyticOrderAt xi rho).toNat :=
    Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero)
  have hmone : (analyticOrderAt xi rho).toNat = 1 :=
    adamsDilation_isometric_eigenpacket_forces_simple hmpos hn v hv U hU
  have heven : Even (analyticOrderAt xi rho).toNat :=
    rhLadder_one_iff_even_order.mp hladder rho hrho hzero
  rw [hmone] at heven
  exact Nat.not_even_one heven

/-- **Same-packet polarized isometric Adams route to RH.**  This couples the two contradictory
constraints on one local source packet: its alternating form makes its length even, while its
faithful realization inside a source isometry makes its positive length one. -/
theorem
    riemannHypothesis_of_rightPolarizedAdamsIsometricEigenpacket
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (hpol : ∀ rho ∈ rightHalf, xi rho = 0 →
      LocalAdamsSymplecticPolarization (analyticOrderAt xi rho).toNat)
    (hiso : ∀ rho ∈ rightHalf, xi rho = 0 →
      ∃ n : ℕ, 2 ≤ n ∧
        ∃ v : Fin (analyticOrderAt xi rho).toNat → H,
          (∀ j, v j ≠ 0) ∧
          ∃ U : H →ₗᵢ[ℂ] H,
            ∀ j, U (v j) = ((n : ℂ) ^ (j : ℕ)) • v j) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  obtain ⟨n, hn, v, hv, U, hU⟩ := hiso rho hrho hzero
  have hmpos : 0 < (analyticOrderAt xi rho).toNat :=
    Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero)
  have hmone : (analyticOrderAt xi rho).toNat = 1 :=
    adamsDilation_isometric_eigenpacket_forces_simple hmpos hn v hv U hU
  have heven : Even (analyticOrderAt xi rho).toNat :=
    even_of_localAdamsSymplecticPolarization (hpol rho hrho hzero)
  rw [hmone] at heven
  exact Nat.not_even_one heven

/-- **Same-packet polarized contractive Adams route to RH.**  This is the source-shaped capstone
for the coefficient pullback adjoint to `|k⟩ ↦ |k^n⟩`: one contraction retains every nonzero local
jet direction, while an alternating polarization on that same packet makes its length even. -/
theorem
    riemannHypothesis_of_rightPolarizedAdamsContractiveEigenpacket
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (hpol : ∀ rho ∈ rightHalf, xi rho = 0 →
      LocalAdamsSymplecticPolarization (analyticOrderAt xi rho).toNat)
    (hcontractive : ∀ rho ∈ rightHalf, xi rho = 0 →
      ∃ n : ℕ, 2 ≤ n ∧
        ∃ v : Fin (analyticOrderAt xi rho).toNat → H,
          (∀ j, v j ≠ 0) ∧
          ∃ U : H →L[ℂ] H,
            (∀ x, ‖U x‖ ≤ ‖x‖) ∧
            ∀ j, U (v j) = ((n : ℂ) ^ (j : ℕ)) • v j) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  obtain ⟨n, hn, v, hv, U, hcontract, hU⟩ := hcontractive rho hrho hzero
  have hmpos : 0 < (analyticOrderAt xi rho).toNat :=
    Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero)
  have hmone : (analyticOrderAt xi rho).toNat = 1 :=
    adamsDilation_contractive_eigenpacket_forces_simple
      hmpos hn v hv U hcontract hU
  have heven : Even (analyticOrderAt xi rho).toNat :=
    even_of_localAdamsSymplecticPolarization (hpol rho hrho hzero)
  rw [hmone] at heven
  exact Nat.not_even_one heven

end


end RHTower

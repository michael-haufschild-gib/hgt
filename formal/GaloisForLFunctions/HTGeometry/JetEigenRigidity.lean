import GaloisForLFunctions.HTGeometry.JetWeightZeroDescent

/-!
# Rigidity of the weight-zero eigen-relations

A nonzero torus-invariant solution of a pure eigen-relation

`R'^κ·Φ(g) = g`

forces the exponent to vanish.  Multiplying by `y₁^κ` turns the relation into `Φ(g·y₁^κ) = g·y₁^κ`,
so the product is a fixed element of the same jet order and hence a constant; the torus then reads
off `2^{-κ} = 1`, and in characteristic zero that forces `κ = 0`.

This is the engine of the descent: at every slicing step the leading coefficient satisfies such a
relation with an exponent determined by the degree, so the degree is pinned by an arithmetic
condition.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

theorem two_zpow_eq_one {κ : ℤ} (h : (2 : C) ^ κ = 1) : κ = 0 := by
  have hnat : ∀ n : ℕ, (2 : C) ^ n = 1 → n = 0 := by
    intro n hn
    have hcast : ((2 ^ n : ℕ) : C) = ((1 : ℕ) : C) := by push_cast; exact hn
    have h2 : (2 : ℕ) ^ n = 2 ^ 0 := by simpa using Nat.cast_injective (R := C) hcast
    exact Nat.pow_right_injective (le_refl 2) h2
  rcases (by omega : (0:ℤ) ≤ κ ∨ κ < 0) with hk | hk
  · lift κ to ℕ using hk with n
    rw [zpow_natCast] at h
    exact_mod_cast hnat n h
  · have hk' : 0 ≤ -κ := by omega
    lift (-κ) to ℕ using hk' with n hn
    have h2 : (2 : C) ^ n = 1 := by
      have hz : (2 : C) ^ (-κ) = 1 := by
        rw [zpow_neg, h, inv_one]
      rw [← hn, zpow_natCast] at hz
      exact hz
    have := hnat n h2
    omega

theorem pd_zpow_jet_one {j : ℕ} (hj : j ≠ 1) (κ : ℤ) :
    JetField.pd ((), j) ((JetField.jet ((), 1) : JetField C Unit) ^ κ) = 0 := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hpow : ∀ n : ℕ, JetField.pd ((), j) ((JetField.jet ((), 1) : JetField C Unit) ^ n) = 0 := by
    intro n
    have hl := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz_pow
        (JetField.jet ((), 1) : JetField C Unit) n
    rw [JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)] at hl
    simpa using hl
  rcases (by omega : (0:ℤ) ≤ κ ∨ κ < 0) with hk | hk
  · lift κ to ℕ using hk with n
    rw [zpow_natCast]
    exact hpow n
  · have hk' : 0 ≤ -κ := by omega
    lift (-κ) to ℕ using hk' with n hn
    have hκ : κ = -(n : ℤ) := by omega
    have hz : ((JetField.jet ((), 1) : JetField C Unit)) ^ κ
        = (((JetField.jet ((), 1) : JetField C Unit)) ^ n)⁻¹ := by
      rw [hκ, zpow_neg, zpow_natCast]
    rw [hz]
    have hli := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz_inv
        ((JetField.jet ((), 1) : JetField C Unit) ^ n)
    rw [hli, hpow n]
    simp

/-- **Eigen-rigidity.**  A nonzero torus-invariant solution of a pure eigen-relation has exponent
zero. -/
theorem exponent_eq_zero_of_weightZero_eigen (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {K : ℕ} (hK : 1 ≤ K)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, K < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {g : JetField C Unit} (hwz : IsWeightZero g) (hg0 : g ≠ 0)
    (hgord : ∀ j : ℕ, K < j → JetField.pd ((), j) g = 0)
    {κ : ℤ} (heq : substitutionDeriv R ^ κ * jetSubstitution R hR g = g) :
    κ = 0 := by
  have htwo : (2 : C) ≠ 0 := two_ne_zero
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  set y : JetField C Unit := (JetField.jet ((), 1) : JetField C Unit) with hydef
  have hyk : y ^ κ ≠ 0 := zpow_ne_zero _ hy1
  have hΦ1 : jetSubstitution R hR y = y * substitutionDeriv R := by
    rw [hydef, jetSubstitution_jet, substitutionJet_one]
  -- the product with `y₁^κ` is fixed
  have hfixed : jetSubstitution R hR (g * y ^ κ) = g * y ^ κ := by
    rw [map_mul, map_zpow₀, hΦ1, mul_zpow]
    linear_combination (y ^ κ) * heq
  have hord : ∀ j : ℕ, K < j → JetField.pd ((), j) (g * y ^ κ) = 0 := by
    intro j hj
    have hleib := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz g (y ^ κ)
    simp only [smul_eq_mul] at hleib
    rw [hleib, hgord j hj, pd_zpow_jet_one (by omega) κ]
    ring
  obtain ⟨e, he⟩ := hfix (g * y ^ κ) hord hfixed
  have he0 : e ≠ 0 := by
    intro hh
    rw [hh, map_zero] at he
    exact hg0 ((mul_eq_zero.mp he).resolve_right hyk)
  have heJ : algebraMap C (JetField C Unit) e ≠ 0 := by
    intro hh
    exact he0 ((algebraMap C (JetField C Unit)).injective (by rw [hh, map_zero]))
  -- the torus reads off the exponent
  have hws : weightScale htwo (g * y ^ κ) = algebraMap C (JetField C Unit) ((2 : C) ^ κ)
      * (g * y ^ κ) := by
    rw [map_mul, map_zpow₀, hydef, weightScale_jet, pow_one, mul_zpow]
    have hwg : weightScale htwo g = g := hwz
    rw [hwg]
    rw [show algebraMap C (JetField C Unit) ((2 : C) ^ κ)
      = (algebraMap C (JetField C Unit) (2 : C)) ^ κ from by rw [map_zpow₀]]
    ring
  rw [he, AlgEquiv.commutes] at hws
  have hone : algebraMap C (JetField C Unit) ((2 : C) ^ κ) = 1 := by
    rw [← he] at hws
    refine mul_right_cancel₀ heJ ?_
    rw [one_mul, ← he]
    exact hws.symm
  refine two_zpow_eq_one (C := C) ?_
  have := (algebraMap C (JetField C Unit)).injective
    (show algebraMap C (JetField C Unit) ((2 : C) ^ κ) = algebraMap C (JetField C Unit) 1 from by
      rw [hone, map_one])
  exact this

/-! ## The degree of the sliced polynomial -/

/-- **Above jet level three the sliced shift is linear.**  The leading coefficient of the polynomial
branch satisfies a pure eigen-relation whose exponent is `(N + 2) − (N + 1)·d`; rigidity forces that
to vanish, and `(N + 1)·d = N + 2` has no solution with `d ≥ 2` when `N ≥ 1`. -/
theorem natDegree_le_one_of_zbranch (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {N : ℕ}
    (hN : 1 ≤ N)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, N + 2 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {u S : Polynomial ↥(jetPrefixField C (N + 2))}
    (huwz : ∀ i : ℕ, IsWeightZero ((u.coeff i : ↥(jetPrefixField C (N + 2))) : JetField C Unit))
    (hu0 : u ≠ 0) (hSdeg : S.natDegree ≤ 1)
    (hu : twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom
        (Polynomial.C (substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)
            ^ (1 - ((N + 2 : ℕ) : ℤ))) * Polynomial.X
          + Polynomial.C (substitutionShiftRatioPrefix R (show 1 < N + 2 by omega)
              * substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)
                ^ (-((N + 2 : ℕ) : ℤ)))) u
      = Polynomial.C (substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)
          ^ (1 - ((N + 3 : ℕ) : ℤ))) * u - S) :
    u.natDegree ≤ 1 := by
  classical
  by_contra hd
  push_neg at hd
  set hk2 : (1 : ℕ) ≤ N + 2 := by omega
  set d : ℕ := u.natDegree with hddef
  set ρP : ↥(jetPrefixField C (N + 2)) := substitutionDerivPrefix R hk2 with hρPdef
  have hρP0 : ρP ≠ 0 := substitutionDerivPrefix_ne_zero R hR hk2
  set aP : ↥(jetPrefixField C (N + 2)) := ρP ^ (1 - ((N + 2 : ℕ) : ℤ)) with haPdef
  set bP : ↥(jetPrefixField C (N + 2)) :=
    substitutionShiftRatioPrefix R (show 1 < N + 2 by omega) * ρP ^ (-((N + 2 : ℕ) : ℤ))
    with hbPdef
  set cP : ↥(jetPrefixField C (N + 2)) := ρP ^ (1 - ((N + 3 : ℕ) : ℤ)) with hcPdef
  have haP0 : aP ≠ 0 := zpow_ne_zero _ hρP0
  set T : Polynomial ↥(jetPrefixField C (N + 2)) :=
    Polynomial.C aP * Polynomial.X + Polynomial.C bP with hTdef
  have hT : T.natDegree = 1 := Polynomial.natDegree_linear haP0
  have hTlead : T.leadingCoeff = aP := Polynomial.leadingCoeff_linear haP0
  -- the leading coefficient relation
  have hSd : S.coeff d = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hcf := congrArg (fun p : Polynomial ↥(jetPrefixField C (N + 2)) => p.coeff d) hu
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, hSd, sub_zero] at hcf
  have hleadL : (twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom T u).coeff d
      = (jetSubstitutionPrefix R hR (N + 2)).toRingHom (u.coeff d) * aP ^ d := by
    have hdeg := natDegree_twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom hT u
    have hlead := leadingCoeff_twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom hT u
    rw [hTlead] at hlead
    rw [show (twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom T u).coeff d
      = (twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom T u).leadingCoeff from by
        rw [Polynomial.leadingCoeff, hdeg]]
    rw [hlead, Polynomial.leadingCoeff, hddef]
  rw [hleadL] at hcf
  -- push to the jet field
  set ι := algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit) with hιdef
  have hιρ : ι ρP = substitutionDeriv R := rfl
  have hΦι : ∀ z : ↥(jetPrefixField C (N + 2)),
      ι ((jetSubstitutionPrefix R hR (N + 2)).toRingHom z) = jetSubstitution R hR (ι z) :=
    fun _ => rfl
  have hJ := congrArg ι hcf
  simp only [haPdef, hcPdef, map_mul, map_pow, map_zpow₀, hιρ, hΦι] at hJ
  set ρ : JetField C Unit := substitutionDeriv R with hρdef
  have hρ0 : ρ ≠ 0 := hR
  have hud0 : ι (u.coeff d) ≠ 0 := by
    intro hh
    have : u.coeff d = 0 := (algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit)).injective
      (by rw [hh, map_zero])
    rw [hddef, ← Polynomial.leadingCoeff] at this
    exact hu0 (Polynomial.leadingCoeff_eq_zero.mp this)
  -- the eigen-relation
  have heig : ρ ^ ((1 - ((N + 2 : ℕ) : ℤ)) * (d : ℤ) - (1 - ((N + 3 : ℕ) : ℤ)))
      * jetSubstitution R hR (ι (u.coeff d)) = ι (u.coeff d) := by
    have hsplit : ρ ^ ((1 - ((N + 2 : ℕ) : ℤ)) * (d : ℤ) - (1 - ((N + 3 : ℕ) : ℤ)))
        * ρ ^ (1 - ((N + 3 : ℕ) : ℤ))
        = (ρ ^ (1 - ((N + 2 : ℕ) : ℤ))) ^ d := by
      rw [← zpow_add₀ hρ0, ← zpow_natCast (ρ ^ (1 - ((N + 2 : ℕ) : ℤ))) d, ← zpow_mul]
      congr 1
      ring
    have hne : ρ ^ (1 - ((N + 3 : ℕ) : ℤ)) ≠ 0 := zpow_ne_zero _ hρ0
    refine mul_right_cancel₀ hne ?_
    calc ρ ^ ((1 - ((N + 2 : ℕ) : ℤ)) * (d : ℤ) - (1 - ((N + 3 : ℕ) : ℤ)))
          * jetSubstitution R hR (ι (u.coeff d)) * ρ ^ (1 - ((N + 3 : ℕ) : ℤ))
        = jetSubstitution R hR (ι (u.coeff d)) * (ρ ^ (1 - ((N + 2 : ℕ) : ℤ))) ^ d := by
          rw [← hsplit]; ring
      _ = ρ ^ (1 - ((N + 3 : ℕ) : ℤ)) * ι (u.coeff d) := hJ
      _ = ι (u.coeff d) * ρ ^ (1 - ((N + 3 : ℕ) : ℤ)) := by ring
  have hord : ∀ j : ℕ, N + 2 < j → JetField.pd ((), j) (ι (u.coeff d)) = 0 := by
    intro j hj
    exact (mem_jetPrefixField_iff (N + 2) _).mp (u.coeff d).2 j (by omega)
  have hzero := exponent_eq_zero_of_weightZero_eigen R hR (K := N + 2) (by omega) hfix
    (huwz d) hud0 hord heig
  have hnat : (1 - ((N + 2 : ℕ) : ℤ)) * (d : ℤ) - (1 - ((N + 3 : ℕ) : ℤ)) = 0 := hzero
  push_cast at hnat
  have hdge : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hNge : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  nlinarith [hnat, hdge, hNge]


end

end GaloisForLFunctions.HTGeometry

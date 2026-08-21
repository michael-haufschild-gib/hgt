import GaloisForLFunctions.HTGeometry.BorelWeil.RankTwoIndependence

/-!
# Nonvanishing of the first cohomology for `GL(2)`

When the weight pairs to at most `−2` with the coroot, the Laurent monomial `t⁻¹` is not a sum of a
function regular on one cell and one regular on the other: clearing denominators turns such a
relation into a polynomial identity in the transcendental coordinate whose coefficient at one degree
reads `1 = 0`.  So the first cohomology of `L_λ` does not vanish — the other half of Bott's theorem
in rank one.

## Main results

* `tPow_neg_one_not_mem_sup` — the separating Laurent monomial.
* `flagCohomology_one_nontrivial` — `H¹(G/B, L_λ) ≠ 0` for `d ≤ −2`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {k : Type*} [Field k] [Infinite k]

theorem tPow_natCast_eq_aeval (j : ℕ) :
    tPow k (j : ℤ) = Polynomial.aeval (tCoord k) ((Polynomial.X : Polynomial k) ^ j) := by
  rw [tPow_natCast, map_pow, Polynomial.aeval_X]

/-- **The separating Laurent monomial.**  For `d ≤ −2` the monomial `t⁻¹` is not a sum of a function
regular on one cell and one regular on the other, after trivialization. -/
theorem tPow_neg_one_not_mem_add {d : ℤ} (hd : d ≤ -2) {a b : FlagLoc 2 k}
    (ha : a ∈ cellSubalg 2 k {(1 : Equiv.Perm (Fin 2))}) (hb : b ∈ cellSubalg 2 k {swapTwo}) :
    a + b * tPow k d ≠ tPow k (-1) := by
  classical
  intro hcon
  rw [cellSubalg_one_eq_adjoin, Algebra.adjoin_singleton_eq_range_aeval] at ha
  rw [cellSubalg_swap_eq_adjoin, Algebra.adjoin_singleton_eq_range_aeval] at hb
  obtain ⟨q, hq⟩ := ha
  obtain ⟨r, hr⟩ := hb
  set M : ℕ := r.natDegree + 1 + (-d).toNat with hM
  have hdM : (d : ℤ) + (M : ℕ) = (r.natDegree : ℤ) + 1 := by
    have hdneg : ((-d).toNat : ℤ) = -d := Int.toNat_of_nonneg (by omega)
    push_cast [hM]
    omega
  -- exponents
  have hMpos : 1 ≤ M := by omega
  -- rewrite the relation as an identity of powers of the coordinate
  have hqval : a = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • tPow k (i : ℤ) := by
    rw [← hq]
    show Polynomial.aeval (tCoord k) q = _
    rw [Polynomial.aeval_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => by rw [tPow_natCast]
  have hrval : b = ∑ j ∈ Finset.range (r.natDegree + 1), r.coeff j • tPow k (-(j : ℤ)) := by
    rw [← hr]
    show Polynomial.aeval (tInv k) r = _
    rw [Polynomial.aeval_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => by rw [tPow_neg_natCast]
  -- multiply by the M-th power of the coordinate
  have hexp : (a + b * tPow k d) * tPow k (M : ℤ)
      = (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • tPow k (i : ℤ) * tPow k (M : ℤ))
        + ∑ j ∈ Finset.range (r.natDegree + 1),
            r.coeff j • tPow k (-(j : ℤ)) * tPow k d * tPow k (M : ℤ) := by
    rw [hqval, hrval]
    simp only [add_mul, Finset.sum_mul]
  have hleft : ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • tPow k (i : ℤ) * tPow k (M : ℤ)
      = ∑ i ∈ Finset.range (q.natDegree + 1),
        q.coeff i • Polynomial.aeval (tCoord k) ((Polynomial.X : Polynomial k) ^ (i + M)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, ← tPow_add, ← tPow_natCast_eq_aeval]
    congr 2
  have hright : ∑ j ∈ Finset.range (r.natDegree + 1),
        r.coeff j • tPow k (-(j : ℤ)) * tPow k d * tPow k (M : ℤ)
      = ∑ j ∈ Finset.range (r.natDegree + 1),
        r.coeff j • Polynomial.aeval (tCoord k)
          ((Polynomial.X : Polynomial k) ^ ((d - (j : ℤ) + (M : ℕ)).toNat)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjle : (j : ℤ) ≤ (r.natDegree : ℤ) := by
      have := Finset.mem_range.mp hj
      omega
    have hnonneg : (0 : ℤ) ≤ d - (j : ℤ) + (M : ℕ) := by omega
    rw [smul_mul_assoc, smul_mul_assoc, ← tPow_add, ← tPow_add, ← tPow_natCast_eq_aeval]
    congr 2
    rw [Int.toNat_of_nonneg hnonneg]
    ring
  have hlastpow : tPow k (-1) * tPow k (M : ℤ)
      = Polynomial.aeval (tCoord k) ((Polynomial.X : Polynomial k) ^ (M - 1)) := by
    rw [← tPow_add, ← tPow_natCast_eq_aeval]
    congr 2
    omega
  have hmul : (∑ i ∈ Finset.range (q.natDegree + 1),
        q.coeff i • Polynomial.aeval (tCoord k) ((Polynomial.X : Polynomial k) ^ (i + M)))
      + (∑ j ∈ Finset.range (r.natDegree + 1),
        r.coeff j • Polynomial.aeval (tCoord k)
          ((Polynomial.X : Polynomial k) ^ ((d - (j : ℤ) + (M : ℕ)).toNat)))
      = Polynomial.aeval (tCoord k) ((Polynomial.X : Polynomial k) ^ (M - 1)) := by
    rw [← hleft, ← hright, ← hexp, hcon, hlastpow]
  -- turn it into an identity of polynomials
  have hpoly : Polynomial.aeval (tCoord k)
      ((∑ i ∈ Finset.range (q.natDegree + 1), Polynomial.C (q.coeff i) * (Polynomial.X : Polynomial k) ^ (i + M))
        + ∑ j ∈ Finset.range (r.natDegree + 1),
            Polynomial.C (r.coeff j) * (Polynomial.X : Polynomial k) ^ ((d - (j : ℤ) + (M : ℕ)).toNat))
      = Polynomial.aeval (tCoord k) ((Polynomial.X : Polynomial k) ^ (M - 1)) := by
    rw [map_add, map_sum, map_sum, ← hmul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by rw [map_mul, Polynomial.aeval_C, Algebra.smul_def]
    · exact Finset.sum_congr rfl fun j _ => by rw [map_mul, Polynomial.aeval_C, Algebra.smul_def]
  have hpeq := aeval_tCoord_injective hpoly
  -- compare the coefficients in degree M - 1
  have hcoeff := congrArg (fun P : Polynomial k => P.coeff (M - 1)) hpeq
  rw [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff,
    Polynomial.coeff_X_pow] at hcoeff
  have hz1 : ∑ i ∈ Finset.range (q.natDegree + 1),
      (Polynomial.C (q.coeff i) * (Polynomial.X : Polynomial k) ^ (i + M)).coeff (M - 1) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  have hz2 : ∑ j ∈ Finset.range (r.natDegree + 1),
      (Polynomial.C (r.coeff j) * (Polynomial.X : Polynomial k) ^ ((d - (j : ℤ) + (M : ℕ)).toNat)).coeff (M - 1)
      = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjle : (j : ℤ) ≤ (r.natDegree : ℤ) := by
      have := Finset.mem_range.mp hj
      omega
    have hlt : ((d - (j : ℤ) + (M : ℕ)).toNat : ℤ) ≤ (M : ℤ) - 2 := by
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  rw [hz1, hz2, if_pos rfl] at hcoeff
  simp at hcoeff

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {k : Type*} [Field k] [Infinite k]

theorem tPow_neg_one_not_mem_sup {lam : Fin 2 → ℤ} (hd : lam 0 - lam 1 ≤ -2) :
    tPow k (-1) * ((cellTriv (1 : Equiv.Perm (Fin 2)) lam : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)
      ∉ cellSections 2 k {(1 : Equiv.Perm (Fin 2))} lam ⊔ cellSections 2 k {swapTwo} lam := by
  classical
  intro hmem
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, hc, hceq⟩ := tPow_mul_cellTriv (k := k) lam
  set T := ((cellTriv (1 : Equiv.Perm (Fin 2)) lam : (FlagLoc 2 k)ˣ) : FlagLoc 2 k) with hT
  set S := ((cellTriv swapTwo lam : (FlagLoc 2 k)ˣ) : FlagLoc 2 k) with hS
  have hTne : T ≠ 0 := Units.ne_zero _
  -- the two pieces, trivialized
  have hA : u * (((cellTriv (1 : Equiv.Perm (Fin 2)) lam)⁻¹ : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)
      ∈ cellSubalg 2 k {(1 : Equiv.Perm (Fin 2))} := by
    refine (mem_cellSections_mul_cellTriv (Finset.mem_singleton_self _) lam).mp ?_
    rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
    exact hu
  have hB : v * (((cellTriv swapTwo lam)⁻¹ : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)
      ∈ cellSubalg 2 k {swapTwo} := by
    refine (mem_cellSections_mul_cellTriv (Finset.mem_singleton_self _) lam).mp ?_
    rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
    exact hv
  have hurec : u = (u * (((cellTriv (1 : Equiv.Perm (Fin 2)) lam)⁻¹ : (FlagLoc 2 k)ˣ) :
      FlagLoc 2 k)) * T := by
    rw [hT, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hvrec : v = (v * (((cellTriv swapTwo lam)⁻¹ : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)) * S := by
    rw [hS, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hSval : S = c⁻¹ • (tPow k (lam 0 - lam 1) * T) := by
    rw [hceq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  -- cancel the trivialization
  have hcancel : (u * (((cellTriv (1 : Equiv.Perm (Fin 2)) lam)⁻¹ : (FlagLoc 2 k)ˣ) : FlagLoc 2 k))
      + (c⁻¹ • (v * (((cellTriv swapTwo lam)⁻¹ : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)))
        * tPow k (lam 0 - lam 1) = tPow k (-1) := by
    refine mul_right_cancel₀ hTne ?_
    rw [add_mul, ← hurec]
    have hv2 : (c⁻¹ • (v * (((cellTriv swapTwo lam)⁻¹ : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)))
        * tPow k (lam 0 - lam 1) * T = v := by
      conv_rhs => rw [hvrec, hSval]
      rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_assoc]
    rw [hv2, huv]
  exact tPow_neg_one_not_mem_add hd hA (Submodule.smul_mem _ _ hB) hcancel

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {k : Type*} [Field k] [Infinite k]

theorem tPow_neg_one_mul_cellTriv_mem (lam : Fin 2 → ℤ) :
    tPow k (-1) * ((cellTriv (1 : Equiv.Perm (Fin 2)) lam : (FlagLoc 2 k)ˣ) : FlagLoc 2 k)
      ∈ cellSections 2 k ({1, swapTwo} : Finset (Equiv.Perm (Fin 2))) lam := by
  classical
  refine (mem_cellSections_mul_cellTriv
    (Finset.mem_insert_self (1 : Equiv.Perm (Fin 2)) {swapTwo}) lam).mpr ?_
  have h1 : tPow k (-1) ∈ cellSections 2 k {swapTwo} (fun _ => 0) := by
    have h := tPow_neg_mem_cellSubalg_swap (k := k) 1
    have hcast : (-((1 : ℕ) : ℤ)) = (-1 : ℤ) := by norm_num
    rw [hcast] at h
    exact h
  have hsub : ({swapTwo} : Finset (Equiv.Perm (Fin 2))) ⊆ {1, swapTwo} :=
    Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  exact cellSections_mono hsub _ h1

/-- The Čech `1`-cochain built from the separating Laurent monomial. -/
noncomputable def sepCochain (lam : Fin 2 → ℤ) : Finset (Equiv.Perm (Fin 2)) → FlagLoc 2 k :=
  fun I => if I = {1, swapTwo} then
    tPow k (-1) * ((cellTriv (1 : Equiv.Perm (Fin 2)) lam : (FlagLoc 2 k)ˣ) : FlagLoc 2 k) else 0

theorem sepCochain_pair (lam : Fin 2 → ℤ) :
    sepCochain (k := k) lam {1, swapTwo}
      = tPow k (-1)
        * ((cellTriv (1 : Equiv.Perm (Fin 2)) lam : (FlagLoc 2 k)ˣ) : FlagLoc 2 k) := by
  rw [sepCochain, if_pos rfl]

theorem sepCochain_of_card_ne (lam : Fin 2 → ℤ) {I : Finset (Equiv.Perm (Fin 2))}
    (hI : I.card ≠ 2) : sepCochain (k := k) lam I = 0 := by
  classical
  rw [sepCochain, if_neg]
  intro hc
  refine hI ?_
  rw [hc]
  rw [Finset.card_insert_of_notMem (by simpa using one_ne_swapTwo), Finset.card_singleton]

theorem sepCochain_mem_flagCocycles (lam : Fin 2 → ℤ) :
    sepCochain (k := k) lam ∈ flagCocycles 2 k lam 1 := by
  classical
  constructor
  · constructor
    · intro I hI
      exact sepCochain_of_card_ne lam (by simpa using hI)
    · intro I
      by_cases hI : I.card = 2
      · rw [eq_pair_of_card_two hI, sepCochain_pair]
        exact tPow_neg_one_mul_cellTriv_mem lam
      · rw [sepCochain_of_card_ne lam hI]
        exact Submodule.zero_mem _
  · show cechDModule k (sepCochain lam) = 0
    funext I
    refine Finset.sum_eq_zero fun u hu => ?_
    have hcard : (I.erase u).card = I.card - 1 := Finset.card_erase_of_mem hu
    have hne : (I.erase u).card ≠ 2 := by
      intro hc
      rw [hc] at hcard
      have hle : I.card ≤ Fintype.card (Equiv.Perm (Fin 2)) := Finset.card_le_univ I
      rw [card_perm_fin_two] at hle
      omega
    rw [sepCochain_of_card_ne lam hne, smul_zero]

theorem sepCochain_not_mem_flagCoboundaries {lam : Fin 2 → ℤ} (hd : lam 0 - lam 1 ≤ -2) :
    sepCochain (k := k) lam ∉ flagCoboundaries 2 k lam 1 := by
  classical
  rintro ⟨ν, hν, hνeq⟩
  have hval : cechDModule k ν {1, swapTwo} = sepCochain (k := k) lam {1, swapTwo} := by
    rw [← hνeq]
    rfl
  rw [sepCochain_pair, cechDModule, Finset.sum_pair one_ne_swapTwo, erase_pair_left,
    erase_pair_right] at hval
  refine tPow_neg_one_not_mem_sup (k := k) hd ?_
  rw [← hval]
  exact Submodule.add_mem _
    (Submodule.mem_sup_right (Submodule.smul_mem _ _ (hν.mem _)))
    (Submodule.mem_sup_left (Submodule.smul_mem _ _ (hν.mem _)))

/-- **Nonvanishing of the first cohomology of the flag variety of `GL(2)`.**  When the weight pairs
to at most `−2` with the coroot, `H¹(G/B, L_λ) ≠ 0`. -/
theorem flagCohomology_one_nontrivial {lam : Fin 2 → ℤ} (hd : lam 0 - lam 1 ≤ -2) :
    Nontrivial (flagCohomology 2 k lam 1) := by
  classical
  refine ⟨⟨Submodule.Quotient.mk ⟨sepCochain lam, sepCochain_mem_flagCocycles lam⟩, 0, ?_⟩⟩
  intro hc
  rw [Submodule.Quotient.mk_eq_zero] at hc
  exact sepCochain_not_mem_flagCoboundaries hd hc

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {k : Type*} [Field k] [Infinite k]

theorem dotAction_swapTwo_zero (lam : Fin 2 → ℤ) :
    dotAction swapTwo lam 0 = lam 1 - 1 := by
  have hidx : (⟨((0 : Fin 2) : ℕ) + 1, zero_succ_lt_two⟩ : Fin 2) = (1 : Fin 2) := rfl
  rw [swapTwo, dotAction_swapNext_self, hidx]

theorem dotAction_swapTwo_one (lam : Fin 2 → ℤ) :
    dotAction swapTwo lam 1 = lam 0 + 1 := by
  have hidx : (⟨((0 : Fin 2) : ℕ) + 1, zero_succ_lt_two⟩ : Fin 2) = (1 : Fin 2) := rfl
  have h := dotAction_swapNext_succ lam (0 : Fin 2) zero_succ_lt_two
  rw [hidx] at h
  rw [swapTwo]
  exact h

/-- The reflected weight is dominant exactly in the antidominant range. -/
theorem antitone_dotAction_swapTwo_iff {lam : Fin 2 → ℤ} :
    Antitone (dotAction swapTwo lam) ↔ lam 0 - lam 1 ≤ -2 := by
  rw [antitone_fin_two_iff, dotAction_swapTwo_zero, dotAction_swapTwo_one]
  omega

theorem permLength_swapTwo : permLength swapTwo = 1 := by
  classical
  have hfil : inversions swapTwo = {((0 : Fin 2), (1 : Fin 2))} := by
    ext p
    obtain ⟨u, v⟩ := p
    rw [inversions, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, huv, hw⟩
      rcases fin_two_cases u with rfl | rfl <;> rcases fin_two_cases v with rfl | rfl
      · exact absurd huv (by decide)
      · rfl
      · exact absurd huv (by decide)
      · exact absurd huv (by decide)
    · intro h
      rw [Prod.ext_iff] at h
      obtain ⟨hu, hv⟩ := h
      simp only at hu hv
      subst hu
      subst hv
      refine ⟨Finset.mem_univ _, by decide, ?_⟩
      have h0 : swapTwo (0 : Fin 2) = 1 := by
        rw [swapTwo, swapNext, Equiv.swap_apply_left]
        exact Fin.ext rfl
      have h1 : swapTwo (1 : Fin 2) = 0 := by
        have hidx : (⟨((0 : Fin 2) : ℕ) + 1, zero_succ_lt_two⟩ : Fin 2) = (1 : Fin 2) :=
          Fin.ext rfl
        rw [swapTwo, swapNext, ← hidx, Equiv.swap_apply_right]
      rw [h0, h1]
      exact (by decide : (0 : Fin 2) < 1)
  rw [permLength, hfil, Finset.card_singleton]

/-- **Bott's theorem for `GL(2)`, antidominant case.**  When the weight pairs to at most `−2` with
the coroot, the cohomology of `L_λ` is concentrated in degree one — the Coxeter length of the Weyl
element making `λ` dominant for the dot action. -/
theorem rankTwo_bott_antidominant [CharZero k] {lam : Fin 2 → ℤ} (hd : lam 0 - lam 1 ≤ -2) :
    Subsingleton (flagCohomology 2 k lam 0) ∧ Nontrivial (flagCohomology 2 k lam 1)
      ∧ (∀ p : ℕ, 2 ≤ p → Subsingleton (flagCohomology 2 k lam p))
      ∧ Antitone (dotAction swapTwo lam) ∧ permLength swapTwo = 1 := by
  refine ⟨?_, flagCohomology_one_nontrivial hd, fun p hp =>
    flagCohomology_subsingleton_of_two_le hp, antitone_dotAction_swapTwo_iff.mpr hd,
    permLength_swapTwo⟩
  have hnot : ¬ Antitone lam := by
    rw [antitone_fin_two_iff]
    omega
  rw [← not_nontrivial_iff_subsingleton]
  intro hcon
  exact hnot ((flagCohomology_zero_nontrivial_iff_int lam).mp hcon)

end GaloisForLFunctions.HTGeometry.BorelWeil

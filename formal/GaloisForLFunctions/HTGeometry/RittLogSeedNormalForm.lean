import GaloisForLFunctions.HTGeometry.RittEigenPowerNormalForm

/-!
# The normal form of a differentially algebraic affine connection

Let `u` be an affine connection of a Ritt frame (`σ u = ρ⁻¹u + b`, `b = −dρ/ρ²`) with
eigen-coordinate
`v` (`σ v = ρ⁻¹v`, `d v = u·v`), for a map that is neither affine (`b ≠ 0`) nor Möbius
(`b₁ ≠ b²/2`).  If `u` is differentially algebraic, exactly one of the following normal forms holds:

1. a power `v^M`, `M ≥ 1`, lies in the base;
2. `u + c·v` lies in the base for some shift-fixed `c` — an invariant affine connection;
3. `d u − u²/2 = γ + κ·v²` with `γ, κ` in the base and `κ` shift-fixed — an invariant projective
   connection.

The proof takes the first jet `d^n u` algebraic over the lower ones.  If `v` is transcendental over
the jet field, the shift symmetry forces `n ≤ 1`: `n = 0` is form 2 with `c = 0`, and `n = 1` gives
`d u = u²/2 + γ`, form 3 with `κ = 0`.  If `v` is algebraic over the jet field, the eigen-power
analysis gives the three forms directly.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (Fr : RittFrame K L)

/-- Transcendence over the jet field implies transcendence over the jet ring. -/
theorem transcendental_adjoin_of_transcendental {u a : L} {n : ℕ}
    (htr : Transcendental ↥(Fr.jetPrefixField u n) a) :
    Transcendental ↥(Algebra.adjoin K (Set.range (Fr.jetFamily u n))) a := by
  intro halg
  apply htr
  obtain ⟨p, hp0, hp⟩ := halg
  have hsub : Algebra.adjoin K (Set.range (Fr.jetFamily u n))
      ≤ (Fr.jetPrefixField u n).toSubalgebra := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact Fr.jet_mem_jetPrefixField j.isLt
  let ι : ↥(Algebra.adjoin K (Set.range (Fr.jetFamily u n))) →+* ↥(Fr.jetPrefixField u n) :=
    (Subalgebra.inclusion hsub).toRingHom
  have hι : Function.Injective ι := Subalgebra.inclusion_injective hsub
  refine ⟨p.map ι, (Polynomial.map_ne_zero_iff hι).mpr hp0, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  rw [Polynomial.aeval_def] at hp
  have hcomp : (algebraMap (↥(Fr.jetPrefixField u n)) L).comp ι
      = algebraMap (↥(Algebra.adjoin K (Set.range (Fr.jetFamily u n)))) L := by
    ext; rfl
  rw [hcomp]
  exact hp

/-- **Jets below the first algebraic one are independent.** -/
theorem algebraicIndependent_jetFamily_of_forall_transcendental {u : L} :
    ∀ n : ℕ, (∀ j < n, Transcendental ↥(Fr.jetPrefixField u j) (Fr.d^[j] u)) →
      AlgebraicIndependent K (Fr.jetFamily u n) := by
  intro n
  induction n with
  | zero => intro _; exact algebraicIndependent_empty_type
  | succ n ih =>
      intro htr
      have hind := ih fun j hj => htr j (by omega)
      have hopt : AlgebraicIndependent K
          (fun o : Option (Fin n) => o.elim (Fr.d^[n] u) (Fr.jetFamily u n)) :=
        AlgebraicIndependent.option_iff.mpr
          ⟨hind, Fr.transcendental_adjoin_of_transcendental (htr n (by omega))⟩
      have hcomp := hopt.comp finSuccEquivLast finSuccEquivLast.injective
      convert hcomp using 1
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [jetFamily]
      · simp [jetFamily]

/-- The first-order term of the line identity of a collapse of order one. -/
theorem pderiv_zero_eq_of_lineSubst_collapse_one {F : MvPolynomial (Fin 1) K} {k : K}
    (hF : aeval (triLineSubst (bellField K 1)) F
      = rename Fin.succ F + X 0 * rename Fin.succ (connBell K 1 1) - C k * X 0 ^ 2) :
    pderiv 0 F = X 0 := by
  classical
  have h := congrArg (pderiv (0 : Fin 2)) hF
  rw [derivation_aeval_eq_sum_pderiv, Fin.sum_univ_one, pderiv_zero_lineSubst, map_sub, map_add,
    pderiv_zero_rename_succ, zero_add, Derivation.leibniz, pderiv_X_self,
    pderiv_zero_rename_succ, Derivation.leibniz, Derivation.leibniz_pow, pderiv_X_self,
    pderiv_C] at h
  have h' := congrArg (aeval (Fin.cons (0 : MvPolynomial (Fin 1) K)
    (X : Fin 1 → MvPolynomial (Fin 1) K))) h
  simp only [map_mul, map_sub, map_add, aeval_zero_lineSubst, aeval_zero_rename_succ,
    smul_eq_mul, map_nsmul, map_pow, aeval_X, Fin.cons_zero, aeval_C, mul_one, mul_zero,
    add_zero] at h'
  rw [bellField, Fin.val_zero, connBell_zero, mul_one, connBell_one (by omega)] at h'
  simpa using h'

/-- **The normal form of a differentially algebraic affine connection.** -/
theorem normalForm_of_differentiallyAlgebraic [CharZero K] [DecidableEq K] {u v : L} {b : K}
    (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2) (hb0 : b ≠ 0) (hS : Fr.logConst b 1 ≠ b ^ 2 / 2)
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hv : Fr.σ v = algebraMap K L Fr.ρ⁻¹ * v) (hv0 : v ≠ 0) (hdv : Fr.d v = u * v)
    (hDA : ∃ n : ℕ, IsAlgebraic ↥(Fr.jetPrefixField u n) (Fr.d^[n] u)) :
    (∃ M : ℕ, 0 < M ∧ ∃ k : K, v ^ M = algebraMap K L k) ∨
      (∃ c a : K, Fr.ψ c = c ∧ u + algebraMap K L c * v = algebraMap K L a) ∨
      (∃ γ κ : K, Fr.ψ κ = κ ∧
        Fr.d u - u ^ 2 / 2 = algebraMap K L γ + algebraMap K L κ * v ^ 2) := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.find hDA := ⟨_, rfl⟩
  have halg : IsAlgebraic ↥(Fr.jetPrefixField u n) (Fr.d^[n] u) := hn ▸ Nat.find_spec hDA
  have hind : AlgebraicIndependent K (Fr.jetFamily u n) :=
    Fr.algebraicIndependent_jetFamily_of_forall_transcendental n fun j hj halgj =>
      Nat.find_min hDA (hn ▸ hj) halgj
  by_cases htr : Transcendental ↥(Fr.jetPrefixField u n) v
  · have hle := Fr.le_one_of_transcendental_eigen hb hb0 hS hu hv hv0 hdv hind halg htr
    obtain ⟨F, hF⟩ := Fr.exists_polynomial_jet_of_transcendental hu hv hv0 hind halg htr
    have hind' := Fr.algebraicIndependent_cons_of_transcendental hind htr
    clear hn
    rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · -- the connection lies in the base
      refine Or.inr (Or.inl ⟨0, coeff 0 F, map_zero _, ?_⟩)
      rw [map_zero, zero_mul, add_zero]
      rw [eq_C_of_isEmpty F, aeval_C] at hF
      simpa using hF
    · -- the Schwarzian lies in the base
      obtain ⟨k, -, hk⟩ := Fr.triLineSubst_collapse hu hv hv0 hdv hind hind' hF
      have hzero := fun e (he : e ≠ 0) (hw : Finsupp.weight (jetWeight 1) e ≠ 1 + 1) =>
        coeff_eq_zero_of_lineSubst_collapse hk he hw
      set γ := coeff 0 F with hγ
      set F₁ := F - C γ with hF₁def
      have hhom : IsWeightedHomogeneous (jetWeight 1) F₁ 2 := by
        intro d hd
        rw [hF₁def, coeff_sub, coeff_C] at hd
        by_cases hd0 : d = 0
        · subst hd0
          rw [if_pos rfl, hγ, sub_self] at hd
          exact absurd rfl hd
        · rw [if_neg (Ne.symm hd0), sub_zero] at hd
          by_contra hw
          exact hd (hzero d hd0 hw)
      have hF₁ := eq_of_isWeightedHomogeneous_two_one hhom
      set α := coeff (Finsupp.single (0 : Fin 1) 2) F₁ with hα
      have hpd := pderiv_zero_eq_of_lineSubst_collapse_one hk
      have hFsplit : F = C γ + C α * X 0 ^ 2 := by rw [← hF₁]; rw [hF₁def]; ring
      have hα2 : α = 1 / 2 := by
        rw [hFsplit, map_add, pderiv_C, zero_add, Derivation.leibniz, Derivation.leibniz_pow,
          pderiv_X_self, pderiv_C] at hpd
        have h2 := congrArg (MvPolynomial.eval (fun _ => (1 : K))) hpd
        simp at h2
        field_simp
        linear_combination h2
      refine Or.inr (Or.inr ⟨γ, 0, map_zero _, ?_⟩)
      have hdu : Fr.d u = Fr.d^[1] u := rfl
      rw [hdu, hF, hFsplit, map_add, map_mul, map_pow, aeval_C, aeval_C, aeval_X, hα2, map_zero,
        zero_mul, add_zero]
      haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
      simp only [map_div₀, map_one, map_ofNat]
      have hu0 : Fr.jetFamily u 1 0 = u := rfl
      rw [hu0]
      ring
  · have halgv : IsAlgebraic ↥(Fr.jetPrefixField u n) v := by
      by_contra h
      exact htr h
    exact Fr.normalForm_of_isAlgebraic_eigen hb hb0 hS hu hv hv0 hdv hind halgv

end RittFrame

end

end GaloisForLFunctions.HTGeometry

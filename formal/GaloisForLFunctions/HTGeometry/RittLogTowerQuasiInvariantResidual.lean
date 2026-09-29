import GaloisForLFunctions.HTGeometry.RittConnectionShiftSymmetry

/-!
# The scale-invariant residual with a constant defect, and the collapse order

The residual of a collapse of the affine logarithmic tower is a weighted homogeneous polynomial `F`
of weight `n + 1` with shift-fixed coefficients.  When the collapsing polynomial also carries a
constant term `γ`, the residual identity acquires a constant:

`towerShift F = ρ^{−(n+1)}·F + δ_n + e`,   `e = ρ^{−(n+1)}γ − ψ(γ)`.

After the weight rescaling, `e` only enters the substitution family at order `ν^{n+1}`.  For
`n ≥ 2` the orders `ν` and `ν²` are untouched, so the generators `z²∂` and `z³∂` still annihilate
the
top-jet graph, which is impossible.

Combined with the shift symmetry (every non-constant monomial of the collapsing polynomial has
weight
`n + 1` as soon as the eigen-coordinate `v` is independent of the jets), a collapse with an
independent eigen-coordinate has order at most one.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (Fr : RittFrame K L)

/-- **The rescaled collapse with a constant defect.** -/
theorem aeval_rescaledTowerRow_const (b : K) {n : ℕ} {F : MvPolynomial (Fin n) K}
    (hψ : ∀ d, Fr.ψ (coeff d F) = coeff d F)
    (hF : F = weightedHomogeneousComponent (jetWeight n) (n + 1) F) {e : K}
    (hpoly : Fr.towerShift b n F = C ((Fr.ρ ^ (n + 1))⁻¹) * F + Fr.defectPoly b n + C e)
    {μ : K} (hμ : μ ≠ 0) :
    aeval (fun j : Fin n =>
        C (μ ^ ((j : ℕ) + 1)) * jetWeightScale n (Fr.ρ / μ) (Fr.towerRow b n j)) F
      = F + C (μ ^ (n + 1)) * jetWeightScale n (Fr.ρ / μ) (Fr.towerRow b n n)
        + C (μ ^ (n + 1) * e) := by
  have hρ := Fr.ρ_ne
  have hcomp : (aeval fun j : Fin n =>
        C (μ ^ ((j : ℕ) + 1)) * jetWeightScale n (Fr.ρ / μ) (Fr.towerRow b n j))
      = (jetWeightScale n (Fr.ρ / μ)).comp
          ((aeval (Fr.towerSub b n)).comp (jetWeightScale n μ)) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    have hws : jetWeightScale n μ (X j) = C (μ ^ ((j : ℕ) + 1)) * X j := by
      rw [jetWeightScale, aeval_X]
    rw [aeval_X, AlgHom.comp_apply, AlgHom.comp_apply, hws, map_mul, aeval_C, algebraMap_eq,
      aeval_X, map_mul, jetWeightScale_C, towerSub_eq_towerRow]
  have hsub : aeval (Fr.towerSub b n) F
      = C ((Fr.ρ ^ (n + 1))⁻¹) * F + Fr.defectPoly b n + C e := by
    rw [← Fr.towerShift_eq_aeval_of_fixed b hψ, hpoly]
  have hscal : μ ^ (n + 1) * (Fr.ρ ^ (n + 1))⁻¹ * (Fr.ρ / μ) ^ (n + 1) = 1 := by
    rw [div_pow]
    field_simp
  rw [hcomp, AlgHom.comp_apply, AlgHom.comp_apply, jetWeightScale_of_weightedHomogeneous hF,
    map_mul, aeval_C, algebraMap_eq, hsub, map_mul, map_add, map_add, map_mul, jetWeightScale_C,
    jetWeightScale_C, jetWeightScale_C, jetWeightScale_of_weightedHomogeneous hF,
    defectPoly_eq_towerRow]
  have hF1 : C (μ ^ (n + 1)) * (C ((Fr.ρ ^ (n + 1))⁻¹) * (C ((Fr.ρ / μ) ^ (n + 1)) * F)) = F := by
    rw [← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, hscal, C_1, one_mul]
  rw [show C (μ ^ (n + 1) * e) = C (μ ^ (n + 1)) * C e from C_mul]
  linear_combination hF1

/-- **The rescaled family moves the top-jet graph by a constant of order `ν^{n+1}`.** -/
theorem towerFamily_quasiInvariant (b : K) {n : ℕ} {F : MvPolynomial (Fin n) K}
    (hψ : ∀ d, Fr.ψ (coeff d F) = coeff d F)
    (hF : F = weightedHomogeneousComponent (jetWeight n) (n + 1) F) {e : K}
    (hpoly : Fr.towerShift b n F = C ((Fr.ρ ^ (n + 1))⁻¹) * F + Fr.defectPoly b n + C e)
    {μ : K} (hμ : μ ≠ 0) :
    aeval (fun J => (Fr.towerFamily b n J).eval (C μ))
        (X (Fin.last n) - rename Fin.castSucc F)
      = X (Fin.last n) - rename Fin.castSucc F - C (μ ^ (n + 1) * e) := by
  have hρ := Fr.ρ_ne
  set N : Fin n → MvPolynomial (Fin n) K :=
    fun j => C (μ ^ ((j : ℕ) + 1)) * jetWeightScale n (Fr.ρ / μ) (Fr.towerRow b n j) with hN
  have hcast : (fun J => (Fr.towerFamily b n J).eval (C μ)) ∘ Fin.castSucc
      = fun j : Fin n => rename Fin.castSucc (N j) := by
    funext j
    simp only [Function.comp_apply]
    rw [Fr.eval_towerFamily b n _ hμ, Fin.val_castSucc, Fr.logCoeff_eq_zero_of_lt _ _ j.isLt,
      mul_zero, C_0, zero_mul, add_zero]
  have hren : aeval (fun j : Fin n => rename Fin.castSucc (N j)) F
      = rename Fin.castSucc (aeval N F) := by
    have h := MvPolynomial.comp_aeval N
      (rename Fin.castSucc : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n + 1)) K)
    exact (congrArg (fun f => f F) h).symm
  rw [map_sub, aeval_X, aeval_rename, hcast, hren, Fr.eval_towerFamily b n _ hμ, Fin.val_last,
    Fr.logCoeff_diag, mul_inv_cancel₀ (pow_ne_zero _ hρ), C_1, one_mul, hN,
    Fr.aeval_rescaledTowerRow_const b hψ hF hpoly hμ, map_add, map_add, rename_C]
  ring

/-- **The scale-invariant residual with a constant defect is impossible in order at least two.** -/
theorem false_of_scaleInvariant_collapse_const [CharZero K] {b : K}
    (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2) (hb0 : b ≠ 0) (hS : Fr.logConst b 1 ≠ b ^ 2 / 2)
    {n : ℕ} (hn : 2 ≤ n) {F : MvPolynomial (Fin n) K}
    (hF : F = weightedHomogeneousComponent (jetWeight n) (n + 1) F)
    (hψ : ∀ d, Fr.ψ (coeff d F) = coeff d F) {e : K}
    (hpoly : Fr.towerShift b n F = C ((Fr.ρ ^ (n + 1))⁻¹) * F + Fr.defectPoly b n + C e) :
    False := by
  set Φ : MvPolynomial (Fin (n + 1)) K := X (Fin.last n) - rename Fin.castSucc F with hΦ
  have hfam : familySubst (Fr.towerFamily b n) Φ
      = Polynomial.C Φ - Polynomial.monomial (n + 1) (C e) := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.Infinite.mono ?_ (((Set.finite_singleton (0 : K)).infinite_compl).image
      (C_injective (Fin (n + 1)) K).injOn)
    rintro _ ⟨μ, hμ, rfl⟩
    show Polynomial.eval _ _ = Polynomial.eval _ _
    rw [eval_familySubst, Fr.towerFamily_quasiInvariant b hψ hF hpoly hμ, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_monomial, ← map_pow, ← C_mul, mul_comm e]
  have hc1 : (familySubst (Fr.towerFamily b n) Φ).coeff 1 = 0 := by
    rw [hfam, Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_monomial,
      if_neg one_ne_zero, if_neg (by omega), sub_zero]
  have hc2 : (familySubst (Fr.towerFamily b n) Φ).coeff 2 = 0 := by
    rw [hfam, Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_monomial,
      if_neg two_ne_zero, if_neg (by omega), sub_zero]
  have h1 : familyDerivOne (Fr.towerFamily_coeff_zero b n) Φ = 0 := by
    rw [familyDerivOne_apply, hc1]
  have h2 : familyDerivTwo (Fr.towerFamily_coeff_zero b n) Φ = 0 := by
    rw [familyDerivTwo_apply, hc2, h1, map_zero, smul_zero, sub_zero]
  rw [Fr.familyDerivOne_towerFamily hb, Derivation.smul_apply, smul_eq_zero] at h1
  rw [Fr.familyDerivTwo_towerFamily hb, Derivation.smul_apply, smul_eq_zero] at h2
  exact not_connectionGen_invariant_graph F
    ⟨h1.resolve_left hb0, h2.resolve_left (sub_ne_zero.mpr hS)⟩

/-! ### The collapse order with an independent eigen-coordinate -/

/-- **A collapse with an independent eigen-coordinate has order at most one.**  If the jets of
the connection `u` collapse at order `n`, and the eigen-coordinate `v` (`d v = u·v`) is
algebraically independent of those jets, then `n ≤ 1` — for any map that is neither affine
(`b₀ ≠ 0`) nor Möbius (`b₁ ≠ b₀²/2`). -/
theorem le_one_of_collapse_of_independent_eigen [CharZero K] {u v : L} {b : K}
    (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2) (hb0 : b ≠ 0) (hS : Fr.logConst b 1 ≠ b ^ 2 / 2)
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hv : Fr.σ v = algebraMap K L Fr.ρ⁻¹ * v) (hv0 : v ≠ 0) (hdv : Fr.d v = u * v)
    {n : ℕ} (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    (hind' : AlgebraicIndependent K (Fin.cons v (Fr.jetFamily u n) : Fin (n + 1) → L))
    {F : MvPolynomial (Fin n) K} (hcol : Fr.d^[n] u = aeval (Fr.jetFamily u n) F) : n ≤ 1 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨k, -, hk⟩ := Fr.triLineSubst_collapse hu hv hv0 hdv hind hind' hcol
  have hzero := fun e (he : e ≠ 0) (hw : Finsupp.weight (jetWeight n) e ≠ n + 1) =>
    coeff_eq_zero_of_lineSubst_collapse hk he hw
  set γ := coeff 0 F with hγ
  set F₁ := F - C γ with hF₁def
  have hcoeff₁ : ∀ e, coeff e F₁ = if e = 0 then 0 else coeff e F := by
    intro e
    by_cases he : e = 0
    · subst he
      rw [if_pos rfl, hF₁def, coeff_sub, coeff_C, if_pos rfl, hγ, sub_self]
    · rw [if_neg he, hF₁def, coeff_sub, coeff_C, if_neg (Ne.symm he), sub_zero]
  -- the collapse relation
  have hrel : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L (Fr.ρ ^ (n + 1))⁻¹ * aeval (Fr.jetFamily u n) F
        + aeval (Fr.jetFamily u n) (Fr.defectPoly b n) := by
    rw [← hcol, Fr.sigma_jet_eq_defect hu n, aeval_defectPoly]
  have hpoly := Fr.towerShift_eq_of_collapse hu hind hrel
  have hwle : WLe n F (n + 1) := by
    intro e he
    by_cases he0 : e = 0
    · subst he0; simp
    · by_contra hlt
      exact (mem_support_iff.mp he) (hzero e he0 (by omega))
  have hrel' : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L (Fr.ρ ^ (n + 1))⁻¹ * aeval (Fr.jetFamily u n) F
        + Fr.towerDefect u b n := by
    rw [hrel, aeval_defectPoly]
  -- the residual `F₁`
  have hψ₁ : ∀ d, Fr.ψ (coeff d F₁) = coeff d F₁ := by
    intro d
    rw [hcoeff₁]
    split_ifs with hd
    · exact map_zero _
    · by_cases hw : Finsupp.weight (jetWeight n) d = n + 1
      · exact Fr.psi_fixed_of_collapse_top hu hind hwle hrel' hw
      · rw [hzero d hd hw, map_zero]
  have hhom : IsWeightedHomogeneous (jetWeight n) F₁ (n + 1) := by
    intro d hd
    rw [hcoeff₁] at hd
    split_ifs at hd with hd0
    · exact absurd rfl hd
    · by_contra hw
      exact hd (hzero d hd0 hw)
  have hF₁ : F₁ = weightedHomogeneousComponent (jetWeight n) (n + 1) F₁ :=
    (weightedHomogeneousComponent_eq_self hhom).symm
  have hpoly₁ : Fr.towerShift b n F₁ = C ((Fr.ρ ^ (n + 1))⁻¹) * F₁ + Fr.defectPoly b n
      + C ((Fr.ρ ^ (n + 1))⁻¹ * γ - Fr.ψ γ) := by
    have h : Fr.towerShift b n F₁ = Fr.towerShift b n F - C (Fr.ψ γ) := by
      rw [hF₁def, map_sub, towerShift_C]
    rw [h, hpoly, hF₁def, map_sub, C_mul]
    ring
  exact Fr.false_of_scaleInvariant_collapse_const hb hb0 hS hn hF₁ hψ₁ hpoly₁

end RittFrame

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.RittLogSeedTranscendentalEigen

/-!
# An algebraic eigen-coordinate has a power in the jet ring

In a Ritt frame let `v` be a shift eigenvector, `σ v = a·v`, algebraic over a shift-stable
intermediate field `E`.  Its minimal polynomial `P` over `E` is carried by the shift to a monic
polynomial of the same degree vanishing at `v` — the image of `P` under the shift, with roots scaled
by `a⁻¹` — so the two agree.  Comparing constant terms, `σ p₀ = a^D·p₀`, and `p₀/v^D` is
shift-fixed:

`v^D ∈ E`.

For the jet field of an affine connection the reduced denominator of `v^D` is a power of `v`, so
some
power `v^M`, `M ≥ 1`, is a *polynomial* in the jets.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (Fr : RittFrame K L) {n : ℕ}

/-- The shift restricted to a shift-stable intermediate field. -/
def sigmaRestrict (E : IntermediateField K L) (hE : ∀ x ∈ E, Fr.σ x ∈ E) : ↥E →+* ↥E where
  toFun a := ⟨Fr.σ (a : L), hE (a : L) a.2⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

theorem algebraMap_sigmaRestrict (E : IntermediateField K L) (hE : ∀ x ∈ E, Fr.σ x ∈ E)
    (a : ↥E) : algebraMap ↥E L (Fr.sigmaRestrict E hE a) = Fr.σ (algebraMap ↥E L a) := rfl

/-- **Multiplicative rigidity.**  A shift eigenvector algebraic over a shift-stable intermediate
field has a positive power in that field. -/
theorem exists_pow_mem_of_isAlgebraic_eigen {E : IntermediateField K L}
    (hE : ∀ x ∈ E, Fr.σ x ∈ E) {v : L} {a : K} (ha : a ≠ 0) (hv0 : v ≠ 0)
    (hv : Fr.σ v = algebraMap K L a * v) (halg : IsAlgebraic ↥E v) :
    ∃ D : ℕ, 0 < D ∧ v ^ D ∈ E := by
  classical
  have hint : IsIntegral ↥E v := halg.isIntegral
  set σE := Fr.sigmaRestrict E hE with hσE
  have hσEinj : Function.Injective σE := σE.injective
  set P := minpoly (↥E) v with hP
  set D := P.natDegree with hD
  have hDpos : 0 < D := minpoly.natDegree_pos hint
  set aE : ↥E := ⟨algebraMap K L a, IntermediateField.algebraMap_mem _ _⟩ with haE
  have haE0 : aE ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    exact ((map_ne_zero_iff _ (algebraMap K L).injective).mpr ha) this
  set q := P.map σE with hq
  have hqdeg : q.natDegree = D := Polynomial.natDegree_map_eq_of_injective hσEinj _
  have hqroot : Polynomial.eval₂ (algebraMap ↥E L) (algebraMap ↥E L aE * v) q = 0 := by
    have hcomp : (algebraMap ↥E L).comp σE = Fr.σ.comp (algebraMap ↥E L) := by
      ext x; rfl
    rw [hq, Polynomial.eval₂_map, hcomp]
    have h1 : algebraMap ↥E L aE * v = Fr.σ v := by rw [hv]; rfl
    rw [h1, ← Polynomial.hom_eval₂]
    have h2 : Polynomial.eval₂ (algebraMap ↥E L) v P = 0 := minpoly.aeval _ _
    rw [h2, map_zero]
  set Q := q.scaleRoots aE⁻¹ with hQ
  have hQroot : Polynomial.aeval v Q = 0 := by
    rw [Polynomial.aeval_def]
    have hv' : v = algebraMap ↥E L aE⁻¹ * (algebraMap ↥E L aE * v) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ haE0, map_one, one_mul]
    rw [hv', hQ, Polynomial.scaleRoots_eval₂_mul, hqroot, mul_zero]
  have hQdeg : Q.natDegree = D := by rw [hQ, Polynomial.natDegree_scaleRoots, hqdeg]
  have hQlead : Q.coeff D = 1 := by
    rw [hQ, Polynomial.coeff_scaleRoots, hqdeg, Nat.sub_self, pow_zero, mul_one, hq,
      Polynomial.coeff_map]
    have hmon : P.coeff D = 1 := (minpoly.monic hint).coeff_natDegree
    rw [hmon, map_one]
  have hQne : Q ≠ 0 := by
    intro h0
    rw [h0, Polynomial.coeff_zero] at hQlead
    exact zero_ne_one hQlead
  have hQP : Q = P := by
    by_contra hne
    have hdeg : Q.degree = P.degree := by
      rw [Polynomial.degree_eq_natDegree hQne,
        Polynomial.degree_eq_natDegree (minpoly.ne_zero hint),
        hQdeg]
    have hlc : Q.leadingCoeff = P.leadingCoeff := by
      rw [Polynomial.leadingCoeff, hQdeg, hQlead, (minpoly.monic hint).leadingCoeff]
    have hlt := Polynomial.degree_sub_lt hdeg hQne hlc
    have hle := minpoly.degree_le_of_ne_zero (↥E) v (sub_ne_zero.mpr hne)
      (by rw [map_sub, hQroot, minpoly.aeval, sub_zero])
    rw [hdeg] at hlt
    exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)
  have h0 : σE (P.coeff 0) * aE⁻¹ ^ D = P.coeff 0 := by
    have := congrArg (fun p : Polynomial ↥E => p.coeff 0) hQP
    rw [hQ, Polynomial.coeff_scaleRoots, hqdeg, Nat.sub_zero, hq, Polynomial.coeff_map] at this
    exact this
  set p0 : L := ((P.coeff 0 : ↥E) : L) with hp0def
  have hp0 : p0 ≠ 0 := by
    intro h
    exact minpoly.coeff_zero_ne_zero hint hv0 (Subtype.ext h)
  have hσp0 : Fr.σ p0 = algebraMap K L a ^ D * p0 := by
    have h := congrArg (fun x : ↥E => (x : L)) h0
    simp only [IntermediateField.coe_mul, IntermediateField.coe_pow, IntermediateField.coe_inv]
      at h
    have h' : Fr.σ p0 * ((algebraMap K L a)⁻¹) ^ D = p0 := h
    have haL : algebraMap K L a ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr ha
    calc Fr.σ p0 = (Fr.σ p0 * ((algebraMap K L a)⁻¹) ^ D) * algebraMap K L a ^ D := by
          rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ haL, one_pow, mul_one]
      _ = algebraMap K L a ^ D * p0 := by rw [h']; ring
  have hvD : v ^ D ≠ 0 := pow_ne_zero _ hv0
  have hfix : Fr.σ (p0 / v ^ D) = p0 / v ^ D := by
    have haL : algebraMap K L a ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr ha
    rw [map_div₀, hσp0, map_pow, hv, mul_pow]
    field_simp
  obtain ⟨c, hc⟩ := Fr.fixed _ hfix
  have hc0 : algebraMap K L c ≠ 0 := by
    rw [hc]
    exact div_ne_zero hp0 hvD
  refine ⟨D, hDpos, ?_⟩
  have : v ^ D = p0 / algebraMap K L c := by
    rw [hc]
    field_simp
  rw [this]
  exact div_mem (P.coeff 0).2 (IntermediateField.algebraMap_mem _ _)

/-- **Some power of an algebraic eigen-coordinate is a polynomial in the jets.** -/
theorem exists_pow_eq_aeval_of_isAlgebraic [DecidableEq K] {u v : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hv : Fr.σ v = algebraMap K L Fr.ρ⁻¹ * v) (hv0 : v ≠ 0)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    (halg : IsAlgebraic ↥(Fr.jetPrefixField u n) v) :
    ∃ M : ℕ, 0 < M ∧ ∃ Q : MvPolynomial (Fin n) K, v ^ M = aeval (Fr.jetFamily u n) Q := by
  obtain ⟨D, hD, hvD⟩ := Fr.exists_pow_mem_of_isAlgebraic_eigen
    (Fr.sigma_mem_affineJetPrefixField hu n) (inv_ne_zero Fr.ρ_ne) hv0 hv halg
  obtain ⟨A, B, hB, hrel, hAB⟩ := Fr.exists_reduced_fraction_of_mem_jetPrefixField hind hvD
  have hσ : Fr.σ (v ^ D) = algebraMap K L (Fr.ρ⁻¹ ^ D) * v ^ D
      + aeval (Fr.jetFamily u n) (0 : MvPolynomial (Fin n) K) := by
    rw [map_zero, add_zero, map_pow, hv, mul_pow, map_pow]
  obtain ⟨μ', hμ'⟩ := Fr.towerShift_denominator hu hind hB hrel hAB
    (pow_ne_zero _ (inv_ne_zero Fr.ρ_ne)) hσ
  obtain ⟨k, W, hk, hBk⟩ := Fr.aeval_eq_of_towerShift_eigen hu hv hv0 hind hB hμ'
  refine ⟨D + W, by omega, C k⁻¹ * A, ?_⟩
  have hkL : algebraMap K L k ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hk
  rw [map_mul, aeval_C, ← hAB, hBk, pow_add, map_inv₀]
  field_simp

end RittFrame

end

end GaloisForLFunctions.HTGeometry

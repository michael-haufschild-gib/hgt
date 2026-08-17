import GaloisForLFunctions.HTGeometry.PrimeValuationLeadingEchelon

/-!
# Infinite-support prime-valuation leading-echelon law

The leading-echelon law of `PrimeValuationLeadingEchelon` requires the private valuation
coefficient of each source to be nonzero at *every* prime.  A finite differential-translation
filter applied to a prime source multiplies each prime coefficient by the value of a fixed
exponential polynomial at `log p`, and that value can vanish: at up to `N - 1` primes for real
shifts, and on a possibly infinite (but logarithmically sparse) set for complex shifts.

This file weakens the hypothesis to "infinitely many primes carry a nonzero private
coefficient".  The only step of the original argument that uses the pointwise hypothesis is the
tail-independence of the weighted jet block; and tail independence is a statement modulo finite
support, so it survives once the weight is nonzero infinitely often and the unweighted block is a
polynomial family in the injective rotated prime clock.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Matrix
open scoped Differential

noncomputable section

set_option maxHeartbeats 1000000

/-- The polynomial assembled from a finite complex coefficient vector. -/
noncomputable def finPoly {m : ℕ} (δ : Fin (m + 1) → ℂ) : Polynomial ℂ :=
  ∑ k : Fin (m + 1), Polynomial.C (δ k) * Polynomial.X ^ (k : ℕ)

theorem coeff_finPoly {m : ℕ} (δ : Fin (m + 1) → ℂ) (j : Fin (m + 1)) :
    (finPoly δ).coeff (j : ℕ) = δ j := by
  classical
  unfold finPoly
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have hne : (j : ℕ) ≠ (k : ℕ) := fun h => hkj (Fin.ext h.symm)
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem finPoly_ne_zero {m : ℕ} {δ : Fin (m + 1) → ℂ} (hδ : δ ≠ 0) : finPoly δ ≠ 0 := by
  intro hzero
  apply hδ
  funext j
  have := coeff_finPoly δ j
  rw [hzero] at this
  simpa using this.symm

theorem eval_finPoly {m : ℕ} (δ : Fin (m + 1) → ℂ) (z : ℂ) :
    (finPoly δ).eval z = ∑ k : Fin (m + 1), δ k * z ^ (k : ℕ) := by
  unfold finPoly
  rw [Polynomial.eval_finsetSum]
  simp

/-- A nonzero polynomial in the rotated prime clock vanishes at only finitely many primes. -/
theorem finite_setOf_clockPoly_eq_zero {m : ℕ} {δ : Fin (m + 1) → ℂ} (hδ : δ ≠ 0)
    {K : ℂ} (hK : K ≠ 0) :
    {p : Nat.Primes | ∑ k : Fin (m + 1), δ k * (K * rotatedPrimeLogClock p) ^ (k : ℕ) = 0}.Finite := by
  classical
  have hroots : {z : ℂ | (finPoly δ).IsRoot z}.Finite :=
    Polynomial.finite_setOf_isRoot (finPoly_ne_zero hδ)
  have hinj : Function.Injective (fun p : Nat.Primes => K * rotatedPrimeLogClock p) := by
    intro p q hpq
    exact rotatedPrimeLogClock_injective (mul_left_cancel₀ hK hpq)
  have hsub : {p : Nat.Primes |
      ∑ k : Fin (m + 1), δ k * (K * rotatedPrimeLogClock p) ^ (k : ℕ) = 0} =
      (fun p : Nat.Primes => K * rotatedPrimeLogClock p) ⁻¹' {z : ℂ | (finPoly δ).IsRoot z} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Polynomial.IsRoot, eval_finPoly]
  rw [hsub]
  exact hroots.preimage hinj.injOn

/-- The rectangle index type of a single jet block. -/
abbrev jetBlockIndex (m : ℕ) : Type := Unit × (Unit × Fin (m + 1))

/-- The canonical equivalence between a jet block index and its jet order. -/
def jetBlockEquiv (m : ℕ) : Fin (m + 1) ≃ jetBlockIndex m where
  toFun k := ((), ((), k))
  invFun x := x.2.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Infinite-support leading-echelon jet theorem.**  The private valuation coefficient need only
be nonzero at infinitely many primes; finitely many, or even a zero-density set of, cancellations
in the private layer cannot destroy differential independence. -/
theorem primeValuationLeadingEchelonJets_algebraicIndependent_of_infinitePrimeDependent
    {d : ℕ} [Nonempty (Fin d)]
    (g : Fin d → ArithmeticFunction ℂ)
    (e : Fin d → ℕ) (he : Function.Injective e)
    (c : Fin d → Nat.Primes → ℂ) (hc : ∀ r, {p : Nat.Primes | c r p ≠ 0}.Infinite)
    (hsupport : ∀ r, SupportedOnPositivePrimePowers (g r))
    (hprivate : ∀ r s (p : Nat.Primes),
      g s ((p : ℕ) ^ (e r + 1)) = if r = s then c s p else 0)
    (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun x : Fin d × Fin (m + 1) =>
        rotatedLogArithmeticJet x.2 (g x.1)) := by
  classical
  let A : Fin d → Type := fun _ => jetBlockIndex m
  letI (r : Fin d) : Fintype (A r) := inferInstance
  letI (r : Fin d) : DecidableEq (A r) := inferInstance
  let a : ∀ r, A r → Nat.Primes → ℂ := fun r x p =>
    c r p * ((((e r + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ (x.2.2 : ℕ))
  have htail : ∀ r, TailCoefficientIndependent (a r) := by
    intro r γ hfin
    by_contra hγ
    set K : ℂ := ((e r + 1 : ℕ) : ℂ) with hKdef
    have hK : K ≠ 0 := by
      rw [hKdef]
      exact_mod_cast Nat.succ_ne_zero (e r)
    set δ : Fin (m + 1) → ℂ := fun k => γ (jetBlockEquiv m k) with hδdef
    have hδ : δ ≠ 0 := by
      intro hzero
      apply hγ
      funext x
      have hx : x = jetBlockEquiv m x.2.2 := rfl
      rw [hx]
      have := congrFun hzero x.2.2
      simpa [hδdef] using this
    have hsum : ∀ p : Nat.Primes,
        (∑ x : A r, γ x * a r x p)
          = c r p * ∑ k : Fin (m + 1), δ k * (K * rotatedPrimeLogClock p) ^ (k : ℕ) := by
      intro p
      rw [Finset.mul_sum]
      rw [← Equiv.sum_comp (jetBlockEquiv m) (fun x : A r => γ x * a r x p)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [a, hδdef, jetBlockEquiv, Equiv.coe_fn_mk, hKdef]
      ring
    have hbig : ({p : Nat.Primes | c r p ≠ 0} \
        {p : Nat.Primes | ∑ k : Fin (m + 1), δ k * (K * rotatedPrimeLogClock p) ^ (k : ℕ) = 0}
        : Set Nat.Primes).Infinite :=
      (hc r).sdiff (finite_setOf_clockPoly_eq_zero hδ hK)
    have hsubset : ({p : Nat.Primes | c r p ≠ 0} \
        {p : Nat.Primes | ∑ k : Fin (m + 1), δ k * (K * rotatedPrimeLogClock p) ^ (k : ℕ) = 0}
        : Set Nat.Primes) ⊆ {p | ∑ x : A r, γ x * a r x p ≠ 0} := by
      intro p hp
      simp only [Set.mem_sdiff, Set.mem_setOf_eq] at hp
      simp only [Set.mem_setOf_eq, hsum p]
      exact mul_ne_zero hp.1 hp.2
    exact (hbig.mono hsubset) hfin
  obtain ⟨q, hq, _havoid, hdet⟩ :=
    cofinitePrimePowerPacket_of_injective_layerExponents d A e he a htail
      ∅ Set.finite_empty
  let I := Σ r, A r
  let exponent : I → ℕ := fun i => e i.1
  let sourceJet : I → ArithmeticFunction ℂ := fun x =>
    rotatedLogArithmeticJet x.2.2.2 (g x.1)
  let M : Matrix I I (ArithmeticFunction ℂ) := fun i j =>
    primeDeriv (q i).1 (sourceJet j)
  have hMsupport : ∀ i j, SupportedOnPrimeRay (q i) (M i j) := by
    intro i j
    exact primeDeriv_rotatedLogArithmeticJet_supportedOnPrimeRay
      (g j.1) (hsupport j.1) (q i) j.2.2.2
  have hcoeff :
      (fun i j => M i j ((q i : ℕ) ^ exponent i)) =
        primePowerBlockMatrix exponent
          (primePowerPacketCoefficientMatrix exponent
            (primePowerSigmaCoefficient a) q) := by
    funext i j
    rcases i with ⟨r, ⟨u, v, k⟩⟩
    rcases j with ⟨s, ⟨u', v', l⟩⟩
    simp only [M, sourceJet, exponent]
    rw [primeDeriv_rotatedLogArithmeticJet_apply_primePow]
    rw [hprivate r s (q ⟨r, (u, (v, k))⟩)]
    by_cases hrs : r = s
    · subst s
      rw [primePowerBlockMatrix, if_pos rfl]
      simp only [primePowerPacketCoefficientMatrix,
        primePowerSigmaCoefficient, a, if_true]
      ring
    · have hers : e r ≠ e s := fun h => hrs (he h)
      rw [if_neg hrs]
      simp only [mul_zero]
      rw [primePowerBlockMatrix, if_neg hers]
  have hMdet : M.det ≠ 0 := by
    apply primeRayMatrix_det_ne_zero q hq exponent M hMsupport
    rw [hcoeff]
    exact hdet
  have hAI : AlgebraicIndependent ℂ sourceJet := by
    refine algebraicIndependent_of_domain_jacobian
      (K := ℂ) (R := ArithmeticFunction ℂ)
      sourceJet (fun i => primeDeriv (q i).1)
      (fun i => primeDeriv_add (q i).1)
      (fun i => primeDeriv_mul (q i).1 (q i).2)
      (fun i => primeDeriv_algebraMap (q i).1 (q i).2)
      M hMdet ?_
    intro i j
    rfl
  let f : (Fin d × Fin (m + 1)) → I := fun x =>
    ⟨x.1, ((), ((), x.2))⟩
  have hf : Function.Injective f := by
    rintro ⟨r, k⟩ ⟨s, l⟩ h
    cases h
    rfl
  have hsub := hAI.comp f hf
  simpa only [Function.comp_apply, f, sourceJet] using! hsub

/-- **Infinite-support prime-valuation leading-echelon law.**  Differential independence over `ℂ`
survives arbitrary cancellation in the private valuation layer as long as infinitely many primes
keep a nonzero private coefficient. -/
theorem primeValuationLeadingEchelon_differentialIndependent_of_infinitePrimeDependent
    {d : ℕ} [Nonempty (Fin d)]
    (g : Fin d → ArithmeticFunction ℂ)
    (e : Fin d → ℕ) (he : Function.Injective e)
    (c : Fin d → Nat.Primes → ℂ) (hc : ∀ r, {p : Nat.Primes | c r p ≠ 0}.Infinite)
    (hsupport : ∀ r, SupportedOnPositivePrimePowers (g r))
    (hprivate : ∀ r s (p : Nat.Primes),
      g s ((p : ℕ) ^ (e r + 1)) = if r = s then c s p else 0) :
    GaloisForLFunctions.DifferentialIndependent ℂ
      (fun r => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (g r)) := by
  unfold GaloisForLFunctions.DifferentialIndependent
  simp_rw [differentialJet_algebraMap_rotatedLogArithmeticJet]
  let x : Fin d → ℕ → arithmeticFunctionFractionField := fun r k =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (rotatedLogArithmeticJet k (g r))
  apply algebraicIndependent_prod_nat_of_fin x
  intro m
  have hraw :=
    primeValuationLeadingEchelonJets_algebraicIndependent_of_infinitePrimeDependent
    g e he c hc hsupport hprivate m
  have hmap := hraw.map'
    (f := IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
    (IsFractionRing.injective (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
  simpa only [Function.comp_apply, x] using! hmap

end

end GaloisForLFunctions.HTGeometry

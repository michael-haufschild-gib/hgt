import GaloisForLFunctions.HTGeometry.GammaShiftClassLaw
import GaloisForLFunctions.HTGeometry.ExpSumGammaFieldRelation

/-!
# Solutions of a shifted Gamma relation of every phase rank

The finite phase law for shifted Gamma coefficients bounds the rational rank of the frequency module
of a strip almost periodic solution.  The bound depends on the relation, and it has to: a sum of `r`
exponentials with rationally independent frequencies satisfies a constant coefficient linear
differential equation of order `r`, and multiplying that equation by `Γ(s + λ)` turns each
coefficient into a one-term shifted Gamma monomial of the shape the law consumes.  The restriction
of the solution to a vertical line is a trigonometric polynomial whose frequency module has rank
exactly `r`.

So the hypothesis class of the shifted law is inhabited at every rank, and its finite bound is
attained.
-/

open Filter Set Topology Function

open scoped BigOperators BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {r : ℕ}

/-- **A shifted Gamma relation satisfied by an exponential sum.**  The annihilator of the frequency
packet, multiplied by `Γ(s + λ)`, is a relation linear in the jets with distinct exponent vectors
and nonzero scalar coefficients. -/
theorem exists_gammaShift_relation_expSum (a : Fin r → ℂ) (μ : Fin r → ℝ) (lam : ℝ) :
    ∃ (N : ℕ) (e : Fin N → Fin ((expSumChar μ).natDegree + 1) → ℕ) (cf : Fin N → ℂ),
      0 < N ∧ Function.Injective e ∧ (∀ α, cf α ≠ 0) ∧
      ∀ s : ℂ, ∑ α : Fin N, (cf α * Complex.Gamma (s + (lam : ℂ)))
        * ∏ i : Fin ((expSumChar μ).natDegree + 1),
            (iteratedDeriv (i : ℕ) (expSum a μ) s) ^ (e α i) = 0 := by
  classical
  set P : Polynomial ℂ := expSumChar μ with hP
  set S : Finset ℕ := P.support with hS
  set N : ℕ := S.card with hN
  set en : Fin N → ℕ := fun α => ((S.equivFin.symm α : {x // x ∈ S}) : ℕ) with hen
  have hmem : ∀ α, en α ∈ S := fun α => (S.equivFin.symm α).2
  have heninj : Function.Injective en := by
    intro α β hab
    have : (S.equivFin.symm α) = (S.equivFin.symm β) := Subtype.ext hab
    exact S.equivFin.symm.injective this
  have hle : ∀ α, en α < P.natDegree + 1 := by
    intro α
    have := Polynomial.le_natDegree_of_mem_supp (en α) (hmem α)
    omega
  have hNpos : 0 < N := by
    rw [hN, Finset.card_pos]
    refine ⟨P.natDegree, ?_⟩
    rw [hS, Polynomial.mem_support_iff]
    have hmonic : P.Monic := by
      rw [hP, expSumChar, expSumAnnihilator]
      exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
    rw [hmonic.coeff_natDegree]
    exact one_ne_zero
  set idx : Fin N → Fin (P.natDegree + 1) := fun α => ⟨en α, hle α⟩ with hidx
  refine ⟨N, fun α i => if i = idx α then 1 else 0, fun α => P.coeff (en α), hNpos, ?_, ?_, ?_⟩
  · intro α β hab
    have h : (if idx α = idx α then (1 : ℕ) else 0) = (if idx α = idx β then (1 : ℕ) else 0) :=
      congrFun hab (idx α)
    rw [if_pos rfl] at h
    have hidxeq : idx α = idx β := by
      by_contra hne
      rw [if_neg hne] at h
      exact absurd h one_ne_zero
    exact heninj (congrArg Fin.val hidxeq)
  · intro α
    have := hmem α
    rw [hS, Polynomial.mem_support_iff] at this
    exact this
  · intro s
    have hprod : ∀ α : Fin N,
        (∏ i : Fin (P.natDegree + 1),
          (iteratedDeriv (i : ℕ) (expSum a μ) s) ^ (if i = idx α then 1 else 0))
        = iteratedDeriv (en α) (expSum a μ) s := by
      intro α
      rw [Finset.prod_eq_single (idx α)]
      · rw [if_pos rfl, pow_one]
      · intro i _ hi
        rw [if_neg hi, pow_zero]
      · intro h
        exact absurd (Finset.mem_univ (idx α)) h
    rw [Finset.sum_congr rfl fun α _ => by rw [hprod α]]
    have hfactor : ∀ α : Fin N,
        (P.coeff (en α) * Complex.Gamma (s + (lam : ℂ))) * iteratedDeriv (en α) (expSum a μ) s
          = Complex.Gamma (s + (lam : ℂ))
            * (P.coeff (en α) * iteratedDeriv (en α) (expSum a μ) s) := by
      intro α
      ring
    rw [Finset.sum_congr rfl fun α _ => hfactor α, ← Finset.mul_sum]
    have hsum : ∑ α : Fin N, P.coeff (en α) * iteratedDeriv (en α) (expSum a μ) s
        = ∑ j ∈ Finset.range (P.natDegree + 1),
            P.coeff j * iteratedDeriv j (expSum a μ) s := by
      have hS' : ∑ α : Fin N, P.coeff (en α) * iteratedDeriv (en α) (expSum a μ) s
          = ∑ j ∈ S, P.coeff j * iteratedDeriv j (expSum a μ) s := by
        rw [← Finset.sum_coe_sort S
          (fun j => P.coeff j * iteratedDeriv j (expSum a μ) s)]
        exact Fintype.sum_equiv S.equivFin.symm _ _ fun α => rfl
      rw [hS']
      refine Finset.sum_subset ?_ ?_
      · intro j hj
        rw [Finset.mem_range]
        have := Polynomial.le_natDegree_of_mem_supp j (by rwa [← hS])
        omega
      · intro j _ hj
        have hzero : P.coeff j = 0 := by
          by_contra hne
          exact hj (by rw [hS, Polynomial.mem_support_iff]; exact hne)
        rw [hzero, zero_mul]
    rw [hsum]
    have hfun : expSum a μ = fun x : ℂ => ∑ k ∈ (Finset.univ : Finset (Fin r)),
        a k * Complex.exp (((μ k : ℝ) : ℂ) * x) := by
      funext x
      rw [expSum]
    rw [hfun, hP, expSumChar,
      expSumAnnihilator_ode Finset.univ a (fun k : Fin r => ((μ k : ℝ) : ℂ)) s, mul_zero]

/-- The one-term shifted Gamma monomial presentation of a scalar multiple of `Γ(s + λ)`. -/
theorem gammaShift_scalar_multiMonomial (c : ℂ) {σ lam : ℝ} (t : ℝ) :
    c * Complex.Gamma (((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ))
      = multiMonomialSum σ ![lam] (fun _ : Fin 1 => c) (fun _ _ => 1) (fun _ => 1)
          (fun _ => 1) (fun _ => 0) t := by
  have hz : ((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ)
      = ((σ + lam : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    push_cast
    ring
  rw [multiMonomialSum]
  simp [gammaLine, hz]

/-- The restriction of an exponential sum to a vertical line is continuous. -/
theorem continuous_expSum_line (a : Fin r → ℂ) (μ : Fin r → ℝ) (σ : ℝ) :
    Continuous (fun t : ℝ => expSum a μ ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
  (differentiable_expSum a μ).continuous.comp (by fun_prop)

/-- The restriction of an exponential sum to a vertical line is Bohr almost periodic. -/
theorem isBohrAlmostPeriodic_expSum_line (a : Fin r → ℂ) (μ : Fin r → ℝ) (σ : ℝ) :
    _root_.HTGeometry.IsBohrAlmostPeriodic
      (fun t : ℝ => expSum a μ ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [expSum_line_eq a μ σ]
  exact isBohrAlmostPeriodic_sum Finset.univ
    (fun _ _ => continuous_const.mul (continuous_expChar _))
    (fun _ _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar _))

/-- The translation orbit of the restriction is totally bounded. -/
theorem hasTotallyBoundedOrbit_expSum_line (a : Fin r → ℂ) (μ : Fin r → ℝ) (σ : ℝ) :
    HasTotallyBoundedOrbit (fun t : ℝ => expSum a μ ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
  hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic (continuous_expSum_line a μ σ)
    (isBohrAlmostPeriodic_expSum_line a μ σ)

/-- The restriction of an exponential sum to a vertical line as a bounded continuous observable. -/
def expSumLineBC (a : Fin r → ℂ) (μ : Fin r → ℝ) (σ : ℝ) : ℝ →ᵇ ℂ :=
  toBC (fun t : ℝ => expSum a μ ((σ : ℂ) + (t : ℂ) * Complex.I))
    (continuous_expSum_line a μ σ) (hasTotallyBoundedOrbit_expSum_line a μ σ)

@[simp] theorem expSumLineBC_apply (a : Fin r → ℂ) (μ : Fin r → ℝ) (σ t : ℝ) :
    expSumLineBC a μ σ t = expSum a μ ((σ : ℂ) + (t : ℂ) * Complex.I) := rfl

/-- **The shifted law's hypotheses are inhabited at every rank.**  For every rationally independent
frequency packet of size `r` and every admissible shift there is a function holomorphic and almost
periodic on the strip which satisfies a relation whose coefficients are one-term shifted Gamma
monomials, and whose frequency module along the line has rank exactly `r`. -/
theorem exists_gammaShift_solution_rank_eq {μ : Fin r → ℝ} (hμ : LinearIndependent ℚ μ)
    {a : Fin r → ℂ} (ha : ∀ k, a k ≠ 0) (σ lam R : ℝ) :
    ∃ (Φ : ℂ → ℂ) (n N : ℕ) (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
      (cc : Fin N → Fin 1 → ℂ) (ee : Fin N → Fin 1 → Fin 1 → ℕ)
      (q p : Fin N → Fin 1 → Polynomial ℂ) (bb : Fin N → Fin 1 → ℤ),
      DifferentiableOn ℂ Φ (verticalStrip σ R) ∧ IsStripAlmostPeriodic Φ σ R ∧
      0 < N ∧ Function.Injective e ∧ (∀ α i, cc α i ≠ 0) ∧ (∀ α i, q α i ≠ 0) ∧
      (∀ α i, p α i ≠ 0) ∧
      (∀ (α : Fin N) (i j : Fin 1), i ≠ j →
        ¬(multiDegree (ee α i) = multiDegree (ee α j)
          ∧ multiExponent ![lam] (ee α i) (q α i) (p α i)
            = multiExponent ![lam] (ee α j) (q α j) (p α j)
          ∧ bb α i = bb α j)) ∧
      (∀ (α : Fin N) (t : ℝ), F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        = multiMonomialSum σ ![lam] (cc α) (ee α) (q α) (p α) (bb α) t) ∧
      (∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0) ∧
      Module.rank ℚ (bohrFrequencyModule fun t : ℝ => Φ ((σ : ℂ) + (t : ℂ) * Complex.I))
        = (r : Cardinal) := by
  classical
  obtain ⟨N, e, cf, hN, he, hcf, hrel⟩ := exists_gammaShift_relation_expSum a μ lam
  refine ⟨expSum a μ, (expSumChar μ).natDegree, N, e,
    fun α s => cf α * Complex.Gamma (s + (lam : ℂ)),
    fun α _ => cf α, fun _ _ _ => 1, fun _ _ => 1, fun _ _ => 1, fun _ _ => 0,
    (differentiable_expSum a μ).differentiableOn, isStripAlmostPeriodic_expSum a μ σ R,
    hN, he, fun α _ => hcf α, fun _ _ => one_ne_zero, fun _ _ => one_ne_zero, ?_, ?_, hrel, ?_⟩
  · intro α i j hij
    exact absurd (Subsingleton.elim i j) hij
  · intro α t
    exact gammaShift_scalar_multiMonomial (cf α) t
  · exact rank_bohrFrequencyModule_expSum_line ha hμ σ

/-- **The shifted finite phase law applies to the exponential sum.**  Every hypothesis of the
multi-translate law is discharged for this solution, so its bound is not vacuous. -/
theorem gammaShift_rank_finite_expSum (a : Fin r → ℂ) (μ : Fin r → ℝ)
    {σ lam R rr ρ : ℝ} (hσ : 0 < σ) (hlam : 0 < σ + lam) (hrr : 0 < rr) (hρ : 0 < ρ)
    (hrρ : rr + ρ < R) (hR : 0 < R) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies (expSumLineBC a μ σ)) ≤ (K : Cardinal) := by
  classical
  obtain ⟨N, e, cf, hN, he, hcf, hrel⟩ := exists_gammaShift_relation_expSum a μ lam
  refine rank_finite_of_gammaShiftMulti (n := (expSumChar μ).natDegree) (M := 1) (r := 1)
    hσ hN one_pos hrr hρ hrρ hR
    (differentiable_expSum a μ).differentiableOn (isStripAlmostPeriodic_expSum a μ σ R)
    e he (fun α s => cf α * Complex.Gamma (s + (lam : ℂ))) ![lam] ?_
    (fun α _ => cf α) (fun α _ => hcf α) (fun _ _ _ => 1) (fun _ _ => 1) (fun _ _ => 1)
    (fun _ _ => one_ne_zero) (fun _ _ => one_ne_zero) (fun _ _ => 0) ?_ ?_ hrel
    (f := expSumLineBC a μ σ) (fun _ => rfl) ?_ ?_
  · intro k
    have : ![lam] k = lam := by fin_cases k; rfl
    rw [this]
    exact hlam
  · intro α i j hij
    exact absurd (Subsingleton.elim i j) hij
  · intro α t
    exact gammaShift_scalar_multiMonomial (cf α) t
  · exact uniformContinuous_of_isBohrAlmostPeriodic (continuous_expSum_line a μ σ)
      (isBohrAlmostPeriodic_expSum_line a μ σ)
  · exact hasTotallyBoundedOrbit_expSum_line a μ σ

end

end GaloisForLFunctions.HTGeometry

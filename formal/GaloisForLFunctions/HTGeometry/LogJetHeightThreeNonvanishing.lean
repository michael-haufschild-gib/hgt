import GaloisForLFunctions.HTGeometry.LogJetHeightThree

/-!
# The logarithmic Jacobian at height three does not vanish

The closed-form `2×2` determinant, cleared of denominators, is the polynomial combination

`Q₁²Q₁'·W(Q₂,v₂) − W(Q₁,v₁)·Q₂Q₂' − Q₁²Q₁'·v₂(Q₂')²`,

whose two coordinates are separated: each summand is a factor in `X₁` times a factor in `X₂`.  Its
coefficient at the top `X₂`-degree `2·deg Q₂ − 1` is

`−deg Q₂ · (lead Q₂)² · (W(Q₁,v₁) + deg Q₂ · lead v₂ · Q₁²Q₁')`,

nonzero because the cross term outgrows the Wronskian.  A separated pair with a nonzero coefficient
in one coordinate is a nonzero polynomial, so the determinant is nonzero in the fraction field.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-! ## Separated pairs -/

/-- **A separated pair is detected by one coefficient.**  If the polynomials
`a₁·(coeff n b₁) − a₂·(coeff n b₂)` do not cancel, then the two-coordinate combination
`a₁(Xᵢ)b₁(Xⱼ) − a₂(Xᵢ)b₂(Xⱼ)` is a nonzero multivariate polynomial. -/
theorem separatedPair_ne_zero {a₁ a₂ b₁ b₂ : Polynomial ℂ} {i j : ℕ} (hij : i ≠ j) (n : ℕ)
    (h : a₁ * Polynomial.C (b₁.coeff n) - a₂ * Polynomial.C (b₂.coeff n) ≠ 0) :
    univFactor a₁ i * univFactor b₁ j - univFactor a₂ i * univFactor b₂ j ≠ 0 := by
  classical
  intro h0
  refine h ?_
  set σ : ℕ → Polynomial (Polynomial ℂ) :=
    fun k => if k = j then Polynomial.X else Polynomial.C Polynomial.X with hσ
  have hlow : ∀ p : Polynomial ℂ,
      MvPolynomial.aeval σ (univFactor p i) = Polynomial.C p := by
    intro p
    rw [univFactor, ← Polynomial.aeval_algHom_apply]
    have hi : σ i = Polynomial.C Polynomial.X := by
      simp only [hσ, if_neg hij]
    have hCX : (Polynomial.CAlgHom : Polynomial ℂ →ₐ[ℂ] Polynomial (Polynomial ℂ))
        Polynomial.X = Polynomial.C Polynomial.X := rfl
    simp only [MvPolynomial.aeval_X, hi, ← hCX]
    rw [Polynomial.aeval_algHom_apply]
    simp
  have hhigh : ∀ p : Polynomial ℂ,
      MvPolynomial.aeval σ (univFactor p j)
        = p.map (Polynomial.C : ℂ →+* Polynomial ℂ) := by
    intro p
    rw [univFactor, ← Polynomial.aeval_algHom_apply]
    have hj : σ j = Polynomial.X := by simp only [hσ, if_pos rfl]
    simp only [MvPolynomial.aeval_X, hj]
    exact Polynomial.coeff_inj.mp rfl
  have hmap := congrArg (fun x => MvPolynomial.aeval σ x) h0
  simp only [map_sub, map_mul, map_zero, hlow, hhigh] at hmap
  have hc := congrArg (fun q : Polynomial (Polynomial ℂ) => q.coeff n) hmap
  simpa [Polynomial.coeff_C_mul, Polynomial.coeff_map] using hc

/-! ## The derivative's degree and leading coefficient -/

theorem natDegree_derivative_eq_sub_one {p : Polynomial ℂ} (hp : 1 ≤ p.natDegree) :
    p.derivative.natDegree = p.natDegree - 1 :=
  Polynomial.natDegree_eq_of_degree_eq_some (Polynomial.degree_derivative (p := p) (by omega))

theorem leadingCoeff_derivative {p : Polynomial ℂ} (hp : 1 ≤ p.natDegree) :
    p.derivative.leadingCoeff = (p.natDegree : ℂ) * p.leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDegree_derivative_eq_sub_one hp, Polynomial.coeff_derivative,
    Polynomial.leadingCoeff]
  have hsub : p.natDegree - 1 + 1 = p.natDegree := by omega
  rw [hsub]
  push_cast [Nat.cast_sub hp]
  ring

theorem derivative_ne_zero_of_one_le {p : Polynomial ℂ} (hp : 1 ≤ p.natDegree) :
    p.derivative ≠ 0 := by
  intro h
  rw [Polynomial.derivative_eq_zero] at h
  omega

/-! ## The two top coefficients of the second coordinate -/

/-- The top coefficient of `Q·Q'`. -/
theorem coeff_mul_derivative_top {Q : Polynomial ℂ} (hQ : 1 ≤ Q.natDegree) :
    (Q * Q.derivative).coeff (2 * Q.natDegree - 1)
      = (Q.natDegree : ℂ) * Q.leadingCoeff ^ 2 := by
  have hidx : Q.natDegree + Q.derivative.natDegree = 2 * Q.natDegree - 1 := by
    rw [natDegree_derivative_eq_sub_one hQ]
    omega
  have h := Polynomial.coeff_mul_degree_add_degree Q Q.derivative
  rw [hidx] at h
  rw [h, leadingCoeff_derivative hQ]
  ring

/-- The top coefficient of `(Q')²·v` for a linear `v`. -/
theorem coeff_derivative_sq_mul_top {Q v : Polynomial ℂ} (hQ : 1 ≤ Q.natDegree)
    (hv : v.natDegree = 1) :
    (Q.derivative ^ 2 * v).coeff (2 * Q.natDegree - 1)
      = (Q.natDegree : ℂ) ^ 2 * Q.leadingCoeff ^ 2 * v.leadingCoeff := by
  have hQ'0 : Q.derivative ≠ 0 := derivative_ne_zero_of_one_le hQ
  have hdeg : (Q.derivative ^ 2).natDegree = 2 * (Q.natDegree - 1) := by
    rw [Polynomial.natDegree_pow, natDegree_derivative_eq_sub_one hQ]
  have hidx : (Q.derivative ^ 2).natDegree + v.natDegree = 2 * Q.natDegree - 1 := by
    rw [hdeg, hv]
    omega
  have h := Polynomial.coeff_mul_degree_add_degree (Q.derivative ^ 2) v
  rw [hidx] at h
  rw [h, Polynomial.leadingCoeff_pow, leadingCoeff_derivative hQ]
  ring

/-! ## The cleared determinant -/

variable (Q v : ℕ → Polynomial ℂ)

/-- The first-coordinate factor carrying the cross term. -/
noncomputable def crossHead (Q : ℕ → Polynomial ℂ) : Polynomial ℂ :=
  Q 1 ^ 2 * (Q 1).derivative

/-- The second-coordinate factor paired with the cross term. -/
noncomputable def crossTail (Q v : ℕ → Polynomial ℂ) : Polynomial ℂ :=
  scaledLogWronskian (Q 2) (v 2) - (Q 2).derivative ^ 2 * v 2

/-- **The height-three determinant with its denominators cleared.**  The result is a separated pair:
each summand is a factor in the first coordinate times a factor in the second. -/
theorem logJetJacobian_one_det_mul {Q : ℕ → Polynomial ℂ} (v : ℕ → Polynomial ℂ)
    (hQ : ∀ i, Q i ≠ 0) :
    (logJetJacobian Q v 1).det * (fact (Q 1) 1 ^ 2 * fact (Q 2) 2 ^ 2)
      = fact (Q 0) 0
        * (fact (crossHead Q) 1 * fact (crossTail Q v) 2
            - fact (scaledLogWronskian (Q 1) (v 1)) 1 * fact (Q 2 * (Q 2).derivative) 2) := by
  have h1 : fact (Q 1) 1 ≠ 0 := fact_ne_zero (hQ 1) 1
  have h2 : fact (Q 2) 2 ≠ 0 := fact_ne_zero (hQ 2) 2
  rw [logJetJacobian_one_det v hQ, crossHead, crossTail]
  simp only [logFactor, prodJet_eq, prodHead_succ, prodHead_zero, one_mul,
    fact_mul, fact_sub, fact_pow]
  field_simp
  ring

/-! ## Nonvanishing -/

/-- **The logarithmic Jacobian at height three is nonzero.**  The hypotheses are the ones the
product law of a cascade of first-order entire maps supplies: nonzero factors, nonconstant
denominators and linear terminal factors. -/
theorem logJetJacobian_one_det_ne_zero {Q : ℕ → Polynomial ℂ} (v : ℕ → Polynomial ℂ)
    (hQ : ∀ i, Q i ≠ 0)
    (hQ1 : 1 ≤ (Q 1).natDegree) (hv1 : (v 1).natDegree ≤ 1)
    (hQ2 : 1 ≤ (Q 2).natDegree) (hv2 : (v 2).natDegree = 1) :
    (logJetJacobian Q v 1).det ≠ 0 := by
  classical
  set d : ℕ := (Q 2).natDegree with hd
  set a : ℂ := (Q 2).leadingCoeff with ha
  set α : ℂ := (v 2).leadingCoeff with hα
  have hv20 : v 2 ≠ 0 := fun h => by simp [h] at hv2
  have hane : a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (hQ 2)
  have hαne : α ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hv20
  have hdne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- the two top coefficients in the second coordinate
  have hb₂ : (Q 2 * (Q 2).derivative).coeff (2 * d - 1) = (d : ℂ) * a ^ 2 :=
    coeff_mul_derivative_top hQ2
  have hb₁ : (crossTail Q v).coeff (2 * d - 1) = -((d : ℂ) ^ 2 * a ^ 2 * α) := by
    rw [crossTail, Polynomial.coeff_sub, coeff_derivative_sq_mul_top hQ2 hv2]
    have hW : (scaledLogWronskian (Q 2) (v 2)).coeff (2 * d - 1) = 0 := by
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      have hle := natDegree_scaledLogWronskian_le_sub_two hQ2 hv2
      omega
    rw [hW]
    ring
  -- the separated pair does not cancel
  have hcross : scaledLogWronskian (Q 1) (v 1)
      + Polynomial.C ((d : ℂ) * α) * Q 1 ^ 2 * (Q 1).derivative ≠ 0 :=
    scaledLogWronskian_add_cross_ne_zero (mul_ne_zero hdne hαne) hQ1 hv1
  have hcoeff : crossHead Q * Polynomial.C ((crossTail Q v).coeff (2 * d - 1))
      - scaledLogWronskian (Q 1) (v 1)
        * Polynomial.C ((Q 2 * (Q 2).derivative).coeff (2 * d - 1)) ≠ 0 := by
    rw [hb₁, hb₂]
    have hfac : crossHead Q * Polynomial.C (-((d : ℂ) ^ 2 * a ^ 2 * α))
        - scaledLogWronskian (Q 1) (v 1) * Polynomial.C ((d : ℂ) * a ^ 2)
        = -(Polynomial.C ((d : ℂ) * a ^ 2)
            * (scaledLogWronskian (Q 1) (v 1)
                + Polynomial.C ((d : ℂ) * α) * Q 1 ^ 2 * (Q 1).derivative)) := by
      rw [crossHead]
      simp only [map_neg, map_mul, map_pow]
      ring
    rw [hfac]
    refine neg_ne_zero.mpr (mul_ne_zero ?_ hcross)
    refine Polynomial.C_ne_zero.mpr ?_
    exact mul_ne_zero hdne (pow_ne_zero 2 hane)
  have hpair : univFactor (crossHead Q) 1 * univFactor (crossTail Q v) 2
      - univFactor (scaledLogWronskian (Q 1) (v 1)) 1
        * univFactor (Q 2 * (Q 2).derivative) 2 ≠ 0 :=
    separatedPair_ne_zero (by omega : (1 : ℕ) ≠ 2) (2 * d - 1) hcoeff
  -- transfer to the fraction field
  have hinj : Function.Injective (algebraMap (MvPolynomial ℕ ℂ) CascadeField) :=
    IsFractionRing.injective _ _
  have hfield : fact (crossHead Q) 1 * fact (crossTail Q v) 2
      - fact (scaledLogWronskian (Q 1) (v 1)) 1 * fact (Q 2 * (Q 2).derivative) 2 ≠ 0 := by
    intro hzero
    refine hpair (hinj ?_)
    simpa [fact, map_sub, map_mul] using hzero
  -- and back through the cleared identity
  intro hdet
  have hid := logJetJacobian_one_det_mul (Q := Q) v hQ
  rw [hdet, zero_mul] at hid
  refine hfield ?_
  have h0 : fact (Q 0) 0 ≠ 0 := fact_ne_zero (hQ 0) 0
  rcases mul_eq_zero.mp hid.symm with h | h
  · exact absurd h h0
  · exact h

end GaloisForLFunctions.HTGeometry

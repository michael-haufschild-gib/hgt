import GaloisForLFunctions.HTGeometry.ConfluentVanishingPolynomial
import GaloisForLFunctions.HTGeometry.OneDimTranslationJetPacket

/-!
# The Hermite evaluation of a one-coordinate translation jet packet is surjective

A finite affine jet packet of a one-coordinate source along a palette of translations reads, at
each of finitely many distinct nodes, the derivatives below a prescribed order.  The total number
of coordinates is the sum of those orders, so evaluating the first that many monomials gives a
square linear map, and it is injective because a polynomial of that degree vanishing to those
orders is zero.  Hence it is surjective.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*}

theorem iteratedDeriv_polynomialEval (P : Polynomial ℂ) (j : ℕ) (w : ℂ) :
    iteratedDeriv j (fun z => P.eval z) w = ((⇑derivative)^[j] P).eval w := by
  induction j generalizing P with
  | zero => simp
  | succ j ih =>
      rw [iteratedDeriv_succ']
      have h : deriv (fun z => P.eval z) = fun z => (derivative P).eval z := by
        funext z
        simp [Polynomial.deriv]
      rw [h, ih, Function.iterate_succ_apply]

/-- One-coordinate multi-indices below `m` are exactly the derivative orders below `m`. -/
def multiIndexBelowOneEquiv (m : ℕ) : MultiIndexBelow 1 m ≃ Fin m where
  toFun a := ⟨a.1 0, by
    have h := a.2
    rw [finsupp_fin_one_eq_single a.1, Finsupp.degree_single] at h
    exact h⟩
  invFun j := ⟨Finsupp.single 0 (j : ℕ), by rw [Finsupp.degree_single]; exact j.isLt⟩
  left_inv a := by
    apply Subtype.ext
    exact (finsupp_fin_one_eq_single a.1).symm
  right_inv j := by
    apply Fin.ext
    simp

theorem card_multiIndexBelowOne (m : ℕ) : Fintype.card (MultiIndexBelow 1 m) = m := by
  rw [Fintype.card_congr (multiIndexBelowOneEquiv m), Fintype.card_fin]

theorem card_patternJet (p : FiniteMultivariateAffineJetPattern H 1) :
    Fintype.card (MultivariateAffinePatternJet p) = ∑ i, p.orders i := by
  show Fintype.card (Σ i, MultiIndexBelow 1 (p.orders i)) = _
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl fun i _ => card_multiIndexBelowOne _

/-- The distinct evaluation nodes of a one-coordinate translation packet. -/
def packetNode (shift : H → ℂ) (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ)
    (q : MultivariateAffinePatternRow p × Fin p.frameCount) : ℂ :=
  base q.1 0 + shift (p.frameCode q.2)

theorem card_coordinate_eq_sum_orders (p : FiniteMultivariateAffineJetPattern H 1) :
    affineJetPacketFiniteCoordinateCount p
      = ∑ q : MultivariateAffinePatternRow p × Fin p.frameCount, p.orders q.2 := by
  rw [affineJetPacketFiniteCoordinateCount, Fintype.card_prod, card_patternJet,
    Fintype.sum_prod_type]
  simp [Finset.sum_const, Finset.card_univ]

theorem injective_packetNode {shift : H → ℂ} {p : FiniteMultivariateAffineJetPattern H 1}
    {base : MultivariateAffinePatternRow p → Fin 1 → ℂ}
    (hinj : Function.Injective
      (fun q : MultivariateAffinePatternRow p × Fin p.frameCount =>
        (fun h => oneDimTranslationFrame (shift h)) (p.frameCode q.2) (base q.1))) :
    Function.Injective (packetNode shift p base) := by
  intro q₁ q₂ h
  rw [packetNode, packetNode] at h
  refine hinj ?_
  funext i
  fin_cases i
  simpa using h

/-- The square Hermite evaluation map of the first `N` scaled monomials at the packet nodes. -/
def packetHermiteMap (shift : H → ℂ) (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ) :
    (Fin (affineJetPacketFiniteCoordinateCount p) → ℂ) →ₗ[ℂ]
      (Fin (affineJetPacketFiniteCoordinateCount p) → ℂ) where
  toFun c k := ∑ n : Fin (affineJetPacketFiniteCoordinateCount p),
    (c n / ((4 : ℂ) * ((Nat.factorial (n : ℕ)) : ℂ))) *
      (((⇑derivative)^[packetOrder p
          ((Fintype.equivFin (MultivariateAffinePatternRow p ×
            MultivariateAffinePatternJet p)).symm k)] (X ^ (n : ℕ) : Polynomial ℂ)).eval
        (packetPoint shift p base
          ((Fintype.equivFin (MultivariateAffinePatternRow p ×
            MultivariateAffinePatternJet p)).symm k)))
  map_add' c d := by
    funext k
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by rw [add_div, add_mul]
  map_smul' r c := by
    funext k
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring

theorem packetHermiteMap_apply (shift : H → ℂ) (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ)
    (c : Fin (affineJetPacketFiniteCoordinateCount p) → ℂ)
    (k : Fin (affineJetPacketFiniteCoordinateCount p)) :
    packetHermiteMap shift p base c k
      = ∑ n : Fin (affineJetPacketFiniteCoordinateCount p),
        (c n / ((4 : ℂ) * ((Nat.factorial (n : ℕ)) : ℂ))) *
          (((⇑derivative)^[packetOrder p
              ((Fintype.equivFin (MultivariateAffinePatternRow p ×
                MultivariateAffinePatternJet p)).symm k)] (X ^ (n : ℕ) : Polynomial ℂ)).eval
            (packetPoint shift p base
              ((Fintype.equivFin (MultivariateAffinePatternRow p ×
                MultivariateAffinePatternJet p)).symm k))) := rfl

/-- Evaluating the iterated derivative of the coefficient polynomial reproduces one packet row. -/
theorem eval_iterate_derivative_coeffPolynomial
    {N : ℕ} (c : Fin N → ℂ) (j : ℕ) (w : ℂ) :
    ((⇑derivative)^[j] (∑ n : Fin N, C (c n / ((4 : ℂ) * ((Nat.factorial (n : ℕ)) : ℂ)))
        * X ^ (n : ℕ))).eval w
      = ∑ n : Fin N, (c n / ((4 : ℂ) * ((Nat.factorial (n : ℕ)) : ℂ)))
        * (((⇑derivative)^[j] (X ^ (n : ℕ) : Polynomial ℂ)).eval w) := by
  have hpow : ∀ Q : Polynomial ℂ, (⇑derivative)^[j] Q
      = ((derivative : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ) ^ j) Q :=
    fun Q => (Module.End.pow_apply derivative j Q).symm
  rw [hpow, map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show (C (c n / ((4 : ℂ) * ((Nat.factorial (n : ℕ)) : ℂ))) * X ^ (n : ℕ) : Polynomial ℂ)
      = (c n / ((4 : ℂ) * ((Nat.factorial (n : ℕ)) : ℂ))) • (X ^ (n : ℕ) : Polynomial ℂ) from
    (Polynomial.smul_eq_C_mul _).symm, map_smul, Polynomial.eval_smul, smul_eq_mul, hpow]

theorem injective_packetHermiteMap {shift : H → ℂ} {p : FiniteMultivariateAffineJetPattern H 1}
    {base : MultivariateAffinePatternRow p → Fin 1 → ℂ}
    (hinj : Function.Injective
      (fun q : MultivariateAffinePatternRow p × Fin p.frameCount =>
        (fun h => oneDimTranslationFrame (shift h)) (p.frameCode q.2) (base q.1))) :
    Function.Injective (packetHermiteMap shift p base) := by
  classical
  rcases Nat.eq_zero_or_pos (affineJetPacketFiniteCoordinateCount p) with hN0 | hNpos
  · intro u v _
    funext n
    rw [hN0] at n
    exact absurd n.isLt (by omega)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  set ε := Fintype.equivFin
    (MultivariateAffinePatternRow p × MultivariateAffinePatternJet p) with hε
  set P : Polynomial ℂ :=
    ∑ n : Fin (affineJetPacketFiniteCoordinateCount p),
      C (c n / ((4 : ℂ) * ((Nat.factorial (n : ℕ)) : ℂ))) * X ^ (n : ℕ) with hP
  have hcoeff : ∀ n : Fin (affineJetPacketFiniteCoordinateCount p),
      P.coeff (n : ℕ) = c n / ((4 : ℂ) * ((Nat.factorial (n : ℕ)) : ℂ)) := by
    intro n
    rw [hP, Polynomial.finsetSum_coeff, Finset.sum_eq_single n]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro m _ hmn
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (fun hcc => hmn (Fin.ext hcc.symm)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ n) h
  have hdeg : P.natDegree < affineJetPacketFiniteCoordinateCount p := by
    have hle : P.natDegree ≤ affineJetPacketFiniteCoordinateCount p - 1 := by
      rw [hP]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun n _ => ?_
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      rw [Polynomial.natDegree_X_pow]
      omega
    omega
  have hvan : ∀ q : MultivariateAffinePatternRow p × Fin p.frameCount, ∀ j, j < p.orders q.2 →
      ((⇑derivative)^[j] P).eval (packetNode shift p base q) = 0 := by
    intro q j hj
    set a : MultiIndexBelow 1 (p.orders q.2) :=
      (multiIndexBelowOneEquiv (p.orders q.2)).symm ⟨j, hj⟩ with ha
    set k : MultivariateAffinePatternRow p × MultivariateAffinePatternJet p :=
      (q.1, ⟨q.2, a⟩) with hk
    have horder : packetOrder p k = j := by
      rw [hk, packetOrder, ha]
      simp [multiIndexBelowOneEquiv]
    have hpoint : packetPoint shift p base k = packetNode shift p base q := rfl
    have hzero := congrFun hc (ε k)
    rw [packetHermiteMap_apply, Pi.zero_apply] at hzero
    rw [← hε, Equiv.symm_apply_apply, horder, hpoint] at hzero
    rw [hP, eval_iterate_derivative_coeffPolynomial]
    exact hzero
  have hPzero : P = 0 :=
    polynomial_eq_zero_of_jets_vanish (packetNode shift p base) (injective_packetNode hinj)
      (fun q => p.orders q.2) (by rw [← card_coordinate_eq_sum_orders]; exact hdeg) hvan
  funext n
  have hcn := hcoeff n
  rw [hPzero, Polynomial.coeff_zero] at hcn
  have hfac : ((4 : ℂ) * ((Nat.factorial (n : ℕ)) : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  rcases div_eq_zero_iff.1 hcn.symm with h | h
  · simpa using h
  · exact absurd h hfac

/-- **Packet Hermite surjectivity.** -/
theorem surjective_packetHermiteMap {shift : H → ℂ} {p : FiniteMultivariateAffineJetPattern H 1}
    {base : MultivariateAffinePatternRow p → Fin 1 → ℂ}
    (hinj : Function.Injective
      (fun q : MultivariateAffinePatternRow p × Fin p.frameCount =>
        (fun h => oneDimTranslationFrame (shift h)) (p.frameCode q.2) (base q.1))) :
    Function.Surjective (packetHermiteMap shift p base) :=
  LinearMap.injective_iff_surjective.1 (injective_packetHermiteMap hinj)

/-! ### The monomial-shifted Hermite map -/

/-- Evaluating the iterated derivative of a weighted monomial sum. -/
theorem eval_iterate_derivative_weightedSum {N : ℕ} (a : Fin N → ℂ) (m : Fin N → ℕ)
    (j : ℕ) (w : ℂ) :
    ((⇑derivative)^[j] (∑ n : Fin N, C (a n) * X ^ (m n))).eval w
      = ∑ n : Fin N, a n * (((⇑derivative)^[j] (X ^ (m n) : Polynomial ℂ)).eval w) := by
  have hpow : ∀ Q : Polynomial ℂ, (⇑derivative)^[j] Q
      = ((derivative : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ) ^ j) Q :=
    fun Q => (Module.End.pow_apply derivative j Q).symm
  rw [hpow, map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show (C (a n) * X ^ (m n) : Polynomial ℂ) = (a n) • (X ^ (m n) : Polynomial ℂ) from
    (Polynomial.smul_eq_C_mul _).symm, map_smul, Polynomial.eval_smul, smul_eq_mul, hpow]

/-- The square Hermite evaluation of the monomials `X^{n+L}` at the packet nodes. -/
def packetShiftedHermiteMap (shift : H → ℂ) (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ) (wt : ℕ → ℂ) (L : ℕ) :
    (Fin (affineJetPacketFiniteCoordinateCount p) → ℂ) →ₗ[ℂ]
      (Fin (affineJetPacketFiniteCoordinateCount p) → ℂ) where
  toFun c k := ∑ n : Fin (affineJetPacketFiniteCoordinateCount p),
    (c n * wt (n : ℕ)) *
      (((⇑derivative)^[packetOrder p
          ((Fintype.equivFin (MultivariateAffinePatternRow p ×
            MultivariateAffinePatternJet p)).symm k)]
        (X ^ ((n : ℕ) + L) : Polynomial ℂ)).eval
        (packetPoint shift p base
          ((Fintype.equivFin (MultivariateAffinePatternRow p ×
            MultivariateAffinePatternJet p)).symm k)))
  map_add' c d := by
    funext k
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by rw [add_mul, add_mul]
  map_smul' r c := by
    funext k
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring

theorem packetShiftedHermiteMap_apply (shift : H → ℂ)
    (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ) (wt : ℕ → ℂ) (L : ℕ)
    (c : Fin (affineJetPacketFiniteCoordinateCount p) → ℂ)
    (k : Fin (affineJetPacketFiniteCoordinateCount p)) :
    packetShiftedHermiteMap shift p base wt L c k
      = ∑ n : Fin (affineJetPacketFiniteCoordinateCount p),
        (c n * wt (n : ℕ)) *
          (((⇑derivative)^[packetOrder p
              ((Fintype.equivFin (MultivariateAffinePatternRow p ×
                MultivariateAffinePatternJet p)).symm k)]
            (X ^ ((n : ℕ) + L) : Polynomial ℂ)).eval
            (packetPoint shift p base
              ((Fintype.equivFin (MultivariateAffinePatternRow p ×
                MultivariateAffinePatternJet p)).symm k))) := rfl

theorem injective_packetShiftedHermiteMap {shift : H → ℂ}
    {p : FiniteMultivariateAffineJetPattern H 1}
    {base : MultivariateAffinePatternRow p → Fin 1 → ℂ} (wt : ℕ → ℂ) (L : ℕ)
    (hwt : ∀ n, wt n ≠ 0)
    (hinj : Function.Injective
      (fun q : MultivariateAffinePatternRow p × Fin p.frameCount =>
        (fun h => oneDimTranslationFrame (shift h)) (p.frameCode q.2) (base q.1)))
    (hne : ∀ q : MultivariateAffinePatternRow p × Fin p.frameCount,
      packetNode shift p base q ≠ 0) :
    Function.Injective (packetShiftedHermiteMap shift p base wt L) := by
  classical
  rcases Nat.eq_zero_or_pos (affineJetPacketFiniteCoordinateCount p) with hN0 | hNpos
  · intro u v _
    funext n
    rw [hN0] at n
    exact absurd n.isLt (by omega)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  set ε := Fintype.equivFin
    (MultivariateAffinePatternRow p × MultivariateAffinePatternJet p) with hε
  set Q : Polynomial ℂ :=
    ∑ n : Fin (affineJetPacketFiniteCoordinateCount p),
      C (c n * wt (n : ℕ)) * X ^ (n : ℕ) with hQ
  have hcoeff : ∀ n : Fin (affineJetPacketFiniteCoordinateCount p),
      Q.coeff (n : ℕ) = c n * wt (n : ℕ) := by
    intro n
    rw [hQ, Polynomial.finsetSum_coeff, Finset.sum_eq_single n]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro m _ hmn
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (fun hcc => hmn (Fin.ext hcc.symm)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ n) h
  have hdeg : Q.natDegree < affineJetPacketFiniteCoordinateCount p := by
    have hle : Q.natDegree ≤ affineJetPacketFiniteCoordinateCount p - 1 := by
      rw [hQ]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun n _ => ?_
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      rw [Polynomial.natDegree_X_pow]
      omega
    omega
  have hprod : (X ^ L : Polynomial ℂ) * Q
      = ∑ n : Fin (affineJetPacketFiniteCoordinateCount p),
        C (c n * wt (n : ℕ)) * X ^ ((n : ℕ) + L) := by
    rw [hQ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [pow_add]; ring
  have hvan : ∀ q : MultivariateAffinePatternRow p × Fin p.frameCount, ∀ j, j < p.orders q.2 →
      ((⇑derivative)^[j] ((X ^ L : Polynomial ℂ) * Q)).eval (packetNode shift p base q) = 0 := by
    intro q j hj
    set a : MultiIndexBelow 1 (p.orders q.2) :=
      (multiIndexBelowOneEquiv (p.orders q.2)).symm ⟨j, hj⟩ with ha
    set k : MultivariateAffinePatternRow p × MultivariateAffinePatternJet p :=
      (q.1, ⟨q.2, a⟩) with hk
    have horder : packetOrder p k = j := by
      rw [hk, packetOrder, ha]
      simp [multiIndexBelowOneEquiv]
    have hpoint : packetPoint shift p base k = packetNode shift p base q := rfl
    have hzero := congrFun hc (ε k)
    rw [packetShiftedHermiteMap_apply, Pi.zero_apply] at hzero
    rw [← hε, Equiv.symm_apply_apply, horder, hpoint] at hzero
    rw [hprod, eval_iterate_derivative_weightedSum]
    exact hzero
  have hQzero : Q = 0 :=
    polynomial_eq_zero_of_shifted_jets_vanish (packetNode shift p base)
      (injective_packetNode hinj) hne (fun q => p.orders q.2) L
      (by rw [← card_coordinate_eq_sum_orders]; exact hdeg) hvan
  funext n
  have hcn := hcoeff n
  rw [hQzero, Polynomial.coeff_zero] at hcn
  rcases mul_eq_zero.1 hcn.symm with h | h
  · simpa using h
  · exact absurd h (hwt _)

/-- **Shifted packet Hermite surjectivity at nonzero nodes.** -/
theorem surjective_packetShiftedHermiteMap {shift : H → ℂ}
    {p : FiniteMultivariateAffineJetPattern H 1}
    {base : MultivariateAffinePatternRow p → Fin 1 → ℂ} (wt : ℕ → ℂ) (L : ℕ)
    (hwt : ∀ n, wt n ≠ 0)
    (hinj : Function.Injective
      (fun q : MultivariateAffinePatternRow p × Fin p.frameCount =>
        (fun h => oneDimTranslationFrame (shift h)) (p.frameCode q.2) (base q.1)))
    (hne : ∀ q : MultivariateAffinePatternRow p × Fin p.frameCount,
      packetNode shift p base q ≠ 0) :
    Function.Surjective (packetShiftedHermiteMap shift p base wt L) :=
  LinearMap.injective_iff_surjective.1 (injective_packetShiftedHermiteMap wt L hwt hinj hne)

end

end GaloisForLFunctions.HTGeometry

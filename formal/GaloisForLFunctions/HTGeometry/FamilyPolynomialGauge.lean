import GaloisForLFunctions.HTGeometry.LocalPolynomialGauge

/-!
Multi-component polynomial gauge: the componentwise version of the multiplicative gauge.

A differential relation among a finite family of functions, each multiplied by its own nonzero
polynomial, pulls back to a relation among the original family.  The jet substitution is block
diagonal — one triangular Leibniz block per component — so the point map is solvable blockwise and
its diagonal is the product of the multipliers.

The translated family `m_u (z + h i)` is the instance that the card's translation-family claim
needs, with `a i = 1 + (X + h i) ^ 2`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Jet coordinates of a finite family: one spectral variable, then one jet block per component. -/
abbrev FamilyJetIndex (m n : ℕ) := Unit ⊕ (Fin m × Fin (n + 1))

/-- The jet vector of a family at a point. -/
def familyJetVec {m n : ℕ} (g : Fin m → ℂ → ℂ) (z : ℂ) : FamilyJetIndex m n → ℂ :=
  Sum.elim (fun _ => z) (fun p => iteratedDeriv (p.2 : ℕ) (g p.1) z)

/-- A finite family satisfies a nonzero differential relation on `U`. -/
def FamilyDifferentiallyAlgebraicOn {m : ℕ} (g : Fin m → ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∃ (n : ℕ) (P : MvPolynomial (FamilyJetIndex m n) ℂ), P ≠ 0 ∧
    ∀ z ∈ U, MvPolynomial.eval (familyJetVec g z) P = 0

/-- The jet variable of order `j` in block `i`, extended by zero outside the packet. -/
def familyJetVariable (m n : ℕ) (i : Fin m) (j : ℕ) : MvPolynomial (FamilyJetIndex m n) ℂ :=
  if h : j < n + 1 then MvPolynomial.X (Sum.inr (i, ⟨j, h⟩)) else 0

/-- Coordinate images of the blockwise Leibniz substitution. -/
def familyMulJetImage {m n : ℕ} (a : Fin m → Polynomial ℂ) :
    FamilyJetIndex m n → MvPolynomial (FamilyJetIndex m n) ℂ :=
  Sum.elim (fun _ => MvPolynomial.X (Sum.inl ()))
    (fun p => ∑ k ∈ Finset.range ((p.2 : ℕ) + 1),
      MvPolynomial.C ((((p.2 : ℕ)).choose k : ℕ) : ℂ) *
        Polynomial.aeval (MvPolynomial.X (Sum.inl () : FamilyJetIndex m n))
          (Polynomial.derivative^[k] (a p.1)) *
        familyJetVariable m n p.1 ((p.2 : ℕ) - k))

@[simp]
theorem eval_familyJetVariable_of_lt {m n : ℕ} (i : Fin m) (j : ℕ) (hj : j < n + 1)
    (v : FamilyJetIndex m n → ℂ) :
    MvPolynomial.eval v (familyJetVariable m n i j) = v (Sum.inr (i, ⟨j, hj⟩)) := by
  simp [familyJetVariable, hj]

@[simp]
theorem eval_familyMulJetImage_inl {m n : ℕ} (a : Fin m → Polynomial ℂ)
    (v : FamilyJetIndex m n → ℂ) :
    MvPolynomial.eval v (familyMulJetImage (m := m) (n := n) a (Sum.inl ())) = v (Sum.inl ()) := by
  simp [familyMulJetImage]

theorem eval_familyMulJetImage_inr {m n : ℕ} (a : Fin m → Polynomial ℂ)
    (i : Fin m) (j : Fin (n + 1)) (v : FamilyJetIndex m n → ℂ) :
    MvPolynomial.eval v (familyMulJetImage (m := m) (n := n) a (Sum.inr (i, j)))
      = ∑ k ∈ Finset.range ((j : ℕ) + 1),
          (((j : ℕ).choose k : ℕ) : ℂ)
            * Polynomial.eval (v (Sum.inl ())) (Polynomial.derivative^[k] (a i))
            * MvPolynomial.eval v (familyJetVariable m n i ((j : ℕ) - k)) := by
  simp only [familyMulJetImage, Sum.elim_inr, map_sum, map_mul, MvPolynomial.eval_C,
    eval_aeval_X]

/-- On actual jets, the blockwise substitution returns the jets of the multiplied family. -/
theorem bindPointMap_familyMulJetImage {m n : ℕ} (a : Fin m → Polynomial ℂ)
    (g : Fin m → ℂ → ℂ) {z : ℂ} (hg : ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z) :
    bindPointMap (familyMulJetImage (m := m) (n := n) a) (familyJetVec g z)
      = familyJetVec (fun i w => Polynomial.eval w (a i) * g i w) z := by
  funext s
  cases s with
  | inl x =>
      cases x
      simp [bindPointMap, familyJetVec]
  | inr p =>
      obtain ⟨i, j⟩ := p
      rw [bindPointMap, eval_familyMulJetImage_inr]
      show _ = iteratedDeriv (j : ℕ) (fun w => Polynomial.eval w (a i) * g i w) z
      rw [iteratedDeriv_mul_polynomial_at (hg i) (a i)]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      have hlt : (j : ℕ) - k < n + 1 := by omega
      rw [eval_familyJetVariable_of_lt _ _ hlt]
      simp [familyJetVec]

/-- Substituting a variable into a nonzero polynomial gives a nonzero polynomial. -/
theorem aeval_X_ne_zero' {σ : Type*} (i : σ) {a : Polynomial ℂ} (ha : a ≠ 0) :
    Polynomial.aeval (MvPolynomial.X i) a ≠ (0 : MvPolynomial σ ℂ) := by
  intro h
  refine ha (Polynomial.funext fun x => ?_)
  have hx := eval_aeval_X i a (fun _ => x)
  rw [h] at hx
  simpa using hx.symm

/-- The point map covers every packet where no multiplier vanishes: each block is triangular. -/
theorem exists_familyMulJetImage_preimage {m n : ℕ} (a : Fin m → Polynomial ℂ)
    (w : FamilyJetIndex m n → ℂ)
    (ha : ∀ i, Polynomial.eval (w (Sum.inl ())) (a i) ≠ 0) :
    ∃ v, bindPointMap (familyMulJetImage (m := m) (n := n) a) v = w := by
  classical
  choose u hu using fun i : Fin m => exists_triangular_solution (ha i)
    (mulPolynomialJetLower (a i) (w (Sum.inl ())))
    (mulPolynomialJetLower_congr (a i) (w (Sum.inl ())))
    (fun k => if h : k < n + 1 then w (Sum.inr (i, ⟨k, h⟩)) else 0)
  refine ⟨Sum.elim (fun _ => w (Sum.inl ())) (fun p => u p.1 (p.2 : ℕ)), ?_⟩
  funext s
  cases s with
  | inl x =>
      cases x
      simp [bindPointMap, familyMulJetImage]
  | inr p =>
      obtain ⟨i, j⟩ := p
      rw [bindPointMap, eval_familyMulJetImage_inr]
      have hsplit := hu i (j : ℕ)
      rw [dif_pos j.isLt] at hsplit
      rw [Finset.sum_range_succ']
      simp only [Sum.elim_inl, Nat.choose_zero_right, Nat.cast_one,
        Function.iterate_zero_apply, Nat.sub_zero, one_mul]
      rw [eval_familyJetVariable_of_lt _ _ j.isLt]
      have hlower : (∑ k ∈ Finset.range (j : ℕ),
          (((j : ℕ).choose (k + 1) : ℕ) : ℂ) *
            Polynomial.eval (w (Sum.inl ())) (Polynomial.derivative^[k + 1] (a i)) *
              MvPolynomial.eval
                (Sum.elim (fun _ => w (Sum.inl ())) (fun q => u q.1 (q.2 : ℕ)) :
                  FamilyJetIndex m n → ℂ)
                (familyJetVariable m n i ((j : ℕ) - (k + 1))))
          = mulPolynomialJetLower (a i) (w (Sum.inl ())) (j : ℕ) (u i) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_range] at hk
        have hlt : (j : ℕ) - (k + 1) < n + 1 := by omega
        rw [eval_familyJetVariable_of_lt _ _ hlt]
        simp
      rw [hlower, add_comm]
      simpa [Sum.elim_inr] using hsplit

/-- **The componentwise polynomial gauge.**  A differential relation among a family each multiplied
by its own nonzero polynomial pulls back to a relation among the original family. -/
theorem familyDifferentiallyAlgebraicOn_of_mul_polynomial {m : ℕ} {U : Set ℂ}
    (g : Fin m → ℂ → ℂ) (a : Fin m → Polynomial ℂ) (ha : ∀ i, a i ≠ 0)
    (hg : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z)
    (h : FamilyDifferentiallyAlgebraicOn
      (fun i w => Polynomial.eval w (a i) * g i w) U) :
    FamilyDifferentiallyAlgebraicOn g U := by
  classical
  obtain ⟨n, P, hP, hrel⟩ := h
  refine ⟨n, MvPolynomial.bind₁ (familyMulJetImage (m := m) (n := n) a) P, ?_, ?_⟩
  · refine bind₁_ne_zero_of_pointMap_surjective _
      (∏ i, Polynomial.aeval (MvPolynomial.X (Sum.inl () : FamilyJetIndex m n)) (a i)) ?_ ?_ hP
    · exact Finset.prod_ne_zero_iff.2 fun i _ => aeval_X_ne_zero' _ (ha i)
    · intro w hw
      refine exists_familyMulJetImage_preimage a w fun i => ?_
      rw [map_prod] at hw
      have hi := Finset.prod_ne_zero_iff.1 hw i (Finset.mem_univ i)
      rwa [eval_aeval_X] at hi
  · intro z hz
    rw [eval_bind₁_eq, bindPointMap_familyMulJetImage a g (hg z hz)]
    exact hrel z hz

/-- The polynomial shifts attached to the jet coordinates of a family. -/
def familyShiftPoly {m n : ℕ} (b : Fin m → Polynomial ℂ) :
    FamilyJetIndex m n → Polynomial ℂ :=
  Sum.elim (fun _ => 0) (fun p => Polynomial.derivative^[(p.2 : ℕ)] (b p.1))

/-- **Adding a polynomial componentwise preserves relation-freeness.** -/
theorem familyDifferentiallyAlgebraicOn_of_add_polynomial {m : ℕ} {U : Set ℂ}
    (g : Fin m → ℂ → ℂ) (b : Fin m → Polynomial ℂ)
    (hg : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z)
    (h : FamilyDifferentiallyAlgebraicOn
      (fun i w => g i w + Polynomial.eval w (b i)) U) :
    FamilyDifferentiallyAlgebraicOn g U := by
  classical
  obtain ⟨n, P, hP, hrel⟩ := h
  refine ⟨n, axisShiftSubst (Sum.inl ()) (familyShiftPoly (m := m) (n := n) b) P,
    axisShiftSubst_ne_zero _ _ hP, ?_⟩
  intro z hz
  rw [eval_axisShiftSubst]
  have hjet : (fun s : FamilyJetIndex m n =>
      if s = Sum.inl () then familyJetVec (n := n) g z (Sum.inl ())
      else familyJetVec (n := n) g z s
        + Polynomial.aeval (familyJetVec (n := n) g z (Sum.inl ()))
            (familyShiftPoly (m := m) (n := n) b s))
      = familyJetVec (n := n) (fun i w => g i w + Polynomial.eval w (b i)) z := by
    funext s
    cases s with
    | inl x =>
        cases x
        simp [familyJetVec]
    | inr p =>
        obtain ⟨i, j⟩ := p
        rw [if_neg (by simp)]
        show familyJetVec (n := n) g z (Sum.inr (i, j))
            + Polynomial.aeval (familyJetVec (n := n) g z (Sum.inl ()))
              (Polynomial.derivative^[(j : ℕ)] (b i))
          = iteratedDeriv (j : ℕ) (fun w => g i w + Polynomial.eval w (b i)) z
        rw [iteratedDeriv_add_polynomial_at (hg z hz i) (b i)]
        simp [familyJetVec]
  rw [hjet]
  exact hrel z hz

/-- **The componentwise affine polynomial gauge.** -/
theorem familyDifferentiallyAlgebraicOn_of_affine {m : ℕ} {U : Set ℂ}
    (g : Fin m → ℂ → ℂ) (a b : Fin m → Polynomial ℂ) (ha : ∀ i, a i ≠ 0)
    (hg : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z)
    (h : FamilyDifferentiallyAlgebraicOn
      (fun i w => Polynomial.eval w (b i) + Polynomial.eval w (a i) * g i w) U) :
    FamilyDifferentiallyAlgebraicOn g U := by
  have hmulSmooth : ∀ z ∈ U, ∀ i,
      ContDiffAt ℂ (⊤ : ℕ∞) (fun w => Polynomial.eval w (a i) * g i w) z := by
    intro z hz i
    have haz : ContDiffAt ℂ (⊤ : ℕ∞) (fun w : ℂ => Polynomial.eval w (a i)) z := by
      simpa only [Polynomial.coe_aeval_eq_eval] using
        (Polynomial.contDiff_aeval (a i) (⊤ : ℕ∞)).contDiffAt
    exact haz.mul (hg z hz i)
  refine familyDifferentiallyAlgebraicOn_of_mul_polynomial g a ha hg ?_
  refine familyDifferentiallyAlgebraicOn_of_add_polynomial
    (fun i w => Polynomial.eval w (a i) * g i w) b hmulSmooth ?_
  obtain ⟨n, P, hP, hrel⟩ := h
  refine ⟨n, P, hP, fun z hz => ?_⟩
  have hfun : (fun i w => Polynomial.eval w (a i) * g i w + Polynomial.eval w (b i))
      = fun i w => Polynomial.eval w (b i) + Polynomial.eval w (a i) * g i w := by
    funext i w
    ring
  rw [hfun]
  exact hrel z hz

end

end GaloisForLFunctions.HTGeometry

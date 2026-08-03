import GaloisForLFunctions.HTGeometry.FamilyPolynomialGauge

/-!
# The shear gauge for finite families

Adding a fixed multiple of one family to another is an invertible linear change of jet coordinates
on the two families taken together.  So a differential relation among the sums pulls back to a
differential relation among the doubled family, and joint independence of the two families implies
independence of the perturbed one.

Unlike the multiplicative and power gauges this needs no nonvanishing locus: the point map of a shear
is surjective outright, since the second block may be set to zero.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **Nonvanishing is preserved by a substitution with a surjective point map.**  The cross-type
form, for substitutions which enlarge the variable set. -/
theorem subst_ne_zero_of_pointMap_surjective' {σ τ : Type*}
    (S : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ) (T : (τ → ℂ) → (σ → ℂ))
    (hST : ∀ (P : MvPolynomial σ ℂ) (v : τ → ℂ),
      MvPolynomial.eval v (S P) = MvPolynomial.eval (T v) P)
    (hsurj : Function.Surjective T)
    {P : MvPolynomial σ ℂ} (hP : P ≠ 0) : S P ≠ 0 := by
  intro hzero
  obtain ⟨w, hw⟩ := exists_eval_ne_zero hP
  obtain ⟨v, hv⟩ := hsurj w
  have hval : MvPolynomial.eval v (S P) = MvPolynomial.eval w P := by
    rw [hST P v, hv]
  rw [hzero, map_zero] at hval
  exact hw hval.symm

/-- The two families laid side by side. -/
def doubledFamily {m : ℕ} (f g : Fin m → ℂ → ℂ) : Fin (m + m) → ℂ → ℂ :=
  Fin.addCases f g

@[simp]
theorem doubledFamily_castAdd {m : ℕ} (f g : Fin m → ℂ → ℂ) (i : Fin m) :
    doubledFamily f g (Fin.castAdd m i) = f i := by
  rw [doubledFamily, Fin.addCases_left]

@[simp]
theorem doubledFamily_natAdd {m : ℕ} (f g : Fin m → ℂ → ℂ) (i : Fin m) :
    doubledFamily f g (Fin.natAdd m i) = g i := by
  rw [doubledFamily, Fin.addCases_right]

/-- Coordinate images of the shear substitution. -/
def familyShearJetImage (m n : ℕ) (c : ℂ) :
    FamilyJetIndex m n → MvPolynomial (FamilyJetIndex (m + m) n) ℂ :=
  Sum.elim (fun _ => MvPolynomial.X (Sum.inl ()))
    fun p => MvPolynomial.X (Sum.inr (Fin.castAdd m p.1, p.2))
      + MvPolynomial.C c * MvPolynomial.X (Sum.inr (Fin.natAdd m p.1, p.2))

/-- The point map of the shear substitution. -/
def shearPointMap (m n : ℕ) (c : ℂ) (v : FamilyJetIndex (m + m) n → ℂ) :
    FamilyJetIndex m n → ℂ :=
  fun s => MvPolynomial.eval v (familyShearJetImage m n c s)

theorem eval_bind₁_shear {m n : ℕ} (c : ℂ) (Q : MvPolynomial (FamilyJetIndex m n) ℂ)
    (v : FamilyJetIndex (m + m) n → ℂ) :
    MvPolynomial.eval v (MvPolynomial.bind₁ (familyShearJetImage m n c) Q)
      = MvPolynomial.eval (shearPointMap m n c v) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p s hp => simp [map_mul, hp, shearPointMap]

/-- **The shear point map is surjective.**  Setting the second block to zero realizes any packet. -/
theorem surjective_shearPointMap (m n : ℕ) (c : ℂ) :
    Function.Surjective (shearPointMap m n c) := by
  classical
  intro w
  refine ⟨Sum.elim (fun _ => w (Sum.inl ()))
    fun q => if h : (q.1 : ℕ) < m then w (Sum.inr (⟨(q.1 : ℕ), h⟩, q.2)) else 0, ?_⟩
  funext s
  cases s with
  | inl x =>
      cases x
      simp [shearPointMap, familyShearJetImage]
  | inr p =>
      obtain ⟨i, k⟩ := p
      have hcast : ((Fin.castAdd m i : Fin (m + m)) : ℕ) < m := by
        simp
      have hnat : ¬ ((Fin.natAdd m i : Fin (m + m)) : ℕ) < m := by
        simp only [Fin.val_natAdd]
        omega
      simp only [shearPointMap, familyShearJetImage, Sum.elim_inr, map_add, map_mul,
        MvPolynomial.eval_X, MvPolynomial.eval_C, Sum.elim_inr]
      rw [dif_pos hcast, dif_neg hnat]
      simp

/-- The point map of the shear carries the jets of the doubled family to the jets of the sum. -/
theorem shearPointMap_familyJetVec {m n : ℕ} (f g : Fin m → ℂ → ℂ) (c : ℂ) {z : ℂ}
    (hf : ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (f i) z) (hg : ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z) :
    shearPointMap m n c (familyJetVec (m := m + m) (n := n) (doubledFamily f g) z)
      = familyJetVec (m := m) (n := n) (fun i w => f i w + c * g i w) z := by
  funext s
  cases s with
  | inl x =>
      cases x
      simp [shearPointMap, familyShearJetImage, familyJetVec]
  | inr p =>
      obtain ⟨i, k⟩ := p
      have hfk : ContDiffAt ℂ (((k : ℕ) : ℕ∞)) (f i) z :=
        (hf i).of_le (by exact_mod_cast (le_top : (((k : ℕ) : ℕ∞)) ≤ ⊤))
      have hgk0 : ContDiffAt ℂ (((k : ℕ) : ℕ∞)) (g i) z :=
        (hg i).of_le (by exact_mod_cast (le_top : (((k : ℕ) : ℕ∞)) ≤ ⊤))
      have hgk : ContDiffAt ℂ (((k : ℕ) : ℕ∞)) (fun w => c * g i w) z :=
        (contDiffAt_const (c := c)).mul hgk0
      have hsum : (fun w => f i w + c * g i w) = f i + fun w => c * g i w := rfl
      have hlin : iteratedDeriv (k : ℕ) (fun w => f i w + c * g i w) z
          = iteratedDeriv (k : ℕ) (f i) z + c * iteratedDeriv (k : ℕ) (g i) z := by
        rw [hsum, iteratedDeriv_add hfk hgk]
        congr 1
        exact iteratedDeriv_const_mul c hgk0
      simp only [shearPointMap, familyShearJetImage, Sum.elim_inr, map_add, map_mul,
        MvPolynomial.eval_X, MvPolynomial.eval_C, familyJetVec, Sum.elim_inr,
        doubledFamily_castAdd, doubledFamily_natAdd]
      rw [hlin]

/-- **The shear gauge.**  A differential relation among the sums `f i + c g i` pulls back to a
differential relation among the two families taken together. -/
theorem familyDifferentiallyAlgebraicOn_doubled_of_shear {m : ℕ} {U : Set ℂ}
    (f g : Fin m → ℂ → ℂ) (c : ℂ)
    (hf : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (f i) z)
    (hg : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z)
    (h : FamilyDifferentiallyAlgebraicOn (fun i w => f i w + c * g i w) U) :
    FamilyDifferentiallyAlgebraicOn (doubledFamily f g) U := by
  obtain ⟨n, P, hP, hrel⟩ := h
  refine ⟨n, MvPolynomial.bind₁ (familyShearJetImage m n c) P, ?_, ?_⟩
  · refine subst_ne_zero_of_pointMap_surjective' (MvPolynomial.bind₁ _) (shearPointMap m n c)
      (fun Q v => eval_bind₁_shear c Q v) (surjective_shearPointMap m n c) hP
  · intro z hz
    rw [eval_bind₁_shear, shearPointMap_familyJetVec f g c (fun i => hf z hz i)
      (fun i => hg z hz i)]
    exact hrel z hz

/-- **Joint independence survives a shear.**  If the two families together satisfy no differential
relation, neither do the sums `f i + c g i`. -/
theorem not_familyDifferentiallyAlgebraicOn_shear {m : ℕ} {U : Set ℂ}
    (f g : Fin m → ℂ → ℂ) (c : ℂ)
    (hf : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (f i) z)
    (hg : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z)
    (h : ¬ FamilyDifferentiallyAlgebraicOn (doubledFamily f g) U) :
    ¬ FamilyDifferentiallyAlgebraicOn (fun i w => f i w + c * g i w) U :=
  fun hrel => h (familyDifferentiallyAlgebraicOn_doubled_of_shear f g c hf hg hrel)

end

end GaloisForLFunctions.HTGeometry

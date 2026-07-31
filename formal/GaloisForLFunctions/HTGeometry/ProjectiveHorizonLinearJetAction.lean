import GaloisForLFunctions.HTGeometry.DifferentialPolynomial
import GaloisForLFunctions.HTGeometry.FreeCoordinateField
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonChartSubsetStabilizer

/-!
# The prolonged linear action on the homogeneous jet field

A projective source is presented by a homogeneous lift `X̃`, whose jets `X̃_k^(l)` are the free
coordinates of the rational field `HomogeneousJetField`.  A unimodular matrix moves the source
point linearly, `X̃ ↦ g X̃`, and a rational jet observable is pulled back along the inverse.  Since
the matrix entries are constants, the substitution commutes with the total-derivative jet shift,
so the special linear group acts by differential field automorphisms.

This supplies the algebraic group action required to read the projective observer groups of
`ProjectiveHorizonChartSubsetStabilizer` as symmetries of an actual jet field.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## Linear substitution of homogeneous jets -/

/-- The homogeneous jet field: one free jet tower per homogeneous coordinate. -/
abbrev HomogeneousJetField (n K : Type*) [Field K] :=
  FreeCoordinateRationalField K (n × ℕ)

/-- Linear substitution of the homogeneous jet coordinates by a matrix, jet order by jet order. -/
def linearJetSubstPoly (g : Matrix n n K) :
    MvPolynomial (n × ℕ) K →ₐ[K] MvPolynomial (n × ℕ) K :=
  MvPolynomial.aeval fun p : n × ℕ => ∑ m, MvPolynomial.C (g p.1 m) * MvPolynomial.X (m, p.2)

omit [DecidableEq n] in
@[simp]
theorem linearJetSubstPoly_X (g : Matrix n n K) (k : n) (l : ℕ) :
    linearJetSubstPoly g (MvPolynomial.X (k, l)) =
      ∑ m, MvPolynomial.C (g k m) * MvPolynomial.X (m, l) := by
  simp [linearJetSubstPoly]

omit [DecidableEq n] in
@[simp]
theorem linearJetSubstPoly_C (g : Matrix n n K) (a : K) :
    linearJetSubstPoly g (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [linearJetSubstPoly, MvPolynomial.algebraMap_eq]

omit [DecidableEq n] in
theorem linearJetSubstPoly_comp (g h : Matrix n n K) :
    (linearJetSubstPoly g).comp (linearJetSubstPoly h) = linearJetSubstPoly (h * g) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨k, l⟩
  have hL : (linearJetSubstPoly g).comp (linearJetSubstPoly h) (MvPolynomial.X (k, l)) =
      ∑ m, ∑ q, MvPolynomial.C (h k m * g m q) * MvPolynomial.X (q, l) := by
    rw [AlgHom.comp_apply, linearJetSubstPoly_X, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, linearJetSubstPoly_C, linearJetSubstPoly_X, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [← mul_assoc, ← map_mul]
  have hR : linearJetSubstPoly (h * g) (MvPolynomial.X (k, l)) =
      ∑ q, ∑ m, MvPolynomial.C (h k m * g m q) * MvPolynomial.X (q, l) := by
    rw [linearJetSubstPoly_X]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
  rw [hL, hR, Finset.sum_comm]

@[simp]
theorem linearJetSubstPoly_one :
    linearJetSubstPoly (1 : Matrix n n K) = AlgHom.id K (MvPolynomial (n × ℕ) K) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨k, l⟩
  rw [linearJetSubstPoly_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro m _ hmk
    rw [Matrix.one_apply_ne (Ne.symm hmk)]
    simp
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- Linear substitution by a unimodular matrix is an algebra automorphism. -/
def linearJetSubstEquiv (g : SpecialLinearGroup n K) :
    MvPolynomial (n × ℕ) K ≃ₐ[K] MvPolynomial (n × ℕ) K :=
  AlgEquiv.ofAlgHom (linearJetSubstPoly (g : Matrix n n K))
    (linearJetSubstPoly ((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K))
    (by
      rw [linearJetSubstPoly_comp, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, linearJetSubstPoly_one])
    (by
      rw [linearJetSubstPoly_comp, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, linearJetSubstPoly_one])

@[simp]
theorem linearJetSubstEquiv_apply (g : SpecialLinearGroup n K)
    (p : MvPolynomial (n × ℕ) K) :
    linearJetSubstEquiv g p = linearJetSubstPoly (g : Matrix n n K) p := rfl

/-! ## The action on the homogeneous jet field -/

/-- Pullback of a rational jet observable along the linear motion of the source point. -/
def linearJetFieldEquiv (g : SpecialLinearGroup n K) :
    HomogeneousJetField n K ≃ₐ[K] HomogeneousJetField n K :=
  IsFractionRing.algEquivOfAlgEquiv (linearJetSubstEquiv g⁻¹)

@[simp]
theorem linearJetFieldEquiv_algebraMap (g : SpecialLinearGroup n K)
    (p : MvPolynomial (n × ℕ) K) :
    linearJetFieldEquiv g (algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) p) =
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
        (linearJetSubstPoly ((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) p) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap (linearJetSubstEquiv g⁻¹) p

theorem linearJetFieldEquiv_one_apply (f : HomogeneousJetField n K) :
    linearJetFieldEquiv (1 : SpecialLinearGroup n K) f = f := by
  obtain ⟨x, y, _, rfl⟩ :=
    IsFractionRing.div_surjective (A := MvPolynomial (n × ℕ) K) f
  rw [map_div₀, linearJetFieldEquiv_algebraMap, linearJetFieldEquiv_algebraMap]
  simp

theorem linearJetFieldEquiv_mul_apply (g h : SpecialLinearGroup n K)
    (f : HomogeneousJetField n K) :
    linearJetFieldEquiv (g * h) f = linearJetFieldEquiv g (linearJetFieldEquiv h f) := by
  obtain ⟨x, y, _, rfl⟩ :=
    IsFractionRing.div_surjective (A := MvPolynomial (n × ℕ) K) f
  have hstep : ∀ p : MvPolynomial (n × ℕ) K,
      linearJetSubstPoly ((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K)
          (linearJetSubstPoly ((h⁻¹ : SpecialLinearGroup n K) : Matrix n n K) p) =
        linearJetSubstPoly (((g * h)⁻¹ : SpecialLinearGroup n K) : Matrix n n K) p := by
    intro p
    have hcomp := congrArg (fun F => F p) (linearJetSubstPoly_comp
      ((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K)
      ((h⁻¹ : SpecialLinearGroup n K) : Matrix n n K))
    simp only [AlgHom.comp_apply] at hcomp
    rw [hcomp, ← Matrix.SpecialLinearGroup.coe_mul, ← _root_.mul_inv_rev]
  rw [map_div₀, map_div₀, map_div₀, linearJetFieldEquiv_algebraMap,
    linearJetFieldEquiv_algebraMap, linearJetFieldEquiv_algebraMap,
    linearJetFieldEquiv_algebraMap, linearJetFieldEquiv_algebraMap,
    linearJetFieldEquiv_algebraMap, hstep, hstep]

/-- The prolonged linear action of the special linear group on the homogeneous jet field. -/
instance linearJetMulSemiringAction :
    MulSemiringAction (SpecialLinearGroup n K) (HomogeneousJetField n K) where
  smul g f := linearJetFieldEquiv g f
  one_smul f := linearJetFieldEquiv_one_apply f
  mul_smul g h f := linearJetFieldEquiv_mul_apply g h f
  smul_zero g := map_zero (linearJetFieldEquiv g)
  smul_add g x y := map_add (linearJetFieldEquiv g) x y
  smul_one g := map_one (linearJetFieldEquiv g)
  smul_mul g x y := map_mul (linearJetFieldEquiv g) x y

@[simp]
theorem linearJetAction_apply (g : SpecialLinearGroup n K) (f : HomogeneousJetField n K) :
    g • f = linearJetFieldEquiv g f := rfl

/-- The action on a homogeneous jet coordinate is linear substitution by the inverse matrix. -/
theorem linearJetAction_freeCoordinate (g : SpecialLinearGroup n K) (k : n) (l : ℕ) :
    g • freeCoordinate K (n × ℕ) (k, l) =
      ∑ m, algebraMap K (HomogeneousJetField n K)
          (((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) k m) *
        freeCoordinate K (n × ℕ) (m, l) := by
  rw [linearJetAction_apply, freeCoordinate, linearJetFieldEquiv_algebraMap,
    linearJetSubstPoly_X, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hC : algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
      (MvPolynomial.C (((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) k m)) =
      algebraMap K (HomogeneousJetField n K)
        (((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) k m) := by
    rw [← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)]
  rw [map_mul, hC]
  rfl

/-! ## Compatibility with the jet shift -/

omit [DecidableEq n] in
/-- Linear substitution by constants commutes with the total-derivative jet shift. -/
theorem linearJetSubstPoly_deriv (g : Matrix n n K) (p : MvPolynomial (n × ℕ) K) :
    linearJetSubstPoly g (differentialPolynomialDerivation n K p) =
      differentialPolynomialDerivation n K (linearJetSubstPoly g p) := by
  have hX : ∀ (k : n) (l : ℕ),
      linearJetSubstPoly g (differentialPolynomialDerivation n K (MvPolynomial.X (k, l))) =
        differentialPolynomialDerivation n K
          (linearJetSubstPoly g (MvPolynomial.X (k, l))) := by
    intro k l
    rw [differentialPolynomialDerivation_X, linearJetSubstPoly_X, linearJetSubstPoly_X,
      map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Derivation.leibniz, differentialPolynomialDerivation_X]
    have hC : differentialPolynomialDerivation n K (MvPolynomial.C (g k m)) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]
      exact Derivation.map_algebraMap _ (g k m)
    rw [hC]
    simp [smul_eq_mul]
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hC : differentialPolynomialDerivation n K (MvPolynomial.C a) = 0 := by
        rw [← MvPolynomial.algebraMap_eq]
        exact Derivation.map_algebraMap _ a
      rw [hC, map_zero, linearJetSubstPoly_C, hC]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      obtain ⟨k, l⟩ := i
      have hL : linearJetSubstPoly g (differentialPolynomialDerivation n K
            (p * MvPolynomial.X (k, l))) =
          linearJetSubstPoly g p *
              linearJetSubstPoly g
                (differentialPolynomialDerivation n K (MvPolynomial.X (k, l))) +
            linearJetSubstPoly g (MvPolynomial.X (k, l)) *
              linearJetSubstPoly g (differentialPolynomialDerivation n K p) := by
        rw [Derivation.leibniz]
        simp [smul_eq_mul]
      have hR : differentialPolynomialDerivation n K
            (linearJetSubstPoly g (p * MvPolynomial.X (k, l))) =
          linearJetSubstPoly g p *
              differentialPolynomialDerivation n K
                (linearJetSubstPoly g (MvPolynomial.X (k, l))) +
            linearJetSubstPoly g (MvPolynomial.X (k, l)) *
              differentialPolynomialDerivation n K (linearJetSubstPoly g p) := by
        rw [map_mul, Derivation.leibniz]
        simp [smul_eq_mul]
      rw [hL, hR, hp, hX]

/-! ## Horizon fields of the observer groups -/

theorem linearJetAction_inv (g : SpecialLinearGroup n K) (f : HomogeneousJetField n K) :
    g • f⁻¹ = (g • f)⁻¹ := by
  rw [linearJetAction_apply, linearJetAction_apply, map_inv₀]

theorem linearJetAction_algebraMap (g : SpecialLinearGroup n K) (a : K) :
    g • algebraMap K (HomogeneousJetField n K) a =
      algebraMap K (HomogeneousJetField n K) a := by
  rw [linearJetAction_apply]
  exact (linearJetFieldEquiv g).commutes a

/-- The horizon field of the covector span indexed by `s`: the rational jet observables invariant
under the whole projective observer group `G_S`. -/
def horizonField (s : Set n) : IntermediateField K (HomogeneousJetField n K) where
  carrier := {f | ∀ g ∈ chartSubsetStabilizer (K := K) s, g • f = f}
  zero_mem' := by intro g _; rw [smul_zero]
  one_mem' := by intro g _; rw [smul_one]
  add_mem' := by
    intro x y hx hy g hg
    rw [smul_add, hx g hg, hy g hg]
  mul_mem' := by
    intro x y hx hy g hg
    rw [smul_mul', hx g hg, hy g hg]
  algebraMap_mem' := by
    intro a g _
    exact linearJetAction_algebraMap g a
  inv_mem' := by
    intro x hx g hg
    rw [linearJetAction_inv, hx g hg]

@[simp]
theorem mem_horizonField_iff' {s : Set n} {f : HomogeneousJetField n K} :
    f ∈ horizonField s ↔ ∀ g ∈ chartSubsetStabilizer (K := K) s, g • f = f :=
  Iff.rfl

/-- **Generator criterion for the horizon field.**  An observable lies in the horizon field of `S`
exactly when it is invariant under the chart transvections indexed by `s`.  This is the exact
content of `mathcal I_S = F^(G_S)` read through the unipotent generation law. -/
theorem mem_horizonField_iff {s : Set n} {f : HomogeneousJetField n K} :
    f ∈ horizonField s ↔ ∀ g ∈ chartSubsetTransvectionSet s K, g • f = f :=
  forall_smul_eq_self_chartSubsetStabilizer_iff s f

/-- **Span-to-intersection law for horizon fields.**  `mathcal I_(S+T) = mathcal I_S ∩ mathcal I_T`
on the homogeneous jet field. -/
theorem horizonField_union (s t : Set n) :
    horizonField (n := n) (K := K) (s ∪ t) = horizonField s ⊓ horizonField t := by
  ext f
  rw [mem_horizonField_iff', IntermediateField.mem_inf, mem_horizonField_iff',
    mem_horizonField_iff']
  exact forall_smul_eq_self_chartSubsetStabilizer_union s t f

/-- The horizon-field assignment reverses inclusions: a larger covector span sees less. -/
theorem horizonField_antitone {s t : Set n} (h : s ⊆ t) :
    horizonField (n := n) (K := K) t ≤ horizonField s :=
  fun _ hf g hg => hf g (chartSubsetStabilizer_mono h hg)

end

end GaloisForLFunctions.HTGeometry

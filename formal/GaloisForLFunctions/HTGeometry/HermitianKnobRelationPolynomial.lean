import GaloisForLFunctions.HTGeometry.HermitianCharpolyFactorization
import GaloisForLFunctions.HTGeometry.FiniteWindowOneKnobUniformity

/-!
# The relation polynomial of a Hermitian one-knob family

For a Hermitian affine family `A + g V` the coefficients of the characteristic polynomial are
polynomials in the knob, so every symmetric expression in the spectrum is a polynomial in the knob.
Applied to the product of a balanced linear form over all relabellings of the spectrum, this
produces the relation polynomial that detects a replica resonance: it vanishes exactly when some
relabelling of the balanced form does, and it is dominated by the form itself.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The Hermitian one-knob affine family. -/
def knobMatrix (A V : Matrix I I ℝ) (g : ℝ) : Matrix I I ℝ := A + g • V

omit [Fintype I] [DecidableEq I] in
theorem isHermitian_knobMatrix {A V : Matrix I I ℝ} (hA : A.IsHermitian) (hV : V.IsHermitian)
    (g : ℝ) : (knobMatrix A V g).IsHermitian := by
  rw [Matrix.IsHermitian, knobMatrix, Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
  rw [show Matrix.conjTranspose A = A from hA, show Matrix.conjTranspose V = V from hV,
    star_trivial]

/-- The knob family with the knob kept as a polynomial variable. -/
def knobPolyMatrix (A V : Matrix I I ℝ) : Matrix I I (Polynomial ℝ) :=
  Matrix.of fun i j => Polynomial.C (A i j) + Polynomial.C (V i j) * Polynomial.X

/-- The characteristic polynomial of the knob family, with the knob kept as a polynomial variable. -/
def knobCharpoly (A V : Matrix I I ℝ) : Polynomial (Polynomial ℝ) :=
  (knobPolyMatrix A V).charpoly

omit [Fintype I] [DecidableEq I] in
theorem knobPolyMatrix_map (A V : Matrix I I ℝ) (g : ℝ) :
    (knobPolyMatrix A V).map (Polynomial.evalRingHom g) = knobMatrix A V g := by
  ext i j
  rw [Matrix.map_apply, knobPolyMatrix, knobMatrix]
  simp only [Matrix.of_apply, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem knobCharpoly_map (A V : Matrix I I ℝ) (g : ℝ) :
    (knobMatrix A V g).charpoly = (knobCharpoly A V).map (Polynomial.evalRingHom g) := by
  rw [knobCharpoly, ← Matrix.charpoly_map, knobPolyMatrix_map]

/-- **The characteristic coefficients are polynomials in the knob.** -/
theorem coeff_charpoly_knobMatrix (A V : Matrix I I ℝ) (g : ℝ) (k : ℕ) :
    (knobMatrix A V g).charpoly.coeff k = ((knobCharpoly A V).coeff k).eval g := by
  rw [knobCharpoly_map, Polynomial.coeff_map]
  rfl

/-- The product of a balanced linear form over all relabellings of the spectrum. -/
def relationSymmetric (c : I → ℝ) : MvPolynomial I ℝ :=
  ∏ σ : Equiv.Perm I, ∑ i, MvPolynomial.C (c i) * MvPolynomial.X (σ i)

theorem relationSymmetric_isSymmetric (c : I → ℝ) : (relationSymmetric c).IsSymmetric := by
  intro τ
  rw [relationSymmetric, map_prod]
  have hterm : ∀ σ : Equiv.Perm I,
      MvPolynomial.rename τ (∑ i, MvPolynomial.C (c i) * MvPolynomial.X (σ i))
        = ∑ i, MvPolynomial.C (c i) * MvPolynomial.X ((τ * σ) i) := by
    intro σ
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X]
    rfl
  calc ∏ σ : Equiv.Perm I,
        MvPolynomial.rename τ (∑ i, MvPolynomial.C (c i) * MvPolynomial.X (σ i))
      = ∏ σ : Equiv.Perm I, ∑ i, MvPolynomial.C (c i) * MvPolynomial.X ((τ * σ) i) :=
        Finset.prod_congr rfl fun σ _ => hterm σ
    _ = ∏ σ : Equiv.Perm I, ∑ i, MvPolynomial.C (c i) * MvPolynomial.X (σ i) :=
        Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => rfl

/-- The relation polynomial exists: a symmetric expression in the spectrum is a polynomial in the
elementary symmetric functions. -/
theorem exists_relationSymmetric_esymmAlgHom (c : I → ℝ) :
    ∃ G : MvPolynomial (Fin (Fintype.card I)) ℝ,
      (MvPolynomial.aeval fun i : Fin (Fintype.card I) =>
        MvPolynomial.esymm I ℝ ((i : ℕ) + 1)) G = relationSymmetric c := by
  obtain ⟨G, hG⟩ := MvPolynomial.esymmAlgHom_surjective (σ := I) ℝ (n := Fintype.card I) le_rfl
    ⟨relationSymmetric c, relationSymmetric_isSymmetric c⟩
  refine ⟨G, ?_⟩
  have hval := congrArg (Subtype.val) hG
  rw [MvPolynomial.esymmAlgHom_apply] at hval
  exact hval


/-- **The relation polynomial** of a Hermitian knob family at a balanced coefficient vector: the
product of the balanced form over all relabellings of the spectrum, expressed in the knob. -/
def knobRelationPolynomial (A V : Matrix I I ℝ) (c : I → ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval
    (fun i : Fin (Fintype.card I) =>
      (-1 : Polynomial ℝ) ^ ((i : ℕ) + 1) *
        (knobCharpoly A V).coeff (Fintype.card I - ((i : ℕ) + 1)))
    (Classical.choose (exists_relationSymmetric_esymmAlgHom c))

/-- **The relation polynomial evaluates to the relabelling product of the balanced form.** -/
theorem eval_knobRelationPolynomial {A V : Matrix I I ℝ} (hA : A.IsHermitian) (hV : V.IsHermitian)
    (c : I → ℝ) (g : ℝ) :
    (knobRelationPolynomial A V c).eval g
      = ∏ σ : Equiv.Perm I, ∑ i, c i * (isHermitian_knobMatrix hA hV g).eigenvalues (σ i) := by
  classical
  set G := Classical.choose (exists_relationSymmetric_esymmAlgHom c) with hG
  have hGspec : (MvPolynomial.aeval fun i : Fin (Fintype.card I) =>
      MvPolynomial.esymm I ℝ ((i : ℕ) + 1)) G = relationSymmetric c :=
    Classical.choose_spec (exists_relationSymmetric_esymmAlgHom c)
  set lam : I → ℝ := (isHermitian_knobMatrix hA hV g).eigenvalues with hlam
  -- the relabelling product is the evaluation of the symmetric relation polynomial
  have hprod : MvPolynomial.aeval lam (relationSymmetric c)
      = ∏ σ : Equiv.Perm I, ∑ i, c i * lam (σ i) := by
    rw [relationSymmetric, map_prod]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    rfl
  -- each elementary symmetric function of the spectrum is a knob polynomial
  have hesymm : ∀ i : Fin (Fintype.card I),
      MvPolynomial.aeval lam (MvPolynomial.esymm I ℝ ((i : ℕ) + 1))
        = ((-1 : Polynomial ℝ) ^ ((i : ℕ) + 1) *
            (knobCharpoly A V).coeff (Fintype.card I - ((i : ℕ) + 1))).eval g := by
    intro i
    have hle : ((i : ℕ) + 1) ≤ Fintype.card I := i.2
    have hlem := isHermitian_esymm_eigenvalues_eq_coeff (𝕜 := ℝ)
      (isHermitian_knobMatrix hA hV g) hle
    rw [coeff_charpoly_knobMatrix] at hlem
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one]
    exact hlem
  -- transport the identity through both algebra homomorphisms
  have hleft : (knobRelationPolynomial A V c).eval g
      = MvPolynomial.aeval (fun i : Fin (Fintype.card I) =>
          ((-1 : Polynomial ℝ) ^ ((i : ℕ) + 1) *
            (knobCharpoly A V).coeff (Fintype.card I - ((i : ℕ) + 1))).eval g) G := by
    rw [knobRelationPolynomial, ← hG]
    have hcomp := MvPolynomial.comp_aeval
      (f := fun i : Fin (Fintype.card I) =>
        (-1 : Polynomial ℝ) ^ ((i : ℕ) + 1) *
          (knobCharpoly A V).coeff (Fintype.card I - ((i : ℕ) + 1)))
      (φ := Polynomial.aeval (R := ℝ) g)
    have happ := congrArg (fun F : MvPolynomial (Fin (Fintype.card I)) ℝ →ₐ[ℝ] ℝ => F G) hcomp
    simp only [AlgHom.comp_apply] at happ
    simpa only [Polynomial.coe_aeval_eq_eval] using happ
  have hright : MvPolynomial.aeval lam (relationSymmetric c)
      = MvPolynomial.aeval (fun i : Fin (Fintype.card I) =>
          MvPolynomial.aeval lam (MvPolynomial.esymm I ℝ ((i : ℕ) + 1))) G := by
    rw [← hGspec]
    have hcomp := MvPolynomial.comp_aeval
      (f := fun i : Fin (Fintype.card I) => MvPolynomial.esymm I ℝ ((i : ℕ) + 1))
      (φ := MvPolynomial.aeval lam)
    have happ := congrArg (fun F : MvPolynomial (Fin (Fintype.card I)) ℝ →ₐ[ℝ] ℝ => F G) hcomp
    simp only [AlgHom.comp_apply] at happ
    exact happ
  rw [hleft, ← hprod, hright]
  refine congrArg (fun f => MvPolynomial.aeval f G) ?_
  funext i
  exact (hesymm i).symm


/-- **Crude eigenvalue bound.**  Every eigenvalue of a Hermitian matrix is bounded by the sum of the
absolute values of its entries. -/
theorem abs_eigenvalues_le_entrySum {A : Matrix I I ℝ} (hA : A.IsHermitian) (j : I) :
    |hA.eigenvalues j| ≤ ∑ i, ∑ k, |A i k| := by
  classical
  set x : I → ℝ := (hA.eigenvectorBasis j).ofLp with hx
  have hmul : A.mulVec x = hA.eigenvalues j • x := hA.mulVec_eigenvectorBasis j
  have hnorm : ‖(hA.eigenvectorBasis j : EuclideanSpace ℝ I)‖ = 1 :=
    OrthonormalBasis.norm_eq_one _ j
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|)
    ⟨j, Finset.mem_univ j⟩
  have hpos : 0 < |x i₀| := by
    rcases lt_or_eq_of_le (abs_nonneg (x i₀)) with h | h
    · exact h
    · exfalso
      have hall : ∀ i, x i = 0 := by
        intro i
        have hle := hmax i (Finset.mem_univ i)
        have : |x i| ≤ 0 := by rw [← h] at hle; exact hle
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      rw [EuclideanSpace.norm_eq] at hnorm
      have hsum : ∑ i, ‖(hA.eigenvectorBasis j : EuclideanSpace ℝ I) i‖ ^ (2 : ℕ) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        have : ((hA.eigenvectorBasis j : EuclideanSpace ℝ I) i) = 0 := hall i
        rw [this, norm_zero]
        norm_num
      rw [hsum, Real.sqrt_zero] at hnorm
      exact zero_ne_one hnorm
  have hrow : hA.eigenvalues j * x i₀ = ∑ k, A i₀ k * x k := by
    have happ := congrFun hmul i₀
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at happ
    exact happ.symm
  have hbound : |hA.eigenvalues j| * |x i₀| ≤ (∑ k, |A i₀ k|) * |x i₀| := by
    calc |hA.eigenvalues j| * |x i₀| = |hA.eigenvalues j * x i₀| := (abs_mul _ _).symm
      _ = |∑ k, A i₀ k * x k| := by rw [hrow]
      _ ≤ ∑ k, |A i₀ k * x k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, |A i₀ k| * |x i₀| := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hmax k (Finset.mem_univ k)) (abs_nonneg _)
      _ = (∑ k, |A i₀ k|) * |x i₀| := by rw [Finset.sum_mul]
  have hrowbound : |hA.eigenvalues j| ≤ ∑ k, |A i₀ k| :=
    le_of_mul_le_mul_right hbound hpos
  refine le_trans hrowbound ?_
  exact Finset.single_le_sum (f := fun i => ∑ k, |A i k|)
    (fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _) (Finset.mem_univ i₀)


/-- The spectrum of the Hermitian knob family as a knob-dependent energy vector. -/
def hermitianKnobSpectrum {A V : Matrix I I ℝ} (hA : A.IsHermitian) (hV : V.IsHermitian)
    (g : ℝ) : I → ℝ := (isHermitian_knobMatrix hA hV g).eigenvalues

theorem abs_hermitianKnobSpectrum_le {A V : Matrix I I ℝ} (hA : A.IsHermitian)
    (hV : V.IsHermitian) {Rad g : ℝ} (hg : |g| ≤ Rad) (j : I) :
    |hermitianKnobSpectrum hA hV g j|
      ≤ (∑ i, ∑ k, |A i k|) + Rad * ∑ i, ∑ k, |V i k| := by
  classical
  refine le_trans (abs_eigenvalues_le_entrySum (isHermitian_knobMatrix hA hV g) j) ?_
  have hentry : ∀ i k, |knobMatrix A V g i k| ≤ |A i k| + Rad * |V i k| := by
    intro i k
    have hval : knobMatrix A V g i k = A i k + g * V i k := by
      rw [knobMatrix]
      simp [Matrix.add_apply, Matrix.smul_apply]
    rw [hval]
    refine le_trans (abs_add_le _ _) ?_
    have : |g * V i k| = |g| * |V i k| := abs_mul _ _
    rw [this]
    have hle : |g| * |V i k| ≤ Rad * |V i k| :=
      mul_le_mul_of_nonneg_right hg (abs_nonneg (V i k))
    linarith
  calc ∑ i, ∑ k, |knobMatrix A V g i k| ≤ ∑ i, ∑ k, (|A i k| + Rad * |V i k|) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hentry i k
    _ = (∑ i, ∑ k, |A i k|) + Rad * ∑ i, ∑ k, |V i k| := by
        rw [Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]

/-- **The relation polynomial is dominated by the balanced form.**  Its other factors are bounded by
the entry sums of the family on a bounded knob range. -/
theorem abs_eval_knobRelationPolynomial_le {A V : Matrix I I ℝ} (hA : A.IsHermitian)
    (hV : V.IsHermitian) (c : I → ℝ) {Rad g : ℝ} (hg : |g| ≤ Rad) :
    |(knobRelationPolynomial A V c).eval g|
      ≤ ((∑ i, |c i|) * ((∑ i, ∑ k, |A i k|) + Rad * ∑ i, ∑ k, |V i k|))
            ^ (Fintype.card (Equiv.Perm I) - 1)
          * |∑ i, c i * hermitianKnobSpectrum hA hV g i| := by
  classical
  set lam : I → ℝ := hermitianKnobSpectrum hA hV g with hlam
  set B : ℝ := (∑ i, |c i|) * ((∑ i, ∑ k, |A i k|) + Rad * ∑ i, ∑ k, |V i k|) with hB
  have hfactor : ∀ σ : Equiv.Perm I, |∑ i, c i * lam (σ i)| ≤ B := by
    intro σ
    calc |∑ i, c i * lam (σ i)| ≤ ∑ i, |c i * lam (σ i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |c i| * ((∑ i, ∑ k, |A i k|) + Rad * ∑ i, ∑ k, |V i k|) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_hermitianKnobSpectrum_le hA hV hg (σ i))
            (abs_nonneg _)
      _ = B := by rw [hB, Finset.sum_mul]
  have hprodrw : |(knobRelationPolynomial A V c).eval g|
      = ∏ σ : Equiv.Perm I, |∑ i, c i * lam (σ i)| := by
    rw [eval_knobRelationPolynomial hA hV c g, Finset.abs_prod]
    rfl
  rw [hprodrw, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : Equiv.Perm I))]
  have hone : |∑ i, c i * lam ((1 : Equiv.Perm I) i)| = |∑ i, c i * lam i| := rfl
  have htail : ∏ σ ∈ Finset.univ.erase (1 : Equiv.Perm I), |∑ i, c i * lam (σ i)|
      ≤ B ^ (Fintype.card (Equiv.Perm I) - 1) := by
    have hcard : (Finset.univ.erase (1 : Equiv.Perm I)).card
        = Fintype.card (Equiv.Perm I) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    calc ∏ σ ∈ Finset.univ.erase (1 : Equiv.Perm I), |∑ i, c i * lam (σ i)|
        ≤ ∏ _σ ∈ Finset.univ.erase (1 : Equiv.Perm I), B :=
          Finset.prod_le_prod (fun σ _ => abs_nonneg _) (fun σ _ => hfactor σ)
      _ = B ^ (Finset.univ.erase (1 : Equiv.Perm I)).card := by rw [Finset.prod_const]
      _ = B ^ (Fintype.card (Equiv.Perm I) - 1) := by rw [hcard]
  have hRad : (0 : ℝ) ≤ Rad := le_trans (abs_nonneg g) hg
  have hBnonneg : 0 ≤ B ^ (Fintype.card (Equiv.Perm I) - 1) := by
    refine pow_nonneg ?_ _
    rw [hB]
    refine mul_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) ?_
    refine add_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _) ?_
    exact mul_nonneg hRad (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _)
  rw [hone]
  calc |∑ i, c i * lam i| * ∏ σ ∈ Finset.univ.erase (1 : Equiv.Perm I), |∑ i, c i * lam (σ i)|
      ≤ |∑ i, c i * lam i| * B ^ (Fintype.card (Equiv.Perm I) - 1) :=
        mul_le_mul_of_nonneg_left htail (abs_nonneg _)
    _ = B ^ (Fintype.card (Equiv.Perm I) - 1) * |∑ i, c i * lam i| := by ring


theorem oneKnobDetuning_hermitianKnobSpectrum {A V : Matrix I I ℝ} (hA : A.IsHermitian)
    (hV : V.IsHermitian) (g : ℝ) (p q : I → ℕ) :
    oneKnobDetuning (hermitianKnobSpectrum hA hV) g p q
      = ∑ i, ((p i : ℝ) - (q i : ℝ)) * hermitianKnobSpectrum hA hV g i := by
  rw [oneKnobDetuning, replicaMultiplicityEnergy, replicaMultiplicityEnergy,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The Hermitian knob family carries relation-probe data.**  The relation polynomial of each
replica multiplicity pair is dominated by the corresponding detuning, and the card's hypothesis
supplies its nonvanishing. -/
def hermitianReplicaRelationDetection {A V : Matrix I I ℝ} (hA : A.IsHermitian)
    (hV : V.IsHermitian) {Rad : ℝ} {J : Set ℝ} (hJ : ∀ g ∈ J, |g| ≤ Rad) (M : ℕ)
    (hnz : ∀ x ∈ replicaPairIndex I M,
      (∀ g ∈ J, oneKnobDetuning (hermitianKnobSpectrum hA hV) g x.2.1 x.2.2 = 0) ∨
        knobRelationPolynomial A V (fun i => (x.2.1 i : ℝ) - (x.2.2 i : ℝ)) ≠ 0) :
    ReplicaRelationDetection (hermitianKnobSpectrum hA hV) J M where
  probe := fun x g =>
    |(knobRelationPolynomial A V (fun i => (x.2.1 i : ℝ) - (x.2.2 i : ℝ))).eval g|
  probe_continuous := fun x =>
    ((knobRelationPolynomial A V (fun i => (x.2.1 i : ℝ) - (x.2.2 i : ℝ))).continuous).abs
  probe_nonneg := fun _ _ => abs_nonneg _
  const := fun x => max 1
    (((∑ i, |(x.2.1 i : ℝ) - (x.2.2 i : ℝ)|) *
      ((∑ i, ∑ k, |A i k|) + Rad * ∑ i, ∑ k, |V i k|)) ^ (Fintype.card (Equiv.Perm I) - 1))
  const_pos := fun _ => lt_of_lt_of_le one_pos (le_max_left _ _)
  dominate := by
    intro x g hg
    refine le_trans (abs_eval_knobRelationPolynomial_le hA hV _ (hJ g hg)) ?_
    rw [oneKnobDetuning_hermitianKnobSpectrum]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
  degenerate_or_finiteZeros := by
    intro x hx
    rcases hnz x hx with hdeg | hne
    · exact Or.inl hdeg
    · refine Or.inr ((Polynomial.finite_setOf_isRoot hne).subset fun g hg => ?_)
      exact abs_eq_zero.mp hg

/-- **Fixed-order one-knob robustness for a Hermitian affine family.**  Outside a finite set of knob
values, every compact knob set carries one finite-window error bound valid for all replica orders
through `M` and all window lengths. -/
theorem hermitian_exists_uniform_finiteWindow_certificate {A V : Matrix I I ℝ} (hA : A.IsHermitian)
    (hV : V.IsHermitian) {Rad : ℝ} {J : Set ℝ} (hJ : ∀ g ∈ J, |g| ≤ Rad) (M : ℕ)
    (hnz : ∀ x ∈ replicaPairIndex I M,
      (∀ g ∈ J, oneKnobDetuning (hermitianKnobSpectrum hA hV) g x.2.1 x.2.2 = 0) ∨
        knobRelationPolynomial A V (fun i => (x.2.1 i : ℝ) - (x.2.2 i : ℝ)) ≠ 0)
    {weight : I → ℝ} (hweight : ∀ i, 0 ≤ weight i) (hweightSum : ∑ i, weight i = 1) :
    ∃ R : Set ℝ, R.Finite ∧ ∀ K : Set ℝ, IsCompact K → K ⊆ J → (∀ g ∈ K, g ∉ R) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ K, ∀ n ≤ M, ∀ T : ℝ, 0 < T →
        ‖finiteSpectralSurvivalFidelityMean weight (hermitianKnobSpectrum hA hV g) n T -
            (fidelityReplicaCollisionMass weight (hermitianKnobSpectrum hA hV g) n : ℂ)‖
          ≤ min 1 (T * δ)⁻¹ := by
  refine ⟨exceptionalKnobSet (hermitianReplicaRelationDetection hA hV hJ M hnz) ∩ J,
    (finite_exceptionalKnobSet _).subset Set.inter_subset_left, fun K hK hKJ hKR => ?_⟩
  refine exists_uniform_finiteWindow_certificate (hermitianReplicaRelationDetection hA hV hJ M hnz)
    hK hKJ ?_ hweight hweightSum
  intro g hg hcon
  exact hKR g hg ⟨hcon, hKJ hg⟩

end

end GaloisForLFunctions.HTGeometry

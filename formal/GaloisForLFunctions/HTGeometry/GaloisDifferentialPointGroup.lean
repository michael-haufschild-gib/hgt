import GaloisForLFunctions.HTGeometry.GaloisMonoidRootDeterminant

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

universe u

variable {K R C : Type u} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]

/-- The point specialization, regarded over the difference base field. -/
def galoisAutAtK (E : Subalgebra C (R ⊗[K] R)) {ι : Type*}
    (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (χ : E →ₐ[C] C) : R →ₐ[K] R :=
  rightComponent ((torsorSpecialization E b hgen hindep χ).restrictScalars K)

@[simp] theorem galoisAutAtK_apply (E : Subalgebra C (R ⊗[K] R)) {ι : Type*}
    (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (χ : E →ₐ[C] C) (x : R) :
    galoisAutAtK E b hgen hindep χ x = galoisAutAt E b hgen hindep χ x := rfl

/-- Torsor specialization intertwines the tensor difference operator. -/
theorem torsorSpecialization_sigma
    (E : Subalgebra C (R ⊗[K] R)) {ι : Type*}
    (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hEσ : ∀ e ∈ E, differenceTensorEquiv σK σR hcompat e = e)
    (χ : E →ₐ[C] C) (a : R ⊗[K] R) :
    torsorSpecialization E b hgen hindep χ
        (differenceTensorEquiv σK σR hcompat a) =
      σR (torsorSpecialization E b hgen hindep χ a) := by
  have ha : a ∈ Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) := by
    rw [hgen]
    trivial
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
      rcases hx with ⟨r, rfl⟩ | hxE
      · change torsorSpecialization E b hgen hindep χ
          (differenceTensorEquiv σK σR hcompat (r ⊗ₜ[K] (1 : R))) = _
        rw [differenceTensorEquiv_tmul, map_one]
        have hval : torsorSpecialization E b hgen hindep χ
            (σR r ⊗ₜ[K] (1 : R)) = σR r := by
          change torsorSpecialization E b hgen hindep χ
            (algebraMap R (R ⊗[K] R) (σR r)) = σR r
          rw [AlgHom.commutes]
          rw [Algebra.algebraMap_self, RingHom.id_apply]
        rw [hval, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      · rw [hEσ x hxE]
        have hx := torsorSpecialization_coe E b hgen hindep χ ⟨x, hxE⟩
        rw [hx, hconstC]
  | algebraMap c =>
      have hc : algebraMap C (R ⊗[K] R) c =
          (algebraMap C R c) ⊗ₜ[K] (1 : R) := by
        rw [IsScalarTower.algebraMap_apply C R (R ⊗[K] R)]
        rfl
      rw [hc, differenceTensorEquiv_tmul, map_one, hconstC]
      have hval : torsorSpecialization E b hgen hindep χ
          ((algebraMap C R c) ⊗ₜ[K] (1 : R)) = algebraMap C R c := by
        change torsorSpecialization E b hgen hindep χ
          (algebraMap R (R ⊗[K] R) (algebraMap C R c)) = algebraMap C R c
        rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      rw [hval, hconstC]
  | add x y _ _ hx hy =>
      rw [map_add, map_add, map_add, hx, hy, map_add]
  | mul x y _ _ hx hy =>
      rw [map_mul, map_mul, map_mul, hx, hy, map_mul]

/-- Every torsor point gives a difference endomorphism. -/
theorem galoisAutAtK_sigma
    (E : Subalgebra C (R ⊗[K] R)) {ι : Type*}
    (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hEσ : ∀ e ∈ E, differenceTensorEquiv σK σR hcompat e = e)
    (χ : E →ₐ[C] C) (x : R) :
    galoisAutAtK E b hgen hindep χ (σR x) =
      σR (galoisAutAtK E b hgen hindep χ x) := by
  let φ := galoisAutAtK E b hgen hindep χ
  have ht := torsorSpecialization_sigma E b hgen hindep hcompat hconstC hEσ χ
    ((1 : R) ⊗ₜ[K] x)
  rw [differenceTensorEquiv_tmul, map_one] at ht
  exact ht

/-- Every torsor point gives an injective difference endomorphism of a sigma-simple ring. -/
theorem galoisAutAtK_injective
    (E : Subalgebra C (R ⊗[K] R)) {ι : Type*}
    (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hEσ : ∀ e ∈ E, differenceTensorEquiv σK σR hcompat e = e)
    (hsimple : IsSigmaSimple σR) (χ : E →ₐ[C] C) :
    Function.Injective (galoisAutAtK E b hgen hindep χ) := by
  let φ := galoisAutAtK E b hgen hindep χ
  have hcomm : ∀ x : R, φ (σR x) = σR (φ x) :=
    galoisAutAtK_sigma E b hgen hindep hcompat hconstC hEσ χ
  have hker : IsSigmaIdeal σR (RingHom.ker φ) := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    rw [hcomm, hx, map_zero]
  rcases hsimple (RingHom.ker φ) hker with hbot | htop
  · exact (RingHom.injective_iff_ker_eq_bot φ).mpr hbot
  · exact False.elim ((RingHom.ker_ne_top φ) htop)

/-- Picard--Vessiot generation makes the point endomorphism surjective. -/
theorem galoisAutAtK_surjective_of_pvGeneration
    (E : Subalgebra C (R ⊗[K] R)) {ι : Type*}
    (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (χ : E →ₐ[C] C)
    (Y : Matrix (Fin 2) (Fin 2) R)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hGdet : IsUnit (galoisMatrixAt E Z hZE χ).det)
    (u : R) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin 2 × Fin 2 => Y p.1 p.2) ∪ {u}) = ⊤) :
    Function.Surjective (galoisAutAtK E b hgen hindep χ) := by
  classical
  let φ := galoisAutAtK E b hgen hindep χ
  let G := galoisMatrixAt E Z hZE χ
  let GR : Matrix (Fin 2) (Fin 2) R := G.map (algebraMap C R)
  let GI : Matrix (Fin 2) (Fin 2) C := G⁻¹
  let GIR : Matrix (Fin 2) (Fin 2) R := GI.map (algebraMap C R)
  have hφconst : ∀ c : C, φ (algebraMap C R c) = algebraMap C R c := by
    intro c
    rw [IsScalarTower.algebraMap_apply C K R c, AlgHom.commutes]
  have hφY : Y.map (φ : R → R) = Y * GR := by
    ext i j
    rw [Matrix.map_apply, galoisAutAtK_apply,
      galoisAutAt_fundamental E b hgen hindep χ Y Z hZE hZ, Matrix.mul_apply]
    rfl
  have hφGIR : GIR.map (φ : R → R) = GIR := by
    ext i j
    change φ (algebraMap C R (GI i j)) = algebraMap C R (GI i j)
    exact hφconst (GI i j)
  have hGGI : G * GI = 1 := Matrix.mul_nonsing_inv G hGdet
  have hpreY : (Y * GIR).map (φ : R → R) = Y := by
    rw [Matrix.map_mul, hφY, hφGIR, mul_assoc]
    have hGRI : GR * GIR = 1 := by
      change G.map (algebraMap C R) * (G⁻¹).map (algebraMap C R) = 1
      rw [← Matrix.map_mul, hGGI]
      simp
    rw [hGRI, Matrix.mul_one]
  have hYrange : ∀ i j, Y i j ∈ φ.range := by
    intro i j
    refine ⟨(Y * GIR) i j, ?_⟩
    exact congrFun (congrFun hpreY i) j
  have hφdet : φ Y.det = Y.det * algebraMap C R G.det := by
    have hmap := RingHom.map_det φ.toRingHom Y
    rw [RingHom.mapMatrix_apply] at hmap
    change φ Y.det = (Y.map (φ : R → R)).det at hmap
    rw [hφY, Matrix.det_mul] at hmap
    have hdetGR : GR.det = algebraMap C R G.det := by
      change (G.map (algebraMap C R)).det = algebraMap C R G.det
      have hd := RingHom.map_det (algebraMap C R) G
      rw [RingHom.mapMatrix_apply] at hd
      exact hd.symm
    rw [hdetGR] at hmap
    exact hmap
  have hφu : φ u * (Y.det * algebraMap C R G.det) = 1 := by
    calc
      φ u * (Y.det * algebraMap C R G.det) = φ Y.det * φ u := by rw [hφdet]; ring
      _ = φ (Y.det * u) := by rw [map_mul]
      _ = 1 := by rw [hu, map_one]
  have hYdet : IsUnit Y.det := by
    refine ⟨⟨Y.det, u, hu, ?_⟩, rfl⟩
    exact mul_eq_one_comm.mp hu
  have hcancel : algebraMap C R G.det * φ u = u := by
    apply hYdet.mul_left_cancel
    calc
      Y.det * (algebraMap C R G.det * φ u) = φ u * (Y.det * algebraMap C R G.det) := by ring
      _ = 1 := hφu
      _ = Y.det * u := hu.symm
  have hurange : u ∈ φ.range := by
    refine ⟨algebraMap C R G.det * u, ?_⟩
    rw [map_mul]
    change φ (algebraMap C R G.det) * φ u = u
    rw [hφconst, hcancel]
  have hgens : Set.range (fun p : Fin 2 × Fin 2 => Y p.1 p.2) ∪ {u} ⊆ φ.range := by
    rintro x (⟨p, rfl⟩ | hx)
    · exact hYrange p.1 p.2
    · rw [Set.mem_singleton_iff] at hx
      rwa [hx]
  have hrange : φ.range = ⊤ := by
    apply top_unique
    rw [← htop]
    exact Algebra.adjoin_le hgens
  intro x
  have hx : x ∈ φ.range := by rw [hrange]; trivial
  exact hx

/-- Tensor specialization attached to a base-field automorphism. -/
def automorphismTensorSpecialization (φ : R ≃ₐ[K] R) : (R ⊗[K] R) →ₐ[K] R :=
  Algebra.TensorProduct.lift (AlgHom.id K R) φ.toAlgHom (fun _ _ => Commute.all _ _)

@[simp] theorem automorphismTensorSpecialization_tmul (φ : R ≃ₐ[K] R) (x y : R) :
    automorphismTensorSpecialization φ (x ⊗ₜ[K] y) = x * φ y := by
  rw [automorphismTensorSpecialization, Algebra.TensorProduct.lift_tmul]
  rfl

/-- Tensor specialization intertwines sigma when the automorphism does. -/
theorem automorphismTensorSpecialization_sigma
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (φ : R ≃ₐ[K] R) (hφσ : ∀ x : R, φ (σR x) = σR (φ x))
    (a : R ⊗[K] R) :
    automorphismTensorSpecialization φ (differenceTensorEquiv σK σR hcompat a) =
      σR (automorphismTensorSpecialization φ a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [differenceTensorEquiv_tmul, automorphismTensorSpecialization_tmul,
        automorphismTensorSpecialization_tmul, hφσ, map_mul]
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy, map_add]

/-- The unique base constant representing a sigma constant. -/
def sigmaConstantPreimage {σR : R ≃+* R}
    (hnew : ∀ x : R, σR x = x → ∃ c : C, x = algebraMap C R c)
    (x : R) (hx : σR x = x) : C :=
  Classical.choose (hnew x hx)

theorem algebraMap_sigmaConstantPreimage {σR : R ≃+* R}
    (hnew : ∀ x : R, σR x = x → ∃ c : C, x = algebraMap C R c)
    (x : R) (hx : σR x = x) :
    algebraMap C R (sigmaConstantPreimage hnew x hx) = x :=
  (Classical.choose_spec (hnew x hx)).symm

/-- A difference automorphism induces a rational point of every tensor-constant subalgebra. -/
def pointOfDifferenceAut
    (E : Subalgebra C (R ⊗[K] R))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hEσ : ∀ e ∈ E, differenceTensorEquiv σK σR hcompat e = e)
    (hnew : ∀ x : R, σR x = x → ∃ c : C, x = algebraMap C R c)
    (φ : R ≃ₐ[K] R) (hφσ : ∀ x : R, φ (σR x) = σR (φ x)) : E →ₐ[C] C := by
  let ψ := automorphismTensorSpecialization φ
  have hfixed : ∀ e : E, σR (ψ (e : R ⊗[K] R)) = ψ e := by
    intro e
    rw [← automorphismTensorSpecialization_sigma hcompat φ hφσ]
    rw [hEσ e e.2]
  let val : E → C := fun e => sigmaConstantPreimage hnew (ψ e) (hfixed e)
  have hval : ∀ e : E, algebraMap C R (val e) = ψ e := by
    intro e
    exact algebraMap_sigmaConstantPreimage hnew (ψ e) (hfixed e)
  have hinj : Function.Injective (algebraMap C R) := (algebraMap C R).injective
  refine
    { toFun := val
      map_one' := hinj (by
        rw [hval]
        simp [ψ])
      map_zero' := hinj (by
        calc
          algebraMap C R (val 0) = ψ 0 := hval 0
          _ = 0 := map_zero ψ
          _ = algebraMap C R 0 := (map_zero (algebraMap C R)).symm)
      map_add' := fun x y => hinj (by
        calc
          algebraMap C R (val (x + y)) = ψ (x + y) := hval (x + y)
          _ = ψ (x : R ⊗[K] R) + ψ (y : R ⊗[K] R) := by rw [map_add]
          _ = algebraMap C R (val x) + algebraMap C R (val y) := by
            rw [← hval x, ← hval y]
          _ = algebraMap C R (val x + val y) := (map_add (algebraMap C R) _ _).symm)
      map_mul' := fun x y => hinj (by
        calc
          algebraMap C R (val (x * y)) = ψ (x * y) := hval (x * y)
          _ = ψ (x : R ⊗[K] R) * ψ (y : R ⊗[K] R) := by rw [map_mul]
          _ = algebraMap C R (val x) * algebraMap C R (val y) := by
            rw [← hval x, ← hval y]
          _ = algebraMap C R (val x * val y) := (map_mul (algebraMap C R) _ _).symm)
      commutes' := fun c => hinj (by
        rw [hval]
        change ψ (algebraMap C (R ⊗[K] R) c) = algebraMap C R c
        rw [IsScalarTower.algebraMap_apply C K (R ⊗[K] R), AlgHom.commutes,
          IsScalarTower.algebraMap_apply C K R]) }

theorem algebraMap_pointOfDifferenceAut
    (E : Subalgebra C (R ⊗[K] R))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hEσ : ∀ e ∈ E, differenceTensorEquiv σK σR hcompat e = e)
    (hnew : ∀ x : R, σR x = x → ∃ c : C, x = algebraMap C R c)
    (φ : R ≃ₐ[K] R) (hφσ : ∀ x : R, φ (σR x) = σR (φ x)) (e : E) :
    algebraMap C R (pointOfDifferenceAut E hcompat hconstC hEσ hnew φ hφσ e) =
      automorphismTensorSpecialization φ e := by
  have hfix : σR (automorphismTensorSpecialization φ (e : R ⊗[K] R)) =
      automorphismTensorSpecialization φ e := by
    rw [← automorphismTensorSpecialization_sigma hcompat φ hφσ]
    rw [hEσ e e.2]
  unfold pointOfDifferenceAut
  apply algebraMap_sigmaConstantPreimage

variable [Differential K] [Differential R] [DifferentialAlgebra K R]

/-- Tensor specialization intertwines the tensor derivation for a differential automorphism. -/
theorem automorphismTensorSpecialization_deriv
    (φ : R ≃ₐ[K] R)
    (hφδ : ∀ x : R, φ (Differential.deriv x) = Differential.deriv (φ x))
    (a : R ⊗[K] R) :
    automorphismTensorSpecialization φ (tensorSquareDerivation (K := K) a) =
      Differential.deriv (automorphismTensorSpecialization φ a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [tensorSquareDerivation_tmul, map_add, automorphismTensorSpecialization_tmul,
        automorphismTensorSpecialization_tmul, automorphismTensorSpecialization_tmul,
        Derivation.leibniz, smul_eq_mul, smul_eq_mul, hφδ]
      ring
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy, map_add]

variable [Differential C] [DifferentialAlgebra C R]

/-- The point induced by a differential automorphism is a differential point. -/
theorem pointOfDifferenceAut_deriv
    (E : Subalgebra C (R ⊗[K] R))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hEσ : ∀ e ∈ E, differenceTensorEquiv σK σR hcompat e = e)
    (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E)
    (hnew : ∀ x : R, σR x = x → ∃ c : C, x = algebraMap C R c)
    (φ : R ≃ₐ[K] R) (hφσ : ∀ x : R, φ (σR x) = σR (φ x))
    (hφδ : ∀ x : R, φ (Differential.deriv x) = Differential.deriv (φ x))
    (e : R ⊗[K] R) (he : e ∈ E) :
    pointOfDifferenceAut E hcompat hconstC hEσ hnew φ hφσ
        ⟨tensorSquareDerivation (K := K) e, hEδ e he⟩ =
      Differential.deriv
        (pointOfDifferenceAut E hcompat hconstC hEσ hnew φ hφσ ⟨e, he⟩) := by
  apply (algebraMap C R).injective
  calc
    algebraMap C R
        (pointOfDifferenceAut E hcompat hconstC hEσ hnew φ hφσ
          ⟨tensorSquareDerivation (K := K) e, hEδ e he⟩) =
        automorphismTensorSpecialization φ (tensorSquareDerivation (K := K) e) :=
      algebraMap_pointOfDifferenceAut E hcompat hconstC hEσ hnew φ hφσ _
    _ = Differential.deriv (automorphismTensorSpecialization φ e) :=
      automorphismTensorSpecialization_deriv φ hφδ e
    _ = Differential.deriv
        (algebraMap C R
          (pointOfDifferenceAut E hcompat hconstC hEσ hnew φ hφσ ⟨e, he⟩)) := by
      rw [algebraMap_pointOfDifferenceAut]
    _ = algebraMap C R
        (Differential.deriv
          (pointOfDifferenceAut E hcompat hconstC hEσ hnew φ hφσ ⟨e, he⟩)) :=
      DifferentialAlgebra.deriv_algebraMap _

omit [Differential K] [Differential R] [DifferentialAlgebra K R]
    [Differential C] [DifferentialAlgebra C R] in
/-- Constructing a point from an automorphism and specializing it recovers that automorphism. -/
theorem galoisAutAtK_pointOfDifferenceAut
    (E : Subalgebra C (R ⊗[K] R)) {ι : Type*}
    (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hEσ : ∀ e ∈ E, differenceTensorEquiv σK σR hcompat e = e)
    (hnew : ∀ x : R, σR x = x → ∃ c : C, x = algebraMap C R c)
    (φ : R ≃ₐ[K] R) (hφσ : ∀ x : R, φ (σR x) = σR (φ x)) :
    galoisAutAtK E b hgen hindep
        (pointOfDifferenceAut E hcompat hconstC hEσ hnew φ hφσ) = φ.toAlgHom := by
  let χ := pointOfDifferenceAut E hcompat hconstC hEσ hnew φ hφσ
  let ψ := automorphismTensorSpecialization φ
  have heq : ∀ a : R ⊗[K] R,
      torsorSpecialization E b hgen hindep χ a = ψ a := by
    intro a
    have ha : a ∈ Algebra.adjoin C
        (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) := by
      rw [hgen]
      trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
        rcases hx with ⟨r, rfl⟩ | hxE
        · calc
            torsorSpecialization E b hgen hindep χ (r ⊗ₜ[K] (1 : R)) = r := by
              change torsorSpecialization E b hgen hindep χ
                (algebraMap R (R ⊗[K] R) r) = r
              rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
            _ = ψ (r ⊗ₜ[K] (1 : R)) := by
              rw [automorphismTensorSpecialization_tmul, map_one, mul_one]
        · have hl := torsorSpecialization_coe E b hgen hindep χ ⟨x, hxE⟩
          rw [hl]
          exact algebraMap_pointOfDifferenceAut E hcompat hconstC hEσ hnew φ hφσ ⟨x, hxE⟩
    | algebraMap c =>
        have hc : algebraMap C (R ⊗[K] R) c =
            (algebraMap C R c) ⊗ₜ[K] (1 : R) := by
          rw [IsScalarTower.algebraMap_apply C R (R ⊗[K] R)]
          rfl
        rw [hc]
        have hl : torsorSpecialization E b hgen hindep χ
            ((algebraMap C R c) ⊗ₜ[K] (1 : R)) = algebraMap C R c := by
          change torsorSpecialization E b hgen hindep χ
            (algebraMap R (R ⊗[K] R) (algebraMap C R c)) = algebraMap C R c
          rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
        rw [hl, automorphismTensorSpecialization_tmul, map_one, mul_one]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
  ext x
  change torsorSpecialization E b hgen hindep χ ((1 : R) ⊗ₜ[K] x) = φ x
  rw [heq, automorphismTensorSpecialization_tmul, one_mul]

omit [Differential K] [Differential R] [DifferentialAlgebra K R]
    [Differential C] [DifferentialAlgebra C R] in
theorem algEquiv_symm_commutes_sigma {σR : R ≃+* R} (φ : R ≃ₐ[K] R)
    (hφσ : ∀ x : R, φ (σR x) = σR (φ x)) (x : R) :
    φ.symm (σR x) = σR (φ.symm x) := by
  apply φ.injective
  rw [φ.apply_symm_apply, hφσ, φ.apply_symm_apply]

theorem algEquiv_symm_commutes_deriv (φ : R ≃ₐ[K] R)
    (hφδ : ∀ x : R, φ (Differential.deriv x) = Differential.deriv (φ x)) (x : R) :
    φ.symm (Differential.deriv x) = Differential.deriv (φ.symm x) := by
  apply φ.injective
  rw [φ.apply_symm_apply, hφδ, φ.apply_symm_apply]

/-- Every differential torsor point has an inverse differential point, with inverse Galois
matrix. -/
theorem exists_inverse_tensorDifferentialPoint
    (E : Subalgebra C (R ⊗[K] R)) {ι : Type*}
    (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hEσ : ∀ e ∈ E, differenceTensorEquiv σK σR hcompat e = e)
    (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E)
    (hsimple : IsSigmaSimple σR)
    (hnew : ∀ x : R, σR x = x → ∃ c : C, x = algebraMap C R c)
    (χ : E →ₐ[C] C)
    (hχ : χ ∈ tensorDifferentialPoints (K := K) (C := C) E hEδ)
    (Y : Matrix (Fin 2) (Fin 2) R)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hGdet : IsUnit (galoisMatrixAt E Z hZE χ).det)
    (u : R) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin 2 × Fin 2 => Y p.1 p.2) ∪ {u}) = ⊤) :
    ∃ χ' ∈ tensorDifferentialPoints (K := K) (C := C) E hEδ,
      galoisMatrixAt E Z hZE χ * galoisMatrixAt E Z hZE χ' = 1 := by
  classical
  let f := galoisAutAtK E b hgen hindep χ
  have hfinj : Function.Injective f :=
    galoisAutAtK_injective E b hgen hindep hcompat hconstC hEσ hsimple χ
  have hfsurj : Function.Surjective f :=
    galoisAutAtK_surjective_of_pvGeneration E b hgen hindep χ Y Z hZE hZ hGdet u hu htop
  let Φ : R ≃ₐ[K] R := AlgEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have hΦσ : ∀ x : R, Φ (σR x) = σR (Φ x) := by
    intro x
    exact galoisAutAtK_sigma E b hgen hindep hcompat hconstC hEσ χ x
  have hΦδ : ∀ x : R, Φ (Differential.deriv x) = Differential.deriv (Φ x) := by
    intro x
    exact galoisAutAt_deriv E b hgen hindep hEδ χ hχ x
  have hΦiσ : ∀ x : R, Φ.symm (σR x) = σR (Φ.symm x) :=
    algEquiv_symm_commutes_sigma Φ hΦσ
  have hΦiδ : ∀ x : R, Φ.symm (Differential.deriv x) = Differential.deriv (Φ.symm x) :=
    algEquiv_symm_commutes_deriv Φ hΦδ
  let χ' := pointOfDifferenceAut E hcompat hconstC hEσ hnew Φ.symm hΦiσ
  have hχ' : χ' ∈ tensorDifferentialPoints E hEδ := by
    intro e he
    exact pointOfDifferenceAut_deriv E hcompat hconstC hEσ hEδ hnew Φ.symm hΦiσ hΦiδ e he
  refine ⟨χ', hχ', ?_⟩
  let G := galoisMatrixAt E Z hZE χ
  let G' := galoisMatrixAt E Z hZE χ'
  let GR : Matrix (Fin 2) (Fin 2) R := G.map (algebraMap C R)
  let GR' : Matrix (Fin 2) (Fin 2) R := G'.map (algebraMap C R)
  have hΦY : Y.map (Φ : R → R) = Y * GR := by
    ext i j
    rw [Matrix.map_apply]
    change galoisAutAtK E b hgen hindep χ (Y i j) = _
    rw [galoisAutAtK_apply,
      galoisAutAt_fundamental E b hgen hindep χ Y Z hZE hZ, Matrix.mul_apply]
    rfl
  have hround : galoisAutAtK E b hgen hindep χ' = Φ.symm.toAlgHom := by
    exact galoisAutAtK_pointOfDifferenceAut E b hgen hindep hcompat hconstC hEσ hnew Φ.symm hΦiσ
  have hΦiY : Y.map (Φ.symm : R → R) = Y * GR' := by
    ext i j
    rw [Matrix.map_apply]
    change Φ.symm (Y i j) = _
    have heval : galoisAutAtK E b hgen hindep χ' (Y i j) = Φ.symm (Y i j) :=
      DFunLike.congr_fun hround (Y i j)
    rw [← heval]
    rw [galoisAutAtK_apply,
      galoisAutAt_fundamental E b hgen hindep χ' Y Z hZE hZ, Matrix.mul_apply]
    rfl
  have hleft : (Y.map (Φ.symm : R → R)).map (Φ : R → R) = Y := by
    ext i j
    simp
  have hfixGR' : GR'.map (Φ : R → R) = GR' := by
    ext i j
    change Φ (algebraMap C R (G' i j)) = algebraMap C R (G' i j)
    change f (algebraMap C R (G' i j)) = algebraMap C R (G' i j)
    rw [IsScalarTower.algebraMap_apply C K R, AlgHom.commutes]
  have happ := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M.map (Φ : R → R)) hΦiY
  rw [hleft, Matrix.map_mul, hΦY, hfixGR', mul_assoc] at happ
  have hYdet : IsUnit Y.det := by
    refine ⟨⟨Y.det, u, hu, mul_eq_one_comm.mp hu⟩, rfl⟩
  have hYunit : IsUnit Y := (Matrix.isUnit_iff_isUnit_det Y).mpr hYdet
  have hprodR : GR * GR' = 1 := by
    apply hYunit.mul_left_cancel
    calc
      Y * (GR * GR') = Y := happ.symm
      _ = Y * 1 := (Matrix.mul_one Y).symm
  apply Matrix.ext
  intro i j
  apply (algebraMap C R).injective
  have hp := congrFun (congrFun hprodR i) j
  change (GR * GR') i j = (1 : Matrix (Fin 2) (Fin 2) R) i j at hp
  change ((G * G').map (algebraMap C R)) i j =
    ((1 : Matrix (Fin 2) (Fin 2) C).map (algebraMap C R)) i j
  rw [Matrix.map_mul]
  rw [Matrix.map_one (algebraMap C R) (map_zero (algebraMap C R)) (map_one (algebraMap C R))]
  change (GR * GR') i j = (1 : Matrix (Fin 2) (Fin 2) R) i j
  exact hp

end

end GaloisForLFunctions.HTGeometry

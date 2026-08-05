import GaloisForLFunctions.HTGeometry.PolynomialHermitianSpectrumGenericity

/-!
# Simultaneous subsystem genericity atlas

A finite quantum network supplies not one Hamiltonian family but a whole
atlas of them: every vertex subset `S` retains its own onsite terms and its
own induced edge terms, and therefore reads a *subfamily* of the ambient
real coefficient vector.  The arbitrary-graph temporal-curvature law needs
all of these restricted families to be maximally projective *at the same
parameter point*, because the temporal curvature of a pair is computed from
three induced restrictions of one fixed Hamiltonian.

This file proves that capstone in exact generality.

* `coefficientRestrict` reads a supplied subfamily of ambient real
  coordinates; `coefficientExtend` is its zero extension.  The restriction
  map is continuous, and it is an open map as soon as the selector is
  injective.
* `preimage_mem_residual_of_isOpenMap` transports residuality backwards
  along any continuous open map.
* `restrictedPolynomialHermitianMaximalSet_dense_residual_fullMeasure`
  proves that one restricted subsystem family with one maximally projective
  witness already has dense, residual, full-measure maximal rank *in the
  ambient coefficient space*.  The proof renames the subsystem variables
  into the ambient variables, so no measure-theoretic pullback is required:
  the pulled-back set is literally the maximal set of a polynomial family in
  the ambient variables.
* `simultaneousRestrictedMaximalSet_dense_residual_fullMeasure` intersects a
  countable atlas of such subsystems.  Density is recovered from
  residuality by Baire, which is what makes a *simultaneous* statement
  possible: a finite intersection of dense sets is not dense, but a
  countable intersection of residual sets is residual and hence dense.
* `ambientRestrictedMaximalSet_residual` and
  `measure_compl_ambientRestrictedMaximalSet_eq_zero` give the
  infinite-network completion: a countable coefficient product carries the
  same residual conclusion, and every law whose finite-dimensional
  restriction marginals are absolutely continuous with respect to Lebesgue
  measure gives the same almost-sure conclusion.

Nothing here is conditional: each statement supplies its own witnesses.
-/

open Set Topology MeasureTheory Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Coefficient restriction and extension -/

/-- Read the supplied subfamily `e` of ambient real coordinates. -/
def coefficientRestrict {ι κ : Type*} (e : κ → ι) (p : ι → ℝ) : κ → ℝ :=
  fun i => p (e i)

@[simp] theorem coefficientRestrict_apply {ι κ : Type*} (e : κ → ι)
    (p : ι → ℝ) (i : κ) : coefficientRestrict e p i = p (e i) := rfl

theorem coefficientRestrict_add {ι κ : Type*} (e : κ → ι) (p q : ι → ℝ) :
    coefficientRestrict e (p + q) =
      coefficientRestrict e p + coefficientRestrict e q := rfl

theorem continuous_coefficientRestrict {ι κ : Type*} (e : κ → ι) :
    Continuous (coefficientRestrict (ι := ι) (κ := κ) e) :=
  continuous_pi fun i => continuous_apply (e i)

theorem measurable_coefficientRestrict {ι κ : Type*} (e : κ → ι) :
    Measurable (coefficientRestrict (ι := ι) (κ := κ) e) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (e i)

open Classical in
/-- Extend a subfamily of coordinates by zero on the unselected ambient
coordinates. -/
def coefficientExtend {ι κ : Type*} (e : κ → ι) (q : κ → ℝ) : ι → ℝ :=
  fun i => if h : ∃ j, e j = i then q h.choose else 0

theorem continuous_coefficientExtend {ι κ : Type*} (e : κ → ι) :
    Continuous (coefficientExtend (ι := ι) (κ := κ) e) := by
  classical
  refine continuous_pi fun i => ?_
  by_cases h : ∃ j, e j = i
  · have hfun :
        (fun q : κ → ℝ => coefficientExtend e q i) = fun q : κ → ℝ => q h.choose := by
      funext q
      simp only [coefficientExtend, dif_pos h]
    rw [hfun]
    exact continuous_apply _
  · have hfun :
        (fun q : κ → ℝ => coefficientExtend e q i) = fun _ : κ → ℝ => (0 : ℝ) := by
      funext q
      simp only [coefficientExtend, dif_neg h]
    rw [hfun]
    exact continuous_const

theorem coefficientExtend_zero {ι κ : Type*} (e : κ → ι) :
    coefficientExtend (ι := ι) (κ := κ) e 0 = 0 := by
  classical
  funext i
  by_cases h : ∃ j, e j = i
  · simp only [coefficientExtend, dif_pos h]
    rfl
  · simp only [coefficientExtend, dif_neg h]
    rfl

theorem coefficientRestrict_coefficientExtend {ι κ : Type*} {e : κ → ι}
    (he : Function.Injective e) (q : κ → ℝ) :
    coefficientRestrict e (coefficientExtend e q) = q := by
  classical
  funext j
  have h : ∃ j', e j' = e j := ⟨j, rfl⟩
  show coefficientExtend e q (e j) = q j
  simp only [coefficientExtend, dif_pos h]
  exact congrArg q (he h.choose_spec)

/-- **Coefficient restriction is an open map.**  Selecting an injective
subfamily of coordinates admits a continuous linear zero-extension section,
and a continuous additive map with a continuous section is open. -/
theorem isOpenMap_coefficientRestrict {ι κ : Type*} {e : κ → ι}
    (he : Function.Injective e) :
    IsOpenMap (coefficientRestrict (ι := ι) (κ := κ) e) := by
  classical
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨u, huU, rfl⟩
  have hφc : Continuous (fun q' : κ → ℝ =>
      u + coefficientExtend e (q' - coefficientRestrict e u)) :=
    continuous_const.add
      ((continuous_coefficientExtend e).comp
        (continuous_id.sub continuous_const))
  have hsection : ∀ q' : κ → ℝ,
      coefficientRestrict e
          (u + coefficientExtend e (q' - coefficientRestrict e u)) = q' := by
    intro q'
    rw [coefficientRestrict_add, coefficientRestrict_coefficientExtend he]
    abel
  refine Filter.mem_of_superset ((hU.preimage hφc).mem_nhds ?_) ?_
  · show u + coefficientExtend e
      (coefficientRestrict e u - coefficientRestrict e u) ∈ U
    rw [sub_self, coefficientExtend_zero, add_zero]
    exact huU
  · intro q' hq'
    exact ⟨_, hq', hsection q'⟩

/-! ### Residuality transports backwards along continuous open maps -/

/-- **Residual pullback.**  A continuous open map pulls residual sets back
to residual sets.  Preimages of dense open sets are dense and open, and the
residual filter is generated by countable intersections of those. -/
theorem preimage_mem_residual_of_isOpenMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hcont : Continuous f) (hopen : IsOpenMap f) {s : Set Y}
    (hs : s ∈ residual Y) : f ⁻¹' s ∈ residual X := by
  rw [mem_residual_iff] at hs ⊢
  obtain ⟨S, hSopen, hSdense, hScount, hSsub⟩ := hs
  refine ⟨(fun t => f ⁻¹' t) '' S, ?_, ?_, hScount.image _, ?_⟩
  · rintro t ⟨t', ht', rfl⟩
    exact (hSopen t' ht').preimage hcont
  · rintro t ⟨t', ht', rfl⟩
    exact (hSdense t' ht').preimage hopen
  · intro x hx
    refine hSsub ?_
    rw [Set.mem_sInter]
    intro t ht
    exact hx (f ⁻¹' t) ⟨t, ht, rfl⟩

/-! ### One restricted subsystem family -/

/-- A subsystem polynomial matrix family read through a supplied selector of
the ambient coefficient coordinates. -/
def renamedPolynomialMatrix {m n : ℕ} {I : Type*}
    (M : Matrix I I (MvPolynomial (Fin n) ℂ)) (e : Fin n → Fin m) :
    Matrix I I (MvPolynomial (Fin m) ℂ) :=
  M.map (MvPolynomial.rename e)

/-- Evaluating the renamed family at an ambient parameter is exactly
evaluating the original family at the restricted parameter. -/
theorem renamedPolynomialMatrix_eval {m n : ℕ} {I : Type*}
    (M : Matrix I I (MvPolynomial (Fin n) ℂ)) (e : Fin n → Fin m)
    (p : Fin m → ℝ) :
    (renamedPolynomialMatrix M e).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p t : ℂ))) =
      M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => ((coefficientRestrict e p) t : ℂ))) := by
  ext a b
  simp only [renamedPolynomialMatrix, Matrix.map_apply,
    MvPolynomial.coe_eval₂Hom]
  rw [MvPolynomial.eval₂_rename]
  rfl

/-- Ambient parameters whose supplied subsystem restriction has maximal
projective rational spectral rank. -/
def restrictedPolynomialHermitianMaximalSet {m n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin n) ℂ))
    (hherm : ∀ q : Fin n → ℝ,
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (q t : ℂ)))).IsHermitian)
    (e : Fin n → Fin m) : Set (Fin m → ℝ) :=
  coefficientRestrict e ⁻¹' polynomialHermitianMatrixMaximalSet M hherm

/-- Hermiticity is inherited by the renamed subsystem family. -/
theorem renamedPolynomialMatrix_isHermitian {m n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin n) ℂ))
    (hherm : ∀ q : Fin n → ℝ,
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (q t : ℂ)))).IsHermitian)
    (e : Fin n → Fin m) (p : Fin m → ℝ) :
    ((renamedPolynomialMatrix M e).map
      (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (p t : ℂ)))).IsHermitian := by
  rw [renamedPolynomialMatrix_eval]
  exact hherm (coefficientRestrict e p)

/-- The renamed maximal set is literally the restricted maximal set. -/
theorem polynomialHermitianMatrixMaximalSet_renamed_eq {m n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin n) ℂ))
    (hherm : ∀ q : Fin n → ℝ,
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (q t : ℂ)))).IsHermitian)
    (e : Fin n → Fin m) :
    polynomialHermitianMatrixMaximalSet (renamedPolynomialMatrix M e)
        (renamedPolynomialMatrix_isHermitian M hherm e) =
      restrictedPolynomialHermitianMaximalSet M hherm e := by
  ext p
  have heig :
      (renamedPolynomialMatrix_isHermitian M hherm e p).eigenvalues =
        (hherm (coefficientRestrict e p)).eigenvalues := by
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
      (renamedPolynomialMatrix_isHermitian M hherm e p)
      (hherm (coefficientRestrict e p))).2
    rw [renamedPolynomialMatrix_eval]
  simp only [polynomialHermitianMatrixMaximalSet,
    restrictedPolynomialHermitianMaximalSet, Set.mem_setOf_eq,
    Set.mem_preimage, heig]

/-- **Restricted subsystem genericity.**  If one ambient parameter makes a
supplied subsystem family maximally projective, then the ambient parameters
with that property are dense, residual and of full Lebesgue measure in the
whole ambient coefficient space.  The unselected coordinates are entirely
free. -/
theorem restrictedPolynomialHermitianMaximalSet_dense_residual_fullMeasure
    {m n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin n) ℂ))
    (hherm : ∀ q : Fin n → ℝ,
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (q t : ℂ)))).IsHermitian)
    (e : Fin n → Fin m) (p₀ : Fin m → ℝ)
    (hmax : MaximallyProjectiveEnergy
      (hherm (coefficientRestrict e p₀)).eigenvalues) :
    Dense (restrictedPolynomialHermitianMaximalSet M hherm e) ∧
      restrictedPolynomialHermitianMaximalSet M hherm e ∈
        residual (Fin m → ℝ) ∧
      volume (restrictedPolynomialHermitianMaximalSet M hherm e)ᶜ = 0 := by
  have heig :
      (renamedPolynomialMatrix_isHermitian M hherm e p₀).eigenvalues =
        (hherm (coefficientRestrict e p₀)).eigenvalues := by
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
      (renamedPolynomialMatrix_isHermitian M hherm e p₀)
      (hherm (coefficientRestrict e p₀))).2
    rw [renamedPolynomialMatrix_eval]
  have hmax₀ :
      MaximallyProjectiveEnergy
        (renamedPolynomialMatrix_isHermitian M hherm e p₀).eigenvalues := by
    rw [heig]; exact hmax
  have hbase :=
    polynomialHermitianMatrixMaximalSet_dense_residual_fullMeasure
      (renamedPolynomialMatrix M e)
      (renamedPolynomialMatrix_isHermitian M hherm e) p₀ hmax₀
  rwa [polynomialHermitianMatrixMaximalSet_renamed_eq M hherm e] at hbase

/-! ### The simultaneous atlas -/

/-- Ambient parameters at which *every* subsystem of a supplied atlas is
maximally projective. -/
def simultaneousRestrictedMaximalSet {m : ℕ} {A : Type*}
    {n : A → ℕ} {I : A → Type*} [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)]
    (M : ∀ a, Matrix (I a) (I a) (MvPolynomial (Fin (n a)) ℂ))
    (hherm : ∀ a, ∀ q : Fin (n a) → ℝ,
      ((M a).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (q t : ℂ)))).IsHermitian)
    (e : ∀ a, Fin (n a) → Fin m) : Set (Fin m → ℝ) :=
  {p | ∀ a, p ∈ restrictedPolynomialHermitianMaximalSet (M a) (hherm a) (e a)}

theorem simultaneousRestrictedMaximalSet_eq_iInter {m : ℕ} {A : Type*}
    {n : A → ℕ} {I : A → Type*} [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)]
    (M : ∀ a, Matrix (I a) (I a) (MvPolynomial (Fin (n a)) ℂ))
    (hherm : ∀ a, ∀ q : Fin (n a) → ℝ,
      ((M a).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (q t : ℂ)))).IsHermitian)
    (e : ∀ a, Fin (n a) → Fin m) :
    simultaneousRestrictedMaximalSet M hherm e =
      ⋂ a, restrictedPolynomialHermitianMaximalSet (M a) (hherm a) (e a) := by
  ext p
  simp [simultaneousRestrictedMaximalSet]

/-- **Simultaneous subsystem atlas.**  Given a countable family of
subsystems, each reading its own subfamily of one ambient real coefficient
vector and each admitting *its own* maximally projective witness, the set of
ambient parameters at which all of them are simultaneously maximally
projective is dense, residual and of full Lebesgue measure.

Density here is a genuine consequence of Baire's theorem: dense sets are not
closed under finite intersection, but residual sets are closed under
countable intersection, and residual sets in a Baire space are dense. -/
theorem simultaneousRestrictedMaximalSet_dense_residual_fullMeasure
    {m : ℕ} {A : Type*} [Countable A]
    {n : A → ℕ} {I : A → Type*} [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)]
    (M : ∀ a, Matrix (I a) (I a) (MvPolynomial (Fin (n a)) ℂ))
    (hherm : ∀ a, ∀ q : Fin (n a) → ℝ,
      ((M a).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (q t : ℂ)))).IsHermitian)
    (e : ∀ a, Fin (n a) → Fin m)
    (p₀ : A → (Fin m → ℝ))
    (hmax : ∀ a, MaximallyProjectiveEnergy
      (hherm a (coefficientRestrict (e a) (p₀ a))).eigenvalues) :
    Dense (simultaneousRestrictedMaximalSet M hherm e) ∧
      simultaneousRestrictedMaximalSet M hherm e ∈ residual (Fin m → ℝ) ∧
      volume (simultaneousRestrictedMaximalSet M hherm e)ᶜ = 0 := by
  have hpiece : ∀ a,
      restrictedPolynomialHermitianMaximalSet (M a) (hherm a) (e a) ∈
          residual (Fin m → ℝ) ∧
        volume
            (restrictedPolynomialHermitianMaximalSet (M a) (hherm a) (e a))ᶜ
          = 0 := by
    intro a
    obtain ⟨_, hres, hnull⟩ :=
      restrictedPolynomialHermitianMaximalSet_dense_residual_fullMeasure
        (M a) (hherm a) (e a) (p₀ a) (hmax a)
    exact ⟨hres, hnull⟩
  have hres : simultaneousRestrictedMaximalSet M hherm e ∈
      residual (Fin m → ℝ) := by
    rw [simultaneousRestrictedMaximalSet_eq_iInter]
    exact countable_iInter_mem.2 fun a => (hpiece a).1
  refine ⟨dense_of_mem_residual hres, hres, ?_⟩
  have hcompl :
      (simultaneousRestrictedMaximalSet M hherm e)ᶜ =
        ⋃ a, (restrictedPolynomialHermitianMaximalSet
          (M a) (hherm a) (e a))ᶜ := by
    rw [simultaneousRestrictedMaximalSet_eq_iInter, Set.compl_iInter]
  rw [hcompl]
  exact measure_iUnion_null fun a => (hpiece a).2

/-! ### Infinite-network completion -/

/-- Ambient parameters, in a possibly infinite coefficient product, at which
every subsystem of a supplied atlas is maximally projective. -/
def ambientRestrictedMaximalSet {ι : Type*} {A : Type*}
    {n : A → ℕ} {I : A → Type*} [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)]
    (M : ∀ a, Matrix (I a) (I a) (MvPolynomial (Fin (n a)) ℂ))
    (hherm : ∀ a, ∀ q : Fin (n a) → ℝ,
      ((M a).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (q t : ℂ)))).IsHermitian)
    (e : ∀ a, Fin (n a) → ι) : Set (ι → ℝ) :=
  {p | ∀ a, coefficientRestrict (e a) p ∈
    polynomialHermitianMatrixMaximalSet (M a) (hherm a)}

theorem ambientRestrictedMaximalSet_eq_iInter {ι : Type*} {A : Type*}
    {n : A → ℕ} {I : A → Type*} [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)]
    (M : ∀ a, Matrix (I a) (I a) (MvPolynomial (Fin (n a)) ℂ))
    (hherm : ∀ a, ∀ q : Fin (n a) → ℝ,
      ((M a).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (q t : ℂ)))).IsHermitian)
    (e : ∀ a, Fin (n a) → ι) :
    ambientRestrictedMaximalSet M hherm e =
      ⋂ a, coefficientRestrict (e a) ⁻¹'
        polynomialHermitianMatrixMaximalSet (M a) (hherm a) := by
  ext p
  simp [ambientRestrictedMaximalSet]

/-- **Infinite-network residual completion.**  A countable atlas of finite
subsystems inside one countable coefficient product has residual — hence
dense — simultaneous maximal projective rank, provided each subsystem has
its own witness.  No finite-dimensionality of the ambient parameter space is
used. -/
theorem ambientRestrictedMaximalSet_residual {ι : Type*} [Countable ι]
    {A : Type*} [Countable A]
    {n : A → ℕ} {I : A → Type*} [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)]
    (M : ∀ a, Matrix (I a) (I a) (MvPolynomial (Fin (n a)) ℂ))
    (hherm : ∀ a, ∀ q : Fin (n a) → ℝ,
      ((M a).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (q t : ℂ)))).IsHermitian)
    (e : ∀ a, Fin (n a) → ι) (he : ∀ a, Function.Injective (e a))
    (q₀ : ∀ a, Fin (n a) → ℝ)
    (hmax : ∀ a, MaximallyProjectiveEnergy (hherm a (q₀ a)).eigenvalues) :
    ambientRestrictedMaximalSet M hherm e ∈ residual (ι → ℝ) ∧
      Dense (ambientRestrictedMaximalSet M hherm e) := by
  have hpiece : ∀ a,
      coefficientRestrict (e a) ⁻¹'
          polynomialHermitianMatrixMaximalSet (M a) (hherm a) ∈
        residual (ι → ℝ) := by
    intro a
    have hbase :=
      polynomialHermitianMatrixMaximalSet_dense_residual_fullMeasure
        (M a) (hherm a) (q₀ a) (hmax a)
    exact preimage_mem_residual_of_isOpenMap
      (continuous_coefficientRestrict (e a))
      (isOpenMap_coefficientRestrict (he a)) hbase.2.1
  have hres : ambientRestrictedMaximalSet M hherm e ∈ residual (ι → ℝ) := by
    rw [ambientRestrictedMaximalSet_eq_iInter]
    exact countable_iInter_mem.2 hpiece
  exact ⟨hres, dense_of_mem_residual hres⟩

/-- **Absolutely continuous marginals kill every bad cylinder.**  If each
finite-dimensional restriction marginal of a law on the ambient coefficient
space is absolutely continuous with respect to Lebesgue measure, then the
simultaneous maximal-rank event has full probability. -/
theorem measure_compl_ambientRestrictedMaximalSet_eq_zero
    {ι : Type*} {A : Type*} [Countable A]
    {n : A → ℕ} {I : A → Type*} [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)]
    (M : ∀ a, Matrix (I a) (I a) (MvPolynomial (Fin (n a)) ℂ))
    (hherm : ∀ a, ∀ q : Fin (n a) → ℝ,
      ((M a).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (q t : ℂ)))).IsHermitian)
    (e : ∀ a, Fin (n a) → ι)
    (μ : Measure (ι → ℝ))
    (hac : ∀ a, (Measure.map (coefficientRestrict (e a)) μ).AbsolutelyContinuous
      (volume : Measure (Fin (n a) → ℝ)))
    (q₀ : ∀ a, Fin (n a) → ℝ)
    (hmax : ∀ a, MaximallyProjectiveEnergy (hherm a (q₀ a)).eigenvalues) :
    μ (ambientRestrictedMaximalSet M hherm e)ᶜ = 0 := by
  have hcompl :
      (ambientRestrictedMaximalSet M hherm e)ᶜ =
        ⋃ a, coefficientRestrict (e a) ⁻¹'
          (polynomialHermitianMatrixMaximalSet (M a) (hherm a))ᶜ := by
    rw [ambientRestrictedMaximalSet_eq_iInter, Set.compl_iInter]
    simp [Set.preimage_compl]
  rw [hcompl]
  refine measure_iUnion_null fun a => ?_
  have hnull :
      (Measure.map (coefficientRestrict (e a)) μ)
        (polynomialHermitianMatrixMaximalSet (M a) (hherm a))ᶜ = 0 := by
    refine hac a ?_
    exact
      (polynomialHermitianMatrixMaximalSet_dense_residual_fullMeasure
        (M a) (hherm a) (q₀ a) (hmax a)).2.2
  obtain ⟨T, hsub, hmeas, hTnull⟩ := exists_measurable_superset_of_null hnull
  have hT : μ (coefficientRestrict (e a) ⁻¹' T) = 0 := by
    rw [← Measure.map_apply (measurable_coefficientRestrict (e a)) hmeas]
    exact hTnull
  exact measure_mono_null (Set.preimage_mono hsub) hT

end

end GaloisForLFunctions.HTGeometry

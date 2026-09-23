import GaloisForLFunctions.HTGeometry.AbelianZetaGas.GasStar

/-!
# The pre-GNS space of the gas

The Gibbs functional is hermitian, positive and linear, so `⟪a, b⟫ = φ(a^* b)` is a semi-inner
product on the monomial algebra.  Completing that seminormed space is the GNS Hilbert space of the
gas; every monomial acts on it as a contraction.
-/

namespace GaloisForLFunctions.HTGeometry

open GasWord Complex

open scoped ComplexOrder InnerProductSpace

theorem gasNome_conj (θ : AbelianZetaParameters) (i : AbelianZetaMode) :
    (starRingEnd ℂ) (gasNome θ i) = gasNome θ i := by
  rw [gasNome, Complex.conj_ofReal]

theorem gasAdjoint_smul {M : Type*} (r : ℂ) (a : GasAlgebra M) :
    gasAdjoint (r • a) = (starRingEnd ℂ) r • gasAdjoint a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [smul_add, gasAdjoint_add, hf, hg, gasAdjoint_add, smul_add]
  | single x c =>
    rw [MonoidAlgebra.smul_single', gasAdjoint_single, gasAdjoint_single,
      MonoidAlgebra.smul_single', map_mul]

/-- The pre-GNS space of the gas at parameters `θ`. -/
def GasPreGNS (_θ : AbelianZetaParameters) : Type := GasAlgebra AbelianZetaMode

namespace GasPreGNS

variable (θ : AbelianZetaParameters)

noncomputable instance : AddCommGroup (GasPreGNS θ) :=
  inferInstanceAs (AddCommGroup (GasAlgebra AbelianZetaMode))

noncomputable instance : Module ℂ (GasPreGNS θ) :=
  inferInstanceAs (Module ℂ (GasAlgebra AbelianZetaMode))

/-- The identification of the pre-GNS space with the algebra. -/
noncomputable def toGas : GasPreGNS θ ≃ₗ[ℂ] GasAlgebra AbelianZetaMode := LinearEquiv.refl ℂ _

/-- The identification of the algebra with the pre-GNS space. -/
noncomputable def ofGas : GasAlgebra AbelianZetaMode ≃ₗ[ℂ] GasPreGNS θ := (toGas θ).symm

@[simp] theorem toGas_ofGas (a : GasAlgebra AbelianZetaMode) : toGas θ (ofGas θ a) = a := rfl

@[simp] theorem ofGas_toGas (a : GasPreGNS θ) : ofGas θ (toGas θ a) = a := rfl

/-- **The semi-inner product of the gas.**  Hermitian by `gibbs_gasAdjoint`, positive by
`gasGibbs_adjoint_mul_self_nonneg`, sesquilinear by linearity of the Gibbs functional. -/
noncomputable abbrev core : PreInnerProductSpace.Core ℂ (GasPreGNS θ) where
  inner a b := gasGibbs θ (gasAdjoint (toGas θ a) * toGas θ b)
  conj_inner_symm a b := by
    show (starRingEnd ℂ) (gasGibbs θ (gasAdjoint (toGas θ b) * toGas θ a))
      = gasGibbs θ (gasAdjoint (toGas θ a) * toGas θ b)
    rw [gasGibbs, ← gibbs_gasAdjoint (gasNome θ) (gasNome_conj θ), gasAdjoint_mul,
      gasAdjoint_gasAdjoint]
  re_inner_nonneg a :=
    (RCLike.nonneg_iff.mp (gasGibbs_adjoint_mul_self_nonneg θ (toGas θ a))).1
  add_left a b c := by
    show gasGibbs θ (gasAdjoint (toGas θ a + toGas θ b) * toGas θ c)
      = gasGibbs θ (gasAdjoint (toGas θ a) * toGas θ c)
        + gasGibbs θ (gasAdjoint (toGas θ b) * toGas θ c)
    rw [gasAdjoint_add, add_mul, map_add]
  smul_left a b r := by
    show gasGibbs θ (gasAdjoint (r • toGas θ a) * toGas θ b)
      = (starRingEnd ℂ) r * gasGibbs θ (gasAdjoint (toGas θ a) * toGas θ b)
    rw [gasAdjoint_smul, smul_mul_assoc, map_smul, smul_eq_mul]

noncomputable instance : SeminormedAddCommGroup (GasPreGNS θ) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := core θ)

noncomputable instance : InnerProductSpace ℂ (GasPreGNS θ) :=
  InnerProductSpace.ofCore (core θ)

theorem inner_def (a b : GasPreGNS θ) :
    ⟪a, b⟫_ℂ = gasGibbs θ (gasAdjoint (toGas θ a) * toGas θ b) := rfl

theorem norm_sq (a : GasPreGNS θ) :
    (‖a‖ : ℂ) ^ (2 : ℕ) = gasGibbs θ (gasAdjoint (toGas θ a) * toGas θ a) := by
  have hnn : 0 ≤ gasGibbs θ (gasAdjoint (toGas θ a) * toGas θ a) :=
    gasGibbs_adjoint_mul_self_nonneg θ (toGas θ a)
  have hre : ‖a‖ = Real.sqrt (gasGibbs θ (gasAdjoint (toGas θ a) * toGas θ a)).re := rfl
  have hre0 : 0 ≤ (gasGibbs θ (gasAdjoint (toGas θ a) * toGas θ a)).re :=
    (RCLike.nonneg_iff.mp hnn).1
  have him : (gasGibbs θ (gasAdjoint (toGas θ a) * toGas θ a)).im = 0 :=
    (RCLike.nonneg_iff.mp hnn).2
  rw [hre, ← Complex.ofReal_pow, Real.sq_sqrt hre0]
  refine Complex.ext ?_ ?_
  · simp
  · simp [him]

theorem norm_eq_sqrt (a : GasPreGNS θ) :
    ‖a‖ = Real.sqrt (gasGibbs θ (gasAdjoint (toGas θ a) * toGas θ a)).re := rfl

/-- **A monomial acts as a contraction of the pre-GNS space.** -/
theorem norm_mulLeft_le (z : GasWord AbelianZetaMode) (x : GasPreGNS θ) :
    ‖ofGas θ (MonoidAlgebra.single z (1 : ℂ) * toGas θ x)‖ ≤ ‖x‖ := by
  rw [norm_eq_sqrt, norm_eq_sqrt]
  refine Real.sqrt_le_sqrt ?_
  have h := gibbs_contraction θ z (toGas θ x)
  exact (Complex.le_def.mp h).1

/-- Left multiplication by a monomial, as a contraction of the pre-GNS space. -/
noncomputable def leftMulPre (z : GasWord AbelianZetaMode) : GasPreGNS θ →L[ℂ] GasPreGNS θ :=
  LinearMap.mkContinuous
    ((ofGas θ).toLinearMap ∘ₗ LinearMap.mulLeft ℂ (MonoidAlgebra.single z (1 : ℂ))
      ∘ₗ (toGas θ).toLinearMap) 1 (fun x => by
        rw [one_mul]
        exact norm_mulLeft_le θ z x)

@[simp] theorem leftMulPre_apply (z : GasWord AbelianZetaMode) (x : GasPreGNS θ) :
    leftMulPre θ z x = ofGas θ (MonoidAlgebra.single z (1 : ℂ) * toGas θ x) := rfl

theorem leftMulPre_one : leftMulPre θ (1 : GasWord AbelianZetaMode) = ContinuousLinearMap.id ℂ _ := by
  ext x
  show ofGas θ (MonoidAlgebra.single (1 : GasWord AbelianZetaMode) (1 : ℂ) * toGas θ x) = x
  rw [← MonoidAlgebra.one_def, one_mul]
  rfl

/-- **The monomial action is multiplicative.** -/
theorem leftMulPre_mul (z w : GasWord AbelianZetaMode) :
    leftMulPre θ (z * w) = (leftMulPre θ z).comp (leftMulPre θ w) := by
  ext x
  show ofGas θ (MonoidAlgebra.single (z * w) (1 : ℂ) * toGas θ x)
    = ofGas θ (MonoidAlgebra.single z (1 : ℂ)
        * toGas θ (ofGas θ (MonoidAlgebra.single w (1 : ℂ) * toGas θ x)))
  rw [toGas_ofGas, ← mul_assoc, MonoidAlgebra.single_mul_single, mul_one]

/-- **The GNS Hilbert space of the gas.** -/
abbrev GasGNS : Type := UniformSpace.Completion (GasPreGNS θ)

/-- The monomial action on the GNS Hilbert space. -/
noncomputable def leftMul (z : GasWord AbelianZetaMode) : GasGNS θ →L[ℂ] GasGNS θ :=
  (leftMulPre θ z).completion

theorem norm_leftMul_le (z : GasWord AbelianZetaMode) : ‖leftMul θ z‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le ((leftMul θ z).continuous.norm) continuous_norm
  | ih a =>
    rw [leftMul, ContinuousLinearMap.completion_apply_coe,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe, leftMulPre_apply]
    exact norm_mulLeft_le θ z a

/-- **The monomial action on the GNS space is multiplicative.** -/
theorem leftMul_mul (z w : GasWord AbelianZetaMode) :
    leftMul θ (z * w) = (leftMul θ z).comp (leftMul θ w) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (leftMul θ (z * w)).continuous
      ((leftMul θ z).comp (leftMul θ w)).continuous
  | ih a =>
    show (leftMulPre θ (z * w)).completion (a : GasGNS θ)
      = (leftMulPre θ z).completion ((leftMulPre θ w).completion (a : GasGNS θ))
    rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe,
      ContinuousLinearMap.completion_apply_coe, leftMulPre_mul]
    rfl

@[simp] theorem leftMul_one :
    leftMul θ (1 : GasWord AbelianZetaMode) = ContinuousLinearMap.id ℂ (GasGNS θ) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (leftMul θ (1 : GasWord AbelianZetaMode)).continuous
      (ContinuousLinearMap.id ℂ (GasGNS θ)).continuous
  | ih a =>
    show (leftMulPre θ (1 : GasWord AbelianZetaMode)).completion (a : GasGNS θ) = (a : GasGNS θ)
    rw [ContinuousLinearMap.completion_apply_coe, leftMulPre_one]
    rfl

/-! ## The representation of the whole algebra -/

/-- **The GNS representation.**  Extend the monomial action linearly over the algebra. -/
noncomputable def rep (a : GasAlgebra AbelianZetaMode) : GasGNS θ →L[ℂ] GasGNS θ :=
  a.coeff.sum fun x c => c • leftMul θ x

theorem rep_single (x : GasWord AbelianZetaMode) (c : ℂ) :
    rep θ (MonoidAlgebra.single x c) = c • leftMul θ x := by
  classical
  rw [rep]
  show (MonoidAlgebra.single x c).coeff.sum (fun x c => c • leftMul θ x) = _
  show (Finsupp.single x c).sum (fun x c => c • leftMul θ x) = _
  rw [Finsupp.sum_single_index (by simp)]

theorem rep_add (a b : GasAlgebra AbelianZetaMode) :
    rep θ (a + b) = rep θ a + rep θ b := by
  classical
  show ((a + b).coeff).sum (fun x c => c • leftMul θ x) = _
  show (a.coeff + b.coeff).sum (fun x c => c • leftMul θ x) = _
  rw [Finsupp.sum_add_index (by intro i _; simp) (by intro i _ c d; rw [add_smul])]
  rfl

@[simp] theorem rep_zero : rep θ (0 : GasAlgebra AbelianZetaMode) = 0 := by
  show ((0 : GasAlgebra AbelianZetaMode).coeff).sum (fun x c => c • leftMul θ x) = 0
  show (0 : GasWord AbelianZetaMode →₀ ℂ).sum (fun x c => c • leftMul θ x) = 0
  rw [Finsupp.sum_zero_index]

@[simp] theorem rep_one : rep θ (1 : GasAlgebra AbelianZetaMode) = ContinuousLinearMap.id ℂ _ := by
  rw [MonoidAlgebra.one_def, rep_single, leftMul_one, one_smul]

/-- **The representation is multiplicative.** -/
theorem rep_mul (a b : GasAlgebra AbelianZetaMode) :
    rep θ (a * b) = (rep θ a).comp (rep θ b) := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [add_mul, rep_add, hf, hg, rep_add, ContinuousLinearMap.add_comp]
  | single x c =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg =>
      rw [mul_add, rep_add, hf, hg, rep_add, ContinuousLinearMap.comp_add]
    | single y d =>
      rw [MonoidAlgebra.single_mul_single, rep_single, rep_single, rep_single, leftMul_mul,
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]

/-! ## The cyclic vector -/

/-- The cyclic vector of the GNS representation. -/
noncomputable def cyclic : GasGNS θ := ((ofGas θ 1 : GasPreGNS θ) : GasGNS θ)

theorem rep_cyclic_single (x : GasWord AbelianZetaMode) (c : ℂ) :
    rep θ (MonoidAlgebra.single x c) (cyclic θ)
      = c • ((ofGas θ (MonoidAlgebra.single x (1 : ℂ)) : GasPreGNS θ) : GasGNS θ) := by
  rw [rep_single, smul_apply, cyclic, leftMul,
    ContinuousLinearMap.completion_apply_coe, leftMulPre_apply]
  show c • ((ofGas θ (MonoidAlgebra.single x (1 : ℂ) * toGas θ (ofGas θ 1)) : GasPreGNS θ)
    : GasGNS θ) = _
  rw [toGas_ofGas, mul_one]

/-- **The Gibbs functional is the vector state at the cyclic vector.** -/
theorem inner_cyclic_rep_cyclic (a : GasAlgebra AbelianZetaMode) :
    ⟪cyclic θ, rep θ a (cyclic θ)⟫_ℂ = gasGibbs θ a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [rep_add, add_apply, inner_add_right, hf, hg, map_add]
  | single x c =>
    rw [rep_cyclic_single, inner_smul_right, gasGibbs, gibbs_single]
    congr 1
    show ⟪((ofGas θ 1 : GasPreGNS θ) : GasGNS θ),
      ((ofGas θ (MonoidAlgebra.single x (1 : ℂ)) : GasPreGNS θ) : GasGNS θ)⟫_ℂ = _
    rw [UniformSpace.Completion.inner_coe, inner_def]
    show gasGibbs θ (gasAdjoint (1 : GasAlgebra AbelianZetaMode)
      * MonoidAlgebra.single x (1 : ℂ)) = _
    rw [gasAdjoint_one, one_mul, gasGibbs, gibbs_single, one_mul]

/-! ## The adjoint property -/

theorem rep_coe (b : GasAlgebra AbelianZetaMode) (p : GasPreGNS θ) :
    rep θ b (p : GasGNS θ) = ((ofGas θ (b * toGas θ p) : GasPreGNS θ) : GasGNS θ) := by
  classical
  induction b using MonoidAlgebra.induction_linear with
  | zero =>
    simp only [rep_zero, zero_apply, zero_mul, map_zero]
    exact (UniformSpace.Completion.coe_zero).symm
  | add f g hf hg =>
    rw [rep_add, add_apply, hf, hg, add_mul]
    show _ = ((ofGas θ (f * toGas θ p) + ofGas θ (g * toGas θ p) : GasPreGNS θ) : GasGNS θ)
    rw [UniformSpace.Completion.coe_add]
  | single x c =>
    rw [rep_single, smul_apply, leftMul, ContinuousLinearMap.completion_apply_coe,
      leftMulPre_apply, ← UniformSpace.Completion.coe_smul]
    congr 1
    show c • ofGas θ (MonoidAlgebra.single x (1 : ℂ) * toGas θ p)
      = ofGas θ (MonoidAlgebra.single x c * toGas θ p)
    have hs : MonoidAlgebra.single x c = c • MonoidAlgebra.single x (1 : ℂ) := by
      rw [MonoidAlgebra.smul_single', mul_one]
    rw [hs, smul_mul_assoc]
    rfl

theorem inner_coe_coe (p q : GasPreGNS θ) :
    ⟪(p : GasGNS θ), (q : GasGNS θ)⟫_ℂ = gasGibbs θ (gasAdjoint (toGas θ p) * toGas θ q) := by
  rw [UniformSpace.Completion.inner_coe, inner_def]

/-- **The representation intertwines the algebra adjoint with the operator adjoint.** -/
theorem inner_rep_gasAdjoint (a : GasAlgebra AbelianZetaMode) (u v : GasGNS θ) :
    ⟪rep θ (gasAdjoint a) u, v⟫_ℂ = ⟪u, rep θ a v⟫_ℂ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp =>
    refine isClosed_eq ?_ ?_
    · exact UniformSpace.Completion.Continuous.inner
        (rep θ (gasAdjoint a)).continuous continuous_const
    · exact UniformSpace.Completion.Continuous.inner continuous_id continuous_const
  | ih p =>
    induction v using UniformSpace.Completion.induction_on with
    | hp =>
      refine isClosed_eq ?_ ?_
      · exact UniformSpace.Completion.Continuous.inner continuous_const continuous_id
      · exact UniformSpace.Completion.Continuous.inner continuous_const (rep θ a).continuous
    | ih q =>
      rw [rep_coe, rep_coe, inner_coe_coe, inner_coe_coe]
      show gasGibbs θ (gasAdjoint (gasAdjoint a * toGas θ p) * toGas θ q)
        = gasGibbs θ (gasAdjoint (toGas θ p) * (a * toGas θ q))
      rw [gasAdjoint_mul, gasAdjoint_gasAdjoint, mul_assoc]

theorem rep_smul (c : ℂ) (a : GasAlgebra AbelianZetaMode) :
    rep θ (c • a) = c • rep θ a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [smul_add, rep_add, hf, hg, rep_add, smul_add]
  | single x c' =>
    rw [MonoidAlgebra.smul_single', rep_single, rep_single, smul_smul]

/-- **The representation intertwines the two adjoints.** -/
theorem adjoint_rep (a : GasAlgebra AbelianZetaMode) :
    rep θ (gasAdjoint a) = ContinuousLinearMap.adjoint (rep θ a) :=
  (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (inner_rep_gasAdjoint θ a)

/-! ## The C⋆-algebra of the gas -/

/-- **The C⋆-algebra of the gas**: the closed `*`-subalgebra of the bounded operators on the GNS
space generated by the image of the monomial algebra. -/
noncomputable def gasCStar : StarSubalgebra ℂ (GasGNS θ →L[ℂ] GasGNS θ) :=
  (StarAlgebra.adjoin ℂ (Set.range (rep θ))).topologicalClosure

theorem rep_mem_gasCStar (a : GasAlgebra AbelianZetaMode) : rep θ a ∈ gasCStar θ := by
  refine StarSubalgebra.le_topologicalClosure _ ?_
  exact StarAlgebra.subset_adjoin ℂ _ ⟨a, rfl⟩

/-! ## The vector state -/

/-- The vector state at the cyclic vector. -/
noncomputable def vectorState : (GasGNS θ →L[ℂ] GasGNS θ) →L[ℂ] ℂ :=
  (innerSL ℂ (cyclic θ)).comp (ContinuousLinearMap.apply ℂ (GasGNS θ) (cyclic θ))

@[simp] theorem vectorState_apply (T : GasGNS θ →L[ℂ] GasGNS θ) :
    vectorState θ T = ⟪cyclic θ, T (cyclic θ)⟫_ℂ := rfl

/-- **The vector state restricts to the Gibbs functional on the monomial algebra.** -/
theorem vectorState_rep (a : GasAlgebra AbelianZetaMode) :
    vectorState θ (rep θ a) = gasGibbs θ a :=
  inner_cyclic_rep_cyclic θ a

@[simp] theorem vectorState_one :
    vectorState θ (ContinuousLinearMap.id ℂ (GasGNS θ)) = 1 := by
  have h := vectorState_rep θ (1 : GasAlgebra AbelianZetaMode)
  rw [rep_one] at h
  rw [h, gasGibbs, gibbs_one]

/-- **The vector state is positive.** -/
theorem vectorState_nonneg (T : GasGNS θ →L[ℂ] GasGNS θ) :
    0 ≤ vectorState θ (ContinuousLinearMap.adjoint T * T) := by
  rw [vectorState_apply]
  show (0 : ℂ) ≤ ⟪cyclic θ, ContinuousLinearMap.adjoint T (T (cyclic θ))⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_right]
  refine RCLike.nonneg_iff.mpr ⟨?_, ?_⟩
  · simpa using inner_self_nonneg (𝕜 := ℂ) (x := T (cyclic θ))
  · simp [← Complex.ofReal_pow]

/-! ## The representation as a `*`-algebra homomorphism -/

/-- The gas algebra is a `*`-ring under the monomial adjoint. -/
noncomputable instance : StarRing (GasAlgebra AbelianZetaMode) where
  star := gasAdjoint
  star_involutive := gasAdjoint_gasAdjoint
  star_mul := gasAdjoint_mul
  star_add := gasAdjoint_add

theorem star_gas_def (a : GasAlgebra AbelianZetaMode) : star a = gasAdjoint a := rfl

/-- **The GNS representation as a unital `*`-algebra homomorphism.** -/
noncomputable def repStarAlgHom :
    GasAlgebra AbelianZetaMode →⋆ₐ[ℂ] (GasGNS θ →L[ℂ] GasGNS θ) where
  toFun := rep θ
  map_one' := rep_one θ
  map_mul' a b := by rw [rep_mul]; rfl
  map_zero' := rep_zero θ
  map_add' := rep_add θ
  commutes' c := by
    show rep θ (MonoidAlgebra.single (1 : GasWord AbelianZetaMode) c) = _
    rw [rep_single, leftMul_one]
    show c • ContinuousLinearMap.id ℂ (GasGNS θ) = _
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  map_star' a := by
    rw [star_gas_def, adjoint_rep]
    rfl

@[simp] theorem repStarAlgHom_apply (a : GasAlgebra AbelianZetaMode) :
    repStarAlgHom θ a = rep θ a := rfl

/-- **The monomial algebra is dense in the C⋆-algebra of the gas.**  Indeed `gasCStar` *is* the
closure of the image of the representation. -/
theorem gasCStar_carrier :
    (gasCStar θ : Set (GasGNS θ →L[ℂ] GasGNS θ)) = closure (Set.range (rep θ)) := by
  have hrange : StarAlgebra.adjoin ℂ (Set.range (rep θ)) = (repStarAlgHom θ).range := by
    have hset : Set.range (rep θ) = ((repStarAlgHom θ).range : Set (GasGNS θ →L[ℂ] GasGNS θ)) := by
      ext T
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, rfl⟩
    rw [hset, StarAlgebra.adjoin_eq]
  show ((StarAlgebra.adjoin ℂ (Set.range (rep θ))).topologicalClosure
    : Set (GasGNS θ →L[ℂ] GasGNS θ)) = _
  rw [hrange]
  show closure ((repStarAlgHom θ).range : Set (GasGNS θ →L[ℂ] GasGNS θ)) = _
  congr 1

/-! ## Uniqueness on the C⋆-algebra -/

/-- **Theorem 4.1, C⋆-form.**  A continuous normalised functional on the operators that satisfies
the KMS exchange identity on the monomial image agrees with the vector state on the whole
C⋆-algebra of the gas.  The exchange identity is imposed on the dense image because the modular
flow at imaginary time is unbounded, so it does not act on the completion. -/
theorem vectorState_unique (ψ : (GasGNS θ →L[ℂ] GasGNS θ) →L[ℂ] ℂ)
    (hone : ψ (ContinuousLinearMap.id ℂ (GasGNS θ)) = 1)
    (hexch : ∀ a b : GasAlgebra AbelianZetaMode,
      ψ (rep θ a * rep θ b) = ψ (rep θ b * rep θ (gasTwist θ a))) :
    ∀ T ∈ gasCStar θ, ψ T = vectorState θ T := by
  set ψ' : GasAlgebra AbelianZetaMode →ₗ[ℂ] ℂ :=
    ψ.toLinearMap.comp (repStarAlgHom θ).toLinearMap with hψ'
  have hψ'one : ψ' 1 = 1 := by
    show ψ (rep θ 1) = 1
    rw [rep_one]
    exact hone
  have hψ'exch : ∀ a b : GasAlgebra AbelianZetaMode,
      ψ' (a * b) = ψ' (b * gasTwist θ a) := by
    intro a b
    show ψ (rep θ (a * b)) = ψ (rep θ (b * gasTwist θ a))
    rw [rep_mul, rep_mul]
    exact hexch a b
  have hψ'eq : ψ' = gasGibbs θ := gasGibbs_unique θ ψ' hψ'exch hψ'one
  have hagree : Set.EqOn (⇑ψ) (⇑(vectorState θ)) (Set.range (rep θ)) := by
    rintro T ⟨a, rfl⟩
    show ψ (rep θ a) = vectorState θ (rep θ a)
    rw [vectorState_rep]
    show ψ' a = gasGibbs θ a
    rw [hψ'eq]
  have hclosure := hagree.closure ψ.continuous (vectorState θ).continuous
  intro T hT
  refine hclosure ?_
  have : T ∈ (gasCStar θ : Set (GasGNS θ →L[ℂ] GasGNS θ)) := hT
  rwa [gasCStar_carrier] at this

end GasPreGNS

end GaloisForLFunctions.HTGeometry

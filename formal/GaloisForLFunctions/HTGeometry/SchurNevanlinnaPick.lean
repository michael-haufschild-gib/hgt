/-
# The Nevanlinna--Pick extension theorem for the Schur class

A family of values `h` prescribed at points `p` of the open unit disc whose Pick kernel is positive
semidefinite is interpolated by a single holomorphic function of the closed unit ball of `H^∞`.

The proof is the lurking isometry.  Positivity of the Pick kernel realizes it as a Gram kernel, the
Pick identity `K + h ⊗ h = p K p + 1` says that two explicit linear maps out of the coefficient
space have equal norms, so one factors isometrically through the other; extending that isometry by
zero on the orthogonal complement produces a contraction of the Hilbert space, and the interpolant
is its transfer function.
-/
import GaloisForLFunctions.HTGeometry.PosSemidefKernelGram

noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} {K : X → X → ℂ}

/-- Adjoin one orthogonal unit vector to a kernel. -/
def augmentKernel (K : X → X → ℂ) : Option X → Option X → ℂ
  | some x, some y => K x y
  | none, none => 1
  | _, _ => 0

@[simp] theorem augmentKernel_some_some (x y : X) :
    augmentKernel K (some x) (some y) = K x y := rfl

@[simp] theorem augmentKernel_none_none : augmentKernel K none none = 1 := rfl

@[simp] theorem augmentKernel_some_none (x : X) : augmentKernel K (some x) none = 0 := rfl

@[simp] theorem augmentKernel_none_some (y : X) : augmentKernel K none (some y) = 0 := rfl

/-- The energy of the augmented kernel splits off the new coordinate. -/
theorem kernelForm_augmentKernel (K : X → X → ℂ) (c : Option X →₀ ℂ) :
    kernelForm (augmentKernel K) c c
      = conj (c none) * c none + kernelForm K c.some c.some := by
  classical
  have hinner : ∀ (y : Option X) (a : ℂ),
      (c.sum fun x b => conj a * b * augmentKernel K x y)
        = conj a * c none * augmentKernel K none y
          + c.some.sum fun x' b => conj a * b * augmentKernel K (some x') y := by
    intro y a
    rw [Finsupp.sum_option_index c (fun x b => conj a * b * augmentKernel K x y)
      (fun o => by ring) (fun o m₁ m₂ => by ring)]
  rw [kernelForm]
  rw [Finsupp.sum_option_index c
    (fun y a => c.sum fun x b => conj a * b * augmentKernel K x y)
    (fun o => by simp) ?_]
  · have hz : (c.some.sum fun x' b => conj (c none) * b * augmentKernel K (some x') none)
        = 0 := by simp
    rw [hinner none (c none), hz, add_zero, augmentKernel_none_none, mul_one]
    congr 1
    rw [kernelForm]
    refine Finsupp.sum_congr (fun y' _ => ?_)
    rw [hinner (some y') (c.some y'), augmentKernel_none_some, mul_zero, zero_add]
    refine Finsupp.sum_congr (fun x' _ => ?_)
    rw [augmentKernel_some_some]
  · intro o m₁ m₂
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr (fun x _ => ?_)
    simp only [map_add]
    ring

/-- **The augmented kernel is positive semidefinite.** -/
theorem isPSDKernel_augmentKernel (hK : IsPSDKernel K) : IsPSDKernel (augmentKernel K) := by
  refine ⟨?_, ?_⟩
  · rintro (_ | x) (_ | y) <;> simp [hK.conj_symm]
  · intro c
    rw [show (c.sum fun y a => c.sum fun x b => conj a * b * augmentKernel K x y)
        = kernelForm (augmentKernel K) c c from rfl, kernelForm_augmentKernel]
    have h1 : (conj (c none) * c none).re = Complex.normSq (c none) := by
      rw [← Complex.normSq_eq_conj_mul_self]
      simp
    have h2 : 0 ≤ (kernelForm K c.some c.some).re := hK.nonneg c.some
    rw [Complex.add_re, h1]
    have := Complex.normSq_nonneg (c none)
    linarith


/-! ## The colligation vectors -/

section Pick

variable [Fact (IsPSDKernel (augmentKernel K))]

/-- The Gram vector of a node. -/
def pickVec (K : X → X → ℂ) [Fact (IsPSDKernel (augmentKernel K))] (x : X) :
    KernelHilbert (augmentKernel K) :=
  KernelHilbert.vector (augmentKernel K) (some x)

/-- The adjoined unit vector. -/
def pickUnit (K : X → X → ℂ) [Fact (IsPSDKernel (augmentKernel K))] :
    KernelHilbert (augmentKernel K) :=
  KernelHilbert.vector (augmentKernel K) none

@[simp] theorem inner_pickVec (x y : X) :
    ⟪pickVec K y, pickVec K x⟫_ℂ = K x y :=
  KernelHilbert.inner_vector (K := augmentKernel K) (some x) (some y)

@[simp] theorem inner_pickUnit_self : ⟪pickUnit K, pickUnit K⟫_ℂ = 1 :=
  KernelHilbert.inner_vector (K := augmentKernel K) none none

@[simp] theorem inner_pickUnit_pickVec (x : X) : ⟪pickUnit K, pickVec K x⟫_ℂ = 0 :=
  KernelHilbert.inner_vector (K := augmentKernel K) (some x) none

@[simp] theorem inner_pickVec_pickUnit (y : X) : ⟪pickVec K y, pickUnit K⟫_ℂ = 0 :=
  KernelHilbert.inner_vector (K := augmentKernel K) none (some y)

theorem norm_pickUnit : ‖(pickUnit K)‖ = 1 := by
  have h : ⟪pickUnit K, pickUnit K⟫_ℂ = 1 := inner_pickUnit_self
  have h2 : ‖(pickUnit K)‖ ^ 2 = 1 := by
    have hx := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (pickUnit K)
    rw [h] at hx
    exact_mod_cast congrArg Complex.re hx.symm
  nlinarith [norm_nonneg (pickUnit K)]

/-- Expansion of an inner product of two finite linear combinations. -/
theorem inner_linearCombination {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v v' : X → E) (c d : X →₀ ℂ) :
    ⟪Finsupp.linearCombination ℂ v c, Finsupp.linearCombination ℂ v' d⟫_ℂ
      = c.sum fun y a => d.sum fun x b => conj a * b * ⟪v y, v' x⟫_ℂ := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  show ⟪∑ y ∈ c.support, c y • v y, ∑ x ∈ d.support, d x • v' x⟫_ℂ
      = ∑ y ∈ c.support, ∑ x ∈ d.support, conj (c y) * d x * ⟪v y, v' x⟫_ℂ
  rw [sum_inner]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [inner_smul_right]
  ring

/-! ## The colligation maps -/

variable (p hval : X → ℂ)

/-- The domain colligation map. -/
def pickDom (K : X → X → ℂ) [Fact (IsPSDKernel (augmentKernel K))] (p : X → ℂ) :
    (X →₀ ℂ) →ₗ[ℂ] KernelHilbert (augmentKernel K) :=
  Finsupp.linearCombination ℂ (fun z => p z • pickVec K z + pickUnit K)

/-- The range colligation map. -/
def pickRan (K : X → X → ℂ) [Fact (IsPSDKernel (augmentKernel K))] (hval : X → ℂ) :
    (X →₀ ℂ) →ₗ[ℂ] KernelHilbert (augmentKernel K) :=
  Finsupp.linearCombination ℂ (fun z => pickVec K z + hval z • pickUnit K)

theorem pickDom_single (z : X) :
    pickDom K p (Finsupp.single z 1) = p z • pickVec K z + pickUnit K := by
  rw [pickDom, Finsupp.linearCombination_single, one_smul]

theorem pickRan_single (z : X) :
    pickRan K hval (Finsupp.single z 1) = pickVec K z + hval z • pickUnit K := by
  rw [pickRan, Finsupp.linearCombination_single, one_smul]

/-- **The Pick identity is an equality of norms.** -/
theorem norm_pickRan_eq_norm_pickDom
    (hid : ∀ x y, K x y + hval x * conj (hval y) = p x * conj (p y) * K x y + 1)
    (c : X →₀ ℂ) : ‖pickRan K hval c‖ = ‖pickDom K p c‖ := by
  have hin : ⟪pickDom K p c, pickDom K p c⟫_ℂ = ⟪pickRan K hval c, pickRan K hval c⟫_ℂ := by
    rw [pickDom, pickRan, inner_linearCombination, inner_linearCombination]
    refine Finsupp.sum_congr (fun y _ => Finsupp.sum_congr (fun x _ => ?_))
    congr 1
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      inner_pickVec, inner_pickUnit_self, inner_pickUnit_pickVec, inner_pickVec_pickUnit,
      mul_zero, add_zero, zero_add, mul_one]
    linear_combination -hid x y
  have h1 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (pickDom K p c)
  have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (pickRan K hval c)
  rw [hin, h2] at h1
  have h3 : ‖pickRan K hval c‖ ^ 2 = ‖pickDom K p c‖ ^ 2 := by
    exact_mod_cast h1
  nlinarith [norm_nonneg (pickRan K hval c), norm_nonneg (pickDom K p c)]

/-- **The lurking contraction.**  The Pick identity produces a contraction of the Gram space
carrying each domain colligation vector to the corresponding range colligation vector. -/
theorem exists_pick_contraction
    (hid : ∀ x y, K x y + hval x * conj (hval y) = p x * conj (p y) * K x y + 1) :
    ∃ V : KernelHilbert (augmentKernel K) →L[ℂ] KernelHilbert (augmentKernel K),
      (∀ v, ‖V v‖ ≤ ‖v‖) ∧
        ∀ z : X, V (p z • pickVec K z + pickUnit K) = pickVec K z + hval z • pickUnit K := by
  classical
  set S : Submodule ℂ (KernelHilbert (augmentKernel K)) := LinearMap.range (pickDom K p) with hS
  set Sc : Submodule ℂ (KernelHilbert (augmentKernel K)) := S.topologicalClosure with hSc
  have hmem : ∀ c, pickDom K p c ∈ Sc := fun c =>
    S.le_topologicalClosure (LinearMap.mem_range_self _ c)
  set e₀ : (X →₀ ℂ) →ₗ[ℂ] ↥Sc := (pickDom K p).codRestrict Sc hmem with he₀
  have hnorm₀ : ∀ c, ‖e₀ c‖ = ‖pickDom K p c‖ := fun c => rfl
  have hdense : DenseRange ⇑e₀ := by
    intro y
    rw [closure_subtype]
    have himg : Subtype.val '' (Set.range ⇑e₀) = (S : Set (KernelHilbert (augmentKernel K))) := by
      ext v
      constructor
      · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
        exact ⟨c, rfl⟩
      · rintro ⟨c, rfl⟩
        exact ⟨e₀ c, ⟨c, rfl⟩, rfl⟩
    rw [himg]
    have h1 : (Sc : Set (KernelHilbert (augmentKernel K)))
        = closure (S : Set (KernelHilbert (augmentKernel K))) := by
      rw [hSc]
      exact Submodule.topologicalClosure_coe S
    rw [← h1]
    exact y.2
  have hb : ∀ c, ‖pickRan K hval c‖ ≤ 1 * ‖e₀ c‖ := by
    intro c
    rw [one_mul, hnorm₀]
    exact le_of_eq (norm_pickRan_eq_norm_pickDom p hval hid c)
  set W : ↥Sc →L[ℂ] KernelHilbert (augmentKernel K) := (pickRan K hval).extendOfNorm e₀ with hW
  refine ⟨W ∘L Sc.orthogonalProjectionOnto, ?_, ?_⟩
  · intro v
    have h1 : ‖W (Sc.orthogonalProjectionOnto v)‖ ≤ 1 * ‖Sc.orthogonalProjectionOnto v‖ :=
      LinearMap.norm_extendOfNorm_apply_le hdense 1 hb _
    have h2 : ‖Sc.orthogonalProjectionOnto v‖ ≤ ‖v‖ := by
      calc ‖Sc.orthogonalProjectionOnto v‖ ≤ ‖Sc.orthogonalProjectionOnto‖ * ‖v‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖v‖ :=
            mul_le_mul_of_nonneg_right (Submodule.orthogonalProjectionOnto_norm_le Sc) (norm_nonneg v)
        _ = ‖v‖ := one_mul _
    rw [one_mul] at h1
    exact le_trans h1 h2
  · intro z
    have hval0 : pickDom K p (Finsupp.single z 1) = p z • pickVec K z + pickUnit K :=
      pickDom_single p z
    have hproj : Sc.orthogonalProjectionOnto (pickDom K p (Finsupp.single z 1))
        = e₀ (Finsupp.single z 1) := by
      have : (e₀ (Finsupp.single z 1) : KernelHilbert (augmentKernel K))
          = pickDom K p (Finsupp.single z 1) := rfl
      rw [← this]
      exact Sc.orthogonalProjectionOnto_mem_subspace_eq_self _
    show W (Sc.orthogonalProjectionOnto (p z • pickVec K z + pickUnit K)) = _
    rw [← hval0, hproj, hW, LinearMap.extendOfNorm_eq hdense ⟨1, hb⟩, pickRan_single]

end Pick

end GaloisForLFunctions.HTGeometry

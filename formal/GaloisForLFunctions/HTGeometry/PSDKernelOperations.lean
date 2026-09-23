import GaloisForLFunctions.HTGeometry.PSDKernelMatrixBridge

/-!
# Operations on positive semidefinite kernels

The coefficient-vector form of kernel positivity is natural in the index type, so a positive
semidefinite kernel stays positive after pullback along an arbitrary map, and every finite Gram
matrix of a positive semidefinite kernel is positive semidefinite.  Combining the latter with the
Schur product theorem for matrices gives the entrywise product of two positive semidefinite
kernels.
-/

noncomputable section

open scoped InnerProductSpace ComplexOrder ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

variable {X Y : Type*} {K K₁ K₂ : X → X → ℂ}

/-! ## Naturality of the kernel form -/

/-- The kernel form of a pulled back kernel is the kernel form of the pushed forward coefficient
vectors. -/
theorem kernelForm_mapDomain (K : X → X → ℂ) (φ : Y → X) (f g : Y →₀ ℂ) :
    kernelForm K (Finsupp.mapDomain φ f) (Finsupp.mapDomain φ g)
      = kernelForm (fun a b => K (φ a) (φ b)) f g := by
  classical
  have hinner : ∀ (y : X) (a : ℂ),
      ((Finsupp.mapDomain φ g).sum fun x b => conj a * b * K x y)
        = g.sum fun x b => conj a * b * K (φ x) y :=
    fun y a => Finsupp.sum_mapDomain_index (fun b => by ring) (fun b m₁ m₂ => by ring)
  have hzero : ∀ y : X,
      ((Finsupp.mapDomain φ g).sum fun x b => conj (0 : ℂ) * b * K x y) = 0 := by
    intro y
    simp
  have hadd : ∀ (y : X) (m₁ m₂ : ℂ),
      ((Finsupp.mapDomain φ g).sum fun x b => conj (m₁ + m₂) * b * K x y)
        = ((Finsupp.mapDomain φ g).sum fun x b => conj m₁ * b * K x y)
          + ((Finsupp.mapDomain φ g).sum fun x b => conj m₂ * b * K x y) := by
    intro y m₁ m₂
    rw [← Finsupp.sum_add]
    exact Finsupp.sum_congr fun x _ => by rw [map_add]; ring
  rw [kernelForm, Finsupp.sum_mapDomain_index hzero hadd, kernelForm]
  exact Finsupp.sum_congr fun y _ => hinner (φ y) (f y)

theorem isPSDKernel_iff_kernelForm :
    IsPSDKernel K ↔ (∀ x y, conj (K x y) = K y x) ∧ ∀ c : X →₀ ℂ, 0 ≤ (kernelForm K c c).re :=
  ⟨fun h => ⟨h.conj_symm, h.nonneg⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Pullback.**  A positive semidefinite kernel stays positive semidefinite after composing the
index with an arbitrary map. -/
theorem IsPSDKernel.comp (hK : IsPSDKernel K) (φ : Y → X) :
    IsPSDKernel (fun a b => K (φ a) (φ b)) := by
  refine isPSDKernel_iff_kernelForm.mpr ⟨fun a b => hK.conj_symm _ _, fun c => ?_⟩
  rw [← kernelForm_mapDomain]
  exact (isPSDKernel_iff_kernelForm.mp hK).2 _

/-! ## Finite Gram matrices -/

/-- **Every finite Gram matrix of a positive semidefinite kernel is positive semidefinite.**  The
proof evaluates the matrix form on the Gram vectors of the kernel Hilbert space. -/
theorem IsPSDKernel.posSemidef (hK : IsPSDKernel K) {n : ℕ} (w : Fin n → X) :
    (Matrix.of fun j k => K (w j) (w k)).PosSemidef := by
  classical
  haveI : Fact (IsPSDKernel K) := ⟨hK⟩
  set v : Fin n → KernelHilbert K := fun j => KernelHilbert.vector K (w j) with hv
  have hentry : ∀ j k, (Matrix.of fun j k => K (w j) (w k)) j k = ⟪v k, v j⟫_ℂ := by
    intro j k
    rw [Matrix.of_apply, hv]
    exact (KernelHilbert.inner_vector (K := K) (w j) (w k)).symm
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext j k
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
    exact hK.conj_symm _ _
  · intro x
    set C : KernelHilbert K := ∑ j, conj (x j) • v j with hC
    have hform : star x ⬝ᵥ (Matrix.of fun j k => K (w j) (w k)).mulVec x = ⟪C, C⟫_ℂ := by
      rw [hC, sum_inner]
      have hstep : ∀ j : Fin n,
          ⟪conj (x j) • v j, ∑ k, conj (x k) • v k⟫_ℂ
            = ∑ k, x j * conj (x k) * ⟪v j, v k⟫_ℂ := by
        intro j
        rw [inner_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [inner_smul_left, inner_smul_right, Complex.conj_conj]
        ring
      simp only [hstep]
      rw [Finset.sum_comm]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hentry j k]
      ring
    rw [hform, inner_self_eq_norm_sq_to_K]
    have h0 : (0 : ℂ) ≤ ((‖C‖ ^ (2 : ℕ) : ℝ) : ℂ) := Complex.zero_le_real.mpr (sq_nonneg _)
    push_cast at h0
    exact h0

/-! ## Algebraic closure properties -/

/-- **Schur product.**  The entrywise product of two positive semidefinite kernels is positive
semidefinite. -/
theorem IsPSDKernel.mul (h₁ : IsPSDKernel K₁) (h₂ : IsPSDKernel K₂) :
    IsPSDKernel (fun x y => K₁ x y * K₂ x y) := by
  refine isPSDKernel_of_forall_posSemidef (fun x y => ?_) (fun n w => ?_)
  · rw [map_mul, h₁.conj_symm, h₂.conj_symm]
  · have hh := (h₁.posSemidef w).hadamard (h₂.posSemidef w)
    have heq : (Matrix.of fun j k => K₁ (w j) (w k)).hadamard
        (Matrix.of fun j k => K₂ (w j) (w k))
        = Matrix.of fun j k => K₁ (w j) (w k) * K₂ (w j) (w k) := by
      ext j k
      simp [Matrix.hadamard]
    rwa [heq] at hh

/-- Sums of positive semidefinite kernels are positive semidefinite. -/
theorem IsPSDKernel.add (h₁ : IsPSDKernel K₁) (h₂ : IsPSDKernel K₂) :
    IsPSDKernel (fun x y => K₁ x y + K₂ x y) := by
  refine isPSDKernel_iff_kernelForm.mpr ⟨fun x y => ?_, fun c => ?_⟩
  · rw [map_add, h₁.conj_symm, h₂.conj_symm]
  · have hsplit : kernelForm (fun x y => K₁ x y + K₂ x y) c c
        = kernelForm K₁ c c + kernelForm K₂ c c := by
      rw [kernelForm, kernelForm, kernelForm, ← Finsupp.sum_add]
      refine Finsupp.sum_congr fun y _ => ?_
      rw [← Finsupp.sum_add]
      exact Finsupp.sum_congr fun x _ => by ring
    rw [hsplit, Complex.add_re]
    exact add_nonneg ((isPSDKernel_iff_kernelForm.mp h₁).2 c)
      ((isPSDKernel_iff_kernelForm.mp h₂).2 c)

/-- The constant kernel `1` is positive semidefinite. -/
theorem isPSDKernel_one : IsPSDKernel (fun _ _ : X => (1 : ℂ)) := by
  refine isPSDKernel_of_forall_posSemidef (fun x y => by simp) (fun n w => ?_)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext j k
    simp
  · intro x
    have hval : star x ⬝ᵥ (Matrix.of fun _ _ : Fin n => (1 : ℂ)).mulVec x
        = conj (∑ j, x j) * (∑ j, x j) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def,
        one_mul, map_sum]
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    rw [hval, ← Complex.normSq_eq_conj_mul_self]
    exact Complex.zero_le_real.mpr (Complex.normSq_nonneg _)

/-- **Rank one.**  Every kernel `e x · conj (e y)` is positive semidefinite. -/
theorem isPSDKernel_rankOne (e : X → ℂ) :
    IsPSDKernel (fun x y => e x * conj (e y)) := by
  refine isPSDKernel_of_forall_posSemidef (fun x y => by rw [map_mul, Complex.conj_conj]; ring)
    (fun n w => ?_)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext j k
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def, map_mul,
      Complex.conj_conj]
    ring
  · intro x
    set A : ℂ := ∑ j, conj (x j) * e (w j) with hA
    have hval : star x ⬝ᵥ (Matrix.of fun j k => e (w j) * conj (e (w k))).mulVec x
        = A * conj A := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def, hA,
        map_sum, map_mul, Complex.conj_conj]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hval, mul_comm, ← Complex.normSq_eq_conj_mul_self]
    exact Complex.zero_le_real.mpr (Complex.normSq_nonneg _)

/-- **Gram kernels are positive.**  Every kernel of the form `⟪R y, R x⟫` in an inner product space
is positive semidefinite. -/
theorem isPSDKernel_gram {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (R : X → H) :
    IsPSDKernel (fun x y => ⟪R y, R x⟫_ℂ) := by
  refine isPSDKernel_of_forall_posSemidef (fun x y => inner_conj_symm _ _) (fun n w => ?_)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext j k
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
    exact inner_conj_symm _ _
  · intro x
    set C : H := ∑ j, conj (x j) • R (w j) with hC
    have hform : star x ⬝ᵥ (Matrix.of fun j k => ⟪R (w k), R (w j)⟫_ℂ).mulVec x = ⟪C, C⟫_ℂ := by
      rw [hC, sum_inner]
      have hstep : ∀ j : Fin n,
          ⟪conj (x j) • R (w j), ∑ k, conj (x k) • R (w k)⟫_ℂ
            = ∑ k, x j * conj (x k) * ⟪R (w j), R (w k)⟫_ℂ := by
        intro j
        rw [inner_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [inner_smul_left, inner_smul_right, Complex.conj_conj]
        ring
      simp only [hstep]
      rw [Finset.sum_comm]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hform, inner_self_eq_norm_sq_to_K]
    have h0 : (0 : ℂ) ≤ ((‖C‖ ^ (2 : ℕ) : ℝ) : ℂ) := Complex.zero_le_real.mpr (sq_nonneg _)
    push_cast at h0
    exact h0

/-! ## Finite kernel energies -/

/-- The energy of a finite node/coefficient system against a kernel. -/
def kernelEnergy (K : X → X → ℂ) {n : ℕ} (c : Fin n → ℂ) (w : Fin n → X) : ℂ :=
  ∑ j, ∑ k, conj (c j) * c k * K (w j) (w k)

theorem dotProduct_mulVec_kernelMatrix (K : X → X → ℂ) {n : ℕ} (c : Fin n → ℂ)
    (w : Fin n → X) :
    star c ⬝ᵥ (Matrix.of fun j k => K (w j) (w k)).mulVec c = kernelEnergy K c w := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def,
    kernelEnergy]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem kernelEnergy_sub (K₁ K₂ : X → X → ℂ) {n : ℕ} (c : Fin n → ℂ) (w : Fin n → X) :
    kernelEnergy (fun x y => K₁ x y - K₂ x y) c w
      = kernelEnergy K₁ c w - kernelEnergy K₂ c w := by
  simp only [kernelEnergy, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- **The Gram realization of a finite kernel energy.**  The energy is the squared norm of the
corresponding combination of Gram vectors. -/
theorem inner_self_kernelCombination (K : X → X → ℂ) [Fact (IsPSDKernel K)]
    {n : ℕ} (c : Fin n → ℂ) (w : Fin n → X) :
    ⟪∑ j, conj (c j) • KernelHilbert.vector K (w j),
        ∑ j, conj (c j) • KernelHilbert.vector K (w j)⟫_ℂ = kernelEnergy K c w := by
  have hL : ⟪∑ j, conj (c j) • KernelHilbert.vector K (w j),
        ∑ j, conj (c j) • KernelHilbert.vector K (w j)⟫_ℂ
      = ∑ j, ∑ k, c j * conj (c k) * K (w k) (w j) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_left, inner_smul_right, Complex.conj_conj, KernelHilbert.inner_vector]
    ring
  rw [hL, kernelEnergy, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem norm_sq_kernelCombination (K : X → X → ℂ) [Fact (IsPSDKernel K)]
    {n : ℕ} (c : Fin n → ℂ) (w : Fin n → X) :
    ((‖∑ j, conj (c j) • KernelHilbert.vector K (w j)‖ : ℂ)) ^ (2 : ℕ) = kernelEnergy K c w := by
  rw [← inner_self_kernelCombination K c w, inner_self_eq_norm_sq_to_K]
  rfl

/-- A Hermitian matrix whose quadratic forms have nonnegative real part is positive
semidefinite. -/
theorem posSemidef_of_isHermitian_of_re_nonneg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hH : M.IsHermitian) (h : ∀ x : Fin n → ℂ, 0 ≤ (star x ⬝ᵥ M.mulVec x).re) : M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH ?_
  intro x
  have hexp : ∀ y : Fin n → ℂ,
      star y ⬝ᵥ M.mulVec y = ∑ j, ∑ k, conj (y j) * (M j k * y k) := by
    intro y
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def]
    exact Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
  have hconj : conj (star x ⬝ᵥ M.mulVec x) = star x ⬝ᵥ M.mulVec x := by
    rw [hexp]
    simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hMab : conj (M b a) = M a b := by
      have hstar := hH.apply a b
      simpa only [RCLike.star_def] using hstar
    rw [hMab]
    ring
  exact Complex.le_def.mpr ⟨by simpa using h x,
    by simpa using (Complex.conj_eq_iff_im.mp hconj).symm⟩

/-- **Energy form of positivity.**  A Hermitian kernel is positive semidefinite exactly when every
finite node/coefficient system has nonnegative energy. -/
theorem isPSDKernel_iff_forall_energy_nonneg {K : X → X → ℂ}
    (hherm : ∀ x y, conj (K x y) = K y x) :
    IsPSDKernel K ↔ ∀ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → X), 0 ≤ (kernelEnergy K c w).re := by
  constructor
  · intro hK n c w
    have hnn := (hK.posSemidef w).dotProduct_mulVec_nonneg c
    rw [dotProduct_mulVec_kernelMatrix] at hnn
    simpa using (Complex.le_def.mp hnn).1
  · intro h
    refine isPSDKernel_of_forall_posSemidef hherm (fun n w => ?_)
    refine posSemidef_of_isHermitian_of_re_nonneg ?_ (fun c => ?_)
    · ext j k
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
      exact hherm _ _
    · rw [dotProduct_mulVec_kernelMatrix]
      exact h n c w

/-- **Kernel domination.**  One positive semidefinite kernel dominates another exactly when it
dominates it on every finite node/coefficient system. -/
theorem isPSDKernel_sub_iff_forall_energy_le {K₁ K₂ : X → X → ℂ} (h₁ : IsPSDKernel K₁)
    (h₂ : IsPSDKernel K₂) :
    IsPSDKernel (fun x y => K₁ x y - K₂ x y) ↔
      ∀ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → X),
        (kernelEnergy K₂ c w).re ≤ (kernelEnergy K₁ c w).re := by
  constructor
  · intro hD n c w
    have hnn := (hD.posSemidef w).dotProduct_mulVec_nonneg c
    have hrw := dotProduct_mulVec_kernelMatrix (fun x y => K₁ x y - K₂ x y) c w
    rw [hrw, kernelEnergy_sub] at hnn
    have hre := (Complex.le_def.mp hnn).1
    simp only [Complex.zero_re, Complex.sub_re] at hre
    linarith
  · intro hle
    refine isPSDKernel_of_forall_posSemidef (fun x y => ?_) (fun n w => ?_)
    · rw [map_sub, h₁.conj_symm, h₂.conj_symm]
    · refine posSemidef_of_isHermitian_of_re_nonneg ?_ (fun c => ?_)
      · ext j k
        simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def, map_sub]
        rw [h₁.conj_symm, h₂.conj_symm]
      · have hrw := dotProduct_mulVec_kernelMatrix (fun x y => K₁ x y - K₂ x y) c w
        rw [hrw, kernelEnergy_sub, Complex.sub_re]
        have := hle n c w
        linarith

end GaloisForLFunctions.HTGeometry

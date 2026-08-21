import Mathlib

/-!
# The complete-history invariant metric cone

Fix a family of transports `T : Gamma -> Matrix n n C` and one positive metric `H` invariant under
all of them.  Multiplication by `H` is a bijection

```text
{A : A invertible, A commutes with every T g, A is H-self-adjoint, H A positive}
   -->  {K : K positive, T g conj-transpose * K * T g = K},
A |-> H A,
```

with inverse `K |-> H^{-1} K`.  Consequently the invariant positive metric is unique up to one
positive scale exactly when the positive `H`-self-adjoint part of the transport commutant is a
single ray.

Two explicit sources of extra rays are recorded.  A nontrivial `H`-orthogonal projection commuting
with every transport gives a two-weight family, and a finite `H`-orthogonal sector system gives an
injective family of weight vectors modulo one common positive scale.

The connected-history reduction is the observation that a compatible metric field is the
inverse-adjoint transport of its root metric, and that two chosen transports agree exactly when the
root loop between them preserves the root metric.
-/

open Matrix
open scoped ComplexOrder

namespace GaloisForLFunctions.HTGeometry

variable {n : Type*} [Fintype n] [DecidableEq n] {Γ : Type*}

/-- A complete-history invariant positive metric for the transport family `T`. -/
structure IsInvariantMetric (T : Γ → Matrix n n ℂ) (K : Matrix n n ℂ) : Prop where
  posDef : K.PosDef
  invariant : ∀ g, (T g)ᴴ * K * T g = K

/-- A positive `H`-self-adjoint invertible factor in the complete-history commutant. -/
structure IsCommutantFactor (T : Γ → Matrix n n ℂ) (H A : Matrix n n ℂ) : Prop where
  unit : IsUnit A
  commutes : ∀ g, A * T g = T g * A
  selfAdjoint : Aᴴ * H = H * A
  positive : (H * A).PosDef

theorem isUnit_det_of_posDef {K : Matrix n n ℂ} (hK : K.PosDef) : IsUnit K.det :=
  (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit

/-- Every transport preserving a positive metric is invertible. -/
theorem isUnit_det_transport {T : Γ → Matrix n n ℂ} {K : Matrix n n ℂ}
    (hK : IsInvariantMetric T K) (g : Γ) : IsUnit (T g).det := by
  have hdet := congrArg Matrix.det (hK.invariant g)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at hdet
  have hKdet : K.det ≠ 0 := (isUnit_det_of_posDef hK.posDef).ne_zero
  field_simp at hdet
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0] at hdet
  simp at hdet

/-! ## The transport transfer identities -/

theorem isUnit_det_conjTranspose {S : Matrix n n ℂ} (hS : IsUnit S.det) : IsUnit (Sᴴ).det := by
  rw [Matrix.det_conjTranspose]
  exact hS.star

/-- An invariant form is transported by the inverse adjoint. -/
theorem mul_transport_eq {S K : Matrix n n ℂ} (hS : IsUnit S.det) (hinv : Sᴴ * K * S = K) :
    K * S = (Sᴴ)⁻¹ * K := by
  have hSH : IsUnit (Sᴴ).det := isUnit_det_conjTranspose hS
  calc K * S = (Sᴴ)⁻¹ * (Sᴴ * K * S) := by
        rw [← mul_assoc, ← mul_assoc, Matrix.nonsing_inv_mul _ hSH, one_mul]
    _ = (Sᴴ)⁻¹ * K := by rw [hinv]

/-- The inverse of an invariant form intertwines in the opposite direction. -/
theorem inv_mul_transport_eq {S H : Matrix n n ℂ} (hS : IsUnit S.det) (hH : IsUnit H.det)
    (hinv : Sᴴ * H * S = H) : H⁻¹ * (Sᴴ)⁻¹ = S * H⁻¹ := by
  have h1 : H * S = (Sᴴ)⁻¹ * H := mul_transport_eq hS hinv
  calc H⁻¹ * (Sᴴ)⁻¹ = H⁻¹ * ((Sᴴ)⁻¹ * H) * H⁻¹ := by
        rw [mul_assoc, mul_assoc, Matrix.mul_nonsing_inv _ hH, mul_one]
    _ = H⁻¹ * (H * S) * H⁻¹ := by rw [h1]
    _ = S * H⁻¹ := by
        rw [← mul_assoc, Matrix.nonsing_inv_mul _ hH, one_mul]

/-! ## The classification -/

/-- **Every positive commutant factor gives an invariant metric.** -/
theorem isInvariantMetric_mul {T : Γ → Matrix n n ℂ} {H A : Matrix n n ℂ}
    (hH : IsInvariantMetric T H) (hA : IsCommutantFactor T H A) :
    IsInvariantMetric T (H * A) := by
  refine ⟨hA.positive, fun g => ?_⟩
  calc (T g)ᴴ * (H * A) * T g = (T g)ᴴ * H * (A * T g) := by simp only [mul_assoc]
    _ = (T g)ᴴ * H * (T g * A) := by rw [hA.commutes g]
    _ = ((T g)ᴴ * H * T g) * A := by simp only [mul_assoc]
    _ = H * A := by rw [hH.invariant g]

/-- **The ratio of two invariant metrics is a positive commutant factor.** -/
theorem isCommutantFactor_inv_mul {T : Γ → Matrix n n ℂ} {H K : Matrix n n ℂ}
    (hH : IsInvariantMetric T H) (hK : IsInvariantMetric T K) :
    IsCommutantFactor T H (H⁻¹ * K) := by
  have hHd : IsUnit H.det := isUnit_det_of_posDef hH.posDef
  have hKd : IsUnit K.det := isUnit_det_of_posDef hK.posDef
  have hHA : H * (H⁻¹ * K) = K := by
    rw [← mul_assoc, Matrix.mul_nonsing_inv _ hHd, one_mul]
  refine ⟨?_, fun g => ?_, ?_, ?_⟩
  · refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
    rw [Matrix.det_mul, Matrix.det_nonsing_inv]
    exact (hHd.ringInverse).mul hKd
  · have hTg : IsUnit (T g).det := isUnit_det_transport hH g
    have h1 : K * T g = ((T g)ᴴ)⁻¹ * K := mul_transport_eq hTg (hK.invariant g)
    have h2 : H⁻¹ * ((T g)ᴴ)⁻¹ = T g * H⁻¹ := inv_mul_transport_eq hTg hHd (hH.invariant g)
    calc H⁻¹ * K * T g = H⁻¹ * (K * T g) := by rw [mul_assoc]
      _ = H⁻¹ * (((T g)ᴴ)⁻¹ * K) := by rw [h1]
      _ = (H⁻¹ * ((T g)ᴴ)⁻¹) * K := by rw [mul_assoc]
      _ = (T g * H⁻¹) * K := by rw [h2]
      _ = T g * (H⁻¹ * K) := by rw [mul_assoc]
  · have hHherm : Hᴴ = H := hH.posDef.isHermitian
    have hKherm : Kᴴ = K := hK.posDef.isHermitian
    calc (H⁻¹ * K)ᴴ * H = Kᴴ * (H⁻¹)ᴴ * H := by rw [Matrix.conjTranspose_mul]
      _ = K * H⁻¹ * H := by rw [hKherm, Matrix.conjTranspose_nonsing_inv, hHherm]
      _ = K := by rw [mul_assoc, Matrix.nonsing_inv_mul _ hHd, mul_one]
      _ = H * (H⁻¹ * K) := hHA.symm
  · rw [hHA]
    exact hK.posDef

/-- The two constructions are mutually inverse. -/
theorem isCommutantFactor_inv_mul_mul {H A : Matrix n n ℂ} (hHd : IsUnit H.det) :
    H⁻¹ * (H * A) = A := by
  rw [← mul_assoc, Matrix.nonsing_inv_mul _ hHd, one_mul]

theorem mul_inv_mul {H K : Matrix n n ℂ} (hHd : IsUnit H.det) : H * (H⁻¹ * K) = K := by
  rw [← mul_assoc, Matrix.mul_nonsing_inv _ hHd, one_mul]

/-- **The complete-history metric-cone classification.**  Multiplication by a fixed invariant
metric `H` is a bijection from the positive `H`-self-adjoint commutant factors onto the invariant
positive metrics. -/
theorem invariantMetric_image_eq {T : Γ → Matrix n n ℂ} {H : Matrix n n ℂ}
    (hH : IsInvariantMetric T H) :
    {K : Matrix n n ℂ | IsInvariantMetric T K}
      = (fun A => H * A) '' {A : Matrix n n ℂ | IsCommutantFactor T H A} := by
  have hHd : IsUnit H.det := isUnit_det_of_posDef hH.posDef
  ext K
  constructor
  · intro hK
    exact ⟨H⁻¹ * K, isCommutantFactor_inv_mul hH hK, mul_inv_mul hHd⟩
  · rintro ⟨A, hA, rfl⟩
    exact isInvariantMetric_mul hH hA

/-! ## Ray rigidity -/

theorem isUnit_det_smul_one {c : ℝ} (hc : c ≠ 0) :
    IsUnit (((c : ℂ) • (1 : Matrix n n ℂ)).det) := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by exact_mod_cast hc)))

omit [DecidableEq n] in
theorem isInvariantMetric_smul {T : Γ → Matrix n n ℂ} {H : Matrix n n ℂ}
    (hH : IsInvariantMetric T H) {c : ℝ} (hc : 0 < c) :
    IsInvariantMetric T ((c : ℂ) • H) := by
  refine ⟨hH.posDef.smul (by exact_mod_cast hc), fun g => ?_⟩
  rw [Matrix.mul_smul, Matrix.smul_mul, hH.invariant g]

theorem isCommutantFactor_smul_one {T : Γ → Matrix n n ℂ} {H : Matrix n n ℂ}
    (hH : IsInvariantMetric T H) {c : ℝ} (hc : 0 < c) :
    IsCommutantFactor T H ((c : ℂ) • (1 : Matrix n n ℂ)) := by
  have hHA : H * ((c : ℂ) • (1 : Matrix n n ℂ)) = (c : ℂ) • H := by
    rw [Matrix.mul_smul, mul_one]
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_smul_one hc.ne'), fun g => ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, one_mul,
      Matrix.mul_smul, mul_one]
    simp
  · rw [hHA]
    exact hH.posDef.smul (by exact_mod_cast hc)

/-- **Ray rigidity.**  The invariant positive metric is unique up to one positive scale exactly
when the positive `H`-self-adjoint commutant is one ray. -/
theorem invariantMetric_eq_ray_iff {T : Γ → Matrix n n ℂ} {H : Matrix n n ℂ}
    (hH : IsInvariantMetric T H) :
    ({K : Matrix n n ℂ | IsInvariantMetric T K} = {K | ∃ c : ℝ, 0 < c ∧ K = (c : ℂ) • H})
      ↔ ({A : Matrix n n ℂ | IsCommutantFactor T H A}
          = {A | ∃ c : ℝ, 0 < c ∧ A = (c : ℂ) • (1 : Matrix n n ℂ)}) := by
  have hHd : IsUnit H.det := isUnit_det_of_posDef hH.posDef
  constructor
  · intro hM
    ext A
    constructor
    · intro hA
      have hHA : IsInvariantMetric T (H * A) := isInvariantMetric_mul hH hA
      obtain ⟨c, hc, hcH⟩ : ∃ c : ℝ, 0 < c ∧ H * A = (c : ℂ) • H :=
        (Set.ext_iff.mp hM (H * A)).mp hHA
      refine ⟨c, hc, ?_⟩
      calc A = H⁻¹ * (H * A) := (isCommutantFactor_inv_mul_mul hHd).symm
        _ = H⁻¹ * ((c : ℂ) • H) := by rw [hcH]
        _ = (c : ℂ) • (H⁻¹ * H) := by rw [Matrix.mul_smul]
        _ = (c : ℂ) • (1 : Matrix n n ℂ) := by rw [Matrix.nonsing_inv_mul _ hHd]
    · rintro ⟨c, hc, rfl⟩
      exact isCommutantFactor_smul_one hH hc
  · intro hC
    ext K
    constructor
    · intro hK
      have hA : IsCommutantFactor T H (H⁻¹ * K) := isCommutantFactor_inv_mul hH hK
      obtain ⟨c, hc, hcI⟩ : ∃ c : ℝ, 0 < c ∧ H⁻¹ * K = (c : ℂ) • (1 : Matrix n n ℂ) :=
        (Set.ext_iff.mp hC (H⁻¹ * K)).mp hA
      refine ⟨c, hc, ?_⟩
      calc K = H * (H⁻¹ * K) := (mul_inv_mul hHd).symm
        _ = H * ((c : ℂ) • (1 : Matrix n n ℂ)) := by rw [hcI]
        _ = (c : ℂ) • H := by rw [Matrix.mul_smul, mul_one]
    · rintro ⟨c, hc, rfl⟩
      exact isInvariantMetric_smul hH hc

/-! ## Connected-history root transport -/

/-- **Root transport.**  A compatible metric field on a connected history graph is determined by
its root metric: every fibre is the inverse-adjoint transport of the root metric. -/
theorem metricField_eq_root_transport {O : Type*} {c : O → Matrix n n ℂ} {K : O → Matrix n n ℂ}
    {o₀ : O} (hc : ∀ o, IsUnit (c o).det)
    (hcomp : ∀ o, (c o)ᴴ * K o * c o = K o₀) (o : O) :
    K o = ((c o)ᴴ)⁻¹ * K o₀ * (c o)⁻¹ := by
  have hcH : IsUnit ((c o)ᴴ).det := isUnit_det_conjTranspose (hc o)
  have e1 : ((c o)ᴴ)⁻¹ * K o₀ * (c o)⁻¹
      = (((c o)ᴴ)⁻¹ * (c o)ᴴ) * K o * (c o * (c o)⁻¹) := by
    rw [← hcomp o]
    simp only [mul_assoc]
  rw [e1, Matrix.nonsing_inv_mul _ hcH, Matrix.mul_nonsing_inv _ (hc o), one_mul, mul_one]

/-- Conjugation by an invertible transport recovers the root metric. -/
theorem conjTranspose_transport_cancel {c K₀ : Matrix n n ℂ} (hc : IsUnit c.det) :
    cᴴ * ((cᴴ)⁻¹ * K₀ * c⁻¹) * c = K₀ := by
  have hcH : IsUnit (cᴴ).det := isUnit_det_conjTranspose hc
  rw [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hcH, one_mul, mul_assoc,
    Matrix.nonsing_inv_mul _ hc, mul_one]

/-- **Path independence is root-loop invariance.**  Two chosen transports to the same object give
the same fibre metric exactly when the root loop between them preserves the root metric. -/
theorem metricField_transport_congr {c c' K₀ : Matrix n n ℂ} (hc' : IsUnit c'.det) :
    (cᴴ)⁻¹ * K₀ * c⁻¹ = (c'ᴴ)⁻¹ * K₀ * c'⁻¹ ↔ (c⁻¹ * c')ᴴ * K₀ * (c⁻¹ * c') = K₀ := by
  have hexpand : (c⁻¹ * c')ᴴ * K₀ * (c⁻¹ * c') = c'ᴴ * ((cᴴ)⁻¹ * K₀ * c⁻¹) * c' := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
    simp only [mul_assoc]
  constructor
  · intro hEq
    rw [hexpand, hEq, conjTranspose_transport_cancel hc']
  · intro hloop
    rw [hexpand] at hloop
    have hcong := congrArg (fun M => ((c'ᴴ)⁻¹ * M) * c'⁻¹) hloop
    rw [← hcong]
    have hcH' : IsUnit (c'ᴴ).det := isUnit_det_conjTranspose hc'
    rw [show ((c'ᴴ)⁻¹ * (c'ᴴ * ((cᴴ)⁻¹ * K₀ * c⁻¹) * c')) * c'⁻¹
        = (((c'ᴴ)⁻¹ * c'ᴴ) * ((cᴴ)⁻¹ * K₀ * c⁻¹)) * (c' * c'⁻¹) by simp only [mul_assoc]]
    rw [Matrix.nonsing_inv_mul _ hcH', Matrix.mul_nonsing_inv _ hc', one_mul, mul_one]


/-! ## Sector spectators -/

/-- A finite `H`-orthogonal sector system commuting with every complete-history transport. -/
structure IsSectorSystem (T : Γ → Matrix n n ℂ) (H : Matrix n n ℂ) {m : ℕ}
    (P : Fin m → Matrix n n ℂ) : Prop where
  idem : ∀ j, P j * P j = P j
  orth : ∀ j k, j ≠ k → P j * P k = 0
  total : ∑ j, P j = 1
  adjoint : ∀ j, (P j)ᴴ * H = H * P j
  commutes : ∀ j g, P j * T g = T g * P j

/-- The weighted sector factor `∑ w_j P_j`. -/
def sectorFactor {m : ℕ} (P : Fin m → Matrix n n ℂ) (w : Fin m → ℝ) : Matrix n n ℂ :=
  ∑ j, (w j : ℂ) • P j

theorem sectorFactor_mul {T : Γ → Matrix n n ℂ} {H : Matrix n n ℂ} {m : ℕ}
    {P : Fin m → Matrix n n ℂ} (hP : IsSectorSystem T H P) (w v : Fin m → ℝ) :
    sectorFactor P w * sectorFactor P v = sectorFactor P (fun j => w j * v j) := by
  classical
  simp only [sectorFactor, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · push_cast
    rw [hP.idem k]
    ring_nf
  · intro j _ hjk
    rw [hP.orth k j (Ne.symm hjk)]
    simp
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem sectorFactor_one {T : Γ → Matrix n n ℂ} {H : Matrix n n ℂ} {m : ℕ}
    {P : Fin m → Matrix n n ℂ} (hP : IsSectorSystem T H P) :
    sectorFactor P (fun _ => 1) = 1 := by
  simp [sectorFactor, hP.total]

theorem isUnit_sectorFactor {T : Γ → Matrix n n ℂ} {H : Matrix n n ℂ} {m : ℕ}
    {P : Fin m → Matrix n n ℂ} (hP : IsSectorSystem T H P) {w : Fin m → ℝ}
    (hw : ∀ j, w j ≠ 0) : IsUnit (sectorFactor P w) := by
  have hinv : sectorFactor P w * sectorFactor P (fun j => (w j)⁻¹) = 1 := by
    rw [sectorFactor_mul hP,
      show (fun j => w j * (w j)⁻¹) = (fun _ : Fin m => (1 : ℝ)) from
        funext fun j => mul_inv_cancel₀ (hw j)]
    exact sectorFactor_one hP
  have hinv' : sectorFactor P (fun j => (w j)⁻¹) * sectorFactor P w = 1 := by
    rw [sectorFactor_mul hP,
      show (fun j => (w j)⁻¹ * w j) = (fun _ : Fin m => (1 : ℝ)) from
        funext fun j => inv_mul_cancel₀ (hw j)]
    exact sectorFactor_one hP
  exact ⟨⟨sectorFactor P w, sectorFactor P (fun j => (w j)⁻¹), hinv, hinv'⟩, rfl⟩

theorem mul_sectorFactor_eq {T : Γ → Matrix n n ℂ} {H : Matrix n n ℂ} {m : ℕ}
    {P : Fin m → Matrix n n ℂ} (hP : IsSectorSystem T H P) (w : Fin m → ℝ) :
    H * sectorFactor P w = ∑ j, (w j : ℂ) • ((P j)ᴴ * H * P j) := by
  simp only [sectorFactor, Finset.mul_sum, Matrix.mul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hj : (P j)ᴴ * H * P j = H * P j := by
    rw [hP.adjoint j, mul_assoc, hP.idem j]
  rw [hj]

theorem isHermitian_mul_sectorFactor {T : Γ → Matrix n n ℂ} {H : Matrix n n ℂ} {m : ℕ}
    {P : Fin m → Matrix n n ℂ} (hP : IsSectorSystem T H P) (hH : H.IsHermitian)
    (w : Fin m → ℝ) : (H * sectorFactor P w).IsHermitian := by
  rw [mul_sectorFactor_eq hP, Matrix.IsHermitian, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH]
  simp only [Matrix.mul_assoc, Complex.star_def, Complex.conj_ofReal]

omit [DecidableEq n] in
theorem dotProduct_sector_term {H : Matrix n n ℂ} (Q : Matrix n n ℂ) (c : ℂ) (x : n → ℂ) :
    star x ⬝ᵥ ((c • (Qᴴ * H * Q)) *ᵥ x) = c * (star (Q *ᵥ x) ⬝ᵥ (H *ᵥ (Q *ᵥ x))) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

/-- **Positive sector weights give invariant positive metrics.** -/
theorem posDef_mul_sectorFactor {T : Γ → Matrix n n ℂ} {H : Matrix n n ℂ} {m : ℕ}
    {P : Fin m → Matrix n n ℂ} (hP : IsSectorSystem T H P) (hH : H.PosDef)
    {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) : (H * sectorFactor P w).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (isHermitian_mul_sectorFactor hP hH.isHermitian w)
    fun x hx => ?_
  rw [mul_sectorFactor_eq hP, Matrix.sum_mulVec, dotProduct_sum]
  have hterm : ∀ j : Fin m,
      star x ⬝ᵥ (((w j : ℂ) • ((P j)ᴴ * H * P j)) *ᵥ x)
        = (w j : ℂ) * (star (P j *ᵥ x) ⬝ᵥ (H *ᵥ (P j *ᵥ x))) := fun j =>
    dotProduct_sector_term (H := H) (P j) _ x
  simp only [hterm]
  have hnonneg : ∀ j : Fin m, 0 ≤ (w j : ℂ) * (star (P j *ᵥ x) ⬝ᵥ (H *ᵥ (P j *ᵥ x))) := by
    intro j
    exact mul_nonneg (by exact_mod_cast (hw j).le)
      (hH.posSemidef.dotProduct_mulVec_nonneg _)
  have hexists : ∃ j : Fin m, P j *ᵥ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hx
    have : x = (∑ j, P j) *ᵥ x := by rw [hP.total, Matrix.one_mulVec]
    rw [Matrix.sum_mulVec] at this
    rw [this]
    exact Finset.sum_eq_zero fun j _ => hcon j
  obtain ⟨j₀, hj₀⟩ := hexists
  refine Finset.sum_pos' (fun j _ => hnonneg j) ⟨j₀, Finset.mem_univ j₀, ?_⟩
  exact mul_pos (by exact_mod_cast hw j₀) (hH.dotProduct_mulVec_pos hj₀)

/-- **The weighted sector family lies in the commutant cone.** -/
theorem isCommutantFactor_sectorFactor {T : Γ → Matrix n n ℂ} {H : Matrix n n ℂ} {m : ℕ}
    {P : Fin m → Matrix n n ℂ} (hP : IsSectorSystem T H P) (hH : IsInvariantMetric T H)
    {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) :
    IsCommutantFactor T H (sectorFactor P w) := by
  refine ⟨isUnit_sectorFactor hP (fun j => (hw j).ne'), fun g => ?_, ?_,
    posDef_mul_sectorFactor hP hH.posDef hw⟩
  · simp only [sectorFactor, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
    exact Finset.sum_congr rfl fun j _ => by rw [hP.commutes j g]
  · simp only [sectorFactor, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Finset.sum_mul,
      Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.conj_ofReal, hP.adjoint j]

/-- **Projective injectivity of the sector weights.**  Two weight vectors give proportional
invariant metrics exactly when they are proportional. -/
theorem sectorFactor_eq_smul_iff {T : Γ → Matrix n n ℂ} {H : Matrix n n ℂ} {m : ℕ}
    {P : Fin m → Matrix n n ℂ} (hP : IsSectorSystem T H P) (hne : ∀ j, P j ≠ 0)
    (w v : Fin m → ℝ) (c : ℝ) :
    sectorFactor P w = (c : ℂ) • sectorFactor P v ↔ ∀ j, w j = c * v j := by
  constructor
  · intro hEq j
    have hmul := congrArg (fun M => M * P j) hEq
    simp only [sectorFactor, Finset.sum_mul, Matrix.smul_mul, Matrix.smul_mul] at hmul
    rw [Finset.sum_eq_single j, Finset.sum_eq_single j] at hmul
    · rw [hP.idem j] at hmul
      have hcoe : ((w j : ℂ)) • P j = ((c * v j : ℝ) : ℂ) • P j := by
        rw [hmul]
        push_cast
        rw [smul_smul]
      have := sub_eq_zero.mpr hcoe
      rw [← sub_smul] at this
      rcases smul_eq_zero.mp this with h | h
      · have : ((w j : ℂ)) - ((c * v j : ℝ) : ℂ) = 0 := h
        have hr : (w j : ℂ) = ((c * v j : ℝ) : ℂ) := by linear_combination this
        exact_mod_cast hr
      · exact absurd h (hne j)
    · intro k _ hkj
      rw [hP.orth k j hkj]
      simp
    · intro hj
      exact absurd (Finset.mem_univ j) hj
    · intro k _ hkj
      rw [hP.orth k j hkj]
      simp
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · intro hw
    simp only [sectorFactor, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hw j]
    push_cast
    ring_nf

/-! ## The two-sector spectator -/

/-- A single `H`-orthogonal spectator projection generates a two-sector system. -/
theorem isSectorSystem_pair {T : Γ → Matrix n n ℂ} {H P : Matrix n n ℂ}
    (hidem : P * P = P) (hadj : Pᴴ * H = H * P) (hcomm : ∀ g, P * T g = T g * P) :
    IsSectorSystem T H ![P, 1 - P] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · simpa using hidem
    · show (1 - P) * (1 - P) = 1 - P
      rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, hidem]
      abel
  · intro j k hjk
    fin_cases j <;> fin_cases k <;> simp_all
    · show P * (1 - P) = 0
      rw [mul_sub, mul_one, hidem, sub_self]
    · show (1 - P) * P = 0
      rw [sub_mul, one_mul, hidem, sub_self]
  · rw [Fin.sum_univ_two]
    show P + (1 - P) = 1
    abel
  · intro j
    fin_cases j
    · simpa using hadj
    · show (1 - P)ᴴ * H = H * (1 - P)
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sub_mul, mul_sub, one_mul, mul_one,
        hadj]
  · intro j g
    fin_cases j
    · simpa using hcomm g
    · show (1 - P) * T g = T g * (1 - P)
      rw [sub_mul, mul_sub, one_mul, mul_one, hcomm g]

/-- **The spectator corollary.**  A nontrivial `H`-orthogonal history-invariant projection gives a
two-parameter family of invariant positive metrics, and distinct weight ratios give
non-proportional metrics. -/
theorem spectator_two_weight {T : Γ → Matrix n n ℂ} {H P : Matrix n n ℂ}
    (hH : IsInvariantMetric T H) (hidem : P * P = P) (hadj : Pᴴ * H = H * P)
    (hcomm : ∀ g, P * T g = T g * P) (hP0 : P ≠ 0) (hP1 : 1 - P ≠ 0)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsInvariantMetric T (H * sectorFactor ![P, 1 - P] ![a, b]) ∧
      (a ≠ b → ∀ c : ℝ, sectorFactor ![P, 1 - P] ![a, b] ≠ (c : ℂ) • (1 : Matrix n n ℂ)) := by
  have hsys := isSectorSystem_pair (T := T) (H := H) hidem hadj hcomm
  have hne : ∀ j : Fin 2, (![P, 1 - P] : Fin 2 → Matrix n n ℂ) j ≠ 0 := by
    intro j
    fin_cases j
    · simpa using hP0
    · simpa using hP1
  have hw : ∀ j : Fin 2, 0 < (![a, b] : Fin 2 → ℝ) j := by
    intro j
    fin_cases j
    · simpa using ha
    · simpa using hb
  refine ⟨isInvariantMetric_mul hH (isCommutantFactor_sectorFactor hsys hH hw), ?_⟩
  intro hab c hcon
  have hone : sectorFactor ![P, 1 - P] ![(1 : ℝ), 1] = 1 := by
    have : (![(1 : ℝ), 1] : Fin 2 → ℝ) = fun _ => 1 := by
      funext j; fin_cases j <;> simp
    rw [this]
    exact sectorFactor_one hsys
  have hcon' : sectorFactor ![P, 1 - P] ![a, b]
      = (c : ℂ) • sectorFactor ![P, 1 - P] ![(1 : ℝ), 1] := by
    rw [hone]
    exact hcon
  have := (sectorFactor_eq_smul_iff hsys hne ![a, b] ![(1 : ℝ), 1] c).mp hcon'
  have h0 := this 0
  have h1 := this 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at h0 h1
  exact hab (h0.trans h1.symm)

end GaloisForLFunctions.HTGeometry

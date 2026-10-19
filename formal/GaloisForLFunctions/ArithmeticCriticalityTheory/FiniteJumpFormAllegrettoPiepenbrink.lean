import GaloisForLFunctions.ArithmeticCriticalityTheory.GroundStateRepresentationAlgebra
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Allegretto–Piepenbrink for a finite jump form

For a finite symmetric nonnegative kernel `K` and an arbitrary potential `ρ`, the Schrödinger form
`E_K(v) − Σ ρ_i v_i²` is the quadratic form of the symmetric matrix
`A = diag(Σ_k K_{ik} − ρ_i) − K`, a matrix with nonpositive off-diagonal entries. The hard direction
of the Allegretto–Piepenbrink theorem is proved here: if the form is nonnegative, a nonnegative
nonzero `ω` with `(L_K ω)_i ≥ ρ_i ω_i` exists. The proof takes a minimiser of the Rayleigh quotient on
the unit sphere, replaces it by its absolute value (which does not increase the form because the
off-diagonal entries are nonpositive), and uses the Euler–Lagrange equation of a minimiser, so the
absolute value is an eigenvector for the lowest eigenvalue, which is nonnegative. The zero set of the
supersolution so obtained is closed under neighbours; under connectivity the supersolution is
strictly positive.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Schrödinger matrix `diag(Σ_k K_{ik} − ρ_i) − K` of the finite jump form with potential `ρ`. -/
def schroedingerMatrix (K : ι → ι → ℝ) (ρ : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => (if i = j then (∑ k, K i k) - ρ i else 0) - K i j

theorem schroedingerMatrix_apply (K : ι → ι → ℝ) (ρ : ι → ℝ) (i j : ι) :
    schroedingerMatrix K ρ i j = (if i = j then (∑ k, K i k) - ρ i else 0) - K i j := by
  simp [schroedingerMatrix]

/-- `(A ω)_i = (L_K ω)_i − ρ_i ω_i`. -/
theorem schroedingerMatrix_mulVec (K : ι → ι → ℝ) (ρ ω : ι → ℝ) (i : ι) :
    (schroedingerMatrix K ρ).mulVec ω i = generator K ω i - ρ i * ω i := by
  unfold generator
  simp only [Matrix.mulVec, dotProduct, schroedingerMatrix_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_sub, Finset.sum_mul]
  ring

omit [DecidableEq ι] in
/-- The jump energy of a symmetric kernel as a diagonal minus an off-diagonal sum. -/
theorem jumpEnergy_eq_sum {K : ι → ι → ℝ} (hK : ∀ i j, K i j = K j i) (v : ι → ℝ) :
    jumpEnergy K v = ∑ i, ∑ j, K i j * v i ^ 2 - ∑ i, ∑ j, K i j * v i * v j := by
  unfold jumpEnergy
  have h1 : ∀ i j, K i j * (v i - v j) ^ 2 =
      K i j * v i ^ 2 + K j i * v j ^ 2 - 2 * (K i j * v i * v j) := by
    intro i j
    rw [hK j i]
    ring
  simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : ∑ i, ∑ j, K j i * v j ^ 2 = ∑ i, ∑ j, K i j * v i ^ 2 := Finset.sum_comm
  rw [h2]
  ring

/-- The quadratic form of the Schrödinger matrix is the jump energy minus the potential. -/
theorem dotProduct_schroedingerMatrix_mulVec {K : ι → ι → ℝ} (hK : ∀ i j, K i j = K j i)
    (ρ v : ι → ℝ) :
    v ⬝ᵥ (schroedingerMatrix K ρ).mulVec v = jumpEnergy K v - ∑ i, ρ i * v i ^ 2 := by
  have e1 : ∑ i, v i * (generator K v i - ρ i * v i) =
      ∑ i, ∑ j, K i j * v i ^ 2 - ∑ i, ∑ j, K i j * v i * v j - ∑ i, ρ i * v i ^ 2 := by
    unfold generator
    simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    congr 1
    · congr 1
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  simp only [dotProduct, schroedingerMatrix_mulVec]
  rw [e1, jumpEnergy_eq_sum hK]

omit [DecidableEq ι] in
/-- Replacing a vector by its absolute value does not increase a Schrödinger form with nonnegative
kernel: this is where the sign of the off-diagonal entries enters. -/
theorem quadraticForm_abs_le {K : ι → ι → ℝ} (hK0 : ∀ i j, 0 ≤ K i j) (ρ v : ι → ℝ) :
    jumpEnergy K (fun i => |v i|) - ∑ i, ρ i * |v i| ^ 2 ≤
      jumpEnergy K v - ∑ i, ρ i * v i ^ 2 := by
  have hρ : ∑ i, ρ i * |v i| ^ 2 = ∑ i, ρ i * v i ^ 2 := by simp [sq_abs]
  rw [hρ]
  have hE : jumpEnergy K (fun i => |v i|) ≤ jumpEnergy K v := by
    unfold jumpEnergy
    refine mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_) (by norm_num)
    refine mul_le_mul_of_nonneg_left ?_ (hK0 i j)
    have h1 : |v i| - |v j| ≤ |v i - v j| := abs_sub_abs_le_abs_sub (v i) (v j)
    have h2 : -|v i - v j| ≤ |v i| - |v j| := by
      have h := abs_sub_abs_le_abs_sub (v j) (v i)
      rw [abs_sub_comm] at h
      linarith
    calc (|v i| - |v j|) ^ 2 ≤ |v i - v j| ^ 2 := sq_le_sq' h2 h1
      _ = (v i - v j) ^ 2 := sq_abs _
  linarith

/-- **Allegretto–Piepenbrink, hard direction (finite).** If the Schrödinger form of a symmetric
nonnegative kernel is nonnegative, there is a nonnegative nonzero supersolution `ρ_i ω_i ≤ (L_K ω)_i`
whose zero set is closed under neighbours. -/
theorem exists_nonneg_supersolution_of_nonneg [Nonempty ι] {K : ι → ι → ℝ}
    (hK : ∀ i j, K i j = K j i) (hK0 : ∀ i j, 0 ≤ K i j) (ρ : ι → ℝ)
    (hQ : ∀ v : ι → ℝ, ∑ i, ρ i * v i ^ 2 ≤ jumpEnergy K v) :
    ∃ ω : ι → ℝ, (∀ i, 0 ≤ ω i) ∧ ω ≠ 0 ∧ (∀ i, ρ i * ω i ≤ generator K ω i) ∧
      (∀ i, ω i = 0 → ∀ j, K i j * ω j = 0) := by
  classical
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (schroedingerMatrix K ρ))
  have hTapp : ∀ x : EuclideanSpace ℝ ι,
      (T x).ofLp = (schroedingerMatrix K ρ).mulVec x.ofLp := by
    intro x
    simp [T, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  have hherm : (schroedingerMatrix K ρ).IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    rw [star_trivial, schroedingerMatrix_apply, schroedingerMatrix_apply, hK j i]
    by_cases h : i = j
    · subst h
      rfl
    · rw [if_neg (Ne.symm h), if_neg h]
  have hT : IsSelfAdjoint T := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    have hcoe : ((T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
        EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) =
        Matrix.toEuclideanLin (schroedingerMatrix K ρ) :=
      LinearMap.coe_toContinuousLinearMap _
    rw [hcoe]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hherm
  have hray : ∀ x : EuclideanSpace ℝ ι,
      T.reApplyInnerSelf x = jumpEnergy K x.ofLp - ∑ i, ρ i * x.ofLp i ^ 2 := by
    intro x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, EuclideanSpace.inner_eq_star_dotProduct, hTapp,
      star_trivial, RCLike.re_to_real, dotProduct_schroedingerMatrix_mulVec hK]
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hS : (Metric.sphere (0 : EuclideanSpace ℝ ι) 1).Nonempty :=
    ⟨EuclideanSpace.single i₀ 1, by simp⟩
  obtain ⟨x₀, hx₀S, hx₀min⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ ι) 1).exists_isMinOn hS
    T.reApplyInnerSelf_continuous.continuousOn
  have hx₀norm : ‖x₀‖ = 1 := mem_sphere_zero_iff_norm.mp hx₀S
  let y : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => |x₀.ofLp i|)
  have hy_ofLp : y.ofLp = fun i => |x₀.ofLp i| := rfl
  have hynorm : ‖y‖ = 1 := by
    rw [EuclideanSpace.norm_eq, hy_ofLp]
    rw [EuclideanSpace.norm_eq] at hx₀norm
    simpa [Real.norm_eq_abs, abs_abs] using hx₀norm
  have hyS : y ∈ Metric.sphere (0 : EuclideanSpace ℝ ι) 1 := mem_sphere_zero_iff_norm.mpr hynorm
  have hymin : IsMinOn T.reApplyInnerSelf (Metric.sphere (0 : EuclideanSpace ℝ ι) 1) y := by
    rw [isMinOn_iff] at hx₀min ⊢
    intro z hz
    have h1 := hx₀min z hz
    have h2 : T.reApplyInnerSelf y ≤ T.reApplyInnerSelf x₀ := by
      rw [hray, hray, hy_ofLp]
      exact quadraticForm_abs_le hK0 ρ x₀.ofLp
    exact le_trans h2 h1
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hynorm
    exact zero_ne_one hynorm
  have hmin' : IsMinOn T.reApplyInnerSelf (Metric.sphere (0 : EuclideanSpace ℝ ι) ‖y‖) y := by
    rwa [hynorm]
  obtain ⟨μ, hTy⟩ : ∃ μ : ℝ, T y = μ • y := ⟨_, (hT.hasEigenvector_of_isMinOn hy0 hmin').apply_eq_smul⟩
  have hAy : ∀ i, (schroedingerMatrix K ρ).mulVec y.ofLp i = μ * y.ofLp i := by
    intro i
    have h := congrArg (fun z : EuclideanSpace ℝ ι => z.ofLp i) hTy
    simpa [hTapp] using h
  have hynn : ∀ i, 0 ≤ y.ofLp i := fun i => by
    rw [hy_ofLp]
    exact abs_nonneg _
  have hμ : 0 ≤ μ := by
    have h1 : T.reApplyInnerSelf y = μ := by
      rw [ContinuousLinearMap.reApplyInnerSelf_apply, hTy, inner_smul_left,
        real_inner_self_eq_norm_sq, hynorm]
      simp
    have h2 : 0 ≤ T.reApplyInnerSelf y := by
      rw [hray]
      linarith [hQ y.ofLp]
    linarith
  refine ⟨y.ofLp, hynn, ?_, ?_, ?_⟩
  · intro h
    apply hy0
    have : y = WithLp.toLp 2 y.ofLp := rfl
    rw [this, h]
    rfl
  · intro i
    have h := hAy i
    rw [schroedingerMatrix_mulVec] at h
    have := mul_nonneg hμ (hynn i)
    linarith
  · intro i hi j
    have h := hAy i
    rw [schroedingerMatrix_mulVec, hi] at h
    unfold generator at h
    simp only [hi, zero_sub, mul_neg, Finset.sum_neg_distrib, mul_zero, sub_zero, neg_eq_zero] at h
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (hK0 i j) (hynn j)).mp h j
      (Finset.mem_univ j)

omit [Fintype ι] [DecidableEq ι] in
/-- A nonnegative nonzero vector whose zero set is closed under neighbours is strictly positive on a
kernel-connected index set. -/
theorem pos_of_connected {K : ι → ι → ℝ} {ω : ι → ℝ} (hω : ∀ i, 0 ≤ ω i) (hne : ω ≠ 0)
    (hclosed : ∀ i, ω i = 0 → ∀ j, K i j * ω j = 0)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => 0 < K a b) i j) : ∀ i, 0 < ω i := by
  intro i
  by_contra hcontra
  have hi : ω i = 0 := le_antisymm (not_lt.mp hcontra) (hω i)
  apply hne
  funext j
  have hprop : ∀ j, Relation.ReflTransGen (fun a b => 0 < K a b) i j → ω j = 0 := by
    intro j hj
    induction hj with
    | refl => exact hi
    | @tail b c _ hbc ih =>
      exact (mul_eq_zero.mp (hclosed b ih c)).resolve_left hbc.ne'
  exact hprop j (hconn i j)

/-- **Finite Allegretto–Piepenbrink equivalence.** On a connected finite kernel the Schrödinger form
is nonnegative if and only if a strictly positive supersolution exists. -/
theorem nonneg_iff_exists_pos_supersolution [Nonempty ι] {K : ι → ι → ℝ}
    (hK : ∀ i j, K i j = K j i) (hK0 : ∀ i j, 0 ≤ K i j)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => 0 < K a b) i j) (ρ : ι → ℝ) :
    (∀ v : ι → ℝ, ∑ i, ρ i * v i ^ 2 ≤ jumpEnergy K v) ↔
      ∃ ω : ι → ℝ, (∀ i, 0 < ω i) ∧ ∀ i, ρ i * ω i ≤ generator K ω i := by
  constructor
  · intro hQ
    obtain ⟨ω, hω, hne, hsuper, hclosed⟩ := exists_nonneg_supersolution_of_nonneg hK hK0 ρ hQ
    exact ⟨ω, pos_of_connected hω hne hclosed hconn, hsuper⟩
  · rintro ⟨ω, hω, hsuper⟩ v
    exact sum_potential_le_jumpEnergy_of_supersolution hK hK0 hω hsuper v

end GaloisForLFunctions.ArithmeticCriticalityTheory

end

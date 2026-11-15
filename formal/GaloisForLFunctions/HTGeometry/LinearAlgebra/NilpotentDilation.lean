import GaloisForLFunctions.HTGeometry.LinearAlgebra.RealIntertwinerDescent
import GaloisForLFunctions.HTGeometry.LinearAlgebra.NilpotentEuler
import GaloisForLFunctions.HTGeometry.LinearAlgebra.ScalingNilpotence
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv

/-!
# Exact dilation boundary for finite linear operators

Every nilpotent real or complex matrix is similar to each of its nonzero scalar
multiples. An Euler operator integrates to conjugation by its exponential.
Complex logarithms give all complex scales; simultaneous real intertwiner
descent supplies every real scale, including negative ones.

Conversely, finite-dimensional scaling rigidity forces a generator admitting a
nonunit positive scale to be nilpotent. Thus similarity to twice an operator is
an exact test for nilpotence. No inner product or Jordan basis is needed.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open NormedSpace

section Algebra
variable {K A : Type*} [RCLike K] [NormedRing A] [NormedAlgebra K A] [CompleteSpace A]

/-- The algebra exponential as a unit, with inverse given by the negative exponential. -/
def clockExpUnit (H : A) : Aˣ := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ K A
  refine ⟨exp H, exp (-H), ?_, ?_⟩
  · rw [← exp_add_of_commute (Commute.refl H).neg_right, add_neg_cancel, exp_zero]
  · rw [← exp_add_of_commute (Commute.refl H).neg_left, neg_add_cancel, exp_zero]

/-- The value of the exponential unit. -/
theorem clockExpUnit_val (H : A) : (clockExpUnit (K := K) H : A) = exp H := rfl

/-- The inverse of the exponential unit. -/
theorem clockExpUnit_inv_val (H : A) : (clockExpUnit (K := K) H).inv = exp (-H) := rfl

/-- Conjugation by an algebra unit. -/
def clockInnerAlgEquiv (u : Aˣ) : A ≃ₐ[K] A :=
  MulSemiringAction.toAlgEquiv K A (ConjAct.toConjAct u)

omit [CompleteSpace A] in
/-- Inner conjugation acts by multiplication on both sides. -/
theorem clockInnerAlgEquiv_apply (u : Aˣ) (N : A) :
    clockInnerAlgEquiv (K := K) u N = u.val * N * u.inv := rfl

/-- An Euler commutator integrates to exact exponential rescaling. -/
theorem clockEuler_exponential (H N : A) (hHN : H * N - N * H = N) (z : K) :
    clockInnerAlgEquiv (K := K) (clockExpUnit (K := K) (z • H)) N = exp z • N := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ K A
  have he : SemiconjBy N (z • H + z • (1 : A)) (z • H) := by
    change N * (z • H + z • (1 : A)) = (z • H) * N
    rw [mul_add, mul_smul_comm, mul_smul_comm, smul_mul_assoc, mul_one, ← smul_add]
    apply congrArg (fun X : A => z • X)
    calc
      N * H + N = N + N * H := add_comm _ _
      _ = H * N := (sub_eq_iff_eq_add.mp hHN).symm
  have hs : exp (z • (1 : A)) = exp z • (1 : A) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← algebraMap_exp_comm z,
      Algebra.algebraMap_eq_smul_one]
  have hcomm : Commute (z • H) (z • (1 : A)) :=
    ((Commute.one_right H).smul_left z).smul_right z
  have hexp := he.exp_right
  change N * exp (z • H + z • (1 : A)) = exp (z • H) * N at hexp
  rw [exp_add_of_commute hcomm, hs, mul_smul_comm, mul_one, mul_smul_comm] at hexp
  rw [clockInnerAlgEquiv_apply, clockExpUnit_val, clockExpUnit_inv_val, ← hexp]
  rw [smul_mul_assoc, mul_assoc,
    ← exp_add_of_commute (Commute.refl (z • H)).neg_right, add_neg_cancel, exp_zero, mul_one]

end Algebra
section Matrices
open scoped Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every nonzero complex scalar multiple of a nilpotent matrix is similar to it. -/
theorem exists_complex_matrix_unit_scale (N : Matrix ι ι ℂ) (hN : IsNilpotent N)
    (q : ℂ) (hq : q ≠ 0) :
    ∃ u : (Matrix ι ι ℂ)ˣ, u.val * N * u.inv = q • N := by
  obtain ⟨H, hH⟩ := exists_matrixEuler_of_isNilpotent N hN
  refine ⟨clockExpUnit (K := ℂ) (Complex.log q • H), ?_⟩
  change clockInnerAlgEquiv (K := ℂ) (clockExpUnit (K := ℂ) (Complex.log q • H)) N = _
  rw [clockEuler_exponential H N hH, ← Complex.exp_eq_exp_ℂ, Complex.exp_log hq]

/-- Every nonzero complex scale is realized by an algebra automorphism. -/
theorem exists_complex_matrix_algEquiv_scale (N : Matrix ι ι ℂ) (hN : IsNilpotent N)
    (q : ℂ) (hq : q ≠ 0) :
    ∃ e : Matrix ι ι ℂ ≃ₐ[ℂ] Matrix ι ι ℂ, e N = q • N := by
  obtain ⟨u, hu⟩ := exists_complex_matrix_unit_scale N hN q hq
  exact ⟨clockInnerAlgEquiv u, hu⟩

/-- Positive complex-matrix scaling is possible exactly at scale one or for a nilpotent matrix. -/
theorem exists_complex_matrix_positive_scale_iff (N : Matrix ι ι ℂ)
    (q : ℝ) (hq : 0 < q) :
    (∃ e : Matrix ι ι ℂ ≃ₐ[ℂ] Matrix ι ι ℂ, e N = (q : ℂ) • N) ↔
      q = 1 ∨ IsNilpotent N := by
  constructor
  · rintro ⟨e, he⟩
    by_cases hq1 : q = 1
    · exact Or.inl hq1
    · right
      apply isNilpotent_of_algHom_scale e.toAlgHom N (q : ℂ) _ he
      intro m n h
      apply pow_right_injective₀ hq hq1
      exact Complex.ofReal_injective (by simpa only [Complex.ofReal_pow] using h)
  · rintro (rfl | hN)
    · exact ⟨AlgEquiv.refl, by simp only [Complex.ofReal_one, one_smul]; rfl⟩
    · exact exists_complex_matrix_algEquiv_scale N hN (q : ℂ)
        (Complex.ofReal_ne_zero.mpr hq.ne')

/-- Complex similarity descends to realize every nonzero real scale of a nilpotent matrix. -/
theorem exists_real_matrix_unit_scale (N : Matrix ι ι ℝ) (hN : IsNilpotent N)
    (q : ℝ) (hq : q ≠ 0) :
    ∃ u : (Matrix ι ι ℝ)ˣ, u.val * N * u.inv = q • N := by
  let φ : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix
  have hn : IsNilpotent (φ N) := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by rw [← map_pow, hk, map_zero]⟩
  obtain ⟨u, hu⟩ := exists_complex_matrix_unit_scale (φ N) hn (q : ℂ)
    (Complex.ofReal_ne_zero.mpr hq)
  have he : u.val * N.map Complex.ofReal = (q • N).map Complex.ofReal * u.val := by
    have hh := congrArg (fun M => M * u.val) hu
    rw [mul_assoc, u.inv_val, mul_one] at hh
    have hs : (q • N).map Complex.ofReal = (q : ℂ) • φ N := by
      ext i j
      change ((q * N i j : ℝ) : ℂ) = (q : ℂ) * (N i j : ℂ)
      exact Complex.ofReal_mul q (N i j)
    rw [hs]
    exact hh
  obtain ⟨D, hD, hd⟩ := exists_real_simultaneous_intertwiner
    (fun _ : Unit => N) (fun _ : Unit => q • N) u.val u.isUnit (fun _ => he)
  refine ⟨hD.unit, ?_⟩
  rw [hD.unit_spec, hd (), mul_assoc]
  change (q • N) * ((hD.unit : Matrix ι ι ℝ) * hD.unit.inv) = q • N
  rw [hD.unit.val_inv, mul_one]

/-- Every nonzero real scale of a nilpotent matrix is realized by an algebra automorphism. -/
theorem exists_real_matrix_algEquiv_scale (N : Matrix ι ι ℝ) (hN : IsNilpotent N)
    (q : ℝ) (hq : q ≠ 0) :
    ∃ e : Matrix ι ι ℝ ≃ₐ[ℝ] Matrix ι ι ℝ, e N = q • N := by
  obtain ⟨u, hu⟩ := exists_real_matrix_unit_scale N hN q hq
  exact ⟨clockInnerAlgEquiv u, hu⟩

/-- Positive real-matrix scaling is possible exactly at scale one or for a nilpotent matrix. -/
theorem exists_real_matrix_positive_scale_iff (N : Matrix ι ι ℝ) (q : ℝ) (hq : 0 < q) :
    (∃ e : Matrix ι ι ℝ ≃ₐ[ℝ] Matrix ι ι ℝ, e N = q • N) ↔ q = 1 ∨ IsNilpotent N := by
  constructor
  · rintro ⟨e, he⟩
    exact real_algHom_scale_eq_one_or_nilpotent e.toAlgHom N q hq he
  · rintro (rfl | hn)
    · exact ⟨AlgEquiv.refl, by simp only [one_smul]; rfl⟩
    · exact exists_real_matrix_algEquiv_scale N hn q hq.ne'

end Matrices
section FiniteEnd
open scoped Matrix.Norms.Frobenius
variable {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A basis transfers nilpotent matrix dilation to every finite-dimensional endomorphism. -/
theorem exists_end_exponential_scale (N : Module.End K V) (hN : IsNilpotent N) (z : K) :
    ∃ T : V ≃ₗ[K] V, T.conj N = exp z • N := by
  let β : Module.End K V ≃ₐ[K]
      Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K :=
    LinearMap.toMatrixAlgEquiv (Module.finBasis K V)
  have hβ : IsNilpotent (β N) := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by rw [← map_pow, hk, map_zero]⟩
  obtain ⟨H, hH⟩ := exists_matrixEuler_of_isNilpotent (β N) hβ
  let e : Module.End K V ≃ₐ[K] Module.End K V :=
    (β.trans (clockInnerAlgEquiv (K := K) (clockExpUnit (K := K) (z • H)))).trans β.symm
  have he : e N = exp z • N := by
    change β.symm (clockInnerAlgEquiv (K := K) (clockExpUnit (K := K) (z • H)) (β N)) = _
    rw [clockEuler_exponential H (β N) hH, map_smul, β.symm_apply_apply]
  obtain ⟨T, hT⟩ := e.eq_linearEquivConjAlgEquiv
  rw [hT] at he
  exact ⟨T, by simpa only [LinearEquiv.conjAlgEquiv_apply,
    LinearEquiv.conj_apply, LinearMap.comp_assoc] using he⟩

end FiniteEnd

section ComplexEnd
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A finite complex nilpotent endomorphism admits every nonzero complex dilation. -/
theorem exists_complex_end_scale (N : Module.End ℂ V) (hN : IsNilpotent N)
    (q : ℂ) (hq : q ≠ 0) : ∃ T : V ≃ₗ[ℂ] V, T.conj N = q • N := by
  obtain ⟨T, hT⟩ := exists_end_exponential_scale N hN (Complex.log q)
  exact ⟨T, by simpa only [← Complex.exp_eq_exp_ℂ, Complex.exp_log hq] using hT⟩

/-- The exact positive-scaling boundary for finite complex endomorphisms. -/
theorem exists_complex_end_positive_scale_iff (N : Module.End ℂ V) (q : ℝ) (hq : 0 < q) :
    (∃ T : V ≃ₗ[ℂ] V, T.conj N = (q : ℂ) • N) ↔ q = 1 ∨ IsNilpotent N := by
  constructor
  · rintro ⟨T, hT⟩
    exact complex_conj_scale_eq_one_or_nilpotent T N q hq hT
  · rintro (rfl | hN)
    · refine ⟨LinearEquiv.refl ℂ V, ?_⟩
      apply LinearMap.ext
      intro x
      simp
    · exact exists_complex_end_scale N hN (q : ℂ) (Complex.ofReal_ne_zero.mpr hq.ne')

end ComplexEnd
section RealEnd
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- A finite real nilpotent endomorphism admits every nonzero real dilation. -/
theorem exists_real_end_scale (N : Module.End ℝ V) (hN : IsNilpotent N)
    (q : ℝ) (hq : q ≠ 0) : ∃ T : V ≃ₗ[ℝ] V, T.conj N = q • N := by
  let β : Module.End ℝ V ≃ₐ[ℝ]
      Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
    LinearMap.toMatrixAlgEquiv (Module.finBasis ℝ V)
  have hβ : IsNilpotent (β N) := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by rw [← map_pow, hk, map_zero]⟩
  obtain ⟨f, hf⟩ := exists_real_matrix_algEquiv_scale (β N) hβ q hq
  let e : Module.End ℝ V ≃ₐ[ℝ] Module.End ℝ V := (β.trans f).trans β.symm
  have he : e N = q • N := by
    change β.symm (f (β N)) = _
    rw [hf, map_smul, β.symm_apply_apply]
  obtain ⟨T, hT⟩ := e.eq_linearEquivConjAlgEquiv
  rw [hT] at he
  exact ⟨T, by simpa only [LinearEquiv.conjAlgEquiv_apply,
    LinearEquiv.conj_apply, LinearMap.comp_assoc] using he⟩

/-- The exact positive-scaling boundary for finite real endomorphisms. -/
theorem exists_real_end_positive_scale_iff (N : Module.End ℝ V) (q : ℝ) (hq : 0 < q) :
    (∃ T : V ≃ₗ[ℝ] V, T.conj N = q • N) ↔ q = 1 ∨ IsNilpotent N := by
  constructor
  · rintro ⟨T, hT⟩
    exact real_algHom_scale_eq_one_or_nilpotent (T.conjAlgEquiv ℝ).toAlgHom N q hq hT
  · rintro (rfl | hN)
    · refine ⟨LinearEquiv.refl ℝ V, ?_⟩
      apply LinearMap.ext
      intro x
      simp
    · exact exists_real_end_scale N hN q hq.ne'

/-- A finite real endomorphism is nilpotent exactly when it is similar to twice itself. -/
theorem real_isNilpotent_iff_conj_double (N : Module.End ℝ V) :
    IsNilpotent N ↔ ∃ T : V ≃ₗ[ℝ] V, T.conj N = (2 : ℝ) • N := by
  rw [exists_real_end_positive_scale_iff N 2 (by norm_num)]
  simp only [show (2 : ℝ) ≠ 1 by norm_num, false_or]

end RealEnd

/-- A finite complex endomorphism is nilpotent exactly when it is similar to twice itself. -/
theorem complex_isNilpotent_iff_conj_double {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (N : Module.End ℂ V) :
    IsNilpotent N ↔ ∃ T : V ≃ₗ[ℂ] V, T.conj N = (2 : ℂ) • N := by
  have h := exists_complex_end_positive_scale_iff N 2 (by norm_num)
  simpa only [Complex.ofReal_ofNat, show (2 : ℝ) ≠ 1 by norm_num, false_or] using h.symm

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.clockEuler_exponential
#print axioms GaloisForLFunctions.HTGeometry.exists_complex_matrix_unit_scale
#print axioms GaloisForLFunctions.HTGeometry.exists_real_matrix_unit_scale
#print axioms GaloisForLFunctions.HTGeometry.exists_complex_end_scale
#print axioms GaloisForLFunctions.HTGeometry.exists_real_end_scale
#print axioms GaloisForLFunctions.HTGeometry.real_isNilpotent_iff_conj_double
#print axioms GaloisForLFunctions.HTGeometry.complex_isNilpotent_iff_conj_double

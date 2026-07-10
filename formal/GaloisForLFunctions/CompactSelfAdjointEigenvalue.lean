/-
# Norm-attaining eigenvalues of compact self-adjoint operators

A nonzero compact self-adjoint operator on a complex Hilbert space has a real eigenvalue of
absolute value equal to its operator norm, with a unit eigenvector: the spectral radius of a
self-adjoint operator is its norm, the spectral radius of an element of a complex Banach algebra
is attained on the spectrum, and every nonzero spectral point of a compact operator is an
eigenvalue (the Fredholm alternative).

The second half sets up the orthogonal-complement step used to exhaust the spectrum: given
finitely many eigenvectors, the supremum `orthSup` of `‖S y‖` over unit vectors orthogonal to
them is realized as an eigenvalue of `S` with an eigenvector orthogonal to all of them — the
restriction of `S` to the orthogonal complement of the span is again compact and self-adjoint,
and its norm is exactly `orthSup`.

Proved here:
* `exists_unit_eigenvector_norm` — a compact self-adjoint `S ≠ 0` has a unit eigenvector with
  real eigenvalue `μ`, `|μ| = ‖S‖`.
* `mem_orthogonal_span_iff` — membership in `(span s)ᗮ` is orthogonality to the generators.
* `orthSup` with `orthSup_nonneg`, `le_orthSup`, `orthSup_le`, `orthSup_le_opNorm`,
  `norm_le_orthSup_mul_norm`, `orthSup_antitone` — the constrained operator norm over the
  orthogonal complement of finitely many vectors.
* `exists_eigenvector_orthSup` — the exhaustion step: if the previous vectors are eigenvectors of
  a positive compact self-adjoint `S` and `orthSup ≠ 0`, then `orthSup` is an eigenvalue with a
  unit eigenvector orthogonal to all previous ones.
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.InnerProductSpace.Adjoint

open scoped InnerProductSpace ComplexConjugate

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Norm-attaining eigenvalue.**  A nonzero compact self-adjoint operator on a complex Hilbert
space has a real eigenvalue of absolute value `‖S‖` with a unit eigenvector: combine
`spectralRadius = ‖S‖` (self-adjointness), attainment of the spectral radius on the spectrum
(Gelfand), and the Fredholm alternative turning the nonzero spectral point into an eigenvalue. -/
theorem exists_unit_eigenvector_norm {S : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) (hS : S ≠ 0) :
    ∃ (μ : ℝ) (x : H), |μ| = ‖S‖ ∧ ‖x‖ = 1 ∧ S x = (μ : ℂ) • x := by
  haveI : Nontrivial (H →L[ℂ] H) := ⟨S, 0, hS⟩
  obtain ⟨k, hk_mem, hk_norm⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty S)
  rw [S.spectralRadius_eq_nnnorm hsym.isSelfAdjoint] at hk_norm
  have hk_norm' : ‖k‖ = ‖S‖ := by
    have h2 : ‖k‖₊ = ‖S‖₊ := ENNReal.coe_inj.mp hk_norm
    exact congrArg NNReal.toReal h2
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, norm_zero] at hk_norm'
    exact hS (by rwa [eq_comm, norm_eq_zero] at hk_norm')
  have heig : Module.End.HasEigenvalue (↑S : Module.End ℂ H) k :=
    (IsCompactOperator.hasEigenvalue_iff_mem_spectrum hcpt hk0).mpr hk_mem
  have hreal : (starRingEnd ℂ) k = k := hsym.conj_eigenvalue_eq_self heig
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  refine ⟨RCLike.re k, (‖v‖⁻¹ : ℂ) • v, ?_, norm_smul_inv_norm hv0, ?_⟩
  · have hk_re : ((RCLike.re k : ℝ) : ℂ) = k := RCLike.conj_eq_iff_re.mp hreal
    calc |RCLike.re k| = ‖((RCLike.re k : ℝ) : ℂ)‖ := (RCLike.norm_ofReal _).symm
      _ = ‖k‖ := by rw [hk_re]
      _ = ‖S‖ := hk_norm'
  · have happ : S v = k • v := hv.apply_eq_smul
    have hk_re : ((RCLike.re k : ℝ) : ℂ) = k := RCLike.conj_eq_iff_re.mp hreal
    rw [map_smul, happ, hk_re, smul_comm]

omit [CompleteSpace H] in
/-- Membership in the orthogonal complement of a span is orthogonality to the generators. -/
theorem _root_.Submodule.mem_orthogonal_span_iff {s : Set H} {x : H} :
    x ∈ (Submodule.span ℂ s)ᗮ ↔ ∀ u ∈ s, inner ℂ u x = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · exact fun h u hu => h u (Submodule.subset_span hu)
  · intro h u hu
    have hker : Submodule.span ℂ s ≤ LinearMap.ker (innerSL ℂ x).toLinearMap := by
      rw [Submodule.span_le]
      intro w hw
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        innerSL_apply_apply]
      rw [← inner_conj_symm, h w hw, map_zero]
    have hx := hker hu
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply] at hx
    rw [← inner_conj_symm, hx, map_zero]

/-- The constrained operator norm: the supremum of `‖S y‖` over vectors of norm at most one that
are orthogonal to the first `n` members of the family `v`. -/
noncomputable def orthSup (S : H →L[ℂ] H) (v : ℕ → H) (n : ℕ) : ℝ :=
  sSup ((fun y => ‖S y‖) '' {y : H | ‖y‖ ≤ 1 ∧ ∀ m < n, inner ℂ (v m) y = 0})

section OrthSup

variable (S : H →L[ℂ] H) (v : ℕ → H) (n : ℕ)

omit [CompleteSpace H] in
theorem orthSup_set_nonempty :
    ((fun y => ‖S y‖) '' {y : H | ‖y‖ ≤ 1 ∧ ∀ m < n, inner ℂ (v m) y = 0}).Nonempty :=
  ⟨‖S 0‖, 0, ⟨by simp, fun m _ => inner_zero_right _⟩, rfl⟩

omit [CompleteSpace H] in
theorem orthSup_set_bddAbove :
    BddAbove ((fun y => ‖S y‖) '' {y : H | ‖y‖ ≤ 1 ∧ ∀ m < n, inner ℂ (v m) y = 0}) := by
  refine ⟨‖S‖, ?_⟩
  rintro r ⟨y, ⟨hy1, -⟩, rfl⟩
  calc ‖S y‖ ≤ ‖S‖ * ‖y‖ := S.le_opNorm y
    _ ≤ ‖S‖ * 1 := by gcongr
    _ = ‖S‖ := mul_one _

omit [CompleteSpace H] in
theorem orthSup_nonneg : 0 ≤ orthSup S v n := by
  have h0 : ‖S 0‖ ≤ orthSup S v n :=
    le_csSup (orthSup_set_bddAbove S v n) ⟨0, ⟨by simp, fun m _ => inner_zero_right _⟩, rfl⟩
  simpa using (norm_nonneg (S 0)).trans h0

omit [CompleteSpace H] in
theorem le_orthSup {y : H} (hy1 : ‖y‖ ≤ 1) (hy2 : ∀ m < n, inner ℂ (v m) y = 0) :
    ‖S y‖ ≤ orthSup S v n :=
  le_csSup (orthSup_set_bddAbove S v n) ⟨y, ⟨hy1, hy2⟩, rfl⟩

omit [CompleteSpace H] in
theorem orthSup_le {c : ℝ}
    (hc : ∀ y : H, ‖y‖ ≤ 1 → (∀ m < n, inner ℂ (v m) y = 0) → ‖S y‖ ≤ c) :
    orthSup S v n ≤ c := by
  refine csSup_le (orthSup_set_nonempty S v n) ?_
  rintro r ⟨y, ⟨hy1, hy2⟩, rfl⟩
  exact hc y hy1 hy2

omit [CompleteSpace H] in
theorem orthSup_le_opNorm : orthSup S v n ≤ ‖S‖ := by
  refine orthSup_le S v n fun y hy1 _ => ?_
  calc ‖S y‖ ≤ ‖S‖ * ‖y‖ := S.le_opNorm y
    _ ≤ ‖S‖ * 1 := by gcongr
    _ = ‖S‖ := mul_one _

omit [CompleteSpace H] in
/-- The constrained-norm bound at every orthogonal vector, any norm:
`‖S y‖ ≤ orthSup · ‖y‖`. -/
theorem norm_le_orthSup_mul_norm {y : H} (hy : ∀ m < n, inner ℂ (v m) y = 0) :
    ‖S y‖ ≤ orthSup S v n * ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  · have hunit : ‖(‖y‖⁻¹ : ℂ) • y‖ ≤ 1 := le_of_eq (norm_smul_inv_norm hy0)
    have horth : ∀ m < n, inner ℂ (v m) ((‖y‖⁻¹ : ℂ) • y) = 0 := by
      intro m hm
      rw [inner_smul_right, hy m hm, mul_zero]
    have hb := le_orthSup S v n hunit horth
    rw [map_smul, norm_smul] at hb
    have hnorm : ‖((‖y‖ : ℂ))⁻¹‖ = ‖y‖⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
    rw [hnorm] at hb
    have hy0' : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy0
    calc ‖S y‖ = ‖y‖⁻¹ * ‖S y‖ * ‖y‖ := by field_simp
      _ ≤ orthSup S v n * ‖y‖ := by
          have := mul_le_mul_of_nonneg_right hb (le_of_lt hy0')
          simpa [mul_comm] using this

omit [CompleteSpace H] in
theorem orthSup_antitone (S : H →L[ℂ] H) (v : ℕ → H) : Antitone (orthSup S v) := by
  intro m n hmn
  refine csSup_le_csSup (orthSup_set_bddAbove S v m) (orthSup_set_nonempty S v n) ?_
  rintro r ⟨y, ⟨hy1, hy2⟩, rfl⟩
  exact ⟨y, ⟨hy1, fun k hk => hy2 k (lt_of_lt_of_le hk hmn)⟩, rfl⟩

end OrthSup

/-- **The exhaustion step.**  If the first `n` members of `v` are eigenvectors of the positive
compact self-adjoint `S` and the constrained norm `orthSup S v n` does not vanish, then it is an
eigenvalue of `S` realized by a unit eigenvector orthogonal to `v 0, …, v (n−1)`: restrict `S` to
the orthogonal complement of their span — invariant since they are eigenvectors — where the
restriction is compact and self-adjoint with norm `orthSup S v n`, and apply the norm-attaining
eigenvalue, whose sign is pinned by positivity. -/
theorem exists_eigenvector_orthSup {S : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) (hpos : ∀ x : H, 0 ≤ RCLike.re (inner ℂ x (S x)))
    (v : ℕ → H) (n : ℕ) (hv : ∀ m < n, ∃ c : ℝ, S (v m) = (c : ℂ) • v m)
    (hne : orthSup S v n ≠ 0) :
    ∃ x : H, ‖x‖ = 1 ∧ (∀ m < n, inner ℂ (v m) x = 0)
      ∧ S x = (orthSup S v n : ℂ) • x := by
  set W : Submodule ℂ H := (Submodule.span ℂ (v '' Set.Iio n))ᗮ with hW
  have hmemW : ∀ y : H, y ∈ W ↔ ∀ m < n, inner ℂ (v m) y = 0 := by
    intro y
    rw [hW, Submodule.mem_orthogonal_span_iff]
    constructor
    · intro h m hm
      exact h (v m) ⟨m, hm, rfl⟩
    · rintro h u ⟨m, hm, rfl⟩
      exact h m hm
  have hWinv : ∀ y ∈ W, S y ∈ W := by
    intro y hy
    rw [hmemW] at hy ⊢
    intro m hm
    obtain ⟨c, hc⟩ := hv m hm
    have h1 : inner ℂ (v m) (S y) = inner ℂ (S (v m)) y := (hsym (v m) y).symm
    rw [h1, hc, inner_smul_left, hy m hm, mul_zero]
  set Sw : W →L[ℂ] W := S.restrict hWinv with hSw
  have hSw_apply : ∀ w : W, (Sw w : H) = S (w : H) := fun w => rfl
  have hSw_compact : IsCompactOperator Sw := hcpt.restrict' hWinv
  have hSw_symm : Sw.IsSymmetric := hsym.restrict_invariant hWinv
  have hSw_norm : ‖Sw‖ = orthSup S v n := by
    refine le_antisymm ?_ ?_
    · refine opNorm_le_bound _ (orthSup_nonneg S v n) fun w => ?_
      have h1 : ‖Sw w‖ = ‖S (w : H)‖ := by rw [show ‖Sw w‖ = ‖(Sw w : H)‖ from rfl, hSw_apply]
      rw [h1, show ‖w‖ = ‖(w : H)‖ from rfl]
      exact norm_le_orthSup_mul_norm S v n ((hmemW _).mp w.2)
    · refine orthSup_le S v n fun y hy1 hy2 => ?_
      have hyW : y ∈ W := (hmemW y).mpr hy2
      calc ‖S y‖ = ‖Sw ⟨y, hyW⟩‖ := by rw [show ‖Sw ⟨y, hyW⟩‖ = ‖(Sw ⟨y, hyW⟩ : H)‖ from rfl,
            hSw_apply]
        _ ≤ ‖Sw‖ * ‖(⟨y, hyW⟩ : W)‖ := Sw.le_opNorm _
        _ ≤ ‖Sw‖ * 1 := by
            gcongr
            exact hy1
        _ = ‖Sw‖ := mul_one _
  have hSw0 : Sw ≠ 0 := by
    intro h
    apply hne
    rw [← hSw_norm, h]
    exact norm_zero (E := ↥W →L[ℂ] ↥W)
  obtain ⟨μ, ξ, hμ_norm, hξ_unit, hξ_eig⟩ :=
    exists_unit_eigenvector_norm hSw_compact hSw_symm hSw0
  have hμ_nonneg : 0 ≤ μ := by
    have h1 : RCLike.re (inner ℂ ξ (Sw ξ)) = μ := by
      rw [hξ_eig, inner_smul_right]
      have : inner ℂ ξ ξ = ((1 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K, hξ_unit]
        norm_num
      rw [this]
      simp
    have h2 : 0 ≤ RCLike.re (inner ℂ ξ (Sw ξ)) := by
      rw [Submodule.coe_inner, hSw_apply]
      exact hpos _
    rw [h1] at h2
    exact h2
  have hμ_val : μ = orthSup S v n := by
    have h1 : |μ| = orthSup S v n := hμ_norm.trans hSw_norm
    rw [abs_of_nonneg hμ_nonneg] at h1
    exact h1
  refine ⟨(ξ : H), hξ_unit, (hmemW _).mp ξ.2, ?_⟩
  have := congrArg (Subtype.val : W → H) hξ_eig
  rw [hSw_apply] at this
  rw [this, Submodule.coe_smul, hμ_val]

end ContinuousLinearMap

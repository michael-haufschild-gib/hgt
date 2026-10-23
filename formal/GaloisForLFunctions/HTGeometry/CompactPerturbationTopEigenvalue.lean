import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Ring.Units

/-!
# The top of the numerical range above a compact perturbation is an eigenvalue

Let `L = K + B` be a symmetric operator on a complex Hilbert space with `K` compact and `‖B‖ ≤ b`.
If the numerical range of `L` exceeds `b`, its supremum `M = sup re⟪Lx, x⟫/‖x‖²` is an eigenvalue of
`L` with a finite-dimensional eigenspace.

Proof.  `S = M - L` is positive, and `‖Sx‖² ≤ ‖S‖ re⟪Sx, x⟫` (expand `re⟪S(x - tSx), x - tSx⟫ ≥ 0`
at `t = 1/‖S‖`); since `re⟪Sx, x⟫` gets arbitrarily small on unit vectors, `S` is not invertible.
As `‖B‖ < M`, `U = M - B` is invertible and `S = U (1 - U⁻¹K)`, so `1 - U⁻¹K` is not invertible:
`1` lies in the spectrum of the compact operator `U⁻¹K`, hence is an eigenvalue (Fredholm
alternative), and an eigenvector of `U⁻¹K` for `1` is an eigenvector of `L` for `M`.

* `HTGeometry.norm_sq_le_of_nonneg` : `‖Sx‖² ≤ ‖S‖ re⟪Sx, x⟫` for positive symmetric `S`.
* `HTGeometry.exists_eigenvector_of_compact_add`.
* `HTGeometry.finiteDimensional_eigenspace_of_compact_add`.
-/

open RCLike ContinuousLinearMap Module End

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

omit [CompleteSpace H] in
/-- **Cauchy–Schwarz for a positive operator**: `‖Sx‖² ≤ ‖S‖ re⟪Sx, x⟫`. -/
theorem norm_sq_le_of_nonneg {S : H →L[ℂ] H} (hS : (S : H →ₗ[ℂ] H).IsSymmetric)
    (hpos : ∀ y, 0 ≤ re ⟪S y, y⟫) (x : H) : ‖S x‖ ^ 2 ≤ ‖S‖ * re ⟪S x, x⟫ := by
  rcases (norm_nonneg S).lt_or_eq with hS0 | hS0
  · set t : ℝ := ‖S‖⁻¹
    have ht : 0 < t := inv_pos.2 hS0
    have h0 := hpos (x - (t : ℂ) • S x)
    have hsymm : ⟪S (S x), x⟫ = ⟪S x, S x⟫ := hS (S x) x
    have hcx : ⟪S (x - (t : ℂ) • S x), x - (t : ℂ) • S x⟫ =
        ⟪S x, x⟫ - ((2 * t * ‖S x‖ ^ 2 : ℝ) : ℂ) + ((t ^ 2 : ℝ) : ℂ) * ⟪S (S x), S x⟫ := by
      rw [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left,
        inner_smul_right, inner_smul_left, inner_smul_right, hsymm, inner_self_eq_norm_sq_to_K,
        Complex.conj_ofReal]
      push_cast
      ring_nf
      try rfl
    have hexp : re ⟪S (x - (t : ℂ) • S x), x - (t : ℂ) • S x⟫ =
        re ⟪S x, x⟫ - 2 * t * ‖S x‖ ^ 2 + t ^ 2 * re ⟪S (S x), S x⟫ := by
      rw [hcx]
      simp only [RCLike.re_to_complex, Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hbd : re ⟪S (S x), S x⟫ ≤ ‖S‖ * ‖S x‖ ^ 2 := by
      calc re ⟪S (S x), S x⟫ ≤ ‖⟪S (S x), S x⟫‖ := re_le_norm _
        _ ≤ ‖S (S x)‖ * ‖S x‖ := norm_inner_le_norm _ _
        _ ≤ ‖S‖ * ‖S x‖ * ‖S x‖ := by gcongr; exact le_opNorm S (S x)
        _ = ‖S‖ * ‖S x‖ ^ 2 := by ring
    rw [hexp] at h0
    have h1 : 0 ≤ re ⟪S x, x⟫ - 2 * t * ‖S x‖ ^ 2 + t ^ 2 * (‖S‖ * ‖S x‖ ^ 2) :=
      h0.trans (by gcongr)
    have htS : t * ‖S‖ = 1 := inv_mul_cancel₀ hS0.ne'
    have h2 : t ^ 2 * (‖S‖ * ‖S x‖ ^ 2) = t * ‖S x‖ ^ 2 := by
      calc t ^ 2 * (‖S‖ * ‖S x‖ ^ 2) = t * (t * ‖S‖) * ‖S x‖ ^ 2 := by ring
        _ = t * ‖S x‖ ^ 2 := by rw [htS, mul_one]
    rw [h2] at h1
    have h3 : t * ‖S x‖ ^ 2 ≤ re ⟪S x, x⟫ := by linarith
    calc ‖S x‖ ^ 2 = ‖S‖ * (t * ‖S x‖ ^ 2) := by
          rw [← mul_assoc, mul_comm ‖S‖ t, htS, one_mul]
      _ ≤ ‖S‖ * re ⟪S x, x⟫ := by gcongr
  · have : S = 0 := norm_eq_zero.1 hS0.symm
    simp [this]

omit [CompleteSpace H] in
private theorem unit_inv_apply_apply (U : (H →L[ℂ] H)ˣ) (y : H) :
    (↑U⁻¹ : H →L[ℂ] H) ((U : H →L[ℂ] H) y) = y := by
  show ((↑U⁻¹ : H →L[ℂ] H) * (U : H →L[ℂ] H)) y = y
  rw [Units.inv_mul]
  rfl

omit [CompleteSpace H] in
private theorem unit_apply_inv_apply (U : (H →L[ℂ] H)ˣ) (y : H) :
    (U : H →L[ℂ] H) ((↑U⁻¹ : H →L[ℂ] H) y) = y := by
  show ((U : H →L[ℂ] H) * (↑U⁻¹ : H →L[ℂ] H)) y = y
  rw [Units.mul_inv]
  rfl

omit [CompleteSpace H] in
/-- A positive operator whose quadratic form is arbitrarily small on unit vectors is not invertible. -/
theorem not_isUnit_of_inf_zero {S : H →L[ℂ] H} (hS : (S : H →ₗ[ℂ] H).IsSymmetric)
    (hpos : ∀ y, 0 ≤ re ⟪S y, y⟫) (hsmall : ∀ δ > 0, ∃ x : H, ‖x‖ = 1 ∧ re ⟪S x, x⟫ < δ) :
    ¬ IsUnit S := by
  rintro ⟨U, rfl⟩
  set c : ℝ := ‖(↑U⁻¹ : H →L[ℂ] H)‖
  have hc : ∀ x : H, ‖x‖ ≤ c * ‖(U : H →L[ℂ] H) x‖ := fun x => by
    calc ‖x‖ = ‖(↑U⁻¹ : H →L[ℂ] H) ((U : H →L[ℂ] H) x)‖ := by rw [unit_inv_apply_apply]
      _ ≤ c * ‖(U : H →L[ℂ] H) x‖ := le_opNorm _ _
  set d : ℝ := c ^ 2 * ‖(U : H →L[ℂ] H)‖
  obtain ⟨x, hx1, hx⟩ := hsmall (1 / (d + 1)) (by positivity)
  have h1 := hc x
  rw [hx1] at h1
  have h2 := norm_sq_le_of_nonneg hS hpos x
  have hc0 : 0 ≤ c := norm_nonneg _
  have h3 : 1 ≤ c ^ 2 * ‖(U : H →L[ℂ] H) x‖ ^ 2 := by
    have := pow_le_pow_left₀ zero_le_one h1 2
    rw [one_pow, mul_pow] at this
    exact this
  have h4 : c ^ 2 * ‖(U : H →L[ℂ] H) x‖ ^ 2 ≤ d * re ⟪(U : H →L[ℂ] H) x, x⟫ := by
    calc c ^ 2 * ‖(U : H →L[ℂ] H) x‖ ^ 2 ≤ c ^ 2 * (‖(U : H →L[ℂ] H)‖ * re ⟪(U : H →L[ℂ] H) x, x⟫) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = d * re ⟪(U : H →L[ℂ] H) x, x⟫ := by ring
  have hd0 : 0 ≤ d := by positivity
  have h5 : d * re ⟪(U : H →L[ℂ] H) x, x⟫ ≤ d * (1 / (d + 1)) :=
    mul_le_mul_of_nonneg_left hx.le hd0
  have h6 : d * (1 / (d + 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith
  linarith

variable {L K B : H →L[ℂ] H}

/-- **The top of the numerical range above a compact perturbation is an eigenvalue.**  If
`L = K + B` is symmetric, `K` is compact, `‖B‖ ≤ b` and `re⟪Lf, f⟫ > b‖f‖²` for some `f`, then
`M = sup re⟪Lx, x⟫/‖x‖²` exceeds `b`, bounds the numerical range, and has an eigenvector. -/
theorem exists_eigenvector_of_compact_add (hL : (L : H →ₗ[ℂ] H).IsSymmetric)
    (hK : IsCompactOperator K) (hLKB : L = K + B) {b : ℝ} (hb : 0 ≤ b) (hB : ‖B‖ ≤ b) {f : H}
    (hf : b * ‖f‖ ^ 2 < re ⟪L f, f⟫) :
    ∃ M : ℝ, b < M ∧ (∀ x, re ⟪L x, x⟫ ≤ M * ‖x‖ ^ 2) ∧ ∃ x, x ≠ 0 ∧ L x = (M : ℂ) • x := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hf
  -- the supremum of the Rayleigh quotient
  haveI : Nonempty {x : H // x ≠ 0} := ⟨⟨f, hf0⟩⟩
  have hbdd : BddAbove (Set.range fun x : {x : H // x ≠ 0} => L.rayleighQuotient x) :=
    ⟨‖L‖, by rintro _ ⟨x, rfl⟩; exact (le_abs_self _).trans (L.rayleighQuotient_le_norm x)⟩
  set M : ℝ := ⨆ x : {x : H // x ≠ 0}, L.rayleighQuotient x with hMdef
  have hle : ∀ x : H, re ⟪L x, x⟫ ≤ M * ‖x‖ ^ 2 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have h1 : L.rayleighQuotient x ≤ M := le_ciSup hbdd ⟨x, hx⟩
      have hx2 : 0 < ‖x‖ ^ 2 := by positivity
      rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf,
        div_le_iff₀ hx2] at h1
      exact h1
  have hbM : b < M := by
    have h1 : L.rayleighQuotient f ≤ M := le_ciSup hbdd ⟨f, hf0⟩
    have hf2 : 0 < ‖f‖ ^ 2 := by positivity
    have h2 : b < L.rayleighQuotient f := by
      rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf,
        lt_div_iff₀ hf2]
      exact hf
    linarith
  refine ⟨M, hbM, hle, ?_⟩
  -- `S = M - L` is positive and not invertible
  set S : H →L[ℂ] H := (M : ℂ) • (1 : H →L[ℂ] H) - L with hSdef
  have hSx : ∀ x, S x = (M : ℂ) • x - L x := fun x => by simp [hSdef]
  have hSsymm : (S : H →ₗ[ℂ] H).IsSymmetric := fun x y => by
    change ⟪S x, y⟫ = ⟪x, S y⟫
    rw [hSx, hSx, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, show ⟪L x, y⟫ = ⟪x, L y⟫ from hL x y]
  have hSre : ∀ x, re ⟪S x, x⟫ = M * ‖x‖ ^ 2 - re ⟪L x, x⟫ := fun x => by
    rw [hSx, inner_sub_left, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K,
      map_sub]
    congr 1
    simp only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sq,
      zero_mul, sub_zero, mul_zero, RCLike.ofReal_eq_complex_ofReal]
  have hSpos : ∀ x, 0 ≤ re ⟪S x, x⟫ := fun x => by rw [hSre]; linarith [hle x]
  have hsmall : ∀ δ > 0, ∃ x : H, ‖x‖ = 1 ∧ re ⟪S x, x⟫ < δ := by
    intro δ hδ
    obtain ⟨⟨y, hy⟩, hyM⟩ := exists_lt_of_lt_ciSup (show M - δ < M by linarith)
    refine ⟨(‖y‖⁻¹ : ℂ) • y, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)]
    · have hq := L.rayleigh_smul y (c := (‖y‖⁻¹ : ℂ)) (by simpa using hy)
      have hn : ‖(‖y‖⁻¹ : ℂ) • y‖ = 1 := by
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
          inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)]
      rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf, hn,
        one_pow, div_one] at hq
      rw [hSre, hn, one_pow, mul_one]
      rw [hq]
      simp only at hyM
      linarith
  have hSnu := not_isUnit_of_inf_zero hSsymm hSpos hsmall
  -- `U = M - B` is invertible
  have hM0 : 0 < M := lt_of_le_of_lt hb hbM
  have hBM : ‖(M : ℂ)⁻¹ • B‖ < 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hM0.le, inv_mul_lt_iff₀ hM0,
      mul_one]
    linarith
  have hU0 : IsUnit ((M : ℂ) • (1 : H →L[ℂ] H) - B) := by
    have e : (M : ℂ) • (1 : H →L[ℂ] H) - B = (M : ℂ) • (1 - (M : ℂ)⁻¹ • B) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hM0.ne'), one_smul]
    rw [e]
    exact (Units.oneSub _ hBM).isUnit.smul (Units.mk0 (M : ℂ) (by exact_mod_cast hM0.ne'))
  obtain ⟨U, hUe⟩ := hU0
  set T : H →L[ℂ] H := (↑U⁻¹ : H →L[ℂ] H) * K with hT
  have hTc : IsCompactOperator T := hK.clm_comp _
  have hST : S = (U : H →L[ℂ] H) * (1 - T) := by
    rw [hT, mul_sub, mul_one, ← mul_assoc, Units.mul_inv, one_mul, hUe, hSdef, hLKB]
    abel
  have hnu : ¬ IsUnit (1 - T) := by
    intro h
    apply hSnu
    rw [hST]
    exact U.isUnit.mul h
  have hspec : (1 : ℂ) ∈ spectrum ℂ T := by
    rw [spectrum.mem_iff, map_one]
    exact hnu
  have hev := (hTc.hasEigenvalue_iff_mem_spectrum one_ne_zero).2 hspec
  obtain ⟨x, hx⟩ := hev.exists_hasEigenvector
  refine ⟨x, hx.2, ?_⟩
  have hTx : T x = x := by
    have := hx.1
    rw [mem_eigenspace_iff, one_smul] at this
    exact this
  have hKx : K x = (U : H →L[ℂ] H) x := by
    have := congrArg (U : H →L[ℂ] H) hTx
    change (U : H →L[ℂ] H) ((↑U⁻¹ : H →L[ℂ] H) (K x)) = _ at this
    rwa [unit_apply_inv_apply] at this
  rw [hLKB]
  change K x + B x = _
  rw [hKx, hUe]
  simp

/-- **The eigenspace above a compact perturbation is finite-dimensional.** -/
theorem finiteDimensional_eigenspace_of_compact_add (hK : IsCompactOperator K) (hLKB : L = K + B)
    {M : ℂ} (hBM : ‖B‖ < ‖M‖) : FiniteDimensional ℂ (eigenspace (L : End ℂ H) M) := by
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp at hBM
    exact absurd hBM (not_lt.2 (norm_nonneg _))
  have hBM' : ‖M⁻¹ • B‖ < 1 := by
    rw [norm_smul, norm_inv, inv_mul_lt_iff₀ (norm_pos_iff.2 hM0), mul_one]
    exact hBM
  have hU0 : IsUnit (M • (1 : H →L[ℂ] H) - B) := by
    have e : M • (1 : H →L[ℂ] H) - B = M • (1 - M⁻¹ • B) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hM0, one_smul]
    rw [e]
    exact (Units.oneSub _ hBM').isUnit.smul (Units.mk0 M hM0)
  obtain ⟨U, hUe⟩ := hU0
  set T : H →L[ℂ] H := (↑U⁻¹ : H →L[ℂ] H) * K with hT
  have hTc : IsCompactOperator T := hK.clm_comp _
  have heq : eigenspace (L : End ℂ H) M = eigenspace (T : End ℂ H) 1 := by
    ext x
    rw [mem_eigenspace_iff, mem_eigenspace_iff, one_smul]
    change L x = M • x ↔ T x = x
    have hLx : L x = K x + B x := by rw [hLKB]; rfl
    have hUx : (U : H →L[ℂ] H) x = M • x - B x := by rw [hUe]; simp
    constructor
    · intro h
      have hKx : K x = (U : H →L[ℂ] H) x := by rw [hUx, ← h, hLx]; abel
      change (↑U⁻¹ : H →L[ℂ] H) (K x) = x
      rw [hKx, unit_inv_apply_apply]
    · intro h
      have hKx : K x = (U : H →L[ℂ] H) x := by
        have := congrArg (U : H →L[ℂ] H) h
        change (U : H →L[ℂ] H) ((↑U⁻¹ : H →L[ℂ] H) (K x)) = _ at this
        rwa [unit_apply_inv_apply] at this
      rw [hLx, hKx, hUx]
      abel
  rw [heq]
  exact ContinuousLinearMap.finite_dimensional_eigenspace hTc 1 one_ne_zero

end

end GaloisForLFunctions.HTGeometry

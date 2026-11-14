import GaloisForLFunctions.CompactHyperbolicSurfaces.CyclicCovers
import GaloisForLFunctions.CompactHyperbolicSurfaces.SelbergZeta

/-!
# A compact surface whose Selberg zeta function has zeros off the critical line

For an odd `n`, the cyclic cover `X = Γ_n\ℍ` of the quaternion surface `Γ(5)\ℍ` has an eigenvalue
`λ ∈ (0, ¼)` (`exists_coverGroup_small_eigenvalue`).  Its Selberg zeta function `Z`

* is the Euler product `Π_{p prim, k ≥ 0} (1 − e^{−(s+k)ℓ_p})` on `Re s > 1`;
* is holomorphic on `Re s > 0`;
* satisfies `Z(1 − s) = Z(s) exp(−|F| ∫_0^{s−½} v tan πv dv)` on `0 < Re s < 1`, the integral taken
  along the segment `v = t(s − ½)`;
* has, in `0 < Re s < 1` and off `Re s = ½`, exactly the zeros `½ ± √(¼ − λ_j)`, `0 < λ_j < ¼`:
  a finite nonempty set (`exists_selbergZeta_small_eigenvalue`).

The zeros come from `λ_j + s(s − 1) = 0`: writing `s = ½ + w`, `w² = ¼ − λ_j` is real, so `w` is
real or purely imaginary, and `Re s ≠ ½`, `0 < Re s < 1` force `w = ±√(¼ − λ_j)`, `0 < λ_j < ¼`
(`offLine_zeros_eq`).
-/

open MeasureTheory Set Real
open scoped MatrixGroups

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

noncomputable section

namespace CompactQuotient

variable (X : CompactQuotient)

/-- **The zeros off the critical line.**  In `0 < Re s < 1`, `Re s ≠ ½`, the zeros of `Z` are the
points `½ ± √(¼ − λ_j)` with `0 < λ_j < ¼`. -/
theorem offLine_zeros_eq (hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ|) {a : ℝ} (ha : 1 < a) :
    {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 ∧ X.selbergZeta ha s = 0} =
      {s | ∃ j : X.SpecIndex ha, 0 < X.spectralParam ha j ∧ X.spectralParam ha j < 1 / 4 ∧
        (s = ((1 / 2 + √(1 / 4 - X.spectralParam ha j) : ℝ) : ℂ) ∨
          s = ((1 / 2 - √(1 / 4 - X.spectralParam ha j) : ℝ) : ℂ))} := by
  ext s
  simp only [Set.mem_setOf_eq]
  rw [selbergZeta_eq_zero_iff hhyp ha]
  constructor
  · rintro ⟨h0, h1, hne, j, hj⟩
    have hre := congrArg Complex.re hj
    have him := congrArg Complex.im hj
    simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im,
      Complex.zero_re, Complex.zero_im] at hre him
    have hy : s.im = 0 := by
      have h2 : s.im * (2 * s.re - 1) = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd (by linarith : s.re = 1 / 2) hne
    rw [hy] at hre
    have hσ2 : (s.re - 1 / 2) ^ 2 = 1 / 4 - X.spectralParam ha j := by linear_combination hre
    have hσ0 : s.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hne
    have hpos2 : 0 < (s.re - 1 / 2) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hσ0))
    have hlt2 : (s.re - 1 / 2) ^ 2 < 1 / 4 := by nlinarith [mul_pos h0 (sub_pos.mpr h1)]
    have hsqrt : √(1 / 4 - X.spectralParam ha j) = |s.re - 1 / 2| := by
      rw [← hσ2, Real.sqrt_sq_eq_abs]
    refine ⟨j, by linarith, by linarith, ?_⟩
    have hs : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hy])
    rcases abs_cases (s.re - 1 / 2) with ⟨habs, -⟩ | ⟨habs, -⟩
    · left
      rw [hs, hsqrt, habs]
      congr 1
      ring
    · right
      rw [hs, hsqrt, habs]
      congr 1
      ring
  · rintro ⟨j, hj0, hj1, hs⟩
    have hσ : 0 < √(1 / 4 - X.spectralParam ha j) := Real.sqrt_pos.mpr (by linarith)
    have hσ' : √(1 / 4 - X.spectralParam ha j) < 1 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; linarith
    have hsq : √(1 / 4 - X.spectralParam ha j) ^ 2 = 1 / 4 - X.spectralParam ha j :=
      Real.sq_sqrt (by linarith)
    rcases hs with rfl | rfl
    · refine ⟨by rw [Complex.ofReal_re]; linarith, by rw [Complex.ofReal_re]; linarith,
        by rw [Complex.ofReal_re]; exact ne_of_gt (by linarith), j, ?_⟩
      have e : ((X.spectralParam ha j : ℝ) : ℂ) +
          ((1 / 2 + √(1 / 4 - X.spectralParam ha j) : ℝ) : ℂ) *
            (((1 / 2 + √(1 / 4 - X.spectralParam ha j) : ℝ) : ℂ) - 1) =
          ((X.spectralParam ha j + (1 / 2 + √(1 / 4 - X.spectralParam ha j)) *
            (1 / 2 + √(1 / 4 - X.spectralParam ha j) - 1) : ℝ) : ℂ) := by
        push_cast; ring
      rw [e, Complex.ofReal_eq_zero]
      linear_combination hsq
    · refine ⟨by rw [Complex.ofReal_re]; linarith, by rw [Complex.ofReal_re]; linarith,
        by rw [Complex.ofReal_re]; exact ne_of_lt (by linarith), j, ?_⟩
      have e : ((X.spectralParam ha j : ℝ) : ℂ) +
          ((1 / 2 - √(1 / 4 - X.spectralParam ha j) : ℝ) : ℂ) *
            (((1 / 2 - √(1 / 4 - X.spectralParam ha j) : ℝ) : ℂ) - 1) =
          ((X.spectralParam ha j + (1 / 2 - √(1 / 4 - X.spectralParam ha j)) *
            (1 / 2 - √(1 / 4 - X.spectralParam ha j) - 1) : ℝ) : ℂ) := by
        push_cast; ring
      rw [e, Complex.ofReal_eq_zero]
      linear_combination hsq

end CompactQuotient

open CompactQuotient

/-- **A compact hyperbolic surface whose Selberg zeta function has a finite nonempty set of zeros
off the critical line.**  For some odd `n`, `X = Γ_n\ℍ` (a cyclic cover of the quaternion surface
`Γ(5)\ℍ`) satisfies: every `γ ≠ 1` is hyperbolic; `Z` is the Euler product
`Π_{p, k} (1 − e^{−(s+k)ℓ_p})` on `Re s > 1`; `Z` is holomorphic on `Re s > 0`;
`Z(1 − s) = Z(s) exp(−|F| ∫_0^{s−½} v tan πv dv)` on `0 < Re s < 1`; and the zeros in
`0 < Re s < 1` off `Re s = ½` are exactly the points `½ ± √(¼ − λ)` for the eigenvalues
`λ ∈ (0, ¼)`, a finite nonempty set. -/
theorem exists_selbergZeta_small_eigenvalue :
    ∃ (n : ℕ) (X : CompactQuotient), X.Γ = coverGroup n ∧
      (∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ|) ∧
      (∀ s : ℂ, 1 < s.re → HasProd (fun x : X.PClass × ℕ =>
          1 - Complex.exp (-((s + x.2) * X.classLen x.1.1))) (X.selbergZeta one_lt_two s)) ∧
      DifferentiableOn ℂ (X.selbergZeta one_lt_two) {s | 0 < s.re} ∧
      (∀ s : ℂ, 0 < s.re → s.re < 1 → X.selbergZeta one_lt_two (1 - s) =
        X.selbergZeta one_lt_two s * Complex.exp (-(X.area *
          ∫ t in (0 : ℝ)..1, (s - 1 / 2) * (((t : ℂ) * (s - 1 / 2)) *
            Complex.tan (π * ((t : ℂ) * (s - 1 / 2))))))) ∧
      {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 ∧ X.selbergZeta one_lt_two s = 0}.Finite ∧
      {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 ∧ X.selbergZeta one_lt_two s = 0}.Nonempty ∧
      {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 ∧ X.selbergZeta one_lt_two s = 0} =
        {s | ∃ j : X.SpecIndex one_lt_two, 0 < X.spectralParam one_lt_two j ∧
          X.spectralParam one_lt_two j < 1 / 4 ∧
          (s = ((1 / 2 + √(1 / 4 - X.spectralParam one_lt_two j) : ℝ) : ℂ) ∨
            s = ((1 / 2 - √(1 / 4 - X.spectralParam one_lt_two j) : ℝ) : ℂ))} := by
  obtain ⟨n, hodd, -, hsmall⟩ := exists_coverGroup_small_eigenvalue (a := 2) one_lt_two
  obtain ⟨X, hX⟩ := exists_compactQuotient_coverGroup hodd
  have hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ| := by
    intro γ hγ
    have hmem : (γ : SL(2, ℝ)) ∈ congGroup 5 := (hX ▸ γ.2 : (γ : SL(2, ℝ)) ∈ coverGroup n).1
    exact two_lt_abs_trSL_congGroup (by norm_num) ⟨γ, hmem⟩ fun h =>
      hγ (Subtype.ext (congrArg (fun x : congGroup 5 => (x : SL(2, ℝ))) h))
  obtain ⟨j, hj0, hj1⟩ := hsmall X hX
  have hzeros := X.offLine_zeros_eq hhyp one_lt_two
  refine ⟨n, X, hX, hhyp, fun s hs => ?_, differentiableOn_selbergZeta (X := X) one_lt_two,
    fun s h0 h1 => selbergZeta_one_sub (X := X) one_lt_two h0 h1, ?_, ?_, hzeros⟩
  · rw [← eulerZeta_eq_selbergZeta hhyp one_lt_two hs]
    exact hasProd_eulerZeta hhyp hs
  · have hS := X.finite_lam_lt one_lt_two (1 / 4)
    refine ((hS.image fun j => ((1 / 2 + √(1 / 4 - X.spectralParam one_lt_two j) : ℝ) : ℂ)).union
      (hS.image fun j => ((1 / 2 - √(1 / 4 - X.spectralParam one_lt_two j) : ℝ) : ℂ))).subset ?_
    rw [hzeros]
    rintro s ⟨j, -, hj, hs | hs⟩
    · exact Or.inl ⟨j, hj, hs.symm⟩
    · exact Or.inr ⟨j, hj, hs.symm⟩
  · rw [hzeros]
    exact ⟨_, j, hj0, hj1, Or.inl rfl⟩

end

end GaloisForLFunctions.CompactHyperbolicSurfaces

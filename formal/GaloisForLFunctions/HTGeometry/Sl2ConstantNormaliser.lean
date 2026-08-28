import GaloisForLFunctions.HTGeometry.Sl2AbsorbingLine

/-!
# The normaliser of `sl₂` over a square-root-closed subfield

If a determinant-one matrix `g` carries the three standard generators `e`, `f`, `h` of `sl₂` into a
subfield `K` under conjugation, then all four entries of `g` already lie in `K`, provided `K` is
closed under square roots.

The computation is explicit.  Writing `g = [[a,b],[c,d]]` with `ad − bc = 1`, the adjoint action
produces

```
    g e g⁻¹ = [[−ac, a²], [−c², ac]],
    g f g⁻¹ = [[bd, −b²], [d², −bd]],
    g h g⁻¹ = [[ad + bc, −2ab], [2cd, −(ad + bc)]],
```

so every product of two of `a, b, c, d` lies in `K`; the determinant then splits `ad` and `bc`
apart.  One of `a`, `b` is nonzero, its square lies in `K`, hence so does it, and dividing the
products by it recovers the remaining entries.

This is the group half of Cassidy's classification: a differential algebraic subgroup whose Lie
algebra is `sl₂` over the constants normalises that Lie algebra, hence lies in `SL₂` over the
constants.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {U : Type*} [Field U]

/-- **The normaliser of `sl₂` over a subfield.**  A determinant-one matrix whose adjoint action
carries the three standard generators into a square-root-closed subfield has all its entries in
that subfield. -/
theorem entries_mem_of_conj_sl2 [CharZero U] (K : Subfield U)
    (hsq : ∀ x ∈ K, ∃ y ∈ K, y * y = x)
    {g : Matrix (Fin 2) (Fin 2) U} (hdet : g.det = 1)
    (hE : ∀ i j, (g * sl2E U * Matrix.adjugate g) i j ∈ K)
    (hF : ∀ i j, (g * sl2F U * Matrix.adjugate g) i j ∈ K)
    (hH : ∀ i j, (g * sl2H U * Matrix.adjugate g) i j ∈ K) :
    ∀ i j, g i j ∈ K := by
  have hadj := Matrix.adjugate_fin_two g
  have ha00 : g.adjugate 0 0 = g 1 1 := by rw [hadj]; simp
  have ha01 : g.adjugate 0 1 = -(g 0 1) := by rw [hadj]; simp
  have ha10 : g.adjugate 1 0 = -(g 1 0) := by rw [hadj]; simp
  have ha11 : g.adjugate 1 1 = g 0 0 := by rw [hadj]; simp
  have hdet' : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact hdet
  -- the entry identities of the adjoint action
  have hE01 : (g * sl2E U * Matrix.adjugate g) 0 1 = g 0 0 * g 0 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, sl2E_00, sl2E_01, sl2E_10, sl2E_11,
      ha00, ha01, ha10, ha11]; ring
  have hE00 : (g * sl2E U * Matrix.adjugate g) 0 0 = -(g 0 0 * g 1 0) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, sl2E_00, sl2E_01, sl2E_10, sl2E_11,
      ha00, ha01, ha10, ha11]; ring
  have hF01 : (g * sl2F U * Matrix.adjugate g) 0 1 = -(g 0 1 * g 0 1) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, sl2F_00, sl2F_01, sl2F_10, sl2F_11,
      ha00, ha01, ha10, ha11]; ring
  have hF00 : (g * sl2F U * Matrix.adjugate g) 0 0 = g 0 1 * g 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, sl2F_00, sl2F_01, sl2F_10, sl2F_11,
      ha00, ha01, ha10, ha11]; ring
  have hH01 : (g * sl2H U * Matrix.adjugate g) 0 1 = -(2 * (g 0 0 * g 0 1)) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, sl2H_00, sl2H_01, sl2H_10, sl2H_11,
      ha00, ha01, ha10, ha11]; ring
  have hH10 : (g * sl2H U * Matrix.adjugate g) 1 0 = 2 * (g 1 0 * g 1 1) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, sl2H_00, sl2H_01, sl2H_10, sl2H_11,
      ha00, ha01, ha10, ha11]; ring
  have hH00 : (g * sl2H U * Matrix.adjugate g) 0 0 = g 0 0 * g 1 1 + g 0 1 * g 1 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, sl2H_00, sl2H_01, sl2H_10, sl2H_11,
      ha00, ha01, ha10, ha11]; ring
  -- the pairwise products lie in the subfield
  have haa : g 0 0 * g 0 0 ∈ K := hE01 ▸ hE 0 1
  have hac : g 0 0 * g 1 0 ∈ K := by
    have h := hE 0 0
    rw [hE00] at h
    simpa using K.neg_mem h
  have hbb : g 0 1 * g 0 1 ∈ K := by
    have h := hF 0 1
    rw [hF01] at h
    simpa using K.neg_mem h
  have hbd : g 0 1 * g 1 1 ∈ K := hF00 ▸ hF 0 0
  have h2K : (2 : U) ∈ K := by
    have h2 : (2 : U) = 1 + 1 := by norm_num
    rw [h2]; exact K.add_mem K.one_mem K.one_mem
  have hab : g 0 0 * g 0 1 ∈ K := by
    have h := hH 0 1
    rw [hH01] at h
    have h' := K.mul_mem (K.inv_mem h2K) (K.neg_mem h)
    have hid : (2 : U)⁻¹ * -(-(2 * (g 0 0 * g 0 1))) = g 0 0 * g 0 1 := by field_simp
    rwa [hid] at h'
  have hsum : g 0 0 * g 1 1 + g 0 1 * g 1 0 ∈ K := hH00 ▸ hH 0 0
  have had : g 0 0 * g 1 1 ∈ K := by
    have h := K.mul_mem (K.inv_mem h2K) (K.add_mem K.one_mem hsum)
    have hid : (2 : U)⁻¹ * (1 + (g 0 0 * g 1 1 + g 0 1 * g 1 0)) = g 0 0 * g 1 1 := by
      field_simp
      linear_combination -hdet'
    rwa [hid] at h
  have hbc : g 0 1 * g 1 0 ∈ K := by
    have h := K.sub_mem hsum had
    have hid : g 0 0 * g 1 1 + g 0 1 * g 1 0 - g 0 0 * g 1 1 = g 0 1 * g 1 0 := by ring
    rwa [hid] at h
  have hsqrt_mem : ∀ x : U, x * x ∈ K → x ∈ K := by
    intro x hx
    obtain ⟨y, hyK, hy⟩ := hsq _ hx
    have hfac : (x - y) * (x + y) = 0 := by linear_combination -hy
    rcases mul_eq_zero.mp hfac with h | h
    · have hxy : x = y := by linear_combination h
      rw [hxy]; exact hyK
    · have hxy : x = -y := by linear_combination h
      rw [hxy]; exact K.neg_mem hyK
  by_cases h00 : g 0 0 = 0
  · have hb0 : g 0 1 ≠ 0 := by
      intro h
      rw [h00, h] at hdet'
      simp at hdet'
    have hbK : g 0 1 ∈ K := hsqrt_mem _ hbb
    have hbinv : (g 0 1)⁻¹ ∈ K := K.inv_mem hbK
    have hcK : g 1 0 ∈ K := by
      have h := K.mul_mem hbinv hbc
      have hid : (g 0 1)⁻¹ * (g 0 1 * g 1 0) = g 1 0 := by field_simp
      rwa [hid] at h
    have hdK : g 1 1 ∈ K := by
      have h := K.mul_mem hbinv hbd
      have hid : (g 0 1)⁻¹ * (g 0 1 * g 1 1) = g 1 1 := by field_simp
      rwa [hid] at h
    have haK : g 0 0 ∈ K := by rw [h00]; exact K.zero_mem
    intro i j
    fin_cases i <;> fin_cases j <;> assumption
  · have haK : g 0 0 ∈ K := hsqrt_mem _ haa
    have hainv : (g 0 0)⁻¹ ∈ K := K.inv_mem haK
    have hbK : g 0 1 ∈ K := by
      have h := K.mul_mem hainv hab
      have hid : (g 0 0)⁻¹ * (g 0 0 * g 0 1) = g 0 1 := by field_simp
      rwa [hid] at h
    have hcK : g 1 0 ∈ K := by
      have h := K.mul_mem hainv hac
      have hid : (g 0 0)⁻¹ * (g 0 0 * g 1 0) = g 1 0 := by field_simp
      rwa [hid] at h
    have hdK : g 1 1 ∈ K := by
      have h := K.mul_mem hainv had
      have hid : (g 0 0)⁻¹ * (g 0 0 * g 1 1) = g 1 1 := by field_simp
      rwa [hid] at h
    intro i j
    fin_cases i <;> fin_cases j <;> assumption

end

end GaloisForLFunctions.HTGeometry

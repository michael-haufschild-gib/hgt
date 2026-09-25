import GaloisForLFunctions.RHTower.SelbergEisensteinCusp

open MeasureTheory

open scoped MatrixGroups

/-!
# Admissible rows at the cusp `σ∞` and period translates

Right multiplication of row vectors by `SL₂(ℤ)` is invertible (`rowMul_inv`) and preserves primitivity
(`isCoprime_rowMul`), so `p ∈ adm(Γ(N))·σ ↔ p σ⁻¹ ∈ adm(Γ(N))` (`mem_image_iff`), and shifting `d` by a multiple of
`|c|N` preserves admissibility at `σ∞` (`mem_image_shift`). Integrals over the period translates `[a + jT, a + (j+1)T]`
of an integrable function sum to its integral (`hasSum_translates`). These are the inputs for the constant term of
`E_∞` at `σ∞`.
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinCuspRows
open GaloisForLFunctions.RHTower.SelbergPoincareFourier GaloisForLFunctions.RHTower.SelbergEisensteinCusp

theorem rowMul_mul (σ τ : SL(2, ℤ)) (p : ℤ × ℤ) : rowMul τ (rowMul σ p) = rowMul (σ * τ) p := by
  simp only [rowMul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Prod.mk.injEq]
  constructor <;> ring

theorem rowMul_one (p : ℤ × ℤ) : rowMul 1 p = p := by simp [rowMul]

theorem rowMul_inv (σ : SL(2, ℤ)) (p : ℤ × ℤ) : rowMul σ⁻¹ (rowMul σ p) = p := by
  rw [rowMul_mul, mul_inv_cancel, rowMul_one]

theorem mem_image_iff (N : ℕ) (σ : SL(2, ℤ)) (p : ℤ × ℤ) : p ∈ rowMul σ '' adm N ↔ rowMul σ⁻¹ p ∈ adm N := by
  constructor
  · rintro ⟨q, hq, rfl⟩; rwa [rowMul_inv]
  · intro h; refine ⟨rowMul σ⁻¹ p, h, ?_⟩
    rw [rowMul_mul, inv_mul_cancel, rowMul_one]

theorem isCoprime_rowMul (σ : SL(2, ℤ)) {p : ℤ × ℤ} (h : IsCoprime p.1 p.2) :
    IsCoprime (rowMul σ p).1 (rowMul σ p).2 := by
  obtain ⟨u, v, huv⟩ := h
  have hdet := σ.2
  rw [Matrix.det_fin_two] at hdet
  -- the inverse row map expresses `p` linearly in `rowMul σ p`
  refine ⟨u * σ 1 1 - v * σ 0 1, v * σ 0 0 - u * σ 1 0, ?_⟩
  simp only [rowMul]
  linear_combination (u * p.1 + v * p.2) * hdet + huv

theorem rowMul_add_shift (σ : SL(2, ℤ)) (c d t : ℤ) :
    rowMul σ (c, d + t) = ((rowMul σ (c, d)).1 + t * σ 1 0, (rowMul σ (c, d)).2 + t * σ 1 1) := by
  simp only [rowMul, Prod.mk.injEq]; constructor <;> ring

/-- **Periodicity of the admissible rows at `σ∞`**: shifting `d` by a multiple of `|c|N` preserves membership. -/
theorem mem_image_shift (N : ℕ) (σ : SL(2, ℤ)) (c d j : ℤ) :
    (c, d + ((c.natAbs * N : ℕ) : ℤ) * j) ∈ rowMul σ '' adm N ↔ (c, d) ∈ rowMul σ '' adm N := by
  rw [mem_image_iff, mem_image_iff, rowMul_add_shift]
  set q := rowMul σ⁻¹ (c, d)
  set t : ℤ := ((c.natAbs * N : ℕ) : ℤ) * j
  have ht : t = (c.natAbs : ℤ) * (N * j) := by simp only [t]; push_cast; ring
  have hNt : (N : ℤ) ∣ t := ⟨(c.natAbs : ℤ) * j, by rw [ht]; ring⟩
  have hct : c ∣ t := by
    have : c ∣ (c.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact self_dvd_abs c
    rw [ht]; exact dvd_mul_of_dvd_left this _
  have hcop : IsCoprime (q.1 + t * (σ⁻¹ : SL(2, ℤ)) 1 0) (q.2 + t * (σ⁻¹ : SL(2, ℤ)) 1 1) ↔ IsCoprime q.1 q.2 := by
    have e := rowMul_add_shift σ⁻¹ c d t
    constructor
    · intro h
      have h1 : IsCoprime (rowMul σ⁻¹ (c, d + t)).1 (rowMul σ⁻¹ (c, d + t)).2 := by rw [e]; exact h
      have h2 := isCoprime_rowMul σ h1
      rw [show rowMul σ (rowMul σ⁻¹ (c, d + t)) = (c, d + t) by rw [rowMul_mul, inv_mul_cancel, rowMul_one]] at h2
      obtain ⟨k, hk⟩ := hct
      have h3 : IsCoprime c d := by
        have := h2; simp only at this; rw [hk] at this
        rw [show d = d + c * k + c * (-k) by ring]
        exact (IsCoprime.add_mul_left_right this _)
      exact isCoprime_rowMul σ⁻¹ h3
    · intro h
      have h2 := isCoprime_rowMul σ h
      simp only [q] at h2
      rw [show rowMul σ (rowMul σ⁻¹ (c, d)) = (c, d) by rw [rowMul_mul, inv_mul_cancel, rowMul_one]] at h2
      obtain ⟨k, hk⟩ := hct
      have h3 : IsCoprime c (d + t) := by
        simp only at h2; rw [hk]; exact h2.add_mul_left_right k
      have := isCoprime_rowMul σ⁻¹ (p := (c, d + t)) h3
      rw [e] at this; exact this
  simp only [adm, Set.mem_setOf_eq]
  have hmod1 : (N : ℤ) ∣ q.1 + t * (σ⁻¹ : SL(2, ℤ)) 1 0 ↔ (N : ℤ) ∣ q.1 :=
    (dvd_add_left (dvd_mul_of_dvd_left hNt _))
  have hmod2 : (((q.2 + t * (σ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = 1) ↔ ((q.2 : ZMod N) = 1) := by
    have : ((t : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNt
    push_cast; rw [this, zero_mul, add_zero]
  rw [hmod1, hmod2, hcop]

/-- Integrals over the period translates `[a + jT, a + (j+1)T]` sum to the full integral. -/
theorem hasSum_translates {f : ℝ → ℂ} (hf : Integrable f) {T : ℝ} (hT : 0 < T) (a : ℝ) :
    HasSum (fun j : ℤ => ∫ x in (0 : ℝ)..T, f (x + a + j * T)) (∫ x, f x) := by
  set g : ℝ → ℂ := fun u => (T : ℂ) * f (u * T + a)
  have hg : Integrable g := by
    have h1 : Integrable (fun u => f (u + a)) := hf.comp_add_right a
    have h2 : Integrable (fun u => f (u * T + a)) := by
      have := h1.comp_mul_right' hT.ne'
      simpa using this
    exact h2.const_mul _
  have hint : ∫ u, g u = ∫ x, f x := by
    simp only [g]
    rw [integral_const_mul, Measure.integral_comp_mul_right (fun v => f (v + a)) T, integral_add_right_eq_self]
    rw [abs_of_pos (inv_pos.mpr hT)]
    have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    rw [Complex.real_smul]; push_cast
    field_simp
  have h := hg.hasSum_intervalIntegral_comp_add_int
  rw [hint] at h
  refine h.congr_fun (fun j => ?_)
  simp only [g]
  rw [intervalIntegral.integral_const_mul]
  have := intervalIntegral.integral_comp_mul_right (a := 0) (b := 1) (fun x => f (x + a + j * T)) hT.ne'
  simp only [zero_mul, one_mul] at this
  have e : (∫ x in (0 : ℝ)..1, f ((x + j) * T + a)) = ∫ x in (0 : ℝ)..1, f (x * T + a + j * T) := by
    apply intervalIntegral.integral_congr; intro x _; simp only; congr 1; ring
  have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [e, this, Complex.real_smul]
  push_cast
  field_simp

end GaloisForLFunctions.RHTower.SelbergEisensteinCuspRows

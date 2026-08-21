/-
# Approximating a phase by a grid angle

The unit circle is `2π`-periodic and `1`-Lipschitz in its angle, so a grid of `m` equally spaced
angles approximates every phase to within `2π/m`, whatever real angle is presented: reduce the
angle modulo `2π`, round down to the grid, and use periodicity to identify the rounded grid point
with a grid index in `Fin m`.  Products of unit-modulus numbers telescope, so a word of `N` such
approximations costs at most `N` times the single-gate error.

Main results:
* `norm_exp_mul_I_sub_one_le`, `norm_exp_sub_exp_le` — the circle is `1`-Lipschitz in its angle.
* `norm_prod_sub_prod_le` — telescoping for unit-modulus factors.
* `gridAngle`, `exists_gridIndex` — **the grid approximation of an arbitrary phase**.
-/
import Mathlib

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The circle is `1`-Lipschitz in its angle at the identity. -/
theorem norm_exp_mul_I_sub_one_le (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ≤ |t| := by
  have hexp : Complex.exp ((t : ℂ) * Complex.I) - 1
      = ((Real.cos t - 1 : ℝ) : ℂ) + ((Real.sin t : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I]
    push_cast
    ring
  rw [hexp]
  have hnorm : ‖((Real.cos t - 1 : ℝ) : ℂ) + ((Real.sin t : ℝ) : ℂ) * Complex.I‖
      = Real.sqrt ((Real.cos t - 1) ^ 2 + Real.sin t ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hnorm]
  have hid : (Real.cos t - 1) ^ 2 + Real.sin t ^ 2 = 2 - 2 * Real.cos t := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hhalf : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    have := Real.cos_two_mul_eq_one_sub (t / 2)
    rw [show 2 * (t / 2) = t by ring] at this
    exact this
  rw [hid, hhalf]
  have h4 : (2 : ℝ) - 2 * (1 - 2 * Real.sin (t / 2) ^ 2) = (2 * Real.sin (t / 2)) ^ 2 := by ring
  rw [h4, Real.sqrt_sq_eq_abs, abs_mul]
  have hs := Real.abs_sin_le_abs (x := t / 2)
  have htwo : |(2:ℝ)| = 2 := by norm_num
  rw [htwo]
  have habs : |t / 2| = |t| / 2 := by
    rw [abs_div]
    norm_num
  rw [habs] at hs
  linarith

/-- **The circle is `1`-Lipschitz in its angle.** -/
theorem norm_exp_sub_exp_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have hfac : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)
      = Complex.exp ((b : ℂ) * Complex.I) *
        (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [hfac, norm_mul, Complex.norm_exp]
  have hre : (((b : ℂ) * Complex.I).re) = 0 := by simp
  rw [hre, Real.exp_zero, one_mul]
  exact norm_exp_mul_I_sub_one_le (a - b)

theorem norm_prod_map_eq_one {ι : Type*} (a : ι → ℂ) (ha : ∀ i, ‖a i‖ = 1) :
    ∀ l : List ι, ‖(l.map a).prod‖ = 1
  | [] => by simp
  | i :: l => by
      rw [List.map_cons, List.prod_cons, norm_mul, ha i, one_mul]
      exact norm_prod_map_eq_one a ha l

/-- **Telescoping for unit-modulus factors.** -/
theorem norm_prod_sub_prod_le {ι : Type*} :
    ∀ (l : List ι) (a b : ι → ℂ), (∀ i, ‖a i‖ = 1) → (∀ i, ‖b i‖ = 1) →
      ‖(l.map a).prod - (l.map b).prod‖ ≤ (l.map fun i => ‖a i - b i‖).sum
  | [], _, _, _, _ => by simp
  | i :: l, a, b, ha, hb => by
      have hih := norm_prod_sub_prod_le l a b ha hb
      have hsplit : (List.map a (i :: l)).prod - (List.map b (i :: l)).prod
          = (a i - b i) * (List.map a l).prod
            + b i * ((List.map a l).prod - (List.map b l).prod) := by
        simp only [List.map_cons, List.prod_cons]
        ring
      have hprodA : ‖(List.map a l).prod‖ = 1 := norm_prod_map_eq_one a ha l
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, hprodA, mul_one, hb i, one_mul]
      simp only [List.map_cons, List.sum_cons]
      linarith [hih]

/-- The `j`-th of `m` equally spaced angles. -/
def gridAngle (m : ℕ) (j : Fin m) : ℝ := 2 * Real.pi * (j : ℕ) / m

/-- **Grid approximation.**  Every phase is matched to within `2π/m` by one of the `m` grid angles,
after the sign `g = ±1` is applied. -/
theorem exists_gridIndex {m : ℕ} (hm : 0 < m) (alpha : ℝ) :
    ∃ j : Fin m, ∀ g : ℝ, |g| = 1 →
      ‖Complex.exp ((-(alpha * g) : ℝ) * Complex.I)
        - Complex.exp ((-(gridAngle m j * g) : ℝ) * Complex.I)‖ ≤ 2 * Real.pi / m := by
  classical
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨q, hqdef⟩ : ∃ q : ℤ, q = ⌊alpha * (m : ℝ) / (2 * Real.pi)⌋ := ⟨_, rfl⟩
  have hmne : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hjlt : (q % (m : ℤ)).toNat < m := by
    have h0 : 0 ≤ q % (m : ℤ) := Int.emod_nonneg q hmne
    have h1 : q % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos q (by exact_mod_cast hm)
    omega
  refine ⟨⟨(q % (m : ℤ)).toNat, hjlt⟩, ?_⟩
  intro g hg
  -- the grid angle of the chosen index differs from `2πq/m` by a multiple of `2π`
  obtain ⟨kk, hkk⟩ : ∃ kk : ℤ, (q : ℝ) = ((q % (m : ℤ)).toNat : ℝ) + (m : ℝ) * kk := by
    refine ⟨q / (m : ℤ), ?_⟩
    have h0 : 0 ≤ q % (m : ℤ) := Int.emod_nonneg q hmne
    have hcast : (((q % (m : ℤ)).toNat : ℤ)) = q % (m : ℤ) := Int.toNat_of_nonneg h0
    have hme := Int.emod_add_mul_ediv q (m : ℤ)
    have hz : q = ((q % (m : ℤ)).toNat : ℤ) + (m : ℤ) * (q / (m : ℤ)) := by
      rw [hcast]
      linarith [hme]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hz
  obtain ⟨beta, hbetadef⟩ : ∃ beta : ℝ, beta = 2 * Real.pi * (q : ℝ) / (m : ℝ) := ⟨_, rfl⟩
  have hgrid : gridAngle m ⟨(q % (m : ℤ)).toNat, hjlt⟩ = beta - 2 * Real.pi * kk := by
    rw [gridAngle, hbetadef, hkk]
    field_simp
    ring
  have hclose : |alpha - beta| ≤ 2 * Real.pi / m := by
    have ht : alpha - beta
        = (2 * Real.pi / (m : ℝ)) * (alpha * (m : ℝ) / (2 * Real.pi) - (q : ℝ)) := by
      rw [hbetadef]
      field_simp
    rw [ht, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi / (m : ℝ))]
    have hfl : (q : ℝ) ≤ alpha * (m : ℝ) / (2 * Real.pi) := by
      rw [hqdef]
      exact Int.floor_le _
    have hfl' : alpha * (m : ℝ) / (2 * Real.pi) < (q : ℝ) + 1 := by
      rw [hqdef]
      exact Int.lt_floor_add_one _
    have habs : |alpha * (m : ℝ) / (2 * Real.pi) - (q : ℝ)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    nlinarith [habs, (by positivity : (0:ℝ) ≤ 2 * Real.pi / (m : ℝ))]
  -- periodicity
  have hper : Complex.exp ((-(gridAngle m ⟨(q % (m : ℤ)).toNat, hjlt⟩ * g) : ℝ) * Complex.I)
      = Complex.exp ((-(beta * g) : ℝ) * Complex.I) := by
    rw [hgrid]
    have hgint : ∃ z : ℤ, (g : ℝ) = (z : ℝ) := by
      rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hg with h | h
      · exact ⟨1, by rw [h]; norm_num⟩
      · exact ⟨-1, by rw [h]; norm_num⟩
    obtain ⟨z, hz⟩ := hgint
    have hsplit : ((-((beta - 2 * Real.pi * kk) * g) : ℝ) : ℂ) * Complex.I
        = ((-(beta * g) : ℝ) : ℂ) * Complex.I + ((kk * z : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      rw [hz]
      push_cast
      ring
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hper]
  refine le_trans (norm_exp_sub_exp_le (-(alpha * g)) (-(beta * g))) ?_
  have habs : |(-(alpha * g)) - (-(beta * g))| = |alpha - beta| := by
    rw [show (-(alpha * g)) - (-(beta * g)) = (alpha - beta) * (-g) by ring, abs_mul, abs_neg, hg,
      mul_one]
  rw [habs]
  exact hclose

end GaloisForLFunctions.HTGeometry

end

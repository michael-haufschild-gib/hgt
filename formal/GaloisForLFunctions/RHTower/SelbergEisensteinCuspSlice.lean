import GaloisForLFunctions.RHTower.SelbergEisensteinCuspRows
import GaloisForLFunctions.RHTower.SelbergPoincareKernel

open Complex MeasureTheory UpperHalfPlane
open scoped FourierTransform MatrixGroups

/-!
# The `c`-slices of the constant term of `E_∞` at the cusp `σ∞`

For `c ≠ 0` the row summand is `(c²)^{-s} ker_{0,y,s}(x + d/c)` (`esumxy_eq`). Splitting `d = r + |c|N j`, admissibility
at `σ∞` depends only on `r` (`Gc_eq`), and the translates of `[0, N]` tile the line (`hasSum_translates_sign`), so
`Σ_d ∫_0^N (row summand) dx = (c²)^{-s} · count_σ(c) · ∫_ℝ ker₀`, where `count_σ(c)` is the number of admissible
residues `d mod |c|N` (`hasSum_Gc`). Absolute convergence comes from the same tiling applied to `|ker₀|`.
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinCuspSlice
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergEisensteinCusp
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspRows GaloisForLFunctions.RHTower.SelbergPoincareFourier

/-- The row summand at the point `x + iy`. -/
noncomputable def esumxy (s : ℂ) (y x : ℝ) (p : ℤ × ℤ) : ℂ :=
  ((y / ((p.1 * x + p.2) ^ 2 + (p.1 * y) ^ 2) : ℝ) : ℂ) ^ s

theorem ker0_eq (y : ℝ) (hy : 0 < y) (s : ℂ) (x : ℝ) : ker 0 y s x = ((wt y x : ℝ) : ℂ) ^ s := by
  unfold ker
  rw [cpow_def_of_ne_zero (by exact_mod_cast (wt_pos hy x).ne'), ← ofReal_log (wt_pos hy x).le]
  simp [mul_comm]

/-- For `c ≠ 0`: `(y/|cz+d|²)^s = (c²)^{-s} ker_{0,y,s}(x + d/c)`. -/
theorem esumxy_eq {y : ℝ} (hy : 0 < y) (s : ℂ) (x : ℝ) {c : ℤ} (hc : c ≠ 0) (d : ℤ) :
    esumxy s y x (c, d) = (((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * ker 0 y s (x + d / c) := by
  rw [ker0_eq y hy]
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hc2 : (0 : ℝ) < (c : ℝ) ^ 2 := by positivity
  have hw := wt_pos hy (x + d / c)
  have e : y / (((c : ℝ) * x + d) ^ 2 + ((c : ℝ) * y) ^ 2) = ((c : ℝ) ^ 2)⁻¹ * wt y (x + d / c) := by
    unfold wt; field_simp
  unfold esumxy
  simp only
  rw [e, ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) hw.le, ofReal_inv, inv_cpow _ _
    (by rw [Complex.arg_ofReal_of_nonneg hc2.le]; exact Real.pi_ne_zero.symm), cpow_neg]

variable (N : ℕ) [NeZero N] (σ : SL(2, ℤ))

/-- The one-period integral of the row summand. -/
noncomputable def Gc (s : ℂ) (y : ℝ) (c d : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..N, (rowMul σ '' adm N).indicator (esumxy s y x) (c, d)

omit [NeZero N] in
theorem Gc_eq {s : ℂ} {y : ℝ} (hy : 0 < y) {c : ℤ} (hc : c ≠ 0) (r j : ℤ) :
    Gc N σ s y c (r + ((c.natAbs * N : ℕ) : ℤ) * j) =
      (rowMul σ '' adm N).indicator (fun _ => (((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s)) (c, r) *
        ∫ x in (0 : ℝ)..N, ker 0 y s (x + r / c + ((c.sign * j : ℤ) : ℝ) * N) := by
  unfold Gc
  by_cases hmem : (c, r) ∈ rowMul σ '' adm N
  · have hmem' := (mem_image_shift N σ c r j).mpr hmem
    rw [Set.indicator_of_mem hmem, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    simp only
    rw [Set.indicator_of_mem hmem', esumxy_eq hy s x hc, arg_shift N hc]
    congr 3; ring
  · have hmem' : (c, r + ((c.natAbs * N : ℕ) : ℤ) * j) ∉ rowMul σ '' adm N :=
      fun h => hmem ((mem_image_shift N σ c r j).mp h)
    rw [Set.indicator_of_notMem hmem, zero_mul]
    have : ∀ x : ℝ, (rowMul σ '' adm N).indicator (esumxy s y x) (c, r + ((c.natAbs * N : ℕ) : ℤ) * j) = 0 :=
      fun x => Set.indicator_of_notMem hmem' _
    simp only [this, intervalIntegral.integral_zero]

/-- Sum over signed period translates. -/
theorem hasSum_translates_sign {f : ℝ → ℂ} (hf : Integrable f) {c : ℤ} (hc : c ≠ 0) (a : ℝ) :
    HasSum (fun j : ℤ => ∫ x in (0 : ℝ)..N, f (x + a + ((c.sign * j : ℤ) : ℝ) * N)) (∫ x, f x) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h := hasSum_translates hf hN a
  rcases lt_or_gt_of_ne hc with hlt | hgt
  · rw [Int.sign_eq_neg_one_of_neg hlt]
    have := (Equiv.neg ℤ).hasSum_iff.mpr h
    refine this.congr_fun (fun j => ?_)
    simp
  · rw [Int.sign_eq_one_of_pos hgt]
    simpa using h

/-- The number of admissible residues `d mod |c|N` at `σ∞`. -/
noncomputable def countσ (c : ℤ) : ℕ := by
  classical
  exact ((Finset.range (c.natAbs * N)).filter (fun r : ℕ => (c, (r : ℤ)) ∈ rowMul σ '' adm N)).card

/-- **The `c`-slice of the constant term at `σ∞`**: `Σ_d ∫_0^N (row summand) = (c²)^{-s} · count_σ(c) · ∫_ℝ ker₀`. -/
theorem hasSum_Gc {s : ℂ} (hs : 1 / 2 < s.re) {y : ℝ} (hy : 0 < y) {c : ℤ} (hc : c ≠ 0) :
    HasSum (Gc N σ s y c) ((((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * (countσ N σ c : ℂ) * ∫ x, ker 0 y s x) := by
  classical
  have hK : 0 < c.natAbs * N := Nat.mul_pos (Int.natAbs_pos.mpr hc) (Nat.pos_of_ne_zero (NeZero.ne N))
  set K := c.natAbs * N
  set e := resEquiv K hK
  have hker := integrable_ker (β := 0) le_rfl hy hs
  set ind : ℕ → ℂ := fun r => (rowMul σ '' adm N).indicator (fun _ => (((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s)) (c, (r : ℤ))
  set I : ℕ → ℤ → ℂ := fun r j => ∫ x in (0 : ℝ)..N, ker 0 y s (x + (r : ℤ) / c + ((c.sign * j : ℤ) : ℝ) * N)
  have hGe : ∀ p : Fin K × ℤ, Gc N σ s y c (e p) = ind p.1 * I p.1 p.2 := by
    intro p
    show Gc N σ s y c ((p.1 : ℤ) + K * p.2) = _
    have := Gc_eq N σ (s := s) hy hc (p.1 : ℤ) p.2
    exact this
  have hI : ∀ r : ℕ, HasSum (I r) (∫ x, ker 0 y s x) := fun r =>
    hasSum_translates_sign N hker hc ((r : ℤ) / (c : ℝ))
  -- absolute summability
  set J : ℕ → ℤ → ℝ := fun r j => ∫ x in (0 : ℝ)..N, ‖ker 0 y s (x + (r : ℤ) / c + ((c.sign * j : ℤ) : ℝ) * N)‖
  have hJ : ∀ r : ℕ, HasSum (J r) (∫ x, ‖ker 0 y s x‖) := by
    intro r
    have h := hasSum_translates_sign N (f := fun x => ((‖ker 0 y s x‖ : ℝ) : ℂ)) hker.norm.ofReal hc ((r : ℤ) / (c : ℝ))
    rw [integral_complex_ofReal] at h
    refine Complex.hasSum_ofReal.mp (h.congr_fun (fun j => ?_))
    simp only [J]; rw [intervalIntegral.integral_ofReal]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hbound : ∀ p : Fin K × ℤ, ‖Gc N σ s y c (e p)‖ ≤ ((c : ℝ) ^ 2) ^ (-s.re) * J p.1 p.2 := by
    intro p
    rw [hGe, norm_mul]
    have h1 : ‖ind p.1‖ ≤ ((c : ℝ) ^ 2) ^ (-s.re) := by
      simp only [ind]
      by_cases hm : (c, ((p.1 : ℕ) : ℤ)) ∈ rowMul σ '' adm N
      · rw [Set.indicator_of_mem hm, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]; simp
      · rw [Set.indicator_of_notMem hm, norm_zero]; positivity
    have h2 : ‖I p.1 p.2‖ ≤ J p.1 p.2 := intervalIntegral.norm_integral_le_integral_norm hN
    exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  have hsumB : Summable (fun p : Fin K × ℤ => ((c : ℝ) ^ 2) ^ (-s.re) * J p.1 p.2) := by
    have hJ0 : ∀ r j, 0 ≤ J r j := fun r j => intervalIntegral.integral_nonneg hN (fun x _ => norm_nonneg _)
    refine (summable_prod_of_nonneg (fun p => by have := hJ0 p.1 p.2; positivity)).mpr
      ⟨fun r => (hJ r).summable.mul_left _, (hasSum_fintype _).summable⟩
  have hsumG : Summable (Gc N σ s y c ∘ e) := Summable.of_norm_bounded hsumB hbound
  have htot : ∑' p : Fin K × ℤ, (Gc N σ s y c ∘ e) p =
      (((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * (countσ N σ c : ℂ) * ∫ x, ker 0 y s x := by
    rw [Summable.tsum_prod hsumG, tsum_fintype]
    have hr : ∀ r : Fin K, ∑' j, (Gc N σ s y c ∘ e) (r, j) = ind r * ∫ x, ker 0 y s x := by
      intro r
      simp only [Function.comp_apply, hGe]
      rw [tsum_mul_left, (hI r).tsum_eq]
    simp_rw [hr]
    rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun r => ind r) K]
    simp only [ind, countσ]
    rw [Finset.sum_congr rfl (fun r _ => Set.indicator_apply _ _ _), Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    ring
  rw [← htot]
  exact (e.hasSum_iff.mp hsumG.hasSum)

end GaloisForLFunctions.RHTower.SelbergEisensteinCuspSlice

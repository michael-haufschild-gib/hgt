import Mathlib

/-!
# One-point recession of a finite polynomial tuple

A finite family of complex polynomials, translated up the imaginary axis by `iT` and rescaled by
`(iT)^{-d}` with `d` the maximum degree, converges as `T → ∞` to its constant leading-coefficient
vector, which is nonzero.  Equivalently the upper functional-projective boundary of a finite
polynomial tuple is a single point: the boundary carrier `C[z] → C` has length one.

The mechanism is the elementary polynomial asymptotic `q(z + iT) / (iT)^d → coeff_d q` for
`deg q ≤ d`, obtained by expanding `q` over `range (d+1)` and taking the scaled limit termwise; the
`k`-th term contributes `coeff_k q · 1^k · 0^{d-k}`, which survives only at `k = d`.
-/

noncomputable section

open Filter Topology Polynomial Complex

namespace HTGeometry

private theorem tendsto_ItInv_zero :
    Tendsto (fun T : ℝ => (Complex.I * (T : ℂ))⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : (fun T : ℝ => ‖(Complex.I * (T : ℂ))⁻¹‖) = fun T : ℝ => |T|⁻¹ := by
    funext T
    rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [h]
  exact tendsto_inv_atTop_zero.comp tendsto_abs_atTop_atTop

private theorem tendsto_shift_mul_inv_one (z : ℂ) :
    Tendsto (fun T : ℝ => (z + Complex.I * (T : ℂ)) * (Complex.I * (T : ℂ))⁻¹) atTop (𝓝 1) := by
  have hlim : Tendsto (fun T : ℝ => z * (Complex.I * (T : ℂ))⁻¹ + 1) atTop (𝓝 1) := by
    simpa using (tendsto_ItInv_zero.const_mul z).add (tendsto_const_nhds (x := (1 : ℂ)))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (T : ℝ) ≠ 0)
  have hw : Complex.I * (T : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hT0
  field_simp

/-- Scaled translated evaluation of a polynomial selects its top coefficient:
`q(z + iT) / (iT)^d → coeff_d q` whenever `deg q ≤ d`. -/
theorem poly_scaled_translate_tendsto (q : Polynomial ℂ) (z : ℂ) {d : ℕ}
    (hd : q.natDegree ≤ d) :
    Tendsto (fun T : ℝ => q.eval (z + Complex.I * (T : ℂ)) / (Complex.I * (T : ℂ)) ^ d)
      atTop (𝓝 (q.coeff d)) := by
  set w : ℝ → ℂ := fun T => Complex.I * (T : ℂ) with hwdef
  have hinv := tendsto_ItInv_zero
  have hratio := tendsto_shift_mul_inv_one z
  have hterm : ∀ k ∈ Finset.range (d + 1),
      Tendsto (fun T : ℝ => q.coeff k * (((z + w T) * (w T)⁻¹) ^ k * ((w T)⁻¹) ^ (d - k)))
        atTop (𝓝 (if k = d then q.coeff d else 0)) := by
    intro k hk
    have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hmul := ((hratio.pow k).mul (hinv.pow (d - k))).const_mul (q.coeff k)
    have hval :
        q.coeff k * ((1 : ℂ) ^ k * (0 : ℂ) ^ (d - k)) = (if k = d then q.coeff d else 0) := by
      by_cases hkd : k = d
      · subst hkd; simp
      · have hdk : d - k ≠ 0 := by omega
        simp [hkd, zero_pow hdk]
    rw [hval] at hmul
    exact hmul
  have hsum := tendsto_finsetSum _ hterm
  rw [Finset.sum_ite_eq' (Finset.range (d + 1)) d (fun _ => q.coeff d)] at hsum
  simp only [Finset.mem_range, Nat.lt_succ_iff, le_refl, if_true] at hsum
  refine hsum.congr (fun T => ?_)
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.sum_div]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [hwdef]
  rw [div_eq_mul_inv, mul_pow, ← inv_pow, mul_assoc, ← pow_add,
    show k + (d - k) = d from by omega]
  ring

/-- One-point recession of a finite nonzero polynomial tuple.  With `d` the maximum degree, the
leading-coefficient vector is nonzero, and the tuple, translated by `iT` and rescaled by
`(iT)^{-d}`, converges to that constant vector.  This is the length-one boundary carrier
`C[z] → C`. -/
theorem finiteTuple_polynomial_onePoint_recession
    {r : ℕ} (p : Fin r → Polynomial ℂ) (hp : ∃ j, p j ≠ 0) :
    ∃ d : ℕ, (∃ j, (p j).coeff d ≠ 0) ∧
      ∀ (z : ℂ) (j : Fin r),
        Tendsto (fun T : ℝ => (p j).eval (z + Complex.I * (T : ℂ)) / (Complex.I * (T : ℂ)) ^ d)
          atTop (𝓝 ((p j).coeff d)) := by
  classical
  obtain ⟨j0, hj0⟩ := hp
  set d := Finset.univ.sup (fun j => (p j).natDegree) with hd
  refine ⟨d, ?_, fun z j =>
    poly_scaled_translate_tendsto (p j) z
      (Finset.le_sup (f := fun j => (p j).natDegree) (Finset.mem_univ j))⟩
  obtain ⟨jmax, -, hjmax⟩ :=
    Finset.exists_mem_eq_sup Finset.univ ⟨j0, Finset.mem_univ j0⟩ (fun j => (p j).natDegree)
  by_cases hj : p jmax = 0
  · have hd0 : d = 0 := by rw [hd, hjmax, hj, Polynomial.natDegree_zero]
    have hnd0 : (p j0).natDegree = 0 :=
      Nat.le_zero.mp (hd0 ▸ Finset.le_sup (f := fun j => (p j).natDegree) (Finset.mem_univ j0))
    refine ⟨j0, ?_⟩
    rw [hd0]
    have hlc : (p j0).coeff ((p j0).natDegree) ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hj0
    rwa [hnd0] at hlc
  · refine ⟨jmax, ?_⟩
    have hdeq : d = (p jmax).natDegree := hd.trans hjmax
    rw [hdeq]
    exact Polynomial.leadingCoeff_ne_zero.mpr hj

end HTGeometry

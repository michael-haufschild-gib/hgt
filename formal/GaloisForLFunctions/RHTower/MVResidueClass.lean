import Zeta23.MV.Final

/-!
# The Montgomery–Vaughan inequality on one residue class

Integers in a fixed residue class modulo `q` are `q` apart, so their logarithms are well spaced:
for distinct positive `n ≡ m (mod q)`,

`q / (n + q) ≤ |log n − log m|`

(`spacing_log_of_modEq`).  Feeding the spacings `δ_n = q/(n + q)` into the weighted Hilbert inequality
of Montgomery and Vaughan (`Zeta23.MV.mv_hilbert`) gives, for any finite set `S` of positive integers
in one residue class and complex weights `x`, `z`,

`‖∑_{n ≠ m ∈ S} x_n z̄_m / (log n − log m)‖ ≤ C (∑ ‖x_n‖² (n + q)/q)^{1/2} (∑ ‖z_n‖² (n + q)/q)^{1/2}`

(`mv_residueClass`), and its real cosine and sine forms with a common phase `c`
(`mv_real_residueClass`).  Compared with the unrestricted inequality, whose weights are `2n`, the weight
`n/q` is smaller by the factor `q`.  This factor makes character averages of Dirichlet
polynomials of length up to `q T` diagonal.
-/

open Complex ComplexConjugate

noncomputable section

namespace RHTower

/-- **Spacing on a residue class.**  For positive integers `n ≠ m` with `n ≡ m (mod q)`,
`q/(n + q) ≤ |log n − log m|`. -/
lemma spacing_log_of_modEq {q n m : ℕ} (hq : 0 < q) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≠ m)
    (hmod : n ≡ m [MOD q]) :
    (q : ℝ) / (n + q) ≤ |Real.log n - Real.log m| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  -- distinct members of a residue class are at least `q` apart
  have hgap : (q : ℝ) ≤ |(n : ℝ) - m| := by
    have hdvd : (q : ℤ) ∣ (m : ℤ) - n := (Nat.modEq_iff_dvd.mp hmod)
    have hne : (m : ℤ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm.symm)
    have hle : (q : ℤ) ≤ |(m : ℤ) - n| := Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
    have : (q : ℝ) ≤ |(m : ℝ) - n| := by exact_mod_cast hle
    rwa [abs_sub_comm] at this
  rcases lt_or_gt_of_ne hnm with h | h
  · -- n < m, so m ≥ n + q and log m − log n ≥ 1 − n/m = (m − n)/m ≥ q/(n + q)
    have hnm' : (n : ℝ) < m := by exact_mod_cast h
    have hmq : (n : ℝ) + q ≤ m := by
      rw [abs_of_neg (by linarith)] at hgap; linarith
    have hlog : 1 - ((m : ℝ) / n)⁻¹ ≤ Real.log ((m : ℝ) / n) :=
      Real.one_sub_inv_le_log_of_pos (by positivity)
    rw [inv_div, Real.log_div hm0.ne' hn0.ne'] at hlog
    have h2 : (q : ℝ) / (n + q) ≤ 1 - n / m := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 - (n : ℝ) / m) * (n + q) = (m - n) * (n + q) / m := by field_simp
      rw [this, le_div_iff₀ hm0]
      nlinarith
    rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.log_le_log hn0 hnm'.le])]
    linarith
  · -- m < n, so n ≥ m + q and log n − log m ≥ 1 − m/n = (n − m)/n ≥ q/n ≥ q/(n + q)
    have hmn' : (m : ℝ) < n := by exact_mod_cast h
    have hnq : (m : ℝ) + q ≤ n := by
      rw [abs_of_pos (by linarith)] at hgap; linarith
    have hlog : 1 - ((n : ℝ) / m)⁻¹ ≤ Real.log ((n : ℝ) / m) :=
      Real.one_sub_inv_le_log_of_pos (by positivity)
    rw [inv_div, Real.log_div hn0.ne' hm0.ne'] at hlog
    have h2 : (q : ℝ) / (n + q) ≤ 1 - m / n := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 - (m : ℝ) / n) * (n + q) = (n - m) * (n + q) / n := by field_simp
      rw [this, le_div_iff₀ hn0]
      nlinarith
    rw [abs_of_nonneg (by linarith [Real.log_le_log hm0 hmn'.le])]
    linarith

/-- **Montgomery–Vaughan on a residue class.**  For a finite set `S` of positive integers that are
pairwise congruent modulo `q > 0`, and complex weights `x`, `z`,
`‖∑_{n ≠ m} x_n z̄_m/(log n − log m)‖ ≤ C (∑ ‖x_n‖²(n+q)/q)^{1/2} (∑ ‖z_n‖²(n+q)/q)^{1/2}`,
with `C` the Montgomery–Vaughan constant. -/
theorem mv_residueClass {C : ℝ} (hMV : Zeta23.MVHilbert C) {q : ℕ} (hq : 0 < q) (S : Finset ℕ)
    (hpos : ∀ n ∈ S, 1 ≤ n) (hcong : ∀ n ∈ S, ∀ m ∈ S, n ≡ m [MOD q]) (x z : ℕ → ℂ) :
    ‖∑ n ∈ S, ∑ m ∈ S,
        (if n = m then (0:ℂ) else x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ))‖
      ≤ C * Real.sqrt (∑ n ∈ S, ‖x n‖ ^ 2 * ((n + q) / q))
          * Real.sqrt (∑ n ∈ S, ‖z n‖ ^ 2 * ((n + q) / q)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have key := hMV S (fun r : S => Real.log ((r:ℕ):ℝ)) (fun r : S => (q : ℝ) / (((r:ℕ):ℝ) + q))
    (fun r => x r) (fun r => z r) ?_ ?_ ?_
  · have e1 : (∑ r : S, ∑ s : S, if r = s then (0:ℂ) else
        x r * conj (z s) / ((Real.log ((r:ℕ):ℝ) - Real.log ((s:ℕ):ℝ) : ℝ) : ℂ))
        = ∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℂ) else
            x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ)) := by
      simp_rw [Subtype.ext_iff]
      rw [Finset.sum_coe_sort S (fun n => ∑ s : S, if n = (s:ℕ) then (0:ℂ) else
            x n * conj (z s) / ((Real.log n - Real.log ((s:ℕ):ℝ) : ℝ) : ℂ))]
      refine Finset.sum_congr rfl fun n _ => ?_
      exact Finset.sum_coe_sort S (fun m => if n = m then (0:ℂ) else
            x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ))
    have e2 : ∀ (w : ℕ → ℂ), (∑ r : S, ‖w r‖ ^ 2 / ((q : ℝ) / (((r:ℕ):ℝ) + q)))
        = ∑ n ∈ S, ‖w n‖ ^ 2 * ((n + q) / q) := by
      intro w
      rw [Finset.sum_coe_sort S (fun n => ‖w n‖ ^ 2 / ((q : ℝ) / ((n:ℝ) + q)))]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [div_div_eq_mul_div, mul_div_assoc]
    rw [e1, e2 x, e2 z] at key
    exact key
  · intro r s hrs
    apply Subtype.ext
    have hr : (0:ℝ) < ((r:ℕ):ℝ) := by exact_mod_cast hpos r r.2
    have hs : (0:ℝ) < ((s:ℕ):ℝ) := by exact_mod_cast hpos s s.2
    have : ((r:ℕ):ℝ) = ((s:ℕ):ℝ) :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr hr) (Set.mem_Ioi.mpr hs) hrs
    exact_mod_cast this
  · intro r
    have hr : (0:ℝ) ≤ ((r:ℕ):ℝ) := Nat.cast_nonneg _
    positivity
  · intro r s hrs
    exact spacing_log_of_modEq hq (hpos r r.2) (hpos s s.2) (fun h => hrs (Subtype.ext h))
      (hcong r r.2 s s.2)

/-- **Real form on a residue class.**  For real weights `u`, `v` and a real phase `c`, the cosine and
sine bilinear sums `∑_{n ≠ m} u_n v_m cos(c(y_n − y_m))/(y_n − y_m)` and its sine analogue
(`y_n = log n`) over a set pairwise congruent modulo `q` are bounded by
`C (∑ u_n²(n+q)/q)^{1/2} (∑ v_n²(n+q)/q)^{1/2}`. -/
theorem mv_real_residueClass {C : ℝ} (hMV : Zeta23.MVHilbert C) {q : ℕ} (hq : 0 < q)
    (S : Finset ℕ) (hpos : ∀ n ∈ S, 1 ≤ n) (hcong : ∀ n ∈ S, ∀ m ∈ S, n ≡ m [MOD q])
    (c : ℝ) (u v : ℕ → ℝ) :
    |∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℝ) else
        u n * v m * Real.cos (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m))|
      ≤ C * Real.sqrt (∑ n ∈ S, u n ^ 2 * ((n + q) / q))
          * Real.sqrt (∑ n ∈ S, v n ^ 2 * ((n + q) / q)) ∧
    |∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℝ) else
        u n * v m * Real.sin (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m))|
      ≤ C * Real.sqrt (∑ n ∈ S, u n ^ 2 * ((n + q) / q))
          * Real.sqrt (∑ n ∈ S, v n ^ 2 * ((n + q) / q)) := by
  set x : ℕ → ℂ := fun n => (u n : ℂ) * Complex.exp ((c * Real.log n : ℝ) * Complex.I) with hx
  set z : ℕ → ℂ := fun n => (v n : ℂ) * Complex.exp ((c * Real.log n : ℝ) * Complex.I) with hz
  have key := mv_residueClass hMV hq S hpos hcong x z
  have hnx : ∀ n, ‖x n‖ ^ 2 = u n ^ 2 := by
    intro n
    simp only [hx, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hnz : ∀ n, ‖z n‖ ^ 2 = v n ^ 2 := by
    intro n
    simp only [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  simp_rw [hnx, hnz] at key
  have hprod : ∀ n m, x n * conj (z m)
      = ((u n * v m : ℝ) : ℂ) * Complex.exp ((c * (Real.log n - Real.log m) : ℝ) * Complex.I) := by
    intro n m
    have harg : ((c * Real.log n : ℝ) : ℂ) * Complex.I
        + ((c * Real.log m : ℝ) : ℂ) * (starRingEnd ℂ) Complex.I
        = ((c * (Real.log n - Real.log m) : ℝ) : ℂ) * Complex.I := by
      rw [Complex.conj_I]; push_cast; ring
    simp only [hx, hz, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    rw [mul_mul_mul_comm, ← Complex.exp_add, harg]
    push_cast; ring
  have hre : (∑ n ∈ S, ∑ m ∈ S,
        (if n = m then (0:ℂ) else x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ))).re
      = ∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℝ) else
        u n * v m * Real.cos (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · simp
    · rw [hprod, Complex.div_ofReal_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have him : (∑ n ∈ S, ∑ m ∈ S,
        (if n = m then (0:ℂ) else x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ))).im
      = ∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℝ) else
        u n * v m * Real.sin (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) := by
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · simp
    · rw [hprod, Complex.div_ofReal_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  constructor
  · rw [← hre]; exact (Complex.abs_re_le_norm _).trans key
  · rw [← him]; exact (Complex.abs_im_le_norm _).trans key

end RHTower

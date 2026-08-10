import GaloisForLFunctions.HTGeometry.QGammaAnalytic
import GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemoryWitnesses

/-!
# Transcendence of `qᶻ` over `ℂ(z)`

No nonzero polynomial in `qᶻ` with rational-function coefficients vanishes identically: reading the
relation on the positive real axis, the lowest surviving power dominates because `q^{kx}` decays
faster than any polynomial grows.  This is the input that makes `z ↦ z`, `u ↦ qᶻ` a well-defined
embedding of the two-variable field `ℂ(z,u)` into the meromorphic germs.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

theorem neg_log_pos (q : RealEulerNome) : 0 < -Real.log q.val :=
  neg_pos.mpr (Real.log_neg q.pos q.lt_one)

theorem qrpow_eq_exp (q : RealEulerNome) (x : ℝ) :
    q.val ^ x = Real.exp (-((-Real.log q.val) * x)) := by
  rw [Real.rpow_def_of_pos q.pos]
  congr 1
  ring

/-- Polynomial growth loses against the geometric decay `q^x`. -/
theorem tendsto_pow_mul_qrpow (q : RealEulerNome) (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * q.val ^ x) atTop (𝓝 0) := by
  set L : ℝ := -Real.log q.val with hL_def
  have hL : 0 < L := neg_log_pos q
  have hbase : Tendsto (fun t : ℝ => t ^ k * Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  have hlin : Tendsto (fun x : ℝ => L * x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hL tendsto_id
  have hcomp : Tendsto (fun x : ℝ => (L * x) ^ k * Real.exp (-(L * x))) atTop (𝓝 0) :=
    hbase.comp hlin
  have hscaled := hcomp.const_mul (L ^ k)⁻¹
  rw [mul_zero] at hscaled
  refine hscaled.congr fun x => ?_
  have hLne : L ≠ 0 := ne_of_gt hL
  rw [qrpow_eq_exp q x, ← hL_def, mul_pow]
  field_simp

/-- The dominating polynomial of a complex polynomial loses against `q^x` as well. -/
theorem tendsto_normPoly_mul_qrpow (q : RealEulerNome) (P : Polynomial ℂ) :
    Tendsto (fun x : ℝ => (normPoly P).eval x * q.val ^ x) atTop (𝓝 0) := by
  have hsum : ∀ x : ℝ, (normPoly P).eval x * q.val ^ x
      = ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ * (x ^ k * q.val ^ x) := by
    intro x
    rw [normPoly, Polynomial.eval_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  have hterms : Tendsto (fun x : ℝ =>
      ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ * (x ^ k * q.val ^ x)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range (P.natDegree + 1))
      (f := fun k (x : ℝ) => ‖P.coeff k‖ * (x ^ k * q.val ^ x)) (a := fun _ => (0 : ℝ))
      (fun k _ => by
        have := (tendsto_pow_mul_qrpow q k).const_mul ‖P.coeff k‖
        rwa [mul_zero] at this)
    simpa using this
  exact hterms.congr fun x => (hsum x).symm

/-- **Transcendence of `qᶻ` over `ℂ(z)`.**  A nonzero polynomial combination of the powers of `qᶻ`
with polynomial coefficients cannot vanish on the positive real axis. -/
theorem exists_qcpow_combination_ne_zero (q : RealEulerNome) {n : ℕ} (c : ℕ → Polynomial ℂ)
    {i₀ : ℕ} (hi₀ : i₀ ≤ n) (hci₀ : c i₀ ≠ 0) (hmin : ∀ i < i₀, c i = 0) :
    ∃ x : ℝ, 1 ≤ x ∧
      ∑ i ∈ Finset.range (n + 1), (c i).eval ((x : ℝ) : ℂ) * (((q.val ^ x : ℝ) : ℂ)) ^ i ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  -- the lowest surviving coefficient tends to zero
  have hbound : ∀ x : ℝ, 1 ≤ x →
      ‖(c i₀).eval ((x : ℝ) : ℂ)‖
        ≤ (∑ i ∈ Finset.range (n + 1), (normPoly (c i)).eval x) * q.val ^ x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
    have hqx : (0 : ℝ) < q.val ^ x := Real.rpow_pos_of_pos q.pos x
    have hzero := hcon x hx
    -- split off the `i₀` term
    have hsplit : (c i₀).eval ((x : ℝ) : ℂ) * (((q.val ^ x : ℝ) : ℂ)) ^ i₀
        = -∑ i ∈ (Finset.range (n + 1)).erase i₀,
            (c i).eval ((x : ℝ) : ℂ) * (((q.val ^ x : ℝ) : ℂ)) ^ i := by
      have hmem : i₀ ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      have := Finset.add_sum_erase _
        (fun i => (c i).eval ((x : ℝ) : ℂ) * (((q.val ^ x : ℝ) : ℂ)) ^ i) hmem
      rw [← this] at hzero
      linear_combination hzero
    -- bound each surviving term
    have hqxpow : ∀ i : ℕ, ‖(((q.val ^ x : ℝ) : ℂ)) ^ i‖ = (q.val ^ x) ^ i := by
      intro i
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqx]
    have hterm : ∀ i ∈ (Finset.range (n + 1)).erase i₀,
        ‖(c i).eval ((x : ℝ) : ℂ) * (((q.val ^ x : ℝ) : ℂ)) ^ i‖
          ≤ (normPoly (c i)).eval x * ((q.val ^ x) ^ (i₀ + 1)) := by
      intro i hi
      have hine : i ≠ i₀ := Finset.ne_of_mem_erase hi
      rcases lt_or_gt_of_ne hine with hlt | hlt
      · -- `i < i₀`: the coefficient vanishes
        have hc0 : (c i).eval ((x : ℝ) : ℂ) = 0 := by rw [hmin i hlt]; simp
        rw [hc0, zero_mul, norm_zero]
        exact mul_nonneg (le_trans (norm_nonneg _) (norm_eval_le_normPoly (c i) hx0))
          (by positivity)
      · -- `i > i₀`: the extra powers only help
        have hpow : (q.val ^ x) ^ i ≤ (q.val ^ x) ^ (i₀ + 1) := by
          refine pow_le_pow_of_le_one (le_of_lt hqx) ?_ (by omega)
          exact Real.rpow_le_one q.pos.le q.lt_one.le hx0
        rw [norm_mul, hqxpow]
        refine mul_le_mul (norm_eval_le_normPoly (c i) hx0) hpow (by positivity) ?_
        exact le_trans (norm_nonneg _) (norm_eval_le_normPoly (c i) hx0)
    have hsum := norm_sum_le ((Finset.range (n + 1)).erase i₀)
      (fun i => (c i).eval ((x : ℝ) : ℂ) * (((q.val ^ x : ℝ) : ℂ)) ^ i)
    have hle : ‖(c i₀).eval ((x : ℝ) : ℂ)‖ * (q.val ^ x) ^ i₀
        ≤ (∑ i ∈ Finset.range (n + 1), (normPoly (c i)).eval x) * ((q.val ^ x) ^ (i₀ + 1)) := by
      have hstart : ‖(c i₀).eval ((x : ℝ) : ℂ)‖ * (q.val ^ x) ^ i₀
          = ‖(c i₀).eval ((x : ℝ) : ℂ) * (((q.val ^ x : ℝ) : ℂ)) ^ i₀‖ := by
        rw [norm_mul, hqxpow]
      rw [hstart, hsplit, norm_neg]
      refine le_trans hsum ?_
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
      intro i _ _
      exact le_trans (norm_nonneg _) (norm_eval_le_normPoly (c i) hx0)
    have hpowpos : (0 : ℝ) < (q.val ^ x) ^ i₀ := pow_pos hqx i₀
    rw [pow_succ] at hle
    nlinarith [hle, hpowpos]
  -- hence the lowest coefficient is zero
  have hmaj : Tendsto (fun x : ℝ =>
      (∑ i ∈ Finset.range (n + 1), (normPoly (c i)).eval x) * q.val ^ x) atTop (𝓝 0) := by
    have hfun : ∀ x : ℝ, (∑ i ∈ Finset.range (n + 1), (normPoly (c i)).eval x) * q.val ^ x
        = ∑ i ∈ Finset.range (n + 1), (normPoly (c i)).eval x * q.val ^ x := by
      intro x
      rw [Finset.sum_mul]
    have := tendsto_finsetSum (Finset.range (n + 1))
      (f := fun i (x : ℝ) => (normPoly (c i)).eval x * q.val ^ x) (a := fun _ => (0 : ℝ))
      (fun i _ => tendsto_normPoly_mul_qrpow q (c i))
    simpa [hfun] using this
  have hev : ∀ᶠ x : ℝ in atTop, ‖(c i₀).eval ((x : ℝ) : ℂ)‖
      ≤ (∑ i ∈ Finset.range (n + 1), (normPoly (c i)).eval x) * q.val ^ x := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    exact hbound x hx
  have hlim : Tendsto (fun x : ℝ => (c i₀).eval ((x : ℝ) : ℂ)) atTop (𝓝 0) :=
    squeeze_zero_norm' hev hmaj
  exact hci₀ (eq_zero_of_tendsto_zero_atTop_real hlim)

end

end GaloisForLFunctions.HTGeometry

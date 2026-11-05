import GaloisForLFunctions.FiniteFreeProbability.EulerProductDriftIsForced

/-!
# The pole side of an Euler product has no Hermite–Biehler normalization

A nonnegative exponential mixture `F(w) = Σ_k a_k e^{i(c − λ_k)w}`, taken coefficientwise as a
formal power series in `w`, has reversed Jensen polynomials with

`R_d(F)(ix) = i^d Σ_k a_k (x + c − λ_k)^d`.

**Theorem.** If all frequencies are `≥ m` and some frequency `λ_K` with `a_K > 0` exceeds
`2c − m`, then for all large odd `d` the polynomial `R_d(F)` has a root in the open upper
half-plane. At `x = 0` the far frequency dominates, `Σ_k a_k (c − λ_k)^d < 0`; the leading
coefficient `Σ_k a_k` is positive, so the odd-degree real function `x ↦ Σ_k a_k (x + c − λ_k)^d`
vanishes at some `x > 0`.

For the pole piece `e^{icw}(1 − q e^{−iℓw})^{−1} = Σ_k q^k e^{i(c − kℓ)w}` the frequencies `kℓ`
are unbounded, so **no translation stabilizes it**, in contrast with the zero side
`1 − q e^{−iℓw}`, which is stabilized exactly by the translation `(log p)/2`.
-/

open Polynomial Filter Topology Complex

namespace FiniteFreeProbability

noncomputable section

/-! ## Exponential mixtures -/

/-- The exponential mixture `Σ_k a_k e^{i(c − λ_k)w}`, coefficientwise. -/
def seriesMixture (a lam : ℕ → ℝ) (c : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk fun i =>
    ∑' k, (a k : ℂ) * PowerSeries.coeff i (expSeries (I * ((c - lam k : ℝ) : ℂ)))

/-- The real moments `Σ_k a_k (c − λ_k)^i / i!`. -/
def mixtureMoment (a lam : ℕ → ℝ) (c : ℝ) (i : ℕ) : ℝ :=
  ∑' k, a k * (c - lam k) ^ i / (i.factorial : ℝ)

theorem coeff_expSeries (z : ℂ) (i : ℕ) :
    PowerSeries.coeff i (expSeries z) = z ^ i / (i.factorial : ℂ) := by
  rw [expSeries, PowerSeries.coeff_mk]

theorem coeff_seriesMixture (a lam : ℕ → ℝ) (c : ℝ) (i : ℕ) :
    PowerSeries.coeff i (seriesMixture a lam c) = I ^ i * (mixtureMoment a lam c i : ℂ) := by
  rw [seriesMixture, PowerSeries.coeff_mk, mixtureMoment, Complex.ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [coeff_expSeries, mul_pow]
  push_cast
  ring

theorem summable_seriesMixture_term {a lam : ℕ → ℝ} {c : ℝ}
    (hsum : ∀ i, Summable fun k => a k * (c - lam k) ^ i) (i : ℕ) :
    Summable fun k => (a k : ℂ) * PowerSeries.coeff i (expSeries (I * ((c - lam k : ℝ) : ℂ))) :=
  ((Complex.summable_ofReal.2 (hsum i)).mul_right (I ^ i / (i.factorial : ℂ))).congr fun k => by
    rw [coeff_expSeries, mul_pow]; push_cast; ring

/-- Multiplying by `e^{ic'w}` translates the mixture. -/
theorem expSeries_mul_seriesMixture {a lam : ℕ → ℝ} {c : ℝ}
    (hsum : ∀ i, Summable fun k => a k * (c - lam k) ^ i) (c' : ℝ) :
    expSeries (I * c') * seriesMixture a lam c = seriesMixture a lam (c + c') := by
  ext n
  rw [PowerSeries.coeff_mul]
  simp only [seriesMixture, PowerSeries.coeff_mk]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (f := fun (p : ℕ × ℕ) (k : ℕ) =>
      PowerSeries.coeff p.1 (expSeries (I * (c' : ℂ))) *
        ((a k : ℂ) * PowerSeries.coeff p.2 (expSeries (I * ((c - lam k : ℝ) : ℂ)))))
    fun p _ => (summable_seriesMixture_term hsum p.2).mul_left _]
  refine tsum_congr fun k => ?_
  simp_rw [mul_left_comm _ (a k : ℂ)]
  rw [← Finset.mul_sum, ← PowerSeries.coeff_mul, expSeries_add]
  congr 3
  push_cast; ring

/-! ## The real sign argument -/

/-- A finite sum `Σ_{i ≤ d} b_i x^{d−i}` with `b_0 > 0` is positive at some `x > 0`. -/
theorem exists_pos_sum_range_pow {d : ℕ} (hd : 1 ≤ d) (b : ℕ → ℝ) (hb : 0 < b 0) :
    ∃ x : ℝ, 0 < x ∧ 0 < ∑ i ∈ Finset.range (d + 1), b i * x ^ (d - i) := by
  set B := ∑ i ∈ Finset.range d, |b (i + 1)|
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => abs_nonneg _
  set x := 1 + B / b 0
  have hx1 : 1 ≤ x := by have := div_nonneg hB hb.le; simp only [x]; linarith
  refine ⟨x, by linarith, ?_⟩
  rw [Finset.sum_range_succ', Nat.sub_zero]
  have hrest : -(B * x ^ (d - 1)) ≤ ∑ i ∈ Finset.range d, b (i + 1) * x ^ (d - (i + 1)) := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    have hpow : x ^ (d - (i + 1)) ≤ x ^ (d - 1) := pow_le_pow_right₀ hx1 (by omega)
    have h1 := mul_nonneg (by linarith [neg_abs_le (b (i + 1))] : 0 ≤ b (i + 1) + |b (i + 1)|)
      (by positivity : (0 : ℝ) ≤ x ^ (d - (i + 1)))
    have h2 := mul_nonneg (abs_nonneg (b (i + 1))) (sub_nonneg.2 hpow)
    linarith
  have hxd : x ^ d = x * x ^ (d - 1) := by rw [← pow_succ', Nat.sub_add_cancel hd]
  have hbx : b 0 * x = b 0 + B := by simp only [x]; field_simp
  have hpd : 0 < b 0 * x ^ (d - 1) := mul_pos hb (by positivity)
  rw [hxd, ← mul_assoc, hbx]
  linarith

/-- On the imaginary axis, a power series with coefficients `i^k r_k` (`r_k` real) has reversed
Jensen polynomials that are real up to the factor `i^d`. -/
theorem eval_jensenRev_I_mul_of_coeff {F : PowerSeries ℂ} (r : ℕ → ℝ)
    (hF : ∀ i, PowerSeries.coeff i F = I ^ i * (r i : ℂ)) (x : ℝ) (d : ℕ) :
    (jensenRev d F).eval (I * x) =
      I ^ d * ((∑ i ∈ Finset.range (d + 1), r i * (d.descFactorial i : ℝ) * x ^ (d - i) : ℝ) : ℂ) := by
  rw [jensenRev_eq_sum, eval_finsetSum, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [eval_mul, eval_C, eval_pow, eval_X, hF, mul_pow,
    show I ^ d = I ^ i * I ^ (d - i) by rw [← pow_add, Nat.add_sub_cancel' hi']]
  push_cast
  ring

/-- **Upper roots from a sign change of the moments.** If `F` has coefficients `i^k r_k` with real
`r_k`, `r_0 > 0` and `r_d < 0`, then `R_d(F)` has a root `iy` with `y > 0`: the real function
`y ↦ Σ_k r_k d!/(d−k)! y^{d−k}` is `d! r_d < 0` at `0` and positive for large `y`. -/
theorem exists_upper_root_of_coeff {F : PowerSeries ℂ} (r : ℕ → ℝ)
    (hF : ∀ i, PowerSeries.coeff i F = I ^ i * (r i : ℂ)) {d : ℕ} (hd : 1 ≤ d) (h0 : 0 < r 0)
    (hneg : r d < 0) : ∃ x : ℂ, (jensenRev d F).IsRoot x ∧ 0 < x.im := by
  set φ : ℝ → ℝ := fun x => ∑ i ∈ Finset.range (d + 1), r i * (d.descFactorial i : ℝ) * x ^ (d - i)
  have hφ0 : φ 0 < 0 := by
    simp only [φ]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero fun i hi => by
      rw [zero_pow (by have := Finset.mem_range.1 hi; omega), mul_zero], zero_add, Nat.sub_self,
      pow_zero, mul_one, Nat.descFactorial_self]
    exact mul_neg_of_neg_of_pos hneg (by positivity)
  obtain ⟨x₁, hx₁, hφx₁⟩ := exists_pos_sum_range_pow hd
    (fun i => r i * (d.descFactorial i : ℝ)) (by simpa using h0)
  have hcont : Continuous φ := by simp only [φ]; fun_prop
  obtain ⟨y, ⟨hy0, -⟩, hφy⟩ := intermediate_value_Ioo hx₁.le hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (φ 0) (φ x₁) from ⟨hφ0, hφx₁⟩)
  refine ⟨I * y, ?_, by simpa using hy0⟩
  rw [IsRoot, eval_jensenRev_I_mul_of_coeff r hF]
  change I ^ d * ((φ y : ℝ) : ℂ) = 0
  rw [hφy]; simp

/-- **The far frequency dominates at odd degree.** -/
theorem eventually_tsum_neg {a lam : ℕ → ℝ} {c m : ℝ} (ha : ∀ k, 0 ≤ a k)
    (hlam : ∀ k, m ≤ lam k) (hsum : ∀ i, Summable fun k => a k * (c - lam k) ^ i)
    {K : ℕ} (haK : 0 < a K) (hK : 2 * c - m < lam K) :
    ∀ᶠ d : ℕ in atTop, Odd d → ∑' k, a k * (c - lam k) ^ d < 0 := by
  classical
  set M := max (c - m) 0
  set A := lam K - c
  have hMA : |M| < A := by
    rw [abs_of_nonneg (le_max_right _ _)]
    have := hlam K
    exact max_lt (by simp only [A]; linarith) (by simp only [A]; linarith)
  have hsum0 : Summable a := (hsum 0).congr fun k => by rw [pow_zero, mul_one]
  have hev := eventually_sum_lt_pow (Finset.range 1) (fun _ => ∑' k, a k) (fun _ => M) haK
    (lt_of_le_of_lt (abs_nonneg _) hMA) fun _ _ => hMA
  filter_upwards [hev] with d hd hodd
  simp only [Finset.sum_range_one, abs_of_nonneg (tsum_nonneg ha)] at hd
  rw [abs_of_nonneg (show 0 ≤ M from le_max_right _ _)] at hd
  have hite : Summable fun k => if k = K then 0 else a k * (c - lam k) ^ d :=
    (hsum d).summable_of_eq_zero_or_self fun k => by split_ifs <;> simp
  rw [(hsum d).tsum_eq_add_tsum_ite K]
  have hK' : a K * (c - lam K) ^ d = -(a K * A ^ d) := by
    rw [show c - lam K = -A by simp only [A]; ring, hodd.neg_pow]; ring
  have hrest : ∑' k, (if k = K then 0 else a k * (c - lam k) ^ d) ≤ (∑' k, a k) * M ^ d := by
    rw [← tsum_mul_right]
    refine Summable.tsum_le_tsum (fun k => ?_) hite (hsum0.mul_right _)
    split_ifs
    · exact mul_nonneg (ha k) (pow_nonneg (le_max_right _ _) _)
    · refine mul_le_mul_of_nonneg_left ?_ (ha k)
      rcases le_or_gt 0 (c - lam k) with h | h
      · exact pow_le_pow_left₀ h ((by linarith [hlam k] : c - lam k ≤ c - m).trans
          (le_max_left _ _)) d
      · exact (hodd.pow_neg h).le.trans (pow_nonneg (le_max_right _ _) d)
  rw [hK']
  linarith

/-- **Instability of nonnegative mixtures with a far frequency.** -/
theorem eventually_exists_upper_root_seriesMixture {a lam : ℕ → ℝ} {c m : ℝ} (ha : ∀ k, 0 ≤ a k)
    (hlam : ∀ k, m ≤ lam k) (hsum : ∀ i, Summable fun k => a k * (c - lam k) ^ i)
    {K : ℕ} (haK : 0 < a K) (hK : 2 * c - m < lam K) :
    ∀ᶠ d : ℕ in atTop, Odd d →
      ∃ x : ℂ, (jensenRev d (seriesMixture a lam c)).IsRoot x ∧ 0 < x.im := by
  filter_upwards [eventually_tsum_neg ha hlam hsum haK hK] with d hd hodd
  refine exists_upper_root_of_coeff (mixtureMoment a lam c) (coeff_seriesMixture a lam c)
    hodd.pos ?_ ?_
  · simp only [mixtureMoment, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
    exact ((hsum 0).congr fun k => by rw [pow_zero, mul_one]).tsum_pos ha K haK
  · simp only [mixtureMoment, div_eq_mul_inv]
    rw [tsum_mul_right]
    exact mul_neg_of_neg_of_pos (hd hodd) (by positivity)

/-! ## Pole pieces -/

/-- The translated pole piece `e^{icw}(1 − q e^{−iℓw})^{−1} = Σ_k q^k e^{i(c − kℓ)w}`. -/
def polePiece (q ℓ c : ℝ) : PowerSeries ℂ :=
  seriesMixture (fun k => q ^ k) (fun k => (k : ℝ) * ℓ) c

theorem summable_geom_mul_pow {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (c ℓ : ℝ) (i : ℕ) :
    Summable fun k : ℕ => q ^ k * (c - k * ℓ) ^ i := by
  have hgeo : Summable fun k : ℕ => ((k : ℝ) + 1) ^ i * q ^ k := by
    have h := ((summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ i * q ^ n) 1).2
      (summable_pow_mul_geometric_of_norm_lt_one i
        (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1))).mul_left q⁻¹
    refine h.congr fun k => ?_
    push_cast
    rw [pow_succ]; field_simp
  refine Summable.of_norm_bounded (hgeo.mul_left ((|c| + |ℓ|) ^ i)) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow, abs_of_pos hq0]
  have hck : |c - k * ℓ| ≤ (|c| + |ℓ|) * ((k : ℝ) + 1) := by
    have h1 := abs_sub c (k * ℓ)
    rw [abs_mul, Nat.abs_cast] at h1
    have h2 : 0 ≤ |c| * k + |ℓ| := by positivity
    nlinarith
  calc q ^ k * |c - k * ℓ| ^ i ≤ q ^ k * ((|c| + |ℓ|) * ((k : ℝ) + 1)) ^ i :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hck i) (by positivity)
    _ = (|c| + |ℓ|) ^ i * (((k : ℝ) + 1) ^ i * q ^ k) := by rw [mul_pow]; ring

/-- The pole piece is the translated inverse of the Euler factor. -/
theorem polePiece_eq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ℓ c : ℝ) :
    polePiece q ℓ c =
      expSeries (I * c) * (1 - PowerSeries.C (q : ℂ) * expSeries (-(I * ℓ)))⁻¹ := by
  have hcc : PowerSeries.constantCoeff (1 - PowerSeries.C (q : ℂ) * expSeries (-(I * ℓ))) ≠ 0 := by
    rw [map_sub, map_one, map_mul, PowerSeries.constantCoeff_C]
    rw [show PowerSeries.constantCoeff (expSeries (-(I * ℓ))) = 1 by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_expSeries]; simp]
    rw [mul_one, sub_ne_zero]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [PowerSeries.eq_mul_inv_iff_mul_eq hcc, mul_sub, mul_one, mul_left_comm, mul_comm _ (expSeries _),
    show -(I * (ℓ : ℂ)) = I * ((-ℓ : ℝ) : ℂ) by push_cast; ring,
    polePiece, expSeries_mul_seriesMixture (summable_geom_mul_pow hq0 hq1 c ℓ)]
  ext n
  rw [map_sub, PowerSeries.coeff_C_mul, seriesMixture, seriesMixture, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk, (summable_seriesMixture_term (summable_geom_mul_pow hq0 hq1 c ℓ) n).tsum_eq_zero_add,
    ← tsum_mul_left]
  simp only [pow_zero, Nat.cast_zero, zero_mul, sub_zero, Complex.ofReal_one, one_mul]
  rw [add_sub_assoc, add_eq_left, sub_eq_zero]
  refine tsum_congr fun k => ?_
  push_cast
  ring_nf

/-- **No translation stabilizes a pole piece.** For `0 < q < 1`, `ℓ > 0` and every translation `c`,
the reversed Jensen polynomials of `e^{icw}(1 − q e^{−iℓw})^{−1}` have a root in the open upper
half-plane for all large odd degrees. -/
theorem eventually_exists_upper_root_polePiece {q ℓ : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hℓ : 0 < ℓ) (c : ℝ) :
    ∀ᶠ d : ℕ in atTop, Odd d →
      ∃ x : ℂ, (jensenRev d (polePiece q ℓ c)).IsRoot x ∧ 0 < x.im := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * c / ℓ)
  rw [div_lt_iff₀ hℓ] at hK
  exact eventually_exists_upper_root_seriesMixture (m := 0) (K := K) (fun k => (pow_pos hq0 k).le)
    (fun k => by positivity) (summable_geom_mul_pow hq0 hq1 c ℓ) (pow_pos hq0 K) (by linarith)

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.eventually_exists_upper_root_polePiece
#print axioms FiniteFreeProbability.polePiece_eq

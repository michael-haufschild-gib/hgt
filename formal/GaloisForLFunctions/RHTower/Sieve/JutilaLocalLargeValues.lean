import GaloisForLFunctions.RHTower.Sieve.SmoothDyadicHalaszMontgomery
import GaloisForLFunctions.RHTower.Sieve.DirichletLargeValues
import GaloisForLFunctions.RHTower.Sieve.DivisorBound
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.HTGeometry.SeparatedPointCount
import GaloisForLFunctions.HTGeometry.PartialFractionIndependence

/-!
# Jutila's local large-values estimate

For a dyadic block `P(x) = ∑_{N ≤ n < 2N} c_n n^{-1-ix}` and a `1`-separated set `S` of diameter
`≤ W` on which `|P| ≥ V`: the smooth Halász–Montgomery inequality bounds `(|S|V)²` by the Gram sum
`∑_{x,y} |H(x-y)|`; near pairs cost `|H| ≤ 3`, far pairs are reflected (Jutila's Lemma 1) into
the dual sums `D_M(1/2 + iτ) = ∑_{m ≤ M} m^{-1/2+iτ}`; Hölder with exponent `2k` over the pairs
and the discrete mean value theorem for `D_M^k` (a Dirichlet polynomial of length `M^k` whose
coefficients count `k`-fold factorisations) give
`|S| ≤ 240(2τ₁+1)G/V² + (80√π G/(√N V²))^{2k} (W + 1 + 4L(1+log L))(1+2 log L) A(1+log M)^k`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology Set

noncomputable section

/-- **The discrete mean value theorem on a finite separated set of reals.** -/
theorem sum_normSq_dirPoly_finset_le (L : ℕ) (hL : 2 ≤ L) (a : Fin L → ℂ) {S : Finset ℝ}
    {W : ℝ} (hW : 0 ≤ W) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ W) :
    ∑ x ∈ S, ‖dirPoly L a x‖ ^ (2 : ℕ) ≤
      (W + 1 + 4 * (L : ℝ) * (1 + Real.log L)) * (1 + 2 * Real.log L) *
        ∑ m : Fin L, ‖a m‖ ^ (2 : ℕ) := by
  classical
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS; simp only [Finset.sum_empty]
    have hlog : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L))
    positivity
  obtain ⟨R, hR⟩ : ∃ R, S.card = R + 1 := ⟨S.card - 1, by
    have := Finset.card_pos.2 hS; omega⟩
  set m₀ := S.min' hS with hm₀
  set c : ℝ := m₀ - 1 / 2 with hc
  set lam : ℕ → ℝ := fun i => sepEnum S hR 1 i - c with hlam
  set a' : Fin L → ℂ := fun n => a n * Complex.exp (((c * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * I)
    with ha'
  have hshift : ∀ t : ℝ, dirPoly L a (t + c) = dirPoly L a' t := by
    intro t
    unfold dirPoly
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [ha']
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  have hnorm' : ∀ n, ‖a' n‖ = ‖a n‖ := by
    intro n
    simp only [ha']
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hgap : ∀ i, lam i + 1 ≤ lam (i + 1) := by
    intro i
    have := sepEnum_gap hR (delta := 1) hsep i
    simp only [hlam]; linarith
  have hlow : 1 / 2 ≤ lam 0 := by
    simp only [hlam]
    rw [sepEnum_of_le hR 1 (Nat.zero_le R)]
    have hmem := S.orderEmbOfFin_mem hR ⟨0, Nat.succ_pos R⟩
    have hmin := S.min'_le _ hmem
    have hmin' : S.orderEmbOfFin hR ⟨0, Nat.succ_pos R⟩ = S.min' hS := by
      rw [Finset.orderEmbOfFin_zero hR (Nat.succ_pos R)]
    rw [hmin', hc, hm₀]; linarith
  have hhigh : lam R + 1 / 2 ≤ W + 1 := by
    simp only [hlam]
    rw [sepEnum_of_le hR 1 le_rfl]
    have hmem := S.orderEmbOfFin_mem hR ⟨R, Nat.lt_succ_self R⟩
    have hd := hdiam _ hmem _ (S.min'_mem hS)
    rw [hc, hm₀]
    have := le_abs_self (S.orderEmbOfFin hR ⟨R, Nat.lt_succ_self R⟩ - S.min' hS)
    linarith
  have hmv := largeValues_dirPoly L hL a' (δ := 1) (T := W + 1) one_pos (by linarith) hgap
    (by norm_num at hlow ⊢; linarith) R (by norm_num at hhigh ⊢; linarith)
  have hsum : ∑ x ∈ S, ‖dirPoly L a x‖ ^ (2 : ℕ) =
      ∑ r ∈ Finset.range (R + 1), ‖dirPoly L a' (lam r)‖ ^ (2 : ℕ) := by
    rw [← Finset.image_orderEmbOfFin_univ S hR, Finset.sum_image
      (fun i _ j _ h => (S.orderEmbOfFin hR).injective h)]
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hlam]
    rw [sepEnum_of_le hR 1 (Nat.lt_succ_iff.1 i.2), ← hshift]
    simp
  rw [hsum]
  refine hmv.trans (le_of_eq ?_)
  simp only [hnorm', div_one]

/-- The `k`-tuples from `[1, M]`. -/
def dualTuples (M k : ℕ) : Finset (Fin k → ℕ) := Fintype.piFinset fun _ => Finset.Icc 1 M

/-- The number of `k`-tuples from `[1, M]` with product `ℓ`. -/
def dualPowCount (M k ℓ : ℕ) : ℕ := ((dualTuples M k).filter fun t => ∏ i, t i = ℓ).card

theorem prod_mem_Icc_of_mem_dualTuples {M k : ℕ} {t : Fin k → ℕ} (ht : t ∈ dualTuples M k) :
    1 ≤ ∏ i, t i ∧ ∏ i, t i ≤ M ^ k := by
  simp only [dualTuples, Fintype.mem_piFinset, Finset.mem_Icc] at ht
  constructor
  · exact Finset.one_le_prod' fun i _ => (ht i).1
  · calc ∏ i, t i ≤ ∏ _i : Fin k, M := Finset.prod_le_prod' fun i _ => (ht i).2
      _ = M ^ k := by simp

theorem natCast_prod_cpow {k : ℕ} (t : Fin k → ℕ) (z : ℂ) :
    (((∏ i, t i : ℕ) : ℂ)) ^ z = ∏ i, ((t i : ℕ) : ℂ) ^ z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
      ih]

/-- **The `k`-th power of the dual sum as a Dirichlet polynomial.** -/
theorem dualPartialSum_pow_eq (M k : ℕ) (z : ℂ) :
    (RHTower.dualPartialSum M z) ^ k =
      ∑ ℓ ∈ Finset.Icc 1 (M ^ k), (dualPowCount M k ℓ : ℂ) * (ℓ : ℂ) ^ (z - 1) := by
  classical
  unfold RHTower.dualPartialSum
  conv_lhs => rw [← Fin.prod_const, Finset.prod_univ_sum]
  have h1 : ∀ t ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 M),
      ∏ i, ((t i : ℕ) : ℂ) ^ (z - 1) = (((∏ i, t i : ℕ) : ℂ)) ^ (z - 1) :=
    fun t _ => (natCast_prod_cpow t (z - 1)).symm
  rw [Finset.sum_congr rfl h1]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun t : Fin k → ℕ => ∏ i, t i)
    (t := Finset.Icc 1 (M ^ k)) (fun t ht => by
      have := prod_mem_Icc_of_mem_dualTuples (M := M) ht
      exact Finset.mem_Icc.2 this)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.sum_congr rfl fun t ht => by rw [(Finset.mem_filter.1 ht).2]]
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

/-- The count is at most `d(ℓ)^k`. -/
theorem dualPowCount_le (M k : ℕ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    dualPowCount M k ℓ ≤ ℓ.divisors.card ^ k := by
  classical
  unfold dualPowCount
  calc ((dualTuples M k).filter fun t => ∏ i, t i = ℓ).card
      ≤ (Fintype.piFinset fun _ : Fin k => ℓ.divisors).card := by
        refine Finset.card_le_card fun t ht => ?_
        rw [Finset.mem_filter] at ht
        rw [Fintype.mem_piFinset]
        intro i
        rw [Nat.mem_divisors]
        refine ⟨?_, hℓ⟩
        rw [← ht.2]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    _ = ℓ.divisors.card ^ k := by rw [Fintype.card_piFinset]; simp

/-- `∑_ℓ c_ℓ/ℓ = (∑_{m ≤ M} 1/m)^k`. -/
theorem sum_dualPowCount_div_eq (M k : ℕ) :
    ∑ ℓ ∈ Finset.Icc 1 (M ^ k), (dualPowCount M k ℓ : ℝ) / ℓ =
      (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / m) ^ k := by
  classical
  conv_rhs => rw [← Fin.prod_const, Finset.prod_univ_sum]
  have h1 : ∀ t ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 M),
      ∏ i, (1 : ℝ) / (t i : ℕ) = 1 / ((∏ i, t i : ℕ) : ℝ) := by
    intro t _; push_cast; rw [Finset.prod_div_distrib, Finset.prod_const_one]
  rw [Finset.sum_congr rfl h1]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun t : Fin k → ℕ => ∏ i, t i)
    (t := Finset.Icc 1 (M ^ k)) (fun t ht => by
      have := prod_mem_Icc_of_mem_dualTuples (M := M) ht
      exact Finset.mem_Icc.2 this)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.sum_congr rfl fun t ht => by rw [(Finset.mem_filter.1 ht).2]]
  rw [Finset.sum_const, nsmul_eq_mul]
  unfold dualPowCount dualTuples
  ring

/-- The `k`-th power of the dual sum along the critical line, as a Dirichlet polynomial in the
second point. -/
def dualPowCoeff (M k : ℕ) (u : ℝ) : Fin (M ^ k) → ℂ := fun n =>
  (dualPowCount M k ((n : ℕ) + 1) : ℂ) * (((n : ℕ) + 1 : ℕ) : ℂ) ^ ((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)

theorem exp_mul_log_succ_eq_cpow (m : ℕ) (t : ℝ) :
    Complex.exp (((t * Real.log ((m : ℝ) + 1)) : ℝ) * I) = (((m + 1 : ℕ)) : ℂ) ^ ((t : ℂ) * I) := by
  have hne : (((m + 1 : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  rw [Complex.cpow_def_of_ne_zero hne]
  have hlog : Complex.log (((m + 1 : ℕ)) : ℂ) = ((Real.log ((m : ℝ) + 1) : ℝ) : ℂ) := by
    rw [show (((m + 1 : ℕ)) : ℂ) = ((((m : ℝ) + 1 : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]
  rw [hlog]
  congr 1; push_cast; ring

theorem dualPartialSum_pow_eq_dirPoly (M k : ℕ) (u y : ℝ) :
    (RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((u - y : ℝ) : ℂ) * I)) ^ k =
      dirPoly (M ^ k) (dualPowCoeff M k u) (-y) := by
  rw [dualPartialSum_pow_eq, GaloisForLFunctions.HTGeometry.sum_Icc_one_eq_sum_fin]
  unfold dirPoly dualPowCoeff
  refine Finset.sum_congr rfl fun n _ => ?_
  have hne : (((n : ℕ) + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n : ℕ)
  rw [exp_mul_log_succ_eq_cpow, mul_assoc, ← Complex.cpow_add _ _ hne]
  congr 2
  push_cast; ring

theorem norm_dualPowCoeff_sq_sum_le (M k : ℕ) (u : ℝ) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ ℓ ∈ Finset.Icc 1 (M ^ k), (dualPowCount M k ℓ : ℝ) ≤ A) :
    ∑ n : Fin (M ^ k), ‖dualPowCoeff M k u n‖ ^ (2 : ℕ) ≤ A * (1 + Real.log M) ^ k := by
  have hterm : ∀ n : Fin (M ^ k), ‖dualPowCoeff M k u n‖ ^ (2 : ℕ) ≤
      A * ((dualPowCount M k ((n : ℕ) + 1) : ℝ) / (((n : ℕ) + 1 : ℕ) : ℝ)) := by
    intro n
    unfold dualPowCoeff
    have hpos : (0 : ℝ) < (((n : ℕ) + 1 : ℕ) : ℝ) := by positivity
    rw [norm_mul, Complex.norm_natCast,
      show (((n : ℕ) + 1 : ℕ) : ℂ) = (((((n : ℕ) + 1 : ℕ) : ℝ)) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    have hre : ((-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I).re = -(1 / 2) := by simp
    rw [hre, mul_pow]
    have hsq : ((((n : ℕ) + 1 : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 = 1 / (((n : ℕ) + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]; norm_num [Real.rpow_neg_one]
    rw [hsq]
    have hc := hA ((n : ℕ) + 1) (Finset.mem_Icc.2 ⟨by omega, by have := n.2; omega⟩)
    have hc0 : (0 : ℝ) ≤ dualPowCount M k ((n : ℕ) + 1) := Nat.cast_nonneg _
    calc (dualPowCount M k ((n : ℕ) + 1) : ℝ) ^ 2 * (1 / (((n : ℕ) + 1 : ℕ) : ℝ))
        ≤ A * (dualPowCount M k ((n : ℕ) + 1)) * (1 / (((n : ℕ) + 1 : ℕ) : ℝ)) := by
          gcongr; rw [sq]; exact mul_le_mul_of_nonneg_right hc hc0
      _ = A * ((dualPowCount M k ((n : ℕ) + 1) : ℝ) / (((n : ℕ) + 1 : ℕ) : ℝ)) := by ring
  refine (Finset.sum_le_sum fun n _ => hterm n).trans ?_
  rw [← Finset.mul_sum]
  have hsum : ∑ n : Fin (M ^ k), (dualPowCount M k ((n : ℕ) + 1) : ℝ) / (((n : ℕ) + 1 : ℕ) : ℝ) =
      (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / m) ^ k := by
    rw [← sum_dualPowCount_div_eq, GaloisForLFunctions.HTGeometry.sum_Icc_one_eq_sum_fin]
  rw [hsum]
  have hH := sum_Icc_one_div_le_one_add_log M
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Finset.sum_nonneg fun m _ => by positivity)
    hH k) hA0

/-- The smooth dyadic Gram entries are bounded by `3`. -/
theorem norm_dyadicSmoothGram_le_three {N : ℝ} (hN : 1 ≤ N) (τ : ℝ) :
    ‖RHTower.dyadicSmoothGram N τ‖ ≤ 3 := by
  have hN0 : 0 < N := by linarith
  rw [dyadicSmoothGram_eq_tsum_gramCoeff hN0 τ]
  have hn : ∀ n : ℕ, ‖(dyadicGramCoeff N n : ℂ) * ((n : ℂ) + 1) ^ (-((τ : ℂ) * I))‖ =
      dyadicGramCoeff N n := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (dyadicGramCoeff_nonneg hN0 n),
      show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  calc ‖∑' n : ℕ, (dyadicGramCoeff N n : ℂ) * ((n : ℂ) + 1) ^ (-((τ : ℂ) * I))‖
      ≤ ∑' n : ℕ, ‖(dyadicGramCoeff N n : ℂ) * ((n : ℂ) + 1) ^ (-((τ : ℂ) * I))‖ :=
        norm_tsum_le_tsum_norm (by simp only [hn]; exact summable_dyadicGramCoeff hN0)
    _ = ∑' n, dyadicGramCoeff N n := by simp only [hn]
    _ ≤ 3 := tsum_dyadicGramCoeff_le hN

theorem continuous_dualPartialSum_criticalLine (M : ℕ) (τ : ℝ) :
    Continuous fun v : ℝ =>
      RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I) := by
  have hd : Continuous (RHTower.dualPartialSum M) :=
    (show Differentiable ℂ (RHTower.dualPartialSum M) from
      fun z => RHTower.differentiableAt_dualPartialSum M z).continuous
  refine hd.comp ?_
  exact continuous_const.add ((Complex.continuous_ofReal.comp
    (continuous_const.add continuous_id)).mul continuous_const)

theorem integrable_gauss_mul_norm_dualPartialSum (M : ℕ) (τ : ℝ) :
    Integrable (fun v : ℝ => Real.exp (-(v ^ 2)) *
      ‖RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)‖) := by
  have hg : Integrable (fun v : ℝ => Real.exp (-1 * v ^ 2)) := integrable_exp_neg_mul_sq one_pos
  refine (hg.mul_const (M : ℝ)).mono' ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_pow 2).neg).mul
      (continuous_dualPartialSum_criticalLine M τ).norm).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun v => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), neg_one_mul]
    have hre : (((1 / 2 : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I).re ≤ 1 := by simp; norm_num
    exact mul_le_mul_of_nonneg_left (RHTower.norm_dualPartialSum_le hre) (Real.exp_pos _).le

/-- For a fixed shift `v`, the `2k`-th moment of the dual sum over the pair differences of a
separated set of diameter `≤ W` is at most `|S|` times the mean value bound for the `k`-th power. -/
theorem sum_pairs_norm_dualPartialSum_pow_le {M k : ℕ} (hL : 2 ≤ M ^ k) {S : Finset ℝ}
    {W A : ℝ} (hW : 0 ≤ W) (hA0 : 0 ≤ A)
    (hA : ∀ ℓ ∈ Finset.Icc 1 (M ^ k), (dualPowCount M k ℓ : ℝ) ≤ A)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ W)
    (v : ℝ) :
    ∑ x ∈ S, ∑ y ∈ S,
        ‖RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((x - y + v : ℝ) : ℂ) * I)‖ ^ (2 * k) ≤
      S.card * ((W + 1 + 4 * ((M ^ k : ℕ) : ℝ) * (1 + Real.log ((M ^ k : ℕ) : ℝ))) *
        (1 + 2 * Real.log ((M ^ k : ℕ) : ℝ)) * (A * (1 + Real.log M) ^ k)) := by
  classical
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun x _ => ?_
  have hterm : ∀ y : ℝ,
      ‖RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((x - y + v : ℝ) : ℂ) * I)‖ ^ (2 * k) =
        ‖dirPoly (M ^ k) (dualPowCoeff M k (x + v)) (-y)‖ ^ (2 : ℕ) := by
    intro y
    rw [← dualPartialSum_pow_eq_dirPoly, norm_pow, ← pow_mul, mul_comm k 2,
      show x - y + v = x + v - y by ring]
  simp only [hterm]
  have hinj : ∀ a ∈ S, ∀ b ∈ S, -a = -b → a = b := fun a _ b _ h => neg_injective h
  rw [← Finset.sum_image (f := fun z => ‖dirPoly (M ^ k) (dualPowCoeff M k (x + v)) z‖ ^ (2 : ℕ))
    hinj]
  have hsep' : ∀ a ∈ S.image Neg.neg, ∀ b ∈ S.image Neg.neg, a ≠ b → 1 ≤ |a - b| := by
    intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb
    rw [show -a' - -b' = -(a' - b') by ring, abs_neg]
    exact hsep a' ha' b' hb' fun h => hab (by rw [h])
  have hdiam' : ∀ a ∈ S.image Neg.neg, ∀ b ∈ S.image Neg.neg, |a - b| ≤ W := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb
    rw [show -a' - -b' = -(a' - b') by ring, abs_neg]
    exact hdiam a' ha' b' hb'
  refine (sum_normSq_dirPoly_finset_le (M ^ k) hL _ hW hsep' hdiam').trans ?_
  have hlogL : 0 ≤ Real.log ((M ^ k : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M ^ k))
  exact mul_le_mul_of_nonneg_left (norm_dualPowCoeff_sq_sum_le M k (x + v) hA0 hA)
    (by positivity)

/-- Hölder over the pairs: `∑_{x,y} |D| ≤ (|S|^{4k-1} Φ)^{1/2k}`. -/
theorem sum_pairs_norm_dualPartialSum_le {M k : ℕ} (hk : 1 ≤ k) (hL : 2 ≤ M ^ k)
    {S : Finset ℝ} {W A : ℝ} (hW : 0 ≤ W) (hA0 : 0 ≤ A)
    (hA : ∀ ℓ ∈ Finset.Icc 1 (M ^ k), (dualPowCount M k ℓ : ℝ) ≤ A)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ W)
    (v : ℝ) :
    ∑ x ∈ S, ∑ y ∈ S,
        ‖RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((x - y + v : ℝ) : ℂ) * I)‖ ≤
      ((S.card : ℝ) ^ (4 * k - 1) *
        ((W + 1 + 4 * ((M ^ k : ℕ) : ℝ) * (1 + Real.log ((M ^ k : ℕ) : ℝ))) *
          (1 + 2 * Real.log ((M ^ k : ℕ) : ℝ)) * (A * (1 + Real.log M) ^ k))) ^
        (((2 * k : ℕ) : ℝ)⁻¹) := by
  classical
  set Φ : ℝ := (W + 1 + 4 * ((M ^ k : ℕ) : ℝ) * (1 + Real.log ((M ^ k : ℕ) : ℝ))) *
      (1 + 2 * Real.log ((M ^ k : ℕ) : ℝ)) * (A * (1 + Real.log M) ^ k) with hΦ
  set f : ℝ × ℝ → ℝ := fun p =>
    ‖RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((p.1 - p.2 + v : ℝ) : ℂ) * I)‖ with hf
  have hsum : ∑ x ∈ S, ∑ y ∈ S,
      ‖RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((x - y + v : ℝ) : ℂ) * I)‖ =
        ∑ p ∈ S ×ˢ S, f p := by
    rw [Finset.sum_product]
  have hsumk : ∑ p ∈ S ×ˢ S, f p ^ (2 * k) ≤ (S.card : ℝ) * Φ := by
    rw [Finset.sum_product]
    exact sum_pairs_norm_dualPartialSum_pow_le hL hW hA0 hA hsep hdiam v
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hhold := pow_sum_le_card_mul_sum_pow (s := S ×ˢ S) (f := f) (fun p _ => norm_nonneg _)
    (2 * m + 1)
  rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, Finset.card_product] at hhold
  have hs0 : 0 ≤ ∑ p ∈ S ×ˢ S, f p := Finset.sum_nonneg fun p _ => norm_nonneg _
  have hpow : (∑ p ∈ S ×ˢ S, f p) ^ (2 * (m + 1)) ≤ (S.card : ℝ) ^ (4 * (m + 1) - 1) * Φ := by
    refine hhold.trans ?_
    push_cast
    calc ((S.card : ℝ) * S.card) ^ (2 * m + 1) * ∑ p ∈ S ×ˢ S, f p ^ (2 * (m + 1))
        ≤ ((S.card : ℝ) * S.card) ^ (2 * m + 1) * ((S.card : ℝ) * Φ) :=
          mul_le_mul_of_nonneg_left hsumk (by positivity)
      _ = (S.card : ℝ) ^ (4 * (m + 1) - 1) * Φ := by
          rw [show 4 * (m + 1) - 1 = 2 * (2 * m + 1) + 1 by omega, pow_succ, pow_mul, sq]
          ring
  rw [hsum]
  have hne : 2 * (m + 1) ≠ 0 := by omega
  calc ∑ p ∈ S ×ˢ S, f p = ((∑ p ∈ S ×ˢ S, f p) ^ (2 * (m + 1))) ^ (((2 * (m + 1) : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast hs0 hne).symm
    _ ≤ ((S.card : ℝ) ^ (4 * (m + 1) - 1) * Φ) ^ (((2 * (m + 1) : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hpow (by positivity)

/-- The final arithmetic of Jutila's local estimate. -/
theorem jutila_local_arith {R V G a b Y Φ B : ℝ} {k : ℕ} (hk : 1 ≤ k) (hR : 0 < R) (hV : 0 < V)
    (hG : 0 ≤ G) (ha : 0 ≤ a) (hb : 0 < b) (hΦ : 0 ≤ Φ)
    (hmain : R ^ 2 * V ^ 2 ≤ 20 * G * (a * R + b * Y + R ^ 2 * B))
    (hB : 20 * G * B ≤ V ^ 2 / 4) (hY : Y ^ (2 * k) ≤ R ^ (4 * k - 1) * Φ) :
    R ≤ 80 * a * G / V ^ 2 + (80 * b * G / V ^ 2) ^ (2 * k) * Φ := by
  have hV2 : 0 < V ^ 2 := by positivity
  have hRV : 0 < R ^ 2 * V ^ 2 := by positivity
  have hsplit : 20 * G * (a * R + b * Y + R ^ 2 * B) =
      20 * G * a * R + 20 * G * b * Y + R ^ 2 * (20 * G * B) := by ring
  have hRB : R ^ 2 * (20 * G * B) ≤ R ^ 2 * (V ^ 2 / 4) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have ht1 : 0 ≤ 80 * a * G / V ^ 2 := by positivity
  have ht2 : 0 ≤ (80 * b * G / V ^ 2) ^ (2 * k) * Φ := by positivity
  by_cases h1 : R ^ 2 * V ^ 2 / 4 ≤ 20 * G * a * R
  · have : R ≤ 80 * a * G / V ^ 2 := by
      rw [le_div_iff₀ hV2]
      have h' : R * (R * V ^ 2) ≤ R * (80 * a * G) := by nlinarith
      exact le_of_mul_le_mul_left (by linarith) hR
    linarith
  · have h2 : R ^ 2 * V ^ 2 / 4 ≤ 20 * G * b * Y := by
      rw [not_le] at h1; nlinarith
    have hG0 : 0 < G := by
      rcases hG.lt_or_eq with h | h
      · exact h
      · rw [← h] at h2; nlinarith
    set B' : ℝ := V ^ 2 / (80 * b * G) with hB'
    have hB'0 : 0 < B' := by positivity
    have hRY : R ^ 2 * B' ≤ Y := by
      rw [hB', mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    have hpow : (R ^ 2 * B') ^ (2 * k) ≤ R ^ (4 * k - 1) * Φ :=
      (pow_le_pow_left₀ (by positivity) hRY _).trans hY
    have hexp : (R ^ 2 * B') ^ (2 * k) = R * B' ^ (2 * k) * R ^ (4 * k - 1) := by
      rw [mul_pow, ← pow_mul, show 2 * (2 * k) = (4 * k - 1) + 1 by omega, pow_succ]; ring
    rw [hexp] at hpow
    have hRΦ : R * B' ^ (2 * k) ≤ Φ := by
      have hRk : 0 < R ^ (4 * k - 1) := by positivity
      nlinarith
    have hinv : (80 * b * G / V ^ 2) = B'⁻¹ := by rw [hB', inv_div]
    have : R ≤ (80 * b * G / V ^ 2) ^ (2 * k) * Φ := by
      rw [hinv, inv_pow, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      exact hRΦ
    linarith

/-- `∑_{x,y ∈ S} ∫ e^{-v²} |D_M(1/2 + i(x - y + v))| dv ≤ √π (|S|^{4k-1} Φ)^{1/2k}`. -/
theorem sum_pairs_integral_norm_dualPartialSum_le {M k : ℕ} (hk : 1 ≤ k) (hL : 2 ≤ M ^ k)
    {S : Finset ℝ} {W A : ℝ} (hW : 0 ≤ W) (hA0 : 0 ≤ A)
    (hA : ∀ ℓ ∈ Finset.Icc 1 (M ^ k), (dualPowCount M k ℓ : ℝ) ≤ A)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ W) :
    ∑ x ∈ S, ∑ y ∈ S, ∫ v : ℝ, Real.exp (-(v ^ 2)) *
        ‖RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((x - y + v : ℝ) : ℂ) * I)‖ ≤
      Real.sqrt Real.pi * ((S.card : ℝ) ^ (4 * k - 1) *
        ((W + 1 + 4 * ((M ^ k : ℕ) : ℝ) * (1 + Real.log ((M ^ k : ℕ) : ℝ))) *
          (1 + 2 * Real.log ((M ^ k : ℕ) : ℝ)) * (A * (1 + Real.log M) ^ k))) ^
        (((2 * k : ℕ) : ℝ)⁻¹) := by
  classical
  set Y : ℝ := ((S.card : ℝ) ^ (4 * k - 1) *
        ((W + 1 + 4 * ((M ^ k : ℕ) : ℝ) * (1 + Real.log ((M ^ k : ℕ) : ℝ))) *
          (1 + 2 * Real.log ((M ^ k : ℕ) : ℝ)) * (A * (1 + Real.log M) ^ k))) ^
        (((2 * k : ℕ) : ℝ)⁻¹) with hYdef
  have hint : ∀ x y : ℝ, Integrable (fun v : ℝ => Real.exp (-(v ^ 2)) *
      ‖RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((x - y + v : ℝ) : ℂ) * I)‖) :=
    fun x y => integrable_gauss_mul_norm_dualPartialSum M (x - y)
  have e : ∫ v : ℝ, ∑ x ∈ S, ∑ y ∈ S, Real.exp (-(v ^ 2)) *
        ‖RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((x - y + v : ℝ) : ℂ) * I)‖ =
      ∑ x ∈ S, ∑ y ∈ S, ∫ v : ℝ, Real.exp (-(v ^ 2)) *
        ‖RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((x - y + v : ℝ) : ℂ) * I)‖ := by
    rw [integral_finsetSum S fun x _ => integrable_finsetSum S fun y _ => hint x y]
    exact Finset.sum_congr rfl fun x _ => integral_finsetSum S fun y _ => hint x y
  rw [← e]
  have hg : ∫ v : ℝ, Real.exp (-(v ^ 2)) = Real.sqrt Real.pi := by
    have := integral_gaussian 1
    simp only [neg_one_mul, div_one] at this
    exact this
  have hgi : Integrable (fun v : ℝ => Real.exp (-(v ^ 2)) * Y) := by
    have := (integrable_exp_neg_mul_sq one_pos).mul_const Y
    simpa only [neg_one_mul] using this
  calc ∫ v : ℝ, ∑ x ∈ S, ∑ y ∈ S, Real.exp (-(v ^ 2)) *
        ‖RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((x - y + v : ℝ) : ℂ) * I)‖
      ≤ ∫ v : ℝ, Real.exp (-(v ^ 2)) * Y := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => ?_) hgi
          (Filter.Eventually.of_forall fun v => ?_)
        · exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by positivity
        · simp only [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left
            (sum_pairs_norm_dualPartialSum_le hk hL hW hA0 hA hsep hdiam v) (Real.exp_pos _).le
    _ = Real.sqrt Real.pi * Y := by rw [integral_mul_const, hg]

/-- **Jutila's local large-values estimate** (with the discrete mean value theorem in place of the
fourth moment).  For a dyadic block `P(x) = ∑_{N ≤ n < 2N} c_n n^{-1-ix}` with
`∑ |c_n|²/n ≤ G`, a `1`-separated set `S` of diameter `≤ W` on which `|P| ≥ V`, a dual length
`M ≥ 2`, a bound `A` for the multiplicities of `k`-fold products from `[1, M]`, and a cut-off
`τ₁ ≥ 1` for which the reflection errors are `≤ V²/(80 G)`:
`|S| ≤ 240 (2τ₁+1) G/V² + (80 √π G/(√N V²))^{2k} Φ`, where
`Φ = (W + 1 + 4L(1 + log L))(1 + 2 log L) · A (1 + log M)^k`, `L = M^k`. -/
theorem exists_card_le_jutila_local {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N M : ℕ) (c : ℕ → ℂ) (S : Finset ℝ) (W V G τ₁ A : ℝ),
      1 ≤ N → 2 ≤ M → 0 ≤ W → 0 < V → 1 ≤ τ₁ → 0 ≤ A →
      (∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ ^ 2 / (n : ℝ)) ≤ G →
      (∀ ℓ ∈ Finset.Icc 1 (M ^ k), (dualPowCount M k ℓ : ℝ) ≤ A) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) → (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ W) →
      (∀ x ∈ S, V ≤ ‖blockPoly N c 1 x‖) →
      20 * G * (C * ((W + 2 * j + 2) ^ (2 * j) * ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) *
          (N : ℝ) ^ (-(1 / 2) - 2 * j : ℝ))) + 2 * (Real.exp (-(τ₁ ^ 2)) / τ₁)) ≤ V ^ 2 / 4 →
      (S.card : ℝ) ≤ 80 * (3 * (2 * τ₁ + 1)) * G / V ^ 2 +
        (80 * (Real.sqrt Real.pi / Real.sqrt N) * G / V ^ 2) ^ (2 * k) *
          ((W + 1 + 4 * ((M ^ k : ℕ) : ℝ) * (1 + Real.log ((M ^ k : ℕ) : ℝ))) *
            (1 + 2 * Real.log ((M ^ k : ℕ) : ℝ)) * (A * (1 + Real.log M) ^ k)) := by
  obtain ⟨C, hC0, hC⟩ := RHTower.exists_norm_dyadicSmoothGram_le hj
  refine ⟨C, hC0, ?_⟩
  intro N M c S W V G τ₁ A hN hM hW hV hτ₁ hA0 hG hA hsep hdiam hbig hsmall
  classical
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hML : 2 ≤ M ^ k := le_trans hM (Nat.le_self_pow (by omega) M)
  set Φ : ℝ := (W + 1 + 4 * ((M ^ k : ℕ) : ℝ) * (1 + Real.log ((M ^ k : ℕ) : ℝ))) *
      (1 + 2 * Real.log ((M ^ k : ℕ) : ℝ)) * (A * (1 + Real.log M) ^ k) with hΦ
  set E : ℝ := C * ((W + 2 * j + 2) ^ (2 * j) * ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) *
      (N : ℝ) ^ (-(1 / 2) - 2 * j : ℝ))) + 2 * (Real.exp (-(τ₁ ^ 2)) / τ₁) with hE
  have hG0 : 0 ≤ G := (Finset.sum_nonneg fun n _ => by positivity).trans hG
  have hlogL : 0 ≤ Real.log ((M ^ k : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M ^ k))
  have hlogM : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M))
  have hΦ0 : 0 ≤ Φ := by rw [hΦ]; positivity
  have hRHS0 : 0 ≤ 80 * (3 * (2 * τ₁ + 1)) * G / V ^ 2 +
      (80 * (Real.sqrt Real.pi / Real.sqrt N) * G / V ^ 2) ^ (2 * k) * Φ := by
    have : 0 ≤ 80 * (3 * (2 * τ₁ + 1)) * G / V ^ 2 := by
      apply div_nonneg _ (sq_nonneg _); have : 0 ≤ τ₁ := by linarith
      positivity
    have h2 : 0 ≤ (80 * (Real.sqrt Real.pi / Real.sqrt N) * G / V ^ 2) ^ (2 * k) * Φ := by
      positivity
    linarith
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS; simpa using hRHS0
  have hR : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.2 hS
  -- the pair bound
  have hpair : ∀ x ∈ S, ∀ y ∈ S, ‖RHTower.dyadicSmoothGram N (x - y)‖ ≤
      (if |x - y| ≤ τ₁ then (3 : ℝ) else 0) + (N : ℝ) ^ (-(1 / 2) : ℝ) *
        (∫ v : ℝ, Real.exp (-(v ^ 2)) *
          ‖RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((x - y + v : ℝ) : ℂ) * I)‖) + E := by
    intro x hx y hy
    have hJ0 : 0 ≤ ∫ v : ℝ, Real.exp (-(v ^ 2)) *
        ‖RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((x - y + v : ℝ) : ℂ) * I)‖ :=
      integral_nonneg fun v => by positivity
    have hNJ := mul_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N) (-(1 / 2) : ℝ)) hJ0
    have hE1 : 0 ≤ C * ((W + 2 * j + 2) ^ (2 * j) * ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) *
        (N : ℝ) ^ (-(1 / 2) - 2 * j : ℝ))) := by positivity
    have hE2 : 0 ≤ 2 * (Real.exp (-(τ₁ ^ 2)) / τ₁) := by
      have : 0 < τ₁ := by linarith
      positivity
    split_ifs with hnear
    · have := norm_dyadicSmoothGram_le_three hNr (x - y)
      linarith
    · rw [not_le] at hnear
      have hτ0 : x - y ≠ 0 := fun h => by rw [h, abs_zero] at hnear; linarith
      have h := hC N (x - y) M hNr hτ0 (by omega)
      have hpowle : (|x - y| + 2 * j + 2) ^ (2 * j) ≤ (W + 2 * j + 2) ^ (2 * j) :=
        pow_le_pow_left₀ (by positivity) (by linarith [hdiam x hx y hy]) _
      have hexp : Real.exp (-((x - y) ^ 2)) / |x - y| ≤ Real.exp (-(τ₁ ^ 2)) / τ₁ := by
        have hsq : τ₁ ^ 2 ≤ (x - y) ^ 2 := by
          rw [← sq_abs (x - y)]; exact pow_le_pow_left₀ (by linarith) hnear.le 2
        calc Real.exp (-((x - y) ^ 2)) / |x - y| ≤ Real.exp (-(τ₁ ^ 2)) / |x - y| :=
              div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (abs_nonneg _)
          _ ≤ Real.exp (-(τ₁ ^ 2)) / τ₁ :=
              div_le_div_of_nonneg_left (Real.exp_pos _).le (by linarith) hnear.le
      have hCle : C * ((|x - y| + 2 * j + 2) ^ (2 * j) * ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) *
          (N : ℝ) ^ (-(1 / 2) - 2 * j : ℝ))) ≤ C * ((W + 2 * j + 2) ^ (2 * j) *
          ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) * (N : ℝ) ^ (-(1 / 2) - 2 * j : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpowle (by positivity)) hC0
      rw [hE]
      linarith
  -- summing the pair bound
  have hnearsum : ∀ x ∈ S, ∑ y ∈ S, (if |x - y| ≤ τ₁ then (3 : ℝ) else 0) ≤ 3 * (2 * τ₁ + 1) := by
    intro x _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard := _root_.card_le_of_separated_of_subset_Icc (a := x - τ₁) (b := x + τ₁) one_pos
      (by linarith) (S.filter fun y => |x - y| ≤ τ₁)
      (fun a ha b hb hab => hsep a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1 hab)
      (fun y hy => by
        have h := abs_le.1 (Finset.mem_filter.1 hy).2
        constructor <;> linarith [h.1, h.2])
    rw [div_one] at hcard
    linarith
  have hJsum := sum_pairs_integral_norm_dualPartialSum_le hk hML hW hA0 hA hsep hdiam
  set Y : ℝ := ((S.card : ℝ) ^ (4 * k - 1) * Φ) ^ (((2 * k : ℕ) : ℝ)⁻¹) with hYdef
  have hY0 : 0 ≤ Y := Real.rpow_nonneg (by positivity) _
  have hHsum : ∑ x ∈ S, ∑ y ∈ S, ‖RHTower.dyadicSmoothGram N (x - y)‖ ≤
      3 * (2 * τ₁ + 1) * S.card + (N : ℝ) ^ (-(1 / 2) : ℝ) * (Real.sqrt Real.pi * Y) +
        (S.card : ℝ) ^ 2 * E := by
    calc ∑ x ∈ S, ∑ y ∈ S, ‖RHTower.dyadicSmoothGram N (x - y)‖
        ≤ ∑ x ∈ S, ∑ y ∈ S, ((if |x - y| ≤ τ₁ then (3 : ℝ) else 0) + (N : ℝ) ^ (-(1 / 2) : ℝ) *
          (∫ v : ℝ, Real.exp (-(v ^ 2)) *
            ‖RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((x - y + v : ℝ) : ℂ) * I)‖) + E) :=
          Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpair x hx y hy
      _ = ∑ x ∈ S, ∑ y ∈ S, (if |x - y| ≤ τ₁ then (3 : ℝ) else 0) + (N : ℝ) ^ (-(1 / 2) : ℝ) *
          (∑ x ∈ S, ∑ y ∈ S, ∫ v : ℝ, Real.exp (-(v ^ 2)) *
            ‖RHTower.dualPartialSum M (((1 / 2 : ℝ) : ℂ) + ((x - y + v : ℝ) : ℂ) * I)‖) +
          (S.card : ℝ) ^ 2 * E := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ 3 * (2 * τ₁ + 1) * S.card + (N : ℝ) ^ (-(1 / 2) : ℝ) * (Real.sqrt Real.pi * Y) +
          (S.card : ℝ) ^ 2 * E := by
          have h1 : ∑ x ∈ S, ∑ y ∈ S, (if |x - y| ≤ τ₁ then (3 : ℝ) else 0) ≤
              3 * (2 * τ₁ + 1) * S.card := by
            calc _ ≤ ∑ _x ∈ S, 3 * (2 * τ₁ + 1) := Finset.sum_le_sum hnearsum
              _ = 3 * (2 * τ₁ + 1) * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
          have h2 := mul_le_mul_of_nonneg_left hJsum
            (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N) (-(1 / 2) : ℝ))
          linarith
  -- Halász–Montgomery
  have hHM := sq_sum_norm_blockPoly_le_gram hN c S
  have hlow : (S.card : ℝ) * V ≤ ∑ x ∈ S, ‖blockPoly N c 1 x‖ := by
    have := Finset.card_nsmul_le_sum S (fun x => ‖blockPoly N c 1 x‖) V hbig
    rwa [nsmul_eq_mul] at this
  have hH0 : 0 ≤ ∑ x ∈ S, ∑ y ∈ S, ‖RHTower.dyadicSmoothGram N (x - y)‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hmain : (S.card : ℝ) ^ 2 * V ^ 2 ≤ 20 * G * (3 * (2 * τ₁ + 1) * S.card +
      Real.sqrt Real.pi / Real.sqrt N * Y + (S.card : ℝ) ^ 2 * E) := by
    have hNsq : (N : ℝ) ^ (-(1 / 2) : ℝ) * (Real.sqrt Real.pi * Y) =
        Real.sqrt Real.pi / Real.sqrt N * Y := by
      rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]; ring
    rw [← hNsq]
    calc (S.card : ℝ) ^ 2 * V ^ 2 = ((S.card : ℝ) * V) ^ 2 := by ring
      _ ≤ (∑ x ∈ S, ‖blockPoly N c 1 x‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hlow 2
      _ ≤ 20 * (∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ ^ 2 / (n : ℝ)) *
          ∑ x ∈ S, ∑ y ∈ S, ‖RHTower.dyadicSmoothGram N (x - y)‖ := hHM
      _ ≤ 20 * G * ∑ x ∈ S, ∑ y ∈ S, ‖RHTower.dyadicSmoothGram N (x - y)‖ :=
          mul_le_mul_of_nonneg_right (by linarith) hH0
      _ ≤ 20 * G * (3 * (2 * τ₁ + 1) * S.card + (N : ℝ) ^ (-(1 / 2) : ℝ) *
          (Real.sqrt Real.pi * Y) + (S.card : ℝ) ^ 2 * E) :=
          mul_le_mul_of_nonneg_left hHsum (by positivity)
  have hYpow : Y ^ (2 * k) ≤ (S.card : ℝ) ^ (4 * k - 1) * Φ := by
    rw [hYdef, Real.rpow_inv_natCast_pow (by positivity) (by omega)]
  have hb : 0 < Real.sqrt Real.pi / Real.sqrt N :=
    div_pos (Real.sqrt_pos.2 Real.pi_pos) (Real.sqrt_pos.2 (by positivity))
  have hsmall' : 20 * G * E ≤ V ^ 2 / 4 := by rw [hE]; exact hsmall
  have ha : 0 ≤ 3 * (2 * τ₁ + 1) := by linarith
  have hmain' : (S.card : ℝ) ^ 2 * V ^ 2 ≤ 20 * G * (3 * (2 * τ₁ + 1) * S.card +
      Real.sqrt Real.pi / Real.sqrt N * Y + (S.card : ℝ) ^ 2 * E) := hmain
  exact jutila_local_arith hk hR hV hG0 ha hb hΦ0 hmain' hsmall' hYpow

end

end RHTower.Sieve

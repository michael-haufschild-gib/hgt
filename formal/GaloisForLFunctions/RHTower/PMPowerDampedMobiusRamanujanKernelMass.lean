import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanKernel

/-!
# Uniform `r^(−1/2)`-weighted mass of the Ramanujan transfer kernel

For a finite set of primes `S` define `A_S(m) = ∏_{p∈S} (1 if p | m, else 1/(p^(1+ε) − 1))`.
Splitting `∑_m` according to `p | m` and using `|w_ε(pm)| = |w_ε(m)|/(p^(1+ε) − 1)` for `p ∤ m`
gives the exact column sums `∑_m |w_ε(m)| A_S(m) = ∏_{p∈S} 2p^(−1−ε)`, starting from
`∑_m |w_ε(m)| = 1`. Hence the transfer kernel has row mass
`∑_m |T_m(r)| = r^(−ε) ∏_{p|r} 2p^(−1−ε)`. The multiplicative majorant
`M(n) = n^(−1/2) ∏_{p|n} 2/p` is summable by an Euler-product criterion, and dominates the
`r^(−1/2)`-weighted row masses for every `ε > 0`. Consequently the weighted kernel mass
`∑_{m≤Q} ∑_{r≤Q/m} |T_m(r)| r^(−1/2)` is bounded by `∑_r M(r)`, uniformly in `Q` and in `ε > 0`.

## Main results

- `tsum_pmPowerDampedRamanujanAbsProduct`: `∑'_m |w_ε(m)| A_S(m) = ∏_{p∈S} 2p^(−(1+ε))` for a finite set of primes `S`.
- `hasSum_norm_pmPowerDampedRamanujanTransfer`: `∑_m |T_m(r)| = r^(−ε) ∏_{p|r} 2p^(−(1+ε))` for `r ≠ 0`.
- `pm_summable_of_multiplicative_local_bound`: a nonnegative multiplicative `f` with `∑_k f(p^k) ≤ exp(b_p)` and `∑ b_p < ∞` is summable.
- `summable_pmRamanujanKernelMajorant`: `∑_n n^(−1/2) ∏_{p|n} 2/p` converges.
- `pmPowerDampedRamanujanTransfer_weighted_row_le_majorant`: `∑_m |T_m(r)| r^(−1/2) ≤ M(r)`.
- `summable_pmPowerDampedRamanujanTransfer_weighted_pair`: `(r, m) ↦ |T_m(r)| r^(−1/2)` is summable.
- `pmPowerDampedRamanujanTransfer_finite_mass_le`: `∑_{m≤Q} ∑_{r≤Q/m} |T_m(r)| r^(−1/2) ≤ ∑'_r M(r)`.

## Hypotheses

All results are unconditional; they assume `0 < ε` and, where stated, that `S` consists of
primes. The final bound is uniform in both `Q` and `ε > 0`.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

/-- For `ε > 0` and prime `p`: `|w_ε(pn)| = 0` if `p | n`, else `|w_ε(n)|/(p^(1+ε) − 1)`. -/
theorem norm_pmPowerDampedRamanujanWeight_prime_mul {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ‖pmPowerDampedRamanujanWeight ε (p*n)‖ =
      if p ∣ n then 0 else ‖pmPowerDampedRamanujanWeight ε n‖/((p : ℝ)^(1+ε)-1) := by
  by_cases hpn : p ∣ n
  · have hns : ¬Squarefree (p*n) := fun hs =>
      (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)) hpn
    simp [hpn, pmPowerDampedRamanujanWeight_eq_zero_of_not_squarefree ε hns]
  · rw [if_neg hpn, pmPowerDampedRamanujanWeight_prime_mul hε hp hpn,
      norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (lt_trans (by norm_num)
        (pmPowerDampedRamanujan_prime_denominator_one_lt hε hp))]

/-- For a prime `p ∉ S` (with `S` a set of primes), `A_S(pn) = A_S(n)`. -/
theorem pmPowerDampedRamanujanAbsProduct_prime_mul (ε : ℝ)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) (n : ℕ) :
    pmPowerDampedRamanujanAbsProduct ε S (p*n) =
      pmPowerDampedRamanujanAbsProduct ε S n := by
  apply Finset.prod_congr rfl
  intro q hq
  have hqp : ¬q ∣ p := by
    intro hd
    rcases (Nat.dvd_prime hp).mp hd with h1 | heq
    · exact (hS q hq).ne_one h1
    · exact hpS (heq ▸ hq)
  simp only [(hS q hq).dvd_mul, hqp, false_or]

/-- For `ε > 0`, `m ↦ |w_ε(m)| A_S(m)` is summable. -/
theorem summable_pmPowerDampedRamanujanAbsProduct_weight {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Summable (fun m : ℕ => ‖pmPowerDampedRamanujanWeight ε m‖*
      pmPowerDampedRamanujanAbsProduct ε S m) := by
  apply Summable.of_nonneg_of_le
    (fun m => mul_nonneg (norm_nonneg _) (pmPowerDampedRamanujanAbsProduct_nonneg hε S hS m))
    (fun m => mul_le_of_le_one_right (norm_nonneg _) (pmPowerDampedRamanujanAbsProduct_le_one hε S hS m))
    (hasSum_norm_pmPowerDampedRamanujanWeight hε).summable

/-- Reindexing `∑'_n 1_{p|n} f(n) = ∑'_n f(pn)` for `p > 0`. -/
theorem pm_real_tsum_dvd (f : ℕ → ℝ) {p : ℕ} (hp : 0 < p) :
    (∑' n : ℕ, if p ∣ n then f n else 0) = ∑' n : ℕ, f (p*n) := by
  classical
  let F : ℕ → ℝ := fun n => if p ∣ n then f n else 0
  have hinj : Function.Injective (fun n : ℕ => p*n) :=
    fun a b hab => Nat.eq_of_mul_eq_mul_left hp hab
  have hsupp : Function.support F ⊆ Set.range (fun n : ℕ => p*n) := by
    intro n hn
    rw [Function.mem_support] at hn
    by_cases hd : p ∣ n
    · rcases hd with ⟨k, rfl⟩; exact ⟨k, rfl⟩
    · exact (hn (by simp [F, hd])).elim
  rw [← hinj.tsum_eq (f := F) hsupp]
  exact tsum_congr fun n => by simp [F]

/-- For `ε > 0` and a new prime `p ∉ S`, adding `p` to `S` multiplies `∑'_m |w_ε(m)| A_S(m)`
by `2p^(−(1+ε))`. -/
theorem tsum_pmPowerDampedRamanujanAbsProduct_insert {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) :
    (∑' n : ℕ, ‖pmPowerDampedRamanujanWeight ε n‖*
      pmPowerDampedRamanujanAbsProduct ε (insert p S) n) =
      (2*(p : ℝ)^(-(1+ε)))*(∑' n : ℕ, ‖pmPowerDampedRamanujanWeight ε n‖*
        pmPowerDampedRamanujanAbsProduct ε S n) := by
  let F : ℕ → ℝ := fun n => ‖pmPowerDampedRamanujanWeight ε n‖*
    pmPowerDampedRamanujanAbsProduct ε S n
  let D : ℕ → ℝ := fun n => if p ∣ n then F n else 0
  let J : ℝ := (p : ℝ)^(1+ε)-1
  let X : ℝ := ∑' n, F n
  let T : ℝ := ∑' n, D n
  have hF := summable_pmPowerDampedRamanujanAbsProduct_weight hε S hS
  have hF0 (n : ℕ) : 0 ≤ F n := mul_nonneg (norm_nonneg _)
    (pmPowerDampedRamanujanAbsProduct_nonneg hε S hS n)
  have hD : Summable D := by
    apply Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hF
    · dsimp only [D]
      split_ifs
      · exact hF0 n
      · exact le_rfl
    · dsimp only [D]
      split_ifs
      · exact le_rfl
      · exact hF0 n
  have hrow (n : ℕ) : F (p*n) = (F n-D n)/J := by
    dsimp only [F, D, J]
    rw [norm_pmPowerDampedRamanujanWeight_prime_mul hε hp,
      pmPowerDampedRamanujanAbsProduct_prime_mul ε S hS hp hpS]
    split_ifs <;> ring
  have hT : T = (X-T)/J := by
    calc
      T = ∑' n : ℕ, F (p*n) := pm_real_tsum_dvd F hp.pos
      _ = (∑' n : ℕ, (F n - D n))/J := by rw [tsum_congr hrow, tsum_div_const]
      _ = (X-T)/J := by rw [hF.tsum_sub hD]
  have hJ : J ≠ 0 := ne_of_gt (lt_trans (by norm_num)
    (pmPowerDampedRamanujan_prime_denominator_one_lt hε hp))
  have hTX : T*(p : ℝ)^(1+ε) = X := by
    have h := (eq_div_iff hJ).mp hT
    dsimp only [J] at h
    nlinarith
  have hterm (n : ℕ) :
      ‖pmPowerDampedRamanujanWeight ε n‖*
        pmPowerDampedRamanujanAbsProduct ε (insert p S) n =
      D n+(F n-D n)/J := by
    rw [pmPowerDampedRamanujanAbsProduct, Finset.prod_insert hpS]
    dsimp only [D, F, J, pmPowerDampedRamanujanAbsProduct]
    split_ifs <;> ring
  calc
    _ = T+(X-T)/J := by
      rw [tsum_congr hterm, hD.tsum_add ((hF.sub hD).div_const J),
        tsum_div_const, hF.tsum_sub hD]
    _ = 2*T := by rw [← hT]; ring
    _ = _ := by
      change 2*T = 2*(p : ℝ)^(-(1+ε))*X
      rw [← hTX, Real.rpow_neg (Nat.cast_nonneg p)]
      have hp0 : (p : ℝ)^(1+ε) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _)
      field_simp

/-- For `ε > 0` and a finite set of primes `S`, `∑'_m |w_ε(m)| A_S(m) = ∏_{p∈S} 2p^(−(1+ε))`. -/
theorem tsum_pmPowerDampedRamanujanAbsProduct {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑' m : ℕ, ‖pmPowerDampedRamanujanWeight ε m‖*
      pmPowerDampedRamanujanAbsProduct ε S m) =
      ∏ p ∈ S, 2*(p : ℝ)^(-(1+ε)) := by
  induction S using Finset.induction_on with
  | empty =>
    simpa only [pmPowerDampedRamanujanAbsProduct, Finset.prod_empty, mul_one] using
      (hasSum_norm_pmPowerDampedRamanujanWeight hε).tsum_eq
  | @insert p S hpS ih =>
    have hp := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    rw [tsum_pmPowerDampedRamanujanAbsProduct_insert hε S hS' hp hpS,
      ih hS', Finset.prod_insert hpS]

/-- For `ε > 0` and `r ≠ 0`, the transfer kernel row mass is
`∑_m |T_m(r)| = r^(−ε) ∏_{p|r} 2p^(−(1+ε))`. -/
theorem hasSum_norm_pmPowerDampedRamanujanTransfer {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hr : r ≠ 0) :
    HasSum (fun m : ℕ => ‖pmPowerDampedRamanujanTransfer ε m r‖)
      ((r : ℝ)^(-ε)*(∏ p ∈ r.primeFactors, 2*(p : ℝ)^(-(1+ε)))) := by
  have hS : ∀ p ∈ r.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hs := (summable_pmPowerDampedRamanujanAbsProduct_weight hε r.primeFactors hS).hasSum
  rw [tsum_pmPowerDampedRamanujanAbsProduct hε r.primeFactors hS] at hs
  apply (hs.mul_left ((r : ℝ)^(-ε))).congr_fun
  intro m
  rw [norm_pmPowerDampedRamanujanTransfer hε m hr]
  ring

/-- Euler-product summability criterion: a nonnegative multiplicative `f` whose prime-power
series satisfy `∑_k f(p^k) ≤ exp(b_p)`, with `b ≥ 0` summable, is summable over `ℕ`. -/
theorem pm_summable_of_multiplicative_local_bound (f : ArithmeticFunction ℝ)
    (hm : f.IsMultiplicative) (hf0 : ∀ n, 0 ≤ f n)
    (hloc : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => f (p^k)))
    (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n) (hb : Summable b)
    (hbound : ∀ {p : ℕ}, p.Prime → (∑' k : ℕ, f (p^k)) ≤ Real.exp (b p)) :
    Summable (fun n : ℕ => f n) := by
  classical
  refine summable_of_sum_range_le (c := Real.exp (∑' n, b n)) hf0 fun N => ?_
  have hnorm : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => ‖f (p^k)‖) := by
    intro p hp
    simpa only [Real.norm_of_nonneg (hf0 _)] using hloc hp
  have hhas := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n => f n) hm.map_one (fun h => hm.map_mul_of_coprime h) hnorm (Finset.range N)).2
  have hsub : ∀ n ∈ (Finset.range N).filter (· ≠ 0), n ∈ Nat.factoredNumbers (Finset.range N) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    refine Nat.mem_factoredNumbers.mpr ⟨hn.2, fun p hp => ?_⟩
    exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.le_of_mem_primeFactorsList hp) hn.1)
  have hrange : (∑ n ∈ Finset.range N, f n) =
      ∑ n ∈ (Finset.range N).filter (· ≠ 0), f n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs with h
    · rfl
    · have hz : n = 0 := by simpa using h
      subst n; simp
  have hle : (∑ n ∈ (Finset.range N).filter (· ≠ 0), f n) ≤
      ∏ p ∈ Finset.range N with p.Prime, ∑' k : ℕ, f (p^k) := by
    rw [← Finset.sum_subtype_of_mem (fun n => f n) hsub]
    exact sum_le_hasSum _ (fun n _ => hf0 n) hhas
  have hprod : (∏ p ∈ Finset.range N with p.Prime, ∑' k : ℕ, f (p^k)) ≤
      Real.exp (∑ p ∈ Finset.range N with p.Prime, b p) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod (fun p _ => tsum_nonneg fun k => hf0 _)
      (fun p hp => hbound (Finset.mem_filter.mp hp).2)
  rw [hrange]
  exact hle.trans (hprod.trans (Real.exp_le_exp.mpr
    (hb.sum_le_tsum _ (fun p _ => hb0 p))))

/-- The multiplicative majorant `M(n) = n^(−1/2) ∏_{p|n} 2/p`. -/
def pmRamanujanKernelMajorant : ArithmeticFunction ℝ where
  toFun n := (n : ℝ)^(-1/2 : ℝ)*ArithmeticFunction.prodPrimeFactors (fun p => 2/(p : ℝ)) n
  map_zero' := by simp

theorem pmRamanujanKernelMajorant_apply {n : ℕ} (hn : n ≠ 0) :
    pmRamanujanKernelMajorant n = (n : ℝ)^(-1/2 : ℝ)*(∏ p ∈ n.primeFactors, 2/(p : ℝ)) := by
  simp only [pmRamanujanKernelMajorant, ArithmeticFunction.coe_mk,
    ArithmeticFunction.prodPrimeFactors_apply hn]

theorem pmRamanujanKernelMajorant_nonneg (n : ℕ) : 0 ≤ pmRamanujanKernelMajorant n := by
  by_cases hn : n = 0
  · subst n; simp
  rw [pmRamanujanKernelMajorant_apply hn]
  apply mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  exact Finset.prod_nonneg fun p _ => by positivity

/-- The majorant `M` is multiplicative. -/
theorem isMultiplicative_pmRamanujanKernelMajorant : pmRamanujanKernelMajorant.IsMultiplicative := by
  constructor
  · simp [pmRamanujanKernelMajorant]
  · intro m n hmn
    change ((m*n : ℕ) : ℝ)^(-1/2 : ℝ)*ArithmeticFunction.prodPrimeFactors _ (m*n) = _
    rw [(ArithmeticFunction.IsMultiplicative.prodPrimeFactors (fun p => 2/(p : ℝ))).map_mul_of_coprime hmn]
    simp only [pmRamanujanKernelMajorant, ArithmeticFunction.coe_mk, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring

theorem pmRamanujanKernelMajorant_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    pmRamanujanKernelMajorant (p^k) = (2/(p : ℝ))*((p : ℝ)^(-1/2 : ℝ))^k := by
  rw [pmRamanujanKernelMajorant_apply (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton, Nat.cast_pow,
    ← Real.rpow_natCast_mul (Nat.cast_nonneg p)]
  rw [mul_comm (k : ℝ) (-1/2), Real.rpow_mul_natCast (Nat.cast_nonneg p)]
  ring

/-- For prime `p`, `∑_k M(p^k) = 1 + (2/p) p^(−1/2)/(1 − p^(−1/2))`. -/
theorem hasSum_pmRamanujanKernelMajorant_prime_pow {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => pmRamanujanKernelMajorant (p^k))
      (1+(2/(p : ℝ))*(p : ℝ)^(-1/2 : ℝ)/(1-(p : ℝ)^(-1/2 : ℝ))) := by
  let q : ℝ := (p : ℝ)^(-1/2 : ℝ)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp.one_lt) (by norm_num)
  have htail : HasSum (fun k : ℕ => pmRamanujanKernelMajorant (p^(k+1)))
      ((2/(p : ℝ))*q/(1-q)) := by
    have hgeom := (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((2/(p : ℝ))*q)
    have heq : (2/(p : ℝ))*q*(1-q)⁻¹ = (2/(p : ℝ))*q/(1-q) := by ring
    rw [heq] at hgeom
    apply hgeom.congr_fun
    intro k
    rw [pmRamanujanKernelMajorant_prime_pow hp (Nat.succ_ne_zero k), pow_succ]
    dsimp only [q]
    ring
  have h := (hasSum_nat_add_iff (f := fun k : ℕ => pmRamanujanKernelMajorant (p^k)) 1).mp htail
  simpa only [Finset.sum_range_one, pow_zero, isMultiplicative_pmRamanujanKernelMajorant.map_one,
    add_comm, q] using h

/-- For prime `p`, `∑_k M(p^k) ≤ exp(C p^(−3/2))` with `C = 2/(1 − 2^(−1/2))`. -/
theorem pmRamanujanKernelMajorant_prime_sum_le_exp {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, pmRamanujanKernelMajorant (p^k)) ≤
      Real.exp ((2/(1-(2 : ℝ)^(-1/2 : ℝ)))*(p : ℝ)^(-3/2 : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq2 : (2 : ℝ)^(-1/2 : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hq : (p : ℝ)^(-1/2 : ℝ) ≤ (2 : ℝ)^(-1/2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by norm_num)
  have htail : (2/(p : ℝ))*(p : ℝ)^(-1/2 : ℝ)/(1-(p : ℝ)^(-1/2 : ℝ)) ≤
      (2/(1-(2 : ℝ)^(-1/2 : ℝ)))*(p : ℝ)^(-3/2 : ℝ) := by
    calc
      _ ≤ (2/(p : ℝ))*(p : ℝ)^(-1/2 : ℝ)/(1-(2 : ℝ)^(-1/2 : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
      _ = _ := by
        rw [show (-3/2 : ℝ) = -1+(-1/2) by ring, Real.rpow_add hp0, Real.rpow_neg_one]
        ring
  rw [(hasSum_pmRamanujanKernelMajorant_prime_pow hp).tsum_eq]
  calc
    _ ≤ 1+(2/(1-(2 : ℝ)^(-1/2 : ℝ)))*(p : ℝ)^(-3/2 : ℝ) := by simpa only [add_comm] using add_le_add_left htail 1
    _ ≤ _ := by
      simpa only [add_comm] using
        Real.add_one_le_exp ((2/(1-(2 : ℝ)^(-1/2 : ℝ)))*(p : ℝ)^(-3/2 : ℝ))

/-- The majorant `M(n) = n^(−1/2) ∏_{p|n} 2/p` is summable. -/
theorem summable_pmRamanujanKernelMajorant : Summable (fun n : ℕ => pmRamanujanKernelMajorant n) := by
  let C : ℝ := 2/(1-(2 : ℝ)^(-1/2 : ℝ))
  have hC : 0 ≤ C := by
    have h := Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (z := (-1/2 : ℝ))
      (by norm_num) (by norm_num)
    exact div_nonneg (by norm_num) (by linarith)
  exact pm_summable_of_multiplicative_local_bound pmRamanujanKernelMajorant
    isMultiplicative_pmRamanujanKernelMajorant pmRamanujanKernelMajorant_nonneg
    (fun hp => (hasSum_pmRamanujanKernelMajorant_prime_pow hp).summable)
    (fun n => C*(n : ℝ)^(-3/2 : ℝ)) (fun n => mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    ((Real.summable_nat_rpow.mpr (by norm_num : (-3/2 : ℝ) < -1)).mul_left C)
    (fun hp => pmRamanujanKernelMajorant_prime_sum_le_exp hp)

/-- For `ε > 0`, each weighted row `m ↦ |T_m(r)| r^(−1/2)` is summable. -/
theorem summable_pmPowerDampedRamanujanTransfer_weighted_row {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    Summable (fun m : ℕ => ‖pmPowerDampedRamanujanTransfer ε m r‖*(r : ℝ)^(-1/2 : ℝ)) := by
  by_cases hr : r = 0
  · subst r; simp
  · exact (hasSum_norm_pmPowerDampedRamanujanTransfer hε hr).summable.mul_right _

/-- For `ε > 0` and `r ≠ 0`, `∑'_m |T_m(r)| r^(−1/2) = r^(−(ε+1/2)) ∏_{p|r} 2p^(−(1+ε))`. -/
theorem tsum_pmPowerDampedRamanujanTransfer_weighted_row {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hr : r ≠ 0) :
    (∑' m : ℕ, ‖pmPowerDampedRamanujanTransfer ε m r‖*(r : ℝ)^(-1/2 : ℝ)) =
      (r : ℝ)^(-(ε+1/2))*(∏ p ∈ r.primeFactors, 2*(p : ℝ)^(-(1+ε))) := by
  rw [tsum_mul_right, (hasSum_norm_pmPowerDampedRamanujanTransfer hε hr).tsum_eq,
    show -(ε+1/2) = -ε+(-1/2) by ring,
    Real.rpow_add (by exact_mod_cast Nat.pos_of_ne_zero hr)]
  ring

/-- For `ε > 0`, the weighted row mass is dominated by the majorant: `∑'_m |T_m(r)| r^(−1/2) ≤ M(r)`. -/
theorem pmPowerDampedRamanujanTransfer_weighted_row_le_majorant {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    (∑' m : ℕ, ‖pmPowerDampedRamanujanTransfer ε m r‖*(r : ℝ)^(-1/2 : ℝ)) ≤
      pmRamanujanKernelMajorant r := by
  by_cases hr : r = 0
  · subst r; simp
  rw [tsum_pmPowerDampedRamanujanTransfer_weighted_row hε hr,
    pmRamanujanKernelMajorant_apply hr]
  have hpow : (r : ℝ)^(-(ε+1/2)) ≤ (r : ℝ)^(-1/2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr) (by linarith)
  have hprod : (∏ p ∈ r.primeFactors, 2*(p : ℝ)^(-(1+ε))) ≤
      ∏ p ∈ r.primeFactors, 2/(p : ℝ) := by
    apply Finset.prod_le_prod (fun p _ => mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    intro p hp
    have h := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le : (1 : ℝ) ≤ p)
      (by linarith : -(1+ε) ≤ (-1 : ℝ))
    simpa only [Real.rpow_neg_one, div_eq_mul_inv] using mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  exact mul_le_mul hpow hprod (Finset.prod_nonneg fun p _ =>
    mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    (Real.rpow_nonneg (Nat.cast_nonneg r) _)

/-- For `ε > 0`, `(r, m) ↦ |T_m(r)| r^(−1/2)` is summable over `ℕ × ℕ`. -/
theorem summable_pmPowerDampedRamanujanTransfer_weighted_pair {ε : ℝ} (hε : 0 < ε) :
    Summable (fun x : ℕ × ℕ => ‖pmPowerDampedRamanujanTransfer ε x.2 x.1‖*
      (x.1 : ℝ)^(-1/2 : ℝ)) := by
  apply (summable_prod_of_nonneg (fun x => mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg x.1) _))).mpr
  exact ⟨summable_pmPowerDampedRamanujanTransfer_weighted_row hε,
    Summable.of_nonneg_of_le
      (fun r => tsum_nonneg fun m => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg r) _))
      (pmPowerDampedRamanujanTransfer_weighted_row_le_majorant hε)
      summable_pmRamanujanKernelMajorant⟩

/-- For `ε > 0`, `∑_{m≤Q} ∑_{r≤Q/m} |T_m(r)| r^(−1/2) ≤ ∑'_r M(r)`, a bound independent of
`Q` and `ε`. -/
theorem pmPowerDampedRamanujanTransfer_finite_mass_le {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    (∑ m ∈ Finset.Icc 1 Q, ∑ r ∈ Finset.Icc 1 (Q/m),
      ‖pmPowerDampedRamanujanTransfer ε m r‖*(r : ℝ)^(-1/2 : ℝ)) ≤
      ∑' r : ℕ, pmRamanujanKernelMajorant r := by
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 Q, ∑ r ∈ Finset.Icc 1 Q,
        ‖pmPowerDampedRamanujanTransfer ε m r‖*(r : ℝ)^(-1/2 : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
          (Finset.mem_Icc.mp hr).2.trans (Nat.div_le_self Q m)⟩
      · intro r _ _
        exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg r) _)
    _ = ∑ r ∈ Finset.Icc 1 Q, ∑ m ∈ Finset.Icc 1 Q,
        ‖pmPowerDampedRamanujanTransfer ε m r‖*(r : ℝ)^(-1/2 : ℝ) := Finset.sum_comm
    _ ≤ ∑ r ∈ Finset.Icc 1 Q, pmRamanujanKernelMajorant r := by
      apply Finset.sum_le_sum
      intro r hr
      exact ((summable_pmPowerDampedRamanujanTransfer_weighted_row hε r).sum_le_tsum
        (Finset.Icc 1 Q) (fun m _ => mul_nonneg (norm_nonneg _)
          (Real.rpow_nonneg (Nat.cast_nonneg r) _))).trans
        (pmPowerDampedRamanujanTransfer_weighted_row_le_majorant hε r)
    _ ≤ _ := summable_pmRamanujanKernelMajorant.sum_le_tsum _
      (fun r _ => pmRamanujanKernelMajorant_nonneg r)

end RHTower

import GaloisForLFunctions.SurfaceOfSpecZ.PositiveCosineSumsOutsideASmallArc
import GaloisForLFunctions.SurfaceOfSpecZ.ConfigurationsNeedAnAttainedTopAtFinitelyManyFrobenii
import GaloisForLFunctions.SurfaceOfSpecZ.AlmostAllPrimesSuffice
import GaloisForLFunctions.RHTower.PrimeShortIntervalsHuxleyAsymptotic
import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant
import GaloisForLFunctions.RHTower.WeilLagFunctionDensityZeroExcursion

/-!
# Zero configurations need an attained top at almost all primes

`AlmostAllPrimesSuffice` proves that a lower bound `2 Re S_Z(log p) ≥ −K` outside a prime set `E`
of relative logarithmic density zero forces every zero of a real-zero-free tempered configuration
`Z` onto the critical line *provided* `sup Re ρ` is attained. This file proves that the attainment
hypothesis cannot be dropped:

* `exists_zeroConfig_primes_off_null_bddBelow_nonattained`: for every `0 < Θ ≤ ½` there exist a
  tempered zero configuration `Z` in `0 < Re s < 1` without real zeros whose real parts have
  unattained supremum `½ + Θ`, a measurable set `S ⊆ ℝ` of upper density zero, and a prime set `E`
  of both Chebyshev prime density zero and relative logarithmic density zero, such that
  `2 Re S_Z(u) ≥ −5` for all `u ≥ 0` outside `S` and `2 Re S_Z(log p) ≥ −5` for every prime
  `p ∉ E`.
* `exists_zeroConfig_primes_off_null_bddBelow_sup_eq_one`: the extreme case `Θ = ½` (`sup Re ρ = 1`).
* `not_forall_onLine_of_bddBelow_primes_off_null`: negation of the unattained almost-all-primes
  implication for tempered configurations.

**Mechanism.** Level `k` replaces the single resonant pair of
`ConfigurationsNeedAnAttainedTopAtFinitelyManyFrobenii` by a finite harmonic cluster
`½ ± x_k + 2πi m B_k` (`1 ≤ m ≤ M_k`) weighted by `p_{k,m} m^8`, where `(M_k, p_k, η_k)` is the
positive cosine polynomial outside `|t − (n + ½)| < δ_k / 2` (`δ_k = 1 / (k + 4)`) from
`PositiveCosineSumsOutsideASmallArc`. Multiplying `sinc(2π m B_k − ix_k)^8` by `m^8` removes its
dependence on `m` up to `O(1 / B_k)`, so the cluster trace is positive outside a `1 / B_k`-periodic
hole union of fractional measure `δ_k`. Choosing `B_{k+1}` after `U_k` and integer window endpoints
`U_{k+1}` after `B_{k+1}` makes each sub-hole wide enough (`≥ x^{3/4}` in prime coordinates) for
Huxley's short-interval bound to control the prime logarithmic mass block by block.
-/

open Complex Filter Topology MeasureTheory Set
open scoped ComplexConjugate Chebyshev Classical

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open ArithmeticFunction

/-! ### Window dominance with a separate positivity floor -/

/-- **General dominance lemma.** On `U_k ≤ λ ≤ U_{k+1}`, if `|a_j|, |b_j| ≤ w_j` with geometric-decay
tower ceilings on `w_j`, `a_k ≥ 0`, `a_{k+1} ≥ 0`, and `e^{(x_k − x_{k−1}) U_k} a_k ≥ 4` for `k ≥ 1`,
then `∑_j (e^{x_j λ} a_j + e^{−x_j λ} b_j) ≥ −5`. -/
theorem neg_five_le_tsum_of_window_general {Θ : ℝ} (hΘ : 0 < Θ) {x w U a b : ℕ → ℝ}
    (hx0 : ∀ j, 0 ≤ x j) (hxΘ : ∀ j, x j ≤ Θ) (hxm : Monotone x) (hw : ∀ j, 0 ≤ w j)
    (hw0 : w 0 ≤ 1) (hwhi : ∀ j, w (j + 1) ≤ (1 / 2) ^ (j + 1) * Real.exp (-(Θ * U j)))
    (hUm : Monotone U) (hU0 : 0 ≤ U 0) (ha : ∀ j, |a j| ≤ w j) (hb : ∀ j, |b j| ≤ w j)
    {lam : ℝ} (hlam : 0 ≤ lam) {k : ℕ} (hkl : U k ≤ lam) (hku : lam ≤ U (k + 1))
    (hak : 0 ≤ a k) (hak1 : 0 ≤ a (k + 1))
    (hlo : ∀ n, k = n + 1 → 4 ≤ Real.exp ((x (n + 1) - x n) * U (n + 1)) * a (n + 1)) :
    -5 ≤ ∑' j, (Real.exp (x j * lam) * a j + Real.exp (-(x j * lam)) * b j) := by
  have hwg := weight_le_geom hw0 hwhi hΘ.le hUm hU0
  have hgeo : Summable fun j : ℕ => 2 * (1 / 2 : ℝ) ^ j :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2
  have hwsum : Summable w := Summable.of_nonneg_of_le hw hwg hgeo
  have hwtot : ∑' j, w j ≤ 4 := by
    calc ∑' j, w j ≤ ∑' j : ℕ, 2 * (1 / 2 : ℝ) ^ j := Summable.tsum_le_tsum hwg hwsum hgeo
      _ = 4 := by rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have hexpx : ∀ j, Real.exp (x j * lam) ≤ Real.exp (Θ * lam) := fun j =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hxΘ j) hlam)
  have hrefl1 : ∀ j, Real.exp (-(x j * lam)) ≤ 1 := fun j =>
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (hx0 j) hlam))
  have hmain : Summable fun j => Real.exp (x j * lam) * a j := by
    refine Summable.of_norm_bounded (hwsum.mul_left (Real.exp (Θ * lam))) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hexpx j) (ha j) (abs_nonneg _) (Real.exp_pos _).le
  have hrefl : Summable fun j => Real.exp (-(x j * lam)) * b j := by
    refine Summable.of_norm_bounded hwsum fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(x j * lam)) * |b j| ≤ 1 * |b j| :=
          mul_le_mul_of_nonneg_right (hrefl1 j) (abs_nonneg _)
      _ ≤ w j := by rw [one_mul]; exact hb j
  rw [hmain.tsum_add hrefl]
  have hR : -4 ≤ ∑' j, Real.exp (-(x j * lam)) * b j := by
    have h := Summable.tsum_le_tsum (fun j => neg_le_mul_of_abs_le (Real.exp_pos _).le
      (hrefl1 j) (hb j)) hwsum.neg hrefl
    rw [tsum_neg] at h
    linarith
  have htail := neg_one_le_tail hΘ.le hxΘ hwhi hUm ha hlam hku hmain
  have hhead : 0 ≤ ∑ j ∈ Finset.range k, Real.exp (x j * lam) * a j +
      Real.exp (x k * lam) * a k := by
    rcases k with _ | n
    · simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      exact mul_nonneg (Real.exp_pos _).le hak
    · have hlo' := hlo n rfl
      have hE : 0 < Real.exp (x n * lam) := Real.exp_pos _
      have hh : -(4 * Real.exp (x n * lam)) ≤
          ∑ j ∈ Finset.range (n + 1), Real.exp (x j * lam) * a j := by
        have h1 : ∀ j ∈ Finset.range (n + 1), -(Real.exp (x n * lam) * w j) ≤
            Real.exp (x j * lam) * a j := by
          intro j hj
          have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hx : Real.exp (x j * lam) ≤ Real.exp (x n * lam) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hxm hjn) hlam)
          have h2 := neg_mul_le_mul_of_abs_le (Real.exp_pos (x j * lam)).le (ha j)
          have h3 := mul_le_mul_of_nonneg_right hx (hw j)
          linarith
        have h2 := Finset.sum_le_sum h1
        have h3 : ∑ j ∈ Finset.range (n + 1), w j ≤ 4 :=
          (hwsum.sum_le_tsum _ (fun j _ => hw j)).trans hwtot
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at h2
        have h4 := mul_le_mul_of_nonneg_left h3 hE.le
        linarith
      have hk : 4 * Real.exp (x n * lam) ≤ Real.exp (x (n + 1) * lam) * a (n + 1) := by
        have hexp_le : Real.exp ((x (n + 1) - x n) * U (n + 1)) ≤
            Real.exp ((x (n + 1) - x n) * lam) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hkl
            (sub_nonneg.mpr (hxm (Nat.le_succ n))))
        have h6 : 4 ≤ Real.exp ((x (n + 1) - x n) * lam) * a (n + 1) :=
          hlo'.trans (mul_le_mul_of_nonneg_right hexp_le hak)
        have h2 : Real.exp (x (n + 1) * lam) =
            Real.exp (x n * lam) * Real.exp ((x (n + 1) - x n) * lam) := by
          rw [← Real.exp_add]; ring_nf
        have h7 := mul_le_mul_of_nonneg_left h6 hE.le
        rw [h2]
        linarith
      linarith
  have hk1 : 0 ≤ Real.exp (x (k + 1) * lam) * a (k + 1) := mul_nonneg (Real.exp_pos _).le hak1
  rw [← hmain.sum_add_tsum_nat_add (k + 2), Finset.sum_range_succ, Finset.sum_range_succ]
  linarith

/-! ### Single-cluster spline harmonics and periodic hole sets -/

namespace PeriodicClusterTower

/-- Periodic hole set of base frequency `B` and fractional width `δ`:
`{u ∈ ℝ | ∃ n ∈ ℤ, |B u − (n + ½)| < δ / 2}`. -/
def holeSet (B : ℕ) (δ : ℝ) : Set ℝ :=
  {u : ℝ | ∃ n : ℤ, |(B : ℝ) * u - (n + 1 / 2)| < δ / 2}

theorem dist_ge_of_notMem_holeSet {B : ℕ} {δ u : ℝ} (hu : u ∉ holeSet B δ) (n : ℤ) :
    δ / 2 ≤ |(B : ℝ) * u - (n + 1 / 2)| := by
  by_contra hlt
  exact hu ⟨n, not_le.mp hlt⟩

/-- Weighted cubic-spline harmonic `(p_m m^8) · sinc(2π m B − ix)^8`. -/
def clusterHarmonic (p : ℕ → ℕ) (B : ℕ) (x : ℝ) (m : ℕ) : ℂ :=
  ((p m * m ^ 8 : ℕ) : ℂ) * sincC (splinePoint (m * B) x) ^ 8

/-- Main exponential amplitude of a cluster at `u`. -/
def clusterMain (M : ℕ) (p : ℕ → ℕ) (B : ℕ) (x u : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    2 * (clusterHarmonic p B x m * cexp (((2 * Real.pi * (m * B : ℕ) * u : ℝ) : ℂ) * I)).re

/-- Reflected exponential amplitude of a cluster at `u`. -/
def clusterRefl (M : ℕ) (p : ℕ → ℕ) (B : ℕ) (x u : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    2 * (conj (clusterHarmonic p B x m) * cexp (((2 * Real.pi * (m * B : ℕ) * u : ℝ) : ℂ) * I)).re

theorem norm_pow_sub_one_le_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ n * ‖z - 1‖ := by
  rw [← geom_sum_mul, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖∑ i ∈ Finset.range n, z ^ i‖
      ≤ ∑ i ∈ Finset.range n, ‖z ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_pow]
          exact pow_le_one₀ (norm_nonneg z) hz
    _ = n := by simp

theorem norm_clusterHarmonic_le (p : ℕ → ℕ) {B m : ℕ} (hB : 1 ≤ B) (hm : 1 ≤ m)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    ‖clusterHarmonic p B x m‖ ≤ (p m : ℝ) / (B : ℝ) ^ 8 := by
  have hmB : 1 ≤ m * B := Nat.mul_pos hm hB
  have hsinc : ‖sincC (splinePoint (m * B) x) ^ 8‖ ≤ 1 / ((m : ℝ) * B) ^ 8 := by
    simpa [Nat.cast_mul] using norm_sincPow_le hmB hx0 hx1 4
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  rw [clusterHarmonic, norm_mul, Complex.norm_natCast]
  calc ((p m * m ^ 8 : ℕ) : ℝ) * ‖sincC (splinePoint (m * B) x) ^ 8‖
      ≤ ((p m : ℝ) * (m : ℝ) ^ 8) * (1 / ((m : ℝ) * B) ^ 8) := by
        push_cast
        exact mul_le_mul_of_nonneg_left hsinc (by positivity)
    _ = (p m : ℝ) / (B : ℝ) ^ 8 := by
        field_simp

theorem abs_clusterMain_le (M : ℕ) (p : ℕ → ℕ) {B : ℕ} (hB : 1 ≤ B)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (u : ℝ) :
    |clusterMain M p B x u| ≤ 2 * (∑ m ∈ Finset.Icc 1 M, (p m : ℝ)) / (B : ℝ) ^ 8 := by
  unfold clusterMain
  calc |∑ m ∈ Finset.Icc 1 M,
          2 * (clusterHarmonic p B x m * cexp (((2 * Real.pi * (m * B : ℕ) * u : ℝ) : ℂ) * I)).re|
      ≤ ∑ m ∈ Finset.Icc 1 M,
          |2 * (clusterHarmonic p B x m *
            cexp (((2 * Real.pi * (m * B : ℕ) * u : ℝ) : ℂ) * I)).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 M, 2 * ((p m : ℝ) / (B : ℝ) ^ 8) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        rw [abs_mul, abs_two]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
        exact norm_clusterHarmonic_le p hB hm1 hx0 hx1
    _ = 2 * (∑ m ∈ Finset.Icc 1 M, (p m : ℝ)) / (B : ℝ) ^ 8 := by
        rw [← Finset.mul_sum, ← Finset.sum_div, mul_div_assoc]

theorem abs_clusterRefl_le (M : ℕ) (p : ℕ → ℕ) {B : ℕ} (hB : 1 ≤ B)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (u : ℝ) :
    |clusterRefl M p B x u| ≤ 2 * (∑ m ∈ Finset.Icc 1 M, (p m : ℝ)) / (B : ℝ) ^ 8 := by
  unfold clusterRefl
  calc |∑ m ∈ Finset.Icc 1 M,
          2 * (conj (clusterHarmonic p B x m) *
            cexp (((2 * Real.pi * (m * B : ℕ) * u : ℝ) : ℂ) * I)).re|
      ≤ ∑ m ∈ Finset.Icc 1 M,
          |2 * (conj (clusterHarmonic p B x m) *
            cexp (((2 * Real.pi * (m * B : ℕ) * u : ℝ) : ℂ) * I)).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 M, 2 * ((p m : ℝ) / (B : ℝ) ^ 8) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        rw [abs_mul, abs_two]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, mul_one]
        exact norm_clusterHarmonic_le p hB hm1 hx0 hx1
    _ = 2 * (∑ m ∈ Finset.Icc 1 M, (p m : ℝ)) / (B : ℝ) ^ 8 := by
        rw [← Finset.mul_sum, ← Finset.sum_div, mul_div_assoc]

/-- **Positivity of a cluster off its periodic hole set.** Because `(m : ℂ)^8` cancels the `m^8`
scaling of `splinePoint (m * B) x ^ 8` up to a relative error `≤ 1 / B`, a cosine polynomial with
floor `η D` outside `holeSet B δ` produces `clusterMain ≥ η D (x / (7 B))^8` once `B ≥ 2 / η`. -/
theorem clusterMain_ge_off_hole {M : ℕ} {p : ℕ → ℕ} {η δ : ℝ} (hη : 0 < η)
    (hcos : ∀ t : ℝ, (∀ n : ℤ, δ / 2 ≤ |t - (n + 1 / 2)|) →
      η * (∑ m ∈ Finset.Icc 1 M, (p m : ℝ)) ≤
        ∑ m ∈ Finset.Icc 1 M, (p m : ℝ) * Real.cos (2 * Real.pi * m * t))
    {B : ℕ} (hB1 : 1 ≤ B) (hBη : 2 / η ≤ B)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) {u : ℝ} (hu : u ∉ holeSet B δ) :
    η * (∑ m ∈ Finset.Icc 1 M, (p m : ℝ)) * (x / (7 * (B : ℝ))) ^ 8 ≤
      clusterMain M p B x u := by
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hBpos : (0 : ℝ) < B := by positivity
  set s : ℝ := (Real.sinh x / (2 * Real.pi * B)) ^ 8
  have hs0 : 0 ≤ s := by
    have : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx0
    positivity
  have hs_ge : (x / (7 * (B : ℝ))) ^ 8 ≤ s := by
    refine pow_le_pow_left₀ (by positivity) ?_ 8
    have hsinh : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx0
    have hpi : 2 * Real.pi * (B : ℝ) ≤ 7 * (B : ℝ) := by nlinarith [Real.pi_lt_d2]
    calc x / (7 * (B : ℝ)) ≤ Real.sinh x / (7 * (B : ℝ)) :=
          div_le_div_of_nonneg_right hsinh (by positivity)
      _ ≤ Real.sinh x / (2 * Real.pi * (B : ℝ)) :=
          div_le_div_of_nonneg_left (Real.sinh_nonneg_iff.mpr hx0) (by positivity) hpi
  -- Compare each harmonic to `(p m : ℝ) * s * cos(2π m B u)`
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      2 * (p m : ℝ) * s * Real.cos (2 * Real.pi * (m : ℝ) * ((B : ℝ) * u)) -
        2 * (p m : ℝ) * s * (1 / (B : ℝ)) ≤
      2 * (clusterHarmonic p B x m * cexp (((2 * Real.pi * (m * B : ℕ) * u : ℝ) : ℂ) * I)).re := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hmB : 1 ≤ m * B := Nat.mul_pos hm1 hB1
    set w : ℂ := splinePoint (m * B) x
    have hw0 : w ≠ 0 := splinePoint_ne_zero hmB x
    have hw_ge : 2 * Real.pi * (m * B : ℕ) ≤ ‖w‖ := norm_splinePoint_ge (m * B) x
    have hwn_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    set z : ℂ := ((2 * Real.pi * (m * B : ℕ) : ℝ) : ℂ) / w
    have hz_norm : ‖z‖ ≤ 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (m * B : ℕ))]
      exact (div_le_one hwn_pos).mpr hw_ge
    have hz_sub : ‖z - 1‖ ≤ 1 / (8 * (B : ℝ)) := by
      have hdiff : z - 1 = ((x : ℂ) * I) / w := by
        dsimp only [z]
        rw [div_sub_one hw0]
        congr 1
        dsimp only [w]
        rw [splinePoint]
        push_cast
        ring
      rw [hdiff, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0,
        Complex.norm_I, mul_one]
      have hden : 8 * (B : ℝ) ≤ 2 * ‖w‖ := by
        have hmB_R : (B : ℝ) ≤ (m * B : ℕ) := by push_cast; nlinarith
        nlinarith [Real.pi_gt_three]
      rw [div_le_div_iff₀ hwn_pos (by positivity)]
      nlinarith
    have hz8 : ‖z ^ 8 - 1‖ ≤ 1 / (B : ℝ) := by
      have h1 := norm_pow_sub_one_le_of_norm_le_one hz_norm 8
      push_cast at h1
      calc ‖z ^ 8 - 1‖ ≤ 8 * ‖z - 1‖ := h1
        _ ≤ 8 * (1 / (8 * (B : ℝ))) := mul_le_mul_of_nonneg_left hz_sub (by norm_num)
        _ = 1 / (B : ℝ) := by field_simp
    have hch : clusterHarmonic p B x m = (((p m : ℝ) * s : ℝ) : ℂ) * z ^ 8 := by
      rw [clusterHarmonic, show (8 : ℕ) = 2 * 4 by rfl, sincC_splinePoint_pow hmB x 4]
      dsimp only [s, z, w]
      have hm0 : ((m : ℂ)) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      have hB0c : ((B : ℂ)) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
      have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      push_cast
      field_simp
    set E : ℂ := cexp (((2 * Real.pi * (m * B : ℕ) * u : ℝ) : ℂ) * I)
    have hEn : ‖E‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hEre : E.re = Real.cos (2 * Real.pi * (m : ℝ) * ((B : ℝ) * u)) := by
      dsimp only [E]
      rw [Complex.exp_ofReal_mul_I_re]
      congr 1
      push_cast
      ring
    have hsplit : clusterHarmonic p B x m * E =
        (((p m : ℝ) * s : ℝ) : ℂ) * E + (((p m : ℝ) * s : ℝ) : ℂ) * ((z ^ 8 - 1) * E) := by
      rw [hch]; ring
    have herr : |((((p m : ℝ) * s : ℝ) : ℂ) * ((z ^ 8 - 1) * E)).re| ≤
        (p m : ℝ) * s * (1 / (B : ℝ)) := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (p m : ℝ) * s)]
      exact mul_le_mul_of_nonneg_left hz8 (by positivity)
    rw [hsplit, Complex.add_re, Complex.re_ofReal_mul, hEre]
    have herr' := neg_abs_le ((((p m : ℝ) * s : ℝ) : ℂ) * ((z ^ 8 - 1) * E)).re
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib] at hsum
  set D : ℝ := ∑ m ∈ Finset.Icc 1 M, (p m : ℝ)
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hcos_val : η * D ≤
      ∑ m ∈ Finset.Icc 1 M, (p m : ℝ) * Real.cos (2 * Real.pi * (m : ℝ) * ((B : ℝ) * u)) :=
    hcos ((B : ℝ) * u) (dist_ge_of_notMem_holeSet hu)
  have h1 : 2 * s * (η * D) ≤
      ∑ m ∈ Finset.Icc 1 M,
        2 * (p m : ℝ) * s * Real.cos (2 * Real.pi * (m : ℝ) * ((B : ℝ) * u)) := by
    calc 2 * s * (η * D)
        ≤ 2 * s * ∑ m ∈ Finset.Icc 1 M,
            (p m : ℝ) * Real.cos (2 * Real.pi * (m : ℝ) * ((B : ℝ) * u)) :=
          mul_le_mul_of_nonneg_left hcos_val (by positivity)
      _ = ∑ m ∈ Finset.Icc 1 M,
            2 * (p m : ℝ) * s * Real.cos (2 * Real.pi * (m : ℝ) * ((B : ℝ) * u)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
  have h2 : (∑ m ∈ Finset.Icc 1 M, 2 * (p m : ℝ) * s * (1 / (B : ℝ))) =
      2 * s * D * (1 / (B : ℝ)) := by
    dsimp only [D]
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hBinv : 1 / (B : ℝ) ≤ η / 2 := by
    rw [div_le_div_iff₀ hBpos (by norm_num)]
    rw [div_le_iff₀ hη] at hBη
    linarith
  have h3 : 2 * s * D * (1 / (B : ℝ)) ≤ 2 * s * D * (η / 2) :=
    mul_le_mul_of_nonneg_left hBinv (by positivity)
  have hmain : η * D * s ≤ clusterMain M p B x u := by
    unfold clusterMain
    linarith
  exact (mul_le_mul_of_nonneg_left hs_ge (by positivity)).trans hmain

/-! ### Level data and mutual window-frequency recursion -/

/-- Fractional hole width `δ_k = 1 / (k + 4)` at level `k`. -/
def holeWidth (k : ℕ) : ℝ := 1 / ((k : ℝ) + 4)

theorem holeWidth_pos (k : ℕ) : 0 < holeWidth k := by
  unfold holeWidth; positivity

theorem holeWidth_le_quarter (k : ℕ) : holeWidth k ≤ 1 / 4 := by
  unfold holeWidth
  exact one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) k])

theorem holeWidth_lt_one (k : ℕ) : holeWidth k < 1 :=
  (holeWidth_le_quarter k).trans_lt (by norm_num)

theorem holeWidth_antitone : Antitone holeWidth := by
  intro a b hab
  unfold holeWidth
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem tendsto_holeWidth : Tendsto holeWidth atTop (𝓝 0) := by
  unfold holeWidth
  exact tendsto_const_nhds.div_atTop
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem exists_level_cosine (k : ℕ) :
    ∃ (M : ℕ) (p : ℕ → ℕ) (η : ℝ),
      1 ≤ M ∧ 1 ≤ (∑ m ∈ Finset.Icc 1 M, p m) ∧ 0 < η ∧
      ∀ t : ℝ, (∀ n : ℤ, holeWidth k / 2 ≤ |t - (n + 1 / 2)|) →
        η * (∑ m ∈ Finset.Icc 1 M, (p m : ℝ)) ≤
          ∑ m ∈ Finset.Icc 1 M, (p m : ℝ) * Real.cos (2 * Real.pi * m * t) :=
  exists_nat_cosine_sum_pos_off_hole (holeWidth_pos k)
    ((holeWidth_le_quarter k).trans (by norm_num))

/-- Degree `M_k` of the positive cosine polynomial at level `k`. -/
def cosDeg (k : ℕ) : ℕ := Classical.choose (exists_level_cosine k)

/-- Natural-number coefficient vector `p_k` at level `k`. -/
def cosWeight (k : ℕ) : ℕ → ℕ :=
  Classical.choose (Classical.choose_spec (exists_level_cosine k))

/-- Positivity floor `η_k` at level `k`. -/
def cosFloor (k : ℕ) : ℝ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (exists_level_cosine k)))

/-- Total natural-number coefficient sum `D_k = ∑_{m=1}^{M_k} p_{k,m}`. -/
def cosMass (k : ℕ) : ℕ := ∑ m ∈ Finset.Icc 1 (cosDeg k), cosWeight k m

theorem cosMass_cast (k : ℕ) :
    (cosMass k : ℝ) = ∑ m ∈ Finset.Icc 1 (cosDeg k), (cosWeight k m : ℝ) := by
  unfold cosMass; push_cast; rfl

theorem level_cosine_spec (k : ℕ) :
    1 ≤ cosDeg k ∧ 1 ≤ cosMass k ∧ 0 < cosFloor k ∧
    ∀ t : ℝ, (∀ n : ℤ, holeWidth k / 2 ≤ |t - (n + 1 / 2)|) →
      cosFloor k * (cosMass k : ℝ) ≤
        ∑ m ∈ Finset.Icc 1 (cosDeg k), (cosWeight k m : ℝ) * Real.cos (2 * Real.pi * m * t) := by
  rw [cosMass_cast]
  exact Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (exists_level_cosine k)))

theorem one_le_cosDeg (k : ℕ) : 1 ≤ cosDeg k := (level_cosine_spec k).1

theorem one_le_cosMass (k : ℕ) : 1 ≤ cosMass k := (level_cosine_spec k).2.1

theorem cosFloor_pos (k : ℕ) : 0 < cosFloor k := (level_cosine_spec k).2.2.1

/-- Nonzero harmonics `1 ≤ m ≤ M_k` with `p_{k,m} ≥ 1`. -/
def activeHarmonics (k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (cosDeg k)).filter fun m => 1 ≤ cosWeight k m

theorem sum_activeHarmonics_eq {α : Type*} [AddCommMonoid α] (k : ℕ) (f : ℕ → α)
    (hf : ∀ m, cosWeight k m = 0 → f m = 0) :
    ∑ m ∈ activeHarmonics k, f m = ∑ m ∈ Finset.Icc 1 (cosDeg k), f m := by
  unfold activeHarmonics
  refine Finset.sum_subset (Finset.filter_subset _ _) fun m hm hnot => ?_
  rw [Finset.mem_filter] at hnot
  have hle : ¬ 1 ≤ cosWeight k m := fun h1 => hnot ⟨hm, h1⟩
  exact hf m (by omega)

/-- Threshold `X₀ ≥ 4` above which `ψ(y + y^{3/4}) − ψ(y) ≤ 2 y^{3/4}`. -/
theorem exists_huxley_step_bound :
    ∃ X₀ : ℝ, 4 ≤ X₀ ∧ ∀ y : ℝ, X₀ ≤ y →
      Chebyshev.psi (y + y ^ (3 / 4 : ℝ)) - Chebyshev.psi y ≤ 2 * y ^ (3 / 4 : ℝ) := by
  have hlim := RHTower.tendsto_psi_short_window_div_seven_twelfths
    (α := 3 / 4) (by norm_num) (by norm_num)
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)))
  refine ⟨max X₁ 4, le_max_right _ _, fun y hy => ?_⟩
  have hy4 : 4 ≤ y := (le_max_right _ _).trans hy
  have hypos : 0 < y ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hlt := hX₁ y ((le_max_left _ _).trans hy)
  exact ((div_lt_iff₀ hypos).mp hlt).le

/-- Fixed Huxley threshold `X₀ ≥ 4`. -/
def huxleyX : ℝ := Classical.choose exists_huxley_step_bound

theorem four_le_huxleyX : 4 ≤ huxleyX := (Classical.choose_spec exists_huxley_step_bound).1

theorem psi_short_le_two_mul {y : ℝ} (hy : huxleyX ≤ y) :
    Chebyshev.psi (y + y ^ (3 / 4 : ℝ)) - Chebyshev.psi y ≤ 2 * y ^ (3 / 4 : ℝ) :=
  (Classical.choose_spec exists_huxley_step_bound).2 y hy

/-- Level-dependent multiplier ensuring weight ceilings, temperedness, and phase accuracy. -/
def baseConst (k : ℕ) : ℕ :=
  2 * cosMass k * cosDeg k ^ 8 * 2 ^ k + ⌈2 / cosFloor k⌉₊ + k + 10

theorem ten_le_baseConst (k : ℕ) : 10 ≤ baseConst k := by unfold baseConst; omega

/-- Positivity floor of level `k` for a given depth `x` and base frequency `B`. -/
def clusterFloorVal (k B : ℕ) (x : ℝ) : ℝ :=
  cosFloor k * (cosMass k : ℝ) * (x / (7 * (B : ℝ))) ^ 8

/-- Pair recursion `(U_k, B_k)` for parameter `Θ`: `B_{k+1}` is chosen from `U_k`, and the integer
window endpoint `U_{k+1}` is then chosen from `B_{k+1}`. -/
def towerPair (Θ : ℝ) : ℕ → ℕ × ℕ
  | 0 => (0, baseConst 0)
  | k + 1 =>
      let prev := towerPair Θ k
      let U_k := prev.1
      let B_next := baseConst (k + 1) * ⌈Real.exp ((Θ / 8) * (U_k : ℝ))⌉₊
      let L_next := clusterFloorVal (k + 1) B_next (SplineTower.depth Θ (k + 1))
      let U_next :=
        max (max (U_k + 4) (⌈Real.log huxleyX⌉₊ + 2))
          (max ⌈Real.log (4 / L_next + 1) /
              (SplineTower.depth Θ (k + 1) - SplineTower.depth Θ k)⌉₊
            (max ⌈8 * Real.log ((B_next : ℝ) / holeWidth (k + 1) + 1)⌉₊
              ⌈16 * Real.log (2 * (baseConst (k + 2) : ℝ) / holeWidth (k + 2) + 1)⌉₊))
      (U_next, B_next)

/-- Integer window endpoint `U_k`. -/
def winNat (Θ : ℝ) (k : ℕ) : ℕ := (towerPair Θ k).1

/-- Base frequency `B_k`. -/
def baseFreq (Θ : ℝ) (k : ℕ) : ℕ := (towerPair Θ k).2

/-- Tower weight ceiling `2 D_k / B_k^8` at level `k`. -/
def clusterWeight (Θ : ℝ) (k : ℕ) : ℝ :=
  2 * (cosMass k : ℝ) / (baseFreq Θ k : ℝ) ^ 8

@[simp] theorem winNat_zero (Θ : ℝ) : winNat Θ 0 = 0 := rfl

@[simp] theorem baseFreq_zero (Θ : ℝ) : baseFreq Θ 0 = baseConst 0 := rfl

theorem baseFreq_succ (Θ : ℝ) (k : ℕ) :
    baseFreq Θ (k + 1) = baseConst (k + 1) * ⌈Real.exp ((Θ / 8) * (winNat Θ k : ℝ))⌉₊ := rfl

theorem winNat_add_four_le_succ (Θ : ℝ) (k : ℕ) : winNat Θ k + 4 ≤ winNat Θ (k + 1) := by
  dsimp only [winNat, towerPair]
  exact (le_max_left _ _).trans (le_max_left _ _)

theorem strictMono_winNat (Θ : ℝ) : StrictMono (winNat Θ) :=
  strictMono_nat_of_lt_succ fun k => by have := winNat_add_four_le_succ Θ k; omega

theorem log_huxleyX_le_winNat_one (Θ : ℝ) : Real.log huxleyX ≤ (winNat Θ 1 : ℝ) := by
  have h1 : ⌈Real.log huxleyX⌉₊ + 2 ≤ winNat Θ 1 := by
    dsimp only [winNat, towerPair]
    exact (le_max_right _ _).trans (le_max_left _ _)
  have hcast : (⌈Real.log huxleyX⌉₊ : ℝ) ≤ winNat Θ 1 := by exact_mod_cast (by omega : ⌈Real.log huxleyX⌉₊ ≤ winNat Θ 1)
  exact (Nat.le_ceil _).trans hcast

theorem one_le_ceil_exp_tower {Θ : ℝ} (_hΘ : 0 < Θ) (k : ℕ) :
    1 ≤ ⌈Real.exp ((Θ / 8) * (winNat Θ k : ℝ))⌉₊ :=
  Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (Real.exp_pos _)).ne'

theorem baseConst_le_baseFreq {Θ : ℝ} (hΘ : 0 < Θ) (k : ℕ) : baseConst k ≤ baseFreq Θ k := by
  rcases k with _ | k
  · exact le_rfl
  · rw [baseFreq_succ]
    exact Nat.le_mul_of_pos_right _ (one_le_ceil_exp_tower hΘ k)

theorem ten_le_baseFreq {Θ : ℝ} (hΘ : 0 < Θ) (k : ℕ) : 10 ≤ baseFreq Θ k :=
  (ten_le_baseConst k).trans (baseConst_le_baseFreq hΘ k)

theorem one_le_baseFreq {Θ : ℝ} (hΘ : 0 < Θ) (k : ℕ) : 1 ≤ baseFreq Θ k := by
  have := ten_le_baseFreq hΘ k; omega

theorem k_le_baseFreq {Θ : ℝ} (hΘ : 0 < Θ) (k : ℕ) : k ≤ baseFreq Θ k :=
  (by unfold baseConst; omega : k ≤ baseConst k).trans (baseConst_le_baseFreq hΘ k)

theorem two_div_cosFloor_le_baseFreq {Θ : ℝ} (hΘ : 0 < Θ) (k : ℕ) :
    2 / cosFloor k ≤ (baseFreq Θ k : ℝ) := by
  have h1 : ⌈2 / cosFloor k⌉₊ ≤ baseConst k := by unfold baseConst; omega
  have h2 : (⌈2 / cosFloor k⌉₊ : ℝ) ≤ baseFreq Θ k := by
    exact_mod_cast h1.trans (baseConst_le_baseFreq hΘ k)
  exact (Nat.le_ceil _).trans h2

theorem clusterWeight_nonneg (Θ : ℝ) (k : ℕ) : 0 ≤ clusterWeight Θ k := by
  unfold clusterWeight; positivity

theorem clusterWeight_zero_le_one (Θ : ℝ) : clusterWeight Θ 0 ≤ 1 := by
  unfold clusterWeight
  rw [baseFreq_zero]
  have hD1 : 1 ≤ cosMass 0 := one_le_cosMass 0
  have hM1 : 1 ≤ cosDeg 0 := one_le_cosDeg 0
  have hMpow : 1 ≤ cosDeg 0 ^ 8 := Nat.one_le_pow 8 _ hM1
  have hB_ge : 2 * cosMass 0 ≤ baseConst 0 := by
    unfold baseConst
    have : 2 * cosMass 0 * 1 ≤ 2 * cosMass 0 * cosDeg 0 ^ 8 := Nat.mul_le_mul_left _ hMpow
    omega
  have hB1 : (1 : ℝ) ≤ baseConst 0 := by
    exact_mod_cast (by have := ten_le_baseConst 0; omega : 1 ≤ baseConst 0)
  have hpow : (baseConst 0 : ℝ) ≤ (baseConst 0 : ℝ) ^ 8 := le_self_pow₀ hB1 (by omega)
  have hBR : 2 * (cosMass 0 : ℝ) ≤ baseConst 0 := by exact_mod_cast hB_ge
  rw [div_le_one (by positivity)]
  linarith

theorem clusterWeight_succ_le {Θ : ℝ} (hΘ : 0 < Θ) (j : ℕ) :
    clusterWeight Θ (j + 1) ≤
      (1 / 2) ^ (j + 1) * Real.exp (-(Θ * (winNat Θ j : ℝ))) := by
  unfold clusterWeight
  rw [baseFreq_succ, Nat.cast_mul, mul_pow]
  have hM1 : 1 ≤ cosDeg (j + 1) := one_le_cosDeg (j + 1)
  have hMpow : 1 ≤ cosDeg (j + 1) ^ 8 := Nat.one_le_pow 8 _ hM1
  have hC_ge : 2 * cosMass (j + 1) * 2 ^ (j + 1) ≤ baseConst (j + 1) := by
    unfold baseConst
    have hmul : 2 * cosMass (j + 1) * 1 * 2 ^ (j + 1) ≤
        2 * cosMass (j + 1) * cosDeg (j + 1) ^ 8 * 2 ^ (j + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hMpow)
    rw [mul_one] at hmul
    omega
  have hC1 : (1 : ℝ) ≤ baseConst (j + 1) := by
    exact_mod_cast (by have := ten_le_baseConst (j + 1); omega : 1 ≤ baseConst (j + 1))
  have hCpow : 2 * (cosMass (j + 1) : ℝ) * 2 ^ (j + 1) ≤ (baseConst (j + 1) : ℝ) ^ 8 := by
    have hCR : 2 * (cosMass (j + 1) : ℝ) * 2 ^ (j + 1) ≤ baseConst (j + 1) := by
      exact_mod_cast hC_ge
    exact hCR.trans (le_self_pow₀ hC1 (by omega))
  have hexp_le : Real.exp ((Θ / 8) * (winNat Θ j : ℝ)) ≤
      (⌈Real.exp ((Θ / 8) * (winNat Θ j : ℝ))⌉₊ : ℝ) := Nat.le_ceil _
  have hexp8 : Real.exp (Θ * (winNat Θ j : ℝ)) ≤
      (⌈Real.exp ((Θ / 8) * (winNat Θ j : ℝ))⌉₊ : ℝ) ^ 8 := by
    calc Real.exp (Θ * (winNat Θ j : ℝ))
        = (Real.exp ((Θ / 8) * (winNat Θ j : ℝ))) ^ 8 := by
            rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ (⌈Real.exp ((Θ / 8) * (winNat Θ j : ℝ))⌉₊ : ℝ) ^ 8 :=
            pow_le_pow_left₀ (Real.exp_pos _).le hexp_le 8
  have hden_pos : 0 < (baseConst (j + 1) : ℝ) ^ 8 *
      (⌈Real.exp ((Θ / 8) * (winNat Θ j : ℝ))⌉₊ : ℝ) ^ 8 := by
    have := one_le_ceil_exp_tower hΘ j
    have hceil_pos : (0 : ℝ) < ⌈Real.exp ((Θ / 8) * (winNat Θ j : ℝ))⌉₊ := by exact_mod_cast this
    positivity
  rw [div_le_iff₀ hden_pos]
  have hprod := mul_le_mul hCpow hexp8 (Real.exp_pos _).le (by positivity)
  have hid : ((1 / 2 : ℝ) ^ (j + 1) * Real.exp (-(Θ * (winNat Θ j : ℝ)))) *
      ((2 * (cosMass (j + 1) : ℝ) * 2 ^ (j + 1)) * Real.exp (Θ * (winNat Θ j : ℝ))) =
      2 * (cosMass (j + 1) : ℝ) := by
    have hpow2 : (1 / 2 : ℝ) ^ (j + 1) * 2 ^ (j + 1) = 1 := by
      rw [← mul_pow]; norm_num
    have hexp0 : Real.exp (-(Θ * (winNat Θ j : ℝ))) * Real.exp (Θ * (winNat Θ j : ℝ)) = 1 := by
      rw [← Real.exp_add]; simp
    calc ((1 / 2 : ℝ) ^ (j + 1) * Real.exp (-(Θ * (winNat Θ j : ℝ)))) *
          ((2 * (cosMass (j + 1) : ℝ) * 2 ^ (j + 1)) * Real.exp (Θ * (winNat Θ j : ℝ)))
        = 2 * (cosMass (j + 1) : ℝ) * ((1 / 2 : ℝ) ^ (j + 1) * 2 ^ (j + 1)) *
            (Real.exp (-(Θ * (winNat Θ j : ℝ))) * Real.exp (Θ * (winNat Θ j : ℝ))) := by ring
      _ = 2 * (cosMass (j + 1) : ℝ) := by rw [hpow2, hexp0]; ring
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (1 / 2) ^ (j + 1) by positivity)
    (Real.exp_pos (-(Θ * (winNat Θ j : ℝ)))).le]

theorem four_le_exp_mul_clusterFloor {Θ : ℝ} (hΘ : 0 < Θ) (n : ℕ) :
    4 ≤ Real.exp ((SplineTower.depth Θ (n + 1) - SplineTower.depth Θ n) *
        (winNat Θ (n + 1) : ℝ)) *
      clusterFloorVal (n + 1) (baseFreq Θ (n + 1)) (SplineTower.depth Θ (n + 1)) := by
  set L := clusterFloorVal (n + 1) (baseFreq Θ (n + 1)) (SplineTower.depth Θ (n + 1))
  have hL_pos : 0 < L := by
    dsimp only [L, clusterFloorVal]
    have hη := cosFloor_pos (n + 1)
    have hD : (0 : ℝ) < cosMass (n + 1) := by exact_mod_cast one_le_cosMass (n + 1)
    have hd := SplineTower.depth_pos hΘ (n + 1)
    have hB : (0 : ℝ) < baseFreq Θ (n + 1) := by exact_mod_cast one_le_baseFreq hΘ (n + 1)
    positivity
  set Δ := SplineTower.depth Θ (n + 1) - SplineTower.depth Θ n
  have hΔ_pos : 0 < Δ := sub_pos.mpr (SplineTower.strictMono_depth hΘ (Nat.lt_succ_self n))
  have hU_ge : ⌈Real.log (4 / L + 1) / Δ⌉₊ ≤ winNat Θ (n + 1) := by
    dsimp only [winNat, towerPair]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hUR : Real.log (4 / L + 1) / Δ ≤ (winNat Θ (n + 1) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hU_ge)
  have hlog : Real.log (4 / L + 1) ≤ Δ * (winNat Θ (n + 1) : ℝ) := by
    rw [div_le_iff₀ hΔ_pos] at hUR
    linarith
  have hexp : 4 / L + 1 ≤ Real.exp (Δ * (winNat Θ (n + 1) : ℝ)) := by
    rw [← Real.exp_log (by positivity : 0 < 4 / L + 1)]
    exact Real.exp_le_exp.mpr hlog
  have hmul := mul_le_mul_of_nonneg_right hexp hL_pos.le
  rw [add_mul, div_mul_cancel₀ 4 hL_pos.ne'] at hmul
  linarith

/-- On window `n + 1`, both `B_{n+1} / δ_{n+1}` and `B_{n+2} / δ_{n+2}` are bounded by
`exp(U_{n+1} / 8)`. -/
theorem baseFreq_div_holeWidth_succ_le {Θ : ℝ} (_hΘ : 0 < Θ) (n : ℕ) :
    (baseFreq Θ (n + 1) : ℝ) / holeWidth (n + 1) ≤
      Real.exp ((winNat Θ (n + 1) : ℝ) / 8) := by
  have hU_ge : ⌈8 * Real.log ((baseFreq Θ (n + 1) : ℝ) / holeWidth (n + 1) + 1)⌉₊ ≤
      winNat Θ (n + 1) := by
    dsimp only [winNat, towerPair]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hUR : 8 * Real.log ((baseFreq Θ (n + 1) : ℝ) / holeWidth (n + 1) + 1) ≤
      (winNat Θ (n + 1) : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hU_ge)
  have hpos : 0 < (baseFreq Θ (n + 1) : ℝ) / holeWidth (n + 1) + 1 := by
    have := holeWidth_pos (n + 1); positivity
  have hlog : Real.log ((baseFreq Θ (n + 1) : ℝ) / holeWidth (n + 1) + 1) ≤
      (winNat Θ (n + 1) : ℝ) / 8 := by linarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hpos] at hexp
  linarith

theorem baseFreq_div_holeWidth_succ_succ_le {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (n : ℕ) :
    (baseFreq Θ (n + 2) : ℝ) / holeWidth (n + 2) ≤
      Real.exp ((winNat Θ (n + 1) : ℝ) / 8) := by
  have hU_ge : ⌈16 * Real.log (2 * (baseConst (n + 2) : ℝ) / holeWidth (n + 2) + 1)⌉₊ ≤
      winNat Θ (n + 1) := by
    dsimp only [winNat, towerPair]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hUR : 16 * Real.log (2 * (baseConst (n + 2) : ℝ) / holeWidth (n + 2) + 1) ≤
      (winNat Θ (n + 1) : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hU_ge)
  have hpos : 0 < 2 * (baseConst (n + 2) : ℝ) / holeWidth (n + 2) + 1 := by
    have := holeWidth_pos (n + 2); positivity
  have hC_exp : 2 * (baseConst (n + 2) : ℝ) / holeWidth (n + 2) ≤
      Real.exp ((winNat Θ (n + 1) : ℝ) / 16) := by
    have hlog : Real.log (2 * (baseConst (n + 2) : ℝ) / holeWidth (n + 2) + 1) ≤
        (winNat Θ (n + 1) : ℝ) / 16 := by linarith
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hpos] at hexp
    linarith
  have hceil : (⌈Real.exp ((Θ / 8) * (winNat Θ (n + 1) : ℝ))⌉₊ : ℝ) ≤
      2 * Real.exp ((winNat Θ (n + 1) : ℝ) / 16) := by
    set y := Real.exp ((Θ / 8) * (winNat Θ (n + 1) : ℝ))
    have hy1 : 1 ≤ y := Real.one_le_exp (by positivity)
    have hy_le : y ≤ Real.exp ((winNat Θ (n + 1) : ℝ) / 16) :=
      Real.exp_le_exp.mpr (by
        have hU0 : (0 : ℝ) ≤ winNat Θ (n + 1) := Nat.cast_nonneg _
        nlinarith)
    have hc := (Nat.ceil_lt_add_one (by linarith : 0 ≤ y)).le
    linarith
  have hB_le : (baseFreq Θ (n + 2) : ℝ) ≤
      2 * (baseConst (n + 2) : ℝ) * Real.exp ((winNat Θ (n + 1) : ℝ) / 16) := by
    rw [baseFreq_succ, Nat.cast_mul]
    calc (baseConst (n + 2) : ℝ) * ⌈Real.exp ((Θ / 8) * (winNat Θ (n + 1) : ℝ))⌉₊
        ≤ (baseConst (n + 2) : ℝ) * (2 * Real.exp ((winNat Θ (n + 1) : ℝ) / 16)) :=
          mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg _)
      _ = 2 * (baseConst (n + 2) : ℝ) * Real.exp ((winNat Θ (n + 1) : ℝ) / 16) := by ring
  calc (baseFreq Θ (n + 2) : ℝ) / holeWidth (n + 2)
      ≤ (2 * (baseConst (n + 2) : ℝ) * Real.exp ((winNat Θ (n + 1) : ℝ) / 16)) /
          holeWidth (n + 2) :=
        div_le_div_of_nonneg_right hB_le (holeWidth_pos _).le
    _ = (2 * (baseConst (n + 2) : ℝ) / holeWidth (n + 2)) *
          Real.exp ((winNat Θ (n + 1) : ℝ) / 16) := by ring
    _ ≤ Real.exp ((winNat Θ (n + 1) : ℝ) / 16) * Real.exp ((winNat Θ (n + 1) : ℝ) / 16) :=
        mul_le_mul_of_nonneg_right hC_exp (Real.exp_pos _).le
    _ = Real.exp ((winNat Θ (n + 1) : ℝ) / 8) := by rw [← Real.exp_add]; congr 1; ring

/-! ### The cluster configuration and its trace expansion -/

/-- Index type for all zeros across levels `k`, active harmonics `m`, and signs `±`. -/
abbrev ClusterIdx : Type := Σ k : ℕ, ↥(activeHarmonics k) × Bool

/-- Zero location `½ ± x_k + 2πi m B_k` associated with `⟨k, (m, b)⟩`. -/
def clusterPt (Θ : ℝ) : ClusterIdx → ℂ
  | ⟨k, (m, true)⟩ =>
      (1 / 2 : ℂ) + (SplineTower.depth Θ k : ℂ) +
        ((2 * Real.pi * (m.1 * baseFreq Θ k : ℕ) : ℝ) : ℂ) * I
  | ⟨k, (m, false)⟩ =>
      (1 / 2 : ℂ) - (SplineTower.depth Θ k : ℂ) +
        ((2 * Real.pi * (m.1 * baseFreq Θ k : ℕ) : ℝ) : ℂ) * I

/-- Multiplicity `p_{k, m} m^8 ≥ 1` of the zero `clusterPt Θ idx`. -/
def idxMult (idx : ClusterIdx) : ℕ :=
  cosWeight idx.1 idx.2.1.1 * idx.2.1.1 ^ 8

theorem one_le_activeHarmonic {k : ℕ} (m : ↥(activeHarmonics k)) : 1 ≤ m.1 :=
  (Finset.mem_Icc.mp (Finset.mem_filter.mp m.2).1).1

theorem activeHarmonic_le_cosDeg {k : ℕ} (m : ↥(activeHarmonics k)) : m.1 ≤ cosDeg k :=
  (Finset.mem_Icc.mp (Finset.mem_filter.mp m.2).1).2

theorem one_le_cosWeight_active {k : ℕ} (m : ↥(activeHarmonics k)) : 1 ≤ cosWeight k m.1 :=
  (Finset.mem_filter.mp m.2).2

theorem one_le_idxMult (idx : ClusterIdx) : 1 ≤ idxMult idx :=
  Nat.mul_pos (one_le_cosWeight_active idx.2.1) (Nat.one_le_pow 8 _ (one_le_activeHarmonic idx.2.1))

theorem clusterPt_true_re (Θ : ℝ) (k : ℕ) (m : ↥(activeHarmonics k)) :
    (clusterPt Θ ⟨k, (m, true)⟩).re = 1 / 2 + SplineTower.depth Θ k := by
  simp [clusterPt]

theorem clusterPt_false_re (Θ : ℝ) (k : ℕ) (m : ↥(activeHarmonics k)) :
    (clusterPt Θ ⟨k, (m, false)⟩).re = 1 / 2 - SplineTower.depth Θ k := by
  simp [clusterPt]

theorem clusterPt_im (Θ : ℝ) (idx : ClusterIdx) :
    (clusterPt Θ idx).im = 2 * Real.pi * (idx.2.1.1 * baseFreq Θ idx.1 : ℕ) := by
  rcases idx with ⟨k, ⟨m, _ | _⟩⟩ <;> simp [clusterPt]

theorem clusterPt_injective {Θ : ℝ} (hΘ : 0 < Θ) : Function.Injective (clusterPt Θ) := by
  rintro ⟨k, ⟨m, b⟩⟩ ⟨k', ⟨m', b'⟩⟩ h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  have hd := (SplineTower.strictMono_depth hΘ).injective
  have h0 := SplineTower.depth_pos hΘ k
  have h0' := SplineTower.depth_pos hΘ k'
  have hk_eq : k = k' ∧ b = b' := by
    cases b <;> cases b'
    · rw [clusterPt_false_re, clusterPt_false_re] at hre
      exact ⟨hd (by linarith), rfl⟩
    · rw [clusterPt_false_re, clusterPt_true_re] at hre; linarith
    · rw [clusterPt_true_re, clusterPt_false_re] at hre; linarith
    · rw [clusterPt_true_re, clusterPt_true_re] at hre
      exact ⟨hd (by linarith), rfl⟩
  rcases hk_eq with ⟨rfl, rfl⟩
  rw [clusterPt_im, clusterPt_im] at him
  have hmB_R : ((m.1 * baseFreq Θ k : ℕ) : ℝ) = (m'.1 * baseFreq Θ k : ℕ) := by
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact mul_left_cancel₀ hpi him
  have hmB : m.1 * baseFreq Θ k = m'.1 * baseFreq Θ k := by exact_mod_cast hmB_R
  have hm_eq : m.1 = m'.1 := Nat.eq_of_mul_eq_mul_right (one_le_baseFreq hΘ k) hmB
  have hsub : m = m' := Subtype.ext hm_eq
  subst hsub
  rfl

theorem reflect_clusterPt (Θ : ℝ) (k : ℕ) (m : ↥(activeHarmonics k)) (b : Bool) :
    reflect (clusterPt Θ ⟨k, (m, b)⟩) = clusterPt Θ ⟨k, (m, !b)⟩ := by
  apply Complex.ext <;> cases b <;> simp [reflect, clusterPt] <;> ring

/-- Multiplicity function on `ℂ` assigning `p_{k,m} m^8` to `clusterPt Θ ⟨k, (m, b)⟩`. -/
def clusterMult (Θ : ℝ) (ρ : ℂ) : ℕ :=
  if h : ρ ∈ Set.range (clusterPt Θ) then idxMult (Classical.choose h) else 1

theorem clusterMult_pt {Θ : ℝ} (hΘ : 0 < Θ) (idx : ClusterIdx) :
    clusterMult Θ (clusterPt Θ idx) = idxMult idx := by
  have hmem : clusterPt Θ idx ∈ Set.range (clusterPt Θ) := ⟨idx, rfl⟩
  rw [clusterMult, dif_pos hmem]
  have heq := clusterPt_injective hΘ (Classical.choose_spec hmem)
  rw [heq]

/-- **The periodic cluster zero configuration.** -/
def clusterConfig {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : ZeroConfig where
  carrier := Set.range (clusterPt Θ)
  mult := clusterMult Θ
  one_le_mult := by
    rintro ρ ⟨idx, rfl⟩
    rw [clusterMult_pt hΘ]
    exact one_le_idxMult idx
  strip := by
    rintro ρ ⟨⟨k, ⟨m, b⟩⟩, rfl⟩
    have h0 := SplineTower.depth_nonneg hΘ k
    have h1 := (SplineTower.depth_lt hΘ k).le
    cases b
    · rw [clusterPt_false_re]; constructor <;> linarith
    · rw [clusterPt_true_re]; constructor <;> linarith
  reflect_mem := by
    rintro ρ ⟨⟨k, ⟨m, b⟩⟩, rfl⟩
    exact ⟨⟨k, (m, !b)⟩, (reflect_clusterPt Θ k m b).symm⟩
  mult_reflect := by
    rintro ρ ⟨⟨k, ⟨m, b⟩⟩, rfl⟩
    rw [reflect_clusterPt, clusterMult_pt hΘ, clusterMult_pt hΘ]
    rfl
  finite_window := by
    intro T₁ T₂
    let S : Set ClusterIdx :=
      {idx : ClusterIdx | idx.1 ≤ ⌊T₂⌋₊ ∧ idx.2.1.1 ≤ ⌊T₂⌋₊}
    have hSfin : S.Finite := by
      refine ((Set.finite_univ (α := ↥(Finset.Iic ⌊T₂⌋₊))).biUnion
        fun k _ => (Set.finite_univ (α := ↥(activeHarmonics k.1) × Bool)).image
          (fun mb => (⟨k.1, mb⟩ : ClusterIdx))).subset ?_
      intro idx hidx
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_univ, true_and]
      exact ⟨⟨idx.1, Finset.mem_Iic.mpr hidx.1⟩, trivial, idx.2, rfl⟩
    refine (hSfin.image (clusterPt Θ)).subset ?_
    rintro ρ ⟨⟨idx, rfl⟩, -, hT⟩
    refine ⟨idx, ?_, rfl⟩
    rw [clusterPt_im] at hT
    have hm1 : 1 ≤ idx.2.1.1 := one_le_activeHarmonic idx.2.1
    have hB1 : 1 ≤ baseFreq Θ idx.1 := one_le_baseFreq hΘ idx.1
    have hkB : idx.1 ≤ idx.2.1.1 * baseFreq Θ idx.1 :=
      (k_le_baseFreq hΘ idx.1).trans (Nat.le_mul_of_pos_left _ hm1)
    have hmB : idx.2.1.1 ≤ idx.2.1.1 * baseFreq Θ idx.1 :=
      Nat.le_mul_of_pos_right _ hB1
    have hkR : (idx.1 : ℝ) ≤ (idx.2.1.1 * baseFreq Θ idx.1 : ℕ) := by exact_mod_cast hkB
    have hmR : (idx.2.1.1 : ℝ) ≤ (idx.2.1.1 * baseFreq Θ idx.1 : ℕ) := by exact_mod_cast hmB
    have hpos : (0 : ℝ) ≤ (idx.2.1.1 * baseFreq Θ idx.1 : ℕ) := Nat.cast_nonneg _
    exact ⟨Nat.le_floor (by nlinarith [Real.pi_gt_three]),
      Nat.le_floor (by nlinarith [Real.pi_gt_three])⟩

theorem gammaOf_clusterPt_true (Θ : ℝ) (k : ℕ) (m : ↥(activeHarmonics k)) :
    gammaOf (clusterPt Θ ⟨k, (m, true)⟩) =
      splinePoint (m.1 * baseFreq Θ k) (SplineTower.depth Θ k) := by
  apply Complex.ext <;> simp [gammaOf, clusterPt, splinePoint, Complex.div_I]

theorem gammaOf_clusterPt_false (Θ : ℝ) (k : ℕ) (m : ↥(activeHarmonics k)) :
    gammaOf (clusterPt Θ ⟨k, (m, false)⟩) =
      conj (splinePoint (m.1 * baseFreq Θ k) (SplineTower.depth Θ k)) := by
  apply Complex.ext <;> simp [gammaOf, clusterPt, splinePoint, Complex.div_I]

theorem normSq_gammaOf_clusterPt_ge {Θ : ℝ} (_hΘ : 0 < Θ) (idx : ClusterIdx) :
    (baseFreq Θ idx.1 : ℝ) ^ 2 ≤ Complex.normSq (gammaOf (clusterPt Θ idx)) := by
  have hre : (gammaOf (clusterPt Θ idx)).re =
      2 * Real.pi * (idx.2.1.1 * baseFreq Θ idx.1 : ℕ) := by
    rcases idx with ⟨k, ⟨m, _ | _⟩⟩
    · rw [gammaOf_clusterPt_false, Complex.conj_re, splinePoint_re]
    · rw [gammaOf_clusterPt_true, splinePoint_re]
  rw [Complex.normSq_apply, hre]
  have hm1 : 1 ≤ idx.2.1.1 := one_le_activeHarmonic idx.2.1
  have hle : baseFreq Θ idx.1 ≤ idx.2.1.1 * baseFreq Θ idx.1 := Nat.le_mul_of_pos_left _ hm1
  have hleR : (baseFreq Θ idx.1 : ℝ) ≤ (idx.2.1.1 * baseFreq Θ idx.1 : ℕ) := by
    exact_mod_cast hle
  have h0 : (0 : ℝ) ≤ baseFreq Θ idx.1 := Nat.cast_nonneg _
  have h1 : (baseFreq Θ idx.1 : ℝ) ≤ 2 * Real.pi * (idx.2.1.1 * baseFreq Θ idx.1 : ℕ) := by
    nlinarith [Real.pi_gt_three]
  have h2 := mul_le_mul h1 h1 h0 (h0.trans h1)
  nlinarith [mul_self_nonneg (gammaOf (clusterPt Θ idx)).im]

/-- **The cluster configuration is tempered.** -/
theorem temperedConfig_clusterConfig {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    TemperedConfig (clusterConfig hΘ hΘ2) := by
  unfold TemperedConfig
  set e := Equiv.ofInjective (clusterPt Θ) (clusterPt_injective hΘ)
  show Summable fun ρ : Set.range (clusterPt Θ) =>
    (clusterMult Θ ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))
  refine (e.summable_iff).mp ?_
  set F : ClusterIdx → ℝ := fun idx =>
    (idxMult idx : ℝ) / (1 + Complex.normSq (gammaOf (clusterPt Θ idx)))
  have hcomp : ((fun ρ : Set.range (clusterPt Θ) =>
      (clusterMult Θ ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) ∘ e) = F := by
    ext idx
    simp only [Function.comp_apply, e, Equiv.ofInjective_apply, clusterMult_pt hΘ, F]
  rw [hcomp]
  have hF0 : ∀ idx, 0 ≤ F idx := fun idx =>
    div_nonneg (Nat.cast_nonneg _) (by linarith [Complex.normSq_nonneg (gammaOf (clusterPt Θ idx))])
  rw [summable_sigma_of_nonneg hF0]
  refine ⟨fun k => (hasSum_fintype _).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun _ => hF0 _) (fun k => ?_)
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  rw [tsum_fintype]
  have hB1 : (1 : ℝ) ≤ baseFreq Θ k := by exact_mod_cast one_le_baseFreq hΘ k
  have hBsq : (baseFreq Θ k : ℝ) ≤ (baseFreq Θ k : ℝ) ^ 2 := le_self_pow₀ hB1 (by omega)
  have hterm : ∀ mb : ↥(activeHarmonics k) × Bool,
      F ⟨k, mb⟩ ≤
        (cosWeight k mb.1.1 : ℝ) * (cosDeg k : ℝ) ^ 8 / (baseFreq Θ k : ℝ) := by
    intro mb
    dsimp only [F, idxMult]
    have hm_le : (mb.1.1 : ℝ) ≤ cosDeg k := by exact_mod_cast activeHarmonic_le_cosDeg mb.1
    have hmpow : (mb.1.1 : ℝ) ^ 8 ≤ (cosDeg k : ℝ) ^ 8 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hm_le 8
    have hnum : ((cosWeight k mb.1.1 * mb.1.1 ^ 8 : ℕ) : ℝ) ≤
        (cosWeight k mb.1.1 : ℝ) * (cosDeg k : ℝ) ^ 8 := by
      push_cast
      exact mul_le_mul_of_nonneg_left hmpow (Nat.cast_nonneg _)
    have hden : (baseFreq Θ k : ℝ) ≤ 1 + Complex.normSq (gammaOf (clusterPt Θ ⟨k, mb⟩)) := by
      have := normSq_gammaOf_clusterPt_ge hΘ ⟨k, mb⟩
      linarith
    exact (div_le_div_of_nonneg_right hnum (by linarith)).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
  calc (∑ mb : ↥(activeHarmonics k) × Bool, F ⟨k, mb⟩)
      ≤ ∑ mb : ↥(activeHarmonics k) × Bool,
          (cosWeight k mb.1.1 : ℝ) * (cosDeg k : ℝ) ^ 8 / (baseFreq Θ k : ℝ) :=
        Finset.sum_le_sum fun mb _ => hterm mb
    _ = 2 * (∑ m : ↥(activeHarmonics k), (cosWeight k m.1 : ℝ)) *
          (cosDeg k : ℝ) ^ 8 / (baseFreq Θ k : ℝ) := by
        rw [Fintype.sum_prod_type]
        simp only [Fintype.sum_bool, ← two_mul, ← Finset.mul_sum, ← Finset.sum_div,
          ← Finset.sum_mul]
        ring
    _ = 2 * (cosMass k : ℝ) * (cosDeg k : ℝ) ^ 8 / (baseFreq Θ k : ℝ) := by
        have hsub : (∑ m : ↥(activeHarmonics k), (cosWeight k m.1 : ℝ)) = cosMass k := by
          rw [Finset.sum_coe_sort (activeHarmonics k) (fun m => (cosWeight k m : ℝ)),
            sum_activeHarmonics_eq k (fun m => (cosWeight k m : ℝ)) (fun m hm => by simp [hm]),
            cosMass_cast]
        rw [hsub]
    _ ≤ (1 / 2 : ℝ) ^ k := by
        have hC_ge : 2 * cosMass k * cosDeg k ^ 8 * 2 ^ k ≤ baseFreq Θ k :=
          (by unfold baseConst; omega :
            2 * cosMass k * cosDeg k ^ 8 * 2 ^ k ≤ baseConst k).trans (baseConst_le_baseFreq hΘ k)
        have hCR : 2 * (cosMass k : ℝ) * (cosDeg k : ℝ) ^ 8 * (2 : ℝ) ^ k ≤ baseFreq Θ k := by
          exact_mod_cast hC_ge
        rw [div_le_iff₀ (by positivity)]
        have hpow2 : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
        have hmul := mul_le_mul_of_nonneg_left hCR (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k by positivity)
        have hid : (1 / 2 : ℝ) ^ k *
            (2 * (cosMass k : ℝ) * (cosDeg k : ℝ) ^ 8 * (2 : ℝ) ^ k) =
            2 * (cosMass k : ℝ) * (cosDeg k : ℝ) ^ 8 := by
          calc (1 / 2 : ℝ) ^ k * (2 * (cosMass k : ℝ) * (cosDeg k : ℝ) ^ 8 * (2 : ℝ) ^ k)
              = 2 * (cosMass k : ℝ) * (cosDeg k : ℝ) ^ 8 * ((1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k) := by
                  ring
            _ = 2 * (cosMass k : ℝ) * (cosDeg k : ℝ) ^ 8 := by rw [hpow2, mul_one]
        linarith

/-- **Trace expansion of the cluster configuration.** -/
theorem two_re_lagStructure_clusterConfig {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (u : ℝ) :
    2 * (lagStructure (clusterConfig hΘ hΘ2) (boxSpline 1 3) u).re =
      ∑' k,
        (Real.exp (SplineTower.depth Θ k * u) *
            clusterMain (cosDeg k) (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) u +
          Real.exp (-(SplineTower.depth Θ k * u)) *
            clusterRefl (cosDeg k) (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) u) := by
  set Z := clusterConfig hΘ hΘ2
  have hb3 := SplineTower.contDiff_two_boxSpline (o := 3) le_rfl
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hs := summable_lagStructure Z (temperedConfig_clusterConfig hΘ hΘ2) hb3 hbs u
  set e := Equiv.ofInjective (clusterPt Θ) (clusterPt_injective hΘ)
  set F : ClusterIdx → ℂ := fun idx =>
    (idxMult idx : ℂ) *
      paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf (clusterPt Θ idx)) *
      cexp (I * gammaOf (clusterPt Θ idx) * u) with hF
  have hcomp : ∀ idx,
      ((Z.mult (e idx) : ℂ) *
        paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf (e idx)) *
        cexp (I * gammaOf (e idx) * u)) = F idx := by
    intro idx
    simp only [Z, clusterConfig, e, Equiv.ofInjective_apply, clusterMult_pt hΘ, hF]
  have hS : HasSum F (lagStructure Z (boxSpline 1 3) u) := by
    have h1 := (e.hasSum_iff).mpr hs.hasSum
    simp only [Function.comp_def, hcomp] at h1
    exact h1
  set g : ℕ → ℂ := fun k =>
    ∑ m ∈ Finset.Icc 1 (cosDeg k),
      (clusterHarmonic (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) m *
          (Real.exp (SplineTower.depth Θ k * u) : ℂ) *
          cexp (((2 * Real.pi * (m * baseFreq Θ k : ℕ) * u : ℝ) : ℂ) * I) +
        conj (clusterHarmonic (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) m) *
          (Real.exp (-(SplineTower.depth Θ k * u)) : ℂ) *
          cexp (((2 * Real.pi * (m * baseFreq Θ k : ℕ) * u : ℝ) : ℂ) * I)) with hg
  have hfib : ∀ k, HasSum (fun mb : ↥(activeHarmonics k) × Bool => F ⟨k, mb⟩) (g k) := by
    intro k
    have hfintype := hasSum_fintype (fun mb : ↥(activeHarmonics k) × Bool => F ⟨k, mb⟩)
    convert hfintype using 1
    rw [Fintype.sum_prod_type]
    have hbool : ∀ m : ↥(activeHarmonics k),
        (∑ b : Bool, F ⟨k, (m, b)⟩) =
          clusterHarmonic (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) m.1 *
            (Real.exp (SplineTower.depth Θ k * u) : ℂ) *
            cexp (((2 * Real.pi * (m.1 * baseFreq Θ k : ℕ) * u : ℝ) : ℂ) * I) +
          conj (clusterHarmonic (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) m.1) *
            (Real.exp (-(SplineTower.depth Θ k * u)) : ℂ) *
            cexp (((2 * Real.pi * (m.1 * baseFreq Θ k : ℕ) * u : ℝ) : ℂ) * I) := by
      intro m
      rw [Fintype.sum_bool]
      simp only [hF, idxMult, gammaOf_clusterPt_true, gammaOf_clusterPt_false,
        SplineTower.paperFT_weilTest_spline (o := 3) le_rfl, show 2 * (3 + 1) = 8 by rfl,
        SplineTower.sincC_conj, map_pow, SplineTower.I_mul_splinePoint,
        SplineTower.I_mul_conj_splinePoint, Complex.exp_add, ← Complex.ofReal_exp,
        clusterHarmonic, map_mul, Complex.conj_natCast]
      ring
    simp_rw [hbool]
    rw [Finset.sum_coe_sort (activeHarmonics k) (fun m =>
      clusterHarmonic (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) m *
          (Real.exp (SplineTower.depth Θ k * u) : ℂ) *
          cexp (((2 * Real.pi * (m * baseFreq Θ k : ℕ) * u : ℝ) : ℂ) * I) +
        conj (clusterHarmonic (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) m) *
          (Real.exp (-(SplineTower.depth Θ k * u)) : ℂ) *
          cexp (((2 * Real.pi * (m * baseFreq Θ k : ℕ) * u : ℝ) : ℂ) * I))]
    rw [sum_activeHarmonics_eq k _ fun m hm => by simp [clusterHarmonic, hm]]
  have hG : HasSum g (lagStructure Z (boxSpline 1 3) u) := hS.sigma hfib
  have hre := (Complex.reCLM.hasSum hG).mul_left 2
  simp only [Complex.reCLM_apply] at hre
  rw [← hre.tsum_eq]
  refine tsum_congr fun k => ?_
  dsimp only [hg, clusterMain, clusterRefl]
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.add_re]
  have h1 : (clusterHarmonic (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) m *
      (Real.exp (SplineTower.depth Θ k * u) : ℂ) *
      cexp (((2 * Real.pi * (m * baseFreq Θ k : ℕ) * u : ℝ) : ℂ) * I)).re =
      Real.exp (SplineTower.depth Θ k * u) *
        (clusterHarmonic (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) m *
          cexp (((2 * Real.pi * (m * baseFreq Θ k : ℕ) * u : ℝ) : ℂ) * I)).re := by
    rw [show clusterHarmonic (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) m *
        (Real.exp (SplineTower.depth Θ k * u) : ℂ) *
        cexp (((2 * Real.pi * (m * baseFreq Θ k : ℕ) * u : ℝ) : ℂ) * I) =
        (Real.exp (SplineTower.depth Θ k * u) : ℂ) *
          (clusterHarmonic (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) m *
            cexp (((2 * Real.pi * (m * baseFreq Θ k : ℕ) * u : ℝ) : ℂ) * I)) by ring,
      Complex.re_ofReal_mul]
  have h2 : (conj (clusterHarmonic (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) m) *
      (Real.exp (-(SplineTower.depth Θ k * u)) : ℂ) *
      cexp (((2 * Real.pi * (m * baseFreq Θ k : ℕ) * u : ℝ) : ℂ) * I)).re =
      Real.exp (-(SplineTower.depth Θ k * u)) *
        (conj (clusterHarmonic (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) m) *
          cexp (((2 * Real.pi * (m * baseFreq Θ k : ℕ) * u : ℝ) : ℂ) * I)).re := by
    rw [show conj (clusterHarmonic (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) m) *
        (Real.exp (-(SplineTower.depth Θ k * u)) : ℂ) *
        cexp (((2 * Real.pi * (m * baseFreq Θ k : ℕ) * u : ℝ) : ℂ) * I) =
        (Real.exp (-(SplineTower.depth Θ k * u)) : ℂ) *
          (conj (clusterHarmonic (cosWeight k) (baseFreq Θ k) (SplineTower.depth Θ k) m) *
            cexp (((2 * Real.pi * (m * baseFreq Θ k : ℕ) * u : ℝ) : ℂ) * I)) by ring,
      Complex.re_ofReal_mul]
  rw [h1, h2]
  ring

/-! ### Unit-block hole structure, upper density zero, and short-interval prime bounds -/

/-- Open sub-hole `((B m + r + ½ − δ/2)/B, (B m + r + ½ + δ/2)/B)` inside `[m, m + 1]`. -/
def subHole (B m r : ℕ) (δ : ℝ) : Set ℝ :=
  Set.Ioo ((((B * m + r : ℕ) : ℝ) + 1 / 2 - δ / 2) / B)
    ((((B * m + r : ℕ) : ℝ) + 1 / 2 + δ / 2) / B)

theorem subHole_subset_Icc {B m r : ℕ} {δ : ℝ} (hB : 1 ≤ B) (hr : r < B)
    (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    subHole B m r δ ⊆ Set.Icc (m : ℝ) (m + 1) := by
  intro u hu
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  rcases hu with ⟨hlo, hhi⟩
  rw [div_lt_iff₀ hBpos] at hlo
  rw [lt_div_iff₀ hBpos] at hhi
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hrB : (r : ℝ) + 1 ≤ B := by exact_mod_cast (Nat.succ_le_of_lt hr)
  push_cast at hlo hhi
  constructor
  · have : (m : ℝ) * B < u * B := by linarith
    exact (mul_lt_mul_iff_left₀ hBpos).mp this |>.le
  · have : u * B < ((m : ℝ) + 1) * B := by linarith
    exact (mul_lt_mul_iff_left₀ hBpos).mp this |>.le

/-- **Exact unit-block decomposition of `holeSet`.** When `0 < δ ≤ ¼`, every periodic hole meeting
`[m, m + 1]` lies strictly inside `(m, m + 1)`, giving an exact union of `B` open intervals. -/
theorem holeSet_inter_Icc_eq {B : ℕ} {δ : ℝ} (hB : 1 ≤ B) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (m : ℕ) :
    holeSet B δ ∩ Set.Icc (m : ℝ) (m + 1) = ⋃ r ∈ Finset.range B, subHole B m r δ := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  ext u
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_range]
  constructor
  · rintro ⟨⟨n, hn⟩, hm1, hm2⟩
    rw [abs_lt] at hn
    have hn_loR : (((B * m : ℕ) : ℤ) : ℝ) - 1 < n := by
      have : (B : ℝ) * m ≤ (B : ℝ) * u := mul_le_mul_of_nonneg_left hm1 hBpos.le
      push_cast
      linarith
    have hn_hiR : (n : ℝ) < (((B * m + B : ℕ) : ℤ) : ℝ) := by
      have : (B : ℝ) * u ≤ (B : ℝ) * (m + 1) := mul_le_mul_of_nonneg_left hm2 hBpos.le
      push_cast
      linarith
    have hn_lo : ((B * m : ℕ) : ℤ) ≤ n := by
      have : ((B * m : ℕ) : ℤ) - 1 < n := by exact_mod_cast hn_loR
      omega
    have hn_hi : n < ((B * m + B : ℕ) : ℤ) := by exact_mod_cast hn_hiR
    set r : ℕ := (n - ((B * m : ℕ) : ℤ)).toNat
    have hrB : r < B := by omega
    have hnr : n = ((B * m + r : ℕ) : ℤ) := by omega
    refine ⟨r, hrB, ?_⟩
    rw [hnr] at hn
    push_cast at hn
    rw [subHole, Set.mem_Ioo, div_lt_iff₀ hBpos, lt_div_iff₀ hBpos]
    push_cast
    constructor <;> linarith
  · rintro ⟨r, hrB, hu⟩
    refine ⟨?_, subHole_subset_Icc hB hrB hδ0 hδ4 hu⟩
    refine ⟨((B * m + r : ℕ) : ℤ), ?_⟩
    rw [subHole, Set.mem_Ioo, div_lt_iff₀ hBpos, lt_div_iff₀ hBpos] at hu
    rw [abs_lt]
    push_cast at hu ⊢
    constructor <;> linarith

theorem measurableSet_holeSet_inter_Icc {B : ℕ} {δ : ℝ} (hB : 1 ≤ B) (hδ0 : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) (m : ℕ) :
    MeasurableSet (holeSet B δ ∩ Set.Icc (m : ℝ) (m + 1)) := by
  rw [holeSet_inter_Icc_eq hB hδ0 hδ4 m]
  exact Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Ioo

theorem volume_holeSet_inter_Icc_le {B : ℕ} {δ : ℝ} (hB : 1 ≤ B) (hδ0 : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) (m : ℕ) :
    volume (holeSet B δ ∩ Set.Icc (m : ℝ) (m + 1)) ≤ ENNReal.ofReal δ := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  rw [holeSet_inter_Icc_eq hB hδ0 hδ4 m]
  refine (measure_biUnion_finset_le (Finset.range B) (fun r => subHole B m r δ)).trans ?_
  have hvol : ∀ r, volume (subHole B m r δ) = ENNReal.ofReal (δ / B) := fun r => by
    rw [subHole, Real.volume_Ioo]
    congr 1
    field_simp
    ring
  simp_rw [hvol]
  rw [Finset.sum_const, Finset.card_range, ← ENNReal.ofReal_nsmul, nsmul_eq_mul,
    mul_div_cancel₀ δ hBpos.ne']

/-- Unique window index `k` with `U_k ≤ m < U_{k+1}`. -/
def winIdx (Θ : ℝ) (m : ℕ) : ℕ :=
  let hex : ∃ k, m < winNat Θ (k + 1) :=
    ⟨m, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ (Nat.lt_succ_self m))
      ((strictMono_winNat Θ).id_le (m + 1) |> Nat.lt_of_lt_of_le (Nat.lt_succ_self m) |> fun h => h)⟩
  Nat.find hex

theorem winIdx_lt_succ (Θ : ℝ) (m : ℕ) : m < winNat Θ (winIdx Θ m + 1) := by
  unfold winIdx
  exact @Nat.find_spec (fun k => m < winNat Θ (k + 1)) _ _

theorem add_one_le_winNat_succ (Θ : ℝ) (m : ℕ) : m + 1 ≤ winNat Θ (winIdx Θ m + 1) :=
  Nat.succ_le_of_lt (winIdx_lt_succ Θ m)

theorem winNat_le_of_winIdx (Θ : ℝ) (m : ℕ) : winNat Θ (winIdx Θ m) ≤ m := by
  unfold winIdx
  generalize_proofs hex
  rcases h : Nat.find hex with _ | j
  · simp
  · have hmin := Nat.find_min hex (show j < Nat.find hex by omega)
    exact not_lt.mp hmin

theorem one_le_winIdx_of_ge (Θ : ℝ) {m : ℕ} (hm : winNat Θ 1 ≤ m) : 1 ≤ winIdx Θ m := by
  by_contra hlt
  have h0 : winIdx Θ m = 0 := by omega
  have := winIdx_lt_succ Θ m
  rw [h0, zero_add] at this
  omega

theorem le_winIdx_of_winNat_le (Θ : ℝ) {K m : ℕ} (hm : winNat Θ K ≤ m) : K ≤ winIdx Θ m := by
  by_contra hlt
  have hk1 : winIdx Θ m + 1 ≤ K := by omega
  have hle := (strictMono_winNat Θ).monotone hk1
  have := winIdx_lt_succ Θ m
  omega

/-- Exceptional set on the unit interval `[m, m + 1]`: the full block for `m < U_1`, and the active
holes of levels `winIdx m` and `winIdx m + 1` for `m ≥ U_1`. -/
def unitHole (Θ : ℝ) (m : ℕ) : Set ℝ :=
  if m < winNat Θ 1 then Set.Icc (m : ℝ) (m + 1)
  else
    (holeSet (baseFreq Θ (winIdx Θ m)) (holeWidth (winIdx Θ m)) ∪
      holeSet (baseFreq Θ (winIdx Θ m + 1)) (holeWidth (winIdx Θ m + 1))) ∩
      Set.Icc (m : ℝ) (m + 1)

/-- Full exceptional lag set `S = ⋃_{m ∈ ℕ} unitHole m`. -/
def exSet (Θ : ℝ) : Set ℝ := ⋃ m : ℕ, unitHole Θ m

/-- Exceptional prime set `E = {p | p prime ∧ log p ∈ S}`. -/
def exPrimes (Θ : ℝ) : Set ℕ := {p : ℕ | p.Prime ∧ Real.log p ∈ exSet Θ}

theorem unitHole_subset_Icc (Θ : ℝ) (m : ℕ) :
    unitHole Θ m ⊆ Set.Icc (m : ℝ) (m + 1) := by
  unfold unitHole
  split_ifs
  · exact Subset.rfl
  · exact Set.inter_subset_right

theorem measurableSet_unitHole {Θ : ℝ} (hΘ : 0 < Θ) (m : ℕ) :
    MeasurableSet (unitHole Θ m) := by
  unfold unitHole
  split_ifs
  · exact measurableSet_Icc
  · rw [Set.union_inter_distrib_right]
    exact (measurableSet_holeSet_inter_Icc (one_le_baseFreq hΘ _) (holeWidth_pos _)
      (holeWidth_le_quarter _) m).union
      (measurableSet_holeSet_inter_Icc (one_le_baseFreq hΘ _) (holeWidth_pos _)
        (holeWidth_le_quarter _) m)

theorem measurableSet_exSet {Θ : ℝ} (hΘ : 0 < Θ) : MeasurableSet (exSet Θ) :=
  MeasurableSet.iUnion (measurableSet_unitHole hΘ)

theorem volume_unitHole_le_one {Θ : ℝ} (_hΘ : 0 < Θ) (m : ℕ) :
    volume (unitHole Θ m) ≤ ENNReal.ofReal 1 := by
  refine (measure_mono (unitHole_subset_Icc Θ m)).trans ?_
  rw [Real.volume_Icc]
  ring_nf
  exact le_rfl

theorem volume_unitHole_le_two_holeWidth {Θ : ℝ} (hΘ : 0 < Θ) {m : ℕ}
    (hm : winNat Θ 1 ≤ m) :
    volume (unitHole Θ m) ≤ ENNReal.ofReal (2 * holeWidth (winIdx Θ m)) := by
  rw [unitHole, if_neg (not_lt.mpr hm), Set.union_inter_distrib_right]
  refine (measure_union_le _ _).trans ?_
  have h1 := volume_holeSet_inter_Icc_le (one_le_baseFreq hΘ (winIdx Θ m))
    (holeWidth_pos (winIdx Θ m)) (holeWidth_le_quarter (winIdx Θ m)) m
  have h2 := volume_holeSet_inter_Icc_le (one_le_baseFreq hΘ (winIdx Θ m + 1))
    (holeWidth_pos (winIdx Θ m + 1)) (holeWidth_le_quarter (winIdx Θ m + 1)) m
  refine (add_le_add h1 h2).trans ?_
  rw [← ENNReal.ofReal_add (holeWidth_pos _).le (holeWidth_pos _).le]
  exact ENNReal.ofReal_le_ofReal (by
    have := holeWidth_antitone (Nat.le_succ (winIdx Θ m)); linarith)

/-- **The exceptional lag set `S` has upper density zero.** -/
theorem upperDensityZero_exSet {Θ : ℝ} (hΘ : 0 < Θ) :
    _root_.RHTower.OneSidedConfiguration.UpperDensityZero (exSet Θ) := by
  intro ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (tendsto_holeWidth.eventually (gt_mem_nhds (show 0 < ε / 4 by positivity)))
  set M₀ : ℕ := max (winNat Θ K) (winNat Θ 1)
  have hM₀_hole : ∀ m : ℕ, M₀ ≤ m → volume (unitHole Θ m) ≤ ENNReal.ofReal (ε / 2) := by
    intro m hm
    have hm1 : winNat Θ 1 ≤ m := (le_max_right _ _).trans hm
    have hmK : K ≤ winIdx Θ m := le_winIdx_of_winNat_le Θ ((le_max_left _ _).trans hm)
    have hw : holeWidth (winIdx Θ m) < ε / 4 := hK _ hmK
    exact (volume_unitHole_le_two_holeWidth hΘ hm1).trans
      (ENNReal.ofReal_le_ofReal (by linarith))
  refine ⟨max 1 (2 * (M₀ : ℝ) / ε + 1), fun T hT => ?_⟩
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hT_large : 2 * (M₀ : ℝ) / ε + 1 ≤ T := (le_max_right _ _).trans hT
  have hsub : exSet Θ ∩ Set.Icc 0 T ⊆ ⋃ m ∈ Finset.range (⌊T⌋₊ + 1), unitHole Θ m := by
    rintro u ⟨huS, hu0, huT⟩
    rw [exSet, Set.mem_iUnion] at huS
    obtain ⟨m, hum⟩ := huS
    have hm_le : (m : ℝ) ≤ u := (unitHole_subset_Icc Θ m hum).1
    have hm_fl : m ≤ ⌊T⌋₊ := Nat.le_floor (hm_le.trans huT)
    exact Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le hm_fl)) hum
  refine (measure_mono hsub).trans ?_
  refine (measure_biUnion_finset_le (Finset.range (⌊T⌋₊ + 1)) (unitHole Θ)).trans ?_
  have hbound : ∀ m ∈ Finset.range (⌊T⌋₊ + 1),
      volume (unitHole Θ m) ≤
        ENNReal.ofReal (if m < M₀ then 1 else ε / 2) := by
    intro m _
    split_ifs with hlt
    · exact volume_unitHole_le_one hΘ m
    · exact hM₀_hole m (not_lt.mp hlt)
  refine (Finset.sum_le_sum hbound).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by split_ifs <;> positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsum_le : (∑ m ∈ Finset.range (⌊T⌋₊ + 1), (if m < M₀ then (1 : ℝ) else ε / 2)) ≤
      (M₀ : ℝ) + ((⌊T⌋₊ : ℝ) + 1) * (ε / 2) := by
    calc (∑ m ∈ Finset.range (⌊T⌋₊ + 1), (if m < M₀ then (1 : ℝ) else ε / 2))
        ≤ ∑ m ∈ Finset.range (⌊T⌋₊ + 1), ((if m < M₀ then (1 : ℝ) else 0) + ε / 2) := by
            refine Finset.sum_le_sum fun m _ => ?_
            split_ifs <;> linarith
      _ = (∑ m ∈ Finset.range (⌊T⌋₊ + 1), if m < M₀ then (1 : ℝ) else 0) +
            ((⌊T⌋₊ : ℝ) + 1) * (ε / 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast; ring
      _ ≤ (∑ _m ∈ Finset.range M₀, (1 : ℝ)) + ((⌊T⌋₊ : ℝ) + 1) * (ε / 2) := by
            gcongr
            rw [← Finset.sum_filter]
            refine (Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => ?_)
              (fun _ _ _ => zero_le_one))
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hm).2
      _ = (M₀ : ℝ) + ((⌊T⌋₊ : ℝ) + 1) * (ε / 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hfl_le : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hM_le : (M₀ : ℝ) + ε / 2 ≤ (ε / 2) * T := by
    calc (M₀ : ℝ) + ε / 2 = (ε / 2) * (2 * (M₀ : ℝ) / ε + 1) := by field_simp
      _ ≤ (ε / 2) * T := mul_le_mul_of_nonneg_left hT_large (by positivity)
  calc (∑ m ∈ Finset.range (⌊T⌋₊ + 1), if m < M₀ then (1 : ℝ) else ε / 2)
      ≤ (M₀ : ℝ) + ((⌊T⌋₊ : ℝ) + 1) * (ε / 2) := hsum_le
    _ ≤ (M₀ : ℝ) + (T + 1) * (ε / 2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    _ = ((M₀ : ℝ) + ε / 2) + (ε / 2) * T := by ring
    _ ≤ (ε / 2) * T + (ε / 2) * T := add_le_add hM_le le_rfl
    _ = ε * T := by ring

/-- **Lower bound `-5` on `2 Re S_Z(u)` outside `exSet Θ`.** -/
theorem two_re_lagStructure_ge_off_exSet {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ∉ exSet Θ) :
    -5 ≤ 2 * (lagStructure (clusterConfig hΘ hΘ2) (boxSpline 1 3) u).re := by
  set m : ℕ := ⌊u⌋₊
  have hmu : (m : ℝ) ≤ u := Nat.floor_le hu0
  have hum1 : u ≤ (m : ℝ) + 1 := (Nat.lt_floor_add_one u).le
  have huIcc : u ∈ Set.Icc (m : ℝ) (m + 1) := ⟨hmu, hum1⟩
  have hnot_unit : u ∉ unitHole Θ m := fun hm_mem => hu (Set.mem_iUnion.mpr ⟨m, hm_mem⟩)
  have hm_ge : winNat Θ 1 ≤ m := by
    by_contra hlt
    apply hnot_unit
    rw [unitHole, if_pos (not_le.mp hlt)]
    exact huIcc
  have hk1 : 1 ≤ winIdx Θ m := one_le_winIdx_of_ge Θ hm_ge
  have hnot_holes :
      u ∉ holeSet (baseFreq Θ (winIdx Θ m)) (holeWidth (winIdx Θ m)) ∧
      u ∉ holeSet (baseFreq Θ (winIdx Θ m + 1)) (holeWidth (winIdx Θ m + 1)) := by
    rw [unitHole, if_neg (not_lt.mpr hm_ge)] at hnot_unit
    exact ⟨fun h1 => hnot_unit ⟨Or.inl h1, huIcc⟩, fun h2 => hnot_unit ⟨Or.inr h2, huIcc⟩⟩
  rw [two_re_lagStructure_clusterConfig hΘ hΘ2 u]
  set k := winIdx Θ m
  have hU_lo : (winNat Θ k : ℝ) ≤ u :=
    (by exact_mod_cast winNat_le_of_winIdx Θ m : (winNat Θ k : ℝ) ≤ m).trans hmu
  have hU_hi : u ≤ (winNat Θ (k + 1) : ℝ) :=
    hum1.trans (by exact_mod_cast (add_one_le_winNat_succ Θ m) : (m : ℝ) + 1 ≤ winNat Θ (k + 1))
  have hfloor : ∀ j, u ∉ holeSet (baseFreq Θ j) (holeWidth j) →
      clusterFloorVal j (baseFreq Θ j) (SplineTower.depth Θ j) ≤
        clusterMain (cosDeg j) (cosWeight j) (baseFreq Θ j) (SplineTower.depth Θ j) u := by
    intro j hj
    have hspec := level_cosine_spec j
    have hmain := clusterMain_ge_off_hole hspec.2.2.1
      (fun t ht => by rw [← cosMass_cast]; exact hspec.2.2.2 t ht)
      (one_le_baseFreq hΘ j) (two_div_cosFloor_le_baseFreq hΘ j)
      (SplineTower.depth_nonneg hΘ j) ((SplineTower.depth_lt hΘ j).le.trans hΘ2) hj
    rwa [← cosMass_cast] at hmain
  have hfloor_nn : ∀ j, 0 ≤ clusterFloorVal j (baseFreq Θ j) (SplineTower.depth Θ j) := fun j => by
    unfold clusterFloorVal
    have := cosFloor_pos j
    have := SplineTower.depth_nonneg hΘ j
    positivity
  refine neg_five_le_tsum_of_window_general hΘ
    (x := SplineTower.depth Θ) (w := clusterWeight Θ) (U := fun j => (winNat Θ j : ℝ))
    (a := fun j => clusterMain (cosDeg j) (cosWeight j) (baseFreq Θ j) (SplineTower.depth Θ j) u)
    (b := fun j => clusterRefl (cosDeg j) (cosWeight j) (baseFreq Θ j) (SplineTower.depth Θ j) u)
    (fun j => SplineTower.depth_nonneg hΘ j)
    (fun j => (SplineTower.depth_lt hΘ j).le)
    (SplineTower.strictMono_depth hΘ).monotone
    (clusterWeight_nonneg Θ)
    (clusterWeight_zero_le_one Θ)
    (clusterWeight_succ_le hΘ)
    (fun i j hij => Nat.cast_le.mpr ((strictMono_winNat Θ).monotone hij))
    (by simp)
    (fun j => by
      have h := abs_clusterMain_le (cosDeg j) (cosWeight j) (one_le_baseFreq hΘ j)
        (SplineTower.depth_nonneg hΘ j) ((SplineTower.depth_lt hΘ j).le.trans hΘ2) u
      rwa [← cosMass_cast] at h)
    (fun j => by
      have h := abs_clusterRefl_le (cosDeg j) (cosWeight j) (one_le_baseFreq hΘ j)
        (SplineTower.depth_nonneg hΘ j) ((SplineTower.depth_lt hΘ j).le.trans hΘ2) u
      rwa [← cosMass_cast] at h)
    hu0 hU_lo hU_hi
    ((hfloor_nn k).trans (hfloor k hnot_holes.1))
    ((hfloor_nn (k + 1)).trans (hfloor (k + 1) hnot_holes.2))
    ?_
  intro n hn
  have hpos_exp : 0 ≤ Real.exp
      ((SplineTower.depth Θ (n + 1) - SplineTower.depth Θ n) * (winNat Θ (n + 1) : ℝ)) :=
    (Real.exp_pos _).le
  have hak := hfloor (n + 1) (hn ▸ hnot_holes.1)
  exact (four_le_exp_mul_clusterFloor hΘ n).trans (mul_le_mul_of_nonneg_left hak hpos_exp)

/-! ### Telescoping Huxley bound on sub-holes and prime density zero -/

/-- Chained short-interval steps `y_0 = a`, `y_{j+1} = y_j + y_j^{3/4}`. -/
def psiStepSeq (a : ℝ) : ℕ → ℝ
  | 0 => a
  | j + 1 => psiStepSeq a j + psiStepSeq a j ^ (3 / 4 : ℝ)

theorem psiStepSeq_ge {a : ℝ} (ha : 0 < a) (j : ℕ) : a ≤ psiStepSeq a j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
      rw [psiStepSeq]
      have hpos : 0 ≤ psiStepSeq a j ^ (3 / 4 : ℝ) :=
        Real.rpow_nonneg (ha.le.trans ih) _
      linarith

theorem psiStepSeq_linear_lower {a : ℝ} (ha : 0 < a) (j : ℕ) :
    a + (j : ℝ) * a ^ (3 / 4 : ℝ) ≤ psiStepSeq a j := by
  induction j with
  | zero => simp [psiStepSeq]
  | succ j ih =>
      rw [psiStepSeq]
      have hpow : a ^ (3 / 4 : ℝ) ≤ psiStepSeq a j ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow ha.le (psiStepSeq_ge ha j) (by norm_num)
      push_cast
      linarith

theorem psi_psiStepSeq_sub_le {a : ℝ} (ha : huxleyX ≤ a) (j : ℕ) :
    Chebyshev.psi (psiStepSeq a j) - Chebyshev.psi a ≤ 2 * (psiStepSeq a j - a) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) (four_le_huxleyX.trans ha)
  induction j with
  | zero => simp [psiStepSeq]
  | succ j ih =>
      have hjX : huxleyX ≤ psiStepSeq a j := ha.trans (psiStepSeq_ge ha0 j)
      have hstep := psi_short_le_two_mul hjX
      change Chebyshev.psi (psiStepSeq a j + psiStepSeq a j ^ (3 / 4 : ℝ)) - Chebyshev.psi a ≤
        2 * (psiStepSeq a j + psiStepSeq a j ^ (3 / 4 : ℝ) - a)
      linarith

/-- **Medium-interval Huxley bound.** Chaining `(y, y + y^{3/4}]` steps gives
`ψ(b) − ψ(a) ≤ 6 (b − a)` whenever `a ≥ X₀` and `a^{3/4} ≤ b − a ≤ a`. -/
theorem psi_sub_le_six_mul {a b : ℝ} (ha : huxleyX ≤ a)
    (hlo : a ^ (3 / 4 : ℝ) ≤ b - a) (hhi : b - a ≤ a) :
    Chebyshev.psi b - Chebyshev.psi a ≤ 6 * (b - a) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) (four_le_huxleyX.trans ha)
  have hapow : 0 < a ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos ha0 _
  have hex : ∃ N : ℕ, b < psiStepSeq a N := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / a ^ (3 / 4 : ℝ))
    refine ⟨N, ?_⟩
    have hmul : b - a < (N : ℝ) * a ^ (3 / 4 : ℝ) := (div_lt_iff₀ hapow).mp hN
    linarith [psiStepSeq_linear_lower ha0 N]
  set N := Nat.find hex
  have hN_spec : b < psiStepSeq a N := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0, psiStepSeq] at hN_spec
    linarith
  obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn_le : psiStepSeq a n ≤ b := not_lt.mp (Nat.find_min hex (by omega))
  have hmono : Chebyshev.psi b ≤ Chebyshev.psi (psiStepSeq a (n + 1)) :=
    Chebyshev.psi_mono (hn ▸ hN_spec).le
  have hchain := psi_psiStepSeq_sub_le ha (n + 1)
  have hseq_succ : psiStepSeq a (n + 1) = psiStepSeq a n + psiStepSeq a n ^ (3 / 4 : ℝ) := rfl
  have hpow_le : psiStepSeq a n ^ (3 / 4 : ℝ) ≤ 2 * (b - a) := by
    have h2a : psiStepSeq a n ≤ 2 * a := by linarith
    have h2pow : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    calc psiStepSeq a n ^ (3 / 4 : ℝ)
        ≤ (2 * a) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow (ha0.le.trans (psiStepSeq_ge ha0 n)) h2a (by norm_num)
      _ = (2 : ℝ) ^ (3 / 4 : ℝ) * a ^ (3 / 4 : ℝ) := Real.mul_rpow (by norm_num) ha0.le
      _ ≤ 2 * a ^ (3 / 4 : ℝ) := mul_le_mul_of_nonneg_right h2pow hapow.le
      _ ≤ 2 * (b - a) := mul_le_mul_of_nonneg_left hlo (by norm_num)
  linarith

theorem sum_prime_log_Ioc_le_psi_sub {a b : ℝ} (hab : a ≤ b) :
    (∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log (p : ℝ)) ≤
      Chebyshev.psi b - Chebyshev.psi a := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc]
  have hsub_icc : Finset.Icc 0 ⌊a⌋₊ ⊆ Finset.Icc 0 ⌊b⌋₊ :=
    Finset.Icc_subset_Icc_right (Nat.floor_le_floor hab)
  rw [← Finset.sum_sdiff hsub_icc, add_sub_cancel_right]
  have hsub : (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime ⊆ Finset.Icc 0 ⌊b⌋₊ \ Finset.Icc 0 ⌊a⌋₊ := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨Nat.zero_le p, hp.1.2⟩, fun h => by omega⟩
  have heq : (∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log (p : ℝ)) =
      ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Λ p :=
    Finset.sum_congr rfl fun p hp =>
      (vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2).symm
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => vonMangoldt_nonneg

theorem sum_union_le_of_nonneg {α : Type*} [DecidableEq α] {s₁ s₂ : Finset α} {f : α → ℝ}
    (hf : ∀ x ∈ s₁ ∪ s₂, 0 ≤ f x) :
    (∑ x ∈ s₁ ∪ s₂, f x) ≤ (∑ x ∈ s₁, f x) + ∑ x ∈ s₂, f x := by
  rw [← Finset.union_sdiff_self_eq_union, Finset.sum_union Finset.disjoint_sdiff]
  refine add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_)
  intro x hx _
  exact hf x (Finset.mem_union_right _ hx)

theorem sum_biUnion_le_of_nonneg {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (t : ι → Finset α) {f : α → ℝ}
    (hf : ∀ i ∈ s, ∀ x ∈ t i, 0 ≤ f x) :
    (∑ x ∈ s.biUnion t, f x) ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have hf_union : ∀ x ∈ t a ∪ s.biUnion t, 0 ≤ f x := by
        intro x hx
        rcases Finset.mem_union.mp hx with hxa | hxs
        · exact hf a (Finset.mem_insert_self a s) x hxa
        · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxs
          exact hf i (Finset.mem_insert_of_mem hi) x hxi
      exact (sum_union_le_of_nonneg hf_union).trans
        (add_le_add le_rfl (ih fun i hi x hx => hf i (Finset.mem_insert_of_mem hi) x hx))

theorem exp_sub_one_le_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.exp t - 1 ≤ 2 * t := by
  have hneg := Real.add_one_le_exp (-t)
  have hprod : Real.exp t * (1 - t) ≤ 1 := by
    calc Real.exp t * (1 - t) ≤ Real.exp t * Real.exp (-t) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos t).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hexp2 : Real.exp t ≤ 2 := by
    calc Real.exp t ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr ht1
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith [Real.log_two_gt_d9])
      _ = 2 := Real.exp_log (by norm_num)
  nlinarith

theorem sum_prime_log_subHole_le {B m r : ℕ} {δ : ℝ} (hB : 1 ≤ B) (hr : r < B)
    (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (hmX : Real.log huxleyX ≤ (m : ℝ)) (hrat : (B : ℝ) / δ ≤ Real.exp ((m : ℝ) / 4))
    (F : Finset ℕ) :
    (∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ subHole B m r δ),
        Real.log (p : ℝ)) ≤
      12 * Real.exp ((m : ℝ) + 1) * (δ / B) := by
  set u₀ := (((B * m + r : ℕ) : ℝ) + 1 / 2 - δ / 2) / B
  set u₁ := (((B * m + r : ℕ) : ℝ) + 1 / 2 + δ / 2) / B
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hu_diff : u₁ - u₀ = δ / B := by
    dsimp only [u₀, u₁]; field_simp; ring
  have hδB_pos : 0 < δ / B := div_pos hδ0 hBpos
  have hδB_le : δ / B ≤ 1 / 4 := (div_le_iff₀ hBpos).mpr (by nlinarith)
  have hu0_ge_m : (m : ℝ) ≤ u₀ := by
    dsimp only [u₀]
    rw [le_div_iff₀ hBpos]
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    push_cast
    linarith
  have hu1_le_m1 : u₁ ≤ (m : ℝ) + 1 := by
    dsimp only [u₁]
    rw [div_le_iff₀ hBpos]
    have hrB : (r : ℝ) + 1 ≤ B := by exact_mod_cast (Nat.succ_le_of_lt hr)
    push_cast
    linarith
  set a := Real.exp u₀
  set b := Real.exp u₁
  have haX : huxleyX ≤ a := by
    have hXpos : 0 < huxleyX := lt_of_lt_of_le (by norm_num) four_le_huxleyX
    rw [← Real.exp_log hXpos]
    exact Real.exp_le_exp.mpr (hmX.trans hu0_ge_m)
  have hab_eq : b - a = a * (Real.exp (δ / B) - 1) := by
    dsimp only [a, b]
    rw [show u₁ = u₀ + (δ / B) by linarith [hu_diff], Real.exp_add]
    ring
  have hb_sub_hi : b - a ≤ 2 * a * (δ / B) := by
    rw [hab_eq]
    have := exp_sub_one_le_two_mul hδB_pos.le (hδB_le.trans (by norm_num))
    have ha_pos : 0 < a := Real.exp_pos u₀
    nlinarith
  have hb_sub_le_a : b - a ≤ a := by
    have ha_pos : 0 < a := Real.exp_pos u₀
    nlinarith
  have hb_sub_lo : a ^ (3 / 4 : ℝ) ≤ b - a := by
    have hexp_lo : δ / B ≤ Real.exp (δ / B) - 1 := by
      linarith [Real.add_one_le_exp (δ / B)]
    have ha_pos : 0 < a := Real.exp_pos u₀
    have h1 : a * (δ / B) ≤ b - a := by rw [hab_eq]; nlinarith
    have h2 : (B : ℝ) / δ ≤ Real.exp (u₀ / 4) :=
      hrat.trans (Real.exp_le_exp.mpr (by linarith))
    have h3 : Real.exp (-(u₀ / 4)) ≤ δ / B := by
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) hBpos]
      rw [div_le_iff₀ hδ0] at h2
      linarith
    have hpow : a ^ (3 / 4 : ℝ) = a * Real.exp (-(u₀ / 4)) := by
      dsimp only [a]
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1; ring
    rw [hpow]
    exact (mul_le_mul_of_nonneg_left h3 ha_pos.le).trans h1
  have hsub_finset :
      F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ subHole B m r δ) ⊆
        (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨_, hp_prime, hlog_lo, hlog_hi⟩ := hp
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
    have hap : a < p := by
      dsimp only [a]
      rw [← Real.exp_log hp_pos]
      exact Real.exp_lt_exp.mpr hlog_lo
    have hpb : (p : ℝ) < b := by
      dsimp only [b]
      rw [← Real.exp_log hp_pos]
      exact Real.exp_lt_exp.mpr hlog_hi
    rw [Finset.mem_Ioc]
    exact ⟨⟨(Nat.floor_lt (Real.exp_pos u₀).le).mpr hap, Nat.le_floor hpb.le⟩, hp_prime⟩
  have ha_le_m1 : a ≤ Real.exp ((m : ℝ) + 1) :=
    Real.exp_le_exp.mpr ((by linarith : u₀ ≤ u₁).trans hu1_le_m1)
  have hab : a ≤ b := Real.exp_le_exp.mpr (by linarith)
  calc (∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ subHole B m r δ),
          Real.log (p : ℝ))
      ≤ ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_finset fun p hp _ =>
          Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
    _ ≤ Chebyshev.psi b - Chebyshev.psi a := sum_prime_log_Ioc_le_psi_sub hab
    _ ≤ 6 * (b - a) := psi_sub_le_six_mul haX hb_sub_lo hb_sub_le_a
    _ ≤ 6 * (2 * a * (δ / B)) := mul_le_mul_of_nonneg_left hb_sub_hi (by norm_num)
    _ ≤ 12 * Real.exp ((m : ℝ) + 1) * (δ / B) := by nlinarith

theorem sum_prime_log_holeSet_inter_Icc_le {B m : ℕ} {δ : ℝ} (hB : 1 ≤ B)
    (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (hmX : Real.log huxleyX ≤ (m : ℝ)) (hrat : (B : ℝ) / δ ≤ Real.exp ((m : ℝ) / 4))
    (F : Finset ℕ) :
    (∑ p ∈ F.filter
        (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ holeSet B δ ∩ Set.Icc (m : ℝ) (m + 1)),
        Real.log (p : ℝ)) ≤
      12 * Real.exp ((m : ℝ) + 1) * δ := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hsub :
      F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ holeSet B δ ∩ Set.Icc (m : ℝ) (m + 1)) ⊆
        (Finset.range B).biUnion
          (fun r => F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ subHole B m r δ)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [holeSet_inter_Icc_eq hB hδ0 hδ4 m, Set.mem_iUnion] at hp
    obtain ⟨hpF, hp_prime, r, hr⟩ := hp
    rw [Set.mem_iUnion] at hr
    obtain ⟨hrB, hmem⟩ := hr
    exact Finset.mem_biUnion.mpr ⟨r, hrB, Finset.mem_filter.mpr ⟨hpF, hp_prime, hmem⟩⟩
  calc (∑ p ∈ F.filter
          (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ holeSet B δ ∩ Set.Icc (m : ℝ) (m + 1)),
          Real.log (p : ℝ))
      ≤ ∑ p ∈ (Finset.range B).biUnion
          (fun r => F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ subHole B m r δ)),
          Real.log (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => by
          obtain ⟨r, _, hp'⟩ := Finset.mem_biUnion.mp hp
          exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp').2.1.one_lt.le)
    _ ≤ ∑ r ∈ Finset.range B,
          ∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ subHole B m r δ),
            Real.log (p : ℝ) :=
        sum_biUnion_le_of_nonneg _ _ fun _ _ p hp =>
          Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_lt.le)
    _ ≤ ∑ _r ∈ Finset.range B, (12 * Real.exp ((m : ℝ) + 1) * (δ / B)) :=
        Finset.sum_le_sum fun r hr =>
          sum_prime_log_subHole_le hB (Finset.mem_range.mp hr) hδ0 hδ4 hmX hrat F
    _ = 12 * Real.exp ((m : ℝ) + 1) * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

/-- **Prime logarithmic mass in `unitHole Θ m` for `m ≥ U_1`.** -/
theorem sum_prime_log_unitHole_le {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) {m : ℕ}
    (hm : winNat Θ 1 ≤ m) (F : Finset ℕ) :
    (∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m),
        Real.log (p : ℝ)) ≤
      24 * Real.exp ((m : ℝ) + 1) * holeWidth (winIdx Θ m) := by
  have hmX : Real.log huxleyX ≤ (m : ℝ) :=
    (log_huxleyX_le_winNat_one Θ).trans (by exact_mod_cast hm)
  have hk1 : 1 ≤ winIdx Θ m := one_le_winIdx_of_ge Θ hm
  obtain ⟨n, hn⟩ : ∃ n, winIdx Θ m = n + 1 := ⟨winIdx Θ m - 1, by omega⟩
  have hU_le : (winNat Θ (n + 1) : ℝ) ≤ m := by
    have := winNat_le_of_winIdx Θ m
    rw [hn] at this
    exact_mod_cast this
  have hexp_le : Real.exp ((winNat Θ (n + 1) : ℝ) / 8) ≤ Real.exp ((m : ℝ) / 4) :=
    Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hrat1 : (baseFreq Θ (winIdx Θ m) : ℝ) / holeWidth (winIdx Θ m) ≤ Real.exp ((m : ℝ) / 4) := by
    rw [hn]
    exact (baseFreq_div_holeWidth_succ_le hΘ n).trans hexp_le
  have hrat2 : (baseFreq Θ (winIdx Θ m + 1) : ℝ) / holeWidth (winIdx Θ m + 1) ≤
      Real.exp ((m : ℝ) / 4) := by
    rw [hn]
    exact (baseFreq_div_holeWidth_succ_succ_le hΘ hΘ2 n).trans hexp_le
  set S₁ := holeSet (baseFreq Θ (winIdx Θ m)) (holeWidth (winIdx Θ m)) ∩ Set.Icc (m : ℝ) (m + 1)
  set S₂ := holeSet (baseFreq Θ (winIdx Θ m + 1)) (holeWidth (winIdx Θ m + 1)) ∩
    Set.Icc (m : ℝ) (m + 1)
  have hsub :
      F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m) ⊆
        F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ S₁) ∪
          F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ S₂) := by
    intro p hp
    rw [Finset.mem_filter, unitHole, if_neg (not_lt.mpr hm), Set.union_inter_distrib_right] at hp
    rcases hp with ⟨hpF, hp_prime, hp1 | hp2⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpF, hp_prime, hp1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpF, hp_prime, hp2⟩)
  have hb1 := sum_prime_log_holeSet_inter_Icc_le (one_le_baseFreq hΘ (winIdx Θ m))
    (holeWidth_pos (winIdx Θ m)) (holeWidth_le_quarter (winIdx Θ m)) hmX hrat1 F
  have hb2 := sum_prime_log_holeSet_inter_Icc_le (one_le_baseFreq hΘ (winIdx Θ m + 1))
    (holeWidth_pos (winIdx Θ m + 1)) (holeWidth_le_quarter (winIdx Θ m + 1)) hmX hrat2 F
  have hanti : holeWidth (winIdx Θ m + 1) ≤ holeWidth (winIdx Θ m) :=
    holeWidth_antitone (Nat.le_succ _)
  calc (∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m), Real.log (p : ℝ))
      ≤ ∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ S₁) ∪
          F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ S₂), Real.log (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => by
          rcases Finset.mem_union.mp hp with hp1 | hp2
          · exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp1).2.1.one_lt.le)
          · exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp2).2.1.one_lt.le)
    _ ≤ (∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ S₁), Real.log (p : ℝ)) +
          (∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ S₂), Real.log (p : ℝ)) :=
        sum_union_le_of_nonneg fun p hp => by
          rcases Finset.mem_union.mp hp with hp1 | hp2
          · exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp1).2.1.one_lt.le)
          · exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp2).2.1.one_lt.le)
    _ ≤ 12 * Real.exp ((m : ℝ) + 1) * holeWidth (winIdx Θ m) +
          12 * Real.exp ((m : ℝ) + 1) * holeWidth (winIdx Θ m + 1) := add_le_add hb1 hb2
    _ ≤ 24 * Real.exp ((m : ℝ) + 1) * holeWidth (winIdx Θ m) := by
        have := Real.exp_pos ((m : ℝ) + 1)
        nlinarith

theorem sum_exp_range_le (K : ℕ) :
    (∑ m ∈ Finset.range (K + 1), Real.exp ((m : ℝ) + 1)) ≤ Real.exp ((K : ℝ) + 2) := by
  have he1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hrew : ∀ m : ℕ, Real.exp ((m : ℝ) + 1) = Real.exp 1 * (Real.exp 1) ^ m := fun m => by
    rw [add_comm, Real.exp_add, ← mul_one (m : ℝ), Real.exp_nat_mul]
  simp_rw [hrew, ← Finset.mul_sum, geom_sum_eq (by linarith : Real.exp 1 ≠ 1)]
  have hden : 1 ≤ Real.exp 1 - 1 := by linarith
  have hdiv : ((Real.exp 1) ^ (K + 1) - 1) / (Real.exp 1 - 1) ≤ (Real.exp 1) ^ (K + 1) := by
    rw [div_le_iff₀ (by linarith)]
    have hpow : 0 ≤ (Real.exp 1) ^ (K + 1) := by positivity
    nlinarith
  calc Real.exp 1 * (((Real.exp 1) ^ (K + 1) - 1) / (Real.exp 1 - 1))
      ≤ Real.exp 1 * (Real.exp 1) ^ (K + 1) := mul_le_mul_of_nonneg_left hdiv (Real.exp_pos 1).le
    _ = Real.exp ((K : ℝ) + 2) := by
        rw [← Real.exp_nat_mul, mul_one, ← Real.exp_add]
        congr 1; push_cast; ring

/-- **Chebyshev prime density zero:** `(∑_{p ≤ X, p ∈ E} log p) / X → 0` as `X → ∞`. -/
theorem tendsto_chebyshev_exPrimes {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    Tendsto
      (fun X : ℝ =>
        (∑ p ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ exPrimes Θ),
          Real.log (p : ℝ)) / X)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ_ε : ℝ := ε / (2 * Real.exp 2)
  have hδ_pos : 0 < δ_ε := by positivity
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (tendsto_holeWidth.eventually (gt_mem_nhds (show 0 < δ_ε / 24 by positivity)))
  set M₀ : ℕ := max (winNat Θ K) (winNat Θ 1)
  set C₀ : ℝ := ∑ p ∈ Finset.Icc 1 ⌊Real.exp M₀⌋₊, Real.log (p : ℝ)
  have hC₀_nn : 0 ≤ C₀ := Finset.sum_nonneg fun p hp =>
    Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hp).1)
  refine ⟨max 2 (2 * (C₀ + 1) / ε), fun X hX => ?_⟩
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hXpos : 0 < X := by linarith
  have hXC : 2 * (C₀ + 1) / ε ≤ X := (le_max_right _ _).trans hX
  set F := Finset.Icc 1 ⌊X⌋₊
  have hsum_nn : 0 ≤ ∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ p ∈ exPrimes Θ), Real.log (p : ℝ) :=
    Finset.sum_nonneg fun p hp =>
      Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_lt.le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hsum_nn hXpos.le), div_lt_iff₀ hXpos]
  -- Split into `m < M₀` (primes `≤ exp M₀`) and `M₀ ≤ m ≤ ⌊log X⌋₊`
  set L : ℕ := ⌊Real.log X⌋₊
  have hsub :
      F.filter (fun p : ℕ => p.Prime ∧ p ∈ exPrimes Θ) ⊆
        Finset.Icc 1 ⌊Real.exp M₀⌋₊ ∪
          ((Finset.range (L + 1)).filter (M₀ ≤ ·)).biUnion
            (fun m => F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpF, hp_prime, _, hp_ex⟩ := hp
    rw [exSet, Set.mem_iUnion] at hp_ex
    obtain ⟨m, hum⟩ := hp_ex
    by_cases hmM : m < M₀
    · apply Finset.mem_union_left
      have hlog_le : Real.log (p : ℝ) ≤ (M₀ : ℝ) := by
        have h1 := (unitHole_subset_Icc Θ m hum).2
        have hmR : (m : ℝ) + 1 ≤ M₀ := by exact_mod_cast (Nat.succ_le_of_lt hmM)
        linarith
      have hp_le : (p : ℝ) ≤ Real.exp M₀ := by
        rw [← Real.exp_log (by exact_mod_cast hp_prime.pos : (0 : ℝ) < p)]
        exact Real.exp_le_exp.mpr hlog_le
      exact Finset.mem_Icc.mpr ⟨hp_prime.one_lt.le, Nat.le_floor hp_le⟩
    · apply Finset.mem_union_right
      have hm_le : (m : ℝ) ≤ Real.log (p : ℝ) := (unitHole_subset_Icc Θ m hum).1
      have hpX : (p : ℝ) ≤ X :=
        (by exact_mod_cast (Finset.mem_Icc.mp hpF).2 : (p : ℝ) ≤ ⌊X⌋₊).trans
          (Nat.floor_le hXpos.le)
      have hlogX : Real.log (p : ℝ) ≤ Real.log X :=
        Real.log_le_log (by exact_mod_cast hp_prime.pos) hpX
      have hmL : m ≤ L := Nat.le_floor (hm_le.trans hlogX)
      exact Finset.mem_biUnion.mpr
        ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hmL), not_lt.mp hmM⟩,
          Finset.mem_filter.mpr ⟨hpF, hp_prime, hum⟩⟩
  have htail_each : ∀ m ∈ (Finset.range (L + 1)).filter (M₀ ≤ ·),
      (∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m),
          Real.log (p : ℝ)) ≤
        δ_ε * Real.exp ((m : ℝ) + 1) := by
    intro m hm
    have hmM : M₀ ≤ m := (Finset.mem_filter.mp hm).2
    have hm1 : winNat Θ 1 ≤ m := (le_max_right _ _).trans hmM
    have hmK : K ≤ winIdx Θ m := le_winIdx_of_winNat_le Θ ((le_max_left _ _).trans hmM)
    have hw : 24 * holeWidth (winIdx Θ m) ≤ δ_ε := by linarith [hK _ hmK]
    calc (∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m),
            Real.log (p : ℝ))
        ≤ 24 * Real.exp ((m : ℝ) + 1) * holeWidth (winIdx Θ m) :=
          sum_prime_log_unitHole_le hΘ hΘ2 hm1 F
      _ = (24 * holeWidth (winIdx Θ m)) * Real.exp ((m : ℝ) + 1) := by ring
      _ ≤ δ_ε * Real.exp ((m : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
  have htail_sum :
      (∑ m ∈ (Finset.range (L + 1)).filter (M₀ ≤ ·), δ_ε * Real.exp ((m : ℝ) + 1)) ≤
        (ε / 2) * X := by
    have h1 : (∑ m ∈ (Finset.range (L + 1)).filter (M₀ ≤ ·), δ_ε * Real.exp ((m : ℝ) + 1)) ≤
        ∑ m ∈ Finset.range (L + 1), δ_ε * Real.exp ((m : ℝ) + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
    have h2 : (∑ m ∈ Finset.range (L + 1), δ_ε * Real.exp ((m : ℝ) + 1)) ≤
        δ_ε * Real.exp ((L : ℝ) + 2) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_exp_range_le L) hδ_pos.le
    have hL_le : (L : ℝ) ≤ Real.log X :=
      Nat.floor_le (Real.log_nonneg (by linarith))
    have hexpL : Real.exp ((L : ℝ) + 2) ≤ Real.exp 2 * X := by
      calc Real.exp ((L : ℝ) + 2) ≤ Real.exp (Real.log X + 2) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp 2 * X := by rw [add_comm, Real.exp_add, Real.exp_log hXpos]
    calc (∑ m ∈ (Finset.range (L + 1)).filter (M₀ ≤ ·), δ_ε * Real.exp ((m : ℝ) + 1))
        ≤ δ_ε * Real.exp ((L : ℝ) + 2) := h1.trans h2
      _ ≤ δ_ε * (Real.exp 2 * X) := mul_le_mul_of_nonneg_left hexpL hδ_pos.le
      _ = (ε / 2) * X := by dsimp only [δ_ε]; field_simp
  have htot :
      (∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ p ∈ exPrimes Θ), Real.log (p : ℝ)) ≤
        C₀ + (ε / 2) * X := by
    have hnn_union : ∀ p ∈ Finset.Icc 1 ⌊Real.exp M₀⌋₊ ∪
        ((Finset.range (L + 1)).filter (M₀ ≤ ·)).biUnion
          (fun m => F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m)),
        0 ≤ Real.log (p : ℝ) := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp1 | hp2
      · exact Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hp1).1)
      · obtain ⟨m, _, hp'⟩ := Finset.mem_biUnion.mp hp2
        exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp').2.1.one_lt.le)
    calc (∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ p ∈ exPrimes Θ), Real.log (p : ℝ))
        ≤ ∑ p ∈ Finset.Icc 1 ⌊Real.exp M₀⌋₊ ∪
            ((Finset.range (L + 1)).filter (M₀ ≤ ·)).biUnion
              (fun m => F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m)),
            Real.log (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hnn_union p hp
      _ ≤ C₀ + ∑ p ∈ ((Finset.range (L + 1)).filter (M₀ ≤ ·)).biUnion
              (fun m => F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m)),
              Real.log (p : ℝ) :=
          sum_union_le_of_nonneg hnn_union
      _ ≤ C₀ + ∑ m ∈ (Finset.range (L + 1)).filter (M₀ ≤ ·),
              ∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m),
                Real.log (p : ℝ) :=
          add_le_add le_rfl (sum_biUnion_le_of_nonneg ((Finset.range (L + 1)).filter (M₀ ≤ ·))
            (fun m => F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m))
            (f := fun p : ℕ => Real.log (p : ℝ)) fun _ _ p hp =>
              Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_lt.le))
      _ ≤ C₀ + ∑ m ∈ (Finset.range (L + 1)).filter (M₀ ≤ ·), δ_ε * Real.exp ((m : ℝ) + 1) :=
          add_le_add le_rfl (Finset.sum_le_sum htail_each)
      _ ≤ C₀ + (ε / 2) * X := add_le_add le_rfl htail_sum
  have hC₀_lt : C₀ < (ε / 2) * X := by
    have := (div_le_iff₀ hε).mp hXC
    linarith
  linarith

/-! ### Relative logarithmic density zero (`σ ↓ 1`) -/

/-- Near `σ = 1⁺`, the prime Dirichlet series satisfies `wSum primeWeight σ ≥ 1 / (4 (σ − 1))`. -/
theorem eventually_wSum_primeWeight_ge :
    ∀ᶠ σ : ℝ in 𝓝[>] 1, 1 / (4 * (σ - 1)) ≤ wSum primeWeight σ := by
  have hre := (Complex.continuous_re.tendsto _).comp
    _root_.RHTower.tendsto_neg_logDeriv_riemannZeta_sub_one_div_real
  obtain ⟨γ, hγ_def⟩ : ∃ γ : ℝ, γ = Real.eulerMascheroniConstant := ⟨_, rfl⟩
  have hlim_ev := hre.eventually
    (lt_mem_nhds (show -(γ + 1) < (-(Real.eulerMascheroniConstant : ℂ)).re by rw [← hγ_def]; simp))
  have hhigh_sum : Summable fun j : ℕ => higherWeight j * ((j : ℝ) + 1) ^ (-1 : ℝ) :=
    summable_higherWeight (by norm_num : (1 : ℝ) / 2 < 1)
  obtain ⟨H, hH_def⟩ : ∃ H : ℝ, H = ∑' j : ℕ, higherWeight j * ((j : ℝ) + 1) ^ (-1 : ℝ) :=
    ⟨_, rfl⟩
  have hH_nn : 0 ≤ H := hH_def ▸ tsum_nonneg fun j => mul_nonneg (higherWeight_nonneg j) (by positivity)
  obtain ⟨C, hC_def⟩ : ∃ C : ℝ, C = |γ| + 1 + H := ⟨_, rfl⟩
  have hC_pos : 0 < C + 1 := by linarith [abs_nonneg γ, hH_nn, hC_def]
  filter_upwards [self_mem_nhdsWithin, hlim_ev,
    Ioo_mem_nhdsGT (lt_add_of_pos_right (1 : ℝ) (show 0 < 1 / (2 * (C + 1)) by positivity))]
    with σ hσ1 hvm hσ_close
  have hσ_gt : 1 < σ := hσ1
  have hsub_pos : 0 < σ - 1 := by linarith
  -- Extract `vmSum σ ≥ 1 / (σ - 1) - (|γ| + 1)`
  have hvm_eq : (-deriv riemannZeta σ / riemannZeta σ - 1 / ((σ : ℂ) - 1)).re =
      vmSum σ - 1 / (σ - 1) := by
    have hlog := ofReal_vmSum hσ_gt
    rw [logDeriv_apply] at hlog
    have h1 : -deriv riemannZeta σ / riemannZeta σ = ((vmSum σ : ℝ) : ℂ) := by
      rw [hlog]; ring
    have h2 : (1 : ℂ) / ((σ : ℂ) - 1) = ((1 / (σ - 1) : ℝ) : ℂ) := by push_cast; rfl
    rw [h1, h2, ← Complex.ofReal_sub, Complex.ofReal_re]
  have hvm' : -(γ + 1) < vmSum σ - 1 / (σ - 1) := by
    dsimp only [Function.comp_apply] at hvm
    rwa [hvm_eq] at hvm
  -- Compare `wSum primeWeight σ = vmSum σ - wSum higherWeight σ`
  have hp_sum := samplingWeight_primeWeight.summable hσ_gt
  have hh_sum := summable_higherWeight (by linarith : (1 : ℝ) / 2 < σ)
  have hsplit : vmSum σ = wSum primeWeight σ + wSum higherWeight σ := by
    rw [vmSum, wSum, wSum, ← hp_sum.tsum_add hh_sum]
    refine tsum_congr fun j => ?_
    rw [← add_mul, primeWeight_add_higherWeight]
  have hhigh_le : wSum higherWeight σ ≤ H := by
    rw [hH_def]
    refine Summable.tsum_le_tsum (fun j => ?_) hh_sum hhigh_sum
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)) (higherWeight_nonneg j)
  have hγ_le : -γ ≤ |γ| := neg_le_abs γ
  have hw_ge : 1 / (σ - 1) - C ≤ wSum primeWeight σ := by
    linarith [hvm', hsplit, hγ_le, hhigh_le, hC_def]
  have hC_small : C ≤ 1 / (2 * (σ - 1)) := by
    have hlt : σ - 1 < 1 / (2 * (C + 1)) := by linarith [hσ_close.2]
    rw [lt_div_iff₀ (by positivity)] at hlt
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hfrac : 1 / (σ - 1) - 1 / (2 * (σ - 1)) = 1 / (2 * (σ - 1)) := by field_simp; ring
  have hhalf : 1 / (4 * (σ - 1)) ≤ 1 / (2 * (σ - 1)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-- **Relative logarithmic density zero:**
`Σ_{p ∈ E} log p · p^{−σ} / Σ_p log p · p^{−σ} → 0` as `σ ↓ 1`. -/
theorem tendsto_relLogDensity_exPrimes {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2)
    [DecidablePred (· ∈ exPrimes Θ)] :
    Tendsto
      (fun σ : ℝ =>
        wSum (fun j => primeWeight j - primeOffWeight (exPrimes Θ) j) σ /
          wSum primeWeight σ)
      (𝓝[>] 1) (𝓝 0) := by
  set h : ℕ → ℝ := fun j => primeWeight j - primeOffWeight (exPrimes Θ) j
  have hh_eq : ∀ j : ℕ, h j =
      if (j + 1).Prime ∧ (j + 1) ∈ exPrimes Θ then Real.log ((j : ℝ) + 1) else 0 := by
    intro j
    by_cases hp : (j + 1).Prime
    · by_cases he : (j + 1) ∈ exPrimes Θ
      · simp [h, primeWeight, primeOffWeight, hp, he, vonMangoldt_apply_prime hp, Nat.cast_add]
      · simp [h, primeWeight, primeOffWeight, hp, he]
    · simp [h, primeWeight, primeOffWeight, hp]
  have hh_nn : ∀ j, 0 ≤ h j := fun j => by
    rw [hh_eq]; split_ifs <;> [exact log_add_one_nonneg j; exact le_rfl]
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ_ε : ℝ := ε / (20 * Real.exp 1)
  have hδ_pos : 0 < δ_ε := by positivity
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (tendsto_holeWidth.eventually (gt_mem_nhds (show 0 < δ_ε / 24 by positivity)))
  set M₀ : ℕ := max (winNat Θ K) (winNat Θ 1)
  set C₀ : ℝ := ∑ p ∈ Finset.Icc 1 ⌊Real.exp M₀⌋₊, Real.log (p : ℝ)
  have hC₀_nn : 0 ≤ C₀ := Finset.sum_nonneg fun p hp =>
    Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hp).1)
  -- Bound `wSum h σ` for every `1 < σ ≤ 3 / 2` via `Real.tsum_le_of_sum_range_le`
  have hwSum_le : ∀ σ : ℝ, 1 < σ → σ ≤ 3 / 2 →
      wSum h σ ≤ C₀ + 2 * Real.exp 1 * δ_ε / (σ - 1) := by
    intro σ hσ1 hσ32
    have hsub_pos : 0 < σ - 1 := by linarith
    refine Real.tsum_le_of_sum_range_le (fun j => mul_nonneg (hh_nn j) (by positivity)) fun N => ?_
    -- Reindex `j ∈ range N` by `p = j + 1 ∈ Icc 1 N`
    have hreindex :
        (∑ j ∈ Finset.range N, h j * ((j : ℝ) + 1) ^ (-σ)) =
          ∑ p ∈ (Finset.Icc 1 N).filter (fun p : ℕ => p.Prime ∧ p ∈ exPrimes Θ),
            Real.log (p : ℝ) * (p : ℝ) ^ (-σ) := by
      rw [Finset.sum_filter]
      have hset : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by ext x; simp
      rw [hset, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [add_comm 1 j, hh_eq]
      split_ifs <;> push_cast <;> ring
    rw [hreindex]
    set F := Finset.Icc 1 N
    -- Split into `m < M₀` (`p ≤ exp M₀`) and `m ≥ M₀` (`m ≤ N`)
    have hsub :
        F.filter (fun p : ℕ => p.Prime ∧ p ∈ exPrimes Θ) ⊆
          Finset.Icc 1 ⌊Real.exp M₀⌋₊ ∪
            ((Finset.range (N + 1)).filter (M₀ ≤ ·)).biUnion
              (fun m => F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpF, hp_prime, _, hp_ex⟩ := hp
      rw [exSet, Set.mem_iUnion] at hp_ex
      obtain ⟨m, hum⟩ := hp_ex
      by_cases hmM : m < M₀
      · apply Finset.mem_union_left
        have hlog_le : Real.log (p : ℝ) ≤ (M₀ : ℝ) := by
          have h1 := (unitHole_subset_Icc Θ m hum).2
          have hmR : (m : ℝ) + 1 ≤ M₀ := by exact_mod_cast (Nat.succ_le_of_lt hmM)
          linarith
        have hp_le : (p : ℝ) ≤ Real.exp M₀ := by
          rw [← Real.exp_log (by exact_mod_cast hp_prime.pos : (0 : ℝ) < p)]
          exact Real.exp_le_exp.mpr hlog_le
        exact Finset.mem_Icc.mpr ⟨hp_prime.one_lt.le, Nat.le_floor hp_le⟩
      · apply Finset.mem_union_right
        have hm_le_log : (m : ℝ) ≤ Real.log (p : ℝ) := (unitHole_subset_Icc Θ m hum).1
        have hlog_le_p : Real.log (p : ℝ) ≤ (p : ℝ) := by
          have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
          linarith [Real.log_le_sub_one_of_pos hp_pos]
        have hpN : (p : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hpF).2
        have hmN : m ≤ N := by exact_mod_cast (hm_le_log.trans (hlog_le_p.trans hpN))
        exact Finset.mem_biUnion.mpr
          ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hmN), not_lt.mp hmM⟩,
            Finset.mem_filter.mpr ⟨hpF, hp_prime, hum⟩⟩
    -- Head bound (`m < M₀`)
    have hhead : (∑ p ∈ Finset.Icc 1 ⌊Real.exp M₀⌋₊, Real.log (p : ℝ) * (p : ℝ) ^ (-σ)) ≤ C₀ := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
      have hrpow : (p : ℝ) ^ (-σ) ≤ 1 := by
        calc (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (0 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
          _ = 1 := Real.rpow_zero _
      exact mul_le_of_le_one_right (Real.log_nonneg hp1) hrpow
    -- Block bound (`m ≥ M₀`)
    have hblock : ∀ m ∈ (Finset.range (N + 1)).filter (M₀ ≤ ·),
        (∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m),
            Real.log (p : ℝ) * (p : ℝ) ^ (-σ)) ≤
          (Real.exp 1 * δ_ε) * (Real.exp (-(σ - 1))) ^ m := by
      intro m hm
      have hmM : M₀ ≤ m := (Finset.mem_filter.mp hm).2
      have hm1 : winNat Θ 1 ≤ m := (le_max_right _ _).trans hmM
      have hmK : K ≤ winIdx Θ m := le_winIdx_of_winNat_le Θ ((le_max_left _ _).trans hmM)
      have hw : 24 * holeWidth (winIdx Θ m) ≤ δ_ε := by linarith [hK _ hmK]
      have hp_rpow : ∀ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m),
          Real.log (p : ℝ) * (p : ℝ) ^ (-σ) ≤ Real.log (p : ℝ) * Real.exp (-σ * m) := by
        intro p hp
        obtain ⟨_, hp_prime, hum⟩ := Finset.mem_filter.mp hp
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
        have hm_le : (m : ℝ) ≤ Real.log (p : ℝ) := (unitHole_subset_Icc Θ m hum).1
        have hrpow_le : (p : ℝ) ^ (-σ) ≤ Real.exp (-σ * m) := by
          rw [Real.rpow_def_of_pos hp_pos]
          exact Real.exp_le_exp.mpr (by nlinarith)
        exact mul_le_mul_of_nonneg_left hrpow_le
          (Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le))
      calc (∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m),
              Real.log (p : ℝ) * (p : ℝ) ^ (-σ))
          ≤ ∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m),
              Real.log (p : ℝ) * Real.exp (-σ * m) := Finset.sum_le_sum hp_rpow
        _ = (∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m),
              Real.log (p : ℝ)) * Real.exp (-σ * m) := (Finset.sum_mul _ _ _).symm
        _ ≤ (24 * Real.exp ((m : ℝ) + 1) * holeWidth (winIdx Θ m)) * Real.exp (-σ * m) :=
            mul_le_mul_of_nonneg_right (sum_prime_log_unitHole_le hΘ hΘ2 hm1 F)
              (Real.exp_pos _).le
        _ ≤ (δ_ε * Real.exp ((m : ℝ) + 1)) * Real.exp (-σ * m) := by
            rw [show 24 * Real.exp ((m : ℝ) + 1) * holeWidth (winIdx Θ m) =
                (24 * holeWidth (winIdx Θ m)) * Real.exp ((m : ℝ) + 1) by ring]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le) (Real.exp_pos _).le
        _ = (Real.exp 1 * δ_ε) * (Real.exp (-(σ - 1))) ^ m := by
            rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add,
              show ((m : ℝ) + 1) + (-σ * (m : ℝ)) = 1 + (m : ℝ) * (-(σ - 1)) by ring,
              Real.exp_add]
            ring
    -- Geometric sum over `m`
    set q : ℝ := Real.exp (-(σ - 1))
    have hq0 : 0 ≤ q := (Real.exp_pos _).le
    have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hgeo : Summable fun m : ℕ => q ^ m := summable_geometric_of_lt_one hq0 hq1
    have h1_sub_q : (σ - 1) / 2 ≤ 1 - q := by
      have hexp_ge : 1 + (σ - 1) ≤ Real.exp (σ - 1) := by linarith [Real.add_one_le_exp (σ - 1)]
      have hq_inv : q * Real.exp (σ - 1) = 1 := by
        dsimp only [q]; rw [← Real.exp_add]; simp
      have hq_le : q * (1 + (σ - 1)) ≤ 1 := by
        calc q * (1 + (σ - 1)) ≤ q * Real.exp (σ - 1) := mul_le_mul_of_nonneg_left hexp_ge hq0
          _ = 1 := hq_inv
      have h32 : 1 + (σ - 1) ≤ 2 := by linarith
      nlinarith
    have htsum_q : (∑' m : ℕ, q ^ m) ≤ 2 / (σ - 1) := by
      rw [tsum_geometric_of_lt_one hq0 hq1, inv_eq_one_div]
      calc 1 / (1 - q) ≤ 1 / ((σ - 1) / 2) :=
            one_div_le_one_div_of_le (by positivity) h1_sub_q
        _ = 2 / (σ - 1) := by field_simp
    have htail_tot :
        (∑ m ∈ (Finset.range (N + 1)).filter (M₀ ≤ ·), (Real.exp 1 * δ_ε) * q ^ m) ≤
          2 * Real.exp 1 * δ_ε / (σ - 1) := by
      have h1 : (∑ m ∈ (Finset.range (N + 1)).filter (M₀ ≤ ·), (Real.exp 1 * δ_ε) * q ^ m) ≤
          ∑ m ∈ Finset.range (N + 1), (Real.exp 1 * δ_ε) * q ^ m :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
      have h2 : (∑ m ∈ Finset.range (N + 1), (Real.exp 1 * δ_ε) * q ^ m) ≤
          ∑' m : ℕ, (Real.exp 1 * δ_ε) * q ^ m :=
        (hgeo.mul_left _).sum_le_tsum _ fun _ _ => by positivity
      rw [tsum_mul_left] at h2
      calc (∑ m ∈ (Finset.range (N + 1)).filter (M₀ ≤ ·), (Real.exp 1 * δ_ε) * q ^ m)
          ≤ (Real.exp 1 * δ_ε) * ∑' m : ℕ, q ^ m := h1.trans h2
        _ ≤ (Real.exp 1 * δ_ε) * (2 / (σ - 1)) :=
            mul_le_mul_of_nonneg_left htsum_q (by positivity)
        _ = 2 * Real.exp 1 * δ_ε / (σ - 1) := by ring
    have hnn_union : ∀ p ∈ Finset.Icc 1 ⌊Real.exp M₀⌋₊ ∪
        ((Finset.range (N + 1)).filter (M₀ ≤ ·)).biUnion
          (fun m => F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m)),
        0 ≤ Real.log (p : ℝ) * (p : ℝ) ^ (-σ) := by
      intro p hp
      have hp1 : (1 : ℝ) ≤ p := by
        rcases Finset.mem_union.mp hp with hp1 | hp2
        · exact_mod_cast (Finset.mem_Icc.mp hp1).1
        · obtain ⟨m, _, hp'⟩ := Finset.mem_biUnion.mp hp2
          exact_mod_cast (Finset.mem_filter.mp hp').2.1.one_lt.le
      exact mul_nonneg (Real.log_nonneg hp1) (by positivity)
    calc (∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ p ∈ exPrimes Θ), Real.log (p : ℝ) * (p : ℝ) ^ (-σ))
        ≤ ∑ p ∈ Finset.Icc 1 ⌊Real.exp M₀⌋₊ ∪
            ((Finset.range (N + 1)).filter (M₀ ≤ ·)).biUnion
              (fun m => F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m)),
            Real.log (p : ℝ) * (p : ℝ) ^ (-σ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hnn_union p hp
      _ ≤ C₀ + ∑ m ∈ (Finset.range (N + 1)).filter (M₀ ≤ ·),
              ∑ p ∈ F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m),
                Real.log (p : ℝ) * (p : ℝ) ^ (-σ) := by
          have hu1 := sum_union_le_of_nonneg hnn_union
          have hu2 := sum_biUnion_le_of_nonneg ((Finset.range (N + 1)).filter (M₀ ≤ ·))
            (fun m => F.filter (fun p : ℕ => p.Prime ∧ Real.log (p : ℝ) ∈ unitHole Θ m))
            (f := fun p : ℕ => Real.log (p : ℝ) * (p : ℝ) ^ (-σ)) fun _ _ p hp => by
              have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_lt.le
              exact mul_nonneg (Real.log_nonneg hp1) (by positivity)
          exact hu1.trans (add_le_add hhead hu2)
      _ ≤ C₀ + ∑ m ∈ (Finset.range (N + 1)).filter (M₀ ≤ ·), (Real.exp 1 * δ_ε) * q ^ m :=
          add_le_add le_rfl (Finset.sum_le_sum hblock)
      _ ≤ C₀ + 2 * Real.exp 1 * δ_ε / (σ - 1) := add_le_add le_rfl htail_tot
  -- Combine numerator upper bound with denominator lower bound `1 / (4 * (σ - 1))`
  set σ_max : ℝ := min (3 / 2) (1 + ε / (16 * (C₀ + 1)))
  have hσ_max_gt : 1 < σ_max := lt_min (by norm_num) (by linarith [show 0 < ε / (16 * (C₀ + 1)) by positivity])
  filter_upwards [eventually_wSum_primeWeight_ge, Ioo_mem_nhdsGT hσ_max_gt] with σ hden ⟨hσ1, hσ2⟩
  have hsub_pos : 0 < σ - 1 := by linarith
  have hσ32 : σ ≤ 3 / 2 := hσ2.le.trans (min_le_left _ _)
  have hσC : σ - 1 < ε / (16 * (C₀ + 1)) := by
    have := hσ2.trans_le (min_le_right _ _)
    linarith
  have hden_pos : 0 < wSum primeWeight σ := lt_of_lt_of_le (by positivity) hden
  have hnum_nn : 0 ≤ wSum h σ := tsum_nonneg fun j => mul_nonneg (hh_nn j) (by positivity)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hnum_nn hden_pos.le)]
  have hnum := hwSum_le σ hσ1 hσ32
  calc wSum h σ / wSum primeWeight σ
      ≤ (C₀ + 2 * Real.exp 1 * δ_ε / (σ - 1)) / (1 / (4 * (σ - 1))) :=
        (div_le_div_of_nonneg_right hnum hden_pos.le).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
    _ = 4 * C₀ * (σ - 1) + 8 * Real.exp 1 * δ_ε := by field_simp; ring
    _ < ε / 4 + 2 * ε / 5 := by
        have h1 : 4 * C₀ * (σ - 1) < ε / 4 := by
          have := (lt_div_iff₀ (by positivity : 0 < 16 * (C₀ + 1))).mp hσC
          nlinarith
        have h2 : 8 * Real.exp 1 * δ_ε = 2 * ε / 5 := by dsimp only [δ_ε]; field_simp; ring
        linarith
    _ < ε := by linarith

end PeriodicClusterTower

/-! ### Main theorems: almost all primes need an attained top -/

open PeriodicClusterTower in
/-- **Zero configurations need an attained top at almost all primes.** For every `0 < Θ ≤ ½`, there
exist a real-zero-free tempered configuration `Z` in `0 < Re s < 1` with unattained
`sup Re ρ = ½ + Θ`, a measurable lag set `S ⊆ ℝ` of upper density zero, and a prime set `E` of both
Chebyshev prime density zero and relative logarithmic density zero, such that `2 Re S_Z(u) ≥ −5`
for all `u ≥ 0` outside `S` and `2 Re S_Z(log p) ≥ −5` for every prime `p ∉ E`. -/
theorem exists_zeroConfig_primes_off_null_bddBelow_nonattained {Θ : ℝ} (hΘ : 0 < Θ)
    (hΘ2 : Θ ≤ 1 / 2) :
    ∃ (Z : ZeroConfig) (S : Set ℝ) (E : Set ℕ) (_ : DecidablePred (· ∈ E)),
      TemperedConfig Z ∧
      (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧
      (∀ β < 1 / 2 + Θ, ∃ ρ ∈ Z.carrier, β < ρ.re) ∧
      MeasurableSet S ∧
      _root_.RHTower.OneSidedConfiguration.UpperDensityZero S ∧
      (∀ p ∈ E, p.Prime) ∧
      Tendsto
        (fun X : ℝ =>
          (∑ p ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ p ∈ E), Real.log (p : ℝ)) / X)
        atTop (𝓝 0) ∧
      Tendsto
        (fun σ : ℝ => wSum (fun j => primeWeight j - primeOffWeight E j) σ / wSum primeWeight σ)
        (𝓝[>] 1) (𝓝 0) ∧
      (∀ u : ℝ, 0 ≤ u → u ∉ S → -5 ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re) ∧
      (∀ p : ℕ, p.Prime → p ∉ E → -5 ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) := by
  classical
  refine ⟨clusterConfig hΘ hΘ2, exSet Θ, exPrimes Θ, inferInstance,
    temperedConfig_clusterConfig hΘ hΘ2, ?_, ?_, ?_,
    measurableSet_exSet hΘ, upperDensityZero_exSet hΘ,
    fun p hp => hp.1, tendsto_chebyshev_exPrimes hΘ hΘ2, tendsto_relLogDensity_exPrimes hΘ hΘ2,
    fun u hu0 hu => two_re_lagStructure_ge_off_exSet hΘ hΘ2 hu0 hu,
    fun p hp hpE => ?_⟩
  · rintro ρ ⟨idx, rfl⟩
    rw [clusterPt_im]
    have hm1 : 1 ≤ idx.2.1.1 := one_le_activeHarmonic idx.2.1
    have hB1 : 1 ≤ baseFreq Θ idx.1 := one_le_baseFreq hΘ idx.1
    have hmB : (0 : ℝ) < (idx.2.1.1 * baseFreq Θ idx.1 : ℕ) := by
      exact_mod_cast Nat.mul_pos hm1 hB1
    positivity
  · rintro ρ ⟨⟨k, ⟨m, b⟩⟩, rfl⟩
    have h0 := SplineTower.depth_nonneg hΘ k
    have h1 := SplineTower.depth_lt hΘ k
    cases b
    · rw [clusterPt_false_re]; linarith
    · rw [clusterPt_true_re]; linarith
  · intro β hβ
    obtain ⟨k, hk⟩ := SplineTower.exists_depth_gt hΘ (show β - 1 / 2 < Θ by linarith)
    have hne : (activeHarmonics k).Nonempty := by
      obtain ⟨m, hm, hpm⟩ := Finset.exists_ne_zero_of_sum_ne_zero
        (Nat.pos_iff_ne_zero.mp (one_le_cosMass k))
      exact ⟨m, Finset.mem_filter.mpr ⟨hm, Nat.one_le_iff_ne_zero.mpr hpm⟩⟩
    obtain ⟨m, hm⟩ := hne
    exact ⟨clusterPt Θ ⟨k, (⟨m, hm⟩, true)⟩, ⟨⟨k, (⟨m, hm⟩, true)⟩, rfl⟩,
      by rw [clusterPt_true_re]; linarith⟩
  · have hnotS : Real.log p ∉ exSet Θ := fun hS => hpE ⟨hp, hS⟩
    have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    exact two_re_lagStructure_ge_off_exSet hΘ hΘ2 hlog0 hnotS

/-- **Full-width failure (`Θ = ½`, `sup Re ρ = 1`).** Even a crude one-sided bound `2 Re S_Z(log p) ≥ −5`
outside a set of primes of relative logarithmic density zero fails to produce *any* zero-free strip
left of `Re s = 1` without attainment. -/
theorem exists_zeroConfig_primes_off_null_bddBelow_sup_eq_one :
    ∃ (Z : ZeroConfig) (E : Set ℕ) (_ : DecidablePred (· ∈ E)),
      TemperedConfig Z ∧
      (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧
      (∀ β < (1 : ℝ), ∃ ρ ∈ Z.carrier, β < ρ.re) ∧
      Tendsto
        (fun σ : ℝ => wSum (fun j => primeWeight j - primeOffWeight E j) σ / wSum primeWeight σ)
        (𝓝[>] 1) (𝓝 0) ∧
      (∀ p : ℕ, p.Prime → p ∉ E → -5 ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) := by
  obtain ⟨Z, _, E, hdec, hZ, hnoreal, _, hsup, _, _, _, _, hrel, _, htrace⟩ :=
    exists_zeroConfig_primes_off_null_bddBelow_nonattained (Θ := 1 / 2) (by norm_num) le_rfl
  exact ⟨Z, E, hdec, hZ, hnoreal, fun β hβ => hsup β (by linarith), hrel, htrace⟩

/-- **Explicit negation of the unattained almost-all-primes implication for tempered configurations.** -/
theorem not_forall_onLine_of_bddBelow_primes_off_null :
    ¬ (∀ (Z : ZeroConfig) (E : Set ℕ) [DecidablePred (· ∈ E)] (K : ℝ),
        TemperedConfig Z →
        (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) →
        Tendsto
          (fun σ : ℝ => wSum (fun j => primeWeight j - primeOffWeight E j) σ / wSum primeWeight σ)
          (𝓝[>] 1) (𝓝 0) →
        (∀ p : ℕ, p.Prime → p ∉ E → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) →
        ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) := by
  intro hall
  obtain ⟨Z, E, hdec, hZ, hnoreal, hsup, hrel, htrace⟩ :=
    exists_zeroConfig_primes_off_null_bddBelow_sup_eq_one
  obtain ⟨ρ, hρ, hre⟩ := hsup (3 / 4) (by norm_num)
  have honline := @hall Z E hdec 5 hZ hnoreal hrel htrace ρ hρ
  linarith

end GaloisForLFunctions.SurfaceOfSpecZ


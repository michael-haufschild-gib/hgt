import GaloisForLFunctions.HyperbolicArakelovTheory.TheArchimedeanCompensationIsSpherical
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheWeilPrimeKernelIsARenormalizedTorsionEnergy

/-!
# The finite places are trees: Weil's local kernel is a Green function at the Ramanujan point

At the archimedean place the fibre of the hyperbolic Arakelov surface is `ℍ³`, and Weil's kernel
there is the Green function `2πG_{1/2}` of `Δ − ¾` restricted to the degree geodesic. At a prime `p`
the corresponding rank-one space is the Bruhat–Tits tree `T_p` of `PGL₂(ℚ_p)`, `(p + 1)`-regular,
and the degrees with a common prime-to-`p` part form an apartment of it (a `p`-ladder `c·p^i`).

**Radial calculus on a regular tree** (`treeAdj`). On functions of the distance `d` to a vertex, the
adjacency operator of the `(q + 1)`-regular tree is `(Af)(0) = (q + 1)f(1)` and
`(Af)(d) = f(d − 1) + q f(d + 1)` for `d ≥ 1`. For `s > 0` put `λ_s = q^s + q^{1−s}` and
`G_s(d) = q^s/(q^{2s} − 1)·q^{−sd}` (`treeEigen`, `treeGreen`). Then

  `(λ_s − A)G_s = δ_0`   (`treeGreen_resolvent`):

`G_s` is the Green function of the tree at the spectral parameter `s`.

**The critical line is the Ramanujan edge** (`treeEigen_sub_two_sqrt`, `treeEigen_eq_iff`).
`λ_s − 2√q = (q^{s/2} − q^{(1−s)/2})² ≥ 0`, with equality exactly at `s = ½`: the eigenvalue `2√q`
is the edge of the tempered spectrum of the tree (the Ramanujan bound), and Weil's critical
parameter `s = ½` is the only one that reaches it.

**Weil's local kernel at `p`** (`weilPrimeKernel_mul_pow_eq_treeGreen`). For `n = m p^k`, `k ≥ 1`,

  `Λ(n/m)(n/m)^{−1/2} = log p · ((p − 1)/√p) · G_{1/2}(k)`,

the tree Green function at the Ramanujan point between two vertices of one apartment at distance
`k = v_p(n) − v_p(m)`; off the ladders the kernel vanishes (`weilPrimeKernel_ne_zero`). Restricted
to an apartment the tree Green function is positive definite (`sum_treeGreen_apartment_nonneg`), as
the `ℍ³` Green function is on the degree geodesic.

So every place of the surface of `Spec ℤ` carries the Green function of a rank-one hyperbolic space
at the critical parameter: `ℍ³` along the degree geodesic at `∞`, the tree `T_p` along its ladders at
`p`. **The adelic Green formula** (`weilDeltaKernel_mul_pow`, `weilDeltaKernel_of_offLadder`): on a
`p`-ladder,

  `W(m, mp^k) = 2cosh(k log p/2) − 2πG_{1/2}(k log p) − log p·((p − 1)/√p)·G^{T_p}_{1/2}(k)`,

and off the ladders `W(m, n) = (3/2)φ_{3/2}(d) − 2πG_{3/2}(d)`, `d = |log(n/m)|`: Weil's off-diagonal
kernel is the pole minus the local Green kernels of all places, the local form of an Arakelov
intersection pairing over all places.
-/

open Real

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory

open ArithmeticEffectivityTheory
open scoped ArithmeticFunction.vonMangoldt

/-- The adjacency operator of the `(q + 1)`-regular tree on radial functions. -/
def treeAdj (q : ℝ) (f : ℕ → ℝ) (d : ℕ) : ℝ :=
  if d = 0 then (q + 1) * f 1 else f (d - 1) + q * f (d + 1)

/-- The tree eigenvalue `λ_s = q^s + q^{1−s}` of the spectral parameter `s`. -/
def treeEigen (q s : ℝ) : ℝ := q ^ s + q ^ (1 - s)

/-- The tree Green function `G_s(d) = q^s/(q^{2s} − 1)·q^{−sd}`. -/
def treeGreen (q s : ℝ) (d : ℕ) : ℝ := q ^ s / (q ^ (2 * s) - 1) * (q ^ (-s)) ^ d

/-- **The tree Green function.** `(λ_s − A)G_s = δ_0` for `q > 1`, `s > 0`. -/
theorem treeGreen_resolvent {q s : ℝ} (hq : 1 < q) (hs : 0 < s) (d : ℕ) :
    treeEigen q s * treeGreen q s d - treeAdj q (treeGreen q s) d = if d = 0 then 1 else 0 := by
  have hq0 : 0 < q := by linarith
  unfold treeEigen treeGreen treeAdj
  set v := q ^ s with hv
  set u := q ^ (-s) with hu
  have hvu : v * u = 1 := by rw [hv, hu, ← Real.rpow_add hq0, add_neg_cancel, Real.rpow_zero]
  have h1s : q ^ (1 - s) = q * u := by
    rw [hu, sub_eq_add_neg, Real.rpow_add hq0, Real.rpow_one]
  have h2s : q ^ (2 * s) = v ^ 2 := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; ring_nf
  have hv1 : 1 < v := Real.one_lt_rpow hq hs
  have hv0 : v ≠ 0 := by linarith
  have hden : v ^ 2 - 1 ≠ 0 := by nlinarith
  have hu' : u = v⁻¹ := eq_inv_of_mul_eq_one_right hvu
  rw [h1s, h2s, hu']
  rcases d with _ | k
  · simp only [if_true, pow_zero, mul_one, pow_one]
    field_simp
    ring
  · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    have hvi : v * v⁻¹ = 1 := mul_inv_cancel₀ hv0
    linear_combination (v / (v ^ 2 - 1) * v⁻¹ ^ k) * hvi

/-- **The critical line is the Ramanujan edge.** `λ_s − 2√q = (q^{s/2} − q^{(1−s)/2})²`. -/
theorem treeEigen_sub_two_sqrt {q : ℝ} (hq : 0 < q) (s : ℝ) :
    treeEigen q s - 2 * Real.sqrt q = (q ^ (s / 2) - q ^ ((1 - s) / 2)) ^ 2 := by
  have e1 : q ^ s = (q ^ (s / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]; ring_nf
  have e2 : q ^ (1 - s) = (q ^ ((1 - s) / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]; ring_nf
  have e3 : Real.sqrt q = q ^ (s / 2) * q ^ ((1 - s) / 2) := by
    rw [← Real.rpow_add hq, Real.sqrt_eq_rpow]; ring_nf
  unfold treeEigen
  rw [e1, e2, e3]
  ring

theorem two_sqrt_le_treeEigen {q : ℝ} (hq : 0 < q) (s : ℝ) : 2 * Real.sqrt q ≤ treeEigen q s := by
  have := treeEigen_sub_two_sqrt hq s
  nlinarith [sq_nonneg (q ^ (s / 2) - q ^ ((1 - s) / 2))]

/-- The tree eigenvalue reaches the Ramanujan edge `2√q` exactly at `s = ½`. -/
theorem treeEigen_eq_iff {q : ℝ} (hq : 1 < q) (s : ℝ) :
    treeEigen q s = 2 * Real.sqrt q ↔ s = 1 / 2 := by
  have hq0 : 0 < q := by linarith
  rw [← sub_eq_zero, treeEigen_sub_two_sqrt hq0, sq_eq_zero_iff, sub_eq_zero]
  constructor
  · intro h
    have hinj : s / 2 = (1 - s) / 2 := by
      have hlog := congrArg Real.log h
      rw [Real.log_rpow hq0, Real.log_rpow hq0] at hlog
      have hl : Real.log q ≠ 0 := (Real.log_pos hq).ne'
      exact mul_right_cancel₀ hl hlog
    linarith
  · rintro rfl; norm_num

/-! ## Weil's local kernel -/

/-- **Weil's kernel at `p` is the tree Green function at the Ramanujan point.** For `k ≥ 1`,
`Λ(p^k)p^{−k/2} = log p · ((p − 1)/√p) · G_{1/2}(k)`. -/
theorem weilPrimeKernel_mul_pow_eq_treeGreen {p m k : ℕ} (hp : p.Prime) (hm : 0 < m) (hk : 1 ≤ k) :
    weilPrimeKernel m (m * p ^ k) =
      Real.log p * (((p : ℝ) - 1) / Real.sqrt p) * treeGreen p (1 / 2) k := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpk : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
  have hne : m ≠ m * p ^ k := by
    intro h
    have : m * 1 = m * p ^ k := by rw [mul_one]; exact h
    exact hpk.ne (Nat.eq_of_mul_eq_mul_left hm this)
  rw [weilPrimeKernel, if_pos ⟨dvd_mul_right m _, hne⟩, Nat.mul_div_cancel_left _ hm,
    ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  unfold treeGreen
  have hs : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp0).ne'
  have e1 : (p : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt p := (Real.sqrt_eq_rpow _).symm
  have e2 : (p : ℝ) ^ (2 * (1 / 2) : ℝ) = p := by norm_num
  have e3 : (p : ℝ) ^ (-(1 / 2) : ℝ) = (Real.sqrt p)⁻¹ := by
    rw [Real.rpow_neg hp0.le, e1]
  have e4 : Real.sqrt ((p ^ k : ℕ) : ℝ) = Real.sqrt p ^ k := by
    rw [show ((p ^ k : ℕ) : ℝ) = (Real.sqrt p ^ k) ^ 2 by
      push_cast; rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hp0.le]]
    exact Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) k)
  rw [e1, e2, e3, e4]
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  rw [one_div, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero k hs), mul_one]

/-- Weil's kernel vanishes off the ladders: a nonzero entry has a prime-power ratio. -/
theorem weilPrimeKernel_ne_zero {m n : ℕ} (h : weilPrimeKernel m n ≠ 0) :
    (m ∣ n ∧ IsPrimePow (n / m)) ∨ (n ∣ m ∧ IsPrimePow (m / n)) := by
  unfold weilPrimeKernel at h
  split_ifs at h with h1 h2
  · left
    refine ⟨h1.1, ?_⟩
    by_contra hpp
    exact h (by rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, zero_div])
  · right
    refine ⟨h2.1, ?_⟩
    by_contra hpp
    exact h (by rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, zero_div])
  · exact absurd rfl h

/-- **The tree Green function is positive definite on an apartment.** For `q > 1`, `s > 0` and
vertices `i ∈ ℤ` of one apartment, `Σ x_i x_j G_s(|i − j|) ≥ 0`. -/
theorem sum_treeGreen_apartment_nonneg {q s : ℝ} (hq : 1 < q) (hs : 0 < s) {ι : Type*}
    (S : Finset ι) (pos : ι → ℤ) (x : ι → ℝ) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S, x i * x j * treeGreen q s (pos i - pos j).natAbs := by
  have hq0 : 0 < q := by linarith
  have hv1 : 1 < q ^ s := Real.one_lt_rpow hq hs
  have hc : 0 ≤ q ^ s / (q ^ (2 * s) - 1) := by
    have h2 : q ^ (2 * s) = (q ^ s) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; ring_nf
    rw [h2]; exact div_nonneg (by linarith) (by nlinarith)
  have ha : 0 < s * Real.log q := mul_pos hs (Real.log_pos hq)
  have hexp : ∀ i j, (q ^ (-s)) ^ (pos i - pos j).natAbs =
      Real.exp (-(s * Real.log q) * |((pos i : ℝ)) - (pos j : ℝ)|) := by
    intro i j
    rw [Real.rpow_def_of_pos hq0, ← Real.exp_nat_mul]
    congr 1
    have : ((pos i - pos j).natAbs : ℝ) = |((pos i : ℝ)) - (pos j : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
    rw [this]; ring
  have hOU := SurfaceOfSpecZ.sum_mul_exp_neg_abs_nonneg S ha (fun i => (pos i : ℝ)) x
  have : ∑ i ∈ S, ∑ j ∈ S, x i * x j * treeGreen q s (pos i - pos j).natAbs =
      q ^ s / (q ^ (2 * s) - 1) *
        ∑ i ∈ S, ∑ j ∈ S, x i * x j * Real.exp (-(s * Real.log q) * |(pos i : ℝ) - (pos j : ℝ)|) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [treeGreen, hexp]; ring
  rw [this]
  exact mul_nonneg hc hOU

/-! ## The adelic Green formula -/

/-- **On a `p`-ladder**, Weil's kernel is the pole minus the `ℍ³` Green function of the distance
`k log p` minus `log p·((p − 1)/√p)` times the tree Green function of the distance `k`. -/
theorem weilDeltaKernel_mul_pow {p m k : ℕ} (hp : p.Prime) (hm : 0 < m) (hk : 1 ≤ k) :
    SurfaceOfSpecZ.weilDeltaKernel m (m * p ^ k) =
      2 * Real.cosh (k * Real.log p / 2) - 2 * π * SurfaceOfSpecZ.hyperbolicGreen (1 / 2) (k * Real.log p) -
        Real.log p * (((p : ℝ) - 1) / Real.sqrt p) * treeGreen p (1 / 2) k := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hd : |Real.log m - Real.log ((m * p ^ k : ℕ) : ℝ)| = k * Real.log p := by
    push_cast
    rw [Real.log_mul hm'.ne' (pow_ne_zero _ hp0.ne'), Real.log_pow]
    rw [show Real.log m - (Real.log m + k * Real.log p) = -(k * Real.log p) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp.one_lt.le)))]
  have hne : k * Real.log p ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (show k ≠ 0 by omega)) (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  rw [SurfaceOfSpecZ.weilDeltaKernel, hd, weilPrimeKernel_mul_pow_eq_treeGreen hp hm hk,
    ← SurfaceOfSpecZ.archProfile_eq_hyperbolicGreen hne]
  rw [show (Real.log m - Real.log ((m * p ^ k : ℕ) : ℝ)) / 2 =
      -(k * Real.log p) / 2 by
    push_cast
    rw [Real.log_mul hm'.ne' (pow_ne_zero _ hp0.ne'), Real.log_pow]; ring]
  rw [show -(k * Real.log p) / 2 = -(k * Real.log p / 2) by ring, Real.cosh_neg]
  rfl

/-- **Off the ladders** Weil's kernel is the archimedean compensation
`(3/2)φ_{3/2} − 2πG_{3/2}` of the hyperbolic distance. -/
theorem weilDeltaKernel_of_offLadder {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (hoff : weilPrimeKernel m n = 0) :
    SurfaceOfSpecZ.weilDeltaKernel m n =
      3 / 2 * sphericalFn (3 / 2) |Real.log m - Real.log n| -
        2 * π * SurfaceOfSpecZ.hyperbolicGreen (3 / 2) |Real.log m - Real.log n| := by
  rw [← archCompensation_eq_spherical hm hn hmn, SurfaceOfSpecZ.weilDeltaKernel_eq, hoff, sub_zero]

end GaloisForLFunctions.HyperbolicArakelovTheory

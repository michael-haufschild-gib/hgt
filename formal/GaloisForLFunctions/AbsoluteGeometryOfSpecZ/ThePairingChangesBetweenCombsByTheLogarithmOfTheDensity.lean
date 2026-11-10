import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePacketsOnTheDegreePointsCarryWeilsArchimedeanForm

/-!
# The pairing changes between combs by the logarithm of the density

A comb is a set of degree points with the masses of its cells in the logarithmic scale. The
comb of the multiples of `g` has the points `g·n` with the masses `1/n`; at the same degree point
the comb of all integers has the mass `1/(g·n)`.

* **The jets do not see the comb** (`levyKernel_mul_mul`, `multiplePairing_eq`): the unitary
  intersection number of `Γ_{gm}` and `Γ_{gn}` depends on `m/n` alone, so the pairing of a packet
  on the comb of the multiples of `g`, with the masses of that comb, is its pairing on the comb of
  all integers.
* **The counterterm does** (`tendsto_multiplePairing_sub_point_counterterm`,
  `tendsto_multiplePairing_sub_density_counterterm`): with the counterterm of the comb, the
  logarithm of its density `n` over `2π`, the limit is Weil's archimedean form; with the
  counterterm `log(g·n/2π)` that the degree point has in the comb of all integers, the limit is
  smaller by `log g·∫ f²`.

Together with the counterterm of the scale alone, which leaves the first moment of the mass
(`tendsto_degreePairing_sub_scale_counterterm`), this fixes the density on a logarithmic window:
it is the density of the comb at the point, and between two combs the pairing of a packet changes
by its mass times the logarithm of the ratio of the densities.
-/

open Finset Filter Topology MeasureTheory
open Zeta23

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The pairing of two degree points, with the masses of the comb of all integers, on the
multiples of `g`: the unitary number depends on the ratio alone. -/
theorem levyKernel_mul_mul {g : ℕ} (hg : 0 < g) (m n : ℕ) :
    levyKernel (g * m) (g * n) = levyKernel m n / (g : ℝ) ^ 2 := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hs : Real.sqrt ((g : ℝ) * m * ((g : ℝ) * n)) = g * Real.sqrt ((m : ℝ) * n) := by
    rw [show (g : ℝ) * m * ((g : ℝ) * n) = (g : ℝ) ^ 2 * ((m : ℝ) * n) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hg'.le]
  unfold levyKernel
  rw [jetKernel_mul_mul hg, Nat.cast_mul, Nat.cast_mul, hs]
  ring

/-- The pairing of the jets on the comb of the multiples of `g` at the scale `g·N`: the unitary
intersection numbers of the degree points `g·m`, `g·n` with the masses `1/m`, `1/n` of the cells
of the comb. -/
noncomputable def multiplePairing (g : ℕ) (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ (Ioc N (N + L * N)).erase n,
    degreeSample f (g * N) (g * m) * degreeSample f (g * N) (g * n) *
      ((g : ℝ) ^ 2 * levyKernel (g * m) (g * n))

theorem degreeSample_mul_mul {g : ℕ} (hg : 0 < g) (f : ℝ → ℝ) (N n : ℕ) :
    degreeSample f (g * N) (g * n) = degreeSample f N n := by
  have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  unfold degreeSample
  rw [Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hg']

/-- **The jets do not see the comb.** The pairing of a packet on the multiples of `g` is its
pairing on all degree points. -/
theorem multiplePairing_eq {g : ℕ} (hg : 0 < g) (f : ℝ → ℝ) (L N : ℕ) :
    multiplePairing g f L N = degreePairing f L N := by
  have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  unfold multiplePairing degreePairing
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [levyKernel_mul_mul hg, degreeSample_mul_mul hg, degreeSample_mul_mul hg]
  field_simp

/-- **With the density of the comb as counterterm the limit is Weil's archimedean form.** -/
theorem tendsto_multiplePairing_sub_density_counterterm {g : ℕ} (hg : 0 < g) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => multiplePairing g f (3 * K) N -
        ∑ n ∈ Ioc N (N + 3 * K * N),
          degreeSample f N n ^ 2 / n * Real.log ((n : ℝ) / (2 * Real.pi))) atTop
      (𝓝 (-(_root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1) -
          (_root_.RHTower.weilPoleTerm
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re))) := by
  refine (tendsto_degreeForm hf hfc hK hsupp).congr fun N => ?_
  rw [multiplePairing_eq hg, degreeForm]

/-- **With the counterterm of the degree point in the comb of all integers the limit is smaller
by `log g·∫ f²`.** -/
theorem tendsto_multiplePairing_sub_point_counterterm {g : ℕ} (hg : 0 < g) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => multiplePairing g f (3 * K) N -
        ∑ n ∈ Ioc N (N + 3 * K * N),
          degreeSample f N n ^ 2 / n * Real.log (((g * n : ℕ) : ℝ) / (2 * Real.pi))) atTop
      (𝓝 (-(_root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1) -
          (_root_.RHTower.weilPoleTerm
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re) -
        Real.log g * ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u ^ 2)) := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have h1 := tendsto_degreeForm hf hfc hK hsupp
  have hS : Tendsto (fun N : ℕ => ∑ n ∈ Ioc N (N + 3 * K * N), degreeSample f N n ^ 2 / n) atTop
      (𝓝 (∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u ^ 2)) :=
    tendsto_degreeSum (G := fun u => f u ^ 2) (hf.continuous.pow 2) (by omega : 1 ≤ 3 * K)
  refine (h1.sub (hS.const_mul (Real.log g))).congr fun N => ?_
  have hC : ∑ n ∈ Ioc N (N + 3 * K * N),
        degreeSample f N n ^ 2 / n * Real.log (((g * n : ℕ) : ℝ) / (2 * Real.pi)) =
      ∑ n ∈ Ioc N (N + 3 * K * N),
          degreeSample f N n ^ 2 / n * Real.log ((n : ℝ) / (2 * Real.pi)) +
        Real.log g * ∑ n ∈ Ioc N (N + 3 * K * N), degreeSample f N n ^ 2 / n := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : (0 : ℝ) < n := by
      have := (Finset.mem_Ioc.mp hn).1
      exact_mod_cast (by omega : 0 < n)
    rw [Nat.cast_mul, mul_div_assoc,
      Real.log_mul hg'.ne' (div_pos hn' (by positivity)).ne']
    ring
  rw [multiplePairing_eq hg, hC, degreeForm]
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

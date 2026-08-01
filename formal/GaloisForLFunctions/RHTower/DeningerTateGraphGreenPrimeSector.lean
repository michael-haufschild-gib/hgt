import GaloisForLFunctions.RHTower.DeningerPoissonHeatTopologyEscape
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.MeanInequalities

/-!
# Tate graph control of the Deninger prime sector

The positive-time Poisson forms lose normalized high-frequency modes.  The canonical repair on a
prime circle is the graph scale of the Tate-normalized generator.  Since every prime period satisfies
`log p ≥ log 2`, the unsmoothed spectral energy is uniformly dominated by the all-prime graph weight.
Graph-normalized high modes retain a nonzero limiting energy.

These are the scalar spectral estimates behind `DAC_TATE_GRAPH_GREEN_PRIME_SECTOR`.
-/

namespace RHTower

open Filter Topology

/-- Weighted graph norm-square coefficient at prime period `L` and Tate frequency `lam`. -/
def deningerTateGraphWeight (L lam : ℝ) : ℝ :=
  L ^ 2 * (1 + lam)

/-- A positive lower period bound uniformly controls unsmoothed energy by graph energy. -/
theorem deningerEnergy_le_tateGraphWeight {c L lam : ℝ} (hc : 0 < c) (hcL : c ≤ L)
    (hlam : 0 ≤ lam) :
    lam ≤ (c ^ 2)⁻¹ * deningerTateGraphWeight L lam := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hL : 0 ≤ L := hc.le.trans hcL
  have hsq : c ^ 2 ≤ L ^ 2 := (sq_le_sq₀ hc.le hL).2 hcL
  have hmul : c ^ 2 * lam ≤ L ^ 2 * (1 + lam) := by
    calc
      c ^ 2 * lam ≤ L ^ 2 * lam := mul_le_mul_of_nonneg_right hsq hlam
      _ ≤ L ^ 2 * (1 + lam) := by gcongr; linarith
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hc2).2
    (by simpa [deningerTateGraphWeight, mul_comm] using hmul)

/-- Every prime period is bounded below by `log 2`. -/
theorem deninger_log_two_le_prime_log (p : Nat.Primes) :
    Real.log 2 ≤ Real.log (p : ℝ) := by
  apply Real.log_le_log (by norm_num)
  exact_mod_cast p.prop.two_le

/-- Exact all-prime graph bound for one nonnegative Tate frequency. -/
theorem deningerPrimeEnergy_le_tateGraphWeight (p : Nat.Primes) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    lam ≤ ((Real.log 2) ^ 2)⁻¹ *
      deningerTateGraphWeight (Real.log (p : ℝ)) lam :=
  deningerEnergy_le_tateGraphWeight (Real.log_pos one_lt_two)
    (deninger_log_two_le_prime_log p) hlam

/-- A summable all-place graph majorant makes the unsmoothed energy summable. -/
theorem deningerTateGraphEnergy_summable {ι : Type*} {c : ℝ} (hc : 0 < c)
    (L lam mass : ι → ℝ) (hcL : ∀ i, c ≤ L i) (hlam : ∀ i, 0 ≤ lam i)
    (hmass : ∀ i, 0 ≤ mass i)
    (hgraph : Summable (fun i => deningerTateGraphWeight (L i) (lam i) * mass i)) :
    Summable (fun i => lam i * mass i) := by
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (hlam i) (hmass i))
    (fun i => ?_) (Summable.mul_left ((c ^ 2)⁻¹) hgraph)
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right
    (deningerEnergy_le_tateGraphWeight hc (hcL i) (hlam i)) (hmass i)

/-- Positive-time smoothing energy is pointwise dominated by unsmoothed energy. -/
theorem deningerPoissonHeatWeight_le_unsmoothed {r lam : ℝ} (hr : 0 ≤ r)
    (hlam : 0 ≤ lam) :
    0 ≤ deningerPoissonHeatWeight r lam ∧
      deningerPoissonHeatWeight r lam ≤ lam := by
  have harg : -(2 * r * lam) ≤ 0 := by nlinarith [mul_nonneg hr hlam]
  have hexpNonneg : 0 ≤ Real.exp (-(2 * r * lam)) := (Real.exp_pos _).le
  have hexpLe : Real.exp (-(2 * r * lam)) ≤ 1 := (Real.exp_le_one_iff).2 harg
  constructor
  · exact mul_nonneg hlam hexpNonneg
  · simpa [deningerPoissonHeatWeight] using mul_le_mul_of_nonneg_left hexpLe hlam

/-- Unsmoothed energy of a graph-normalized `k`th Tate circle mode at period `L`. -/
noncomputable def deningerTateGraphNormalizedModeEnergy (L : ℝ) (k : ℕ) : ℝ :=
  (2 * Real.pi * (k : ℝ)) /
    (L ^ 2 * (1 + 2 * Real.pi * (k : ℝ)))

/-- Squared scalar amplitude of a graph-normalized Tate circle mode. -/
noncomputable def deningerTateGraphNormalizedModeMass (L : ℝ) (k : ℕ) : ℝ :=
  (deningerTateGraphWeight L (deningerTateCircleModeRate k))⁻¹

/-- The chosen high-frequency modes have graph norm exactly one. -/
theorem deningerTateGraphNormalizedMode_graphWeight (L : ℝ) (hL : L ≠ 0) (k : ℕ) :
    deningerTateGraphWeight L (deningerTateCircleModeRate k) *
      deningerTateGraphNormalizedModeMass L k = 1 := by
  rw [deningerTateGraphNormalizedModeMass, mul_inv_cancel₀]
  unfold deningerTateGraphWeight
  have hLsq : L ^ 2 ≠ 0 := pow_ne_zero 2 hL
  have hrate : 0 ≤ deningerTateCircleModeRate k := by
    exact mul_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) (Nat.cast_nonneg k)
  exact mul_ne_zero hLsq (by linarith)

/-- Its unsmoothed scalar energy is exactly the displayed normalized energy. -/
theorem deningerTateGraphNormalizedMode_energy_eq (L : ℝ) (k : ℕ) :
    deningerTateCircleModeRate k * deningerTateGraphNormalizedModeMass L k =
      deningerTateGraphNormalizedModeEnergy L k := by
  simp only [deningerTateGraphNormalizedModeMass, deningerTateGraphWeight,
    deningerTateCircleModeRate, deningerTateGraphNormalizedModeEnergy]
  rw [div_eq_mul_inv]

/-- Graph-normalized high modes retain limiting energy `L⁻²`; they do not escape. -/
theorem deningerTateGraphNormalizedModeEnergy_tendsto (L : ℝ) (hL : L ≠ 0) :
    Tendsto (deningerTateGraphNormalizedModeEnergy L) atTop (𝓝 ((L ^ 2)⁻¹)) := by
  have hbase : Tendsto
      (fun k : ℕ => (k : ℝ) / ((k : ℝ) + (2 * Real.pi)⁻¹))
      atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop ((2 * Real.pi)⁻¹)
  have hmul : Tendsto
      (fun k : ℕ => (L ^ 2)⁻¹ * ((k : ℝ) / ((k : ℝ) + (2 * Real.pi)⁻¹)))
      atTop (𝓝 ((L ^ 2)⁻¹ * 1)) :=
    tendsto_const_nhds.mul hbase
  have htarget : (L ^ 2)⁻¹ * (1 : ℝ) = (L ^ 2)⁻¹ := by ring
  rw [htarget] at hmul
  refine hmul.congr' (Eventually.of_forall fun k => ?_)
  simp only [deningerTateGraphNormalizedModeEnergy]
  have hpi : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  field_simp
  ring

/-- At a genuine prime period, the retained high-frequency energy is strictly positive. -/
theorem deningerTateGraphNormalizedModeEnergy_prime_limit_pos (p : Nat.Primes) :
    0 < ((Real.log (p : ℝ)) ^ 2)⁻¹ := by
  have hp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.prop.one_lt)
  positivity

/-- Graph summability in each variable makes the unsmoothed cross-energy absolutely summable. -/
theorem deningerTateGraphCrossEnergy_summable
    {ι : Type*} {c : ℝ} (hc : 0 < c)
    (L lam massX massY : ι → ℝ)
    (hcL : ∀ i, c ≤ L i)
    (hlam : ∀ i, 0 ≤ lam i)
    (hmassX : ∀ i, 0 ≤ massX i)
    (hmassY : ∀ i, 0 ≤ massY i)
    (hgraphX : Summable (fun i =>
      deningerTateGraphWeight (L i) (lam i) * massX i))
    (hgraphY : Summable (fun i =>
      deningerTateGraphWeight (L i) (lam i) * massY i)) :
    Summable (fun i =>
      Real.sqrt (lam i * massX i) * Real.sqrt (lam i * massY i)) := by
  have henergyX : Summable (fun i => lam i * massX i) :=
    deningerTateGraphEnergy_summable hc L lam massX hcL hlam hmassX hgraphX
  have henergyY : Summable (fun i => lam i * massY i) :=
    deningerTateGraphEnergy_summable hc L lam massY hcL hlam hmassY hgraphY
  have hmajorant : Summable (fun i =>
      (lam i * massX i + lam i * massY i) / 2) := by
    simpa only [div_eq_mul_inv] using
      (henergyX.add henergyY).mul_right ((2 : ℝ)⁻¹)
  refine Summable.of_nonneg_of_le (fun i =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (fun i => ?_) hmajorant
  have hX : 0 ≤ lam i * massX i := mul_nonneg (hlam i) (hmassX i)
  have hY : 0 ≤ lam i * massY i := mul_nonneg (hlam i) (hmassY i)
  have hsX := Real.sq_sqrt hX
  have hsY := Real.sq_sqrt hY
  nlinarith [sq_nonneg (Real.sqrt (lam i * massX i) -
    Real.sqrt (lam i * massY i))]

/-- Cauchy--Schwarz bound for a summable all-place cross-energy. -/
theorem deningerTateGraphCrossEnergy_tsum_le
    {ι : Type*}
    (energyX energyY : ι → ℝ)
    (hX : ∀ i, 0 ≤ energyX i)
    (hY : ∀ i, 0 ≤ energyY i)
    (hsumX : Summable energyX)
    (hsumY : Summable energyY) :
    ∑' i, Real.sqrt (energyX i) * Real.sqrt (energyY i) ≤
      Real.sqrt (∑' i, energyX i) * Real.sqrt (∑' i, energyY i) := by
  have hsquareX :
      Summable (fun i => Real.sqrt (energyX i) ^ (2 : ℝ)) := by
    simpa [Real.rpow_two, Real.sq_sqrt (hX _)] using hsumX
  have hsquareY :
      Summable (fun i => Real.sqrt (energyY i) ^ (2 : ℝ)) := by
    simpa [Real.rpow_two, Real.sq_sqrt (hY _)] using hsumY
  have hholder :=
    Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
      (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
      (fun i => Real.sqrt_nonneg (energyX i))
      (fun i => Real.sqrt_nonneg (energyY i))
      hsquareX hsquareY
  have hh := hholder.2
  simp only [Real.rpow_two, Real.sq_sqrt (hX _),
    Real.sq_sqrt (hY _)] at hh
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  exact hh

/-- The all-place unsmoothed cross-energy is bounded by the two weighted graph energies. -/
theorem deningerTateGraphCrossEnergy_tsum_le_graph
    {ι : Type*} {c : ℝ} (hc : 0 < c)
    (L lam massX massY : ι → ℝ)
    (hcL : ∀ i, c ≤ L i)
    (hlam : ∀ i, 0 ≤ lam i)
    (hmassX : ∀ i, 0 ≤ massX i)
    (hmassY : ∀ i, 0 ≤ massY i)
    (hgraphX : Summable (fun i =>
      deningerTateGraphWeight (L i) (lam i) * massX i))
    (hgraphY : Summable (fun i =>
      deningerTateGraphWeight (L i) (lam i) * massY i)) :
    ∑' i, Real.sqrt (lam i * massX i) * Real.sqrt (lam i * massY i) ≤
      Real.sqrt (∑' i, (c ^ 2)⁻¹ *
        deningerTateGraphWeight (L i) (lam i) * massX i) *
      Real.sqrt (∑' i, (c ^ 2)⁻¹ *
        deningerTateGraphWeight (L i) (lam i) * massY i) := by
  have henergyX : Summable (fun i => lam i * massX i) :=
    deningerTateGraphEnergy_summable hc L lam massX hcL hlam hmassX hgraphX
  have henergyY : Summable (fun i => lam i * massY i) :=
    deningerTateGraphEnergy_summable hc L lam massY hcL hlam hmassY hgraphY
  have hmajorX : Summable (fun i => (c ^ 2)⁻¹ *
      deningerTateGraphWeight (L i) (lam i) * massX i) := by
    simpa only [mul_assoc] using hgraphX.mul_left ((c ^ 2)⁻¹)
  have hmajorY : Summable (fun i => (c ^ 2)⁻¹ *
      deningerTateGraphWeight (L i) (lam i) * massY i) := by
    simpa only [mul_assoc] using hgraphY.mul_left ((c ^ 2)⁻¹)
  have hsumX :
      (∑' i, lam i * massX i) ≤
        ∑' i, (c ^ 2)⁻¹ * deningerTateGraphWeight (L i) (lam i) * massX i :=
    henergyX.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_right
      (deningerEnergy_le_tateGraphWeight hc (hcL i) (hlam i)) (hmassX i)) hmajorX
  have hsumY :
      (∑' i, lam i * massY i) ≤
        ∑' i, (c ^ 2)⁻¹ * deningerTateGraphWeight (L i) (lam i) * massY i :=
    henergyY.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_right
      (deningerEnergy_le_tateGraphWeight hc (hcL i) (hlam i)) (hmassY i)) hmajorY
  refine (deningerTateGraphCrossEnergy_tsum_le
    (fun i => lam i * massX i) (fun i => lam i * massY i)
    (fun i => mul_nonneg (hlam i) (hmassX i))
    (fun i => mul_nonneg (hlam i) (hmassY i)) henergyX henergyY).trans ?_
  exact mul_le_mul (Real.sqrt_le_sqrt hsumX) (Real.sqrt_le_sqrt hsumY)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end RHTower

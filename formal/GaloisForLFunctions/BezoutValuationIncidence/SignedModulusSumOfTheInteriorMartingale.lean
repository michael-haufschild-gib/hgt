import GaloisForLFunctions.BezoutValuationIncidence.AllDampingVinogradovKorobovBandAndInteriorGrowth
import GaloisForLFunctions.BezoutValuationIncidence.BirthDelayedInteriorJumpCenteringAndUniformPairBounds
import GaloisForLFunctions.BezoutValuationIncidence.NaturalCutoffMultiDepthCofactorAndConditionalTailBridge
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ReceiverRowParsevalSpectrumAndHorizonUniformVariance

/-!
# The Signed Modulus Sum of the Interior Martingale and Sub-Half-Damping Contraction Laws

Along a predecessor jump progression `n = d − 1 + d k` (`d ≥ 1`), each two-endpoint-deleted
interior sawtooth atom `interiorSawtoothAtom e n` (`e ≥ 1`) has exact reduced-orbit mean
`interiorJumpOrbitMean d e = 0` when `gcd(d, e) = 1`, and `(e − gcd(d, e)) / (2 e²)` when
`gcd(d, e) > 1`. In `InteriorJumpOrbitCenteringAndCompensatedBounds` and
`BirthDelayedInteriorJumpCenteringAndUniformPairBounds`, the modulus sum over `e ∈ [1, N]` was
bounded after taking `|c(e)|` term by term, leaving open the evaluation of the signed sum over
moduli `e` and its effect on the horizon-free interior martingale.

This module resolves the signed modulus sum at both finite cutoff `N` and infinite horizon `N → ∞`,
and establishes the resulting cutoff-free progression and sub-half-damping laws for the Bézout
interior martingale:

1. **Exact Divisor Decomposition of `interiorJumpOrbitMean` into the BVI Modal Weights `μ(u)` and
   `φ(u) − μ(u)` (`interiorJumpOrbitMean_eq_sum_gcd_divisors`,
   `interiorJumpOrbitMean_eq_sum_divisors`,
   `sum_Icc_mul_interiorJumpOrbitMean_eq_selbergMultiplesCoord`)**:
   For every `g ≥ 1`, `∑_{u ∣ g, u > 1} μ(u) = −1_{g > 1}` and
   `∑_{u ∣ g, u > 1} (φ(u) − μ(u)) = g · 1_{g > 1}`. Applied to `g = gcd(d, e)`, this decomposes
   `interiorJumpOrbitMean d e` into common divisors `u ∣ gcd(d, e)` (`u > 1`):
   $$\operatorname{interiorJumpOrbitMean}(d, e)
     = -\frac{1}{2} \sum_{\substack{u \mid d \\ u > 1}} \mathbf{1}_{u \mid e}
       \left(\frac{\mu(u)}{e} + \frac{\varphi(u) - \mu(u)}{e^2}\right).$$
   Consequently, for **every** cutoff `N : ℕ`, **every** divisor row `c : ℕ → ℝ`, and **every**
   jump modulus `d ≥ 1`, the `N`-term signed sum over interior moduli `e ∈ [1, N]` collapses into a
   finite sum over the proper divisors `u ∣ d` (`u > 1`) in Selberg multiples coordinates:
   $$\sum_{e=1}^N c(e)\,\operatorname{interiorJumpOrbitMean}(d, e)
     = -\frac{1}{2} \sum_{\substack{u \mid d \\ u > 1}}
       \Bigl(\mu(u)\,Y_{N,c}(u) + \bigl(\varphi(u) - \mu(u)\bigr)\,Y_{N, c/e}(u)\Bigr).$$
   In particular, if the Selberg coordinates of `c` and `c/e` vanish on the proper divisors of `d`,
   the signed jump-orbit drift vanishes identically (`sum_Icc_mul_interiorJumpOrbitMean_eq_zero_of_selberg_disjoint`).

2. **Horizon-Free Closed Form, Radical Invariance, and Double-Modulus Summability for the Damped
   Möbius Row (`pmSignedInteriorJumpOrbitMean_eq_sum_divisors`,
   `pmSignedInteriorJumpOrbitMean_prime`,
   `pmSignedInteriorJumpOrbitMean_eq_of_primeFactors_eq`,
   `summable_pmPowerDampedRealWeight_div_mul_pmSignedInteriorJumpOrbitMean`)**:
   For every `ε > 0` and `d ≥ 1`, the infinite signed series
   $$\mathcal{M}_\varepsilon(d) := \sum_{e=1}^\infty c_\varepsilon(e)\,\operatorname{interiorJumpOrbitMean}(d, e)$$
   is absolutely summable and evaluates in closed form via the Route PM Ramanujan weights
   `Y_ε(u) = pmRealRamanujanWeight ε u` and `Y_{1+ε}(u) = pmRealRamanujanWeight (1 + ε) u`:
   $$\mathcal{M}_\varepsilon(d)
     = -\frac{1}{2} \sum_{\substack{u \mid d \\ u > 1}}
       \Bigl(\mu(u)\,Y_\varepsilon(u) + \bigl(\varphi(u) - \mu(u)\bigr)\,Y_{1+\varepsilon}(u)\Bigr).$$
   At any prime jump modulus `d = p`,
   $$\mathcal{M}_\varepsilon(p)
     = -\frac{1}{2}\left(\frac{\alpha_\varepsilon}{p^{1+\varepsilon} - 1}
       - \frac{p\,\alpha_{1+\varepsilon}}{p^{2+\varepsilon} - 1}\right).$$
   Because `Y_ε(u)` and `Y_{1+ε}(u)` vanish outside squarefree `u`, `\mathcal{M}_ε(d)` depends on
   `d` **only through its radical** (`d.primeFactors`), so `\mathcal{M}_ε(d^k) = \mathcal{M}_ε(d)`
   for all `k ≥ 1`, and the double-modulus drift series
   `∑_{d ≥ 1} (c_ε(d) / d) \mathcal{M}_ε(d)` is absolutely summable for every `ε > 0`.

3. **Cutoff-Free Signed Progression Bounds and Sub-Half-Damping Laws for the Interior Martingale
   (`exists_abs_pmBezoutInteriorPrefix_jump_compensated_le_vk_all_pos`,
   `eventually_abs_compensated_interiorMartingale_le_growth_of_pos`,
   `eventually_abs_pmBezoutInteriorMartingaleSum_le_growth_of_pos`,
   `eventually_abs_compensated_interiorMartingale_le_mul_periodEnergy_of_pos`)**:
   Keeping the signed sum over `e` in `pmBezoutInteriorPrefix ε n` removes the external cutoff
   `N = (d + 2) L` along every jump progression `n = d − 1 + d k` and yields for every
   `0 < ε < 1/2`:
   - `|2 M_T^{int}(ε) + 2 c^{int}(ε) H_T^{comp}| ≤ C_ε T^{1−2ε} exp(−κ σ(T)/270)`,
   - `|M_T^{int}(ε)| ≤ C'_ε T^{1−2ε} exp(−κ σ(T)/270)` (improving the sign-blind jump bound by a
     full factor of `T^{−ε}`),
   - `|2 M_N^{int}(ε) + 2 c^{int}(ε) H_N^{comp}| ≤ C''_ε exp(−κ σ(N)/270) E_prim(N)`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin
open GaloisForLFunctions.TransHorizonIncidenceMechanics RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Divisor Decomposition of `interiorJumpOrbitMean` & Selberg Coordinate Collapse -/

/-- For every `g ≥ 1`, the sum of `moebiusReal u` over the proper divisors `u ∣ g` (`1 < u`) is `0`
if `g = 1` and `-1` if `g > 1`. -/
theorem sum_divisors_filter_gt_one_moebiusReal {g : ℕ} (hg : 1 ≤ g) :
    ∑ u ∈ g.divisors.filter (fun u => 1 < u), moebiusReal u =
      if g = 1 then 0 else -1 := by
  have h1_mem : 1 ∈ g.divisors := Nat.one_mem_divisors.mpr (by omega)
  have hpart : g.divisors = insert 1 (g.divisors.filter (fun u => 1 < u)) := by
    ext u
    simp only [mem_insert, mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hug, hg0⟩
      have hu_pos : 0 < u := Nat.pos_of_dvd_of_pos hug hg
      by_cases hu1 : u = 1
      · exact Or.inl hu1
      · exact Or.inr ⟨⟨hug, hg0⟩, by omega⟩
    · rintro (rfl | ⟨⟨hug, hg0⟩, _⟩)
      · exact ⟨one_dvd g, by omega⟩
      · exact ⟨hug, hg0⟩
  have hnot : 1 ∉ g.divisors.filter (fun u => 1 < u) := by simp
  have htot := sum_divisors_moebiusReal_eq_ite_one hg
  rw [hpart, sum_insert hnot] at htot
  have hmu1 : moebiusReal 1 = 1 := by unfold moebiusReal; simp
  rw [hmu1] at htot
  by_cases hg1 : g = 1
  · simp [hg1] at htot ⊢
    linarith
  · simp [hg1] at htot ⊢
    linarith

/-- For every `g ≥ 1`, the sum of the Bézout–Dirichlet modal weight `(Nat.totient u : ℝ) - moebiusReal u`
over `u ∣ g` (`1 < u`) is `0` if `g = 1` and `(g : ℝ)` if `g > 1`. -/
theorem sum_divisors_filter_gt_one_totient_sub_moebiusReal {g : ℕ} (hg : 1 ≤ g) :
    ∑ u ∈ g.divisors.filter (fun u => 1 < u), ((Nat.totient u : ℝ) - moebiusReal u) =
      if g = 1 then 0 else (g : ℝ) := by
  have hpart : g.divisors = insert 1 (g.divisors.filter (fun u => 1 < u)) := by
    ext u
    simp only [mem_insert, mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hug, hg0⟩
      have hu_pos : 0 < u := Nat.pos_of_dvd_of_pos hug hg
      by_cases hu1 : u = 1
      · exact Or.inl hu1
      · exact Or.inr ⟨⟨hug, hg0⟩, by omega⟩
    · rintro (rfl | ⟨⟨hug, hg0⟩, _⟩)
      · exact ⟨one_dvd g, by omega⟩
      · exact ⟨hug, hg0⟩
  have hnot : 1 ∉ g.divisors.filter (fun u => 1 < u) := by simp
  have htot_nat : (∑ u ∈ g.divisors, (Nat.totient u : ℝ)) = (g : ℝ) := by
    exact_mod_cast Nat.sum_totient g
  have hmu := sum_divisors_moebiusReal_eq_ite_one hg
  have hfull :
      ∑ u ∈ g.divisors, ((Nat.totient u : ℝ) - moebiusReal u) =
        (g : ℝ) - if g = 1 then 1 else 0 := by
    rw [sum_sub_distrib, htot_nat, hmu]
  rw [hpart, sum_insert hnot] at hfull
  have h1 : (Nat.totient 1 : ℝ) - moebiusReal 1 = 0 := by
    unfold moebiusReal; simp
  rw [h1, zero_add] at hfull
  rw [hfull]
  by_cases hg1 : g = 1
  · subst hg1; norm_num
  · simp [hg1]

/-- **Exact GCD-Divisor Decomposition of `interiorJumpOrbitMean`
(`interiorJumpOrbitMean_eq_sum_gcd_divisors`):**
For every `d ≥ 1` and `e ≥ 1`, `interiorJumpOrbitMean d e` decomposes over the common divisors
`u ∣ gcd(d, e)` with `u > 1` into the Bézout coprime modal weight `moebiusReal u / e` and the
Bézout–Dirichlet reserve weight `((Nat.totient u : ℝ) - moebiusReal u) / e²`. -/
theorem interiorJumpOrbitMean_eq_sum_gcd_divisors {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) :
    interiorJumpOrbitMean d e =
      -(1 / 2 : ℝ) *
        ∑ u ∈ (Nat.gcd d e).divisors.filter (fun u => 1 < u),
          (moebiusReal u / (e : ℝ) +
            ((Nat.totient u : ℝ) - moebiusReal u) / (e : ℝ) ^ 2) := by
  set g := Nat.gcd d e
  have hg : 1 ≤ g := Nat.gcd_pos_of_pos_left e hd
  have heR : (e : ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  rw [sum_add_distrib, ← sum_div, ← sum_div,
    sum_divisors_filter_gt_one_moebiusReal hg,
    sum_divisors_filter_gt_one_totient_sub_moebiusReal hg]
  unfold interiorJumpOrbitMean
  change (if g = 1 then 0 else ((e : ℝ) - (g : ℝ)) / (2 * (e : ℝ) ^ 2)) = _
  split_ifs with hg1
  · ring
  · field_simp [heR]
    ring

/-- **Divisor-Indicator Expansion of `interiorJumpOrbitMean` (`interiorJumpOrbitMean_eq_sum_divisors`):**
For every `d ≥ 1` and `e ≥ 1`, `interiorJumpOrbitMean d e` is a sum over the proper divisors
`u ∣ d` (`1 < u`) gated by the divisibility indicator `u ∣ e`. -/
theorem interiorJumpOrbitMean_eq_sum_divisors {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) :
    interiorJumpOrbitMean d e =
      -(1 / 2 : ℝ) *
        ∑ u ∈ d.divisors.filter (fun u => 1 < u),
          if u ∣ e then
            moebiusReal u / (e : ℝ) +
              ((Nat.totient u : ℝ) - moebiusReal u) / (e : ℝ) ^ 2
          else 0 := by
  rw [interiorJumpOrbitMean_eq_sum_gcd_divisors hd he, ← sum_filter]
  congr 1
  refine sum_congr ?_ (fun _ _ => rfl)
  ext u
  simp only [mem_filter, Nat.mem_divisors]
  have hg0 : Nat.gcd d e ≠ 0 := (Nat.gcd_pos_of_pos_left e hd).ne'
  have hd0 : d ≠ 0 := by omega
  constructor
  · rintro ⟨⟨hug, _⟩, hu1⟩
    exact ⟨⟨⟨hug.trans (Nat.gcd_dvd_left d e), hd0⟩, hu1⟩, hug.trans (Nat.gcd_dvd_right d e)⟩
  · rintro ⟨⟨⟨hud, _⟩, hu1⟩, hue⟩
    exact ⟨⟨Nat.dvd_gcd hud hue, hg0⟩, hu1⟩

/-- **Exact Collapse of the Signed Interior Modulus Sum into Selberg Coordinates
(`sum_Icc_mul_interiorJumpOrbitMean_eq_selbergMultiplesCoord`):**
For **every** cutoff `N : ℕ`, **every** divisor row `c : ℕ → ℝ`, and **every** jump modulus
`d ≥ 1`, the signed sum of `c e * interiorJumpOrbitMean d e` over `1 ≤ e ≤ N` collapses into a
finite sum over the proper divisors `u ∣ d` (`u > 1`) of `selbergMultiplesCoord N c u` and
`selbergMultiplesCoord N (fun e => c e / e) u`. -/
theorem sum_Icc_mul_interiorJumpOrbitMean_eq_selbergMultiplesCoord
    (N : ℕ) (c : ℕ → ℝ) {d : ℕ} (hd : 1 ≤ d) :
    (∑ e ∈ Icc 1 N, c e * interiorJumpOrbitMean d e) =
      -(1 / 2 : ℝ) *
        ∑ u ∈ d.divisors.filter (fun u => 1 < u),
          (moebiusReal u * selbergMultiplesCoord N c u +
            ((Nat.totient u : ℝ) - moebiusReal u) *
              selbergMultiplesCoord N (fun e => c e / (e : ℝ)) u) := by
  have hterm : ∀ e ∈ Icc 1 N,
      c e * interiorJumpOrbitMean d e =
        -(1 / 2 : ℝ) *
          ∑ u ∈ d.divisors.filter (fun u => 1 < u),
            if u ∣ e then
              moebiusReal u * (c e / (e : ℝ)) +
                ((Nat.totient u : ℝ) - moebiusReal u) * ((c e / (e : ℝ)) / (e : ℝ))
            else 0 := by
    intro e he
    have he1 : 1 ≤ e := (mem_Icc.mp he).1
    rw [interiorJumpOrbitMean_eq_sum_divisors hd he1, ← mul_assoc, mul_comm (c e) (-(1 / 2 : ℝ)),
      mul_assoc, mul_sum]
    congr 1
    refine sum_congr rfl fun u _ => ?_
    split_ifs with hue
    · ring
    · ring
  rw [sum_congr rfl hterm, ← mul_sum, sum_comm]
  congr 1
  refine sum_congr rfl fun u _ => ?_
  unfold selbergMultiplesCoord
  rw [sum_filter, sum_filter, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun e _ => ?_
  split_ifs with hue <;> ring

/-- **Prime Jump-Modulus Evaluation (`sum_Icc_mul_interiorJumpOrbitMean_prime`):**
At any prime jump modulus `p`, the signed interior modulus sum over `e ∈ [1, N]` reduces to the
single mode `u = p`:
`∑_{e=1}^N c(e) interiorJumpOrbitMean(p, e) = (1/2) Y_{N,c}(p) − (p/2) Y_{N,c/e}(p)`. -/
theorem sum_Icc_mul_interiorJumpOrbitMean_prime
    (N : ℕ) (c : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    (∑ e ∈ Icc 1 N, c e * interiorJumpOrbitMean p e) =
      (1 / 2 : ℝ) * selbergMultiplesCoord N c p -
        ((p : ℝ) / 2) * selbergMultiplesCoord N (fun e => c e / (e : ℝ)) p := by
  rw [sum_Icc_mul_interiorJumpOrbitMean_eq_selbergMultiplesCoord N c hp.one_lt.le]
  have hdiv : p.divisors.filter (fun u => 1 < u) = {p} := by
    ext u
    simp only [mem_filter, hp.divisors, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hu1⟩
      · omega
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, hp.one_lt⟩
  have hmup : moebiusReal p = -1 := by
    unfold moebiusReal
    rw [ArithmeticFunction.moebius_apply_prime hp]
    norm_num
  rw [hdiv, sum_singleton, totient_sub_moebiusReal_prime hp, hmup]
  ring

/-- **Exact Vanishing Under Coprime Selberg Support
(`sum_Icc_mul_interiorJumpOrbitMean_eq_zero_of_selberg_disjoint`):**
If `selbergMultiplesCoord N c u = 0` and `selbergMultiplesCoord N (fun e => c e / e) u = 0` for
every proper divisor `u ∣ d` (`1 < u`), then the signed interior jump-orbit drift along
`n ≡ −1 (mod d)` vanishes identically. -/
theorem sum_Icc_mul_interiorJumpOrbitMean_eq_zero_of_selberg_disjoint
    (N : ℕ) (c : ℕ → ℝ) {d : ℕ} (hd : 1 ≤ d)
    (hc : ∀ u : ℕ, u ∣ d → 1 < u → selbergMultiplesCoord N c u = 0)
    (hce : ∀ u : ℕ, u ∣ d → 1 < u → selbergMultiplesCoord N (fun e => c e / (e : ℝ)) u = 0) :
    (∑ e ∈ Icc 1 N, c e * interiorJumpOrbitMean d e) = 0 := by
  rw [sum_Icc_mul_interiorJumpOrbitMean_eq_selbergMultiplesCoord N c hd]
  suffices h0 :
      (∑ u ∈ d.divisors.filter (fun u => 1 < u),
        (moebiusReal u * selbergMultiplesCoord N c u +
          ((Nat.totient u : ℝ) - moebiusReal u) *
            selbergMultiplesCoord N (fun e => c e / (e : ℝ)) u)) = 0 by
    rw [h0, mul_zero]
  refine sum_eq_zero fun u hu => ?_
  simp only [mem_filter, Nat.mem_divisors] at hu
  rw [hc u hu.1.1 hu.2, hce u hu.1.1 hu.2]
  ring

/-- **Selberg-Coordinate Form of the Finite-Cutoff Interior Jump Centering Bound
(`abs_bezoutInteriorSawtoothSum_centered_jump_compensated_selberg_le`):**
For every `N T L : ℕ`, weight `c : ℕ → ℝ`, and `d : ℕ+`, centering `bezoutInteriorSawtoothSum N c`
along the jump progression `(d : ℕ) − 1 + d * k` by its Selberg-coordinate divisor sum is bounded
uniformly in `T` and `L`. -/
theorem abs_bezoutInteriorSawtoothSum_centered_jump_compensated_selberg_le
    (N T L : ℕ) (c : ℕ → ℝ) (d : ℕ+) :
    |∑ k ∈ range L, interiorJumpCompensatedWeight d T k *
      (bezoutInteriorSawtoothSum N c ((d : ℕ) - 1 + d * k) +
        (1 / 2 : ℝ) *
          ∑ u ∈ (d : ℕ).divisors.filter (fun u => 1 < u),
            (moebiusReal u * selbergMultiplesCoord N c u +
              ((Nat.totient u : ℝ) - moebiusReal u) *
                selbergMultiplesCoord N (fun e => c e / (e : ℝ)) u))| ≤
      ∑ e ∈ Icc 1 N, |c e| * (((e / Nat.gcd d e : ℕ) : ℝ) / (d : ℝ)) := by
  have h := abs_bezoutInteriorSawtoothSum_centered_jump_compensated_le N T L c d
  rw [sum_Icc_mul_interiorJumpOrbitMean_eq_selbergMultiplesCoord N c d.pos] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  refine sum_congr rfl fun k _ => ?_
  ring

/-! ## §2. Horizon-Free Closed Form, Radical Invariance & Double-Modulus Summability (`N → ∞`) -/

/-- The horizon-free signed interior jump-orbit drift for the power-damped Möbius row at damping
`ε` and jump modulus `d`:
`pmSignedInteriorJumpOrbitMean ε d = ∑'_{e : ℕ} pmPowerDampedRealWeight ε e * interiorJumpOrbitMean d e`. -/
def pmSignedInteriorJumpOrbitMean (ε : ℝ) (d : ℕ) : ℝ :=
  ∑' e : ℕ, pmPowerDampedRealWeight ε e * interiorJumpOrbitMean d e

/-- Pointwise bound: for every `ε : ℝ`, `d ≥ 1`, and `e : ℕ`,
`|pmPowerDampedRealWeight ε e * interiorJumpOrbitMean d e| ≤ (1 / 2) * (e : ℝ) ^ (-1 - ε)`. -/
theorem abs_pmPowerDampedRealWeight_mul_interiorJumpOrbitMean_le
    (ε : ℝ) {d : ℕ} (hd : 1 ≤ d) (e : ℕ) :
    |pmPowerDampedRealWeight ε e * interiorJumpOrbitMean d e| ≤
      (1 / 2 : ℝ) * (e : ℝ) ^ (-1 - ε) := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · have hz : pmPowerDampedRealWeight ε 0 = 0 := by
      unfold pmPowerDampedRealWeight moebiusReal; simp
    rw [hz, zero_mul, abs_zero]
    positivity
  · have he0 : (0 : ℝ) < e := by exact_mod_cast he
    have hmean0 : 0 ≤ interiorJumpOrbitMean d e :=
      interiorJumpOrbitMean_nonneg ⟨d, hd⟩ ⟨e, he⟩
    have hmean : interiorJumpOrbitMean d e ≤ 1 / (2 * (e : ℝ)) :=
      interiorJumpOrbitMean_le ⟨d, hd⟩ ⟨e, he⟩
    have hc : |pmPowerDampedRealWeight ε e| ≤ (e : ℝ) ^ (-ε) := by
      unfold pmPowerDampedRealWeight
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg he0.le _)]
      have hmu : |moebiusReal e| ≤ 1 := by
        unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      exact mul_le_of_le_one_left (Real.rpow_nonneg he0.le _) hmu
    rw [abs_mul, abs_of_nonneg hmean0]
    calc |pmPowerDampedRealWeight ε e| * interiorJumpOrbitMean d e
        ≤ (e : ℝ) ^ (-ε) * (1 / (2 * (e : ℝ))) :=
          mul_le_mul hc hmean hmean0 (Real.rpow_nonneg he0.le _)
      _ = (1 / 2 : ℝ) * ((e : ℝ) ^ (-ε) / (e : ℝ)) := by ring
      _ = (1 / 2 : ℝ) * (e : ℝ) ^ (-1 - ε) := by
          rw [← Real.rpow_sub_one he0.ne', show -ε - 1 = -1 - ε by ring]

/-- **Summability of the Signed Interior Modulus Series
(`summable_pmPowerDampedRealWeight_mul_interiorJumpOrbitMean`):**
For every `ε > 0` and `d ≥ 1`, the series `e ↦ pmPowerDampedRealWeight ε e * interiorJumpOrbitMean d e`
is absolutely summable. -/
theorem summable_pmPowerDampedRealWeight_mul_interiorJumpOrbitMean
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 1 ≤ d) :
    Summable (fun e : ℕ => pmPowerDampedRealWeight ε e * interiorJumpOrbitMean d e) := by
  refine Summable.of_norm_bounded
    ((Real.summable_nat_rpow.mpr (by linarith : -1 - ε < -1)).mul_left (1 / 2 : ℝ))
    fun e => ?_
  rw [Real.norm_eq_abs]
  exact abs_pmPowerDampedRealWeight_mul_interiorJumpOrbitMean_le ε hd e

/-- As `N → ∞`, the finite signed interior modulus sum converges to `pmSignedInteriorJumpOrbitMean ε d`. -/
theorem tendsto_sum_Icc_pmPowerDamped_interiorJumpOrbitMean
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 1 ≤ d) :
    Tendsto
      (fun N : ℕ => ∑ e ∈ Icc 1 N, pmPowerDampedRealWeight ε e * interiorJumpOrbitMean d e)
      atTop (𝓝 (pmSignedInteriorJumpOrbitMean ε d)) := by
  have hs := (summable_pmPowerDampedRealWeight_mul_interiorJumpOrbitMean hε hd).hasSum
  have hcomp := hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine hcomp.congr fun N => ?_
  simp only [Function.comp_apply]
  have hr : range (N + 1) = insert 0 (Icc 1 N) := by
    ext e; simp only [mem_range, mem_insert, mem_Icc]; omega
  have hz : pmPowerDampedRealWeight ε 0 = 0 := by
    unfold pmPowerDampedRealWeight moebiusReal; simp
  rw [hr, sum_insert (by simp), hz, zero_mul, zero_add]

/-- **Exact Horizon-Free Closed Form of the Signed Interior Modulus Sum
(`pmSignedInteriorJumpOrbitMean_eq_sum_divisors`):**
For every `ε > 0` and `d ≥ 1`, the infinite signed sum `pmSignedInteriorJumpOrbitMean ε d`
evaluates in closed form to the finite divisor sum over `u ∣ d` (`1 < u`) of the Route PM Ramanujan
weights `pmRealRamanujanWeight ε u` and `pmRealRamanujanWeight (1 + ε) u`:
$$\mathcal{M}_\varepsilon(d)
  = -\frac{1}{2} \sum_{\substack{u \mid d \\ u > 1}}
    \Bigl(\mu(u)\,Y_\varepsilon(u) + \bigl(\varphi(u) - \mu(u)\bigr)\,Y_{1+\varepsilon}(u)\Bigr).$$ -/
theorem pmSignedInteriorJumpOrbitMean_eq_sum_divisors
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 1 ≤ d) :
    pmSignedInteriorJumpOrbitMean ε d =
      -(1 / 2 : ℝ) *
        ∑ u ∈ d.divisors.filter (fun u => 1 < u),
          (moebiusReal u * pmRealRamanujanWeight ε u +
            ((Nat.totient u : ℝ) - moebiusReal u) * pmRealRamanujanWeight (1 + ε) u) := by
  have h1 := tendsto_sum_Icc_pmPowerDamped_interiorJumpOrbitMean hε hd
  have hfun :
      (fun e : ℕ => pmPowerDampedRealWeight ε e / (e : ℝ)) =
        pmPowerDampedRealWeight (1 + ε) := by
    funext e
    exact pmPowerDampedRealWeight_div_eq_add_one ε e
  have h2 :
      Tendsto
        (fun N : ℕ =>
          -(1 / 2 : ℝ) *
            ∑ u ∈ d.divisors.filter (fun u => 1 < u),
              (moebiusReal u * selbergMultiplesCoord N (pmPowerDampedRealWeight ε) u +
                ((Nat.totient u : ℝ) - moebiusReal u) *
                  selbergMultiplesCoord N (fun e => pmPowerDampedRealWeight ε e / (e : ℝ)) u))
        atTop
        (𝓝
          (-(1 / 2 : ℝ) *
            ∑ u ∈ d.divisors.filter (fun u => 1 < u),
              (moebiusReal u * pmRealRamanujanWeight ε u +
                ((Nat.totient u : ℝ) - moebiusReal u) * pmRealRamanujanWeight (1 + ε) u))) := by
    refine Tendsto.const_mul (-(1 / 2 : ℝ)) (tendsto_finsetSum _ fun u hu => ?_)
    have hu_pos : 0 < u := by
      have := (mem_filter.mp hu).2
      omega
    have ht1 :
        Tendsto (fun N : ℕ => selbergMultiplesCoord N (pmPowerDampedRealWeight ε) u)
          atTop (𝓝 (pmRealRamanujanWeight ε u)) :=
      tendsto_selbergMultiplesCoord_pmPowerDamped hε hu_pos
    have ht2 :
        Tendsto
          (fun N : ℕ => selbergMultiplesCoord N (fun e => pmPowerDampedRealWeight ε e / (e : ℝ)) u)
          atTop (𝓝 (pmRealRamanujanWeight (1 + ε) u)) := by
      rw [hfun]
      exact tendsto_selbergMultiplesCoord_pmPowerDamped (by linarith : 0 < 1 + ε) hu_pos
    exact (ht1.const_mul (moebiusReal u)).add
      (ht2.const_mul ((Nat.totient u : ℝ) - moebiusReal u))
  have heq :
      (fun N : ℕ => ∑ e ∈ Icc 1 N, pmPowerDampedRealWeight ε e * interiorJumpOrbitMean d e) =
        fun N : ℕ =>
          -(1 / 2 : ℝ) *
            ∑ u ∈ d.divisors.filter (fun u => 1 < u),
              (moebiusReal u * selbergMultiplesCoord N (pmPowerDampedRealWeight ε) u +
                ((Nat.totient u : ℝ) - moebiusReal u) *
                  selbergMultiplesCoord N (fun e => pmPowerDampedRealWeight ε e / (e : ℝ)) u) := by
    funext N
    exact sum_Icc_mul_interiorJumpOrbitMean_eq_selbergMultiplesCoord N
      (pmPowerDampedRealWeight ε) hd
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-- At `d = 1`, `pmSignedInteriorJumpOrbitMean ε 1 = 0`. -/
@[simp] theorem pmSignedInteriorJumpOrbitMean_one (ε : ℝ) :
    pmSignedInteriorJumpOrbitMean ε 1 = 0 := by
  unfold pmSignedInteriorJumpOrbitMean interiorJumpOrbitMean
  simp

/-- **Closed Form at Prime Jump Moduli (`pmSignedInteriorJumpOrbitMean_prime`):**
For every `ε > 0` and prime `p`,
$$\mathcal{M}_\varepsilon(p)
  = \frac{1}{2}\,Y_\varepsilon(p) - \frac{p}{2}\,Y_{1+\varepsilon}(p)
  = -\frac{1}{2}\left(\frac{\alpha_\varepsilon}{p^{1+\varepsilon} - 1}
    - \frac{p\,\alpha_{1+\varepsilon}}{p^{2+\varepsilon} - 1}\right).$$ -/
theorem pmSignedInteriorJumpOrbitMean_prime
    {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    pmSignedInteriorJumpOrbitMean ε p =
      (1 / 2 : ℝ) * pmRealRamanujanWeight ε p -
        ((p : ℝ) / 2) * pmRealRamanujanWeight (1 + ε) p ∧
    pmSignedInteriorJumpOrbitMean ε p =
      -(1 / 2 : ℝ) *
        ((pmPowerDampedDivisorDensity ε).re / ((p : ℝ) ^ (1 + ε) - 1) -
          (p : ℝ) * (pmPowerDampedDivisorDensity (1 + ε)).re / ((p : ℝ) ^ (2 + ε) - 1)) := by
  have hdiv : p.divisors.filter (fun u => 1 < u) = {p} := by
    ext u
    simp only [mem_filter, hp.divisors, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hu1⟩
      · omega
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, hp.one_lt⟩
  have hmup : moebiusReal p = -1 := by
    unfold moebiusReal
    rw [ArithmeticFunction.moebius_apply_prime hp]
    norm_num
  have h1 :
      pmSignedInteriorJumpOrbitMean ε p =
        (1 / 2 : ℝ) * pmRealRamanujanWeight ε p -
          ((p : ℝ) / 2) * pmRealRamanujanWeight (1 + ε) p := by
    rw [pmSignedInteriorJumpOrbitMean_eq_sum_divisors hε hp.one_lt.le,
      hdiv, sum_singleton, totient_sub_moebiusReal_prime hp, hmup]
    ring
  refine ⟨h1, ?_⟩
  rw [h1, pmRealRamanujanWeight_prime hε hp,
    pmRealRamanujanWeight_prime (by linarith : 0 < 1 + ε) hp,
    show (1 : ℝ) + (1 + ε) = 2 + ε by ring]
  ring

/-- `pmRealRamanujanWeight ε u` vanishes whenever `¬ Squarefree u`. -/
theorem pmRealRamanujanWeight_eq_zero_of_not_squarefree (ε : ℝ) {u : ℕ} (hu : ¬ Squarefree u) :
    pmRealRamanujanWeight ε u = 0 := by
  unfold pmRealRamanujanWeight
  rw [pmPowerDampedRamanujanWeight_eq_zero_of_not_squarefree ε hu, Complex.zero_re]

/-- **Squarefree Divisor Restriction (`pmSignedInteriorJumpOrbitMean_eq_sum_squarefree_divisors`):**
Because both `pmRealRamanujanWeight ε u` and `pmRealRamanujanWeight (1 + ε) u` vanish outside
squarefree integers, only the squarefree proper divisors `u ∣ d` (`1 < u ∧ Squarefree u`) contribute
to `pmSignedInteriorJumpOrbitMean ε d`. -/
theorem pmSignedInteriorJumpOrbitMean_eq_sum_squarefree_divisors
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 1 ≤ d) :
    pmSignedInteriorJumpOrbitMean ε d =
      -(1 / 2 : ℝ) *
        ∑ u ∈ d.divisors.filter (fun u => 1 < u ∧ Squarefree u),
          (moebiusReal u * pmRealRamanujanWeight ε u +
            ((Nat.totient u : ℝ) - moebiusReal u) * pmRealRamanujanWeight (1 + ε) u) := by
  rw [pmSignedInteriorJumpOrbitMean_eq_sum_divisors hε hd]
  congr 1
  have hsub :
      d.divisors.filter (fun u => 1 < u ∧ Squarefree u) =
        (d.divisors.filter (fun u => 1 < u)).filter Squarefree := by
    ext u; simp only [mem_filter]; tauto
  rw [hsub]
  refine (sum_filter_of_ne fun u _ hnot => ?_).symm
  by_contra hsq
  exact hnot (by
    rw [pmRealRamanujanWeight_eq_zero_of_not_squarefree ε hsq,
      pmRealRamanujanWeight_eq_zero_of_not_squarefree (1 + ε) hsq]
    ring)

/-- Two positive integers with the same prime factors have the exact same squarefree divisors. -/
private theorem squarefree_mem_divisors_iff_of_primeFactors_eq
    {d₁ d₂ u : ℕ} (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    (hpf : d₁.primeFactors = d₂.primeFactors) (hsq : Squarefree u) :
    u ∈ d₁.divisors ↔ u ∈ d₂.divisors := by
  have hu0 : u ≠ 0 := hsq.ne_zero
  simp only [Nat.mem_divisors, show d₁ ≠ 0 by omega, show d₂ ≠ 0 by omega, ne_eq,
    not_false_eq_true, and_true]
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  have h1 : (∏ p ∈ u.primeFactors, p) ∣ d₁ ↔ u.primeFactors ⊆ d₁.primeFactors := by
    constructor
    · intro hdvd p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      exact Nat.mem_primeFactors.mpr
        ⟨hp_prime, (Finset.dvd_prod_of_mem _ hp).trans hdvd, by omega⟩
    · intro hsub
      calc (∏ p ∈ u.primeFactors, p)
          ∣ ∏ p ∈ d₁.primeFactors, p := Finset.prod_dvd_prod_of_subset _ _ _ hsub
        _ ∣ d₁ := Nat.prod_primeFactors_dvd d₁
  have h2 : (∏ p ∈ u.primeFactors, p) ∣ d₂ ↔ u.primeFactors ⊆ d₂.primeFactors := by
    constructor
    · intro hdvd p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      exact Nat.mem_primeFactors.mpr
        ⟨hp_prime, (Finset.dvd_prod_of_mem _ hp).trans hdvd, by omega⟩
    · intro hsub
      calc (∏ p ∈ u.primeFactors, p)
          ∣ ∏ p ∈ d₂.primeFactors, p := Finset.prod_dvd_prod_of_subset _ _ _ hsub
        _ ∣ d₂ := Nat.prod_primeFactors_dvd d₂
  rw [h1, h2, hpf]

/-- **Radical Invariance of `pmSignedInteriorJumpOrbitMean`
(`pmSignedInteriorJumpOrbitMean_eq_of_primeFactors_eq`):**
For every `ε > 0` and any `d₁, d₂ ≥ 1` with `d₁.primeFactors = d₂.primeFactors`,
`pmSignedInteriorJumpOrbitMean ε d₁ = pmSignedInteriorJumpOrbitMean ε d₂`. -/
theorem pmSignedInteriorJumpOrbitMean_eq_of_primeFactors_eq
    {ε : ℝ} (hε : 0 < ε) {d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    (hpf : d₁.primeFactors = d₂.primeFactors) :
    pmSignedInteriorJumpOrbitMean ε d₁ = pmSignedInteriorJumpOrbitMean ε d₂ := by
  rw [pmSignedInteriorJumpOrbitMean_eq_sum_squarefree_divisors hε hd₁,
    pmSignedInteriorJumpOrbitMean_eq_sum_squarefree_divisors hε hd₂]
  congr 1
  refine sum_congr ?_ (fun _ _ => rfl)
  ext u
  simp only [mem_filter]
  exact ⟨fun ⟨hm, hu1, hsq⟩ =>
    ⟨(squarefree_mem_divisors_iff_of_primeFactors_eq hd₁ hd₂ hpf hsq).mp hm, hu1, hsq⟩,
    fun ⟨hm, hu1, hsq⟩ =>
    ⟨(squarefree_mem_divisors_iff_of_primeFactors_eq hd₁ hd₂ hpf hsq).mpr hm, hu1, hsq⟩⟩

/-- **Power Invariance (`pmSignedInteriorJumpOrbitMean_pow`):**
For every `ε > 0`, `d ≥ 1`, and `k ≥ 1`,
`pmSignedInteriorJumpOrbitMean ε (d ^ k) = pmSignedInteriorJumpOrbitMean ε d`. -/
theorem pmSignedInteriorJumpOrbitMean_pow
    {ε : ℝ} (hε : 0 < ε) {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k) :
    pmSignedInteriorJumpOrbitMean ε (d ^ k) = pmSignedInteriorJumpOrbitMean ε d :=
  pmSignedInteriorJumpOrbitMean_eq_of_primeFactors_eq hε (Nat.one_le_pow k d hd) hd
    (Nat.primeFactors_pow d (by omega))

/-- Uniform bound on `|pmSignedInteriorJumpOrbitMean ε d|` for all `d ≥ 1`. -/
theorem abs_pmSignedInteriorJumpOrbitMean_le
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 1 ≤ d) :
    |pmSignedInteriorJumpOrbitMean ε d| ≤
      (1 / 2 : ℝ) * ∑' e : ℕ, (e : ℝ) ^ (-1 - ε) := by
  unfold pmSignedInteriorJumpOrbitMean
  have hs : Summable (fun e : ℕ => (1 / 2 : ℝ) * (e : ℝ) ^ (-1 - ε)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -1 - ε < -1)).mul_left (1 / 2 : ℝ)
  have h1 := norm_tsum_le_tsum_norm
    (summable_pmPowerDampedRealWeight_mul_interiorJumpOrbitMean hε hd).norm
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun e => ?_)
    (summable_pmPowerDampedRealWeight_mul_interiorJumpOrbitMean hε hd).norm hs
  rw [Real.norm_eq_abs]
  exact abs_pmPowerDampedRealWeight_mul_interiorJumpOrbitMean_le ε hd e

/-- **Absolute Double-Modulus Summability (`summable_pmPowerDampedRealWeight_div_mul_pmSignedInteriorJumpOrbitMean`):**
For every `ε > 0`, the global double-modulus drift series
`d ↦ (pmPowerDampedRealWeight ε d / d) * pmSignedInteriorJumpOrbitMean ε d` is absolutely summable. -/
theorem summable_pmPowerDampedRealWeight_div_mul_pmSignedInteriorJumpOrbitMean
    {ε : ℝ} (hε : 0 < ε) :
    Summable (fun d : ℕ =>
      (pmPowerDampedRealWeight ε d / (d : ℝ)) * pmSignedInteriorJumpOrbitMean ε d) := by
  set Z := (1 / 2 : ℝ) * ∑' e : ℕ, (e : ℝ) ^ (-1 - ε)
  have hZ0 : 0 ≤ Z := by
    unfold Z
    exact mul_nonneg (by positivity) (tsum_nonneg fun e => Real.rpow_nonneg (Nat.cast_nonneg e) _)
  refine Summable.of_norm_bounded
    ((Real.summable_nat_rpow.mpr (by linarith : -1 - ε < -1)).mul_right Z)
    fun d => ?_
  rw [Real.norm_eq_abs, abs_mul]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [Nat.cast_zero, div_zero, abs_zero, zero_mul]
    exact mul_nonneg (Real.rpow_nonneg le_rfl _) hZ0
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have h1 : |pmPowerDampedRealWeight ε d / (d : ℝ)| ≤ (d : ℝ) ^ (-1 - ε) := by
      refine (abs_pmPowerDampedRealWeight_div_le d).trans ?_
      rw [← Real.rpow_sub_one hd0.ne', show -ε - 1 = -1 - ε by ring]
    have h2 := abs_pmSignedInteriorJumpOrbitMean_le hε hd
    exact mul_le_mul h1 h2 (abs_nonneg _) (Real.rpow_nonneg hd0.le _)

/-! ## §3. Cutoff-Free Signed Progression Bounds and Sub-Half-Damping Laws for the Interior Martingale -/

/-- Exact identification of `weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n`
with `pmPowerDampedCenteredDivisorPrefix ε n`. -/
theorem weightCenteredPrefix_pmPowerDamped_eq (ε : ℝ) (n : ℕ) :
    weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n =
      pmPowerDampedCenteredDivisorPrefix ε n := by
  rw [weightCenteredPrefix, RHTower.pmPowerDampedCenteredDivisorPrefix_eq]
  rfl

/-- **All-Damping Vinogradov–Korobov Bound on `pmBezoutInteriorPrefix`
(`exists_abs_pmBezoutInteriorPrefix_le_vk_all_pos`):**
There exist `K ≥ 0` and `N₁ : ℕ` such that for **every** `0 < ε ≤ 1/2` and every `n ≥ N₁`,
`|pmBezoutInteriorPrefix ε n| ≤ (K / ε + 1 / 2) n^{1−ε} exp(−κ σ(n)/240)`. -/
theorem exists_abs_pmBezoutInteriorPrefix_le_vk_all_pos :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₁ : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ n : ℕ, N₁ ≤ n →
      |pmBezoutInteriorPrefix ε n| ≤
        (K / ε + 1 / 2) * (n : ℝ) ^ (1 - ε) * Real.exp (-(vkKappa * vkScale n / 240)) := by
  obtain ⟨K, hK0, N₀, hpre⟩ := exists_abs_weightCenteredPrefix_pmPowerDamped_le_vk_all_pos
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop.eventually (eventually_vk_conditions one_pos 0)).and
      (hlog.eventually_ge_atTop 3))
  refine ⟨K, hK0, max N₀ N₂, fun ε hε hε2 n hn => ?_⟩
  have hn0' : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N₂ ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hvk, hℓ3⟩ := hN₂ n hn2
  obtain ⟨-, -, -, -, -, hle, -⟩ := hvk
  rw [log_vkHeight] at hle
  have hn0 : (0 : ℝ) < n := by
    by_contra h
    have : (n : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg n)
    rw [this, Real.log_zero] at hℓ3; linarith
  have hA := hpre ε hε hε2 n hn0'
  rw [weightCenteredPrefix_pmPowerDamped_eq] at hA
  have hsplit := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε n
  have hI : pmBezoutInteriorPrefix ε n =
      pmPowerDampedCenteredDivisorPrefix ε n - addDiff (pmActiveSawtoothComponent ε) n := by
    linarith [hsplit]
  have hact := abs_addDiff_pmActiveSawtoothComponent_le_half hε.le n
  have h1le : 1 ≤ (n : ℝ) ^ (1 - ε) * Real.exp (-(vkKappa * vkScale n / 240)) := by
    rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]
    exact Real.one_le_exp (by nlinarith)
  rw [hI]
  calc |pmPowerDampedCenteredDivisorPrefix ε n - addDiff (pmActiveSawtoothComponent ε) n|
      ≤ |pmPowerDampedCenteredDivisorPrefix ε n| + |addDiff (pmActiveSawtoothComponent ε) n| :=
        abs_sub _ _
    _ ≤ K / ε * (n : ℝ) ^ (1 - ε) * Real.exp (-(vkKappa * vkScale n / 240)) +
          (1 / 2) * ((n : ℝ) ^ (1 - ε) * Real.exp (-(vkKappa * vkScale n / 240))) :=
        add_le_add hA (by linarith)
    _ = (K / ε + 1 / 2) * (n : ℝ) ^ (1 - ε) * Real.exp (-(vkKappa * vkScale n / 240)) := by ring

/-- **Cutoff-Free Vinogradov–Korobov Bound Along Every Predecessor Jump Progression
(`exists_abs_pmBezoutInteriorPrefix_jump_compensated_le_vk_all_pos`):**
Retaining the signed sum over interior moduli `e` in `pmBezoutInteriorPrefix ε n` removes the
external modulus cutoff `N = (d + 2) L` along every jump progression `n = d − 1 + d k` (`d ≥ 1`):
there exist `K ≥ 0` and `N₁ : ℕ` such that for all `0 < ε ≤ 1/2`, `d ≥ 1`, `T : ℕ`, and
`1 ≤ K₀ ≤ L` with `N₁ ≤ d − 1 + d K₀`,
$$\left|\sum_{k \in \operatorname{Ico}\,K_0\,L}
  \operatorname{interiorJumpCompensatedWeight}\,d\,T\,k \cdot
    \operatorname{pmBezoutInteriorPrefix}\,\varepsilon\,(d - 1 + d k)\right|
  \le (K / \varepsilon + 1 / 2)\,d^{-\varepsilon}
    \sum_{k \in \operatorname{Ico}\,K_0\,L}
      (k + 1)^{-\varepsilon}\,\exp\bigl(-\kappa\,\sigma(d - 1 + d k) / 240\bigr).$$ -/
theorem exists_abs_pmBezoutInteriorPrefix_jump_compensated_le_vk_all_pos :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₁ : ℕ,
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      ∀ (d : ℕ+), ∀ (T K₀ L : ℕ), N₁ ≤ (d : ℕ) - 1 + d * K₀ →
        |∑ k ∈ Ico K₀ L,
          interiorJumpCompensatedWeight d T k *
            pmBezoutInteriorPrefix ε ((d : ℕ) - 1 + d * k)| ≤
          (K / ε + 1 / 2) * (d : ℝ) ^ (-ε) *
            ∑ k ∈ Ico K₀ L,
              ((k : ℝ) + 1) ^ (-ε) *
                Real.exp (-(vkKappa * vkScale (((d : ℕ) - 1 + d * k : ℕ) : ℝ) / 240)) := by
  obtain ⟨K, hK0, N₁, hvk⟩ := exists_abs_pmBezoutInteriorPrefix_le_vk_all_pos
  refine ⟨K, hK0, N₁, fun ε hε hε2 d T K₀ L hN₁ => ?_⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast d.pos
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  have hk_ge : K₀ ≤ k := (mem_Ico.mp hk).1
  set n := (d : ℕ) - 1 + d * k
  have hn_ge : N₁ ≤ n := le_trans hN₁ (Nat.add_le_add_left (Nat.mul_le_mul_left d hk_ge) _)
  have hw0 : 0 ≤ interiorJumpCompensatedWeight d T k := le_max_right _ _
  have hw_le : interiorJumpCompensatedWeight d T k ≤ 1 / ((d : ℝ) * ((k : ℝ) + 1)) :=
    max_le (sub_le_self _ (by positivity)) (by positivity)
  have hpre := hvk ε hε hε2 n hn_ge
  have hn_le : (n : ℝ) ≤ (d : ℝ) * ((k : ℝ) + 1) := by
    have hd_pos : 0 < (d : ℕ) := d.pos
    have hnat : n + 1 = (d : ℕ) * (k + 1) := by
      dsimp [n]; rw [Nat.mul_add, Nat.mul_one]; omega
    have hR : (n : ℝ) + 1 = (d : ℝ) * ((k : ℝ) + 1) := by exact_mod_cast hnat
    linarith
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hpow_le :
      (n : ℝ) ^ (1 - ε) / ((d : ℝ) * ((k : ℝ) + 1)) ≤
        (d : ℝ) ^ (-ε) * ((k : ℝ) + 1) ^ (-ε) := by
    calc (n : ℝ) ^ (1 - ε) / ((d : ℝ) * ((k : ℝ) + 1))
        ≤ ((d : ℝ) * ((k : ℝ) + 1)) ^ (1 - ε) / ((d : ℝ) * ((k : ℝ) + 1)) :=
          div_le_div_of_nonneg_right
            (Real.rpow_le_rpow (Nat.cast_nonneg n) hn_le (by linarith)) (by positivity)
      _ = ((d : ℝ) * ((k : ℝ) + 1)) ^ (-ε) := by
          rw [← Real.rpow_sub_one (by positivity : (d : ℝ) * ((k : ℝ) + 1) ≠ 0),
            show 1 - ε - 1 = -ε by ring]
      _ = (d : ℝ) ^ (-ε) * ((k : ℝ) + 1) ^ (-ε) :=
          Real.mul_rpow hd0.le hk1_pos.le
  rw [abs_mul, abs_of_nonneg hw0]
  calc interiorJumpCompensatedWeight d T k * |pmBezoutInteriorPrefix ε n|
      ≤ (1 / ((d : ℝ) * ((k : ℝ) + 1))) *
          ((K / ε + 1 / 2) * (n : ℝ) ^ (1 - ε) * Real.exp (-(vkKappa * vkScale n / 240))) :=
        mul_le_mul hw_le hpre (abs_nonneg _) (by positivity)
    _ = (K / ε + 1 / 2) * ((n : ℝ) ^ (1 - ε) / ((d : ℝ) * ((k : ℝ) + 1))) *
          Real.exp (-(vkKappa * vkScale n / 240)) := by ring
    _ ≤ (K / ε + 1 / 2) * ((d : ℝ) ^ (-ε) * ((k : ℝ) + 1) ^ (-ε)) *
          Real.exp (-(vkKappa * vkScale n / 240)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow_le (by positivity))
          (Real.exp_pos _).le
    _ = (K / ε + 1 / 2) * (d : ℝ) ^ (-ε) *
          (((k : ℝ) + 1) ^ (-ε) * Real.exp (-(vkKappa * vkScale n / 240))) := by ring

/-- **Two-Sided Uniform `O_ε(1)` Energy Tracking of the Compensated Interior Martingale
(`exists_abs_compensated_interiorMartingale_le_discreteEnergy_add`):**
For every `ε > 0`, there exists `C ≥ 0` such that for all `T : ℕ`,
`|2 * pmBezoutInteriorMartingaleSum ε T + 2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T| ≤ pmPowerDampedDivisorDiscreteEnergy ε T + C`. -/
theorem exists_abs_compensated_interiorMartingale_le_discreteEnergy_add
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |2 * pmBezoutInteriorMartingaleSum ε T +
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T| ≤
        pmPowerDampedDivisorDiscreteEnergy ε T + C := by
  obtain ⟨C, hC0, hC⟩ := exists_pmBezoutInterior_compensated_energy_bound hε
  refine ⟨C, hC0, fun T => ?_⟩
  have hE0 := pmPowerDampedDivisorDiscreteEnergy_nonneg ε T
  obtain ⟨hlow, hhigh⟩ := abs_le.mp (hC T)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **All-Damping Sub-Half-Damping Growth Bound on the Compensated Interior Martingale Bracket
(`eventually_abs_compensated_interiorMartingale_le_growth_of_pos`):**
For **every** `0 < ε < 1/2`, there exists `C ≥ 0` such that for all large `T : ℕ`,
`|2 M_T^{int}(ε) + 2 c^{int}(ε) H_T^{comp}| ≤ C T^{1−2ε} exp(−κ σ(T)/270)`. -/
theorem eventually_abs_compensated_interiorMartingale_le_growth_of_pos
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop,
      |2 * pmBezoutInteriorMartingaleSum ε T +
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T| ≤
        C * (T : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale T / 270)) := by
  obtain ⟨C₁, hC₁, hE⟩ := eventually_receiver_le_growth_of_pos hε hε2
  obtain ⟨C₂, hC₂, htrack⟩ := exists_abs_compensated_interiorMartingale_le_discreteEnergy_add hε
  set a := 1 - 2 * ε with hadef
  have ha0 : 0 < a := by rw [hadef]; linarith
  have hκ := vkKappa_pos
  have hratio := (tendsto_vkScale_div_log.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_le_nhds (show (0 : ℝ) < a * 270 / (2 * vkKappa) by positivity))
  have hlog : Tendsto (fun T : ℕ => Real.log T) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  filter_upwards [hE, hratio, hlog.eventually_ge_atTop 3] with T hET hTr hT3
  simp only [Function.comp_apply] at hTr
  have hT0 : (0 : ℝ) < T := by
    by_contra h
    have : (T : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg T)
    rw [this, Real.log_zero] at hT3; linarith
  set s := vkKappa * vkScale T / 270 with hsdef
  have hsa : s ≤ a / 2 * Real.log T := by
    have hσ' : vkScale T ≤ a * 270 / (2 * vkKappa) * Real.log T := by
      rwa [div_le_iff₀ (by linarith)] at hTr
    rw [hsdef]
    calc vkKappa * vkScale T / 270 ≤ vkKappa * (a * 270 / (2 * vkKappa) * Real.log T) / 270 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hσ' hκ.le) (by norm_num)
      _ = a / 2 * Real.log T := by field_simp
  set G := (T : ℝ) ^ a * Real.exp (-s) with hGdef
  have hGsq : (T : ℝ) ^ (a / 2) ≤ G := by
    rw [hGdef, Real.rpow_def_of_pos hT0, Real.rpow_def_of_pos hT0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hG1 : 1 ≤ G := le_trans (Real.one_le_rpow (by
    have := Real.add_one_le_exp (Real.log T)
    rw [Real.exp_log hT0] at this; linarith) (by positivity)) hGsq
  have hET' : pmPowerDampedDivisorDiscreteEnergy ε T ≤ C₁ * G := by
    rw [hGdef]; exact le_trans hET (le_of_eq (by ring))
  calc |2 * pmBezoutInteriorMartingaleSum ε T +
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T|
      ≤ pmPowerDampedDivisorDiscreteEnergy ε T + C₂ := htrack T
    _ ≤ C₁ * G + C₂ * G := by nlinarith
    _ = (C₁ + C₂) * (T : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale T / 270)) := by
        rw [hGdef, hadef, hsdef]; ring

/-- **All-Damping Sub-Half-Damping Growth Bound on the Raw Interior Martingale `M_T^{int}(ε)`
(`eventually_abs_pmBezoutInteriorMartingaleSum_le_growth_of_pos`):**
For **every** `0 < ε < 1/2`, there exists `C ≥ 0` such that for all large `T : ℕ`,
`|pmBezoutInteriorMartingaleSum ε T| ≤ C T^{1−2ε} exp(−κ σ(T)/270)`.
This improves the sign-blind jump bound `O_ε(T^{1−ε} exp(−κ σ(T)/270))` by a full factor of `T^{−ε}`. -/
theorem eventually_abs_pmBezoutInteriorMartingaleSum_le_growth_of_pos
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop,
      |pmBezoutInteriorMartingaleSum ε T| ≤
        C * (T : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale T / 270)) := by
  obtain ⟨C₁, hC₁, hbr⟩ := eventually_abs_compensated_interiorMartingale_le_growth_of_pos hε hε2
  set a := 1 - 2 * ε with hadef
  have ha0 : 0 < a := by rw [hadef]; linarith
  have hκ := vkKappa_pos
  have hratio := (tendsto_vkScale_div_log.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_le_nhds (show (0 : ℝ) < a * 270 / (2 * vkKappa) by positivity))
  have hlog : Tendsto (fun T : ℕ => Real.log T) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  set K_log := |pmInteriorLogCounterterm ε| * (2 / a + |Real.eulerMascheroniConstant| + 3)
  have hK_log : 0 ≤ K_log := by positivity
  refine ⟨C₁ / 2 + K_log, by positivity, ?_⟩
  filter_upwards [hbr, hratio, hlog.eventually_ge_atTop 3, eventually_ge_atTop 1]
    with T hbrT hTr hT3 hT1
  simp only [Function.comp_apply] at hTr
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  set s := vkKappa * vkScale T / 270 with hsdef
  have hsa : s ≤ a / 2 * Real.log T := by
    have hσ' : vkScale T ≤ a * 270 / (2 * vkKappa) * Real.log T := by
      rwa [div_le_iff₀ (by linarith)] at hTr
    rw [hsdef]
    calc vkKappa * vkScale T / 270 ≤ vkKappa * (a * 270 / (2 * vkKappa) * Real.log T) / 270 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hσ' hκ.le) (by norm_num)
      _ = a / 2 * Real.log T := by field_simp
  set G := (T : ℝ) ^ a * Real.exp (-s) with hGdef
  have hGsq : (T : ℝ) ^ (a / 2) ≤ G := by
    rw [hGdef, Real.rpow_def_of_pos hT0, Real.rpow_def_of_pos hT0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hG1 : 1 ≤ G := le_trans (Real.one_le_rpow (by
    have := Real.add_one_le_exp (Real.log T)
    rw [Real.exp_log hT0] at this; linarith) (by positivity)) hGsq
  have hlog_le : Real.log T ≤ (2 / a) * G := by
    have hexp := Real.add_one_le_exp (Real.log T * (a / 2))
    rw [← Real.rpow_def_of_pos hT0 (a / 2)] at hexp
    have h1 : a / 2 * Real.log T ≤ G := by linarith
    have h2 : Real.log T = (2 / a) * (a / 2 * Real.log T) := by field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hcomp_le : |pmCompensatedHarmonicSum T| ≤ (2 / a + |Real.eulerMascheroniConstant| + 3) * G := by
    rw [abs_of_nonneg (pmCompensatedHarmonicSum_nonneg T)]
    have hsub := (abs_le.mp (abs_pmCompensatedHarmonicSum_sub_log_le hT1)).2
    have hpos_const : 0 ≤ |Real.eulerMascheroniConstant| + 3 := by positivity
    calc pmCompensatedHarmonicSum T
        ≤ Real.log T + (|Real.eulerMascheroniConstant| + 3) := by linarith
      _ ≤ (2 / a) * G + (|Real.eulerMascheroniConstant| + 3) * G := by nlinarith
      _ = (2 / a + |Real.eulerMascheroniConstant| + 3) * G := by ring
  have hcounter :
      |pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T| ≤ K_log * G := by
    rw [abs_mul, show K_log * G = |pmInteriorLogCounterterm ε| *
      ((2 / a + |Real.eulerMascheroniConstant| + 3) * G) by unfold K_log; ring]
    exact mul_le_mul_of_nonneg_left hcomp_le (abs_nonneg _)
  have hbrT' :
      |2 * pmBezoutInteriorMartingaleSum ε T +
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T| ≤ C₁ * G := by
    rw [hGdef]; exact le_trans hbrT (le_of_eq (by ring))
  have hsplit :
      pmBezoutInteriorMartingaleSum ε T =
        (1 / 2 : ℝ) *
          (2 * pmBezoutInteriorMartingaleSum ε T +
            2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T) -
          pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T := by ring
  rw [hsplit]
  calc |(1 / 2 : ℝ) *
        (2 * pmBezoutInteriorMartingaleSum ε T +
          2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T) -
        pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T|
      ≤ (1 / 2 : ℝ) *
          |2 * pmBezoutInteriorMartingaleSum ε T +
            2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T| +
          |pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ (1 / 2 : ℝ) * (C₁ * G) + K_log * G := by linarith
    _ = (C₁ / 2 + K_log) * (T : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale T / 270)) := by
        rw [hGdef, hadef, hsdef]; ring

/-- **All-Damping Decay of the Compensated Interior Martingale Against the Period Energy
(`eventually_abs_compensated_interiorMartingale_le_mul_periodEnergy_of_pos`):**
For **every** `0 < ε < 1/2`, there exists `C ≥ 0` such that for all large `N : ℕ`,
`|2 M_N^{int}(ε) + 2 c^{int}(ε) H_N^{comp}| ≤ C exp(−κ σ(N)/270) E_prim(N)`. -/
theorem eventually_abs_compensated_interiorMartingale_le_mul_periodEnergy_of_pos
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      |2 * pmBezoutInteriorMartingaleSum ε N +
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum N| ≤
        C * Real.exp (-(vkKappa * vkScale N / 270)) *
          sievePrimitiveEnergy N (pmPowerDampedRealWeight ε) := by
  obtain ⟨C, hC0, hC⟩ := eventually_abs_compensated_interiorMartingale_le_growth_of_pos hε hε2
  refine ⟨10368 * C, by positivity, ?_⟩
  filter_upwards [hC, eventually_sievePrimitiveEnergy_pmPowerDamped_growth hε hε2]
    with N hN hP
  have hlow := hP.1
  have he : 0 ≤ Real.exp (-(vkKappa * vkScale N / 270)) := (Real.exp_pos _).le
  calc _ ≤ C * (N : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale N / 270)) := hN
    _ ≤ C * (10368 * sievePrimitiveEnergy N (pmPowerDampedRealWeight ε)) *
          Real.exp (-(vkKappa * vkScale N / 270)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC0) he
    _ = _ := by ring

end

end GaloisForLFunctions.BezoutValuationIncidence

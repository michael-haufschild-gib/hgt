import GaloisForLFunctions.BiScaleUncertainty.NyquistWeightTailMass
import GaloisForLFunctions.BiScaleUncertainty.NyquistWeightPrefixMass
import GaloisForLFunctions.BiScaleUncertainty.NyquistWideSourceEnergy
import GaloisForLFunctions.BiScaleUncertainty.NyquistWideResidualEscape
import GaloisForLFunctions.BiScaleUncertainty.SignedDyadicCollarPartition

/-!
# Critical Nyquist Finite Part and Signed Broad-Source Classification

This module formalizes the **Critical Nyquist Finite Part and Signed Broad-Source Classification**
(`docs/reports/BiScaleUncertainty/NyquistCriticalFinitePart.md`), completing the analysis of the
critical Taylor-order boundary $\beta = m + 1$ in Bi-Scale / Logarithmic-Grid Uncertainty Theory:

1. **Critical Nyquist Cell Discrepancy and Inverse-Square Bound (§1–§2):**
   At the critical exponent $\beta = m + 1$, the Nyquist cell mass $\alpha_k$ diverges
   logarithmically ($\sum_{k < M} \alpha_k \sim c_m \log(M+1)$ where
   $c_m = (m+1)^{m+1} / (2(m+2)!)$). Subtracting the continuous mean counterterm $c_m \delta_k$
   (where $\delta_k = \log(k+2) - \log(k+1)$ is the $k$-th logarithmic cell width) defines the
   cell discrepancy
   $$d_k(m) := \alpha_k(m+1, m) - c_m \delta_k.$$
   We prove the explicit uniform bound (`abs_nyquistCriticalCellDiscrepancy_le`):
   $$|d_k(m)| \le D_m \frac{\delta_k}{k + 1} \le \frac{D_m}{(k + 1)^2},
     \qquad D_m := c_m 2^{m+1}.$$
2. **Absolute Summability and Tail Bounds of the Critical Nyquist Finite Part $\mathcal{B}_m$ (§3):**
   The cell discrepancies $d_k(m)$ are absolutely summable (`summable_abs_nyquistCriticalCellDiscrepancy`),
   defining the **Critical Nyquist Finite Part**
   $$\mathcal{B}_m := \sum_{k=0}^\infty d_k(m), \qquad
     \mathcal{B}_{m, N} := \sum_{k=0}^\infty d_{N+k}(m),$$
   with explicit quantitative tail bound (`abs_nyquistCriticalFinitePartTail_le`):
   $$|\mathcal{B}_{m, N}| \le \frac{2 D_m}{N + 1}, \qquad |\mathcal{B}_m| \le 2 D_m.$$
   At every logarithmic node $T_N = \log(N+1)$, the continuous counterterm telescopes (`∑_{k < N} \delta_k = \log(N+1)`),
   giving the exact nodal identity and $O(1/(N+1))$ convergence (`abs_nyquistCriticalPrefixPrimitive_sub_finitePart_le`):
   $$\left|\left(\sum_{k < N} \alpha_k - c_m \log(N + 1)\right) - \mathcal{B}_m\right|
     = |\mathcal{B}_{m, N}| \le \frac{2 D_m}{N + 1}.$$
3. **Autocorrelation Total Mass Identity and Rescaled-Source Classification (§4–§5):**
   For every compactly supported continuous source $f \in C_c(\mathbb{R}, \mathbb{R})$, Fubini/convolution
   gives the exact autocorrelation total mass identity (`integral_autocorr_eq_sq_integral`):
   $$\int_{\mathbb{R}} \operatorname{autocorr}(f, x)\,dx = \left(\int_{\mathbb{R}} f(u)\,du\right)^2.$$
   We construct the explicit smooth zero-mean cancellation witness
   $g(u) = p(u) - p(u - 4)$ (where $p = \operatorname{nyquistWideBump}$), proving that:
   - $\int_{\mathbb{R}} g(u)\,du = 0$ and $\int_{\mathbb{R}} \operatorname{autocorr}(g, x)\,dx = 0$
     (so its critical leading slope $c_m (\int g)^2 / (2 \int g^2)$ vanishes identically),
   - while for $p = \operatorname{nyquistWideBump}$, $\int_{\mathbb{R}} \operatorname{autocorr}(p, x)\,dx > 0$
     and the critical Nyquist residual diverges to $+\infty$ despite $\mathcal{E}_{\mathrm{norm}}(p_j) \to 0$.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped BigOperators CompactlySupported Convolution
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

/-! ## §1. Elementary Polynomial Bounds on `[0, 1]` -/

/-- Bernoulli lower bound on `[0, 1]`: for `0 ≤ t ≤ 1` and `r : ℕ`, `1 - r * t ≤ (1 - t) ^ r`. -/
theorem one_sub_mul_le_pow_of_unit {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) (r : ℕ) :
    1 - (r : ℝ) * t ≤ (1 - t) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [ pow_succ, Nat.cast_add, Nat.cast_one ]
      have h1mt : 0 ≤ 1 - t := sub_nonneg.mpr ht1
      have hmul : (1 - (r : ℝ) * t) * (1 - t) ≤ (1 - t) ^ r * (1 - t) :=
        mul_le_mul_of_nonneg_right ih h1mt
      have hsq : 0 ≤ (r : ℝ) * t ^ 2 := by positivity
      linarith

/-- Exponential-envelope upper bound on `[0, 1]`: for `0 ≤ t ≤ 1` and `r : ℕ`,
`(1 + t) ^ r ≤ 1 + (2 ^ r - 1) * t`. -/
theorem one_add_pow_le_two_pow_sub_one_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (r : ℕ) :
    (1 + t) ^ r ≤ 1 + ((2 : ℝ) ^ r - 1) * t := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ]
      have h1pt : 0 ≤ 1 + t := by linarith
      have hmul : (1 + t) ^ r * (1 + t) ≤ (1 + ((2 : ℝ) ^ r - 1) * t) * (1 + t) :=
        mul_le_mul_of_nonneg_right ih h1pt
      have h2r : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      have htsq : t ^ 2 ≤ t := by nlinarith
      have hterm : ((2 : ℝ) ^ r - 1) * t ^ 2 ≤ ((2 : ℝ) ^ r - 1) * t :=
        mul_le_mul_of_nonneg_left htsq (sub_nonneg.mpr h2r)
      have hexp : (2 : ℝ) ^ (r + 1) = 2 * (2 : ℝ) ^ r := by ring
      rw [hexp]
      linarith

/-- For every `r : ℕ`, `(r : ℝ) + 1 ≤ 2 ^ r`. -/
theorem natCast_add_one_le_two_pow (r : ℕ) :
    (r : ℝ) + 1 ≤ (2 : ℝ) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      have h2r : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      linarith

/-- For `0 ≤ s ≤ t ≤ 1` and `m : ℕ`, `s ^ (m + 1) ≤ t`. -/
theorem pow_succ_le_of_le_unit {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) (m : ℕ) :
    s ^ (m + 1) ≤ t := by
  induction m with
  | zero => simpa using hst
  | succ m ih =>
      rw [pow_succ]
      have hs1 : s ≤ 1 := hst.trans ht1
      calc
        s ^ (m + 1) * s ≤ t * 1 :=
          mul_le_mul ih hs1 hs (hs.trans hst)
        _ = t := mul_one t

/-! ## §2. Critical Nyquist Cell Discrepancy and Explicit Inverse-Square Bound -/

/-- Critical continuous mean density $c_m = \frac{(m+1)^{m+1}}{2 (m+2)!}$ at $\beta = m + 1$. -/
def nyquistCriticalConstant (m : ℕ) : ℝ :=
  nyquistWeightCellConstant ((m : ℝ) + 1) m

/-- Discrepancy scale constant $D_m = c_m 2^{m+1}$ at $\beta = m + 1$. -/
def nyquistCriticalDiscrepancyScale (m : ℕ) : ℝ :=
  nyquistCriticalConstant m * (2 : ℝ) ^ (m + 1)

/-- Critical Nyquist cell discrepancy $d_k(m) = \alpha_k(m+1, m) - c_m \delta_k$ on cell $k$. -/
def nyquistCriticalCellDiscrepancy (m k : ℕ) : ℝ :=
  nyquistWeightCellMass ((m : ℝ) + 1) m k -
    nyquistCriticalConstant m * nyquistWeightCellWidth k

theorem nyquistCriticalConstant_pos (m : ℕ) :
    0 < nyquistCriticalConstant m :=
  nyquistWeightCellConstant_pos (by positivity : 0 < (m : ℝ) + 1) m

theorem nyquistCriticalDiscrepancyScale_pos (m : ℕ) :
    0 < nyquistCriticalDiscrepancyScale m := by
  unfold nyquistCriticalDiscrepancyScale
  exact mul_pos (nyquistCriticalConstant_pos m) (by positivity)

/-- Exact factorization of the critical endpoint jet term: for `0 < n` and any `δ : ℝ`,
$$\frac{J_{m+1}(\log n) \delta^{m+2}}{(m+2)!}
  = c_m \delta \left((n \delta)^{m+1} + (-1)^{m+1} \left(\frac{\delta}{n}\right)^{m+1}\right).$$ -/
theorem nyquistCriticalJet_endpoint_identity (m : ℕ) {n : ℝ} (hn : 0 < n) (δ : ℝ) :
    nyquistWeightJet ((m : ℝ) + 1) (m + 1) (Real.log n) * δ ^ (m + 2) /
        ((m + 2).factorial : ℝ) =
      nyquistCriticalConstant m * δ *
        ((n * δ) ^ (m + 1) + (-1 : ℝ) ^ (m + 1) * (δ / n) ^ (m + 1)) := by
  rw [nyquistWeightJet_log ((m : ℝ) + 1) (m + 1) hn]
  have hcast : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  have hrpow1 : n ^ ((m : ℝ) + 1) = n ^ (m + 1) := by
    rw [hcast, Real.rpow_natCast]
  have hrpow2 : n ^ (-((m : ℝ) + 1)) = (n ^ (m + 1))⁻¹ := by
    rw [Real.rpow_neg hn.le, hrpow1]
  rw [hrpow1, hrpow2]
  unfold nyquistCriticalConstant nyquistWeightCellConstant
  have hfac : ((m + 2).factorial : ℝ) ≠ 0 := by positivity
  have hn_ne : n ^ (m + 1) ≠ 0 := pow_ne_zero (m + 1) hn.ne'
  rw [mul_pow, div_pow, pow_succ δ (m + 1)]
  field_simp [hfac, hn_ne]

/-- Lower and upper bounds on the normalized cell ratio $\alpha_k / (c_m \delta_k) - 1$. -/
theorem nyquistCriticalCellDiscrepancy_bounds (m k : ℕ) :
    -nyquistCriticalDiscrepancyScale m * nyquistWeightCellWidth k / ((k + 1 : ℕ) : ℝ) ≤
        nyquistCriticalCellDiscrepancy m k ∧
      nyquistCriticalCellDiscrepancy m k ≤
        nyquistCriticalDiscrepancyScale m * nyquistWeightCellWidth k / ((k + 1 : ℕ) : ℝ) := by
  let N : ℝ := ((k + 1 : ℕ) : ℝ)
  let t : ℝ := 1 / N
  let δ : ℝ := nyquistWeightCellWidth k
  have hN : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (by omega : 1 ≤ k + 1)
  have hNpos : 0 < N := by linarith
  have hNp1pos : 0 < N + 1 := by linarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact div_le_one_of_le₀ hN hNpos.le
  have hδbounds := nyquistWeightCellWidth_bounds k
  have hNp1_eq : ((k + 2 : ℕ) : ℝ) = N + 1 := by
    dsimp [N]
    push_cast
    ring
  have hδpos : 0 < δ := nyquistWeightCellWidth_pos k
  have hδ_le_t : δ ≤ t := hδbounds.2
  have hδ_ge : 1 / (N + 1) ≤ δ := by
    rw [← hNp1_eq]
    exact hδbounds.1
  have hNδ_ge : 1 - t ≤ N * δ := by
    have h1 : N / (N + 1) ≤ N * δ := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hδ_ge hNpos.le
    have h2 : 1 - t ≤ N / (N + 1) := by
      dsimp [t]
      rw [le_div_iff₀ hNp1pos]
      have h3 : (1 - 1 / N) * N = N - 1 := by field_simp [hNpos.ne']
      have h4 : (1 - 1 / N) * (N + 1) = (N - 1) + (1 - 1 / N) := by
        calc
          (1 - 1 / N) * (N + 1) = (1 - 1 / N) * N + (1 - 1 / N) := by ring
          _ = (N - 1) + (1 - 1 / N) := by rw [h3]
      rw [h4]
      have h1N : 0 ≤ 1 / N := by positivity
      linarith
    exact h2.trans h1
  have hNp1δ_le : (N + 1) * δ ≤ 1 + t := by
    have h1 : (N + 1) * δ ≤ (N + 1) * t :=
      mul_le_mul_of_nonneg_left hδ_le_t hNp1pos.le
    have h2 : (N + 1) * t = 1 + t := by
      dsimp [t]
      field_simp [hNpos.ne']
    rwa [h2] at h1
  have hs1_le : (δ / N) ^ (m + 1) ≤ t := by
    apply pow_succ_le_of_le_unit (by positivity) _ ht1
    calc
      δ / N ≤ δ / 1 := div_le_div_of_nonneg_left hδpos.le zero_lt_one hN
      _ = δ := div_one δ
      _ ≤ t := hδ_le_t
  have hs2_le : (δ / (N + 1)) ^ (m + 1) ≤ t := by
    apply pow_succ_le_of_le_unit (by positivity) _ ht1
    calc
      δ / (N + 1) ≤ δ / 1 := div_le_div_of_nonneg_left hδpos.le zero_lt_one (by linarith)
      _ = δ := div_one δ
      _ ≤ t := hδ_le_t
  have hmass := nyquistWeightCellMass_bounds (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1) m k
  have hnode0 : nyquistResidualNode k = Real.log N := rfl
  have hnode1 : nyquistResidualNode (k + 1) = Real.log (N + 1) := by
    unfold nyquistResidualNode
    rw [hNp1_eq]
  have hjet0 := nyquistCriticalJet_endpoint_identity m hNpos δ
  have hjet1 := nyquistCriticalJet_endpoint_identity m hNp1pos δ
  rw [← hnode0] at hjet0
  rw [← hnode1] at hjet1
  have hcpos : 0 < nyquistCriticalConstant m * δ :=
    mul_pos (nyquistCriticalConstant_pos m) hδpos
  constructor
  · -- Lower bound on d_k
    have hpow_ge : 1 - ((m + 1 : ℕ) : ℝ) * t ≤ (N * δ) ^ (m + 1) := by
      calc
        1 - ((m + 1 : ℕ) : ℝ) * t ≤ (1 - t) ^ (m + 1) :=
          one_sub_mul_le_pow_of_unit ht0 ht1 (m + 1)
        _ ≤ (N * δ) ^ (m + 1) :=
          pow_le_pow_left₀ (sub_nonneg.mpr ht1) hNδ_ge (m + 1)
    have hsign : -(δ / N) ^ (m + 1) ≤ (-1 : ℝ) ^ (m + 1) * (δ / N) ^ (m + 1) := by
      have habs : |(-1 : ℝ) ^ (m + 1) * (δ / N) ^ (m + 1)| = (δ / N) ^ (m + 1) := by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (by positivity)]
      linarith [neg_abs_le ((-1 : ℝ) ^ (m + 1) * (δ / N) ^ (m + 1))]
    have h2pow := natCast_add_one_le_two_pow (m + 1)
    have hcomb : 1 - (2 : ℝ) ^ (m + 1) * t ≤
        (N * δ) ^ (m + 1) + (-1 : ℝ) ^ (m + 1) * (δ / N) ^ (m + 1) := by
      have hmt : (((m + 1 : ℕ) : ℝ) + 1) * t ≤ (2 : ℝ) ^ (m + 1) * t :=
        mul_le_mul_of_nonneg_right h2pow ht0
      linarith
    have hlow := hmass.1
    change nyquistWeightJet ((m : ℝ) + 1) (m + 1) (nyquistResidualNode k) * δ ^ (m + 2) /
      ((m + 2).factorial : ℝ) ≤ nyquistWeightCellMass ((m : ℝ) + 1) m k at hlow
    rw [hjet0] at hlow
    have hmul := mul_le_mul_of_nonneg_left hcomb hcpos.le
    have hring :
        nyquistCriticalConstant m * δ * (1 - (2 : ℝ) ^ (m + 1) * t) =
          nyquistCriticalConstant m * δ -
            nyquistCriticalDiscrepancyScale m * δ / N := by
      unfold nyquistCriticalDiscrepancyScale
      dsimp [t]
      ring
    rw [hring] at hmul
    unfold nyquistCriticalCellDiscrepancy
    have hneg :
        -nyquistCriticalDiscrepancyScale m * δ / N =
          -(nyquistCriticalDiscrepancyScale m * δ / N) := by ring
    dsimp [N, δ] at hmul hlow hneg ⊢
    linarith
  · -- Upper bound on d_k
    have hpow_le : ((N + 1) * δ) ^ (m + 1) ≤ 1 + ((2 : ℝ) ^ (m + 1) - 1) * t := by
      calc
        ((N + 1) * δ) ^ (m + 1) ≤ (1 + t) ^ (m + 1) :=
          pow_le_pow_left₀ (by positivity) hNp1δ_le (m + 1)
        _ ≤ 1 + ((2 : ℝ) ^ (m + 1) - 1) * t :=
          one_add_pow_le_two_pow_sub_one_mul ht0 ht1 (m + 1)
    have hsign : (-1 : ℝ) ^ (m + 1) * (δ / (N + 1)) ^ (m + 1) ≤ (δ / (N + 1)) ^ (m + 1) := by
      have habs : |(-1 : ℝ) ^ (m + 1) * (δ / (N + 1)) ^ (m + 1)| = (δ / (N + 1)) ^ (m + 1) := by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (by positivity)]
      linarith [le_abs_self ((-1 : ℝ) ^ (m + 1) * (δ / (N + 1)) ^ (m + 1))]
    have hcomb :
        ((N + 1) * δ) ^ (m + 1) + (-1 : ℝ) ^ (m + 1) * (δ / (N + 1)) ^ (m + 1) ≤
          1 + (2 : ℝ) ^ (m + 1) * t := by
      linarith
    have hupp := hmass.2
    change nyquistWeightCellMass ((m : ℝ) + 1) m k ≤
      nyquistWeightJet ((m : ℝ) + 1) (m + 1) (nyquistResidualNode (k + 1)) * δ ^ (m + 2) /
        ((m + 2).factorial : ℝ) at hupp
    rw [hjet1] at hupp
    have hmul := mul_le_mul_of_nonneg_left hcomb hcpos.le
    have hring :
        nyquistCriticalConstant m * δ * (1 + (2 : ℝ) ^ (m + 1) * t) =
          nyquistCriticalConstant m * δ +
            nyquistCriticalDiscrepancyScale m * δ / N := by
      unfold nyquistCriticalDiscrepancyScale
      dsimp [t]
      ring
    rw [hring] at hmul
    unfold nyquistCriticalCellDiscrepancy
    dsimp [N, δ] at hmul hupp ⊢
    linarith

/-- **Explicit Critical Cell Discrepancy Bound (`|d_k(m)| ≤ D_m δ_k / (k+1)`):** -/
theorem abs_nyquistCriticalCellDiscrepancy_le_width_div (m k : ℕ) :
    |nyquistCriticalCellDiscrepancy m k| ≤
      nyquistCriticalDiscrepancyScale m * nyquistWeightCellWidth k / ((k + 1 : ℕ) : ℝ) := by
  have hb := nyquistCriticalCellDiscrepancy_bounds m k
  have hneg :
      -(nyquistCriticalDiscrepancyScale m * nyquistWeightCellWidth k / ((k + 1 : ℕ) : ℝ)) =
        -nyquistCriticalDiscrepancyScale m * nyquistWeightCellWidth k / ((k + 1 : ℕ) : ℝ) := by
    ring
  rw [abs_le, hneg]
  exact hb

/-- **Inverse-Square Bound on the Critical Cell Discrepancy (`|d_k(m)| ≤ D_m / (k+1)^2`):** -/
theorem abs_nyquistCriticalCellDiscrepancy_le_inv_sq (m k : ℕ) :
    |nyquistCriticalCellDiscrepancy m k| ≤
      nyquistCriticalDiscrepancyScale m * (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
  have h1 := abs_nyquistCriticalCellDiscrepancy_le_width_div m k
  have h2 := (nyquistWeightCellWidth_bounds k).2
  have hD := (nyquistCriticalDiscrepancyScale_pos m).le
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  calc
    |nyquistCriticalCellDiscrepancy m k| ≤
        nyquistCriticalDiscrepancyScale m * nyquistWeightCellWidth k / ((k + 1 : ℕ) : ℝ) := h1
    _ ≤ nyquistCriticalDiscrepancyScale m * (1 / ((k + 1 : ℕ) : ℝ)) / ((k + 1 : ℕ) : ℝ) := by
      gcongr
    _ = nyquistCriticalDiscrepancyScale m * (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
      have hrpow : (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) = 1 / (((k + 1 : ℕ) : ℝ) ^ 2) := by
        rw [Real.rpow_neg hk.le, one_div]
        norm_cast
      rw [hrpow]
      ring

/-! ## §3. Absolute Summability and Quantitative Tail Bounds for the Critical Nyquist Finite Part -/

/-- Absolute summability of the critical cell discrepancy tail starting at `N`. -/
theorem summable_abs_nyquistCriticalCellDiscrepancy_tail (m N : ℕ) :
    Summable (fun k : ℕ => |nyquistCriticalCellDiscrepancy m (N + k)|) := by
  have hmaj : Summable (fun k : ℕ =>
      nyquistCriticalDiscrepancyScale m * (((N + k + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) :=
    (summable_nyquistPowerTail (by norm_num : (-2 : ℝ) < -1) N).mul_left
      (nyquistCriticalDiscrepancyScale m)
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun k => by
      simpa only [Nat.add_assoc] using abs_nyquistCriticalCellDiscrepancy_le_inv_sq m (N + k))
    hmaj

/-- Summability of the critical cell discrepancy tail starting at `N`. -/
theorem summable_nyquistCriticalCellDiscrepancy_tail (m N : ℕ) :
    Summable (fun k : ℕ => nyquistCriticalCellDiscrepancy m (N + k)) :=
  (summable_abs_nyquistCriticalCellDiscrepancy_tail m N).of_abs

/-- Absolute summability of `nyquistCriticalCellDiscrepancy m`. -/
theorem summable_abs_nyquistCriticalCellDiscrepancy (m : ℕ) :
    Summable (fun k : ℕ => |nyquistCriticalCellDiscrepancy m k|) := by
  simpa only [Nat.zero_add] using summable_abs_nyquistCriticalCellDiscrepancy_tail m 0

/-- Summability of `nyquistCriticalCellDiscrepancy m`. -/
theorem summable_nyquistCriticalCellDiscrepancy (m : ℕ) :
    Summable (nyquistCriticalCellDiscrepancy m) :=
  (summable_abs_nyquistCriticalCellDiscrepancy m).of_abs

/-- The tail $\mathcal{B}_{m, N} = \sum_{k=0}^\infty d_{N+k}(m)$ of the Critical Nyquist Finite Part. -/
def nyquistCriticalFinitePartTail (m N : ℕ) : ℝ :=
  ∑' k : ℕ, nyquistCriticalCellDiscrepancy m (N + k)

/-- **The Critical Nyquist Finite Part** $\mathcal{B}_m = \sum_{k=0}^\infty d_k(m)$. -/
def nyquistCriticalFinitePart (m : ℕ) : ℝ :=
  nyquistCriticalFinitePartTail m 0

/-- **Quantitative Tail Bound for the Critical Nyquist Finite Part (`|B_{m, N}| ≤ 2 D_m / (N + 1)`):** -/
theorem abs_nyquistCriticalFinitePartTail_le (m N : ℕ) :
    |nyquistCriticalFinitePartTail m N| ≤
      2 * nyquistCriticalDiscrepancyScale m / ((N + 1 : ℕ) : ℝ) := by
  unfold nyquistCriticalFinitePartTail
  have hs := summable_abs_nyquistCriticalCellDiscrepancy_tail m N
  have hs_norm : Summable (fun k : ℕ => ‖nyquistCriticalCellDiscrepancy m (N + k)‖) := by
    simpa only [Real.norm_eq_abs] using hs
  have hps := summable_nyquistPowerTail (by norm_num : (-2 : ℝ) < -1) N
  have hD := (nyquistCriticalDiscrepancyScale_pos m).le
  have hN : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  calc
    |∑' k : ℕ, nyquistCriticalCellDiscrepancy m (N + k)| ≤
        ∑' k : ℕ, |nyquistCriticalCellDiscrepancy m (N + k)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs_norm
    _ ≤ ∑' k : ℕ, nyquistCriticalDiscrepancyScale m * (((N + k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) :=
      Summable.tsum_le_tsum
        (fun k => by
          simpa only [Nat.add_assoc] using abs_nyquistCriticalCellDiscrepancy_le_inv_sq m (N + k))
        hs (hps.mul_left _)
    _ = nyquistCriticalDiscrepancyScale m * nyquistPowerTail (-2) N := by
      rw [Summable.tsum_mul_left _ hps]
      rfl
    _ ≤ nyquistCriticalDiscrepancyScale m *
        ((1 + 1 / (-(-2 : ℝ) - 1)) * ((N + 1 : ℕ) : ℝ) ^ ((-2 : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (nyquistPowerTail_le (by norm_num : (-2 : ℝ) < -1) N) hD
    _ = 2 * nyquistCriticalDiscrepancyScale m / ((N + 1 : ℕ) : ℝ) := by
      have hrpow : ((N + 1 : ℕ) : ℝ) ^ ((-2 : ℝ) + 1) = 1 / ((N + 1 : ℕ) : ℝ) := by
        rw [show (-2 : ℝ) + 1 = -1 by ring, Real.rpow_neg_one, one_div]
      rw [hrpow]
      ring

/-- Global bound on the Critical Nyquist Finite Part: $|\mathcal{B}_m| \le 2 D_m$. -/
theorem abs_nyquistCriticalFinitePart_le (m : ℕ) :
    |nyquistCriticalFinitePart m| ≤ 2 * nyquistCriticalDiscrepancyScale m := by
  unfold nyquistCriticalFinitePart
  simpa using abs_nyquistCriticalFinitePartTail_le m 0

/-- Renormalized prefix primitive at logarithmic node $T_N = \log(N+1)$:
$$F_m(\log(N+1)) := \sum_{k < N} \alpha_k(m+1, m) - c_m \log(N + 1).$$ -/
def nyquistCriticalPrefixPrimitive (m N : ℕ) : ℝ :=
  nyquistWeightPrefixMass ((m : ℝ) + 1) m 0 N -
    nyquistCriticalConstant m * nyquistResidualNode N

/-- Exact telescoping identity on logarithmic nodes:
$$F_m(\log(N+1)) = \sum_{k < N} d_k(m).$$ -/
theorem nyquistCriticalPrefixPrimitive_eq_sum_discrepancy (m N : ℕ) :
    nyquistCriticalPrefixPrimitive m N =
      ∑ k ∈ Finset.range N, nyquistCriticalCellDiscrepancy m k := by
  unfold nyquistCriticalPrefixPrimitive nyquistWeightPrefixMass nyquistCriticalCellDiscrepancy
  simp only [Nat.zero_add, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hwidth := sum_nyquistWeightCellWidth 0 N
  simp only [Nat.zero_add, nyquistResidualNode_zero, sub_zero] at hwidth
  rw [hwidth]

/-- Decomposition of $\mathcal{B}_m$ into the nodal prefix primitive $F_m(\log(N+1))$ and the
tail $\mathcal{B}_{m, N}$. -/
theorem nyquistCriticalFinitePart_eq_prefix_add_tail (m N : ℕ) :
    nyquistCriticalFinitePart m =
      nyquistCriticalPrefixPrimitive m N + nyquistCriticalFinitePartTail m N := by
  unfold nyquistCriticalFinitePart nyquistCriticalFinitePartTail
  rw [nyquistCriticalPrefixPrimitive_eq_sum_discrepancy]
  simpa only [Nat.zero_add, Nat.add_comm N] using
    (Summable.sum_add_tsum_nat_add N (summable_nyquistCriticalCellDiscrepancy m)).symm

/-- **Quantitative Nodal Convergence to the Critical Nyquist Finite Part:**
$$\left|F_m(\log(N+1)) - \mathcal{B}_m\right| \le \frac{2 D_m}{N + 1}.$$ -/
theorem abs_nyquistCriticalPrefixPrimitive_sub_finitePart_le (m N : ℕ) :
    |nyquistCriticalPrefixPrimitive m N - nyquistCriticalFinitePart m| ≤
      2 * nyquistCriticalDiscrepancyScale m / ((N + 1 : ℕ) : ℝ) := by
  have heq :
      nyquistCriticalPrefixPrimitive m N - nyquistCriticalFinitePart m =
        -nyquistCriticalFinitePartTail m N := by
    linarith [nyquistCriticalFinitePart_eq_prefix_add_tail m N]
  rw [heq, abs_neg]
  exact abs_nyquistCriticalFinitePartTail_le m N

/-- The renormalized prefix primitive $F_m(\log(N+1))$ converges to $\mathcal{B}_m$ as $N \to \infty$. -/
theorem tendsto_nyquistCriticalPrefixPrimitive (m : ℕ) :
    Tendsto (nyquistCriticalPrefixPrimitive m) atTop (𝓝 (nyquistCriticalFinitePart m)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm' (a := fun N : ℕ =>
      2 * nyquistCriticalDiscrepancyScale m / ((N + 1 : ℕ) : ℝ))
  · exact Eventually.of_forall fun N => by
      rw [Real.norm_eq_abs]
      exact abs_nyquistCriticalPrefixPrimitive_sub_finitePart_le m N
  · have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (2 * nyquistCriticalDiscrepancyScale m)
    simpa only [Nat.cast_add, Nat.cast_one, mul_one_div, mul_zero] using h1

/-! ## §4. Autocorrelation Total Mass Identity and Signed Cancellation Witness -/

/-- **Autocorrelation Total Mass Identity (`∫ ℝ, autocorr f x = (∫ ℝ, f u)^2`):**
For any compactly supported continuous source $f \in C_c(\mathbb{R}, \mathbb{R})$, the total
integral of its autocorrelation equals the square of the source mean. -/
theorem integral_autocorr_eq_sq_integral (f : C_c(ℝ, ℝ)) :
    (∫ x, autocorr f x) = (∫ u, f u) ^ 2 := by
  have hf : Integrable (f : ℝ → ℝ) volume :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hf_neg : Integrable (fun u : ℝ => f (-u)) volume := hf.comp_neg
  have hconv :
      ∀ x : ℝ, autocorr f x =
        (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun u => f (-u))) (-x) := by
    intro x
    unfold autocorr convolution
    simp only [ContinuousLinearMap.mul_apply']
    congr 1
    funext u
    congr 1
    congr 1
    ring
  simp_rw [hconv]
  rw [integral_neg_eq_self]
  have hmul := integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf hf_neg
  simp only [ContinuousLinearMap.mul_apply', integral_neg_eq_self] at hmul
  rw [hmul, sq]

/-- Shifted two-copy difference source $g_{f, T}(u) := f(u) - f(u - T)$. -/
def shiftedCopyDifference (f : ℝ → ℝ) (T u : ℝ) : ℝ :=
  f u - f (u - T)

/-- For any integrable $f$ and shift $T$, `shiftedCopyDifference f T` has exact zero mean:
$$\int_{\mathbb{R}} (f(u) - f(u - T))\,du = 0.$$ -/
theorem integral_shiftedCopyDifference_eq_zero {f : ℝ → ℝ} (hf : Integrable f) (T : ℝ) :
    (∫ u, shiftedCopyDifference f T u) = 0 := by
  unfold shiftedCopyDifference
  have hfT : Integrable (fun u => f (u - T)) := hf.comp_sub_right T
  rw [integral_sub hf hfT, integral_sub_right_eq_self f T, sub_self]

/-- Exact 3-lag autocorrelation expansion of `shiftedCopyDifference f T`:
$$\operatorname{autocorr}(f - \tau_T f, x)
  = 2 \operatorname{autocorr}(f, x) - \operatorname{autocorr}(f, x - T) - \operatorname{autocorr}(f, x + T).$$ -/
theorem autocorr_shiftedCopyDifference {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f) (T x : ℝ) :
    autocorr (shiftedCopyDifference f T) x =
      2 * autocorr f x - autocorr f (x - T) - autocorr f (x + T) := by
  have h00 : Integrable (fun u => f u * f (u + x)) :=
    (hf.mul (hf.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hfc.mul_right
  have h01 : Integrable (fun u => f u * f (u + x - T)) :=
    (hf.mul (hf.comp ((continuous_id.add continuous_const).sub continuous_const))).integrable_of_hasCompactSupport
      hfc.mul_right
  have h10 : Integrable (fun u => f (u - T) * f (u + x)) := by
    have hc : HasCompactSupport (fun u => f (u - T)) :=
      hfc.comp_homeomorph (Homeomorph.subRight T)
    exact ((hf.comp (continuous_id.sub continuous_const)).mul
      (hf.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport hc.mul_right
  have h11 : Integrable (fun u => f (u - T) * f (u + x - T)) := by
    have hc : HasCompactSupport (fun u => f (u - T)) :=
      hfc.comp_homeomorph (Homeomorph.subRight T)
    exact ((hf.comp (continuous_id.sub continuous_const)).mul
      (hf.comp ((continuous_id.add continuous_const).sub continuous_const))).integrable_of_hasCompactSupport
        hc.mul_right
  have hexpand :
      (fun u => shiftedCopyDifference f T u * shiftedCopyDifference f T (u + x)) =
        fun u => ((f u * f (u + x) + f (u - T) * f (u + x - T)) - f u * f (u + x - T)) -
          f (u - T) * f (u + x) := by
    ext u
    unfold shiftedCopyDifference
    ring
  unfold autocorr
  rw [hexpand]
  have hA : Integrable (fun u => f u * f (u + x) + f (u - T) * f (u + x - T)) := h00.add h11
  have hB : Integrable (fun u =>
      (f u * f (u + x) + f (u - T) * f (u + x - T)) - f u * f (u + x - T)) := hA.sub h01
  rw [integral_sub hB h10, integral_sub hA h01, integral_add h00 h11]
  have hi11 : (∫ u, f (u - T) * f (u + x - T)) = ∫ u, f u * f (u + x) := by
    have hshift := integral_sub_right_eq_self (μ := volume) (fun u => f u * f (u + x)) T
    simpa only [add_sub_right_comm] using hshift
  have hi01 : (∫ u, f u * f (u + x - T)) = ∫ u, f u * f (u + (x - T)) := by
    congr 1; ext u; ring_nf
  have hi10 : (∫ u, f (u - T) * f (u + x)) = ∫ u, f u * f (u + (x + T)) := by
    have hshift := integral_sub_right_eq_self (μ := volume) (fun u => f u * f (u + (x + T))) T
    have heq : (fun u => f (u - T) * f (u - T + (x + T))) = (fun u => f (u - T) * f (u + x)) := by
      ext u; congr 2; ring
    rw [heq] at hshift
    exact hshift
  rw [hi11, hi01, hi10]
  ring

/-- **Negative Correlation Witness at the Separating Lag (`H_g(T) = -1/2`):**
Whenever `autocorr f T = 0` and `autocorr f (2 * T) = 0`, the shifted difference
$g = f - \tau_T f$ has $\operatorname{autocorr}(g, 0) = 2 \operatorname{autocorr}(f, 0)$ and
$\operatorname{autocorr}(g, T) = -\operatorname{autocorr}(f, 0)$. -/
theorem autocorr_shiftedCopyDifference_at_zero_and_shift {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f) {T : ℝ}
    (hT : autocorr f T = 0) (h2T : autocorr f (2 * T) = 0) :
    autocorr (shiftedCopyDifference f T) 0 = 2 * autocorr f 0 ∧
      autocorr (shiftedCopyDifference f T) T = -autocorr f 0 := by
  have heven : autocorr f (-T) = 0 := by
    rw [autocorr_neg f T, hT]
  constructor
  · rw [autocorr_shiftedCopyDifference hfc hf T 0, zero_sub, zero_add, heven, hT]
    ring
  · rw [autocorr_shiftedCopyDifference hfc hf T T, sub_self, ← two_mul, hT, h2T]
    ring

/-- The concrete smooth compactly supported zero-mean witness
$g(u) = \operatorname{nyquistWideBump}(u) - \operatorname{nyquistWideBump}(u - 4)$. -/
def nyquistZeroMeanWitness : C_c(ℝ, ℝ) :=
  ⟨⟨shiftedCopyDifference (nyquistWideBump : ℝ → ℝ) 4,
      nyquistWideBump.continuous.sub
        (nyquistWideBump.continuous.comp (continuous_id.sub continuous_const))⟩,
    nyquistWideBump.hasCompactSupport.sub
      (nyquistWideBump.hasCompactSupport.comp_homeomorph (Homeomorph.subRight 4))⟩

/-- `nyquistZeroMeanWitness` has exact zero source integral and zero total autocorrelation mass,
contrasting with the positive-mean `nyquistWideBump` family whose critical residual escapes to $+\infty$. -/
theorem nyquistZeroMeanWitness_integral_and_autocorr_mass_eq_zero :
    (∫ u, nyquistZeroMeanWitness u) = 0 ∧
      (∫ x, autocorr nyquistZeroMeanWitness x) = 0 := by
  have hint : (∫ u, nyquistZeroMeanWitness u) = 0 :=
    integral_shiftedCopyDifference_eq_zero
      (nyquistWideBump.continuous.integrable_of_hasCompactSupport
        nyquistWideBump.hasCompactSupport) 4
  refine ⟨hint, ?_⟩
  rw [integral_autocorr_eq_sq_integral nyquistZeroMeanWitness, hint, sq, mul_zero]

end GaloisForLFunctions.BiScaleUncertainty

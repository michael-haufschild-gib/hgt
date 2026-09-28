import GaloisForLFunctions.RHTower.WeilPositivityConductorObstruction
import GaloisForLFunctions.HTGeometry.DigammaAsymptotic
import GaloisForLFunctions.RHTower.DigammaVerticalMinimum

/-!
# Weil positivity bounds the multiplicative Toeplitz matrix of the prime weights

Let `lam : ℕ → ℝ` be a weight system for which the finite-atom Weil symbol (with the archimedean
term of `ζ`) is nonnegative on every polar-constrained `C²` test at every level.  Then the
multiplicative Toeplitz form of `lam(n) n^{-1/2}` is bounded by the archimedean symbol at the
Nyquist scale:

**Theorem** (`weil_multiplicativeToeplitz_bound`).  There is an absolute constant `C₀` such that
for every `N ≥ 1` and every `c` supported in `[1, N]`,
`2 ∑_{2 ≤ n ≤ N} lam(n) n^{-1/2} Re ∑_m c(nm) conj(c(m)) ≤ (log N + C₀) ∑_m |c(m)|²`.

The tests are resonators: narrow polar-free bumps `g_w(x - log m)` of width `w = 1/(N+1)`,
`g_w = ψ_w'' - ψ_w/4` with `ψ_w(x) = ψ(x/w)`.  Distinct logarithms of integers `≤ N` are
`1/(N+1)` apart, so the autocorrelation of the resonator meets the atom `log n` exactly on the
multiplicative diagonal `m = n m'`; the archimedean symbol is at most `log(1/w) + O(1)` on the
spectrum of the bumps, where `O(1)` is controlled by the scale-free ratio `w² ‖g_w'‖² / ‖g_w‖²`.

**Corollaries.**
* `weil_twisted_density_bound`: for every completely multiplicative unimodular `χ`,
  `2 ∑_{nm ≤ N, n ≥ 2} lam(n) Re χ(n)/(nm) ≤ (log N + C₀) ∑_{m ≤ N} 1/m`.
* `weil_log_density_le`: `∑_{nm ≤ N, n ≥ 2} lam(n)/(nm) ≤ (1/2 + ε)(log N)²` for large `N`.  In the
  logarithmic mean `∑_{k ≤ N}(lam ⋆ 1)(k)/k` a Weil-positive weight system has density at most
  one, the density of `Λ`, for which `∑_{k ≤ N} log k / k = (log N)²/2 + O(1)`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23
open ComplexConjugate

namespace RHTower

noncomputable section

namespace ResonatorProfile

/-- The unit profile: the smooth bump `weilBump`, equal to `1` near `0` and supported in
`(-1/4, 1/4)`. -/
def Ψ (v : ℝ) : ℝ := weilBump v

def d1 : ℝ → ℝ := deriv Ψ
def d2 : ℝ → ℝ := deriv d1
def d3 : ℝ → ℝ := deriv d2

theorem contDiff_Ψ (n : ℕ) : ContDiff ℝ n Ψ := weilBump.contDiff

theorem contDiff_d1 (n : ℕ) : ContDiff ℝ n d1 := (contDiff_Ψ (n + 1)).deriv'

theorem contDiff_d2 (n : ℕ) : ContDiff ℝ n d2 := (contDiff_d1 (n + 1)).deriv'

theorem contDiff_d3 (n : ℕ) : ContDiff ℝ n d3 := (contDiff_d2 (n + 1)).deriv'

theorem Ψ_eq_zero {v : ℝ} (hv : 1 / 4 ≤ |v|) : Ψ v = 0 := by
  have h : v ∉ Function.support (weilBump : ℝ → ℝ) := by
    rw [weilBump.support_eq]
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
    exact hv
  exact Function.notMem_support.mp h

theorem Ψ_zero : Ψ 0 = 1 :=
  weilBump.one_of_mem_closedBall (Metric.mem_closedBall_self weilBump.rIn_pos.le)

/-- A function vanishing on `|v| ≥ r` has derivative vanishing on `|v| > r`. -/
theorem deriv_eq_zero_of_eq_zero {F : ℝ → ℝ} {r : ℝ} (hF : ∀ v, r ≤ |v| → F v = 0) {v : ℝ}
    (hv : r < |v|) : deriv F v = 0 := by
  have hev : F =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
    have hopen : IsOpen {x : ℝ | r < |x|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hv] with x hx
    exact hF x (le_of_lt hx)
  rw [hev.deriv_eq]; simp

theorem d1_eq_zero {v : ℝ} (hv : 1 / 4 < |v|) : d1 v = 0 :=
  deriv_eq_zero_of_eq_zero (fun _ h => Ψ_eq_zero h) hv

theorem d2_eq_zero {v : ℝ} (hv : 1 / 4 < |v|) : d2 v = 0 := by
  have hopen : IsOpen {x : ℝ | 1 / 4 < |x|} := isOpen_lt continuous_const continuous_abs
  have hev : d1 =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hv] with x hx
    exact d1_eq_zero hx
  show deriv d1 v = 0
  rw [hev.deriv_eq]; simp

theorem d3_eq_zero {v : ℝ} (hv : 1 / 4 < |v|) : d3 v = 0 := by
  have hopen : IsOpen {x : ℝ | 1 / 4 < |x|} := isOpen_lt continuous_const continuous_abs
  have hev : d2 =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hv] with x hx
    exact d2_eq_zero hx
  show deriv d2 v = 0
  rw [hev.deriv_eq]; simp

theorem hasCompactSupport_of_vanish {F : ℝ → ℝ} (hF : ∀ v, 1 / 4 < |v| → F v = 0) :
    HasCompactSupport F :=
  hasCompactSupport_of_support_subset_abs (Λ := 1 / 4) fun v hv => by
    by_contra h; push Not at h; exact hv (hF v h)

theorem hasCompactSupport_Ψ : HasCompactSupport Ψ :=
  hasCompactSupport_of_vanish fun _ h => Ψ_eq_zero h.le

theorem hasCompactSupport_d1 : HasCompactSupport d1 :=
  hasCompactSupport_of_vanish fun _ h => d1_eq_zero h

theorem hasCompactSupport_d2 : HasCompactSupport d2 :=
  hasCompactSupport_of_vanish fun _ h => d2_eq_zero h

theorem hasCompactSupport_d3 : HasCompactSupport d3 :=
  hasCompactSupport_of_vanish fun _ h => d3_eq_zero h

/-- Integration by parts: `∫ Ψ'' Ψ = -∫ (Ψ')²`. -/
theorem integral_d2_mul_Ψ : ∫ v, d2 v * Ψ v = -∫ v, d1 v * d1 v := by
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := Ψ) (v := d1) (u' := d1)
    (v' := d2)
    (fun x _ => ((contDiff_Ψ 1).differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => ((contDiff_d1 1).differentiable (by norm_num) x).hasDerivAt)
    (((contDiff_Ψ 0).continuous.mul (contDiff_d2 0).continuous).integrable_of_hasCompactSupport
      hasCompactSupport_Ψ.mul_right)
    (((contDiff_d1 0).continuous.mul (contDiff_d1 0).continuous).integrable_of_hasCompactSupport
      hasCompactSupport_d1.mul_right)
    (((contDiff_Ψ 0).continuous.mul (contDiff_d1 0).continuous).integrable_of_hasCompactSupport
      hasCompactSupport_Ψ.mul_right)
  rw [show (fun v => d2 v * Ψ v) = fun v => Ψ v * d2 v by funext v; ring, key]

theorem integral_d2_sq_pos : 0 < ∫ v, d2 v ^ 2 := by
  have hc : Continuous fun v => d2 v ^ 2 := (contDiff_d2 0).continuous.pow 2
  by_contra hle
  push Not at hle
  have hnn : ∀ v, 0 ≤ d2 v ^ 2 := fun v => sq_nonneg _
  have hint : Integrable fun v => d2 v ^ 2 :=
    hc.integrable_of_hasCompactSupport (hasCompactSupport_d2.comp_left (g := fun x : ℝ => x ^ 2) (by simp))
  have hzero : ∫ v, d2 v ^ 2 = 0 := le_antisymm hle (integral_nonneg hnn)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp hzero
  have hall : ∀ v, d2 v ^ 2 = 0 := by
    intro v
    exact congrFun (hc.ae_eq_iff_eq volume continuous_const |>.mp hae) v
  have hd2 : ∀ v, d2 v = 0 := fun v => pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hall v)
  -- `d1` is constant, hence zero
  have hd1c : ∀ x y, d1 x = d1 y := fun x y =>
    is_const_of_deriv_eq_zero ((contDiff_d1 1).differentiable (by norm_num)) (fun v => hd2 v) x y
  have hd1 : ∀ v, d1 v = 0 := fun v => by rw [hd1c v 1]; exact d1_eq_zero (by norm_num)
  have hΨc : ∀ x y, Ψ x = Ψ y := fun x y =>
    is_const_of_deriv_eq_zero ((contDiff_Ψ 1).differentiable (by norm_num)) (fun v => hd1 v) x y
  have h1 := hΨc 0 1
  rw [Ψ_zero, Ψ_eq_zero (by norm_num)] at h1
  norm_num at h1

/-! ### The profile at width `w` -/

theorem hasDerivAt_comp_div {F : ℝ → ℝ} (hF : Differentiable ℝ F) (w u : ℝ) :
    HasDerivAt (fun x => F (x / w)) (deriv F (u / w) / w) u := by
  have h1 : HasDerivAt (fun x : ℝ => x / w) (1 / w) u := (hasDerivAt_id u).div_const w
  have h2 := (hF (u / w)).hasDerivAt.comp u h1
  have e : deriv F (u / w) / w = deriv F (u / w) * (1 / w) := by ring
  rw [e]; exact h2

theorem hasDerivAt_ofReal_comp_div {F : ℝ → ℝ} (hF : Differentiable ℝ F) (w u : ℝ) :
    HasDerivAt (fun x => ((F (x / w) : ℝ) : ℂ)) (((deriv F (u / w) / w : ℝ) : ℂ)) u :=
  (hasDerivAt_comp_div hF w u).ofReal_comp

/-- The profile at width `w`, as a complex function. -/
def ψC (w u : ℝ) : ℂ := ((Ψ (u / w) : ℝ) : ℂ)

/-- The polar-free profile `ψ_w'' - ψ_w/4`, written out. -/
def gR (w u : ℝ) : ℝ := d2 (u / w) / w ^ 2 - Ψ (u / w) / 4

/-- Its derivative, written out. -/
def gR' (w u : ℝ) : ℝ := d3 (u / w) / w ^ 3 - d1 (u / w) / (4 * w)

def gC (w u : ℝ) : ℂ := ((gR w u : ℝ) : ℂ)

theorem differentiable_Ψ : Differentiable ℝ Ψ := (contDiff_Ψ 1).differentiable (by norm_num)
theorem differentiable_d1 : Differentiable ℝ d1 := (contDiff_d1 1).differentiable (by norm_num)
theorem differentiable_d2 : Differentiable ℝ d2 := (contDiff_d2 1).differentiable (by norm_num)

theorem deriv_ψC (w : ℝ) : deriv (ψC w) = fun u => ((d1 (u / w) / w : ℝ) : ℂ) := by
  funext u; exact (hasDerivAt_ofReal_comp_div differentiable_Ψ w u).deriv

theorem deriv_deriv_ψC (w : ℝ) :
    deriv (deriv (ψC w)) = fun u => ((d2 (u / w) / w ^ 2 : ℝ) : ℂ) := by
  rw [deriv_ψC]
  funext u
  have h := (hasDerivAt_ofReal_comp_div differentiable_d1 w u).div_const (w : ℂ)
  have e : (fun x => ((d1 (x / w) / w : ℝ) : ℂ)) = fun x => ((d1 (x / w) : ℝ) : ℂ) / (w : ℂ) := by
    funext x; push_cast; ring
  rw [e, h.deriv]
  show ((deriv d1 (u / w) / w : ℝ) : ℂ) / (w : ℂ) = ((d2 (u / w) / w ^ 2 : ℝ) : ℂ)
  push_cast; rw [show deriv d1 = d2 from rfl]; ring

theorem gC_eq (w : ℝ) : gC w = fun u => deriv (deriv (ψC w)) u - ψC w u / 4 := by
  rw [deriv_deriv_ψC]; funext u; simp [gC, gR, ψC]

theorem hasDerivAt_gR (w u : ℝ) : HasDerivAt (gR w) (gR' w u) u := by
  have h2 := (hasDerivAt_comp_div differentiable_d2 w u).div_const (w ^ 2)
  have h0 := (hasDerivAt_comp_div differentiable_Ψ w u).div_const 4
  have h := h2.sub h0
  have hv : deriv d2 (u / w) / w / w ^ 2 - deriv Ψ (u / w) / w / 4 = gR' w u := by
    unfold gR'; rw [show deriv d2 = d3 from rfl, show deriv Ψ = d1 from rfl]
    rcases eq_or_ne w 0 with hw | hw
    · subst hw; simp
    · field_simp
  rw [hv] at h
  exact h

theorem deriv_gC (w : ℝ) : deriv (gC w) = fun u => ((gR' w u : ℝ) : ℂ) := by
  funext u; exact (hasDerivAt_gR w u).ofReal_comp.deriv

theorem contDiff_gR (w : ℝ) (n : ℕ) : ContDiff ℝ n (gR w) := by
  unfold gR
  exact (((contDiff_d2 n).comp (contDiff_id.div_const w)).div_const _).sub
    (((contDiff_Ψ n).comp (contDiff_id.div_const w)).div_const _)

theorem contDiff_gR' (w : ℝ) (n : ℕ) : ContDiff ℝ n (gR' w) := by
  unfold gR'
  exact (((contDiff_d3 n).comp (contDiff_id.div_const w)).div_const _).sub
    (((contDiff_d1 n).comp (contDiff_id.div_const w)).div_const _)

theorem contDiff_gC (w : ℝ) (n : ℕ) : ContDiff ℝ n (gC w) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_gR w n)

theorem contDiff_deriv_gC (w : ℝ) (n : ℕ) : ContDiff ℝ n (deriv (gC w)) := by
  rw [deriv_gC]; exact Complex.ofRealCLM.contDiff.comp (contDiff_gR' w n)

theorem contDiff_ψC (w : ℝ) (n : ℕ) : ContDiff ℝ n (ψC w) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_Ψ n).comp (contDiff_id.div_const w))

theorem abs_div_gt {w u : ℝ} (hw : 0 < w) (hu : w / 4 < |u|) : 1 / 4 < |u / w| := by
  rw [abs_div, abs_of_pos hw, lt_div_iff₀ hw]; linarith

theorem gR_eq_zero {w u : ℝ} (hw : 0 < w) (hu : w / 4 < |u|) : gR w u = 0 := by
  have h := abs_div_gt hw hu
  simp [gR, d2_eq_zero h, Ψ_eq_zero h.le]

theorem gR'_eq_zero {w u : ℝ} (hw : 0 < w) (hu : w / 4 < |u|) : gR' w u = 0 := by
  have h := abs_div_gt hw hu
  simp [gR', d3_eq_zero h, d1_eq_zero h]

theorem hasCompactSupport_ψC {w : ℝ} (hw : 0 < w) : HasCompactSupport (ψC w) :=
  hasCompactSupport_of_support_subset_abs (Λ := w / 4) fun u hu => by
    by_contra h; push Not at h
    exact hu (by simp [ψC, Ψ_eq_zero (abs_div_gt hw h).le])

/-- **Polar-free.** `ĝ_w(z) = -(z² + 1/4) ψ̂_w(z)`. -/
theorem paperFT_gC {w : ℝ} (hw : 0 < w) (z : ℂ) :
    paperFT (gC w) z = -(z ^ 2 + 1 / 4) * paperFT (ψC w) z := by
  have hc2 := contDiff_ψC w 2
  have hcs := hasCompactSupport_ψC hw
  have hdd := paperFT_deriv_deriv hc2 hcs z
  have hc0 : Continuous (deriv (deriv (ψC w))) := by
    rw [deriv_deriv_ψC]; exact Complex.continuous_ofReal.comp
      (((contDiff_d2 0).continuous.comp (continuous_id.div_const w)).div_const _)
  have hi1 : Integrable
      (fun u : ℝ => deriv (deriv (ψC w)) u * Complex.exp (I * z * u)) :=
    (hc0.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.deriv.deriv.mul_right
  have hi0 : Integrable (fun u : ℝ => ψC w u * Complex.exp (I * z * u)) :=
    (hc2.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have hi2 : Integrable (fun u : ℝ => ψC w u / 4 * Complex.exp (I * z * u)) :=
    (hi0.div_const 4).congr (Eventually.of_forall fun u => by simp only; ring)
  unfold paperFT at hdd ⊢
  rw [gC_eq]
  simp only [sub_mul]
  rw [integral_sub hi1 hi2, hdd]
  have : ∫ u : ℝ, ψC w u / 4 * Complex.exp (I * z * u) =
      (∫ u : ℝ, ψC w u * Complex.exp (I * z * u)) / 4 := by
    rw [← integral_div]; congr 1; funext u; ring
  rw [this]; ring

theorem paperFT_gC_pole {w : ℝ} (hw : 0 < w) : paperFT (gC w) (I / 2) = 0 ∧
    paperFT (gC w) (-(I / 2)) = 0 := by
  have h1 : (I / 2) ^ 2 + 1 / 4 = 0 := by ring_nf; rw [I_sq]; ring
  have h2 : (-(I / 2)) ^ 2 + 1 / 4 = 0 := by ring_nf; rw [I_sq]; ring
  exact ⟨by rw [paperFT_gC hw, h1]; ring, by rw [paperFT_gC hw, h2]; ring⟩

/-! ### Scaling of the `L²` masses -/

theorem integral_sq_comp_div (F : ℝ → ℝ) {w : ℝ} (hw : 0 < w) :
    ∫ u, F (u / w) ^ 2 = w * ∫ v, F v ^ 2 := by
  have := Measure.integral_comp_div (fun v => F v ^ 2) w
  rw [this, abs_of_pos hw, smul_eq_mul]

theorem integrable_of_cs {F : ℝ → ℝ} (hc : Continuous F) (hs : HasCompactSupport F) :
    Integrable F := hc.integrable_of_hasCompactSupport hs

theorem integral_gR_sq_ge {w : ℝ} (hw : 0 < w) :
    (∫ v, d2 v ^ 2) / w ^ 3 ≤ ∫ u, gR w u ^ 2 := by
  set ε := w ^ 2 / 4 with hε
  have hpt : ∀ u, gR w u ^ 2 = (d2 (u / w) - ε * Ψ (u / w)) ^ 2 / w ^ 4 := by
    intro u; simp only [gR, hε]; field_simp
  have hc2 := (contDiff_d2 0).continuous
  have hcΨ := (contDiff_Ψ 0).continuous
  have hc1 := (contDiff_d1 0).continuous
  have i22 : Integrable fun v => d2 v ^ 2 :=
    integrable_of_cs (hc2.pow 2) (hasCompactSupport_d2.comp_left (g := fun x : ℝ => x ^ 2) (by simp))
  have i2Ψ : Integrable fun v => d2 v * Ψ v :=
    integrable_of_cs (hc2.mul hcΨ) hasCompactSupport_Ψ.mul_left
  have iΨΨ : Integrable fun v => Ψ v ^ 2 :=
    integrable_of_cs (hcΨ.pow 2) (hasCompactSupport_Ψ.comp_left (g := fun x : ℝ => x ^ 2) (by simp))
  have hexp : ∫ v, (d2 v - ε * Ψ v) ^ 2 =
      (∫ v, d2 v ^ 2) + 2 * ε * (∫ v, d1 v * d1 v) + ε ^ 2 * ∫ v, Ψ v ^ 2 := by
    have e : (fun v => (d2 v - ε * Ψ v) ^ 2) =
        fun v => d2 v ^ 2 - 2 * ε * (d2 v * Ψ v) + ε ^ 2 * Ψ v ^ 2 := by funext v; ring
    rw [e, integral_add (f := fun v => d2 v ^ 2 - 2 * ε * (d2 v * Ψ v))
      (g := fun v => ε ^ 2 * Ψ v ^ 2) (i22.sub (i2Ψ.const_mul _)) (iΨΨ.const_mul _),
      integral_sub (f := fun v => d2 v ^ 2) (g := fun v => 2 * ε * (d2 v * Ψ v)) i22
        (i2Ψ.const_mul _), integral_const_mul, integral_const_mul, integral_d2_mul_Ψ]
    ring
  have hnn1 : 0 ≤ ∫ v, d1 v * d1 v := integral_nonneg fun v => mul_self_nonneg _
  have hnnΨ : 0 ≤ ∫ v, Ψ v ^ 2 := integral_nonneg fun v => sq_nonneg _
  have hεpos : 0 ≤ ε := by positivity
  have hscale : ∫ u, gR w u ^ 2 = w * (∫ v, (d2 v - ε * Ψ v) ^ 2) / w ^ 4 := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_div]
    rw [integral_sq_comp_div (fun v => d2 v - ε * Ψ v) hw]
  rw [hscale, hexp]
  have hw4 : (0 : ℝ) < w ^ 4 := by positivity
  have hw3 : (0 : ℝ) < w ^ 3 := by positivity
  rw [div_le_div_iff₀ hw3 hw4]
  have h0 : 0 ≤ 2 * ε * (∫ v, d1 v * d1 v) + ε ^ 2 * ∫ v, Ψ v ^ 2 := by positivity
  have : w * ((∫ v, d2 v ^ 2) + 2 * ε * (∫ v, d1 v * d1 v) + ε ^ 2 * ∫ v, Ψ v ^ 2) * w ^ 3 =
      (∫ v, d2 v ^ 2) * w ^ 4 + (2 * ε * (∫ v, d1 v * d1 v) + ε ^ 2 * ∫ v, Ψ v ^ 2) * w ^ 4 := by
    ring
  rw [this]
  nlinarith

theorem integral_gR'_sq_le {w : ℝ} (hw : 0 < w) :
    ∫ u, gR' w u ^ 2 ≤ 2 * (∫ v, d3 v ^ 2) / w ^ 5 + (∫ v, d1 v ^ 2) / (8 * w) := by
  have hc3 := (contDiff_d3 0).continuous
  have hc1 := (contDiff_d1 0).continuous
  have i33 : Integrable fun v => d3 v ^ 2 :=
    integrable_of_cs (hc3.pow 2) (hasCompactSupport_d3.comp_left (g := fun x : ℝ => x ^ 2) (by simp))
  have i11 : Integrable fun v => d1 v ^ 2 :=
    integrable_of_cs (hc1.pow 2) (hasCompactSupport_d1.comp_left (g := fun x : ℝ => x ^ 2) (by simp))
  have hle : ∀ u, gR' w u ^ 2 ≤ 2 / w ^ 6 * d3 (u / w) ^ 2 + 1 / (8 * w ^ 2) * d1 (u / w) ^ 2 := by
    intro u
    unfold gR'
    have hw3 : (0 : ℝ) < w ^ 3 := by positivity
    set a := d3 (u / w); set b := d1 (u / w)
    have : (a / w ^ 3 - b / (4 * w)) ^ 2 ≤ 2 * (a / w ^ 3) ^ 2 + 2 * (b / (4 * w)) ^ 2 := by
      nlinarith [sq_nonneg (a / w ^ 3 + b / (4 * w))]
    calc (a / w ^ 3 - b / (4 * w)) ^ 2 ≤ 2 * (a / w ^ 3) ^ 2 + 2 * (b / (4 * w)) ^ 2 := this
      _ = 2 / w ^ 6 * a ^ 2 + 1 / (8 * w ^ 2) * b ^ 2 := by field_simp; ring
  have j3 : Integrable fun u => d3 (u / w) ^ 2 := by
    have := (i33.comp_div (ne_of_gt hw)); simpa using this
  have j1 : Integrable fun u => d1 (u / w) ^ 2 := by
    have := (i11.comp_div (ne_of_gt hw)); simpa using this
  have hint : Integrable fun u => gR' w u ^ 2 :=
    integrable_of_cs ((contDiff_gR' w 0).continuous.pow 2)
      (hasCompactSupport_of_support_subset_abs (Λ := w / 4) fun u hu => by
        by_contra h; push Not at h; exact hu (by simp [gR'_eq_zero hw h]))
  calc ∫ u, gR' w u ^ 2 ≤ ∫ u, (2 / w ^ 6 * d3 (u / w) ^ 2 + 1 / (8 * w ^ 2) * d1 (u / w) ^ 2) :=
        integral_mono hint ((j3.const_mul _).add (j1.const_mul _)) hle
    _ = 2 / w ^ 6 * (w * ∫ v, d3 v ^ 2) + 1 / (8 * w ^ 2) * (w * ∫ v, d1 v ^ 2) := by
        rw [integral_add (j3.const_mul _) (j1.const_mul _), integral_const_mul, integral_const_mul,
          integral_sq_comp_div d3 hw, integral_sq_comp_div d1 hw]
    _ = 2 * (∫ v, d3 v ^ 2) / w ^ 5 + (∫ v, d1 v ^ 2) / (8 * w) := by field_simp

/-- The profile constant `K = (2‖ψ⁽³⁾‖² + ‖ψ'‖²)/‖ψ''‖²`. -/
def profileRatio : ℝ := (2 * (∫ v, d3 v ^ 2) + ∫ v, d1 v ^ 2) / ∫ v, d2 v ^ 2

theorem profileRatio_nonneg : 0 ≤ profileRatio := by
  unfold profileRatio
  have := integral_d2_sq_pos
  have h3 : 0 ≤ ∫ v, d3 v ^ 2 := integral_nonneg fun v => sq_nonneg _
  have h1 : 0 ≤ ∫ v, d1 v ^ 2 := integral_nonneg fun v => sq_nonneg _
  positivity

/-- **Scaling law.** For `0 < w ≤ 1`: `w² ∫ (g_w')² ≤ K ∫ g_w²`. -/
theorem sq_mul_integral_gR'_le {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    w ^ 2 * ∫ u, gR' w u ^ 2 ≤ profileRatio * ∫ u, gR w u ^ 2 := by
  have hup := integral_gR'_sq_le hw
  have hlo := integral_gR_sq_ge hw
  have hpos := integral_d2_sq_pos
  have h3 : 0 ≤ ∫ v, d3 v ^ 2 := integral_nonneg fun v => sq_nonneg _
  have h1 : 0 ≤ ∫ v, d1 v ^ 2 := integral_nonneg fun v => sq_nonneg _
  have hw3 : 0 < w ^ 3 := by positivity
  have step1 : w ^ 2 * ∫ u, gR' w u ^ 2 ≤ (2 * (∫ v, d3 v ^ 2) + ∫ v, d1 v ^ 2) / w ^ 3 := by
    calc w ^ 2 * ∫ u, gR' w u ^ 2
        ≤ w ^ 2 * (2 * (∫ v, d3 v ^ 2) / w ^ 5 + (∫ v, d1 v ^ 2) / (8 * w)) :=
          mul_le_mul_of_nonneg_left hup (by positivity)
      _ = 2 * (∫ v, d3 v ^ 2) / w ^ 3 + w * (∫ v, d1 v ^ 2) / 8 := by field_simp
      _ ≤ (2 * (∫ v, d3 v ^ 2) + ∫ v, d1 v ^ 2) / w ^ 3 := by
          rw [add_div]
          have : w * (∫ v, d1 v ^ 2) / 8 ≤ (∫ v, d1 v ^ 2) / w ^ 3 := by
            rw [div_le_div_iff₀ (by norm_num) hw3]
            have hw4 : w ^ 4 ≤ 8 := by
              calc w ^ 4 ≤ 1 := pow_le_one₀ hw.le hw1
                _ ≤ 8 := by norm_num
            nlinarith
          linarith
  have step2 : (2 * (∫ v, d3 v ^ 2) + ∫ v, d1 v ^ 2) / w ^ 3 ≤ profileRatio * ∫ u, gR w u ^ 2 := by
    unfold profileRatio
    calc (2 * (∫ v, d3 v ^ 2) + ∫ v, d1 v ^ 2) / w ^ 3
        = (2 * (∫ v, d3 v ^ 2) + ∫ v, d1 v ^ 2) / (∫ v, d2 v ^ 2) * ((∫ v, d2 v ^ 2) / w ^ 3) := by
          field_simp
      _ ≤ (2 * (∫ v, d3 v ^ 2) + ∫ v, d1 v ^ 2) / (∫ v, d2 v ^ 2) * ∫ u, gR w u ^ 2 :=
          mul_le_mul_of_nonneg_left hlo (by positivity)
  exact step1.trans step2

end ResonatorProfile

/-! ### The archimedean symbol grows like `log |τ|` -/

theorem archimedeanWeilSymbol_le_log_add (τ : ℝ) :
    archimedeanWeilSymbol (τ / (2 * π)) ≤ Real.log (1 + |τ|) + 4 := by
  rw [archimedeanWeilSymbol_eq]
  have harg : π * (τ / (2 * π)) = τ / 2 := by field_simp
  rw [harg]
  set t : ℝ := max 1 (|τ| / 2) with ht
  have ht1 : 1 ≤ t := le_max_left _ _
  have htpos : 0 < t := by linarith
  have hmono := re_digamma_mono_of_abs_le (a := 1 / 4) (by norm_num) (y := τ / 2) (z := t)
    (by rw [abs_of_pos htpos, abs_div, abs_two]; exact le_max_right _ _)
  have hvert := re_digamma_vertical_bound_uncond (σ := 1 / 4) (t := t) (by norm_num) htpos
  have hup := (abs_le.mp hvert).2
  have hinv : 1 / t ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hpi2 : π / (2 * t) ≤ π / 2 := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num); linarith
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hlog : Real.log ((1 / 4) ^ 2 + t ^ 2) ≤ 1 + 2 * Real.log (1 + |τ|) := by
    have h1 : 0 < 1 + |τ| := by positivity
    have hle : (1 / 4 : ℝ) ^ 2 + t ^ 2 ≤ Real.exp 1 * (1 + |τ|) ^ 2 := by
      have he : (2.7 : ℝ) < Real.exp 1 := by
        have := Real.exp_one_gt_d9; norm_num at this ⊢; linarith
      have ht2 : t ^ 2 ≤ 1 + τ ^ 2 / 4 := by
        rcases le_total 1 (|τ| / 2) with h | h
        · rw [ht, max_eq_right h]; rw [div_pow, sq_abs]; linarith
        · rw [ht, max_eq_left h]; nlinarith [sq_nonneg τ]
      have habs : τ ^ 2 = |τ| ^ 2 := (sq_abs τ).symm
      nlinarith [abs_nonneg τ, sq_nonneg (1 + |τ|)]
    calc Real.log ((1 / 4) ^ 2 + t ^ 2) ≤ Real.log (Real.exp 1 * (1 + |τ|) ^ 2) :=
          Real.log_le_log (by positivity) hle
      _ = 1 + 2 * Real.log (1 + |τ|) := by
          rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow]
          push_cast; ring
  have hlogpi : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hcast : ((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I = ((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I :=
    rfl
  calc (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)).re - Real.log π
      ≤ (Complex.digamma (((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)).re := by linarith
    _ ≤ (1 / 2) * Real.log ((1 / 4) ^ 2 + t ^ 2) + (1 / t ^ 2 + π / (2 * t)) := by linarith
    _ ≤ Real.log (1 + |τ|) + 4 := by nlinarith

/-! ### Translates, sums and autocorrelations -/

theorem paperFT_translate' (h : ℝ → ℂ) (x : ℝ) (z : ℂ) :
    paperFT (fun u => h (u - x)) z = Complex.exp (I * z * x) * paperFT h z := by
  unfold paperFT
  have := integral_sub_right_eq_self (μ := volume)
    (fun v : ℝ => h v * Complex.exp (I * z * ((v + x : ℝ) : ℂ))) x
  simp only [sub_add_cancel] at this
  rw [this, ← integral_const_mul]
  congr 1; funext v
  push_cast
  rw [mul_add, Complex.exp_add]; ring

/-- The autocorrelation of a finite combination of translates. -/
theorem weilTest_sum_translates {S : Finset ℕ} {c : ℕ → ℂ} {x : ℕ → ℝ} {h : ℝ → ℂ}
    (hc : Continuous h) (hcs : HasCompactSupport h) (y : ℝ) :
    EF.weilTest (fun u => ∑ m ∈ S, c m * h (u - x m)) (fun u => ∑ m ∈ S, c m * h (u - x m)) y =
      ∑ m ∈ S, ∑ m' ∈ S, c m * conj (c m') * EF.weilTest h h (y - x m + x m') := by
  rw [weilTest_apply]
  have hpt : ∀ t : ℝ, (∑ m ∈ S, c m * h (t - x m)) * conj (∑ m ∈ S, c m * h (t - y - x m)) =
      ∑ m ∈ S, ∑ m' ∈ S, c m * conj (c m') * (h (t - x m) * conj (h (t - y - x m'))) := by
    intro t
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    rw [map_mul]; ring
  have hint : ∀ m m' : ℕ, Integrable fun t : ℝ => h (t - x m) * conj (h (t - y - x m')) := by
    intro m m'
    have h1 : Continuous fun t : ℝ => h (t - x m) := hc.comp (continuous_id.sub continuous_const)
    have h2 : Continuous fun t : ℝ => conj (h (t - y - x m')) :=
      continuous_conj.comp (hc.comp ((continuous_id.sub continuous_const).sub continuous_const))
    refine (h1.mul h2).integrable_of_hasCompactSupport ?_
    exact (hcs.comp_homeomorph (Homeomorph.subRight (x m))).mul_right
  simp_rw [sub_sub] at hpt hint ⊢
  have hpt' : ∀ t : ℝ, (∑ m ∈ S, c m * h (t - x m)) * conj (∑ m ∈ S, c m * h (t - (y + x m))) =
      ∑ m ∈ S, ∑ m' ∈ S, c m * conj (c m') * (h (t - x m) * conj (h (t - (y + x m')))) := hpt
  rw [integral_congr_ae (Eventually.of_forall hpt')]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun m' _ => (hint m m').const_mul _]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun m' _ => (hint m m').const_mul _]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [integral_const_mul]
  congr 1
  rw [weilTest_apply]
  have := integral_add_right_eq_self (μ := volume)
    (fun t : ℝ => h (t - x m) * conj (h (t - (y + x m')))) (x m)
  rw [← this]
  congr 1; funext s
  congr 3 <;> ring

theorem weilTest_self_eq_zero {h : ℝ → ℂ} {r : ℝ} (hh : ∀ u, r < |u| → h u = 0) {Y : ℝ}
    (hY : 2 * r < |Y|) : EF.weilTest h h Y = 0 := by
  rw [weilTest_apply]
  have : (fun t => h t * conj (h (t - Y))) = fun _ => 0 := by
    funext t
    rcases le_or_gt |t| r with ht | ht
    · have : r < |t - Y| := by
        have := abs_sub_abs_le_abs_sub Y t
        rw [abs_sub_comm] at this; linarith
      rw [hh _ this, map_zero, mul_zero]
    · rw [hh t ht, zero_mul]
  rw [this, integral_zero]

theorem weilTest_self_zero_ofReal {g : ℝ → ℝ} :
    EF.weilTest (fun u => ((g u : ℝ) : ℂ)) (fun u => ((g u : ℝ) : ℂ)) 0 =
      ((∫ t, g t ^ 2 : ℝ) : ℂ) := by
  rw [weilTest_apply, ← integral_complex_ofReal]
  congr 1; funext t
  simp only [sub_zero, Complex.conj_ofReal]
  push_cast; ring

/-! ### The gap between logarithms of integers -/

theorem inv_succ_le_log_sub {p q : ℕ} (hp : 0 < p) (hpq : p < q) :
    1 / (q : ℝ) ≤ Real.log q - Real.log p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast (hp.trans hpq)
  have hle : (p : ℝ) ≤ q - 1 := by
    have : p + 1 ≤ q := hpq
    have : ((p + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast this
    push_cast at this; linarith
  have h1 := Real.log_le_sub_one_of_pos (show 0 < (p : ℝ) / q by positivity)
  rw [Real.log_div hp'.ne' hq'.ne'] at h1
  have : (p : ℝ) / q - 1 ≤ -(1 / q) := by
    rw [div_sub_one hq'.ne', neg_div', div_le_div_iff_of_pos_right hq']; linarith
  linarith

/-- Distinct positive integers `q ≠ m` with `m ≤ N` have `|log q - log m| ≥ 1/(N+1)`. -/
theorem log_gap {N m q : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) (hq : 1 ≤ q) (hqm : q ≠ m) :
    1 / ((N : ℝ) + 1) ≤ |Real.log q - Real.log m| := by
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  rcases lt_or_gt_of_ne hqm with h | h
  · have := inv_succ_le_log_sub (by omega) h
    rw [abs_sub_comm, abs_of_nonneg (by linarith [one_div_nonneg.mpr (Nat.cast_nonneg (α := ℝ) m)])]
    refine le_trans ?_ this
    apply one_div_le_one_div_of_le (by exact_mod_cast (show 0 < m by omega))
    have : (m : ℝ) ≤ N := by exact_mod_cast hmN
    linarith
  · -- `m < q`: compare with `m + 1 ≤ q`
    have hm1 : m < m + 1 := Nat.lt_succ_self m
    have h1 := inv_succ_le_log_sub (by omega) hm1
    have hmono : Real.log ((m + 1 : ℕ) : ℝ) ≤ Real.log q :=
      Real.log_le_log (by positivity) (by exact_mod_cast h)
    rw [abs_of_nonneg (by linarith [one_div_nonneg.mpr (Nat.cast_nonneg (α := ℝ) (m + 1))])]
    refine le_trans ?_ (le_trans h1 (by linarith))
    apply one_div_le_one_div_of_le (by positivity)
    have : (m : ℝ) ≤ N := by exact_mod_cast hmN
    push_cast; linarith

/-! ### The resonator test -/

open ResonatorProfile

/-- The point `log m - (log N)/2`. -/
def resPt (N m : ℕ) : ℝ := Real.log m - Real.log N / 2

/-- **The resonator test.**  Narrow polar-free bumps of width `w` at the points
`log m - (log N)/2`, `1 ≤ m ≤ N`, with coefficients `c m`. -/
def resonator (N : ℕ) (c : ℕ → ℂ) (w u : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N, c m * gC w (u - resPt N m)

/-- Its derivative. -/
def resonatorDeriv (N : ℕ) (c : ℕ → ℂ) (w u : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N, c m * deriv (gC w) (u - resPt N m)

theorem contDiff_resonator (N : ℕ) (c : ℕ → ℂ) (w : ℝ) (n : ℕ) :
    ContDiff ℝ n (resonator N c w) := by
  unfold resonator
  exact ContDiff.sum fun m _ =>
    contDiff_const.mul ((contDiff_gC w n).comp (contDiff_id.sub contDiff_const))

theorem contDiff_resonatorDeriv (N : ℕ) (c : ℕ → ℂ) (w : ℝ) (n : ℕ) :
    ContDiff ℝ n (resonatorDeriv N c w) := by
  unfold resonatorDeriv
  exact ContDiff.sum fun m _ =>
    contDiff_const.mul ((contDiff_deriv_gC w n).comp (contDiff_id.sub contDiff_const))

theorem deriv_resonator (N : ℕ) (c : ℕ → ℂ) (w : ℝ) :
    deriv (resonator N c w) = resonatorDeriv N c w := by
  funext u
  have h : HasDerivAt (resonator N c w) (resonatorDeriv N c w u) u := by
    unfold resonator resonatorDeriv
    apply HasDerivAt.fun_sum
    intro m _
    have hd : HasDerivAt (gC w) (deriv (gC w) (u - resPt N m)) (u - resPt N m) :=
      ((contDiff_gC w 1).differentiable (by norm_num) _).hasDerivAt
    exact (hd.comp_sub_const u (resPt N m)).const_mul (c m)
  exact h.deriv

theorem abs_resPt_le {N m : ℕ} (hm : m ∈ Finset.Icc 1 N) : |resPt N m| ≤ Real.log N / 2 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
  have hm0 : (1 : ℝ) ≤ m := by exact_mod_cast h1
  have hmN : (m : ℝ) ≤ N := by exact_mod_cast h2
  have hlm : 0 ≤ Real.log m := Real.log_nonneg hm0
  have hlmN : Real.log m ≤ Real.log N := Real.log_le_log (by linarith) hmN
  unfold resPt; rw [abs_le]; constructor <;> linarith

theorem gC_eq_zero {w u : ℝ} (hw : 0 < w) (hu : w / 4 < |u|) : gC w u = 0 := by
  simp [gC, gR_eq_zero hw hu]

theorem deriv_gC_eq_zero {w u : ℝ} (hw : 0 < w) (hu : w / 4 < |u|) : deriv (gC w) u = 0 := by
  rw [deriv_gC]; simp [gR'_eq_zero hw hu]

theorem sum_translates_eq_zero {N : ℕ} {c : ℕ → ℂ} {w : ℝ} {h : ℝ → ℂ}
    (hh : ∀ v, w / 4 < |v| → h v = 0) {u : ℝ} (hu : Real.log N / 2 + w / 4 < |u|) :
    ∑ m ∈ Finset.Icc 1 N, c m * h (u - resPt N m) = 0 := by
  refine Finset.sum_eq_zero fun m hm => ?_
  have hp := abs_resPt_le hm
  have : w / 4 < |u - resPt N m| := by
    have := abs_sub_abs_le_abs_sub u (resPt N m); linarith
  rw [hh _ this, mul_zero]

theorem tsupport_subset_of_vanish {F : ℝ → ℂ} {a : ℝ} (hF : ∀ u, a < |u| → F u = 0) :
    tsupport F ⊆ Icc (-a) a := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  by_contra h
  apply hu
  apply hF
  simp only [mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
  · exact lt_of_lt_of_le h (le_abs_self u)

theorem hasCompactSupport_gC {w : ℝ} (hw : 0 < w) : HasCompactSupport (gC w) :=
  hasCompactSupport_of_support_subset_abs (Λ := w / 4) fun u hu => by
    by_contra h; push Not at h; exact hu (gC_eq_zero hw h)

theorem hasCompactSupport_deriv_gC {w : ℝ} (hw : 0 < w) : HasCompactSupport (deriv (gC w)) :=
  hasCompactSupport_of_support_subset_abs (Λ := w / 4) fun u hu => by
    by_contra h; push Not at h; exact hu (deriv_gC_eq_zero hw h)

theorem paperFT_resonator {N : ℕ} {c : ℕ → ℂ} {w : ℝ} (hw : 0 < w) (z : ℂ) :
    paperFT (resonator N c w) z =
      ∑ m ∈ Finset.Icc 1 N, c m * (Complex.exp (I * z * resPt N m) * paperFT (gC w) z) := by
  have hint : ∀ m : ℕ, Integrable fun u : ℝ => c m * gC w (u - resPt N m) * cexp (I * z * u) := by
    intro m
    refine (((continuous_const.mul ((contDiff_gC w 0).continuous.comp
      (continuous_id.sub continuous_const))).mul (by fun_prop))).integrable_of_hasCompactSupport ?_
    exact (((hasCompactSupport_gC hw).comp_homeomorph
      (Homeomorph.subRight (resPt N m))).mul_left).mul_right
  unfold resonator
  have e : (fun u : ℝ => (∑ m ∈ Finset.Icc 1 N, c m * gC w (u - resPt N m)) * cexp (I * z * u)) =
      fun u => ∑ m ∈ Finset.Icc 1 N, c m * gC w (u - resPt N m) * cexp (I * z * u) := by
    funext u; rw [Finset.sum_mul]
  show ∫ u, (∑ m ∈ Finset.Icc 1 N, c m * gC w (u - resPt N m)) * cexp (I * z * u) = _
  rw [e, integral_finsetSum _ fun m _ => hint m]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← paperFT_translate']
  unfold paperFT
  rw [← integral_const_mul]
  congr 1; funext u; ring

theorem paperFT_resonator_pole {N : ℕ} {c : ℕ → ℂ} {w : ℝ} (hw : 0 < w) :
    paperFT (resonator N c w) (I / 2) = 0 ∧ paperFT (resonator N c w) (-(I / 2)) = 0 := by
  obtain ⟨h1, h2⟩ := paperFT_gC_pole hw
  constructor <;> rw [paperFT_resonator hw] <;> simp [h1, h2]

/-! ### Selection of the multiplicative diagonal -/

theorem resPt_sub (N m m' : ℕ) : -resPt N m + resPt N m' = Real.log m' - Real.log m := by
  unfold resPt; ring

/-- At `y = log n` only the pairs `m = n m'` survive. -/
theorem weilTest_translates_log {N n : ℕ} {c : ℕ → ℂ} {h : ℝ → ℂ} (hc0 : Continuous h)
    (hcs : HasCompactSupport h)
    (hvan : ∀ Y, 1 / ((N : ℝ) + 1) ≤ |Y| → EF.weilTest h h Y = 0)
    (hc : ∀ m, N < m → c m = 0) (hn : 1 ≤ n) :
    EF.weilTest (fun u => ∑ m ∈ Finset.Icc 1 N, c m * h (u - resPt N m))
        (fun u => ∑ m ∈ Finset.Icc 1 N, c m * h (u - resPt N m)) (Real.log n) =
      EF.weilTest h h 0 * ∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m) := by
  rw [weilTest_sum_translates hc0 hcs, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' hm' => ?_
  have hm'1 : 1 ≤ m' := (Finset.mem_Icc.mp hm').1
  have harg : ∀ m : ℕ, Real.log n - resPt N m + resPt N m' =
      Real.log ((n * m' : ℕ) : ℝ) - Real.log m := by
    intro m
    have : Real.log ((n * m' : ℕ) : ℝ) = Real.log n + Real.log m' := by
      push_cast
      exact Real.log_mul (by exact_mod_cast (show n ≠ 0 by omega))
        (by exact_mod_cast (show m' ≠ 0 by omega))
    rw [this]; unfold resPt; ring
  have hterm : ∀ m ∈ Finset.Icc 1 N, m ≠ n * m' →
      c m * conj (c m') * EF.weilTest h h (Real.log n - resPt N m + resPt N m') = 0 := by
    intro m hm hne
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    rw [harg m, hvan _ (log_gap hm1 hmN (by nlinarith) (Ne.symm hne)), mul_zero]
  have key : ∑ m ∈ Finset.Icc 1 N, c m * conj (c m') *
      EF.weilTest h h (Real.log n - resPt N m + resPt N m') =
      c (n * m') * conj (c m') * EF.weilTest h h 0 := by
    by_cases hin : n * m' ∈ Finset.Icc 1 N
    · rw [Finset.sum_eq_single (n * m') (fun m hm hne => hterm m hm hne)
        (fun h' => absurd hin h'), harg, sub_self]
    · have hgt : N < n * m' := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hin
        rcases hin with h | h
        · exfalso; nlinarith
        · exact h
      rw [hc _ hgt, zero_mul, zero_mul]
      exact Finset.sum_eq_zero fun m hm => by
        have hne : m ≠ n * m' := by
          have := (Finset.mem_Icc.mp hm).2; omega
        exact hterm m hm hne
  rw [key]; ring

/-- At `y = -log n` only the pairs `m' = n m` survive. -/
theorem weilTest_translates_neg_log {N n : ℕ} {c : ℕ → ℂ} {h : ℝ → ℂ} (hc0 : Continuous h)
    (hcs : HasCompactSupport h)
    (hvan : ∀ Y, 1 / ((N : ℝ) + 1) ≤ |Y| → EF.weilTest h h Y = 0)
    (hc : ∀ m, N < m → c m = 0) (hn : 1 ≤ n) :
    EF.weilTest (fun u => ∑ m ∈ Finset.Icc 1 N, c m * h (u - resPt N m))
        (fun u => ∑ m ∈ Finset.Icc 1 N, c m * h (u - resPt N m)) (-Real.log n) =
      EF.weilTest h h 0 * ∑ m ∈ Finset.Icc 1 N, c m * conj (c (n * m)) := by
  rw [weilTest_sum_translates hc0 hcs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have harg : ∀ m' : ℕ, -Real.log n - resPt N m + resPt N m' =
      Real.log m' - Real.log ((n * m : ℕ) : ℝ) := by
    intro m'
    have : Real.log ((n * m : ℕ) : ℝ) = Real.log n + Real.log m := by
      push_cast
      exact Real.log_mul (by exact_mod_cast (show n ≠ 0 by omega))
        (by exact_mod_cast (show m ≠ 0 by omega))
    rw [this]; unfold resPt; ring
  have hterm : ∀ m' ∈ Finset.Icc 1 N, m' ≠ n * m →
      c m * conj (c m') * EF.weilTest h h (-Real.log n - resPt N m + resPt N m') = 0 := by
    intro m' hm' hne
    obtain ⟨hm'1, hm'N⟩ := Finset.mem_Icc.mp hm'
    have hg := log_gap hm'1 hm'N (show 1 ≤ n * m by nlinarith) (Ne.symm hne)
    rw [abs_sub_comm] at hg
    rw [harg m', hvan _ hg, mul_zero]
  have key : ∑ m' ∈ Finset.Icc 1 N, c m * conj (c m') *
      EF.weilTest h h (-Real.log n - resPt N m + resPt N m') =
      c m * conj (c (n * m)) * EF.weilTest h h 0 := by
    by_cases hin : n * m ∈ Finset.Icc 1 N
    · rw [Finset.sum_eq_single (n * m) (fun m' hm' hne => hterm m' hm' hne)
        (fun h' => absurd hin h'), harg, sub_self]
    · have hgt : N < n * m := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hin
        rcases hin with h | h
        · exfalso; nlinarith
        · exact h
      rw [hc _ hgt, map_zero, mul_zero, zero_mul]
      exact Finset.sum_eq_zero fun m' hm' => by
        have hne : m' ≠ n * m := by
          have := (Finset.mem_Icc.mp hm').2; omega
        exact hterm m' hm' hne
  rw [key]; ring

theorem sum_conj_swap (N n : ℕ) (c : ℕ → ℂ) :
    ∑ m ∈ Finset.Icc 1 N, c m * conj (c (n * m)) =
      conj (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem sum_mul_conj_eq (N : ℕ) (c : ℕ → ℂ) :
    ∑ m ∈ Finset.Icc 1 N, c (1 * m) * conj (c m) =
      ((∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

/-! ### The multiplicative Toeplitz bound -/

/-- **The Weil–Toeplitz bound.**  If the finite-atom Weil symbol with weights `lam` (and the
archimedean term of `ζ`) is nonnegative on every polar-constrained `C²` test at every level, then
for every `N ≥ 1` and every coefficient vector `c` supported in `[1, N]`,
`2 ∑_{2 ≤ n ≤ N} lam(n) n^{-1/2} Re ∑_m c(nm) conj(c m) ≤ (log N + C₀) ∑_m |c m|²`,
with an absolute constant `C₀`.  Equivalently, the `N × N` multiplicative Toeplitz matrix
`[lam(m/m') (m/m')^{-1/2} 1_{m' ∣ m}] + transpose` has top eigenvalue `≤ log N + C₀`.

Tests: narrow polar-free bumps `g_w(x - log m)`, `w = 1/(N+1)`; their autocorrelation sees the
atom `log n` only on the exact multiplicative diagonal `m = n m'`, and the archimedean symbol is
bounded by `log(1/w) + O(1)` on their spectrum. -/
theorem weil_multiplicativeToeplitz_bound {lam : ℕ → ℝ}
    (hW : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) :
    ∃ C₀ : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ c : ℕ → ℂ, (∀ m, N < m → c m = 0) →
      2 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
          (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re ≤
        (Real.log N + C₀) * ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 := by
  refine ⟨Real.log 2 + 9 / 2 + profileRatio / 2, fun N hN c hc => ?_⟩
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set w : ℝ := 1 / ((N : ℝ) + 1) with hwdef
  have hw : 0 < w := by positivity
  have hw1 : w ≤ 1 := by rw [hwdef, div_le_one hN1]; linarith
  have hwN : w * ((N : ℝ) + 1) = 1 := by rw [hwdef]; field_simp
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  set a : ℝ := Real.log N / 2 + w / 4 with hadef
  have ha : 0 ≤ a := by positivity
  set F := resonator N c w with hFdef
  set F' := resonatorDeriv N c w with hF'def
  have hFvan : ∀ u, a < |u| → F u = 0 := fun u hu =>
    sum_translates_eq_zero (fun v hv => gC_eq_zero hw hv) hu
  have hF'van : ∀ u, a < |u| → F' u = 0 := fun u hu =>
    sum_translates_eq_zero (fun v hv => deriv_gC_eq_zero hw hv) hu
  have hFs : tsupport F ⊆ Icc (-a) a := tsupport_subset_of_vanish hFvan
  have hF's : tsupport F' ⊆ Icc (-a) a := tsupport_subset_of_vanish hF'van
  have hF2 : ContDiff ℝ 2 F := contDiff_resonator N c w 2
  have hF'2 : ContDiff ℝ 2 F' := contDiff_resonatorDeriv N c w 2
  have hFcs : HasCompactSupport F :=
    hasCompactSupport_of_support_subset_abs (Λ := a) fun u hu => by
      by_contra h; push Not at h; exact hu (hFvan u h)
  obtain ⟨hp1, hp2⟩ := paperFT_resonator_pole (N := N) (c := c) hw
  have hpos := hW a ha F hF2 hFs hp1 hp2
  rw [integral_weilAtomSymbol_eq_arch_sub hF2 hFs lam] at hpos
  -- the autocorrelation masses
  set k0r : ℝ := ∫ t, gR w t ^ 2 with hk0r
  set k1r : ℝ := ∫ t, gR' w t ^ 2 with hk1r
  have hk0 : EF.weilTest (gC w) (gC w) 0 = (k0r : ℂ) := weilTest_self_zero_ofReal (g := gR w)
  have hk1 : EF.weilTest (deriv (gC w)) (deriv (gC w)) 0 = (k1r : ℂ) := by
    rw [deriv_gC]; exact weilTest_self_zero_ofReal (g := gR' w)
  have hk0pos : 0 < k0r := lt_of_lt_of_le (div_pos integral_d2_sq_pos (by positivity))
    (integral_gR_sq_ge hw)
  have hgap : 2 * (w / 4) < 1 / ((N : ℝ) + 1) := by
    rw [← hwdef]; linarith
  have hvan0 : ∀ Y, 1 / ((N : ℝ) + 1) ≤ |Y| → EF.weilTest (gC w) (gC w) Y = 0 :=
    fun Y hY => weilTest_self_eq_zero (fun u hu => gC_eq_zero hw hu) (by linarith)
  have hvan1 : ∀ Y, 1 / ((N : ℝ) + 1) ≤ |Y| →
      EF.weilTest (deriv (gC w)) (deriv (gC w)) Y = 0 :=
    fun Y hY => weilTest_self_eq_zero (fun u hu => deriv_gC_eq_zero hw hu) (by linarith)
  have hgc0 : Continuous (gC w) := (contDiff_gC w 0).continuous
  have hgc1 : Continuous (deriv (gC w)) := (contDiff_deriv_gC w 0).continuous
  have hgs0 := hasCompactSupport_gC hw
  have hgs1 := hasCompactSupport_deriv_gC hw
  set S : ℕ → ℂ := fun n => ∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m) with hSdef
  -- the atoms
  have hsel : ∀ n : ℕ, 1 ≤ n →
      (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re = 2 * k0r * (S n).re := by
    intro n hn
    have h1 := weilTest_translates_log hgc0 hgs0 hvan0 hc hn
    have h2 := weilTest_translates_neg_log hgc0 hgs0 hvan0 hc hn
    rw [sum_conj_swap] at h2
    rw [show F = fun u => ∑ m ∈ Finset.Icc 1 N, c m * gC w (u - resPt N m) from rfl, h1, h2, hk0]
    simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.conj_re, hSdef]
    ring
  have hS0 : ∀ n, N < n → S n = 0 := by
    intro n hn
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm1 := (Finset.mem_Icc.mp hm).1
    rw [hc (n * m) (by nlinarith), zero_mul]
  have hM : N ≤ ⌊Real.exp (2 * a)⌋₊ := by
    apply Nat.le_floor
    have : Real.exp (Real.log N) ≤ Real.exp (2 * a) := Real.exp_le_exp.mpr (by rw [hadef]; linarith)
    rwa [Real.exp_log (by linarith)] at this
  have hatoms : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, lam n / Real.sqrt n *
      (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re =
      2 * k0r * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * (S n).re := by
    calc ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, lam n / Real.sqrt n *
          (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re
        = ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, 2 * k0r * (lam n / Real.sqrt n * (S n).re) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [hsel n (by have := (Finset.mem_Icc.mp hn).1; omega)]; ring
      _ = ∑ n ∈ Finset.Icc 2 N, 2 * k0r * (lam n / Real.sqrt n * (S n).re) := by
          refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hM) fun n hn hnot => ?_).symm
          have hnN : N < n := by
            simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
            rcases hnot with h | h
            · have := (Finset.mem_Icc.mp hn).1; omega
            · exact h
          rw [hS0 n hnN]; simp
      _ = 2 * k0r * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * (S n).re := by
          rw [Finset.mul_sum]
  set sumc : ℝ := ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 with hsumc
  have hsum : 0 ≤ sumc := Finset.sum_nonneg fun m _ => sq_nonneg _
  -- the Plancherel masses
  have hmass0 : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 = 2 * π * k0r * sumc := by
    have h := integral_normSq_paperFT_mul_cos_eq hF2 hFs 0
    simp only [mul_zero, Real.cos_zero, mul_one, neg_zero] at h
    rw [h]
    have h0 := weilTest_translates_log (n := 1) hgc0 hgs0 hvan0 hc le_rfl
    simp only [Nat.cast_one, Real.log_one] at h0
    rw [show F = fun u => ∑ m ∈ Finset.Icc 1 N, c m * gC w (u - resPt N m) from rfl, h0, hk0,
      sum_mul_conj_eq]
    simp only [Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  have hmass1 : ∫ τ : ℝ, ‖paperFT F' τ‖ ^ 2 = 2 * π * k1r * sumc := by
    have h := integral_normSq_paperFT_mul_cos_eq hF'2 hF's 0
    simp only [mul_zero, Real.cos_zero, mul_one, neg_zero] at h
    rw [h]
    have h0 := weilTest_translates_log (n := 1) hgc1 hgs1 hvan1 hc le_rfl
    simp only [Nat.cast_one, Real.log_one] at h0
    rw [show F' = fun u => ∑ m ∈ Finset.Icc 1 N, c m * deriv (gC w) (u - resPt N m) from rfl, h0,
      hk1, sum_mul_conj_eq]
    simp only [Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  -- the archimedean symbol on the spectrum of the resonator
  have hderiv : ∀ τ : ℝ, ‖paperFT F' τ‖ ^ 2 = τ ^ 2 * ‖paperFT F τ‖ ^ 2 := by
    intro τ
    rw [hF'def, ← deriv_resonator, paperFT_deriv (contDiff_resonator N c w 1) hFcs]
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      one_mul, mul_pow, sq_abs]
  set α : ℝ := Real.log ((N : ℝ) + 1) + 9 / 2 with hα
  set β : ℝ := w ^ 2 / 2 with hβ
  have hpt : ∀ τ : ℝ, ‖paperFT F τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) ≤
      α * ‖paperFT F τ‖ ^ 2 + β * ‖paperFT F' τ‖ ^ 2 := by
    intro τ
    have hA := archimedeanWeilSymbol_le_log_add τ
    have hpos1 : 0 < 1 + w * |τ| := by positivity
    have hle : 1 + |τ| ≤ ((N : ℝ) + 1) * (1 + w * |τ|) := by
      have : ((N : ℝ) + 1) * (1 + w * |τ|) = (N : ℝ) + 1 + |τ| := by
        rw [mul_add, mul_one, ← mul_assoc, mul_comm ((N : ℝ) + 1) w, hwN, one_mul]
      rw [this]; linarith
    have hlog1 : Real.log (1 + |τ|) ≤ Real.log ((N : ℝ) + 1) + w * |τ| := by
      calc Real.log (1 + |τ|) ≤ Real.log (((N : ℝ) + 1) * (1 + w * |τ|)) :=
            Real.log_le_log (by positivity) hle
        _ = Real.log ((N : ℝ) + 1) + Real.log (1 + w * |τ|) :=
            Real.log_mul (by positivity) (by positivity)
        _ ≤ Real.log ((N : ℝ) + 1) + w * |τ| := by
            have := Real.log_le_sub_one_of_pos hpos1; linarith
    have hamgm : w * |τ| ≤ 1 / 2 + w ^ 2 * τ ^ 2 / 2 := by
      have := sq_nonneg (w * |τ| - 1)
      have h2 : (w * |τ|) ^ 2 = w ^ 2 * τ ^ 2 := by rw [mul_pow, sq_abs]
      nlinarith
    have hA' : archimedeanWeilSymbol (τ / (2 * π)) ≤ α + β * τ ^ 2 := by
      rw [hα, hβ]; linarith
    rw [hderiv τ]
    have hnn : 0 ≤ ‖paperFT F τ‖ ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_left hA' hnn
    linarith
  have hint1 := integrable_normSq_paperFT_mul_arch hF2 hFs
  have hint2 := integrable_normSq_paperFT hF2 hFs
  have hint3 := integrable_normSq_paperFT hF'2 hF's
  have harch : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) ≤
      α * (2 * π * k0r * sumc) + β * (2 * π * k1r * sumc) := by
    calc ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))
        ≤ ∫ τ : ℝ, (α * ‖paperFT F τ‖ ^ 2 + β * ‖paperFT F' τ‖ ^ 2) :=
          integral_mono hint1 ((hint2.const_mul α).add (hint3.const_mul β)) hpt
      _ = α * (∫ τ : ℝ, ‖paperFT F τ‖ ^ 2) + β * ∫ τ : ℝ, ‖paperFT F' τ‖ ^ 2 := by
          rw [integral_add (hint2.const_mul α) (hint3.const_mul β), integral_const_mul,
            integral_const_mul]
      _ = α * (2 * π * k0r * sumc) + β * (2 * π * k1r * sumc) := by rw [hmass0, hmass1]
  have hratio : β * k1r ≤ profileRatio / 2 * k0r := by
    have := sq_mul_integral_gR'_le hw hw1
    rw [hβ, hk1r, hk0r]; nlinarith
  have hlog2 : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by positivity) (by linarith)
  set T : ℝ := ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * (S n).re with hT
  rw [hatoms] at hpos
  have hk2 : 0 < 2 * π * k0r := by positivity
  have hmain : 2 * π * k0r * (2 * T) ≤ 2 * π * k0r * ((α + profileRatio / 2) * sumc) := by
    have h1 : β * (2 * π * k1r * sumc) ≤ 2 * π * sumc * (profileRatio / 2 * k0r) := by
      have := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2 * π * sumc by positivity)
      linarith
    nlinarith
  have h2T : 2 * T ≤ (α + profileRatio / 2) * sumc := le_of_mul_le_mul_left hmain hk2
  calc 2 * T ≤ (α + profileRatio / 2) * sumc := h2T
    _ ≤ (Real.log N + (Real.log 2 + 9 / 2 + profileRatio / 2)) * sumc := by
        apply mul_le_mul_of_nonneg_right _ hsum
        rw [hα]; linarith

/-! ### Density corollaries -/

theorem sum_Icc_inv_le_one_add_log (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m ≤ 1 + Real.log N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp
    · have h := inv_succ_le_log_sub hpos (Nat.lt_succ_self N)
      push_cast at h ⊢
      linarith

/-- **Twisted density law.**  For every completely multiplicative unimodular `χ`, Weil-positive
weights satisfy `2 ∑_{n ≥ 2, m ≥ 1, n m ≤ N} lam(n) Re χ(n)/(n m) ≤ (log N + C₀) ∑_{m ≤ N} 1/m`:
the resonator `c(m) = χ(m) m^{-1/2}` in the Weil–Toeplitz bound. -/
theorem weil_twisted_density_bound {lam : ℕ → ℝ}
    (hW : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) :
    ∃ C₀ : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ χ : ℕ → ℂ, (∀ a b, χ (a * b) = χ a * χ b) →
      (∀ m, ‖χ m‖ = 1) →
      2 * ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
          (if n * m ≤ N then lam n * (χ n).re / (n * m) else 0) ≤
        (Real.log N + C₀) * ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m := by
  obtain ⟨C₀, hC⟩ := weil_multiplicativeToeplitz_bound hW
  refine ⟨C₀, fun N hN χ hmul hnorm => ?_⟩
  set c : ℕ → ℂ := fun m => if m ≤ N then χ m * ((1 / Real.sqrt m : ℝ) : ℂ) else 0 with hcdef
  have hc : ∀ m, N < m → c m = 0 := fun m hm => by simp [hcdef, not_le.mpr hm]
  have h := hC N hN c hc
  have hχconj : ∀ m, χ m * conj (χ m) = 1 := fun m => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; simp
  have hlhs : ∀ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
      (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re =
      ∑ m ∈ Finset.Icc 1 N, (if n * m ≤ N then lam n * (χ n).re / (n * m) else 0) := by
    intro n hn
    have hn1 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (show 0 < n by omega)
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    by_cases hnm : n * m ≤ N
    · rw [if_pos hnm]
      simp only [hcdef, if_pos hnm, if_pos hmN, map_mul, Complex.conj_ofReal, hmul]
      have hsq : Real.sqrt ((n * m : ℕ) : ℝ) = Real.sqrt n * Real.sqrt m := by
        push_cast; exact Real.sqrt_mul hn1.le _
      rw [hsq]
      have hsm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
      have hr : (1 / (Real.sqrt n * Real.sqrt m)) * (1 / Real.sqrt m) = 1 / (Real.sqrt n * m) := by
        rw [div_mul_div_comm, one_mul, mul_assoc, hsm]
      have e : χ n * χ m * ((1 / (Real.sqrt n * Real.sqrt m) : ℝ) : ℂ) *
          (conj (χ m) * ((1 / Real.sqrt m : ℝ) : ℂ)) =
          χ n * (χ m * conj (χ m)) * ((1 / (Real.sqrt n * m) : ℝ) : ℂ) := by
        rw [← hr]; push_cast; ring
      rw [e, hχconj, mul_one, Complex.re_mul_ofReal]
      have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn1.le
      have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn1
      calc lam n / Real.sqrt n * ((χ n).re * (1 / (Real.sqrt n * m)))
          = lam n * (χ n).re / ((Real.sqrt n * Real.sqrt n) * m) := by field_simp
        _ = lam n * (χ n).re / (n * m) := by rw [hsn]
    · rw [if_neg hnm]
      simp [hcdef, if_neg hnm]
  have hrhs : ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 = ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    simp only [hcdef, if_pos hmN, norm_mul, hnorm, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity), div_pow, one_pow, Real.sq_sqrt hm0.le]
  rw [Finset.sum_congr rfl hlhs, hrhs] at h
  exact h

/-- **Upper log-density law.**  Weil-positive weights (with the archimedean term of `ζ`) have
`∑_{n ≥ 2, m ≥ 1, n m ≤ N} lam(n)/(n m) ≤ (1/2 + ε) (log N)²` for all large `N`: in the
logarithmic mean `∑_{k ≤ N} (lam ⋆ 1)(k)/k`, their density is at most that of `Λ`. -/
theorem weil_log_density_le {lam : ℕ → ℝ}
    (hW : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
          (if n * m ≤ N then lam n / (n * m) else 0) ≤ (1 / 2 + ε) * Real.log N ^ 2 := by
  obtain ⟨C₀, hC⟩ := weil_twisted_density_bound hW
  set L₀ : ℝ := 2 * (|C₀| + 1) / ε + |C₀| + 1 with hL₀
  refine ⟨⌈Real.exp L₀⌉₊ + 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : L₀ ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNr]
    have h1 : Real.exp L₀ ≤ ⌈Real.exp L₀⌉₊ := Nat.le_ceil _
    have h2 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ N := by exact_mod_cast (show ⌈Real.exp L₀⌉₊ ≤ N by omega)
    linarith
  have hq0 : 0 ≤ 2 * (|C₀| + 1) / ε := by positivity
  have hL1 : 1 ≤ L₀ := by rw [hL₀]; linarith [abs_nonneg C₀]
  set L := Real.log N with hLdef
  have hχ := hC N hN1 (fun _ => 1) (fun a b => by ring) (fun m => by simp)
  simp only [Complex.one_re, mul_one] at hχ
  have hH := sum_Icc_inv_le_one_add_log N
  have hLC : 0 ≤ L + C₀ := by
    have h1 : |C₀| + 1 ≤ L₀ := by rw [hL₀]; linarith
    linarith [neg_abs_le C₀]
  have hstep : 2 * ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then lam n / (n * m) else 0) ≤ (L + C₀) * (1 + L) :=
    hχ.trans (mul_le_mul_of_nonneg_left hH hLC)
  have hquad : (L + C₀) * (1 + L) ≤ (1 + 2 * ε) * L ^ 2 := by
    have hLpos : 1 ≤ L := hL1.trans hlog
    have hdiv : 2 * (|C₀| + 1) / ε ≤ L := by rw [hL₀] at hlog; linarith [abs_nonneg C₀]
    have hbig : 2 * (|C₀| + 1) ≤ L * ε := (div_le_iff₀ hε).mp hdiv
    have hC : C₀ ≤ |C₀| := le_abs_self C₀
    have h1 : (L + C₀) * (1 + L) ≤ L ^ 2 + 2 * (|C₀| + 1) * L := by nlinarith [abs_nonneg C₀]
    have h2 : 2 * (|C₀| + 1) * L ≤ ε * L ^ 2 := by nlinarith
    nlinarith
  linarith


end

end RHTower

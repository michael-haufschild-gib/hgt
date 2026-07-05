/-
# Jensen-section substrate (Lemma R / task #139, first layer)

The section-asymptotics layer absent from mathlib, built from `SpurRescale`'s per-coefficient
(E5) bound. For a finite real carrier `g(z) = Σ_{j<J} c_j z^j`, the RESCALED Jensen section is
`Ã_d(z) = Σ_{j<J} φ_d(j) c_j z^j` with `φ_d(j) = ∏_{i<j}(1 − i/d)`, and its first heat
approximation `Σ_{j<J} c_j (1 − C(j,2)/d) z^j = g − z²g″/(2d)`. Doc 25 (E5):

> `|Ã_d(z) − (g − z²g″/(2d))| ≤ C_ρ / d²` on `|z| ≤ ρ`, `C_ρ = ½ Σ |c_j| C(j,2)² ρ^j`.

This is the (R1) foundation of Lemma R (the cluster splitting): summing the per-coefficient
(E5) bound gives the two-term section expansion with an explicit `1/d²` remainder. The
subsequent heat resummation to `He_m` (the full Lemma R, m ≥ 4) builds on this.

* `rescaledSection`, `heatApprox` — the section and its two-term heat approximation.
* `rescaledSection_sub_heatApprox_abs_le` — the (E5) two-term bound (this file's theorem).
-/
import GaloisForLFunctions.RHTower.SpurRescale

namespace RHTower

open Finset

/-- The rescaled Jensen section `Ã_d(z) = Σ_{j<J} φ_d(j) c_j z^j`,
`φ_d(j) = ∏_{i<j}(1 − i/d)`, for a finite real carrier with coefficients `c`. -/
noncomputable def rescaledSection (c : ℕ → ℝ) (J d : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ range J, (∏ i ∈ range j, (1 - (i : ℝ) / d)) * c j * z ^ j

/-- The first heat approximation `Σ_{j<J} c_j (1 − C(j,2)/d) z^j = g − z²g″/(2d)`. -/
noncomputable def heatApprox (c : ℕ → ℝ) (J d : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ range J, c j * (1 - (j.choose 2 : ℝ) / d) * z ^ j

/-- The finite carrier `g(z) = Σ_{j<J} c_j z^j`. -/
noncomputable def carrier (c : ℕ → ℝ) (J : ℕ) (z : ℝ) : ℝ := ∑ j ∈ range J, c j * z ^ j

/-- The curvature term `Σ_{j<J} c_j C(j,2) z^j = z²·g″(z)/2` (since `C(j,2)·z^j` is the
`j`-monomial of `z²g″/2`). -/
noncomputable def curvatureTerm (c : ℕ → ℝ) (J : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ range J, c j * (j.choose 2 : ℝ) * z ^ j

/-- The carrier `g(z) = Σ_{j<J} c_j z^j` is differentiable with `g′(z) = Σ_{j<J} c_j·j·z^{j−1}`
— the section substrate connects to the actual carrier derivative (toward the recentered
cluster evaluation `g(x*+σu)`). -/
theorem carrier_hasDerivAt (c : ℕ → ℝ) (J : ℕ) (z : ℝ) :
    HasDerivAt (carrier c J) (∑ j ∈ range J, c j * (j : ℝ) * z ^ (j - 1)) z := by
  have hterm : ∀ j ∈ range J,
      HasDerivAt (fun z => c j * z ^ j) (c j * (j : ℝ) * z ^ (j - 1)) z := by
    intro j _
    have h := (hasDerivAt_pow j z).const_mul (c j)
    convert h using 1; ring
  have hsum := HasDerivAt.fun_sum hterm
  exact hsum

/-- The carrier second derivative `g″(z) = Σ_{j<J} c_j·j·(j−1)·z^{j−2}` (derivative of
`carrier_hasDerivAt`'s output). The `j = 0, 1` terms vanish via the `j·(j−1)` factor. -/
theorem carrier_deriv_hasDerivAt (c : ℕ → ℝ) (J : ℕ) (z : ℝ) :
    HasDerivAt (fun w => ∑ j ∈ range J, c j * (j : ℝ) * w ^ (j - 1))
      (∑ j ∈ range J, c j * (j : ℝ) * ((j - 1 : ℕ) : ℝ) * z ^ (j - 2)) z := by
  refine HasDerivAt.fun_sum (fun j _ => ?_)
  have h := (hasDerivAt_pow (j - 1) z).const_mul (c j * (j : ℝ))
  have hexp : j - 1 - 1 = j - 2 := by omega
  rw [hexp] at h
  convert h using 1
  ring

/-- The recentered monomial `g(w) = aₘ(w−x*)ᵐ` has `g′(z) = aₘ·m·(z−x*)ᵐ⁻¹` — the clean
carrier for the cluster splitting near an `m`-fold zero at `x*`. -/
theorem monomial_hasDerivAt (am xs : ℝ) (m : ℕ) (z : ℝ) :
    HasDerivAt (fun w => am * (w - xs) ^ m) (am * (m : ℝ) * (z - xs) ^ (m - 1)) z := by
  have hbase : HasDerivAt (fun w : ℝ => w - xs) 1 z := by
    simpa using (hasDerivAt_id z).sub_const xs
  have h := (hbase.pow m).const_mul am
  convert h using 1
  ring

/-- Its second derivative `g″(z) = aₘ·m·(m−1)·(z−x*)ᵐ⁻²`. -/
theorem monomial_hasDerivAt2 (am xs : ℝ) (m : ℕ) (z : ℝ) :
    HasDerivAt (fun w => am * (m : ℝ) * (w - xs) ^ (m - 1))
      (am * (m : ℝ) * ((m - 1 : ℕ) : ℝ) * (z - xs) ^ (m - 2)) z := by
  have hbase : HasDerivAt (fun w : ℝ => w - xs) 1 z := by
    simpa using (hasDerivAt_id z).sub_const xs
  have h := (hbase.pow (m - 1)).const_mul (am * (m : ℝ))
  have hexp : m - 1 - 1 = m - 2 := by omega
  rw [hexp] at h
  convert h using 1
  ring

/-- **Cluster evaluation (the Lemma R crux, `m = k+2`).** The recentered-monomial heat form
`g − z²g″/(2d)` at `z = x*+σu`, with `g = aₘ(z−x*)ᵐ` (so `g″` from `monomial_hasDerivAt2`),
splits EXACTLY at the cluster scale `σ²d = x*²` into the Hermite two-term form plus the R3
freezing correction:
`aₘ(σu)ᵐ − (x*+σu)²·aₘ·m(m−1)(σu)ᵐ⁻²/(2d)
  = aₘ σᵐ(uᵐ − C(m,2)uᵐ⁻²) − aₘ·m(m−1)σᵐ⁻²uᵐ⁻²(2x*σu+σ²u²)/(2d)`.
The first term is `aₘ σᵐ Heₘ(u)` for `m ≤ 3` (`cluster_hermite_scaling`); the second is the
`O(σ)` freezing term. This is doc 25 §3.1 made exact. -/
theorem heatMono_cluster (am xs σ u : ℝ) (k d : ℕ) (hd : 0 < d)
    (hσ : σ ^ 2 * (d : ℝ) = xs ^ 2) :
    am * (σ * u) ^ (k + 2)
      - (xs + σ * u) ^ 2 * (am * ((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) * (σ * u) ^ k)
        / (2 * (d : ℝ))
      = am * σ ^ (k + 2) * (u ^ (k + 2) - ((k + 2).choose 2 : ℝ) * u ^ k)
        - am * ((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) * σ ^ k * u ^ k
          * (2 * xs * σ * u + σ ^ 2 * u ^ 2) / (2 * (d : ℝ)) := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hexpand : (xs + σ * u) ^ 2 = σ ^ 2 * (d : ℝ) + (2 * xs * (σ * u) + (σ * u) ^ 2) := by
    rw [show (xs + σ * u) ^ 2 = xs ^ 2 + (2 * xs * (σ * u) + (σ * u) ^ 2) from by ring, ← hσ]
  rw [hexpand, mul_pow, mul_pow, pow_add σ k 2, pow_add u k 2, Nat.cast_choose_two]
  push_cast
  field_simp
  ring

/-- **(E4) derivative form**: `curvatureTerm = z²·g″(z)/2`, identifying the coefficient
curvature `Σ c_j C(j,2) z^j` with the analytic `z²g″/2` (`C(j,2) = j(j−1)/2`). The `j=0,1`
terms vanish on both sides. -/
theorem curvatureTerm_eq_deriv (c : ℕ → ℝ) (J : ℕ) (z : ℝ) :
    curvatureTerm c J z
      = z ^ 2 * (∑ j ∈ range J, c j * (j : ℝ) * ((j - 1 : ℕ) : ℝ) * z ^ (j - 2)) / 2 := by
  rw [curvatureTerm, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  match j with
  | 0 => simp
  | 1 => simp
  | (k + 2) =>
    rw [show k + 2 - 1 = k + 1 from rfl, show k + 2 - 2 = k from rfl,
      Nat.cast_choose_two, pow_add]
    push_cast
    ring

/-- **(E4) heat-form identity**: `heatApprox = g − (z²g″/2)/d`, the backward-heat smoothing of
the carrier at time-scale `1/d` (doc 25 (E4)). The two-term section is `g` minus its curvature
term scaled by `1/d` — the structural form on which the cluster splitting rests. -/
theorem heatApprox_eq (c : ℕ → ℝ) (J d : ℕ) (hd : 0 < d) (z : ℝ) :
    heatApprox c J d z = carrier c J z - curvatureTerm c J z / d := by
  rw [heatApprox, carrier, curvatureTerm, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  field_simp

/-- **(E5) two-term section bound.** The rescaled section differs from its two-term heat
approximation by at most `C_ρ / d²`, `C_ρ = ½ Σ |c_j| C(j,2)² ρ^j`, on `|z| ≤ ρ`: summing
`SpurRescale.phi_first_order` (`|φ_d(j) − (1 − C(j,2)/d)| ≤ (C(j,2)/d)²/2`) coefficientwise. -/
theorem rescaledSection_sub_heatApprox_abs_le (c : ℕ → ℝ) (J : ℕ) {d : ℕ} (hd : 1 ≤ d)
    {z ρ : ℝ} (hz : |z| ≤ ρ) :
    |rescaledSection c J d z - heatApprox c J d z|
      ≤ (∑ j ∈ range J, |c j| * ((j.choose 2 : ℝ)) ^ 2 * ρ ^ j) / (2 * (d : ℝ) ^ 2) := by
  have hρ : 0 ≤ ρ := le_trans (abs_nonneg z) hz
  have hd0 : (0 : ℝ) < d := by positivity
  rw [rescaledSection, heatApprox, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hfactor : (∏ i ∈ range j, (1 - (i : ℝ) / d)) * c j * z ^ j
      - c j * (1 - (j.choose 2 : ℝ) / d) * z ^ j
      = c j * z ^ j * ((∏ i ∈ range j, (1 - (i : ℝ) / d)) - (1 - (j.choose 2 : ℝ) / d)) := by
    ring
  rw [hfactor, abs_mul, abs_mul]
  have he5 := phi_first_order j hd
  have hzj : |z ^ j| ≤ ρ ^ j := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg z) hz j
  have hCd : (((j.choose 2 : ℝ)) / d) ^ 2 / 2
      = ((j.choose 2 : ℝ)) ^ 2 / (2 * (d : ℝ) ^ 2) := by
    rw [div_pow]; field_simp
  have hstep : |z ^ j| * |(∏ i ∈ range j, (1 - (i : ℝ) / d)) - (1 - (j.choose 2 : ℝ) / d)|
      ≤ ρ ^ j * (((j.choose 2 : ℝ)) ^ 2 / (2 * (d : ℝ) ^ 2)) := by
    rw [← hCd]
    exact mul_le_mul hzj he5 (abs_nonneg _) (pow_nonneg hρ j)
  calc |c j| * |z ^ j|
        * |(∏ i ∈ range j, (1 - (i : ℝ) / d)) - (1 - (j.choose 2 : ℝ) / d)|
      = |c j| * (|z ^ j|
          * |(∏ i ∈ range j, (1 - (i : ℝ) / d)) - (1 - (j.choose 2 : ℝ) / d)|) := by ring
    _ ≤ |c j| * (ρ ^ j * (((j.choose 2 : ℝ)) ^ 2 / (2 * (d : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hstep (abs_nonneg _)
    _ = |c j| * ((j.choose 2 : ℝ)) ^ 2 * ρ ^ j / (2 * (d : ℝ) ^ 2) := by ring

end RHTower

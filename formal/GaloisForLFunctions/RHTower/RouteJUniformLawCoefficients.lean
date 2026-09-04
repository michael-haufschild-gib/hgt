import GaloisForLFunctions.RHTower.RouteJUniformLaw
import GaloisForLFunctions.RHTower.RouteJScalingProfile

/-!
# Asymptotics of the two-index coefficients `a(k, σ)`, `b(k, σ)`

Fixed `σ`, `k → ∞`:  `a/k² → 64 σ (1−σ²)`,  `b/k² → −64 σ² (1−σ²)`.
Scaling regime (`σ_j → 0`, `k_j σ_j → X`):  `a/k → 64 X`,  `b/k → 8`.

Each rational piece is rewritten as a quotient of polynomials in `u = 1/k` (and `y = kσ`) and
the limits are read off by continuity.
-/

open Filter Topology Finset
open scoped Real

namespace RHTower
namespace RouteJUniform

open LegendreBoost RouteJProfile CosineModeResponse RouteJBeatMode

/-! ## Polynomial forms -/

noncomputable def denA1 (u : ℝ) : ℝ := 2 * (u + 2) * (u + 4) * (3 * u + 4)
noncomputable def denA2 (u : ℝ) : ℝ := 2 * (2 * u + 1) * (3 * u + 2) * (5 * u + 4) * (7 * u + 4)
noncomputable def denB1 (u : ℝ) : ℝ := (u + 2) * (u + 4) * (3 * u + 4)
noncomputable def denB2 (u : ℝ) : ℝ := 8 * (2 * u + 1) * (3 * u + 2) * (5 * u + 4) * (7 * u + 4)

noncomputable def numAR1 (s u : ℝ) : ℝ :=
  -s * (5 * u + 8) * (21 * s ^ 2 * u ^ 2 + 80 * s ^ 2 * u + 64 * s ^ 2 - 11 * u ^ 2 - 40 * u - 32)
noncomputable def numAR2 (s u : ℝ) : ℝ :=
  -s * (u + 1) * (13 * u + 8) *
    (165 * s ^ 2 * u ^ 2 + 208 * s ^ 2 * u + 64 * s ^ 2 - 83 * u ^ 2 - 104 * u - 32)
noncomputable def polA0 (s u : ℝ) : ℝ := 4 * s * (u + 1) * (9 * u + 8)
noncomputable def numBR1 (s u : ℝ) : ℝ :=
  (5 * u + 8) * (6 * s ^ 2 * u ^ 2 + 22 * s ^ 2 * u + 16 * s ^ 2 - u ^ 2 - 2 * u)
noncomputable def numBR2 (s u : ℝ) : ℝ :=
  (13 * u + 8) * (1485 * s ^ 4 * u ^ 3 + 3192 * s ^ 4 * u ^ 2 + 2240 * s ^ 4 * u + 512 * s ^ 4 -
    1122 * s ^ 2 * u ^ 3 - 2400 * s ^ 2 * u ^ 2 - 1680 * s ^ 2 * u - 384 * s ^ 2 - 35 * u ^ 3 -
    48 * u ^ 2 - 16 * u)
noncomputable def polB0 (s u : ℝ) : ℝ := -(9 * u + 8) * (11 * s ^ 2 * u + 8 * s ^ 2 - 3 * u) / 2

noncomputable def ynumAR1 (y u : ℝ) : ℝ :=
  -y * (5 * u + 8) * (21 * u ^ 4 * y ^ 2 + 80 * u ^ 3 * y ^ 2 + 64 * u ^ 2 * y ^ 2 - 11 * u ^ 2 -
    40 * u - 32)
noncomputable def ynumAR2 (y u : ℝ) : ℝ :=
  -y * (u + 1) * (13 * u + 8) *
    (165 * u ^ 4 * y ^ 2 + 208 * u ^ 3 * y ^ 2 + 64 * u ^ 2 * y ^ 2 - 83 * u ^ 2 - 104 * u - 32)
noncomputable def ypolA0 (y u : ℝ) : ℝ := 4 * y * (u + 1) * (9 * u + 8)
noncomputable def ynumBR1 (y u : ℝ) : ℝ :=
  (5 * u + 8) * (6 * u ^ 3 * y ^ 2 + 22 * u ^ 2 * y ^ 2 + 16 * u * y ^ 2 - u - 2)
noncomputable def ynumBR2 (y u : ℝ) : ℝ :=
  (13 * u + 8) * (1485 * u ^ 6 * y ^ 4 + 3192 * u ^ 5 * y ^ 4 + 2240 * u ^ 4 * y ^ 4 -
    1122 * u ^ 4 * y ^ 2 + 512 * u ^ 3 * y ^ 4 - 2400 * u ^ 3 * y ^ 2 - 1680 * u ^ 2 * y ^ 2 -
    35 * u ^ 2 - 384 * u * y ^ 2 - 48 * u - 16)
noncomputable def ypolB0 (y u : ℝ) : ℝ := -(9 * u + 8) * (11 * u ^ 2 * y ^ 2 + 8 * u * y ^ 2 - 3) * (1 / 2)

/-! ## Identities -/

section identities
variable {k : ℕ} (hk : 1 ≤ k) (s : ℝ)
include hk

theorem coefAR1_eq_u : coefAR1 k s = numAR1 s (1 / k) / denA1 (1 / k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have h1 : (0 : ℝ) < 2 * k + 1 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 1 := by positivity
  have h3 : (0 : ℝ) < 4 * k + 3 := by positivity
  unfold coefAR1 shA0 numAR1 denA1
  field_simp
  ring

theorem coefAR2_eq_u : coefAR2 k s = numAR2 s (1 / k) / denA2 (1 / k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have h1 : (0 : ℝ) < 2 * k + 3 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 5 := by positivity
  have h3 : (0 : ℝ) < 4 * k + 7 := by positivity
  have h4 : (0 : ℝ) < k + 2 := by positivity
  unfold coefAR2 shA8 numAR2 denA2
  field_simp
  ring

theorem coefA0_eq_u : coefA0 k s / (k : ℝ) ^ 2 = polA0 s (1 / k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  unfold coefA0 polA0
  field_simp
  ring

theorem coefBR1_eq_u : coefBR1 k s = numBR1 s (1 / k) / denB1 (1 / k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have h1 : (0 : ℝ) < 2 * k + 1 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 1 := by positivity
  have h3 : (0 : ℝ) < 4 * k + 3 := by positivity
  unfold coefBR1 shB0 numBR1 denB1
  field_simp
  ring

theorem coefBR2_eq_u : coefBR2 k s = numBR2 s (1 / k) / denB2 (1 / k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have h1 : (0 : ℝ) < 2 * k + 3 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 5 := by positivity
  have h3 : (0 : ℝ) < 4 * k + 7 := by positivity
  have h4 : (0 : ℝ) < k + 2 := by positivity
  unfold coefBR2 shB8 numBR2 denB2
  field_simp
  ring

theorem coefB0_eq_u : coefB0 k s / (k : ℝ) ^ 2 = polB0 s (1 / k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  unfold coefB0 polB0
  field_simp
  ring

theorem coefAR1_eq_y : (k : ℝ) * coefAR1 k s = ynumAR1 (k * s) (1 / k) / denA1 (1 / k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have h1 : (0 : ℝ) < 2 * k + 1 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 1 := by positivity
  have h3 : (0 : ℝ) < 4 * k + 3 := by positivity
  unfold coefAR1 shA0 ynumAR1 denA1
  field_simp
  ring

theorem coefAR2_eq_y : (k : ℝ) * coefAR2 k s = ynumAR2 (k * s) (1 / k) / denA2 (1 / k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have h1 : (0 : ℝ) < 2 * k + 3 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 5 := by positivity
  have h3 : (0 : ℝ) < 4 * k + 7 := by positivity
  have h4 : (0 : ℝ) < k + 2 := by positivity
  unfold coefAR2 shA8 ynumAR2 denA2
  field_simp
  ring

theorem coefA0_eq_y : coefA0 k s / (k : ℝ) = ypolA0 (k * s) (1 / k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  unfold coefA0 ypolA0
  field_simp
  ring

theorem coefBR1_eq_y : (k : ℝ) * coefBR1 k s = ynumBR1 (k * s) (1 / k) / denB1 (1 / k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have h1 : (0 : ℝ) < 2 * k + 1 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 1 := by positivity
  have h3 : (0 : ℝ) < 4 * k + 3 := by positivity
  unfold coefBR1 shB0 ynumBR1 denB1
  field_simp
  ring

theorem coefBR2_eq_y : (k : ℝ) * coefBR2 k s = ynumBR2 (k * s) (1 / k) / denB2 (1 / k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have h1 : (0 : ℝ) < 2 * k + 3 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 5 := by positivity
  have h3 : (0 : ℝ) < 4 * k + 7 := by positivity
  have h4 : (0 : ℝ) < k + 2 := by positivity
  unfold coefBR2 shB8 ynumBR2 denB2
  field_simp
  ring

theorem coefB0_eq_y : coefB0 k s / (k : ℝ) = ypolB0 (k * s) (1 / k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  unfold coefB0 ypolB0
  field_simp
  ring

end identities

/-! ## Generic limit lemmas -/

theorem tendsto_num_div_den {num den : ℝ → ℝ} (hn : Continuous num) (hd : Continuous den)
    (h0 : den 0 ≠ 0) :
    Tendsto (fun k : ℕ => num (1 / (k : ℝ)) / den (1 / (k : ℝ))) atTop (𝓝 (num 0 / den 0)) :=
  ((hn.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat).div
    ((hd.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat) h0

theorem tendsto_num_div_den₂ {ι : Type*} {l : Filter ι} {num : ℝ → ℝ → ℝ} {den : ℝ → ℝ}
    (hn : Continuous (fun p : ℝ × ℝ => num p.1 p.2)) (hd : Continuous den) {Y : ℝ}
    (h0 : den 0 ≠ 0) {u y : ι → ℝ} (hu : Tendsto u l (𝓝 0)) (hy : Tendsto y l (𝓝 Y)) :
    Tendsto (fun j => num (y j) (u j) / den (u j)) l (𝓝 (num Y 0 / den 0)) := by
  have h1 : Tendsto (fun j => num (y j) (u j)) l (𝓝 (num Y 0)) :=
    (hn.tendsto (Y, 0)).comp (hy.prodMk_nhds hu)
  exact h1.div ((hd.tendsto 0).comp hu) h0

/-! ## Fixed-`σ` limits -/

theorem tendsto_coefAR1 (s : ℝ) :
    Tendsto (fun k : ℕ => coefAR1 k s) atTop (𝓝 (-4 * s * (2 * s ^ 2 - 1))) := by
  have h := tendsto_num_div_den (num := numAR1 s) (den := denA1)
    (by unfold numAR1; fun_prop) (by unfold denA1; fun_prop) (by unfold denA1; norm_num)
  have hv : numAR1 s 0 / denA1 0 = -4 * s * (2 * s ^ 2 - 1) := by unfold numAR1 denA1; ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact (coefAR1_eq_u hk s).symm

theorem tendsto_coefAR2 (s : ℝ) :
    Tendsto (fun k : ℕ => coefAR2 k s) atTop (𝓝 (-4 * s * (2 * s ^ 2 - 1))) := by
  have h := tendsto_num_div_den (num := numAR2 s) (den := denA2)
    (by unfold numAR2; fun_prop) (by unfold denA2; fun_prop) (by unfold denA2; norm_num)
  have hv : numAR2 s 0 / denA2 0 = -4 * s * (2 * s ^ 2 - 1) := by unfold numAR2 denA2; ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact (coefAR2_eq_u hk s).symm

theorem tendsto_coefA0_div_sq (s : ℝ) :
    Tendsto (fun k : ℕ => coefA0 k s / (k : ℝ) ^ 2) atTop (𝓝 (32 * s)) := by
  have h : Tendsto (fun k : ℕ => polA0 s (1 / (k : ℝ))) atTop (𝓝 (polA0 s 0)) :=
    ((by unfold polA0; fun_prop : Continuous (polA0 s)).tendsto 0).comp
      tendsto_one_div_atTop_nhds_zero_nat
  have hv : polA0 s 0 = 32 * s := by unfold polA0; ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact (coefA0_eq_u hk s).symm

theorem tendsto_coefBR1 (s : ℝ) :
    Tendsto (fun k : ℕ => coefBR1 k s) atTop (𝓝 (4 * s ^ 2)) := by
  have h := tendsto_num_div_den (num := numBR1 s) (den := denB1)
    (by unfold numBR1; fun_prop) (by unfold denB1; fun_prop) (by unfold denB1; norm_num)
  have hv : numBR1 s 0 / denB1 0 = 4 * s ^ 2 := by unfold numBR1 denB1; ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact (coefBR1_eq_u hk s).symm

theorem tendsto_coefBR2 (s : ℝ) :
    Tendsto (fun k : ℕ => coefBR2 k s) atTop (𝓝 (4 * s ^ 2 * (4 * s ^ 2 - 3))) := by
  have h := tendsto_num_div_den (num := numBR2 s) (den := denB2)
    (by unfold numBR2; fun_prop) (by unfold denB2; fun_prop) (by unfold denB2; norm_num)
  have hv : numBR2 s 0 / denB2 0 = 4 * s ^ 2 * (4 * s ^ 2 - 3) := by unfold numBR2 denB2; ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact (coefBR2_eq_u hk s).symm

theorem tendsto_coefB0_div_sq (s : ℝ) :
    Tendsto (fun k : ℕ => coefB0 k s / (k : ℝ) ^ 2) atTop (𝓝 (-32 * s ^ 2)) := by
  have h : Tendsto (fun k : ℕ => polB0 s (1 / (k : ℝ))) atTop (𝓝 (polB0 s 0)) :=
    ((by unfold polB0; fun_prop : Continuous (polB0 s)).tendsto 0).comp
      tendsto_one_div_atTop_nhds_zero_nat
  have hv : polB0 s 0 = -32 * s ^ 2 := by unfold polB0; ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact (coefB0_eq_u hk s).symm

theorem radProd1_div_sq_eq (k : ℕ) : radProd1 k / (k : ℝ) ^ 2 = beatQuot k 0 1 := by
  unfold radProd1 beatQuot
  rfl

theorem radProd2_div_sq_eq (k : ℕ) : radProd2 k / (k : ℝ) ^ 2 = beatQuot k 2 3 := rfl

theorem tendsto_radProd1_div_sq : Tendsto (fun k : ℕ => radProd1 k / (k : ℝ) ^ 2) atTop (𝓝 4) := by
  simp_rw [radProd1_div_sq_eq]
  exact tendsto_beatQuot 0 1

theorem tendsto_radProd2_div_sq : Tendsto (fun k : ℕ => radProd2 k / (k : ℝ) ^ 2) atTop (𝓝 4) := by
  simp_rw [radProd2_div_sq_eq]
  exact tendsto_beatQuot 2 3

/-- `a(k, σ)/k² → 64 σ (1 − σ²)`. -/
theorem tendsto_twoIndexA_div_sq (s : ℝ) :
    Tendsto (fun k : ℕ => twoIndexA k s / (k : ℝ) ^ 2) atTop (𝓝 (64 * s * (1 - s ^ 2))) := by
  have h := ((tendsto_radProd1_div_sq.mul (tendsto_coefAR1 s)).add
    (tendsto_radProd2_div_sq.mul (tendsto_coefAR2 s))).add (tendsto_coefA0_div_sq s)
  have hv : (4 * (-4 * s * (2 * s ^ 2 - 1)) + 4 * (-4 * s * (2 * s ^ 2 - 1)) + 32 * s) =
      64 * s * (1 - s ^ 2) := by ring
  rw [hv] at h
  refine h.congr' (Eventually.of_forall fun k => ?_)
  unfold twoIndexA
  ring

/-- `b(k, σ)/k² → −64 σ² (1 − σ²)`. -/
theorem tendsto_twoIndexB_div_sq (s : ℝ) :
    Tendsto (fun k : ℕ => twoIndexB k s / (k : ℝ) ^ 2) atTop (𝓝 (-64 * s ^ 2 * (1 - s ^ 2))) := by
  have h := ((tendsto_radProd1_div_sq.mul (tendsto_coefBR1 s)).add
    (tendsto_radProd2_div_sq.mul (tendsto_coefBR2 s))).add (tendsto_coefB0_div_sq s)
  have hv : (4 * (4 * s ^ 2) + 4 * (4 * s ^ 2 * (4 * s ^ 2 - 3)) + -32 * s ^ 2) =
      -64 * s ^ 2 * (1 - s ^ 2) := by ring
  rw [hv] at h
  refine h.congr' (Eventually.of_forall fun k => ?_)
  unfold twoIndexB
  ring

/-! ## Scaling-regime limits -/

namespace ScalingLimits

open RouteJProfile.ScalingData

variable (D : RouteJProfile.ScalingData)

theorem tendsto_k_inv' : Tendsto (fun j => 1 / (D.k j : ℝ)) atTop (𝓝 0) := by
  simpa only [one_div] using D.tendsto_k_inv

theorem eventually_k_ge (m : ℕ) : ∀ᶠ j in atTop, m ≤ D.k j :=
  D.tendsto_k_nat.eventually (eventually_ge_atTop m)

theorem tendsto_radProd1_div_sq :
    Tendsto (fun j => radProd1 (D.k j) / (D.k j : ℝ) ^ 2) atTop (𝓝 4) :=
  RouteJUniform.tendsto_radProd1_div_sq.comp D.tendsto_k_nat

theorem tendsto_radProd2_div_sq :
    Tendsto (fun j => radProd2 (D.k j) / (D.k j : ℝ) ^ 2) atTop (𝓝 4) :=
  RouteJUniform.tendsto_radProd2_div_sq.comp D.tendsto_k_nat

theorem tendsto_k_mul_coefAR1 :
    Tendsto (fun j => (D.k j : ℝ) * coefAR1 (D.k j) (D.σ j)) atTop (𝓝 (4 * D.X)) := by
  have h := tendsto_num_div_den₂ (num := ynumAR1) (den := denA1)
    (by unfold ynumAR1; fun_prop) (by unfold denA1; fun_prop) (by unfold denA1; norm_num)
    (tendsto_k_inv' D) D.tendsto_k_mul_σ
  have hv : ynumAR1 D.X 0 / denA1 0 = 4 * D.X := by unfold ynumAR1 denA1; ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_k_ge D 1] with j hj
  exact (coefAR1_eq_y hj (D.σ j)).symm

theorem tendsto_k_mul_coefAR2 :
    Tendsto (fun j => (D.k j : ℝ) * coefAR2 (D.k j) (D.σ j)) atTop (𝓝 (4 * D.X)) := by
  have h := tendsto_num_div_den₂ (num := ynumAR2) (den := denA2)
    (by unfold ynumAR2; fun_prop) (by unfold denA2; fun_prop) (by unfold denA2; norm_num)
    (tendsto_k_inv' D) D.tendsto_k_mul_σ
  have hv : ynumAR2 D.X 0 / denA2 0 = 4 * D.X := by unfold ynumAR2 denA2; ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_k_ge D 1] with j hj
  exact (coefAR2_eq_y hj (D.σ j)).symm

theorem tendsto_coefA0_div_k :
    Tendsto (fun j => coefA0 (D.k j) (D.σ j) / (D.k j : ℝ)) atTop (𝓝 (32 * D.X)) := by
  have h : Tendsto (fun j => ypolA0 ((D.k j : ℝ) * D.σ j) (1 / (D.k j : ℝ))) atTop
      (𝓝 (ypolA0 D.X 0)) :=
    ((by unfold ypolA0; fun_prop : Continuous (fun p : ℝ × ℝ => ypolA0 p.1 p.2)).tendsto
      (D.X, 0)).comp (D.tendsto_k_mul_σ.prodMk_nhds (tendsto_k_inv' D))
  have hv : ypolA0 D.X 0 = 32 * D.X := by unfold ypolA0; ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_k_ge D 1] with j hj
  exact (coefA0_eq_y hj (D.σ j)).symm

theorem tendsto_k_mul_coefBR1 :
    Tendsto (fun j => (D.k j : ℝ) * coefBR1 (D.k j) (D.σ j)) atTop (𝓝 (-1 / 2)) := by
  have h := tendsto_num_div_den₂ (num := ynumBR1) (den := denB1)
    (by unfold ynumBR1; fun_prop) (by unfold denB1; fun_prop) (by unfold denB1; norm_num)
    (tendsto_k_inv' D) D.tendsto_k_mul_σ
  have hv : ynumBR1 D.X 0 / denB1 0 = -1 / 2 := by unfold ynumBR1 denB1; ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_k_ge D 1] with j hj
  exact (coefBR1_eq_y hj (D.σ j)).symm

theorem tendsto_k_mul_coefBR2 :
    Tendsto (fun j => (D.k j : ℝ) * coefBR2 (D.k j) (D.σ j)) atTop (𝓝 (-1 / 2)) := by
  have h := tendsto_num_div_den₂ (num := ynumBR2) (den := denB2)
    (by unfold ynumBR2; fun_prop) (by unfold denB2; fun_prop) (by unfold denB2; norm_num)
    (tendsto_k_inv' D) D.tendsto_k_mul_σ
  have hv : ynumBR2 D.X 0 / denB2 0 = -1 / 2 := by unfold ynumBR2 denB2; ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_k_ge D 1] with j hj
  exact (coefBR2_eq_y hj (D.σ j)).symm

theorem tendsto_coefB0_div_k :
    Tendsto (fun j => coefB0 (D.k j) (D.σ j) / (D.k j : ℝ)) atTop (𝓝 12) := by
  have h : Tendsto (fun j => ypolB0 ((D.k j : ℝ) * D.σ j) (1 / (D.k j : ℝ))) atTop
      (𝓝 (ypolB0 D.X 0)) :=
    ((by unfold ypolB0; fun_prop : Continuous (fun p : ℝ × ℝ => ypolB0 p.1 p.2)).tendsto
      (D.X, 0)).comp (D.tendsto_k_mul_σ.prodMk_nhds (tendsto_k_inv' D))
  have hv : ypolB0 D.X 0 = 12 := by unfold ypolB0; ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_k_ge D 1] with j hj
  exact (coefB0_eq_y hj (D.σ j)).symm

/-- `a(k_j, σ_j)/k_j → 64 X`. -/
theorem tendsto_twoIndexA_div_k :
    Tendsto (fun j => twoIndexA (D.k j) (D.σ j) / (D.k j : ℝ)) atTop (𝓝 (64 * D.X)) := by
  have h := (((tendsto_radProd1_div_sq D).mul (tendsto_k_mul_coefAR1 D)).add
    ((tendsto_radProd2_div_sq D).mul (tendsto_k_mul_coefAR2 D))).add (tendsto_coefA0_div_k D)
  have hv : (4 * (4 * D.X) + 4 * (4 * D.X) + 32 * D.X) = 64 * D.X := by ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_k_ge D 1] with j hj
  have hk0 : (D.k j : ℝ) ≠ 0 := by exact_mod_cast (by omega : D.k j ≠ 0)
  unfold twoIndexA
  field_simp

/-- `b(k_j, σ_j)/k_j → 8`. -/
theorem tendsto_twoIndexB_div_k :
    Tendsto (fun j => twoIndexB (D.k j) (D.σ j) / (D.k j : ℝ)) atTop (𝓝 8) := by
  have h := (((tendsto_radProd1_div_sq D).mul (tendsto_k_mul_coefBR1 D)).add
    ((tendsto_radProd2_div_sq D).mul (tendsto_k_mul_coefBR2 D))).add (tendsto_coefB0_div_k D)
  have hv : (4 * (-1 / 2) + 4 * (-1 / 2) + (12 : ℝ)) = 8 := by norm_num
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_k_ge D 1] with j hj
  have hk0 : (D.k j : ℝ) ≠ 0 := by exact_mod_cast (by omega : D.k j ≠ 0)
  unfold twoIndexB
  field_simp

end ScalingLimits

end RouteJUniform
end RHTower

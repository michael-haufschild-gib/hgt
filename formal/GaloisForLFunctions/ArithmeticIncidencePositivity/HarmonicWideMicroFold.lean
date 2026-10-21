import GaloisForLFunctions.ArithmeticIncidencePositivity.OverlappingPrimeStripsJointHarnack
import GaloisForLFunctions.ArithmeticIncidencePositivity.FirstPrimeOddPartPaymentWall

/-!
# The harmonic wide micro-fold: the even part of a pair group optimized away

On the strip `[p, r]`, `L = p + r`, a quadruple `x, L − x, y, L − y` has two pair groups. The
same-distance group carries the kernels `ω(t) − ω(L ± w)`, `t = |u − v|`, `w = u + v`; the crossing
group carries `ω(t') − ω(L ± w')`, `t' = u + v`, `w' = |u − v|`. Both pairs of a group see the odd
difference `D` and the same even difference `e`:
`K₁(D + e)² + K₂(D − e)² ≥ (4K₁K₂/(K₁ + K₂)) D²` (`harmonic_pair_ge`), the minimum over `e`.
The wide fold of `WideMicroFoldExactRates` keeps only `2 min(K₁, K₂)`; the harmonic mean also keeps
a share of the excess `δ = ω(L − w) − ω(L + w)`.

* **Recovered rate** (`two_mul_add_le_harmonic`, `harmonic_group_ge`). If `cs w ≤ δ` and
  `cs w ≤ κ (ω(t) − ω(L − w))`, the group rate is at least `ω(t) − ω(L − w) + γ w`, `γ = cs/(2 + κ)`.
  At `L = log 2`, `δ ≥ (28/(9√2)) w ≥ 2.19 w` term by term in `ω = Σ e^{−(2k+½)t}`
  (`slope_mul_le_archLevyDensity_reflect`).
* **Shared band** (`two_mul_band_le_harmonic`, `harmonic_band_group_ge`). If the upper pair of the
  same-distance group keeps only the fraction `1 − θ` (the rest pays a second, inner strip
  `[c, r]`), the group rate is at least `ρ(ω(t) − ω(L − w))`, `ρ = 2(1 − θ)/(2 − θ)`, not `0`.
* **Quadruple and strip** (`harmonicQuadruple_ge`, `harmonicMicroFold_strip_ge`). With these rates
  and the gauge `β + t`, the `θ`-withheld surplus of `[p, r]²` is at least `λ ∫_p^r α²` once the
  harmonic weight integrates to `2λ` at every folded point. `foldedStrip_ge` is the strip
  inequality for any kernel and weight satisfying the quadruple inequality.
* **The integrated weight** (`integral_harmonicFoldWeight_ge`). The weight is the wide weight plus
  `2γ` times the recovered shares, whose integral is a polynomial (`integral_recovery_eq`), minus
  on the band the withheld part, bounded by `(2(1 − ρ)(u − (b + η)/2 + c_w(η − u)²) +
  2γ(u − b)(u² − b²))/(β + u)` (`integral_wideSameRate_band_le_simple`).
* **Splitting the box** (`integral_box_thetaWithheld_eq`): withholding `θ` of `[c, r]²` removes `θ`
  times the surplus of `[c, r]²`.
-/

open MeasureTheory Set Filter Topology intervalIntegral
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The harmonic mean of a pair group -/

/-- **A pair group with its even difference optimized away.** For `K₁, K₂ ≥ 0`:
`K₁(D + e)² + K₂(D − e)² ≥ (4K₁K₂/(K₁ + K₂)) D²`, the minimum over `e`. -/
theorem harmonic_pair_ge {K₁ K₂ D e : ℝ} (h1 : 0 ≤ K₁) (h2 : 0 ≤ K₂) :
    4 * K₁ * K₂ / (K₁ + K₂) * D ^ 2 ≤ K₁ * (D + e) ^ 2 + K₂ * (D - e) ^ 2 := by
  rcases eq_or_lt_of_le (add_nonneg h1 h2) with h0 | h0
  · rw [← h0, div_zero, zero_mul]; positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ h0]
  nlinarith [sq_nonneg ((K₁ - K₂) * D + (K₁ + K₂) * e)]

/-- **The recovered rate.** If `K₁ = K₂ + δ`, `0 ≤ δ' ≤ δ` and `δ' ≤ κ K₂`, the harmonic coefficient is at
least `2(K₂ + δ'/(2 + κ))`: the smaller kernel plus a share of the excess. -/
theorem two_mul_add_le_harmonic {K₂ δ δ' κ : ℝ} (hK : 0 ≤ K₂) (hκ : 0 ≤ κ) (hδ' : 0 ≤ δ')
    (hδδ : δ' ≤ δ) (hδκ : δ' ≤ κ * K₂) :
    2 * (K₂ + δ' / (2 + κ)) ≤ 4 * (K₂ + δ) * K₂ / ((K₂ + δ) + K₂) := by
  have hδ : 0 ≤ δ := hδ'.trans hδδ
  rcases eq_or_lt_of_le (show 0 ≤ 2 * K₂ + δ by linarith) with h0 | h0
  · have hK0 : K₂ = 0 := by linarith
    have hd0 : δ = 0 := by linarith
    have : δ' = 0 := by linarith
    subst hK0; subst hd0; subst this; simp
  rw [show (K₂ + δ) + K₂ = 2 * K₂ + δ by ring, le_div_iff₀ h0]
  have h2κ : 0 < 2 + κ := by linarith
  have e : δ' / (2 + κ) * (2 * K₂ + δ) * (2 + κ) = δ' * (2 * K₂ + δ) := by field_simp
  have key : δ' / (2 + κ) * (2 * K₂ + δ) ≤ K₂ * δ := by
    rw [← mul_le_mul_iff_of_pos_right h2κ, e]
    nlinarith [mul_le_mul_of_nonneg_left hδδ hK, mul_le_mul_of_nonneg_left hδκ hδ]
  nlinarith [key]

/-- **The band rate.** If the larger kernel keeps only the fraction `1 − θ`, the harmonic coefficient is at
least `2ρK₂`, `ρ = 2(1 − θ)/(2 − θ)`. -/
theorem two_mul_band_le_harmonic {K₁ K₂ θ : ℝ} (hK : 0 ≤ K₂) (h12 : K₂ ≤ K₁) (hθ1 : θ ≤ 1) :
    2 * (2 * (1 - θ) / (2 - θ) * K₂) ≤ 4 * ((1 - θ) * K₁) * K₂ / ((1 - θ) * K₁ + K₂) := by
  have h2θ : 0 < 2 - θ := by linarith
  rcases eq_or_lt_of_le (show 0 ≤ (1 - θ) * K₁ + K₂ by nlinarith) with h0 | h0
  · have hK0 : K₂ = 0 := by nlinarith
    rw [hK0]; simp
  rw [le_div_iff₀ h0]
  have e : 2 * (2 * (1 - θ) / (2 - θ) * K₂) * ((1 - θ) * K₁ + K₂) * (2 - θ) =
      4 * (1 - θ) * K₂ * ((1 - θ) * K₁ + K₂) := by field_simp; ring
  rw [← mul_le_mul_iff_of_pos_right h2θ, e]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hθ1) hK) (sub_nonneg.2 h12)]

/-! ### The reflected slope of `ω` at `log 2` -/

/-- `e^{−(2k + ½) log 2} = (1/4)^k / √2`. -/
theorem exp_neg_mode_logTwo (k : ℕ) :
    Real.exp (-(2 * (k : ℝ) + 1 / 2) * Real.log 2) = (1 / 4) ^ k * Real.exp (-(Real.log 2 / 2)) := by
  have e : -(2 * (k : ℝ) + 1 / 2) * Real.log 2 = (k : ℝ) * (-(2 * Real.log 2)) + -(Real.log 2 / 2) := by
    ring
  rw [e, Real.exp_add, Real.exp_nat_mul]
  congr 2
  rw [show -(2 * Real.log 2) = -Real.log 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring, Real.exp_neg,
    Real.exp_log (by norm_num)]
  norm_num

/-- **The reflected slope at `log 2`.** `ω(log 2 − w) − ω(log 2 + w) ≥ (28/(9√2)) w ≥ 2.19 w` for
`0 ≤ w < log 2`: term by term `e^{−c(L−w)} − e^{−c(L+w)} ≥ 2cw e^{−cL}`, and
`Σ (2k + ½) e^{−(2k+½) log 2} = 14/(9√2)`. -/
theorem slope_mul_le_archLevyDensity_reflect {w : ℝ} (hw0 : 0 ≤ w) (hw : w < Real.log 2) :
    219 / 100 * w ≤ archLevyDensity (Real.log 2 - w) - archLevyDensity (Real.log 2 + w) := by
  have hL := Real.log_two_gt_d9
  have h1 := RHTower.ArchimedeanAnomaly.hasSum_archLevyDensity (show 0 < Real.log 2 - w by linarith)
  have h2 := RHTower.ArchimedeanAnomaly.hasSum_archLevyDensity (show 0 < Real.log 2 + w by linarith)
  set E := Real.exp (-(Real.log 2 / 2)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- the lower series `Σ 2(2k + ½) w (1/4)^k E`
  have g1 : HasSum (fun k : ℕ => (1 / 4 : ℝ) ^ k) (4 / 3) := by
    have := hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
    norm_num at this ⊢; exact this
  have g2 : HasSum (fun k : ℕ => (k : ℝ) * (1 / 4 : ℝ) ^ k) (4 / 9) := by
    have := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := 1 / 4) (by norm_num)
    norm_num at this ⊢; exact this
  have g : HasSum (fun k : ℕ => 2 * (2 * (k : ℝ) + 1 / 2) * w * ((1 / 4) ^ k * E))
      (2 * w * E * (2 * (4 / 9) + 1 / 2 * (4 / 3))) := by
    have := ((g2.mul_left 2).add (g1.mul_left (1 / 2))).mul_left (2 * w * E)
    refine this.congr_fun fun k => ?_
    ring
  have hle := hasSum_le (fun k => ?_) g (h1.sub h2)
  · -- `E = 1/√2 ≥ 0.7071`
    have hE1 : 0.7071 ≤ E := by
      have hs : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
        rw [Real.sqrt_eq_rpow, ← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_mul]
        rw [Real.log_exp]; ring_nf
      rw [hE, Real.exp_neg, hs]
      have : Real.sqrt 2 ≤ 1.41422 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      rw [le_inv_comm₀ (by norm_num) (Real.sqrt_pos.mpr (by norm_num))]
      calc Real.sqrt 2 ≤ 1.41422 := this
        _ ≤ 0.7071⁻¹ := by norm_num
    nlinarith
  · have hc : 0 ≤ 2 * (k : ℝ) + 1 / 2 := by positivity
    show 2 * (2 * (k : ℝ) + 1 / 2) * w * ((1 / 4) ^ k * E) ≤
      Real.exp (-(2 * (k : ℝ) + 1 / 2) * (Real.log 2 - w)) - Real.exp (-(2 * (k : ℝ) + 1 / 2) * (Real.log 2 + w))
    have e1 : Real.exp (-(2 * (k : ℝ) + 1 / 2) * (Real.log 2 - w)) =
        Real.exp (-(2 * (k : ℝ) + 1 / 2) * Real.log 2) * Real.exp ((2 * (k : ℝ) + 1 / 2) * w) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(2 * (k : ℝ) + 1 / 2) * (Real.log 2 + w)) =
        Real.exp (-(2 * (k : ℝ) + 1 / 2) * Real.log 2) * Real.exp (-((2 * (k : ℝ) + 1 / 2) * w)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2, exp_neg_mode_logTwo k, ← hE]
    have hsinh : (2 * (k : ℝ) + 1 / 2) * w ≤ Real.sinh ((2 * (k : ℝ) + 1 / 2) * w) :=
      Real.self_le_sinh_iff.mpr (mul_nonneg hc hw0)
    rw [Real.sinh_eq] at hsinh
    have hq : 0 ≤ (1 / 4 : ℝ) ^ k * E := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsinh hq]

/-! ### The harmonic rates and the folded weight -/

/-- The harmonic rate of a pair group at distance `t` and reflected offset `w`:
`ω(t) − ω(L − w) + γ w`, the smaller kernel plus a share `γ w` of the excess `ω(L − w) − ω(L + w)`. -/
def harmonicRate (L γ t w : ℝ) : ℝ := archLevyDensity t - archLevyDensity (L - w) + γ * w

/-- The same-distance rate; on the band `u, v ≥ b`, where the upper pair is shared, `ρ R₋`. -/
def harmonicSameRate (L γ b ρ u v : ℝ) : ℝ :=
  if b ≤ u ∧ b ≤ v then ρ * wideSameRate L u v else harmonicRate L γ |u - v| (u + v)

/-- The crossing rate `R₊ + γ|u − v|`. -/
def harmonicCrossRate (L γ u v : ℝ) : ℝ := harmonicRate L γ (u + v) |u - v|

/-- The harmonic folded weight in the gauge `β + t`: `2(m₁ − m₂)(1 − (β + v)/(β + u)) + 4m₂`. -/
def harmonicFoldWeight (L β γ b ρ u v : ℝ) : ℝ :=
  2 * ((harmonicSameRate L γ b ρ u v - harmonicCrossRate L γ u v) * (1 - (β + v) / (β + u))) +
    4 * harmonicCrossRate L γ u v

theorem harmonicSameRate_comm (L γ b ρ u v : ℝ) :
    harmonicSameRate L γ b ρ v u = harmonicSameRate L γ b ρ u v := by
  unfold harmonicSameRate
  by_cases h : b ≤ u ∧ b ≤ v
  · rw [if_pos ⟨h.2, h.1⟩, if_pos h, wideSameRate_comm]
  · rw [if_neg (fun h' => h ⟨h'.2, h'.1⟩), if_neg h, abs_sub_comm, add_comm]

theorem harmonicCrossRate_comm (L γ u v : ℝ) : harmonicCrossRate L γ v u = harmonicCrossRate L γ u v := by
  unfold harmonicCrossRate; rw [abs_sub_comm, add_comm]

/-- **The folded pair with the harmonic rates.** -/
theorem harmonicFold_folded {L β γ b ρ u v a a' : ℝ} (hβ : 0 < β) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hdeg : 0 ≤ harmonicSameRate L γ b ρ u v - harmonicCrossRate L γ u v ∨ (u = v ∧ a = a')) :
    a ^ 2 * harmonicFoldWeight L β γ b ρ u v + a' ^ 2 * harmonicFoldWeight L β γ b ρ v u ≤
      2 * harmonicSameRate L γ b ρ u v * (a - a') ^ 2 + 2 * harmonicCrossRate L γ u v * (a + a') ^ 2 := by
  have hβu : 0 < β + u := by positivity
  have hβv : 0 < β + v := by positivity
  have hq : 0 < (β + v) / (β + u) := div_pos hβv hβu
  have hqinv : (β + u) / (β + v) = 1 / ((β + v) / (β + u)) := by field_simp
  unfold harmonicFoldWeight
  rw [harmonicSameRate_comm L γ b ρ u v, harmonicCrossRate_comm L γ u v, hqinv]
  refine sharpFold_core hq rfl ?_
  rcases hdeg with h | ⟨huv, haa⟩
  · exact Or.inl h
  · exact Or.inr ⟨haa, by rw [huv, div_self hβv.ne']⟩

/-! ### Pair groups at their harmonic rates -/

/-- **A pair group at its recovered rate.** For `t > 0`, `w ≥ 0`, `t + w < L`, kernels
`ω(t) − ω(L ± w)` in either order, the slope `cs w ≤ ω(L − w) − ω(L + w)` and `cs w ≤ κ(ω(t) − ω(L − w))`:
the group dominates `2 · harmonicRate · D²` with `γ = cs/(2 + κ)`. -/
theorem harmonic_group_ge {L κ cs t w D e K₁ K₂ : ℝ} (hκ : 0 ≤ κ) (ht : 0 < t) (htw : t + w < L) (hcs : 0 ≤ cs * w)
    (hslope : cs * w ≤ archLevyDensity (L - w) - archLevyDensity (L + w))
    (hcond : cs * w ≤ κ * (archLevyDensity t - archLevyDensity (L - w)))
    (hK : (K₁ = archLevyDensity t - archLevyDensity (L + w) ∧
        K₂ = archLevyDensity t - archLevyDensity (L - w)) ∨
      (K₁ = archLevyDensity t - archLevyDensity (L - w) ∧
        K₂ = archLevyDensity t - archLevyDensity (L + w))) :
    2 * harmonicRate L (cs / (2 + κ)) t w * D ^ 2 ≤ K₁ * (D + e) ^ 2 + K₂ * (D - e) ^ 2 := by
  set B := archLevyDensity t - archLevyDensity (L - w) with hB
  set δ := archLevyDensity (L - w) - archLevyDensity (L + w) with hδ
  have hB0 : 0 ≤ B := by
    have := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr ht)
      (mem_Ioi.mpr (by linarith : 0 < L - w)) (by linarith)
    rw [hB]; linarith
  have hA : archLevyDensity t - archLevyDensity (L + w) = B + δ := by rw [hB, hδ]; ring
  have hH := two_mul_add_le_harmonic hB0 hκ hcs hslope hcond
  have hrate : harmonicRate L (cs / (2 + κ)) t w = B + cs * w / (2 + κ) := by
    unfold harmonicRate; rw [hB]; ring
  have hsym : 4 * K₁ * K₂ / (K₁ + K₂) = 4 * (B + δ) * B / ((B + δ) + B) := by
    rcases hK with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hA]
    · rw [h1, h2, hA]; ring_nf
  have hK0 : 0 ≤ K₁ ∧ 0 ≤ K₂ := by
    have : 0 ≤ B + δ := by linarith
    rcases hK with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hA]; exact ⟨this, hB0⟩
    · rw [h1, h2, hA]; exact ⟨hB0, this⟩
  have hp := harmonic_pair_ge (D := D) (e := e) hK0.1 hK0.2
  rw [hsym] at hp
  rw [hrate]
  nlinarith [mul_le_mul_of_nonneg_right hH (sq_nonneg D)]

/-- **A pair group on the shared band.** If the larger kernel `ω(t) − ω(L + w)` keeps only the fraction
`1 − θ`, the group dominates `2ρ(ω(t) − ω(L − w)) D²`, `ρ = 2(1 − θ)/(2 − θ)`. -/
theorem harmonic_band_group_ge {L θ t w D e K₁ K₂ : ℝ} (ht : 0 < t) (hw : 0 ≤ w) (htw : t + w < L)
    (hθ1 : θ ≤ 1)
    (hK : (K₁ = (1 - θ) * (archLevyDensity t - archLevyDensity (L + w)) ∧
        K₂ = archLevyDensity t - archLevyDensity (L - w)) ∨
      (K₁ = archLevyDensity t - archLevyDensity (L - w) ∧
        K₂ = (1 - θ) * (archLevyDensity t - archLevyDensity (L + w)))) :
    2 * (2 * (1 - θ) / (2 - θ) * (archLevyDensity t - archLevyDensity (L - w))) * D ^ 2 ≤
      K₁ * (D + e) ^ 2 + K₂ * (D - e) ^ 2 := by
  set A := archLevyDensity t - archLevyDensity (L + w) with hA
  set B := archLevyDensity t - archLevyDensity (L - w) with hB
  have hB0 : 0 ≤ B := by
    have := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr ht)
      (mem_Ioi.mpr (by linarith : 0 < L - w)) (by linarith)
    rw [hB]; linarith
  have hBA : B ≤ A := by
    have := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith : 0 < L - w))
      (mem_Ioi.mpr (by linarith : 0 < L + w)) (by linarith)
    rw [hA, hB]; linarith
  have hH := two_mul_band_le_harmonic hB0 hBA hθ1
  have hA0 : 0 ≤ (1 - θ) * A := mul_nonneg (by linarith) (hB0.trans hBA)
  have hsym : 4 * K₁ * K₂ / (K₁ + K₂) = 4 * ((1 - θ) * A) * B / ((1 - θ) * A + B) := by
    rcases hK with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]; ring_nf
  have hK0 : 0 ≤ K₁ ∧ 0 ≤ K₂ := by
    rcases hK with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨hA0, hB0⟩
    · rw [h1, h2]; exact ⟨hB0, hA0⟩
  have hp := harmonic_pair_ge (D := D) (e := e) hK0.1 hK0.2
  rw [hsym] at hp
  nlinarith [mul_le_mul_of_nonneg_right hH (sq_nonneg D)]

/-! ### The harmonic quadruple inequality -/

/-- The surplus kernel with the fraction `θ` of the pairs of `[c, ∞)²` withheld. -/
def thetaWithheldKernel (c θ x y : ℝ) : ℝ :=
  if c ≤ x ∧ c ≤ y then (1 - θ) * surplusKernel x y else surplusKernel x y

/-- The four surplus terms of the quadruple `x, L − x, y, L − y` for a kernel `k`. -/
def quadrupleSum (k : ℝ → ℝ → ℝ) (F : ℝ → ℝ) (L x y : ℝ) : ℝ :=
  k x y * (F x - F y) ^ 2 + k (L - x) (L - y) * (F (L - x) - F (L - y)) ^ 2 +
    k x (L - y) * (F x - F (L - y)) ^ 2 + k (L - x) y * (F (L - x) - F y) ^ 2

theorem quadrupleSum_reflect_left (k : ℝ → ℝ → ℝ) (F : ℝ → ℝ) (L x y : ℝ) :
    quadrupleSum k F L (L - x) y = quadrupleSum k F L x y := by
  unfold quadrupleSum; rw [sub_sub_cancel]; ring

theorem quadrupleSum_reflect_right (k : ℝ → ℝ → ℝ) (F : ℝ → ℝ) (L x y : ℝ) :
    quadrupleSum k F L x (L - y) = quadrupleSum k F L x y := by
  unfold quadrupleSum; rw [sub_sub_cancel]; ring

section HarmonicQuadruple

/-- The four differences of a quadruple in odd and even parts about `L/2`. -/
theorem quadruple_differences (F : ℝ → ℝ) (L x y : ℝ) :
    F x - F y = (reflectedOddPart F L x - reflectedOddPart F L y) +
        ((F x + F (L - x)) / 2 - (F y + F (L - y)) / 2) ∧
      F (L - x) - F (L - y) = -((reflectedOddPart F L x - reflectedOddPart F L y) -
        ((F x + F (L - x)) / 2 - (F y + F (L - y)) / 2)) ∧
      F x - F (L - y) = (reflectedOddPart F L x + reflectedOddPart F L y) +
        ((F x + F (L - x)) / 2 - (F y + F (L - y)) / 2) ∧
      F (L - x) - F y = -((reflectedOddPart F L x + reflectedOddPart F L y) -
        ((F x + F (L - x)) / 2 - (F y + F (L - y)) / 2)) := by
  unfold reflectedOddPart
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- The four surplus kernels of a right-half quadruple in folded coordinates. -/
theorem surplusKernel_quadruple_folded {L u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    surplusKernel (L / 2 + u) (L / 2 + v) = archLevyDensity |u - v| - archLevyDensity (L + (u + v)) ∧
      surplusKernel (L - (L / 2 + u)) (L - (L / 2 + v)) =
        archLevyDensity |u - v| - archLevyDensity (L - (u + v)) ∧
      surplusKernel (L / 2 + u) (L - (L / 2 + v)) =
        archLevyDensity (u + v) - archLevyDensity (L + (u - v)) ∧
      surplusKernel (L - (L / 2 + u)) (L / 2 + v) =
        archLevyDensity (u + v) - archLevyDensity (L - (u - v)) := by
  unfold surplusKernel
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show L / 2 + u - (L / 2 + v) = u - v by ring]; congr 2; ring
  · rw [show L - (L / 2 + u) - (L - (L / 2 + v)) = -(u - v) by ring, abs_neg]; congr 2; ring
  · rw [show L / 2 + u - (L - (L / 2 + v)) = u + v by ring, abs_of_nonneg (by linarith)]
    congr 2; ring
  · rw [show L - (L / 2 + u) - (L / 2 + v) = -(u + v) by ring, abs_neg, abs_of_nonneg (by linarith)]
    congr 2; ring

variable {p r L β cs κ c θ : ℝ} (hp : 0 < p) (hL : p + r = L) (hβ : 0 < β) (hκ : 0 ≤ κ)
  (hcs : 0 ≤ cs) (hθ1 : θ ≤ 1) (hcm : L / 2 < c)
  (hslope : ∀ w, 0 ≤ w → w ≤ r - p → cs * w ≤ archLevyDensity (L - w) - archLevyDensity (L + w))
  (hC1 : ∀ u v, 0 ≤ u → u ≤ (r - p) / 2 → 0 ≤ v → v ≤ (r - p) / 2 → u ≠ v →
    cs * (u + v) ≤ κ * wideSameRate L u v)
  (hC2 : ∀ u v, 0 ≤ u → u ≤ (r - p) / 2 → 0 ≤ v → v ≤ (r - p) / 2 → 0 < u + v →
    cs * |u - v| ≤ κ * wideCrossRate L u v)
  (hC3 : ∀ u v, c - L / 2 ≤ u → u ≤ (r - p) / 2 → c - L / 2 ≤ v → v ≤ (r - p) / 2 → u ≠ v →
    wideCrossRate L u v + cs / (2 + κ) * |u - v| ≤ 2 * (1 - θ) / (2 - θ) * wideSameRate L u v)

include hp hL hκ hcs hθ1 hcm hslope hC1 in
/-- The same-distance group of a right-half quadruple at the harmonic same rate. -/
theorem harmonicSameGroup_ge {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ (r - p) / 2) (hv0 : 0 ≤ v)
    (hv1 : v ≤ (r - p) / 2) (F : ℝ → ℝ) :
    2 * harmonicSameRate L (cs / (2 + κ)) (c - L / 2) (2 * (1 - θ) / (2 - θ)) u v *
        (reflectedOddPart F L (L / 2 + u) - reflectedOddPart F L (L / 2 + v)) ^ 2 ≤
      thetaWithheldKernel c θ (L / 2 + u) (L / 2 + v) * (F (L / 2 + u) - F (L / 2 + v)) ^ 2 +
        thetaWithheldKernel c θ (L - (L / 2 + u)) (L - (L / 2 + v)) *
          (F (L - (L / 2 + u)) - F (L - (L / 2 + v))) ^ 2 := by
  obtain ⟨d1, d2, -, -⟩ := quadruple_differences F L (L / 2 + u) (L / 2 + v)
  obtain ⟨s1, s2, -, -⟩ := surplusKernel_quadruple_folded (L := L) hu0 hv0
  set a := reflectedOddPart F L (L / 2 + u)
  set a' := reflectedOddPart F L (L / 2 + v)
  set e := (F (L / 2 + u) + F (L - (L / 2 + u))) / 2 - (F (L / 2 + v) + F (L - (L / 2 + v))) / 2
  have hk2 : thetaWithheldKernel c θ (L - (L / 2 + u)) (L - (L / 2 + v)) =
      surplusKernel (L - (L / 2 + u)) (L - (L / 2 + v)) := by
    unfold thetaWithheldKernel; rw [if_neg (fun h => by linarith [h.1])]
  rw [d1, d2, neg_sq, hk2]
  rcases eq_or_ne u v with huv | huv
  · subst huv
    have hd1 := d1
    rw [sub_self] at hd1
    have haa : a' = a := rfl
    have he : e = 0 := by rw [haa] at hd1; linarith
    rw [haa, he]; simp
  have ht : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
  have htw : |u - v| + (u + v) < L := by
    rcases le_total u v with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  unfold harmonicSameRate
  by_cases hB : c - L / 2 ≤ u ∧ c - L / 2 ≤ v
  · rw [if_pos hB]
    have hk1 : thetaWithheldKernel c θ (L / 2 + u) (L / 2 + v) =
        (1 - θ) * surplusKernel (L / 2 + u) (L / 2 + v) := by
      unfold thetaWithheldKernel; rw [if_pos ⟨by linarith [hB.1], by linarith [hB.2]⟩]
    rw [hk1]
    unfold wideSameRate
    exact harmonic_band_group_ge ht (by linarith) htw hθ1 (Or.inl ⟨by rw [s1], s2⟩)
  · rw [if_neg hB]
    have hk1 : thetaWithheldKernel c θ (L / 2 + u) (L / 2 + v) = surplusKernel (L / 2 + u) (L / 2 + v) := by
      unfold thetaWithheldKernel
      rw [if_neg (fun h => hB ⟨by linarith [h.1], by linarith [h.2]⟩)]
    rw [hk1]
    exact harmonic_group_ge hκ ht htw (mul_nonneg hcs (by linarith))
      (hslope _ (by linarith) (by linarith)) (hC1 u v hu0 hu1 hv0 hv1 huv) (Or.inl ⟨s1, s2⟩)

include hp hL hκ hcs hcm hslope hC2 in
/-- The crossing group of a right-half quadruple at the harmonic crossing rate. -/
theorem harmonicCrossGroup_ge {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ (r - p) / 2) (hv0 : 0 ≤ v)
    (hv1 : v ≤ (r - p) / 2) (F : ℝ → ℝ) :
    2 * harmonicCrossRate L (cs / (2 + κ)) u v *
        (reflectedOddPart F L (L / 2 + u) + reflectedOddPart F L (L / 2 + v)) ^ 2 ≤
      thetaWithheldKernel c θ (L / 2 + u) (L - (L / 2 + v)) * (F (L / 2 + u) - F (L - (L / 2 + v))) ^ 2 +
        thetaWithheldKernel c θ (L - (L / 2 + u)) (L / 2 + v) *
          (F (L - (L / 2 + u)) - F (L / 2 + v)) ^ 2 := by
  obtain ⟨-, -, d3, d4⟩ := quadruple_differences F L (L / 2 + u) (L / 2 + v)
  obtain ⟨-, -, s3, s4⟩ := surplusKernel_quadruple_folded (L := L) hu0 hv0
  set a := reflectedOddPart F L (L / 2 + u)
  set a' := reflectedOddPart F L (L / 2 + v)
  set e := (F (L / 2 + u) + F (L - (L / 2 + u))) / 2 - (F (L / 2 + v) + F (L - (L / 2 + v))) / 2
  have hk3 : thetaWithheldKernel c θ (L / 2 + u) (L - (L / 2 + v)) =
      surplusKernel (L / 2 + u) (L - (L / 2 + v)) := by
    unfold thetaWithheldKernel; rw [if_neg (fun h => by linarith [h.2])]
  have hk4 : thetaWithheldKernel c θ (L - (L / 2 + u)) (L / 2 + v) =
      surplusKernel (L - (L / 2 + u)) (L / 2 + v) := by
    unfold thetaWithheldKernel; rw [if_neg (fun h => by linarith [h.1])]
  rw [d3, d4, neg_sq, hk3, hk4]
  rcases eq_or_lt_of_le (add_nonneg hu0 hv0) with h0 | h0
  · have hu' : u = 0 := by linarith
    have hv' : v = 0 := by linarith
    subst hu' hv'
    have hS : a + a' = 0 := by
      show reflectedOddPart F L (L / 2 + 0) + reflectedOddPart F L (L / 2 + 0) = 0
      unfold reflectedOddPart; rw [show L - (L / 2 + 0) = L / 2 + 0 by ring]; ring
    have h3' : F (L / 2 + 0) - F (L - (L / 2 + 0)) = 0 := by
      rw [show L - (L / 2 + 0) = L / 2 + 0 by ring, sub_self]
    have h3 : (a + a') + e = 0 := by linarith [d3, h3']
    have h4 : (a + a') - e = 0 := by linarith [d3, h3', hS]
    rw [h3, h4, hS]; simp
  have htw : (u + v) + |u - v| < L := by
    rcases le_total u v with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  unfold harmonicCrossRate
  refine harmonic_group_ge hκ h0 htw (mul_nonneg hcs (abs_nonneg _))
    (hslope _ (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith))
    (hC2 u v hu0 hu1 hv0 hv1 h0) ?_
  rcases le_total v u with h | h
  · rw [abs_of_nonneg (by linarith)]; exact Or.inl ⟨s3, s4⟩
  · rw [abs_of_nonpos (by linarith), neg_sub]
    refine Or.inr ⟨?_, ?_⟩
    · rw [s3]; congr 2; ring
    · rw [s4]; congr 2; ring

include hp hL hκ hcs hC3 in
/-- The harmonic same rate dominates the crossing rate off the diagonal. -/
theorem harmonicSame_sub_cross_nonneg {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ (r - p) / 2) (hv0 : 0 ≤ v)
    (hv1 : v ≤ (r - p) / 2) (huv : u ≠ v) :
    0 ≤ harmonicSameRate L (cs / (2 + κ)) (c - L / 2) (2 * (1 - θ) / (2 - θ)) u v -
      harmonicCrossRate L (cs / (2 + κ)) u v := by
  unfold harmonicSameRate harmonicCrossRate
  by_cases hB : c - L / 2 ≤ u ∧ c - L / 2 ≤ v
  · rw [if_pos hB]
    have h := hC3 u v hB.1 hu1 hB.2 hv1 huv
    unfold harmonicRate
    unfold wideCrossRate at h
    linarith only [h]
  · rw [if_neg hB]
    have hsc := wideSameRate_sub_crossRate_nonneg (L := L) hu0 hv0 huv (by
      rcases le_total u v with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith)
    have hab : |u - v| ≤ u + v := abs_le.mpr ⟨by linarith, by linarith⟩
    have hγ0 : 0 ≤ cs / (2 + κ) := by positivity
    have hm := mul_le_mul_of_nonneg_left hab hγ0
    unfold harmonicRate
    unfold wideSameRate wideCrossRate at hsc
    linarith only [hsc, hm]

include hp hL hβ hκ hcs hθ1 hcm hslope hC1 hC2 hC3 in
/-- **The harmonic quadruple on the right half.** For `x, y ∈ [L/2, r]` the four `θ`-withheld surplus
terms dominate `α(x)² W(u, v) + α(y)² W(v, u)` with the harmonic weight. -/
theorem harmonicQuadruple_ge_right {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ (r - p) / 2) (hv0 : 0 ≤ v)
    (hv1 : v ≤ (r - p) / 2) (F : ℝ → ℝ) :
    reflectedOddPart F L (L / 2 + u) ^ 2 * harmonicFoldWeight L β (cs / (2 + κ)) (c - L / 2)
        (2 * (1 - θ) / (2 - θ)) u v +
      reflectedOddPart F L (L / 2 + v) ^ 2 * harmonicFoldWeight L β (cs / (2 + κ)) (c - L / 2)
        (2 * (1 - θ) / (2 - θ)) v u ≤
      quadrupleSum (thetaWithheldKernel c θ) F L (L / 2 + u) (L / 2 + v) := by
  have G1 := harmonicSameGroup_ge (θ := θ) hp hL hκ hcs hθ1 hcm hslope hC1 hu0 hu1 hv0 hv1 F
  have G2 := harmonicCrossGroup_ge (θ := θ) hp hL hκ hcs hcm hslope hC2 hu0 hu1 hv0 hv1 F
  have hdeg : 0 ≤ harmonicSameRate L (cs / (2 + κ)) (c - L / 2) (2 * (1 - θ) / (2 - θ)) u v -
      harmonicCrossRate L (cs / (2 + κ)) u v ∨
      (u = v ∧ reflectedOddPart F L (L / 2 + u) = reflectedOddPart F L (L / 2 + v)) := by
    rcases eq_or_ne u v with huv | huv
    · exact Or.inr ⟨huv, by rw [huv]⟩
    · exact Or.inl (harmonicSame_sub_cross_nonneg hp hL hκ hcs hC3 hu0 hu1 hv0 hv1 huv)
  have hf := harmonicFold_folded (L := L) (β := β) (γ := cs / (2 + κ)) (b := c - L / 2)
    (ρ := 2 * (1 - θ) / (2 - θ)) hβ hu0 hv0 hdeg
  unfold quadrupleSum
  linarith only [hf, G1, G2]


theorem reflectedOddPart_reflect (F : ℝ → ℝ) (L x : ℝ) :
    reflectedOddPart F L (L - x) = -reflectedOddPart F L x := by
  unfold reflectedOddPart; rw [sub_sub_cancel]; ring

/-- `L/2 + |x − L/2|` is `x` or `L − x`. -/
theorem half_add_abs_eq (L x : ℝ) : L / 2 + |x - L / 2| = x ∨ L / 2 + |x - L / 2| = L - x := by
  rcases le_total 0 (x - L / 2) with h | h
  · left; rw [abs_of_nonneg h]; ring
  · right; rw [abs_of_nonpos h]; ring

include hp hL hβ hκ hcs hθ1 hcm hslope hC1 hC2 hC3 in
/-- **The harmonic quadruple inequality.** For `x, y ∈ [p, r]`, `p + r = L`, the four `θ`-withheld
surplus terms of `x, L − x, y, L − y` dominate `α(x)² W(u, v) + α(y)² W(v, u)`,
`u = |x − L/2|`, `v = |y − L/2|`. -/
theorem harmonicQuadruple_ge {x y : ℝ} (hx : x ∈ Icc p r) (hy : y ∈ Icc p r) (F : ℝ → ℝ) :
    reflectedOddPart F L x ^ 2 * harmonicFoldWeight L β (cs / (2 + κ)) (c - L / 2)
        (2 * (1 - θ) / (2 - θ)) |x - L / 2| |y - L / 2| +
      reflectedOddPart F L y ^ 2 * harmonicFoldWeight L β (cs / (2 + κ)) (c - L / 2)
        (2 * (1 - θ) / (2 - θ)) |y - L / 2| |x - L / 2| ≤
      quadrupleSum (thetaWithheldKernel c θ) F L x y := by
  have hu1 : |x - L / 2| ≤ (r - p) / 2 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hv1 : |y - L / 2| ≤ (r - p) / 2 := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  have h := harmonicQuadruple_ge_right (θ := θ) hp hL hβ hκ hcs hθ1 hcm hslope hC1 hC2 hC3
    (abs_nonneg _) hu1 (abs_nonneg _) hv1 F
  have ex : reflectedOddPart F L (L / 2 + |x - L / 2|) ^ 2 = reflectedOddPart F L x ^ 2 := by
    rcases half_add_abs_eq L x with e | e <;> rw [e]
    rw [reflectedOddPart_reflect, neg_sq]
  have ey : reflectedOddPart F L (L / 2 + |y - L / 2|) ^ 2 = reflectedOddPart F L y ^ 2 := by
    rcases half_add_abs_eq L y with e | e <;> rw [e]
    rw [reflectedOddPart_reflect, neg_sq]
  have eq : quadrupleSum (thetaWithheldKernel c θ) F L (L / 2 + |x - L / 2|) (L / 2 + |y - L / 2|) =
      quadrupleSum (thetaWithheldKernel c θ) F L x y := by
    rcases half_add_abs_eq L x with e | e <;> rcases half_add_abs_eq L y with e' | e' <;>
      rw [e, e'] <;>
      simp only [quadrupleSum_reflect_left, quadrupleSum_reflect_right]
  rw [ex, ey, eq] at h
  exact h
end HarmonicQuadruple

/-! ### The folded strip inequality for a general weight -/

section FoldedStrip

variable {F : ℝ → ℝ} {K p r L : ℝ} (hF : Continuous F) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
  (hpr : p < r) (hL : p + r = L)

include hF hFL hpr hL in
/-- **The folded strip inequality.** Let a pair kernel `Kf` and a folded weight `Wt` satisfy the
quadruple inequality `α(x)² Wt(u, v) + α(y)² Wt(v, u) ≤ quadrupleSum Kf` on `[p, r]²`. If the weight
integrates to at least `2λ` at every folded point `u ∈ (0, (r − p)/2]`, then
`λ ∫_p^r α² ≤ ∫_p^r ∫_p^r Kf(x, y)(F x − F y)²`. -/
theorem foldedStrip_ge {lam C₁ C₂ : ℝ} (Kf Wt : ℝ → ℝ → ℝ)
    (hKm : Measurable (Function.uncurry fun x y => Kf x y * (F x - F y) ^ 2))
    (hKb : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r, |Kf x y * (F x - F y) ^ 2| ≤ C₁)
    (hWm : Measurable (Function.uncurry Wt))
    (hWb : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r,
      abs (reflectedOddPart F L x ^ 2 * Wt |x - L / 2| |y - L / 2|) ≤ C₂)
    (hquad : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r,
      reflectedOddPart F L x ^ 2 * Wt |x - L / 2| |y - L / 2| +
        reflectedOddPart F L y ^ 2 * Wt |y - L / 2| |x - L / 2| ≤ quadrupleSum Kf F L x y)
    (hpot : ∀ u, 0 < u → u ≤ (r - p) / 2 → 2 * lam ≤ ∫ y in p..r, Wt u |y - L / 2|) :
    lam * (∫ x in p..r, reflectedOddPart F L x ^ 2) ≤
      ∫ x in p..r, ∫ y in p..r, Kf x y * (F x - F y) ^ 2 := by
  set C := C₁ with hC
  have hmg : Measurable (Function.uncurry fun x y => Kf x y * (F x - F y) ^ 2) := hKm
  have hrefl : ∀ x, x ∈ Icc p r → L - x ∈ Icc p r := fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hbd : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r, |(fun x y => Kf x y * (F x - F y) ^ 2) x y| ≤ C := hKb
  obtain ⟨hi0, ho0⟩ := intervalIntegrable_iterated hpr.le hmg hbd
  have hm1 := measurable_uncurry_reflect_both hmg L
  have hm2 := measurable_uncurry_reflect_snd hmg L
  have hm3 := measurable_uncurry_reflect_fst hmg L
  obtain ⟨hi1, ho1⟩ := intervalIntegrable_iterated hpr.le hm1 fun x hx y hy =>
    hbd _ (hrefl x hx) _ (hrefl y hy)
  obtain ⟨hi2, ho2⟩ := intervalIntegrable_iterated hpr.le hm2 fun x hx y hy =>
    hbd _ hx _ (hrefl y hy)
  obtain ⟨hi3, ho3⟩ := intervalIntegrable_iterated hpr.le hm3 fun x hx y hy =>
    hbd _ (hrefl x hx) _ hy
  set T := ∫ x in p..r, ∫ y in p..r, (fun x y => Kf x y * (F x - F y) ^ 2) x y with hT
  -- the three reflected copies equal `T`
  have hT1 : (∫ x in p..r, ∫ y in p..r, (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) (L - y)) = T := by
    have e : (fun x => ∫ y in p..r, (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) (L - y)) = fun x => ∫ y in p..r, (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) y :=
      funext fun x => integral_strip_reflect hL ((fun x y => Kf x y * (F x - F y) ^ 2) (L - x))
    rw [e]
    exact integral_strip_reflect hL (fun x => ∫ y in p..r, (fun x y => Kf x y * (F x - F y) ^ 2) x y)
  have hT2 : (∫ x in p..r, ∫ y in p..r, (fun x y => Kf x y * (F x - F y) ^ 2) x (L - y)) = T := by
    have e : (fun x => ∫ y in p..r, (fun x y => Kf x y * (F x - F y) ^ 2) x (L - y)) = fun x => ∫ y in p..r, (fun x y => Kf x y * (F x - F y) ^ 2) x y :=
      funext fun x => integral_strip_reflect hL ((fun x y => Kf x y * (F x - F y) ^ 2) x)
    rw [e]
  have hT3 : (∫ x in p..r, ∫ y in p..r, (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) y) = T :=
    integral_strip_reflect hL (fun x => ∫ y in p..r, (fun x y => Kf x y * (F x - F y) ^ 2) x y)
  -- the sum of the four copies, as one iterated integral
  have hsum : (∫ x in p..r, ∫ y in p..r, ((fun x y => Kf x y * (F x - F y) ^ 2) x y + (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) (L - y) + (fun x y => Kf x y * (F x - F y) ^ 2) x (L - y) + (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) y)) =
      4 * T := by
    have hin : ∀ x ∈ uIcc p r, (∫ y in p..r, ((fun x y => Kf x y * (F x - F y) ^ 2) x y + (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) (L - y) + (fun x y => Kf x y * (F x - F y) ^ 2) x (L - y) + (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) y)) =
        (∫ y in p..r, (fun x y => Kf x y * (F x - F y) ^ 2) x y) + (∫ y in p..r, (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) (L - y)) + (∫ y in p..r, (fun x y => Kf x y * (F x - F y) ^ 2) x (L - y)) +
          ∫ y in p..r, (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) y := fun x hx => by
      rw [uIcc_of_le hpr.le] at hx
      rw [intervalIntegral.integral_add ((hi0 x hx).add (hi1 x hx) |>.add (hi2 x hx)) (hi3 x hx),
        intervalIntegral.integral_add ((hi0 x hx).add (hi1 x hx)) (hi2 x hx),
        intervalIntegral.integral_add (hi0 x hx) (hi1 x hx)]
    rw [intervalIntegral.integral_congr hin, intervalIntegral.integral_add ((ho0.add ho1).add ho2) ho3,
      intervalIntegral.integral_add (ho0.add ho1) ho2, intervalIntegral.integral_add ho0 ho1,
      hT1, hT2, hT3]
    ring
  -- integrability of the summed integrand
  have hms : Measurable (Function.uncurry fun x y => (fun x y => Kf x y * (F x - F y) ^ 2) x y +
      (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) (L - y) + (fun x y => Kf x y * (F x - F y) ^ 2) x (L - y) + (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) y) := by
    have := ((hmg.add hm1).add hm2).add hm3
    exact this
  obtain ⟨his, hos⟩ := intervalIntegrable_iterated (C := 4 * C) hpr.le hms fun x hx y hy => by
    have h0 := hbd x hx y hy
    have h1 := hbd _ (hrefl x hx) _ (hrefl y hy)
    have h2 := hbd _ hx _ (hrefl y hy)
    have h3 := hbd _ (hrefl x hx) _ hy
    calc |(fun x y => Kf x y * (F x - F y) ^ 2) x y + (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) (L - y) + (fun x y => Kf x y * (F x - F y) ^ 2) x (L - y) +
          (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) y|
        ≤ |(fun x y => Kf x y * (F x - F y) ^ 2) x y| + |(fun x y => Kf x y * (F x - F y) ^ 2) (L - x) (L - y)| + |(fun x y => Kf x y * (F x - F y) ^ 2) x (L - y)| +
          |(fun x y => Kf x y * (F x - F y) ^ 2) (L - x) y| := by
          have := abs_add_le ((fun x y => Kf x y * (F x - F y) ^ 2) x y + (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) (L - y) +
            (fun x y => Kf x y * (F x - F y) ^ 2) x (L - y)) ((fun x y => Kf x y * (F x - F y) ^ 2) (L - x) y)
          have := abs_add_le ((fun x y => Kf x y * (F x - F y) ^ 2) x y + (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) (L - y))
            ((fun x y => Kf x y * (F x - F y) ^ 2) x (L - y))
          have := abs_add_le ((fun x y => Kf x y * (F x - F y) ^ 2) x y) ((fun x y => Kf x y * (F x - F y) ^ 2) (L - x) (L - y))
          linarith
      _ ≤ 4 * C₁ := by linarith
  -- the folded weight
  set η := (r - p) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hαc : Continuous fun x => reflectedOddPart F L x ^ 2 := by
    unfold reflectedOddPart; fun_prop
  have hΦm : Measurable (Function.uncurry fun x y =>
      reflectedOddPart F L x ^ 2 * Wt |x - L / 2| |y - L / 2|) :=
    ((hαc.measurable.comp measurable_fst).mul
      (measurable_uncurry_abs_sub hWm (L / 2)))
  have hΦb : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r,
      abs (reflectedOddPart F L x ^ 2 * Wt |x - L / 2| |y - L / 2|) ≤ C₂ := hWb
  obtain ⟨hiΦ, hoΦ⟩ := intervalIntegrable_iterated hpr.le hΦm hΦb
  have hΦm' : Measurable (Function.uncurry fun x y =>
      reflectedOddPart F L y ^ 2 * Wt |y - L / 2| |x - L / 2|) :=
    hΦm.comp measurable_swap
  obtain ⟨hiΦ', hoΦ'⟩ := intervalIntegrable_iterated hpr.le hΦm' fun x hx y hy => hΦb y hy x hx
  -- the pointwise inequality, integrated
  have hinner1 : ∀ x ∈ Icc p r,
      (∫ y in p..r, reflectedOddPart F L x ^ 2 * Wt |x - L / 2| |y - L / 2|) +
        (∫ y in p..r, reflectedOddPart F L y ^ 2 * Wt |y - L / 2| |x - L / 2|) ≤
      ∫ y in p..r, ((fun x y => Kf x y * (F x - F y) ^ 2) x y + (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) (L - y) +
        (fun x y => Kf x y * (F x - F y) ^ 2) x (L - y) + (fun x y => Kf x y * (F x - F y) ^ 2) (L - x) y) := fun x hx => by
    rw [← intervalIntegral.integral_add (hiΦ x hx) (hiΦ' x hx)]
    refine intervalIntegral.integral_mono_on hpr.le ((hiΦ x hx).add (hiΦ' x hx)) (his x hx)
      fun y hy => ?_
    have h := hquad x hx y hy
    unfold quadrupleSum at h
    exact h
  have hint1 :
      (∫ x in p..r, ∫ y in p..r,
          reflectedOddPart F L x ^ 2 * Wt |x - L / 2| |y - L / 2|) +
        (∫ x in p..r, ∫ y in p..r,
          reflectedOddPart F L y ^ 2 * Wt |y - L / 2| |x - L / 2|) ≤
        4 * T := by
    rw [← intervalIntegral.integral_add hoΦ hoΦ', ← hsum]
    exact intervalIntegral.integral_mono_on hpr.le (hoΦ.add hoΦ') hos fun x hx => hinner1 x hx
  have hswap := integral_integral_swap_box hpr.le hΦm hΦb
  -- the inner integral is the potential of the folded odd part
  have hinner : ∀ x ∈ Icc p r, 2 * lam * reflectedOddPart F L x ^ 2 ≤
      ∫ y in p..r, reflectedOddPart F L x ^ 2 * Wt |x - L / 2| |y - L / 2| := by
    intro x hx
    have hu : |x - L / 2| ≤ η := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    rcases eq_or_lt_of_le (abs_nonneg (x - L / 2)) with h0 | h0
    · have hα := abs_reflectedOddPart_le (L := L) hFL x
      have : reflectedOddPart F L x = 0 := by
        rw [← h0, mul_zero] at hα; exact abs_nonpos_iff.mp hα
      rw [this]; simp
    rw [intervalIntegral.integral_const_mul, mul_comm (2 * lam)]
    exact mul_le_mul_of_nonneg_left (hpot _ h0 hu) (sq_nonneg _)
  have hmono := intervalIntegral.integral_mono_on hpr.le ((hαc.intervalIntegrable p r).const_mul
    (2 * lam)) hoΦ fun x hx => hinner x hx
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [hswap] at hint1
  linarith

end FoldedStrip

/-! ### The harmonic weight: decomposition, measurability, bounds -/

/-- The harmonic weight is the wide weight plus the recovered shares, minus the shared band. -/
theorem harmonicFoldWeight_eq (L β γ b ρ u v : ℝ) :
    harmonicFoldWeight L β γ b ρ u v = wideFoldWeight L β u v +
      2 * γ * ((u + v) * (1 - (β + v) / (β + u)) + |u - v| * (1 + (β + v) / (β + u))) -
      (if b ≤ u ∧ b ≤ v then 2 * (1 - ρ) * wideSameRate L u v * (1 - (β + v) / (β + u)) +
        2 * γ * (u + v) * (1 - (β + v) / (β + u)) else 0) := by
  unfold harmonicFoldWeight harmonicSameRate harmonicCrossRate harmonicRate wideFoldWeight wideCrossRate
  split_ifs
  · unfold wideSameRate; ring
  · unfold wideSameRate; ring

theorem measurable_harmonicFoldWeight (L β γ b ρ : ℝ) :
    Measurable (Function.uncurry (harmonicFoldWeight L β γ b ρ)) := by
  unfold harmonicFoldWeight harmonicSameRate harmonicCrossRate harmonicRate wideSameRate
  have h1 : Measurable fun z : ℝ × ℝ => archLevyDensity |z.1 - z.2| :=
    measurable_archLevyDensity.comp (measurable_fst.sub measurable_snd).abs
  have h2 : Measurable fun z : ℝ × ℝ => archLevyDensity (L - (z.1 + z.2)) :=
    measurable_archLevyDensity.comp (measurable_const.sub (measurable_fst.add measurable_snd))
  have h3 : Measurable fun z : ℝ × ℝ => archLevyDensity (z.1 + z.2) :=
    measurable_archLevyDensity.comp (measurable_fst.add measurable_snd)
  have h4 : Measurable fun z : ℝ × ℝ => archLevyDensity (L - |z.1 - z.2|) :=
    measurable_archLevyDensity.comp (measurable_const.sub (measurable_fst.sub measurable_snd).abs)
  have hs : Measurable fun z : ℝ × ℝ => if b ≤ z.1 ∧ b ≤ z.2 then ρ * (archLevyDensity |z.1 - z.2| -
      archLevyDensity (L - (z.1 + z.2))) else archLevyDensity |z.1 - z.2| - archLevyDensity (L - (z.1 + z.2)) +
      γ * (z.1 + z.2) :=
    Measurable.ite ((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)) ((h1.sub h2).const_mul ρ)
      ((h1.sub h2).add ((measurable_fst.add measurable_snd).const_mul γ))
  have hc : Measurable fun z : ℝ × ℝ => archLevyDensity (z.1 + z.2) - archLevyDensity (L - |z.1 - z.2|) +
      γ * |z.1 - z.2| := (h3.sub h4).add ((measurable_fst.sub measurable_snd).abs.const_mul γ)
  exact (((hs.sub hc).mul (measurable_const.sub ((measurable_const.add measurable_snd).div
    (measurable_const.add measurable_fst)))).const_mul 2).add (hc.const_mul 4)

/-- **The harmonic weight differs from the wide weight by a bounded amount.** For `0 < u ≤ η`,
`0 ≤ v ≤ η`, `2p ≤ L − 2η`, `η ≤ 1`, `γ ≥ 0`, `0 ≤ ρ ≤ 1`. -/
theorem abs_harmonicFoldWeight_le {L β γ b ρ p η u v : ℝ} (hβ : 0 < β) (hp : 0 < p) (hu0 : 0 < u)
    (hv0 : 0 ≤ v) (hu : u ≤ η) (hv : v ≤ η) (hη1 : η ≤ 1) (hLη : 2 * p ≤ L - 2 * η) (hγ : 0 ≤ γ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    |harmonicFoldWeight L β γ b ρ u v| ≤ |wideFoldWeight L β u v| +
      (2 * γ * (2 * η * (η / β) + η * (2 + η / β)) +
        2 * ((1 / 2 + η / 4 + archLevyDensity (2 * p) * η) / β) + 2 * γ * (2 * η * (η / β))) := by
  have hβu : 0 < β + u := by linarith
  have hη0 : 0 ≤ η := by linarith
  have hηβ : 0 ≤ η / β := div_nonneg hη0 hβ.le
  have hq1 : |1 - (β + v) / (β + u)| ≤ η / β := by
    have e : 1 - (β + v) / (β + u) = (u - v) / (β + u) := by field_simp; ring
    rw [e, abs_div, abs_of_pos hβu, div_le_div_iff₀ hβu hβ]
    have : |u - v| ≤ η := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith
  have hq2 : |1 + (β + v) / (β + u)| ≤ 2 + η / β := by
    have h0 : 0 ≤ (β + v) / (β + u) := div_nonneg (by linarith) hβu.le
    have h1 : (β + v) / (β + u) ≤ 1 + η / β := by
      rw [div_le_iff₀ hβu]
      have : 0 ≤ η / β * u := mul_nonneg hηβ hu0.le
      have e : (1 + η / β) * (β + u) = β + u + η + η / β * u := by field_simp; ring
      rw [e]; linarith
    rw [abs_of_nonneg (by linarith)]; linarith
  have hab : |u - v| ≤ η := abs_le.mpr ⟨by linarith, by linarith⟩
  have huv : u + v ≤ 2 * η := by linarith
  have hω2p := archLevyDensity_pos (show 0 < 2 * p by linarith)
  have hE0 : 0 ≤ 1 / 2 + η / 4 + archLevyDensity (2 * p) * η := by
    have := mul_nonneg hω2p.le hη0; linarith
  have hEβ : 0 ≤ (1 / 2 + η / 4 + archLevyDensity (2 * p) * η) / β := div_nonneg hE0 hβ.le
  have h2γ : 0 ≤ 2 * γ := by linarith
  have hb0 : 0 ≤ 2 * γ * (2 * η * (η / β)) := mul_nonneg h2γ (mul_nonneg (by linarith) hηβ)
  -- the recovered shares
  have hrec : |2 * γ * ((u + v) * (1 - (β + v) / (β + u)) + |u - v| * (1 + (β + v) / (β + u)))| ≤
      2 * γ * (2 * η * (η / β) + η * (2 + η / β)) := by
    rw [abs_mul, abs_of_nonneg h2γ]
    refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) h2γ
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ u + v), abs_abs]
    have k1 := mul_le_mul huv hq1 (abs_nonneg _) (by linarith)
    have k2 := mul_le_mul hab hq2 (abs_nonneg _) (by linarith)
    linarith
  -- the shared band
  have hR : |wideSameRate L u v * (1 - (β + v) / (β + u))| ≤
      (1 / 2 + η / 4 + archLevyDensity (2 * p) * η) / β := by
    have e : wideSameRate L u v * (1 - (β + v) / (β + u)) =
        (archLevyDensity |u - v| * (u - v) - archLevyDensity (L - (u + v)) * (u - v)) / (β + u) := by
      unfold wideSameRate; field_simp; ring
    rw [e, abs_div, abs_of_pos hβu, div_le_div_iff₀ hβu hβ]
    have k1 : |archLevyDensity |u - v| * (u - v)| ≤ 1 / 2 + η / 4 := by
      rcases eq_or_ne u v with h | h
      · rw [h, sub_self, mul_zero, abs_zero]; linarith
      have hd : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr h)
      have hm := mul_archLevyDensity_le hd (by linarith)
      rw [abs_mul, abs_of_pos (archLevyDensity_pos hd)]
      linarith
    have k2 : |archLevyDensity (L - (u + v)) * (u - v)| ≤ archLevyDensity (2 * p) * η := by
      have hpos : 0 < L - (u + v) := by linarith
      rw [abs_mul, abs_of_pos (archLevyDensity_pos hpos)]
      exact mul_le_mul (strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith))
        (mem_Ioi.mpr hpos) (by linarith)) hab (abs_nonneg _) hω2p.le
    have k3 := abs_sub (archLevyDensity |u - v| * (u - v)) (archLevyDensity (L - (u + v)) * (u - v))
    nlinarith [mul_le_mul_of_nonneg_left (show β ≤ β + u by linarith) hE0]
  have hband : |(if b ≤ u ∧ b ≤ v then 2 * (1 - ρ) * wideSameRate L u v * (1 - (β + v) / (β + u)) +
      2 * γ * (u + v) * (1 - (β + v) / (β + u)) else 0)| ≤
      2 * ((1 / 2 + η / 4 + archLevyDensity (2 * p) * η) / β) + 2 * γ * (2 * η * (η / β)) := by
    have h0 : 0 ≤ 2 * ((1 / 2 + η / 4 + archLevyDensity (2 * p) * η) / β) + 2 * γ * (2 * η * (η / β)) := by
      linarith
    split_ifs
    · refine (abs_add_le _ _).trans ?_
      have k1 : |2 * (1 - ρ) * wideSameRate L u v * (1 - (β + v) / (β + u))| ≤
          2 * ((1 / 2 + η / 4 + archLevyDensity (2 * p) * η) / β) := by
        rw [show 2 * (1 - ρ) * wideSameRate L u v * (1 - (β + v) / (β + u)) =
          (2 * (1 - ρ)) * (wideSameRate L u v * (1 - (β + v) / (β + u))) by ring, abs_mul,
          abs_of_nonneg (by linarith : 0 ≤ 2 * (1 - ρ))]
        nlinarith [mul_le_mul_of_nonneg_left hR (by linarith : 0 ≤ 2 * (1 - ρ))]
      have k2 : |2 * γ * (u + v) * (1 - (β + v) / (β + u))| ≤ 2 * γ * (2 * η * (η / β)) := by
        rw [show 2 * γ * (u + v) * (1 - (β + v) / (β + u)) =
          (2 * γ) * ((u + v) * (1 - (β + v) / (β + u))) by ring, abs_mul, abs_of_nonneg h2γ,
          abs_mul, abs_of_nonneg (by linarith : 0 ≤ u + v)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul huv hq1 (abs_nonneg _) (by linarith)) h2γ
      linarith
    · rw [abs_zero]; exact h0
  rw [harmonicFoldWeight_eq]
  have t := abs_sub (wideFoldWeight L β u v +
    2 * γ * ((u + v) * (1 - (β + v) / (β + u)) + |u - v| * (1 + (β + v) / (β + u))))
    (if b ≤ u ∧ b ≤ v then 2 * (1 - ρ) * wideSameRate L u v * (1 - (β + v) / (β + u)) +
      2 * γ * (u + v) * (1 - (β + v) / (β + u)) else 0)
  have t2 := abs_add_le (wideFoldWeight L β u v)
    (2 * γ * ((u + v) * (1 - (β + v) / (β + u)) + |u - v| * (1 + (β + v) / (β + u))))
  linarith

/-- The odd part squared against a weight bounded by `C' + 4ω(u + v)`. -/
theorem abs_sq_mul_weight_le {F : ℝ → ℝ} {K L η C' x y w : ℝ} (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
    (hu : |x - L / 2| ≤ η) (hC' : 0 ≤ C')
    (hw : 0 < |x - L / 2| → |w| ≤ C' + 4 * archLevyDensity (|x - L / 2| + |y - L / 2|)) :
    abs (reflectedOddPart F L x ^ 2 * w) ≤ K ^ 2 * η ^ 2 * C' + K ^ 2 * (2 * η + η ^ 2) := by
  have hα := abs_reflectedOddPart_le (L := L) hFL x
  have hK0 : 0 ≤ K := by
    have := hFL 1 0; norm_num at this; linarith [abs_nonneg (F 1 - F 0)]
  set u := |x - L / 2| with hudef
  set v := |y - L / 2| with hvdef
  have hu0 : 0 ≤ u := abs_nonneg _
  have hv0 : 0 ≤ v := abs_nonneg _
  have hη0 : 0 ≤ η := hu0.trans hu
  have hR0 : 0 ≤ K ^ 2 * η ^ 2 * C' + K ^ 2 * (2 * η + η ^ 2) := by positivity
  rcases eq_or_lt_of_le hu0 with h0 | h0
  · have : reflectedOddPart F L x = 0 := by
      have := hα; rw [← h0, mul_zero] at this; exact abs_nonpos_iff.mp this
    rw [this, zero_pow two_ne_zero, zero_mul, abs_zero]; exact hR0
  have hα2 : reflectedOddPart F L x ^ 2 ≤ K ^ 2 * u ^ 2 := by
    rw [← sq_abs]
    have := mul_le_mul hα hα (abs_nonneg _) (mul_nonneg hK0 hu0)
    nlinarith [abs_nonneg (reflectedOddPart F L x)]
  have hωu := archLevyDensity_le_inv (show 0 < u + v by linarith)
  have h1 : u ^ 2 * archLevyDensity (u + v) ≤ u / 2 + u ^ 2 / 4 := by
    have h2 := mul_le_mul_of_nonneg_left hωu (sq_nonneg u)
    have h3 : u ^ 2 * (1 / (2 * (u + v))) ≤ u / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hu2 : u ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hu0 hu 2
  have hm := mul_le_mul hα2 (hw h0) (abs_nonneg _) (mul_nonneg (sq_nonneg K) (sq_nonneg u))
  have h4 : K ^ 2 * (u ^ 2 * archLevyDensity (u + v)) ≤ K ^ 2 * (u / 2 + u ^ 2 / 4) :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg K)
  have h5 : K ^ 2 * (u / 2 + u ^ 2 / 4) ≤ K ^ 2 * ((2 * η + η ^ 2) / 4) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg K)
  have h6 : K ^ 2 * u ^ 2 * C' ≤ K ^ 2 * η ^ 2 * C' :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu2 (sq_nonneg K)) hC'
  have e : K ^ 2 * u ^ 2 * (C' + 4 * archLevyDensity (u + v)) =
      K ^ 2 * u ^ 2 * C' + 4 * (K ^ 2 * (u ^ 2 * archLevyDensity (u + v))) := by ring
  rw [e] at hm
  linarith

/-- **The harmonic folded weight is bounded on the strip.** -/
theorem abs_harmonicFoldedWeight_le {F : ℝ → ℝ} {K p r L β γ b ρ η x y : ℝ}
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hp : 0 < p) (hL : p + r = L) (hr1 : r - p ≤ 1)
    (hη : (r - p) / 2 = η) (hβ : 0 < β) (hγ : 0 ≤ γ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hx : x ∈ Icc p r)
    (hy : y ∈ Icc p r) :
    abs (reflectedOddPart F L x ^ 2 * harmonicFoldWeight L β γ b ρ |x - L / 2| |y - L / 2|) ≤
      K ^ 2 * η ^ 2 * (3 / β + 2 * archLevyDensity (2 * p) * η / β + 4 * archLevyDensity (2 * p) +
        (2 * γ * (2 * η * (η / β) + η * (2 + η / β)) +
          2 * ((1 / 2 + η / 4 + archLevyDensity (2 * p) * η) / β) + 2 * γ * (2 * η * (η / β)))) +
        K ^ 2 * (2 * η + η ^ 2) := by
  have hω2p := archLevyDensity_pos (show 0 < 2 * p by linarith)
  have hu : |x - L / 2| ≤ η := by rw [← hη, abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hv : |y - L / 2| ≤ η := by rw [← hη, abs_le]; constructor <;> linarith [hy.1, hy.2]
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hu
  have hηβ : 0 ≤ η / β := div_nonneg hη0 hβ.le
  have hE1 : 0 ≤ (1 / 2 + η / 4 + archLevyDensity (2 * p) * η) / β :=
    div_nonneg (by have := mul_nonneg hω2p.le hη0; linarith) hβ.le
  have hC' : 0 ≤ 3 / β + 2 * archLevyDensity (2 * p) * η / β + 4 * archLevyDensity (2 * p) +
      (2 * γ * (2 * η * (η / β) + η * (2 + η / β)) +
        2 * ((1 / 2 + η / 4 + archLevyDensity (2 * p) * η) / β) + 2 * γ * (2 * η * (η / β))) := by
    have h1 : 0 ≤ 3 / β := by positivity
    have h2 : 0 ≤ 2 * archLevyDensity (2 * p) * η / β := by positivity
    have h3 : 0 ≤ 2 * γ * (2 * η * (η / β) + η * (2 + η / β)) := by positivity
    have h4 : 0 ≤ 2 * γ * (2 * η * (η / β)) := by positivity
    linarith
  refine abs_sq_mul_weight_le (y := y) hFL hu hC' fun h0 => ?_
  have hW := abs_wideFoldWeight_le (L := L) (p := p) hβ hp h0 (abs_nonneg _) hu hv (by linarith)
    (by linarith)
  have hWE := abs_harmonicFoldWeight_le (L := L) (γ := γ) (b := b) (ρ := ρ) (p := p) hβ hp h0
    (abs_nonneg _) hu hv (by linarith) (by linarith) hγ hρ0 hρ1
  linarith

/-! ### The harmonic micro-fold of the strip -/

section HarmonicStrip

variable {F : ℝ → ℝ} {K p r L β cs κ c θ : ℝ} (hF : Continuous F)
  (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hp : 0 < p) (hpr : p < r) (hL : p + r = L)
  (hr1 : r - p ≤ 1) (hβ : 0 < β) (hκ : 0 ≤ κ) (hcs : 0 ≤ cs) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
  (hcm : L / 2 < c)
  (hslope : ∀ w, 0 ≤ w → w ≤ r - p → cs * w ≤ archLevyDensity (L - w) - archLevyDensity (L + w))
  (hC1 : ∀ u v, 0 ≤ u → u ≤ (r - p) / 2 → 0 ≤ v → v ≤ (r - p) / 2 → u ≠ v →
    cs * (u + v) ≤ κ * wideSameRate L u v)
  (hC2 : ∀ u v, 0 ≤ u → u ≤ (r - p) / 2 → 0 ≤ v → v ≤ (r - p) / 2 → 0 < u + v →
    cs * |u - v| ≤ κ * wideCrossRate L u v)
  (hC3 : ∀ u v, c - L / 2 ≤ u → u ≤ (r - p) / 2 → c - L / 2 ≤ v → v ≤ (r - p) / 2 → u ≠ v →
    wideCrossRate L u v + cs / (2 + κ) * |u - v| ≤ 2 * (1 - θ) / (2 - θ) * wideSameRate L u v)

include hF hFL hp hpr hL hr1 hβ hκ hcs hθ0 hθ1 hcm hslope hC1 hC2 hC3 in
/-- **The harmonic micro-fold of the strip with a shared band.** If the harmonic weight integrates to
at least `2λ` at every folded point, the surplus of `[p, r]²` with the fraction `θ` of the pairs of
`[c, r]²` withheld is at least `λ ∫_p^r α²`. -/
theorem harmonicMicroFold_strip_ge {lam : ℝ}
    (hpot : ∀ u, 0 < u → u ≤ (r - p) / 2 → 2 * lam ≤ ∫ y in p..r,
      harmonicFoldWeight L β (cs / (2 + κ)) (c - L / 2) (2 * (1 - θ) / (2 - θ)) u |y - L / 2|) :
    lam * (∫ x in p..r, reflectedOddPart F L x ^ 2) ≤
      ∫ x in p..r, ∫ y in p..r, thetaWithheldKernel c θ x y * (F x - F y) ^ 2 := by
  have hρ0 : 0 ≤ 2 * (1 - θ) / (2 - θ) := div_nonneg (by linarith) (by linarith)
  have hρ1 : 2 * (1 - θ) / (2 - θ) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hγ : 0 ≤ cs / (2 + κ) := div_nonneg hcs (by linarith)
  refine foldedStrip_ge hF hFL hpr hL (C₁ := 3 / 2 * K ^ 2 * (r - p)) (thetaWithheldKernel c θ)
    (harmonicFoldWeight L β (cs / (2 + κ)) (c - L / 2) (2 * (1 - θ) / (2 - θ))) ?_ ?_
    (measurable_harmonicFoldWeight _ _ _ _ _)
    (fun x hx y hy => abs_harmonicFoldedWeight_le hFL hp hL hr1 rfl hβ hγ hρ0 hρ1 hx hy)
    (fun x hx y hy => harmonicQuadruple_ge hp hL hβ hκ hcs hθ1 hcm hslope hC1 hC2 hC3 hx hy F) hpot
  · unfold thetaWithheldKernel
    refine Measurable.mul (Measurable.ite ((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)) (measurable_surplusKernel.const_mul _)
      measurable_surplusKernel) ?_
    exact ((hF.measurable.comp measurable_fst).sub (hF.measurable.comp measurable_snd)).pow_const 2
  · intro x hx y hy
    have h := abs_strip_integrand_le hFL hp hr1 hx hy
    unfold thetaWithheldKernel
    split_ifs
    · rw [mul_assoc, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - θ)]
      nlinarith [abs_nonneg (surplusKernel x y * (F x - F y) ^ 2)]
    · exact h

end HarmonicStrip

/-- **Sharing a fraction of an inner square.** For `0 < p < c ≤ r`, withholding the fraction `θ` of the
pairs of `[c, r]²` removes `θ` times the surplus of `[c, r]²` from the surplus of `[p, r]²`. -/
theorem integral_box_thetaWithheld_eq {F : ℝ → ℝ} {K p c r θ : ℝ} (hF : Continuous F)
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hp : 0 < p) (hpc : p < c) (hcr : c ≤ r)
    (hr1 : r - p ≤ 1) :
    (∫ x in p..r, ∫ y in p..r, thetaWithheldKernel c θ x y * (F x - F y) ^ 2) =
      (∫ x in p..r, ∫ y in p..r, surplusKernel x y * (F x - F y) ^ 2) -
        θ * ∫ x in c..r, ∫ y in c..r, surplusKernel x y * (F x - F y) ^ 2 := by
  have hpr : p ≤ r := hpc.le.trans hcr
  have hsplit := integral_box_eq_withheld_add hF hFL hp hpc hcr hr1
  have hmg : Measurable (Function.uncurry fun x y => surplusKernel x y * (F x - F y) ^ 2) :=
    measurable_stripIntegrand hF
  have hmw : Measurable (Function.uncurry fun x y => withheldKernel c x y * (F x - F y) ^ 2) := by
    unfold withheldKernel
    refine Measurable.mul (Measurable.ite ((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)) measurable_const measurable_surplusKernel) ?_
    exact ((hF.measurable.comp measurable_fst).sub (hF.measurable.comp measurable_snd)).pow_const 2
  have hbg : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r,
      |(fun x y => surplusKernel x y * (F x - F y) ^ 2) x y| ≤ 3 / 2 * K ^ 2 * (r - p) :=
    fun x hx y hy => abs_strip_integrand_le hFL hp hr1 hx hy
  have hbw : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r,
      |(fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y| ≤ 3 / 2 * K ^ 2 * (r - p) :=
    fun x hx y hy => by
      have h := abs_strip_integrand_le hFL hp hr1 hx hy
      simp only
      unfold withheldKernel
      split_ifs
      · rw [zero_mul, abs_zero]; exact (abs_nonneg _).trans h
      · exact h
  obtain ⟨hig, hog⟩ := intervalIntegrable_iterated hpr hmg hbg
  obtain ⟨hiw, how⟩ := intervalIntegrable_iterated hpr hmw hbw
  -- the `θ`-withheld kernel is `θ` times the withheld kernel plus `1 − θ` times the full kernel
  have key : ∀ x ∈ uIcc p r, (∫ y in p..r, thetaWithheldKernel c θ x y * (F x - F y) ^ 2) =
      θ * (∫ y in p..r, withheldKernel c x y * (F x - F y) ^ 2) +
        (1 - θ) * ∫ y in p..r, surplusKernel x y * (F x - F y) ^ 2 := by
    intro x hx
    rw [uIcc_of_le hpr] at hx
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hiw x hx).const_mul θ) ((hig x hx).const_mul (1 - θ))]
    refine intervalIntegral.integral_congr fun y _ => ?_
    unfold thetaWithheldKernel withheldKernel
    split_ifs <;> ring
  rw [intervalIntegral.integral_congr key, intervalIntegral.integral_add (how.const_mul θ)
    (hog.const_mul (1 - θ)), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  linear_combination -θ * hsplit

/-! ### The integrated recovery and the integrated band -/

/-- The recovered shares integrate in closed form: for `0 < u ≤ η`,
`(β + u) ∫_0^η ((u + v)(1 − q) + |u − v|(1 + q)) dv = u²η − η³/3 + (2β + u)u²/2 + u³/6 +
(β + u)(η − u)² + (η − u)³/3`, `q = (β + v)/(β + u)`. -/
theorem integral_recovery_eq {β η u : ℝ} (hβ : 0 < β) (hu : 0 < u) (huη : u ≤ η) :
    (∫ v in (0 : ℝ)..η, ((u + v) * (1 - (β + v) / (β + u)) + |u - v| * (1 + (β + v) / (β + u)))) =
      (u ^ 2 * η - η ^ 3 / 3 + (2 * β + u) * u ^ 2 / 2 + u ^ 3 / 6 + (β + u) * (η - u) ^ 2 +
        (η - u) ^ 3 / 3) / (β + u) := by
  have hβu : 0 < β + u := by linarith
  have hc : Continuous fun v : ℝ => (u + v) * (1 - (β + v) / (β + u)) + |u - v| * (1 + (β + v) / (β + u)) := by
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := u) (hc.intervalIntegrable 0 u)
    (hc.intervalIntegrable u η)]
  have e1 : (∫ v in (0 : ℝ)..u, ((u + v) * (1 - (β + v) / (β + u)) + |u - v| * (1 + (β + v) / (β + u)))) =
      ∫ v in (0 : ℝ)..u, ((u + v) * (u - v) + (u - v) * (2 * β + u + v)) / (β + u) :=
    intervalIntegral.integral_congr fun v hv => by
      rw [uIcc_of_le hu.le] at hv
      rw [abs_of_nonneg (by linarith [hv.2])]
      field_simp; ring
  have e2 : (∫ v in u..η, ((u + v) * (1 - (β + v) / (β + u)) + |u - v| * (1 + (β + v) / (β + u)))) =
      ∫ v in u..η, ((u + v) * (u - v) + (v - u) * (2 * β + u + v)) / (β + u) :=
    intervalIntegral.integral_congr fun v hv => by
      rw [uIcc_of_le huη] at hv
      rw [abs_of_nonpos (by linarith [hv.1])]
      field_simp; ring
  rw [e1, e2, intervalIntegral.integral_div, intervalIntegral.integral_div,
    integral_deriv_eq_sub' (fun v => u ^ 2 * v - v ^ 3 / 3 + (2 * β + u) * u * v - (2 * β + u) * v ^ 2 / 2 +
      u * v ^ 2 / 2 - v ^ 3 / 3 + u * v ^ 2 / 2 - u * v ^ 2 / 2 + 0)
      (by funext v; simp (disch := fun_prop); ring) (fun v _ => by fun_prop) (by fun_prop),
    integral_deriv_eq_sub' (fun v => u ^ 2 * v - v ^ 3 / 3 + v ^ 3 / 3 + (2 * β + u) * v ^ 2 / 2 -
      u * (2 * β + u) * v - u * v ^ 2 / 2 + 0)
      (by funext v; simp (disch := fun_prop); ring) (fun v _ => by fun_prop) (by fun_prop)]
  field_simp
  ring

section Band

variable {L β γ ρ η b u ωlo ωhi : ℝ} (hβ : 0 < β) (hb : 0 < b) (hbu : b ≤ u) (huη : u ≤ η)
  (hLη : 2 * η < L) (hη1 : η ≤ 1 / 2) (hρ1 : ρ ≤ 1)
  (hlo : ωlo ≤ archLevyDensity (L - 2 * b)) (hhi : archLevyDensity (L - 2 * η) ≤ ωhi)

include hb hbu huη hLη hη1 hlo hhi in
/-- **The same-distance rate on the band, integrated against the gauge difference.** For `b ≤ u ≤ η`:
`∫_b^η R₋(u, v)(u − v) dv ≤ (u − b)/2 + (u − b)²/8 − ωlo(u − b)²/2 − (η − u)/2 − (η − u)²/8 +
(η − u)³/144 + (η − u)⁴/128 + ωhi(η − u)²/2`. -/
theorem integral_wideSameRate_band_le :
    (∫ v in b..η, wideSameRate L u v * (u - v)) ≤
      (u - b) / 2 + (u - b) ^ 2 / 8 - ωlo * (u - b) ^ 2 / 2 - (η - u) / 2 - (η - u) ^ 2 / 8 +
        (η - u) ^ 3 / 144 + (η - u) ^ 4 / 128 + ωhi * (η - u) ^ 2 / 2 := by
  have hpos : ∀ v ∈ Icc b η, 0 < L - (u + v) := fun v hv => by linarith [hv.2]
  have hm : Measurable fun v => wideSameRate L u v * (u - v) := by
    unfold wideSameRate
    exact ((measurable_archLevyDensity.comp (measurable_const.sub measurable_id).abs).sub
      (measurable_archLevyDensity.comp (measurable_const.sub (measurable_const.add measurable_id)))).mul
        (measurable_const.sub measurable_id)
  -- the integrand is bounded on the band
  have hbd : ∀ v ∈ Icc b η, |wideSameRate L u v * (u - v)| ≤ 1 + archLevyDensity (L - 2 * η) := by
    intro v hv
    unfold wideSameRate
    rw [sub_mul]
    have hk1 : |archLevyDensity |u - v| * (u - v)| ≤ 1 / 2 + 1 / 4 := by
      rcases eq_or_ne u v with h | h
      · rw [h, sub_self, mul_zero, abs_zero]; norm_num
      have hd : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr h)
      have hd1 : |u - v| ≤ 1 := abs_le.mpr ⟨by linarith [hv.1, hv.2], by linarith [hv.1, hv.2]⟩
      rw [abs_mul, abs_of_pos (archLevyDensity_pos hd)]
      have := mul_archLevyDensity_le hd hd1
      nlinarith
    have hk2 : |archLevyDensity (L - (u + v)) * (u - v)| ≤ archLevyDensity (L - 2 * η) := by
      rw [abs_mul, abs_of_pos (archLevyDensity_pos (hpos v hv))]
      have h1 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith : 0 < L - 2 * η))
        (mem_Ioi.mpr (hpos v hv)) (by linarith [hv.2])
      have h2 : |u - v| ≤ 1 := abs_le.mpr ⟨by linarith [hv.1, hv.2], by linarith [hv.1, hv.2]⟩
      have h3 := archLevyDensity_pos (hpos v hv)
      nlinarith [abs_nonneg (u - v)]
    have := abs_sub (archLevyDensity |u - v| * (u - v)) (archLevyDensity (L - (u + v)) * (u - v))
    linarith
  have hint : ∀ a c, b ≤ a → a ≤ c → c ≤ η →
      IntervalIntegrable (fun v => wideSameRate L u v * (u - v)) volume a c := fun a c ha hac hc =>
    intervalIntegrable_of_abs_le hac hm fun v hv => hbd v ⟨by linarith [hv.1], by linarith [hv.2]⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := u) (hint b u le_rfl hbu huη)
    (hint u η hbu huη le_rfl)]
  -- `v ≤ u`: `τ ω(τ) ≤ ½ + τ/4` and `ω(L − u − v) ≥ ωlo`
  have h1 : (∫ v in b..u, wideSameRate L u v * (u - v)) ≤
      ∫ v in b..u, (1 / 2 + (u - v) / 4 - ωlo * (u - v)) := by
    refine intervalIntegral.integral_mono_on hbu (hint b u le_rfl hbu huη)
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun v hv => ?_
    unfold wideSameRate
    have hlv : ωlo ≤ archLevyDensity (L - (u + v)) :=
      hlo.trans (strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (hpos v ⟨hv.1, hv.2.trans huη⟩))
        (mem_Ioi.mpr (by linarith : 0 < L - 2 * b)) (by linarith [hv.1]))
    have hw0 : 0 ≤ u - v := by linarith [hv.2]
    have hk : archLevyDensity |u - v| * (u - v) ≤ 1 / 2 + (u - v) / 4 := by
      rcases eq_or_lt_of_le hw0 with h | h
      · rw [← h, mul_zero]; norm_num
      rw [abs_of_pos h, mul_comm]
      exact mul_archLevyDensity_le h (by linarith [hv.1])
    nlinarith [mul_le_mul_of_nonneg_right hlv hw0]
  -- `v ≥ u`: `τ ω(τ) ≥ ½ + τ/4 − τ²/48 − τ³/32` and `ω(L − u − v) ≤ ωhi`, off the endpoint `v = u`
  have h2 : (∫ v in u..η, wideSameRate L u v * (u - v)) ≤
      ∫ v in u..η, (-(1 / 2 + (v - u) / 4 - (v - u) ^ 2 / 48 - (v - u) ^ 3 / 32) + ωhi * (v - u)) := by
    refine intervalIntegral.integral_mono_ae_restrict huη (hint u η hbu huη le_rfl)
      (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun v hv => ?_)
    unfold wideSameRate
    have hhv : archLevyDensity (L - (u + v)) ≤ ωhi :=
      (strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith : 0 < L - 2 * η))
        (mem_Ioi.mpr (hpos v ⟨by linarith [hv.1], hv.2⟩)) (by linarith [hv.2])).trans hhi
    have hw : 0 < v - u := by linarith [hv.1]
    have hk : 1 / 2 + (v - u) / 4 - (v - u) ^ 2 / 48 - (v - u) ^ 3 / 32 ≤
        archLevyDensity |u - v| * (v - u) := by
      rw [abs_sub_comm, abs_of_pos hw, mul_comm]
      exact mul_archLevyDensity_ge_sharp_of_le_two hw (by linarith [hv.2])
    nlinarith [mul_le_mul_of_nonneg_right hhv hw.le]
  have e1 : (∫ v in b..u, (1 / 2 + (u - v) / 4 - ωlo * (u - v))) =
      (u - b) / 2 + (u - b) ^ 2 / 8 - ωlo * (u - b) ^ 2 / 2 := by
    rw [integral_deriv_eq_sub' (fun v => v / 2 - (u - v) ^ 2 / 8 + ωlo * (u - v) ^ 2 / 2)
      (by funext v; simp (disch := fun_prop); ring) (fun v _ => by fun_prop) (by fun_prop)]
    ring
  have e2 : (∫ v in u..η, (-(1 / 2 + (v - u) / 4 - (v - u) ^ 2 / 48 - (v - u) ^ 3 / 32) + ωhi * (v - u))) =
      -((η - u) / 2) - (η - u) ^ 2 / 8 + (η - u) ^ 3 / 144 + (η - u) ^ 4 / 128 + ωhi * (η - u) ^ 2 / 2 := by
    rw [integral_deriv_eq_sub' (fun v => -(v / 2) - (v - u) ^ 2 / 8 + (v - u) ^ 3 / 144 +
        (v - u) ^ 4 / 128 + ωhi * (v - u) ^ 2 / 2)
      (by funext v; simp (disch := fun_prop); ring) (fun v _ => by fun_prop) (by fun_prop)]
    ring
  rw [e1] at h1
  rw [e2] at h2
  linarith

include hb hbu huη hLη hη1 hlo hhi in
/-- **The band bound in a simple form.** With `ωlo ≥ 1/4` and `cw ≥ ωhi/2 − 1/8 + (η − b)/144 +
(η − b)²/128`: `∫_b^η R₋(u, v)(u − v) dv ≤ u − (b + η)/2 + cw (η − u)²`. -/
theorem integral_wideSameRate_band_le_simple {cw : ℝ} (hlo4 : 1 / 4 ≤ ωlo)
    (hcw : ωhi / 2 - 1 / 8 + (η - b) / 144 + (η - b) ^ 2 / 128 ≤ cw) :
    (∫ v in b..η, wideSameRate L u v * (u - v)) ≤ u - (b + η) / 2 + cw * (η - u) ^ 2 := by
  have h := integral_wideSameRate_band_le (ωlo := ωlo) (ωhi := ωhi) hb hbu huη hLη hη1 hlo hhi
  have hw0 : 0 ≤ η - u := by linarith
  have hwb : η - u ≤ η - b := by linarith
  have hz : 0 ≤ (u - b) ^ 2 * (ωlo / 2 - 1 / 8) := mul_nonneg (sq_nonneg _) (by linarith)
  have h3 : (η - u) ^ 3 / 144 ≤ (η - u) ^ 2 * ((η - b) / 144) := by
    have := mul_le_mul_of_nonneg_left hwb (sq_nonneg (η - u)); nlinarith
  have h4 : (η - u) ^ 4 / 128 ≤ (η - u) ^ 2 * ((η - b) ^ 2 / 128) := by
    have := pow_le_pow_left₀ hw0 hwb 2
    have := mul_le_mul_of_nonneg_left this (sq_nonneg (η - u)); nlinarith
  have h5 := mul_le_mul_of_nonneg_left hcw (sq_nonneg (η - u))
  nlinarith

end Band

/-! ### The integrated harmonic weight -/

/-- **The crossing part of the wide fold, with the polynomial remainders kept.** -/
theorem wideCrossRate_integral_ge_sharp {L η u Λ : ℝ} (hu : 0 < u) (huη : u ≤ η) (hLη : 2 * η < L)
    (hL : L ≤ 3 / 4) (hΛ : Real.log L - Real.log (L - η) ≤ Λ) :
    2 * (Real.log (u + η) - Real.log u) - 2 * Λ - (3 * η ^ 2 + 7 * η ^ 3) / 24 - 8 * L ^ 4 / 1000 +
        ((L ^ 2 - (L - u) ^ 2) + (L ^ 3 - (L - u) ^ 3)) / 24 +
        ((L ^ 2 - (L + u - η) ^ 2) + (L ^ 3 - (L + u - η) ^ 3)) / 24 ≤
      4 * ∫ v in (0 : ℝ)..η, wideCrossRate L u v := by
  have hR := integral_wideCrossRate (L := L) hu huη (by linarith)
  have hI1 := integral_archLevyDensity_ge_secondOrder hu (by linarith : u ≤ u + η) (by linarith)
  have hI2 := integral_archLevyDensity_le_secondOrder (by linarith : 0 < L - u) (by linarith : L - u ≤ L) hL
  have hI3 := integral_archLevyDensity_le_secondOrder (by linarith : 0 < L + u - η)
    (by linarith : L + u - η ≤ L) hL
  have hprod : Real.log L + Real.log (L - η) ≤ Real.log (L - u) + Real.log (L + u - η) := by
    rw [← Real.log_mul (by linarith) (by linarith), ← Real.log_mul (by linarith) (by linarith)]
    have hd : L * (L - η) ≤ (L - u) * (L + u - η) := by
      have : 0 ≤ u * (η - u) := mul_nonneg hu.le (by linarith)
      linarith only [this]
    exact Real.log_le_log (by nlinarith) hd
  obtain ⟨hP1, -, -, hQ4⟩ := wideCrossRate_poly_aux hu huη (by linarith : η < L)
  rw [hR]
  linarith only [hI1, hI2, hI3, hprod, hΛ, hP1, hQ4]

theorem intervalIntegrable_wideFoldWeight_row {L β η u : ℝ} (hβ : 0 < β) (hu : 0 < u) (huη : u ≤ η)
    (hLη : 2 * η < L) (hη1 : η ≤ 1 / 2) :
    IntervalIntegrable (fun v => wideFoldWeight L β u v) volume 0 η :=
  intervalIntegrable_of_abs_le (by linarith) (measurable_wideFoldWeight L β).of_uncurry_left
    fun v hv => abs_wideFoldWeight_le_of_mem hβ hu huη hv hLη hη1

theorem abs_wideSameRate_mul_le {L η u v : ℝ} (hu : 0 ≤ u) (hu' : u ≤ η) (hv : 0 ≤ v) (hv' : v ≤ η)
    (hLη : 2 * η < L) (hη1 : η ≤ 1 / 2) :
    |wideSameRate L u v * (u - v)| ≤ 1 + archLevyDensity (L - 2 * η) := by
  unfold wideSameRate
  rw [sub_mul]
  have hpos : 0 < L - (u + v) := by linarith
  have hd1 : |u - v| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hk1 : |archLevyDensity |u - v| * (u - v)| ≤ 1 / 2 + 1 / 4 := by
    rcases eq_or_ne u v with h | h
    · rw [h, sub_self, mul_zero, abs_zero]; norm_num
    have hd : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr h)
    rw [abs_mul, abs_of_pos (archLevyDensity_pos hd)]
    have := mul_archLevyDensity_le hd hd1
    nlinarith
  have hk2 : |archLevyDensity (L - (u + v)) * (u - v)| ≤ archLevyDensity (L - 2 * η) := by
    rw [abs_mul, abs_of_pos (archLevyDensity_pos hpos)]
    have h1 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith : 0 < L - 2 * η))
      (mem_Ioi.mpr hpos) (by linarith)
    have h3 := archLevyDensity_pos hpos
    nlinarith [abs_nonneg (u - v)]
  have := abs_sub (archLevyDensity |u - v| * (u - v)) (archLevyDensity (L - (u + v)) * (u - v))
  linarith

/-- **The integrated harmonic weight.** For `0 < u ≤ η`, the harmonic weight integrates over `[0, η]`
to at least the wide weight plus the recovered shares, minus (on the band `u ≥ b`) the shared part. -/
theorem integral_harmonicFoldWeight_ge {L β γ ρ η b u ωlo ωhi cw : ℝ} (hβ : 0 < β) (hu : 0 < u)
    (huη : u ≤ η) (hLη : 2 * η < L) (hη1 : η ≤ 1 / 2) (hγ : 0 ≤ γ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hb : 0 < b) (hbη : b ≤ η)
    (hlo : ωlo ≤ archLevyDensity (L - 2 * b)) (hhi : archLevyDensity (L - 2 * η) ≤ ωhi)
    (hlo4 : 1 / 4 ≤ ωlo) (hcw : ωhi / 2 - 1 / 8 + (η - b) / 144 + (η - b) ^ 2 / 128 ≤ cw) :
    (∫ v in (0 : ℝ)..η, wideFoldWeight L β u v) +
        2 * γ * ((u ^ 2 * η - η ^ 3 / 3 + (2 * β + u) * u ^ 2 / 2 + u ^ 3 / 6 + (β + u) * (η - u) ^ 2 +
          (η - u) ^ 3 / 3) / (β + u)) -
        (if b ≤ u then (2 * (1 - ρ) * (u - (b + η) / 2 + cw * (η - u) ^ 2) +
          2 * γ * ((u - b) * (u ^ 2 - b ^ 2))) / (β + u) else 0) ≤
      ∫ v in (0 : ℝ)..η, harmonicFoldWeight L β γ b ρ u v := by
  have hη : 0 ≤ η := by linarith
  have hβu : 0 < β + u := by linarith
  set Rv : ℝ → ℝ := fun v => (u + v) * (1 - (β + v) / (β + u)) + |u - v| * (1 + (β + v) / (β + u))
    with hRv
  set Bv : ℝ → ℝ := fun v => if b ≤ u ∧ b ≤ v then 2 * (1 - ρ) * wideSameRate L u v *
    (1 - (β + v) / (β + u)) + 2 * γ * (u + v) * (1 - (β + v) / (β + u)) else 0 with hBv
  have hW := intervalIntegrable_wideFoldWeight_row hβ hu huη hLη hη1
  have hR : IntervalIntegrable Rv volume 0 η := Continuous.intervalIntegrable (by rw [hRv]; fun_prop) _ _
  have hH : IntervalIntegrable (fun v => harmonicFoldWeight L β γ b ρ u v) volume 0 η := by
    refine intervalIntegrable_of_abs_le hη (measurable_harmonicFoldWeight L β γ b ρ).of_uncurry_left
      (C := 3 / β + 2 * archLevyDensity (2 * ((L - 2 * η) / 2)) * η / β +
        4 * (archLevyDensity u + archLevyDensity (2 * ((L - 2 * η) / 2))) +
        (2 * γ * (2 * η * (η / β) + η * (2 + η / β)) +
          2 * ((1 / 2 + η / 4 + archLevyDensity (2 * ((L - 2 * η) / 2)) * η) / β) +
            2 * γ * (2 * η * (η / β)))) fun v hv => ?_
    have h1 := abs_harmonicFoldWeight_le (L := L) (γ := γ) (b := b) (ρ := ρ) (p := (L - 2 * η) / 2) hβ
      (by linarith) hu hv.1 huη hv.2 (by linarith) (by linarith) hγ hρ0 hρ1
    have h2 := abs_wideFoldWeight_le (L := L) (p := (L - 2 * η) / 2) hβ (by linarith) hu hv.1 huη hv.2
      hη1 (by linarith)
    have h3 : archLevyDensity (u + v) ≤ archLevyDensity u :=
      strictAntiOn_archLevyDensity.antitoneOn hu (show 0 < u + v by linarith [hv.1]) (by linarith [hv.1])
    linarith
  have hBe : ∀ v, Bv v = wideFoldWeight L β u v + 2 * γ * Rv v - harmonicFoldWeight L β γ b ρ u v :=
    fun v => by rw [hBv, hRv, harmonicFoldWeight_eq]; ring
  have hB : IntervalIntegrable Bv volume 0 η := by
    have := (hW.add (hR.const_mul (2 * γ))).sub hH
    exact this.congr fun v _ => (hBe v).symm
  -- the decomposition
  have hdec : (∫ v in (0 : ℝ)..η, harmonicFoldWeight L β γ b ρ u v) =
      (∫ v in (0 : ℝ)..η, wideFoldWeight L β u v) + 2 * γ * (∫ v in (0 : ℝ)..η, Rv v) -
        ∫ v in (0 : ℝ)..η, Bv v := by
    have e : (fun v => harmonicFoldWeight L β γ b ρ u v) =
        fun v => wideFoldWeight L β u v + 2 * γ * Rv v - Bv v := funext fun v => by rw [hBe]; ring
    rw [e, intervalIntegral.integral_sub (hW.add (hR.const_mul _)) hB,
      intervalIntegral.integral_add hW (hR.const_mul _), intervalIntegral.integral_const_mul]
  have hrec : (∫ v in (0 : ℝ)..η, Rv v) = (u ^ 2 * η - η ^ 3 / 3 + (2 * β + u) * u ^ 2 / 2 + u ^ 3 / 6 +
      (β + u) * (η - u) ^ 2 + (η - u) ^ 3 / 3) / (β + u) := integral_recovery_eq hβ hu huη
  -- the band
  have hband : (∫ v in (0 : ℝ)..η, Bv v) ≤ (if b ≤ u then (2 * (1 - ρ) * (u - (b + η) / 2 + cw * (η - u) ^ 2) +
      2 * γ * ((u - b) * (u ^ 2 - b ^ 2))) / (β + u) else 0) := by
    by_cases hbu : b ≤ u
    · rw [if_pos hbu]
      have hBi : ∀ a c, 0 ≤ a → a ≤ c → c ≤ η → IntervalIntegrable Bv volume a c := fun a c ha hac hc =>
        hB.mono_set (by rw [uIcc_of_le hac, uIcc_of_le hη]; exact Icc_subset_Icc ha hc)
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := b) (hBi 0 b le_rfl hb.le hbη)
        (hBi b η hb.le hbη le_rfl)]
      have h0 : (∫ v in (0 : ℝ)..b, Bv v) = 0 := by
        rw [intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
        rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ)) fun v hv => by
          rw [hBv]; simp only; rw [if_neg (fun h => by linarith [h.2, hv.2])]]
        simp
      have hm : Measurable fun v => wideSameRate L u v * (u - v) := by
        unfold wideSameRate
        exact ((measurable_archLevyDensity.comp (measurable_const.sub measurable_id).abs).sub
          (measurable_archLevyDensity.comp (measurable_const.sub (measurable_const.add measurable_id)))).mul
            (measurable_const.sub measurable_id)
      have hSi : IntervalIntegrable (fun v => wideSameRate L u v * (u - v)) volume b η :=
        intervalIntegrable_of_abs_le hbη hm fun v hv =>
          abs_wideSameRate_mul_le hu.le huη (hb.le.trans hv.1) hv.2 hLη hη1
      have hPi : IntervalIntegrable (fun v => (u + v) * (u - v)) volume b η :=
        Continuous.intervalIntegrable (by fun_prop) _ _
      have hon : (∫ v in b..η, Bv v) = (2 * (1 - ρ) * (∫ v in b..η, wideSameRate L u v * (u - v)) +
          2 * γ * ∫ v in b..η, (u + v) * (u - v)) / (β + u) := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_add (hSi.const_mul _) (hPi.const_mul _), ← intervalIntegral.integral_div]
        refine intervalIntegral.integral_congr fun v hv => ?_
        rw [uIcc_of_le hbη] at hv
        rw [hBv]; simp only; rw [if_pos ⟨hbu, hv.1⟩]
        field_simp; ring
      have hpoly : (∫ v in b..η, (u + v) * (u - v)) ≤ (u - b) * (u ^ 2 - b ^ 2) := by
        rw [integral_deriv_eq_sub' (fun v => u ^ 2 * v - v ^ 3 / 3)
          (by funext v; simp (disch := fun_prop); ring) (fun v _ => by fun_prop) (by fun_prop)]
        nlinarith [mul_nonneg (sub_nonneg.2 huη) (sub_nonneg.2 hbu), mul_nonneg (sub_nonneg.2 huη)
          (mul_nonneg (sub_nonneg.2 huη) (sub_nonneg.2 hbu)), mul_nonneg (sub_nonneg.2 hbu)
          (sub_nonneg.2 hbu), mul_nonneg (mul_nonneg (sub_nonneg.2 hbu) (sub_nonneg.2 hbu)) hb.le,
          mul_nonneg (sub_nonneg.2 huη) (mul_nonneg (sub_nonneg.2 huη) (sub_nonneg.2 huη)),
          mul_nonneg (sub_nonneg.2 huη) (mul_nonneg (sub_nonneg.2 huη) hu.le)]
      have hS := integral_wideSameRate_band_le_simple (ωlo := ωlo) (ωhi := ωhi) hb hbu huη hLη hη1 hlo hhi
        hlo4 hcw
      rw [h0, zero_add, hon, div_le_div_iff_of_pos_right hβu]
      have h1ρ : 0 ≤ 2 * (1 - ρ) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hS h1ρ, mul_le_mul_of_nonneg_left hpoly (by linarith : 0 ≤ 2 * γ)]
    · rw [if_neg hbu]
      have e : (fun v => Bv v) = fun _ => (0 : ℝ) := funext fun v => by
        rw [hBv]; simp only; rw [if_neg (fun h => hbu h.1)]
      rw [e]; simp
  rw [hdec, hrec]
  linarith

end GaloisForLFunctions.ArithmeticIncidencePositivity

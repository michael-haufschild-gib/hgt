import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability
import GaloisForLFunctions.RHTower.RouteRBurnolXiPrimeTwoCompletionLanding

/-!
# The all-prime Burnol--Xi completion and its inverse-completion wall

For every ordinary prime the Burnol sub-window `[p⁻¹, 1]` has completed Mellin source

`F_p(w) = Γ_ℝ(w) (p^w - 1) ζ(w) / w`,

and the rational multiplier `C_p(w) = w²(w-1) / (2(p^w - 1))` carries it to `ξ` exactly.  The
multiplier is nonzero throughout the open critical strip, so a leading Xi Cartier coefficient
transports to the inverse-completed prime coefficient

`U_{ρ,p} = c_ρ / (p log p · C_p(ρ)) = K_ρ (p^ρ - 1) / (p log p)`.

Square summability of `U_ρ` over the primes holds exactly on the closed left half of the critical
strip.  The upper side is an integer comparison with `∑ 1/(n (log n)²)`; the lower side uses only
power-over-log growth and Euler's divergence of `∑ 1/p`.

The prime-log Green potential `Q_p = -(p+1)/(p (log p)²)` turns the unit--double valuation shuttle
into the boundary `A_p = Q_p R_p = 1/(p log p)`, and the physical endpoint presentation differs
from it by a sequence whose inverse completion is square summable across the whole strip.
-/

open Complex Real Filter Topology

noncomputable section

namespace RHTower

/-! ## The completion multiplier at an arbitrary prime -/

/-- The all-prime Burnol--Xi completion multiplier `C_p(w) = w²(w-1)/(2(p^w-1))`. -/
def burnolAllPrimeCompletionMultiplier (p : ℕ) (w : ℂ) : ℂ :=
  w ^ 2 * (w - 1) / (2 * ((p : ℂ) ^ w - 1))

/-- The completed Mellin source of the Burnol window `[p⁻¹, 1]`. -/
def burnolAllPrimeCompletedMellin (p : ℕ) (w : ℂ) : ℂ :=
  Complex.Gammaℝ w * ((p : ℂ) ^ w - 1) * (riemannZeta w / w)

theorem inv_nat_cpow_neg_eq_cpow {p : ℕ} (hp : 0 < p) (w : ℂ) :
    (((p : ℝ)⁻¹ : ℝ) : ℂ) ^ (-w) = (p : ℂ) ^ w := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have harg : Complex.arg ((p : ℝ) : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hppos.le]
    exact ne_of_lt Real.pi_pos
  have hcast : (((p : ℝ)⁻¹ : ℝ) : ℂ) = (((p : ℝ) : ℂ))⁻¹ := by
    push_cast
    ring
  rw [hcast, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]
  congr 1

/-- The prime dilation factor is nonzero in the open right half-plane. -/
theorem nat_cpow_sub_one_ne_zero {p : ℕ} (hp : 2 ≤ p) {w : ℂ} (hw : 0 < w.re) :
    (p : ℂ) ^ w - 1 ≠ 0 := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
  have hcast : ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) := by push_cast; ring
  have hnorm : ‖(p : ℂ) ^ w‖ = (p : ℝ) ^ w.re := by
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hppos]
  have hgt : (1 : ℝ) < (p : ℝ) ^ w.re := Real.one_lt_rpow_iff_of_pos hppos |>.mpr (Or.inl ⟨hp1, hw⟩)
  intro h
  have heq : (p : ℂ) ^ w = 1 := by linear_combination h
  rw [heq, norm_one] at hnorm
  linarith [hnorm ▸ hgt]

/-- The all-prime completion multiplier does not vanish in the open critical strip. -/
theorem burnolAllPrimeCompletionMultiplier_ne_zero {p : ℕ} (hp : 2 ≤ p)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    burnolAllPrimeCompletionMultiplier p w ≠ 0 := by
  have hwne0 : w ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hw0; linarith
  have hwne1 : w ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hw1; linarith
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hwne0) (sub_ne_zero.mpr hwne1))
    (mul_ne_zero two_ne_zero (nat_cpow_sub_one_ne_zero hp hw0))

/-- **The prime window source is the honest Burnol co-Poisson sub-window vector.** -/
theorem soninMellinEvaluation_primeWindow_eq {p : ℕ} (hp : 2 ≤ p)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    soninMellinEvaluation w
        (((coPoissonSubWindowSonin (c := ((p : ℝ)⁻¹ : ℝ)) (d := 1)
          (by positivity) (by
            have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.one_le_of_lt hp
            rw [inv_le_one_iff₀]
            exact Or.inr hp1) :
            soninExtendedSpace (subWindowAperture ((p : ℝ)⁻¹) 1)) : evenSubspace) : SoninL2) =
      burnolAllPrimeCompletedMellin p w := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  rw [soninMellinEvaluation_coPoissonSubWindowSonin _ _ hw0 hw1,
    show (((1 : ℝ) : ℂ)) = (1 : ℂ) by norm_num, Complex.one_cpow,
    inv_nat_cpow_neg_eq_cpow (by omega : 0 < p) w,
    burnolAllPrimeCompletedMellin, mellinCompletionFactor, Complex.Gammaℝ_def]
  ring

/-- **The exact pre-divisor all-prime completion identity `C_p F_p = ξ`.** -/
theorem burnolAllPrimeCompletionMultiplier_mul_completedMellin {p : ℕ} (hp : 2 ≤ p)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    burnolAllPrimeCompletionMultiplier p w * burnolAllPrimeCompletedMellin p w = xi w := by
  have hwne0 : w ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hw0; linarith
  have hwne1 : w ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hw1; linarith
  have hG : Complex.Gammaℝ w ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hw0
  rw [burnolAllPrimeCompletionMultiplier, burnolAllPrimeCompletedMellin,
    xi_eq_archFactor_mul_zeta hwne0 hwne1 hG, archFactor]
  field_simp [nat_cpow_sub_one_ne_zero hp hw0, hwne0]

/-! ## The inverse-completed prime coefficient -/

/-- The multiplicity-leading inverse-completed Cartier coefficient at the prime `p`. -/
def burnolAllPrimeInverseCompletionCoefficient (c ρ : ℂ) (p : ℕ) : ℂ :=
  c / ((p : ℂ) * ((Real.log (p : ℝ) : ℝ) : ℂ) * burnolAllPrimeCompletionMultiplier p ρ)

/-- The constant of the inverse completion, `K_ρ = 2 c / (ρ²(ρ-1))`. -/
def burnolAllPrimeInverseCompletionConstant (c ρ : ℂ) : ℂ := 2 * c / (ρ ^ 2 * (ρ - 1))

theorem burnolAllPrimeInverseCompletionConstant_ne_zero {c ρ : ℂ} (hc : c ≠ 0)
    (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) : burnolAllPrimeInverseCompletionConstant c ρ ≠ 0 :=
  div_ne_zero (mul_ne_zero two_ne_zero hc)
    (mul_ne_zero (pow_ne_zero 2 hρ0) (sub_ne_zero.mpr hρ1))

/-- **Explicit inverse completion.** -/
theorem burnolAllPrimeInverseCompletionCoefficient_eq {c ρ : ℂ} {p : ℕ} (hp : 2 ≤ p)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    burnolAllPrimeInverseCompletionCoefficient c ρ p =
      burnolAllPrimeInverseCompletionConstant c ρ *
        (((p : ℂ) ^ ρ - 1) / ((p : ℂ) * ((Real.log (p : ℝ) : ℝ) : ℂ))) := by
  have hρne0 : ρ ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hρ0; linarith
  have hρne1 : ρ ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hρ1; linarith
  have hdil : (p : ℂ) ^ ρ - 1 ≠ 0 := nat_cpow_sub_one_ne_zero hp hρ0
  rw [burnolAllPrimeInverseCompletionCoefficient, burnolAllPrimeInverseCompletionConstant,
    burnolAllPrimeCompletionMultiplier]
  field_simp

/-- Norm of the inverse-completed coefficient. -/
theorem norm_burnolAllPrimeInverseCompletionCoefficient {c ρ : ℂ} {p : ℕ} (hp : 2 ≤ p)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ‖burnolAllPrimeInverseCompletionCoefficient c ρ p‖ =
      ‖burnolAllPrimeInverseCompletionConstant c ρ‖ *
        (‖(p : ℂ) ^ ρ - 1‖ / ((p : ℝ) * Real.log (p : ℝ))) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hlogpos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.trans_lt' one_lt_two)
  rw [burnolAllPrimeInverseCompletionCoefficient_eq hp hρ0 hρ1, norm_mul, norm_div, norm_mul]
  congr 2
  rw [Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogpos]


/-! ## The sharp inverse-completion wall -/

/-- Upper prime-dilation bound for the numerator of the inverse completion. -/
theorem norm_nat_cpow_sub_one_le {p : ℕ} (hp : 2 ≤ p) (ρ : ℂ) :
    ‖(p : ℂ) ^ ρ - 1‖ ≤ (p : ℝ) ^ ρ.re + 1 := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hcast : ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) := by push_cast; ring
  have hnorm : ‖(p : ℂ) ^ ρ‖ = (p : ℝ) ^ ρ.re := by
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hppos]
  calc ‖(p : ℂ) ^ ρ - 1‖ ≤ ‖(p : ℂ) ^ ρ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = (p : ℝ) ^ ρ.re + 1 := by rw [hnorm, norm_one]

/-- Lower prime-dilation bound for the numerator of the inverse completion. -/
theorem le_norm_nat_cpow_sub_one {p : ℕ} (hp : 2 ≤ p) (ρ : ℂ) :
    (p : ℝ) ^ ρ.re - 1 ≤ ‖(p : ℂ) ^ ρ - 1‖ := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hcast : ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) := by push_cast; ring
  have hnorm : ‖(p : ℂ) ^ ρ‖ = (p : ℝ) ^ ρ.re := by
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hppos]
  have h := norm_sub_norm_le ((p : ℂ) ^ ρ) 1
  rw [hnorm, norm_one] at h
  exact h

/-- Pointwise upper bound on the closed left half of the strip. -/
theorem norm_burnolAllPrimeInverseCompletionCoefficient_sq_le {c ρ : ℂ} {p : ℕ} (hp : 2 ≤ p)
    (hρ0 : 0 < ρ.re) (hρhalf : ρ.re ≤ 1 / 2) :
    ‖burnolAllPrimeInverseCompletionCoefficient c ρ p‖ ^ 2 ≤
      4 * ‖burnolAllPrimeInverseCompletionConstant c ρ‖ ^ 2 *
        (1 / ((p : ℝ) * Real.log (p : ℝ) ^ 2)) := by
  have hρ1 : ρ.re < 1 := by linarith
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
  have hLpos : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hPne : (p : ℝ) ≠ 0 := ne_of_gt hppos
  have hLne : Real.log (p : ℝ) ≠ 0 := ne_of_gt hLpos
  set K : ℝ := ‖burnolAllPrimeInverseCompletionConstant c ρ‖ with hK
  have hKnn : 0 ≤ K := norm_nonneg _
  have hnum : ‖(p : ℂ) ^ ρ - 1‖ ≤ 2 * Real.sqrt (p : ℝ) := by
    refine (norm_nat_cpow_sub_one_le hp ρ).trans ?_
    have h1 : (p : ℝ) ^ ρ.re ≤ (p : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    have h2 : (1 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hp1.le (by norm_num)
    rw [Real.sqrt_eq_rpow]
    linarith
  rw [norm_burnolAllPrimeInverseCompletionCoefficient hp hρ0 hρ1, ← hK]
  have hbound : K * (‖(p : ℂ) ^ ρ - 1‖ / ((p : ℝ) * Real.log (p : ℝ))) ≤
      K * (2 * Real.sqrt (p : ℝ) / ((p : ℝ) * Real.log (p : ℝ))) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (by positivity)) hKnn
  have hnn : 0 ≤ K * (‖(p : ℂ) ^ ρ - 1‖ / ((p : ℝ) * Real.log (p : ℝ))) := by positivity
  refine (pow_le_pow_left₀ hnn hbound 2).trans_eq ?_
  rw [mul_pow, div_pow, mul_pow, mul_pow, Real.sq_sqrt hppos.le]
  field_simp
  ring

/-- Pointwise lower bound past the growth threshold. -/
theorem norm_burnolAllPrimeInverseCompletionCoefficient_sq_ge {c ρ : ℂ} {p : ℕ} (hp : 2 ≤ p)
    (hρhalf : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1)
    (hge2 : 2 ≤ (p : ℝ) ^ ρ.re)
    (hlog : Real.log (p : ℝ) ^ 2 ≤ (p : ℝ) ^ (2 * ρ.re - 1)) :
    ‖burnolAllPrimeInverseCompletionConstant c ρ‖ ^ 2 / 4 * (1 / (p : ℝ)) ≤
      ‖burnolAllPrimeInverseCompletionCoefficient c ρ p‖ ^ 2 := by
  have hρ0 : 0 < ρ.re := by linarith
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
  have hLpos : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  set K : ℝ := ‖burnolAllPrimeInverseCompletionConstant c ρ‖ with hK
  have hKnn : 0 ≤ K := norm_nonneg _
  have hnum : (p : ℝ) ^ ρ.re / 2 ≤ ‖(p : ℂ) ^ ρ - 1‖ := by
    have := le_norm_nat_cpow_sub_one hp ρ
    linarith
  rw [norm_burnolAllPrimeInverseCompletionCoefficient hp hρ0 hρ1, ← hK]
  have hstep : K * ((p : ℝ) ^ ρ.re / 2 / ((p : ℝ) * Real.log (p : ℝ))) ≤
      K * (‖(p : ℂ) ^ ρ - 1‖ / ((p : ℝ) * Real.log (p : ℝ))) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (by positivity)) hKnn
  have hnn : 0 ≤ K * ((p : ℝ) ^ ρ.re / 2 / ((p : ℝ) * Real.log (p : ℝ))) := by positivity
  refine le_trans ?_ (pow_le_pow_left₀ hnn hstep 2)
  have hrpow : ((p : ℝ) ^ ρ.re) ^ 2 = (p : ℝ) ^ (2 * ρ.re - 1) * (p : ℝ) := by
    have h1 : (p : ℝ) ^ (2 * ρ.re - 1) * (p : ℝ) =
        (p : ℝ) ^ (2 * ρ.re - 1) * (p : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
    rw [h1, ← Real.rpow_add hppos, ← Real.rpow_natCast ((p : ℝ) ^ ρ.re) 2,
      ← Real.rpow_mul hppos.le]
    congr 1
    push_cast
    ring
  have hexpand : (K * ((p : ℝ) ^ ρ.re / 2 / ((p : ℝ) * Real.log (p : ℝ)))) ^ 2 =
      K ^ 2 * ((p : ℝ) ^ (2 * ρ.re - 1) * (p : ℝ)) /
        (4 * ((p : ℝ) * Real.log (p : ℝ)) ^ 2) := by
    rw [← hrpow]
    field_simp
    ring
  have hleft : K ^ 2 / 4 * (1 / (p : ℝ)) = K ^ 2 / (4 * (p : ℝ)) := by field_simp
  rw [hleft, hexpand, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hlog
    (by positivity : (0 : ℝ) ≤ 4 * K ^ 2 * (p : ℝ) ^ 2)]

/-- **Convergent side of the wall.** -/
theorem summable_burnolAllPrimeInverseCompletionCoefficient_sq_of_re_le_half
    {c ρ : ℂ} (hρ0 : 0 < ρ.re) (hρhalf : ρ.re ≤ 1 / 2) :
    Summable (fun p : Nat.Primes =>
      ‖burnolAllPrimeInverseCompletionCoefficient c ρ (p : ℕ)‖ ^ 2) :=
  Summable.of_nonneg_of_le (fun p => by positivity)
    (fun p => norm_burnolAllPrimeInverseCompletionCoefficient_sq_le p.2.two_le hρ0 hρhalf)
    (burnolSummable_prime_one_div_mul_log_sq.mul_left
      (4 * ‖burnolAllPrimeInverseCompletionConstant c ρ‖ ^ 2))

/-- Threshold beyond which the prime-dilation gain dominates the logarithmic loss. -/
theorem burnolPrimeWallThreshold {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ N : ℕ, ∀ x : ℝ, (N : ℝ) ≤ x →
      2 ≤ x ^ σ ∧ Real.log x ^ 2 ≤ x ^ (2 * σ - 1) := by
  have hpos : 0 < 2 * σ - 1 := by linarith
  obtain ⟨N₀, hN₀⟩ := (burnolEventually_log_pow_le_rpow hpos 2).exists_forall_of_atTop
  refine ⟨max 4 ⌈N₀⌉₊, ?_⟩
  intro x hx
  have hx4 : (4 : ℝ) ≤ x := le_trans (by exact_mod_cast le_max_left 4 ⌈N₀⌉₊) hx
  have hxN : N₀ ≤ x := by
    refine le_trans (Nat.le_ceil N₀) ?_
    exact le_trans (by exact_mod_cast le_max_right 4 ⌈N₀⌉₊) hx
  refine ⟨?_, hN₀ x hxN⟩
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have h1 : x ^ ((1 : ℝ) / 2) ≤ x ^ σ := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h2 : (4 : ℝ) ^ ((1 : ℝ) / 2) ≤ x ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (by norm_num) hx4 (by norm_num)
  have h3 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 2,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  linarith [h3 ▸ h2, h1]

/-- **Divergent side of the wall.** -/
theorem not_summable_burnolAllPrimeInverseCompletionCoefficient_sq_of_half_lt_re
    {c ρ : ℂ} (hc : c ≠ 0) (hρhalf : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1) :
    ¬ Summable (fun p : Nat.Primes =>
      ‖burnolAllPrimeInverseCompletionCoefficient c ρ (p : ℕ)‖ ^ 2) := by
  have hρ0 : 0 < ρ.re := by linarith
  have hρne0 : ρ ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hρ0; linarith
  have hρne1 : ρ ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hρ1; linarith
  set K : ℝ := ‖burnolAllPrimeInverseCompletionConstant c ρ‖ with hK
  have hKpos : 0 < K :=
    norm_pos_iff.mpr (burnolAllPrimeInverseCompletionConstant_ne_zero hc hρne0 hρne1)
  obtain ⟨N, hN⟩ := burnolPrimeWallThreshold hρhalf
  intro hsum
  set s : Set Nat.Primes := {p : Nat.Primes | (p : ℕ) < N} with hs
  have hsfin : s.Finite :=
    Set.Finite.preimage (Subtype.val_injective.injOn) (Set.finite_Iio N)
  have hsub : Summable (fun x : ↥sᶜ => ‖burnolAllPrimeInverseCompletionCoefficient c ρ
      ((x : Nat.Primes) : ℕ)‖ ^ 2) := hsum.subtype _
  have hcomp : Summable (fun x : ↥sᶜ => K ^ 2 / 4 * (1 / (((x : Nat.Primes) : ℕ) : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) ?_ hsub
    rintro ⟨p, hp⟩
    have hple : N ≤ (p : ℕ) := by
      have : ¬ ((p : ℕ) < N) := hp
      omega
    have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
    have hPN : (N : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hple
    obtain ⟨hge2, hlog⟩ := hN ((p : ℕ) : ℝ) hPN
    exact norm_burnolAllPrimeInverseCompletionCoefficient_sq_ge hp2 hρhalf hρ1 hge2 hlog
  have hone : Summable (fun x : ↥sᶜ => 1 / (((x : Nat.Primes) : ℕ) : ℝ)) := by
    have h := hcomp.mul_left (4 / K ^ 2)
    refine h.congr (fun x => ?_)
    field_simp
  exact burnolNotSummable_prime_one_div ((Set.Finite.summable_compl_iff hsfin).mp hone)

/-- **The sharp all-prime inverse-completion wall.**  Square summability of the inverse-completed
prime Cartier coefficients is exactly the closed left half of the critical strip. -/
theorem summable_burnolAllPrimeInverseCompletionCoefficient_sq_iff
    {c ρ : ℂ} (hc : c ≠ 0) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    Summable (fun p : Nat.Primes =>
        ‖burnolAllPrimeInverseCompletionCoefficient c ρ (p : ℕ)‖ ^ 2) ↔
      ρ.re ≤ 1 / 2 := by
  constructor
  · intro hsum
    by_contra hlt
    exact not_summable_burnolAllPrimeInverseCompletionCoefficient_sq_of_half_lt_re
      hc (lt_of_not_ge hlt) hρ1 hsum
  · intro hle
    exact summable_burnolAllPrimeInverseCompletionCoefficient_sq_of_re_le_half hρ0 hle


/-! ## The singular potential and the physical endpoint presentation -/

/-- Unit--double valuation shuttle coefficient `R_p = -log p / (p+1)`. -/
def burnolValuationShuttle (p : ℕ) : ℝ := -Real.log (p : ℝ) / ((p : ℝ) + 1)

/-- Physical prime-endpoint coefficient `W_p = log p / p`. -/
def burnolPhysicalEndpointWeight (p : ℕ) : ℝ := Real.log (p : ℝ) / (p : ℝ)

/-- Endpoint response `E_p = log p / (p (p+1))`. -/
def burnolEndpointResponse (p : ℕ) : ℝ := Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) + 1))

/-- Prime-log Green potential `Q_p = -(p+1) / (p (log p)²)`. -/
def burnolPrimeLogGreenPotential (p : ℕ) : ℝ := -((p : ℝ) + 1) / ((p : ℝ) * Real.log (p : ℝ) ^ 2)

/-- The strict source boundary `A_p = 1 / (p log p)`. -/
def burnolSourceBoundary (p : ℕ) : ℝ := 1 / ((p : ℝ) * Real.log (p : ℝ))

/-- **Pre-divisor response renormalization `W_p + R_p = E_p`.** -/
theorem burnolPhysicalEndpointWeight_add_valuationShuttle {p : ℕ} (hp : 2 ≤ p) :
    burnolPhysicalEndpointWeight p + burnolValuationShuttle p = burnolEndpointResponse p := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  rw [burnolPhysicalEndpointWeight, burnolValuationShuttle, burnolEndpointResponse]
  field_simp
  ring

/-- **The Green potential turns the valuation shuttle into the strict boundary.** -/
theorem burnolPrimeLogGreenPotential_mul_valuationShuttle {p : ℕ} (hp : 2 ≤ p) :
    burnolPrimeLogGreenPotential p * burnolValuationShuttle p = burnolSourceBoundary p := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
  have hLpos : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  rw [burnolPrimeLogGreenPotential, burnolValuationShuttle, burnolSourceBoundary]
  field_simp

/-- **The potential of the endpoint response is the inverse-square correction.** -/
theorem burnolPrimeLogGreenPotential_mul_endpointResponse {p : ℕ} (hp : 2 ≤ p) :
    burnolPrimeLogGreenPotential p * burnolEndpointResponse p =
      -(1 / ((p : ℝ) ^ 2 * Real.log (p : ℝ))) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
  have hLpos : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  rw [burnolPrimeLogGreenPotential, burnolEndpointResponse]
  field_simp

/-- **The second presentation `Q_p W_p + A_p = Q_p E_p`.** -/
theorem burnolPrimeLogGreenPotential_physical_presentation {p : ℕ} (hp : 2 ≤ p) :
    burnolPrimeLogGreenPotential p * burnolPhysicalEndpointWeight p + burnolSourceBoundary p =
      burnolPrimeLogGreenPotential p * burnolEndpointResponse p := by
  rw [← burnolPrimeLogGreenPotential_mul_valuationShuttle hp, ← mul_add,
    burnolPhysicalEndpointWeight_add_valuationShuttle hp]

/-- **The cofinal boundary is square summable.** -/
theorem burnolSummable_sourceBoundary_sq :
    Summable (fun p : Nat.Primes => burnolSourceBoundary (p : ℕ) ^ 2) := by
  have hle : ∀ p : Nat.Primes, burnolSourceBoundary (p : ℕ) ^ 2 ≤
      (1 / Real.log 2 ^ 2) * (1 / (((p : ℕ) : ℝ) ^ 2)) := by
    intro p
    have hp : 2 ≤ (p : ℕ) := p.2.two_le
    have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
      have : (0 : ℕ) < (p : ℕ) := by omega
      exact_mod_cast this
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp
    have hL2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hLmono : Real.log 2 ≤ Real.log ((p : ℕ) : ℝ) := Real.log_le_log two_pos hp2
    have hrhs : (1 / Real.log 2 ^ 2) * (1 / (((p : ℕ) : ℝ) ^ 2)) =
        1 / (((p : ℕ) : ℝ) ^ 2 * Real.log 2 ^ 2) := by
      field_simp
    rw [burnolSourceBoundary, div_pow, one_pow, mul_pow, hrhs]
    have hsq : Real.log 2 ^ 2 ≤ Real.log ((p : ℕ) : ℝ) ^ 2 := by nlinarith
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  exact Summable.of_nonneg_of_le (fun p => sq_nonneg _) hle
    (burnolSummable_prime_one_div_sq.mul_left (1 / Real.log 2 ^ 2))

/-! ## The physical endpoint correction is harmless on the whole strip -/

/-- The inverse-square physical endpoint correction. -/
def burnolAllPrimePhysicalCorrection (c ρ : ℂ) (p : ℕ) : ℂ :=
  c / ((p : ℂ) ^ 2 * ((Real.log (p : ℝ) : ℝ) : ℂ) * burnolAllPrimeCompletionMultiplier p ρ)

theorem burnolAllPrimePhysicalCorrection_eq {c ρ : ℂ} {p : ℕ} (hp : 2 ≤ p)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    burnolAllPrimePhysicalCorrection c ρ p =
      burnolAllPrimeInverseCompletionConstant c ρ *
        (((p : ℂ) ^ ρ - 1) / ((p : ℂ) ^ 2 * ((Real.log (p : ℝ) : ℝ) : ℂ))) := by
  have hρne0 : ρ ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hρ0; linarith
  have hρne1 : ρ ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hρ1; linarith
  have hdil : (p : ℂ) ^ ρ - 1 ≠ 0 := nat_cpow_sub_one_ne_zero hp hρ0
  rw [burnolAllPrimePhysicalCorrection, burnolAllPrimeInverseCompletionConstant,
    burnolAllPrimeCompletionMultiplier]
  field_simp

/-- Pointwise bound for the physical endpoint correction. -/
theorem norm_burnolAllPrimePhysicalCorrection_sq_le {c ρ : ℂ} {p : ℕ} (hp : 2 ≤ p)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ‖burnolAllPrimePhysicalCorrection c ρ p‖ ^ 2 ≤
      (4 * ‖burnolAllPrimeInverseCompletionConstant c ρ‖ ^ 2 / Real.log 2 ^ 2) *
        (1 / ((p : ℝ) ^ 2)) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hL2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hLpos : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hLmono : Real.log 2 ≤ Real.log (p : ℝ) := Real.log_le_log two_pos hp2
  set K : ℝ := ‖burnolAllPrimeInverseCompletionConstant c ρ‖ with hK
  have hKnn : 0 ≤ K := norm_nonneg _
  have hnum : ‖(p : ℂ) ^ ρ - 1‖ ≤ 2 * (p : ℝ) := by
    refine (norm_nat_cpow_sub_one_le hp ρ).trans ?_
    have h1 : (p : ℝ) ^ ρ.re ≤ (p : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1.le hρ1.le
    rw [Real.rpow_one] at h1
    linarith
  have hnorm : ‖burnolAllPrimePhysicalCorrection c ρ p‖ =
      K * (‖(p : ℂ) ^ ρ - 1‖ / ((p : ℝ) ^ 2 * Real.log (p : ℝ))) := by
    rw [burnolAllPrimePhysicalCorrection_eq hp hρ0 hρ1, norm_mul, norm_div, norm_mul, ← hK]
    congr 2
    rw [norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos]
  rw [hnorm]
  have hbound : K * (‖(p : ℂ) ^ ρ - 1‖ / ((p : ℝ) ^ 2 * Real.log (p : ℝ))) ≤
      K * (2 * (p : ℝ) / ((p : ℝ) ^ 2 * Real.log 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ hKnn
    refine div_le_div₀ (by positivity) hnum (by positivity) ?_
    nlinarith
  have hnn : 0 ≤ K * (‖(p : ℂ) ^ ρ - 1‖ / ((p : ℝ) ^ 2 * Real.log (p : ℝ))) := by positivity
  refine (pow_le_pow_left₀ hnn hbound 2).trans_eq ?_
  field_simp
  ring

/-- **The physical endpoint correction is square summable throughout the strip.** -/
theorem burnolSummable_allPrimePhysicalCorrection_sq {c ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    Summable (fun p : Nat.Primes =>
      ‖burnolAllPrimePhysicalCorrection c ρ (p : ℕ)‖ ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun p => norm_burnolAllPrimePhysicalCorrection_sq_le p.2.two_le hρ0 hρ1)
    (burnolSummable_prime_one_div_sq.mul_left
      (4 * ‖burnolAllPrimeInverseCompletionConstant c ρ‖ ^ 2 / Real.log 2 ^ 2))

/-- Adding a square-summable sequence does not change square summability. -/
theorem burnolSummable_norm_sq_add_iff {ι : Type*} {f g : ι → ℂ}
    (hg : Summable (fun i => ‖g i‖ ^ 2)) :
    Summable (fun i => ‖f i + g i‖ ^ 2) ↔ Summable (fun i => ‖f i‖ ^ 2) := by
  have hbound : ∀ a b : ℂ, ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    intro a b
    have h1 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  constructor
  · intro hsum
    have hmaj : Summable (fun i => 2 * ‖f i + g i‖ ^ 2 + 2 * ‖g i‖ ^ 2) :=
      (hsum.mul_left 2).add (hg.mul_left 2)
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) hmaj
    have h := hbound (f i + g i) (-g i)
    simpa using h
  · intro hsum
    have hmaj : Summable (fun i => 2 * ‖f i‖ ^ 2 + 2 * ‖g i‖ ^ 2) :=
      (hsum.mul_left 2).add (hg.mul_left 2)
    exact Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => hbound (f i) (g i)) hmaj

/-- **The physical endpoint presentation differs from the strict boundary by the correction.** -/
theorem burnolAllPrimePhysical_inverse_completion {c ρ : ℂ} {p : ℕ} (hp : 2 ≤ p)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ((burnolPrimeLogGreenPotential p * burnolPhysicalEndpointWeight p : ℝ) : ℂ) * c /
        burnolAllPrimeCompletionMultiplier p ρ =
      -burnolAllPrimeInverseCompletionCoefficient c ρ p -
        burnolAllPrimePhysicalCorrection c ρ p := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
  have hLpos : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hCne : burnolAllPrimeCompletionMultiplier p ρ ≠ 0 :=
    burnolAllPrimeCompletionMultiplier_ne_zero hp hρ0 hρ1
  have hpC : ((p : ℕ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hLC : ((Real.log (p : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hLpos)
  have hval : burnolPrimeLogGreenPotential p * burnolPhysicalEndpointWeight p =
      -(((p : ℝ) + 1) / ((p : ℝ) ^ 2 * Real.log (p : ℝ))) := by
    rw [burnolPrimeLogGreenPotential, burnolPhysicalEndpointWeight]
    field_simp
  rw [hval, burnolAllPrimeInverseCompletionCoefficient, burnolAllPrimePhysicalCorrection]
  push_cast
  field_simp
  ring

/-- **The two presentations share the entrance wall.** -/
theorem summable_burnolAllPrimePhysicalPresentation_sq_iff
    {c ρ : ℂ} (hc : c ≠ 0) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    Summable (fun p : Nat.Primes =>
        ‖((burnolPrimeLogGreenPotential (p : ℕ) * burnolPhysicalEndpointWeight (p : ℕ) : ℝ) : ℂ) *
          c / burnolAllPrimeCompletionMultiplier (p : ℕ) ρ‖ ^ 2) ↔
      ρ.re ≤ 1 / 2 := by
  have hrewrite : (fun p : Nat.Primes =>
      ‖((burnolPrimeLogGreenPotential (p : ℕ) * burnolPhysicalEndpointWeight (p : ℕ) : ℝ) : ℂ) *
        c / burnolAllPrimeCompletionMultiplier (p : ℕ) ρ‖ ^ 2) =
      fun p : Nat.Primes => ‖(-burnolAllPrimeInverseCompletionCoefficient c ρ (p : ℕ)) +
        (-burnolAllPrimePhysicalCorrection c ρ (p : ℕ))‖ ^ 2 := by
    funext p
    rw [burnolAllPrimePhysical_inverse_completion p.2.two_le hρ0 hρ1]
    ring_nf
  have hcorr : Summable (fun p : Nat.Primes =>
      ‖-burnolAllPrimePhysicalCorrection c ρ (p : ℕ)‖ ^ 2) := by
    simpa only [norm_neg] using burnolSummable_allPrimePhysicalCorrection_sq
      (c := c) (ρ := ρ) hρ0 hρ1
  rw [hrewrite, burnolSummable_norm_sq_add_iff hcorr]
  simpa only [norm_neg] using
    summable_burnolAllPrimeInverseCompletionCoefficient_sq_iff (c := c) (ρ := ρ) hc hρ0 hρ1

end RHTower

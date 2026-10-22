import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeLogHeightGreen

/-!
# Centered Mellin jets on the prime-log height source

For a complex parameter `s` and an order `j`, the centered Mellin conormal jet

`M_s^{(j)}(a) = ∑_m (-ℓ(m))^j e^{-(s-½)ℓ(m)} a_m`

is a continuous functional on the source: the frequency is bounded by the logarithmic height, so
the exponential factor is bounded by a real power of the height, and every seminorm beyond
`|Re(s-½)| + j` dominates the jet.  Reflection exchanges `s` and `1-s` up to the sign `(-1)^j`,
so the completion retains every finite-order centered jet at every complex parameter, not only on
the critical line.

* `deningerMellinJet` : the jet.
* `deningerMellinJet_norm_le` : **continuity.**
* `deningerMellinJet_reflect` : **the functional equation of the jet.**
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- The integrand of the centered Mellin jet. -/
def deningerMellinSymbol (s : ℂ) (j : ℕ) (m : DeningerPrimeLattice) : ℂ :=
  ((-(deningerFreq m) : ℝ) : ℂ) ^ j *
    Complex.exp (-(s - 1 / 2) * ((deningerFreq m : ℝ) : ℂ))

/-- The Mellin symbol is a multiplier of growth `|Re(s-½)| + j`. -/
theorem deningerMellinSymbol_norm_le (s : ℂ) (j k : ℕ)
    (hk : |(s - 1 / 2).re| + (j : ℝ) ≤ (k : ℝ)) (m : DeningerPrimeLattice) :
    ‖deningerMellinSymbol s j m‖ ≤ deningerHeight m ^ k := by
  have hHpos : (0 : ℝ) < deningerHeight m := deningerHeight_pos m
  have hH1 : (1 : ℝ) ≤ deningerHeight m := one_le_deningerHeight m
  have hjk : (j : ℝ) ≤ (k : ℝ) := by
    have habs : 0 ≤ |(s - 1 / 2).re| := abs_nonneg _
    linarith
  have hjkNat : j ≤ k := by exact_mod_cast hjk
  -- the polynomial factor
  have hpoly : ‖((-(deningerFreq m) : ℝ) : ℂ) ^ j‖ ≤ deningerHeight m ^ j := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_deningerFreq_le_height m) j
  -- the exponential factor
  have hre : (-(s - 1 / 2) * ((deningerFreq m : ℝ) : ℂ)).re
      = -((s - 1 / 2).re * deningerFreq m) := by
    simp [Complex.mul_re]
    ring
  have hexp : ‖Complex.exp (-(s - 1 / 2) * ((deningerFreq m : ℝ) : ℂ))‖
      ≤ deningerHeight m ^ ((k : ℝ) - (j : ℝ)) := by
    rw [Complex.norm_exp, hre]
    have hbound : -((s - 1 / 2).re * deningerFreq m)
        ≤ |(s - 1 / 2).re| * Real.log (deningerHeight m) := by
      have h1 : -((s - 1 / 2).re * deningerFreq m) ≤ |(s - 1 / 2).re * deningerFreq m| :=
        neg_le_abs _
      have h2 : |(s - 1 / 2).re * deningerFreq m|
          = |(s - 1 / 2).re| * |deningerFreq m| := abs_mul _ _
      have h3 : |deningerFreq m| ≤ Real.log (deningerHeight m) :=
        abs_deningerFreq_le_log_height m
      have h4 : |(s - 1 / 2).re| * |deningerFreq m|
          ≤ |(s - 1 / 2).re| * Real.log (deningerHeight m) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      rw [h2] at h1
      linarith
    have hmono : Real.exp (-((s - 1 / 2).re * deningerFreq m))
        ≤ Real.exp (|(s - 1 / 2).re| * Real.log (deningerHeight m)) :=
      Real.exp_le_exp.mpr hbound
    have hrpow : Real.exp (|(s - 1 / 2).re| * Real.log (deningerHeight m))
        = deningerHeight m ^ |(s - 1 / 2).re| := by
      rw [Real.rpow_def_of_pos hHpos, mul_comm]
    have hstep : deningerHeight m ^ |(s - 1 / 2).re|
        ≤ deningerHeight m ^ ((k : ℝ) - (j : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
    rw [hrpow] at hmono
    exact le_trans hmono hstep
  have hsplit : deningerHeight m ^ j * deningerHeight m ^ ((k : ℝ) - (j : ℝ))
      = deningerHeight m ^ k := by
    rw [← Real.rpow_natCast (deningerHeight m) j, ← Real.rpow_natCast (deningerHeight m) k,
      ← Real.rpow_add hHpos]
    ring_nf
  rw [deningerMellinSymbol, norm_mul]
  calc ‖((-(deningerFreq m) : ℝ) : ℂ) ^ j‖ *
        ‖Complex.exp (-(s - 1 / 2) * ((deningerFreq m : ℝ) : ℂ))‖
      ≤ deningerHeight m ^ j * deningerHeight m ^ ((k : ℝ) - (j : ℝ)) := by
        refine mul_le_mul hpoly hexp (norm_nonneg _) ?_
        exact pow_nonneg hHpos.le _
    _ = deningerHeight m ^ k := hsplit

private theorem deningerMellinJet_summable (s : ℂ) (j k : ℕ)
    (hk : |(s - 1 / 2).re| + (j : ℝ) ≤ (k : ℝ)) (a : DeningerHeightKothe) :
    Summable fun m : DeningerPrimeLattice =>
      deningerMellinSymbol s j m * (a : DeningerPrimeLattice → ℂ) m := by
  refine Summable.of_norm_bounded (a.2 k) fun m => ?_
  show ‖deningerMellinSymbol s j m * (a : DeningerPrimeLattice → ℂ) m‖
      ≤ deningerHeightKotheData.w k m * ‖(a : DeningerPrimeLattice → ℂ) m‖
  rw [deningerHeightKotheData_w, norm_mul]
  exact mul_le_mul_of_nonneg_right (deningerMellinSymbol_norm_le s j k hk m) (norm_nonneg _)

/-- **The centered Mellin conormal jet** `M_s^{(j)}(a) = ∑_m (-ℓ(m))^j e^{-(s-½)ℓ(m)} a_m`. -/
def deningerMellinJet (s : ℂ) (j : ℕ) (a : DeningerHeightKothe) : ℂ :=
  ∑' m, deningerMellinSymbol s j m * (a : DeningerPrimeLattice → ℂ) m

/-- **Continuity of the jet**: every seminorm beyond `|Re(s-½)| + j` dominates it. -/
theorem deningerMellinJet_norm_le (s : ℂ) (j k : ℕ)
    (hk : |(s - 1 / 2).re| + (j : ℝ) ≤ (k : ℝ)) (a : DeningerHeightKothe) :
    ‖deningerMellinJet s j a‖ ≤ deningerHeightSeminorm k a := by
  have hnormSummable : Summable fun m : DeningerPrimeLattice =>
      ‖deningerMellinSymbol s j m * (a : DeningerPrimeLattice → ℂ) m‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) (a.2 k)
    show ‖deningerMellinSymbol s j m * (a : DeningerPrimeLattice → ℂ) m‖
        ≤ deningerHeightKotheData.w k m * ‖(a : DeningerPrimeLattice → ℂ) m‖
    rw [deningerHeightKotheData_w, norm_mul]
    exact mul_le_mul_of_nonneg_right (deningerMellinSymbol_norm_le s j k hk m) (norm_nonneg _)
  refine le_trans (norm_tsum_le_tsum_norm hnormSummable) ?_
  rw [deningerHeightSeminorm_apply]
  refine Summable.tsum_le_tsum (fun m => ?_) hnormSummable (a.2 k)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (deningerMellinSymbol_norm_le s j k hk m) (norm_nonneg _)

/-- The Mellin symbol at a reflected index is the symbol of the reflected parameter. -/
theorem deningerMellinSymbol_neg (s : ℂ) (j : ℕ) (m : DeningerPrimeLattice) :
    deningerMellinSymbol s j (-m) = (-1) ^ j * deningerMellinSymbol (1 - s) j m := by
  rw [deningerMellinSymbol, deningerMellinSymbol, deningerFreq_neg]
  have hpow : ((-(-(deningerFreq m)) : ℝ) : ℂ) ^ j
      = (-1) ^ j * ((-(deningerFreq m) : ℝ) : ℂ) ^ j := by
    rw [neg_neg]
    rw [show ((deningerFreq m : ℝ) : ℂ) = (-1) * ((-(deningerFreq m) : ℝ) : ℂ) by push_cast; ring]
    rw [mul_pow]
  have hexp : Complex.exp (-(s - 1 / 2) * ((-(deningerFreq m) : ℝ) : ℂ))
      = Complex.exp (-((1 - s) - 1 / 2) * ((deningerFreq m : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [hpow, hexp]
  ring

/-- **The functional equation of the jet.**  Reflection exchanges `s` with `1-s` up to the sign
`(-1)^j`. -/
theorem deningerMellinJet_reflect (s : ℂ) (j : ℕ) (a : DeningerHeightKothe) :
    deningerMellinJet s j (deningerHeightReflect a)
      = (-1) ^ j * deningerMellinJet (1 - s) j a := by
  rw [deningerMellinJet, deningerMellinJet]
  rw [← (Equiv.neg DeningerPrimeLattice).tsum_eq
    (fun m : DeningerPrimeLattice =>
      deningerMellinSymbol s j m *
        ((deningerHeightReflect a : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) m)]
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  show deningerMellinSymbol s j (-m) *
      ((deningerHeightReflect a : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) (-m)
      = (-1) ^ j * (deningerMellinSymbol (1 - s) j m * (a : DeningerPrimeLattice → ℂ) m)
  rw [deningerHeightReflect_coe, neg_neg, deningerMellinSymbol_neg]
  ring

end

end RHTower

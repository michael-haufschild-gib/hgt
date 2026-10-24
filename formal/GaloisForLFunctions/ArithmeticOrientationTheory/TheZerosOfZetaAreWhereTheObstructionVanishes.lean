import GaloisForLFunctions.ArithmeticOrientationTheory.UnpayabilityIsLocatedOnTheBohrPolydisk
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheOscillatingSmoothPowerShiftsItsPoleOffTheRealAbscissa

/-!
# The zeros of zeta are where the obstruction vanishes

The oscillating probe `c(d) = d^{−ε} cos(t log d)`, `0 < ε < ½`, has its pole at
`ρ = 1 − ε + it` and its conjugate.  Trans-Horizon Incidence Mechanics proves that a critical
Wiener kernel `k` repairs it iff `K(ρ) = 0` or `ζ(ρ) = 0`
(`receiverBounded_dirichletConv_oscillatingSmoothPower_iff`).  In the language of the Bohr
spectrum (`UnpayabilityIsLocatedOnTheBohrPolydisk`):

* **Off the zeros the obstruction is the conjugate pair** (`mem_obstructionHull_oscillating_iff`):
  if `ζ(ρ) ≠ 0`, the obstruction hull of the probe consists of the Bohr points that agree with the
  half-plane point `ρ` or with `ρ̄` at every prime.  The repairing ideal is the intersection of the
  two maximal ideals (`mem_paidIdeal_oscillating_iff`), since a real kernel vanishes at `ρ` iff it
  vanishes at `ρ̄` (`complexPoleValue_conj`).
* **At a zero the obstruction vanishes** (`obstructionHull_oscillating_nonempty_iff`): the hull is
  empty iff `ζ(ρ) = 0`.

So the zeros of `ζ` in the strip `½ < Re s < 1` are exactly the points `ρ` at which the receiver's
spectral obstruction of the probe disappears: the hull, the field's index object for payment, reads
the zero set of `ζ` point by point.
-/

open Finset ArithmeticFunction LSeries Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt

noncomputable section
set_option autoImplicit false

/-! ### Conjugation and the complex pole value -/

/-- A real kernel takes conjugate pole values at conjugate points. -/
theorem complexPoleValue_conj (f : ℕ → ℝ) (ρ : ℂ) :
    complexPoleValue f (starRingEnd ℂ ρ) = starRingEnd ℂ (complexPoleValue f ρ) := by
  unfold complexPoleValue
  rw [Complex.conj_tsum]
  refine tsum_congr fun j => ?_
  rw [map_mul, Complex.conj_ofReal, ← map_neg, Complex.cpow_conj _ _ (by
    rw [Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg j)]; exact Real.pi_ne_zero.symm),
    Complex.conj_ofReal]

theorem summable_complexPoleValue {f : ℕ → ℝ} (hf : CriticalWiener f) {ρ : ℂ} (hρ : 1 / 2 ≤ ρ.re) :
    Summable fun j : ℕ => (f j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ) := by
  refine Summable.of_norm (hf.of_nonneg_of_le (fun _ => norm_nonneg _) fun j => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ; linarith
    simp [Complex.zero_cpow (neg_ne_zero.2 this)]
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hj), Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) (by linarith)

/-- The Dirichlet series of an element of `𝒲_{1/2}` splits into the pole values of its parts. -/
theorem lSeries_eq_complexPoleValue (k : WienerAlgebraAt (1 / 2)) {ρ : ℂ} (hρ : 1 / 2 ≤ ρ.re) :
    LSeries (⇑k.toFn) ρ = complexPoleValue (rePart k) ρ + I * complexPoleValue (imPart k) ρ := by
  unfold LSeries complexPoleValue
  rw [← tsum_mul_left, ← (summable_complexPoleValue (criticalWiener_rePart k) hρ).tsum_add
    ((summable_complexPoleValue (criticalWiener_imPart k) hρ).mul_left I)]
  refine tsum_congr fun j => ?_
  rcases eq_or_ne j 0 with rfl | hj
  · have : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ; linarith
    simp [Complex.zero_cpow (neg_ne_zero.2 this)]
  · rw [term_of_ne_zero hj, div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.ofReal_natCast]
    unfold rePart imPart
    conv_lhs => rw [← Complex.re_add_im (k.toFn j)]
    ring

/-! ### The repairing ideal and the hull of the oscillating probe -/

theorem summable_abs_oscillatingSmoothPower_div {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Summable fun d : ℕ => |oscillatingSmoothPower ε t d / d| := by
  refine (Real.summable_nat_rpow.mpr (by linarith : -(1 + ε) < -1)).of_nonneg_of_le
    (fun _ => abs_nonneg _) fun d => ?_
  have h : oscillatingSmoothPower ε t d / d =
      dampedSignWeight (fun d => Real.cos (t * Real.log d)) ε d / d := by
    unfold oscillatingSmoothPower dampedSignWeight; ring
  rw [h, dampedSignWeight_div hε, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg d) _) (Real.abs_cos_le_one _)

theorem half_le_re_oscillationExponent {ε : ℝ} (hε2 : ε < 1 / 2) (t : ℝ) :
    1 / 2 ≤ (oscillationExponent ε t).re := by
  rw [oscillationExponent_re]; linarith

theorem half_le_re_conj_oscillationExponent {ε : ℝ} (hε2 : ε < 1 / 2) (t : ℝ) :
    1 / 2 ≤ (starRingEnd ℂ (oscillationExponent ε t)).re := by
  rw [Complex.conj_re, oscillationExponent_re]; linarith

/-- The pole point `ρ = 1 − ε + it` of the oscillating probe. -/
def oscPoint (ε t : ℝ) (hε2 : ε < 1 / 2) : BohrPoint :=
  halfPlanePoint (1 / 2) (oscillationExponent ε t) (half_le_re_oscillationExponent hε2 t)

/-- Its conjugate `ρ̄`. -/
def oscPointConj (ε t : ℝ) (hε2 : ε < 1 / 2) : BohrPoint :=
  halfPlanePoint (1 / 2) (starRingEnd ℂ (oscillationExponent ε t))
    (half_le_re_conj_oscillationExponent hε2 t)

/-- **Off the zeros, the repairing ideal of the probe is the intersection of the maximal ideals of
`ρ` and `ρ̄`.** -/
theorem mem_paidIdeal_oscillating_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {t : ℝ}
    (hz : riemannZeta (oscillationExponent ε t) ≠ 0) (k : WienerAlgebraAt (1 / 2)) :
    k ∈ paidIdeal (oscillatingSmoothPower ε t) (summable_abs_oscillatingSmoothPower_div hε t) ↔
      bohrEval (1 / 2) k.toFn (oscPoint ε t hε2) = 0 ∧
        bohrEval (1 / 2) k.toFn (oscPointConj ε t hε2) = 0 := by
  rw [mem_paidIdeal _ _, receiverBounded_dirichletConv_oscillatingSmoothPower_iff hε hε2 t
      (criticalWiener_rePart k),
    receiverBounded_dirichletConv_oscillatingSmoothPower_iff hε hε2 t (criticalWiener_imPart k),
    oscPoint, oscPointConj, bohrEval_halfPlanePoint, bohrEval_halfPlanePoint,
    lSeries_eq_complexPoleValue k (half_le_re_oscillationExponent hε2 t),
    lSeries_eq_complexPoleValue k (half_le_re_conj_oscillationExponent hε2 t),
    complexPoleValue_conj, complexPoleValue_conj]
  rw [or_iff_left hz, or_iff_left hz]
  set A := complexPoleValue (rePart k) (oscillationExponent ε t)
  set B := complexPoleValue (imPart k) (oscillationExponent ε t)
  constructor
  · rintro ⟨hA, hB⟩
    simp [hA, hB]
  · rintro ⟨h1, h2⟩
    -- `A + iB = 0` and `Ā + iB̄ = 0` force `A = B = 0`
    have h2' : A - I * B = 0 := by
      have := congrArg (starRingEnd ℂ) h2
      simpa [map_add, map_mul, Complex.conj_I, Complex.conj_conj, sub_eq_add_neg] using this
    have hA : A = 0 := by linear_combination (h1 + h2') / 2
    have hB : B = 0 := by
      have : I * B = 0 := by linear_combination (h1 - h2') / 2
      exact (mul_eq_zero.1 this).resolve_left Complex.I_ne_zero
    exact ⟨hA, hB⟩

/-- **Off the zeros the obstruction of the probe is the conjugate pair**: if `ζ(ρ) ≠ 0`, a Bohr
point lies in the hull iff it agrees with `ρ` or with `ρ̄` at every prime. -/
theorem mem_obstructionHull_oscillating_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {t : ℝ}
    (hz : riemannZeta (oscillationExponent ε t) ≠ 0) (ω : BohrPoint) :
    ω ∈ obstructionHull (oscillatingSmoothPower ε t) (summable_abs_oscillatingSmoothPower_div hε t) ↔
      (∀ p : ℕ, p.Prime → ω.ω p = (oscPoint ε t hε2).ω p) ∨
        (∀ p : ℕ, p.Prime → ω.ω p = (oscPointConj ε t hε2).ω p) := by
  constructor
  · intro hω
    by_contra hno
    push Not at hno
    obtain ⟨⟨p, hp, hp'⟩, ⟨q, hq, hq'⟩⟩ := hno
    -- a kernel vanishing at `ρ` through `p` and at `ρ̄` through `q`, but not at `ω`
    set a : ℂ := (oscPoint ε t hε2).ω p / (p : ℂ) ^ ((1 / 2 : ℝ) : ℂ)
    set b : ℂ := (oscPointConj ε t hε2).ω q / (q : ℂ) ^ ((1 / 2 : ℝ) : ℂ)
    set k : WienerAlgebraAt (1 / 2) := (pointMass p - a • 1) * (pointMass q - b • 1)
    have hev : ∀ ν : BohrPoint, bohrEval (1 / 2) k.toFn ν =
        (ν.ω p / (p : ℂ) ^ ((1 / 2 : ℝ) : ℂ) - a) * (ν.ω q / (q : ℂ) ^ ((1 / 2 : ℝ) : ℂ) - b) :=
      fun ν => by
        rw [← bohrCharacter_apply, map_mul, map_sub, map_sub, map_smul, map_smul, map_one,
          bohrCharacter_apply, bohrCharacter_apply, toFn_pointMass, toFn_pointMass,
          bohrEval_pointMass hp.ne_zero, bohrEval_pointMass hq.ne_zero, smul_eq_mul, smul_eq_mul,
          mul_one, mul_one]
    have hk : k ∈ paidIdeal (oscillatingSmoothPower ε t)
        (summable_abs_oscillatingSmoothPower_div hε t) := by
      rw [mem_paidIdeal_oscillating_iff hε hε2 hz, hev, hev]
      exact ⟨by simp [a], by simp [b]⟩
    have h := hω k hk
    rw [hev] at h
    have hp0 : (p : ℂ) ^ ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h' => hp.ne_zero (by exact_mod_cast h'.1)
    have hq0 : (q : ℂ) ^ ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h' => hq.ne_zero (by exact_mod_cast h'.1)
    rcases mul_eq_zero.1 h with h1 | h1
    · exact hp' ((div_left_inj' hp0).1 (sub_eq_zero.1 h1))
    · exact hq' ((div_left_inj' hq0).1 (sub_eq_zero.1 h1))
  · rintro (h | h) k hk
    · rw [bohrEval_congr k.toFn (BohrPoint.eq_of_primes h)]
      exact ((mem_paidIdeal_oscillating_iff hε hε2 hz k).1 hk).1
    · rw [bohrEval_congr k.toFn (BohrPoint.eq_of_primes h)]
      exact ((mem_paidIdeal_oscillating_iff hε hε2 hz k).1 hk).2

/-- **The zeros of `ζ` are where the obstruction vanishes**: for `0 < ε < ½` the obstruction hull
of the probe at `ρ = 1 − ε + it` is empty iff `ζ(ρ) = 0`. -/
theorem obstructionHull_oscillating_nonempty_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (t : ℝ) :
    (obstructionHull (oscillatingSmoothPower ε t)
        (summable_abs_oscillatingSmoothPower_div hε t)).Nonempty ↔
      riemannZeta (oscillationExponent ε t) ≠ 0 := by
  rw [obstructionHull_nonempty_iff, receiverBounded_oscillatingSmoothPower_iff hε hε2.le t]
  rfl

end

end GaloisForLFunctions.ArithmeticOrientationTheory

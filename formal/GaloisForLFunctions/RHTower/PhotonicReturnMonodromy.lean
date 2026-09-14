import GaloisForLFunctions.Hurwitz.AnchorTransversality
import GaloisForLFunctions.RHTower.HeatEnergyTangent
import GaloisForLFunctions.Hurwitz.MonodromyScalar
import GaloisForLFunctions.RHTower.PhotonicParabolicReturn

/-!
# The photonic return germ on its logarithmic phase cover

The actual continued Hurwitz functions give a holomorphic regular phase germ.
Adding the singular phase power on the logarithmic cover agrees exactly with
the existing periodic-zeta return boundary. Its nontrivial deck character
canonically projects out the regular germ; that germ's first jet reconstructs
the full parabolic return matrix, including its nilpotent channel.

These are analytic continuation and specialization identities, with no RH input.
The ramified map from physical band-edge detuning to Floquet phase, and any
mechanism confining the response defects to real monodromy, remain separate.
-/

open Complex HurwitzZeta HurwitzZetaContinuation

namespace RHTower

private theorem photonic_continued_shift (w : ℂ) (hw : 0 < w.re) (a : ℝ) :
    continuedHzeta w (1 + (a : ℂ)) = riemannZeta w + shiftDiffSeries a w := by
  rw [continuedHzeta, regularizationOrder_eq_zero hw, continuedAt, restoration_zero]
  rw [add_comm]
  congr 1
  apply tsum_congr
  intro n
  rw [remainder, taylorPoly_zero, shiftDiffTerm]
  push_cast
  congr 2
  ring

/-- The two anchored Hurwitz channels forming the regular phase germ. -/
noncomputable def photonicRegularPhase (s z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Gamma (1 - s) *
    (exp ((Real.pi : ℂ) * I * (1 - s) / 2) *
        continuedHzeta (1 - s) (1 + z / (2 * (Real.pi : ℂ))) +
      exp (-(Real.pi : ℂ) * I * (1 - s) / 2) *
        continuedHzeta (1 - s) (1 - z / (2 * (Real.pi : ℂ))))

/-- The constant term is the meromorphically continued return count. -/
theorem photonicRegularPhase_zero :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → photonicRegularPhase s 0 = riemannZeta s := by
  intro s h0 h1
  have hw : 0 < (1 - s).re := by simp; linarith
  have hn : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hne : 1 - s ≠ 1 := by
    intro he
    have hre := congrArg Complex.re he
    simp at hre
    linarith
  have hf := riemannZeta_one_sub hn hne
  rw [sub_sub_cancel] at hf
  simp only [photonicRegularPhase, zero_div, add_zero, sub_zero, continuedHzeta_at_one]
  rw [hf, Complex.cos]
  rw [show (Real.pi : ℂ) * (1 - s) / 2 * I =
    (Real.pi : ℂ) * I * (1 - s) / 2 by ring,
    show -((Real.pi : ℂ) * (1 - s) / 2) * I =
    -(Real.pi : ℂ) * I * (1 - s) / 2 by ring]
  ring

/-- Complex-shift analyticity crosses the zero-phase boundary. -/
theorem photonicRegularPhase_analytic :
    ∀ s : ℂ, s.re < 1 → AnalyticAt ℂ (photonicRegularPhase s) 0 := by
  intro s h1
  have hw : 0 < (1 - s).re := by simp; linarith
  have hp : AnalyticAt ℂ (fun z : ℂ => 1 + z / (2 * (Real.pi : ℂ))) 0 :=
    analyticAt_const.add analyticAt_id.div_const
  have hm : AnalyticAt ℂ (fun z : ℂ => 1 - z / (2 * (Real.pi : ℂ))) 0 :=
    analyticAt_const.sub analyticAt_id.div_const
  have hh := continuedHzeta_analyticAt_one hw
  have hhp : AnalyticAt ℂ
      (fun z : ℂ => continuedHzeta (1 - s) (1 + z / (2 * (Real.pi : ℂ)))) 0 :=
    hh.comp_of_eq hp (by simp)
  have hhm : AnalyticAt ℂ
      (fun z : ℂ => continuedHzeta (1 - s) (1 - z / (2 * (Real.pi : ℂ)))) 0 :=
    hh.comp_of_eq hm (by simp)
  exact analyticAt_const.mul ((analyticAt_const.mul hhp).add (analyticAt_const.mul hhm))

/-- Agreement with the already certified real-phase regular part. -/
theorem photonicRegularPhase_boundary :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → ∀ θ : ℝ,
      photonicRegularPhase s θ = riemannZeta s + jonquiereRemainder s θ := by
  intro s h0 h1 θ
  have hw : 0 < (1 - s).re := by simp; linarith
  have hp := photonic_continued_shift (1 - s) hw (θ / (2 * Real.pi))
  have hm := photonic_continued_shift (1 - s) hw (-(θ / (2 * Real.pi)))
  push_cast at hp hm
  rw [← sub_eq_add_neg] at hm
  have hc := photonicRegularPhase_zero s h0 h1
  simp only [photonicRegularPhase, zero_div, add_zero, sub_zero,
    continuedHzeta_at_one] at hc
  rw [photonicRegularPhase, hp, hm, jonquiereRemainder]
  linear_combination hc

/-- The first regular phase derivative retains the nilpotent return channel. -/
theorem photonicRegularPhase_hasDerivAt :
    ∀ s : ℂ, 0 < s.re → s.re < 1 →
      HasDerivAt (photonicRegularPhase s) (I * riemannZeta (s - 1)) 0 := by
  intro s h0 h1
  have hw : 0 < (1 - s).re := by simp; linarith
  have hid : HasDerivAt (fun z : ℂ => z) 1 0 := hasDerivAt_id 0
  have hp : HasDerivAt (fun z : ℂ => 1 + z / (2 * (Real.pi : ℂ)))
      (1 / (2 * (Real.pi : ℂ))) 0 :=
    (hid.div_const (2 * (Real.pi : ℂ))).const_add 1
  have hm : HasDerivAt (fun z : ℂ => 1 - z / (2 * (Real.pi : ℂ)))
      (-(1 / (2 * (Real.pi : ℂ)))) 0 :=
    (hid.div_const (2 * (Real.pi : ℂ))).const_sub 1
  have hh : HasDerivAt (continuedHzeta (1 - s))
      (-(1 - s) * riemannZeta ((1 - s) + 1)) 1 := continuedHzeta_hasDerivAt_one hw
  have hhp : HasDerivAt
      (fun z : ℂ => continuedHzeta (1 - s) (1 + z / (2 * (Real.pi : ℂ))))
      ((-(1 - s) * riemannZeta ((1 - s) + 1)) * (1 / (2 * (Real.pi : ℂ)))) 0 :=
    hh.comp_of_eq 0 hp (by simp)
  have hhm : HasDerivAt
      (fun z : ℂ => continuedHzeta (1 - s) (1 - z / (2 * (Real.pi : ℂ))))
      ((-(1 - s) * riemannZeta ((1 - s) + 1)) * -(1 / (2 * (Real.pi : ℂ)))) 0 :=
    hh.comp_of_eq 0 hm (by simp)
  have hd : HasDerivAt (photonicRegularPhase s)
      ((2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Gamma (1 - s) *
        (exp ((Real.pi : ℂ) * I * (1 - s) / 2) *
          ((-(1 - s) * riemannZeta ((1 - s) + 1)) * (1 / (2 * (Real.pi : ℂ)))) +
        exp (-(Real.pi : ℂ) * I * (1 - s) / 2) *
          ((-(1 - s) * riemannZeta ((1 - s) + 1)) * -(1 / (2 * (Real.pi : ℂ)))))) 0 :=
    ((hhp.const_mul (exp ((Real.pi : ℂ) * I * (1 - s) / 2))).add
    (hhm.const_mul (exp (-(Real.pi : ℂ) * I * (1 - s) / 2)))).const_mul
      ((2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Gamma (1 - s))
  rw [← jonquiereTangent_eq h0 h1]
  convert hd using 1
  unfold jonquiereTangent
  ring

/-- The first jet in the logarithmic multiplier coordinate `X = iθ`. -/
noncomputable def photonicProjectedReturn (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  photonicUpper (photonicRegularPhase s 0) (-I * deriv (photonicRegularPhase s) 0)

/-- The regular first jet is exactly the previously certified parabolic response. -/
theorem photonicProjectedReturn_eq :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → photonicProjectedReturn s = photonicReturn s := by
  intro s h0 h1
  rw [photonicProjectedReturn, photonicRegularPhase_zero s h0 h1,
    (photonicRegularPhase_hasDerivAt s h0 h1).deriv, photonicReturn]
  congr 1
  rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

/-- The continued phase response on the cover `θ = exp w`. -/
noncomputable def photonicReturnLift (s w : ℂ) : ℂ :=
  jonquiereLead s * exp ((s - 1) * w) + photonicRegularPhase s (exp w)

/-- The actual singular-phase character, in the corpus's Hurwitz convention. -/
noncomputable def photonicReturnCharacter (s : ℂ) : ℂ :=
  HurwitzOrbit.monoScalar (1 - s)

/-- The lift is holomorphic over a sufficiently small punctured phase disk. -/
theorem photonicReturnLift_analytic_near_puncture :
    ∀ s : ℂ, s.re < 1 → ∃ r : ℝ, 0 < r ∧
      ∀ w : ℂ, ‖exp w‖ < r → AnalyticAt ℂ (photonicReturnLift s) w := by
  intro s h1
  obtain ⟨r, hr, han⟩ := Metric.eventually_nhds_iff.mp
    (photonicRegularPhase_analytic s h1).eventually_analyticAt
  refine ⟨r, hr, ?_⟩
  intro w hw
  have hh : AnalyticAt ℂ (photonicRegularPhase s) (exp w) :=
    han (by simpa only [dist_zero_right] using hw)
  have he : AnalyticAt ℂ (fun z : ℂ => exp ((s - 1) * z)) w :=
    analyticAt_cexp.comp (analyticAt_const.mul analyticAt_id)
  exact (analyticAt_const.mul he).add (hh.comp analyticAt_cexp)

/-- This lift continues the actual periodic return boundary. -/
theorem photonicReturnLift_boundary :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → ∀ θ : ℝ, 0 < θ → θ ≤ Real.pi →
      photonicReturnLift s (Complex.log (θ : ℂ)) =
        expZeta ((θ / (2 * Real.pi) : ℝ) : UnitAddCircle) s := by
  intro s h0 h1 θ hθ0 hθ1
  have hθ : (θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hθ0.ne'
  rw [photonicReturnLift, Complex.exp_log hθ, photonicRegularPhase_boundary s h0 h1,
    expZeta_eq_jonquiere h0 h1 hθ0 hθ1, Complex.cpow_def_of_ne_zero hθ,
    mul_comm (s - 1) (Complex.log (θ : ℂ))]
  ring

/-- One positive phase loop fixes the regular component and scales the singular one. -/
theorem photonicReturnLift_deck (s w : ℂ) :
    photonicReturnLift s (w + 2 * (Real.pi : ℂ) * I) =
      photonicReturnCharacter s * photonicReturnLift s w +
        (1 - photonicReturnCharacter s) * photonicRegularPhase s (exp w) := by
  have he : exp (w + 2 * (Real.pi : ℂ) * I) = exp w := by
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hs : exp ((s - 1) * (2 * (Real.pi : ℂ) * I)) = photonicReturnCharacter s := by
    unfold photonicReturnCharacter HurwitzOrbit.monoScalar
    congr 1
    ring
  simp only [photonicReturnLift, he, mul_add, Complex.exp_add, hs]
  ring

/-- The two continuation characters remain distinct throughout the open strip. -/
theorem photonicReturnCharacter_ne_one :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → photonicReturnCharacter s ≠ 1 := by
  intro s h0 h1 he
  obtain ⟨m, hm⟩ := (HurwitzOrbit.monoScalar_eq_one_iff (1 - s)).mp he
  have hre := congrArg Complex.re hm
  simp only [Complex.sub_re, Complex.one_re, Complex.intCast_re] at hre
  have hm0 : (0 : ℤ) < m := by exact_mod_cast (show (0 : ℝ) < m by linarith)
  have hm1 : m < (1 : ℤ) := by exact_mod_cast (show (m : ℝ) < 1 by linarith)
  exact (Int.not_lt.mpr (Int.add_one_le_iff.mpr hm0)) hm1

/-- The singular component is present: the return lift is not deck-invariant. -/
theorem photonicReturnLift_deck_ne_self :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → ∀ w : ℂ,
      photonicReturnLift s (w + 2 * (Real.pi : ℂ) * I) ≠ photonicReturnLift s w := by
  intro s h0 h1 w he
  have hc : photonicReturnCharacter s - 1 ≠ 0 :=
    sub_ne_zero.mpr (photonicReturnCharacter_ne_one s h0 h1)
  have hl : jonquiereLead s ≠ 0 :=
    mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)) (Complex.exp_ne_zero _)
  have hz : (photonicReturnCharacter s - 1) * jonquiereLead s * exp ((s - 1) * w) = 0 := by
    rw [photonicReturnLift_deck, photonicReturnLift] at he
    linear_combination he
  exact (mul_ne_zero (mul_ne_zero hc hl) (Complex.exp_ne_zero _)) hz

/-- Canonical extraction uses continuation and its character, with no chosen subtraction term. -/
theorem photonicReturnLift_invariant_projection :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → ∀ w : ℂ,
      (photonicReturnLift s (w + 2 * (Real.pi : ℂ) * I) -
        photonicReturnCharacter s * photonicReturnLift s w) /
        (1 - photonicReturnCharacter s) = photonicRegularPhase s (exp w) := by
  intro s h0 h1 w
  have hne : 1 - photonicReturnCharacter s ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (photonicReturnCharacter_ne_one s h0 h1))
  rw [photonicReturnLift_deck, add_sub_cancel_left, mul_div_cancel_left₀ _ hne]

end RHTower

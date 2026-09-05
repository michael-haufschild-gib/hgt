import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaClosureWalls
import Mathlib.Tactic

/-!
# Strict monotonicity and uniqueness of the closure root

Pointwise order of the complete-integral radicands makes `K` strictly increasing and `E` strictly
decreasing on the entire regular real domain `m<1`.  Consequently `E/K` is strictly decreasing in
the classical chamber, so `2E=K` has at most one solution.  Appendix A's modulus equivalence then
proves uniqueness of the paper's corresponding negative root of `Q`, without numerical evaluation.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Two strictly ordered parameters in the regular real elliptic domain. -/
structure StrictSubcriticalPair where
  lower : SubcriticalModulus
  upper : SubcriticalModulus
  lt_order : (lower : ℝ) < (upper : ℝ)

theorem completeEIntegrand_antitone (P : StrictSubcriticalPair) (θ : ℝ) :
    completeEIntegrand P.upper θ ≤ completeEIntegrand P.lower θ := by
  rw [completeEIntegrand, completeEIntegrand]
  apply Real.sqrt_le_sqrt
  have hs : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right P.lt_order.le hs
  linarith

theorem completeKIntegrand_monotone (P : StrictSubcriticalPair) (θ : ℝ) :
    completeKIntegrand P.lower θ ≤ completeKIntegrand P.upper θ := by
  have hlow := subcriticalRadicand_pos P.lower θ
  have hupp := subcriticalRadicand_pos P.upper θ
  have hs : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right P.lt_order.le hs
  have hsqrt : Real.sqrt (1 - (P.upper : ℝ) * Real.sin θ ^ 2) ≤
      Real.sqrt (1 - (P.lower : ℝ) * Real.sin θ ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  rw [completeKIntegrand, completeKIntegrand, ← one_div, ← one_div]
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hupp) hsqrt

theorem completeEIntegrand_strict_at_halfPi (P : StrictSubcriticalPair) :
    completeEIntegrand P.upper (Real.pi / 2) <
      completeEIntegrand P.lower (Real.pi / 2) := by
  rw [completeEIntegrand, completeEIntegrand]
  apply Real.sqrt_lt_sqrt
  · exact (subcriticalRadicand_pos P.upper (Real.pi / 2)).le
  · simpa using sub_lt_sub_left P.lt_order 1

theorem completeKIntegrand_strict_at_halfPi (P : StrictSubcriticalPair) :
    completeKIntegrand P.lower (Real.pi / 2) <
      completeKIntegrand P.upper (Real.pi / 2) := by
  have hlow := subcriticalRadicand_pos P.lower (Real.pi / 2)
  have hupp := subcriticalRadicand_pos P.upper (Real.pi / 2)
  have hsqrt : Real.sqrt (1 - (P.upper : ℝ) * Real.sin (Real.pi / 2) ^ 2) <
      Real.sqrt (1 - (P.lower : ℝ) * Real.sin (Real.pi / 2) ^ 2) := by
    apply Real.sqrt_lt_sqrt hupp.le
    simpa using sub_lt_sub_left P.lt_order 1
  rw [completeKIntegrand, completeKIntegrand]
  exact (inv_lt_inv₀ (Real.sqrt_pos.mpr hlow) (Real.sqrt_pos.mpr hupp)).2 hsqrt

/-- `E` is strictly decreasing on every ordered pair below `m=1`. -/
theorem completeEllipticE_strictAntitone (P : StrictSubcriticalPair) :
    completeEllipticE P.upper < completeEllipticE P.lower := by
  have hl := continuous_completeEIntegrand P.upper
  have hu := continuous_completeEIntegrand P.lower
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (show (0 : ℝ) < Real.pi / 2 by positivity) hl.continuousOn hu.continuousOn
    (fun θ _ => completeEIntegrand_antitone P θ)
    ⟨Real.pi / 2, ⟨by positivity, le_rfl⟩, completeEIntegrand_strict_at_halfPi P⟩
  simpa [completeEllipticE, completeEIntegrand] using h

/-- `K` is strictly increasing on every ordered pair below `m=1`. -/
theorem completeEllipticK_strictMonotone (P : StrictSubcriticalPair) :
    completeEllipticK P.lower < completeEllipticK P.upper := by
  have hl := continuous_completeKIntegrand P.lower
  have hu := continuous_completeKIntegrand P.upper
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (show (0 : ℝ) < Real.pi / 2 by positivity) hl.continuousOn hu.continuousOn
    (fun θ _ => completeKIntegrand_monotone P θ)
    ⟨Real.pi / 2, ⟨by positivity, le_rfl⟩, completeKIntegrand_strict_at_halfPi P⟩
  simpa [completeEllipticK, completeKIntegrand] using h

/-- Strictly ordered parameters inside the classical chamber. -/
structure StrictClassicalPair where
  lower : ClassicalModulus
  upper : ClassicalModulus
  lt_order : (lower : ℝ) < (upper : ℝ)

noncomputable def StrictClassicalPair.toSubcritical (P : StrictClassicalPair) :
    StrictSubcriticalPair where
  lower := classicalAsSubcritical P.lower
  upper := classicalAsSubcritical P.upper
  lt_order := P.lt_order

/-- The quotient `E/K` strictly decreases through the classical chamber. -/
theorem completeEllipticE_div_K_strictAntitone (P : StrictClassicalPair) :
    completeEllipticE P.upper / completeEllipticK P.upper <
      completeEllipticE P.lower / completeEllipticK P.lower := by
  have hE : completeEllipticE P.upper < completeEllipticE P.lower := by
    simpa [StrictClassicalPair.toSubcritical, classicalAsSubcritical] using
      completeEllipticE_strictAntitone P.toSubcritical
  have hK : completeEllipticK P.lower < completeEllipticK P.upper := by
    simpa [StrictClassicalPair.toSubcritical, classicalAsSubcritical] using
      completeEllipticK_strictMonotone P.toSubcritical
  have hKl : 0 < completeEllipticK P.lower := completeEllipticK_classical_pos P.lower
  have hKu : 0 < completeEllipticK P.upper := completeEllipticK_classical_pos P.upper
  have hEl : 0 < completeEllipticE P.lower := completeEllipticE_classical_pos P.lower
  calc
    completeEllipticE P.upper / completeEllipticK P.upper <
        completeEllipticE P.lower / completeEllipticK P.upper :=
      div_lt_div_of_pos_right hE hKu
    _ < completeEllipticE P.lower / completeEllipticK P.lower :=
      (div_lt_div_iff₀ hKu hKl).2 (mul_lt_mul_of_pos_left hK hEl)

theorem classicalClosureCore_strictAntitone (P : StrictClassicalPair) :
    classicalClosureCore P.upper < classicalClosureCore P.lower := by
  have h := completeEllipticE_div_K_strictAntitone P
  rw [classicalClosureCore, classicalClosureCore]
  have hu : 2 * completeEllipticE P.upper / completeEllipticK P.upper =
      2 * (completeEllipticE P.upper / completeEllipticK P.upper) := by ring
  have hl : 2 * completeEllipticE P.lower / completeEllipticK P.lower =
      2 * (completeEllipticE P.lower / completeEllipticK P.lower) := by ring
  rw [hu, hl]
  linarith

/-- Classical solutions of `2E=K`, represented without theorem-side hypotheses. -/
abbrev ClassicalClosureRoot :=
  {m : ClassicalModulus // classicalClosureCore m = 0}

/-- The paper's classical closure root is unique if it exists. -/
theorem classicalClosureRoot_unique (a b : ClassicalClosureRoot) : a = b := by
  apply Subtype.ext
  rcases lt_trichotomy (a.val : ℝ) (b.val : ℝ) with hab | hab | hba
  · let P : StrictClassicalPair := ⟨a.val, b.val, hab⟩
    have h := classicalClosureCore_strictAntitone P
    change classicalClosureCore b.val < classicalClosureCore a.val at h
    rw [a.property, b.property] at h
    exact False.elim (lt_irrefl 0 h)
  · exact Subtype.ext hab
  · let P : StrictClassicalPair := ⟨b.val, a.val, hba⟩
    have h := classicalClosureCore_strictAntitone P
    change classicalClosureCore a.val < classicalClosureCore b.val at h
    rw [a.property, b.property] at h
    exact False.elim (lt_irrefl 0 h)

instance : Subsingleton ClassicalClosureRoot :=
  ⟨classicalClosureRoot_unique⟩

/-- Negative roots of the paper's closed-knot scale. -/
abbrev NegativeClosureRoot := {m : NegativeModulus // closureQ m = 0}

/-- The corresponding negative root of `Q` is unique if it exists. -/
theorem negativeClosureRoot_unique (a b : NegativeClosureRoot) : a = b := by
  have haIntegral := (closureQ_negative_eq_zero_iff a.val).mp a.property
  have hbIntegral := (closureQ_negative_eq_zero_iff b.val).mp b.property
  let ca : ClassicalClosureRoot :=
    ⟨extendedToClassical a.val,
      (classicalClosureCore_eq_zero_iff (extendedToClassical a.val)).mpr haIntegral⟩
  let cb : ClassicalClosureRoot :=
    ⟨extendedToClassical b.val,
      (classicalClosureCore_eq_zero_iff (extendedToClassical b.val)).mpr hbIntegral⟩
  have hc : ca = cb := Subsingleton.elim ca cb
  have hn : extendedToClassical a.val = extendedToClassical b.val := by
    exact congrArg Subtype.val hc
  apply Subtype.ext
  exact modulusEquiv.injective hn

instance : Subsingleton NegativeClosureRoot :=
  ⟨negativeClosureRoot_unique⟩

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

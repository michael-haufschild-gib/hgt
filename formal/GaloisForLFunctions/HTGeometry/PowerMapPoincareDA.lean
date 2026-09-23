import GaloisForLFunctions.HTGeometry.RittDichotomy

/-!
# The power map is on the differentially algebraic branch of the dichotomy

Conjugating `x ↦ x^p` to the origin gives `g w = (1 + w)^p - 1`, whose Poincaré germ is
`Φ z = exp z - 1`.  It satisfies the order-one Ritt relation with `A t = 1 + t`, so the clock of the
power map is differentially algebraic, and the corresponding multiplicative cocycle
`g'(t) A(t) = p · A(g t)` holds identically.

This is the positive branch of the rational RG generation dichotomy: the noiseless tree map, being
Möbius-conjugate to `x ↦ x^p`, has a differentially algebraic exact clock.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The conjugate of `x ↦ x^p` at the fixed point `1`, translated to the origin. -/
def powerMapGerm (p : ℕ) : ℂ → ℂ := fun w => (1 + w) ^ p - 1

/-- The Poincaré germ of the power map. -/
def powerMapPoincare : ℂ → ℂ := fun z => Complex.exp z - 1

@[simp] theorem powerMapPoincare_zero : powerMapPoincare 0 = 0 := by
  simp [powerMapPoincare]

theorem deriv_powerMapPoincare : deriv powerMapPoincare = Complex.exp := by
  funext z
  have h : HasDerivAt powerMapPoincare (Complex.exp z) z := by
    show HasDerivAt (fun w : ℂ => Complex.exp w - 1) (Complex.exp z) z
    simpa using (Complex.hasDerivAt_exp z).sub_const 1
  exact h.deriv

theorem analyticOnNhd_powerMapPoincare (U : Set ℂ) :
    AnalyticOnNhd ℂ powerMapPoincare U :=
  fun z _ => analyticAt_cexp.sub analyticAt_const

/-- **The Poincaré equation for the power map.**  `Φ (p z) = g (Φ z)`. -/
theorem powerMapPoincare_functionalEquation (p : ℕ) (z : ℂ) :
    powerMapPoincare ((p : ℂ) * z) = powerMapGerm p (powerMapPoincare z) := by
  simp only [powerMapPoincare, powerMapGerm]
  rw [show (1 : ℂ) + (Complex.exp z - 1) = Complex.exp z from by ring, ← Complex.exp_nat_mul]

/-- **The Ritt relation for the power map.**  `Φ' = A(Φ)` with `A t = 1 + t`. -/
theorem powerMapPoincare_rittForm (z : ℂ) :
    Polynomial.eval (powerMapPoincare z) (1 : Polynomial ℂ) * deriv powerMapPoincare z ^ (1 : ℕ)
      = 1 * z ^ (0 : ℕ) * Polynomial.eval (powerMapPoincare z) (Polynomial.X + 1) := by
  rw [deriv_powerMapPoincare]
  simp [powerMapPoincare]

/-- **The power map lies on the differentially algebraic branch.**  Its Poincaré germ satisfies an
algebraic differential equation on every set. -/
theorem differentiallyAlgebraicOn_powerMapPoincare (U : Set ℂ) :
    DifferentiallyAlgebraicOn powerMapPoincare U := by
  refine differentiallyAlgebraicOn_of_rittForm (r := 1) (j := 0) (a := 1) one_pos
    (P := Polynomial.X + 1) (Q := 1) one_ne_zero (fun z _ => powerMapPoincare_rittForm z)

/-- **The Ritt cocycle for the power map** holds identically: `g'(t) A(t) = p · A(g t)` with
`A t = 1 + t`. -/
theorem powerMapGerm_cocycle (p : ℕ) (t : ℂ) :
    deriv (powerMapGerm p) t ^ (1 : ℕ) * (1 + t) = (p : ℂ) ^ (1 + 0) * (1 + powerMapGerm p t) := by
  have hd : deriv (powerMapGerm p) t = (p : ℂ) * (1 + t) ^ (p - 1) := by
    have h : HasDerivAt (powerMapGerm p) ((p : ℂ) * (1 + t) ^ (p - 1) * 1) t := by
      show HasDerivAt (fun w : ℂ => (1 + w) ^ p - 1) _ t
      have hbase : HasDerivAt (fun w : ℂ => 1 + w) 1 t := by
        simpa using (hasDerivAt_id t).const_add 1
      exact (hbase.pow p).sub_const 1
    simpa using h.deriv
  rw [hd, pow_one, powerMapGerm]
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp
  · have hsucc : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp
    have hkey : (1 + t) ^ (p - 1) * (1 + t) = (1 + t) ^ p := by
      rw [← pow_succ, hsucc]
    calc (p : ℂ) * (1 + t) ^ (p - 1) * (1 + t)
        = (p : ℂ) * ((1 + t) ^ (p - 1) * (1 + t)) := by ring
      _ = (p : ℂ) * (1 + t) ^ p := by rw [hkey]
      _ = (p : ℂ) ^ (1 + 0) * (1 + ((1 + t) ^ p - 1)) := by ring

end

end GaloisForLFunctions.HTGeometry

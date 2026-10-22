import GaloisForLFunctions.RHTower.Suzuki.SuzukiSourceAlignmentSlack

/-!
# The maximal relative edge is the even parity floor

The relative Rayleigh ratio of the two parity forms is a decreasing Möbius function of the
normalized Hankel quotient: with `c = C(f)` and `h = H(f)`,

`q_o(f)/q_e(f) = (c - h)/(c + h)`,

and the substitution `t = h/c` turns it into `(1-t)/(1+t)`.  Hence its supremum over all test
vectors is `(1-m)/(1+m)` at the bottom `m` of the normalized Hankel quotient, and a *single* test
vector already produces a lower bound for the edge.

The natural test vector is an even ground mode.  At the even floor its own even energy vanishes,
so the shifted ratio is `1 + η_e/(α_e - λ)` where `η_e` is its odd energy — and the Möbius inverse
turns that into the edge bound `r ≥ η_e/(2(α_e - λ) + η_e)`.  A source-invisible even ground mode
therefore drives the abstract edge towards `-1` without admitting the exponential source, which is
why a uniform edge ceiling is only a sufficient no-go.
-/

noncomputable section

namespace RHTower

/-! ## The Möbius form of the relative ratio -/

/-- **`(255)`, upper bound: the relative ratio never exceeds the Möbius value at the bottom of the
normalized quotient.** -/
theorem relativeRatio_le {c h m : ℝ} (hm1 : -1 < m) (hmh : m * c ≤ h) (hpos : 0 < c + h) :
    (c - h) / (c + h) ≤ (1 - m) / (1 + m) := by
  have h1m : (0 : ℝ) < 1 + m := by linarith
  rw [div_le_div_iff₀ hpos h1m]
  nlinarith

/-- **`(255)`, approximation: a near-minimizing test vector realises the Möbius value up to the
same shift.** -/
theorem le_relativeRatio {c h t : ℝ} (ht1 : -1 < t) (hth : h ≤ t * c) (hpos : 0 < c + h) :
    (1 - t) / (1 + t) ≤ (c - h) / (c + h) := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  rw [div_le_div_iff₀ h1t hpos]
  nlinarith

/-! ## The Möbius inverse -/

/-- The Cayley map is strictly increasing, so a ratio lower bound is an edge lower bound. -/
theorem edge_ge_of_ratio {r X : ℝ} (hr : |r| < 1) (hX : 1 ≤ X)
    (hratio : X ≤ (1 + r) / (1 - r)) :
    (X - 1) / (X + 1) ≤ r := by
  rcases abs_lt.mp hr with ⟨hr1, hr2⟩
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hX1 : (0 : ℝ) < X + 1 := by linarith
  rw [le_div_iff₀ h1r] at hratio
  rw [div_le_iff₀ hX1]
  nlinarith

/-- **`(256)`: an even ground mode with positive odd energy forces a negative edge.**  Testing the
relative ratio on the even ground mode gives `1 + η/(α_e - λ)`, and the Möbius inverse converts it
into the explicit edge bound. -/
theorem edge_ge_of_ground_test {r η d : ℝ} (hr : |r| < 1) (hη : 0 ≤ η) (hd : 0 < d)
    (hratio : 1 + η / d ≤ (1 + r) / (1 - r)) :
    η / (2 * d + η) ≤ r := by
  have hX : (1 : ℝ) ≤ 1 + η / d := by
    have : 0 ≤ η / d := div_nonneg hη hd.le
    linarith
  have hmain := edge_ge_of_ratio hr hX hratio
  have hval : ((1 + η / d) - 1) / ((1 + η / d) + 1) = η / (2 * d + η) := by
    have hden : (0 : ℝ) < 2 * d + η := by linarith
    field_simp
    ring
  rwa [hval] at hmain

/-- The shifted ground test value: at the even floor the even energy is the shift gap and the odd
energy adds the ground defect. -/
theorem ground_test_ratio {αe lam η : ℝ} (hlam : lam < αe) :
    (η + (αe - lam)) / (αe - lam) = 1 + η / (αe - lam) := by
  have hd : (0 : ℝ) < αe - lam := by linarith
  field_simp
  ring

/-- A positive ground defect gives a strictly positive edge, uniformly on every shift range
bounded away from the floor. -/
theorem edge_pos_of_ground_defect {r η d : ℝ} (hr : |r| < 1) (hη : 0 < η) (hd : 0 < d)
    (hratio : 1 + η / d ≤ (1 + r) / (1 - r)) :
    0 < r :=
  lt_of_lt_of_le (by positivity) (edge_ge_of_ground_test hr hη.le hd hratio)

end RHTower

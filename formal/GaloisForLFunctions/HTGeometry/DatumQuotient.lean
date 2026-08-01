import GaloisForLFunctions.HTGeometry.GammaFieldShapeConvergence

/-!
# The datum of a quotient

Two data `s^p·X → c` and `s^q·Y → d ≠ 0` combine to a residue for the quotient: dividing by the shape
`s^q/s^p` turns `X/Y` into `(s^p X)/(s^q Y)`, whose limit is `c/d`.

Since numerator and denominator degrees enter the shape separately, no negative exponent is needed:
the quotient of two field elements is a residue against a `polyJetShape`.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- **The datum of a quotient.** -/
theorem tendsto_div_polyJetShape_of_data (_hσ : 0 < σ) {X Y : ℝ → ℂ} {p q : ℕ} {c d : ℂ} (hd : d ≠ 0)
    (hX : Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p * X t) atTop (nhds c))
    (hY : Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ q * Y t) atTop (nhds d)) :
    Tendsto (fun t : ℝ => (X t / Y t) / polyJetShape σ 0 q p t) atTop (nhds (c / d)) := by
  have hlim : Tendsto (fun t : ℝ => (((σ : ℂ) + (t : ℂ) * Complex.I) ^ p * X t)
      / (((σ : ℂ) + (t : ℂ) * Complex.I) ^ q * Y t)) atTop (nhds (c / d)) := hX.div hY hd
  refine hlim.congr' ?_
  filter_upwards [eventually_vertical_ne_zero σ, hY.eventually_ne hd] with t hs hne
  have hY0 : Y t ≠ 0 := by
    intro h
    rw [h, mul_zero] at hne
    exact hne rfl
  rw [polyJetShape, pow_zero, one_mul]
  field_simp

end GaloisForLFunctions

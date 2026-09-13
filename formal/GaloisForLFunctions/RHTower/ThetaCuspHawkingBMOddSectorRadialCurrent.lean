import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedRadialActionCurrent

/-!
# The odd-sector radial current between the `−` mode and the `++` scalar–vector response

The `++` scalar–vector response of route HB is the mixed-block stream metric
`T·A_a, R·A_a` with radial factors `T = (r²−1)·∂_r(e·u)`, `R = 2s·e·u/(r²−1)` built from the
doubled-rate envelope `e` (`∂_r e = 2s·e/(r(r²−1))`) and the profile `u = 1` (resolvent covector
stream) or `u = 1/r²` (square covector stream); the `−` mode's vector part is the mixed block
`−σ·m/r·V_a, −σ·m/(r²−1)·V_a` with envelope `m` at rate `σ = −3−s` (`∂_r m = σ·m/(r(r²−1))`).
On these explicit jets the radial Einstein symplectic density of the mixed sector
(`mixed_radial_action_current`), `Σ_a (T_a (∂₀V_a − ∂₁U_a) − U_a (∂₀R_a − ∂₁T_a))`, is the
envelope product `e·m`, the angular pairing `Σ_a A_a V_a`, and an explicit rational factor:
`−6s(s+1)(s+3)/r³` for the resolvent stream and `2(s+3)((s+3)r² − (s+1)(3s+5))/r⁵` for the square
stream (`oddSector_radialDensity_resolvent`, `oddSector_radialDensity_square`). Both are regular at
the horizon and decay like `r⁻³`, so the odd-sector `++−` flux `r²·(density)` has neither a
divergence nor a finite part at the AdS boundary; the only boundary divergence of the whole `++`
response is the scalar–scalar linear one.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace RHTower.D4BMOddSectorCurrent
noncomputable section

/-- Radial symplectic density of the mixed sector on explicit jets: first jet `(T, R)` with radial
derivatives `(T₁, R₁)` and time rate `w`, second jet `(U, V)` with radial derivatives `(U₁, V₁)`
and time rate `v`, angular pairing `A` (the sum over the two covector components is carried by the
product `A = Σ_a A_a V_a`). -/
def radialDensity (w v T T₁ R R₁ U U₁ V V₁ : ℂ) : ℂ :=
  T * (v * V - U₁) - U * (w * R - T₁)

/-- Resolvent-covector stream: profile `u = 1`. -/
theorem oddSector_radialDensity_resolvent (s r e m : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    let e₁ := 2 * s * e / (r * (r ^ 2 - 1))
    let e₂ := 2 * s * e₁ / (r * (r ^ 2 - 1)) - 2 * s * e * (3 * r ^ 2 - 1) / (r * (r ^ 2 - 1)) ^ 2
    let m₁ := (-3 - s) * m / (r * (r ^ 2 - 1))
    let T := (r ^ 2 - 1) * e₁
    let T₁ := 2 * r * e₁ + (r ^ 2 - 1) * e₂
    let R := 2 * s * e / (r ^ 2 - 1)
    let R₁ := 2 * s * e₁ / (r ^ 2 - 1) - 2 * s * e * (2 * r) / (r ^ 2 - 1) ^ 2
    let U := -(-3 - s) * m / r
    let U₁ := -(-3 - s) * (m₁ * r - m) / r ^ 2
    let V := -(-3 - s) * m / (r ^ 2 - 1)
    let V₁ := -(-3 - s) * (m₁ * (r ^ 2 - 1) - m * (2 * r)) / (r ^ 2 - 1) ^ 2
    radialDensity (2 * s) (-3 - s) T T₁ R R₁ U U₁ V V₁ =
      (-6 * s * (s + 1) * (s + 3) / r ^ 3) * (e * m) := by
  intro e₁ e₂ m₁ T T₁ R R₁ U U₁ V V₁
  unfold radialDensity
  simp only [e₁, e₂, m₁, T, T₁, R, R₁, U, U₁, V, V₁]
  field_simp
  ring

/-- Square-covector stream: profile `u = 1/r²`. -/
theorem oddSector_radialDensity_square (s r e m : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    let e₁ := 2 * s * e / (r * (r ^ 2 - 1))
    let e₂ := 2 * s * e₁ / (r * (r ^ 2 - 1)) - 2 * s * e * (3 * r ^ 2 - 1) / (r * (r ^ 2 - 1)) ^ 2
    let m₁ := (-3 - s) * m / (r * (r ^ 2 - 1))
    let g := e / r ^ 2
    let g₁ := e₁ / r ^ 2 - 2 * e / r ^ 3
    let g₂ := e₂ / r ^ 2 - 4 * e₁ / r ^ 3 + 6 * e / r ^ 4
    let T := (r ^ 2 - 1) * g₁
    let T₁ := 2 * r * g₁ + (r ^ 2 - 1) * g₂
    let R := 2 * s * g / (r ^ 2 - 1)
    let R₁ := 2 * s * g₁ / (r ^ 2 - 1) - 2 * s * g * (2 * r) / (r ^ 2 - 1) ^ 2
    let U := -(-3 - s) * m / r
    let U₁ := -(-3 - s) * (m₁ * r - m) / r ^ 2
    let V := -(-3 - s) * m / (r ^ 2 - 1)
    let V₁ := -(-3 - s) * (m₁ * (r ^ 2 - 1) - m * (2 * r)) / (r ^ 2 - 1) ^ 2
    radialDensity (2 * s) (-3 - s) T T₁ R R₁ U U₁ V V₁ =
      (2 * (s + 3) * ((s + 3) * r ^ 2 - (s + 1) * (3 * s + 5)) / r ^ 5) * (e * m) := by
  intro e₁ e₂ m₁ g g₁ g₂ T T₁ R R₁ U U₁ V V₁
  unfold radialDensity
  simp only [e₁, e₂, m₁, g, g₁, g₂, T, T₁, R, R₁, U, U₁, V, V₁]
  field_simp
  ring

/-- The corpus mixed radial density on a pair of mixed jets whose entries are a radial factor times
a covector: it is the covector pairing times the scalar density above. -/
theorem mixedJet_radialDensity (p : D4BMBackground.ExteriorPoint) (w v T T₁ R R₁ U U₁ V V₁ : ℂ)
    (A B : Fin 2 → ℂ) :
    (p.val 1 : ℂ) ^ 2 / (p.val 3 : ℂ) ^ 2 * D4BMMixedActionCurrent.actionSymplectic
      (D4BMBackground.jet (p.val 1) (p.val 3))
      (D4BMMixedActionCurrent.mixedJet (fun a => T * A a) (fun a => R * A a)
        (fun k a => if k = 0 then w * T * A a else if k = 1 then T₁ * A a else 0)
        (fun k a => if k = 0 then w * R * A a else if k = 1 then R₁ * A a else 0))
      (D4BMMixedActionCurrent.mixedJet (fun a => U * B a) (fun a => V * B a)
        (fun k a => if k = 0 then v * U * B a else if k = 1 then U₁ * B a else 0)
        (fun k a => if k = 0 then v * V * B a else if k = 1 then V₁ * B a else 0)) 1 =
      (∑ a : Fin 2, A a * B a) * radialDensity w v T T₁ R R₁ U U₁ V V₁ := by
  rw [D4BMMixedActionCurrent.mixed_radial_action_current]
  simp only [Fin.sum_univ_two, Fin.isValue, if_true, if_false, one_ne_zero, zero_ne_one]
  unfold radialDensity
  ring

end
end RHTower.D4BMOddSectorCurrent

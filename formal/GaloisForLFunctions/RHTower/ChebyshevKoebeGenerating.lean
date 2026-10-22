import GaloisForLFunctions.RHTower.AnharmonicChebyshevOrientationCasimir

/-!
# Koebe resolvent form of the Chebyshev generating kernel

Let `K(v) = 27v / (1 - v)²` be the endpoint-scaled Koebe map. For a node `θ ≠ 0`, the Chebyshev
generating denominator `1 - 2v(1 - 2θ) + v²` is related to the Koebe resolvent at the point
`-(27/4)/θ` by the cross identity
`(1 - 2v(1 - 2θ) + v²) K(v) = 4vθ (K(v) + (27/4)/θ)`. This module derives the resolvent
formula, rewrites the centered Chebyshev kernel `θ(1 - v²)/(1 - 2v(1 - 2θ) + v²)` as
`(1 - v²)/(4v)` times the Koebe resolvent, and shows that a pole `K(v) = -(27/4)/θ` forces the
Joukowski relation `1 - 2θ = (v + v⁻¹)/2`.

## Main results

- `chebyshevKoebe_resolvent_cross`: the cross identity above, for `v ≠ 1`, `θ ≠ 0`.
- `chebyshevKoebe_resolvent`: `K(v)/(K(v) + (27/4)/θ) = 4vθ/(1 - 2v(1 - 2θ) + v²)` when the
  denominator is nonzero.
- `chebyshevKoebe_centeredNode`: the centered Chebyshev kernel equals `(1 - v²)/(4v)` times the
  Koebe resolvent.
- `chebyshevKoebe_joukowski`: `K(v) = -(27/4)/θ` implies `1 - 2θ = (v + v⁻¹)/2`.

## Hypotheses

Unconditional algebraic identities; the premises `v ≠ 0`, `v ≠ 1`, `θ ≠ 0` and nonvanishing of
the Chebyshev denominator only exclude division by zero.
-/

namespace RHTower

/-- Cross identity for `v ≠ 1`, `θ ≠ 0`: `(1 - 2v(1 - 2θ) + v²) K(v) = 4vθ (K(v) + (27/4)/θ)`,
where `K(v) = 27v/(1 - v)²` is the Koebe map. -/
theorem chebyshevKoebe_resolvent_cross
    {v θ : ℂ} (hv : v ≠ 1) (hθ : θ ≠ 0) :
    (1 - 2 * v * (1 - 2 * θ) + v ^ (2 : ℕ)) *
        chebyshevTraceKoebeMap v =
      4 * v * θ * (chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / θ)) := by
  simp only [chebyshevTraceKoebeMap]
  field_simp [hv, hθ]
  ring

/-- Koebe resolvent formula: if `v ≠ 1`, `θ ≠ 0` and `1 - 2v(1 - 2θ) + v² ≠ 0`, then
`K(v)/(K(v) + (27/4)/θ) = 4vθ/(1 - 2v(1 - 2θ) + v²)`. -/
theorem chebyshevKoebe_resolvent
    {v θ : ℂ} (hv : v ≠ 1) (hθ : θ ≠ 0)
    (hden : 1 - 2 * v * (1 - 2 * θ) + v ^ (2 : ℕ) ≠ 0) :
    chebyshevTraceKoebeMap v /
        (chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / θ)) =
      4 * v * θ / (1 - 2 * v * (1 - 2 * θ) + v ^ (2 : ℕ)) := by
  have hcross := chebyshevKoebe_resolvent_cross hv hθ
  have hx : (-(27 / 4 : ℂ) / θ) ≠ 0 :=
    div_ne_zero (by norm_num) hθ
  have hdiff : chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / θ) ≠ 0 := by
    intro h
    have hX : chebyshevTraceKoebeMap v = 0 := by
      rw [h, mul_zero] at hcross
      exact (mul_eq_zero.mp hcross).resolve_left hden
    apply hx
    have heq := sub_eq_zero.mp h
    exact heq.symm.trans hX
  apply (div_eq_div_iff hdiff hden).2
  calc
    chebyshevTraceKoebeMap v *
        (1 - 2 * v * (1 - 2 * θ) + v ^ (2 : ℕ)) =
      (1 - 2 * v * (1 - 2 * θ) + v ^ (2 : ℕ)) *
        chebyshevTraceKoebeMap v := by ring
    _ = 4 * v * θ *
        (chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / θ)) := hcross

/-- For `v ≠ 0, 1`, `θ ≠ 0` and nonzero Chebyshev denominator, the centered Chebyshev kernel
`θ(1 - v²)/(1 - 2v(1 - 2θ) + v²)` equals `(1 - v²)/(4v)` times the Koebe resolvent at `-(27/4)/θ`. -/
theorem chebyshevKoebe_centeredNode
    {v θ : ℂ} (hv0 : v ≠ 0) (hv1 : v ≠ 1) (hθ : θ ≠ 0)
    (hden : 1 - 2 * v * (1 - 2 * θ) + v ^ (2 : ℕ) ≠ 0) :
    θ * (1 - v ^ (2 : ℕ)) /
        (1 - 2 * v * (1 - 2 * θ) + v ^ (2 : ℕ)) =
      (1 - v ^ (2 : ℕ)) / (4 * v) *
        (chebyshevTraceKoebeMap v /
          (chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / θ))) := by
  rw [chebyshevKoebe_resolvent hv1 hθ hden]
  field_simp [hv0, hden]

/-- If `v ≠ 0, 1`, `θ ≠ 0` and `K(v) = -(27/4)/θ`, then `1 - 2θ = (v + v⁻¹)/2`: Koebe poles are the
Joukowski preimages of the Chebyshev node. -/
theorem chebyshevKoebe_joukowski
    {v θ : ℂ} (hv0 : v ≠ 0) (hv1 : v ≠ 1) (hθ : θ ≠ 0)
    (hnode : chebyshevTraceKoebeMap v = -(27 / 4 : ℂ) / θ) :
    1 - 2 * θ = (v + v⁻¹) / 2 := by
  have hcross := chebyshevKoebe_resolvent_cross hv1 hθ
  rw [hnode] at hcross
  have hx : (-(27 / 4 : ℂ) / θ) ≠ 0 := by
    exact div_ne_zero (by norm_num) hθ
  have hden : 1 - 2 * v * (1 - 2 * θ) + v ^ (2 : ℕ) = 0 := by
    have hm := hcross
    rw [sub_self, mul_zero] at hm
    exact (mul_eq_zero.mp hm).resolve_right hx
  field_simp [hv0]
  linear_combination (-1) * hden

end RHTower

import GaloisForLFunctions.RHTower.AnharmonicChebyshevOrientationCasimir

namespace RHTower

theorem chebyshevKoebe_resolvent_cross
    {v θ : ℂ} (hv : v ≠ 1) (hθ : θ ≠ 0) :
    (1 - 2 * v * (1 - 2 * θ) + v ^ (2 : ℕ)) *
        chebyshevTraceKoebeMap v =
      4 * v * θ * (chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / θ)) := by
  simp only [chebyshevTraceKoebeMap]
  field_simp [hv, hθ]
  ring

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

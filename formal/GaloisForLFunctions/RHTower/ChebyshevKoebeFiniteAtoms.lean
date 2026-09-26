import GaloisForLFunctions.RHTower.ChebyshevKoebeGenerating

open scoped BigOperators
open Filter Topology

namespace RHTower

noncomputable def finiteChebyshevCenteredRational {ι : Type*}
    (S : Finset ι) (w θ : ι → ℂ) (v : ℂ) : ℂ :=
  ∑ i ∈ S,
    w i * θ i * (1 - v ^ (2 : ℕ)) /
      (1 - 2 * v * (1 - 2 * θ i) + v ^ (2 : ℕ))

noncomputable def finiteKoebeResolvent {ι : Type*}
    (S : Finset ι) (w θ : ι → ℂ) (v : ℂ) : ℂ :=
  ∑ i ∈ S,
    if θ i = 0 then 0 else
      w i * (chebyshevTraceKoebeMap v /
        (chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / θ i)))

theorem finiteChebyshevCenteredRational_eq_koebe {ι : Type*}
    (S : Finset ι) (w θ : ι → ℂ) {v : ℂ}
    (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (hden : ∀ i ∈ S, 1 - 2 * v * (1 - 2 * θ i) + v ^ (2 : ℕ) ≠ 0) :
    finiteChebyshevCenteredRational S w θ v =
      (1 - v ^ (2 : ℕ)) / (4 * v) * finiteKoebeResolvent S w θ v := by
  classical
  rw [finiteChebyshevCenteredRational, finiteKoebeResolvent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hθ : θ i = 0
  · simp [hθ]
  simp only [if_neg hθ]
  calc
    w i * θ i * (1 - v ^ (2 : ℕ)) /
        (1 - 2 * v * (1 - 2 * θ i) + v ^ (2 : ℕ)) =
      w i * (θ i * (1 - v ^ (2 : ℕ)) /
        (1 - 2 * v * (1 - 2 * θ i) + v ^ (2 : ℕ))) := by ring
    _ = w i * ((1 - v ^ (2 : ℕ)) / (4 * v) *
        (chebyshevTraceKoebeMap v /
          (chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / θ i)))) := by
      rw [chebyshevKoebe_centeredNode hv0 hv1 hθ (hden i hi)]
    _ = (1 - v ^ (2 : ℕ)) / (4 * v) *
        (w i * (chebyshevTraceKoebeMap v /
          (chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / θ i)))) := by ring

theorem finiteChebyshevCenteredRational_eq_koebe_eventually {ι : Type*}
    (S : Finset ι) (w θ : ι → ℂ) :
    ∀ᶠ v in 𝓝 (0 : ℂ), v ≠ 0 →
      finiteChebyshevCenteredRational S w θ v =
        (1 - v ^ (2 : ℕ)) / (4 * v) * finiteKoebeResolvent S w θ v := by
  have hden : ∀ᶠ v in 𝓝 (0 : ℂ),
      ∀ i ∈ S, 1 - 2 * v * (1 - 2 * θ i) + v ^ (2 : ℕ) ≠ 0 := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
        have hcont : ContinuousAt
            (fun v : ℂ => 1 - 2 * v * (1 - 2 * θ i) + v ^ (2 : ℕ)) 0 := by
          fun_prop
        have hi0 : (1 - 2 * (0 : ℂ) * (1 - 2 * θ i) +
            (0 : ℂ) ^ (2 : ℕ)) ≠ 0 := by norm_num
        have hiev := hcont.eventually_ne hi0
        filter_upwards [hiev, ih] with v hv hS j hj
        rcases Finset.mem_insert.mp hj with rfl | hjS
        · exact hv
        · exact hS j hjS
  have hv1 : ∀ᶠ v in 𝓝 (0 : ℂ), v ≠ 1 :=
    eventually_ne_nhds (by norm_num)
  filter_upwards [hden, hv1] with v hD hv1 hv0
  exact finiteChebyshevCenteredRational_eq_koebe S w θ hv0 hv1 hD

end RHTower

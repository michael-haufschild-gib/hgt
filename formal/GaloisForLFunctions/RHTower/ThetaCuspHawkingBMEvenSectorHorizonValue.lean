import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorBoundaryFlux

/-!
# Horizon regularity of the even-sector radial current

At the fundamental harmonic the radial symplectic current between the `−` mode and the `++`
Laurent responses is, for `r ≠ 0, ±1`, the rational function `evenCurrentSSLam` (resp.
`evenCurrentVVLam`) whose denominator is `r⁷` times a nonzero constant: the factor `r² − 1` of the
generic denominator cancels. Hence the current extends continuously to the horizon `r = 1`, with the
explicit limits `evenHorizonSS`, `evenHorizonVV` (`evenCurrentSS_horizon`, `evenCurrentVV_horizon`).
The horizon divergence of the flux therefore sits entirely in the envelope `z^{(s−3)/2}` carried by
the two modes, not in the reconstructed radial functions.
-/

set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream
open Filter Topology
noncomputable section

/-- The SS radial current at the fundamental harmonic as a rational function of `r`. -/
def evenCurrentSSLam (s r : ℂ) : ℂ := (((15 / 8 : ℂ) * s ^ 2 + (103 / 16 : ℂ) * s ^ 3 + (17 / 2 : ℂ) * s ^ 4 + (43 / 8 : ℂ) * s ^ 5 + (13 / 8 : ℂ) * s ^ 6 + (3 / 16 : ℂ) * s ^ 7) + r * ((0 : ℂ) + r * (((3 : ℂ) + (25 / 2 : ℂ) * s + (75 / 8 : ℂ) * s ^ 2 + (-19 / 2 : ℂ) * s ^ 3 + (-115 / 8 : ℂ) * s ^ 4 + (-23 / 4 : ℂ) * s ^ 5 + (-3 / 4 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((5 / 2 : ℂ) * s + (3 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 4) + r * ((0 : ℂ) + r * ((-3 : ℂ) * s + (-1 / 2 : ℂ) * s ^ 2))))))) / (r ^ 7 * s * (s + 3))

theorem evenCurrentSS_eq' (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    evenCurrentSS s r ((s + 1) * (s + 2)) (laurentMasterA s ((s + 1) * (s + 2))) (laurentMasterB s ((s + 1) * (s + 2))) = evenCurrentSSLam s r :=
  evenCurrentSS_eq s r hr hf hs hs3 hs1

/-- Horizon value of the SS radial current. -/
def evenHorizonSS (s : ℂ) : ℂ := ((3 : ℂ) + (12 : ℂ) * s + (55 / 4 : ℂ) * s ^ 2 + (-49 / 16 : ℂ) * s ^ 3 + (-51 / 8 : ℂ) * s ^ 4 + (-3 / 8 : ℂ) * s ^ 5 + (7 / 8 : ℂ) * s ^ 6 + (3 / 16 : ℂ) * s ^ 7) / (s * (s + 3))

theorem evenCurrentSSLam_one (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) : evenCurrentSSLam s 1 = evenHorizonSS s := by
  unfold evenCurrentSSLam evenHorizonSS
  field_simp
  ring

theorem evenCurrentSSLam_continuousAt (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    ContinuousAt (evenCurrentSSLam s) 1 := by
  unfold evenCurrentSSLam
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · simp only [one_pow, one_mul]
    exact mul_ne_zero hs hs3

/-- The SS radial current extends continuously to the horizon. -/
theorem evenCurrentSS_horizon (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    Tendsto (fun r : ℂ => evenCurrentSS s r ((s + 1) * (s + 2)) (laurentMasterA s ((s + 1) * (s + 2))) (laurentMasterB s ((s + 1) * (s + 2))))
      (𝓝[≠] (1 : ℂ)) (𝓝 (evenHorizonSS s)) := by
  have hc : Tendsto (evenCurrentSSLam s) (𝓝[≠] (1 : ℂ)) (𝓝 (evenHorizonSS s)) := by
    rw [← evenCurrentSSLam_one s hs hs3]
    exact ((evenCurrentSSLam_continuousAt s hs hs3).tendsto).mono_left nhdsWithin_le_nhds
  refine hc.congr' ?_
  have h0 : ∀ᶠ r in 𝓝[≠] (1 : ℂ), r ≠ 0 :=
    (eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 0)).filter_mono nhdsWithin_le_nhds
  have hm : ∀ᶠ r in 𝓝[≠] (1 : ℂ), r ≠ -1 :=
    (eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ -1)).filter_mono nhdsWithin_le_nhds
  have h1 : ∀ᶠ r in 𝓝[≠] (1 : ℂ), r ≠ 1 := self_mem_nhdsWithin
  filter_upwards [h0, hm, h1] with r hr0 hrm hr1
  have hf : r ^ 2 - 1 ≠ 0 := by
    rw [show r ^ 2 - 1 = (r - 1) * (r + 1) by ring]
    exact mul_ne_zero (sub_ne_zero.mpr hr1) (fun h => hrm (eq_neg_of_add_eq_zero_left h))
  exact (evenCurrentSS_eq' s r hr0 hf hs hs3 hs1).symm

/-- The VV radial current at the fundamental harmonic as a rational function of `r`. -/
def evenCurrentVVLam (s r : ℂ) : ℂ := (((-15 / 2 : ℂ) * s + (-103 / 4 : ℂ) * s ^ 2 + (-34 : ℂ) * s ^ 3 + (-43 / 2 : ℂ) * s ^ 4 + (-13 / 2 : ℂ) * s ^ 5 + (-3 / 4 : ℂ) * s ^ 6) + r * ((0 : ℂ) + r * (((88 : ℂ) + (184 : ℂ) * s + (120 : ℂ) * s ^ 2 + (20 : ℂ) * s ^ 3 + (-11 / 2 : ℂ) * s ^ 4 + (-3 / 2 : ℂ) * s ^ 5) + r * ((0 : ℂ) + r * ((66 : ℂ) + (70 : ℂ) * s + (-3 : ℂ) * s ^ 2 + (-7 : ℂ) * s ^ 3))))) / (r ^ 7 * (s + 3))

theorem evenCurrentVV_eq' (s r : ℂ) (hr : r ≠ 0) (hf : r ^ 2 - 1 ≠ 0) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    evenCurrentVV s r ((s + 1) * (s + 2)) (vvLaurentMasterA s ((s + 1) * (s + 2))) (vvLaurentMasterB s ((s + 1) * (s + 2))) = evenCurrentVVLam s r :=
  evenCurrentVV_eq s r hr hf hs hs3 hs1

/-- Horizon value of the VV radial current. -/
def evenHorizonVV (s : ℂ) : ℂ := ((154 : ℂ) + (493 / 2 : ℂ) * s + (365 / 4 : ℂ) * s ^ 2 + (-21 : ℂ) * s ^ 3 + (-27 : ℂ) * s ^ 4 + (-8 : ℂ) * s ^ 5 + (-3 / 4 : ℂ) * s ^ 6) / ((s + 3))

theorem evenCurrentVVLam_one (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) : evenCurrentVVLam s 1 = evenHorizonVV s := by
  unfold evenCurrentVVLam evenHorizonVV
  field_simp
  ring

theorem evenCurrentVVLam_continuousAt (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    ContinuousAt (evenCurrentVVLam s) 1 := by
  unfold evenCurrentVVLam
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · simp only [one_pow, one_mul]
    exact hs3

/-- The VV radial current extends continuously to the horizon. -/
theorem evenCurrentVV_horizon (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hs1 : s + 1 ≠ 0) :
    Tendsto (fun r : ℂ => evenCurrentVV s r ((s + 1) * (s + 2)) (vvLaurentMasterA s ((s + 1) * (s + 2))) (vvLaurentMasterB s ((s + 1) * (s + 2))))
      (𝓝[≠] (1 : ℂ)) (𝓝 (evenHorizonVV s)) := by
  have hc : Tendsto (evenCurrentVVLam s) (𝓝[≠] (1 : ℂ)) (𝓝 (evenHorizonVV s)) := by
    rw [← evenCurrentVVLam_one s hs hs3]
    exact ((evenCurrentVVLam_continuousAt s hs hs3).tendsto).mono_left nhdsWithin_le_nhds
  refine hc.congr' ?_
  have h0 : ∀ᶠ r in 𝓝[≠] (1 : ℂ), r ≠ 0 :=
    (eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 0)).filter_mono nhdsWithin_le_nhds
  have hm : ∀ᶠ r in 𝓝[≠] (1 : ℂ), r ≠ -1 :=
    (eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ -1)).filter_mono nhdsWithin_le_nhds
  have h1 : ∀ᶠ r in 𝓝[≠] (1 : ℂ), r ≠ 1 := self_mem_nhdsWithin
  filter_upwards [h0, hm, h1] with r hr0 hrm hr1
  have hf : r ^ 2 - 1 ≠ 0 := by
    rw [show r ^ 2 - 1 = (r - 1) * (r + 1) by ring]
    exact mul_ne_zero (sub_ne_zero.mpr hr1) (fun h => hrm (eq_neg_of_add_eq_zero_left h))
  exact (evenCurrentVV_eq' s r hr0 hf hs hs3 hs1).symm

end
end RHTower.D4BMScalarStream

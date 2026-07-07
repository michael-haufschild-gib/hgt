/-
The whole-loop band-edge count is even, with no endpoint-orientation hypothesis.

On a single lateral edge the parity of the forced band-edge crossings equals the agreement of the
two endpoint orientations (`exists_crossing_enum_parity`), and that endpoint datum is freely
steerable (`endpoint_orientation_no_go`).  The steering vanishes once the phase advances a whole
number of turns over the segment: if `θ b − θ a = k·(2π)`, then the endpoint sines coincide,
`sin(θ b) = sin(θ a + 2πk) = sin(θ a)`, so the two endpoint imaginary parts carry the same sign as
`sin(θ a)` with no free orientation to steer, and the crossing count is `2k` — even.

Thus a phase that closes onto a whole number of turns discharges the paired-flux interface
unconditionally: the fixed-point-free consecutive-crossing pairing exists because the count is even,
and the winding integer `k`, not the endpoint signs, is what fixes the parity.  This is the whole-loop
reading of the band-edge algebra — the rigid winding integer in place of the steerable endpoint pair.
-/
import GaloisForLFunctions.RHTower.EdgeEventParity

open Complex

namespace RHTower

/-! ### §1 A whole-turn phase advance fixes the endpoint sines -/

/-- A phase advancing by a whole number of turns leaves the sine unchanged. -/
theorem sin_of_phase_wind {θa θb : ℝ} {k : ℤ} (hw : θb - θa = (k : ℝ) * (2 * Real.pi)) :
    Real.sin θb = Real.sin θa := by
  rw [show θb = θa + (k : ℝ) * (2 * Real.pi) from by linarith, Real.sin_add_int_mul_two_pi]

/-! ### §2 The whole-loop crossing enumeration and its automatic pairing -/

/-- **The band-edge count is even when the phase winds a whole number of turns.**  For a carrier in
polar form with positive modulus and strictly monotone continuous phase, if the phase advance over
the segment is an integer multiple of `2π` and the basepoint is not itself a crossing, then the
forced crossings are a strictly ordered finite family that exhausts all crossings, their number is
even, and their event list carries paired flux — with no endpoint-orientation hypothesis.  The
endpoint agreement that the per-edge form assumes is here a theorem: the whole-turn advance forces
`sin(θ b) = sin(θ a)`, so both endpoints carry the sign of `sin(θ a)`. -/
theorem crossings_fluxPaired_of_phase_winds {F : ℝ → ℂ} {r θ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hpolar : ∀ τ ∈ Set.Icc a b, F τ = (r τ : ℂ) * Complex.exp ((θ τ : ℝ) * I))
    (hr : ∀ τ ∈ Set.Icc a b, 0 < r τ)
    (hmono : StrictMonoOn θ (Set.Icc a b)) (hθc : ContinuousOn θ (Set.Icc a b))
    (hsin : Real.sin (θ a) ≠ 0)
    {k : ℤ} (hwind : θ b - θ a = (k : ℝ) * (2 * Real.pi)) :
    ∃ (n : ℕ) (e : Fin n → ℝ), StrictMono e ∧
      (∀ i, e i ∈ Set.Icc a b ∧ (F (e i)).im = 0) ∧
      (∀ τ ∈ Set.Icc a b, (F τ).im = 0 → ∃ i, e i = τ) ∧
      Even n ∧ LedgerFluxPaired (List.replicate n 1) := by
  have haa : a ∈ Set.Icc a b := ⟨le_refl a, hab.le⟩
  have hbb : b ∈ Set.Icc a b := ⟨hab.le, le_refl b⟩
  have hIma : (F a).im = r a * Real.sin (θ a) := by rw [hpolar a haa, polar_im]
  have hImb : (F b).im = r b * Real.sin (θ b) := by rw [hpolar b hbb, polar_im]
  have hsinb : Real.sin (θ b) = Real.sin (θ a) := sin_of_phase_wind hwind
  have hna : (F a).im ≠ 0 := by rw [hIma]; exact mul_ne_zero (ne_of_gt (hr a haa)) hsin
  have hnb : (F b).im ≠ 0 := by
    rw [hImb, hsinb]; exact mul_ne_zero (ne_of_gt (hr b hbb)) hsin
  -- endpoint agreement is forced: both imaginary parts share the sign of `sin (θ a)`
  have hagree : 0 < (F a).im ↔ 0 < (F b).im := by
    rw [hIma, hImb, hsinb, mul_pos_iff_of_pos_left (hr a haa),
      mul_pos_iff_of_pos_left (hr b hbb)]
  obtain ⟨n, e, hemono, hev, hexh, hpar⟩ :=
    exists_crossing_enum_parity hab hpolar hr hmono hθc hna hnb
  have hEven : Even n := hpar.mpr hagree
  exact ⟨n, e, hemono, hev, hexh, hEven,
    ledgerFluxPaired_replicate_one (nonempty_bandEdgePairing_of_even hEven.two_dvd)⟩

/-! ### §3 The incidence carrier: paired flux with the winding integer in place of `hagree` -/

/-- **The incidence pencil's band-edge events are paired when its phase winds a whole number of
turns.**  On a lateral edge presented in polar form with positive modulus and a strictly monotone
continuous phase (as produced by `incidence_edge_polar_data`), with the basepoint not a crossing and
the phase advance an integer multiple of `2π`, the forced band-edge events come in an even number and
their event list carries paired flux — discharging the paired-flux interface with no
endpoint-orientation datum.  The parity is fixed by the winding integer of the phase, not by the
steerable endpoint signs. -/
theorem exists_incidence_edge_events_fluxPaired_of_wind {Λ₁ Λ₂ : ℂ → ℂ} {U : Set ℂ}
    {σ a b : ℝ} {R θ : ℝ → ℝ}
    (hab : a < b) (hmapU : ∀ τ ∈ Set.Icc a b, stripPt σ τ ∈ U)
    (hΛ1ne : ∀ z ∈ U, Λ₁ z ≠ 0)
    (hpolar : ∀ τ ∈ Set.Icc a b,
      incidence Λ₁ Λ₂ (stripPt σ τ) = (R τ : ℂ) * Complex.exp ((θ τ : ℝ) * I))
    (hR : ∀ τ ∈ Set.Icc a b, 0 < R τ)
    (hmono : StrictMonoOn θ (Set.Icc a b)) (hθc : ContinuousOn θ (Set.Icc a b))
    (hsin : Real.sin (θ a) ≠ 0)
    {k : ℤ} (hwind : θ b - θ a = (k : ℝ) * (2 * Real.pi)) :
    ∃ (n : ℕ) (e : Fin n → ℝ), StrictMono e ∧
      (∀ i, e i ∈ Set.Icc a b ∧
        pencil Λ₁ Λ₂ ((incidence Λ₁ Λ₂ (stripPt σ (e i))).re : ℂ) 1 (stripPt σ (e i)) = 0) ∧
      Even n ∧ LedgerFluxPaired (List.replicate n 1) := by
  obtain ⟨n, e, hemono, hev, _hexh, hEven, hpar⟩ :=
    crossings_fluxPaired_of_phase_winds (F := fun τ => incidence Λ₁ Λ₂ (stripPt σ τ))
      hab hpolar hR hmono hθc hsin hwind
  refine ⟨n, e, hemono, fun i => ⟨(hev i).1, ?_⟩, hEven, hpar⟩
  exact incidence_real_member_zero_of_im_zero
    (hΛ1ne (stripPt σ (e i)) (hmapU (e i) (hev i).1)) (hev i).2

end RHTower

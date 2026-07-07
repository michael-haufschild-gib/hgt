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

/-- **A closed contour's phase winds a whole number of turns.**  If a carrier in polar form with
positive modulus takes the same value at the two endpoints of the parameter interval, then the
continuous phase advances by an integer multiple of `2π`: the moduli agree (they are the common
absolute value) and the unit factors agree, so `exp((θ b − θ a)i) = 1`.  This discharges the
whole-turn hypothesis from loop closure — no assumption on the winding integer is needed. -/
theorem phase_winds_of_loop_closed {r θ : ℝ → ℝ} {a b : ℝ} (hra : 0 < r a) (hrb : 0 < r b)
    (hclosed : (r a : ℂ) * Complex.exp ((θ a : ℝ) * I) = (r b : ℂ) * Complex.exp ((θ b : ℝ) * I)) :
    ∃ k : ℤ, θ b - θ a = (k : ℝ) * (2 * Real.pi) := by
  have hnorm : r a = r b := by
    have hn := congrArg norm hclosed
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, mul_one, mul_one,
      Real.norm_of_nonneg hra.le, Real.norm_of_nonneg hrb.le] at hn
    exact hn
  have hr0 : (r a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hra
  have hclosed' : (r a : ℂ) * Complex.exp ((θ a : ℝ) * I)
      = (r a : ℂ) * Complex.exp ((θ b : ℝ) * I) := by rw [hnorm] at hclosed ⊢; exact hclosed
  have hexp : Complex.exp ((θ a : ℝ) * I) = Complex.exp ((θ b : ℝ) * I) :=
    mul_left_cancel₀ hr0 hclosed'
  have hdiv : Complex.exp (((θ b : ℝ) * I) - ((θ a : ℝ) * I)) = 1 := by
    rw [Complex.exp_sub, ← hexp, div_self (Complex.exp_ne_zero _)]
  rw [Complex.exp_eq_one_iff] at hdiv
  obtain ⟨n, hn⟩ := hdiv
  refine ⟨n, ?_⟩
  have hcast : (((θ b - θ a : ℝ)) : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    have hrw : ((θ b : ℝ) * I) - ((θ a : ℝ) * I) = ((θ b - θ a : ℝ) : ℂ) * I := by push_cast; ring
    rw [hrw] at hn; rw [hn]; ring
  exact_mod_cast hcast

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

/-! ### §4 The pairing discharged from loop closure, with the winding hypothesis removed -/

/-- **Loop closure discharges the whole-turn hypothesis.**  For a carrier in polar form with
positive modulus, strictly monotone continuous phase, whose value at the two endpoints coincides
(the contour closes) and whose basepoint is not a crossing, the forced crossings are even in number
and their event list carries paired flux — with neither an endpoint-orientation hypothesis nor an
assumed winding integer.  Closure supplies the whole-turn advance (`phase_winds_of_loop_closed`), and
that in turn forces the count even.  Equivalently: the endpoint agreement `exists_crossing_enum_parity`
needs is here vacuous, both endpoints being the same point. -/
theorem crossings_fluxPaired_of_loop_closed {F : ℝ → ℂ} {r θ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hpolar : ∀ τ ∈ Set.Icc a b, F τ = (r τ : ℂ) * Complex.exp ((θ τ : ℝ) * I))
    (hr : ∀ τ ∈ Set.Icc a b, 0 < r τ)
    (hmono : StrictMonoOn θ (Set.Icc a b)) (hθc : ContinuousOn θ (Set.Icc a b))
    (hsin : Real.sin (θ a) ≠ 0) (hclosed : F a = F b) :
    ∃ (n : ℕ) (e : Fin n → ℝ), StrictMono e ∧
      (∀ i, e i ∈ Set.Icc a b ∧ (F (e i)).im = 0) ∧
      (∀ τ ∈ Set.Icc a b, (F τ).im = 0 → ∃ i, e i = τ) ∧
      Even n ∧ LedgerFluxPaired (List.replicate n 1) := by
  have haa : a ∈ Set.Icc a b := ⟨le_refl a, hab.le⟩
  have hbb : b ∈ Set.Icc a b := ⟨hab.le, le_refl b⟩
  have hpa := hpolar a haa
  have hpb := hpolar b hbb
  obtain ⟨k, hwind⟩ := phase_winds_of_loop_closed (r := r) (θ := θ) (hr a haa) (hr b hbb)
    (by rw [← hpa, ← hpb]; exact hclosed)
  exact crossings_fluxPaired_of_phase_winds hab hpolar hr hmono hθc hsin hwind

/-- **The incidence pencil's band-edge events are paired around a closed contour.**  On a closed
contour `γ` (returning to its start, `γ lo = γ hi`) along which the incidence carrier is presented in
polar form with positive modulus and strictly monotone continuous phase and the basepoint is not a
crossing, the forced band-edge events come in an even number and carry paired flux, with the pencil
members vanishing at each event — no endpoint-orientation datum and no assumed winding integer.
Closure supplies the whole-turn advance, so the count is even. -/
theorem exists_incidence_loop_events_fluxPaired {Λ₁ Λ₂ : ℂ → ℂ} {γ : ℝ → ℂ}
    {lo hi : ℝ} {R θ : ℝ → ℝ}
    (hab : lo < hi) (hΛ1ne : ∀ τ ∈ Set.Icc lo hi, Λ₁ (γ τ) ≠ 0)
    (hpolar : ∀ τ ∈ Set.Icc lo hi,
      incidence Λ₁ Λ₂ (γ τ) = (R τ : ℂ) * Complex.exp ((θ τ : ℝ) * I))
    (hR : ∀ τ ∈ Set.Icc lo hi, 0 < R τ)
    (hmono : StrictMonoOn θ (Set.Icc lo hi)) (hθc : ContinuousOn θ (Set.Icc lo hi))
    (hsin : Real.sin (θ lo) ≠ 0) (hγ : γ lo = γ hi) :
    ∃ (n : ℕ) (e : Fin n → ℝ), StrictMono e ∧
      (∀ i, e i ∈ Set.Icc lo hi ∧
        pencil Λ₁ Λ₂ ((incidence Λ₁ Λ₂ (γ (e i))).re : ℂ) 1 (γ (e i)) = 0) ∧
      Even n ∧ LedgerFluxPaired (List.replicate n 1) := by
  obtain ⟨n, e, hemono, hev, _hexh, hEven, hpar⟩ :=
    crossings_fluxPaired_of_loop_closed (F := fun τ => incidence Λ₁ Λ₂ (γ τ))
      hab hpolar hR hmono hθc hsin (show incidence Λ₁ Λ₂ (γ lo) = incidence Λ₁ Λ₂ (γ hi) by rw [hγ])
  refine ⟨n, e, hemono, fun i => ⟨(hev i).1, ?_⟩, hEven, hpar⟩
  exact incidence_real_member_zero_of_im_zero (hΛ1ne (e i) (hev i).1) (hev i).2

end RHTower

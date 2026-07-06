/-
The parity of the band-edge crossing count, from the boundary orientation.

Along a lateral edge the incidence carrier has a strictly monotone phase, so its imaginary part
vanishes exactly at the phase's crossings of integer multiples of `π`.  These crossings are in
bijection with the integers `k` with `θ(a) < kπ < θ(b)`, so their number is
`⌊θ(b)/π⌋ − ⌊θ(a)/π⌋`, and — because the sign of `sin` on `(mπ,(m+1)π)` is `(−1)^m` — this count
is even exactly when the two endpoints of the edge lie on the same side of the real axis
(`Im` of the same sign).  This is the consecutive-crossing pairing's boundary condition made
exact: when the endpoint orientations agree, the forced crossings come in an even number and
pair, discharging the paired-flux interface.  The residual content of the whole route is then a
single boundary datum — the agreement of the endpoint orientations — supplied by the functional
equation of the box.
-/
import GaloisForLFunctions.RHTower.EdgeEventLedger

open Complex

namespace RHTower

/-! ### The sign of the phase's sine -/

/-- On `(mπ, (m+1)π)` the sine has sign `(−1)^m`: it is positive exactly when `⌊x/π⌋` is even. -/
theorem sin_pos_iff_even_floor {x : ℝ} (hx : Real.sin x ≠ 0) :
    0 < Real.sin x ↔ Even ⌊x / Real.pi⌋ := by
  set k : ℤ := ⌊x / Real.pi⌋ with hk
  have hπ : 0 < Real.pi := Real.pi_pos
  have hr0 : 0 ≤ x - k * Real.pi := by
    have := Int.sub_floor_div_mul_nonneg x hπ; simpa [hk] using this
  have hr1 : x - k * Real.pi < Real.pi := by
    have h := Int.lt_floor_add_one (x / Real.pi)
    have hx2 : x < (k + 1) * Real.pi := by
      rw [← hk] at h; rw [div_lt_iff₀ hπ] at h; nlinarith [h]
    nlinarith [hx2]
  have hsplit : Real.sin x = (-1) ^ k * Real.sin (x - k * Real.pi) := by
    have := Real.sin_add_int_mul_pi (x - k * Real.pi) k
    rw [sub_add_cancel] at this
    rw [this]
  have hrne : x - k * Real.pi ≠ 0 := by
    intro h; rw [hsplit, h, Real.sin_zero, mul_zero] at hx; exact hx rfl
  have hrpos : 0 < x - k * Real.pi := lt_of_le_of_ne hr0 (Ne.symm hrne)
  have hsinr : 0 < Real.sin (x - k * Real.pi) := Real.sin_pos_of_pos_of_lt_pi hrpos hr1
  rw [hsplit]
  constructor
  · intro hpos
    by_contra hodd
    rw [Int.not_even_iff_odd] at hodd
    rw [hodd.neg_one_zpow] at hpos
    nlinarith [hsinr]
  · intro heven
    rw [heven.neg_one_zpow]; linarith [hsinr]

/-! ### The imaginary part of a polar carrier -/

/-- The imaginary part of `r·exp(iθ)` is `r·sin θ`. -/
theorem polar_im {r θ : ℝ} : ((r : ℂ) * Complex.exp ((θ : ℝ) * I)).im = r * Real.sin θ := by
  rw [Complex.mul_im]
  simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-! ### The exact enumeration of crossings and its parity -/

/-- **The band-edge crossings enumerated, with the parity criterion.**  For a carrier presented
in polar form with a positive modulus and a strictly monotone continuous phase, whose endpoints
are not themselves crossings, the points where the imaginary part vanishes are a strictly ordered
finite family `e : Fin n → [a,b]` that exhausts all crossings, and `n` is even exactly when the
two endpoints have imaginary parts of the same sign.  The consecutive-crossing pairing therefore
applies precisely when the endpoint orientations agree. -/
theorem exists_crossing_enum_parity {F : ℝ → ℂ} {r θ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hpolar : ∀ τ ∈ Set.Icc a b, F τ = (r τ : ℂ) * Complex.exp ((θ τ : ℝ) * I))
    (hr : ∀ τ ∈ Set.Icc a b, 0 < r τ)
    (hmono : StrictMonoOn θ (Set.Icc a b)) (hθc : ContinuousOn θ (Set.Icc a b))
    (hna : (F a).im ≠ 0) (hnb : (F b).im ≠ 0) :
    ∃ (n : ℕ) (e : Fin n → ℝ), StrictMono e ∧
      (∀ i, e i ∈ Set.Icc a b ∧ (F (e i)).im = 0) ∧
      (∀ τ ∈ Set.Icc a b, (F τ).im = 0 → ∃ i, e i = τ) ∧
      (Even n ↔ (0 < (F a).im ↔ 0 < (F b).im)) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have haa : a ∈ Set.Icc a b := ⟨le_refl a, hab.le⟩
  have hbb : b ∈ Set.Icc a b := ⟨hab.le, le_refl b⟩
  have hImF : ∀ τ ∈ Set.Icc a b, (F τ).im = r τ * Real.sin (θ τ) := by
    intro τ hτ; rw [hpolar τ hτ, polar_im]
  have hsinθa : Real.sin (θ a) ≠ 0 := by
    intro h; apply hna; rw [hImF a haa, h, mul_zero]
  have hsinθb : Real.sin (θ b) ≠ 0 := by
    intro h; apply hnb; rw [hImF b hbb, h, mul_zero]
  have hθab : θ a < θ b := hmono haa hbb hab
  set fa : ℤ := ⌊θ a / Real.pi⌋ with hfa
  set fb : ℤ := ⌊θ b / Real.pi⌋ with hfb
  have hfa_lt : θ a < ((fa : ℝ) + 1) * Real.pi := by
    have h := Int.lt_floor_add_one (θ a / Real.pi)
    rw [← hfa, div_lt_iff₀ hπ] at h; linarith [h]
  have hfa_le_real : (fa : ℝ) * Real.pi ≤ θ a := by
    have h := Int.floor_le (θ a / Real.pi); rw [← hfa, le_div_iff₀ hπ] at h; linarith [h]
  have hfa_lt_real : (fa : ℝ) * Real.pi < θ a := by
    rcases lt_or_eq_of_le hfa_le_real with h | h
    · exact h
    · exact absurd (by rw [← h]; exact Real.sin_int_mul_pi fa) hsinθa
  have hfb_le : (fb : ℝ) * Real.pi ≤ θ b := by
    have h := Int.floor_le (θ b / Real.pi); rw [← hfb, le_div_iff₀ hπ] at h; linarith [h]
  have hfb_lt : (fb : ℝ) * Real.pi < θ b := by
    rcases lt_or_eq_of_le hfb_le with h | h
    · exact h
    · exact absurd (by rw [← h]; exact Real.sin_int_mul_pi fb) hsinθb
  have hfa_le_fb : fa ≤ fb :=
    Int.floor_mono ((div_le_div_iff_of_pos_right hπ).mpr hθab.le)
  set C : ℤ := fb - fa with hC
  have hC0 : 0 ≤ C := by rw [hC]; omega
  set n : ℕ := C.toNat with hn
  have hnC : (n : ℤ) = C := Int.toNat_of_nonneg hC0
  set lvl : Fin n → ℝ := fun i => ((fa + 1 + (i : ℕ) : ℤ) : ℝ) * Real.pi with hlvl
  have hlvl_mem : ∀ i : Fin n, θ a ≤ lvl i ∧ lvl i ≤ θ b := by
    intro i
    have hin : (i : ℤ) < C := by rw [← hnC]; exact_mod_cast i.isLt
    refine ⟨?_, ?_⟩
    · rw [hlvl]
      have hle : ((fa : ℝ) + 1) * Real.pi ≤ ((fa + 1 + (i : ℕ) : ℤ) : ℝ) * Real.pi :=
        mul_le_mul_of_nonneg_right
          (by push_cast; have : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _; linarith) hπ.le
      linarith [hfa_lt, hle]
    · have hik : (fa + 1 + (i : ℕ) : ℤ) ≤ fb := by rw [hC] at hin; omega
      have hle : ((fa + 1 + (i : ℕ) : ℤ) : ℝ) * Real.pi ≤ (fb : ℝ) * Real.pi :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hik) hπ.le
      rw [hlvl]; linarith [hle, hfb_le]
  have hpre : ∀ i : Fin n, ∃ τ ∈ Set.Icc a b, θ τ = lvl i := by
    intro i
    obtain ⟨τ, hτ, hθτ⟩ :=
      intermediate_value_Icc hab.le hθc ⟨(hlvl_mem i).1, (hlvl_mem i).2⟩
    exact ⟨τ, hτ, hθτ⟩
  choose e he hθe using hpre
  have hemono : StrictMono e := by
    intro i j hij
    have hlvlij : lvl i < lvl j := by
      rw [hlvl]; apply mul_lt_mul_of_pos_right _ hπ
      have hij' : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
      push_cast; linarith
    have hθij : θ (e i) < θ (e j) := by rw [hθe i, hθe j]; exact hlvlij
    rcases lt_trichotomy (e i) (e j) with h | h | h
    · exact h
    · rw [h] at hθij; exact absurd rfl (ne_of_lt hθij)
    · exact absurd (hmono (he j) (he i) h) (not_lt.mpr hθij.le)
  have hev : ∀ i, e i ∈ Set.Icc a b ∧ (F (e i)).im = 0 := by
    intro i
    refine ⟨he i, ?_⟩
    rw [hImF (e i) (he i), hθe i]
    simp only [hlvl]
    rw [Real.sin_int_mul_pi, mul_zero]
  have hexh : ∀ τ ∈ Set.Icc a b, (F τ).im = 0 → ∃ i, e i = τ := by
    intro τ hτ hcross
    have hsinτ : Real.sin (θ τ) = 0 := by
      have h := hImF τ hτ
      rw [hcross] at h
      rcases mul_eq_zero.mp h.symm with h' | h'
      · exact absurd h' (ne_of_gt (hr τ hτ))
      · exact h'
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsinτ
    have hτnea : τ ≠ a := by
      rintro rfl; exact hna (by rw [hImF τ hτ] at hcross ⊢; exact hcross)
    have hτneb : τ ≠ b := by
      rintro rfl; exact hnb (by rw [hImF τ hτ] at hcross ⊢; exact hcross)
    have hθτa : θ a < θ τ := hmono haa hτ (lt_of_le_of_ne hτ.1 (Ne.symm hτnea))
    have hθτb : θ τ < θ b := hmono hτ hbb (lt_of_le_of_ne hτ.2 hτneb)
    have hkπ : (k : ℝ) * Real.pi = θ τ := hk
    have hfa_k : fa < k := by
      have hlt : (fa : ℝ) < (k : ℝ) := by
        have h2 : (fa : ℝ) * Real.pi < (k : ℝ) * Real.pi := by rw [hkπ]; linarith [hfa_lt_real, hθτa]
        exact lt_of_mul_lt_mul_right h2 hπ.le
      exact_mod_cast hlt
    have hk_fb : k ≤ fb := by
      have hlt : (k : ℝ) * Real.pi < ((fb : ℝ) + 1) * Real.pi := by
        rw [hkπ]
        have h := Int.lt_floor_add_one (θ b / Real.pi)
        rw [← hfb, div_lt_iff₀ hπ] at h; linarith [h, hθτb]
      have : (k : ℝ) < (fb : ℝ) + 1 := lt_of_mul_lt_mul_right hlt hπ.le
      have hkint : k < fb + 1 := by exact_mod_cast this
      omega
    have hlocal : 0 < fb - fa := by omega
    have hi_lt : (k - fa - 1).toNat < n := by
      have : ((k - fa - 1).toNat : ℤ) < (n : ℤ) := by
        rw [Int.toNat_of_nonneg (by omega), hnC, hC]; omega
      exact_mod_cast this
    refine ⟨⟨(k - fa - 1).toNat, hi_lt⟩, ?_⟩
    have hlvl_eq : lvl ⟨(k - fa - 1).toNat, hi_lt⟩ = θ τ := by
      simp only [hlvl]
      rw [show ((fa + 1 + ((k - fa - 1).toNat : ℕ) : ℤ) : ℝ) = (k : ℝ) from by
        rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k - fa - 1)]; push_cast; ring, hkπ]
    have hθ_eq := hθe ⟨(k - fa - 1).toNat, hi_lt⟩
    rw [hlvl_eq] at hθ_eq
    exact hmono.injOn (he _) hτ hθ_eq
  refine ⟨n, e, hemono, hev, hexh, ?_⟩
  have hFa : (0 < (F a).im ↔ 0 < Real.sin (θ a)) := by
    rw [hImF a haa]; exact mul_pos_iff_of_pos_left (hr a haa)
  have hFb : (0 < (F b).im ↔ 0 < Real.sin (θ b)) := by
    rw [hImF b hbb]; exact mul_pos_iff_of_pos_left (hr b hbb)
  have hEvenN : Even n ↔ (Even fa ↔ Even fb) := by
    rw [← Int.even_coe_nat, hnC, hC, Int.even_sub]; tauto
  rw [hEvenN, hFa, hFb, sin_pos_iff_even_floor hsinθa, sin_pos_iff_even_floor hsinθb, ← hfa, ← hfb]

/-! ### The pairing discharged from endpoint agreement -/

/-- **Agreeing endpoints pair the crossings.**  When the two endpoints of a monotone-phase edge
have imaginary parts of the same sign, the crossings between them are even in number and carry
the consecutive-crossing pairing, so their event list satisfies the paired-flux interface — with
no pairing assumed. -/
theorem crossings_fluxPaired_of_endpoints_agree {F : ℝ → ℂ} {r θ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hpolar : ∀ τ ∈ Set.Icc a b, F τ = (r τ : ℂ) * Complex.exp ((θ τ : ℝ) * I))
    (hr : ∀ τ ∈ Set.Icc a b, 0 < r τ)
    (hmono : StrictMonoOn θ (Set.Icc a b)) (hθc : ContinuousOn θ (Set.Icc a b))
    (hna : (F a).im ≠ 0) (hnb : (F b).im ≠ 0)
    (hagree : 0 < (F a).im ↔ 0 < (F b).im) :
    ∃ (n : ℕ) (e : Fin n → ℝ), StrictMono e ∧
      (∀ i, e i ∈ Set.Icc a b ∧ (F (e i)).im = 0) ∧
      (∀ τ ∈ Set.Icc a b, (F τ).im = 0 → ∃ i, e i = τ) ∧
      LedgerFluxPaired (List.replicate n 1) := by
  obtain ⟨n, e, hemono, hev, hexh, hpar⟩ :=
    exists_crossing_enum_parity hab hpolar hr hmono hθc hna hnb
  exact ⟨n, e, hemono, hev, hexh,
    ledgerFluxPaired_replicate_one (nonempty_bandEdgePairing_of_even (hpar.mpr hagree).two_dvd)⟩

/-- **The band-edge events of the incidence pencil are paired when the edge endpoints agree.**
On a lateral edge where the anchor and target are analytic and nonvanishing, the incidence phase
rate is bounded below by `ρ₀ > 0`, the endpoints are not crossings, and their orientations agree,
the forced band-edge events come in an even number and their event list carries paired flux.  The
entire paired-flux burden is discharged into a single boundary datum: the agreement of the two
endpoint orientations of the incidence carrier. -/
theorem exists_incidence_edge_events_fluxPaired {Λ₁ Λ₂ : ℂ → ℂ} {U : Set ℂ} {σ a b ρ₀ : ℝ}
    (hab : a < b) (hρ : 0 < ρ₀) (hU : IsOpen U)
    (hmapU : ∀ τ ∈ Set.Icc a b, stripPt σ τ ∈ U)
    (hΛ1 : AnalyticOnNhd ℂ Λ₁ U) (hΛ1ne : ∀ z ∈ U, Λ₁ z ≠ 0)
    (hΛ2 : AnalyticOnNhd ℂ Λ₂ U) (hΛ2ne : ∀ z ∈ U, Λ₂ z ≠ 0)
    (hfloor : ∀ τ ∈ Set.Icc a b,
      ρ₀ ≤ (logDeriv Λ₂ (stripPt σ τ) - logDeriv Λ₁ (stripPt σ τ)).re)
    (hna : (incidence Λ₁ Λ₂ (stripPt σ a)).im ≠ 0)
    (hnb : (incidence Λ₁ Λ₂ (stripPt σ b)).im ≠ 0)
    (hagree : 0 < (incidence Λ₁ Λ₂ (stripPt σ a)).im ↔
      0 < (incidence Λ₁ Λ₂ (stripPt σ b)).im) :
    ∃ (n : ℕ) (e : Fin n → ℝ), StrictMono e ∧
      (∀ i, e i ∈ Set.Icc a b ∧
        pencil Λ₁ Λ₂ ((incidence Λ₁ Λ₂ (stripPt σ (e i))).re : ℂ) 1 (stripPt σ (e i)) = 0) ∧
      LedgerFluxPaired (List.replicate n 1) := by
  obtain ⟨R, θ, hRpos, hpolar, hθc, hratefloor⟩ :=
    incidence_edge_polar_data hab.le hU hmapU hΛ1 hΛ1ne hΛ2 hΛ2ne hfloor
  have hmono : StrictMonoOn θ (Set.Icc a b) := by
    intro x hx y hy hxy
    nlinarith [hratefloor x hx y hy hxy.le, hρ, sub_pos.mpr hxy]
  obtain ⟨n, e, hemono, hev, hexh, hpar⟩ :=
    crossings_fluxPaired_of_endpoints_agree (F := fun τ => incidence Λ₁ Λ₂ (stripPt σ τ))
      hab hpolar hRpos hmono hθc hna hnb hagree
  refine ⟨n, e, hemono, fun i => ⟨(hev i).1, ?_⟩, hpar⟩
  exact incidence_real_member_zero_of_im_zero
    (hΛ1ne (stripPt σ (e i)) (hmapU (e i) (hev i).1)) (hev i).2

end RHTower

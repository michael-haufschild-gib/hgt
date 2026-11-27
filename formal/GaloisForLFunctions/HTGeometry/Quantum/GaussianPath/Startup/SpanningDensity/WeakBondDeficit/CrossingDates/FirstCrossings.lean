import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.CrossingDates.Envelope

/-! # Physical first-crossing times for budgets below a full bond sweep -/

open Real Set MeasureTheory Filter
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open PrescribedTimes
noncomputable section

/-- For a budget missing d bonds, the first robust crossing has time
of order (K/d¹⁰)^(1/9), uniformly when a constant times K^(11/20) ≤ d ≤ γK.
The ninth-power form avoids fractional powers in the statement. -/
theorem gaussian_first_crossing_scale :
    ∃ γ>0, ∃ Q>0, ∃ l>0, ∃ L>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let x := fun i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
      ∀ d : ℕ, 0<d → d≤n+1 → (d:ℝ)≤γ*K → Q*K^11≤(d:ℝ)^20 →
        ∀ ρ∈Ioc (1/20:ℝ) (1/4), let σ := crossingOrigin n (n+1-d) ρ x
          l*K≤σ^9*(d:ℝ)^10 ∧ σ^9*(d:ℝ)^10≤L*K := by
  obtain ⟨M,hM,a,ha,b,hb,γ,hγ,hw⟩ := gaussian_crossing_envelope
  have hM' := zero_lt_one.trans_le hM
  let l := a/M^10
  let L := a*M^10
  let Q := L^2/b
  have hl : 0<l := div_pos ha (pow_pos hM' _)
  have hL : 0<L := mul_pos ha (pow_pos hM' _)
  have hQ : 0<Q := div_pos (sq_pos_of_pos hL) hb
  refine ⟨min γ ((1/M)^9),lt_min hγ (pow_pos (one_div_pos.mpr hM') _),
    Q^9,pow_pos hQ _,l^9,pow_pos hl _,L^9,pow_pos hL _,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  intro K x d hd hdn hsmall hlarge ρ hρ σ
  have hK : 0<K := by dsimp only [K]; positivity
  have hd' : 0<(d:ℝ) := Nat.cast_pos.mpr hd
  let h := ((d:ℝ)/K)^(1/9:ℝ)
  have hh : 0<h := rpow_pos_of_pos (div_pos hd' hK) _
  have h9 : h^9=(d:ℝ)/K := by
    dsimp only [h]
    rw [←rpow_natCast,←rpow_mul (div_nonneg hd'.le hK.le)]
    norm_num
  have hrepr : (d:ℝ)=K*h^9 := by rw [h9]; field_simp
  have hγd := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left ..) hK.le)
  have hr : h≤1/M := by
    have he := (div_le_iff₀ hK).mpr (hsmall.trans
      (mul_le_mul_of_nonneg_right (min_le_right ..) hK.le))
    by_contra! hbad
    exact he.not_gt (h9 ▸ pow_lt_pow_left₀ hbad (one_div_pos.mpr hM').le (by decide : 9≠0))
  have hm : M*h≤1 := by
    have he := (le_div_iff₀ hM').mp hr
    linarith only [he]
  have hden := mul_pos hK (pow_pos hh 20)
  have hscale : Q≤K*h^20 := by
    have he : Q^9≤(K*h^20)^9 := by
      apply le_of_mul_le_mul_right _ (pow_pos hK 11)
      exact hlarge.trans_eq (by rw [hrepr]; ring)
    by_contra! hbad
    exact he.not_gt (pow_lt_pow_left₀ hbad hden.le (by decide : 9≠0))
  have hLo : a/(K*(M*h)^10)=l/(K*h^10) := by dsimp only [l]; field_simp
  have hHi : a/(K*(h/M)^10)=L/(K*h^10) := by dsimp only [L]; field_simp
  have he : K*(a/(K*(h/M)^10))^2≤b := by
    rw [hHi,show K*(L/(K*h^10))^2=L^2/(K*h^20) by field_simp,div_le_iff₀ hden]
    have h' := (div_le_iff₀ hb).mp hscale
    linarith only [h']
  have hσ := hn d h hdn hrepr hγd hh hm he ρ hρ
  change σ∈Icc (a/(K*(M*h)^10)) (a/(K*(h/M)^10)) at hσ
  rw [hLo,hHi] at hσ
  have h₀ := div_pos hl (mul_pos hK (pow_pos hh 10))
  have price (z : ℝ) : (z/(K*h^10))^9*(d:ℝ)^10=z^9*K := by
    rw [hrepr]
    field_simp
  rw [←price l,←price L]
  exact ⟨mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h₀.le hσ.1 9) (pow_nonneg hd'.le _),
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (h₀.le.trans hσ.1) hσ.2 9) (pow_nonneg hd'.le _)⟩

#print axioms gaussian_first_crossing_scale
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit

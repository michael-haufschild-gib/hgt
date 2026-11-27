import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.PrecisionProfile.SweepError

/-! # Residence of a deficient bond sweep at any positive precision -/

open Filter MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section

/-- Prescribing the missing gate count d leaves the whole interval
|t|⁹d¹⁰ ≤ l K affordable. The constant l can be chosen for any
positive error and the allowed range of deficits is independent of it. -/
theorem gaussian_residence_at_precision :
    ∃ γ>0, ∃ Q>0, ∀ ε : ℝ, 0<ε → ∃ l>0,
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
        let K : ℝ := (n+2:ℕ)
        let u := pathPauliDisorderShell ω n
        ∀ d : ℕ, 0<d → (d:ℝ)≤γ*K → Q*K^11≤(d:ℝ)^20 →
          ∀ t : ℝ, |t| ^ 9*(d:ℝ)^10≤l*K →
            HasProjectiveCircuitApproximation (n+2) ε (n+1-d) (unitaryEvolution (pathHamiltonian u) t) := by
  obtain ⟨γ,hγ,Q,hQ,A,hA,B,hB,hw⟩ := gaussian_sweep_error
  let M := max 1 Q
  have hM : 0<M := zero_lt_one.trans_le (le_max_left ..)
  refine ⟨γ^9,pow_pos hγ _,M^9,pow_pos hM _,?_⟩
  intro ε hε
  let a := min 1 (ε/(A+B))
  have ha : 0<a := lt_min zero_lt_one (div_pos hε (add_pos hA hB))
  have hprice := (le_div_iff₀ (add_pos hA hB)).mp (min_le_right (1:ℝ) (ε/(A+B)))
  refine ⟨a^9,pow_pos ha _,?_⟩
  filter_upwards [hw] with ω hw
  filter_upwards [hw] with n hn
  intro K u d hd hdγ hgrid t ht
  have hK : 0<K := by dsimp only [K]; positivity
  have hdp : 0<(d:ℝ) := Nat.cast_pos.mpr hd
  let h := ((d:ℝ)/K)^(1/9:ℝ)
  have hh : 0<h := rpow_pos_of_pos (div_pos hdp hK) _
  have hh9 : h^9=(d:ℝ)/K := by
    dsimp only [h]
    rw [←rpow_natCast,←rpow_mul (div_nonneg hdp.le hK.le)]
    norm_num
  have hd' : (d:ℝ)=K*h^9 := by rw [hh9]; field_simp
  have hr : h≤γ := by
    by_contra! hbad
    exact ((div_le_iff₀ hK).mpr hdγ).not_gt (hh9 ▸ pow_lt_pow_left₀ hbad hγ.le (by decide : 9≠0))
  have hscale : M≤K*h^20 := by
    have he : M^9≤(K*h^20)^9 := by
      apply le_of_mul_le_mul_right _ (pow_pos hK 11)
      exact hgrid.trans_eq (by rw [hd']; ring)
    by_contra! hb
    exact he.not_gt (pow_lt_pow_left₀ hb (mul_nonneg hK.le (pow_nonneg hh.le _)) (by decide : 9≠0))
  let V := K*h^10
  have hspeed : |t| * V≤a := by
    have hs : (|t| * V)^9≤a^9 := by
      apply le_of_mul_le_mul_right _ hK
      apply le_trans _ ht
      rw [hd']
      dsimp only [V]
      exact le_of_eq (by ring)
    by_contra! hb
    exact hs.not_gt (pow_lt_pow_left₀ hb ha.le (by decide : 9≠0))
  have hKV : K≤V^2 := calc
    _ ≤ K*(K*h^20) := le_mul_of_one_le_right hK.le ((le_max_left ..).trans hscale)
    _ = _ := by dsimp only [V]; ring
  have htime : K*t^2≤a := calc
    _ ≤ V^2*t^2 := mul_le_mul_of_nonneg_right hKV (sq_nonneg t)
    _ = (|t| * V)^2 := by rw [mul_pow |t| V,sq_abs,mul_comm]
    _ ≤ a^2 := pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (mul_nonneg hK.le (pow_nonneg hh.le _))) hspeed 2
    _ ≤ a := by simpa only [sq,mul_one] using mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (ε/(A+B))) ha.le
  obtain ⟨z,hz,D,hD,hfit⟩ := hn h hh hr ((le_max_right ..).trans hscale) d hd'.le t
  refine ⟨z,hz,D,hD,hfit.trans ?_⟩
  have hs := mul_le_mul_of_nonneg_left hspeed hA.le
  have hb := mul_le_mul_of_nonneg_left htime hB.le
  change a*(A+B)≤ε at hprice
  change A* |t| * V+B*K*t^2≤ε
  linarith only [hs,hb,hprice]

#print axioms gaussian_residence_at_precision
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit

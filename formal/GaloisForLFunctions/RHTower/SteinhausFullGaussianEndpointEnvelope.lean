import GaloisForLFunctions.RHTower.SteinhausFullGaussianAbsoluteMass

open Complex Filter Topology
noncomputable section
namespace RHTower

private theorem scaled_rpow_identity {x R : ℝ} (hx : 0 < x) (hR : 0 < R) (σ : ℝ) :
    x ^ (σ - 1) * R ^ (-σ) = (x / R) ^ σ / x := by
  rw [Real.rpow_sub hx, Real.rpow_one, Real.rpow_neg hR.le,
    Real.div_rpow hx.le hR.le]
  ring

private theorem scaled_rpow_le_endpoints {x R a b σ : ℝ}
    (hx : 0 < x) (hR : 0 < R) (ha : a ≤ σ) (hb : σ ≤ b) :
    x ^ (σ - 1) * R ^ (-σ) ≤
      x ^ (a - 1) * R ^ (-a) + x ^ (b - 1) * R ^ (-b) := by
  rw [scaled_rpow_identity hx hR, scaled_rpow_identity hx hR,
    scaled_rpow_identity hx hR, ← add_div]
  apply div_le_div_of_nonneg_right _ hx.le
  by_cases hq : 1 ≤ x / R
  · exact (Real.rpow_le_rpow_of_exponent_le hq hb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg (div_pos hx hR).le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge (div_pos hx hR) (le_of_not_ge hq) ha).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (div_pos hx hR).le _))

/-- Two real endpoint masses dominate every intermediate actual normalized coefficient mass. -/
theorem normalizedGaussianAbsoluteMass_le_endpoints {a b σ R : ℝ}
    (hR : 0 < R) (ha : a ≤ σ) (hb : σ ≤ b) :
    normalizedGaussianAbsoluteMass σ R ≤
      normalizedGaussianAbsoluteMass a R + normalizedGaussianAbsoluteMass b R := by
  let u : ℝ → ℕ → ℝ := fun q n =>
    ‖((n + 1 : ℕ) : ℂ) ^ ((q : ℂ) - 1) *
      smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)‖ * R ^ (-q)
  have hsum (q : ℝ) : Summable (u q) := summable_normalizedGaussianAbsoluteTerms q hR
  have heq (q : ℝ) : normalizedGaussianAbsoluteMass q R = ∑' n : ℕ, u q n := by
    exact (tsum_mul_right).symm
  rw [heq σ, heq a, heq b, ← (hsum a).tsum_add (hsum b)]
  apply Summable.tsum_le_tsum _ (hsum σ) ((hsum a).add (hsum b))
  intro n
  have h := mul_le_mul_of_nonneg_right
    (scaled_rpow_le_endpoints (x := (n + 1 : ℝ)) (by positivity) hR ha hb)
    (norm_nonneg (smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)))
  dsimp only [u]
  simp only [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n),
    Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one,
    add_mul, mul_assoc, mul_left_comm, mul_comm] using h

/-- The literal normalized cofactor is eventually bounded on every closed abscissa band
inside the unit strip, uniformly in all imaginary parts, phases, and coherent twists. -/
theorem exists_normalizedFullGaussianCofactor_band_bound
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℝ in atTop, 0 < R ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ∀ (ω : SteinhausModel.Omega) (t : ℝ),
        ‖steinhausFullGaussianCofactor s R ω * (R : ℂ) ^ (-(s + (t : ℂ) * I))‖ ≤ C := by
  let La := (Complex.exp ((a : ℂ) ^ 2) / (a : ℂ)).re
  let Lb := (Complex.exp ((b : ℂ) ^ 2) / (b : ℂ)).re
  have hA : ∀ᶠ R : ℝ in atTop, normalizedGaussianAbsoluteMass a R < La + 1 :=
    (tendsto_normalizedGaussianAbsoluteMass ha (hab.trans_lt hb)).eventually
      (gt_mem_nhds (by dsimp only [La]; linarith))
  have hB : ∀ᶠ R : ℝ in atTop, normalizedGaussianAbsoluteMass b R < Lb + 1 :=
    (tendsto_normalizedGaussianAbsoluteMass (ha.trans_le hab) hb).eventually
      (gt_mem_nhds (by dsimp only [Lb]; linarith))
  refine ⟨|La| + |Lb| + 2, by positivity, ?_⟩
  filter_upwards [hA, hB, eventually_gt_atTop (0 : ℝ)] with R hAR hBR hR
  refine ⟨hR, fun s hsA hsB ω t => ?_⟩
  have hnorm := norm_normalizedFullGaussianCofactor_le_absoluteMass s hR ω t
  have hinter := normalizedGaussianAbsoluteMass_le_endpoints hR hsA hsB
  have hLa := le_abs_self La
  have hLb := le_abs_self Lb
  linarith

end RHTower

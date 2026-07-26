import GaloisForLFunctions.RHTower.GammaCellMobility
import GaloisForLFunctions.RHTower.IntegralFEPolynomial

/-!
# The nonzero degree-zero class acts on the gamma-completed cell

The degree-zero structure theorem discharges the only missing analytic hypothesis in the expected
convolution action.  A nonzero integral multiplicative degree-zero member has finite coefficient
support, hence an everywhere-summable L-series.  It can therefore multiply any member of
`GammaFECell`; the coefficient streams convolve and the completion factors multiply.
-/

open Complex

namespace RHTower

noncomputable section

/-- Finite coefficient support supplies L-series summability at every point. -/
theorem lSeriesSummable_of_finite_coefficient_support {a : ArithmeticFunction ℂ}
    (hfin : (Function.support (fun n => a n)).Finite) (s : ℂ) :
    LSeriesSummable (fun n => a n) s := by
  apply summable_of_ne_finset_zero (s := hfin.toFinset)
  intro n hn
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn0 _ s]
    have ha : a n = 0 := by
      by_contra hane
      exact hn (hfin.mem_toFinset.mpr (Function.mem_support.mpr hane))
    rw [ha]
    simp

/-- Every gamma-cell member is nonzero somewhere.  Its multiplicative coefficient stream has first
coefficient `1` and converges on `Re s > 1`, so its L-series cannot vanish identically there. -/
theorem gammaFECell_exists_ne_zero {f : ℂ → ℂ} (hf : GammaFECell f) :
    ∃ s : ℂ, f s ≠ 0 := by
  obtain ⟨a, ha_mul, _ha_int, ha_summ, ha_rep, _γ, _hγne, _hγfe⟩ := hf
  by_contra hnone
  push Not at hnone
  have hev : (fun x : ℝ => LSeries (fun n => a n) x) =ᶠ[Filter.atTop] 0 := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    simp only [Pi.zero_apply]
    rw [← ha_rep (x : ℂ) (by simpa using hx)]
    exact hnone (x : ℂ)
  rcases LSeries_eventually_eq_zero_iff'.mp hev with hall | htop
  · have h1 := hall 1 one_ne_zero
    rw [ha_mul.map_one] at h1
    exact one_ne_zero h1
  · have hsumm := ha_summ 2 (by norm_num)
    have hle := hsumm.abscissaOfAbsConv_le
    rw [htop] at hle
    simp at hle

/-- The degree-zero functional equation becomes a symmetric completion after multiplication by
`Q^(s-1/2)`. -/
theorem integralFEClass_gamma_completion {g : ℂ → ℂ}
    (hg : IntegralMultiplicativeFEClass g) (s : ℂ) :
    ∃ Q : ℕ, 2 ≤ Q ∧
      ((Q : ℕ) : ℂ) ^ ((1 - s) - 1 / 2) * g (1 - s) =
        ((Q : ℕ) : ℂ) ^ (s - 1 / 2) * g s := by
  obtain ⟨_a, _hmul, _hint, _hrep, Q, hQ, hFE⟩ := hg
  have hQ0 : (((Q : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show Q ≠ 0 by omega)
  refine ⟨Q, hQ, ?_⟩
  rw [hFE (1 - s), show 1 - (1 - s) = s by ring,
    ← mul_assoc, ← Complex.cpow_add _ _ hQ0]
  congr 2
  ring

/-- **Positive degree-zero action theorem.** Every nonzero member of the exact integral
multiplicative degree-zero class acts on `GammaFECell` by multiplication.  Nonzeroness selects the
finite-support branch of the degree-zero structure theorem, so its summability premise follows
automatically. -/
theorem gammaFECell_mul_integralFEClass_of_exists_ne_zero {f g : ℂ → ℂ}
    (hf : GammaFECell f) (hg : IntegralMultiplicativeFEClass g)
    (hgne : ∃ s : ℂ, g s ≠ 0) :
    GammaFECell (fun s => f s * g s) := by
  have hg0 := hg
  obtain ⟨_a0, _ha0mul, _ha0int, _ha0rep, Q, hQ, hFE⟩ := hg
  rcases integralMultiplicativeFEClass_finite_or_zero hg0 with hzero |
      ⟨b, hb_mul, hb_int, hb_rep, hb_fin⟩
  · obtain ⟨s, hs⟩ := hgne
    exact (hs (hzero s)).elim
  · obtain ⟨a, ha_mul, ha_int, ha_summ, ha_rep, γf, hγf_ne, hγf_fe⟩ := hf
    have hb_summ : ∀ s : ℂ, LSeriesSummable (fun n => b n) s :=
      fun s => lSeriesSummable_of_finite_coefficient_support hb_fin s
    have hQ0 : (((Q : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show Q ≠ 0 by omega)
    have hg_fe (s : ℂ) :
        ((Q : ℕ) : ℂ) ^ ((1 - s) - 1 / 2) * g (1 - s) =
          ((Q : ℕ) : ℂ) ^ (s - 1 / 2) * g s := by
      rw [hFE (1 - s), show 1 - (1 - s) = s by ring,
        ← mul_assoc, ← Complex.cpow_add _ _ hQ0]
      congr 2
      ring
    refine ⟨a * b, ha_mul.mul hb_mul,
      intCast_conv_integral a b ha_int hb_int, ?_, ?_,
      fun s => γf s * ((Q : ℕ) : ℂ) ^ (s - 1 / 2), ?_, ?_⟩
    · intro s hs
      exact ArithmeticFunction.LSeriesSummable_mul (ha_summ s hs) (hb_summ s)
    · intro s hs
      show f s * g s = LSeries (fun n => (a * b) n) s
      rw [ArithmeticFunction.LSeries_mul' (ha_summ s hs) (hb_summ s),
        ← ha_rep s hs, ← hb_rep s]
    · intro s hs hs1
      exact mul_ne_zero (hγf_ne s hs hs1)
        (Complex.cpow_ne_zero_iff.mpr (Or.inl hQ0))
    · intro s hs hs1
      show (γf (1 - s) * ((Q : ℕ) : ℂ) ^ ((1 - s) - 1 / 2)) *
          (f (1 - s) * g (1 - s)) =
        (γf s * ((Q : ℕ) : ℂ) ^ (s - 1 / 2)) * (f s * g s)
      calc
        _ = (γf (1 - s) * f (1 - s)) *
            (((Q : ℕ) : ℂ) ^ ((1 - s) - 1 / 2) * g (1 - s)) := by ring
        _ = (γf s * f s) *
            (((Q : ℕ) : ℂ) ^ (s - 1 / 2) * g s) := by
              rw [hγf_fe s hs hs1, hg_fe s]
        _ = _ := by ring

/-- **Exact actor classification.** The universal multiplicative actors on the gamma cell are
precisely the nonzero members of the integral multiplicative degree-zero class. -/
theorem integralFEClass_acts_on_gammaFECell_iff {g : ℂ → ℂ}
    (hg : IntegralMultiplicativeFEClass g) :
    (∃ s : ℂ, g s ≠ 0) ↔
      ∀ f : ℂ → ℂ, GammaFECell f → GammaFECell (fun s => f s * g s) := by
  constructor
  · intro hgne f hf
    exact gammaFECell_mul_integralFEClass_of_exists_ne_zero hf hg hgne
  · intro hact
    have hmember := hact riemannZeta zeta_mem_gammaFECell
    obtain ⟨s, hs⟩ := gammaFECell_exists_ne_zero hmember
    refine ⟨s, ?_⟩
    intro hgs
    exact hs (by simp [hgs])

end

end RHTower

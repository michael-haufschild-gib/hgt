import GaloisForLFunctions.RHTower.CreaseHolonomy
import GaloisForLFunctions.RHTower.HorizontalFibreParity
import GaloisForLFunctions.RHTower.HardyZ

/-!
# From a sign change of Hardy's `Z` to an odd-order critical zero

The seam-parity theorem reads the parity of the enclosed on-line order off the endpoint signs of
`ξ` restricted to the critical line.  An odd total forces one summand to be odd, so a sign flip
produces a *single* critical zero of odd order.  Hardy's `Z` differs from that restriction by a
strictly negative factor, so its sign changes are exactly the seam flips.

Combined with the fibre-parity law, every sign change of `Z` in a window contributes an ordinate to
the odd-fibre count `O(T)` of `HorizontalOddFiberCharging.lean`.  This is the bridge that lets any
sign-change detector — Selberg's, or Levinson's `Re[γ(s)G(s)]` — feed the odd-fibre charging law.
-/

open Complex Set


noncomputable section

namespace RHTower

/-- **A seam sign flip produces an on-line zero of odd order.**  On a critical-line segment with
nonvanishing endpoints, the endpoint sign product is negative exactly when the enclosed on-line
order is odd; an odd total forces one summand to be odd. -/
theorem exists_odd_order_line_zero_of_sign_flip {τ₁ τ₂ : ℝ} (hτ : τ₁ < τ₂)
    (hend₁ : xi (linePt τ₁) ≠ 0) (hend₂ : xi (linePt τ₂) ≠ 0)
    (hsign : (xi (linePt τ₁)).re * (xi (linePt τ₂)).re < 0) :
    ∃ τ' ∈ Set.Ioo τ₁ τ₂, xi (linePt τ') = 0 ∧
      Odd ((analyticOrderAt xi (linePt τ')).toNat) := by
  classical
  set Z : Finset ℝ :=
    ((xi_line_zeros_finite τ₁ τ₂).toFinset).filter (fun t => t ∈ Set.Ioo τ₁ τ₂) with hZdef
  have hZ : ∀ t, t ∈ Z ↔ t ∈ Set.Ioo τ₁ τ₂ ∧ xi (linePt t) = 0 := by
    intro t
    rw [hZdef, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨_, hzero⟩, hio⟩
      exact ⟨hio, hzero⟩
    · rintro ⟨hio, hzero⟩
      exact ⟨⟨⟨hio.1.le, hio.2.le⟩, hzero⟩, hio⟩
  obtain ⟨h, hhan, hhne, hhfact⟩ := xi_line_multi_peel hZ hend₁ hend₂
  have hreal : ∀ u : ℝ, (xi (linePt u)).im = 0 := fESchwarz_real_on_line xi_fESchwarz
  have hlinePtc : Continuous linePt := by
    unfold linePt
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hhcont : Continuous h :=
    continuous_iff_continuousAt.mpr fun x => (hhan x (Set.mem_univ x)).continuousAt
  have hflip := line_sign_flip_iff_odd_total_order
    (f := xi) (h := h) (zs := Z) (m := fun τ' => (analyticOrderAt xi (linePt τ')).toNat)
    (τ₁ := τ₁) (τ₂ := τ₂) hτ
    (fun τ' hτ'z => Set.mem_Ioo.mp ((hZ τ').mp hτ'z).1)
    (fun u _ => hhfact (linePt u)) (hhcont.comp hlinePtc) hhne (fun u _ => hreal u)
  have hodd : Odd (∑ τ' ∈ Z, (analyticOrderAt xi (linePt τ')).toNat) := hflip.mp hsign
  by_contra hcon
  rw [not_exists] at hcon
  have hcon' : ∀ τ', τ' ∈ Set.Ioo τ₁ τ₂ → xi (linePt τ') = 0 →
      ¬ Odd ((analyticOrderAt xi (linePt τ')).toNat) := by
    intro τ' hio hzero hodd'
    exact hcon τ' ⟨hio, hzero, hodd'⟩
  have heven : Even (∑ τ' ∈ Z, (analyticOrderAt xi (linePt τ')).toNat) := by
    refine Finset.even_sum (f := fun τ' : ℝ => (analyticOrderAt xi (linePt τ')).toNat) ?_
    intro τ' hτ'
    obtain ⟨hio, hzero⟩ := (hZ τ').mp hτ'
    exact Nat.not_odd_iff_even.mp (hcon' τ' hio hzero)
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- The real restriction of `ξ` on the critical line is a negative multiple of Hardy's `Z`. -/
theorem re_xi_linePt_eq (τ : ℝ) :
    (xi (linePt τ)).re = (-(1 / 4 + τ ^ 2) / 2) * ‖Gammaℝ (linePt τ)‖ * hardyZ τ := by
  rw [xi_line_eq_scale_mul_hardyZ, Complex.ofReal_re]

theorem re_xi_linePt_scale_pos (τ : ℝ) :
    0 < (1 / 4 + τ ^ 2) / 2 * ‖Gammaℝ (linePt τ)‖ := by
  have hre : (0 : ℝ) < (linePt τ).re := by rw [linePt_re]; norm_num
  have hne : Gammaℝ (linePt τ) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre
  have hpos : 0 < ‖Gammaℝ (linePt τ)‖ := norm_pos_iff.mpr hne
  have : (0 : ℝ) < (1 / 4 + τ ^ 2) / 2 := by positivity
  exact mul_pos this hpos

/-- **A Hardy sign change produces a critical-line zero of odd order.**  Hardy's `Z` differs from
the real restriction of `ξ` by a strictly negative factor, so its sign changes are seam sign flips,
and a seam flip encloses an odd total on-line order. -/
theorem exists_odd_order_line_zero_of_hardyZ_sign_flip {τ₁ τ₂ : ℝ} (hτ : τ₁ < τ₂)
    (hsign : hardyZ τ₁ * hardyZ τ₂ < 0) :
    ∃ τ' ∈ Set.Ioo τ₁ τ₂, xi (linePt τ') = 0 ∧
      Odd ((analyticOrderAt xi (linePt τ')).toNat) := by
  have hZ₁ : hardyZ τ₁ ≠ 0 := by
    intro h; rw [h, zero_mul] at hsign; exact absurd hsign (lt_irrefl 0)
  have hZ₂ : hardyZ τ₂ ≠ 0 := by
    intro h; rw [h, mul_zero] at hsign; exact absurd hsign (lt_irrefl 0)
  have hend₁ : xi (linePt τ₁) ≠ 0 := fun h => hZ₁ ((xi_line_eq_zero_iff_hardyZ τ₁).mp h)
  have hend₂ : xi (linePt τ₂) ≠ 0 := fun h => hZ₂ ((xi_line_eq_zero_iff_hardyZ τ₂).mp h)
  refine exists_odd_order_line_zero_of_sign_flip hτ hend₁ hend₂ ?_
  rw [re_xi_linePt_eq, re_xi_linePt_eq]
  have hs₁ := re_xi_linePt_scale_pos τ₁
  have hs₂ := re_xi_linePt_scale_pos τ₂
  have hrw : ((-(1 / 4 + τ₁ ^ 2) / 2) * ‖Gammaℝ (linePt τ₁)‖ * hardyZ τ₁)
      * ((-(1 / 4 + τ₂ ^ 2) / 2) * ‖Gammaℝ (linePt τ₂)‖ * hardyZ τ₂)
      = ((1 / 4 + τ₁ ^ 2) / 2 * ‖Gammaℝ (linePt τ₁)‖)
        * ((1 / 4 + τ₂ ^ 2) / 2 * ‖Gammaℝ (linePt τ₂)‖) * (hardyZ τ₁ * hardyZ τ₂) := by
    ring
  rw [hrw]
  exact mul_neg_of_pos_of_neg (mul_pos hs₁ hs₂) hsign

end RHTower

end

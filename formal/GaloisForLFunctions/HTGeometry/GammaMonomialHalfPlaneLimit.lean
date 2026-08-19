import GaloisForLFunctions.HTGeometry.GammaMonomialStripLimit
import GaloisForLFunctions.HTGeometry.GammaMonomialOrbitAnalytic
import GaloisForLFunctions.HTGeometry.PeriodicHalfPlaneVanishing

/-!
# The gamma monomial tends to one on the whole half plane

A gamma monomial with real nonnegative shifts, vanishing degree and vanishing first moment satisfies
`M(s) = 1 + O(1/‖s‖)` on a half plane — with no restriction on `Re s`.

The tube limit gives this only on bounded vertical strips.  The upgrade is the orbit limit
`C(s) = lim_n M(s+n)`: it is analytic, `1`-periodic, and within `O(1/‖s‖)` of `M`, so on a strip it
inherits the tube limit and vanishes at height infinity; periodicity spreads that decay across the
whole half plane, and a Liouville-type argument then forces `C ≡ 1`.  Feeding `C ≡ 1` back into the
orbit bound gives the half-plane estimate for `M` itself.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- **The orbit limit of a balanced gamma monomial is identically one.** -/
theorem gammaMonomialOrbitLimit_eq_one {r : ℕ} (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (g : Fin r → ℤ) (hdeg : ∑ i, g i = 0) (hmom : ∑ i, (g i : ℝ) * lam i = 0) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ s : ℂ, R₀ < s.re →
      gammaMonomialOrbitLimit (fun i => ((lam i : ℝ) : ℂ)) g s = 1 := by
  set lamC : Fin r → ℂ := fun i => ((lam i : ℝ) : ℂ) with hlamC
  have hmomC : ∑ i, ((g i : ℤ) : ℂ) * lamC i = 0 := by
    have hcast : ((∑ i, (g i : ℝ) * lam i : ℝ) : ℂ) = 0 := by rw [hmom]; simp
    rw [← hcast, hlamC]
    push_cast
    ring
  obtain ⟨A, Rb₁, hA0, hRb₁, hbound⟩ :=
    norm_gammaMonomialOrbitLimit_sub_le lamC g hdeg hmomC
  obtain ⟨Rb₂, hRb₂, hdiff⟩ := differentiableOn_gammaMonomialOrbitLimit lamC g hdeg hmomC
  obtain ⟨Rb₃, hRb₃, hshift⟩ := gammaMonomialOrbitLimit_shift lamC g hdeg hmomC
  set S : ℝ := ∑ i, |(lamC i).re| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set R₀ : ℝ := max (max S (max Rb₁ (max Rb₂ Rb₃))) 1 with hR₀
  have hR₀1 : 1 ≤ R₀ := le_max_right _ _
  have hSR : S ≤ R₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hb1R : Rb₁ ≤ R₀ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hb2R : Rb₂ ≤ R₀ :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_max_left _ _)
  have hb3R : Rb₃ ≤ R₀ :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_max_left _ _)
  -- On the half plane the real part dominates every threshold.
  have hnorm : ∀ s : ℂ, R₀ < s.re → R₀ < ‖s‖ := by
    intro s hs
    have := Complex.abs_re_le_norm s
    have h2 : s.re ≤ |s.re| := le_abs_self _
    linarith
  set F : ℂ → ℂ := fun s => gammaMonomialOrbitLimit lamC g s - 1 with hF
  have hper : ∀ s : ℂ, R₀ < s.re → F (s + 1) = F s := by
    intro s hs
    have h1 : S < (s + 1).re := by
      rw [Complex.add_re, Complex.one_re]; linarith
    have h2 : Rb₃ ≤ ‖s‖ := le_trans hb3R (le_of_lt (hnorm s hs))
    rw [hF]
    simp only
    rw [hshift s (by linarith) h2]
  have hFdiff : DifferentiableOn ℂ F {s : ℂ | R₀ < s.re} := by
    refine DifferentiableOn.sub ?_ (differentiableOn_const 1)
    refine hdiff.mono fun s hs => ?_
    exact ⟨by simp only [Set.mem_setOf_eq] at hs; linarith,
      lt_of_le_of_lt hb2R (hnorm s (by simpa using hs))⟩
  have hdecay : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ s : ℂ, R₀ < s.re → T ≤ |s.im| → ‖F s‖ ≤ ε := by
    intro ε hε
    obtain ⟨T₁, hT₁⟩ := exists_strip_gammaMonomial_sub_one lam hlam g hdeg hmom
      (M := R₀ + 3) (by linarith) (ε := ε / 2) (by linarith)
    refine ⟨max T₁ (max 1 (2 * A * (1 + ε / 2) / ε)), fun s hs hT => ?_⟩
    obtain ⟨s₀, hs₀l, hs₀u, hs₀im, hs₀F⟩ := exists_block_translate hper s hs
    have hs₀re : R₀ < s₀.re := by linarith
    have hs₀pos : 0 < s₀.re := by linarith
    have hs₀norm : R₀ < ‖s₀‖ := hnorm s₀ hs₀re
    have hTim : max T₁ (max 1 (2 * A * (1 + ε / 2) / ε)) ≤ |s₀.im| := by rw [hs₀im]; exact hT
    have hT1le : T₁ ≤ |s₀.im| := le_trans (le_max_left _ _) hTim
    have hT2le : max 1 (2 * A * (1 + ε / 2) / ε) ≤ |s₀.im| := le_trans (le_max_right _ _) hTim
    have hone : (1 : ℝ) ≤ |s₀.im| := le_trans (le_max_left _ _) hT2le
    have hquot : 2 * A * (1 + ε / 2) / ε ≤ |s₀.im| := le_trans (le_max_right _ _) hT2le
    have hMbound : ‖gammaMonomial lamC g s₀ - 1‖ ≤ ε / 2 :=
      hT₁ s₀ hs₀pos (by linarith) hT1le
    have hMnorm : ‖gammaMonomial lamC g s₀‖ ≤ 1 + ε / 2 := by
      have := norm_sub_norm_le (gammaMonomial lamC g s₀) (1 : ℂ)
      rw [norm_one] at this
      linarith
    have hSs₀ : S < s₀.re := by linarith
    have hb1s₀ : Rb₁ ≤ ‖s₀‖ := le_trans hb1R (le_of_lt hs₀norm)
    have hCb := hbound s₀ hSs₀ hb1s₀
    have hims₀ : |s₀.im| ≤ ‖s₀‖ := Complex.abs_im_le_norm s₀
    have hs₀pos' : (0 : ℝ) < ‖s₀‖ := by linarith
    have hstep : A * ‖gammaMonomial lamC g s₀‖ / ‖s₀‖ ≤ ε / 2 := by
      have hnum : A * ‖gammaMonomial lamC g s₀‖ ≤ A * (1 + ε / 2) :=
        mul_le_mul_of_nonneg_left hMnorm hA0
      have hden : 2 * A * (1 + ε / 2) / ε ≤ ‖s₀‖ := le_trans hquot hims₀
      rw [div_le_iff₀ hs₀pos']
      have hAe : 2 * A * (1 + ε / 2) ≤ ε * ‖s₀‖ := by
        rw [div_le_iff₀ hε] at hden
        linarith
      linarith
    have hfinal : ‖F s₀‖ ≤ ε := by
      rw [hF]
      simp only
      have hsplit : gammaMonomialOrbitLimit lamC g s₀ - 1
          = (gammaMonomialOrbitLimit lamC g s₀ - gammaMonomial lamC g s₀)
            + (gammaMonomial lamC g s₀ - 1) := by ring
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      linarith [le_trans hCb hstep, hMbound]
    rwa [hs₀F] at hfinal
  refine ⟨R₀, hR₀1, fun s hs => ?_⟩
  have hzero := eq_zero_of_periodic_of_vertical_decay hFdiff hper hdecay s hs
  rw [hF] at hzero
  simp only at hzero
  exact sub_eq_zero.mp hzero

/-- **`M(s) = 1 + O(1/‖s‖)` on a half plane**, with no restriction on `Re s`. -/
theorem exists_norm_gammaMonomial_sub_one_le {r : ℕ} (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (g : Fin r → ℤ) (hdeg : ∑ i, g i = 0) (hmom : ∑ i, (g i : ℝ) * lam i = 0) :
    ∃ A R₀ : ℝ, 0 ≤ A ∧ 1 ≤ R₀ ∧ ∀ s : ℂ, R₀ < s.re →
      ‖gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s - 1‖ ≤ A / ‖s‖ := by
  set lamC : Fin r → ℂ := fun i => ((lam i : ℝ) : ℂ) with hlamC
  have hmomC : ∑ i, ((g i : ℤ) : ℂ) * lamC i = 0 := by
    have hcast : ((∑ i, (g i : ℝ) * lam i : ℝ) : ℂ) = 0 := by rw [hmom]; simp
    rw [← hcast, hlamC]
    push_cast
    ring
  obtain ⟨A₁, Rb₁, hA0, hRb₁, hbound⟩ := norm_gammaMonomialOrbitLimit_sub_le lamC g hdeg hmomC
  obtain ⟨R₁, hR₁, hone⟩ := gammaMonomialOrbitLimit_eq_one lam hlam g hdeg hmom
  set S : ℝ := ∑ i, |(lamC i).re| with hS
  set R₀ : ℝ := max (max R₁ (max S Rb₁)) (max 1 (2 * A₁)) with hR₀
  have hR₀1 : 1 ≤ R₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR₁R : R₁ ≤ R₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hSR : S ≤ R₀ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hb1R : Rb₁ ≤ R₀ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have h2AR : 2 * A₁ ≤ R₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨2 * A₁, R₀, by linarith, hR₀1, fun s hs => ?_⟩
  have hnorm : R₀ < ‖s‖ := by
    have h1 := Complex.abs_re_le_norm s
    have h2 : s.re ≤ |s.re| := le_abs_self _
    linarith
  have hspos : (0 : ℝ) < ‖s‖ := by linarith
  have hC1 : gammaMonomialOrbitLimit lamC g s = 1 := hone s (by linarith)
  have hb := hbound s (by linarith) (by linarith)
  rw [hC1] at hb
  have hMn : (0 : ℝ) ≤ ‖gammaMonomial lamC g s‖ := norm_nonneg _
  have hhalf : A₁ / ‖s‖ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hspos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hrw : A₁ * ‖gammaMonomial lamC g s‖ / ‖s‖ = (A₁ / ‖s‖) * ‖gammaMonomial lamC g s‖ := by
    ring
  have hcmp : (A₁ / ‖s‖) * ‖gammaMonomial lamC g s‖ ≤ (1 / 2) * ‖gammaMonomial lamC g s‖ :=
    mul_le_mul_of_nonneg_right hhalf hMn
  have hlow : ‖gammaMonomial lamC g s‖ - 1 ≤ ‖(1 : ℂ) - gammaMonomial lamC g s‖ := by
    have := norm_sub_norm_le (gammaMonomial lamC g s) (1 : ℂ)
    rw [norm_one] at this
    rw [norm_sub_rev]
    linarith
  have hMle : ‖gammaMonomial lamC g s‖ ≤ 2 := by
    rw [hrw] at hb
    linarith [le_trans hlow hb, hcmp]
  rw [norm_sub_rev]
  refine le_trans hb ?_
  rw [div_le_div_iff₀ hspos hspos]
  nlinarith [mul_nonneg (mul_nonneg hA0 hspos.le)
    (by linarith : (0:ℝ) ≤ 2 - ‖gammaMonomial lamC g s‖)]

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.GammaProdRatioTubeLimit
import GaloisForLFunctions.HTGeometry.GammaMonomialShift

/-!
# The gamma monomial tends to one on a vertical strip

A gamma monomial `M(s) = ∏ Γ(s + λ_k)^{g_k}` with real nonnegative shifts, vanishing degree and
vanishing first moment tends to `1` as `|Im s| → ∞`, uniformly for `Re s` in a bounded strip.

This is the tube limit of `GammaProdRatioTubeLimit` rewritten in the monomial language, with the
two-sided statement obtained from the one-sided one by conjugation symmetry.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- Real shifts and integer exponents make the gamma monomial commute with conjugation. -/
theorem gammaMonomial_conj {r : ℕ} (lam : Fin r → ℝ) (g : Fin r → ℤ) (s : ℂ) :
    gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g (starRingEnd ℂ s)
      = starRingEnd ℂ (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s) := by
  rw [gammaMonomial, gammaMonomial, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow₀, ← Complex.Gamma_conj]
  have hconj : (starRingEnd ℂ) s + ((lam i : ℝ) : ℂ)
      = (starRingEnd ℂ) (s + ((lam i : ℝ) : ℂ)) := by simp
  rw [hconj]

/-- Splitting an integer exponent vector into its positive and negative parts. -/
theorem toNat_sub_toNat_neg (n : ℤ) : ((n.toNat : ℤ) - (((-n).toNat : ℤ))) = n := by omega

/-- The ratio of the two gamma products of `GammaProdRatioTubeLimit` is the gamma monomial. -/
theorem gammaProd_ratio_eq_gammaMonomial {r : ℕ} (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (g : Fin r → ℤ) {σ t : ℝ} (hσ : 0 < σ) :
    (∏ i : Fin r, gammaLine (σ + lam i) t ^ ((g i).toNat))
        / (∏ i : Fin r, gammaLine (σ + lam i) t ^ (((-(g i)).toNat)))
      = gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  rw [← Finset.prod_div_distrib, gammaMonomial]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hσi : 0 < σ + lam i := by have := hlam i; linarith
  have hne : gammaLine (σ + lam i) t ≠ 0 := gammaLine_ne_zero hσi t
  have hval : gammaLine (σ + lam i) t
      = Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I + ((lam i : ℝ) : ℂ)) := by
    rw [gammaLine]
    congr 1
    push_cast
    ring
  have hwne : Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I + ((lam i : ℝ) : ℂ)) ≠ 0 := by
    rw [← hval]; exact hne
  rw [hval, ← zpow_natCast _ ((g i).toNat), ← zpow_natCast _ (((-(g i)).toNat)),
    ← zpow_sub₀ hwne, toNat_sub_toNat_neg]

/-- **Uniform convergence to `1` on a vertical strip.** -/
theorem exists_strip_gammaMonomial_sub_one {r : ℕ} (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (g : Fin r → ℤ) (hdeg : ∑ i, g i = 0) (hmom : ∑ i, (g i : ℝ) * lam i = 0)
    {M : ℝ} (hM : 0 < M) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ s : ℂ, 0 < s.re → s.re ≤ M → T ≤ |s.im| →
      ‖gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s - 1‖ ≤ ε := by
  have hef : ∀ i, ((((g i).toNat : ℤ)) - ((((-(g i)).toNat) : ℤ))) = g i := fun i =>
    toNat_sub_toNat_neg (g i)
  have hdeg' : ∑ i, ((((g i).toNat) : ℤ)) = ∑ i, ((((-(g i)).toNat) : ℤ)) := by
    have : ∑ i, (((((g i).toNat) : ℤ)) - ((((-(g i)).toNat) : ℤ))) = 0 := by
      rw [← hdeg]; exact Finset.sum_congr rfl fun i _ => hef i
    rw [Finset.sum_sub_distrib] at this
    linarith
  have hmom' : ∑ i, ((((g i).toNat) : ℝ)) * lam i = ∑ i, ((((-(g i)).toNat) : ℝ)) * lam i := by
    have hstep : ∀ i : Fin r, ((((g i).toNat) : ℝ)) * lam i - ((((-(g i)).toNat) : ℝ)) * lam i
        = (g i : ℝ) * lam i := by
      intro i
      have := hef i
      have hR : ((((g i).toNat) : ℝ)) - ((((-(g i)).toNat) : ℝ)) = (g i : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
      calc ((((g i).toNat) : ℝ)) * lam i - ((((-(g i)).toNat) : ℝ)) * lam i
          = (((((g i).toNat) : ℝ)) - ((((-(g i)).toNat) : ℝ))) * lam i := by ring
        _ = (g i : ℝ) * lam i := by rw [hR]
    have : ∑ i, (((((g i).toNat) : ℝ)) * lam i - ((((-(g i)).toNat) : ℝ)) * lam i) = 0 := by
      rw [← hmom]; exact Finset.sum_congr rfl fun i _ => hstep i
    rw [Finset.sum_sub_distrib] at this
    linarith
  obtain ⟨T₀, hT₀⟩ := tubeLimit_gammaProd_ratio hM lam hlam
    (fun i => (g i).toNat) (fun i => ((-(g i)).toNat)) hdeg' hmom' ε hε
  refine ⟨max T₀ 0, fun s hre hreM him => ?_⟩
  have hT₀le : T₀ ≤ max T₀ 0 := le_max_left _ _
  by_cases hpos : 0 ≤ s.im
  · have hts : max T₀ 0 ≤ s.im := by rwa [abs_of_nonneg hpos] at him
    have h := hT₀ s.re s.im hre hreM (le_trans hT₀le hts)
    dsimp only at h
    rwa [gammaProd_ratio_eq_gammaMonomial (σ := s.re) (t := s.im) lam hlam g hre,
      Complex.re_add_im] at h
  · have hneg : s.im < 0 := by linarith [not_le.mp hpos]
    set s' : ℂ := starRingEnd ℂ s with hs'
    have hre' : s'.re = s.re := by simp [hs']
    have him' : s'.im = -s.im := by simp [hs']
    have hts : max T₀ 0 ≤ s'.im := by
      rw [him']
      rwa [abs_of_neg hneg] at him
    have hre'pos : 0 < s'.re := by rw [hre']; exact hre
    have hre'M : s'.re ≤ M := by rw [hre']; exact hreM
    have h := hT₀ s'.re s'.im hre'pos hre'M (le_trans hT₀le hts)
    dsimp only at h
    rw [gammaProd_ratio_eq_gammaMonomial (σ := s'.re) (t := s'.im) lam hlam g hre'pos,
      Complex.re_add_im] at h
    rw [gammaMonomial_conj lam g s] at h
    have hnorm : ‖(starRingEnd ℂ) (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s) - 1‖
        = ‖gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s - 1‖ := by
      have : (starRingEnd ℂ) (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s) - 1
          = (starRingEnd ℂ) (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s - 1) := by
        simp
      rw [this, RCLike.norm_conj]
    rwa [hnorm] at h

end

end GaloisForLFunctions.HTGeometry

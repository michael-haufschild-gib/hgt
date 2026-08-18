import GaloisForLFunctions.HTGeometry.ArchimedeanNoFlatCancellation

/-!
# The Stirling signature of a finite Gamma product

For `G(s) = e^{αs} s^β ∏_j Γ(λ_j s + μ_j)^{n_j}` the logarithmic derivative is

```text
G'/G(s) = α + β/s + ∑_j n_j λ_j ψ(λ_j s + μ_j),
```

and inserting the affine signature `ψ(λ s + μ) = log λ + log s + (μ−½)/(λ s) + O(|s|⁻²)` gives

```text
G'/G(s) = [α + ∑_j n_j λ_j log λ_j] + [∑_j n_j λ_j] log s
          + [β + ∑_j n_j (μ_j − ½)] / s + O(|s|⁻²).
```

Combined with `three_term_expansion_eq_zero` this separates distinct exponent data: two such
products with the same logarithmic derivative on a real ray have the same signature triple.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

/-- The model logarithmic derivative of a finite shifted-Gamma product. -/
def gammaProductLogDeriv {r : ℕ} (lam : Fin r → ℝ) (mu n : Fin r → ℂ) (al be : ℂ) (s : ℂ) : ℂ :=
  al + be / s + ∑ j, n j * lam j * Complex.digamma ((lam j : ℂ) * s + mu j)

/-- The three signature data: the constant, the `log s` coefficient, and the `1/s` residue. -/
def gammaProductSignature {r : ℕ} (lam : Fin r → ℝ) (mu n : Fin r → ℂ) (al be : ℂ) : ℂ × ℂ × ℂ :=
  (al + ∑ j, n j * lam j * ((Real.log (lam j) : ℝ) : ℂ),
    ∑ j, n j * lam j,
    be + ∑ j, n j * (mu j - 1 / 2))

set_option maxHeartbeats 1000000 in
/-- **The Stirling signature of a finite Gamma product.** -/
theorem exists_norm_gammaProductLogDeriv_expansion_le {r : ℕ} {lam : Fin r → ℝ}
    (hlam : ∀ j, 0 < lam j) (mu n : Fin r → ℂ) (al be : ℂ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ s : ℂ, 0 < s.re →
      (∀ j, 0 < ((lam j : ℂ) * s + mu j).re) → R ≤ ‖s‖ →
      ‖gammaProductLogDeriv lam mu n al be s -
        ((gammaProductSignature lam mu n al be).1
          + (gammaProductSignature lam mu n al be).2.1 * Complex.log s
          + (gammaProductSignature lam mu n al be).2.2 / s)‖
        ≤ C / ‖s‖ ^ 2 := by
  classical
  have hchoice : ∀ j : Fin r, ∃ CR : ℝ × ℝ, 0 ≤ CR.1 ∧ 0 ≤ CR.2 ∧
      ∀ s : ℂ, 0 < s.re → 0 < ((lam j : ℂ) * s + mu j).re → CR.2 ≤ ‖s‖ →
        ‖Complex.digamma ((lam j : ℂ) * s + mu j) -
          (((Real.log (lam j) : ℝ) : ℂ) + Complex.log s + (mu j - 1 / 2) / ((lam j : ℂ) * s))‖
          ≤ CR.1 / ‖s‖ ^ 2 := by
    intro j
    obtain ⟨C, R, hC, hR, hb⟩ := exists_norm_digamma_affine_expansion_le (hlam j) (mu j)
    exact ⟨(C, R), hC, hR, hb⟩
  choose CR hC hR hb using hchoice
  refine ⟨∑ j, ‖n j * (lam j : ℂ)‖ * (CR j).1, ∑ j, (CR j).2,
    Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (hC j),
    Finset.sum_nonneg fun j _ => hR j, fun s hs hre hRle => ?_⟩
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hRj : ∀ j : Fin r, (CR j).2 ≤ ‖s‖ := by
    intro j
    refine le_trans ?_ hRle
    exact Finset.single_le_sum (f := fun i => (CR i).2) (fun i _ => hR i) (Finset.mem_univ j)
  -- the difference is the weighted sum of the per-factor defects
  have hdiff : gammaProductLogDeriv lam mu n al be s -
      ((gammaProductSignature lam mu n al be).1
        + (gammaProductSignature lam mu n al be).2.1 * Complex.log s
        + (gammaProductSignature lam mu n al be).2.2 / s)
      = ∑ j, (n j * (lam j : ℂ)) *
        (Complex.digamma ((lam j : ℂ) * s + mu j) -
          (((Real.log (lam j) : ℝ) : ℂ) + Complex.log s + (mu j - 1 / 2) / ((lam j : ℂ) * s))) := by
    rw [gammaProductLogDeriv, gammaProductSignature]
    have hexpand : ∀ j : Fin r, (n j * (lam j : ℂ)) *
        (Complex.digamma ((lam j : ℂ) * s + mu j) -
          (((Real.log (lam j) : ℝ) : ℂ) + Complex.log s + (mu j - 1 / 2) / ((lam j : ℂ) * s)))
        = n j * (lam j : ℂ) * Complex.digamma ((lam j : ℂ) * s + mu j)
          - n j * (lam j : ℂ) * ((Real.log (lam j) : ℝ) : ℂ)
          - n j * (lam j : ℂ) * Complex.log s
          - n j * (mu j - 1 / 2) / s := by
      intro j
      have hlamne : ((lam j : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact (hlam j).ne'
      field_simp
      ring
    rw [Finset.sum_congr rfl fun j _ => hexpand j]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.sum_div]
    ring
  rw [hdiff]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ j ∈ Finset.univ, ‖(n j * (lam j : ℂ)) *
      (Complex.digamma ((lam j : ℂ) * s + mu j) -
        (((Real.log (lam j) : ℝ) : ℂ) + Complex.log s + (mu j - 1 / 2) / ((lam j : ℂ) * s)))‖
      ≤ ‖n j * (lam j : ℂ)‖ * (CR j).1 / ‖s‖ ^ 2 := by
    intro j _
    rw [norm_mul]
    have hbj := hb j s hs (hre j) (hRj j)
    have hnn : (0 : ℝ) ≤ ‖n j * (lam j : ℂ)‖ := norm_nonneg _
    calc ‖n j * (lam j : ℂ)‖ * ‖Complex.digamma ((lam j : ℂ) * s + mu j) -
          (((Real.log (lam j) : ℝ) : ℂ) + Complex.log s + (mu j - 1 / 2) / ((lam j : ℂ) * s))‖
        ≤ ‖n j * (lam j : ℂ)‖ * ((CR j).1 / ‖s‖ ^ 2) := mul_le_mul_of_nonneg_left hbj hnn
      _ = ‖n j * (lam j : ℂ)‖ * (CR j).1 / ‖s‖ ^ 2 := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_div]

/-! ## Separation of the signature -/

set_option maxHeartbeats 1000000 in
/-- **Distinct signatures are visible.**  Two finite shifted-Gamma products whose logarithmic
derivatives agree along a real ray have the same Stirling signature triple.  This is the
archimedean separation of monomials: no flat cancellation can hide a signature difference. -/
theorem gammaProductSignature_eq_of_logDeriv_eq {r r' : ℕ}
    {lam : Fin r → ℝ} (hlam : ∀ j, 0 < lam j) (mu n : Fin r → ℂ) (al be : ℂ)
    {lam' : Fin r' → ℝ} (hlam' : ∀ j, 0 < lam' j) (mu' n' : Fin r' → ℂ) (al' be' : ℂ)
    (T : ℝ)
    (hEq : ∀ t : ℝ, T ≤ t → 1 ≤ t →
      gammaProductLogDeriv lam mu n al be ((t : ℝ) : ℂ)
        = gammaProductLogDeriv lam' mu' n' al' be' ((t : ℝ) : ℂ)) :
    gammaProductSignature lam mu n al be = gammaProductSignature lam' mu' n' al' be' := by
  classical
  obtain ⟨C₁, R₁, hC₁, hR₁, hb₁⟩ :=
    exists_norm_gammaProductLogDeriv_expansion_le hlam mu n al be
  obtain ⟨C₂, R₂, hC₂, hR₂, hb₂⟩ :=
    exists_norm_gammaProductLogDeriv_expansion_le hlam' mu' n' al' be'
  set S : ℂ × ℂ × ℂ := gammaProductSignature lam mu n al be with hSdef
  set S' : ℂ × ℂ × ℂ := gammaProductSignature lam' mu' n' al' be' with hS'def
  set P : ℝ := ∑ j, (|(mu j).re| + 1) / lam j with hPdef
  set P' : ℝ := ∑ j, (|(mu' j).re| + 1) / lam' j with hP'def
  set Rtot : ℝ := max (max T 1) (max (max R₁ R₂) (max P P')) with hRtotdef
  have hkey : ∀ t : ℝ, Rtot ≤ t → 1 ≤ t →
      ‖(S.1 - S'.1) + (S.2.1 - S'.2.1) * ((Real.log t : ℝ) : ℂ)
        + (S.2.2 - S'.2.2) / ((t : ℝ) : ℂ)‖ ≤ (C₁ + C₂) / t ^ 2 := by
    intro t hRt ht1
    have ht0 : (0 : ℝ) < t := by linarith
    have htT : T ≤ t := le_trans (le_trans (le_max_left T 1) (le_max_left _ _)) hRt
    have htR₁ : R₁ ≤ t :=
      le_trans (le_trans (le_trans (le_max_left R₁ R₂) (le_max_left _ _)) (le_max_right _ _)) hRt
    have htR₂ : R₂ ≤ t :=
      le_trans (le_trans (le_trans (le_max_right R₁ R₂) (le_max_left _ _)) (le_max_right _ _)) hRt
    have htP : P ≤ t :=
      le_trans (le_trans (le_trans (le_max_left P P') (le_max_right _ _)) (le_max_right _ _)) hRt
    have htP' : P' ≤ t :=
      le_trans (le_trans (le_trans (le_max_right P P') (le_max_right _ _)) (le_max_right _ _)) hRt
    have hsre : (0 : ℝ) < (((t : ℝ) : ℂ)).re := by
      rw [Complex.ofReal_re]
      linarith
    have hnorm : ‖((t : ℝ) : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hre : ∀ j : Fin r, 0 < ((lam j : ℂ) * ((t : ℝ) : ℂ) + mu j).re := by
      intro j
      rw [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
      have hle : (|(mu j).re| + 1) / lam j ≤ t := by
        refine le_trans ?_ htP
        rw [hPdef]
        exact Finset.single_le_sum (f := fun i => (|(mu i).re| + 1) / lam i)
          (fun i _ => div_nonneg (by positivity) (hlam i).le) (Finset.mem_univ j)
      rw [div_le_iff₀ (hlam j)] at hle
      nlinarith [neg_abs_le (mu j).re, hle]
    have hre' : ∀ j : Fin r', 0 < ((lam' j : ℂ) * ((t : ℝ) : ℂ) + mu' j).re := by
      intro j
      rw [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
      have hle : (|(mu' j).re| + 1) / lam' j ≤ t := by
        refine le_trans ?_ htP'
        rw [hP'def]
        exact Finset.single_le_sum (f := fun i => (|(mu' i).re| + 1) / lam' i)
          (fun i _ => div_nonneg (by positivity) (hlam' i).le) (Finset.mem_univ j)
      rw [div_le_iff₀ (hlam' j)] at hle
      nlinarith [neg_abs_le (mu' j).re, hle]
    have h1 := hb₁ ((t : ℝ) : ℂ) hsre hre (by rw [hnorm]; exact htR₁)
    have h2 := hb₂ ((t : ℝ) : ℂ) hsre hre' (by rw [hnorm]; exact htR₂)
    rw [hnorm] at h1 h2
    have hlogeq : Complex.log ((t : ℝ) : ℂ) = ((Real.log t : ℝ) : ℂ) :=
      (Complex.ofReal_log ht0.le).symm
    have hEqt := hEq t htT ht1
    have hid : (S.1 - S'.1) + (S.2.1 - S'.2.1) * ((Real.log t : ℝ) : ℂ)
        + (S.2.2 - S'.2.2) / ((t : ℝ) : ℂ)
        = (gammaProductLogDeriv lam' mu' n' al' be' ((t : ℝ) : ℂ) -
            (S'.1 + S'.2.1 * Complex.log ((t : ℝ) : ℂ) + S'.2.2 / ((t : ℝ) : ℂ)))
          - (gammaProductLogDeriv lam mu n al be ((t : ℝ) : ℂ) -
            (S.1 + S.2.1 * Complex.log ((t : ℝ) : ℂ) + S.2.2 / ((t : ℝ) : ℂ))) := by
      rw [hEqt, hlogeq]
      ring
    rw [hid]
    refine le_trans (norm_sub_le _ _) ?_
    have hsum : C₂ / t ^ 2 + C₁ / t ^ 2 = (C₁ + C₂) / t ^ 2 := by ring
    linarith [h1, h2, hsum.le, hsum.ge]
  obtain ⟨ha, hbb, hc⟩ := three_term_expansion_eq_zero (K := C₁ + C₂) (R := Rtot) hkey
  have h1 : S.1 = S'.1 := by linear_combination ha
  have h2 : S.2.1 = S'.2.1 := by linear_combination hbb
  have h3 : S.2.2 = S'.2.2 := by linear_combination hc
  exact Prod.ext h1 (Prod.ext h2 h3)

end

end GaloisForLFunctions.HTGeometry

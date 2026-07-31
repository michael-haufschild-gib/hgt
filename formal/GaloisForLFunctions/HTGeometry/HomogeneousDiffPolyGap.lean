import GaloisForLFunctions.HTGeometry.DifferentialMonomialGapValue
import GaloisForLFunctions.HTGeometry.PolynomialEvalSelector

/-!
# Homogeneous differential polynomials with nonzero leading symbol don't vanish on a gap series

Let `f` be a superlacunary gap series supported on a high tail with infinitely many nonzero
coefficients.  A differential polynomial that is homogeneous of degree `r` and total order `O`
— a finite combination `∑_{μ∈S} c_μ · ∏ₜ f^{(μₜ)}` with every `∑ₜ μₜ = O` — is a nonzero power
series whenever its **leading symbol** `∑_{μ∈S} c_μ · ∏ₜ (X)_{μₜ}` is a nonzero polynomial
(`exists_threshold_homogeneous_diffPoly_gap_ne_zero`).

At the shared balanced index `r·bnat M − O` every monomial reads all source exponents equal to
`bnat M`, so the coefficient is `(coeff (bnat M) f)^r` times the leading symbol evaluated at
`bnat M`.  A nonzero leading symbol is nonzero at infinitely many scales, and infinitely many of
those carry a nonzero series coefficient, so some balanced coefficient is nonzero.
-/

open PowerSeries Filter Finset Polynomial

namespace GaloisForLFunctions

/-- **Homogeneous hypertranscendence witness.**  A homogeneous differential polynomial with
nonzero leading symbol does not vanish on a tail-supported superlacunary gap series. -/
theorem exists_threshold_homogeneous_diffPoly_gap_ne_zero {bnat : ℕ → ℕ}
    (hpos : ∀ᶠ n in atTop, 0 < bnat n)
    (hratio : Tendsto (fun n => (bnat (n + 1) : ℝ) / (bnat n : ℝ)) atTop atTop)
    (hbinj : Function.Injective bnat)
    {r O : ℕ} (S : Finset (Fin r → ℕ)) (hS : ∀ μ ∈ S, ∑ t, μ t = O) (c : (Fin r → ℕ) → ℂ)
    (hLead : (∑ μ ∈ S, c μ • ∏ t, descPochhammer ℂ (μ t)) ≠ 0) :
    ∃ Nstar : ℕ, ∀ f : ℂ⟦X⟧,
      (∀ k, coeff k f ≠ 0 → ∃ n, Nstar ≤ n ∧ k = bnat n) →
      {M | coeff (bnat M) f ≠ 0}.Infinite →
      (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f) ≠ 0 := by
  classical
  choose Nfun hNfun using fun (μ : Fin r → ℕ) =>
    exists_threshold_coeff_balanced_diff_monomial_eq hpos hratio μ
  obtain ⟨N2, _, _, _, hstair⟩ := exists_gap_threshold hpos hratio 0
  set maxJS := S.sup (fun μ => Finset.univ.sup μ) with hmaxJS
  refine ⟨max (S.sup Nfun) (N2 + maxJS), fun f hsupp hinf => ?_⟩
  set Nstar := max (S.sup Nfun) (N2 + maxJS) with hNstar
  set L := ∑ μ ∈ S, c μ • ∏ t, descPochhammer ℂ (μ t) with hL
  have hs' : {M | coeff (bnat M) f ≠ 0 ∧ Nstar ≤ M}.Infinite := by
    have : {M | coeff (bnat M) f ≠ 0} \ Set.Iio Nstar ⊆
        {M | coeff (bnat M) f ≠ 0 ∧ Nstar ≤ M} := by
      rintro M ⟨h1, h2⟩; exact ⟨h1, not_lt.mp h2⟩
    exact (hinf.sdiff (Set.finite_Iio Nstar)).mono this
  obtain ⟨M, ⟨hMne, hMge⟩, hLM⟩ :=
    exists_mem_eval_ne_zero (b := fun n => (bnat n : ℂ)) (Nat.cast_injective.comp hbinj) hLead hs'
  have hNfM : S.sup Nfun ≤ M := le_trans (le_max_left _ _) hMge
  have hbig : N2 + maxJS ≤ M := le_trans (le_max_right _ _) hMge
  have hbM_ge : maxJS ≤ bnat M := by
    have hst := hstair (M - N2); rw [show N2 + (M - N2) = M by omega] at hst; omega
  have hbnatM_ge : ∀ μ ∈ S, ∀ t, μ t ≤ bnat M := fun μ hμ t =>
    le_trans (le_trans (Finset.le_sup (Finset.mem_univ t))
      (Finset.le_sup (f := fun μ => Finset.univ.sup μ) hμ)) hbM_ge
  have hidx : ∀ μ ∈ S, ∑ t, (bnat M - μ t) = r * bnat M - O := by
    intro μ hμ
    have h1 : (∑ t, (bnat M - μ t)) + O = r * bnat M := by
      rw [← hS μ hμ, ← Finset.sum_add_distrib,
        Finset.sum_congr rfl (fun t _ => Nat.sub_add_cancel (hbnatM_ge μ hμ t)),
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hval : ∀ μ ∈ S, coeff (r * bnat M - O) (∏ t, (⇑(d⁄dX ℂ))^[μ t] f)
      = coeff (bnat M) f ^ r * ∏ t, (Nat.descFactorial (bnat M) (μ t) : ℂ) := by
    intro μ hμ
    rw [← hidx μ hμ]
    refine hNfun μ f (fun k hk => ?_) M (le_trans (Finset.le_sup hμ) hNfM)
    obtain ⟨n, hn, hkn⟩ := hsupp k hk
    exact ⟨n, le_trans (le_trans (Finset.le_sup hμ) (le_max_left _ _)) hn, hkn⟩
  have hLeval : L.eval (bnat M : ℂ)
      = ∑ μ ∈ S, c μ * ∏ t, (Nat.descFactorial (bnat M) (μ t) : ℂ) := by
    rw [hL, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_prod]
    refine congrArg _ (Finset.prod_congr rfl fun t _ => ?_)
    exact descPochhammer_eval_eq_descFactorial ℂ (bnat M) (μ t)
  have hPcoeff : coeff (r * bnat M - O) (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f)
      = coeff (bnat M) f ^ r * L.eval (bnat M : ℂ) := by
    rw [map_sum, hLeval, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [map_smul, smul_eq_mul, hval μ hμ]
    ring
  intro hzero
  rw [hzero, map_zero] at hPcoeff
  exact (mul_ne_zero (pow_ne_zero r hMne) hLM) hPcoeff.symm

end GaloisForLFunctions

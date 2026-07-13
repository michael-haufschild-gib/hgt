import GaloisForLFunctions.HTGeometry.HomogeneousDiffPolyGap
import GaloisForLFunctions.HTGeometry.DifferentialMonomialGapVanish
import GaloisForLFunctions.HTGeometry.GapWindowThreshold

/-!
# Degree-homogeneous differential polynomials with a nonzero order-class leading symbol

A differential polynomial homogeneous only in **degree** `r` (arity `r`, arbitrary total orders)
does not vanish on a tail-supported superlacunary gap series once one of its total-order classes
has a nonzero leading symbol (`exists_threshold_degHom_diffPoly_gap_ne_zero`).

At the balanced index `r·bnat M − O₀` for the chosen order `O₀`, the same-degree separation
kills every monomial of total order `≠ O₀`, while the order-`O₀` monomials contribute their
leading-symbol value; a scale where that symbol and the series coefficient are both nonzero
finishes it.
-/

open PowerSeries Filter Finset Polynomial

namespace GaloisForLFunctions

/-- **Degree-homogeneous hypertranscendence witness.** -/
theorem exists_threshold_degHom_diffPoly_gap_ne_zero {bnat : ℕ → ℕ}
    (hpos : ∀ᶠ n in atTop, 0 < bnat n)
    (hratio : Tendsto (fun n => (bnat (n + 1) : ℝ) / (bnat n : ℝ)) atTop atTop)
    (hbmono : Monotone bnat) (hbinj : Function.Injective bnat)
    {r : ℕ} (hr : 0 < r) (O₀ : ℕ) (S : Finset (Fin r → ℕ)) (c : (Fin r → ℕ) → ℂ)
    (hLead : (∑ μ ∈ S.filter (fun μ => ∑ t, μ t = O₀), c μ • ∏ t, descPochhammer ℂ (μ t)) ≠ 0) :
    ∃ Nstar : ℕ, ∀ f : ℂ⟦X⟧,
      (∀ k, coeff k f ≠ 0 → ∃ n, Nstar ≤ n ∧ k = bnat n) →
      {M | coeff (bnat M) f ≠ 0}.Infinite →
      (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f) ≠ 0 := by
  classical
  choose Nfun hNfun using fun (μ : Fin r → ℕ) =>
    exists_threshold_coeff_balanced_diff_monomial_eq hpos hratio μ
  obtain ⟨N2, _, _, _, hstair⟩ := exists_gap_threshold hpos hratio 0
  set Omax := S.sup (fun μ => ∑ t, μ t) with hOmax
  set maxJS := S.sup (fun μ => Finset.univ.sup μ) with hmaxJS
  obtain ⟨Nw, hNw⟩ := exists_threshold_gap_window hpos hratio r Omax
  set S₀ := S.filter (fun μ => ∑ t, μ t = O₀) with hS₀
  set L := ∑ μ ∈ S₀, c μ • ∏ t, descPochhammer ℂ (μ t) with hL
  have hO₀le : O₀ ≤ Omax := by
    obtain ⟨μ₀, hμ₀⟩ := Finset.nonempty_of_sum_ne_zero hLead
    rw [Finset.mem_filter] at hμ₀
    rw [← hμ₀.2]; exact Finset.le_sup hμ₀.1
  refine ⟨max (max (S.sup Nfun) Nw) (N2 + maxJS), fun f hsupp hinf => ?_⟩
  set Nstar := max (max (S.sup Nfun) Nw) (N2 + maxJS) with hNstar
  have hs' : {M | coeff (bnat M) f ≠ 0 ∧ Nstar ≤ M}.Infinite :=
    (hinf.diff (Set.finite_Iio Nstar)).mono (by rintro M ⟨h1, h2⟩; exact ⟨h1, not_lt.mp h2⟩)
  obtain ⟨M, ⟨hMne, hMge⟩, hLM⟩ :=
    exists_mem_eval_ne_zero (b := fun n => (bnat n : ℂ)) (Nat.cast_injective.comp hbinj) hLead hs'
  have hNfM : S.sup Nfun ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMge
  have hNwM : Nw ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMge
  have hbigM : N2 + maxJS ≤ M := le_trans (le_max_right _ _) hMge
  obtain ⟨hgap, hsucc⟩ := hNw M hNwM
  have hbM_ge : maxJS ≤ bnat M := by
    have hs := hstair (M - N2); rw [show N2 + (M - N2) = M by omega] at hs; omega
  have hbnatM_ge : ∀ μ ∈ S, ∀ t, μ t ≤ bnat M := fun μ hμ t =>
    le_trans (le_trans (Finset.le_sup (Finset.mem_univ t))
      (Finset.le_sup (f := fun μ => Finset.univ.sup μ) hμ)) hbM_ge
  have hsumμ_le : ∀ μ ∈ S, ∑ t, μ t ≤ Omax := fun μ hμ => Finset.le_sup hμ
  have hO₀lt : O₀ < bnat M := by omega
  set N := r * bnat M - O₀ with hN
  have hNadd : N + O₀ = r * bnat M := by
    have : O₀ ≤ r * bnat M := le_trans (le_of_lt hO₀lt) (Nat.le_mul_of_pos_left _ hr)
    omega
  -- source-sum for a monomial μ ∈ S at index N
  have hidx : ∀ μ ∈ S, (∑ t, (bnat M - μ t)) + (∑ t, μ t) = r * bnat M := by
    intro μ hμ
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun t _ => Nat.sub_add_cancel (hbnatM_ge μ hμ t)),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- coeff N of P split by order class
  have hPcoeff : coeff N (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f)
      = coeff (bnat M) f ^ r * L.eval (bnat M : ℂ) := by
    rw [map_sum]
    have hLeval : L.eval (bnat M : ℂ)
        = ∑ μ ∈ S₀, c μ * ∏ t, (Nat.descFactorial (bnat M) (μ t) : ℂ) := by
      rw [hL, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_prod]
      exact congrArg _ (Finset.prod_congr rfl fun t _ =>
        descPochhammer_eval_eq_descFactorial ℂ (bnat M) (μ t))
    rw [hLeval, Finset.mul_sum]
    rw [← Finset.sum_filter_add_sum_filter_not S (fun μ => ∑ t, μ t = O₀)]
    have hoff : ∑ μ ∈ S.filter (fun μ => ¬ ∑ t, μ t = O₀),
        coeff N (c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f) = 0 := by
      refine Finset.sum_eq_zero fun μ hμ => ?_
      rw [Finset.mem_filter] at hμ
      obtain ⟨hμS, hμne⟩ := hμ
      rw [map_smul, smul_eq_mul]
      have hsupp' : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n := fun k hk =>
        let ⟨n, _, hkn⟩ := hsupp k hk; ⟨n, hkn⟩
      have hne' : N + ∑ t, μ t ≠ r * bnat M := by
        intro h; apply hμne; omega
      have hub' : N + ∑ t, μ t < bnat (M + 1) := by
        have := hsumμ_le μ hμS; omega
      have hlb' : (r - 1) * bnat M + bnat (M - 1) < N + ∑ t, μ t := by
        have h1 : (r - 1) * bnat M + bnat M = r * bnat M := by
          cases r with
          | zero => omega
          | succ r' => rw [Nat.succ_sub_one, Nat.succ_mul]
        omega
      rw [coeff_prod_iterate_derivative_eq_zero_of_ne hbmono μ hsupp' hlb' hub' hne', mul_zero]
    rw [hoff, add_zero]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [Finset.mem_filter] at hμ
    obtain ⟨hμS, hμO₀⟩ := hμ
    rw [map_smul, smul_eq_mul]
    have hval := hNfun μ f
      (fun k hk => let ⟨n, hn, hkn⟩ := hsupp k hk;
        ⟨n, le_trans (le_trans (Finset.le_sup hμS) (le_trans (le_max_left _ _)
          (le_max_left _ _))) hn, hkn⟩)
      M (le_trans (le_trans (Finset.le_sup hμS) (le_trans (le_max_left _ _) (le_max_left _ _)))
        hMge)
    have hidxμ : ∑ t, (bnat M - μ t) = N := by
      have h := hidx μ hμS; rw [hμO₀] at h; omega
    rw [hidxμ] at hval
    rw [hval]; ring
  intro hzero
  rw [hzero, map_zero] at hPcoeff
  exact (mul_ne_zero (pow_ne_zero r hMne) hLM) hPcoeff.symm

end GaloisForLFunctions

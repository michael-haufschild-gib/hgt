import GaloisForLFunctions.HTGeometry.DifferentialMonomialGapNonzero
import GaloisForLFunctions.HTGeometry.IterateDerivativeFalling

/-!
# The balanced coefficient value of a differential monomial of a gap series

Past a threshold, at the balanced index `r·bnat M − ∑ₜ jₜ` the coefficient of the differential
monomial `∏ₜ f^{(jₜ)}` of a tail-supported superlacunary series equals
`(coeff (bnat M) f)^r · ∏ₜ descFactorial (bnat M) jₜ`
(`exists_threshold_coeff_balanced_diff_monomial_eq`): the source exponents are all `bnat M`, so
each factor reads the same coefficient weighted by the falling factorial of `bnat M` at its
derivative order.  Summed over the monomials of a fixed-degree-and-order differential
polynomial, the shared factor `(coeff (bnat M) f)^r` peels off and the leading-symbol
combination is evaluated at `bnat M`.
-/

open PowerSeries Filter Finset

namespace GaloisForLFunctions

/-- **Exact balanced-coefficient value.**  At the balanced index the differential-monomial
coefficient is `(coeff (bnat M) f)^r` times the product of falling factorials of `bnat M`. -/
theorem exists_threshold_coeff_balanced_diff_monomial_eq {bnat : ℕ → ℕ}
    (hpos : ∀ᶠ n in atTop, 0 < bnat n)
    (hratio : Tendsto (fun n => (bnat (n + 1) : ℝ) / (bnat n : ℝ)) atTop atTop)
    {r : ℕ} (j : Fin r → ℕ) :
    ∃ Nstar : ℕ, ∀ f : ℂ⟦X⟧,
      (∀ k, coeff k f ≠ 0 → ∃ n, Nstar ≤ n ∧ k = bnat n) →
      ∀ M, Nstar ≤ M →
      coeff (∑ t, (bnat M - j t)) (∏ t, (⇑(d⁄dX ℂ))^[j t] f)
        = coeff (bnat M) f ^ r * ∏ t, (Nat.descFactorial (bnat M) (j t) : ℂ) := by
  classical
  have hposR : ∀ᶠ n in atTop, 0 < ((bnat n : ℝ)) := hpos.mono fun n h => by exact_mod_cast h
  obtain ⟨N48, h48⟩ := eventually_balanced_unique_rep hposR hratio r
  obtain ⟨N2, _, _, _, hstair⟩ := exists_gap_threshold hpos hratio 0
  set maxJ := Finset.univ.sup j with hmaxJ
  refine ⟨max N48 (N2 + maxJ), fun f hsupp M hM => ?_⟩
  have hMge2 : N2 + maxJ ≤ M := le_trans (le_max_right _ _) hM
  have hbM_ge : maxJ ≤ bnat M := by
    have hs := hstair (M - N2)
    rw [show N2 + (M - N2) = M by omega] at hs
    omega
  have hjle : ∀ t, j t ≤ bnat M := fun t => le_trans (Finset.le_sup (Finset.mem_univ t)) hbM_ge
  set l0 : Fin r →₀ ℕ :=
    Finsupp.onFinset Finset.univ (fun t => bnat M - j t) (fun a _ => Finset.mem_univ a) with hl0
  have hl0app : ∀ t, l0 t = bnat M - j t := fun t => by rw [hl0, Finsupp.onFinset_apply]
  set N := ∑ t, (bnat M - j t) with hN
  have hl0mem : l0 ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N := by
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨by rw [Finset.sum_congr rfl (fun t _ => hl0app t)], Finsupp.support_onFinset_subset⟩
  have hNsum : N + ∑ t, j t = r * bnat M := by
    rw [hN, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun t _ => Nat.sub_add_cancel (hjle t)),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have huniq : ∀ l ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N, l ≠ l0 →
      ∃ t, coeff (l t + j t) f = 0 := by
    intro l hl hne
    by_contra hcon
    push Not at hcon
    apply hne
    choose nt hnt hbnt using fun t => hsupp (l t + j t) (hcon t)
    have hsum_nat : ∑ t, bnat (nt t) = N + ∑ t, j t := by
      have e1 : ∑ t, bnat (nt t) = ∑ t, (l t + j t) :=
        Finset.sum_congr rfl (fun t _ => (hbnt t).symm)
      rw [e1, Finset.sum_add_distrib]
      congr 1
      rw [Finset.mem_finsuppAntidiag] at hl
      exact hl.1
    have hcast : ∑ t, ((bnat (nt t) : ℝ)) = (r : ℝ) * (bnat M : ℝ) := by
      rw [← Nat.cast_sum, hsum_nat, hNsum]; push_cast; ring
    have hall := h48 M nt (le_trans (le_max_left _ _) hM)
      (fun t => le_trans (le_max_left _ _) (hnt t)) hcast
    ext t
    rw [hl0app t]
    have hbM : l t + j t = bnat M := by rw [hbnt t, hall t]
    omega
  rw [coeff_prod_iterate_derivative_of_unique j f N l0 hl0mem huniq]
  have hfac : ∀ t, coeff (l0 t + j t) f * ∏ i ∈ Finset.range (j t), ((l0 t + 1 + i : ℕ) : ℂ)
      = coeff (bnat M) f * (Nat.descFactorial (bnat M) (j t) : ℂ) := by
    intro t
    have hsource : l0 t + j t = bnat M := by rw [hl0app t, Nat.sub_add_cancel (hjle t)]
    rw [← Nat.cast_prod, prod_range_succ_add_eq_descFactorial, hsource]
  rw [Finset.prod_congr rfl (fun t _ => hfac t), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

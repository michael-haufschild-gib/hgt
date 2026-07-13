import GaloisForLFunctions.HTGeometry.DifferentialMonomialUnique
import GaloisForLFunctions.HTGeometry.BalancedCoefficient

/-!
# A differential monomial of a superlacunary gap series is nonzero

For an integer exponent sequence with divergent ratio, past a per-monomial threshold every
power series supported on the tail exponents (with a nonzero coefficient there) has every
differential monomial `∏ₜ f^{(jₜ)}` nonzero as a power series
(`exists_threshold_diff_monomial_gap_ne_zero`).

At the balanced coefficient index `N = ∑ₜ(bnat M − jₜ)` the source exponents are forced to be
all `bnat M`: any other antidiagonal tuple would represent `r·bnat M` as a sum of `r` tail
exponents in a second way, contradicting the balanced-representation uniqueness.  Because the
source is a tail exponent, its index is automatically past the uniqueness threshold, so no
small-index analysis is needed.  The unique surviving term is a product of nonzero coefficients
and nonzero rising-factorial weights.
-/

open PowerSeries Filter Finset

namespace GaloisForLFunctions

/-- **Differential-monomial nonvanishing for gap series.**  Past a threshold depending on the
exponent sequence and the derivative orders, a differential monomial of a tail-supported
superlacunary series is a nonzero power series. -/
theorem exists_threshold_diff_monomial_gap_ne_zero {bnat : ℕ → ℕ}
    (hpos : ∀ᶠ n in atTop, 0 < bnat n)
    (hratio : Tendsto (fun n => (bnat (n + 1) : ℝ) / (bnat n : ℝ)) atTop atTop)
    {r : ℕ} (j : Fin r → ℕ) :
    ∃ Nstar : ℕ, ∀ f : ℂ⟦X⟧,
      (∀ k, coeff k f ≠ 0 → ∃ n, Nstar ≤ n ∧ k = bnat n) →
      (∃ m, Nstar ≤ m ∧ coeff (bnat m) f ≠ 0) →
      (∏ t, (⇑(d⁄dX ℂ))^[j t] f) ≠ 0 := by
  classical
  have hposR : ∀ᶠ n in atTop, 0 < ((bnat n : ℝ)) := hpos.mono fun n h => by exact_mod_cast h
  obtain ⟨N48, h48⟩ := eventually_balanced_unique_rep hposR hratio r
  obtain ⟨N2, _, _, _, hstair⟩ := exists_gap_threshold hpos hratio 0
  set maxJ := Finset.univ.sup j with hmaxJ
  refine ⟨max N48 (N2 + maxJ), fun f hsupp hnz => ?_⟩
  obtain ⟨M, hM, hMne⟩ := hnz
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
    refine ⟨?_, Finsupp.support_onFinset_subset⟩
    show (∑ t ∈ Finset.univ, l0 t) = N
    rw [Finset.sum_congr rfl (fun t _ => hl0app t)]
  have hl0ne : ∀ t, coeff (l0 t + j t) f ≠ 0 := by
    intro t
    rw [hl0app t, Nat.sub_add_cancel (hjle t)]
    exact hMne
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
    have hMN48 : N48 ≤ M := le_trans (le_max_left _ _) hM
    have hntN48 : ∀ t, N48 ≤ nt t := fun t => le_trans (le_max_left _ _) (hnt t)
    have hall := h48 M nt hMN48 hntN48 hcast
    ext t
    rw [hl0app t]
    have hbM : l t + j t = bnat M := by rw [hbnt t, hall t]
    omega
  intro hzero
  exact coeff_prod_iterate_derivative_ne_zero_of_unique j f N l0 hl0mem hl0ne huniq
    (by rw [hzero, map_zero])

end GaloisForLFunctions

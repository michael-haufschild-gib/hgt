import GaloisForLFunctions.MagnitudeConvolutionExtraction
import GaloisForLFunctions.MagnitudeBalancedGap
import GaloisForLFunctions.ArchimedeanValuationGap

/-!
# Full-support magnitude survival of a single differential monomial

For a full-support power series `f` whose coefficient magnitudes `b n = -log‖coeff n f‖` are
superlacunary (`b(n+1)/b n → ∞`), the differential monomial `∏ₜ f^{(jₜ)}` has a **nonzero**
coefficient at the balanced position `r·M − ∑ j` for every large `M`.

The `N`-th coefficient is the antidiagonal convolution (`coeff_prod_iterate_deriv`); its terms carry
integer falling-factorial weights `∏ₜ descFactorial(kₜ, jₜ)`.  At `N = r·M − ∑ j` the balanced source
tuple `(M,…,M)` has a nonzero weight and, by the quantitative valuation gap
(`tuple_valuation_gap_lower`), strictly dominates every other atom once the superlacunary growth
outpaces the polynomial atom count (`exists_dominates_log`).  The Archimedean integer bend
(`sum_ne_zero_of_valuation_gap`) then forbids cancellation.  No integer normalization of the ambient
differential equation is needed: the gap is supplied by the magnitudes, the weight by combinatorics.
-/

open PowerSeries Finset Filter
open scoped Nat

namespace GaloisForLFunctions

/-- The finite antidiagonal of tuples `Fin r →₀ ℕ` summing to `N` has at most `(N+1)^r` elements
(each coordinate is bounded by `N`). -/
theorem antidiag_card_le {r N : ℕ} :
    ((Finset.univ : Finset (Fin r)).finsuppAntidiag N).card ≤ (N + 1) ^ r := by
  classical
  have hmaps : Set.MapsTo (fun l : Fin r →₀ ℕ => (fun t => l t : Fin r → ℕ))
      ((Finset.univ : Finset (Fin r)).finsuppAntidiag N)
      (Fintype.piFinset (fun _ : Fin r => Finset.range (N + 1))) := by
    intro l hl
    rw [Finset.mem_coe, Finset.mem_finsuppAntidiag] at hl
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro t; rw [Finset.mem_range]
    exact Nat.lt_succ_of_le
      (hl.1 ▸ Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ t))
  have hinj : Set.InjOn (fun l : Fin r →₀ ℕ => (fun t => l t : Fin r → ℕ))
      ((Finset.univ : Finset (Fin r)).finsuppAntidiag N) :=
    fun l1 _ l2 _ heq => DFunLike.coe_injective heq
  calc ((Finset.univ : Finset (Fin r)).finsuppAntidiag N).card
      ≤ (Fintype.piFinset (fun _ : Fin r => Finset.range (N + 1))).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (N + 1) ^ r := by rw [Fintype.card_piFinset]; simp

/-- **Single-monomial full-support magnitude survival.**  For a full-support series `f` with
superlacunary magnitudes `b n = -log‖coeff n f‖`, the differential monomial `∏ₜ f^{(jₜ)}` has a
nonzero coefficient at the balanced position `r·M − ∑ j` for all large `M`. -/
theorem coeff_diffMonomial_balanced_ne_zero {f : ℂ⟦X⟧} {b : ℕ → ℝ}
    (hb : ∀ n, ‖(coeff n) f‖ = Real.exp (- b n))
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop)
    {r : ℕ} (hr : 0 < r) (j : Fin r → ℕ) :
    ∃ Nstar : ℕ, ∀ M : ℕ, Nstar ≤ M →
      (coeff (r * M - ∑ t, j t)) (∏ t, (⇑(d⁄dX ℂ))^[j t] f) ≠ 0 := by
  classical
  obtain ⟨Ng, m₀, hm₀, hgapP2⟩ := tuple_valuation_gap_lower hpos hratio hr
  set sj : ℕ := ∑ t, j t with hsj
  obtain ⟨Nd, hNd⟩ := exists_dominates_log hpos hratio (2 * ((r : ℝ) + sj))
    (2 * ((r : ℝ) + sj) * Real.log ((r : ℝ) + 1) - ((r : ℝ) - 1) * m₀ + 1)
  set maxJ := Finset.univ.sup j with hmaxJ
  refine ⟨max (max Ng Nd) maxJ, fun M hM => ?_⟩
  have hMj : ∀ t, j t ≤ M := fun t =>
    le_trans (Finset.le_sup (Finset.mem_univ t)) (le_trans (le_max_right _ _) hM)
  have hMg : Ng ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMd : Nd ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  set N : ℕ := r * M - sj with hN
  set s := (Finset.univ : Finset (Fin r)).finsuppAntidiag N with hs
  set cW : (Fin r →₀ ℕ) → ℤ := fun l => ((∏ t, (l t + j t).descFactorial (j t) : ℕ) : ℤ) with hcW
  set xA : (Fin r →₀ ℕ) → ℂ := fun l => ∏ t, (coeff (l t + j t)) f with hxA
  set V : (Fin r →₀ ℕ) → ℝ := fun l => ∑ t, b (l t + j t) with hV
  have hsjle : sj ≤ r * M := by
    calc sj = ∑ t, j t := hsj
      _ ≤ ∑ _t : Fin r, M := Finset.sum_le_sum (fun t _ => hMj t)
      _ = r * M := by simp [Finset.card_univ]
  have hcoeff : (coeff N) (∏ t, (⇑(d⁄dX ℂ))^[j t] f) = ∑ l ∈ s, (cW l : ℂ) * xA l := by
    rw [coeff_prod_iterate_deriv f j N]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.prod_mul_distrib, hcW, hxA]; push_cast; ring
  rw [hcoeff]
  have hktle : ∀ l ∈ s, ∀ t, l t + j t ≤ r * M := by
    intro l hl t
    rw [hs, Finset.mem_finsuppAntidiag] at hl
    have hlt : l t ≤ N := hl.1 ▸ Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ t)
    have hjt : j t ≤ sj := hsj ▸ Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ t)
    omega
  set l₀ : Fin r →₀ ℕ := Finsupp.onFinset Finset.univ (fun t => M - j t)
    (fun a _ => Finset.mem_univ a) with hl0
  have hl0app : ∀ t, l₀ t = M - j t := fun t => Finsupp.onFinset_apply
  have hl0shift : ∀ t, l₀ t + j t = M := fun t => by have := hMj t; rw [hl0app]; omega
  have hl0mem : l₀ ∈ s := by
    rw [hs, Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finsupp.support_onFinset_subset⟩
    rw [Finset.sum_congr rfl (fun t _ => hl0app t)]
    have hsum : (∑ t, (M - j t)) + sj = r * M := by
      rw [hsj, ← Finset.sum_add_distrib,
        Finset.sum_congr rfl (fun t _ => Nat.sub_add_cancel (hMj t))]
      simp [Finset.card_univ]
    omega
  have hc : cW l₀ ≠ 0 := by
    rw [hcW, Int.natCast_ne_zero, Finset.prod_ne_zero_iff]
    intro t _
    rw [hl0shift t]
    exact fun h => absurd (Nat.descFactorial_eq_zero_iff_lt.mp h) (Nat.not_lt.mpr (hMj t))
  have hnorm : ∀ l ∈ s, ‖xA l‖ = Real.exp (- V l) := by
    intro l _
    rw [hxA, norm_prod, hV, neg_eq_neg_one_mul, Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_congr rfl fun t _ => by rw [hb (l t + j t)]; ring_nf
  have hVl0 : V l₀ = (r : ℝ) * b M := by
    show (∑ t, b (l₀ t + j t)) = (r : ℝ) * b M
    rw [Finset.sum_congr rfl (fun t _ => by rw [hl0shift t])]
    simp [Finset.card_univ]
  set B : ℝ := (((r * M + 1) ^ (r + sj) : ℕ) : ℝ) with hB
  have hBge1 : 1 ≤ B := by rw [hB]; exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have hcard : (s.card : ℝ) ≤ B := by
    rw [hB]; refine Nat.cast_le.mpr (le_trans (hs ▸ antidiag_card_le) ?_)
    calc (N + 1) ^ r ≤ (r * M + 1) ^ r := Nat.pow_le_pow_left (by omega) r
      _ ≤ (r * M + 1) ^ (r + sj) := Nat.pow_le_pow_right (by omega) (by omega)
  have hcB : ∀ l ∈ s, ‖(cW l : ℂ)‖ ≤ B := by
    intro l hl
    rw [hcW, hB]
    have hnat : (∏ t, (l t + j t).descFactorial (j t)) ≤ (r * M + 1) ^ (r + sj) := by
      calc (∏ t, (l t + j t).descFactorial (j t))
          ≤ ∏ t, (l t + j t) ^ (j t) :=
            Finset.prod_le_prod' (fun t _ => Nat.descFactorial_le_pow _ _)
        _ ≤ ∏ t, (r * M + 1) ^ (j t) :=
            Finset.prod_le_prod' (fun t _ => Nat.pow_le_pow_left (by have := hktle l hl t; omega) _)
        _ = (r * M + 1) ^ (∑ t, j t) := by rw [Finset.prod_pow_eq_pow_sum]
        _ ≤ (r * M + 1) ^ (r + sj) := Nat.pow_le_pow_right (by omega) (by rw [← hsj]; omega)
    calc ‖((((∏ t, (l t + j t).descFactorial (j t) : ℕ)) : ℤ) : ℂ)‖
        = ((∏ t, (l t + j t).descFactorial (j t) : ℕ) : ℝ) := by
          rw [Int.cast_natCast, Complex.norm_natCast]
      _ ≤ (((r * M + 1) ^ (r + sj) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hlogfact : 2 * Real.log B ≤ 2 * ((r : ℝ) + sj) * Real.log ((M : ℝ) + 2)
      + 2 * ((r : ℝ) + sj) * Real.log ((r : ℝ) + 1) := by
    have hlogB : Real.log B = ((r : ℝ) + sj) * Real.log ((r : ℝ) * M + 1) := by
      rw [hB]; push_cast [Real.log_pow]; ring
    have hlogle : Real.log ((r : ℝ) * M + 1) ≤ Real.log ((r : ℝ) + 1) + Real.log ((M : ℝ) + 2) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      apply Real.log_le_log (by positivity)
      nlinarith [Nat.cast_nonneg r (α := ℝ), Nat.cast_nonneg M (α := ℝ)]
    nlinarith [hlogB, hlogle, mul_le_mul_of_nonneg_left hlogle
      (by positivity : (0 : ℝ) ≤ 2 * ((r : ℝ) + sj))]
  have hgap : ∀ l ∈ s, l ≠ l₀ → V l₀ + 2 * Real.log B < V l := by
    intro l hl hne
    have hksum : (∑ t, (l t + j t)) = r * M := by
      rw [Finset.sum_add_distrib]
      rw [hs, Finset.mem_finsuppAntidiag] at hl
      rw [hl.1, ← hsj]; omega
    have hkne : ∃ t, (l t + j t) ≠ M := by
      by_contra h; simp only [not_exists, not_ne_iff] at h
      exact hne (by ext t; have := h t; have := hMj t; rw [hl0app]; omega)
    have hbig : ((r : ℝ) + 1) * b M + ((r : ℝ) - 1) * m₀ ≤ V l := by
      show ((r : ℝ) + 1) * b M + ((r : ℝ) - 1) * m₀ ≤ ∑ t, b (l t + j t)
      exact hgapP2 M hMg (fun t => l t + j t) hksum hkne
    have hdom := hNd M hMd
    rw [hVl0]
    nlinarith [hlogfact, hbig, hdom]
  exact sum_ne_zero_of_valuation_gap s cW xA hl0mem hc V hnorm B hBge1 hcB hcard hgap

end GaloisForLFunctions

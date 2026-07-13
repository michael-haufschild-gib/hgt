import GaloisForLFunctions.HTGeometry.MagnitudeConvolutionExtraction
import GaloisForLFunctions.HTGeometry.MagnitudeBalancedGap

/-!
# First-order jet linear independence for superlacunary magnitudes

For a full-support series `F` whose coefficient magnitudes `b n = -log‖coeff n F‖` are superlacunary,
the derivative jets `F, F', …, F⁽ᵐ⁾` are `ℂ`-linearly independent (`jets_linearIndependent`): no
nonzero constant-coefficient first-order algebraic differential equation annihilates `F`.  At a
coefficient index `K + jmin` (the lowest active jet order) that jet term strictly dominates every
higher-order term, whose relative falling-factorial-weighted magnitude vanishes
(`jet_ratio_tendsto_zero`); a reverse-triangle estimate then keeps the coefficient nonzero.
-/

open PowerSeries Filter
open scoped Nat

namespace GaloisForLFunctions

theorem jet_term_le {F : ℂ⟦X⟧} {b : ℕ → ℝ} (hb : ∀ n, ‖(coeff n) F‖ = Real.exp (- b n))
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) (jmin j : ℕ) (hlt : jmin < j) :
    ∀ᶠ N in atTop, ‖(coeff (N + j)) F‖ * (((N + j).descFactorial j : ℕ) : ℝ)
      ≤ ‖(coeff (N + jmin)) F‖ * ((((N + j) ^ j : ℕ) : ℝ) * Real.exp (- b (N + jmin))) := by
  have h2b : ∀ᶠ N in atTop, 2 * b (N + jmin) ≤ b (N + j) := by
    have h2 : ∀ᶠ n in atTop, (2:ℝ) ≤ b (n+1) / b n := hratio.eventually_ge_atTop 2
    obtain ⟨Nm, hmono⟩ := exists_eventually_monotone hpos hratio
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hpos.and h2)
    refine Filter.eventually_atTop.mpr ⟨max Nm N2, fun N hN => ?_⟩
    have hbase : 2 * b (N + jmin) ≤ b (N + jmin + 1) := by
      obtain ⟨hbp, hr⟩ := hN2 (N + jmin) (by have : N2 ≤ N := le_trans (le_max_right _ _) hN; omega)
      rw [le_div_iff₀ hbp] at hr; linarith
    have hstep : b (N + jmin + 1) ≤ b (N + j) :=
      hmono (N + jmin + 1) (N + j) (by have : Nm ≤ N := le_trans (le_max_left _ _) hN; omega) (by omega)
    linarith
  filter_upwards [h2b] with N hN2b
  rw [hb, hb]
  have hdesc : ((N + j).descFactorial j : ℝ) ≤ (((N + j) ^ j : ℕ) : ℝ) := by
    exact_mod_cast Nat.descFactorial_le_pow _ _
  have hexp : Real.exp (- b (N + j)) ≤ Real.exp (- b (N + jmin)) * Real.exp (- b (N + jmin)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
  calc Real.exp (- b (N + j)) * ((N + j).descFactorial j : ℝ)
      ≤ (Real.exp (- b (N + jmin)) * Real.exp (- b (N + jmin))) * (((N + j) ^ j : ℕ) : ℝ) := by
        apply mul_le_mul hexp hdesc (by positivity) (by positivity)
    _ = Real.exp (- b (N + jmin)) * ((((N + j) ^ j : ℕ) : ℝ) * Real.exp (- b (N + jmin))) := by ring

/-- **First-order jet independence.**  For a full-support superlacunary series `F`, the derivative
jets `F, F', …, F⁽ᵐ⁾` are `ℂ`-linearly independent: no nonzero constant-coefficient first-order ADE
annihilates `F`.  At a coefficient index `N + jmin` (lowest active order) the jet term dominates all
higher-order terms, whose relative magnitude vanishes (`jet_ratio_tendsto_zero`). -/
theorem jets_linearIndependent {F : ℂ⟦X⟧} {b : ℕ → ℝ} (hb : ∀ n, ‖(coeff n) F‖ = Real.exp (- b n))
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) (m : ℕ) :
    LinearIndependent ℂ (fun j : Fin (m + 1) => (⇑(d⁄dX ℂ))^[(j : ℕ)] F) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hcne
  rw [not_forall] at hcne
  obtain ⟨i0, hi0⟩ := hcne
  set S := Finset.univ.filter (fun i : Fin (m + 1) => c i ≠ 0) with hSdef
  have hSne : S.Nonempty := ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ i0, hi0⟩⟩
  set jm := S.min' hSne with hjmdef
  have hjmS : jm ∈ S := S.min'_mem hSne
  have hcjm : c jm ≠ 0 := (Finset.mem_filter.mp hjmS).2
  have hcjmpos : 0 < ‖c jm‖ := norm_pos_iff.mpr hcjm
  have hFpos : ∀ n, 0 < ‖(coeff n) F‖ := fun n => by rw [hb]; exact Real.exp_pos _
  have hcoeff : ∀ K, ∑ i : Fin (m + 1),
      c i * ((coeff (K + (i:ℕ))) F * (((K + (i:ℕ)).descFactorial (i:ℕ) : ℕ) : ℂ)) = 0 := by
    intro K
    have h0 := congrArg (coeff K) hc
    rw [map_sum, map_zero] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul, smul_eq_mul, coeff_iterate_deriv F (i:ℕ) K]
  -- higher-order indices
  set T := Finset.univ.filter (fun i : Fin (m + 1) => jm < i) with hTdef
  -- the sum of higher relative magnitudes tends to 0
  have hsum0 : Tendsto (fun K => ∑ i ∈ T, ‖c i‖ *
      ((((K + (i:ℕ)) ^ (i:ℕ) : ℕ) : ℝ) * Real.exp (- b (K + (jm:ℕ))))) atTop (nhds 0) := by
    have : (0:ℝ) = ∑ i ∈ T, ‖c i‖ * 0 := by simp
    rw [this]
    apply tendsto_finsetSum
    intro i hi
    exact (jet_ratio_tendsto_zero hpos hratio (jm:ℕ) (i:ℕ)).const_mul (‖c i‖)
  have hdom : ∀ᶠ K in atTop, ∑ i ∈ T, ‖c i‖ *
      ((((K + (i:ℕ)) ^ (i:ℕ) : ℕ) : ℝ) * Real.exp (- b (K + (jm:ℕ)))) < ‖c jm‖ :=
    hsum0.eventually_lt_const hcjmpos
  -- also each higher term is bounded (jet_term_le), gathered eventually
  have hterms : ∀ᶠ K in atTop, ∀ i ∈ T, ‖(coeff (K + (i:ℕ))) F‖ * (((K + (i:ℕ)).descFactorial (i:ℕ) : ℕ) : ℝ)
      ≤ ‖(coeff (K + (jm:ℕ))) F‖ * ((((K + (i:ℕ)) ^ (i:ℕ) : ℕ) : ℝ) * Real.exp (- b (K + (jm:ℕ)))) := by
    rw [eventually_all_finset]
    intro i hi
    exact jet_term_le hb hpos hratio (jm:ℕ) (i:ℕ) (by simpa [hTdef] using (Finset.mem_filter.mp hi).2)
  obtain ⟨K, hKdom, hKterms⟩ := (hdom.and hterms).exists
  have hTsub : T ⊆ Finset.univ.erase jm := by
    intro i hi
    have hlt : jm < i := by simpa [hTdef] using (Finset.mem_filter.mp hi).2
    exact Finset.mem_erase.mpr ⟨(ne_of_lt hlt).symm, Finset.mem_univ i⟩
  set g : Fin (m + 1) → ℂ := fun i =>
    c i * ((coeff (K + (i:ℕ))) F * (((K + (i:ℕ)).descFactorial (i:ℕ) : ℕ) : ℂ)) with hgdef
  set R : Fin (m + 1) → ℝ := fun i =>
    (((K + (i:ℕ)) ^ (i:ℕ) : ℕ) : ℝ) * Real.exp (- b (K + (jm:ℕ))) with hRdef
  have hczero : ∀ i, i ∉ T → i ≠ jm → c i = 0 := by
    intro i hiT hijm
    by_contra hci
    have hle : jm ≤ i := S.min'_le i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hci⟩)
    exact hiT (by simpa [hTdef] using lt_of_le_of_ne hle (Ne.symm hijm))
  have hgnorm : ∀ i, ‖g i‖
      = ‖c i‖ * (‖(coeff (K + (i:ℕ))) F‖ * (((K + (i:ℕ)).descFactorial (i:ℕ) : ℕ) : ℝ)) := by
    intro i; rw [hgdef]; simp only [norm_mul, Complex.norm_natCast]
  have hperbound : ∀ i ∈ Finset.univ.erase jm, ‖g i‖ ≤ ‖(coeff (K + (jm:ℕ))) F‖ * (‖c i‖ * R i) := by
    intro i hi
    by_cases hiT : i ∈ T
    · rw [hgnorm, hRdef]
      calc ‖c i‖ * (‖(coeff (K + (i:ℕ))) F‖ * (((K + (i:ℕ)).descFactorial (i:ℕ) : ℕ) : ℝ))
          ≤ ‖c i‖ * (‖(coeff (K + (jm:ℕ))) F‖
              * ((((K + (i:ℕ)) ^ (i:ℕ) : ℕ) : ℝ) * Real.exp (- b (K + (jm:ℕ))))) :=
            mul_le_mul_of_nonneg_left (hKterms i hiT) (norm_nonneg _)
        _ = ‖(coeff (K + (jm:ℕ))) F‖
              * (‖c i‖ * ((((K + (i:ℕ)) ^ (i:ℕ) : ℕ) : ℝ) * Real.exp (- b (K + (jm:ℕ))))) := by ring
    · have hci : c i = 0 := hczero i hiT (Finset.mem_erase.mp hi).1
      simp [hgnorm, hci]
  have hrest_lt : ‖∑ i ∈ Finset.univ.erase jm, g i‖ < ‖g jm‖ := by
    have hstep1 : ‖∑ i ∈ Finset.univ.erase jm, g i‖
        ≤ ‖(coeff (K + (jm:ℕ))) F‖ * ∑ i ∈ Finset.univ.erase jm, ‖c i‖ * R i := by
      rw [Finset.mul_sum]
      exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum hperbound)
    have heq : ∑ i ∈ Finset.univ.erase jm, ‖c i‖ * R i = ∑ i ∈ T, ‖c i‖ * R i := by
      refine (Finset.sum_subset hTsub (fun i hi hiT => ?_)).symm
      have : c i = 0 := hczero i hiT (Finset.mem_erase.mp hi).1
      simp [this]
    rw [heq] at hstep1
    have hlt2 : ‖(coeff (K + (jm:ℕ))) F‖ * ∑ i ∈ T, ‖c i‖ * R i
        < ‖(coeff (K + (jm:ℕ))) F‖ * ‖c jm‖ := mul_lt_mul_of_pos_left hKdom (hFpos _)
    have hgjm : ‖(coeff (K + (jm:ℕ))) F‖ * ‖c jm‖ ≤ ‖g jm‖ := by
      rw [hgnorm]
      have h1 : (1:ℝ) ≤ (((K + (jm:ℕ)).descFactorial (jm:ℕ) : ℕ) : ℝ) := by
        rw [Nat.one_le_cast]
        exact Nat.one_le_iff_ne_zero.mpr
          (fun h => absurd (Nat.descFactorial_eq_zero_iff_lt.mp h) (by omega))
      have hnn : (0:ℝ) ≤ ‖c jm‖ * ‖(coeff (K + (jm:ℕ))) F‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      nlinarith [h1, hnn]
    linarith [hstep1, hlt2, hgjm]
  have hz : g jm + ∑ i ∈ Finset.univ.erase jm, g i = 0 := by
    rw [Finset.add_sum_erase _ g (Finset.mem_univ jm)]; exact hcoeff K
  rw [add_eq_zero_iff_eq_neg] at hz
  rw [hz, norm_neg] at hrest_lt
  exact lt_irrefl _ hrest_lt

end GaloisForLFunctions

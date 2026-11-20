import GaloisForLFunctions.CountingHolography.Sections.PrimeDisplacementGramAndModeQuotients

/-!
# The Gram matrix of two prime-shell copies of one witness

Place one integer witness `u : Fin M → ℤ` on two blocks of primes above any cutoff, the second
block at logarithmic distance `Δ ≥ 0` from the first. As the base scale grows the two probes are
disjoint and signed prime-supported, and their Gram matrix tends to

  `[[I, A(Δ)], [A(Δ), I]]`,  `I = integerProbe u = A(0)`,  `A(Δ) = probeAutocorr u Δ`

(`tendsto_gram_primeShellCopies`), where `A(Δ) = Σ_{i,j} Re S(Δ + log(i+1) − log(j+1)) u_i u_j` is
the cross-scale autocorrelation of the witness, `S` the spline series over the zeros. This is the
reference value for every two-probe construction from one witness: for a negative witness the
copies at distance `Δ` eventually form a negative-definite pair when `|A(Δ)| < |I|`
(`eventually_negDef_primeShellCopies`) and eventually fail when `|A(Δ)| > |I|`
(`eventually_not_negDef_primeShellCopies`).
-/

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open Complex Filter Topology Set Finset Matrix

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open ArithmeticScatteringHolography CountingHolography HTGeometry
open RenormalizedIntersectionTheory

private theorem extend_pairing {M N : ℕ} {ι₁ ι₂ : Fin M → Fin N}
    (hι₁ : Function.Injective ι₁) (hι₂ : Function.Injective ι₂) (u₁ u₂ : Fin M → ℤ) :
    probePairing N (Function.extend ι₁ u₁ 0) (Function.extend ι₂ u₂ 0) =
      ∑ i : Fin M, ∑ j : Fin M,
        (atomGram N (ι₁ i) (ι₂ j)).re * (u₁ i : ℝ) * (u₂ j : ℝ) := by
  have hsum_ext {ι : Fin M → Fin N} (hι : Function.Injective ι) (w : Fin N → ℝ) (u : Fin M → ℤ) :
      (∑ ℓ : Fin N, w ℓ * ((Function.extend ι u 0 ℓ : ℤ) : ℝ)) =
        ∑ i : Fin M, w (ι i) * (u i : ℝ) := by
    have hoff : ∀ ℓ : Fin N, ℓ ∉ Finset.univ.image ι →
        w ℓ * ((Function.extend ι u 0 ℓ : ℤ) : ℝ) = 0 := by
      intro ℓ hℓ
      have hz : Function.extend ι u 0 ℓ = 0 :=
        Function.extend_apply' _ _ _ fun ⟨i, hi⟩ =>
          hℓ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
      rw [hz, Int.cast_zero, mul_zero]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)) fun ℓ _ hℓ => hoff ℓ hℓ,
      Finset.sum_image fun i _ j _ h => hι h]
    exact Finset.sum_congr rfl fun i _ => by rw [hι.extend_apply]
  unfold probePairing
  have houter :
      (∑ ℓ : Fin N, ∑ ℓ' : Fin N,
        (atomGram N ℓ ℓ').re * ((Function.extend ι₁ u₁ 0 ℓ : ℤ) : ℝ) *
          ((Function.extend ι₂ u₂ 0 ℓ' : ℤ) : ℝ)) =
      ∑ ℓ : Fin N,
        (∑ ℓ' : Fin N, (atomGram N ℓ ℓ').re * ((Function.extend ι₂ u₂ 0 ℓ' : ℤ) : ℝ)) *
          ((Function.extend ι₁ u₁ 0 ℓ : ℤ) : ℝ) := by
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun ℓ' _ => by ring
  rw [houter, hsum_ext hι₁ _ u₁]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsum_ext hι₂ (fun ℓ' => (atomGram N (ι₁ i) ℓ').re) u₂, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The limit Gram matrix of two prime-shell copies.** Copies of `u` on two blocks of primes
above `P₀`, at logarithmic distance `Δ`, have Gram entries tending to `I, A(Δ), I`. -/
theorem tendsto_gram_primeShellCopies {M : ℕ} (u : Fin M → ℤ) (P₀ : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∃ (Nseq : ℕ → ℕ) (ι : (n : ℕ) → Fin 2 → Fin M → Fin (Nseq n)),
      (∀ n, Function.Injective (fun p : Fin 2 × Fin M => ι n p.1 p.2)) ∧
      (∀ n r i, ((ι n r i).val + 1).Prime ∧ P₀ < (ι n r i).val + 1) ∧
      Tendsto (fun n => probePairing (Nseq n) (Function.extend (ι n 0) u 0)
        (Function.extend (ι n 0) u 0)) atTop (𝓝 (integerProbe M u)) ∧
      Tendsto (fun n => probePairing (Nseq n) (Function.extend (ι n 1) u 0)
        (Function.extend (ι n 1) u 0)) atTop (𝓝 (integerProbe M u)) ∧
      Tendsto (fun n => probePairing (Nseq n) (Function.extend (ι n 0) u 0)
        (Function.extend (ι n 1) u 0)) atTop (𝓝 (probeAutocorr u Δ)) := by
  let Δ_vec : Fin 2 → ℝ := ![0, Δ]
  have hΔ_vec (r : Fin 2) : 0 ≤ Δ_vec r := by fin_cases r <;> simp [Δ_vec, hΔ]
  obtain ⟨U, _, hU⟩ := exists_shifted_primeBlocks_log_approx 2 M P₀ Δ_vec hΔ_vec
  have hseq (n : ℕ) := hU (max U (n : ℝ)) (le_max_left _ _)
  choose Nseq ιseq hι_inj hι_props using hseq
  have hι_row_inj (n : ℕ) (r : Fin 2) : Function.Injective (ιseq n r) :=
    fun i j hij => (Prod.ext_iff.mp (hι_inj n (a₁ := (r, i)) (a₂ := (r, j)) hij)).2
  have hzero : Tendsto (fun n : ℕ => (6 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hexp_bound (n : ℕ) (hn1 : 1 ≤ n) :
      2 * Real.exp (-(1 / 3 : ℝ) * (n : ℝ)) ≤ (6 : ℝ) / (n : ℝ) := by
    have hlin : (1 / 3 : ℝ) * (n : ℝ) ≤ Real.exp ((1 / 3 : ℝ) * (n : ℝ)) := by
      linarith [Real.add_one_le_exp ((1 / 3 : ℝ) * (n : ℝ))]
    rw [neg_mul, Real.exp_neg]
    have hinv := inv_anti₀ (by positivity : 0 < (1 / 3 : ℝ) * (n : ℝ)) hlin
    rw [show ((1 / 3 : ℝ) * (n : ℝ))⁻¹ = (3 : ℝ) / (n : ℝ) by field_simp] at hinv
    calc 2 * (Real.exp ((1 / 3 : ℝ) * (n : ℝ)))⁻¹ ≤ 2 * ((3 : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 6 / (n : ℝ) := by ring
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt U
  have hconv_block (r s : Fin 2) :
      Tendsto (fun n : ℕ => probePairing (Nseq n)
        (Function.extend (ιseq n r) u 0) (Function.extend (ιseq n s) u 0))
        atTop (𝓝 (∑ i : Fin M, ∑ j : Fin M,
          (splineSeries (Δ_vec r - Δ_vec s + Real.log ((i : ℝ) + 1) - Real.log ((j : ℝ) + 1))).re *
            (u i : ℝ) * (u j : ℝ))) := by
    refine (tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_finsetSum Finset.univ fun j _ => ?_).congr fun n =>
        (extend_pairing (hι_row_inj n r) (hι_row_inj n s) u u).symm
    have harg : Tendsto
        (fun n : ℕ =>
          Real.log (((ιseq n r i).val : ℝ) + 1) - Real.log (((ιseq n s j).val : ℝ) + 1))
        atTop (𝓝 (Δ_vec r - Δ_vec s + Real.log ((i : ℝ) + 1) - Real.log ((j : ℝ) + 1))) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (by simpa only [sub_zero] using tendsto_const_nhds.sub hzero)
        (by simpa only [add_zero] using tendsto_const_nhds.add hzero) ?_ ?_
      · filter_upwards [eventually_ge_atTop (max N₀ 1)] with n hn
        have hmax : max U (n : ℝ) = (n : ℝ) :=
          max_eq_right (hN₀.le.trans (by exact_mod_cast (le_max_left N₀ 1).trans hn))
        have hb := hexp_bound n ((le_max_right N₀ 1).trans hn)
        have hi := (hι_props n r i).2.2
        have hj := (hι_props n s j).2.2
        rw [hmax] at hi hj
        linarith only [hi.2, hj.1, hb]
      · filter_upwards [eventually_ge_atTop (max N₀ 1)] with n hn
        have hmax : max U (n : ℝ) = (n : ℝ) :=
          max_eq_right (hN₀.le.trans (by exact_mod_cast (le_max_left N₀ 1).trans hn))
        have hb := hexp_bound n ((le_max_right N₀ 1).trans hn)
        have hi := (hι_props n r i).2.2
        have hj := (hι_props n s j).2.2
        rw [hmax] at hi hj
        linarith only [hi.1, hj.2, hb]
    have hsp := ((Complex.continuous_re.comp continuous_splineSeries).tendsto _).comp harg
    refine ((hsp.mul_const (u i : ℝ)).mul_const (u j : ℝ)).congr fun n => ?_
    dsimp only [Function.comp_apply]
    rw [atomGram_eq_splineSeries]
  refine ⟨Nseq, ιseq, hι_inj, fun n r i => ⟨(hι_props n r i).1, (hι_props n r i).2.1⟩, ?_, ?_, ?_⟩
  · rw [← probeAutocorr_zero, probeAutocorr]
    have h00 : Δ_vec 0 - Δ_vec 0 = 0 := sub_self _
    simpa only [h00] using hconv_block 0 0
  · rw [← probeAutocorr_zero, probeAutocorr]
    have h11 : Δ_vec 1 - Δ_vec 1 = 0 := sub_self _
    simpa only [h11] using hconv_block 1 1
  · have h21 := hconv_block 1 0
    have h10 : Δ_vec 1 - Δ_vec 0 = Δ := by simp [Δ_vec]
    rw [h10, ← probeAutocorr] at h21
    exact h21.congr fun n => probePairing_symm (Nseq n) _ _

/-- **Copies below the reference correlation form a negative-definite pair.** -/
theorem eventually_negDef_primeShellCopies {M : ℕ} {u : Fin M → ℤ} (hneg : integerProbe M u < 0)
    (P₀ : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ) (hA : |probeAutocorr u Δ| < -integerProbe M u) :
    ∃ (Nseq : ℕ → ℕ) (ι : (n : ℕ) → Fin 2 → Fin M → Fin (Nseq n)),
      (∀ n, Function.Injective (fun p : Fin 2 × Fin M => ι n p.1 p.2)) ∧
      (∀ n r i, ((ι n r i).val + 1).Prime ∧ P₀ < (ι n r i).val + 1) ∧
      ∀ᶠ n in atTop,
        probePairing (Nseq n) (Function.extend (ι n 0) u 0) (Function.extend (ι n 0) u 0) < 0 ∧
        probePairing (Nseq n) (Function.extend (ι n 1) u 0) (Function.extend (ι n 1) u 0) < 0 ∧
        (probePairing (Nseq n) (Function.extend (ι n 0) u 0) (Function.extend (ι n 1) u 0)) ^ 2 <
          probePairing (Nseq n) (Function.extend (ι n 0) u 0) (Function.extend (ι n 0) u 0) *
            probePairing (Nseq n) (Function.extend (ι n 1) u 0) (Function.extend (ι n 1) u 0) := by
  obtain ⟨Nseq, ι, hinj, hprime, h11, h22, h12⟩ := tendsto_gram_primeShellCopies u P₀ hΔ
  refine ⟨Nseq, ι, hinj, hprime, ?_⟩
  have hgap : (probeAutocorr u Δ) ^ 2 < integerProbe M u * integerProbe M u := by
    have h := pow_lt_pow_left₀ hA (abs_nonneg _) two_ne_zero
    rw [sq_abs] at h
    nlinarith only [h]
  have hlim := (h11.mul h22).sub (h12.pow 2)
  refine (h11.eventually (gt_mem_nhds hneg)).and ((h22.eventually (gt_mem_nhds hneg)).and ?_)
  exact ((tendsto_order.mp hlim).1 0 (sub_pos.mpr hgap)).mono fun n hn => by linarith only [hn]

/-- **Copies above the reference correlation are never a negative-definite pair.** -/
theorem eventually_not_negDef_primeShellCopies {M : ℕ} {u : Fin M → ℤ} (P₀ : ℕ) {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hA : |integerProbe M u| < |probeAutocorr u Δ|) :
    ∃ (Nseq : ℕ → ℕ) (ι : (n : ℕ) → Fin 2 → Fin M → Fin (Nseq n)),
      (∀ n, Function.Injective (fun p : Fin 2 × Fin M => ι n p.1 p.2)) ∧
      (∀ n r i, ((ι n r i).val + 1).Prime ∧ P₀ < (ι n r i).val + 1) ∧
      ∀ᶠ n in atTop,
        probePairing (Nseq n) (Function.extend (ι n 0) u 0) (Function.extend (ι n 0) u 0) *
            probePairing (Nseq n) (Function.extend (ι n 1) u 0) (Function.extend (ι n 1) u 0) <
          (probePairing (Nseq n) (Function.extend (ι n 0) u 0) (Function.extend (ι n 1) u 0)) ^ 2 := by
  obtain ⟨Nseq, ι, hinj, hprime, h11, h22, h12⟩ := tendsto_gram_primeShellCopies u P₀ hΔ
  refine ⟨Nseq, ι, hinj, hprime, ?_⟩
  have hgap : integerProbe M u * integerProbe M u < (probeAutocorr u Δ) ^ 2 := by
    have h := pow_lt_pow_left₀ hA (abs_nonneg _) two_ne_zero
    rw [sq_abs, sq_abs] at h
    nlinarith only [h]
  have hlim := (h12.pow 2).sub (h11.mul h22)
  exact ((tendsto_order.mp hlim).1 0 (sub_pos.mpr hgap)).mono fun n hn => by linarith only [hn]

#print axioms tendsto_gram_primeShellCopies
#print axioms eventually_negDef_primeShellCopies
#print axioms eventually_not_negDef_primeShellCopies

end GaloisForLFunctions.CountingHolography.Sections

import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheAbelEscapeAtomsOfZetaAreItsDominantZeros

/-!
# The Abel escape capacity of the dominant zeros

`TheAbelEscapeAtomsOfZetaAreItsDominantZeros` gives each dominant simple zero `ρ` of `ζ` an atom of
mass `π ‖r_ρ‖²`, `r_ρ = ζ(ρ − ε)/(ζ′(ρ)(ρ − ε))`, in the scaled spectral measure of the receiver at
its abscissa `θ`. The atoms sit in disjoint windows and the total spectral mass is `2π` times the
Abel energy, so the atoms are paid out of the escape rate.

* **The capacity law** (`eventually_le_mul_integral_lineSymbol`,
  `eventually_le_mul_abelGram_receiver`). For every finite set of dominant simple zeros and every
  `M < π Σ_ρ ‖r_ρ‖²`, eventually `M ≤ e ∫ ‖G_ε(θ + e + iy)‖² dy = 2π e A_{θ+e}(0, 0)`: the escape rate
  dominates the total residue mass of the dominant zeros.
* **Non-summable residues escape to infinite height**
  (`tendsto_mul_abelGram_receiver_atTop_of_not_summable`,
  `tendsto_receiver_atom_share_zero_of_not_summable`). If the residue masses of the dominant simple
  zeros are not summable, the escape is faster than `1/e`, and every window's share of the
  spectral measure tends to zero: no finite-height atom survives normalization.
* **An unattained abscissa escapes to infinite height**
  (`tendsto_receiver_window_share_zero_of_unattained`). If the receiver escapes at `θ` but no zero
  of `ζ` lies on `Re s = θ + ½ + ε`, every compact window's share tends to zero.

These are the two cases that the explicit-formula split leaves open (README §9.8); in the Abel
normalization both escape to infinite height, and otherwise the dominant zeros pay the escape up to
the capacity defect `lim 2π e A − π Σ ‖r_ρ‖² ≥ 0`, the mass at infinite height.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy (dampedMobiusEnergy)

/-- The residue `r_ρ = ζ(ρ − ε)/(ζ′(ρ)(ρ − ε))` of the receiver symbol at the translated zero. -/
def receiverResidue (ε : ℝ) (ρ : ℂ) : ℂ :=
  riemannZeta (ρ - ε) / (deriv riemannZeta ρ * (ρ - ε))

/-- The data of the receiver on the line `Re s = θ + e`: `L¹ ∩ L²` under dominance. -/
theorem receiver_data {ε θ e : ℝ} (hθ : 0 < θ) (he : 0 < e)
    (hdom : ∀ κ : ℝ, 2 * θ < κ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ) :
    Integrable (dampedProfile (receiverLogProfile ε) (θ + e)) ∧
      MemLp (dampedProfile (receiverLogProfile ε) (θ + e)) 2 := by
  obtain ⟨C, hC, hE⟩ := hdom (2 * θ + e) (by linarith)
  exact integrable_and_memLp_dampedProfile_receiver hC (by linarith) hE
    (show (2 * θ + e) / 2 < θ + e by linarith)

/-- **The capacity law.** For a finite set `s` of simple zeros on the line `Re ρ = θ + ½ + ε`
(dominant: energy `O((T+1)^κ)` for `κ > 2θ`) and every `M < π Σ_{ρ ∈ s} ‖r_ρ‖²`, eventually
`M ≤ e ∫ ‖G_ε(θ + e + iy)‖² dy`. -/
theorem eventually_le_mul_integral_lineSymbol {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ1 : θ + 1 / 2 + ε < 1)
    (hdom : ∀ κ : ℝ, 2 * θ < κ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ)
    (s : Finset ℂ) (hs : ∀ ρ ∈ s, riemannZeta ρ = 0 ∧ deriv riemannZeta ρ ≠ 0 ∧
      ρ.re = θ + 1 / 2 + ε) {M : ℝ}
    (hM : M < Real.pi * ∑ ρ ∈ s, ‖receiverResidue ε ρ‖ ^ 2) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ),
      M ≤ e * ∫ y, ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2 := by
  -- the atom of each zero, on every small window
  have hatom : ∀ ρ ∈ s, ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun e : ℝ => e * ∫ y in (ρ.im - δ)..(ρ.im + δ),
        ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2) (𝓝[>] 0)
        (𝓝 (Real.pi * ‖receiverResidue ε ρ‖ ^ 2)) := by
    intro ρ hρ
    obtain ⟨hz, hd, hre⟩ := hs ρ hρ
    have hdom' : ∀ κ : ℝ, 2 * (ρ.re - ε) - 1 < κ →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ :=
      fun κ hκ => hdom κ (by rw [hre] at hκ; linarith)
    obtain ⟨δ₀, hδ₀, h⟩ := tendsto_receiver_window_atom hε hz hd (by rw [hre]; linarith)
      (by rw [hre]; linarith) hdom'
    refine ⟨δ₀, hδ₀, fun δ hδ hδδ₀ => ?_⟩
    have := h δ hδ hδδ₀ (fun _ => 1) 0 1 le_rfl continuous_const (fun y => by simp)
      (fun y => by simp)
    simp only [mul_one] at this
    rw [show ρ.re - ε - 1 / 2 = θ by rw [hre]; ring] at this
    exact this
  choose! δ₀ hδ₀ hT using hatom
  -- a common radius below every `δ₀` and below half of every gap of ordinates
  have hevδ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ (∀ ρ ∈ s, δ ≤ δ₀ ρ) ∧
      ∀ ρ ∈ s, ∀ ρ' ∈ s, ρ ≠ ρ' → 2 * δ < |ρ.im - ρ'.im| := by
    refine eventually_mem_nhdsWithin.and (Filter.Eventually.and ?_ ?_)
    · refine (eventually_all_finset s).mpr fun ρ hρ => ?_
      exact ((gt_mem_nhds (hδ₀ ρ hρ)).filter_mono nhdsWithin_le_nhds).mono fun δ h => h.le
    · refine (eventually_all_finset s).mpr fun ρ hρ => (eventually_all_finset s).mpr fun ρ' hρ' => ?_
      by_cases hne : ρ = ρ'
      · exact Eventually.of_forall fun δ h => absurd hne h
      · have him : ρ.im ≠ ρ'.im := fun h => hne (Complex.ext (by
          rw [(hs ρ hρ).2.2, (hs ρ' hρ').2.2]) h)
        have hpos : 0 < |ρ.im - ρ'.im| := abs_pos.mpr (sub_ne_zero.mpr him)
        exact ((gt_mem_nhds (show (0 : ℝ) < |ρ.im - ρ'.im| / 2 by linarith)).filter_mono
          nhdsWithin_le_nhds).mono fun δ h _ => by linarith
  obtain ⟨δ, hδ0, hδle, hgap⟩ := hevδ.exists
  have hdisj : (s : Set ℂ).Pairwise
      (Function.onFun Disjoint fun ρ : ℂ => Icc (ρ.im - δ) (ρ.im + δ)) := by
    intro ρ hρ ρ' hρ' hne
    refine Set.disjoint_left.mpr fun y hy hy' => ?_
    have hlt := hgap ρ hρ ρ' hρ' hne
    have hle : |ρ.im - ρ'.im| ≤ 2 * δ :=
      abs_le.mpr ⟨by linarith [hy.1, hy.2, hy'.1, hy'.2], by linarith [hy.1, hy.2, hy'.1, hy'.2]⟩
    linarith
  -- the windows converge to the atoms
  have hsum : Tendsto (fun e : ℝ => ∑ ρ ∈ s, e * ∫ y in (ρ.im - δ)..(ρ.im + δ),
      ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2) (𝓝[>] 0)
      (𝓝 (∑ ρ ∈ s, Real.pi * ‖receiverResidue ε ρ‖ ^ 2)) :=
    tendsto_finsetSum s fun ρ hρ => hT ρ hρ δ hδ0 (hδle ρ hρ)
  rw [← Finset.mul_sum] at hsum
  filter_upwards [hsum.eventually (le_mem_nhds hM), self_mem_nhdsWithin] with e he he0
  have he0' : (0 : ℝ) < e := he0
  obtain ⟨hI, hL⟩ := receiver_data hθ he0' hdom
  have hint : Integrable (fun y => ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2) :=
    _root_.RHTower.integrable_norm_sq_laplaceBoundary hI.ofReal hL.ofReal
  refine he.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ he0'.le
  have hunion : (∫ y in ⋃ ρ ∈ s, Icc (ρ.im - δ) (ρ.im + δ), ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2) =
      ∑ ρ ∈ s, ∫ y in (ρ.im - δ)..(ρ.im + δ),
        ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2 := by
    rw [integral_biUnion_finset s (fun _ _ => measurableSet_Icc) hdisj
      (fun _ _ => hint.integrableOn)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
  rw [← hunion]
  exact setIntegral_le_integral hint (Eventually.of_forall fun y => by positivity)

/-- The capacity law in Abel form: eventually `M ≤ 2π e A_{θ+e}(0, 0)`. -/
theorem eventually_le_mul_abelGram_receiver {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ1 : θ + 1 / 2 + ε < 1)
    (hdom : ∀ κ : ℝ, 2 * θ < κ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ)
    (s : Finset ℂ) (hs : ∀ ρ ∈ s, riemannZeta ρ = 0 ∧ deriv riemannZeta ρ ≠ 0 ∧
      ρ.re = θ + 1 / 2 + ε) {M : ℝ}
    (hM : M < Real.pi * ∑ ρ ∈ s, ‖receiverResidue ε ρ‖ ^ 2) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ),
      M ≤ 2 * Real.pi * (e * abelGram (receiverLogProfile ε) (θ + e) 0 0) := by
  filter_upwards [eventually_le_mul_integral_lineSymbol hε hθ hθ1 hdom s hs hM,
    self_mem_nhdsWithin] with e he he0
  obtain ⟨hI, hL⟩ := receiver_data hθ he0 hdom
  rw [integral_norm_sq_lineSymbol hI hL] at he
  linarith

/-- **Non-summable residues force super-`1/e` escape.** If the residue masses of a family `Z` of
dominant simple zeros on `Re ρ = θ + ½ + ε` are not summable, `e A_{θ+e}(0, 0) → ∞`. -/
theorem tendsto_mul_abelGram_receiver_atTop_of_not_summable {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ1 : θ + 1 / 2 + ε < 1)
    (hdom : ∀ κ : ℝ, 2 * θ < κ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ)
    (Z : Set ℂ) (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ deriv riemannZeta ρ ≠ 0 ∧
      ρ.re = θ + 1 / 2 + ε)
    (hns : ¬ Summable fun ρ : Z => ‖receiverResidue ε ρ‖ ^ 2) :
    Tendsto (fun e : ℝ => e * abelGram (receiverLogProfile ε) (θ + e) 0 0) (𝓝[>] 0) atTop := by
  refine tendsto_atTop.mpr fun B => ?_
  -- a finite subfamily whose residue mass exceeds `2B + 1`
  obtain ⟨u, hu⟩ : ∃ u : Finset Z, 2 * B + 1 < ∑ ρ ∈ u, ‖receiverResidue ε ρ‖ ^ 2 := by
    by_contra h
    simp only [not_exists, not_lt] at h
    exact hns (summable_of_sum_le (fun _ => by positivity) h)
  set s : Finset ℂ := u.map (Function.Embedding.subtype _) with hsdef
  have hs : ∀ ρ ∈ s, riemannZeta ρ = 0 ∧ deriv riemannZeta ρ ≠ 0 ∧ ρ.re = θ + 1 / 2 + ε := by
    intro ρ hρ
    obtain ⟨ρ', -, rfl⟩ := Finset.mem_map.mp hρ
    exact hZ ρ'.1 ρ'.2
  have hsum : ∑ ρ ∈ s, ‖receiverResidue ε ρ‖ ^ 2 = ∑ ρ ∈ u, ‖receiverResidue ε ρ‖ ^ 2 := by
    rw [hsdef, Finset.sum_map]; rfl
  have hM : 2 * Real.pi * B < Real.pi * ∑ ρ ∈ s, ‖receiverResidue ε ρ‖ ^ 2 := by
    rw [hsum]; have := Real.pi_pos; nlinarith
  filter_upwards [eventually_le_mul_abelGram_receiver hε hθ hθ1 hdom s hs hM] with e he
  have := Real.pi_pos
  nlinarith

/-- In the non-summable case every finite-height atom is lost in the normalization: the share of
the window of any dominant simple zero in the spectral measure tends to zero. -/
theorem tendsto_receiver_atom_share_zero_of_not_summable {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ1 : θ + 1 / 2 + ε < 1)
    (hdom : ∀ κ : ℝ, 2 * θ < κ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ)
    (Z : Set ℂ) (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ deriv riemannZeta ρ ≠ 0 ∧
      ρ.re = θ + 1 / 2 + ε)
    (hns : ¬ Summable fun ρ : Z => ‖receiverResidue ε ρ‖ ^ 2) {ρ : ℂ} (hρ : ρ ∈ Z) :
    ∃ δ > 0, Tendsto (fun e : ℝ =>
      (∫ y in (ρ.im - δ)..(ρ.im + δ), ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2) /
        ∫ y, ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hz, hd, hre⟩ := hZ ρ hρ
  obtain ⟨δ, hδ, h⟩ := tendsto_receiver_window_atom hε hz hd (by rw [hre]; linarith)
    (by rw [hre]; linarith) fun κ hκ => hdom κ (by rw [hre] at hκ; linarith)
  refine ⟨δ, hδ, ?_⟩
  have hnum := h δ hδ le_rfl (fun _ => 1) 0 1 le_rfl continuous_const (fun y => by simp)
    (fun y => by simp)
  simp only [mul_one] at hnum
  rw [show ρ.re - ε - 1 / 2 = θ by rw [hre]; ring] at hnum
  have hden : Tendsto (fun e : ℝ => e * ∫ y, ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2)
      (𝓝[>] 0) atTop := by
    have h2 := (tendsto_mul_abelGram_receiver_atTop_of_not_summable hε hθ hθ1 hdom Z hZ
      hns).const_mul_atTop (show (0 : ℝ) < 2 * Real.pi by positivity)
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with e he
    obtain ⟨hI, hL⟩ := receiver_data hθ he hdom
    rw [integral_norm_sq_lineSymbol hI hL]
    ring
  refine (hnum.div_atTop hden).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with e he
  exact mul_div_mul_left _ _ (ne_of_gt he)

/-- **An unattained abscissa escapes to infinite height.** If the receiver escapes at `θ` and no
zero of `ζ` lies on the line `Re s = θ + ½ + ε`, the share of every compact window in the spectral
measure tends to zero. -/
theorem tendsto_receiver_window_share_zero_of_unattained {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hθ1 : θ + 1 / 2 + ε < 1)
    (hdom : ∀ κ : ℝ, 2 * θ < κ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ)
    (hfree : ∀ y : ℝ, riemannZeta (((θ + 1 / 2 + ε : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0)
    (hesc : Tendsto (fun e : ℝ => abelGram (receiverLogProfile ε) (θ + e) 0 0) (𝓝[>] 0) atTop)
    {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    Tendsto (fun e : ℝ => (∫ y in y₁..y₂, ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2) /
      ∫ y, ‖lineSymbol (receiverLogProfile ε) (θ + e) y‖ ^ 2) (𝓝[>] 0) (𝓝 0) :=
  tendsto_receiver_window_share_zero hε hθ hθ1 hy hdom (fun y _ => hfree y) hesc

end GaloisForLFunctions.ArithmeticCorrespondencePositivity

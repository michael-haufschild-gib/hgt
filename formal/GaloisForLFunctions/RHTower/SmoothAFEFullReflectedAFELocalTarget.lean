import GaloisForLFunctions.RHTower.SmoothAFEFullReflectedAFE

open MeasureTheory Filter Finset
open scoped Topology
noncomputable section
namespace RHTower
open SteinhausModel

/-- The complete coefficient-faithful reflected AFE has arbitrary bounded finite-node
targets in every prescribed finite phase cell with arbitrarily small power cost.
This is an original product-measure statement; it supplies no deterministic height count. -/
theorem exists_fullReflectedAFE_prescribedPhase_localTarget
    {J : ℕ} (hJ : 0 < J) (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    (hinj : Function.Injective (fun j => rightDisplacedLinePt (d j) (b j)))
    (P : ℕ) (ω : Omega) {δ M ε ρ : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * (n ^ 2 : ℕ)) ((7 / 4 : ℝ) * (n ^ 2 : ℕ)),
      ∀ t : EuclideanSpace ℂ (Fin J), ‖t‖ ≤ M →
        c * ((n ^ 2 : ℕ) : ℝ) ^ (-ε) ≤ steinhausMeasure.real
          (steinhausCharacterCell P (steinhausLogPhaseShift ω (-tau)) δ ∩
            {η | ‖steinhausHilbertFullReflectedAFE d b tau (n ^ 2) η - t‖ < ρ}) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_steinhausHilbertReflectedCorrection_le hJ d b hd hdhalf
  obtain ⟨B, δc, hδc, htol⟩ :=
    exists_steinhausHilbertReflectedCorrection_character_tolerance hJ d b hd hdhalf (half_pos hρ)
  let Q := max P B
  let δ' := min δ δc
  have hδ' : 0 < δ' := lt_min hδ hδc
  obtain ⟨c, hc, hprimal⟩ := exists_fullReflectedCarrier_prescribedPhase_localTarget
    hJ d b hd hdhalf hinj Q ω hδ' (add_nonneg hM hC) hε (half_pos hρ)
  have hoffset : ∀ᶠ n : ℕ in atTop, ∀ j, 4 * |b j| ≤ (n : ℝ) := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (4 * |b j|))
  refine ⟨c, hc, ?_⟩
  filter_upwards [hprimal, hoffset, eventually_ge_atTop 1] with n hn hbn hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn2 : (n : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) := by
    simp only [Nat.cast_pow]
    nlinarith
  have hn21 : 1 ≤ n ^ 2 := by
    have hp : 0 < n ^ 2 := pow_pos (by omega : 0 < n) _
    omega
  intro tau htau t ht
  have hwindow (j : Fin J) :
      ((n ^ 2 : ℕ) : ℝ) ≤ tau + b j ∧ tau + b j ≤ 2 * (n ^ 2 : ℕ) := by
    have hb := (hbn j).trans hn2
    constructor <;> linarith [htau.1, htau.2, neg_abs_le (b j), le_abs_self (b j)]
  let ξ := steinhausLogPhaseShift ω (-tau)
  let v := steinhausHilbertReflectedCorrection d b tau (n ^ 2) ξ
  have hv : ‖v‖ ≤ C := hbound _ hn21 tau hwindow ξ
  have ht' : ‖t - v‖ ≤ M + C := (norm_sub_le _ _).trans (add_le_add ht hv)
  refine (hn tau htau (t - v) ht').trans (measureReal_mono ?_)
  intro η hη
  have hcellP : η ∈ steinhausCharacterCell P ξ δ := by
    intro k hk
    exact (hη.1 k (mem_Icc.mpr ⟨(mem_Icc.mp hk).1,
      (mem_Icc.mp hk).2.trans (le_max_left _ _)⟩)).trans_le (min_le_left _ _)
  have hcellB : η ∈ steinhausCharacterCell B ξ δc := by
    intro k hk
    exact (hη.1 k (mem_Icc.mpr ⟨(mem_Icc.mp hk).1,
      (mem_Icc.mp hk).2.trans (le_max_right _ _)⟩)).trans_le (min_le_right _ _)
  refine ⟨hcellP, ?_⟩
  have hcorr := htol _ hn21 tau hwindow ξ η hcellB
  change ‖steinhausHilbertReflectedCorrection d b tau (n ^ 2) η - v‖ < ρ / 2 at hcorr
  have heq : steinhausHilbertFullReflectedAFE d b tau (n ^ 2) η - t =
      (steinhausHilbertFullReflectedCarrier d b tau (n ^ 2) η - (t - v)) +
        (steinhausHilbertReflectedCorrection d b tau (n ^ 2) η - v) := by
    unfold steinhausHilbertFullReflectedAFE
    abel
  change ‖steinhausHilbertFullReflectedAFE d b tau (n ^ 2) η - t‖ < ρ
  rw [heq]
  have htarget : ‖steinhausHilbertFullReflectedCarrier d b tau (n ^ 2) η - (t - v)‖ < ρ / 2 := hη.2
  exact (norm_add_le _ _).trans_lt (by linarith)

end RHTower

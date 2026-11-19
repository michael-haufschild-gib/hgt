import GaloisForLFunctions.SquareRootThreshold.AStripGivesLittlewoodWindows
import GaloisForLFunctions.SquareRootThreshold.AnExplicitClusterDetectorConstant
import GaloisForLFunctions.SquareRootThreshold.GroundEnergyAbscissaAndLagGridAttainmentBridge
import GaloisForLFunctions.RHTower.XiSliceEventualPositivityFiniteOffLine

/-!
# Critical-line copies in every fixed window

When the off-line divisor is finite, every sufficiently high window of fixed
positive radius contains at least a positive multiple of the logarithm of its
height in critical-line zero copies. The multiplicity is the xi multiplicity.
-/

noncomputable section
open Complex Set Filter Zeta23
open scoped Topology
namespace GaloisForLFunctions.SquareRootThreshold
open _root_.RHTower

private theorem critical_above {q : XiZeroCopy} {b : ℝ}
    (hb : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 → |(q.1 : ℂ).im| ≤ b)
    (hq : b < |(q.1 : ℂ).im|) : (q.1 : ℂ).re = 1/2 := by
  have hz : (xiSpectralPoint q).im = 0 := by
    by_contra h
    exact (not_le_of_gt hq) (hb q h)
  symm
  simpa [xiSpectralPoint,sub_eq_zero] using hz

/-- Every fixed window high in a finite off-line layer contains logarithmically
many critical-line copies, including their original multiplicities. -/
theorem critical_line_crowding_of_finiteOffLine (hf : BacklundConverse.FiniteOffLine)
    {h : ℝ} (hh : 0 < h) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ y : ℝ in atTop,
      ∃ S : Finset XiZeroCopy, c*Real.log y ≤ S.card ∧
        ∀ q ∈ S, (q.1 : ℂ).re = 1/2 ∧ |(q.1 : ℂ).im-y| ≤ h := by
  obtain ⟨b,hb⟩ := (hf.image fun q => |(q.1 : ℂ).im|).bddAbove
  have hcrit (q : XiZeroCopy) (hq : b < |(q.1 : ℂ).im|) : (q.1 : ℂ).re = 1/2 :=
    critical_above (fun q hn => hb ⟨q,hn,rfl⟩) hq
  have hstrip : Littlewood.ZeroFreeStrip 0 (b+1) := by
    intro ρ hρ hheight
    obtain ⟨q,rfl⟩ := exists_xiZeroCopy_of_mem_zetaZeroConfig hρ
    rw [hcrit q (by linarith only [hheight]),sub_self,abs_zero]
  let ℓ := max 1 (Littlewood.windowD / h)
  have hℓ : 1 ≤ ℓ := le_max_left _ _
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ
  let δ := Littlewood.windowD / ℓ
  have hδ : δ ≤ h := by
    apply (div_le_iff₀ hℓ0).mpr
    simpa only [mul_comm h] using (div_le_iff₀ hh).mp (le_max_right 1 (Littlewood.windowD / h))
  obtain ⟨_,_,hc⟩ := Littlewood.exists_strip_window_count_bound
  obtain ⟨M,hM⟩ := hc ℓ 0 (b+1) hℓ le_rfl hstrip
  let A := ℓ * Littlewood.bumpMass^2
  let e := Littlewood.energy 0 / 4
  have he : 0 < e := div_pos Littlewood.energy_zero_pos (by norm_num)
  have hA : 0 ≤ A := mul_nonneg hℓ0.le (sq_nonneg _)
  have hAp : 0 < A+1 := by linarith
  refine ⟨e/(A+1),div_pos he hAp,?_⟩
  filter_upwards [hM, Real.tendsto_log_atTop.eventually (eventually_ge_atTop (M/e)),
    eventually_gt_atTop (b+δ)] with y hcount hy hheight
  let S := zetaWindowXiCopies (y-δ) (y+δ)
  refine ⟨S,?_,?_⟩
  · simp only [zero_mul,sub_zero,mul_zero] at hcount
    have hreal : Littlewood.energy 0/2*Real.log y-M ≤ A*(S.card:ℝ) := by
      simpa only [S,card_zetaWindowXiCopies] using hcount
    have hMle := (div_le_iff₀ he).mp hy
    have hnn : 0 ≤ (S.card:ℝ) := Nat.cast_nonneg _
    rw [div_mul_eq_mul_div,div_le_iff₀ hAp]
    dsimp only [e] at hMle ⊢
    linarith only [hreal,hMle,hnn]
  · intro q hq
    obtain ⟨hl,hu⟩ := mem_zetaWindowXiCopies_ordinates hq
    have hbq : b < (q.1 : ℂ).im := by linarith only [hl,hheight]
    exact ⟨hcrit q (hbq.trans_le (le_abs_self _)),
      abs_le.mpr ⟨by linarith only [hl,hδ],by linarith only [hu,hδ]⟩⟩

#print axioms critical_line_crowding_of_finiteOffLine
end GaloisForLFunctions.SquareRootThreshold

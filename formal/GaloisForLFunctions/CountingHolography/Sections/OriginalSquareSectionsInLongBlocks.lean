import GaloisForLFunctions.CountingHolography.Sections.SquareTracePeaksInEveryLogarithmicWindow
import GaloisForLFunctions.CountingHolography.Sections.OrdinarySquareGeneratorsInEveryLogarithmicWindow

/-!
# Original sections on consecutive square conductors in every log window

A peak of the dyadic trace can be rounded to a whole power-length interval
of integer square roots. Its oscillation loses one power of the root. At
each conductor in the interval, ordinary floors and the degree reserve pay
the original full lattice at every positive multiplicity simultaneously.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology SquareRootThreshold ArithmeticScatteringHolography
open SurfaceOfSpecZ.ScaleLocality

private abbrev Q (n : ℕ) := integerProbe _ (successorSquareTriple n)

/-- Across all roots in the block the difference from the single continuous
peak is controlled by its lower growth exponent. -/
private theorem square_block_loss {β a : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1) (ha : 0 ≤ a)
    (hr : 2*zetaZeroWidth+β-1 ≤ 2*a) :
    ∃ E : ℝ, ∀ {u : ℝ}, 0 ≤ u → ∀ {d : ℕ}, upperSquareIndex u ≤ d →
      (d:ℝ) ≤ (upperSquareIndex u:ℝ)+(upperSquareIndex u:ℝ)^β →
      squareLongTrace u-Q d ≤ E*Real.exp (a*u) := by
  obtain ⟨C,hC,h⟩ := realSplineTrace_square_power_gap hβ'
  obtain ⟨K,hK⟩ := successorSquare_relative_trace_limit.bddAbove_range
  let B := 6*|realSplineTrace 0|+4*|K|
  refine ⟨B+4*C+2*C*(2:ℝ)^(2*a),fun {u} hu {d} hd hd' => ?_⟩
  let X := Real.exp (u/2)
  let n := upperSquareIndex u
  have hX : 1 ≤ X := Real.one_le_exp (by linarith only [hu])
  have hx : 0 < X := Real.exp_pos _
  have hn : X ≤ (n:ℝ) := Nat.le_ceil _
  have hn' : (n:ℝ) ≤ X+1 := (Nat.ceil_lt_add_one hx.le).le
  have hn₂ : (n:ℝ) ≤ 2*X := by linarith only [hn',hX]
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg n) hn₂ hβ
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hx.le] at hp
  have htwo : (2:ℝ)^β ≤ 2 := by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hβ'
  have hb := Real.one_le_rpow hX hβ
  have hb₀ := Real.rpow_nonneg hx.le β
  have hdx : X ≤ (d:ℝ) := hn.trans (Nat.cast_le.mpr hd)
  have hupper : (d:ℝ) ≤ X+3*X^β := by
    change (d:ℝ) ≤ (n:ℝ)+(n:ℝ)^β at hd'
    linarith only [hd',hn',hp,mul_le_mul_of_nonneg_right htwo hb₀,hb]
  have htop : ((2*d+1:ℕ):ℝ) ≤ 2*X+7*(2*X)^β := by
    push_cast
    have hh := Real.rpow_le_rpow hx.le (by linarith only [hx] : X ≤ 2*X) hβ
    linarith only [hupper,hh,hb]
  let r := 2*zetaZeroWidth+β-1
  have h₁ := h hX hdx (show (d:ℝ) ≤ X+7*X^β by linarith only [hupper,hb₀])
  have hX₂ : 1 ≤ 2*X := by linarith only [hX]
  have h₂ := h hX₂ (show 2*X ≤ ((2*d+1:ℕ):ℝ) by push_cast; linarith only [hdx]) htop
  have hex : X^(2*a)=Real.exp (a*u) := by
    rw [Real.rpow_def_of_pos hx]; dsimp only [X]; rw [Real.log_exp]; congr 1; ring
  have e₁ : C*X^r ≤ C*Real.exp (a*u) := by
    rw [← hex]; exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX hr) hC
  have e₂ : C*(2*X)^r ≤ C*(2:ℝ)^(2*a)*Real.exp (a*u) := by
    rw [← hex,mul_assoc,← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hx.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX₂ hr) hC
  have hl : 2*Real.log X=u := by dsimp only [X]; rw [Real.log_exp]; ring
  have hl' : 2*Real.log (2*X)=u+Real.log 4 := by
    rw [Real.log_mul two_ne_zero hx.ne',show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    push_cast; linarith only [hl]
  rw [hl] at h₁; rw [hl'] at h₂
  have hk : realSplineTrace (2*(Real.log ((2*d+1:ℕ):ℝ)-Real.log d)) ≤ |K| := by
    have hh := hK ⟨d,rfl⟩
    simp only [Real.log_pow,Nat.cast_ofNat] at hh
    rw [mul_sub]
    exact hh.trans (le_abs_self K)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hc := le_mul_of_one_le_right hB (Real.one_le_exp (mul_nonneg ha hu))
  dsimp only [Q,squareLongTrace]
  rw [integerProbe_successorSquareTriple ((upperSquareIndex_pos _).trans_le hd)]
  dsimp only [B] at hc ⊢
  linarith only [(abs_le.mp (h₁.trans e₁)).1,(abs_le.mp (h₂.trans e₂)).2,hk,hc,neg_abs_le (realSplineTrace 0)]

private theorem square_degree_blocks {β : ℝ} (hβ : 0 ≤ β) (hβ' : β < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, ∀ᶠ T : ℝ in atTop, ∃ n ≥ M, 0 < n ∧
      |2*Real.log n-T| ≤ 18*Real.log (T+2) ∧
      ∀ {d : ℕ}, n ≤ d → (d:ℝ) ≤ (n:ℝ)+(n:ℝ)^β → δ ≤ Q d := by
  by_cases hRH : RiemannHypothesis
  · obtain ⟨δ,hδ,hgood⟩ := successorSquare_degree_gap_of_rh hRH
    obtain ⟨N,hN⟩ := eventually_atTop.mp hgood
    refine ⟨δ,hδ,fun M => ?_⟩
    filter_upwards [tendsto_upperSquareIndex.eventually_ge_atTop (max M N),eventually_ge_atTop (Real.exp 1)]
      with T hn hT
    have hT₀ := (Real.exp_pos 1).le.trans hT
    have hlog : 1 ≤ Real.log (T+2) := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hT.trans (show T ≤ T+2 by linarith))
    obtain ⟨h₁,h₂⟩ := upperSquareIndex_log_near hT₀
    refine ⟨upperSquareIndex T,(le_max_left _ _).trans hn,upperSquareIndex_pos T,abs_le.mpr ⟨?_,?_⟩,
      fun {d} hd _ => hN d ((le_max_right _ _).trans (hn.trans hd))⟩ <;> linarith only [h₁,h₂,hlog]
  · have hw : 0 < zetaZeroWidth := lt_of_le_of_ne zetaZeroWidth_nonneg
      (Ne.symm (fun he => hRH (riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr he)))
    let a := max 0 (zetaZeroWidth+(β-1)/2)
    have ha : 0 ≤ a := le_max_left _ _
    have haw : a < zetaZeroWidth := max_lt hw (by linarith only [hβ'])
    have hr : 2*zetaZeroWidth+β-1 ≤ 2*a := by linarith only [le_max_right (0:ℝ) (zetaZeroWidth+(β-1)/2)]
    obtain ⟨E,hE⟩ := square_block_loss hβ hβ'.le ha hr
    have hpeak := squareLongTrace_peaks_in_every_logarithmic_window ha haw (E+1)
    refine ⟨1,zero_lt_one,fun M => ?_⟩
    obtain ⟨U,hU⟩ := eventually_atTop.mp (tendsto_upperSquareIndex.eventually_ge_atTop M)
    filter_upwards [hpeak,primeLogarithmicRadius_shape,eventually_ge_atTop (2*|U|),eventually_ge_atTop (Real.exp 1)]
      with T ⟨u,hnear,hp⟩ hshape hT heT
    have hrT : 32*Real.log (T+2) ≤ T := hshape.2
    have hu₀ : 0 ≤ u := by linarith only [(abs_le.mp hnear).1,hrT,abs_nonneg U,hT]
    have huU : U ≤ u := by linarith only [(abs_le.mp hnear).1,hrT,hT,le_abs_self U]
    have hlog : 1 ≤ Real.log (T+2) := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (heT.trans (show T ≤ T+2 by linarith))
    obtain ⟨hl,hu⟩ := upperSquareIndex_log_near hu₀
    refine ⟨upperSquareIndex u,hU u huU,upperSquareIndex_pos u,abs_le.mpr ⟨?_,?_⟩,?_⟩
    · linarith only [(abs_le.mp hnear).1,hl,hlog]
    · linarith only [(abs_le.mp hnear).2,hu,hlog]
    · intro d hd hd'
      linarith only [hp,hE hu₀ hd hd',Real.one_le_exp (mul_nonneg ha hu₀)]

/-- Every sufficiently late log window contains the start of a block of
length n^β for any fixed sublinear power. At every conductor in the block,
all positive multiplicities obey the same ordinary power bound and have
exponentially many full sections at their original radius. -/
theorem original_square_sections_in_long_blocks {β : ℝ} (hβ : 0 ≤ β) (hβ' : β < 1) :
    ∃ (B : ℕ) (γ : ℝ), 0 < B ∧ 0 < γ ∧ ∀ᶠ T : ℝ in atTop, ∃ n : ℕ, 0 < n ∧
      |2*Real.log n-T| ≤ 18*Real.log (T+2) ∧ ∀ {d m : ℕ}, n ≤ d → (d:ℝ) ≤ (n:ℝ)+(n:ℝ)^β → 0 < m →
        let a := m • successorSquareTriple d
        ordinaryPrimeGenerator a ≤ (B:ℚ)^(m^2) ∧
        Real.log (generator a:ℝ)+γ*((d:ℝ)^2+(m:ℝ)^2) ≤ radius a ∧
        2*⌊Real.exp (γ*((d:ℝ)^2+(m:ℝ)^2))⌋₊+1 ≤ (smallSections (generator a:ℝ) (radius a)).card := by
  obtain ⟨δ,hδ,hblock⟩ := square_degree_blocks hβ hβ'
  obtain ⟨γ,hγ,hfull⟩ := all_original_surpluses_of_degree_reserve hδ
  obtain ⟨B,hB,hord⟩ := all_ordinary_generators_of_degree_floor (-δ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hfull.and hord)
  refine ⟨B,γ,hB,hγ,(hblock N).mono ?_⟩
  rintro T ⟨n,hn,hn₁,hT,hgood⟩
  refine ⟨n,hn₁,hT,?_⟩
  intro d m hd hd' hm
  obtain ⟨hf,ho⟩ := hN d (hn.trans hd)
  have hQ := hgood hd hd'
  have h := hf hQ hm
  let a := m • successorSquareTriple d
  let t := γ*((d:ℝ)^2+(m:ℝ)^2)
  change Real.log (generator a:ℝ)+t ≤ radius a at h
  refine ⟨ho (by simpa only [neg_neg] using hQ) hm,h,?_⟩
  have hg : 0 < (generator a:ℝ) := by exact_mod_cast contactGenerator_pos _ _ _
  have he := Real.exp_le_exp.mpr (show t ≤ radius a-Real.log (generator a:ℝ) by linarith only [h])
  rw [Real.exp_sub,Real.exp_log hg] at he
  rw [card_smallSections]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.floor_mono he)) _

#print axioms original_square_sections_in_long_blocks

end GaloisForLFunctions.CountingHolography.Sections

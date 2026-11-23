import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Ceilings
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.LineRange

/-! # Quantized last passing heights of actual omissions -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

def FirstMove (b : SpectralBand 1) (j : ℕ) : Prop :=
  (∀ k < j, (b k).val = occupationWeight k) ∧ (b j).val ≠ occupationWeight j

def passingHeights (b : SpectralBand 1) : Set ℝ := {t | 0 < t ∧ b ∈ ceilingFiber (1/t^2)}
def lastHeight (b : SpectralBand 1) := sSup (passingHeights b)

theorem physical_first_move {b : SpectralBand 1} (hb : b ∈ physicalSpectra 1) : ∃ j, FirstMove b j := by
  classical
  obtain ⟨P,hd,hc,rfl⟩ := hb
  let b := physicalSpectrum P hd hc
  have hpos : 0 < traceLoss (projected P) := by
    have he : traceLoss (projected P) ∈ lossesAtRank 1 := ⟨P,hd,hc,rfl⟩
    rw [lossesAtRank_one] at he
    exact he.1
  have hex : ∃ k, (b k).val ≠ occupationWeight k := by
    by_contra! hz
    have hzero := (all_moment_ceilings_iff b (le_refl (0:ℝ))).mpr (fun k _ => hz k)
    have hh := hzero (⟨2,by norm_num⟩ : GibbsExponent)
    change momentLoss ⟨2,by norm_num⟩ (physicalSpectrum P hd hc) ≤ (0:ℝ)^(2:ℝ) at hh
    rw [momentLoss_two,Real.rpow_two,zero_pow (by decide : 2 ≠ 0)] at hh
    exact hpos.not_ge hh
  exact ⟨Nat.find hex,fun k hk => not_not.mp (Nat.find_min hex hk),Nat.find_spec hex⟩

/-- The first displaced occupation is the least power ceiling admitted by this particular spectrum. -/
theorem ceiling_iff_first_move {j : ℕ} {b : SpectralBand 1} (hj : FirstMove b j) {h : ℝ} (hh : 0 ≤ h) :
    b ∈ ceilingFiber h ↔ occupationWeight j ≤ h := by
  rw [show b ∈ ceilingFiber h ↔ _ from all_moment_ceilings_iff b hh]
  constructor
  · exact fun hc => le_of_not_gt (fun he => hj.2 (hc j he))
  · intro hc k hk
    exact hj.1 k (lt_of_not_ge (fun he => hk.not_ge ((occupationWeight_antitone he).trans hc)))

theorem passing_heights_interval {j : ℕ} {b : SpectralBand 1} (hj : FirstMove b j) :
    passingHeights b = Ioc 0 (Real.sqrt ((j:ℝ)+1)) := by
  ext t
  change (0 < t ∧ b ∈ ceilingFiber (1/t^2)) ↔ 0 < t ∧ t ≤ Real.sqrt ((j:ℝ)+1)
  apply and_congr_right
  intro ht
  have hj' : 0 < (j:ℝ)+1 := by positivity
  rw [ceiling_iff_first_move hj (one_div_pos.mpr (sq_pos_of_pos ht)).le,occupationWeight_eq,← one_div ((j:ℝ)+1),
    one_div_le_one_div hj' (sq_pos_of_pos ht),Real.le_sqrt ht.le hj'.le]

theorem lastHeight_of_first_move {j : ℕ} {b : SpectralBand 1} (hj : FirstMove b j) :
    lastHeight b = Real.sqrt ((j:ℝ)+1) := by
  rw [lastHeight,passing_heights_interval hj,csSup_Ioc (Real.sqrt_pos.mpr (by positivity))]

/-- The cutoff integer of any fixed physical omission exists and is determined uniquely by its entire passing interval. -/
theorem unique_passing_integer {b : SpectralBand 1} (hb : b ∈ physicalSpectra 1) :
    ∃! j : ℕ, passingHeights b = Ioc 0 (Real.sqrt ((j:ℝ)+1)) := by
  obtain ⟨j,hj⟩ := physical_first_move hb
  refine ⟨j,passing_heights_interval hj,?_⟩
  intro k hk
  have he := congrArg sSup (hk.symm.trans (passing_heights_interval hj))
  rw [csSup_Ioc (Real.sqrt_pos.mpr (by positivity)),csSup_Ioc (Real.sqrt_pos.mpr (by positivity))] at he
  have he' := congrArg (fun x : ℝ => x^2) he
  simp only [Real.sq_sqrt (by positivity : 0 ≤ (k:ℝ)+1),Real.sq_sqrt (by positivity : 0 ≤ (j:ℝ)+1)] at he'
  exact_mod_cast add_right_cancel he'

/-- All positive-integer cutoff labels are realized by genuine omissions. -/
theorem realize_first_move (j : ℕ) : ∃ b ∈ physicalSpectra 1, FirstMove b j := by
  let a : SpectralBand 1 := fun k => if k=j then coldEdge 1 k else hotEdge 1 k
  refine ⟨physicalCompletion (j+1) a,completion_physical _ _,?_⟩
  constructor
  · intro k hk
    rw [completion_fixes a (hk.trans (Nat.lt_succ_self j))]
    change (if k=j then coldEdge 1 k else hotEdge 1 k).val = _
    rw [if_neg hk.ne]
    rfl
  · rw [completion_fixes a (Nat.lt_succ_self j)]
    change (if j=j then coldEdge 1 j else hotEdge 1 j).val ≠ _
    rw [if_pos rfl]
    exact (occupationWeight_strictAnti (Nat.lt_succ_self j)).ne

theorem last_height_spectrum :
    lastHeight '' physicalSpectra 1 = range (fun j : ℕ => Real.sqrt ((j:ℝ)+1)) := by
  ext t
  constructor
  · rintro ⟨b,hb,rfl⟩
    obtain ⟨j,hj⟩ := physical_first_move hb
    exact ⟨j,(lastHeight_of_first_move hj).symm⟩
  · rintro ⟨j,rfl⟩
    obtain ⟨b,hb,hj⟩ := realize_first_move j
    exact ⟨b,hb,lastHeight_of_first_move hj⟩

#print axioms physical_first_move
#print axioms passing_heights_interval
#print axioms lastHeight_of_first_move
#print axioms unique_passing_integer
#print axioms realize_first_move
#print axioms last_height_spectrum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

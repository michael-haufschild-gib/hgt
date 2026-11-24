import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.Lines

/-! # Recovering the two energy labels and the damping from a measured Fourier line -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

/-- Logarithmic loss relative to the observed zero-frequency coefficient. -/
def lineLoss (x ω : ℝ) := -Real.log ‖overlapCoefficient x ω / overlapCoefficient x 0‖

theorem lineLoss_reduced {x : ℝ} (hx : 1/2 < x) {a b : ℕ+} (hc : a.Coprime b) :
    lineLoss x (gapFrequency (a,b)) = (x+x)*(energy a+energy b) := by
  rw [lineLoss,relative_overlap_line hx hc,norm_heat,Complex.ofReal_re,Real.log_exp,energy_mul]
  ring

/-- Measured frequency gives the energy difference; measured line intensity gives the energy sum. -/
theorem read_reduced_energies {x : ℝ} (hx : 1/2 < x) {a b : ℕ+} (hc : a.Coprime b) :
    let ω := gapFrequency (a,b)
    ((lineLoss x ω/(x+x)+ω/2)/2,(lineLoss x ω/(x+x)-ω/2)/2) = (energy a,energy b) := by
  dsimp only
  rw [lineLoss_reduced hx hc,mul_div_cancel_left₀ _ (by linarith : x+x ≠ 0),gapFrequency]
  apply Prod.ext <;> dsimp only <;> ring

/-- The excess over damping times frequency measures only the smaller label on a positive line. -/
theorem lineLoss_excess {x : ℝ} (hx : 1/2 < x) {a b : ℕ+} (hc : a.Coprime b) :
    lineLoss x (gapFrequency (a,b))-x*gapFrequency (a,b) = (4*x)*energy b := by
  rw [lineLoss_reduced hx hc,gapFrequency]
  ring

theorem gapFrequency_one_right (n : ℕ+) : gapFrequency (n,1) = 2*energy n := by
  simp [gapFrequency,energy]

private theorem vacuum_coprime (n : ℕ+) : n.Coprime 1 := PNat.coprime_coe.mp (by simp)

private theorem vacuum_observed {x : ℝ} (hx : 1/2 < x) (n : ℕ+) : overlapCoefficient x (2*energy n) ≠ 0 :=
  (overlapCoefficient_support hx _).mpr ⟨n,1,vacuum_coprime n,gapFrequency_one_right n⟩

/-- Set of losses per unit frequency on positive lines with nonzero observed weight. -/
def observedLossRates (x : ℝ) : Set ℝ := {r | ∃ ω : ℝ, 0 < ω ∧ overlapCoefficient x ω ≠ 0 ∧
  r = lineLoss x ω/ω}

theorem vacuum_loss_rate {x : ℝ} (hx : 1/2 < x) (n : ℕ+) (hn : 0 < energy n) :
    lineLoss x (2*energy n)/(2*energy n) = x := by
  have he := lineLoss_excess hx (vacuum_coprime n)
  rw [gapFrequency_one_right,show energy 1 = 0 by simp [energy],mul_zero,sub_eq_zero] at he
  exact (div_eq_iff (mul_pos (by positivity) hn).ne').mpr he

/-- The damping is the least of the measured positive-frequency loss rates. -/
theorem damping_isLeast {x : ℝ} (hx : 1/2 < x) : IsLeast (observedLossRates x) x := by
  constructor
  · have h2 : 0 < energy (2:ℕ+) := Real.log_pos (by change (1:ℝ)<2; norm_num)
    exact ⟨2*energy (2:ℕ+),mul_pos (by positivity) h2,vacuum_observed hx 2,(vacuum_loss_rate hx 2 h2).symm⟩
  · rintro _ ⟨ω,hω,hC,rfl⟩
    obtain ⟨a,b,hc,rfl⟩ := (overlapCoefficient_support hx _).mp hC
    apply (le_div_iff₀ hω).mpr
    apply sub_nonneg.mp
    rw [lineLoss_excess hx hc]
    exact mul_nonneg (by linarith) (Real.log_nonneg (by exact_mod_cast b.pos))

/-- Membership can be tested from the time signal alone by minimizing over the other observed lines. -/
def minimumLossLine (x ω : ℝ) : Prop :=
  0 < ω ∧ overlapCoefficient x ω ≠ 0 ∧ IsLeast (observedLossRates x) (lineLoss x ω/ω)

theorem minimumLossLine_iff {x ω : ℝ} (hx : 1/2 < x) :
    minimumLossLine x ω ↔ ∃ n : ℕ+, 0 < energy n ∧ 2*energy n = ω := by
  constructor
  · rintro ⟨hω,hC,hmin⟩
    obtain ⟨a,b,hc,rfl⟩ := (overlapCoefficient_support hx _).mp hC
    have he := (div_eq_iff hω.ne').mp (hmin.unique (damping_isLeast hx))
    have hz : (4*x)*energy b = 0 := (lineLoss_excess hx hc).symm.trans (sub_eq_zero.mpr he)
    have hb := (mul_eq_zero.mp hz).resolve_left (by linarith)
    have hb1 : b = 1 := label_of_energy_eq (hb.trans (by simp [energy]))
    subst b
    rw [gapFrequency_one_right] at hω ⊢
    exact ⟨a,by linarith,rfl⟩
  · rintro ⟨n,hn,rfl⟩
    refine ⟨mul_pos (by positivity) hn,vacuum_observed hx n,?_⟩
    rw [vacuum_loss_rate hx n hn]
    exact damping_isLeast hx

#print axioms lineLoss_reduced
#print axioms read_reduced_energies
#print axioms lineLoss_excess
#print axioms gapFrequency_one_right
#print axioms vacuum_loss_rate
#print axioms damping_isLeast
#print axioms minimumLossLine_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

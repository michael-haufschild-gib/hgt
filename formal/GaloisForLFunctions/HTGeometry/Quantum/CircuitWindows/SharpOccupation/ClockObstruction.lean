import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Entropy lower bound for a syndetic return clock -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

/-- A return in every length-G interval bounds the unit-resolved mean
spacing by G+1, including for an observation begun at the identity. -/
private theorem mean_le_clock {n j : ℕ} {H : selfAdjoint (Register n)} {ε G : ℝ} {t : ℕ → ℝ}
    (ht : records H j ε 0 t) (hclock : ∀ u : ℝ, ∃ v ∈ Icc u (u+G), v ∈ visitSet H j ε)
    (i : ℕ) (hi : 0 < i) : (t i-0)/i ≤ G+1 := by
  have h (m : ℕ) : t m ≤ (m:ℝ)*(G+1) := by
    induction m with
    | zero => simp only [ht.1,Nat.cast_zero,zero_mul,le_refl]
    | succ m ih =>
      obtain ⟨v,hv,hcheap⟩ := hclock (t m+1)
      have hstep := ((ht.2 m).2 ⟨hv.1,hcheap⟩).trans hv.2
      rw [Nat.cast_succ,add_mul,one_mul]
      linarith only [hstep,ih]
  rw [sub_zero,div_le_iff₀ (Nat.cast_pos.mpr hi),mul_comm]
  exact h i

/-- Every admissible clock for polynomial or other subcritical budgets
has at least the lower exponential rate of the corresponding mean spacing. -/
theorem gaussian_return_clock_floor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ, subcriticalBudget s →
      ∀ ε ∈ Ioo (0:ℝ) (Real.sqrt 2), ∀ b : ℝ, physicalArc ε < b →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        ∀ j ≤ s N, ∀ G : ℝ, (∀ u : ℝ, ∃ v ∈ Icc u (u+G), v ∈ visitSet H j ε) →
          1/b^D < G+1 := by
  filter_upwards [gaussian_physical_return_rates] with ω hw
  intro s hs ε hε b hb
  have hx := (physicalArc_spec hε.1 hε.2).1
  obtain ⟨l,hl,hlx⟩ := exists_between hx.1
  filter_upwards [hw s hs ε hε l b hl hlx hb] with k hk
  intro N D H j hj G hG
  obtain ⟨t,ht,hbound⟩ := (hk j hj 0).2
  obtain ⟨i,hi,hr⟩ := ((eventually_gt_atTop (0:ℕ)).and hbound).exists
  exact hr.1.trans_le (mean_le_clock ht hG i hi)

/-- Even the smallest admissible empty-circuit clock leaves the corrected
deadline pG/(1-p) larger than 6ᴰ when p=(3/8)ᴰ. -/
theorem gaussian_first_deadline_certificate_floor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let p := (3/8:ℝ)^D
      ∀ G : ℝ, (∀ u : ℝ, ∃ v ∈ Icc u (u+G), v ∈ visitSet H 0 (1/10)) →
        (16:ℝ)^D < G+1 ∧ (6:ℝ)^D < p*G/(1-p) := by
  have he : (1/10:ℝ) ∈ Ioo 0 (Real.sqrt 2) := ⟨by norm_num, by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    nlinarith only [hh, Real.sqrt_nonneg 2]⟩
  obtain ⟨hx,ht⟩ := physicalArc_spec he.1 he.2
  have hx' : physicalArc (1/10) < 1/16 := by
    have h := three_mul_le_arcTolerance (x := 1/24) (by norm_num) (by norm_num)
    have hh : zeroGateArcTolerance (physicalArc (1/10)) < zeroGateArcTolerance (1/24) := by
      rw [ht]; linarith only [h]
    have hsmall := (strictMonoOn_zeroGateArcTolerance.lt_iff_lt
      ⟨hx.1.le,hx.2.le⟩ (by constructor <;> norm_num : (1/24:ℝ) ∈ Icc 0 (1/2))).mp hh
    exact hsmall.trans (by norm_num)
  filter_upwards [gaussian_return_clock_floor] with ω hw
  filter_upwards [hw _ (polynomial_subcritical 0) (1/10) he (1/16) hx'] with k hk
  intro N D H p G hG
  have h16 := hk 0 (Nat.zero_le _) G hG
  change 1/(1/16:ℝ)^D < G+1 at h16
  have hinv : 1/(1/16:ℝ)^D = (16:ℝ)^D := by simp [one_div]
  rw [hinv] at h16
  have hD : 0 < D := by dsimp [D]; positivity
  have hp : 0 < p := pow_pos (by norm_num) D
  have hp1 : p < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hD.ne'
  have hsix : p*(16:ℝ)^D = (6:ℝ)^D := by
    dsimp only [p]; rw [←mul_pow]; norm_num
  have hh := mul_lt_mul_of_pos_left h16 hp
  rw [hsix] at hh
  have h6 : 1 ≤ (6:ℝ)^D := one_le_pow₀ (by norm_num)
  refine ⟨h16,(lt_div_iff₀ (sub_pos.mpr hp1)).mpr ?_⟩
  nlinarith only [hh,mul_le_mul_of_nonneg_right h6 hp.le]

#print axioms gaussian_return_clock_floor
#print axioms gaussian_first_deadline_certificate_floor
end
end GaloisForLFunctions.HTGeometry.SharpOccupation

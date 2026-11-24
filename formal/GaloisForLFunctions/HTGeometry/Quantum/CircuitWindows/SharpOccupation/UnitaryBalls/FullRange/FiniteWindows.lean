import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FiniteRecords.Transfer
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.FullRange.GaussianRate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.HighPrecision.ScalarWindows

/-! # Sharp affordable-time exponents on finite windows of a frozen chain -/
open Set Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
noncomputable section

private theorem dimension_tendsto : Tendsto (fun k : ℕ => (2:ℕ)^(k+3)) atTop atTop :=
  tendsto_atTop_mono (fun k => (show k ≤ k+3 by omega).trans (Nat.lt_two_pow_self (n:=k+3)).le) tendsto_id

private theorem power_slack {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ᶠ k : ℕ in atTop, 2*a^((2:ℕ)^(k+3)) < b^((2:ℕ)^(k+3)) := by
  have h : 1 < b/a := (lt_div_iff₀ ha).mpr (by rwa [one_mul])
  filter_upwards [((tendsto_pow_atTop_atTop_of_one_lt h).comp dimension_tendsto).eventually_gt_atTop 2] with k hk
  change 2 < (b/a)^((2:ℕ)^(k+3)) at hk
  rw [div_pow] at hk
  exact (lt_div_iff₀ (pow_pos ha _)).mp hk

/-- Every interval longer than twice the fine recurrence deadline has
the sharp long-time occupation exponent. The same prefix and deadline
work for every origin and every gate budget below the given schedule. -/
theorem gaussian_finite_occupation_full :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ, subcriticalBudget s →
      ∀ x ∈ Ioo (0:ℝ) 1, ∀ l b : ℝ, 0 < l → l < x → x < b →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D : ℕ := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        ∀ j ≤ s N, ∀ a T : ℝ, 2*(2:ℝ)^(D^c) ≤ T →
          l^D < visitFraction H j (zeroGateArcTolerance x) a (a+T) ∧
          visitFraction H j (zeroGateArcTolerance x) a (a+T) < b^D := by
  obtain ⟨c,hclock⟩ := SpectralJets.HighPrecision.gaussian_fine_scalar_windows
  refine ⟨c,?_⟩
  filter_upwards [hclock,UnitaryBalls.gaussian_occupation_rate] with ω hc ho
  intro s hs x hx l b hl hlx hxb
  obtain ⟨p,hlp,hpx⟩ := exists_between hlx
  obtain ⟨y,hpy,hyx⟩ := exists_between hpx
  obtain ⟨z,hxz,hz⟩ := exists_between (lt_min hxb hx.2)
  obtain ⟨q,hzq,hqb⟩ := exists_between (hz.trans_le (min_le_left ..))
  have hy : y ∈ Ioo (0:ℝ) 1 := ⟨(hl.trans hlp).trans hpy,hyx.trans hx.2⟩
  have hz' : z ∈ Ioo (0:ℝ) 1 := ⟨hx.1.trans hxz,hz.trans_le (min_le_right ..)⟩
  let tol := zeroGateArcTolerance
  have htol {u v : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) (hv : v ∈ Ioo (0:ℝ) 1) (huv : u<v) :
      tol u < tol v := strictMonoOn_zeroGateArcTolerance_full ⟨hu.1.le,hu.2.le⟩ ⟨hv.1.le,hv.2.le⟩ huv
  have hδ : Tendsto (fun k : ℕ => (1/2:ℝ)^((2:ℕ)^(k+3))) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp dimension_tendsto
  filter_upwards [hc,ho s hs y hy p 1 (hl.trans hlp).le hpy hy.2,
    ho s hs z hz' 0 q le_rfl hz'.1 hzq,power_slack hl hlp,power_slack (hz'.1.trans hzq) hqb,
    hδ.eventually_lt_const (sub_pos.mpr (htol hy hx hyx)),hδ.eventually_lt_const (sub_pos.mpr (htol hx hz' hxz))]
    with k hper hlow hhigh hls hbs hδl hδu
  intro N D H j hj a T hT
  let G := (2:ℝ)^(D^c)
  let δ := 1/(2:ℝ)^D
  have hG : 0 < G := pow_pos (by norm_num) _
  have ht : G < T := by change 2*G ≤ T at hT; linarith only [hG,hT]
  have hTpos := hG.trans ht
  have h₁ : tol y+δ ≤ tol x := by
    rw [one_div_pow] at hδl
    change δ < tol x-tol y at hδl
    linarith only [hδl]
  have h₂ : tol x+δ ≤ tol z := by
    rw [one_div_pow] at hδu
    change δ < tol z-tol x at hδu
    linarith only [hδu]
  have hw := circuit_window_transfer H j h₁ h₂ hG hper
    (hlow.mono fun _ h => (h j hj).1.le) (hhigh.mono fun _ h => (h j hj).2.le) a T ht
  let V := volume.real (visitSet H j (tol x) ∩ Icc a (a+T))
  have hBound : p^D*(T-G) ≤ V ∧ V ≤ q^D*(T+G) := hw
  change 2*G ≤ T at hT
  have hlo := (mul_le_mul_of_nonneg_left (show T/2 ≤ T-G by linarith only [hT]) (pow_pos (hl.trans hlp) D).le).trans hBound.1
  have hhi := hBound.2.trans (mul_le_mul_of_nonneg_left (show T+G ≤ 2*T by linarith only [ht]) (pow_pos (hz'.1.trans hzq) D).le)
  change 2*l^D < p^D at hls
  change 2*q^D < b^D at hbs
  change l^D < V/(a+T-a) ∧ V/(a+T-a) < b^D
  rw [add_sub_cancel_left]
  refine ⟨(lt_div_iff₀ hTpos).mpr ?_,(div_lt_iff₀ hTpos).mpr ?_⟩
  · linarith only [hlo,mul_lt_mul_of_pos_right hls hTpos]
  · linarith only [hhi,mul_lt_mul_of_pos_right hbs hTpos]

#print axioms gaussian_finite_occupation_full
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords

import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedGaps

/-!
# Nonzero boundary singularities of the balanced partition

The balanced labels stay in one open semicircle at the first radix
frequency. The rotated trace therefore dominates a fixed positive fraction
of the absolute heat sum all the way to the isometry boundary.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open Filter
open scoped Topology ComplexConjugate

/-- Dirichlet partition on the positive cutoffs with exact occupation balance. -/
def balancedPartition (t : ExceptionalTime) (j : ℕ) (s : ℂ) : ℂ :=
  ∑' x, balancedHeat t j s x

/-- Positive radial mass of the balanced gas. -/
def balancedMass (t : ExceptionalTime) (j : ℕ) (β : ℝ) : ℝ :=
  ∑' x, ‖balancedHeat t j (β:ℂ) x‖

theorem balanced_partition_real (t : ExceptionalTime) (j : ℕ) (β : ℝ) :
    balancedPartition t j (β:ℂ) = (balancedMass t j β:ℂ) := by
  rw [balancedPartition,balancedMass,Complex.ofReal_tsum]
  apply tsum_congr
  intro x
  unfold balancedHeat
  rw [norm_heat,Complex.ofReal_re,heat,Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]

theorem balanced_mass_blowup (t : ExceptionalTime) (j : ℕ) :
    Tendsto (balancedMass t j) (𝓝[>] (1/2:ℝ)) atTop := by
  classical
  let u : ℝ := 1/2
  let w (β : ℝ) (x : PositiveBalancedCutoff t j) := ‖balancedHeat t j (β:ℂ) x‖
  have hn : ¬Summable (w u) := by
    change ¬Summable (fun x => ‖balancedHeat t j (u:ℂ) x‖)
    rw [balanced_heat_summable_iff,Complex.ofReal_re]
    exact lt_irrefl _
  have hc (x : PositiveBalancedCutoff t j) : Continuous (fun β => w β x) := by
    change Continuous (fun β : ℝ => ‖Complex.exp (-(β:ℂ)*(energy (⟨x.val.val,x.property⟩:ℕ+):ℂ))‖)
    fun_prop
  apply tendsto_atTop.mpr
  intro M
  have hF : ∃ F : Finset (PositiveBalancedCutoff t j), M < ∑ x ∈ F, w u x := by
    by_contra! hb
    exact hn (summable_of_sum_le (fun _ => norm_nonneg _) hb)
  obtain ⟨F,hF⟩ := hF
  have hcont : Continuous (fun β => ∑ x ∈ F, w β x) := continuous_finsetSum _ fun x _ => hc x
  have hlocal : ∀ᶠ β in 𝓝[>] u, M < ∑ x ∈ F, w β x :=
    (hcont.continuousAt.tendsto.eventually (Ioi_mem_nhds hF)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hlocal,self_mem_nhdsWithin] with β hm hβ
  have hs : Summable (w β) := (balanced_heat_summable_iff t j (β:ℂ)).mpr hβ
  exact hm.le.trans (hs.sum_le_tsum F (fun x _ => norm_nonneg _))

theorem balanced_partition_real_blowup (t : ExceptionalTime) (j : ℕ) :
    Tendsto (fun β : ℝ => (balancedPartition t j (β:ℂ)).re) (𝓝[>] (1/2:ℝ)) atTop := by
  simpa only [balanced_partition_real,Complex.ofReal_re] using balanced_mass_blowup t j

private theorem rotated_exp (a β τ E : ℝ) :
    (Complex.exp ((a:ℂ)*Complex.I)*Complex.exp (-(⟨β,τ⟩:ℂ)*(E:ℂ))).re =
      Real.cos (a-τ*E)*Real.exp (-β*E) := by
  rw [← Complex.exp_add,Complex.exp_re]
  simp [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,sub_eq_add_neg,mul_comm]

/-- A unit rotation works simultaneously for all temperatures and all balanced labels. -/
theorem balanced_resonant_cone (t : ExceptionalTime) (j : ℕ) :
    let τ := Real.pi/energy (tailRadix t j)
    ∃ A : ℂ, ‖A‖ = 1 ∧ ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (x : PositiveBalancedCutoff t j),
      c*‖balancedHeat t j (β:ℂ) x‖ ≤ (A*balancedHeat t j ⟨β,τ⟩ x).re := by
  let τ := Real.pi/energy (tailRadix t j)
  obtain ⟨θ,hθ₀,hθ,harc⟩ := balanced_clock_arc t j
  let a := θ/2
  have ha₀ : 0 ≤ a := div_nonneg hθ₀ (by norm_num)
  have ha : a < Real.pi/2 := div_lt_div_of_pos_right hθ (by norm_num)
  refine ⟨Complex.exp ((a:ℂ)*Complex.I),by simp [Complex.norm_exp],Real.cos a,
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [ha₀,Real.pi_pos],ha⟩,?_⟩
  intro β x
  let E := Real.log (x.val.val:ℝ)
  obtain ⟨k,hlo,hhi⟩ := harc x
  let v := τ*E-(k:ℝ)*(2*Real.pi)
  change 0 ≤ v at hlo
  change v ≤ θ at hhi
  have habs : |a-v| ≤ a := abs_le.mpr ⟨by dsimp only [a]; linarith only [hhi],by linarith only [hlo]⟩
  have hcut : a-τ*E = (a-v)-(k:ℝ)*(2*Real.pi) := by dsimp only [v]; ring
  have hcos : Real.cos a ≤ Real.cos (a-τ*E) := by
    rw [hcut,Real.cos_sub_nat_mul_two_pi,← Real.cos_abs (a-v)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith only [ha,Real.pi_pos]) habs
  change Real.cos a*‖heat (β:ℂ) (⟨x.val.val,x.property⟩:ℕ+)‖ ≤
    (Complex.exp ((a:ℂ)*Complex.I)*Complex.exp (-(⟨β,τ⟩:ℂ)*(E:ℂ))).re
  rw [rotated_exp,norm_heat,Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right hcos (Real.exp_pos _).le

private theorem positive_frequency (t : ExceptionalTime) (j : ℕ) :
    let τ := Real.pi/energy (tailRadix t j)
    Tendsto (fun β : ℝ => ‖balancedPartition t j ⟨β,τ⟩‖) (𝓝[>] (1/2:ℝ)) atTop := by
  let τ := Real.pi/energy (tailRadix t j)
  obtain ⟨A,hA,c,hc,hcone⟩ := balanced_resonant_cone t j
  have bound (β : {r : ℝ // 1/2 < r}) : c*balancedMass t j β.val ≤ ‖balancedPartition t j ⟨β.val,τ⟩‖ := by
    let z : ℂ := ⟨β.val,τ⟩
    have h₀ := (balanced_heat_summable_iff t j (β.val:ℂ)).mpr β.property
    have h₁ := ((balanced_heat_summable_iff t j z).mpr β.property).of_norm
    have hA₁ := h₁.mul_left A
    have hR := (Complex.hasSum_re hA₁.hasSum).summable
    have h := Summable.tsum_le_tsum (hcone β.val) (h₀.mul_left c) hR
    rw [tsum_mul_left,← Complex.re_tsum hA₁,tsum_mul_left] at h
    change c*balancedMass t j β.val ≤ (A*balancedPartition t j z).re at h
    calc c*balancedMass t j β.val ≤ (A*balancedPartition t j z).re := h
         _ ≤ ‖A*balancedPartition t j z‖ := Complex.re_le_norm _
         _ = ‖balancedPartition t j z‖ := by rw [norm_mul,hA,one_mul]
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [(balanced_mass_blowup t j).eventually_ge_atTop (M/c),self_mem_nhdsWithin] with β hb hβ
  apply le_trans _ (bound ⟨β,hβ⟩)
  simpa only [mul_comm] using (div_le_iff₀ hc).mp hb

private theorem conjugate_reading (t : ExceptionalTime) (j : ℕ) (β τ : ℝ) :
    balancedPartition t j ⟨β,-τ⟩ = conj (balancedPartition t j ⟨β,τ⟩) := by
  rw [balancedPartition,balancedPartition,Complex.conj_tsum]
  apply tsum_congr
  intro x
  have he : conj (⟨β,τ⟩ : ℂ) = ⟨β,-τ⟩ := Complex.ext (Complex.conj_re _) (Complex.conj_im _)
  unfold balancedHeat heat
  rw [← Complex.exp_conj,map_mul,map_neg,Complex.conj_ofReal,he]

/-- The balanced partition blows up at both conjugate nonzero first clock frequencies. -/
theorem balanced_partition_resonant_blowup (t : ExceptionalTime) (j : ℕ) :
    let τ := Real.pi/energy (tailRadix t j)
    Tendsto (fun β : ℝ => ‖balancedPartition t j ⟨β,τ⟩‖) (𝓝[>] (1/2:ℝ)) atTop ∧
    Tendsto (fun β : ℝ => ‖balancedPartition t j ⟨β,-τ⟩‖) (𝓝[>] (1/2:ℝ)) atTop := by
  refine ⟨positive_frequency t j,?_⟩
  simpa only [conjugate_reading,Complex.norm_conj] using positive_frequency t j

#print axioms balanced_partition_real_blowup
#print axioms balanced_mass_blowup
#print axioms balanced_resonant_cone
#print axioms balanced_partition_resonant_blowup

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

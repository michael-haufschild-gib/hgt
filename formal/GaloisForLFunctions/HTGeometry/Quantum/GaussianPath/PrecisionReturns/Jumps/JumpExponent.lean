import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Jumps.VisitJump

/-! # Size and location of jumps of the first-return clock -/
open Filter Topology Set Real Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Jumps
noncomputable section

/-- Difference between the limiting first date at stricter precisions and
the attained first date at precision ρ. -/
def leftJump (v : ℝ→ℝ) (ρ : ℝ) := sInf (v '' Ioo 0 ρ)-v ρ

private abbrev rate (f : ℝ→ℝ) (ε : ℝ) := log (f ε)/log (1/ε)

/-- A record floor reached within one time unit has the same logarithmic
precision as the starting tolerance. Its actual one-sided jump has the
full return exponent whenever the skipped interval has that exponent. -/
private theorem jump_rate {v ρ B : ℝ→ℝ} {a d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hpos : ∀ ε > 0, a ≤ v ε) (hv : Tendsto (rate v) (𝓝[>] 0) (𝓝 d))
    (hB : Tendsto B (𝓝[>] 0) atTop) (hb : Tendsto (rate B) (𝓝[>] 0) (𝓝 d))
    (hr : ∀ ε > 0, ρ ε∈Ioc 0 ε ∧ v (ρ ε)∈Icc (v ε) (v ε+1) ∧
      ∀ δ∈Ioo 0 (ρ ε), v ε+1+B ε ≤ v δ) :
    Tendsto (fun ε => log (1/ρ ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 1) ∧
    Tendsto (rate (fun ε => leftJump v (ρ ε))) (𝓝[>] 0) (𝓝 d) := by
  have ht : Tendsto ρ (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g:=fun _ : ℝ => 0) (h:=id)
        tendsto_const_nhds (tendsto_id.mono_left nhdsWithin_le_nhds)
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact (hr ε hε).1.1.le
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact (hr ε hε).1.2
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hr ε hε).1.1
  have hsum := hv.add (tendsto_const_div_log_one_div (log (1+1/a)))
  rw [add_zero] at hsum
  have hnum : Tendsto (rate (fun ε => v (ρ ε))) (𝓝[>] 0) (𝓝 d) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hv hsum
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
      exact div_le_div_of_nonneg_right (log_le_log (ha.trans_le (hpos ε hε.1)) (hr ε hε.1).2.1.1)
        (log_pos ((one_lt_div hε.1).mpr hε.2)).le
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
      have h := hr ε hε.1
      have hm : v ε+1 ≤ v ε*(1+1/a) := by
        rw [mul_add,mul_one,←mul_div_assoc,mul_one]
        exact add_le_add le_rfl ((one_le_div ha).mpr (hpos ε hε.1))
      change log (v (ρ ε))/log (1/ε) ≤ log (v ε)/log (1/ε)+log (1+1/a)/log (1/ε)
      rw [←add_div,←log_mul (ha.trans_le (hpos ε hε.1)).ne' (by positivity : 0 < 1+1/a).ne']
      exact div_le_div_of_nonneg_right (log_le_log (ha.trans_le (hpos _ h.1.1)) (h.2.1.2.trans hm))
        (log_pos ((one_lt_div hε.1).mpr hε.2)).le
  have hden := hv.comp ht
  have hratio := hnum.div hden hd.ne'
  rw [div_self hd.ne'] at hratio
  have hρlim : Tendsto (fun ε => log (1/ρ ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    apply hratio.congr'
    filter_upwards [hden.eventually_const_lt hd] with ε hε
    have hne : log (v (ρ ε))≠0 := by
      intro hz
      change 0 < log (v (ρ ε))/log (1/ρ ε) at hε
      rw [hz,zero_div] at hε
      exact hε.false
    change (log (v (ρ ε))/log (1/ε))/(log (v (ρ ε))/log (1/ρ ε))=_
    rw [div_div_div_comm,div_self hne,one_div,inv_div]
  have hhalf := ((scaled_exponent (f:=v) (by norm_num : (0:ℝ)<1/2) hv).comp ht).mul hρlim
  rw [mul_one] at hhalf
  have hu : Tendsto (rate (fun ε => v (ρ ε/2))) (𝓝[>] 0) (𝓝 d) := by
    apply hhalf.congr'
    filter_upwards [ht.eventually (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
    have hp := (log_pos ((one_lt_div hε.1).mpr hε.2)).ne'
    change log (v ((1/2)*ρ ε))/log (1/ρ ε)*(log (1/ρ ε)/log (1/ε))=_
    rw [one_div_mul_eq_div]
    dsimp only [rate]
    field_simp [hp]
  refine ⟨hρlim,tendsto_of_tendsto_of_tendsto_of_le_of_le' hb hu ?_ ?_⟩
  all_goals
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ),hB.eventually_gt_atTop 0] with ε hε hposB
    have h := hr ε hε.1
    have hh : ρ ε/2∈Ioo 0 (ρ ε) := ⟨half_pos h.1.1,half_lt_self h.1.1⟩
    have hn := mem_image_of_mem v hh
    have hbd : ∀ b∈v '' Ioo 0 (ρ ε), v ε+1+B ε ≤ b := by
      rintro _ ⟨δ,hδ,rfl⟩
      exact h.2.2 δ hδ
    have hlow := le_csInf ⟨_,hn⟩ hbd
    have hhigh := csInf_le ⟨_,hbd⟩ hn
    have hlo : B ε ≤ leftJump v (ρ ε) := by unfold leftJump; linarith only [hlow,h.2.1.2]
    have hhi : leftJump v (ρ ε) ≤ v (ρ ε/2) := (sub_le_self _ (ha.trans_le (hpos _ h.1.1)).le).trans hhigh
    have hlog := (log_pos ((one_lt_div hε.1).mpr hε.2)).le
    first | exact div_le_div_of_nonneg_right (log_le_log hposB hlo) hlog
          | exact div_le_div_of_nonneg_right (log_le_log (hposB.trans_le hlo) hhi) hlog

/-- On every physical prefix and for each budget below half the number
of sites, arbitrarily fine changes of tolerance skip time intervals
of size ε^(-(2^N-2)+o(1)). The threshold where the jump occurs is
ε^(1+o(1)). The observation origin may be chosen from the draw. -/
theorem gaussian_first_return_jump_exponent :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a > (0:ℝ), ∀ s : ℕ, 2*s < N →
        let v := firstVisit H a s
        ∃ ρ : ℝ→ℝ, (∀ ε > 0, ρ ε∈Ioc 0 ε ∧ v (ρ ε)∈Icc (v ε) (v ε+1)) ∧
          Tendsto (fun ε => log (1/ρ ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 1) ∧
          Tendsto (fun ε => log (leftJump v (ρ ε))/log (1/ε)) (𝓝[>] 0) (𝓝 ((2^N-2:ℕ):ℝ)) := by
  classical
  filter_upwards [gaussian_first_return_precision_jumps,gaussian_first_return_precision_exponent] with ω hj he k
  intro N H a ha s hs v
  obtain ⟨B,hB,hb,h⟩ := hj k
  let ρ (ε : ℝ) := if hp : 0 < ε then (h a ha s hs ε hp).choose else 0
  have hr (ε : ℝ) (hp : 0 < ε) := (h a ha s hs ε hp).choose_spec
  have hr' (ε : ℝ) (hp : 0 < ε) : ρ ε∈Ioc 0 ε ∧ v (ρ ε)∈Icc (v ε) (v ε+1) ∧
      ∀ δ∈Ioo 0 (ρ ε), v ε+1+B ε ≤ v δ := by
    simp only [ρ,dif_pos hp]
    exact ⟨(hr ε hp).1,(hr ε hp).2.1 _ ⟨le_rfl,(hr ε hp).1.2⟩,(hr ε hp).2.2⟩
  have hdim : 2 < (2:ℕ)^N := (by norm_num : 2 < (2:ℕ)^3).trans_le
    (Nat.pow_le_pow_right (by decide) (by dsimp [N]; omega))
  refine ⟨ρ,fun ε hp => ⟨(hr' ε hp).1,(hr' ε hp).2.1⟩,?_⟩
  exact jump_rate ha (by exact_mod_cast (show 0 < 2^N-2 by omega))
    (fun ε hp => (firstVisit_isLeast H a s hp).1.1) (he k a ha s hs).2.1 hB hb hr'

#print axioms gaussian_first_return_jump_exponent
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Jumps

import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.PairDuration

/-! # The largest local span of physical visits has a sharp budget correction -/
open Real Matrix Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
open FirstAscent SharpOccupation
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- Largest separation at most b between two dates at the stated budget and error. -/
def localVisitSpan {N : ℕ} (H : selfAdjoint (Reg N)) (s : ℕ) (ε b : ℝ) :=
  sSup {t ∈ Icc (0:ℝ) b | ∃ v ∈ visitSet H s ε, v+t ∈ visitSet H s ε}

/-- The identity visit gives the correct order for the largest span over
all dates. Each additional sparse gate delays each end on the same scale
as the first ascent. -/
theorem gaussian_maximal_physical_span :
    ∃ b c C : ℝ, ∃ M : ℕ, 0<b ∧ 0<c ∧ 0<C ∧ 0<M ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
        let N := n+2
        let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
        let W := circuitHamiltonianSpectralWidth H
        ∀ s : ℕ, 0<s → M*s≤N → let F := (s:ℝ)*sqrt (log (N/s))/(N:ℝ)^2
          localVisitSpan H s (1/10) b-8*arcsin (1/20)/W ∈ Icc (c*F) (C*F) := by
  obtain ⟨b,C,k,hb,hC,hk,hu⟩ := gaussian_pair_duration
  obtain ⟨c,_,m,hc,_,hm,hl⟩ := gaussian_first_ascent_window
  obtain ⟨a,_,ha,_,hw⟩ := gaussian_initial_clock
  let M := max (2*k) m
  let θ := arcsin (1/20)
  have hθ : 0 < θ := arcsin_pos.mpr (by norm_num)
  obtain ⟨L,hL⟩ := exists_nat_ge ((8*θ/a+2*c)/b)
  refine ⟨b,2*c,2*C,M,hb,mul_pos two_pos hc,mul_pos two_pos hC,hm.trans_le (le_max_right ..),?_⟩
  filter_upwards [hu,hl,hw] with ω hu hl hw
  filter_upwards [hu,hl,hw,eventually_ge_atTop L] with n hu hl hw hn
  intro N H W s hs hsize F
  have hN : 0<(N:ℝ) := by dsimp only [N]; positivity
  have hsp : 0<(s:ℝ) := Nat.cast_pos.mpr hs
  have hF : 0≤F := by dsimp only [F]; positivity
  have hW : 0<W := (mul_pos ha hN).trans_le hw.1
  have hm' := (Nat.mul_le_mul_right s (le_max_right ..)).trans hsize
  have hk' : k*(s+s)≤N := by
    calc k*(s+s) = (2*k)*s := by ring
         _ ≤ M*s := Nat.mul_le_mul_right s (le_max_left ..)
         _ ≤ N := hsize
  have hsN := (Nat.le_mul_of_pos_left s hm).trans hm'
  have hscale := budget_mass_bound (L:=1) zero_le_one hsp hN (by exact_mod_cast hsN)
    (by simpa only [one_pow,one_mul] using (show (s:ℝ) ≤ N by exact_mod_cast hsN))
  let T := 4*θ/W+c*F
  have hT : 0≤T := add_nonneg (div_nonneg (mul_nonneg (by norm_num) hθ.le) hW.le) (mul_nonneg hc.le hF)
  have hspan : 2*T ≤ b := by
    have hsmall : F ≤ 1/(N:ℝ) := by
      apply (le_div_iff₀ hN).mpr
      change ((s:ℝ)*sqrt (log (N/s))/(N:ℝ)^2)*(N:ℝ) ≤ _
      rw [show ((s:ℝ)*sqrt (log (N/s))/(N:ℝ)^2)*(N:ℝ) = (s/N)*sqrt (log (N/s)) by field_simp; ring]
      simpa only [one_mul] using hscale
    have hlen : ((8*θ/a+2*c)/b) ≤ (N:ℝ) := hL.trans (by exact_mod_cast (show L≤N by dsimp only [N]; omega))
    have h₁ := div_le_div_of_nonneg_left (show 0≤4*θ by positivity) (mul_pos ha hN) hw.1
    have h₂ := mul_le_mul_of_nonneg_left hsmall hc.le
    calc 2*T ≤ 2*(4*θ/(a*N)+c*(1/(N:ℝ))) := by dsimp only [T]; linarith only [h₁,h₂]
         _ = (8*θ/a+2*c)/(N:ℝ) := by ring
         _ ≤ b := (div_le_iff₀ hN).mpr (by linarith only [(div_le_iff₀ hb).mp hlen])
  have hfit : T ∈ visitSet H s (1/10) := (hl s hs hm').1 T ⟨hT,le_rfl⟩
  have hneg : -T ∈ visitSet H s (1/10) := HasProjectiveCircuitApproximation.neg_time H hfit
  let S := {t ∈ Icc (0:ℝ) b | ∃ v ∈ visitSet H s (1/10), v+t ∈ visitSet H s (1/10)}
  have hmem : 2*T ∈ S := ⟨⟨mul_nonneg two_pos.le hT,hspan⟩,-T,hneg,by rwa [show -T+2*T=T by ring]⟩
  have hlow := le_csSup (s:=S) (show BddAbove S from ⟨b,fun _ h => h.1.2⟩) hmem
  have hhigh : sSup S ≤ 8*θ/W+2*C*F := by
    apply csSup_le ⟨_,hmem⟩
    rintro t ⟨ht,v,hv,ht'⟩
    have hh := hu s s hk' v (v+t) (le_add_of_nonneg_right ht.1) (by simpa only [add_sub_cancel_left] using ht.2) hv ht'
    rw [add_sub_cancel_left] at hh
    have hlog : sqrt (log (N/((s:ℝ)+s))) ≤ sqrt (log (N/s)) :=
      sqrt_le_sqrt (log_le_log (div_pos hN (add_pos hsp hsp))
        (div_le_div_of_nonneg_left hN.le hsp (le_add_of_nonneg_right hsp.le)))
    have hmul := mul_le_mul_of_nonneg_left hlog (add_nonneg hsp.le hsp.le)
    have hscale' := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmul (sq_nonneg _)) hC.le
    dsimp only [F]
    linarith only [hh,hscale']
  change 2*c*F ≤ sSup S-8*θ/W ∧ sSup S-8*θ/W ≤ 2*C*F
  dsimp only [T] at hlow
  exact ⟨by linarith only [hlow],by linarith only [hhigh]⟩

#print axioms gaussian_maximal_physical_span
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents

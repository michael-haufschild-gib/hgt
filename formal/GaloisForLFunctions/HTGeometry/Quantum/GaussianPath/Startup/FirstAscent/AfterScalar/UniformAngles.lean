import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.PhysicalWindow

/-! # Initial gate-budget windows uniform in angular tolerance -/
open MeasureTheory Filter Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.AfterScalar
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- A chord error proportional to time costs a fixed amount of energy width. -/
private theorem chord_deadline {t W f θ : ℝ} (hθ : 0 ≤ θ) (ht : 0 ≤ t) (hf : 0 ≤ f)
    (hw : t*W ≤ π) (h : 2*sin (t*W/4) ≤ 2*sin θ+t*f) : t*(W-4*f) ≤ 4*θ := by
  rcases le_total (t*W/4) θ with hsmall | hlarge
  · nlinarith only [hsmall,mul_nonneg ht hf]
  · have hs := sine_chord_floor hθ hlarge (by linarith only [hw])
    linarith only [hs,h]

/-- Every angular tolerance in [θ₀/2,2θ₀] has the same budget corrections
to its empty exit date, simultaneously in tolerance and gate count. -/
theorem gaussian_uniform_angles :
    ∃ c C a b : ℝ, ∃ M : ℕ, 0 < c ∧ 0 < C ∧ 0 < a ∧ 0 < b ∧ 0 < M ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
        let N := n+2
        let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
        let W := circuitHamiltonianSpectralWidth H
        let θ₀ := arcsin (1/20)
        a*N ≤ W ∧ W ≤ b*N ∧ ∀ s : ℕ, 0 < s → M*s ≤ N →
          let F := (s:ℝ)*sqrt (log ((N:ℝ)/s))/(N:ℝ)^2
          ∀ θ ∈ Icc (θ₀/2) (2*θ₀),
            (∀ t ∈ Icc 0 (4*θ/W+c*F),
              HasProjectiveCircuitApproximation N (2*sin θ) s (unitaryEvolution H.val t)) ∧
            ∀ t ∈ Icc 0 (π/W), HasProjectiveCircuitApproximation N (2*sin θ) s (unitaryEvolution H.val t) →
              t ≤ 4*θ/W+C*F := by
  obtain ⟨B,hB,hfloor⟩ := gaussian_initial_floor
  obtain ⟨a,b,ha,hb,hclock⟩ := gaussian_initial_clock
  obtain ⟨m,hm,hfields⟩ := gaussian_field_delay
  obtain ⟨k,hk⟩ := exists_nat_ge B
  let M := max m (max 42 k)
  let θ₀ := arcsin (1/20)
  have hθ₀ : 0 < θ₀ := arcsin_pos.mpr (by norm_num)
  have hπ : 2*θ₀ ≤ π/4 := by
    have h := GaloisForLFunctions.arcsin_le_pi_half_mul (1/20) (by norm_num) (by norm_num)
    dsimp only [θ₀]; linarith only [h,pi_pos]
  let c := 2*θ₀/(18*b^2)
  let C := π*1344/a^2
  refine ⟨c,C,a,b,M,by dsimp [c]; positivity,by dsimp [C]; positivity,ha,hb,
    hm.trans_le (le_max_left ..),?_⟩
  filter_upwards [hfloor,hclock,hfields] with ω hf hc hl
  filter_upwards [hf,hc,hl] with n hf hc hl
  intro N H W θ₀'
  refine ⟨hc.1,hc.2.1,?_⟩
  intro s hs hsize F θ hθ
  have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
  have hsp : 0 < (s:ℝ) := by exact_mod_cast hs
  have hW := (mul_pos ha hN).trans_le hc.1
  let f := (s:ℝ)*sqrt (log ((N:ℝ)/s))
  have hfn : 0 ≤ f := mul_nonneg hsp.le (sqrt_nonneg _)
  have hM (i : ℕ) (hi : i ≤ M) : i*s ≤ N := (Nat.mul_le_mul_right s hi).trans hsize
  have h42 := hM 42 ((le_max_left 42 k).trans (le_max_right ..))
  have hsN : (s:ℝ) ≤ N := by exact_mod_cast (show s ≤ N by omega)
  have hscale : B ≤ (N:ℝ)/s := (le_div_iff₀ hsp).mpr ((mul_le_mul_of_nonneg_right hk hsp.le).trans
    (by exact_mod_cast hM k ((le_max_right 42 k).trans (le_max_right ..))))
  have hθp : 0 ≤ θ := (half_pos hθ₀).le.trans hθ.1
  constructor
  · intro t ht
    have hcF : c*F ≤ 4*θ*(f/18)/(b*N)^2 := by
      change 2*θ₀/(18*b^2)*(f/(N:ℝ)^2) ≤ _
      have hθ' : 2*θ₀ ≤ 4*θ := by linarith only [show θ₀/2 ≤ θ from hθ.1]
      calc _ = (2*θ₀)*(f/18)/(b*N)^2 := by field_simp
           _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hθ' (by positivity)) (sq_nonneg _)
    have ht' := delay_lower (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hθp) ht.1
      (div_nonneg hfn (by norm_num : (0:ℝ) ≤ 18)) hW hc.2.1 (ht.2.trans (add_le_add le_rfl hcF))
    exact hl s hs (hM m (le_max_left ..)) θ t (hθ.2.trans hπ) ht.1 ht'
  · intro t ht hv
    have hw := (le_div_iff₀ hW).mp ht.2
    have hcap : 42*s ≤ Fintype.card (PathLabel n) := h42.trans (by
      simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,N]; omega)
    have hlow := hf s hs hcap t ht.1 hw
    have hdist := (hasProjectiveCircuitApproximation_iff_infDist _ s _).mp hv
    change orbitCircuitDistance H s t ≤ 2*sin θ at hdist
    change 2*sin (t*W/4) ≤ orbitCircuitDistance H s t+4*t*(42*s)*sqrt (log (B*N/(42*s))) at hlow
    have hroot := sqrt_log_ratio hB hsp hN hsN hscale
    have hgap : 4*(42*(s:ℝ))*sqrt (log (B*N/(42*s))) ≤ 336*f := by
      dsimp only [f]; linarith only [mul_le_mul_of_nonneg_left hroot hsp.le]
    have hch : 2*sin (t*W/4) ≤ 2*sin θ+t*(336*f) := by
      linarith only [hlow,hdist,mul_le_mul_of_nonneg_left hgap ht.1]
    have hstop := chord_deadline hθp ht.1 (show 0 ≤ 336*f by positivity) hw hch
    have htime := delay_upper ha hN hc.1 (show 0 ≤ 4*(336*f) by positivity) ht.2 hstop
    refine htime.trans_eq ?_
    change 4*θ/W+π*(4*(336*f))/(a*N)^2=4*θ/W+C*(f/(N:ℝ)^2)
    apply congrArg (fun v : ℝ => 4*θ/W+v)
    dsimp only [C]; field_simp; ring

#print axioms gaussian_uniform_angles
end
end GaloisForLFunctions.HTGeometry.FirstAscent.AfterScalar

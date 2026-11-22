import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianFieldDelay
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.DelayBound
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.DelayScale
import GaloisForLFunctions.HTGeometry.ArcsineSeries

/-! # The fixed-error gate window at the first empty-circuit exit -/
open MeasureTheory Filter Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- Two-sided timing of the initial budget frontier at physical error 1/10.
Every time through t₀+cF is affordable and every time above t₀+CF in the
initial semicircle is unaffordable, with F=s√log(N/s)/N². -/
theorem gaussian_first_ascent_window :
    ∃ c C : ℝ, ∃ M : ℕ, 0<c ∧ 0<C ∧ 0<M ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
        let N := n+2
        let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),
          isSelfAdjoint_pathHamiltonian _⟩
        let W := circuitHamiltonianSpectralWidth H
        let t₀ := 4*arcsin (1/20)/W
        ∀ s : ℕ, 0<s → M*s ≤ N →
          let F := (s:ℝ)*sqrt (log ((N:ℝ)/s))/(N:ℝ)^2
          (∀ t ∈ Icc 0 (t₀+c*F), HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val t)) ∧
          ∀ t ∈ Icc 0 (π/W), HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val t) →
            t ≤ t₀+C*F := by
  obtain ⟨a,b,B,ha,hb,hB,hu⟩ := gaussian_short_circuit_deadline
  obtain ⟨m,hm,hl⟩ := gaussian_field_delay
  obtain ⟨k,hk⟩ := exists_nat_ge B
  let M := max m (max 42 k)
  let θ := arcsin (1/20)
  let u := 4*θ
  have hθ : 0<θ := arcsin_pos.mpr (by norm_num)
  have hu0 : 0<u := mul_pos (by norm_num) hθ
  have hθπ : θ ≤ π/4 := by
    have h := GaloisForLFunctions.arcsin_le_pi_half_mul (1/20) (by norm_num) (by norm_num)
    change arcsin (1/20) ≤ _
    linarith only [h,pi_pos]
  refine ⟨u/(18*b^2),π*1344/a^2,M,by positivity,by positivity,hm.trans_le (le_max_left ..),?_⟩
  filter_upwards [hu,hl] with ω hu hl
  filter_upwards [hu,hl] with n hn hfields
  intro N H W t₀ s hs hsize F
  have hN : 0<(N:ℝ) := by dsimp [N]; positivity
  have hs' : 0<(s:ℝ) := by exact_mod_cast hs
  have hW : 0<W := (mul_pos ha hN).trans_le hn.1
  have hab : W ≤ b*N := hn.2.1
  let f := (s:ℝ)*sqrt (log ((N:ℝ)/s))
  have hf : 0 ≤ f := mul_nonneg hs'.le (sqrt_nonneg _)
  have hM (i : ℕ) (hi : i ≤ M) : i*s ≤ N := (Nat.mul_le_mul_right s hi).trans hsize
  have h42 := hM 42 ((le_max_left 42 k).trans (le_max_right ..))
  have hsn : (s:ℝ) ≤ N := by exact_mod_cast (show s ≤ N by omega)
  have hscale : B ≤ (N:ℝ)/s := (le_div_iff₀ hs').mpr ((mul_le_mul_of_nonneg_right hk hs'.le).trans
    (by exact_mod_cast hM k ((le_max_right 42 k).trans (le_max_right ..))))
  constructor
  · intro t ht
    have htime : t ≤ u/W+u*(f/18)/(b*N)^2 := ht.2.trans_eq (by
      change u/W+u/(18*b^2)*(f/(N:ℝ)^2)=_
      field_simp)
    have h := delay_lower hu0.le ht.1 (div_nonneg hf (by norm_num)) hW hab htime
    have he := hfields s hs (hM m (le_max_left ..)) θ t hθπ ht.1 h
    have hsine : 2*sin θ=1/10 := by rw [show sin θ=1/20 from sin_arcsin (by norm_num) (by norm_num)]; norm_num
    rwa [hsine] at he
  · intro t ht he
    have hcap : 42*s ≤ Fintype.card (PathLabel n) := h42.trans (by
      simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,N]; omega)
    have hstop := hn.2.2 s hs hcap t ht he
    have hroot := sqrt_log_ratio hB hs' hN hsn hscale
    have hgap : 16*(42*(s:ℝ))*sqrt (log (B*N/(42*s))) ≤ 1344*f := by
      dsimp only [f]
      nlinarith only [mul_le_mul_of_nonneg_left hroot hs'.le]
    have hcost : t*(W-1344*f) ≤ u :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hgap W) ht.1).trans hstop
    have h := delay_upper ha hN hn.1 (by positivity : 0 ≤ 1344*f) ht.2 hcost
    apply h.trans_eq
    change u/W+π*(1344*f)/(a*N)^2=u/W+(π*1344/a^2)*(f/(N:ℝ)^2)
    field_simp

#print axioms gaussian_first_ascent_window
end
end GaloisForLFunctions.HTGeometry.FirstAscent

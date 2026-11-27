import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.CrossingDates.AfterVisit.Rebound
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.PhysicalHorizon

/-! # A common subsequent return after crossings below one bond sweep -/

open Set Filter Real MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open PrecisionReturns
noncomputable section

private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

private theorem crossing_delay_bounds {K d τ A γ l L Q : ℝ}
    (hK : 1≤K) (hd : 0<d) (ht : 0≤τ) (hA : 0<A)
    (hg : γ≤1) (hg' : A^9*γ<l) (hdg : d≤γ*K) (hQ : L^2≤Q)
    (hscale : Q*K^11≤d^20) (hlo : l*K≤τ^9*d^10) (hhi : τ^9*d^10≤L*K) :
    A/K<τ ∧ τ≤1 := by
  have hpos := zero_lt_one.trans_le hK
  constructor
  · apply (div_lt_iff₀ hpos).mpr
    by_contra! h
    have hdK : d≤K := hdg.trans ((mul_le_mul_of_nonneg_right hg hpos.le).trans_eq (one_mul K))
    have hp := pow_le_pow_left₀ (mul_nonneg ht hd.le) ((mul_le_mul_of_nonneg_left hdK ht).trans h) 9
    have hf : τ^9*d^10≤(A^9*γ)*K := calc
      _ = (τ*d)^9*d := by ring
      _ ≤ A^9*(γ*K) := mul_le_mul hp hdg hd.le (pow_nonneg hA.le _)
      _ = _ := (mul_assoc ..).symm
    exact (mul_lt_mul_of_pos_right hg' hpos).not_ge (hlo.trans hf)
  · have hh : L*K≤d^10 := by
      apply le_of_sq_le_sq _ (pow_nonneg hd.le 10)
      rw [mul_pow]
      exact ((mul_le_mul hQ (pow_le_pow_right₀ hK (by decide : 2≤11)) (sq_nonneg K)
        ((sq_nonneg L).trans hQ)).trans hscale).trans_eq (by ring)
    by_contra! h
    have hp : (1:ℝ)<τ^9 := one_lt_pow₀ h (by decide)
    exact (lt_mul_of_one_lt_left (pow_pos hd 10) hp).not_ge (hhi.trans hh)

/-- All admissible crossing heights and deficits select exactly the same next
low return. Moving the observation start anywhere from inverse size to the
superlinear horizon also selects that date, even for a different return budget. -/
theorem gaussian_deficit_common_return :
    ∃ κ>0, ∃ A>0, ∃ δ>0, ∃ γ>0, ∃ Q>0, ∃ l>0, ∃ L>0,
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
        let K : ℝ := (n+2:ℕ)
        let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
        let T := δ*K^(65/64:ℝ)
        ∀ (v : ℝ) (s r : ℕ), ((s+r:ℕ):ℝ)≤κ*K →
          HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H.val v) →
          let w := firstVisit H (v+1) r (1/10)
          v+T<w ∧ (∀ h∈Icc (A/K) T, firstVisit H (v+h) r (1/10)=w) ∧
          ∀ d : ℕ, 0<d → 2*s≤d → (d:ℝ)≤γ*K → Q*K^11≤(d:ℝ)^20 →
            ∀ ρ∈Icc (9/80:ℝ) (1/8), ∃ τ : ℝ,
              IsLeast {t : ℝ | 0≤t ∧ ρ≤orbitCircuitDistance H (n+1-d) (v+t)} τ ∧
              orbitCircuitDistance H (n+1-d) (v+τ)=ρ ∧
              l*K≤τ^9*(d:ℝ)^10 ∧ τ^9*(d:ℝ)^10≤L*K ∧ A/K<τ ∧ τ≤1 ∧
              firstVisit H (v+τ) r (1/10)=w := by
  obtain ⟨κ,hκ,A,hA,δ,hδ,hgap⟩ := BlockDilations.AdaptiveCuts.gaussian_superlinear_visit_spacing
  obtain ⟨g,hg,R,hR,l,hl,L,hL,hcross⟩ := gaussian_visit_crossing_scale
  let γ := min (min g 1) (l/(2*A^9))
  let Q := max R (L^2)
  have hγ : 0<γ := lt_min (lt_min hg zero_lt_one) (by positivity)
  have hg' : A^9*γ<l := by
    have he := (le_div_iff₀ (show 0<2*A^9 by positivity)).mp (min_le_right (min g 1) (l/(2*A^9)))
    change γ*(2*A^9)≤l at he
    linarith only [he,hl]
  refine ⟨κ,hκ,A,hA,δ,hδ,γ,hγ,Q,hR.trans_le (le_max_left ..),l,hl,L,hL,?_⟩
  filter_upwards [hgap,hcross] with ω hw hx
  filter_upwards [hw,hx,eventually_ge_atTop ⌈max A (1/δ)⌉₊] with n hn hx hsize
  intro K H T v s r hsr hv w
  have hK : 1≤K := by dsimp only [K]; exact_mod_cast (by omega : 1≤n+2)
  have hpos := zero_lt_one.trans_le hK
  have hmax : max A (1/δ)≤K := (Nat.le_ceil _).trans (Nat.cast_le.mpr (show ⌈max A (1/δ)⌉₊≤n+2 by omega))
  have hsmall : A/K≤1 := (div_le_one hpos).mpr ((le_max_left ..).trans hmax)
  have hlarge : 1≤T := calc
    1 ≤ δ*K := by have he := (div_le_iff₀ hδ).mp ((le_max_right ..).trans hmax); linarith only [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [rpow_one] using
      (rpow_le_rpow_of_exponent_le hK (by norm_num : (1:ℝ)≤65/64))) hδ.le
  have hit (h : ℝ) := firstVisit_isLeast H (v+h) r (by norm_num : (0:ℝ)<1/10)
  have past (h : ℝ) (hh : A/K≤h) : v+T<firstVisit H (v+h) r (1/10) := by
    let u := firstVisit H (v+h) r (1/10)
    have hb : A/K≤u-v := by linarith only [hh,(hit h).1.1]
    have he := hn v u s r (1/10) (1/10) (by norm_num) hsr hv (hit h).1.2
    rw [abs_of_nonneg ((div_pos hA hpos).le.trans hb)] at he
    change u-v<A/K ∨ T<u-v at he
    linarith only [he.resolve_left hb.not_gt]
  have hw' := past 1 hsmall
  have common (h : ℝ) (hh : h∈Icc (A/K) T) : firstVisit H (v+h) r (1/10)=w := by
    apply le_antisymm ((hit h).2 ⟨(add_le_add (le_refl v) hh.2).trans hw'.le,(hit 1).1.2⟩)
    exact (hit 1).2 ⟨(add_le_add (le_refl v) hlarge).trans (past h hh.1).le,(hit h).1.2⟩
  refine ⟨hw',common,?_⟩
  intro d hd hs hdg hscale ρ hρ
  obtain ⟨τ,hm,he,hlo,hhi⟩ := hx d s hd hs (hdg.trans (mul_le_mul_of_nonneg_right
    ((min_le_left ..).trans (min_le_left ..)) hpos.le))
    ((mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg hpos.le _)).trans hscale) v hv ρ hρ
  obtain ⟨ht,hu⟩ := crossing_delay_bounds hK (Nat.cast_pos.mpr hd) hm.1.1 hA
    ((min_le_left ..).trans (min_le_right ..)) hg' hdg (le_max_right ..) hscale hlo hhi
  exact ⟨τ,hm,he,hlo,hhi,ht,hu,common _ ⟨ht.le,hu.trans hlarge⟩⟩

#print axioms gaussian_deficit_common_return
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit

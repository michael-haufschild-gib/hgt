import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.PrescribedExcess
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.FirstExcess

/-! # A quantitative upper date for departure beyond one bond sweep -/
open MeasureTheory Filter Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
noncomputable section

private abbrev chain (ω : PathPauliDisorder) (n : ℕ) : selfAdjoint (Register (n+2)) :=
  ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩

/-- A positive density of excess gates still fails by the prescribed
date t. The bound applies after every physical-error visit on that prefix. -/
theorem gaussian_first_excess_by {t : ℝ} (ht : 0<t) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ (v : ℝ) (s q : ℕ),
      HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution (chain ω n).val v) →
      ((2*s+q:ℕ):ℝ) ≤ prescribedExcess t*(n+1:ℕ) →
      let u := firstExcessAfter ω n (s+q) v (1/8)
      0≤u ∧ u≤t ∧ orbitCircuitDistance (chain ω n) (n+1+(s+q)) (v+u)=1/8 ∧
        ∀ x∈Ico 0 u, orbitCircuitDistance (chain ω n) (n+1+(s+q)) (v+x)<1/8 := by
  filter_upwards [gaussian_prescribed_excess ht] with ω hw
  filter_upwards [hw] with n hn
  intro v s q hv hq
  apply firstExcessAfter_le_of_increment ω n s q ht.le (by norm_num : (1/10:ℝ)<1/8) hv
  rintro ⟨z,hz,C,hC,he⟩
  have hh := hn (s+(n+1+(s+q))) ⟨z,hz,C,hC,he.trans (by norm_num)⟩
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at hh hq
  linarith only [hh,hq]

/-- For each excess density h at most c exp(-A), the first crossing occurs by
sqrt(A/log(c/h)), eventually on almost every frozen prefix. The prefix
limit is taken at fixed h. -/
theorem gaussian_inverse_log_departure :
    ∃ c>0, ∃ A>0, ∀ h : ℝ, 0<h → h≤c*exp (-A) →
      let t := sqrt (A/log (c/h))
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ (v : ℝ) (s q : ℕ),
        HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution (chain ω n).val v) →
        ((2*s+q:ℕ):ℝ) ≤ h*(n+1:ℕ) →
        let u := firstExcessAfter ω n (s+q) v (1/8)
        0≤u ∧ u≤t ∧ orbitCircuitDistance (chain ω n) (n+1+(s+q)) (v+u)=1/8 ∧
          ∀ x∈Ico 0 u, orbitCircuitDistance (chain ω n) (n+1+(s+q)) (v+x)<1/8 := by
  obtain ⟨c,hc,A,hA,hsmall,_⟩ := prescribed_excess_scales
  refine ⟨c,hc,A,hA,?_⟩
  intro h hh hle t
  have hlog : A≤log (c/h) := by
    apply (le_log_iff_exp_le (div_pos hc hh)).mpr
    apply (le_div_iff₀ hh).mpr
    rw [exp_neg] at hle
    exact (mul_le_mul_of_nonneg_left hle (exp_pos A).le).trans_eq
      (by field_simp)
  have hp := hA.trans_le hlog
  have ht : 0<t := sqrt_pos.mpr (div_pos hA hp)
  have ht₁ : t≤1 := (sqrt_le_one.mpr ((div_le_one hp).mpr hlog))
  have hs : t^2=A/log (c/h) := sq_sqrt (div_pos hA hp).le
  have he : c*exp (-A/t^2)=h := by
    rw [hs,show -A/(A/log (c/h))= -log (c/h) by field_simp,exp_neg,exp_log (div_pos hc hh)]
    field_simp
  have hfit := hsmall t ht ht₁
  rw [he] at hfit
  filter_upwards [gaussian_first_excess_by ht] with ω hw
  filter_upwards [hw] with n hn
  intro v s q hv hq
  exact hn v s q hv (hq.trans (mul_le_mul_of_nonneg_right hfit (by positivity)))

#print axioms gaussian_first_excess_by
#print axioms gaussian_inverse_log_departure

/-- After the actual first low visit, a positive excess can be included
in the gate budget while preserving the inverse-logarithmic deadline. -/
theorem gaussian_inverse_log_first_rebound :
    ∃ c>0, ∃ A>0, ∀ h : ℝ, 0<h → h≤c*exp (-A) →
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ s q : ℕ,
        ((2*s+q:ℕ):ℝ) ≤ h*(n+1:ℕ) →
        let v := firstLowAfterCrossing ω n s
        let u := firstExcessAfter ω n (s+q) v (1/8)
        0 ≤ u ∧ u ≤ sqrt (A/log (c/h)) ∧ orbitCircuitDistance (chain ω n) (n+1+(s+q)) (v+u)=1/8 ∧
          ∀ x∈Ico 0 u, orbitCircuitDistance (chain ω n) (n+1+(s+q)) (v+x)<1/8 := by
  obtain ⟨c,hc,A,hA,hh⟩ := gaussian_inverse_log_departure
  refine ⟨c,hc,A,hA,?_⟩
  intro h hp hle
  filter_upwards [hh h hp hle] with ω hw
  filter_upwards [hw] with n hn
  intro s q hq v u
  exact hn v s q (PrecisionReturns.firstVisit_isLeast (chain ω n) _ s
    (by norm_num : (0:ℝ)<1/10)).1.2 hq

#print axioms gaussian_inverse_log_first_rebound
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks

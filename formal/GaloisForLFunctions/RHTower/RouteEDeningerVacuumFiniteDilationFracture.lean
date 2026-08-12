import GaloisForLFunctions.RHTower.DeningerExpSchwartz
import GaloisForLFunctions.HTGeometry.KrylovReplicaMomentAmplificationLaw
import Mathlib.Analysis.Analytic.Order

/-!
# Route E Deninger vacuum finite-dilation fracture

The strict Deninger--Meyer source contains no nonzero analytic log-pull `t ↦ G(exp t)`.
Source decay forces the analytic germ `G` to have infinite order at the origin; an entire `G` is
therefore zero.  Applying this classification to a finite exponential amplitude and then to its
Vandermonde moments proves that no nonzero finite mask of distinct vacuum dilates enters the
strict source.
-/

namespace RHTower

open Filter Topology SchwartzMap

noncomputable section

/-- **Analytic log-pull fracture.** If a Schwartz representative of `G(exp t)` belongs to the
strict Deninger source, then the analytic germ `G` has infinite vanishing order at zero. -/
theorem deningerExpSchwartz_logPull_analyticOrderAt_eq_top
    (G : ℂ → ℂ) (hG : AnalyticAt ℂ G 0)
    (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerExpSchwartz)
    (hpull : ∀ t : ℝ, f t = G (Real.exp t)) :
    analyticOrderAt G 0 = ⊤ := by
  by_contra hnot
  obtain ⟨g, hg, hg0, hfactor⟩ := hG.analyticOrderAt_ne_top.mp hnot
  let n := analyticOrderNatAt G 0
  obtain ⟨C, hC⟩ := hf ((n : ℝ) + 1) 0
  have hCnonneg : 0 ≤ C := by
    have h := hC 0
    simp only [abs_zero, mul_zero, Real.exp_zero, one_mul] at h
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero] at h
    exact (norm_nonneg (f 0)).trans h
  have hexp0 : Tendsto (fun t : ℝ => (Real.exp t : ℂ)) atBot (𝓝 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp Real.tendsto_exp_atBot
  have hfactorBot := hfactor.comp_tendsto hexp0
  have hboundg : ∀ᶠ t : ℝ in atBot, ‖g (Real.exp t)‖ ≤ C * Real.exp t := by
    filter_upwards [hfactorBot, (eventually_atBot.2 ⟨0, fun t ht => ht⟩)] with t hfac ht
    have hsource := hC t
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero] at hsource
    rw [hpull t] at hsource
    simp only [Function.comp_apply] at hfac
    rw [hfac, sub_zero, norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos t)] at hsource
    have hexpEq : Real.exp (((n : ℝ) + 1) * |t|) *
          (Real.exp t ^ n * ‖g (Real.exp t)‖) =
        Real.exp (-t) * ‖g (Real.exp t)‖ := by
      rw [abs_of_nonpos ht]
      rw [← Real.exp_nat_mul]
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf
    rw [hexpEq] at hsource
    have hpos := Real.exp_pos (-t)
    have hinv : (Real.exp (-t))⁻¹ = Real.exp t := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [show C * Real.exp t = C / Real.exp (-t) by rw [div_eq_mul_inv, hinv]]
    apply (le_div_iff₀ hpos).2
    simpa [mul_comm] using hsource
  have hbound0 : Tendsto (fun t : ℝ => ‖g (Real.exp t)‖) atBot (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · exact hboundg
    · simpa using (tendsto_const_nhds.mul Real.tendsto_exp_atBot)
  have hlim := hg.continuousAt.tendsto.comp hexp0
  have hnormlim : Tendsto (fun t : ℝ => ‖g (Real.exp t)‖) atBot (𝓝 ‖g 0‖) := hlim.norm
  have : ‖g 0‖ = 0 := tendsto_nhds_unique hnormlim hbound0
  exact hg0 (norm_eq_zero.mp this)

/-- **Entire log-pull classification.** The only entire function whose logarithmic pull has a
strict Deninger source representative is the zero function. -/
theorem deningerExpSchwartz_logPull_entire_eq_zero
    (G : ℂ → ℂ) (hG : ∀ z, AnalyticAt ℂ G z)
    (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerExpSchwartz)
    (hpull : ∀ t : ℝ, f t = G (Real.exp t)) :
    G = 0 := by
  apply (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 hG).mp
  exact deningerExpSchwartz_logPull_analyticOrderAt_eq_top G (hG 0) f hf hpull

open GaloisForLFunctions.HTGeometry

/-- A finite linear mask of vacuum dilations in logarithmic coordinates. -/
def routeEDeningerFiniteVacuumDilation {r : ℕ}
    (rate : Fin r → ℝ) (coefficient : Fin r → ℂ) (t : ℝ) : ℂ :=
  finiteComplexExponentialAmplitude coefficient (fun j => -(rate j : ℂ)) (Real.exp t)

/-- Deninger's logarithmic vacuum profile `V(t)=exp(-exp t)`. -/
def routeEDeningerVacuumLogProfile (t : ℝ) : ℂ := Complex.exp (-Real.exp t)

/-- Positive dilation rates identify the finite amplitude with literal translated vacuum
profiles `V(t + log a_j)`. -/
theorem routeEDeningerFiniteVacuumDilation_eq_shifted_vacuum
    {r : ℕ} (rate : Fin r → ℝ) (coefficient : Fin r → ℂ)
    (hrate : ∀ j, 0 < rate j) (t : ℝ) :
    routeEDeningerFiniteVacuumDilation rate coefficient t =
      ∑ j, coefficient j * routeEDeningerVacuumLogProfile (t + Real.log (rate j)) := by
  classical
  unfold routeEDeningerFiniteVacuumDilation routeEDeningerVacuumLogProfile
  unfold finiteComplexExponentialAmplitude
  apply Finset.sum_congr rfl
  intro j _hj
  congr 2
  rw [Real.exp_add, Real.exp_log (hrate j)]
  push_cast
  ring

/-- **Finite-dilation Vandermonde fracture.** Distinct dilation rates and strict Deninger source
membership force every coefficient of the finite vacuum mask to vanish. -/
theorem routeEDeningerFiniteVacuumDilation_coeff_eq_zero
    {r : ℕ} (rate : Fin r → ℝ) (coefficient : Fin r → ℂ)
    (hrate : Function.Injective rate)
    (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerExpSchwartz)
    (hpull : ∀ t : ℝ, f t = routeEDeningerFiniteVacuumDilation rate coefficient t) :
    coefficient = 0 := by
  let G := finiteComplexExponentialAmplitude coefficient (fun j => -(rate j : ℂ))
  have hG : AnalyticAt ℂ G 0 :=
    finiteComplexExponentialAmplitude_analyticAt coefficient (fun j => -(rate j : ℂ)) 0
  have htop : analyticOrderAt G 0 = ⊤ :=
    deningerExpSchwartz_logPull_analyticOrderAt_eq_top G hG f hf hpull
  have hmom : ∀ k : Fin r,
      ∑ j : Fin r, coefficient j * (-(rate j : ℂ)) ^ (k : ℕ) = 0 := by
    intro k
    have horder : ((k : ℕ) + 1 : ℕ) ≤ analyticOrderAt G 0 := by
      rw [htop]
      simp
    have hderiv := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hG).mp horder
      (k : ℕ) (Nat.lt_succ_self _)
    rw [iteratedDeriv_finiteComplexExponentialAmplitude_zero] at hderiv
    exact hderiv
  have hrateC : Function.Injective (fun j : Fin r => -(rate j : ℂ)) := by
    intro i j hij
    apply hrate
    exact_mod_cast neg_injective hij
  exact Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hrateC hmom

/-- Exact source-membership classification for a finite distinct-rate vacuum mask. -/
theorem exists_deningerExpSchwartz_finiteVacuumDilation_iff
    {r : ℕ} (rate : Fin r → ℝ) (coefficient : Fin r → ℂ)
    (hrate : Function.Injective rate) :
    (∃ f : DeningerExpSchwartz,
      ∀ t : ℝ, (((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t =
        routeEDeningerFiniteVacuumDilation rate coefficient t) ↔ coefficient = 0 := by
  constructor
  · rintro ⟨f, hrepr⟩
    exact routeEDeningerFiniteVacuumDilation_coeff_eq_zero rate coefficient hrate
      (f : 𝓢(ℝ, ℂ)) f.2 hrepr
  · intro hc
    subst coefficient
    refine ⟨0, fun t => ?_⟩
    simp [routeEDeningerFiniteVacuumDilation, finiteComplexExponentialAmplitude]

/-- **Literal shifted-vacuum classification.** For positive distinct `a_j`, a finite sum
`sum_j c_j V(t+log a_j)` lies in the strict Deninger source exactly when every `c_j` is zero. -/
theorem exists_deningerExpSchwartz_shiftedVacuum_iff
    {r : ℕ} (rate : Fin r → ℝ) (coefficient : Fin r → ℂ)
    (hratePos : ∀ j, 0 < rate j) (hrateInj : Function.Injective rate) :
    (∃ f : DeningerExpSchwartz,
      ∀ t : ℝ, (((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t =
        ∑ j, coefficient j *
          routeEDeningerVacuumLogProfile (t + Real.log (rate j))) ↔ coefficient = 0 := by
  rw [← exists_deningerExpSchwartz_finiteVacuumDilation_iff rate coefficient hrateInj]
  constructor <;> rintro ⟨f, hrepr⟩ <;> refine ⟨f, fun t => ?_⟩
  · rw [routeEDeningerFiniteVacuumDilation_eq_shifted_vacuum
      rate coefficient hratePos t]
    exact hrepr t
  · rw [← routeEDeningerFiniteVacuumDilation_eq_shifted_vacuum
      rate coefficient hratePos t]
    exact hrepr t

end

end RHTower

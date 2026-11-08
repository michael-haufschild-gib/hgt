import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarCenterCutoffsAreContinuous
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ReciprocalChebyshevProfilesAdmitSampledApproximation
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.LeftCutoffsPreserveLipschitzApproximation

/-!
# The sampled polar profile admits compact Lipschitz approximation

Terminal cutoffs control the logarithmic singularity in square mean. Finite
reciprocal Chebyshev jumps admit ramp approximations. Polynomial density then
gives a compact Lipschitz test with an exact left support cutoff.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- The polar profile in logarithmic coordinates, with the square-root sampling density. -/
def polarLogSampleProfile (q u : ℝ) : ℝ :=
  q * Real.sqrt (Real.exp u) *
    (polarCenterProfile (fun _ => 1) (Real.exp u) -
      Chebyshev.psi (1 / Real.exp u) - Real.log (2 * Real.pi))

/-- The regularized logarithmic profile is continuous on each negative compact interval. -/
lemma continuousOn_regularized_polarLogSampleProfile {a η : ℝ} (hη : 0 < η) (q : ℝ) :
    ContinuousOn (fun u => q * Real.sqrt (Real.exp u) *
      (polarCenterProfile (polarCenterCutoff (Real.exp a) η) (Real.exp u) -
        chebyshevReciprocalRamp (Real.exp a) η (Real.exp u) - Real.log (2 * Real.pi))) (Set.Icc a 0) := by
  have he : Set.MapsTo Real.exp (Set.Icc a 0) (Set.Icc (0 : ℝ) 1) := fun u hu =>
    ⟨(Real.exp_pos u).le, by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hu.2⟩
  exact (continuous_const.mul (Real.continuous_sqrt.comp Real.continuous_exp)).continuousOn.mul
    (((continuousOn_polarCenterProfile_cutoff (Real.exp_pos a) hη).comp
      Real.continuous_exp.continuousOn he).sub
        ((continuous_chebyshevReciprocalRamp (Real.exp a) hη).comp Real.continuous_exp).continuousOn
      |>.sub continuousOn_const)

/-- A quantitative sampled approximation controls both the terminal logarithm and all prime jumps. -/
theorem exists_polarLogSampleProfile_approximation_bound {a η ρ : ℝ}
    (hη : 0 < η) (hηa : η ≤ Real.exp a) (hη4 : η ≤ 1 / 4) (hρ : 0 < ρ) (q : ℝ) :
    ∃ f : ℝ → ℝ, ∃ K : NNReal, HasCompactSupport f ∧ LipschitzWith K f ∧
      (∀ u, u ≤ a → f u = 0) ∧ ∀ N : ℕ, 8 ≤ N →
      (∑ n ∈ Icc 1 N,
        (leftProfileCutoff a (Real.log ((n : ℝ) / N)) *
          polarLogSampleProfile q (Real.log ((n : ℝ) / N)) -
            f (Real.log ((n : ℝ) / N))) ^ 2) / N ≤
        3 * q ^ 2 * (18 * (η + 1 / N) + 64 * Real.sqrt (η + 1 / N) +
          (∑ k ∈ Icc 1 ⌊1 / Real.exp a⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ) ^ 2) *
            ((Icc 1 ⌊1 / Real.exp a⌋₊).card * (2 * η + 4 / N))) + 3 * ρ ^ 2 := by
  let δ := Real.exp a
  let g : ℝ → ℝ := fun u => q * Real.sqrt (Real.exp u) *
    (polarCenterProfile (polarCenterCutoff δ η) (Real.exp u) -
      chebyshevReciprocalRamp δ η (Real.exp u) - Real.log (2 * Real.pi))
  obtain ⟨f, K, hfc, hLip, hfzero, hfapprox⟩ :=
    exists_compact_leftCutoff_lipschitz_approximation
      (continuousOn_regularized_polarLogSampleProfile hη q) hρ
  refine ⟨f, K, hfc, hLip, hfzero, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  let S := Ioc ⌊δ * (N : ℝ)⌋₊ N
  let E := fun n : ℕ => leftProfileCutoff a (Real.log ((n : ℝ) / N)) *
    polarLogSampleProfile q (Real.log ((n : ℝ) / N)) - f (Real.log ((n : ℝ) / N))
  let P := fun n : ℕ => polarCenterProfile (fun _ => 1) ((n : ℝ) / N) -
    polarCenterProfile (polarCenterCutoff δ η) ((n : ℝ) / N)
  let J := fun n : ℕ => Chebyshev.psi (1 / ((n : ℝ) / N)) -
    chebyshevReciprocalRamp δ η ((n : ℝ) / N)
  have hsub : S ⊆ Icc 1 N := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hn
    exact mem_Icc.mpr ⟨by omega, hhi⟩
  have hzero : ∀ n ∈ Icc 1 N, n ∉ S → E n = 0 := by
    intro n hn hnS
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnlo : n ≤ ⌊δ * (N : ℝ)⌋₊ := by
      by_contra hlt
      exact hnS (mem_Ioc.mpr ⟨by omega, (mem_Icc.mp hn).2⟩)
    have hx : (n : ℝ) / N ≤ δ := (div_le_iff₀ hN0).mpr
      ((by exact_mod_cast hnlo : (n : ℝ) ≤ ⌊δ * (N : ℝ)⌋₊).trans
        (Nat.floor_le (by positivity)))
    have hu : Real.log ((n : ℝ) / N) ≤ a :=
      (Real.log_le_iff_le_exp (div_pos hn0 hN0)).mpr hx
    dsimp only [E]
    rw [leftProfileCutoff_eq_zero hu, hfzero _ hu, zero_mul, sub_self]
  have heq : (∑ n ∈ Icc 1 N, E n ^ 2) = ∑ n ∈ S, E n ^ 2 := by
    symm
    apply sum_subset hsub
    intro n hn hnS
    rw [hzero n hn hnS, zero_pow (by decide : 2 ≠ 0)]
  have hpoint : ∀ n ∈ S, E n ^ 2 ≤ 3 * q ^ 2 * (P n ^ 2 + J n ^ 2) + 3 * ρ ^ 2 := by
    intro n hn
    have hnI := hsub hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hnI).1
    have hx0 := div_pos hn0 hN0
    have hx1 : (n : ℝ) / N ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast (mem_Icc.mp hnI).2)
    have hδx : δ ≤ (n : ℝ) / N := (le_div_iff₀ hN0).mpr
      ((Nat.floor_lt (by positivity : 0 ≤ δ * (N : ℝ))).mp (mem_Ioc.mp hn).1).le
    let u := Real.log ((n : ℝ) / N)
    have hu : u ∈ Set.Icc a 0 := ⟨(Real.le_log_iff_exp_le hx0).mpr hδx,
      Real.log_nonpos hx0.le hx1⟩
    have hex : Real.exp u = (n : ℝ) / N := Real.exp_log hx0
    let t := leftProfileCutoff a u * q * Real.sqrt ((n : ℝ) / N)
    have ht2 : t ^ 2 ≤ q ^ 2 := by
      obtain ⟨hcut0, hcut1⟩ := leftProfileCutoff_bounds a u
      have hcut2 : leftProfileCutoff a u ^ 2 ≤ 1 := by
        nlinarith only [hcut0, hcut1, mul_nonneg hcut0 (sub_nonneg.mpr hcut1)]
      have hcutx : leftProfileCutoff a u ^ 2 * ((n : ℝ) / N) ≤ 1 :=
        (mul_le_mul hcut2 hx1 hx0.le zero_le_one).trans_eq (one_mul _)
      have hh := mul_le_mul_of_nonneg_right hcutx (sq_nonneg q)
      dsimp only [t]
      rw [mul_pow, mul_pow, Real.sq_sqrt hx0.le]
      nlinarith only [hh]
    have hd : (leftProfileCutoff a u * g u - f u) ^ 2 ≤ ρ ^ 2 := by
      have hh := pow_le_pow_left₀ (abs_nonneg _) (hfapprox u hu).le 2
      have he : (leftProfileCutoff a u * g u - f u) ^ 2 =
          (f u - leftProfileCutoff a u * g u) ^ 2 := by ring
      rw [he]
      simpa only [sq_abs] using hh
    have he : E n = t * P n - t * J n + (leftProfileCutoff a u * g u - f u) := by
      dsimp only [E, polarLogSampleProfile, t, P, J, g, u]
      rw [Real.exp_log hx0]
      ring
    have hthree (x y z : ℝ) : (x - y + z) ^ 2 ≤ 3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2 := by
      nlinarith only [sq_nonneg (x + y), sq_nonneg (x - z), sq_nonneg (y + z)]
    have hp := mul_le_mul_of_nonneg_right ht2 (sq_nonneg (P n))
    have hj := mul_le_mul_of_nonneg_right ht2 (sq_nonneg (J n))
    have htotal := hthree (t * P n) (t * J n) (leftProfileCutoff a u * g u - f u)
    rw [he]
    rw [mul_pow, mul_pow] at htotal
    nlinarith only [htotal, hp, hj, hd]
  have hs := sum_le_sum hpoint
  simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at hs
  have hcard : (S.card : ℝ) ≤ N := by
    have hc := card_le_card hsub
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using (show (S.card : ℝ) ≤ (Icc 1 N).card by exact_mod_cast hc)
  have hc := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ 3 * ρ ^ 2)
  have hdiv : (∑ n ∈ S, E n ^ 2) / N ≤
      3 * q ^ 2 * ((∑ n ∈ S, P n ^ 2) / N + (∑ n ∈ S, J n ^ 2) / N) + 3 * ρ ^ 2 := by
    have hh : (∑ n ∈ S, E n ^ 2) ≤
        3 * q ^ 2 * ((∑ n ∈ S, P n ^ 2) + ∑ n ∈ S, J n ^ 2) + N * (3 * ρ ^ 2) := by
      nlinarith only [hs, hc]
    exact (div_le_div_of_nonneg_right hh hN0.le).trans_eq (by field_simp [hN0.ne'])
  change (∑ n ∈ Icc 1 N, E n ^ 2) / N ≤ _
  rw [heq]
  exact hdiv.trans (add_le_add (mul_le_mul_of_nonneg_left
    (add_le_add (normalized_sum_polarCenterProfile_sub_cutoff_sq_le (Real.exp_pos a) hη hη4 hN)
      (normalized_sum_chebyshevPsi_sub_ramp_sq_le (Real.exp_pos a) hη hηa hN1))
    (by positivity : 0 ≤ 3 * q ^ 2)) le_rfl)

/-- The left-truncated polar profile is approximable to arbitrary sampled square accuracy by one
compact Lipschitz test, uniformly for all sufficiently large horizons. -/
theorem exists_polarLogSampleProfile_lipschitz_approximation (a q : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, ∃ K : NNReal, HasCompactSupport f ∧ LipschitzWith K f ∧
      (∀ u, u ≤ a → f u = 0) ∧ ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Icc 1 N,
        (leftProfileCutoff a (Real.log ((n : ℝ) / N)) *
          polarLogSampleProfile q (Real.log ((n : ℝ) / N)) -
            f (Real.log ((n : ℝ) / N))) ^ 2) / N ≤ ε := by
  let J : ℝ := (∑ k ∈ Icc 1 ⌊1 / Real.exp a⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ) ^ 2) *
    (Icc 1 ⌊1 / Real.exp a⌋₊).card
  let t : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hs : Tendsto (fun k => Real.sqrt (t k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp ht
  let e : ℝ → ℝ := fun η => 3 * q ^ 2 * (18 * η + 64 * Real.sqrt η + J * (2 * η)) + 3 * η ^ 2
  have he : Tendsto (fun k => e (t k)) atTop (𝓝 0) := by
    have hh := ((((ht.const_mul 18).add (hs.const_mul 64)).add
      ((ht.const_mul 2).const_mul J)).const_mul (3 * q ^ 2)).add ((ht.pow 2).const_mul 3)
    simpa only [e, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using hh
  obtain ⟨k, hka, hk4, hke⟩ := ((ht.eventually (gt_mem_nhds (Real.exp_pos a))).and
    ((ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).and
      (he.eventually (gt_mem_nhds hε)))).exists
  have htk : 0 < t k := by dsimp only [t]; positivity
  obtain ⟨f, K, hfc, hLip, hfzero, hbound⟩ :=
    exists_polarLogSampleProfile_approximation_bound htk hka.le hk4.le htk q
  refine ⟨f, K, hfc, hLip, hfzero, ?_⟩
  have hi : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hn : Tendsto (fun N : ℕ => t k + 1 / (N : ℝ)) atTop (𝓝 (t k)) := by
    simpa only [add_zero] using hi.const_add (t k)
  have hr : Tendsto (fun N : ℕ => Real.sqrt (t k + 1 / (N : ℝ))) atTop (𝓝 (Real.sqrt (t k))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hn
  have hboundLim : Tendsto (fun N : ℕ =>
      3 * q ^ 2 * (18 * (t k + 1 / N) + 64 * Real.sqrt (t k + 1 / N) +
        J * (2 * t k + 4 / N)) + 3 * t k ^ 2) atTop (𝓝 (e (t k))) := by
    have hi4 : Tendsto (fun N : ℕ => 4 / (N : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero, mul_one_div] using hi.const_mul 4
    have hh := ((((hn.const_mul 18).add (hr.const_mul 64)).add
      ((hi4.const_add (2 * t k)).const_mul J)).const_mul (3 * q ^ 2)).add_const (3 * t k ^ 2)
    simpa only [e, add_zero] using hh
  filter_upwards [eventually_ge_atTop 8, hboundLim.eventually (gt_mem_nhds hke)] with N hN hsmall
  have hh := hbound N hN
  have heq : (∑ k ∈ Icc 1 ⌊1 / Real.exp a⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ) ^ 2) *
      ((Icc 1 ⌊1 / Real.exp a⌋₊).card * (2 * t k + 4 / N)) = J * (2 * t k + 4 / N) := by
    dsimp only [J]
    ring
  rw [heq] at hh
  exact hh.trans hsmall.le

#print axioms exists_polarLogSampleProfile_lipschitz_approximation

#print axioms exists_polarLogSampleProfile_approximation_bound
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

import GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalResidue
import GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalDensityLaplace

/-!
# The necessary gamma coefficient on the full signed null cone

Every pole weight strictly larger than the nonnegative gamma coefficient gives
negative smooth null mixtures, even after arbitrary mass slack. This is a
necessary boundary; it does not assert positivity at equal weights.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- The elementary zeta residue in the same parameter as the modified datum. -/
theorem critical_zeta_residue :
    Tendsto (fun s : ℝ => s * ∑' m : ℕ, (m:ℝ)^(-(1+s))) (𝓝[>] 0) (𝓝 1) := by
  have hx : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hshift : Tendsto (fun s : ℝ => 1+s) (𝓝[>] 0) (𝓝[>] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa only [add_zero] using (tendsto_const_nhds.add hx :
        Tendsto (fun s : ℝ => 1+s) (𝓝[>] 0) (𝓝 (1+0)))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change 1 < 1+s
      linarith [show 0 < s from hs]
  have hz := tendsto_sub_mul_tsum_nat_rpow.comp hshift
  simpa only [Function.comp_def, add_sub_cancel_left, Real.rpow_neg (Nat.cast_nonneg _),
    one_div] using hz

/-- Any actual smooth-test completion has pole weight at most its gamma coefficient. -/
theorem critical_pole_weight_le_gamma {a b C : ℝ} (ha : 0 ≤ a) {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1) : b ≤ a := by
  have hx : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlim : Tendsto
      (fun s : ℝ => s^2 * (criticalDirichletReal lam (1+s) * ∑' m : ℕ, (m:ℝ)^(-(1+s))))
      (𝓝[>] 0) (𝓝 b) := by
    have hp := (criticalDirichletReal_residue ha h).mul critical_zeta_residue
    simp only [mul_one] at hp
    apply hp.congr
    intro s
    ring
  by_contra hn
  have hab : a < b := lt_of_not_ge hn
  let ε := (b-a)/4
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨M, _, hM⟩ := critical_dirichlet_product_ceiling ha h hε
  have hu : Tendsto (fun s : ℝ => a+2*ε+M*s^2) (𝓝[>] 0) (𝓝 (a+2*ε)) := by
    simpa using tendsto_const_nhds.add ((hx.pow 2).const_mul M)
  have hle : b ≤ a+2*ε := le_of_tendsto_of_tendsto hlim hu (by
    filter_upwards [self_mem_nhdsWithin] with s hs using hM s hs)
  dsimp [ε] at hle
  linarith

/-- Unconditional negative-null-mixture theorem: no analytic producer premise remains. -/
theorem exists_negative_smooth_null_mixture {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (C : ℝ) :
    ∃ c : SmoothTest →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      linearCombination ℝ (fun f : SmoothTest => logVector f.1) c = 0 ∧
      linearCombination ℝ (fun f : SmoothTest => criticalDatum a b C f.1.1) c < 0 := by
  by_contra hn
  have hpos : SmoothNullPositive a b C := by
    intro c hc hz
    exact le_of_not_gt fun hneg => hn ⟨c, hc, hz, hneg⟩
  obtain ⟨lam, _, _, hlam⟩ := exists_critical_completion hpos
  exact (not_lt_of_ge (critical_pole_weight_le_gamma ha hlam)) hab

/-- In particular, reducing the actual gamma coefficient cannot be repaired by any mass constant. -/
theorem exists_negative_half_gamma_null_mixture (C : ℝ) :
    ∃ c : SmoothTest →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      linearCombination ℝ (fun f : SmoothTest => logVector f.1) c = 0 ∧
      linearCombination ℝ (fun f : SmoothTest => criticalDatum (1/2) 1 C f.1.1) c < 0 :=
  exists_negative_smooth_null_mixture (by norm_num) (by norm_num) C

/-- The mass of a smooth finite mixture. -/
def smoothMixtureMass : (SmoothTest →₀ ℝ) →ₗ[ℝ] ℝ :=
  linearCombination ℝ (fun f : SmoothTest => testMass f.1.1)

theorem testMass_nonneg (f : ℝ → ℂ) : 0 ≤ testMass f :=
  integral_nonneg fun _ => sq_nonneg _

theorem testMass_eq_zero_iff (f : SmoothTest) : testMass f.1.1 = 0 ↔ f.1.1 = 0 := by
  constructor
  · intro hm
    funext x
    by_contra hx
    have hcont : Continuous (fun u : ℝ => ‖f.1.1 u‖ ^ 2) :=
      f.2.continuous.norm.pow 2
    have hcomp : HasCompactSupport (fun u : ℝ => ‖f.1.1 u‖ ^ 2) :=
      f.1.2.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
    have hnonzero : ‖f.1.1 x‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
    have hp : 0 < testMass f.1.1 :=
      Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
        hcont hcomp (fun _ => sq_nonneg _) hnonzero
    linarith
  · intro hf
    simp [testMass, hf]

theorem criticalDatum_zero (a b C : ℝ) : criticalDatum a b C (0 : ℝ → ℂ) = 0 := by
  simp [criticalDatum, testGamma, testPole, testMass, Zeta23.EF.weilTest,
    Zeta23.paperFT]

theorem smoothMixtureMass_nonneg {c : SmoothTest →₀ ℝ} (hc : ∀ f, 0 ≤ c f) :
    0 ≤ smoothMixtureMass c := by
  change 0 ≤ ∑ f ∈ c.support, c f * testMass f.1.1
  exact Finset.sum_nonneg fun f _ => mul_nonneg (hc f) (testMass_nonneg _)

/-- A negative nonnegative mixture cannot have zero mass. -/
theorem smoothMixtureMass_pos_of_negative {a b C : ℝ} {c : SmoothTest →₀ ℝ}
    (hc : ∀ f, 0 ≤ c f)
    (hneg : linearCombination ℝ (fun f : SmoothTest => criticalDatum a b C f.1.1) c < 0) :
    0 < smoothMixtureMass c := by
  by_contra hn
  have hm : smoothMixtureMass c = 0 :=
    le_antisymm (le_of_not_gt hn) (smoothMixtureMass_nonneg hc)
  have hterms : ∀ f ∈ c.support, c f * testMass f.1.1 = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun f _ =>
      mul_nonneg (hc f) (testMass_nonneg _))).mp
    exact hm
  have hz : linearCombination ℝ (fun f : SmoothTest => criticalDatum a b C f.1.1) c = 0 := by
    change ∑ f ∈ c.support, c f * criticalDatum a b C f.1.1 = 0
    apply Finset.sum_eq_zero
    intro f hf
    rcases mul_eq_zero.mp (hterms f hf) with hcf | hmf
    · rw [hcf, zero_mul]
    · rw [(testMass_eq_zero_iff f).mp hmf, criticalDatum_zero, mul_zero]
  linarith

theorem mixture_criticalDatum_mass (a b C : ℝ) (c : SmoothTest →₀ ℝ) :
    linearCombination ℝ (fun f : SmoothTest => criticalDatum a b C f.1.1) c =
      linearCombination ℝ (fun f : SmoothTest => criticalDatum a b 0 f.1.1) c +
        C * smoothMixtureMass c := by
  change (∑ f ∈ c.support, c f * criticalDatum a b C f.1.1) =
    (∑ f ∈ c.support, c f * criticalDatum a b 0 f.1.1) +
      C * ∑ f ∈ c.support, c f * testMass f.1.1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f _
  unfold criticalDatum
  ring

/-- The signed energy is unbounded below even after fixing the mass to one. -/
theorem exists_normalized_critical_null_below {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (R : ℝ) :
    ∃ c : SmoothTest →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      linearCombination ℝ (fun f : SmoothTest => logVector f.1) c = 0 ∧
      smoothMixtureMass c = 1 ∧
      linearCombination ℝ (fun f : SmoothTest => criticalDatum a b 0 f.1.1) c < R := by
  obtain ⟨c, hc, hz, hneg⟩ := exists_negative_smooth_null_mixture ha hab (-R)
  have hm := smoothMixtureMass_pos_of_negative hc hneg
  refine ⟨(smoothMixtureMass c)⁻¹ • c, ?_, ?_, ?_, ?_⟩
  · intro f
    exact mul_nonneg (inv_nonneg.mpr hm.le) (hc f)
  · rw [map_smul, hz, smul_zero]
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hm.ne']
  · rw [map_smul, smul_eq_mul, ← div_eq_inv_mul]
    apply (div_lt_iff₀ hm).mpr
    rw [mixture_criticalDatum_mass] at hneg
    linarith

end RHTower.WeilWorkPBAP

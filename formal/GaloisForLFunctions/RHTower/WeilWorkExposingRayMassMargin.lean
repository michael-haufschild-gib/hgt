import GaloisForLFunctions.RHTower.WeilWorkExposingRayFiniteRealization

/-!
# Exact exposing-ray mass and the zero-margin boundary

Every nonnegative mixture matching the literal truncated ray retains a fixed
positive physical mass per unit ray multiplier. The exact natural-aperture
realizations therefore have exponentially small mass-normalized energy excess
from above, and disprove every fixed positive mass margin, even with arbitrary
fixed box-tail slack. Every integer atom, including the zero tail, is matched.

These unconditional constructions give no lower sign for the energy excess and
do not prove prime-blind positivity or the universal RH receiver.
Paper proof: docs/reports/weil-work/results/02-exposing-ray/MATCHED-MASS-MARGIN-PROOF.md.
-/

open MeasureTheory Filter Topology Set Real Zeta23
noncomputable section
namespace RHTower.ExposingRayMass

/-- Physical squared L2 mass, with no Fourier normalization factor. -/
def mass (f : ℝ → ℂ) : ℝ := ∫ u, ‖f u‖ ^ 2

/-- Complete complex autocorrelation is bounded by physical mass. -/
theorem norm_corr_le_mass {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (y : ℝ) : ‖EF.weilTest f f y‖ ≤ mass f := by
  have hs : HasCompactSupport (fun u => ‖f u‖ ^ 2) := by
    simp only [pow_two]
    exact hfc.norm.mul_right
  have hi : Integrable (fun u => ‖f u‖ ^ 2) :=
    (hf.norm.pow 2).integrable_of_hasCompactSupport hs
  have hiy : Integrable (fun u => ‖f (u-y)‖ ^ 2) := hi.comp_sub_right y
  have hmajor : Integrable (fun u => (‖f u‖ ^ 2 + ‖f (u-y)‖ ^ 2)/2) :=
    (hi.add hiy).div_const 2
  have hpt : ∀ u : ℝ, ‖f u‖ * ‖f (u-y)‖ ≤
      (‖f u‖ ^ 2 + ‖f (u-y)‖ ^ 2)/2 := fun u => by
    nlinarith [sq_nonneg (‖f u‖-‖f (u-y)‖)]
  have hbound := integral_mono_of_nonneg
    (Eventually.of_forall fun u => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    hmajor (Eventually.of_forall hpt)
  have hnorm : ‖EF.weilTest f f y‖ ≤ ∫ u, ‖f u‖ * ‖f (u-y)‖ := by
    rw [weilTest_apply]
    have h := norm_integral_le_integral_norm (μ := volume)
      (fun u => f u * starRingEnd ℂ (f (u-y)))
    simpa only [norm_mul,Complex.norm_conj] using h
  have hshift : (∫ u, ‖f (u-y)‖ ^ 2) = mass f :=
    integral_sub_right_eq_self (fun u => ‖f u‖ ^ 2) y
  have heq : (∫ u, (‖f u‖ ^ 2 + ‖f (u-y)‖ ^ 2)/2) = mass f := by
    rw [integral_div,integral_add hi hiy,hshift]
    change (mass f + mass f)/2 = mass f
    ring
  exact hnorm.trans (hbound.trans_eq heq)

/-- Both signed logarithmic samples are retained in the trace bound. -/
theorem abs_atom_le_mass {a : ℝ} {f : ℝ → ℂ} (hf : IsPolarTest a f) (n : ℕ) :
    |atomCoeff f n| ≤ 2*mass f := by
  have hfc : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hf.2.2.1
  have hp := norm_corr_le_mass hf.2.1.continuous hfc (log n)
  have hm := norm_corr_le_mass hf.2.1.continuous hfc (-log n)
  exact (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (by linarith))

/-- The literal ray forces a fixed positive physical mass per unit multiplier,
for every nonnegative matched mixture, independently of its aperture or representation. -/
theorem matched_mass_floor :
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ {ι : Type} [Fintype ι] (a : ι → ℝ) (f : ι → ℝ → ℂ) (α : ι → ℝ) (t : ℝ),
        (∀ i, IsPolarTest (a i) (f i)) → (∀ i, 0 ≤ α i) →
        (∀ n : ℕ, 2 ≤ n → 2*π*∑ i, α i*atomCoeff (f i) n=t*exposingWeightTrunc N n) →
        t*m₀ ≤ ∑ i, α i*mass (f i) := by
  obtain ⟨n,hn,hp⟩ := ((eventually_ge_atTop 2).and exposingWeight_eventually_pos).exists
  refine ⟨exposingWeight n/(4*π),div_pos hp (by positivity),n,fun N hN => ?_⟩
  intro ι _ a f α t hf hα hm
  have hbound : (∑ i, α i*atomCoeff (f i) n) ≤ 2*∑ i, α i*mass (f i) := by
    calc (∑ i, α i*atomCoeff (f i) n) ≤ ∑ i, α i*(2*mass (f i)) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left
            ((le_abs_self _).trans (abs_atom_le_mass (hf i) n)) (hα i)
      _ = 2*∑ i, α i*mass (f i) := by rw [Finset.mul_sum]; congr 1; ext i; ring
  have hmatch := hm n hn
  rw [exposingWeightTrunc,if_pos hN] at hmatch
  have h := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 2*π by positivity)
  rw [hmatch] at h
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (show 0 < 4*π by positivity)).mpr
  nlinarith [h]

/-- Exact all-integer matched families retain positive mass at natural aperture,
while their energy excess has the literal vanishing box-tail upper bound. -/
theorem near_threshold_mass :
    ∃ C m₀ : ℝ, 0 ≤ C ∧ 0 < m₀ ∧ ∀ᶠ N : ℕ in atTop,
      ∃ (m : ℕ) (a : Fin m → ℝ) (f : Fin m → ℝ → ℂ) (α : Fin m → ℝ),
        (∀ i, a i ≤ log N/2+C) ∧ (∀ i, IsPolarTest (a i) (f i)) ∧
        (∀ i, 0 ≤ α i) ∧
        (∀ n : ℕ, 2 ≤ n → 2*π*∑ i, α i*atomCoeff (f i) n=exposingWeightTrunc N n) ∧
        m₀ ≤ (∑ i, α i*mass (f i)) ∧
        (∑ i, α i*archEnergy (f i)) ≤ archimedeanExposingThreshold+2*exposingTail N := by
  obtain ⟨C,hC⟩ := ExposingRayRealization.natural_aperture
  obtain ⟨m₀,hm₀,N₀,hM⟩ := matched_mass_floor
  refine ⟨max C 0,m₀,le_max_right _ _,hm₀,?_⟩
  filter_upwards [hC 1 (by norm_num),eventually_ge_atTop N₀] with N hN hNN
  obtain ⟨m,a,f,α,ha,hf,hα,hm,hE⟩ := hN
  refine ⟨m,a,f,α,fun i => (ha i).trans (by linarith [le_max_left C 0]),
    hf,hα,hm,?_,?_⟩
  · simpa only [one_mul] using hM N hNN a f α 1 hf hα (by simpa only [one_mul] using hm)
  · norm_num only at hE
    exact hE

/-- For every subcritical theta rate, exact matched families have exponentially
small mass-normalized energy excess from above. This asserts no lower sign. -/
theorem normalized_excess_upper {r : ℝ} (hr : 0 < r)
    (hrr : r < exposingWeightDecayRate) :
    ∃ C K m₀ : ℝ, 0 ≤ C ∧ 0 < K ∧ 0 < m₀ ∧ ∀ᶠ N : ℕ in atTop,
      ∃ (m : ℕ) (a : Fin m → ℝ) (f : Fin m → ℝ → ℂ) (α : Fin m → ℝ),
        (∀ i, a i ≤ log N/2+C) ∧ (∀ i, IsPolarTest (a i) (f i)) ∧
        (∀ i, 0 ≤ α i) ∧
        (∀ n : ℕ, 2 ≤ n → 2*π*∑ i, α i*atomCoeff (f i) n=exposingWeightTrunc N n) ∧
        m₀ ≤ (∑ i, α i*mass (f i)) ∧
        (∑ i, α i*archEnergy (f i))-archimedeanExposingThreshold ≤
          K*exp (-(r*N))*(∑ i, α i*mass (f i)) := by
  obtain ⟨C,m₀,hC,hm₀,hfam⟩ := near_threshold_mass
  obtain ⟨B,hB,hT⟩ := exposingTail_exponential_upper hr hrr
  let K := 2*B/m₀
  have hK : 0 < K := div_pos (by positivity) hm₀
  refine ⟨C,K,m₀,hC,hK,hm₀,?_⟩
  filter_upwards [hfam] with N hN
  obtain ⟨m,a,f,α,ha,hf,hα,hm,hM,hE⟩ := hN
  refine ⟨m,a,f,α,ha,hf,hα,hm,hM,?_⟩
  calc (∑ i, α i*archEnergy (f i))-archimedeanExposingThreshold ≤
        2*exposingTail N := by linarith
    _ ≤ 2*(B*exp (-(r*N))) := mul_le_mul_of_nonneg_left (hT N) (by norm_num)
    _ = (K*exp (-(r*N)))*m₀ := by dsimp [K]; field_simp
    _ ≤ (K*exp (-(r*N)))*(∑ i, α i*mass (f i)) :=
      mul_le_mul_of_nonneg_left hM (mul_pos hK (exp_pos _)).le

/-- Every fixed positive mass margin fails on the exact exposing ray, even after
allowing any fixed real multiple of the box tail. No positivity premise is used. -/
theorem mass_margin_counterexample :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, ∀ᶠ N : ℕ in atTop,
      N ≤ ⌊exp (2*(log N/2+C))⌋₊ ∧
      ∃ (m : ℕ) (a : Fin m → ℝ) (f : Fin m → ℝ → ℂ) (α : Fin m → ℝ),
        (∀ i, a i ≤ log N/2+C) ∧ (∀ i, IsPolarTest (a i) (f i)) ∧
        (∀ i, 0 ≤ α i) ∧
        (∀ n : ℕ, 2 ≤ n → 2*π*∑ i, α i*atomCoeff (f i) n=exposingWeightTrunc N n) ∧
        (∑ i, α i*archEnergy (f i))-ε*(∑ i, α i*mass (f i)) <
          archimedeanExposingThreshold-c*exposingTail N := by
  obtain ⟨C,m₀,hC,hm₀,hfam⟩ := near_threshold_mass
  refine ⟨C,hC,fun ε hε c => ?_⟩
  have ht : Tendsto (fun N : ℕ => (c+2)*exposingTail N) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_exposingTail.const_mul (c+2)
  have hsmall : ∀ᶠ N : ℕ in atTop, (c+2)*exposingTail N < ε*m₀ :=
    Tendsto.eventually_lt_const (mul_pos hε hm₀) ht
  filter_upwards [hfam,hsmall,eventually_ge_atTop 1] with N hN hs hN1
  obtain ⟨m,a,f,α,ha,hf,hα,hm,hM,hE⟩ := hN
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hfloor : N ≤ ⌊exp (2*(log N/2+C))⌋₊ := by
    apply Nat.le_floor
    calc (N:ℝ) = exp (log N) := (exp_log hNpos).symm
      _ ≤ exp (2*(log N/2+C)) := exp_le_exp.mpr (by linarith)
  refine ⟨hfloor,m,a,f,α,ha,hf,hα,hm,?_⟩
  have := mul_le_mul_of_nonneg_left hM hε.le
  nlinarith

end RHTower.ExposingRayMass

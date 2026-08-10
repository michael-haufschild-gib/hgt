import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ModulusBudget
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount

/-!
# Divergence of the modulus budget

The realization defect of one prime is `−log|Γ_{q_p}(1+it)|`, and its leading term is
`q_p (1 − cos(tσ log p))`.  The window count of the previous module shows that the leading series
diverges for every nonzero phase throughout `1/2 < σ ≤ 1`; since the defect differs from it by an
absolutely convergent series, the defect series diverges too.

Consequently the modulus of any phase-gauged product `∏ Γ_{q_p}(1+it) u_p` with `‖u_p‖ = 1` tends
to `0`: a unimodular gauge cannot pay a modulus debt.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter
open scoped Topology

/-- A nonnegative family that is not summable has partial sums escaping to `+∞`. -/
theorem tendsto_finsetSum_atTop_of_not_summable {ι : Type*} {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) (h : ¬ Summable f) :
    Tendsto (fun s : Finset ι => ∑ i ∈ s, f i) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  have hex : ∃ s : Finset ι, b < ∑ i ∈ s, f i := by
    by_contra hcon
    exact h (summable_of_sum_le hf fun s => le_of_not_gt fun hgt => hcon ⟨s, hgt⟩)
  obtain ⟨s₀, hs₀⟩ := hex
  filter_upwards [Filter.eventually_ge_atTop s₀] with s hs
  exact le_trans hs₀.le (Finset.sum_le_sum_of_subset_of_nonneg hs fun i _ _ => hf i)

/-! ## The leading series diverges for every nonzero phase -/

theorem not_summable_leading_primes_of_ne_zero {σ τ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hτ : τ ≠ 0) :
    ¬ Summable (fun p : Nat.Primes =>
      ((p : ℕ) : ℝ) ^ (-σ) * (1 - Real.cos (τ * Real.log ((p : ℕ) : ℝ)))) := by
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · intro hsum
    refine not_summable_leading_primes hσ hσ1 (by linarith : (0 : ℝ) < -τ) ?_
    refine hsum.congr fun p => ?_
    rw [show -τ * Real.log ((p : ℕ) : ℝ) = -(τ * Real.log ((p : ℕ) : ℝ)) by ring, Real.cos_neg]
  · exact not_summable_leading_primes hσ hσ1 hpos

theorem phaseAngle_primeNome {σ : ℝ} (hσ : 0 < σ) (t : ℝ) (p : Nat.Primes) :
    phaseAngle (primeNome hσ p) t = (t * σ) * Real.log ((p : ℕ) : ℝ) := by
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [phaseAngle, primeNome_val, Real.log_rpow hp]
  ring

/-- **The leading term of the modulus budget is not summable** anywhere in the condensed chamber,
for every nonzero `t`. -/
theorem not_summable_leading {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) {t : ℝ} (ht : t ≠ 0) :
    ¬ Summable (fun p : Nat.Primes =>
      (primeNome hσ p).val * (1 - Real.cos (phaseAngle (primeNome hσ p) t))) := by
  intro hsum
  refine not_summable_leading_primes_of_ne_zero hσ hσ1 (mul_ne_zero ht hσ.ne') ?_
  refine hsum.congr fun p => ?_
  rw [primeNome_val, phaseAngle_primeNome]

/-! ## The defect series diverges -/

theorem primeDefect_nonneg (q : RealEulerNome) (t : ℝ) : 0 ≤ primeDefect q t := by
  rw [primeDefect, neg_log_norm_qGammaOn]
  exact tsum_nonneg fun jr => ladderTerm_nonneg q.pos.le _ jr

/-- **(GAS3.2): the modulus budget diverges.**  For `1/2 < σ ≤ 1` and `t ≠ 0` the realization
defects of the primes are not summable. -/
theorem not_summable_primeDefect {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ) (hσ1 : σ ≤ 1)
    {t : ℝ} (ht : t ≠ 0) :
    ¬ Summable (fun p : Nat.Primes => primeDefect (primeNome hσ p) t) := by
  intro hsum
  refine not_summable_leading hσ hσ1 ht ?_
  have hdiff := summable_defect_sub_leading hσ hhalf t
  have := hsum.sub hdiff
  refine this.congr fun p => ?_
  rw [primeDefect]
  ring

/-- The defect series, read over the naturals. -/
noncomputable def primeDefectNat {σ : ℝ} (hσ : 0 < σ) (t : ℝ) (n : ℕ) : ℝ :=
  if h : n.Prime then primeDefect (primeNome hσ ⟨n, h⟩) t else 0

theorem primeDefectNat_nonneg {σ : ℝ} (hσ : 0 < σ) (t : ℝ) (n : ℕ) :
    0 ≤ primeDefectNat hσ t n := by
  rw [primeDefectNat]
  split
  · exact primeDefect_nonneg _ _
  · exact le_rfl

theorem not_summable_primeDefectNat {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ) (hσ1 : σ ≤ 1)
    {t : ℝ} (ht : t ≠ 0) : ¬ Summable (primeDefectNat hσ t) := by
  intro hsum
  refine not_summable_primeDefect hσ hhalf hσ1 ht ?_
  refine (hsum.comp_injective Nat.Primes.coe_nat_injective).congr fun p => ?_
  show primeDefectNat hσ t ((p : ℕ)) = _
  rw [primeDefectNat, dif_pos p.2]

/-- **(GAS3.2) in the card's form:** `Δ_P(t) = ∑_{p ≤ P} −log|φ_p(t)| → ∞`. -/
theorem tendsto_defectPartial_atTop {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ) (hσ1 : σ ≤ 1)
    {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun P : ℕ => ∑ n ∈ Finset.range P, primeDefectNat hσ t n) atTop atTop :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg (primeDefectNat_nonneg hσ t)).1
    (not_summable_primeDefectNat hσ hhalf hσ1 ht)

/-- The same over finite sets of primes. -/
theorem tendsto_defectSum_atTop {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ) (hσ1 : σ ≤ 1)
    {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun s : Finset Nat.Primes => ∑ p ∈ s, primeDefect (primeNome hσ p) t)
      atTop atTop :=
  tendsto_finsetSum_atTop_of_not_summable (fun _ => primeDefect_nonneg _ _)
    (not_summable_primeDefect hσ hhalf hσ1 ht)

/-! ## Item 1 of Theorem 2.2: no phase gauge produces a nonzero limit -/

/-- **A unimodular gauge cannot pay the modulus debt:** for `1/2 < σ ≤ 1` and `t ≠ 0`, the
gauged product `∏ Γ_{q_p}(1+it) u_p` has modulus tending to `0` for every family of unimodular
`u_p`. -/
theorem tendsto_norm_prod_gauge_zero {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ) (hσ1 : σ ≤ 1)
    {t : ℝ} (ht : t ≠ 0) (u : Nat.Primes → ℂ) (hu : ∀ p, ‖u p‖ = 1) :
    Tendsto (fun s : Finset Nat.Primes =>
        ‖∏ p ∈ s, (qGammaOn (primeNome hσ p) (1 + (t : ℂ) * Complex.I) * u p)‖)
      atTop (𝓝 0) := by
  have hdiv := tendsto_defectSum_atTop hσ hhalf hσ1 ht
  have hneg : Tendsto (fun s : Finset Nat.Primes =>
      -∑ p ∈ s, primeDefect (primeNome hσ p) t) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hdiv
  have hexp := Real.tendsto_exp_atBot.comp hneg
  refine hexp.congr fun s => ?_
  exact (norm_prod_gauge (fun p => primeNome hσ p) t u hu s).symm

/-! ## Theorem 1.1: no centering produces a characteristic function -/

/-- **Theorem 1.1, analytic core.**  For `1/2 < σ ≤ 1` the gauged characteristic products admit no
pointwise limit that is continuous at the origin.  Since every characteristic function is
continuous and takes the value `1` at `0`, no centering makes the socle series converge in
distribution.

The mechanism is the modulus budget alone: the limit must vanish at every `t ≠ 0`, so it cannot
approach `1` at the origin. -/
theorem not_exists_continuousAt_limit {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ) (hσ1 : σ ≤ 1)
    (u : ℝ → Nat.Primes → ℂ) (hu : ∀ t p, ‖u t p‖ = 1) :
    ¬ ∃ ψ : ℝ → ℂ, ψ 0 = 1 ∧ ContinuousAt ψ 0 ∧
      ∀ t : ℝ, Tendsto (fun s : Finset Nat.Primes =>
          ∏ p ∈ s, (qGammaOn (primeNome hσ p) (1 + (t : ℂ) * Complex.I) * u t p))
        atTop (𝓝 (ψ t)) := by
  rintro ⟨ψ, hψ0, hcont, hconv⟩
  have hzero : ∀ t : ℝ, t ≠ 0 → ψ t = 0 := by
    intro t ht
    have hnorm : Tendsto (fun s : Finset Nat.Primes =>
        ‖∏ p ∈ s, (qGammaOn (primeNome hσ p) (1 + (t : ℂ) * Complex.I) * u t p)‖)
      atTop (𝓝 ‖ψ t‖) := (continuous_norm.continuousAt).tendsto.comp (hconv t)
    have := tendsto_nhds_unique hnorm (tendsto_norm_prod_gauge_zero hσ hhalf hσ1 ht (u t) (hu t))
    exact norm_eq_zero.1 this
  have hnb : (𝓝[≠] (0 : ℝ)).NeBot := inferInstance
  have h1 : Tendsto ψ (𝓝[≠] (0 : ℝ)) (𝓝 (ψ 0)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto ψ (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hzero t ht).symm
  have := tendsto_nhds_unique h1 h2
  rw [hψ0] at this
  exact one_ne_zero this

/-- The same for an arbitrary real centering `c_p`, which is the card's statement. -/
theorem not_exists_centering_limit {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ) (hσ1 : σ ≤ 1)
    (c : Nat.Primes → ℝ) :
    ¬ ∃ ψ : ℝ → ℂ, ψ 0 = 1 ∧ ContinuousAt ψ 0 ∧
      ∀ t : ℝ, Tendsto (fun s : Finset Nat.Primes =>
          ∏ p ∈ s, (qGammaOn (primeNome hσ p) (1 + (t : ℂ) * Complex.I)
            * Complex.exp (-((t * c p : ℝ) : ℂ) * Complex.I)))
        atTop (𝓝 (ψ t)) := by
  refine not_exists_continuousAt_limit hσ hhalf hσ1
    (fun t p => Complex.exp (-((t * c p : ℝ) : ℂ) * Complex.I)) fun t p => ?_
  rw [show -((t * c p : ℝ) : ℂ) * Complex.I = ((-(t * c p) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

end GaloisForLFunctions.HTGeometry

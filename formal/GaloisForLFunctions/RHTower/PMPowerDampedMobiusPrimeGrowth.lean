import GaloisForLFunctions.RHTower.PMPowerDampedMobiusNormFloor
import GaloisForLFunctions.RHTower.MobiusFinitePrimeApertureSourceConsumption

/-! Exact finite-prime sources stabilize to the literal power-damped source.
Every positive damping neighborhood contains a norm-increasing canonical
prime-cutoff step and a finite source exceeding every prescribed subunit budget.
Uniform prime-step contraction is therefore impossible; finite norm admission
for arbitrarily small positive damping remains open. -/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower


/-- A finite-prime source retains exactly the squarefree divisors of the prime product. -/
def pmFinitePrimePowerDampedFermiSource (S : Finset ℕ) (ε t : ℝ) : ℂ :=
  -(∑ d ∈ Finset.Icc 1 (∏ p ∈ S, p),
    finitePrimeApertureMobiusCoefficient S d * (((d : ℝ) ^ (-ε) : ℝ) : ℂ) *
      fermiNymanGen (d : ℝ) t)

theorem pm_finitePrime_coefficient_eq_zero_above_product {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) {d : ℕ} (hd : (∏ p ∈ S, p) < d) :
    finitePrimeApertureMobiusCoefficient S d = 0 := by
  unfold finitePrimeApertureMobiusCoefficient
  split_ifs with hcover
  · by_cases hsq : Squarefree d
    · have hle : d ≤ ∏ p ∈ S, p := by
        rw [← Nat.prod_primeFactors_of_squarefree hsq]
        exact Finset.prod_le_prod_of_subset_of_one_le' hcover
          (fun p hp _ => (hS p hp).one_le)
      omega
    · simp [mobiusComplexCoefficient,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
  · rfl

theorem memLp_pmFinitePrimePowerDampedFermiSource (S : Finset ℕ) (ε : ℝ) :
    MemLp (pmFinitePrimePowerDampedFermiSource S ε) 2
      (volume.restrict (Ioi (0 : ℝ))) := by
  let c : ℕ → ℂ := fun d => finitePrimeApertureMobiusCoefficient S d *
    (((d : ℝ) ^ (-ε) : ℝ) : ℂ)
  have h := memLp_finsetSum (Finset.Icc 1 (∏ p ∈ S, p)) (f := fun d =>
    fun t : ℝ => c d * fermiNymanGen (d : ℝ) t) (fun d hd =>
      (memLp_pm_fermiNymanGen (by exact_mod_cast (Finset.mem_Icc.mp hd).1)).const_mul (c d))
  exact h.neg

theorem pmFinitePrimePowerDampedFermiSource_empty (ε : ℝ) :
    pmFinitePrimePowerDampedFermiSource ∅ ε = -fermiNymanGen 1 := by
  funext t
  simp [pmFinitePrimePowerDampedFermiSource, finitePrimeApertureMobiusCoefficient,
    mobiusComplexCoefficient]

theorem pmFinitePrimePowerDampedFermiSource_eq_of_covers {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (ε : ℝ) {t : ℝ} (ht : 0 < t)
    (hcover : mobiusFinitePrimeAperture ⌊1 / t⌋₊ ⊆ S) :
    pmFinitePrimePowerDampedFermiSource S ε t = pmPowerDampedFermiSource ε t := by
  let K := max (∏ p ∈ S, p) ⌊1 / t⌋₊
  have hext : pmFinitePrimePowerDampedFermiSource S ε t =
      -(∑ d ∈ Finset.Icc 1 K,
        finitePrimeApertureMobiusCoefficient S d * (((d : ℝ) ^ (-ε) : ℝ) : ℂ) *
          fermiNymanGen (d : ℝ) t) := by
    unfold pmFinitePrimePowerDampedFermiSource
    congr 1
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right (le_max_left _ _))
    intro d hd hnot
    have hgt : (∏ p ∈ S, p) < d := by
      have hd1 := (Finset.mem_Icc.mp hd).1
      have hn := mt Finset.mem_Icc.mpr hnot
      omega
    rw [pm_finitePrime_coefficient_eq_zero_above_product hS hgt, zero_mul, zero_mul]
  rw [hext, pmPowerDampedFermiSource_eq_sum ε ht (le_max_right _ _)]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdsmall : d ≤ ⌊1 / t⌋₊
  · rw [finitePrimeApertureMobiusCoefficient_eq_of_covers hcover hdsmall]
    simp only [mobiusComplexCoefficient, Complex.ofReal_mul, Complex.ofReal_intCast]
  · have hd1 := (Finset.mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hxd : 1 / t < (d : ℝ) :=
      (Nat.lt_floor_add_one (1 / t)).trans_le (by exact_mod_cast (by omega : ⌊1 / t⌋₊ + 1 ≤ d))
    have hinv : 1 / (d : ℝ) < t := by
      apply (div_lt_iff₀ hd0).mpr
      have h := (div_lt_iff₀ ht).mp hxd
      nlinarith
    rw [fermiNymanGen_eq_zero_of_inv_lt hd0 hinv, mul_zero, mul_zero]

theorem tendsto_pmFinitePrimePowerDampedFermiSource (ε : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N => pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε t)
      atTop (𝓝 (pmPowerDampedFermiSource ε t)) := by
  have heq : ∀ᶠ N : ℕ in atTop,
      pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε t =
        pmPowerDampedFermiSource ε t := by
    filter_upwards [eventually_ge_atTop ⌊1 / t⌋₊] with N hN
    apply pmFinitePrimePowerDampedFermiSource_eq_of_covers
      (fun p hp => (Finset.mem_filter.mp hp).2) ε ht
    intro p hp
    simp only [mobiusFinitePrimeAperture, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [heq] with N hN
  exact hN.symm

/-- A uniform canonical prime-cutoff budget passes to the literal source. -/
theorem pmPowerDampedFermiSource_norm_le_of_canonical_prime_budget (ε : ℝ) {C : ENNReal}
    (hC : ∀ N : ℕ,
      eLpNorm (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε) 2
        (volume.restrict (Ioi (0 : ℝ))) ≤ C) :
    eLpNorm (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ≤ C := by
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (Eventually.of_forall hC)
    (fun N => (memLp_pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact tendsto_pmFinitePrimePowerDampedFermiSource ε ht

/-- A uniform finite-prime budget passes to the literal source without changing coefficients. -/
theorem pmPowerDampedFermiSource_norm_le_of_prime_budget (ε : ℝ) {C : ENNReal}
    (hC : ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) →
      eLpNorm (pmFinitePrimePowerDampedFermiSource S ε) 2
        (volume.restrict (Ioi (0 : ℝ))) ≤ C) :
    eLpNorm (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ≤ C :=
  pmPowerDampedFermiSource_norm_le_of_canonical_prime_budget ε
    (fun N => hC (mobiusFinitePrimeAperture N) (fun _ hp => (Finset.mem_filter.mp hp).2))

/-- Norm monotonicity at every fresh prime would confine all finite sources to the seed budget. -/
theorem pmFinitePrimePowerDampedFermiSource_seed_bound_of_insert_le (ε : ℝ)
    (hstep : ∀ S : Finset ℕ, (∀ q ∈ S, Nat.Prime q) → ∀ p : ℕ, Nat.Prime p → p ∉ S →
      eLpNorm (pmFinitePrimePowerDampedFermiSource (insert p S) ε) 2
        (volume.restrict (Ioi (0 : ℝ))) ≤
      eLpNorm (pmFinitePrimePowerDampedFermiSource S ε) 2
        (volume.restrict (Ioi (0 : ℝ)))) :
    ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) →
      eLpNorm (pmFinitePrimePowerDampedFermiSource S ε) 2
        (volume.restrict (Ioi (0 : ℝ))) ≤
      eLpNorm (fermiNymanGen 1) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    rw [pmFinitePrimePowerDampedFermiSource_empty, eLpNorm_neg]
  | @insert p S hp ih =>
    intro hS
    have hsub : ∀ q ∈ S, Nat.Prime q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    exact (hstep S hsub p (hS p (Finset.mem_insert_self _ _)) hp).trans (ih hsub)

/-- Every positive damping neighborhood contains an actual finite-prime norm-increasing step. -/
theorem pmFinitePrimePowerDampedFermiSource_exists_growth {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ S : Finset ℕ, (∀ q ∈ S, Nat.Prime q) ∧
      ∃ p : ℕ, Nat.Prime p ∧ p ∉ S ∧
        eLpNorm (pmFinitePrimePowerDampedFermiSource S ε) 2
          (volume.restrict (Ioi (0 : ℝ))) <
        eLpNorm (pmFinitePrimePowerDampedFermiSource (insert p S) ε) 2
          (volume.restrict (Ioi (0 : ℝ))) := by
  by_contra h
  push Not at h
  apply pmPowerDampedFermiSource_no_seed_norm_neighborhood
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  apply pmPowerDampedFermiSource_norm_le_of_prime_budget
  exact pmFinitePrimePowerDampedFermiSource_seed_bound_of_insert_le ε (h ε hε hεδ)

/-- Successive canonical apertures add precisely the next integer when it is prime. -/
theorem pm_mobiusFinitePrimeAperture_succ (N : ℕ) :
    mobiusFinitePrimeAperture (N + 1) =
      if Nat.Prime (N + 1) then insert (N + 1) (mobiusFinitePrimeAperture N)
      else mobiusFinitePrimeAperture N := by
  simp only [mobiusFinitePrimeAperture, Finset.range_add_one (n := N + 1), Finset.filter_insert]

/-- Even canonical increasing-prime cutoffs must increase norm in every damping neighborhood. -/
theorem pmFinitePrimePowerDampedFermiSource_exists_canonical_growth {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ N : ℕ, Nat.Prime (N + 1) ∧
      eLpNorm (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε) 2
        (volume.restrict (Ioi (0 : ℝ))) <
      eLpNorm (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (N + 1)) ε) 2
        (volume.restrict (Ioi (0 : ℝ))) := by
  by_contra h
  push Not at h
  apply pmPowerDampedFermiSource_no_seed_norm_neighborhood
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  apply pmPowerDampedFermiSource_norm_le_of_canonical_prime_budget
  intro N
  induction N with
  | zero =>
    have hz : mobiusFinitePrimeAperture 0 = ∅ := by
      simp [mobiusFinitePrimeAperture, Nat.not_prime_zero]
    rw [hz, pmFinitePrimePowerDampedFermiSource_empty, eLpNorm_neg]
  | succ N ih =>
    by_cases hp : Nat.Prime (N + 1)
    · exact (h ε hε hεδ N hp).trans ih
    · rw [pm_mobiusFinitePrimeAperture_succ, if_neg hp]
      exact ih

/-- Every subunit budget is exceeded by a canonical finite-prime source arbitrarily near zero. -/
theorem pmFinitePrimePowerDampedFermiSource_exceeds_subunit_budget
    {C : ENNReal} (hC : C < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ N : ℕ,
      C < eLpNorm (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε) 2
        (volume.restrict (Ioi (0 : ℝ))) := by
  by_contra h
  push Not at h
  apply pmPowerDampedFermiSource_no_subunit_neighborhood hC
  exact ⟨δ, hδ, fun ε hε hεδ =>
    pmPowerDampedFermiSource_norm_le_of_canonical_prime_budget ε (h ε hε hεδ)⟩

end RHTower

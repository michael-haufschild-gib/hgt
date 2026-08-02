import GaloisForLFunctions.HTGeometry.QuasiAbelianAutomorphicForms
import GaloisForLFunctions.HTGeometry.MultivariateEntireVanishingPower
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Poincare series for a fixed quasi-Abelian automorphic factor

The literal Poincare term attached to a seed `f` and lattice element `γ` is

`ψ(γ,x)⁻¹ f(x+γ)`.

Local normal convergence makes its sum line-entire. Reindexing the sum by lattice translation
and applying the factor cocycle proves the exact fixed-factor automorphy law. No convergence or
jet-surjectivity conclusion is stored in the factor structure: every constructed section carries
its own local-normal-convergence proof.
-/

open Filter Function Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One term of the Poincare series generated from `seed` by the fixed factor `ψ`. -/
def poincareTerm {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (γ : Γ) (x : Fin d → ℂ) : ℂ :=
  ((ψ.factor γ).1 x)⁻¹ * seed.1 (x + γ.1)

/-- Each Poincare term is continuous. -/
theorem continuous_poincareTerm {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d) (γ : Γ) :
    Continuous (poincareTerm ψ seed γ) := by
  apply Continuous.mul
  · exact (ψ.factor γ).1.continuous.inv₀ (ψ.nowhereZero γ)
  · exact seed.1.continuous.comp (continuous_id.add continuous_const)

/-- Each Poincare term remains entire on every affine complex line. -/
theorem lineEntire_poincareTerm {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d) (γ : Γ) :
    LineEntire ⟨poincareTerm ψ seed γ, continuous_poincareTerm ψ seed γ⟩ := by
  intro x v
  have hf : Differentiable ℂ
      (fun z : ℂ => ((ψ.factor γ).1 (x + z • v))⁻¹) :=
    ((ψ.factor γ).property x v).inv fun z => ψ.nowhereZero γ (x + z • v)
  have hs := seed.property (x + γ.1) v
  change Differentiable ℂ (fun z : ℂ =>
    ((ψ.factor γ).1 (x + z • v))⁻¹ * seed.1 (x + z • v + γ.1))
  apply hf.mul
  simpa only [add_assoc, add_left_comm, add_comm] using hs

/-- One Poincare summand as a compact-open entire source. -/
def poincareTermEntire {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d) (γ : Γ) :
    MultivariateEntire d :=
  ⟨⟨poincareTerm ψ seed γ, continuous_poincareTerm ψ seed γ⟩,
    lineEntire_poincareTerm ψ seed γ⟩

/-- Translation of a line-entire source by an arbitrary vector. -/
def multivariateEntireTranslate {d : ℕ} (f : MultivariateEntire d)
    (y : Fin d → ℂ) : MultivariateEntire d :=
  ⟨⟨fun x ↦ f.1 (x + y), f.1.continuous.comp (continuous_id.add continuous_const)⟩,
    fun x v ↦ by
      change Differentiable ℂ (fun z : ℂ ↦ f.1 ((x + z • v) + y))
      simpa only [add_assoc, add_left_comm, add_comm] using f.property (x + y) v⟩

@[simp]
theorem multivariateEntireTranslate_apply {d : ℕ} (f : MultivariateEntire d)
    (y x : Fin d → ℂ) :
    (multivariateEntireTranslate f y).1 x = f.1 (x + y) :=
  rfl

/-- The reciprocal of one nowhere-zero automorphic-factor term is again line-entire. -/
def automorphicFactorInverseEntire {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (γ : Γ) : MultivariateEntire d :=
  ⟨⟨fun x ↦ ((ψ.factor γ).1 x)⁻¹,
      (ψ.factor γ).1.continuous.inv₀ (ψ.nowhereZero γ)⟩,
    fun x v ↦ (ψ.factor γ).property x v |>.inv
      (fun z ↦ ψ.nowhereZero γ (x + z • v))⟩

@[simp]
theorem automorphicFactorInverseEntire_apply {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    (γ : Γ) (x : Fin d → ℂ) :
    (automorphicFactorInverseEntire ψ γ).1 x = ((ψ.factor γ).1 x)⁻¹ :=
  rfl

/-- A Poincare term is literally reciprocal factor times translated seed. -/
theorem poincareTermEntire_eq_mul_translate {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    (seed : MultivariateEntire d) (γ : Γ) :
    poincareTermEntire ψ seed γ =
      multivariateEntireMul (automorphicFactorInverseEntire ψ γ)
        (multivariateEntireTranslate seed γ.1) := by
  ext x
  rfl

/-- The zero-index Poincare term is exactly the seed, by normalization of the factor. -/
@[simp]
theorem poincareTermEntire_zero {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    (seed : MultivariateEntire d) :
    poincareTermEntire ψ seed 0 = seed := by
  ext x
  change ((ψ.factor 0).1 x)⁻¹ * seed.1 (x + (0 : Γ).1) = seed.1 x
  rw [ψ.normalized]
  simp

/-- A power-zero built into a seed survives translation and reciprocal-factor multiplication:
every lower mixed jet of the corresponding Poincare term still vanishes. -/
theorem multiIndexJetEvalCLM_poincareTermEntire_eq_zero_of_seed_power
    {d m : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed h g : MultivariateEntire d)
    (γ : Γ) (x : Fin d → ℂ)
    (hseed : seed = multivariateEntireMul (multivariateEntirePow h m) g)
    (hh : h.1 (x + γ.1) = 0) (a : Fin d →₀ ℕ)
    (ha : Finsupp.degree a < m) :
    multiIndexJetEvalCLM x a (poincareTermEntire ψ seed γ) = 0 := by
  let ht := multivariateEntireTranslate h γ.1
  let gt := multivariateEntireTranslate g γ.1
  have hterm : poincareTermEntire ψ seed γ =
      multivariateEntireMul (multivariateEntirePow ht m)
        (multivariateEntireMul (automorphicFactorInverseEntire ψ γ) gt) := by
    ext y
    rw [poincareTermEntire_eq_mul_translate, multivariateEntireMul_apply,
      multivariateEntireMul_apply, multivariateEntirePow_apply,
      automorphicFactorInverseEntire_apply]
    change ((ψ.factor γ).1 y)⁻¹ * seed.1 (y + γ.1) =
      h.1 (y + γ.1) ^ m *
        (((ψ.factor γ).1 y)⁻¹ * g.1 (y + γ.1))
    rw [hseed]
    change ((ψ.factor γ).1 y)⁻¹ *
        (h.1 (y + γ.1) ^ m * g.1 (y + γ.1)) = _
    ring
  rw [hterm]
  exact multiIndexJetEvalCLM_mul_pow_eq_zero_of_degree_lt ht
    (multivariateEntireMul (automorphicFactorInverseEntire ψ γ) gt)
    x hh a ha

/-- Pointwise Poincare sum over the complete translation lattice. -/
def poincareSeries {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (x : Fin d → ℂ) : ℂ :=
  ∑' γ, poincareTerm ψ seed γ x

/-- The factor cocycle transports one Poincare term to its shifted lattice index. -/
theorem poincareTerm_shift {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (γ δ : Γ) (x : Fin d → ℂ) :
    poincareTerm ψ seed γ (x + δ.1) =
      (ψ.factor δ).1 x * poincareTerm ψ seed (γ + δ) x := by
  rw [poincareTerm, poincareTerm]
  have hc := ψ.cocycle γ δ x
  have hγ := ψ.nowhereZero γ (x + δ.1)
  have hδ := ψ.nowhereZero δ x
  rw [hc]
  field_simp
  congr 1
  ext i
  simp [add_comm, add_left_comm]

/-- Reindexing the complete sum gives the fixed-factor automorphy law. -/
theorem poincareSeries_shift {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (δ : Γ) (x : Fin d → ℂ) :
    poincareSeries ψ seed (x + δ.1) =
      (ψ.factor δ).1 x * poincareSeries ψ seed x := by
  simp_rw [poincareSeries, poincareTerm_shift ψ seed]
  rw [tsum_mul_left]
  exact congrArg ((ψ.factor δ).1 x * ·)
    ((Equiv.addRight δ).tsum_eq (fun γ => poincareTerm ψ seed γ x))

/-- A locally normally convergent Poincare sum is continuous. -/
theorem continuous_poincareSeries_of_summableLocallyUniformly
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun γ => poincareTerm ψ seed γ) Set.univ) :
    Continuous (poincareSeries ψ seed) := by
  rw [← continuousOn_univ]
  apply hnormal.hasSumLocallyUniformlyOn.continuousOn
  exact (Filter.Eventually.of_forall fun S =>
    (continuous_finsetSum S fun γ _ =>
      continuous_poincareTerm ψ seed γ).continuousOn).frequently

/-- A locally normally convergent Poincare sum is entire on every affine complex line. -/
theorem lineEntire_poincareSeries_of_summableLocallyUniformly
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun γ => poincareTerm ψ seed γ) Set.univ) :
    LineEntire ⟨poincareSeries ψ seed,
      continuous_poincareSeries_of_summableLocallyUniformly ψ seed hnormal⟩ := by
  intro x v
  let line := affineComplexLine x v
  have hline : SummableLocallyUniformlyOn
      (fun γ z => poincareTerm ψ seed γ (line z)) Set.univ :=
    hnormal.comp line (mapsTo_univ _ _) line.continuous.continuousOn
  have hd : DifferentiableOn ℂ
      (fun z => ∑' γ, poincareTerm ψ seed γ (line z)) Set.univ := by
    apply hline.hasSumLocallyUniformlyOn.differentiableOn
    · exact Filter.Eventually.of_forall fun S =>
        (Differentiable.fun_sum fun γ _ =>
          lineEntire_poincareTerm ψ seed γ x v).differentiableOn
    · exact isOpen_univ
  simpa [poincareSeries, line, affineComplexLine] using
    (differentiableOn_univ.mp hd)

/-- A locally normally convergent Poincare series as a line-entire source. -/
def poincareSeriesEntire {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun γ => poincareTerm ψ seed γ) Set.univ) :
    MultivariateEntire d :=
  ⟨⟨poincareSeries ψ seed,
      continuous_poincareSeries_of_summableLocallyUniformly ψ seed hnormal⟩,
    lineEntire_poincareSeries_of_summableLocallyUniformly ψ seed hnormal⟩

/-- Local normal convergence is convergence of the Poincare series inside the compact-open
`MultivariateEntire` source space.  This packages the analytic theorem in the form consumed by
every continuous mixed-jet observation. -/
theorem hasSum_poincareTermEntire_of_summableLocallyUniformly
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun γ => poincareTerm ψ seed γ) Set.univ) :
    HasSum (fun γ => poincareTermEntire ψ seed γ)
      (poincareSeriesEntire ψ seed hnormal) := by
  change Tendsto
    (fun s : Finset Γ => ∑ γ ∈ s, poincareTermEntire ψ seed γ) atTop
    (nhds (poincareSeriesEntire ψ seed hnormal))
  apply tendsto_multivariateEntire_of_locallyUniform
  rw [← tendstoLocallyUniformlyOn_univ]
  have hnormal' : TendstoLocallyUniformlyOn
      (fun s : Finset Γ => fun x => ∑ γ ∈ s, poincareTerm ψ seed γ x)
      (fun x => ∑' γ, poincareTerm ψ seed γ x) atTop Set.univ :=
    hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
      hnormal.hasSumLocallyUniformlyOn
  convert hnormal' using 1
  · ext s x
    simp [poincareTermEntire]
  · ext x
    simp [poincareSeriesEntire, poincareSeries]

/-- Every mixed jet of a locally normally convergent Poincare series is the sum of the
corresponding mixed jets of its actual terms. -/
theorem hasSum_multiIndexJetEvalCLM_poincareTermEntire
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun γ => poincareTerm ψ seed γ) Set.univ)
    (x : Fin d → ℂ) (a : Fin d →₀ ℕ) :
    HasSum (fun γ => multiIndexJetEvalCLM x a (poincareTermEntire ψ seed γ))
      (multiIndexJetEvalCLM x a (poincareSeriesEntire ψ seed hnormal)) :=
  (multiIndexJetEvalCLM x a).hasSum
    (hasSum_poincareTermEntire_of_summableLocallyUniformly ψ seed hnormal)

/-- If a normally summable seed contains an order-`m` power zero at every nonzero translate of
`x`, then its Poincare sum has exactly the same complete mixed jet below order `m` as the seed.
This is the rigorous single-surviving-term step in Abe's integer-lattice base construction. -/
theorem multiIndexJetEvalCLM_poincareSeriesEntire_eq_seed_of_powerZeros
    {d m : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed h g : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun γ ↦ poincareTerm ψ seed γ) Set.univ)
    (hseed : seed = multivariateEntireMul (multivariateEntirePow h m) g)
    (x : Fin d → ℂ) (hzero : ∀ γ : Γ, γ ≠ 0 → h.1 (x + γ.1) = 0)
    (a : Fin d →₀ ℕ) (ha : Finsupp.degree a < m) :
    multiIndexJetEvalCLM x a (poincareSeriesEntire ψ seed hnormal) =
      multiIndexJetEvalCLM x a seed := by
  have hsum := hasSum_multiIndexJetEvalCLM_poincareTermEntire
    ψ seed hnormal x a
  calc
    multiIndexJetEvalCLM x a (poincareSeriesEntire ψ seed hnormal) =
        ∑' γ : Γ, multiIndexJetEvalCLM x a (poincareTermEntire ψ seed γ) :=
      hsum.tsum_eq.symm
    _ = multiIndexJetEvalCLM x a (poincareTermEntire ψ seed 0) := by
      apply tsum_eq_single 0
      intro γ hγ
      exact multiIndexJetEvalCLM_poincareTermEntire_eq_zero_of_seed_power
        ψ seed h g γ x hseed (hzero γ hγ) a ha
    _ = multiIndexJetEvalCLM x a seed := by rw [poincareTermEntire_zero]

/-- **Poincare construction.** Every locally normally convergent Poincare series belongs to the
fixed automorphic-factor section space. -/
def poincareSeriesAutomorphicForm {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (seed : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun γ => poincareTerm ψ seed γ) Set.univ) : ψ.forms :=
  ⟨poincareSeriesEntire ψ seed hnormal,
    fun γ x => poincareSeries_shift ψ seed γ x⟩

end

end GaloisForLFunctions.HTGeometry

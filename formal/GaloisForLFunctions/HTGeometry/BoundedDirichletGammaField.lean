import GaloisForLFunctions.HTGeometry.DirichletGammaFieldFieldCoefficients
import GaloisForLFunctions.HTGeometry.ZetaGammaFieldHypertranscendence
import GaloisForLFunctions.HTGeometry.VerticalPhaseRank

/-!
# Bounded Dirichlet series over the Gamma field

A Dirichlet series `∑ a_n (n+1)^{-s}` with `‖a_n‖ ≤ 1` converges uniformly on every closed half-plane
to the right of `1`, hence is almost periodic on every vertical strip there.  If moreover its
coefficients are nonzero at arbitrarily many primes, the logarithms of those primes are independent
Bohr frequencies of the line restriction, its frequency rank exceeds every natural number, and the
finite phase law excludes every relation with coefficients in `ℂ(s)⟨Γ⟩`.

Zeta is the case `a ≡ 1`; a Dirichlet `L`-series is the case `a_n = χ(n+1)`, whose coefficients are
nonzero at every prime not dividing the modulus.
-/

open Filter Set Topology Function

open scoped Differential

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance bddDirDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance bddDirIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance bddDirDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance bddDirComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance bddDirRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- A term of a bounded Dirichlet series is dominated by the comparison series. -/
theorem norm_boundedDirichlet_term_le {a : ℕ → ℂ} (hb : ∀ i, ‖a i‖ ≤ 1) {c : ℝ} (i : ℕ) {z : ℂ}
    (hz : c ≤ z.re) :
    ‖a i * Complex.exp (-((Real.log ((i : ℝ) + 1) : ℝ) : ℂ) * z)‖ ≤ 1 / ((i : ℝ) + 1) ^ c := by
  have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hone : (1 : ℝ) ≤ (i : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  have hterm : ‖(1 : ℂ) / ((i : ℂ) + 1) ^ z‖ = 1 / ((i : ℝ) + 1) ^ z.re := norm_zeta_term i z
  have hmono : ((i : ℝ) + 1) ^ c ≤ ((i : ℝ) + 1) ^ z.re :=
    Real.rpow_le_rpow_of_exponent_le hone hz
  have hcpos : (0 : ℝ) < ((i : ℝ) + 1) ^ c := Real.rpow_pos_of_pos hpos c
  have hrpos : (0 : ℝ) < ((i : ℝ) + 1) ^ z.re := Real.rpow_pos_of_pos hpos z.re
  rw [norm_mul, exp_neg_log_succ_mul i z, hterm]
  have hle1 : ‖a i‖ ≤ 1 := hb i
  calc ‖a i‖ * (1 / ((i : ℝ) + 1) ^ z.re) ≤ 1 * (1 / ((i : ℝ) + 1) ^ z.re) := by
        refine mul_le_mul_of_nonneg_right hle1 ?_
        positivity
    _ = 1 / ((i : ℝ) + 1) ^ z.re := by ring
    _ ≤ 1 / ((i : ℝ) + 1) ^ c := by
        exact one_div_le_one_div_of_le hcpos hmono

/-- **Uniform approximation of a bounded Dirichlet series by its partial sums** on a closed
half-plane to the right of `1`. -/
theorem boundedDirichlet_uniform_approx {a : ℕ → ℂ} {D : ℂ → ℂ} (hb : ∀ i, ‖a i‖ ≤ 1)
    (hsum : ∀ z : ℂ, 1 < z.re →
      HasSum (fun i : ℕ => a i * Complex.exp (-((Real.log ((i : ℝ) + 1) : ℝ) : ℂ) * z)) (D z))
    {c : ℝ} (hc : 1 < c) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n₀ : ℕ, N ≤ n₀ → ∀ z : ℂ, c ≤ z.re →
      ‖D z - ∑ i ∈ Finset.range n₀,
        a i * Complex.exp (-((Real.log ((i : ℝ) + 1) : ℝ) : ℂ) * z)‖ ≤ ε := by
  classical
  set g : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 1) ^ c with hgdef
  have hg : Summable g := summable_zeta_compare hc
  have htail : Filter.Tendsto (fun n => ∑' i, g (i + n)) Filter.atTop (nhds 0) :=
    tendsto_sum_nat_add g
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (htail.eventually (ge_mem_nhds (by simpa using hε)))
  refine ⟨N, fun n₀ hn₀ z hz => ?_⟩
  have hz1 : 1 < z.re := lt_of_lt_of_le hc hz
  set f : ℕ → ℂ :=
    fun i => a i * Complex.exp (-((Real.log ((i : ℝ) + 1) : ℝ) : ℂ) * z) with hfdef
  have hbound : ∀ i : ℕ, ‖f i‖ ≤ g i := fun i => norm_boundedDirichlet_term_le hb i hz
  have hfs : Summable f := (hsum z hz1).summable
  have hDz : D z = ∑' i : ℕ, f i := (hsum z hz1).tsum_eq.symm
  have hsplit : ∑ i ∈ Finset.range n₀, f i + ∑' i, f (i + n₀) = ∑' i, f i :=
    hfs.sum_add_tsum_nat_add n₀
  rw [hDz, ← hsplit]
  have hcancel : ∑ i ∈ Finset.range n₀, f i + ∑' i, f (i + n₀) - ∑ i ∈ Finset.range n₀, f i
      = ∑' i, f (i + n₀) := by ring
  rw [hcancel]
  have hshift : Summable (fun i => f (i + n₀)) := (summable_nat_add_iff n₀).mpr hfs
  have hgshift : Summable (fun i => g (i + n₀)) := (summable_nat_add_iff n₀).mpr hg
  calc ‖∑' i, f (i + n₀)‖ ≤ ∑' i, ‖f (i + n₀)‖ := norm_tsum_le_tsum_norm (by simpa using hshift.norm)
    _ ≤ ∑' i, g (i + n₀) := Summable.tsum_le_tsum (fun i => hbound _) hshift.norm hgshift
    _ ≤ ε := hN n₀ hn₀

/-- The strip form of the approximation. -/
theorem boundedDirichlet_conv {a : ℕ → ℂ} {D : ℂ → ℂ} (hb : ∀ i, ‖a i‖ ≤ 1)
    (hsum : ∀ z : ℂ, 1 < z.re →
      HasSum (fun i : ℕ => a i * Complex.exp (-((Real.log ((i : ℝ) + 1) : ℝ) : ℂ) * z)) (D z))
    {σ R : ℝ} (hRσ : R ≤ σ - 1) :
    ∀ r' : ℝ, r' < R → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ z ∈ closedStrip σ r',
      ‖D z - ∑ i ∈ Finset.range n₀,
        a i * Complex.exp (-((Real.log ((i : ℝ) + 1) : ℝ) : ℂ) * z)‖ ≤ ε := by
  intro r' hr' ε hε
  have hc : 1 < σ - r' := by linarith
  obtain ⟨N, hN⟩ := boundedDirichlet_uniform_approx hb hsum hc hε
  refine ⟨N, fun z hz => hN N le_rfl z ?_⟩
  have habs : |z.re - σ| ≤ r' := hz
  have := (abs_le.mp habs).1
  linarith

/-- The negated logarithms of an injective family of primes are `ℤ`-independent. -/
theorem linearIndependent_neg_log_primes {K : ℕ} (ps : Fin (K + 1) → Nat.Primes)
    (hps : Function.Injective ps) :
    LinearIndependent ℤ (fun i : Fin (K + 1) => -(Real.log (((ps i : ℕ)) : ℝ))) := by
  have hQ : LinearIndependent ℚ (fun i : Fin (K + 1) => Real.log (((ps i : ℕ)) : ℝ)) :=
    linearIndependent_log_primes.comp ps hps
  have hZ : LinearIndependent ℤ (fun i : Fin (K + 1) => Real.log (((ps i : ℕ)) : ℝ)) := by
    refine hQ.restrict_scalars ?_
    intro u v huv
    have h : ((u : ℚ)) = ((v : ℚ)) := by simpa [zsmul_eq_mul] using huv
    exact_mod_cast h
  have hfun : ((fun _ : Fin (K + 1) => (-1 : ℤˣ)) •
        (fun i : Fin (K + 1) => Real.log (((ps i : ℕ)) : ℝ)))
      = fun i : Fin (K + 1) => -(Real.log (((ps i : ℕ)) : ℝ)) := by
    funext i
    simp [Units.smul_def]
  have h := hZ.units_smul (fun _ : Fin (K + 1) => (-1 : ℤˣ))
  rw [hfun] at h
  exact h

/-- **A bounded Dirichlet series with infinitely many nonvanishing prime coefficients satisfies no
Gamma-field relation.**  The coefficients of the relation are arbitrary nonzero elements of the
differential field generated by `Γ` over `ℂ(s)`. -/
theorem no_gammaField_field_relation_of_boundedDirichlet {σ : ℝ} (hσ : 1 < σ)
    (a : ℕ → ℂ) (D : ℂ → ℂ) (hb : ∀ i, ‖a i‖ ≤ 1)
    (hsum : ∀ z : ℂ, 1 < z.re →
      HasSum (fun i : ℕ => a i * Complex.exp (-((Real.log ((i : ℝ) + 1) : ℝ) : ℂ) * z)) (D z))
    (hD : DifferentiableOn ℂ D (verticalStrip σ ((σ - 1) / 2)))
    (hprimes : ∀ K : ℕ, ∃ ps : Fin (K + 1) → Nat.Primes, Function.Injective ps ∧
      ∀ i, a ((ps i : ℕ) - 1) ≠ 0)
    {n N : ℕ} (hN : 0 < N) (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter D)
    (x : Fin N → upperEndMeroField)
    (hxmem : ∀ α, x α ∈ differentialAdjoin (RatFunc ℂ)
      ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : ∀ α, x α ≠ 0) :
    ∑ α : Fin N, x α * ∏ i : Fin (n + 1),
        (differentialJet (i : ℕ)
          (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ)) ^ (e α i)
      ≠ 0 := by
  classical
  set lam : ℕ → ℝ := fun i => Real.log ((i : ℝ) + 1) with hlam
  have hR : (0 : ℝ) < (σ - 1) / 2 := by linarith
  have hRσ : (σ - 1) / 2 ≤ σ - 1 := by linarith
  have hconv := boundedDirichlet_conv hb hsum (σ := σ) (R := (σ - 1) / 2) hRσ
  have hap : IsStripAlmostPeriodic D σ ((σ - 1) / 2) :=
    isStripAlmostPeriodic_dirichlet a lam D hconv
  set f : ℝ →ᵇ ℂ := verticalRestriction D hR hD hap with hfdef
  have hf : ∀ y : ℝ, f y = D ((σ : ℂ) + (y : ℂ) * Complex.I) :=
    verticalRestriction_apply D hR hD hap
  -- the independent frequency families
  have hrank : ∀ K : ℕ, ∃ idx : Fin (K + 1) → ℕ, (∀ i, a (idx i) ≠ 0) ∧
      (∀ i : Fin (K + 1), ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, idx i < n₀ ∧ ∀ t : ℝ,
        ‖D ((σ : ℂ) + (t : ℂ) * Complex.I)
          - ∑ i' ∈ Finset.range n₀,
            a i' * Complex.exp (-(lam i' : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ ε) ∧
      LinearIndependent ℤ (fun i : Fin (K + 1) => -(lam (idx i))) := by
    intro K
    obtain ⟨ps, hps, hne⟩ := hprimes K
    refine ⟨fun i => (ps i : ℕ) - 1, hne, ?_, ?_⟩
    · intro i ε hε
      obtain ⟨M, hM⟩ := boundedDirichlet_uniform_approx hb hsum hσ hε
      refine ⟨max M ((ps i : ℕ) - 1 + 1),
        lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _), fun t => ?_⟩
      exact hM _ (le_max_left _ _) _ (by simp)
    · have hcast : ∀ i : Fin (K + 1), lam ((ps i : ℕ) - 1) = Real.log (((ps i : ℕ)) : ℝ) := by
        intro i
        have hp1 : 1 ≤ (ps i : ℕ) := ((ps i).2).one_lt.le
        rw [hlam]
        simp only
        rw [Nat.cast_sub hp1]
        push_cast
        ring_nf
      have hfun : (fun i : Fin (K + 1) => -(lam ((ps i : ℕ) - 1)))
          = fun i : Fin (K + 1) => -(Real.log (((ps i : ℕ)) : ℝ)) := by
        funext i
        rw [hcast i]
      rw [hfun]
      exact linearIndependent_neg_log_primes ps hps
  exact dirichlet_no_gammaField_field_relation (by linarith) hR a lam D
    zetaFrequency_injective hD hconv hf hrank hN e he Ψ hΨ x hxmem hx0

end

end GaloisForLFunctions.HTGeometry

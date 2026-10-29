import GaloisForLFunctions.HeckeLFunctions.HeckeLSeriesHaveEulerProducts
import GaloisForLFunctions.HeckeLFunctions.TheTrivialCharacterHasAPositiveResidue

/-!
# Positive occupation expansions of quadratic Hecke products

For a quadratic ray class character, the product of its Euler factor with
the trivial factor is two ordinary geometric factors at a positive prime,
one doubled-frequency geometric factor at a negative prime, and one at a
prime dividing the modulus. Finitely supported occupations therefore give
an actual general Dirichlet series with coefficient one and nonnegative
frequencies. Prime-norm summability justifies the product and every reindexing.

A prime outside the modulus exists already from the positive trivial residue:
otherwise the trivial Euler product would be identically one. Hence the
particle type is nonempty, as required for the Landau nonvanishing argument.
-/

noncomputable section
open NumberField IsDedekindDomain Filter Topology
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- Quadratic Hecke values and the trivial value have exactly three possible joint values. -/
theorem quadratic_heckeValue_cases {ψ : HeckeCharacter 𝔪} (hψ : ψ ^ 2 = 1)
    (I : Ideal (𝓞 K)) :
    (heckeValue 𝔪 1 I = 0 ∧ heckeValue 𝔪 ψ I = 0) ∨
    (heckeValue 𝔪 1 I = 1 ∧ heckeValue 𝔪 ψ I = 1) ∨
    (heckeValue 𝔪 1 I = 1 ∧ heckeValue 𝔪 ψ I = -1) := by
  by_cases hi : ∃ hI : I ≠ ⊥, idealUnit hI ∈ idealGroup 𝔪
  · obtain ⟨hI, hm⟩ := hi
    rw [heckeValue_of_mem 𝔪 1 hI hm, heckeValue_of_mem 𝔪 ψ hI hm]
    simp only [MonoidHom.one_apply, Units.val_one, one_ne_zero, false_and, false_or,
      true_and]
    have hs : (ψ (rayClass 𝔪 ⟨idealUnit hI, hm⟩) : ℂ) ^ 2 = 1 := by
      simpa only [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, MonoidHom.one_apply,
        Units.val_one] using
        congrArg (fun η : HeckeCharacter 𝔪 => (η (rayClass 𝔪 ⟨idealUnit hI, hm⟩) : ℂ)) hψ
    have hp : ((ψ (rayClass 𝔪 ⟨idealUnit hI, hm⟩) : ℂ) - 1) *
        ((ψ (rayClass 𝔪 ⟨idealUnit hI, hm⟩) : ℂ) + 1) = 0 := by
      calc
        _ = (ψ (rayClass 𝔪 ⟨idealUnit hI, hm⟩) : ℂ) ^ 2 - 1 := by ring
        _ = 0 := by rw [hs, sub_self]
    exact (mul_eq_zero.mp hp).imp sub_eq_zero.mp eq_neg_of_add_eq_zero_left
  · exact Or.inl ⟨heckeValue_of_not_mem 𝔪 1 hi, heckeValue_of_not_mem 𝔪 ψ hi⟩

/-- A prime outside the modulus exists: otherwise the trivial Euler product has zero residue. -/
theorem exists_prime_heckeValue_one_ne_zero :
    ∃ v : HeightOneSpectrum (𝓞 K), heckeValue 𝔪 1 v.asIdeal ≠ 0 := by
  by_contra hn
  push Not at hn
  have heq (σ : ℝ) (hσ : 1 < σ) : heckeL 𝔪 1 σ = 1 := by
    rw [← heckeL_eulerProduct_tprod 𝔪 1 (by simpa using hσ)]
    simp only [hn, zero_mul, sub_zero, inv_one, tprod_one]
  have hc : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one] using
      (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * heckeL 𝔪 1 σ)
      (𝓝[>] 1) (𝓝 (0 : ℂ)) := by
    have ht := hc.sub_const 1
    simp only [sub_self] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [heq σ hσ, mul_one]
  have h := tendsto_nhds_unique (tendsto_sub_one_mul_heckeL_one (𝔪 := 𝔪)) hz
  exact (Complex.ofReal_ne_zero.mpr (heckeDensity_pos 𝔪).ne') h

/-- One doubled-frequency particle for a negative prime; two ordinary particles for a positive prime. -/
def heckeQuadraticParticle (ψ : HeckeCharacter 𝔪) :=
  {j : HeightOneSpectrum (𝓞 K) × Bool //
    heckeValue 𝔪 ψ j.1.asIdeal = 1 ∨
      (heckeValue 𝔪 ψ j.1.asIdeal = -1 ∧ j.2 = false)}

theorem nonempty_heckeQuadraticParticle {ψ : HeckeCharacter 𝔪} (hψ : ψ ^ 2 = 1) :
    Nonempty (heckeQuadraticParticle 𝔪 ψ) := by
  obtain ⟨v, hv⟩ := exists_prime_heckeValue_one_ne_zero 𝔪
  rcases quadratic_heckeValue_cases 𝔪 hψ v.asIdeal with hz | hp | hm
  · exact False.elim (hv hz.1)
  · exact ⟨⟨(v, false), Or.inl hp.2⟩⟩
  · exact ⟨⟨(v, false), Or.inr ⟨hm.2, rfl⟩⟩⟩

/-- The elementary positive Euler factor decomposition, including the excluded primes. -/
theorem quadratic_heckeEulerFactor (ψ : HeckeCharacter 𝔪) (hψ : ψ ^ 2 = 1)
    (v : HeightOneSpectrum (𝓞 K)) (x : ℂ) :
    (1 - heckeValue 𝔪 1 v.asIdeal * x)⁻¹ *
        (1 - heckeValue 𝔪 ψ v.asIdeal * x)⁻¹ =
      if heckeValue 𝔪 ψ v.asIdeal = 1 then (1 - x)⁻¹ * (1 - x)⁻¹
      else if heckeValue 𝔪 ψ v.asIdeal = -1 then (1 - x ^ 2)⁻¹ else 1 := by
  rcases quadratic_heckeValue_cases 𝔪 hψ v.asIdeal with hz | hp | hm
  · norm_num [hz.1, hz.2]
  · simp only [hp.1, hp.2, one_mul, if_true]
  · rw [hm.1, hm.2]
    norm_num only [one_mul, neg_one_mul, sub_neg_eq_add]
    rw [← mul_inv]
    congr 1
    ring

/-- The positive frequency multiplicity of a quadratic Euler particle. -/
def heckeQuadraticParticleDegree (ψ : HeckeCharacter 𝔪) (j : heckeQuadraticParticle 𝔪 ψ) : ℕ :=
  if heckeValue 𝔪 ψ j.1.1.asIdeal = -1 then 2 else 1

/-- Each particle contributes one contracting geometric nome on the convergence half-plane. -/
def heckeQuadraticParticleNome (ψ : HeckeCharacter 𝔪) (s : ℂ)
    (j : heckeQuadraticParticle 𝔪 ψ) : ℂ :=
  ((Ideal.absNorm j.1.1.asIdeal : ℂ) ^ (-s)) ^ heckeQuadraticParticleDegree 𝔪 ψ j

private theorem norm_primeNorm_cpow_lt_one {s : ℂ} (hs : 1 < s.re)
    (v : HeightOneSpectrum (𝓞 K)) : ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 := by
  have hv := ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
  have hv0 : 0 < Ideal.absNorm v.asIdeal := lt_of_lt_of_le (by norm_num) hv
  rw [Complex.norm_natCast_cpow_of_pos hv0, Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (show 1 < Ideal.absNorm v.asIdeal by omega))
    (neg_neg_of_pos (zero_lt_one.trans hs))

theorem norm_heckeQuadraticParticleNome_le (ψ : HeckeCharacter 𝔪) {s : ℂ}
    (hs : 1 < s.re) (j : heckeQuadraticParticle 𝔪 ψ) :
    ‖heckeQuadraticParticleNome 𝔪 ψ s j‖ ≤ ‖(Ideal.absNorm j.1.1.asIdeal : ℂ) ^ (-s)‖ := by
  rw [heckeQuadraticParticleNome, norm_pow, heckeQuadraticParticleDegree]
  split_ifs
  · rw [pow_two]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (norm_primeNorm_cpow_lt_one hs j.1.1).le (norm_nonneg _)
  · rw [pow_one]

theorem norm_heckeQuadraticParticleNome_lt_one (ψ : HeckeCharacter 𝔪) {s : ℂ}
    (hs : 1 < s.re) (j : heckeQuadraticParticle 𝔪 ψ) :
    ‖heckeQuadraticParticleNome 𝔪 ψ s j‖ < 1 :=
  (norm_heckeQuadraticParticleNome_le 𝔪 ψ hs j).trans_lt (norm_primeNorm_cpow_lt_one hs j.1.1)

theorem summable_norm_heckeQuadraticParticleNome (ψ : HeckeCharacter 𝔪) {s : ℂ}
    (hs : 1 < s.re) : Summable (fun j => ‖heckeQuadraticParticleNome 𝔪 ψ s j‖) := by
  have hp := numberField_summable_finitePlace_norm_cpow (K := K) hs
  have hd : Summable (fun j : HeightOneSpectrum (𝓞 K) × Bool =>
      ‖(Ideal.absNorm j.1.asIdeal : ℂ) ^ (-s)‖) := by
    apply (summable_prod_of_nonneg (fun j => norm_nonneg _)).mpr
    refine ⟨fun v => (hasSum_fintype (fun _ : Bool =>
      ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖)).summable, ?_⟩
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      hp.mul_left (Fintype.card Bool : ℝ)
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (norm_heckeQuadraticParticleNome_le 𝔪 ψ hs) (hd.subtype _)

/-- The logarithmic frequency of a positive quadratic Euler particle. -/
def heckeQuadraticParticleFrequency (ψ : HeckeCharacter 𝔪)
    (j : heckeQuadraticParticle 𝔪 ψ) : ℝ :=
  heckeQuadraticParticleDegree 𝔪 ψ j * Real.log (Ideal.absNorm j.1.1.asIdeal)

theorem heckeQuadraticParticleFrequency_nonneg (ψ : HeckeCharacter 𝔪)
    (j : heckeQuadraticParticle 𝔪 ψ) : 0 ≤ heckeQuadraticParticleFrequency 𝔪 ψ j := by
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Real.log_nonneg
  exact_mod_cast (show 1 ≤ Ideal.absNorm j.1.1.asIdeal from
    (by norm_num : 1 ≤ 2).trans (ArtinMertens.two_le_absNorm_of_isPrime j.1.1.isPrime j.1.1.ne_bot))

/-- Extend the particle nome by zero to the two copies of every prime ideal. -/
def heckeQuadraticAllNome (ψ : HeckeCharacter 𝔪) (s : ℂ)
    (j : HeightOneSpectrum (𝓞 K) × Bool) : ℂ :=
  if heckeValue 𝔪 ψ j.1.asIdeal = 1 ∨
      (heckeValue 𝔪 ψ j.1.asIdeal = -1 ∧ j.2 = false) then
    ((Ideal.absNorm j.1.asIdeal : ℂ) ^ (-s)) ^
      (if heckeValue 𝔪 ψ j.1.asIdeal = -1 then 2 else 1 : ℕ)
  else 0

theorem heckeQuadraticAllNome_coe (ψ : HeckeCharacter 𝔪) (s : ℂ)
    (j : heckeQuadraticParticle 𝔪 ψ) :
    heckeQuadraticAllNome 𝔪 ψ s j.1 = heckeQuadraticParticleNome 𝔪 ψ s j := by
  rw [heckeQuadraticAllNome, if_pos j.2]
  rfl

/-- The two particle slots reproduce the actual two Hecke Euler factors at each prime. -/
theorem prod_heckeQuadraticAllNome (ψ : HeckeCharacter 𝔪) (hψ : ψ ^ 2 = 1)
    (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) :
    (∏ b : Bool, (1 - heckeQuadraticAllNome 𝔪 ψ s (v, b))⁻¹) =
      (1 - heckePrimeTerm 𝔪 1 s v)⁻¹ * (1 - heckePrimeTerm 𝔪 ψ s v)⁻¹ := by
  change _ = (1 - heckeValue 𝔪 1 v.asIdeal * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ *
    (1 - heckeValue 𝔪 ψ v.asIdeal * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹
  rw [quadratic_heckeEulerFactor 𝔪 ψ hψ]
  by_cases hp : heckeValue 𝔪 ψ v.asIdeal = 1
  · norm_num [heckeQuadraticAllNome, hp]
    rw [pow_two, mul_inv]
  · by_cases hm : heckeValue 𝔪 ψ v.asIdeal = -1
    · norm_num [heckeQuadraticAllNome, hp, hm]
    · simp [heckeQuadraticAllNome, hp, hm]

/-- The product of a quadratic Hecke series and the trivial series has a positive occupation expansion. -/
theorem heckeL_mul_eq_quadraticOccupation (ψ : HeckeCharacter 𝔪) (hψ : ψ ^ 2 = 1)
    {s : ℂ} (hs : 1 < s.re) :
    heckeL 𝔪 1 s * heckeL 𝔪 ψ s =
      ∑' ν : heckeQuadraticParticle 𝔪 ψ →₀ ℕ,
        HTGeometry.nomeMonomial (heckeQuadraticParticleNome 𝔪 ψ s) ν := by
  have hocc := HTGeometry.hasProd_inv_one_sub_nome (heckeQuadraticParticleNome 𝔪 ψ s)
    (norm_heckeQuadraticParticleNome_lt_one 𝔪 ψ hs)
    (summable_norm_heckeQuadraticParticleNome 𝔪 ψ hs)
  have hsupport : Function.mulSupport (fun j => (1 - heckeQuadraticAllNome 𝔪 ψ s j)⁻¹) ⊆
      {j : HeightOneSpectrum (𝓞 K) × Bool |
        heckeValue 𝔪 ψ j.1.asIdeal = 1 ∨
          (heckeValue 𝔪 ψ j.1.asIdeal = -1 ∧ j.2 = false)} := by
    intro j hj
    by_contra hn
    change ¬(heckeValue 𝔪 ψ j.1.asIdeal = 1 ∨
      (heckeValue 𝔪 ψ j.1.asIdeal = -1 ∧ j.2 = false)) at hn
    exact hj (by simp only [heckeQuadraticAllNome, if_neg hn, sub_zero, inv_one])
  have hall := (hasProd_subtype_iff_of_mulSupport_subset hsupport).mp
    (show HasProd (fun j : heckeQuadraticParticle 𝔪 ψ =>
      (1 - heckeQuadraticAllNome 𝔪 ψ s j.1)⁻¹) _ from by
        simpa only [heckeQuadraticAllNome_coe] using hocc)
  have hprime := hall.prod_fiberwise (fun v =>
    (prod_heckeQuadraticAllNome 𝔪 ψ hψ s v) ▸ hasProd_fintype
      (fun b : Bool => (1 - heckeQuadraticAllNome 𝔪 ψ s (v, b))⁻¹))
  exact ((heckeL_eulerProduct_hasProd 𝔪 1 hs).mul
    (heckeL_eulerProduct_hasProd 𝔪 ψ hs)).unique hprime

/-- The particle nome is the exponential of its positive logarithmic frequency. -/
theorem heckeQuadraticParticleNome_eq_exp (ψ : HeckeCharacter 𝔪) (s : ℂ)
    (j : heckeQuadraticParticle 𝔪 ψ) :
    heckeQuadraticParticleNome 𝔪 ψ s j =
      Complex.exp (-(s * (heckeQuadraticParticleFrequency 𝔪 ψ j : ℂ))) := by
  have hn : (Ideal.absNorm j.1.1.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr j.1.1.ne_bot)
  rw [heckeQuadraticParticleNome, Complex.cpow_def_of_ne_zero hn,
    ← Complex.exp_nat_mul, heckeQuadraticParticleFrequency,
    Complex.ofReal_mul, Complex.ofReal_natCast, Complex.natCast_log]
  congr 1
  ring

/-- The additive frequency of a finite occupation of positive Euler particles. -/
def heckeQuadraticOccupationEnergy (ψ : HeckeCharacter 𝔪)
    (ν : heckeQuadraticParticle 𝔪 ψ →₀ ℕ) : ℝ :=
  ∑ j ∈ ν.support, (ν j : ℝ) * heckeQuadraticParticleFrequency 𝔪 ψ j

theorem heckeQuadraticOccupationEnergy_nonneg (ψ : HeckeCharacter 𝔪)
    (ν : heckeQuadraticParticle 𝔪 ψ →₀ ℕ) : 0 ≤ heckeQuadraticOccupationEnergy 𝔪 ψ ν :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _)
    (heckeQuadraticParticleFrequency_nonneg 𝔪 ψ j))

/-- Every occupation has coefficient one in the generalized Dirichlet expansion. -/
theorem heckeQuadraticOccupation_eq_exp (ψ : HeckeCharacter 𝔪) (s : ℂ)
    (ν : heckeQuadraticParticle 𝔪 ψ →₀ ℕ) :
    HTGeometry.nomeMonomial (heckeQuadraticParticleNome 𝔪 ψ s) ν =
      Complex.exp (-(s * (heckeQuadraticOccupationEnergy 𝔪 ψ ν : ℂ))) := by
  rw [HTGeometry.nomeMonomial, Finsupp.prod]
  simp_rw [heckeQuadraticParticleNome_eq_exp, ← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  congr 1
  simp only [heckeQuadraticOccupationEnergy, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_natCast, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem summable_norm_heckeQuadraticOccupation (ψ : HeckeCharacter 𝔪) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (fun ν : heckeQuadraticParticle 𝔪 ψ →₀ ℕ =>
      ‖Complex.exp (-(s * (heckeQuadraticOccupationEnergy 𝔪 ψ ν : ℂ)))‖) := by
  have h := (HTGeometry.summable_nomeMonomial_pow_iff 0 (heckeQuadraticParticleNome 𝔪 ψ s)
    (norm_heckeQuadraticParticleNome_lt_one 𝔪 ψ hs)).mpr
      (by simpa only [zero_add, pow_one] using summable_norm_heckeQuadraticParticleNome 𝔪 ψ hs)
  simpa only [zero_add, pow_one, heckeQuadraticOccupation_eq_exp] using h

/-- Quadratic Hecke products agree with the explicitly positive general Dirichlet series. -/
theorem heckeL_mul_eq_positive_exponentialSeries (ψ : HeckeCharacter 𝔪) (hψ : ψ ^ 2 = 1)
    {s : ℂ} (hs : 1 < s.re) :
    heckeL 𝔪 1 s * heckeL 𝔪 ψ s =
      ∑' ν : heckeQuadraticParticle 𝔪 ψ →₀ ℕ,
        Complex.exp (-(s * (heckeQuadraticOccupationEnergy 𝔪 ψ ν : ℂ))) := by
  rw [heckeL_mul_eq_quadraticOccupation 𝔪 ψ hψ hs]
  exact tsum_congr (heckeQuadraticOccupation_eq_exp 𝔪 ψ s)

end GaloisForLFunctions.HeckeLFunctions

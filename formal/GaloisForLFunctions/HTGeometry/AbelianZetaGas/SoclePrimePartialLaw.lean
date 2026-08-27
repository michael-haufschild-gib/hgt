import GaloisForLFunctions.HTGeometry.QGammaFiveChart
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ModulusDivergence

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable section

/-- Primes at most the cutoff. -/
abbrev SoclePrimeIndex (P : ℕ) := {p : ℕ // p ∈ Nat.primesLE P}

/-- A cutoff prime, regarded as a prime subtype. -/
def soclePrimeIndexPrime {P : ℕ} (p : SoclePrimeIndex P) : Nat.Primes :=
  ⟨p, (Nat.mem_primesLE.mp p.2).2⟩

/-- Sum of the independent local q-Gamma atoms, with arbitrary primewise centering. -/
def soclePrimePartialSum (c : Nat.Primes → ℝ) {P : ℕ}
    (x : SoclePrimeIndex P → ℝ) : ℝ :=
  ∑ p : SoclePrimeIndex P, (x p - c (soclePrimeIndexPrime p))

theorem measurable_soclePrimePartialSum (c : Nat.Primes → ℝ) (P : ℕ) :
    Measurable (soclePrimePartialSum c : (SoclePrimeIndex P → ℝ) → ℝ) := by
  change Measurable (fun x : SoclePrimeIndex P → ℝ =>
    ∑ p : SoclePrimeIndex P, (x p - c (soclePrimeIndexPrime p)))
  fun_prop

/-- Embedding of the cutoff prime index into all primes. -/
def soclePrimeEmbedding (P : ℕ) : SoclePrimeIndex P ↪ Nat.Primes where
  toFun := soclePrimeIndexPrime
  inj' _ _ h := Subtype.ext (congrArg (fun r : Nat.Primes => (r : ℕ)) h)

/-- Finite set of prime subtypes lying below the cutoff. -/
def primeCutoff (P : ℕ) : Finset Nat.Primes :=
  Finset.univ.map (soclePrimeEmbedding P)

/-- Law of the centered socle sum over the primes `p ≤ P`. Each local law is the actual q-Gamma
atomic law of the prime nome `p^{-σ}`. -/
def soclePrimePartialMeasure {σ : ℝ} (hσ : 0 < σ) (c : Nat.Primes → ℝ) (P : ℕ) : Measure ℝ :=
  (Measure.pi fun p : SoclePrimeIndex P => qLaw (primeNome hσ (soclePrimeIndexPrime p))).map
    (soclePrimePartialSum c)

instance soclePrimePartialMeasure_isProbability {σ : ℝ} (hσ : 0 < σ)
    (c : Nat.Primes → ℝ) (P : ℕ) : IsProbabilityMeasure (soclePrimePartialMeasure hσ c P) :=
  Measure.isProbabilityMeasure_map (measurable_soclePrimePartialSum c P).aemeasurable

/-- Probability-measure packaging of the cutoff socle law. -/
def soclePrimePartialLaw {σ : ℝ} (hσ : 0 < σ) (c : Nat.Primes → ℝ) (P : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨soclePrimePartialMeasure hσ c P, inferInstance⟩

theorem qChar_eq_qGammaOn_one_add_I (q : RealEulerNome) (t : ℝ) :
    qChar q t = qGammaOn q (1 + (t : ℂ) * Complex.I) := by
  have h := (qGammaOn_eq_qGamma (qGammaShiftPoint q (Complex.I * (t : ℂ)) (by simp))).symm
  rw [qChar, qGammaResponse]
  convert h using 1
  simp [qGammaShiftPoint]
  ring_nf

/-- Exact characteristic function of the cutoff centered socle law. -/
theorem charFun_soclePrimePartialMeasure {σ : ℝ} (hσ : 0 < σ)
    (c : Nat.Primes → ℝ) (P : ℕ) (t : ℝ) :
    charFun (soclePrimePartialMeasure hσ c P) t =
      ∏ p ∈ primeCutoff P,
        (qGammaOn (primeNome hσ p) (1 + (t : ℂ) * Complex.I) *
          Complex.exp (-((t * c p : ℝ) : ℂ) * Complex.I)) := by
  classical
  rw [charFun_apply_real, soclePrimePartialMeasure,
    integral_map (measurable_soclePrimePartialSum c P).aemeasurable
      (Measurable.aestronglyMeasurable (by fun_prop))]
  have hprod : ∀ x : SoclePrimeIndex P → ℝ,
      Complex.exp ((t : ℂ) * (soclePrimePartialSum c x : ℂ) * Complex.I) =
        ∏ p : SoclePrimeIndex P,
          Complex.exp ((t : ℂ) * ((x p - c (soclePrimeIndexPrime p) : ℝ) : ℂ) * Complex.I) := by
    intro x
    rw [← Complex.exp_sum, soclePrimePartialSum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  simp only [hprod]
  rw [integral_fintype_prod_eq_prod
    (fun p x => Complex.exp
      ((t : ℂ) * ((x - c (soclePrimeIndexPrime p) : ℝ) : ℂ) * Complex.I))]
  have hlocal : ∀ p : SoclePrimeIndex P,
      (∫ x : ℝ,
          Complex.exp ((t : ℂ) * ((x - c (soclePrimeIndexPrime p) : ℝ) : ℂ) * Complex.I)
            ∂qLaw (primeNome hσ (soclePrimeIndexPrime p))) =
        qGammaOn (primeNome hσ (soclePrimeIndexPrime p))
            (1 + (t : ℂ) * Complex.I) *
          Complex.exp (-((t * c (soclePrimeIndexPrime p) : ℝ) : ℂ) * Complex.I) := by
    intro p
    have hsplit : ∀ x : ℝ,
        Complex.exp ((t : ℂ) * ((x - c (soclePrimeIndexPrime p) : ℝ) : ℂ) * Complex.I) =
          Complex.exp (-((t * c (soclePrimeIndexPrime p) : ℝ) : ℂ) * Complex.I) *
            Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) := by
      intro x
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [hsplit]
    rw [integral_const_mul, ← charFun_apply_real,
      charFun_qLaw, qChar_eq_qGammaOn_one_add_I]
    ring
  simp only [hlocal]
  simp only [primeCutoff, Finset.prod_map, Function.Embedding.coeFn_mk, soclePrimeEmbedding]

/-- Finite prime cutoffs are cofinal among finite sets of primes. -/
theorem tendsto_primeCutoff_atTop : Tendsto primeCutoff atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro s
  filter_upwards [eventually_ge_atTop (∑ p ∈ s, (p : ℕ))] with n hn
  intro p hp
  rw [primeCutoff, Finset.mem_map]
  have hle : (p : ℕ) ≤ ∑ q ∈ s, (q : ℕ) := by
    exact Finset.single_le_sum (s := s) (f := fun q : Nat.Primes => (q : ℕ))
      (fun q _ => Nat.zero_le (q : ℕ)) hp
  have hpn : (p : ℕ) ≤ n := le_trans hle hn
  let q : SoclePrimeIndex n := ⟨(p : ℕ), Nat.mem_primesLE.mpr ⟨hpn, p.2⟩⟩
  exact ⟨q, Finset.mem_univ q, Subtype.ext rfl⟩

/-- Throughout the condensed chamber, actual cutoff socle laws have no weak limit under any
primewise centering. This is the distributional form of Theorem 1.1. -/
theorem not_tendsto_soclePrimePartialLaw {σ : ℝ} (hσ : 0 < σ)
    (hhalf : 1 / 2 < σ) (hσ1 : σ ≤ 1) (c : Nat.Primes → ℝ)
    (μ : ProbabilityMeasure ℝ) :
    ¬ Tendsto (soclePrimePartialLaw hσ c) atTop (𝓝 μ) := by
  intro hμ
  have hchar := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hμ
  have hzero : ∀ t : ℝ, t ≠ 0 → charFun (μ : Measure ℝ) t = 0 := by
    intro t ht
    let u : Nat.Primes → ℂ := fun p =>
      Complex.exp (-((t * c p : ℝ) : ℂ) * Complex.I)
    have hu : ∀ p, ‖u p‖ = 1 := by
      intro p
      simp [u, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
    have hnorm0 := (tendsto_norm_prod_gauge_zero hσ hhalf hσ1 ht u hu).comp
      tendsto_primeCutoff_atTop
    change Tendsto (fun P : ℕ =>
      ‖∏ p ∈ primeCutoff P,
        (qGammaOn (primeNome hσ p) (1 + (t : ℂ) * Complex.I) * u p)‖)
      atTop (𝓝 0) at hnorm0
    have hnormμ : Tendsto
        (fun P : ℕ => ‖charFun (soclePrimePartialMeasure hσ c P) t‖)
        atTop (𝓝 ‖charFun (μ : Measure ℝ) t‖) := by
      have h := continuous_norm.continuousAt.tendsto.comp (hchar t)
      change Tendsto (fun P : ℕ => ‖charFun (soclePrimePartialMeasure hσ c P) t‖)
        atTop (𝓝 ‖charFun (μ : Measure ℝ) t‖) at h
      exact h
    have heq : ‖charFun (μ : Measure ℝ) t‖ = 0 := by
      apply tendsto_nhds_unique hnormμ
      simpa only [charFun_soclePrimePartialMeasure, u] using hnorm0
    exact norm_eq_zero.mp heq
  have hcont : ContinuousAt (charFun (μ : Measure ℝ)) 0 := continuous_charFun.continuousAt
  have hpunct : Tendsto (charFun (μ : Measure ℝ)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hzero t ht).symm
  have hzeroAt : charFun (μ : Measure ℝ) 0 = 0 :=
    tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds) hpunct
  have hone : charFun (μ : Measure ℝ) 0 = 1 := by simp
  exact one_ne_zero (hone.symm.trans hzeroAt)

end

end GaloisForLFunctions.HTGeometry

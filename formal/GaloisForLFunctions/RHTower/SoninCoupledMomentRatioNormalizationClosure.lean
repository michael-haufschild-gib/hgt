import GaloisForLFunctions.RHTower.SoninCoupledPrimeArchGramTransfer

/-!
# Coupled Sonin moment-ratio normalization closure

The coupled all-prime source column is nonzero at every positive aperture.  Consequently its
zeroth trace moment is always strictly positive, and normalized moment-ratio coupling needs only
the convergence of its nonconstant ratios.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

local instance coupledMatrixFirstCountable
    {m n R : Type*} [TopologicalSpace R] [FirstCountableTopology R]
    [Countable m] [Countable n] :
    FirstCountableTopology (Matrix m n R) :=
  inferInstanceAs (FirstCountableTopology (m → n → R))

/-- Unit projective scale, used to embed the unscaled coupled Gram family into its projective
completion. -/
def soninCoupledUnitPositiveScale : SoninPositiveScale :=
  ⟨1, zero_lt_one⟩

@[simp]
theorem soninAllPrimeCoupledProjectiveGramBlock_unitScale
    (N : ℕ) (a : SoninPositiveAperture) :
    soninAllPrimeCoupledProjectiveGramBlock N
        (soninCoupledUnitPositiveScale, a) =
      soninAllPrimeCoupledGramBlock N a := by
  ext i j
  rw [soninAllPrimeCoupledProjectiveGramBlock_apply,
    soninAllPrimeCoupledGramBlock_eq_traceMoment]
  simp [soninCoupledUnitPositiveScale]

/-- Convergence of the nonconstant coupled moment ratios.  Degree-zero positivity is omitted
because it follows from the prime-square residual channel at every positive aperture. -/
def SoninCoupledPrimeArchNonconstantMomentRatioCoupling
    (aperture : ℕ → ℕ → SoninPositiveAperture) : Prop :=
  ∀ N k, 0 < k → k < 2 * N - 1 →
    Tendsto (fun j : ℕ =>
        soninAllPrimeCoupledTraceMoment (aperture N j) k /
          soninAllPrimeCoupledTraceMoment (aperture N j) 0)
      atTop
      (nhds ((((normalizedPrimeArchMoment k : ℝ) : ℂ) /
        ((normalizedPrimeArchMoment 0 : ℝ) : ℂ))))

/-- Every entrywise finite Gram coupling recovers all `2N - 1` Hankel moments.  The reverse
direction was already supplied by the Hankel identity. -/
theorem soninCoupledPrimeArchFiniteMomentCoupling_of_gramCoupling
    {aperture : ℕ → ℕ → SoninPositiveAperture}
    (h : SoninCoupledPrimeArchFiniteGramCoupling aperture) :
    SoninCoupledPrimeArchFiniteMomentCoupling aperture := by
  intro N k hk
  have hN : 0 < N := by omega
  by_cases hsmall : k < N
  · let i : Fin N := ⟨0, hN⟩
    let l : Fin N := ⟨k, hsmall⟩
    have hentry :=
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (h N) i) l
    simpa only [soninAllPrimeCoupledGramBlock_eq_traceMoment,
      primeArchNormalizedHankelBlock, i, l, Fin.val_mk, zero_add] using hentry
  · have hi : k - (N - 1) < N := by omega
    have hl : N - 1 < N := by omega
    let i : Fin N := ⟨k - (N - 1), hi⟩
    let l : Fin N := ⟨N - 1, hl⟩
    have hsum : (i : ℕ) + (l : ℕ) = k := by
      dsimp only [i, l]
      omega
    have hentry :=
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (h N) i) l
    simpa only [soninAllPrimeCoupledGramBlock_eq_traceMoment,
      primeArchNormalizedHankelBlock, hsum] using hentry

/-- Finite coupled Hankel-block convergence and convergence of the encoded finite moment segment
are equivalent. -/
theorem soninCoupledPrimeArchFiniteGramCoupling_iff_momentCoupling
    {aperture : ℕ → ℕ → SoninPositiveAperture} :
    SoninCoupledPrimeArchFiniteGramCoupling aperture ↔
      SoninCoupledPrimeArchFiniteMomentCoupling aperture :=
  ⟨soninCoupledPrimeArchFiniteMomentCoupling_of_gramCoupling,
    soninCoupledPrimeArchFiniteGramCoupling_of_momentCoupling⟩

/-- Every projective finite Gram coupling recovers all projectively scaled moments in the encoded
`2N - 1` segment. -/
theorem soninCoupledPrimeArchProjectiveFiniteMomentCoupling_of_gramCoupling
    {data : ℕ → ℕ → SoninPositiveScale × SoninPositiveAperture}
    (h : SoninCoupledPrimeArchProjectiveFiniteGramCoupling data) :
    SoninCoupledPrimeArchProjectiveFiniteMomentCoupling data := by
  intro N k hk
  have hN : 0 < N := by omega
  by_cases hsmall : k < N
  · let i : Fin N := ⟨0, hN⟩
    let l : Fin N := ⟨k, hsmall⟩
    have hentry :=
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (h N) i) l
    simpa only [soninAllPrimeCoupledProjectiveGramBlock_apply,
      primeArchNormalizedHankelBlock, i, l, Fin.val_mk, zero_add] using hentry
  · have hi : k - (N - 1) < N := by omega
    have hl : N - 1 < N := by omega
    let i : Fin N := ⟨k - (N - 1), hi⟩
    let l : Fin N := ⟨N - 1, hl⟩
    have hsum : (i : ℕ) + (l : ℕ) = k := by
      dsimp only [i, l]
      omega
    have hentry :=
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (h N) i) l
    simpa only [soninAllPrimeCoupledProjectiveGramBlock_apply,
      primeArchNormalizedHankelBlock, hsum] using hentry

/-- Projective finite Gram convergence and projectively scaled finite-moment convergence are
equivalent. -/
theorem soninCoupledPrimeArchProjectiveFiniteGramCoupling_iff_momentCoupling
    {data : ℕ → ℕ → SoninPositiveScale × SoninPositiveAperture} :
    SoninCoupledPrimeArchProjectiveFiniteGramCoupling data ↔
      SoninCoupledPrimeArchProjectiveFiniteMomentCoupling data :=
  ⟨soninCoupledPrimeArchProjectiveFiniteMomentCoupling_of_gramCoupling,
    soninCoupledPrimeArchProjectiveFiniteGramCoupling_of_momentCoupling⟩

/-- An unscaled finite Gram coupling is a projective coupling at unit scale. -/
theorem soninCoupledPrimeArchProjectiveFiniteGramCoupling_of_finiteGramCoupling
    {aperture : ℕ → ℕ → SoninPositiveAperture}
    (h : SoninCoupledPrimeArchFiniteGramCoupling aperture) :
    SoninCoupledPrimeArchProjectiveFiniteGramCoupling
      (fun N j => (soninCoupledUnitPositiveScale, aperture N j)) := by
  intro N
  simpa only [soninAllPrimeCoupledProjectiveGramBlock_unitScale] using h N

/-- Unscaled finite Gram closure is contained in projective finite Gram closure. -/
theorem soninCoupledPrimeArchProjectiveFiniteGramClosure_of_finiteGramClosure
    (h : SoninCoupledPrimeArchFiniteGramClosure) :
    SoninCoupledPrimeArchProjectiveFiniteGramClosure := by
  intro N
  apply closure_mono ?_ (h N)
  rintro M ⟨a, rfl⟩
  exact ⟨(soninCoupledUnitPositiveScale, a),
    soninAllPrimeCoupledProjectiveGramBlock_unitScale N a⟩

/-- Static finite Gram closure supplies an explicit entrywise convergent aperture schedule at
every cutoff. -/
theorem exists_soninCoupledPrimeArchFiniteGramCoupling_of_closure
    (h : SoninCoupledPrimeArchFiniteGramClosure) :
    ∃ aperture : ℕ → ℕ → SoninPositiveAperture,
      SoninCoupledPrimeArchFiniteGramCoupling aperture := by
  have hseq : ∀ N : ℕ,
      ∃ x : ℕ → Matrix (Fin N) (Fin N) ℂ,
        (∀ j : ℕ, x j ∈ Set.range (soninAllPrimeCoupledGramBlock N)) ∧
          Tendsto x atTop (nhds (primeArchNormalizedHankelBlock N)) := by
    intro N
    exact mem_closure_iff_seq_limit.mp (h N)
  choose x hxmem hxtend using hseq
  have hex : ∀ N j : ℕ, ∃ a : SoninPositiveAperture,
      x N j = soninAllPrimeCoupledGramBlock N a := by
    intro N j
    obtain ⟨a, ha⟩ := hxmem N j
    exact ⟨a, ha.symm⟩
  choose aperture hx using hex
  refine ⟨aperture, ?_⟩
  intro N
  simpa only [← hx] using hxtend N

/-- Static finite Gram closure is equivalent to existence of explicit finite Gram coupling. -/
theorem soninCoupledPrimeArchFiniteGramClosure_iff_exists_coupling :
    SoninCoupledPrimeArchFiniteGramClosure ↔
      ∃ aperture : ℕ → ℕ → SoninPositiveAperture,
        SoninCoupledPrimeArchFiniteGramCoupling aperture := by
  constructor
  · exact exists_soninCoupledPrimeArchFiniteGramCoupling_of_closure
  · rintro ⟨aperture, h⟩
    exact soninCoupledPrimeArchFiniteGramClosure_of_coupling h

/-- Static finite Gram closure is also equivalent to existence of the shorter finite-moment
coupling interface. -/
theorem soninCoupledPrimeArchFiniteGramClosure_iff_exists_momentCoupling :
    SoninCoupledPrimeArchFiniteGramClosure ↔
      ∃ aperture : ℕ → ℕ → SoninPositiveAperture,
        SoninCoupledPrimeArchFiniteMomentCoupling aperture := by
  constructor
  · intro h
    obtain ⟨aperture, haperture⟩ :=
      exists_soninCoupledPrimeArchFiniteGramCoupling_of_closure h
    exact ⟨aperture,
      soninCoupledPrimeArchFiniteMomentCoupling_of_gramCoupling haperture⟩
  · rintro ⟨aperture, h⟩
    exact soninCoupledPrimeArchFiniteGramClosure_of_coupling
      (soninCoupledPrimeArchFiniteGramCoupling_of_momentCoupling h)

/-- Static projective finite Gram closure supplies an explicit projectively scaled convergent
schedule at every cutoff. -/
theorem exists_soninCoupledPrimeArchProjectiveFiniteGramCoupling_of_closure
    (h : SoninCoupledPrimeArchProjectiveFiniteGramClosure) :
    ∃ data : ℕ → ℕ → SoninPositiveScale × SoninPositiveAperture,
      SoninCoupledPrimeArchProjectiveFiniteGramCoupling data := by
  have hseq : ∀ N : ℕ,
      ∃ x : ℕ → Matrix (Fin N) (Fin N) ℂ,
        (∀ j : ℕ,
          x j ∈ Set.range (soninAllPrimeCoupledProjectiveGramBlock N)) ∧
          Tendsto x atTop (nhds (primeArchNormalizedHankelBlock N)) := by
    intro N
    exact mem_closure_iff_seq_limit.mp (h N)
  choose x hxmem hxtend using hseq
  have hex : ∀ N j : ℕ,
      ∃ d : SoninPositiveScale × SoninPositiveAperture,
        x N j = soninAllPrimeCoupledProjectiveGramBlock N d := by
    intro N j
    obtain ⟨d, hd⟩ := hxmem N j
    exact ⟨d, hd.symm⟩
  choose data hx using hex
  refine ⟨data, ?_⟩
  intro N
  simpa only [← hx] using hxtend N

/-- Static projective finite Gram closure is equivalent to existence of explicit projective Gram
coupling. -/
theorem soninCoupledPrimeArchProjectiveFiniteGramClosure_iff_exists_coupling :
    SoninCoupledPrimeArchProjectiveFiniteGramClosure ↔
      ∃ data : ℕ → ℕ → SoninPositiveScale × SoninPositiveAperture,
        SoninCoupledPrimeArchProjectiveFiniteGramCoupling data := by
  constructor
  · exact exists_soninCoupledPrimeArchProjectiveFiniteGramCoupling_of_closure
  · rintro ⟨data, h⟩
    exact soninCoupledPrimeArchProjectiveFiniteGramClosure_of_coupling h

/-- Static projective finite Gram closure is likewise equivalent to existence of projectively
scaled finite-moment coupling. -/
theorem soninCoupledPrimeArchProjectiveFiniteGramClosure_iff_exists_momentCoupling :
    SoninCoupledPrimeArchProjectiveFiniteGramClosure ↔
      ∃ data : ℕ → ℕ → SoninPositiveScale × SoninPositiveAperture,
        SoninCoupledPrimeArchProjectiveFiniteMomentCoupling data := by
  constructor
  · intro h
    obtain ⟨data, hdata⟩ :=
      exists_soninCoupledPrimeArchProjectiveFiniteGramCoupling_of_closure h
    exact ⟨data,
      soninCoupledPrimeArchProjectiveFiniteMomentCoupling_of_gramCoupling hdata⟩
  · rintro ⟨data, h⟩
    exact soninCoupledPrimeArchProjectiveFiniteGramClosure_of_coupling
      (soninCoupledPrimeArchProjectiveFiniteGramCoupling_of_momentCoupling h)

/-- A projectively scaled moment coupling determines the canonical source moment ratios: the
positive auxiliary scale cancels between every moment and the zeroth moment. -/
theorem soninCoupledPrimeArchMomentRatioCoupling_of_projectiveFiniteMomentCoupling
    {data : ℕ → ℕ → SoninPositiveScale × SoninPositiveAperture}
    (h : SoninCoupledPrimeArchProjectiveFiniteMomentCoupling data) :
    SoninCoupledPrimeArchMomentRatioCoupling (fun N j => (data N j).2) := by
  constructor
  · intro N j
    exact
      (soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_column_ne_zero
        (data N j).2).2
        (soninAllPrimeColumnCoordinateOperator_ne_zero
          (data N j).2.1 (data N j).2.2)
  · intro N k hk0 hk
    have hnum := h N k hk
    have hden := h N 0 (by omega)
    have htarget0 :
        ((normalizedPrimeArchMoment 0 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr normalizedPrimeArchMoment_zero_pos.ne'
    have hdiv := hnum.div hden htarget0
    convert hdiv using 1
    funext j
    have hscale :
        (((data N j).1.1 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (data N j).1.2)
    change
      soninAllPrimeCoupledTraceMoment (data N j).2 k /
          soninAllPrimeCoupledTraceMoment (data N j).2 0 =
        ((((data N j).1.1 : ℝ) : ℂ) *
            soninAllPrimeCoupledTraceMoment (data N j).2 k) /
          ((((data N j).1.1 : ℝ) : ℂ) *
            soninAllPrimeCoupledTraceMoment (data N j).2 0)
    field_simp [hscale]

/-- Projective finite Gram convergence therefore has a canonical, scale-free moment-ratio
consequence. -/
theorem soninCoupledPrimeArchMomentRatioCoupling_of_projectiveFiniteGramCoupling
    {data : ℕ → ℕ → SoninPositiveScale × SoninPositiveAperture}
    (h : SoninCoupledPrimeArchProjectiveFiniteGramCoupling data) :
    SoninCoupledPrimeArchMomentRatioCoupling (fun N j => (data N j).2) :=
  soninCoupledPrimeArchMomentRatioCoupling_of_projectiveFiniteMomentCoupling
    (soninCoupledPrimeArchProjectiveFiniteMomentCoupling_of_gramCoupling h)

/-- Projective finite Gram closure therefore supplies an explicit canonical, scale-free
moment-ratio coupling. -/
theorem exists_soninCoupledPrimeArchMomentRatioCoupling_of_projectiveFiniteGramClosure
    (h : SoninCoupledPrimeArchProjectiveFiniteGramClosure) :
    ∃ aperture : ℕ → ℕ → SoninPositiveAperture,
      SoninCoupledPrimeArchMomentRatioCoupling aperture := by
  obtain ⟨data, hdata⟩ :=
    exists_soninCoupledPrimeArchProjectiveFiniteGramCoupling_of_closure h
  exact ⟨fun N j => (data N j).2,
    soninCoupledPrimeArchMomentRatioCoupling_of_projectiveFiniteGramCoupling hdata⟩

/-- Projective finite Gram closure is exactly existence of a canonical scale-free moment-ratio
coupling; the auxiliary projective scale carries no additional source information. -/
theorem soninCoupledPrimeArchProjectiveFiniteGramClosure_iff_exists_momentRatioCoupling :
    SoninCoupledPrimeArchProjectiveFiniteGramClosure ↔
      ∃ aperture : ℕ → ℕ → SoninPositiveAperture,
        SoninCoupledPrimeArchMomentRatioCoupling aperture := by
  constructor
  · exact
      exists_soninCoupledPrimeArchMomentRatioCoupling_of_projectiveFiniteGramClosure
  · rintro ⟨aperture, haperture⟩
    obtain ⟨data, hdata⟩ :=
      exists_soninCoupledPrimeArchProjectiveFiniteMomentCoupling_of_momentRatioCoupling
        haperture
    exact soninCoupledPrimeArchProjectiveFiniteGramClosure_of_coupling
      (soninCoupledPrimeArchProjectiveFiniteGramCoupling_of_momentCoupling hdata)

/-- Unscaled finite Gram closure has a canonical normalized moment-ratio witness via its unit-scale
projective embedding. -/
theorem exists_soninCoupledPrimeArchMomentRatioCoupling_of_finiteGramClosure
    (h : SoninCoupledPrimeArchFiniteGramClosure) :
    ∃ aperture : ℕ → ℕ → SoninPositiveAperture,
      SoninCoupledPrimeArchMomentRatioCoupling aperture :=
  exists_soninCoupledPrimeArchMomentRatioCoupling_of_projectiveFiniteGramClosure
    (soninCoupledPrimeArchProjectiveFiniteGramClosure_of_finiteGramClosure h)

/-- The original moment-ratio coupling is exactly nonconstant ratio convergence: its
degree-zero positivity conjunct is automatic from source data. -/
theorem soninCoupledPrimeArchMomentRatioCoupling_iff_nonconstant
    {aperture : ℕ → ℕ → SoninPositiveAperture} :
    SoninCoupledPrimeArchMomentRatioCoupling aperture ↔
      SoninCoupledPrimeArchNonconstantMomentRatioCoupling aperture := by
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    intro N j
    exact
      (soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_column_ne_zero
        (aperture N j)).2
        (soninAllPrimeColumnCoordinateOperator_ne_zero
          (aperture N j).1 (aperture N j).2)

/-- Nonconstant coupled moment-ratio convergence alone implies RH; no normalization sign or
nondegeneracy hypothesis remains. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchNonconstantMomentRatioCoupling
    {aperture : ℕ → ℕ → SoninPositiveAperture}
    (h : SoninCoupledPrimeArchNonconstantMomentRatioCoupling aperture) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninCoupledPrimeArchMomentRatioCoupling
    (soninCoupledPrimeArchMomentRatioCoupling_iff_nonconstant.2 h)

end

end RHTower

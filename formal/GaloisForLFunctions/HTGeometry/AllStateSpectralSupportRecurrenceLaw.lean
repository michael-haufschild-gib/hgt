import GaloisForLFunctions.HTGeometry.QuditPathPhysicalRecurrenceCollisionLaw
import GaloisForLFunctions.HTGeometry.PhysicalFirstReturnHorizonInstabilityLaw

/-!
# The all-state spectral-support recurrence law

For a finite simple spectrum, a pure state's survival fidelity depends exactly on the energy levels
with nonzero spectral weight.  In a real-affine Hermitian family that escapes every real spectral
relation, almost every parameter is simultaneously Diophantine-extremal on every one of the
finitely many nontrivial support subsets.  Consequently one Hamiltonian has the sharp physical
first-return exponent for every normalized state, with the exponent determined by exact spectral
support size rather than ambient Hilbert-space dimension.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Canonical restriction to a finite spectral support -/

variable {D : ℕ}

/-- Increasing enumeration of a finite subset of `Fin D`. -/
def supportIndex (S : Finset (Fin D)) {m : ℕ} (hcard : S.card = m) : Fin m → Fin D :=
  fun i => (S.orderIsoOfFin hcard i).1

theorem supportIndex_injective (S : Finset (Fin D)) {m : ℕ} (hcard : S.card = m) :
    Function.Injective (supportIndex S hcard) := by
  intro i j hij
  apply (S.orderIsoOfFin hcard).injective
  exact Subtype.ext hij

theorem supportIndex_strictMono (S : Finset (Fin D)) {m : ℕ} (hcard : S.card = m) :
    StrictMono (supportIndex S hcard) := by
  intro i j hij
  exact (S.orderIsoOfFin hcard).strictMono hij

/-- Energy packet obtained by increasingly enumerating a selected support. -/
def supportEnergy (E : Fin D → ℝ) (S : Finset (Fin D)) {m : ℕ}
    (hcard : S.card = m) : Fin m → ℝ :=
  fun i => E (supportIndex S hcard i)

/-- Weight packet obtained by increasingly enumerating a selected support. -/
def supportWeight (p : Fin D → ℝ) (S : Finset (Fin D)) {m : ℕ}
    (hcard : S.card = m) : Fin m → ℝ :=
  fun i => p (supportIndex S hcard i)

/-- Exact nonzero support of a finite spectral-weight packet. -/
def spectralWeightSupport (p : Fin D → ℝ) : Finset (Fin D) :=
  Finset.univ.filter fun i => p i ≠ 0

@[simp] theorem mem_spectralWeightSupport_iff (p : Fin D → ℝ) (i : Fin D) :
    i ∈ spectralWeightSupport p ↔ p i ≠ 0 := by
  simp [spectralWeightSupport]

/-- Canonical cardinality identity used for a support with at least three points. -/
theorem support_card_eq_sub_three_add_three (S : Finset (Fin D)) (hS : 3 ≤ S.card) :
    S.card = (S.card - 3) + 3 := by
  omega

/-- Selected projective gap ratios of a support with at least three levels. -/
def supportGapRatio (E : Fin D → ℝ) (S : Finset (Fin D)) (hS : 3 ≤ S.card) :
    Fin ((S.card - 3) + 1) → ℝ :=
  anchoredGapRatioMap
    (supportEnergy E S (support_card_eq_sub_three_add_three S hS)) 0 1
    (fun k => k.succ.succ)

theorem sum_supportWeight_spectralWeightSupport (p : Fin D → ℝ) {m : ℕ}
    (hcard : (spectralWeightSupport p).card = m) :
    ∑ i, supportWeight p (spectralWeightSupport p) hcard i = ∑ j, p j := by
  let S := spectralWeightSupport p
  let equiv : Fin m ≃ S := (S.orderIsoOfFin hcard).toEquiv
  calc
    ∑ i, supportWeight p S hcard i = ∑ i, p (equiv i) := by
      rfl
    _ = ∑ x : S, p x := Equiv.sum_comp equiv (fun x : S => p x)
    _ = ∑ x ∈ S, p x := (Finset.sum_subtype S (fun _ => Iff.rfl) p).symm
    _ = ∑ j, p j := by
      apply Finset.sum_filter_of_ne
      intro j _ hj
      simpa [S, spectralWeightSupport] using hj

/-- Removing zero-weight levels leaves the complete spectral return amplitude unchanged. -/
theorem spectralReturnAmplitude_support (E p : Fin D → ℝ) {m : ℕ}
    (hcard : (spectralWeightSupport p).card = m) (t : ℝ) :
    spectralReturnAmplitude
        (supportEnergy E (spectralWeightSupport p) hcard)
        (supportWeight p (spectralWeightSupport p) hcard) t =
      spectralReturnAmplitude E p t := by
  let S := spectralWeightSupport p
  let equiv : Fin m ≃ S := (S.orderIsoOfFin hcard).toEquiv
  let f : Fin D → ℂ := fun j =>
    (p j : ℂ) * Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)
  calc
    spectralReturnAmplitude (supportEnergy E S hcard) (supportWeight p S hcard) t
        = ∑ i, f (equiv i) := by
          rfl
    _ = ∑ x : S, f x := Equiv.sum_comp equiv (fun x : S => f x)
    _ = ∑ x ∈ S, f x := (Finset.sum_subtype S (fun _ => Iff.rfl) f).symm
    _ = ∑ j, f j := by
      apply Finset.sum_filter_of_ne
      intro j _ hj
      by_contra hpj
      apply hj
      simp [f, hpj]
    _ = spectralReturnAmplitude E p t := rfl

/-- Exact support compression of fidelity deficit. -/
theorem spectralReturnDeficit_support (E p : Fin D → ℝ) {m : ℕ}
    (hcard : (spectralWeightSupport p).card = m) (t : ℝ) :
    spectralReturnDeficit
        (supportEnergy E (spectralWeightSupport p) hcard)
        (supportWeight p (spectralWeightSupport p) hcard) t =
      spectralReturnDeficit E p t := by
  rw [spectralReturnDeficit, spectralReturnDeficit,
    spectralReturnAmplitude_support E p hcard t]

/-- Exact support compression of every first-return time. -/
theorem fidelityReturnTime_support (E p : Fin D → ℝ) {m : ℕ}
    (hcard : (spectralWeightSupport p).card = m) (t₀ δ : ℝ) :
    fidelityReturnTime
        (supportEnergy E (spectralWeightSupport p) hcard)
        (supportWeight p (spectralWeightSupport p) hcard) t₀ δ =
      fidelityReturnTime E p t₀ δ := by
  rw [fidelityReturnTime, fidelityReturnTime, fidelityReturnSet, fidelityReturnSet]
  congr 1
  ext t
  simp only [Set.mem_setOf_eq]
  rw [spectralReturnDeficit_support E p hcard t]

theorem spectralWeightSupport_nonempty_of_sum_eq_one (p : Fin D → ℝ)
    (hp1 : ∑ j, p j = 1) : (spectralWeightSupport p).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hpzero : ∀ j, p j = 0 := by
    intro j
    by_contra hj
    have hmem : j ∈ spectralWeightSupport p := (mem_spectralWeightSupport_iff p j).2 hj
    rw [hne] at hmem
    simp at hmem
  have : ∑ j, p j = 0 := by simp [hpzero]
  linarith

theorem supportWeight_pos (p : Fin D → ℝ) (hpnn : ∀ j, 0 ≤ p j) {m : ℕ}
    (hcard : (spectralWeightSupport p).card = m) (i : Fin m) :
    0 < supportWeight p (spectralWeightSupport p) hcard i := by
  let S := spectralWeightSupport p
  have hmem : supportIndex S hcard i ∈ S := (S.orderIsoOfFin hcard i).2
  have hne : p (supportIndex S hcard i) ≠ 0 :=
    (mem_spectralWeightSupport_iff p _).1 hmem
  exact lt_of_le_of_ne (hpnn _) (Ne.symm hne)

theorem hasPositiveProjectiveReturn_fin_one (E : Fin 1 → ℝ) :
    HasPositiveProjectiveReturn E := by
  refine ⟨1, one_pos, ?_⟩
  exact fun j => Fin.elim0 j

theorem hasPositiveProjectiveReturn_fin_two (E : Fin 2 → ℝ) (hgap : E 0 < E 1) :
    HasPositiveProjectiveReturn E := by
  have hgap0 : 0 < E 1 - E 0 := sub_pos.mpr hgap
  refine ⟨2 * Real.pi / (E 1 - E 0), by positivity, ?_⟩
  intro j
  have hj : j = 0 := Fin.eq_zero j
  subst j
  refine ⟨1, ?_⟩
  simp only [Fin.succ_zero_eq_one, Int.cast_one, mul_one]
  exact div_mul_cancel₀ (2 * Real.pi) hgap0.ne'

/-- Exact first-return exponent of an arbitrary nonnegative probability packet, classified by the
cardinality of its nonzero support.  The Diophantine premise is imposed simultaneously on every
support of size at least three; the one- and two-level strata are exactly periodic. -/
theorem tendsto_log_fidelityReturnTime_supportCard (E p : Fin D → ℝ)
    (hp1 : ∑ j, p j = 1) (hpnn : ∀ j, 0 ≤ p j) (hE : StrictMono E)
    (hgood : ∀ (S : Finset (Fin D)) (hS : 3 ≤ S.card),
      ¬ KleinbockMargulis.VWA (supportGapRatio E S hS))
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto
      (fun δ : ℝ => Real.log (fidelityReturnTime E p t₀ δ) / Real.log (1 / δ))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((spectralWeightSupport p).card - 2 : ℕ) : ℝ) / 2)) := by
  let S := spectralWeightSupport p
  have hSne : S.Nonempty := spectralWeightSupport_nonempty_of_sum_eq_one p hp1
  have hSpos : 0 < S.card := Finset.card_pos.mpr hSne
  by_cases hsmall : S.card ≤ 2
  · have hcases : S.card = 1 ∨ S.card = 2 := by omega
    rcases hcases with hcard | hcard
    · let E' : Fin 1 → ℝ := supportEnergy E S hcard
      let p' : Fin 1 → ℝ := supportWeight p S hcard
      have hp1' : ∑ i, p' i = 1 := by
        calc
          ∑ i, p' i = ∑ j, p j := by
            simpa [S, p'] using sum_supportWeight_spectralWeightSupport p hcard
          _ = 1 := hp1
      have hppos' : ∀ i, 0 < p' i := by
        intro i
        simpa [S, p'] using supportWeight_pos p hpnn hcard i
      have hmain := tendsto_log_fidelityReturnTime_zero_of_hasPositiveProjectiveReturn
        E' p' hp1' hppos' (hasPositiveProjectiveReturn_fin_one E') ht₀
      have htrans : Tendsto
          (fun δ : ℝ => Real.log (fidelityReturnTime E p t₀ δ) / Real.log (1 / δ))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        refine hmain.congr' ?_
        filter_upwards with δ
        rw [fidelityReturnTime_support E p hcard t₀ δ]
      simpa [S, hcard] using htrans
    · let E' : Fin 2 → ℝ := supportEnergy E S hcard
      let p' : Fin 2 → ℝ := supportWeight p S hcard
      have hp1' : ∑ i, p' i = 1 := by
        calc
          ∑ i, p' i = ∑ j, p j := by
            simpa [S, p'] using sum_supportWeight_spectralWeightSupport p hcard
          _ = 1 := hp1
      have hppos' : ∀ i, 0 < p' i := by
        intro i
        simpa [S, p'] using supportWeight_pos p hpnn hcard i
      have hE' : StrictMono E' := hE.comp (supportIndex_strictMono S hcard)
      have hgap : E' 0 < E' 1 := hE' (by omega)
      have hmain := tendsto_log_fidelityReturnTime_zero_of_hasPositiveProjectiveReturn
        E' p' hp1' hppos' (hasPositiveProjectiveReturn_fin_two E' hgap) ht₀
      have htrans : Tendsto
          (fun δ : ℝ => Real.log (fidelityReturnTime E p t₀ δ) / Real.log (1 / δ))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        refine hmain.congr' ?_
        filter_upwards with δ
        rw [fidelityReturnTime_support E p hcard t₀ δ]
      simpa [S, hcard] using htrans
  · have hS : 3 ≤ S.card := by omega
    let e : ℕ := S.card - 3
    have hcard : S.card = e + 3 := by
      dsimp [e]
      omega
    let E' : Fin (e + 3) → ℝ := supportEnergy E S hcard
    let p' : Fin (e + 3) → ℝ := supportWeight p S hcard
    have hp1' : ∑ i, p' i = 1 := by
      calc
        ∑ i, p' i = ∑ j, p j := by
          simpa [S, p'] using sum_supportWeight_spectralWeightSupport p hcard
        _ = 1 := hp1
    have hppos' : ∀ i, 0 < p' i := by
      intro i
      simpa [S, p'] using supportWeight_pos p hpnn hcard i
    let c : ℝ := Finset.univ.inf' Finset.univ_nonempty p'
    have hcpos : 0 < c := by
      rw [show c = Finset.univ.inf' Finset.univ_nonempty p' from rfl,
        Finset.lt_inf'_iff]
      exact fun i _ => hppos' i
    have hcp : ∀ i, c ≤ p' i := fun i => Finset.inf'_le p' (Finset.mem_univ i)
    have hE' : StrictMono E' := hE.comp (supportIndex_strictMono S hcard)
    have hgap : 0 < E' 1 - E' 0 := sub_pos.mpr (hE' Fin.zero_lt_one)
    have hnv : ¬ KleinbockMargulis.VWA
        (anchoredGapRatioMap E' 0 1 (fun k => k.succ.succ)) := by
      simpa [supportGapRatio, E', e, hcard] using hgood S hS
    have hmain := tendsto_log_fidelityReturnTime E' p' hp1' hppos' hcpos hcp hgap hnv ht₀
    have htrans : Tendsto
        (fun δ : ℝ => Real.log (fidelityReturnTime E p t₀ δ) / Real.log (1 / δ))
        (𝓝[>] (0 : ℝ)) (𝓝 (((e + 1 : ℕ) : ℝ) / 2)) := by
      refine hmain.congr' ?_
      filter_upwards with δ
      rw [fidelityReturnTime_support E p hcard t₀ δ]
    have he : e + 1 = S.card - 2 := by
      dsimp [e]
      omega
    rw [he] at htrans
    simpa [S] using htrans

/-! ## One common extremal set for every support -/

variable {N : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}

/-- Almost every point of a simple spectral chart is simultaneously non-VWA on every selected
support of cardinality at least three.  Only a finite intersection is taken: `Finset (Fin D)` is a
finite type. -/
theorem ae_all_supportGapRatio_not_vwa [NeZero N]
    (hP : ∀ a, (P a).IsHermitian)
    (hEsc : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUsimple : U ⊆ simpleEnsembleLocus hP) :
    ∀ᵐ θ, θ ∈ U →
      ∀ (S : Finset (Fin D)) (hS : 3 ≤ S.card),
        ¬ KleinbockMargulis.VWA (supportGapRatio (sortedEnsembleSpectrum hP θ) S hS) := by
  suffices h : ∀ᵐ θ, ∀ S : Finset (Fin D), θ ∈ U →
      ∀ hS : 3 ≤ S.card,
        ¬ KleinbockMargulis.VWA (supportGapRatio (sortedEnsembleSpectrum hP θ) S hS) by
    filter_upwards [h] with θ hθ hθU
    exact fun S => hθ S hθU
  rw [Filter.eventually_all]
  intro S
  by_cases hS : 3 ≤ S.card
  · let hcard : S.card = (S.card - 3) + 3 := support_card_eq_sub_three_add_three S hS
    let idx : Fin ((S.card - 3) + 3) → Fin D := supportIndex S hcard
    have hidx : Function.Injective idx := supportIndex_injective S hcard
    have htail : Function.Injective (fun k : Fin ((S.card - 3) + 1) => idx k.succ.succ) :=
      hidx.comp ((Fin.succ_injective _).comp (Fin.succ_injective _))
    have hanchor : ∀ k : Fin ((S.card - 3) + 1), idx k.succ.succ ≠ idx 0 := by
      intro k hk
      have hfin := hidx hk
      exact Fin.succ_ne_zero k.succ hfin
    have hclock : ∀ k : Fin ((S.card - 3) + 1), idx k.succ.succ ≠ idx 1 := by
      intro k hk
      have hfin := hidx hk
      have h1 : (1 : Fin ((S.card - 3) + 3)) = Fin.succ (0 : Fin ((S.card - 3) + 2)) := rfl
      rw [h1] at hfin
      exact Fin.succ_ne_zero k (Fin.succ_injective _ hfin)
    have hac : idx 0 ≠ idx 1 := fun h => zero_ne_one (hidx h)
    have hnull := theoremA_sortedGapRatio (n := (S.card - 3) + 1) (by omega)
      hP hEsc htail hanchor hclock hac hU hUc hUne hUsimple
    have hae := ae_not_vwa_of_volume_eq_zero hnull
    filter_upwards [hae] with θ hθ hθU
    intro hS'
    have : hS' = hS := Subsingleton.elim _ _
    subst hS'
    have hratio : supportGapRatio (sortedEnsembleSpectrum hP θ) S hS =
        anchoredGapRatioMap (sortedEnsembleSpectrum hP θ)
          (idx 0) (idx 1) (fun k => idx k.succ.succ) := by
      funext k
      simp [supportGapRatio, supportEnergy, anchoredGapRatioMap, idx]
    rw [hratio]
    exact hθ hθU
  · filter_upwards with θ
    intro _ hS'
    exact (hS hS').elim

/-! ## Physical orbit and local-family capstones -/

/-- Spectral weights of a physical state, indexed in increasing energy order. -/
def sortedStateSpectralWeights (hP : ∀ a, (P a).IsHermitian)
    (θ : Fin N → ℝ) (Ω : Fin D → ℂ) : Fin D → ℝ :=
  let hH := isHermitian_spectralEnsembleMatrix hP θ
  fun i => spectralWeights
    (hermitianEigenBasis (spectralEnsembleMatrix P θ) hH) Ω
    (Tuple.sort hH.eigenvalues i)

/-- Real spectral escape gives one conull set of Hamiltonians on which the exact physical
first-return exponent is classified simultaneously for every normalized state by its exact
spectral support size. -/
theorem ae_tendsto_log_orbitFidelityReturnTime_supportCard_sortedSpectrum [NeZero N]
    (hP : ∀ a, (P a).IsHermitian)
    (hEsc : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUsimple : U ⊆ simpleEnsembleLocus hP) :
    ∀ᵐ θ, θ ∈ U →
      ∀ Ω : Fin D → ℂ, finiteComplexInner Ω Ω = 1 →
        ∀ {t₀ : ℝ}, 0 < t₀ →
          Tendsto
            (fun δ : ℝ => Real.log
                (orbitFidelityReturnTime (spectralEnsembleMatrix P θ) Ω t₀ δ) /
              Real.log (1 / δ))
            (𝓝[>] (0 : ℝ))
            (𝓝 ((((spectralWeightSupport (sortedStateSpectralWeights hP θ Ω)).card - 2 : ℕ) : ℝ)
              / 2)) := by
  have hall := ae_all_supportGapRatio_not_vwa hP hEsc hU hUc hUne hUsimple
  filter_upwards [hall] with θ hθ hθU
  intro Ω hΩ t₀ ht₀
  let hH := isHermitian_spectralEnsembleMatrix hP θ
  let ρ : Fin D ≃ Fin D := (Tuple.sort hH.eigenvalues).symm
  let E : Fin D → ℝ := hH.eigenvalues ∘ Tuple.sort hH.eigenvalues
  let p : Fin D → ℝ := fun i => spectralWeights
    (hermitianEigenBasis (spectralEnsembleMatrix P θ) hH) Ω (ρ.symm i)
  have hp1 : ∑ i, p i = 1 := by
    rw [show (∑ i, p i) = ∑ j, spectralWeights
        (hermitianEigenBasis (spectralEnsembleMatrix P θ) hH) Ω j from
      Equiv.sum_comp ρ.symm
        (spectralWeights (hermitianEigenBasis (spectralEnsembleMatrix P θ) hH) Ω)]
    exact sum_spectralWeights
      (isOrthoEigenBasis_hermitian (spectralEnsembleMatrix P θ) hH) hΩ
  have hpnn : ∀ i, 0 ≤ p i := by
    intro i
    exact spectralWeights_nonneg
      (hermitianEigenBasis (spectralEnsembleMatrix P θ) hH) Ω (ρ.symm i)
  have hraw : Function.Injective hH.eigenvalues := by
    simpa [hH, simpleEnsembleLocus] using hUsimple hθU
  have hEinj : Function.Injective E := by
    exact hraw.comp (Tuple.sort hH.eigenvalues).injective
  have hEmono : Monotone E := by
    exact monotone_sortedTuple hH.eigenvalues
  have hE : StrictMono E := hEmono.strictMono_of_injective hEinj
  have hEsorted : E = sortedEnsembleSpectrum hP θ := by
    funext i
    simp [E, sortedEnsembleSpectrum, sortedTuple]
  have hgood : ∀ (S : Finset (Fin D)) (hS : 3 ≤ S.card),
      ¬ KleinbockMargulis.VWA (supportGapRatio E S hS) := by
    intro S hS
    rw [hEsorted]
    exact hθ hθU S hS
  have hmain := tendsto_log_fidelityReturnTime_supportCard E p hp1 hpnn hE hgood ht₀
  have hphysical : Tendsto
      (fun δ : ℝ => Real.log
          (orbitFidelityReturnTime (spectralEnsembleMatrix P θ) Ω t₀ δ) /
        Real.log (1 / δ))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((spectralWeightSupport p).card - 2 : ℕ) : ℝ) / 2)) := by
    refine hmain.congr' ?_
    filter_upwards with δ
    rw [orbitFidelityReturnTime_eq ρ
      (isOrthoEigenBasis_hermitian (spectralEnsembleMatrix P θ) hH) Ω t₀ δ]
    rfl
  simpa [p, ρ, hH, sortedStateSpectralWeights] using hphysical

/-- Exact all-state support-size first-return law for the full onsite-plus-nearest-neighbour qudit
path coefficient family. -/
def QuditPathAllStateSupportRecurrenceLaw (n q : ℕ) : Prop :=
    ∃ e : ℕ, q ^ n = e + 3 ∧
    ∃ (Physical Observer : Type) (instP : Fintype Physical)
      (instPd : DecidableEq Physical)
      (T : RootedTensorTree Physical Observer) (eObs : Observer ≃ Fin n),
      letI := instP
      letI := instPd
      T.graph = SimpleGraph.comap eObs (SimpleGraph.pathGraph n) ∧
      ∃ (eSt : Physical ≃ Fin (e + 3))
        (_ : NeZero (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule))
        (P : Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) →
          Matrix (Fin (e + 3)) (Fin (e + 3)) ℂ)
        (hP : ∀ a, (P a).IsHermitian),
        (∀ a, P a = Matrix.reindex eSt eSt
          (realMatrixSubmoduleGenerator T.hermitianLocalHamiltonianSubmodule a)) ∧
        (∃ U : Set (Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) → ℝ),
          IsOpen U ∧ IsPreconnected U ∧ U.Nonempty ∧ U ⊆ simpleEnsembleLocus hP) ∧
        ∀ {U : Set (Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) → ℝ)},
          IsOpen U → IsPreconnected U → U.Nonempty →
          U ⊆ simpleEnsembleLocus hP →
          ∀ᵐ θ ∂volume, θ ∈ U →
            ∀ Ω : Fin (e + 3) → ℂ, finiteComplexInner Ω Ω = 1 →
              ∀ {t₀ : ℝ}, 0 < t₀ →
                Tendsto
                  (fun δ : ℝ => Real.log
                      (orbitFidelityReturnTime (spectralEnsembleMatrix P θ) Ω t₀ δ) /
                    Real.log (1 / δ))
                  (𝓝[>] (0 : ℝ))
                  (𝓝 ((((spectralWeightSupport
                    (sortedStateSpectralWeights hP θ Ω)).card - 2 : ℕ) : ℝ) / 2))

/-- Conventional-parameter local path theorem. -/
theorem quditPathAllStateSupportRecurrenceLaw_of_two_le
    (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    QuditPathAllStateSupportRecurrenceLaw n q := by
  obtain ⟨D, hD, hD4, Physical, Observer, instP, instPd, T, eObs, hgraph,
      eSt, hNeZero, P, hPHermitian, hprov, hfamily⟩ :=
    exists_quditPathChain_coordinateFamily n q hn hq
  obtain ⟨e, rfl⟩ : ∃ e, D = e + 3 := ⟨D - 3, by omega⟩
  letI := instP
  letI := instPd
  haveI := hNeZero
  refine ⟨e, hD, Physical, Observer, instP, instPd, T, eObs, hgraph,
    eSt, hNeZero, P, hPHermitian, hprov,
    exists_chart_of_spectrumEscapes (by omega) hPHermitian hfamily, ?_⟩
  intro U hUopen hUconn hUne hUsimple
  exact ae_tendsto_log_orbitFidelityReturnTime_supportCard_sortedSpectrum
    hPHermitian hfamily.toRealRelations hUopen hUconn hUne hUsimple

/-- **Unconditional local-many-body capstone.**  Site number and local dimension are shifted by
two, so every pair of natural-number inputs names a nontrivial static nearest-neighbour path.  One
conull set of Hamiltonians then obeys the exact support-size first-return law for every normalized
state simultaneously. -/
theorem universalQuditPathAllStateSupportRecurrenceLaw (n q : ℕ) :
    QuditPathAllStateSupportRecurrenceLaw (n + 2) (q + 2) :=
  quditPathAllStateSupportRecurrenceLaw_of_two_le
    (n + 2) (q + 2) (by omega) (by omega)

end

end GaloisForLFunctions.HTGeometry

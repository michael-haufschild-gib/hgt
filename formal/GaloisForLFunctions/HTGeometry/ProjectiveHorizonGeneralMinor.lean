import GaloisForLFunctions.HTGeometry.ProjectiveHorizonElementaryField

/-!
# Minors with arbitrary jet orders

The invariance of a jet determinant under an observer group uses only how the rows transform, so it
holds for any choice of jet orders along the columns, not just the initial segment.  This file
records the jet array with an arbitrary injective column labelling, its nondegeneracy, and its
invariance.

These are the normalised transverse jets of the moving-frame picture: with rows a covector span
together with one outside direction, and columns an initial block together with one further jet
order, the determinant is the transverse jet of that order with its span component removed.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- A square array of homogeneous jets with arbitrary row labels and arbitrary jet orders. -/
def jetArrayGen (t : Finset n) (ρ : ↥t → n) (ord : ↥t → ℕ) :
    Matrix ↥t ↥t (HomogeneousJetField n K) :=
  Matrix.of fun m c => freeCoordinate K (n × ℕ) (ρ m, ord c)

omit [Fintype n] in
/-- **Nondegeneracy.**  Distinct row labels and distinct jet orders give a nonzero determinant. -/
theorem jetArrayGen_det_ne_zero (t : Finset n) {ρ : ↥t → n} {ord : ↥t → ℕ}
    (hρ : Function.Injective ρ) (hord : Function.Injective ord) :
    (jetArrayGen (K := K) t ρ ord).det ≠ 0 := by
  have hpoly : (Matrix.of fun m c =>
      (MvPolynomial.X ((ρ m, ord c) : n × ℕ) : MvPolynomial (n × ℕ) K)).det ≠ 0 := by
    refine det_map_X_ne_zero _ ?_
    intro m c m' c' h
    exact ⟨hρ (congrArg Prod.fst h), hord (congrArg Prod.snd h)⟩
  intro hzero
  refine hpoly ?_
  have hdet : algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
      ((Matrix.of fun m c =>
        (MvPolynomial.X ((ρ m, ord c) : n × ℕ) : MvPolynomial (n × ℕ) K)).det) =
      (jetArrayGen (K := K) t ρ ord).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    rfl
  rw [hzero] at hdet
  exact (map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial (n × ℕ) K)
    (HomogeneousJetField n K))).1 hdet

/-- The determinant of a general jet array of a covector span. -/
def jetDetGen (t : Finset n) (ord : ↥t → ℕ) : HomogeneousJetField n K :=
  (jetArrayGen t (fun m => (m : n)) ord).det

omit [Fintype n] in
theorem jetDetGen_ne_zero (t : Finset n) {ord : ↥t → ℕ} (hord : Function.Injective ord) :
    jetDetGen (K := K) t ord ≠ 0 :=
  jetArrayGen_det_ne_zero t Subtype.coe_injective hord

/-- **Invariance for arbitrary jet orders.**  Any square jet array of a covector span, with any
choice of jet orders, has determinant invariant under the observer group of that span. -/
theorem jetDetGen_invariant {t : Finset n} (ord : ↥t → ℕ) {g : SpecialLinearGroup n K}
    (hg : g ∈ chartSubsetStabilizer (K := K) (↑t : Set n)) :
    g • jetDetGen (K := K) t ord = jetDetGen t ord := by
  have hginv : (g⁻¹ : SpecialLinearGroup n K) ∈
      chartSubsetStabilizer (K := K) (↑t : Set n) := inv_mem hg
  have hmap : (jetArrayGen (K := K) t (fun m => (m : n)) ord).map
        ((linearJetFieldEquiv g : HomogeneousJetField n K →+* HomogeneousJetField n K)) =
      ((blockRestrict t (g⁻¹ : SpecialLinearGroup n K)).map
        (algebraMap K (HomogeneousJetField n K))) *
          (jetArrayGen t (fun m => (m : n)) ord) := by
    ext m c
    rw [Matrix.map_apply, jetArrayGen, Matrix.of_apply, Matrix.mul_apply]
    show linearJetFieldEquiv g (freeCoordinate K (n × ℕ) ((m : n), ord c)) = _
    rw [← linearJetAction_apply, linearJetAction_freeCoordinate_of_mem hg m (ord c)]
    exact Finset.sum_congr rfl fun q _ => rfl
  have hdetB : ((blockRestrict t (g⁻¹ : SpecialLinearGroup n K)).map
      (algebraMap K (HomogeneousJetField n K))).det = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_blockRestrict hginv, map_one]
  have hF : g • (jetArrayGen (K := K) t (fun m => (m : n)) ord).det =
      ((linearJetFieldEquiv g : HomogeneousJetField n K →+* HomogeneousJetField n K))
        (jetArrayGen (K := K) t (fun m => (m : n)) ord).det := rfl
  rw [jetDetGen, hF, RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_mul, hdetB,
    one_mul]

/-- General minors of a span are horizon observables of that span. -/
theorem jetDetGen_mem_horizonField (t : Finset n) (ord : ↥t → ℕ) :
    jetDetGen (K := K) t ord ∈ horizonField (K := K) (↑t : Set n) := by
  rw [mem_horizonField_iff']
  intro g hg
  exact jetDetGen_invariant ord hg

/-- General minors of any superset of a span are still horizon observables of that span: with rows
a span together with one outside direction and columns an initial block together with one further
jet order, these are the normalised transverse jets. -/
theorem jetDetGen_mem_horizonField_of_subset {t u : Finset n} (htu : t ⊆ u) (ord : ↥u → ℕ) :
    jetDetGen (K := K) u ord ∈ horizonField (K := K) (↑t : Set n) := by
  rw [mem_horizonField_iff']
  intro g hg
  exact jetDetGen_invariant ord (chartSubsetStabilizer_mono (Finset.coe_subset.2 htu) hg)

/-- The normalised transverse jet of a span: a general minor of the enlarged span divided by the
minor of the span itself. -/
def jetGenRatio (t u : Finset n) (ord : ↥u → ℕ) (ordt : ↥t → ℕ) :
    HomogeneousJetField n K :=
  jetDetGen u ord / jetDetGen t ordt

theorem jetGenRatio_mem_horizonField {t u : Finset n} (htu : t ⊆ u) (ord : ↥u → ℕ)
    (ordt : ↥t → ℕ) :
    jetGenRatio (K := K) t u ord ordt ∈ horizonField (K := K) (↑t : Set n) :=
  div_mem (jetDetGen_mem_horizonField_of_subset htu ord) (jetDetGen_mem_horizonField t ordt)

end

end GaloisForLFunctions.HTGeometry

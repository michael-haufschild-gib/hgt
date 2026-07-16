import GaloisForLFunctions.HTGeometry.FreeKaehlerHorizonScheme

/-!
# Many-worlds nonuniqueness behind one holographic horizon

Fix one linear horizon law.  Its free pretemporal realizations at depths `n + 2` have pairwise
distinct affine Kähler/minor ideals, because their universal vertex thicknesses are the strictly
increasing triangular numbers.  Nevertheless, power saturation identifies every one of them with
the same external horizon scheme.

Thus exact horizon reconstruction and bulk uniqueness are different statements.  The boundary
recovers the saturated law scheme faithfully, while forgetting an infinite family of genuinely
different affine vertex thickenings.  This is the precise algebraic content of the many-worlds
holographic interpretation: one boundary law admits infinitely many pre-directional bulk depths.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial
open scoped Pointwise

universe u v

variable {K : Type u} {ι : Type v} [Field K] [Fintype ι]

/-- The one-equation packet defining the coordinate hyperplane at `i`.  Indexing the repeated
equation by law directions keeps the terminal payload in the same universe as law space. -/
def hyperplaneLaw (i : ι) : ι → MvPolynomial ι K := fun _ ↦ X i

omit [Fintype ι] in
/-- The terminal law ideal of `hyperplaneLaw` is the principal coordinate ideal. -/
theorem lawEquationIdeal_hyperplaneLaw (i : ι) :
    lawEquationIdeal (hyperplaneLaw (K := K) i) =
      Ideal.span ({X i} : Set (MvPolynomial ι K)) := by
  rw [lawEquationIdeal]
  change Ideal.span (Set.range (fun _ : ι ↦ X i)) = Ideal.span ({X i} : Set _)
  apply congrArg Ideal.span
  ext q
  constructor
  · rintro ⟨j, rfl⟩
    exact Set.mem_singleton _
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    exact ⟨i, rfl⟩

omit [Fintype ι] in
/-- Multiplying one fixed coordinate law by two different powers of the irrelevant ideal produces
different affine ideals. -/
theorem irrelevantPow_mul_X_span_ne {i : ι} {a b : ℕ} (hab : a < b) :
    idealOfVars ι K ^ a * Ideal.span ({X i} : Set _) ≠
      idealOfVars ι K ^ b * Ideal.span ({X i} : Set _) := by
  intro hEq
  have hXi : X i ∈ idealOfVars ι K :=
    Ideal.subset_span ⟨i, rfl⟩
  have hXiSpan : X i ∈ Ideal.span ({X i} : Set (MvPolynomial ι K)) :=
    Ideal.subset_span (Set.mem_singleton _)
  have hmem : X i ^ (a + 1) ∈
      idealOfVars ι K ^ a * Ideal.span ({X i} : Set _) := by
    rw [pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hXi a) hXiSpan
  have hspan_le : Ideal.span ({X i} : Set (MvPolynomial ι K)) ≤ idealOfVars ι K := by
    exact Ideal.span_le.2 (by simpa using hXi)
  have hproduct_le :
      idealOfVars ι K ^ b * Ideal.span ({X i} : Set _) ≤ idealOfVars ι K ^ (b + 1) := by
    calc
      idealOfVars ι K ^ b * Ideal.span ({X i} : Set _) ≤
          idealOfVars ι K ^ b * idealOfVars ι K := Ideal.mul_mono_right hspan_le
      _ = idealOfVars ι K ^ (b + 1) := (pow_succ _ _).symm
  have hbad : X i ^ (a + 1) ∈ idealOfVars ι K ^ (b + 1) :=
    hproduct_le (hEq ▸ hmem)
  have hnot : X i ^ (a + 1) ∉ idealOfVars ι K ^ (b + 1) := by
    rw [X_pow_eq_monomial,
      monomial_mem_pow_idealOfVars_iff (b + 1) (Finsupp.single i (a + 1)) one_ne_zero]
    simpa using (Nat.not_le_of_gt (Nat.succ_lt_succ hab))
  exact hnot hbad

/-- Advancing one jet layer adds the previous depth to the pretemporal vertex thickness. -/
theorem pretemporalVertexThickness_succ (d : ℕ) :
    pretemporalVertexThickness (d + 1) = pretemporalVertexThickness d + d := by
  unfold pretemporalVertexThickness
  rw [← Finset.sum_range_id (d + 1), ← Finset.sum_range_id d,
    Finset.sum_range_succ]

/-- From depth two onward, the universal affine vertex thickness is strictly increasing. -/
theorem pretemporalVertexThickness_strictMono :
    StrictMono (fun n : ℕ ↦ pretemporalVertexThickness (n + 2)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [show n + 1 + 2 = (n + 2) + 1 by omega,
    pretemporalVertexThickness_succ (n + 2)]
  omega

/-- The scalar Kähler/minor ideal of the depth-`d` free realization of one coordinate horizon. -/
def hyperplaneBulkPrincipalIdeal (i : ι) (d : ℕ) : Ideal (MvPolynomial ι K) :=
  universalLinearJetMinorIdeal
    (blockDiagonalLinearJetCoefficient
      (pretemporalPrincipalRowCoefficient (hyperplaneLaw (K := K) i) d))

/-- Every bulk depth has exactly the same saturated holographic horizon. -/
theorem hyperplaneBulkPrincipalIdeal_saturation_independent
    (i : ι) (d e : ℕ) :
    idealPowerSaturation (idealOfVars ι K) (hyperplaneBulkPrincipalIdeal (K := K) i d) =
      idealPowerSaturation (idealOfVars ι K) (hyperplaneBulkPrincipalIdeal (K := K) i e) := by
  unfold hyperplaneBulkPrincipalIdeal
  rw [freePretemporalPrincipalMinorIdeal_saturation,
    freePretemporalPrincipalMinorIdeal_saturation]

/-- The affine bulk ideals at depths `n + 2` are pairwise distinct. -/
theorem hyperplaneBulkPrincipalIdeal_pairwise_distinct (i : ι) :
    Pairwise fun n e : ℕ ↦
      hyperplaneBulkPrincipalIdeal (K := K) i (n + 2) ≠
        hyperplaneBulkPrincipalIdeal (K := K) i (e + 2) := by
  intro n e hne
  have hdistinct : ∀ {x y : ℕ}, x < y →
      hyperplaneBulkPrincipalIdeal (K := K) i (x + 2) ≠
        hyperplaneBulkPrincipalIdeal (K := K) i (y + 2) := by
    intro x y hxy
    unfold hyperplaneBulkPrincipalIdeal
    rw [freePretemporalPrincipalMinorIdeal_eq_generalPrincipalSymbolIdeal,
      freePretemporalPrincipalMinorIdeal_eq_generalPrincipalSymbolIdeal,
      generalPrincipalSymbolIdeal_eq_irrelevantPow_mul,
      generalPrincipalSymbolIdeal_eq_irrelevantPow_mul,
      lawEquationIdeal_hyperplaneLaw]
    exact irrelevantPow_mul_X_span_ne
      (pretemporalVertexThickness_strictMono hxy)
  rcases lt_or_gt_of_ne hne with hne' | hne'
  · exact hdistinct hne'
  · exact (hdistinct hne').symm

/-- **Many-worlds holographic nonuniqueness.**  There are infinitely many pairwise distinct
pretemporal bulk principal ideals over one fixed saturated horizon scheme. -/
theorem hyperplane_holographic_manyWorlds (i : ι) :
    (Pairwise fun n e : ℕ ↦
      hyperplaneBulkPrincipalIdeal (K := K) i (n + 2) ≠
        hyperplaneBulkPrincipalIdeal (K := K) i (e + 2)) ∧
    (∀ n e : ℕ,
      idealPowerSaturation (idealOfVars ι K)
          (hyperplaneBulkPrincipalIdeal (K := K) i (n + 2)) =
        idealPowerSaturation (idealOfVars ι K)
          (hyperplaneBulkPrincipalIdeal (K := K) i (e + 2))) := by
  exact ⟨hyperplaneBulkPrincipalIdeal_pairwise_distinct i,
    fun n e ↦ hyperplaneBulkPrincipalIdeal_saturation_independent i (n + 2) (e + 2)⟩

end

end GaloisForLFunctions.HTGeometry

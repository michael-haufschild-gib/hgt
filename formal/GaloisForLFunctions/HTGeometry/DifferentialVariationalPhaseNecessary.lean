import GaloisForLFunctions.HTGeometry.DifferentialVariationalRankOnePhase

/-!
# Necessary implications in the differential variational phase law

Bounded orbit displacement forces zero stable Euclidean speed.  A fixed projective lattice vertex
forces every orbit to be bounded, independently of the chosen base point.  Combining these facts
with the exact norm identity gives all easy directions of the phase law and identifies strict
positive speed exactly with a nonzero Cartan translation vector.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- Every subadditive clock gauge has nonnegative stable translation length. -/
theorem SubadditiveClockGauge.translationLength_nonneg
    {G : Type*} [Group G] (W : SubadditiveClockGauge G) (g : G) :
    0 ≤ W.translationLength g := by
  apply ge_of_tendsto' (W.tendsto_normalizedOrbitCost g)
  intro n
  exact
    div_nonneg (W.cost_nonneg _) (Nat.cast_nonneg n)

/-- A fixed vertex remains fixed by every nonnegative iterate. -/
theorem differentialVariational_fixedVertex_pow
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (σ : DifferentialFieldAut C K)
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (hx : σ.projectiveBuildingAction b x = x) (n : ℕ) :
    (σ ^ n).projectiveBuildingAction b x = x := by
  induction n with
  | zero => rw [pow_zero, DifferentialFieldAut.projectiveBuildingAction_one]
  | succ n ih =>
      rw [pow_succ, DifferentialFieldAut.projectiveBuildingAction_mul, ih, hx]

/-- Boundedness of a projective Euclidean orbit is independent of the lattice base point. -/
theorem differentialVariationalEuclideanOrbitBounded_base_independent
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x y : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    DifferentialVariationalEuclideanOrbitBounded b x σ ↔
      DifferentialVariationalEuclideanOrbitBounded b y σ := by
  have htransfer : ∀
      (u v : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)),
      DifferentialVariationalEuclideanOrbitBounded b u σ →
        DifferentialVariationalEuclideanOrbitBounded b v σ := by
    intro u v
    rintro ⟨B, hB⟩
    refine ⟨B + 2 *
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance v u, fun n => ?_⟩
    have hcomp := differentialVariationalEuclideanOrbitGauge_cost_base_le b v u (σ ^ n)
    calc
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance v
          ((σ ^ n).projectiveBuildingAction b v) ≤
        DiffOp.differentialVariationalProjectiveEuclideanVertexDistance u
            ((σ ^ n).projectiveBuildingAction b u) +
          2 * DiffOp.differentialVariationalProjectiveEuclideanVertexDistance v u := hcomp
      _ ≤ B + 2 * DiffOp.differentialVariationalProjectiveEuclideanVertexDistance v u := by
        gcongr
        exact hB n
  exact ⟨htransfer x y, htransfer y x⟩

/-- A fixed projective lattice vertex makes every Euclidean orbit bounded. -/
theorem differentialVariationalHasFixedVertex_implies_orbitBounded
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K)
    (hfix : DifferentialVariationalHasFixedVertex b σ) :
    DifferentialVariationalEuclideanOrbitBounded b x σ := by
  obtain ⟨y, hy⟩ := hfix
  apply (differentialVariationalEuclideanOrbitBounded_base_independent b y x σ).mp
  refine ⟨0, fun n => ?_⟩
  rw [differentialVariational_fixedVertex_pow b σ y hy n]
  exact le_of_eq
    (DiffOp.differentialVariationalProjectiveEuclideanVertexDistance_self y)

/-- Bounded Euclidean orbit displacement forces zero stable translation speed. -/
theorem differentialVariationalEuclideanOrbitBounded_implies_translationLength_eq_zero
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K)
    (hbounded : DifferentialVariationalEuclideanOrbitBounded b x σ) :
    differentialVariationalEuclideanTranslationLength b x σ = 0 := by
  obtain ⟨B, hB⟩ := hbounded
  have hzero : Filter.Tendsto (fun n : ℕ =>
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
          ((σ ^ n).projectiveBuildingAction b x) / n)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact div_nonneg
        (DiffOp.differentialVariationalProjectiveEuclideanVertexDistance_nonneg _ _)
        (Nat.cast_nonneg n)
    · intro n
      exact div_le_div_of_nonneg_right (hB n) (Nat.cast_nonneg n)
    · exact tendsto_const_div_atTop_nhds_zero_nat B
  exact tendsto_nhds_unique
    (tendsto_differentialVariationalEuclidean_normalizedOrbitDistance b x σ) hzero

/-- Bounded orbit displacement forces the complete Cartan translation vector to vanish. -/
theorem differentialVariationalEuclideanOrbitBounded_implies_cartanVector_eq_zero
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K)
    (hbounded : DifferentialVariationalEuclideanOrbitBounded b x σ) :
    differentialVariationalCartanTranslationVector b x σ = 0 := by
  rw [← differentialVariationalEuclideanTranslationLength_eq_zero_iff_cartanVector_eq_zero]
  exact differentialVariationalEuclideanOrbitBounded_implies_translationLength_eq_zero
    b x σ hbounded

/-- A fixed projective lattice vertex forces zero intrinsic Cartan translation vector. -/
theorem differentialVariationalHasFixedVertex_implies_cartanVector_eq_zero
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K)
    (hfix : DifferentialVariationalHasFixedVertex b σ) :
    differentialVariationalCartanTranslationVector b x σ = 0 :=
  differentialVariationalEuclideanOrbitBounded_implies_cartanVector_eq_zero b x σ
    (differentialVariationalHasFixedVertex_implies_orbitBounded b x σ hfix)

/-- Strict positive Euclidean speed is exactly nonvanishing of the intrinsic Cartan vector. -/
theorem differentialVariationalEuclideanTranslationLength_pos_iff_cartanVector_ne_zero
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    0 < differentialVariationalEuclideanTranslationLength b x σ ↔
      differentialVariationalCartanTranslationVector b x σ ≠ 0 := by
  have hnonneg : 0 ≤ differentialVariationalEuclideanTranslationLength b x σ :=
    (differentialVariationalEuclideanOrbitGauge b x).translationLength_nonneg σ
  constructor
  · intro hpos hvector
    have hzero :=
      (differentialVariationalEuclideanTranslationLength_eq_zero_iff_cartanVector_eq_zero
        b x σ).mpr hvector
    linarith
  · intro hvector
    have hne : differentialVariationalEuclideanTranslationLength b x σ ≠ 0 := by
      intro hzero
      exact hvector
        ((differentialVariationalEuclideanTranslationLength_eq_zero_iff_cartanVector_eq_zero
          b x σ).mp hzero)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Positive variational speed excludes every bounded Euclidean orbit. -/
theorem differentialVariationalEuclideanTranslationLength_pos_implies_orbitUnbounded
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K)
    (hpos : 0 < differentialVariationalEuclideanTranslationLength b x σ) :
    ¬ DifferentialVariationalEuclideanOrbitBounded b x σ := by
  intro hbounded
  rw [differentialVariationalEuclideanOrbitBounded_implies_translationLength_eq_zero
    b x σ hbounded] at hpos
  exact lt_irrefl 0 hpos

/-- Positive variational speed excludes a fixed projective lattice vertex. -/
theorem differentialVariationalEuclideanTranslationLength_pos_implies_noFixedVertex
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K)
    (hpos : 0 < differentialVariationalEuclideanTranslationLength b x σ) :
    ¬ DifferentialVariationalHasFixedVertex b σ := by
  intro hfix
  exact differentialVariationalEuclideanTranslationLength_pos_implies_orbitUnbounded
    b x σ hpos
      (differentialVariationalHasFixedVertex_implies_orbitBounded b x σ hfix)

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphColumnOriginModel
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JointOriginWeights
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LeftOriginZeros

/-! The origin equations give the same local Koszul model in the left
column and in the joint column containing the graph equations. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH.WeightedChartSystem

namespace GlobalTheory.WH

variable {k F E L : Type} [Field k] [Field F] [Field E] [Field L]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower k F E] [IsScalarTower k F L] [IsScalarTower k E L] [IsScalarTower F E L]
  {d : ℕ} {x : Fin (d + 1) → F} (h : IsPd k x) (j₂ : E →ₐ[k] L)
  {p q : ℕ} {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)

local notation "B" => RY x j₂ I J
local notation "B₀" => rB k L x {0}
local notation "T" => graphChartSystem h j₂ q p

omit [Algebra k E] [Algebra F E] [Algebra E L]
  [IsScalarTower k F E] [IsScalarTower k E L] [IsScalarTower F E L] in
/-- A chart with the same local values as an origin fibre point admits
an origin-ideal model when the selected weights are the origin coordinates. -/
theorem originColumn_model_of_localValues {A : Subalgebra k L}
    [IsAlgClosed k] [IsReduced (B₀ ⧸ originIdeal k L x)]
    (hL : IsFinCover k L x) (e : A →ₐ[k] k) (f : OriginFibrePoint k L x)
    (hval : ∀ a b, Val A e a b ↔ Val B₀ f.1 a b)
    {ι : Type} (r : ι → A) (sel : Fin d → ι)
    (hsel : ∀ m, (r (sel m) : L) = (localOriginCoordinate f m : L)) :
    loc A e = loc B₀ f.1 ∧
      ∃ u : ι → loc B₀ f.1, (∀ l, (u l : L) = (r l : L)) ∧
        Ideal.span (Set.range fun m => u (sel m)) =
          RingHom.ker (locEval B₀ f.1).toRingHom := by
  have hloc := loc_eq_of_val_iff A e hval
  let u (l : ι) : loc B₀ f.1 := ⟨r l, hloc ▸ le_loc A e (r l).property⟩
  have hu : (fun m => u (sel m)) = localOriginCoordinate f :=
    funext fun m => Subtype.ext (hsel m)
  exact ⟨hloc, u, fun _ => rfl, hu.symm ▸ hL.span_localOriginCoordinates f⟩

theorem graphColumnWeights_leftOrigin (l : Fin d) :
    (graphColumnWeights h j₂ hi hj
      ((T).leftOriginWeights_admitted (graphChartSystem_good h j₂ q p)) l : L) =
      algebraMap F L (x l.succ / x i) :=
  originAffineWeight_eq h j₂ i j l

theorem graphColumnWeights_joint_left {ι : Type} [LinearOrder ι]
    {n : ι → ℕ × ℕ} {z : ι → L} (hz : (T).Admitted n z) (l : ι) :
    graphColumnWeights h j₂ hi hj
      ((T).jointWeights_admitted (graphChartSystem_good h j₂ q p) hz) (joinedLeft (κ := Fin d) l) =
      graphColumnWeights h j₂ hi hj hz l :=
  Subtype.ext rfl

theorem graphColumnWeights_joint_right {ι : Type} [LinearOrder ι]
    {n : ι → ℕ × ℕ} {z : ι → L} (hz : (T).Admitted n z) (l : Fin d) :
    graphColumnWeights h j₂ hi hj
      ((T).jointWeights_admitted (graphChartSystem_good h j₂ q p) hz) (joinedRight (ι := ι) l) =
      graphColumnWeights h j₂ hi hj
        ((T).leftOriginWeights_admitted (graphChartSystem_good h j₂ q p)) l :=
  Subtype.ext rfl

end GlobalTheory.WH

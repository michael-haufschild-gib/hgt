import GaloisForLFunctions.RHTower.WeilPaperPacketPrimitiveInterpolation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Linear sampling of the zero-mass integer-null Weil space

The paper's prime-subset masks give surjective finite rational sampling maps on
the actual signed mixture space. Consecutive coprime labels supply arbitrarily
large real coordinate quotients, proving that this null space is infinite-dimensional.
Every finite sampler also admits a linear right inverse.
-/

open Complex Zeta23
noncomputable section
namespace RHTower.WeilWorkPBAP

open WeilOneSided

/-- Signed finite mixtures satisfying all integer constraints and zero autocorrelation mass. -/
def paperNullMassSpace : Submodule ℝ (WeilTestFn →₀ ℝ) :=
  LinearMap.ker defect ⊓ LinearMap.ker
    (Finsupp.linearCombination ℝ (fun f : WeilTestFn => EF.weilTest f.1 f.1 0))

@[simp] theorem mem_paperNullMassSpace (d : WeilTestFn →₀ ℝ) :
    d ∈ paperNullMassSpace ↔ defect d = 0 ∧ mixtureSample d 0 = 0 := Iff.rfl

/-- All primitive rational samples in one packet, as a real linear map on the native null space. -/
def paperPrimitiveSampler (N : ℕ) :
    paperNullMassSpace →ₗ[ℝ] (PaperPacketPrimitiveEdge N → ℂ) :=
  (LinearMap.pi fun r : PaperPacketPrimitiveEdge N =>
    Finsupp.linearCombination ℝ (fun f : WeilTestFn =>
      EF.weilTest f.1 f.1 (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)))).comp
        paperNullMassSpace.subtype

@[simp] theorem paperPrimitiveSampler_apply (N : ℕ) (d : paperNullMassSpace)
    (r : PaperPacketPrimitiveEdge N) :
    paperPrimitiveSampler N d r =
      mixtureSample d.1 (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) := rfl

/-- The positive-pair construction realizes every finite complex observation vector. -/
theorem paperPrimitiveSampler_surjective (N : ℕ) :
    Function.Surjective (paperPrimitiveSampler N) := by
  intro z
  obtain ⟨d, hd, hm, hs⟩ := exists_integer_null_zero_mass_primitive_interpolant 0 z
  exact ⟨⟨d, hd, hm⟩, funext hs⟩

/-- Primitive observations admit linear lifts into the exact zero-mass integer-null space. -/
theorem exists_paperPrimitiveSampler_rightInverse (N : ℕ) :
    ∃ S : (PaperPacketPrimitiveEdge N → ℂ) →ₗ[ℝ] paperNullMassSpace,
      (paperPrimitiveSampler N).comp S = LinearMap.id :=
  (paperPrimitiveSampler N).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (paperPrimitiveSampler_surjective N))

theorem rank_primitive_samples_le_nullMassSpace (N : ℕ) :
    Module.rank ℝ (PaperPacketPrimitiveEdge N → ℂ) ≤ Module.rank ℝ paperNullMassSpace :=
  (paperPrimitiveSampler N).rank_le_of_surjective (paperPrimitiveSampler_surjective N)

/-- Consecutive positive labels give arbitrarily many distinct primitive edges. -/
def paperConsecutiveEdge (n : ℕ) (i : Fin n) : PaperPacketPrimitiveEdge (n + 2) :=
  ⟨(⟨(i : ℕ) + 2, Finset.mem_Icc.mpr (by have := i.isLt; constructor <;> omega)⟩,
    ⟨(i : ℕ) + 3, Finset.mem_Icc.mpr (by have := i.isLt; constructor <;> omega)⟩),
    by
      change 1 < (i : ℕ) + 2 ∧ (i : ℕ) + 2 < (i : ℕ) + 3 ∧
        Nat.Coprime ((i : ℕ) + 2) ((i : ℕ) + 3)
      refine ⟨by omega, by omega, ?_⟩
      change Nat.Coprime ((i : ℕ) + 2) (((i : ℕ) + 2) + 1)
      simp⟩

theorem paperConsecutiveEdge_injective (n : ℕ) : Function.Injective (paperConsecutiveEdge n) := by
  intro i j h
  have hv := congrArg (fun r : PaperPacketPrimitiveEdge (n + 2) => (r.1.1 : ℕ)) h
  change (i : ℕ) + 2 = (j : ℕ) + 2 at hv
  apply Fin.ext
  omega

/-- Real samples on consecutive reduced ratios form an arbitrary finite coordinate quotient. -/
def paperConsecutiveSampler (n : ℕ) : paperNullMassSpace →ₗ[ℝ] (Fin n → ℝ) :=
  (LinearMap.pi fun i : Fin n => Complex.reCLM.toLinearMap.comp
    (Finsupp.linearCombination ℝ (fun f : WeilTestFn =>
      EF.weilTest f.1 f.1 (Real.log ((paperConsecutiveEdge n i).1.1 : ℕ) -
        Real.log ((paperConsecutiveEdge n i).1.2 : ℕ))))).comp paperNullMassSpace.subtype

@[simp] theorem paperConsecutiveSampler_apply (n : ℕ) (d : paperNullMassSpace) (i : Fin n) :
    paperConsecutiveSampler n d i =
      (mixtureSample d.1 (Real.log ((paperConsecutiveEdge n i).1.1 : ℕ) -
        Real.log ((paperConsecutiveEdge n i).1.2 : ℕ))).re := rfl

/-- Every real coordinate vector occurs while every integer defect and the mass stay zero. -/
theorem paperConsecutiveSampler_surjective (n : ℕ) :
    Function.Surjective (paperConsecutiveSampler n) := by
  intro v
  let z : PaperPacketPrimitiveEdge (n + 2) → ℂ :=
    Function.extend (paperConsecutiveEdge n) (fun i => (v i : ℂ)) (fun _ => 0)
  obtain ⟨d, hd⟩ := paperPrimitiveSampler_surjective (n + 2) z
  refine ⟨d, funext fun i => ?_⟩
  have hi := congrFun hd (paperConsecutiveEdge n i)
  have hz := (paperConsecutiveEdge_injective n).extend_apply (fun j => (v j : ℂ)) (fun _ => 0) i
  exact congrArg Complex.re (hi.trans hz)

/-- Arbitrarily large finite real coordinate spaces have linear lifts into the native null space. -/
theorem exists_paperConsecutiveSampler_rightInverse (n : ℕ) :
    ∃ S : (Fin n → ℝ) →ₗ[ℝ] paperNullMassSpace,
      (paperConsecutiveSampler n).comp S = LinearMap.id :=
  (paperConsecutiveSampler n).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (paperConsecutiveSampler_surjective n))

/-- All integer constraints and zero mass leave an infinite-dimensional real space of exact mixtures. -/
theorem not_finiteDimensional_paperNullMassSpace :
    ¬ FiniteDimensional ℝ paperNullMassSpace := by
  intro hfin
  letI := hfin
  have h := LinearMap.finrank_le_finrank_of_surjective
    (paperConsecutiveSampler_surjective (Module.finrank ℝ paperNullMassSpace + 1))
  rw [Module.finrank_fin_fun] at h
  omega

end RHTower.WeilWorkPBAP

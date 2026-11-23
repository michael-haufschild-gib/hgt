import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedFixedPoints
import Mathlib.Data.Matrix.Basic

/-! At a fixed point over the reduced origin fibre, the second pullback
has a first-order expansion in the first pullback coordinates. -/

noncomputable section

open GlobalTheory.PD GlobalTheory.SchemeCohomology

namespace GlobalTheory.WH

variable {k F E L : Type} [Field k] [Field F] [Field E] [Field L]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower k F E] [IsScalarTower k F L] [IsScalarTower k E L] [IsScalarTower F E L]
  {d : ℕ} {x : Fin (d + 1) → F}

/-- At a fixed origin point, clearing a nonvanishing denominator gives
the rows of the second pullback in the origin parameters. -/
theorem exists_fixedChartRows (hL : IsFinCover k L x)
    [IsReduced ((rB k L x {0}) ⧸ Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem k L x j⟩ : rB k L x {0})))]
    (e : rB k L x {0} →ₐ[k] k)
    (hz : ∀ j, e ⟨_, tco_mem k L x j⟩ = 0)
    (j₂ : E →ₐ[k] L) (hfix : IsFix (rB k L x {0}) e j₂ (rB k E x {0})) :
    ∃ M : Matrix (Fin d) (Fin d) k, ∀ m : Fin d,
      ∃ (c : rB k L x {0}) (g : Fin d → rB k L x {0}),
        e c ≠ 0 ∧
        (c : L) * j₂ (algebraMap F E (x m.succ / x 0)) =
          ∑ l, (g l : L) * algebraMap F L (x l.succ / x 0) ∧
        ∀ l, e (g l) = e c * M m l := by
  have row (m : Fin d) :
      ∃ (c : rB k L x {0}) (g : Fin d → rB k L x {0}),
        e c ≠ 0 ∧ (c : L) * j₂ (algebraMap F E (x m.succ / x 0)) =
          ∑ l, (g l : L) * algebraMap F L (x l.succ / x 0) := by
    let u : rB k E x {0} := ⟨_, tco_mem k E x m⟩
    let p : rB k L x {0} := rBPullback x {0} u
    obtain ⟨b, hb, hbu, hne, hval⟩ := hfix u u.2 p.2
    change e ⟨b * j₂ u, hbu⟩ = e ⟨b, hb⟩ * e p at hval
    have hp : e p = 0 := by
      rw [show p = ⟨_, tco_mem k L x m⟩ from rBPullback_originCoordinate x m]
      exact hz m
    rw [hp, mul_zero] at hval
    obtain ⟨a, g, ha, h⟩ := exists_regular_parameters_of_reduced_quotient hL e _ hval
    refine ⟨a * ⟨b, hb⟩, g, ?_, ?_⟩
    · simpa only [map_mul, ha, one_mul] using hne
    · rw [Subalgebra.coe_mul, mul_assoc]
      exact congrArg ((rB k L x {0}).val) h |>.trans (map_sum _ _ _)
  choose c g hc h using row
  refine ⟨Matrix.of (fun m l => e (g m l) / e (c m)), fun m => ⟨c m, g m, hc m, h m, ?_⟩⟩
  intro l
  change e (g m l) = e (c m) * (e (g m l) / e (c m))
  rw [mul_comm, div_mul_cancel₀ _ (hc m)]

end GlobalTheory.WH

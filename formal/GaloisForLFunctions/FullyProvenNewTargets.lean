/-
# `2-fully-proven/new` Lean targets, including q62 branch surfaces

Door grade: BRIDGE / formal ledger.  This file adds no mathematical shortcut: it
collects the Lean proof objects currently serving the cards in
`docs/drafts/pipeline/2-fully-proven/new`.  Connected hRigid/q62 endpoints are
exposed as explicit branch proof objects here; their theorem names state the
remaining hypotheses still carried by those branches.

The rule here is strict.  A declaration below is either:
* a theorem wrapper around an existing proof object, or
* a target `Prop` whose proof is supplied immediately by an existing theorem.

For cards whose paper statement is wider than the present Lean theorem, the
wrapper name says which branch is proved.
-/
import GaloisForLFunctions.Hurwitz.N2Final
import GaloisForLFunctions.Hurwitz.NonRationality
import GaloisForLFunctions.Hurwitz.N2HalfInteger
import GaloisForLFunctions.Hurwitz.N2HZeta
import GaloisForLFunctions.Hurwitz.AllNQuadFilt
import GaloisForLFunctions.Hurwitz.AllNHalfInteger
import GaloisForLFunctions.Hurwitz.AllNRowExtraction
import GaloisForLFunctions.Hurwitz.AllNRelationClose
import GaloisForLFunctions.Hurwitz.AllNTailIndependence
import GaloisForLFunctions.Hurwitz.MonodromyScalar
import GaloisForLFunctions.Hurwitz.PolylogPoleTower
import GaloisForLFunctions.U0.U0CardTheorems
import GaloisForLFunctions.U0.U0PhiCircleWindow
import GaloisForLFunctions.U0.U0PhiFourWindow
import GaloisForLFunctions.U0.U0WindowNormalization
import GaloisForLFunctions.U0.U0CoverMono
import GaloisForLFunctions.U0.U0CoverTransport
import GaloisForLFunctions.U0.U0PhiLifts
import GaloisForLFunctions.U0.U0PhiCard
import GaloisForLFunctions.Bottcher.AlgIndep
import GaloisForLFunctions.Bottcher.MonodromyObstruction
import GaloisForLFunctions.Bottcher.CoverMonodromy
import GaloisForLFunctions.Bottcher.DyadicMonodromy
import GaloisForLFunctions.Bottcher.MonodromyMultiplier
import GaloisForLFunctions.Bottcher.Rigidity
import GaloisForLFunctions.Bottcher.Q62ConnectedAssembly
import GaloisForLFunctions.Bottcher.JuliaBasinCrossing
import GaloisForLFunctions.Bottcher.Q62DeepDataAssembly
import GaloisForLFunctions.Bottcher.IndexWiring
import GaloisForLFunctions.Bottcher.IndexWiringRelative
import GaloisForLFunctions.Bottcher.RelativeDenseApproach
import GaloisForLFunctions.Bottcher.RelativeRigidityCountableAvoidance
import GaloisForLFunctions.Bottcher.RelativeRigidityDenseApproach
import GaloisForLFunctions.Bottcher.RelativeRigidityLocalSlitModel
import GaloisForLFunctions.Bottcher.RelativeRigidityGlobalBranchCrossing
import GaloisForLFunctions.Bottcher.RelativeRigidityReturnOrder
import GaloisForLFunctions.Bottcher.RelativeRigidityMultiplierOnePeriod
import GaloisForLFunctions.Bottcher.CrossRatioNormalBridge
import GaloisForLFunctions.Bottcher.HDiscLoopDeck

noncomputable section

open Complex Filter Topology MeasureTheory Metric Polynomial
open HurwitzN2Tail U0MeroCarrier U0KummerRepick Bottcher

namespace FullyProvenNewTargets

/-! ## Hurwitz cards -/

/-- Generic Lean target for
`hurwitz-quadratic-n2-density-shadow.md`.

This is the older generic branch: it assumes `s ∉ ℤ` and `2s ∉ ℤ`.
The exact card statement without the `2s ∉ ℤ` side condition is
`HurwitzN2DensityShadowTarget` below. -/
def HurwitzN2DensityShadowGenericTarget (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, (k : ℂ) ≠ s) →
  (∀ k : ℤ, (k : ℂ) ≠ 2 * s) →
  ∀ (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ)
      (N : ℕ),
    (∀ n, N ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval (-(n : ℂ) + Complex.exp z) *
          ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin 3, (l k).eval (-(n : ℂ) + Complex.exp z) *
            (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) →
    q 0 0 = 0 ∧ q 2 2 = 0 ∧ q 1 1 = 0 ∧ q 0 2 + q 2 0 = 0
      ∧ l 2 = 0 ∧ l 0 = 0 ∧ l 1 = 0 ∧ cc = 0

/-- Formal wrapper for the generic branch of
`hurwitz-quadratic-n2-density-shadow.md`. -/
theorem hurwitz_quadratic_n2_density_shadow_generic (s : ℂ) :
    HurwitzN2DensityShadowGenericTarget s := by
  intro hs1 hsZ h2sZ q l cc N hrel
  exact HurwitzN2Final.hurwitz_n2_unconditional
    (s := s) (N := N) hs1 hsZ h2sZ q l cc hrel

/-- Generic branch of the all-`N` quadratic-block target for
`hurwitz-quadratic-all-n-tail-independence.md`.

This is the older generic branch: it assumes `s ∉ ℤ` and `2s ∉ ℤ`.
The exact quadratic-block target without the `2s ∉ ℤ` side condition is
`HurwitzAllNQuadraticBlockTarget` below. -/
def HurwitzAllNQuadraticBlockGenericTarget (N : ℕ) (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, (k : ℂ) ≠ s) →
  (∀ k : ℤ, (k : ℂ) ≠ 2 * s) →
  ∀ (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) (M : ℕ),
    (∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) →
    ∀ w, w ≤ 2 * N → HurwitzAllNQuadFilt.AqN q w = 0

/-- Formal wrapper for the all-`N` quadratic-block spine. -/
theorem hurwitz_quadratic_allN_tail_independence_quadratic_block (N : ℕ) (s : ℂ) :
    HurwitzAllNQuadraticBlockGenericTarget N s := by
  intro hs1 hs h2s q l cc M hrel
  exact HurwitzAllNQuadFilt.allN_quad_vanish_genuine
    (N := N) (s := s) (M := M) hs1 hs h2s q l cc hrel

/-- Exact all-`N` quadratic-block target for
`hurwitz-quadratic-all-n-tail-independence.md`.

This records the Lean-proved quadratic spine with no `2s ∉ ℤ` side condition:
every quadratic weight coefficient `A_w` vanishes for the genuine factored
relation whenever `s` is nonintegral.  The final rational-tail independence /
linear-constant descent advertised by the paper card remains a separate target,
not hidden here. -/
def HurwitzAllNQuadraticBlockTarget (N : ℕ) (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, (k : ℂ) ≠ s) →
  ∀ (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) (M : ℕ),
    (∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) →
    ∀ w, w ≤ 2 * N → HurwitzAllNQuadFilt.AqN q w = 0

/-- Formal wrapper for the exact all-`N` quadratic-block spine, including the
half-integer branch. -/
theorem hurwitz_quadratic_allN_tail_independence_quadratic_block_all_noninteger
    (N : ℕ) (s : ℂ) : HurwitzAllNQuadraticBlockTarget N s := by
  intro hs1 hs q l cc M hrel
  exact HurwitzAllNHalfInteger.allN_quad_vanish_genuine_all_noninteger
    (N := N) (s := s) (M := M) hs1 hs q l cc hrel

/-- Card-name theorem for the proved quadratic spine of
`hurwitz-quadratic-all-n-tail-independence.md`.  This is not the final tail-independence close; it is
the unconditional all-noninteger quadratic-block theorem. -/
theorem hurwitz_quadratic_all_n_tail_independence_quadratic_block (N : ℕ) (s : ℂ) :
    HurwitzAllNQuadraticBlockTarget N s :=
  hurwitz_quadratic_allN_tail_independence_quadratic_block_all_noninteger N s

/-- Top-row extraction target for the all-`N` Hurwitz row descent: if the
linear+cross block `Ψ_N` vanishes, its top Laurent coefficient is the top
shifted-Hurwitz row equation. This is the first uniform row-descent brick after
the quadratic block theorem. -/
def HurwitzAllNTopRowExtractionTarget (N : ℕ) (s : ℂ) : Prop :=
  1 < s.re →
  ∀ (n : ℕ) (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ),
    (∀ z : ℂ, z.re < -Real.log 2 →
      HurwitzAllNQuadFilt.PsiN s n q l
        (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) →
    (∑ j : Fin (N + 1), ((q (Fin.last N) j + q j (Fin.last N)).eval (-(n : ℂ)))
        * HurwitzZetaShift.hzeta (s + (j : ℂ)) (-(n : ℂ)))
      + (l (Fin.last N)).eval (-(n : ℂ)) = 0

/-- Formal wrapper for the all-`N` top-row extraction theorem. -/
theorem hurwitz_allN_top_row_extraction (N : ℕ) (s : ℂ) :
    HurwitzAllNTopRowExtractionTarget N s := by
  intro hs1 n q l hPsi
  exact HurwitzAllNRowExtraction.top_row_extract (N := N) hs1 n q l hPsi

/-- Symmetric-form top-row extraction target, matching the row-close interface
used in `HurwitzAllNTailIndependence`. -/
def HurwitzAllNSymmetricTopRowExtractionTarget (N : ℕ) (s : ℂ) : Prop :=
  1 < s.re →
  ∀ (n : ℕ) (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ),
    (∀ i j, q i j = q j i) →
    (∀ z : ℂ, z.re < -Real.log 2 →
      HurwitzAllNQuadFilt.PsiN s n q l
        (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) →
    (l (Fin.last N)).eval (-(n : ℂ)) +
      (∑ i : Fin (N + 1), (q i (Fin.last N)).eval (-(n : ℂ)) *
        (2 * HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))) = 0

/-- Formal wrapper for the symmetric-form top-row extraction theorem. -/
theorem hurwitz_allN_symmetric_top_row_extraction (N : ℕ) (s : ℂ) :
    HurwitzAllNSymmetricTopRowExtractionTarget N s := by
  intro hs1 n q l hSymm hPsi
  exact HurwitzAllNRowExtraction.top_row_extract_symmetric (N := N) hs1 n q l hSymm hPsi

/-- Top-column close target from the exact pole-root tail input: if the
linear+cross block `Ψ_N` vanishes for all large `n`, then the symmetric top
quadratic column and top linear coefficient vanish. -/
def HurwitzAllNTopColumnCloseFromPoleRootTarget (N : ℕ) (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, s ≠ (k : ℂ)) →
  HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s →
  ∀ (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ) (M : ℕ),
    (∀ i j, q i j = q j i) →
    (∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 →
      HurwitzAllNQuadFilt.PsiN s n q l
        (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) →
    (∀ i : Fin (N + 1), q i (Fin.last N) = 0) ∧ l (Fin.last N) = 0

/-- Formal wrapper for the all-`N` top-column close from the exact
pole-root tail input. -/
theorem hurwitz_allN_top_column_close_from_pole_root (N : ℕ) (s : ℂ) :
    HurwitzAllNTopColumnCloseFromPoleRootTarget N s := by
  intro hs1 hsZ hpole q l M hSymm hPsi
  exact HurwitzAllNRowExtraction.top_column_close_of_poleRootInput
    (N := N) (s := s) (M := M) hs1 hsZ hpole q l hSymm hPsi

/-- Complete two-shift row-close target from the exact pole-root tail input:
the first recursive row-descent instance closes both quadratic columns and both
linear coefficients for `N = 1`. -/
def HurwitzN1ColumnCloseFromPoleRootTarget (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, s ≠ (k : ℂ)) →
  HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput 1 s →
  ∀ (q : Fin 2 → Fin 2 → Polynomial ℂ) (l : Fin 2 → Polynomial ℂ) (M : ℕ),
    (∀ i j, q i j = q j i) →
    (∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 →
      HurwitzAllNQuadFilt.PsiN s n q l
        (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) →
    (∀ i j : Fin 2, q i j = 0) ∧ (∀ j : Fin 2, l j = 0)

/-- Formal wrapper for the complete `N = 1` Hurwitz row close from the exact
pole-root tail input. -/
theorem hurwitz_n1_column_close_from_pole_root (s : ℂ) :
    HurwitzN1ColumnCloseFromPoleRootTarget s := by
  intro hs1 hsZ hpole q l M hSymm hPsi
  exact HurwitzAllNRowExtraction.two_column_close_of_poleRootInput
    (s := s) (M := M) hs1 hsZ hpole q l hSymm hPsi

/-- One-step all-`N` column-close target from the exact pole-root tail input:
assuming all higher columns have already closed, the filtered `Ψ_N` identity
extracts the `j`-th row equation and closes the `j`-th quadratic column and
linear coefficient. -/
def HurwitzAllNColumnCloseStepFromPoleRootTarget (N : ℕ) (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, s ≠ (k : ℂ)) →
  HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s →
  ∀ (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ) (M : ℕ) (j : Fin (N + 1)),
    (∀ i j, q i j = q j i) →
    (∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 →
      HurwitzAllNQuadFilt.PsiN s n q l
        (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) →
    (∀ k : Fin (N + 1), (j : ℕ) < (k : ℕ) →
      (∀ i : Fin (N + 1), q i k = 0) ∧ l k = 0) →
    (∀ i : Fin (N + 1), q i j = 0) ∧ l j = 0

/-- Formal wrapper for the one-step all-`N` column close from exact pole-root
tail input. -/
theorem hurwitz_allN_column_close_step_from_pole_root (N : ℕ) (s : ℂ) :
    HurwitzAllNColumnCloseStepFromPoleRootTarget N s := by
  intro hs1 hsZ hpole q l M j hSymm hPsi hhigher
  exact HurwitzAllNRowExtraction.column_close_of_higher_columns_closed
    (N := N) (s := s) (M := M) hs1 hsZ hpole q l hSymm hPsi j hhigher

/-- Full all-`N` column-close target from the exact pole-root tail input:
finite downward descent from the top column closes every quadratic column and
every linear coefficient of the linear+cross block. -/
def HurwitzAllNColumnsCloseFromPoleRootTarget (N : ℕ) (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, s ≠ (k : ℂ)) →
  HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s →
  ∀ (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ) (M : ℕ),
    (∀ i j, q i j = q j i) →
    (∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 →
      HurwitzAllNQuadFilt.PsiN s n q l
        (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) →
    (∀ i j : Fin (N + 1), q i j = 0) ∧ (∀ j : Fin (N + 1), l j = 0)

/-- Formal wrapper for the full all-`N` finite column descent from exact
pole-root tail input. -/
theorem hurwitz_allN_columns_close_from_pole_root (N : ℕ) (s : ℂ) :
    HurwitzAllNColumnsCloseFromPoleRootTarget N s := by
  intro hs1 hsZ hpole q l M hSymm hPsi
  exact HurwitzAllNRowExtraction.all_columns_close_of_poleRootInput
    (N := N) (s := s) (M := M) hs1 hsZ hpole q l hSymm hPsi

/-- Relation-level `Ψ_N` vanishing target for the all-`N` Hurwitz card:
the genuine local degree-`≤ 2` relation forces the singular linear+cross block
to vanish for all large `n`, with no `2s ∉ ℤ` side condition. -/
def HurwitzAllNPsiVanishFromRelationTarget (N : ℕ) (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) (M : ℕ),
    (∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
      z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) →
    ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 →
      HurwitzAllNQuadFilt.PsiN s n q l
        (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0

/-- Formal wrapper for relation-level `Ψ_N` vanishing in the all-`N` Hurwitz
card. -/
theorem hurwitz_allN_psi_vanish_from_relation (N : ℕ) (s : ℂ) :
    HurwitzAllNPsiVanishFromRelationTarget N s := by
  intro hs1 hsZ q l cc M hrel
  exact HurwitzAllNRelationClose.allN_psi_vanish_genuine_all_noninteger
    (N := N) (s := s) (M := M) hs1 hsZ q l cc hrel

/-- Relation-level all-`N` column-close target from exact pole-root tail input:
the genuine local degree-`≤ 2` relation gives `Ψ_N = 0`, and finite descent
closes every quadratic column and linear coefficient. -/
def HurwitzAllNColumnsCloseFromRelationPoleRootTarget (N : ℕ) (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, s ≠ (k : ℂ)) →
  HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s →
  ∀ (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) (M : ℕ),
    (∀ i j, q i j = q j i) →
    (∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
      z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) →
    (∀ i j : Fin (N + 1), q i j = 0) ∧ (∀ j : Fin (N + 1), l j = 0)

/-- Formal wrapper for relation-level all-`N` column close from exact pole-root
tail input. -/
theorem hurwitz_allN_columns_close_from_relation_pole_root (N : ℕ) (s : ℂ) :
    HurwitzAllNColumnsCloseFromRelationPoleRootTarget N s := by
  intro hs1 hsZ hpole q l cc M hSymm hrel
  exact HurwitzAllNRelationClose.all_columns_close_of_genuine_relation_poleRootInput
    (N := N) (s := s) (M := M) hs1 hsZ hpole q l cc hSymm hrel

/-- Full relation-level all-`N` coefficient close from exact pole-root tail
input, in symmetric quadratic form: all quadratic coefficients, all linear
coefficients, and the constant coefficient vanish. -/
def HurwitzAllNCoefficientsCloseFromRelationPoleRootTarget (N : ℕ) (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, s ≠ (k : ℂ)) →
  HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s →
  ∀ (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) (M : ℕ),
    (∀ i j, q i j = q j i) →
    (∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
      z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) →
    (∀ i j : Fin (N + 1), q i j = 0) ∧ (∀ j : Fin (N + 1), l j = 0) ∧ cc = 0

/-- Formal wrapper for the full relation-level all-`N` coefficient close from
exact pole-root tail input. -/
theorem hurwitz_allN_coefficients_close_from_relation_pole_root (N : ℕ) (s : ℂ) :
    HurwitzAllNCoefficientsCloseFromRelationPoleRootTarget N s := by
  intro hs1 hsZ hpole q l cc M hSymm hrel
  exact HurwitzAllNRelationClose.all_coefficients_close_of_genuine_relation_poleRootInput
    (N := N) (s := s) (M := M) hs1 hsZ hpole q l cc hSymm hrel

/-- Formal row/constant close target for
`hurwitz-quadratic-all-n-tail-independence.md`, once the rational-tail
independence lemma has supplied its exact Lean interface. -/
def HurwitzAllNRowCloseFromTailIndependenceTarget (N : ℕ) : Prop :=
  ∀ (V : Fin (N + 1) → ℕ → ℂ)
    (eta zeta : Fin (N + 1) → ℂ)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ),
    HurwitzAllNTailIndependence.RationalTailIndependent V →
    (∀ i, eta i ≠ 0) →
    (∀ j : Fin (N + 1), ∃ M : ℕ, ∀ n, M ≤ n →
      (l j).eval (-(n : ℂ)) +
        (∑ i : Fin (N + 1),
          (q i j).eval (-(n : ℂ)) * (2 * (zeta i + eta i * V i n))) = 0) →
    (∃ M : ℕ, ∀ n, M ≤ n → cc.eval (-(n : ℂ)) = 0) →
    (∀ i j, q i j = 0) ∧ (∀ j, l j = 0) ∧ cc = 0

/-- Formal wrapper for the all-`N` row/constant close from the rational-tail
interface.  This is the algebraic close; the polylog pole-tower lemma is still
the missing analytic theorem needed to remove the `RationalTailIndependent`
input from the final all-`N` card. -/
theorem hurwitz_quadratic_allN_tail_independence_row_close_from_tail_interface (N : ℕ) :
    HurwitzAllNRowCloseFromTailIndependenceTarget N := by
  intro V eta zeta q l cc hTail heta hrow hcc
  exact HurwitzAllNTailIndependence.rows_and_constant_close_of_rationalTailIndependent
    V hTail eta zeta heta q l cc hrow hcc

/-- Proved base case of the rational-tail interface: one tail sequence is
independent from rational functions as soon as its finite difference is a
noninteger power with nonzero multiplier. -/
def HurwitzRationalTailSingleTarget : Prop :=
  ∀ {s η : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) → η ≠ 0 → ∀ {V : ℕ → ℂ},
    (∀ n : ℕ, 1 ≤ n → V n - V (n - 1) = η * (n : ℂ) ^ (-s)) →
    HurwitzAllNTailIndependence.RationalTailIndependent (N := 0) (fun _ => V)

/-- Formal wrapper for the proved `N=0` rational-tail case. -/
theorem hurwitz_rational_tail_single_from_diff :
    HurwitzRationalTailSingleTarget := by
  intro s eta hs hη V hdiff
  exact HurwitzAllNTailIndependence.rationalTailIndependent_single_of_diff hs hη hdiff

/-- Algebraic pole-tower target for the rational-tail lemma: the top pole
coefficient polynomial cannot vanish at all positive `2πi` pole locations unless
all top coefficients vanish. -/
def HurwitzPolylogPoleTowerTopCoeffTarget (M : ℕ) : Prop :=
  ∀ {gamma a : Fin (M + 1) → ℂ},
    (∀ j, gamma j ≠ 0) →
    (∀ n : ℕ,
      (∑ j : Fin (M + 1),
        a j * gamma j *
          (HurwitzPolylogPoleTower.twoPiI * ((n + 1 : ℕ) : ℂ)) ^ (j : ℕ)) = 0) →
    ∀ j, a j = 0

/-- Formal wrapper for the algebraic pole-tower injectivity step used by the
polylog proof of rational-tail independence. -/
theorem hurwitz_polylog_pole_tower_top_coefficients (M : ℕ) :
    HurwitzPolylogPoleTowerTopCoeffTarget M := by
  intro gamma a hgamma hroot j
  exact HurwitzPolylogPoleTower.coefficients_zero_of_pole_sum_roots hgamma hroot j

/-! ## `u₀ ⟂ φ_b` cards -/

/-- Shared carrier target for the three u0-phi cards.

The only extra input is the explicit `PhibKummerInputs` provider; no placeholder
declaration is introduced. -/
def U0PhiIndependenceCarrierTarget {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b) : Prop :=
  letI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  NoRelation (RatFunc ℂ) (phiMero b hU_esc)
    (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext))

/-- Formal wrapper for `u0-phi-independence.md` (connected branch), conditional
on the explicit Kummer-input provider. -/
theorem u0_phi_independence_connected_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hKummer : U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  U0CardTheorems.u0_phi_independence_connected hUo hUc hUne hUinf hU_ext hU_esc hKummer

/-- Formal wrapper for `u0-phi-independence-disconnected.md`, conditional on
the explicit Kummer-input provider. -/
theorem u0_phi_independence_disconnected_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hKummer : U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  U0CardTheorems.u0_phi_independence_disconnected hUo hUc hUne hUinf hU_ext hU_esc hKummer

/-- Formal wrapper for `u0-phi-independence-all-parameters.md`, conditional on
the explicit Kummer-input provider. -/
theorem u0_phi_independence_all_parameters_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hKummer : U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  U0CardTheorems.u0_phi_independence_all_parameters hUo hUc hUne hUinf hU_ext hU_esc
    hKummer

/-- Card-name theorem for `u0-phi-independence.md`, using the current explicit Kummer provider. -/
theorem u0_phi_independence {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hKummer : U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  u0_phi_independence_connected_card hUo hUc hUne hUinf hU_ext hU_esc hKummer

/-- Card-name theorem for `u0-phi-independence-disconnected.md`, using the current explicit Kummer
provider. -/
theorem u0_phi_independence_disconnected {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hKummer : U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  u0_phi_independence_disconnected_card hUo hUc hUne hUinf hU_ext hU_esc hKummer

/-- Card-name theorem for `u0-phi-independence-all-parameters.md`, using the current explicit
Kummer provider. -/
theorem u0_phi_independence_all_parameters {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hKummer : U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  u0_phi_independence_all_parameters_card hUo hUc hUne hUinf hU_ext hU_esc hKummer

/-! ## Böttcher monodromy cards, non-hRigid side -/

/-- Algebraic target for
`not-new-but-required/unbounded-one-coordinate-monodromy-obstruction.md`. -/
def UnboundedOneCoordinateMonodromyTarget
    {K M : Type*} [Field K] [Field M] [Algebra K M] (F G : M) : Prop :=
  Transcendental K G →
  F ≠ 0 →
  (∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
    d < m ∧ orderOf ζ = m ∧ σ G = G ∧ σ ζ = ζ ∧ σ F = ζ * F) →
  ∀ P : Polynomial (Polynomial K),
    (P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom).eval F = 0 →
    P = 0

/-- Formal wrapper for the unbounded one-coordinate monodromy obstruction. -/
theorem unbounded_one_coordinate_monodromy_obstruction_card
    {K M : Type*} [Field K] [Field M] [Algebra K M] (F G : M) :
    UnboundedOneCoordinateMonodromyTarget (K := K) (M := M) F G := by
  intro hG hF mono P hrel
  exact Bottcher.algIndep_of_unbounded_monodromy (K := K) (M := M) F G hG hF mono P hrel

/-- Abstract q62 mixed-case endpoint: one disconnected coordinate's unbounded dyadic monodromy
already gives `NoRelation`, so the mixed branch does not consume the E-vS hRigid input. -/
def q62_mixed_unbounded_monodromy_formal_proof :=
  @Bottcher.q62_mixed

/-- Abstract q62 both-connected reduction: after `φ_{c₂}` transcendence, the remaining hRigid analytic
input is exactly `TranscendentalOverAdjoin φ_{c₁} φ_{c₂}`. -/
def q62_both_connected_transcendentalOverAdjoin_formal_proof :=
  @Bottcher.q62_both_connected

/-- Symmetry of the q62 relation target, used by the assembled hRigid branch when the disconnected
coordinate is the second parameter. -/
def q62_noRelation_symm_formal_proof :=
  @Bottcher.noRelation_symm

/-- Assembled hRigid slot for top-level q62: mixed cases are discharged by monodromy, while the
both-connected case is isolated as `TranscendentalOverAdjoin`. -/
def q62_hRigid_assemble_formal_proof :=
  @Bottcher.hRigid_assemble

/-- Final abstract q62 join from separated data: `hDisc` supplies the both-disconnected branch, and
`hRigid_assemble` supplies mixed plus both-connected branches. -/
def q62_independence_of_hDisc_hRigidData_formal_proof :=
  @Bottcher.q62_independence_of_hDisc_hRigidData

/-- Concrete connected q62 bridge: direct `phiMero` transcendence plus
`TranscendentalOverAdjoin (phiMero c₁) (phiMero c₂)` closes the connected case. -/
def q62_connected_phiMero_transcendentalOverAdjoin_formal_proof :=
  @Bottcher.q62_independence_connected_phiMero_of_transcendentalOverAdjoin

/-- Top-level q62 case split: hDisc discharges both-disconnected parameters and the assembled hRigid
slot discharges all cases where at least one parameter is connected. -/
def q62_top_case_split_formal_proof :=
  @Bottcher.q62_independence

/-- Card-name proof object for `q62-bottcher-independence-n2-all-parameters.md`.

This is the abstract all-parameter case-split theorem: hDisc supplies the disconnected branch and the
hRigid slot supplies the connected/mixed branch. -/
def q62_bottcher_independence_n2_all_parameters_formal_proof :=
  @Bottcher.q62_independence

/-- Order-only target for
`not-new-but-required/bottcher-dyadic-monodromy-finite-type-absence.md`. -/
def BottcherDyadicUnboundedOrderTarget : Prop :=
  ∀ d : ℕ, ∃ ζ : ℂ, d < orderOf ζ

/-- Formal wrapper: dyadic multipliers have unbounded order. -/
theorem bottcher_dyadic_monodromy_finite_type_absence_order :
    BottcherDyadicUnboundedOrderTarget :=
  Bottcher.exists_complex_orderOf_gt

/-- Card-name theorem for
`not-new-but-required/bottcher-dyadic-monodromy-finite-type-absence.md`. -/
theorem bottcher_dyadic_monodromy_finite_type_absence :
    BottcherDyadicUnboundedOrderTarget :=
  bottcher_dyadic_monodromy_finite_type_absence_order

/-- Carrier-level Prüfer order target in the cover-germ ring. -/
def BottcherCoverGermDyadicOrderTarget : Prop :=
  ∀ (c₁ c₂ : ℂ) (n m d : ℕ),
    ∃ (k : ℕ) (ζ : ℂ), ζ ^ (2 ^ k) = 1 ∧ ζ ≠ 0 ∧
      orderOf ((ζ : Bottcher.coverGerm c₁ c₂ n m)) = 2 ^ k ∧ d < 2 ^ k

/-- Formal wrapper: dyadic order tower transferred to the cover-germ carrier. -/
theorem bottcher_exact_pruefer_coverGerm_order :
    BottcherCoverGermDyadicOrderTarget := by
  intro c₁ c₂ n m d
  exact Bottcher.exists_dyadic_order_gt_coverGerm c₁ c₂ n m d

/-- Formal `monoF` coordinate datum from exact Prüfer monodromy on the
cover-germ carrier. -/
theorem bottcher_exact_pruefer_coverGerm_monoF
    (c₁ c₂ : ℂ) (m d : ℕ) :
    ∃ (k : ℕ) (ζ : ℂ) (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ k) = 1),
      d < orderOf ((ζ : Bottcher.coverGerm c₁ c₂ k m)) ∧
      Bottcher.deckGermEquiv hζ hpow (Bottcher.zGerm : Bottcher.coverGerm c₁ c₂ k m)
        = Bottcher.zGerm ∧
      Bottcher.deckGermEquiv hζ hpow (Bottcher.v2Germ : Bottcher.coverGerm c₁ c₂ k m)
        = Bottcher.v2Germ ∧
      Bottcher.deckGermEquiv hζ hpow ((ζ : Bottcher.coverGerm c₁ c₂ k m))
        = (ζ : Bottcher.coverGerm c₁ c₂ k m) ∧
      Bottcher.deckGermEquiv hζ hpow (Bottcher.v1Germ : Bottcher.coverGerm c₁ c₂ k m)
        = (ζ : Bottcher.coverGerm c₁ c₂ k m) * Bottcher.v1Germ :=
  Bottcher.coverGerm_monoF_datum c₁ c₂ m d

/-- Formal `monoG` coordinate datum from exact Prüfer monodromy on the
cover-germ carrier. -/
theorem bottcher_exact_pruefer_coverGerm_monoG
    (c₁ c₂ : ℂ) (n d : ℕ) :
    ∃ (k : ℕ) (ζ : ℂ) (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ k) = 1),
      d < orderOf ((ζ : Bottcher.coverGerm c₁ c₂ n k)) ∧
      Bottcher.deckGermEquiv₂ hζ hpow (Bottcher.zGerm : Bottcher.coverGerm c₁ c₂ n k)
        = Bottcher.zGerm ∧
      Bottcher.deckGermEquiv₂ hζ hpow (Bottcher.v1Germ : Bottcher.coverGerm c₁ c₂ n k)
        = Bottcher.v1Germ ∧
      Bottcher.deckGermEquiv₂ hζ hpow ((ζ : Bottcher.coverGerm c₁ c₂ n k))
        = (ζ : Bottcher.coverGerm c₁ c₂ n k) ∧
      Bottcher.deckGermEquiv₂ hζ hpow (Bottcher.v2Germ : Bottcher.coverGerm c₁ c₂ n k)
        = (ζ : Bottcher.coverGerm c₁ c₂ n k) * Bottcher.v2Germ :=
  Bottcher.coverGerm_monoG_datum c₁ c₂ n d

/-- Period-to-order target for the Böttcher exact-monodromy pipeline. -/
def BottcherPeriodMultiplierOrderTarget : Prop :=
  ∀ (μ : Measure ℂ), IsFiniteMeasure μ →
  ∀ {c : ℂ} {R : ℝ} (n : ℕ), 0 ≤ R → μ (sphere c R) = 0 →
    Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap c R) θ • (circleMap c R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod μ) →
    (μ (ball c R)).toReal = (((2 ^ n : ℕ) : ℝ))⁻¹ →
    orderOf (Complex.exp (∮ z in C(c, R), ∫ ζ, (z - ζ)⁻¹ ∂μ)) = 2 ^ n

/-- Formal wrapper: period `2πi / 2^n` gives multiplier order `2^n`. -/
theorem bottcher_exact_pruefer_period_multiplier_order :
    BottcherPeriodMultiplierOrderTarget := by
  intro μ hfinite c R n h0 hsphere hint hmass
  letI : IsFiniteMeasure μ := hfinite
  exact Bottcher.multiplier_orderOf_of_mass μ n h0 hsphere hint hmass

/-! ## q62 both-disconnected / hDisc branch -/

/-- The non-hRigid hDisc tower target used by
`q62-both-disconnected.md` and the disconnected branch of
`q62-bottcher-independence-n2-all-parameters.md`. -/
def Q62HDiscFixedInverseTowerTarget (c₁ c₂ : ℂ) : Prop :=
  (∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
    (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
    ∀ d : ℕ,
      ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ),
        n = d + 1 ∧
        max 2 ‖c₁‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        concreteAnnulusHLiftFOutputWithFixedInverse c₂ ψ₁ n d R' hR'pos) ∧
  (∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₂ : ℂ → ℂ),
    (∀ d : ℕ, coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R') ∧
    ∀ d : ℕ,
      ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ),
        n = d + 1 ∧
        max 2 ‖c₂‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        concreteAnnulusHLiftGOutputWithFixedInverse c₁ ψ₂ n d R' hR'pos)

/-- Formal wrapper for the completed hDisc loop/deck tower, excluding the hRigid branch. -/
theorem q62_both_disconnected_hdisc_fixed_inverse_towers (c₁ c₂ : ℂ) :
    Q62HDiscFixedInverseTowerTarget c₁ c₂ :=
  Bottcher.exteriorAnnulus_loop_and_uniform_hliftFG_towers_with_fixed_inverse c₁ c₂

/-- Card-name theorem for `q62-both-disconnected.md`: the completed non-hRigid hDisc loop/deck
tower used by the disconnected q62 close. -/
theorem q62_both_disconnected (c₁ c₂ : ℂ) :
    Q62HDiscFixedInverseTowerTarget c₁ c₂ :=
  q62_both_disconnected_hdisc_fixed_inverse_towers c₁ c₂

/-- Constructed hDisc uniform two-direction z-fixing deck towers.  This is a raw
non-hRigid construction object below the q62 disconnected close. -/
def q62_hdisc_uniform_two_zfixing_deck_towers_formal_proof :=
  @Bottcher.exteriorAnnulus_loop_and_uniform_two_zfixing_deck_towers

/-- Constructed hDisc full per-depth z-fixing/monoFG package with nonzero moving coordinates. -/
def q62_hdisc_full_zfixing_monoFG_steps_formal_proof :=
  @Bottcher.exteriorAnnulus_loop_and_full_zfixing_monoFG_steps

/-- Existing hDisc deep-data close for q62; exposed as a Lean object so the card
mapping has a stable name without importing the hRigid path. -/
def q62_both_disconnected_deep_data_escape_formal_proof :=
  @Bottcher.q62_disconnected_of_deepData_escape

/-- Topological image-winding hDisc close for q62; the analytic radicand-period condition is derived
from the image-loop winding bridge before applying the existing deep-data close. -/
def q62_both_disconnected_image_winding_deep_data_escape_formal_proof :=
  @Bottcher.q62_disconnected_of_imageWindingDeepData_escape

/-- Existing additive loop/deck close for q62 both-disconnected; exposed for the
same card mapping. -/
def q62_both_disconnected_additive_loop_deck_formal_proof :=
  @Bottcher.q62_independence_disconnected_of_dyadic_additive_loop_and_two_zfixing_decks

/-- Existing vertical-strip loop/deck close for q62 both-disconnected; exposed for
the same card mapping. -/
def q62_both_disconnected_vertical_strip_loop_deck_formal_proof :=
  @Bottcher.q62_independence_disconnected_of_dyadic_verticalStrip_loop_and_two_zfixing_decks

/-! ## q62 connected / hRigid branch surfaces -/

/-- Connected rightmost geometry brick: every quadratic filled Julia set has a rightmost frontier
point whose strict right-half-plane slices are preconnected basin-side sectors. This is a seed for
the hRigid local-topology lane, not the full local-tip conclusion. -/
def q62_connected_rightmost_frontier_rightHalfplane_basin_sector_formal_proof :=
  @Bottcher.exists_rightmost_frontier_rightHalfplane_basin_sector

/-- Connected q62 geometry seed: distinct parameters give, after possible swap, a Julia-frontier point
off the other filled Julia set, plus an other-basin ball and a nontrivial frontier-side basin filter. -/
def q62_connected_frontier_off_other_basin_seed_formal_proof :=
  @Bottcher.exists_frontier_filledJulia_off_other_with_basin_ball

/-- Local-radius natural-boundary obstruction for a separable algebraic relation: continuation only
needs one positive preconnected lens radius. -/
def q62_connected_no_separable_relation_naturalBoundary_localLens_formal_proof :=
  @BottcherIndep.no_separable_relation_of_natural_boundary_localLens

/-- Local-radius `ℂ(z)[g]` natural-boundary obstruction for the Böttcher capstone. -/
def q62_connected_no_phi_relation_naturalBoundary_localLens_formal_proof :=
  @BottcherIndep.no_phi_relation_of_natural_boundary_localLens

/-- Local-radius countable-avoidance Böttcher capstone with an explicit bad-locus countability input. -/
def q62_connected_phi_indep_capstone_countableAvoidance_localLens_formal_proof :=
  @BottcherIndep.phi_indep_capstone_countableAvoidance_localLens

/-- Local-radius uncountable-target Böttcher capstone with an explicit bad-locus countability input. -/
def q62_connected_phi_indep_capstone_uncountable_bad_localLens_formal_proof :=
  @BottcherIndep.phi_indep_capstone_uncountable_bad_localLens

/-- Local-radius countable-avoidance Böttcher capstone whose analytic bad locus is generated
internally from one full-degree separable witness in the analytic region. -/
def q62_connected_phi_indep_capstone_countableAvoidance_localLens_analyticBad_formal_proof :=
  @Bottcher.phi_indep_capstone_countableAvoidance_localLens_of_analytic_bad_locus

/-- Local-radius uncountable-target Böttcher capstone whose analytic bad locus is generated internally
from one full-degree separable witness in the analytic region. -/
def q62_connected_phi_indep_capstone_uncountable_localLens_analyticBad_formal_proof :=
  @Bottcher.phi_indep_capstone_uncountable_localLens_of_analytic_bad_locus

/-- Natural-boundary connected `NoRelation` endpoint using countable-avoidance sparse crossing and
common-basin geometry. -/
def q62_connected_noRelation_naturalBoundary_gamma_offOther_countableAvoidance_formal_proof :=
  @Bottcher.noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance

/-- hRigid endpoint using countable-avoidance sparse crossing and common-basin geometry. -/
def hrig_phiMero_naturalBoundary_gamma_offOther_countableAvoidance_formal_proof :=
  @Bottcher.hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance

/-- Connected q62 endpoint using countable-avoidance sparse crossing and common-basin geometry. -/
def q62_connected_naturalBoundary_gamma_offOther_countableAvoidance_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance

/-- Natural-boundary connected `NoRelation` endpoint using countable-avoidance sparse crossing and
local-radius common-basin geometry. -/
def q62_connected_noRelation_naturalBoundary_gamma_offOther_countableAvoidance_localTip_formal_proof :=
  @Bottcher.noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localTip

/-- hRigid endpoint using countable-avoidance sparse crossing and local-radius common-basin geometry. -/
def hrig_phiMero_naturalBoundary_gamma_offOther_countableAvoidance_localTip_formal_proof :=
  @Bottcher.hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localTip

/-- Connected q62 endpoint using countable-avoidance sparse crossing and local-radius common-basin geometry. -/
def q62_connected_naturalBoundary_gamma_offOther_countableAvoidance_localTip_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localTip

/-- Natural-boundary `NoRelation` endpoint using countable avoidance, carrier-closure contact, and
punctured-sector preconnectedness; the common-basin component is built internally. -/
def q62_connected_noRelation_naturalBoundary_gamma_offOther_countableAvoidance_carrierClosure_formal_proof :=
  @Bottcher.noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosure

/-- Natural-boundary hRigid endpoint using countable avoidance, carrier-closure contact, and
punctured-sector preconnectedness; the common-basin component is built internally. -/
def hrig_phiMero_naturalBoundary_gamma_offOther_countableAvoidance_carrierClosure_formal_proof :=
  @Bottcher.hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosure

/-- Natural-boundary connected q62 endpoint using countable avoidance, carrier-closure contact, and
punctured-sector preconnectedness; the common-basin component is built internally. -/
def q62_connected_naturalBoundary_gamma_offOther_countableAvoidance_carrierClosure_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosure

/-- Natural-boundary `NoRelation` endpoint using countable avoidance, carrier-closure contact, and
local-radius punctured-sector preconnectedness; the common-basin component is built internally. -/
def q62_connected_noRelation_naturalBoundary_gamma_offOther_countableAvoidance_carrierClosureLocalTip_formal_proof :=
  @Bottcher.noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip

/-- Natural-boundary hRigid endpoint using countable avoidance, carrier-closure contact, and
local-radius punctured-sector preconnectedness; the common-basin component is built internally. -/
def hrig_phiMero_naturalBoundary_gamma_offOther_countableAvoidance_carrierClosureLocalTip_formal_proof :=
  @Bottcher.hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip

/-- Natural-boundary connected q62 endpoint using countable avoidance, carrier-closure contact, and
local-radius punctured-sector preconnectedness; the common-basin component is built internally. -/
def q62_connected_naturalBoundary_gamma_offOther_countableAvoidance_carrierClosureLocalTip_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip

/-- Natural-boundary `NoRelation` endpoint using countable-avoidance translated-slit sector targets;
the punctured-sector preconnectedness input is derived internally. -/
def q62_connected_noRelation_naturalBoundary_gamma_offOther_countableAvoidance_carrierClosureSlitSector_formal_proof :=
  @Bottcher.noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector

/-- Natural-boundary hRigid endpoint using countable-avoidance translated-slit sector targets; the
punctured-sector preconnectedness input is derived internally. -/
def hrig_phiMero_naturalBoundary_gamma_offOther_countableAvoidance_carrierClosureSlitSector_formal_proof :=
  @Bottcher.hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector

/-- Natural-boundary connected q62 endpoint using countable-avoidance translated-slit sector targets;
the punctured-sector preconnectedness input is derived internally. -/
def q62_connected_naturalBoundary_gamma_offOther_countableAvoidance_carrierClosureSlitSector_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector

/-- Natural-boundary `NoRelation` endpoint with countable avoidance and local-radius rotated slit sectors. -/
def q62_connected_noRelation_naturalBoundary_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip_formal_proof :=
  @Bottcher.noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip

/-- Natural-boundary hRigid endpoint with countable avoidance and local-radius rotated slit sectors. -/
def hrig_phiMero_naturalBoundary_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip_formal_proof :=
  @Bottcher.hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip

/-- Natural-boundary connected q62 endpoint with countable avoidance and local-radius rotated slit sectors. -/
def q62_connected_naturalBoundary_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip

/-- Natural-boundary `NoRelation` endpoint using uncountably many all-scale rotated-slit-good frontier
targets. -/
def q62_connected_noRelation_naturalBoundary_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable_formal_proof :=
  @Bottcher.noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable

/-- Natural-boundary hRigid endpoint using uncountably many all-scale rotated-slit-good frontier targets. -/
def hrig_phiMero_naturalBoundary_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable_formal_proof :=
  @Bottcher.hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable

/-- Natural-boundary connected q62 endpoint using uncountably many all-scale rotated-slit-good frontier
targets. -/
def q62_connected_naturalBoundary_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable

/-- Natural-boundary `NoRelation` endpoint using uncountably many local-radius rotated-slit-good frontier
targets. -/
def q62_connected_noRelation_naturalBoundary_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip_formal_proof :=
  @Bottcher.noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip

/-- Natural-boundary hRigid endpoint using uncountably many local-radius rotated-slit-good frontier targets. -/
def hrig_phiMero_naturalBoundary_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip_formal_proof :=
  @Bottcher.hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip

/-- Natural-boundary connected q62 endpoint using uncountably many local-radius rotated-slit-good frontier
targets. -/
def q62_connected_naturalBoundary_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip

/-- Natural-boundary `NoRelation` endpoint using uncountably many translated-slit-good local frontier
targets; countable avoidance and punctured-sector preconnectedness are built internally. -/
def q62_connected_noRelation_naturalBoundary_gamma_offOther_countableAvoidance_localFrontierSlitUncountable_formal_proof :=
  @Bottcher.noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable

/-- Natural-boundary hRigid endpoint using uncountably many translated-slit-good local frontier targets;
countable avoidance and punctured-sector preconnectedness are built internally. -/
def hrig_phiMero_naturalBoundary_gamma_offOther_countableAvoidance_localFrontierSlitUncountable_formal_proof :=
  @Bottcher.hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable

/-- Natural-boundary connected q62 endpoint using uncountably many translated-slit-good local frontier
targets; countable avoidance and punctured-sector preconnectedness are built internally. -/
def q62_connected_naturalBoundary_gamma_offOther_countableAvoidance_localFrontierSlitUncountable_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable

/-- Empty-interior `NoRelation` endpoint using countable avoidance, carrier-closure contact, and
punctured-sector preconnectedness; the common-basin component is built internally. -/
def q62_connected_noRelation_emptyInterior_gamma_offOther_countableAvoidance_carrierClosure_formal_proof :=
  @Bottcher.noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosure

/-- Empty-interior hRigid endpoint using countable avoidance, carrier-closure contact, and
punctured-sector preconnectedness; the common-basin component is built internally. -/
def hrig_phiMero_emptyInterior_gamma_offOther_countableAvoidance_carrierClosure_formal_proof :=
  @Bottcher.hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosure

/-- Empty-interior connected q62 endpoint using countable avoidance, carrier-closure contact, and
punctured-sector preconnectedness; the common-basin component is built internally. -/
def q62_connected_emptyInterior_gamma_offOther_countableAvoidance_carrierClosure_formal_proof :=
  @Bottcher.q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosure

/-- Empty-interior `NoRelation` endpoint using countable-avoidance slit-sector targets; the
punctured-sector preconnectedness input is derived internally. -/
def q62_connected_noRelation_emptyInterior_gamma_offOther_countableAvoidance_carrierClosureSlitSector_formal_proof :=
  @Bottcher.noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector

/-- Empty-interior hRigid endpoint using countable-avoidance slit-sector targets; the
punctured-sector preconnectedness input is derived internally. -/
def hrig_phiMero_emptyInterior_gamma_offOther_countableAvoidance_carrierClosureSlitSector_formal_proof :=
  @Bottcher.hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector

/-- Empty-interior connected q62 endpoint using countable-avoidance slit-sector targets; the
punctured-sector preconnectedness input is derived internally. -/
def q62_connected_emptyInterior_gamma_offOther_countableAvoidance_carrierClosureSlitSector_formal_proof :=
  @Bottcher.q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector

/-- Empty-interior `NoRelation` endpoint using a local perfect-frontier
countable-avoidance target set, with the common-basin component built internally. -/
def q62_connected_noRelation_emptyInterior_gamma_offOther_countableAvoidance_localFrontierTarget_formal_proof :=
  @Bottcher.noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTarget

/-- Empty-interior hRigid endpoint using a local perfect-frontier countable-avoidance
target set, with the common-basin component built internally. -/
def hrig_phiMero_emptyInterior_gamma_offOther_countableAvoidance_localFrontierTarget_formal_proof :=
  @Bottcher.hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTarget

/-- Empty-interior connected q62 endpoint using a local perfect-frontier
countable-avoidance target set, with the common-basin component built internally. -/
def q62_connected_emptyInterior_gamma_offOther_countableAvoidance_localFrontierTarget_formal_proof :=
  @Bottcher.q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTarget

/-- Empty-interior `NoRelation` endpoint using uncountably many local translated-slit-good frontier
targets; countable avoidance and punctured-sector preconnectedness are built internally. -/
def q62_connected_noRelation_emptyInterior_gamma_offOther_countableAvoidance_localFrontierSlitUncountable_formal_proof :=
  @Bottcher.noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable

/-- Empty-interior hRigid endpoint using uncountably many local translated-slit-good frontier targets;
countable avoidance and punctured-sector preconnectedness are built internally. -/
def hrig_phiMero_emptyInterior_gamma_offOther_countableAvoidance_localFrontierSlitUncountable_formal_proof :=
  @Bottcher.hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable

/-- Empty-interior connected q62 endpoint using uncountably many local translated-slit-good frontier
targets; countable avoidance and punctured-sector preconnectedness are built internally. -/
def q62_connected_emptyInterior_gamma_offOther_countableAvoidance_localFrontierSlitUncountable_formal_proof :=
  @Bottcher.q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable

/-- Formal obstruction to the all-scale translated-slit supply interface: among points of a carrier
`K`, the all-scale translated-slit basin condition is subsingleton. -/
def q62_connected_allScaleTranslatedSlitSupply_subsingleton_obstruction_formal_proof :=
  @Bottcher.subsingleton_mem_all_scale_translated_slitPlane_subset_compl

/-- Card-facing obstruction to the current uncountable local-frontier translated-slit supply: after
intersecting with any local set, off-other condition, and analytic region, the all-scale slit-good
filled-Julia frontier targets are countable. -/
def q62_connected_localFrontierSlitUncountable_allScale_obstruction_formal_proof :=
  @Bottcher.countable_local_frontier_offOther_all_scale_translated_slitPlane_subset_compl_filledJulia

/-- Rotated translated-slit local topology brick: a unit-rotated slit-sector basin inclusion at every
scale gives the full local `htip` preconnectedness. -/
def q62_connected_rotatedSlitSector_localTip_formal_proof :=
  @Bottcher.local_tip_preconnected_of_rotated_translated_slitPlane_subset_compl

/-- Local-radius rotated translated-slit topology brick: a unit-rotated slit-sector basin inclusion
below a radius gives `htip` below that radius, avoiding the all-scale ray obstruction. -/
def q62_connected_rotatedSlitSector_localRadiusTip_formal_proof :=
  @Bottcher.local_tip_preconnected_of_rotated_translated_slitPlane_subset_compl_le

/-- Local-radius branch-continuation bridge: branch-family continuation only needs `htip` below some
positive radius, not at all scales. -/
def q62_connected_branchContinuation_localRadiusTip_formal_proof :=
  @Bottcher.continuesAcross_of_global_basin_branch_analytic_localTip

/-- Cross-ratio/Montel source brick: differentiability of the cross-ratio iterate on the local patch. -/
def hrig_differentiableOn_crossRatio_iterate_formal_proof :=
  @Bottcher.differentiableOn_crossRatio_iterate

/-- Cross-ratio/Montel algebra brick: a genuine cross-ratio value has nonzero inverse-Möbius
denominator. -/
def hrig_crossRatio_solve_den_ne_zero_formal_proof :=
  @Bottcher.crossRatio_solve_den_ne_zero

/-- Cross-ratio/Montel algebra brick: the inverse-Möbius transform recovers the target value from
its cross-ratio. -/
def hrig_crossRatio_solve_w_formal_proof :=
  @Bottcher.crossRatio_solve_w

/-- Cross-ratio/Montel algebra brick: the inverse-Möbius transform recovers the quadratic iterate
from its cross-ratio value. -/
def hrig_crossRatio_iterate_solve_formal_proof :=
  @Bottcher.crossRatio_iterate_solve

/-- Cross-ratio/Montel algebra brick: the inverse-Möbius denominator is nonzero for a quadratic
iterate cross-ratio value. -/
def hrig_crossRatio_iterate_solve_den_ne_zero_formal_proof :=
  @Bottcher.crossRatio_iterate_solve_den_ne_zero

/-- Cross-ratio/Montel bridge: the inverse-Möbius transform used to pass from cross-ratio values
back to iterate values. -/
def hrig_crossRatioInverse_formal_proof :=
  @Bottcher.crossRatioInverse

/-- Cross-ratio/Montel bridge: on a local patch where `R` is the genuine iterate cross-ratio, the
inverse-Möbius transform recovers the iterate. -/
def hrig_eqOn_iterate_eq_crossRatioInverse_formal_proof :=
  @Bottcher.eqOn_iterate_eq_crossRatioInverse

/-- Cross-ratio/Montel bridge: the inverse-Möbius denominator is nonzero on such a local patch. -/
def hrig_eqOn_crossRatioInverse_den_ne_zero_formal_proof :=
  @Bottcher.eqOn_crossRatioInverse_den_ne_zero

/-- Cross-ratio/Montel bridge: family form of the local-patch iterate recovery theorem. -/
def hrig_forall_eqOn_iterate_eq_crossRatioInverse_formal_proof :=
  @Bottcher.forall_eqOn_iterate_eq_crossRatioInverse

/-- Cross-ratio/Montel bridge: family form of the local-patch denominator nonzero theorem. -/
def hrig_forall_crossRatioInverse_den_ne_zero_formal_proof :=
  @Bottcher.forall_crossRatioInverse_den_ne_zero

/-- Cross-ratio/Montel source brick: absence of a period-`n` fixed point makes the cross-ratio
iterate avoid `1`. -/
def hrig_crossRatio_iterate_ne_one_of_not_periodic_formal_proof :=
  @Bottcher.crossRatio_iterate_ne_one_of_not_periodic

/-- Cross-ratio/Montel source brick: the local avoidance hypotheses make the cross-ratio iterate
avoid `0`. -/
def hrig_crossRatio_iterate_ne_zero_of_avoids_formal_proof :=
  @Bottcher.crossRatio_iterate_ne_zero_of_avoids

/-- Cross-ratio/Montel source brick: the local patch map omits both `0` and `1`. -/
def hrig_crossRatio_iterate_omits_zero_one_on_formal_proof :=
  @Bottcher.crossRatio_iterate_omits_zero_one_on

/-- Rotated translated-slit local topology brick: every positive-radius tip ball contains
a point of the rotated slit sector. -/
def q62_connected_rotatedSlitSector_nonempty_formal_proof :=
  @Bottcher.nonempty_ball_inter_rotated_translated_slitPlane

/-- Dense-approach hRigid obstruction bridge: a local-radius rotated slit-sector basin inclusion
supplies the dense preconnected approach model directly, without first proving full punctured-basin
preconnectedness. -/
def q62_connected_rotatedSlitSector_denseApproach_contradiction_formal_proof :=
  @Bottcher.false_of_global_basin_branch_analytic_rotatedSlitDenseApproach

/-- Dense-approach `NoRelation` endpoint: countable avoidance plus a common-basin dense approach
model at the selected target gives the connected relative relation obstruction. -/
def q62_connected_noRelation_commonBasin_gamma_offOther_countableAvoidance_denseApproach_formal_proof :=
  @Bottcher.noRelation_phiMero_of_commonBasin_gamma_offOther_countableAvoidance_denseApproach

/-- Dense-approach hRigid endpoint: countable avoidance plus a common-basin dense approach model
at the selected target gives the relative hRigid proof object. -/
def hrig_phiMero_commonBasin_gamma_offOther_countableAvoidance_denseApproach_formal_proof :=
  @Bottcher.hrig_phiMero_of_commonBasin_gamma_offOther_countableAvoidance_denseApproach

/-- Dense-approach connected q62 endpoint: countable avoidance plus a common-basin dense approach
model at the selected target gives the connected q62 relation obstruction. -/
def q62_connected_commonBasin_gamma_offOther_countableAvoidance_denseApproach_formal_proof :=
  @Bottcher.q62_independence_connected_of_commonBasin_gamma_offOther_countableAvoidance_denseApproach

/-- Rotated-slit dense-approach `NoRelation` endpoint: countable avoidance plus a local
common-basin rotated slit sector supplies the dense approach model internally. -/
def q62_connected_noRelation_commonBasin_gamma_offOther_countableAvoidance_rotatedSlitDenseApproach_formal_proof :=
  @Bottcher.noRelation_phiMero_of_commonBasin_gamma_offOther_countableAvoidance_rotatedSlitDenseApproach

/-- Rotated-slit dense-approach hRigid endpoint: countable avoidance plus a local common-basin
rotated slit sector supplies the dense approach model internally. -/
def hrig_phiMero_commonBasin_gamma_offOther_countableAvoidance_rotatedSlitDenseApproach_formal_proof :=
  @Bottcher.hrig_phiMero_of_commonBasin_gamma_offOther_countableAvoidance_rotatedSlitDenseApproach

/-- Rotated-slit dense-approach connected q62 endpoint: countable avoidance plus a local
common-basin rotated slit sector supplies the dense approach model internally. -/
def q62_connected_commonBasin_gamma_offOther_countableAvoidance_rotatedSlitDenseApproach_formal_proof :=
  @Bottcher.q62_independence_connected_of_commonBasin_gamma_offOther_countableAvoidance_rotatedSlitDenseApproach

/-- Empty-interior `NoRelation` endpoint with countable avoidance and carrier-closure local-tip geometry. -/
def q62_connected_noRelation_emptyInterior_gamma_offOther_countableAvoidance_carrierClosureLocalTip_formal_proof :=
  @Bottcher.noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip

/-- Empty-interior hRigid endpoint with countable avoidance and carrier-closure local-tip geometry. -/
def hrig_phiMero_emptyInterior_gamma_offOther_countableAvoidance_carrierClosureLocalTip_formal_proof :=
  @Bottcher.hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip

/-- Empty-interior connected q62 endpoint with countable avoidance and carrier-closure local-tip geometry. -/
def q62_connected_emptyInterior_gamma_offOther_countableAvoidance_carrierClosureLocalTip_formal_proof :=
  @Bottcher.q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip

/-- Empty-interior `NoRelation` endpoint with countable avoidance and local-radius rotated slit sectors. -/
def q62_connected_noRelation_emptyInterior_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip_formal_proof :=
  @Bottcher.noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip

/-- Empty-interior hRigid endpoint with countable avoidance and local-radius rotated slit sectors. -/
def hrig_phiMero_emptyInterior_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip_formal_proof :=
  @Bottcher.hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip

/-- Empty-interior connected q62 endpoint with countable avoidance and local-radius rotated slit sectors. -/
def q62_connected_emptyInterior_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip_formal_proof :=
  @Bottcher.q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip

/-- Empty-interior `NoRelation` endpoint using uncountably many local all-scale rotated-slit-good
frontier targets; countable avoidance and punctured-sector preconnectedness are built internally. -/
def q62_connected_noRelation_emptyInterior_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable_formal_proof :=
  @Bottcher.noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable

/-- Empty-interior hRigid endpoint using uncountably many local all-scale rotated-slit-good frontier
targets; countable avoidance and punctured-sector preconnectedness are built internally. -/
def hrig_phiMero_emptyInterior_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable_formal_proof :=
  @Bottcher.hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable

/-- Empty-interior connected q62 endpoint using uncountably many local all-scale rotated-slit-good
frontier targets; countable avoidance and punctured-sector preconnectedness are built internally. -/
def q62_connected_emptyInterior_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable_formal_proof :=
  @Bottcher.q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable

/-- Empty-interior `NoRelation` endpoint using uncountably many local-radius rotated-slit-good frontier
targets. -/
def q62_connected_noRelation_emptyInterior_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip_formal_proof :=
  @Bottcher.noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip

/-- Empty-interior hRigid endpoint using uncountably many local-radius rotated-slit-good frontier targets. -/
def hrig_phiMero_emptyInterior_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip_formal_proof :=
  @Bottcher.hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip

/-- Empty-interior connected q62 endpoint using uncountably many local-radius rotated-slit-good frontier
targets. -/
def q62_connected_emptyInterior_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip_formal_proof :=
  @Bottcher.q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip

/-- Empty-interior `NoRelation` endpoint using a local translated-slit basin sector; the
punctured-sector preconnectedness input is derived internally. -/
def q62_connected_noRelation_emptyInterior_gamma_offOther_countableAvoidance_localFrontierSlitModel_formal_proof :=
  @Bottcher.noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitModel

/-- Empty-interior hRigid endpoint using a local translated-slit basin sector; the
punctured-sector preconnectedness input is derived internally. -/
def hrig_phiMero_emptyInterior_gamma_offOther_countableAvoidance_localFrontierSlitModel_formal_proof :=
  @Bottcher.hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitModel

/-- Empty-interior connected q62 endpoint using a local translated-slit basin sector; the
punctured-sector preconnectedness input is derived internally. -/
def q62_connected_emptyInterior_gamma_offOther_countableAvoidance_localFrontierSlitModel_formal_proof :=
  @Bottcher.q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitModel

/-- Natural-boundary `NoRelation` endpoint using pointwise local-radius rotated slit-sector frontier
models; the countable-avoidance target set and local-tip geometry are built internally. -/
def q62_connected_noRelation_naturalBoundary_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip_formal_proof :=
  @Bottcher.noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip

/-- Natural-boundary hRigid endpoint using pointwise local-radius rotated slit-sector frontier models. -/
def hrig_phiMero_naturalBoundary_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip_formal_proof :=
  @Bottcher.hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip

/-- Natural-boundary connected q62 endpoint using pointwise local-radius rotated slit-sector frontier
models. -/
def q62_connected_naturalBoundary_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip

/-- Empty-interior `NoRelation` endpoint using pointwise local-radius rotated slit-sector frontier
models; the countable-avoidance target set and local-tip geometry are built internally. -/
def q62_connected_noRelation_emptyInterior_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip_formal_proof :=
  @Bottcher.noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip

/-- Empty-interior hRigid endpoint using pointwise local-radius rotated slit-sector frontier models. -/
def hrig_phiMero_emptyInterior_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip_formal_proof :=
  @Bottcher.hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip

/-- Empty-interior connected q62 endpoint using pointwise local-radius rotated slit-sector frontier
models. -/
def q62_connected_emptyInterior_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip_formal_proof :=
  @Bottcher.q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip

/-- Empty-interior `NoRelation` endpoint using pointwise local-radius rotated slit-sector frontier
models through the dense-approach obstruction, so the local target set is selected internally. -/
def q62_connected_noRelation_emptyInterior_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelDenseApproach_formal_proof :=
  @Bottcher.noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelDenseApproach

/-- Empty-interior hRigid endpoint using pointwise local-radius rotated slit-sector frontier models
through the dense-approach obstruction. -/
def hrig_phiMero_emptyInterior_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelDenseApproach_formal_proof :=
  @Bottcher.hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelDenseApproach

/-- Empty-interior connected q62 endpoint using pointwise local-radius rotated slit-sector frontier
models through the dense-approach obstruction. -/
def q62_connected_emptyInterior_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelDenseApproach_formal_proof :=
  @Bottcher.q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelDenseApproach

/-- Strongest current natural-boundary connected q62 endpoint: square-root level
branches plus off-other crossing data, with the repelling second-map witnesses
promoted to eventual support input. -/
def q62_connected_naturalBoundary_sqrt_family_offOther_crossing_eventualG_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_eventualG

/-- Empty-interior counterpart of the connected q62 endpoint, derived through
the natural-boundary bridge. -/
def q62_connected_emptyInterior_sqrt_family_offOther_crossing_eventualG_formal_proof :=
  @Bottcher.q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing_eventualG

/-- Natural-boundary connected q62 endpoint consuming the newer return-order hRigid payload. -/
def q62_connected_naturalBoundary_sqrt_family_offOther_crossing_returnOrderG_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_returnOrderG

/-- Empty-interior connected q62 endpoint consuming the newer return-order hRigid payload. -/
def q62_connected_emptyInterior_sqrt_family_offOther_crossing_returnOrderG_formal_proof :=
  @Bottcher.q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing_returnOrderG

/-- Natural-boundary connected q62 endpoint consuming the root-of-unity-safe multiplier-one-period
hRigid payload. -/
def q62_connected_naturalBoundary_sqrt_family_offOther_crossing_multiplierOnePeriodG_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_multiplierOnePeriodG

/-- Empty-interior connected q62 endpoint consuming the root-of-unity-safe multiplier-one-period
hRigid payload. -/
def q62_connected_emptyInterior_sqrt_family_offOther_crossing_multiplierOnePeriodG_formal_proof :=
  @Bottcher.q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing_multiplierOnePeriodG

/-- Natural-boundary connected q62 endpoint consuming eventual bounds on exact multiplier-one periods
and non-strong-root cardinality. -/
def q62_connected_naturalBoundary_sqrt_family_offOther_crossing_exactMultiplierOnePeriodBoundCardG_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_exactMultiplierOnePeriodBoundCardG

/-- Card-name proof object for `q62-bottcher-independence-natural-boundary.md`.

This records the strongest current natural-boundary connected branch endpoint exposed in Lean. -/
def q62_bottcher_independence_natural_boundary_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_exactMultiplierOnePeriodBoundCardG

/-- Card-name proof object for `q62a-bottcher-independence-hyperbolic.md`.

The hyperbolic card is represented by the same current natural-boundary connected branch endpoint;
the theorem name below is the stable card-facing handle. -/
def q62a_bottcher_independence_hyperbolic_formal_proof :=
  @Bottcher.q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_exactMultiplierOnePeriodBoundCardG

/-- Empty-interior connected q62 endpoint consuming eventual bounds on exact multiplier-one periods
and non-strong-root cardinality. -/
def q62_connected_emptyInterior_sqrt_family_offOther_crossing_exactMultiplierOnePeriodBoundCardG_formal_proof :=
  @Bottcher.q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing_exactMultiplierOnePeriodBoundCardG

/-- Absolute connected `φ_c` hRigid bridge from the root-of-unity-safe multiplier-one-period support
predicate.  This is the general parabolic-support input now targeted by the connected q62 route. -/
def hrig_phiMero_multiplierOnePeriod_support_formal_proof :=
  @Bottcher.phiMero_transcendental_of_repelling_eventually_multiplierOnePeriod_contentDenominator_noExtra_input

/-- Absolute connected `φ_c` hRigid bridge from an eventual bound on exact multiplier-one periods
plus finite eventual non-strong support. -/
def hrig_phiMero_exactMultiplierOnePeriodBound_formal_proof :=
  @Bottcher.phiMero_transcendental_of_repelling_eventually_exactMultiplierOnePeriodBound_contentDenominator_noExtra_input

/-- Absolute connected `φ_c` hRigid bridge from eventual bounds on exact multiplier-one periods and
the cardinality of non-strong roots. -/
def hrig_phiMero_exactMultiplierOnePeriodBound_cardBound_formal_proof :=
  @Bottcher.phiMero_transcendental_of_repelling_eventually_exactMultiplierOnePeriodBound_cardBound_contentDenominator_noExtra_input

/-- Strong-root source bridge: frequent unbounded cardinality of strong fixed-point roots yields an
infinite global strong-periodic target set. -/
def hrig_infinite_strongFixedPointRoots_union_of_frequently_card_gt_formal_proof :=
  @Bottcher.infinite_strongFixedPointRoots_union_of_frequently_card_gt

/-- Strong-root source bridge: frequent unbounded strong fixed-point roots yield a Julia-frontier
accumulation point for the global strong-periodic target set. -/
def hrig_frontier_accumulation_of_frequently_strongFixedPointRoots_card_gt_formal_proof :=
  @Bottcher.exists_frontier_accumulation_of_frequently_strongFixedPointRoots_card_gt

/-- Localizer bridge: a strong-periodic accumulation point in the interior of a target region yields
an infinite closed-ball strong-periodic supply inside that region. -/
def hrig_closedBall_strongly_repelling_periodic_set_of_accPt_in_interior_formal_proof :=
  @Bottcher.exists_closedBall_strongly_repelling_periodic_set_of_accPt_in_interior

/-- Localizer bridge: perfect Julia frontier plus dense strong fixed roots yields an infinite
closed-ball strong-periodic supply inside an interior target region. -/
def hrig_closedBall_strongFixedPointRoots_supply_of_perfect_frontier_dense_formal_proof :=
  @Bottcher.exists_closedBall_strongFixedPointRoots_supply_of_perfect_frontier_dense

/-- Localizer bridge: connected empty-interior Julia set plus dense strong fixed roots yields an
infinite closed-ball strong-periodic supply inside an interior target region. -/
def hrig_closedBall_strongFixedPointRoots_supply_of_frontier_dense_formal_proof :=
  @Bottcher.exists_closedBall_strongFixedPointRoots_supply_of_frontier_dense

/-- Localizer bridge: connected empty-interior Julia set plus dense strong fixed roots yields an
infinite closed-ball strong-periodic supply inside an open target region. -/
def hrig_closedBall_strongFixedPointRoots_supply_of_frontier_dense_open_formal_proof :=
  @Bottcher.exists_closedBall_strongFixedPointRoots_supply_of_frontier_dense_open

/-- Localizer bridge: perfect Julia frontier plus dense strong fixed roots yields an infinite
closed-ball strong-periodic supply inside an open target region. -/
def hrig_closedBall_strongFixedPointRoots_supply_of_perfect_frontier_dense_open_formal_proof :=
  @Bottcher.exists_closedBall_strongFixedPointRoots_supply_of_perfect_frontier_dense_open

/-- Localizer bridge: connected empty-interior Julia set plus natural orbit-product density of
strongly repelling periodic points yields an open-region closed-ball supply. -/
def hrig_closedBall_strongly_repelling_periodic_supply_of_frontier_dense_open_formal_proof :=
  @Bottcher.exists_closedBall_strongly_repelling_periodic_supply_of_frontier_dense_open

/-- Localizer bridge: perfect Julia frontier plus natural orbit-product density of strongly
repelling periodic points yields an open-region closed-ball supply. -/
def hrig_closedBall_strongly_repelling_periodic_supply_of_perfect_frontier_dense_open_formal_proof :=
  @Bottcher.exists_closedBall_strongly_repelling_periodic_supply_of_perfect_frontier_dense_open

/-- Global β/γ frontier endpoint for connected q62.  This is the canonical
nonresonance branch currently exposed before the local hRigid completion
removes the remaining branch hypotheses. -/
def q62_connected_repelling_global_betaGamma_frontier_derivNonres_separable_repellingG_formal_proof :=
  @Bottcher.q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_derivNonres_separable_repellingG

/-- Global β/γ hRigid crossing endpoint where frontier membership and canonical nonresonance are
derived from an accumulating strong-repelling periodic target supply. -/
def hrig_phiMero_repelling_global_betaGamma_crossing_orbitNorm_autoFrontierNonres_formal_proof :=
  @Bottcher.hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_crossing_orbitNorm_autoFrontierNonres

/-- Connected q62 endpoint from global β/γ crossing where the hRigid-side callback only supplies an
accumulating strong-repelling periodic target supply. -/
def q62_connected_repelling_global_betaGamma_crossing_orbitNorm_autoFrontierNonres_repellingG_formal_proof :=
  @Bottcher.q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_crossing_orbitNorm_autoFrontierNonres_repellingG

/-- Global β/γ hRigid endpoint where a local infinite strong-periodic supply in a closed ball
creates the required accumulating target internally. -/
def hrig_phiMero_repelling_global_betaGamma_closedBallStrongOrbitNorm_autoAccum_formal_proof :=
  @Bottcher.hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_closedBallStrongOrbitNorm_autoAccum

/-- Connected q62 endpoint from global β/γ branches and a local infinite strong-periodic supply in a
closed ball; the accumulated hRigid target is created internally. -/
def q62_connected_repelling_global_betaGamma_closedBallStrongOrbitNorm_autoAccum_repellingG_formal_proof :=
  @Bottcher.q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_closedBallStrongOrbitNorm_autoAccum_repellingG

/-- Global β/γ hRigid endpoint where the callback supplies an interior accumulation point of
strong-periodic targets, and Lean shrinks it to the closed-ball supply internally. -/
def hrig_phiMero_repelling_global_betaGamma_accumulationInteriorStrongOrbitNorm_closedBall_formal_proof :=
  @Bottcher.hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_accumulationInteriorStrongOrbitNorm_closedBall

/-- Connected q62 endpoint from global β/γ branches and an interior accumulation point of
strong-periodic targets; the closed-ball hRigid supply is constructed internally. -/
def q62_connected_repelling_global_betaGamma_accumulationInteriorStrongOrbitNorm_closedBall_repellingG_formal_proof :=
  @Bottcher.q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_accumulationInteriorStrongOrbitNorm_closedBall_repellingG

/-- Global β/γ hRigid endpoint where perfect Julia frontier plus dense strong roots create the
closed-ball strong-periodic supply internally. -/
def hrig_phiMero_repelling_global_betaGamma_perfectFrontierDenseStrongRoots_autoClosedBall_formal_proof :=
  @Bottcher.hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongRoots_autoClosedBall

/-- Connected q62 endpoint from global β/γ branches where perfect Julia frontier plus dense strong
roots create the closed-ball hRigid supply internally. -/
def q62_connected_repelling_global_betaGamma_perfectFrontierDenseStrongRoots_autoClosedBall_repellingG_formal_proof :=
  @Bottcher.q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongRoots_autoClosedBall_repellingG

/-- Global β/γ hRigid endpoint where connected empty-interior Julia geometry plus dense strong roots
create the closed-ball strong-periodic supply internally. -/
def hrig_phiMero_repelling_global_betaGamma_connectedEmptyInteriorDenseStrongRoots_autoClosedBall_formal_proof :=
  @Bottcher.hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongRoots_autoClosedBall

/-- Connected q62 endpoint from global β/γ branches where connected empty-interior Julia geometry plus
dense strong roots create the closed-ball hRigid supply internally. -/
def q62_connected_repelling_global_betaGamma_connectedEmptyInteriorDenseStrongRoots_autoClosedBall_repellingG_formal_proof :=
  @Bottcher.q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongRoots_autoClosedBall_repellingG

/-- Global β/γ hRigid endpoint where perfect Julia frontier plus dense strong roots create the
closed-ball strong-periodic supply from an open crossing region. -/
def hrig_phiMero_repelling_global_betaGamma_perfectFrontierDenseStrongRoots_openRegion_autoClosedBall_formal_proof :=
  @Bottcher.hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongRoots_openRegion_autoClosedBall

/-- Global β/γ hRigid endpoint where connected empty-interior Julia geometry plus dense strong roots
create the closed-ball strong-periodic supply from an open crossing region. -/
def hrig_phiMero_repelling_global_betaGamma_connectedEmptyInteriorDenseStrongRoots_openRegion_autoClosedBall_formal_proof :=
  @Bottcher.hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongRoots_openRegion_autoClosedBall

/-- Connected q62 endpoint where perfect Julia frontier plus dense strong roots create the hRigid
supply from an open crossing region. -/
def q62_connected_repelling_global_betaGamma_perfectFrontierDenseStrongRoots_openRegion_autoClosedBall_repellingG_formal_proof :=
  @Bottcher.q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongRoots_openRegion_autoClosedBall_repellingG

/-- Connected q62 endpoint where connected empty-interior Julia geometry plus dense strong roots
create the hRigid supply from an open crossing region. -/
def q62_connected_repelling_global_betaGamma_connectedEmptyInteriorDenseStrongRoots_openRegion_autoClosedBall_repellingG_formal_proof :=
  @Bottcher.q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongRoots_openRegion_autoClosedBall_repellingG

/-- Global β/γ hRigid endpoint where perfect Julia frontier plus natural orbit-product density create
the closed-ball strong-periodic supply from an open crossing region. -/
def hrig_phiMero_repelling_global_betaGamma_perfectFrontierDenseStrongOrbitNorm_openRegion_autoClosedBall_formal_proof :=
  @Bottcher.hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongOrbitNorm_openRegion_autoClosedBall

/-- Global β/γ hRigid endpoint where connected empty-interior Julia geometry plus natural
orbit-product density create the closed-ball strong-periodic supply from an open crossing region. -/
def hrig_phiMero_repelling_global_betaGamma_connectedEmptyInteriorDenseStrongOrbitNorm_openRegion_autoClosedBall_formal_proof :=
  @Bottcher.hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongOrbitNorm_openRegion_autoClosedBall

/-- Connected q62 endpoint where perfect Julia frontier plus natural orbit-product density create the
hRigid supply from an open crossing region. -/
def q62_connected_repelling_global_betaGamma_perfectFrontierDenseStrongOrbitNorm_openRegion_autoClosedBall_repellingG_formal_proof :=
  @Bottcher.q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongOrbitNorm_openRegion_autoClosedBall_repellingG

/-- Connected q62 endpoint where connected empty-interior Julia geometry plus natural orbit-product
density create the hRigid supply from an open crossing region. -/
def q62_connected_repelling_global_betaGamma_connectedEmptyInteriorDenseStrongOrbitNorm_openRegion_autoClosedBall_repellingG_formal_proof :=
  @Bottcher.q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongOrbitNorm_openRegion_autoClosedBall_repellingG

/-- Level-root hRigid crossing endpoint where frontier membership is derived from an accumulating
strong-repelling periodic target supply. -/
def hrig_phiMero_level_roots_crossing_orbitNorm_autoFrontier_formal_proof :=
  @Bottcher.hrig_phiMero_of_level_roots_modulus_auto_gamma_frontierAnalytic_crossing_orbitNorm_autoFrontier

/-- Connected q62 endpoint from the level-root crossing route, with the hRigid-side frontier condition
derived from strong periodic repulsion. -/
def q62_connected_level_roots_crossing_orbitNorm_autoFrontier_repellingG_formal_proof :=
  @Bottcher.q62_independence_connected_of_level_roots_modulus_auto_gamma_frontierAnalytic_crossing_orbitNorm_autoFrontier_repellingG

/-- Absolute connected `φ_c` transcendence through the index route, with the exceptional-mass
smallness period chosen internally from eventual bulk data. -/
def hrig_phiMero_absolute_index_eventual_formal_proof :=
  @Bottcher.phiMero_transcendental_via_index_eventual

/-- Absolute connected `φ_c` transcendence through the index route, with both fixed-root membership and
exceptional-mass smallness derived internally from a fixed repelling exceptional set. -/
def hrig_phiMero_absolute_index_eventual_fixedB_formal_proof :=
  @Bottcher.phiMero_transcendental_via_index_eventual_fixedB

/-- Relative connected hRigid input through the index route, with the exceptional-mass smallness
period chosen internally from eventual bulk data. -/
def hrig_phiMero_relative_index_eventual_formal_proof :=
  @Bottcher.hrig_phiMero_via_index_eventual

/-- Relative connected hRigid input through the index route, with both fixed-root membership and
exceptional-mass smallness derived internally from a fixed repelling exceptional set. -/
def hrig_phiMero_relative_index_eventual_fixedB_formal_proof :=
  @Bottcher.hrig_phiMero_via_index_eventual_fixedB

end FullyProvenNewTargets

namespace FullyProvenNewTargets

noncomputable section

/-- Polynomial-valued pole-tower target for the rational-tail lemma: if each
coefficient degree yields the pole-root identities, all coefficient polynomials
are zero. -/
def HurwitzPolylogPoleTowerPolynomialTarget (M : ℕ) : Prop :=
  ∀ {gamma : Fin (M + 1) → ℂ} {p : Fin (M + 1) → Polynomial ℂ},
    (∀ j, gamma j ≠ 0) →
    (∀ (d n : ℕ),
      (∑ j : Fin (M + 1),
        (p j).coeff d * gamma j *
          (HurwitzPolylogPoleTower.twoPiI * ((n + 1 : ℕ) : ℂ)) ^ (j : ℕ)) = 0) →
    ∀ j, p j = 0

/-- Formal wrapper for polynomial-valued pole-tower injectivity. -/
theorem hurwitz_polylog_pole_tower_polynomials (M : ℕ) :
    HurwitzPolylogPoleTowerPolynomialTarget M := by
  intro gamma p hgamma hroot j
  exact HurwitzPolylogPoleTower.polynomials_zero_of_pole_sum_roots hgamma hroot j

end

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Nonzero Gamma-coefficient target for the actual pole tower in the Hurwitz
rational-tail proof. -/
def HurwitzGammaPoleCoefficientsNonzeroTarget (M : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
    ∀ j : Fin (M + 1), Complex.Gamma (1 - s - (j : ℂ)) ≠ 0

/-- Formal wrapper for nonvanishing of `Gamma(1-s-j)` under `s ∉ Z`. -/
theorem hurwitz_gamma_pole_coefficients_nonzero (M : ℕ) :
    HurwitzGammaPoleCoefficientsNonzeroTarget M := by
  intro s hs j
  exact HurwitzPolylogPoleTower.gamma_one_sub_shift_ne_zero hs j

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Actual Gamma-coefficient scalar pole-tower target for the Hurwitz rational-tail proof. -/
def HurwitzGammaPoleTowerTopCoeffTarget (M : ℕ) : Prop :=
  ∀ {s : ℂ} {a : Fin (M + 1) → ℂ},
    (∀ k : ℤ, s ≠ (k : ℂ)) →
    (∀ n : ℕ,
      (∑ j : Fin (M + 1),
        a j * Complex.Gamma (1 - s - (j : ℂ)) *
          (HurwitzPolylogPoleTower.twoPiI * ((n + 1 : ℕ) : ℂ)) ^ (j : ℕ)) = 0) →
    ∀ j, a j = 0

/-- Formal wrapper for actual Gamma-coefficient scalar pole-tower injectivity. -/
theorem hurwitz_gamma_pole_tower_top_coefficients (M : ℕ) :
    HurwitzGammaPoleTowerTopCoeffTarget M := by
  intro s a hs hroot j
  exact HurwitzPolylogPoleTower.coefficients_zero_of_gamma_pole_sum_roots hs hroot j

/-- Actual Gamma-coefficient polynomial-valued pole-tower target for the Hurwitz rational-tail proof. -/
def HurwitzGammaPoleTowerPolynomialTarget (M : ℕ) : Prop :=
  ∀ {s : ℂ} {p : Fin (M + 1) → Polynomial ℂ},
    (∀ k : ℤ, s ≠ (k : ℂ)) →
    (∀ (d n : ℕ),
      (∑ j : Fin (M + 1),
        (p j).coeff d * Complex.Gamma (1 - s - (j : ℂ)) *
          (HurwitzPolylogPoleTower.twoPiI * ((n + 1 : ℕ) : ℂ)) ^ (j : ℕ)) = 0) →
    ∀ j, p j = 0

/-- Formal wrapper for actual Gamma-coefficient polynomial-valued pole-tower injectivity. -/
theorem hurwitz_gamma_pole_tower_polynomials (M : ℕ) :
    HurwitzGammaPoleTowerPolynomialTarget M := by
  intro s p hs hroot j
  exact HurwitzPolylogPoleTower.polynomials_zero_of_gamma_pole_sum_roots hs hroot j

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Concrete singleton rational-tail target for the actual Hurwitz negative-integer
shift sequence `n ↦ ζ(s+j,-n)`. -/
def HurwitzRationalTailSingleHzetaShiftTarget : Prop :=
  ∀ {s : ℂ}, 1 < s.re → (∀ k : ℤ, s ≠ (k : ℂ)) → ∀ j : ℕ,
    HurwitzAllNTailIndependence.RationalTailIndependent (N := 0)
      (fun _ n => HurwitzZetaShift.hzeta (s + (j : ℂ)) (-(n : ℂ)))

/-- Formal wrapper for the actual shifted Hurwitz singleton tail sequence. -/
theorem hurwitz_rational_tail_single_hzeta_shift :
    HurwitzRationalTailSingleHzetaShiftTarget := by
  intro s hs1 hsZ j
  exact HurwitzAllNTailIndependence.rationalTailIndependent_hzeta_shift_neg_nat_single hs1 hsZ j

end FullyProvenNewTargets

namespace FullyProvenNewTargets

noncomputable section

/-- Sharper concrete-carrier U0 target: the local Lean proof has already
discharged `φ_b ≠ 0` and `u₀` transcendence, so only the exact monodromy tower
remains. -/
def U0PhiIndependenceMonoCarrierTarget {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b) : Prop :=
  letI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  (∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
    d < m ∧ orderOf ζ = m ∧
    σ (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) =
      algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext) ∧
    σ ζ = ζ ∧ σ (phiMero b hU_esc) = ζ * phiMero b hU_esc) →
  U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for the concrete U0 carrier theorem with only the monodromy
tower left as input. -/
theorem u0_phi_independence_mono_carrier_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b) :
    U0PhiIndependenceMonoCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc := by
  intro mono
  exact U0MeroCarrier.u0_phib_independence_concrete hUo hUc hUne hUinf hU_ext hU_esc mono

end

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Cover-germ U0 monodromy target: for every order bound, the Böttcher cover carries a dyadic deck
transformation that fixes `z`, fixes the lifted `u₀`, fixes the multiplier, and scales `φ_b`. -/
def U0CoverGermMonoFTarget (c₁ c₂ : ℂ) (m : ℕ) : Prop :=
  ∀ d : ℕ,
    ∃ (k : ℕ) (ζ : ℂ) (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ k) = 1),
      d < orderOf ((ζ : Bottcher.coverGerm c₁ c₂ k m)) ∧
      Bottcher.deckGermEquiv hζ hpow (Bottcher.zGerm : Bottcher.coverGerm c₁ c₂ k m)
        = Bottcher.zGerm ∧
      Bottcher.deckGermEquiv hζ hpow (U0CoverMono.u0Cover : Bottcher.coverGerm c₁ c₂ k m)
        = U0CoverMono.u0Cover ∧
      Bottcher.deckGermEquiv hζ hpow ((ζ : Bottcher.coverGerm c₁ c₂ k m))
        = (ζ : Bottcher.coverGerm c₁ c₂ k m) ∧
      Bottcher.deckGermEquiv hζ hpow (Bottcher.v1Germ : Bottcher.coverGerm c₁ c₂ k m)
        = (ζ : Bottcher.coverGerm c₁ c₂ k m) * Bottcher.v1Germ

/-- Formal wrapper for the cover-germ U0 monodromy tower. -/
theorem u0_coverGerm_monoF_card (c₁ c₂ : ℂ) (m : ℕ) :
    U0CoverGermMonoFTarget c₁ c₂ m := by
  intro d
  exact U0CoverMono.u0_coverGerm_monoF_datum c₁ c₂ m d

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Natural-boundary target for the c-velocity `u₀`. This is the analytic core used by the U0-phi
cards: `u₀` continues across no point of the unit circle. -/
def U0NaturalBoundaryTarget : Prop :=
  ∀ z₀ : ℂ, ‖z₀‖ = 1 → ¬ U0NaturalBoundary.ContinuesAcross U0.u0 U0NaturalBoundary.Ext z₀

/-- Formal wrapper for the fully proved natural boundary of `u₀`. -/
theorem u0_natural_boundary_card : U0NaturalBoundaryTarget :=
  U0NaturalBoundary.u0_natural_boundary

/-- Carrier transcendence target for `u₀` at the Böttcher meromorphic field. -/
def U0MeroTranscendenceCarrierTarget {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) : Prop :=
  letI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  Transcendental (RatFunc ℂ)
    (algebraMap (analyticSubring U) (meroField U) (U0MeroCarrier.u0AnSub hU_ext))

/-- Formal wrapper for `u₀` transcendence in the concrete Böttcher meromorphic carrier. -/
theorem u0_mero_transcendence_carrier_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) :
    U0MeroTranscendenceCarrierTarget hUo hUc hUne hUinf hU_ext :=
  U0MeroCarrier.u0Mero_transcendental hUo hUc hUne hUinf hU_ext

/-- Cover-germ no-relation target for lifted `u₀`. -/
def U0CoverNoRelationTarget (c₁ c₂ : ℂ) (n m : ℕ) : Prop :=
  ∀ P : (Polynomial ℂ)[X], 1 ≤ P.natDegree →
    ((fun p : ℂ × ℂ × ℂ => U0Transcendence.evalU0 P p.1 : ℂ × ℂ × ℂ → ℂ) :
      Bottcher.coverGerm c₁ c₂ n m) = 0 →
    False

/-- Formal wrapper for absence of polynomial relations for lifted `u₀` on the Böttcher cover germ. -/
theorem u0_cover_no_relation_card (c₁ c₂ : ℂ) (n m : ℕ) :
    U0CoverNoRelationTarget c₁ c₂ n m := by
  intro P hP hrel
  exact U0CoverMono.u0Cover_no_relation (c₁ := c₁) (c₂ := c₂) (n := n) (m := m) P hP hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Local-orbit root-counting target: three distinct monodromy orbit points kill a degree-`≤2`
polynomial. -/
def HurwitzOrbitThreePointTarget : Prop :=
  ∀ {p : Polynomial ℂ} {q : ℂ}, p.natDegree ≤ 2 →
    (1 : ℂ) ≠ q → (1 : ℂ) ≠ q ^ 2 → q ≠ q ^ 2 →
    (∀ m : ℕ, p.eval (q ^ m) = 0) → p = 0

/-- Formal wrapper for the three-point local-orbit obstruction. -/
theorem hurwitz_orbit_three_point_card : HurwitzOrbitThreePointTarget := by
  intro p q hp h1q h1q2 hqq2 hroots
  exact HurwitzOrbit.orbit_eq_zero_of_three_distinct hp h1q h1q2 hqq2 hroots

/-- Order-two local-orbit target: vanishing at `1` and `-1` kills the odd coefficient. -/
def HurwitzOrbitOrderTwoOddCoeffTarget : Prop :=
  ∀ {p : Polynomial ℂ}, p.natDegree ≤ 2 → p.eval 1 = 0 → p.eval (-1) = 0 → p.coeff 1 = 0

/-- Formal wrapper for the order-two odd-coefficient obstruction. -/
theorem hurwitz_orbit_order_two_odd_coeff_card : HurwitzOrbitOrderTwoOddCoeffTarget := by
  intro p hp h1 hm1
  exact HurwitzOrbit.coeff_one_eq_zero_of_pm_one hp h1 hm1

/-- Monodromy-scalar generic branch target: `s∉ℤ` and `2s∉ℤ` give three distinct orbit points. -/
def HurwitzMonodromyScalarGenericOrbitTarget : Prop :=
  ∀ {s : ℂ}, (∀ m : ℤ, s ≠ (m : ℂ)) → (∀ m : ℤ, 2 * s ≠ (m : ℂ)) →
    (1 : ℂ) ≠ HurwitzOrbit.monoScalar s ∧
      (1 : ℂ) ≠ (HurwitzOrbit.monoScalar s) ^ 2 ∧
      HurwitzOrbit.monoScalar s ≠ (HurwitzOrbit.monoScalar s) ^ 2

/-- Formal wrapper for the generic monodromy-scalar orbit branch. -/
theorem hurwitz_monoScalar_generic_orbit_card : HurwitzMonodromyScalarGenericOrbitTarget := by
  intro s hs h2s
  exact HurwitzOrbit.monoScalar_three_distinct hs h2s

/-- Monodromy-scalar order-two branch target: the half-integer case has scalar `-1`. -/
def HurwitzMonodromyScalarOrderTwoTarget : Prop :=
  ∀ {s : ℂ}, (∀ m : ℤ, s ≠ (m : ℂ)) → (∃ m : ℤ, 2 * s = (m : ℂ)) →
    HurwitzOrbit.monoScalar s = -1

/-- Formal wrapper for the half-integer monodromy-scalar branch. -/
theorem hurwitz_monoScalar_order_two_card : HurwitzMonodromyScalarOrderTwoTarget := by
  intro s hs h2s
  exact HurwitzOrbit.monoScalar_eq_neg_one hs h2s

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Local split target for the shifted Hurwitz ladder at negative integers. -/
def HurwitzHzetaShiftLocalSplitTarget : Prop :=
  ∀ {s : ℂ}, 1 < s.re → ∀ k n : ℕ, ∀ x : ℂ,
    HurwitzZetaShift.hzeta (s + k) (-(n : ℂ) + x)
      = x ^ (-(s + k))
        + ∑' m : ℕ, (if m = n then 0 else ((m : ℂ) + (-(n : ℂ) + x)) ^ (-(s + k)))

/-- Formal wrapper for the actual shifted Hurwitz local split. -/
theorem hurwitz_hzeta_shift_local_split_card : HurwitzHzetaShiftLocalSplitTarget := by
  intro s hs k n x
  exact HurwitzZetaShift.hzeta_local_split_shift hs k n x

/-- Finite-difference target for Hurwitz negative-integer tail values. -/
def HurwitzHzetaNegNatDiffTarget : Prop :=
  ∀ {s : ℂ}, 1 < s.re → ∀ {n : ℕ}, 1 ≤ n →
    HurwitzZetaShift.hzeta s (-(n : ℂ)) - HurwitzZetaShift.hzeta s (-((n - 1 : ℕ) : ℂ))
      = Complex.exp (-((Real.pi : ℂ) * Complex.I * s)) * (n : ℂ) ^ (-s)

/-- Formal wrapper for the actual negative-integer Hurwitz finite-difference identity. -/
theorem hurwitz_hzeta_neg_nat_diff_card : HurwitzHzetaNegNatDiffTarget := by
  intro s hs n hn
  exact HurwitzZetaShift.hzeta_neg_nat_diff hs hn

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Cover-side transported `u₀` transcendence target for the U0-phi lift route. The base-side algebra is
fixed to the canonical `ratfuncToMero`; the remaining hypothesis is precisely that the cover projection
is compatible with the `ℂ(z)` algebra map. -/
def U0PrecompMeroCrossTranscendenceTarget {U V : Set ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hmaps : Set.MapsTo g U V) (h : Tendsto g (𝓟 U) (𝓟 V))
    (hsurj : Set.SurjOn g U V)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (hV_ext : V ⊆ U0NaturalBoundary.Ext)
    [haveI := isDomain_analyticSubring U hUo hUc hUne; Algebra (RatFunc ℂ) (meroField U)] : Prop :=
  (haveI := isDomain_analyticSubring U hUo hUc hUne
   haveI := isDomain_analyticSubring V hVo hVc hVne
   letI : Algebra (RatFunc ℂ) (meroField V) := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
   ∀ k : RatFunc ℂ, U0CoverTransport.precompMeroCross hg hmaps h hsurj hUo hUc hUne hVo hVc hVne
      (algebraMap (RatFunc ℂ) (meroField V) k) = algebraMap (RatFunc ℂ) (meroField U) k) →
  haveI := isDomain_analyticSubring U hUo hUc hUne
  haveI := isDomain_analyticSubring V hVo hVc hVne
  letI : Algebra (RatFunc ℂ) (meroField V) := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
  Transcendental (RatFunc ℂ)
    (U0CoverTransport.precompMeroCross hg hmaps h hsurj hUo hUc hUne hVo hVc hVne
      (algebraMap (analyticSubring V) (meroField V) (U0MeroCarrier.u0AnSub hV_ext)))

/-- Formal wrapper for transporting the concrete `u₀` carrier transcendence to a cover carrier. -/
theorem u0_precompMeroCross_transcendence_card {U V : Set ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hmaps : Set.MapsTo g U V) (h : Tendsto g (𝓟 U) (𝓟 V))
    (hsurj : Set.SurjOn g U V)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (hV_ext : V ⊆ U0NaturalBoundary.Ext)
    [haveI := isDomain_analyticSubring U hUo hUc hUne; Algebra (RatFunc ℂ) (meroField U)] :
    U0PrecompMeroCrossTranscendenceTarget hg hmaps h hsurj hUo hUc hUne hVo hVc hVne hVinf hV_ext := by
  intro hcompat
  exact U0CoverTransport.u0_transcendental_precompMeroCross hg hmaps h hsurj hUo hUc hUne
    hVo hVc hVne hVinf hV_ext hcompat

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- U0-phi lift-route wrapper with cover-side `u₀` transcendence supplied by projection transport. This
is the lift-level card target after removing the separate `hG` input; remaining inputs are the
projection algebra compatibility, `φ_b ≠ 0`, and the deck lift scaling `φ_b` while fixing transported
`u₀`. -/
theorem u0_phi_independence_precomp_lifts_card {U V : Set ℂ} {g : ℂ → ℂ}
    (hgbase : AnalyticOnNhd ℂ g U) (hbaseMaps : Set.MapsTo g U V)
    (hbase : Tendsto g (𝓟 U) (𝓟 V)) (hbaseSurj : Set.SurjOn g U V)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (hV_ext : V ⊆ U0NaturalBoundary.Ext)
    [haveI := isDomain_analyticSubring U hUo hUc hUne; Algebra (RatFunc ℂ) (meroField U)]
    (hcompat : haveI := isDomain_analyticSubring U hUo hUc hUne
      haveI := isDomain_analyticSubring V hVo hVc hVne
      letI : Algebra (RatFunc ℂ) (meroField V) := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
      ∀ k : RatFunc ℂ, U0CoverTransport.precompMeroCross hgbase hbaseMaps hbase hbaseSurj
          hUo hUc hUne hVo hVc hVne
          (algebraMap (RatFunc ℂ) (meroField V) k) = algebraMap (RatFunc ℂ) (meroField U) k)
    (aφ : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) aφ ≠ 0)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (gdeck gdeck' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ gdeck U) (hg' : AnalyticOnNhd ℂ gdeck' U)
        (hmaps : Set.MapsTo gdeck U U) (hmaps' : Set.MapsTo gdeck' U U)
        (hgg' : Set.EqOn (gdeck ∘ gdeck') id U) (hg'g : Set.EqOn (gdeck' ∘ gdeck) id U),
        d < orderOf ζ₀ ∧
        (aφ : Germ (𝓟 U) ℂ).compTendsto gdeck (tendsto_principal_principal.mpr hmaps)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (aφ : Germ (𝓟 U) ℂ) ∧
        ((U0CoverTransport.precompAnalyticCross hgbase hbaseMaps hbase
            (U0MeroCarrier.u0AnSub hV_ext) : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto
          gdeck (tendsto_principal_principal.mpr hmaps)
          = (U0CoverTransport.precompAnalyticCross hgbase hbaseMaps hbase
              (U0MeroCarrier.u0AnSub hV_ext) : analyticSubring U) ∧
        ∀ k : RatFunc ℂ, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap (RatFunc ℂ) (meroField U) k) = algebraMap (RatFunc ℂ) (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) aφ)
      (algebraMap (analyticSubring U) (meroField U)
        (U0CoverTransport.precompAnalyticCross hgbase hbaseMaps hbase
          (U0MeroCarrier.u0AnSub hV_ext))) :=
  U0PhiLifts.u0_phib_independence_of_precomp_lifts hgbase hbaseMaps hbase hbaseSurj
    hUo hUc hUne hVo hVc hVne hVinf hV_ext hcompat aφ hF hliftF

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Actual shifted Hurwitz multi-tail reduction target: full rational-tail independence for
`n ↦ ζ(s+i,-n)` follows from the corresponding harmonic-sum tail family. -/
def HurwitzHzetaTailFromHarmonicTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, 1 < s.re →
    HurwitzAllNTailIndependence.RationalTailIndependent (N := N)
      (HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s) →
    HurwitzAllNTailIndependence.RationalTailIndependent (N := N)
      (fun i n => HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))

/-- Formal wrapper for the affine reduction from actual Hurwitz tail values to harmonic sums. -/
theorem hurwitz_hzeta_tail_from_harmonic_card (N : ℕ) :
    HurwitzHzetaTailFromHarmonicTarget N := by
  intro s hs hH
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.rationalTailIndependent_hzeta_shift_neg_nat_of_harmonic
    (N := N) hs hH

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Singleton harmonic-tail rational independence target, the base case for the harmonic-sum reduction of
the Hurwitz rational-tail gate. -/
def HurwitzHarmonicTailSingleTarget : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
    HurwitzAllNTailIndependence.RationalTailIndependent (N := 0)
      (HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := 0) s)

/-- Formal wrapper for singleton harmonic-tail rational independence. -/
theorem hurwitz_harmonic_tail_single_card : HurwitzHarmonicTailSingleTarget := by
  intro s hsZ
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.rationalTailIndependent_harmonic_single hsZ

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Descended U0-phi lift-route wrapper with cover-side `u₀` transcendence supplied by projection
transport. This is the deep-ball descent analogue of `u0_phi_independence_precomp_lifts_card`. -/
theorem u0_phi_descended_precomp_lifts_card {U B V : Set ℂ} {π ι : ℂ → ℂ}
    (hπ : AnalyticOnNhd ℂ π U) (hπmaps : Set.MapsTo π U B)
    (hπtend : Tendsto π (𝓟 U) (𝓟 B)) (hπsurj : Set.SurjOn π U B)
    (hι : AnalyticOnNhd ℂ ι V) (hmaps : Set.MapsTo ι V U) (hUc : IsPreconnected U)
    (hopen : IsOpen (ι '' V)) (hne : (ι '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (hBo : IsOpen B) (hBc : IsPreconnected B) (hBne : B.Nonempty) (hBinf : B.Infinite)
    (hB_ext : B ⊆ U0NaturalBoundary.Ext)
    {p₀ : analyticSubring U} {f₀ : ℂ → ℂ} (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀)
    (hinf : (f₀ '' U).Infinite)
    (hp0ι : (p₀ : Germ (𝓟 U) ℂ).compTendsto ι (tendsto_principal_principal.mpr hmaps)
        = (↑(fun w : ℂ => w) : Germ (𝓟 V) ℂ))
    (aφ : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) aφ ≠ 0)
    (hcompat : haveI := isDomain_analyticSubring U hUo hUc hUne
      haveI := isDomain_analyticSubring B hBo hBc hBne
      letI := (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne).toAlgebra
      letI : Algebra (RatFunc ℂ) (meroField B) := (ratfuncToMero B hBo hBc hBne hBinf).toAlgebra
      ∀ k : RatFunc ℂ, U0CoverTransport.precompMeroCross hπ hπmaps hπtend hπsurj hUo hUc hUne hBo hBc hBne
          (algebraMap (RatFunc ℂ) (meroField B) k) = algebraMap (RatFunc ℂ) (meroField U) k)
    (hliftF : haveI := isDomain_analyticSubring U hUo hUc hUne
        letI := (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne).toAlgebra
        ∀ d : ℕ, ∃ (ζ₀ : ℂ) (gdeck gdeck' : ℂ → ℂ)
          (hg : AnalyticOnNhd ℂ gdeck U) (hg' : AnalyticOnNhd ℂ gdeck' U)
          (hmg : Set.MapsTo gdeck U U) (hmg' : Set.MapsTo gdeck' U U)
          (hgg' : Set.EqOn (gdeck ∘ gdeck') id U) (hg'g : Set.EqOn (gdeck' ∘ gdeck) id U),
          d < orderOf ζ₀ ∧
          (aφ : Germ (𝓟 U) ℂ).compTendsto gdeck (tendsto_principal_principal.mpr hmg)
            = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (aφ : Germ (𝓟 U) ℂ) ∧
          ((U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
              (U0MeroCarrier.u0AnSub hB_ext) : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto
            gdeck (tendsto_principal_principal.mpr hmg)
            = (U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
                (U0MeroCarrier.u0AnSub hB_ext) : analyticSubring U) ∧
          ∀ k : RatFunc ℂ, precompMeroEquiv hg hg' hmg hmg' hgg' hg'g hUo hUc hUne
            (algebraMap (RatFunc ℂ) (meroField U) k) = algebraMap (RatFunc ℂ) (meroField U) k) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    letI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ)
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U) aφ))
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U)
          (U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
            (U0MeroCarrier.u0AnSub hB_ext)))) :=
  U0PhiLifts.u0_phib_noRelation_descended_precomp hπ hπmaps hπtend hπsurj hι hmaps hUc hopen hne
    hUo hUne hVo hVc hVne hVinf hBo hBc hBne hBinf hB_ext hp0 hinf hp0ι aφ hF hcompat hliftF

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Descended U0-phi lift-route wrapper where the deck's `RatFunc ℂ`-linearity is derived from fixing
the projection germ `p₀`. This removes the explicit “deck fixes all base rational functions” hypothesis
from the descended precomp lift route. -/
theorem u0_phi_descended_precomp_projection_lifts_card {U B V : Set ℂ} {π ι : ℂ → ℂ}
    (hπ : AnalyticOnNhd ℂ π U) (hπmaps : Set.MapsTo π U B)
    (hπtend : Tendsto π (𝓟 U) (𝓟 B)) (hπsurj : Set.SurjOn π U B)
    (hι : AnalyticOnNhd ℂ ι V) (hmaps : Set.MapsTo ι V U) (hUc : IsPreconnected U)
    (hopen : IsOpen (ι '' V)) (hne : (ι '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (hBo : IsOpen B) (hBc : IsPreconnected B) (hBne : B.Nonempty) (hBinf : B.Infinite)
    (hB_ext : B ⊆ U0NaturalBoundary.Ext)
    {p₀ : analyticSubring U} {f₀ : ℂ → ℂ} (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀)
    (hinf : (f₀ '' U).Infinite)
    (hp0ι : (p₀ : Germ (𝓟 U) ℂ).compTendsto ι (tendsto_principal_principal.mpr hmaps)
        = (↑(fun w : ℂ => w) : Germ (𝓟 V) ℂ))
    (aφ : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) aφ ≠ 0)
    (hcompat : haveI := isDomain_analyticSubring U hUo hUc hUne
      haveI := isDomain_analyticSubring B hBo hBc hBne
      letI := (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne).toAlgebra
      letI : Algebra (RatFunc ℂ) (meroField B) := (ratfuncToMero B hBo hBc hBne hBinf).toAlgebra
      ∀ k : RatFunc ℂ, U0CoverTransport.precompMeroCross hπ hπmaps hπtend hπsurj hUo hUc hUne hBo hBc hBne
          (algebraMap (RatFunc ℂ) (meroField B) k) = algebraMap (RatFunc ℂ) (meroField U) k)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (gdeck gdeck' : ℂ → ℂ)
          (hg : AnalyticOnNhd ℂ gdeck U) (_hg' : AnalyticOnNhd ℂ gdeck' U)
          (hmg : Set.MapsTo gdeck U U) (_hmg' : Set.MapsTo gdeck' U U)
          (_hgg' : Set.EqOn (gdeck ∘ gdeck') id U) (_hg'g : Set.EqOn (gdeck' ∘ gdeck) id U),
          d < orderOf ζ₀ ∧
          (aφ : Germ (𝓟 U) ℂ).compTendsto gdeck (tendsto_principal_principal.mpr hmg)
            = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (aφ : Germ (𝓟 U) ℂ) ∧
          ((U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
              (U0MeroCarrier.u0AnSub hB_ext) : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto
            gdeck (tendsto_principal_principal.mpr hmg)
            = (U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
                (U0MeroCarrier.u0AnSub hB_ext) : analyticSubring U) ∧
          precompAnalytic hg hmg p₀ = p₀) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    letI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ)
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U) aφ))
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U)
          (U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
            (U0MeroCarrier.u0AnSub hB_ext)))) :=
  U0PhiLifts.u0_phib_noRelation_descended_precomp_projection_lifts hπ hπmaps hπtend hπsurj
    hι hmaps hUc hopen hne hUo hUne hVo hVc hVne hVinf hBo hBc hBne hBinf hB_ext hp0
    hinf hp0ι aφ hF hcompat hliftF

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Descended U0-phi lift-route wrapper where both algebra-compatibility inputs are supplied by
projection identities: `p₀ = π` gives cross-precomposition `RatFunc ℂ`-linearity, and deck-fixing `p₀`
gives deck `RatFunc ℂ`-linearity. -/
theorem u0_phi_descended_precomp_projection_base_lifts_card {U B V : Set ℂ} {π ι : ℂ → ℂ}
    (hπ : AnalyticOnNhd ℂ π U) (hπmaps : Set.MapsTo π U B)
    (hπtend : Tendsto π (𝓟 U) (𝓟 B)) (hπsurj : Set.SurjOn π U B)
    (hι : AnalyticOnNhd ℂ ι V) (hmaps : Set.MapsTo ι V U) (hUc : IsPreconnected U)
    (hopen : IsOpen (ι '' V)) (hne : (ι '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (hBo : IsOpen B) (hBc : IsPreconnected B) (hBne : B.Nonempty) (hBinf : B.Infinite)
    (hB_ext : B ⊆ U0NaturalBoundary.Ext)
    {p₀ : analyticSubring U} {f₀ : ℂ → ℂ} (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀)
    (hinf : (f₀ '' U).Infinite) (hp0π : (p₀ : Germ (𝓟 U) ℂ) = ↑π)
    (hp0ι : (p₀ : Germ (𝓟 U) ℂ).compTendsto ι (tendsto_principal_principal.mpr hmaps)
        = (↑(fun w : ℂ => w) : Germ (𝓟 V) ℂ))
    (aφ : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) aφ ≠ 0)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (gdeck gdeck' : ℂ → ℂ)
          (hg : AnalyticOnNhd ℂ gdeck U) (_hg' : AnalyticOnNhd ℂ gdeck' U)
          (hmg : Set.MapsTo gdeck U U) (_hmg' : Set.MapsTo gdeck' U U)
          (_hgg' : Set.EqOn (gdeck ∘ gdeck') id U) (_hg'g : Set.EqOn (gdeck' ∘ gdeck) id U),
          d < orderOf ζ₀ ∧
          (aφ : Germ (𝓟 U) ℂ).compTendsto gdeck (tendsto_principal_principal.mpr hmg)
            = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (aφ : Germ (𝓟 U) ℂ) ∧
          ((U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
              (U0MeroCarrier.u0AnSub hB_ext) : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto
            gdeck (tendsto_principal_principal.mpr hmg)
            = (U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
                (U0MeroCarrier.u0AnSub hB_ext) : analyticSubring U) ∧
          precompAnalytic hg hmg p₀ = p₀) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    letI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ)
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U) aφ))
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne
        (algebraMap (analyticSubring U) (meroField U)
          (U0CoverTransport.precompAnalyticCross hπ hπmaps hπtend
            (U0MeroCarrier.u0AnSub hB_ext)))) :=
  U0PhiLifts.u0_phib_noRelation_descended_precomp_projection_base_lifts hπ hπmaps hπtend hπsurj
    hι hmaps hUc hopen hne hUo hUne hVo hVc hVne hVinf hBo hBc hBne hBinf hB_ext hp0
    hinf hp0π hp0ι aφ hF hliftF

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Actual shifted-Hurwitz row/constant close from the harmonic-tail family. This is the card-level row
descent after the affine reduction from `ζ(s+i,-n)` to harmonic sums; the only remaining Hurwitz
all-`N` analytic input is harmonic-tail rational independence. -/
def HurwitzHzetaRowCloseFromHarmonicTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, 1 < s.re →
    HurwitzAllNTailIndependence.RationalTailIndependent (N := N)
      (HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s) →
    ∀ (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ),
      (∀ j : Fin (N + 1), ∃ M : ℕ, ∀ n, M ≤ n →
        (l j).eval (-(n : ℂ)) +
          (∑ i : Fin (N + 1),
            (q i j).eval (-(n : ℂ)) *
              (2 * HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))) = 0) →
      (∃ M : ℕ, ∀ n, M ≤ n → cc.eval (-(n : ℂ)) = 0) →
      (∀ i j, q i j = 0) ∧ (∀ j, l j = 0) ∧ cc = 0

/-- Formal wrapper for actual shifted-Hurwitz row/constant close from harmonic-tail independence. -/
theorem hurwitz_hzeta_row_close_from_harmonic_card (N : ℕ) :
    HurwitzHzetaRowCloseFromHarmonicTarget N := by
  intro s hs1 hH q l cc hrow hcc
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.rows_and_constant_close_of_hzeta_shift_neg_nat_of_harmonic
    (N := N) hs1 hH q l cc hrow hcc

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Polylog pole-root bridge target for harmonic-tail rational independence. This is the final algebraic
close of the Hurwitz all-`N` tail lemma after the fractional-polylog analysis supplies
`HarmonicPoleRootInput`. -/
def HurwitzHarmonicTailFromPoleRootTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
    HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s →
    HurwitzAllNTailIndependence.RationalTailIndependent (N := N)
      (HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s)

/-- Formal wrapper: Gamma pole-tower injectivity turns the polylog pole-root bridge into harmonic-tail
rational independence. -/
theorem hurwitz_harmonic_tail_from_pole_root_card (N : ℕ) :
    HurwitzHarmonicTailFromPoleRootTarget N := by
  intro s hsZ hpole
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.rationalTailIndependent_harmonic_of_poleRootInput
    (N := N) hsZ hpole

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Actual shifted-Hurwitz row/constant close directly from the polylog pole-root bridge. This is the
most concrete all-`N` row-close target currently isolated: the remaining analytic input is exactly
`HarmonicPoleRootInput`. -/
def HurwitzHzetaRowCloseFromPoleRootTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, 1 < s.re → (∀ k : ℤ, s ≠ (k : ℂ)) →
    HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s →
    ∀ (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ),
      (∀ j : Fin (N + 1), ∃ M : ℕ, ∀ n, M ≤ n →
        (l j).eval (-(n : ℂ)) +
          (∑ i : Fin (N + 1),
            (q i j).eval (-(n : ℂ)) *
              (2 * HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))) = 0) →
      (∃ M : ℕ, ∀ n, M ≤ n → cc.eval (-(n : ℂ)) = 0) →
      (∀ i j, q i j = 0) ∧ (∀ j, l j = 0) ∧ cc = 0

/-- Formal wrapper for actual shifted-Hurwitz row/constant close from the polylog pole-root bridge. -/
theorem hurwitz_hzeta_row_close_from_pole_root_card (N : ℕ) :
    HurwitzHzetaRowCloseFromPoleRootTarget N := by
  intro s hs1 hsZ hpole q l cc hrow hcc
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.rows_and_constant_close_of_hzeta_shift_neg_nat_of_poleRootInput
    hs1 hsZ hpole q l cc hrow hcc

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Actual shifted-Hurwitz rational-tail independence directly from the polylog pole-root bridge. -/
def HurwitzHzetaTailFromPoleRootTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, 1 < s.re → (∀ k : ℤ, s ≠ (k : ℂ)) →
    HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s →
    HurwitzAllNTailIndependence.RationalTailIndependent (N := N)
      (fun i n => HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))

/-- Formal wrapper for actual shifted-Hurwitz rational-tail independence from the pole-root bridge. -/
theorem hurwitz_hzeta_tail_from_pole_root_card (N : ℕ) :
    HurwitzHzetaTailFromPoleRootTarget N := by
  intro s hs1 hsZ hpole
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.rationalTailIndependent_hzeta_shift_neg_nat_of_poleRootInput
    (N := N) hs1 hsZ hpole

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- U0-phi carrier independence from the weaker per-depth non-square radical provider. This replaces the
full `PhibKummerInputs` provider by `PhibRadicalData`; primitive roots and irreducibility are built by
the Kummer algebra. -/
theorem u0_phi_independence_radical_data_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hRadical : U0CardTheorems.PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  U0CardTheorems.u0_phi_independence_carrier_radical_data hUo hUc hUne hUinf hU_ext hU_esc
    hRadical

/-- Formal wrapper for `u0-phi-independence.md` from the weaker radical-data provider. -/
theorem u0_phi_independence_connected_radical_data_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hRadical : U0CardTheorems.PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  U0CardTheorems.u0_phi_independence_connected_radical_data hUo hUc hUne hUinf hU_ext hU_esc
    hRadical

/-- Formal wrapper for `u0-phi-independence-disconnected.md` from the weaker radical-data provider. -/
theorem u0_phi_independence_disconnected_radical_data_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hRadical : U0CardTheorems.PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  U0CardTheorems.u0_phi_independence_disconnected_radical_data hUo hUc hUne hUinf hU_ext hU_esc
    hRadical

/-- Formal wrapper for `u0-phi-independence-all-parameters.md` from the weaker radical-data provider. -/
theorem u0_phi_independence_all_parameters_radical_data_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hRadical : U0CardTheorems.PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  U0CardTheorems.u0_phi_independence_all_parameters_radical_data hUo hUc hUne hUinf hU_ext hU_esc
    hRadical

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- U0-phi carrier independence from finite square-root deck data over the Kummer radicand. This is a
narrower provider than `PhibRadicalData`: the non-square clause is derived from deck scaling. -/
theorem u0_phi_independence_squareRootDeckData_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hDeck : U0CardTheorems.PhibSquareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  U0CardTheorems.u0_phi_independence_carrier_squareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc
    hDeck

/-- Formal wrapper for `u0-phi-independence.md` from finite square-root deck data. -/
theorem u0_phi_independence_connected_squareRootDeckData_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hDeck : U0CardTheorems.PhibSquareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  u0_phi_independence_squareRootDeckData_card hUo hUc hUne hUinf hU_ext hU_esc hDeck

/-- Formal wrapper for `u0-phi-independence-disconnected.md` from finite square-root deck data. -/
theorem u0_phi_independence_disconnected_squareRootDeckData_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hDeck : U0CardTheorems.PhibSquareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  u0_phi_independence_squareRootDeckData_card hUo hUc hUne hUinf hU_ext hU_esc hDeck

/-- Formal wrapper for `u0-phi-independence-all-parameters.md` from finite square-root deck data. -/
theorem u0_phi_independence_all_parameters_squareRootDeckData_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (hDeck : U0CardTheorems.PhibSquareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc) :
    U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc :=
  u0_phi_independence_squareRootDeckData_card hUo hUc hUne hUinf hU_ext hU_esc hDeck

/-- U0 provider-reduction target: finite square-root deck data over the Kummer
radicand supplies the weaker radical-data provider. -/
def U0PhibRadicalDataFromSquareRootDeckDataTarget : Prop :=
  ∀ {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibSquareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc →
    U0CardTheorems.PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for the U0 square-root-deck-data to radical-data provider reduction. -/
theorem u0_phib_radicalData_from_squareRootDeckData :
    U0PhibRadicalDataFromSquareRootDeckDataTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc hDeck
  exact U0CardTheorems.phibRadicalData_of_squareRootDeckData
    hUo hUc hUne hUinf hU_ext hU_esc hDeck

/-- U0 provider-reduction target: radical data supplies the full Kummer input
provider consumed by the carrier theorem. -/
def U0PhibKummerInputsFromRadicalDataTarget : Prop :=
  ∀ {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc →
    U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for the U0 radical-data to Kummer-input provider reduction. -/
theorem u0_phib_kummerInputs_from_radicalData :
    U0PhibKummerInputsFromRadicalDataTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc hRadical
  exact U0CardTheorems.phibKummerInputs_of_radicalData
    hUo hUc hUne hUinf hU_ext hU_esc hRadical

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Finite-type obstruction target for dyadic monodromy: unbounded element orders rule out any finite
monodromy carrier. This is the algebraic consequence used by the finite-type and finite-cover support
cards before the topological finite-index part enters. -/
def BottcherUnboundedOrderNoFiniteCarrierTarget : Prop :=
  ∀ {G : Type} [Monoid G], (∀ d : ℕ, ∃ x : G, d < orderOf x) → ¬ Finite G

/-- Formal wrapper: unbounded dyadic order cannot live in a finite monodromy carrier. -/
theorem bottcher_dyadic_monodromy_no_finite_carrier :
    BottcherUnboundedOrderNoFiniteCarrierTarget := by
  intro G hG h
  exact Bottcher.not_finite_of_unbounded_order h

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Finite quotient obstruction target for the Böttcher-Prüfer finite-cover card: a power-divisible
monodromy group has no nontrivial finite quotient. -/
def BottcherPowerDivisibleFiniteQuotientTrivialTarget : Prop :=
  ∀ {G : Type} [Group G] (H : Subgroup G), H.Normal →
    (∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, x ^ n = g) →
    Finite (G ⧸ H) → H = ⊤

/-- Formal wrapper: finite quotient collapse for power-divisible monodromy. -/
theorem bottcher_pruefer_finite_quotient_power_divisible_obstruction :
    BottcherPowerDivisibleFiniteQuotientTrivialTarget := by
  intro G hG H hHnormal hdiv hfin
  haveI : H.Normal := hHnormal
  haveI : Finite (G ⧸ H) := hfin
  exact Bottcher.subgroup_eq_top_of_powerDivisible_finite_quotient H hdiv

/-- Finite-index subgroup obstruction target for the Böttcher-Prüfer finite-cover card. -/
def BottcherPowerDivisibleFiniteIndexTrivialTarget : Prop :=
  ∀ {G : Type} [Group G] (H : Subgroup G), H.Normal → H.FiniteIndex →
    (∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, x ^ n = g) → H = ⊤

/-- Formal wrapper: power-divisible monodromy has no proper normal finite-index subgroup. -/
theorem bottcher_pruefer_finite_index_power_divisible_obstruction :
    BottcherPowerDivisibleFiniteIndexTrivialTarget := by
  intro G hG H hHnormal hfinite hdiv
  haveI : H.Normal := hHnormal
  haveI : H.FiniteIndex := hfinite
  exact Bottcher.subgroup_eq_top_of_powerDivisible_finiteIndex H hdiv

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Homomorphism-form finite-cover obstruction target: every map from a power-divisible monodromy group
into a finite group is trivial. -/
def BottcherPowerDivisibleFiniteCodomainTrivialTarget : Prop :=
  ∀ {G Q : Type} [Group G] [Group Q], Finite Q → (φ : G →* Q) →
    (∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, x ^ n = g) → ∀ g : G, φ g = 1

/-- Formal wrapper: finite target groups cannot detect power-divisible monodromy. -/
theorem bottcher_pruefer_finite_codomain_power_divisible_obstruction :
    BottcherPowerDivisibleFiniteCodomainTrivialTarget := by
  intro G Q hG hQ hfin φ hdiv g
  haveI : Finite Q := hfin
  exact Bottcher.monoidHom_eq_one_of_powerDivisible_finite_codomain φ hdiv g

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Finite-image obstruction target: every homomorphic finite monodromy image of a power-divisible group
is trivial. -/
def BottcherPowerDivisibleFiniteImageTrivialTarget : Prop :=
  ∀ {G Q : Type} [Group G] [Group Q] (φ : G →* Q), Finite φ.range →
    (∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, x ^ n = g) → ∀ g : G, φ g = 1

/-- Formal wrapper: finite monodromy images cannot detect power-divisible monodromy. -/
theorem bottcher_pruefer_finite_image_power_divisible_obstruction :
    BottcherPowerDivisibleFiniteImageTrivialTarget := by
  intro G Q hG hQ φ hfin hdiv g
  haveI : Finite φ.range := hfin
  exact Bottcher.monoidHom_eq_one_of_powerDivisible_finite_range φ hdiv g

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Additive Prüfer/divisible finite-cover algebra target. This packages the exact card-level statement
that a divisible abelian monodromy group cannot lose information through a finite quotient, finite-index
subgroup, finite codomain, or finite image. -/
def BottcherAddDivisibleFiniteCoverAlgebraTarget : Prop :=
  (∀ {G : Type} [AddCommGroup G] (H : AddSubgroup G),
    (∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, n • x = g) →
    Finite (G ⧸ H) → H = ⊤) ∧
  (∀ {G : Type} [AddCommGroup G] (H : AddSubgroup G), H.FiniteIndex →
    (∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, n • x = g) → H = ⊤) ∧
  (∀ {G Q : Type} [AddCommGroup G] [AddCommGroup Q], Finite Q → (φ : G →+ Q) →
    (∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, n • x = g) → ∀ g : G, φ g = 0) ∧
  (∀ {G Q : Type} [AddCommGroup G] [AddCommGroup Q] (φ : G →+ Q), Finite φ.range →
    (∀ n : ℕ, 0 < n → ∀ g : G, ∃ x : G, n • x = g) → ∀ g : G, φ g = 0)

/-- Formal wrapper: additive divisible monodromy has no nontrivial finite quotient, finite-index loss,
finite codomain shadow, or finite image. -/
theorem bottcher_pruefer_additive_divisible_finite_cover_obstruction :
    BottcherAddDivisibleFiniteCoverAlgebraTarget := by
  constructor
  · intro G hG H hdiv hfin
    haveI : Finite (G ⧸ H) := hfin
    exact Bottcher.addSubgroup_eq_top_of_nsmulDivisible_finite_quotient H hdiv
  constructor
  · intro G hG H hfinite hdiv
    haveI : H.FiniteIndex := hfinite
    exact Bottcher.addSubgroup_eq_top_of_nsmulDivisible_finiteIndex H hdiv
  constructor
  · intro G Q hG hQ hfin φ hdiv g
    haveI : Finite Q := hfin
    exact Bottcher.addMonoidHom_eq_zero_of_nsmulDivisible_finite_codomain φ hdiv g
  · intro G Q hG hQ φ hfin hdiv g
    haveI : Finite φ.range := hfin
    exact Bottcher.addMonoidHom_eq_zero_of_nsmulDivisible_finite_range φ hdiv g

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Exact additive subgroup form of the Böttcher-Prüfer finite-cover clarification: if `D` is divisible
inside an ambient abelian monodromy group, every finite quotient kills `D`; for a finite-index subgroup
`B`, this says `D ≤ B` and hence `B ∩ D = D`. -/
def BottcherAddDivisibleSubgroupFiniteCoverTarget : Prop :=
  (∀ {A : Type} [AddCommGroup A] (D B : AddSubgroup A),
    (∀ n : ℕ, 0 < n → ∀ d : A, d ∈ D → ∃ e : A, e ∈ D ∧ n • e = d) →
    Finite (A ⧸ B) → D ≤ B) ∧
  (∀ {A : Type} [AddCommGroup A] (D B : AddSubgroup A), B.FiniteIndex →
    (∀ n : ℕ, 0 < n → ∀ d : A, d ∈ D → ∃ e : A, e ∈ D ∧ n • e = d) →
    D ≤ B ∧ B ⊓ D = D)

/-- Formal wrapper: the divisible Prüfer subgroup survives every finite-index cover subgroup. -/
theorem bottcher_pruefer_divisible_subgroup_finite_cover_obstruction :
    BottcherAddDivisibleSubgroupFiniteCoverTarget := by
  constructor
  · intro A hA D B hdiv hfin
    haveI : Finite (A ⧸ B) := hfin
    exact Bottcher.addSubgroup_le_of_nsmulDivisible_of_finite_quotient D B hdiv
  · intro A hA D B hfinite hdiv
    haveI : B.FiniteIndex := hfinite
    exact ⟨Bottcher.addSubgroup_le_of_nsmulDivisible_of_finiteIndex D B hdiv,
      Bottcher.addSubgroup_inf_eq_right_of_nsmulDivisible_of_finiteIndex D B hdiv⟩

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Exact image-step target for the finite-cover proof: finite-index source subgroups have finite-index
image inside the monodromy image, and therefore still contain every divisible subgroup of that image. -/
def BottcherAddFiniteIndexImageDivisibleSubgroupTarget : Prop :=
  (∀ {G A : Type} [AddGroup G] [AddGroup A] (H : AddSubgroup G), H.FiniteIndex →
    (ρ : G →+ A) → (H.map ρ.rangeRestrict).FiniteIndex) ∧
  (∀ {G A : Type} [AddGroup G] [AddCommGroup A] (H : AddSubgroup G), H.FiniteIndex →
    (ρ : G →+ A) → (D : AddSubgroup ρ.range) →
    (∀ n : ℕ, 0 < n → ∀ d : ρ.range, d ∈ D → ∃ e : ρ.range, e ∈ D ∧ n • e = d) →
    D ≤ H.map ρ.rangeRestrict ∧ (H.map ρ.rangeRestrict) ⊓ D = D)

/-- Formal wrapper: `rho(H)` has finite index in `rho(G)`, so finite covers still see the divisible
Prüfer subgroup in the monodromy image. -/
theorem bottcher_pruefer_finite_index_image_divisible_subgroup_obstruction :
    BottcherAddFiniteIndexImageDivisibleSubgroupTarget := by
  constructor
  · intro G A hG hA H hfinite ρ
    haveI : H.FiniteIndex := hfinite
    exact Bottcher.addSubgroup_map_rangeRestrict_finiteIndex H ρ
  · intro G A hG hA H hfinite ρ D hdiv
    haveI : H.FiniteIndex := hfinite
    exact ⟨Bottcher.addSubgroup_le_map_rangeRestrict_of_nsmulDivisible_finiteIndex H ρ D hdiv,
      Bottcher.addSubgroup_inf_map_rangeRestrict_eq_right_of_nsmulDivisible_finiteIndex H ρ D hdiv⟩

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Final nontriviality target for the finite-cover proof: if the monodromy image contains a nonzero
divisible subgroup, every finite-index source subgroup has a loop with nonzero monodromy, so the
restricted monodromy cannot be identically zero. -/
def BottcherAddFiniteIndexRestrictionNontrivialTarget : Prop :=
  (∀ {G A : Type} [AddGroup G] [AddCommGroup A] (H : AddSubgroup G), H.FiniteIndex →
    (ρ : G →+ A) → (D : AddSubgroup ρ.range) →
    (∀ n : ℕ, 0 < n → ∀ d : ρ.range, d ∈ D → ∃ e : ρ.range, e ∈ D ∧ n • e = d) →
    (∃ d : ρ.range, d ∈ D ∧ d ≠ 0) → ∃ h : G, h ∈ H ∧ ρ h ≠ 0) ∧
  (∀ {G A : Type} [AddGroup G] [AddCommGroup A] (H : AddSubgroup G), H.FiniteIndex →
    (ρ : G →+ A) → (D : AddSubgroup ρ.range) →
    (∀ n : ℕ, 0 < n → ∀ d : ρ.range, d ∈ D → ∃ e : ρ.range, e ∈ D ∧ n • e = d) →
    (∃ d : ρ.range, d ∈ D ∧ d ≠ 0) → ¬ ∀ h : G, h ∈ H → ρ h = 0)

/-- Formal wrapper: finite covers cannot make the monodromy restriction trivial while a nonzero divisible
Prüfer subgroup survives in the image. -/
theorem bottcher_pruefer_finite_index_restriction_nontrivial_obstruction :
    BottcherAddFiniteIndexRestrictionNontrivialTarget := by
  constructor
  · intro G A hG hA H hfinite ρ D hdiv hne
    haveI : H.FiniteIndex := hfinite
    exact Bottcher.exists_mem_finiteIndex_subgroup_apply_ne_zero_of_nsmulDivisible_nontrivial
      H ρ D hdiv hne
  · intro G A hG hA H hfinite ρ D hdiv hne
    haveI : H.FiniteIndex := hfinite
    exact Bottcher.not_forall_mem_finiteIndex_subgroup_apply_eq_zero_of_nsmulDivisible_nontrivial
      H ρ D hdiv hne

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Exact Hurwitz target: for nonintegral parameter `s`, the harmonic pole-root input is precisely
rational-tail independence for the all-`N` harmonic Hurwitz tails. -/
def HurwitzHarmonicPoleRootExactTarget : Prop :=
  ∀ (N : ℕ) (s : ℂ), (∀ k : ℤ, s ≠ (k : ℂ)) →
    (HurwitzAllNTailIndependence.RationalTailIndependent (N := N)
      (HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s) ↔
    HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s)

/-- Formal wrapper: the analytic pole-root provider has exactly the same Lean content as harmonic
rational-tail independence. -/
theorem hurwitz_harmonic_pole_root_exact_target : HurwitzHarmonicPoleRootExactTarget := by
  intro N s hsZ
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.rationalTailIndependent_harmonic_iff_poleRootInput hsZ

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Connected U0 Step 2 capstone: if a preconnected basin avoids the unit circle, contains an exterior
point, and the filled set lies inside the closed unit disk, complete invariance forces `b = 0`. -/
def U0BasinAvoidsCircleForcesExceptionalTarget : Prop :=
  ∀ {K : Set ℂ} {b w : ℂ},
    IsPreconnected Kᶜ →
    (∀ z ∈ Kᶜ, ‖z‖ ≠ 1) →
    w ∈ Kᶜ → 1 < ‖w‖ →
    K ⊆ Metric.closedBall (0 : ℂ) 1 →
    (∀ z : ℂ, z ^ 2 + b ∈ K ↔ z ∈ K) →
    b = 0

/-- Formal wrapper for the connected `u₀ ⟂ φ_b` Step 2 endgame. -/
theorem u0_basin_avoids_circle_forces_exceptional_card :
    U0BasinAvoidsCircleForcesExceptionalTarget := by
  intro K b w hΩc havoid hw hwn hKsub hinvK
  exact U0PhiCard.eq_zero_of_basin_avoids_circle_of_subset_disk_and_completeInvariant
    hΩc havoid hw hwn hKsub hinvK

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Connected U0 Step 2 crossing target: with the same disk-containment and complete-invariance
hypotheses, a nonzero parameter forces the basin to meet the unit circle. -/
def U0BasinCircleCrossingFromNonzeroTarget : Prop :=
  ∀ {K : Set ℂ} {b w : ℂ},
    b ≠ 0 →
    IsPreconnected Kᶜ →
    w ∈ Kᶜ → 1 < ‖w‖ →
    K ⊆ Metric.closedBall (0 : ℂ) 1 →
    (∀ z : ℂ, z ^ 2 + b ∈ K ↔ z ∈ K) →
    ∃ z : ℂ, z ∈ Kᶜ ∧ ‖z‖ = 1

/-- Formal wrapper for the positive unit-circle crossing form of the connected U0 card. -/
theorem u0_basin_circle_crossing_from_nonzero_card :
    U0BasinCircleCrossingFromNonzeroTarget := by
  intro K b w hb hΩc hw hwn hKsub hinvK
  exact U0PhiCard.exists_circle_point_of_nonzero_basin_subset_disk_and_completeInvariant
    hb hΩc hw hwn hKsub hinvK

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Connected U0 Step 2-to-Step 3 handoff: an open basin containing a unit-circle point contains
unit-circle points frequently in the punctured neighbourhood of that point. This turns the positive
crossing output into the accumulating-set input consumed by `U0PhiCard.u0_phi_card_step3`. -/
def U0OpenUnitCircleAccumulationTarget : Prop :=
  ∀ {Ω : Set ℂ} (_ : IsOpen Ω) {z₀ : ℂ}, z₀ ∈ Ω → ‖z₀‖ = 1 →
    ∃ᶠ z in 𝓝[≠] z₀, z ∈ Ω ∩ {z : ℂ | ‖z‖ = 1}

/-- Formal wrapper for the open unit-circle accumulation handoff in the U0 cards. -/
theorem u0_open_unitCircle_accumulation_card : U0OpenUnitCircleAccumulationTarget := by
  intro Ω hΩo z₀ hzΩ hz₀
  exact U0PhiCard.frequently_mem_open_unitCircle_of_mem hΩo hzΩ hz₀

/-- Card proof object for the U0 Step-3 continuation contradiction after the Step-2 output has been
reduced to a single open-basin unit-circle crossing point. -/
def u0_phi_no_relation_3var_open_crossing_formal_proof :=
  @U0PhiCard.u0_phi_no_relation_3var_open_crossing

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- One-coordinate Kummer radical input target: the same radical data format used by the Kummer
no-relation close already forces the coordinate to be transcendental. -/
def BottcherKummerRadicalTranscendenceTarget : Prop :=
  ∀ {K V : Type} [Field K] [Field V] [Algebra K V] (G : V), G ≠ 0 →
    (∀ d : ℕ, ∃ (B : Type) (_ : Field B) (_ : Algebra K B)
      (i : B →ₐ[K] V) (a ζ : B) (k : ℕ),
      d < 2 ^ k ∧ IsPrimitiveRoot ζ (2 ^ k) ∧ Irreducible (X ^ (2 ^ k) - C a) ∧
      G ^ (2 ^ k) = i a) →
    Transcendental K G

/-- Formal wrapper for one-coordinate transcendence directly from Kummer radical inputs. -/
theorem bottcher_kummer_radical_transcendence : BottcherKummerRadicalTranscendenceTarget := by
  intro K V hK hV hKV G hG inputs
  exact Bottcher.transcendental_of_kummer_radical_inputs G hG inputs

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Strengthened disconnected Kummer close: the `φ₂` transcendence input is derived internally from its
own radical tower, leaving nonzero coordinates plus the two radical input towers. -/
def q62_disconnected_kummer_with_radical_transcendence_formal_proof :=
  @Bottcher.q62_disconnected_kummer_with_radical_transcendence

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Disconnected q62 radical close with no separate `φ₂` transcendence input: both coordinates are
supplied by non-square radical towers. -/
def q62_disconnected_two_radical_data_formal_proof :=
  @Bottcher.q62_disconnected_of_two_radical_data

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Deep-data q62 disconnected close where both coordinates carry their own non-square radical data, so
no separate `φ₂` transcendence input remains. -/
def q62_disconnected_deep_data_two_radical_formal_proof :=
  @Bottcher.q62_disconnected_of_deepData_two_radical

/-- Image-winding version of the two-radical deep-data q62 close. -/
def q62_disconnected_image_winding_deep_data_two_radical_formal_proof :=
  @Bottcher.q62_disconnected_of_imageWindingDeepData_two_radical

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Escape-form deep-data q62 disconnected close where `φ₂` compatibility and transcendence are both
built from supplied escape/radical data rather than separate premises. -/
def q62_disconnected_deep_data_escape_two_radical_formal_proof :=
  @Bottcher.q62_disconnected_of_deepData_escape_two_radical

/-- Image-winding version of the escape-form two-radical deep-data q62 close. -/
def q62_disconnected_image_winding_deep_data_escape_two_radical_formal_proof :=
  @Bottcher.q62_disconnected_of_imageWindingDeepData_escape_two_radical

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Half-integer Hurwitz N=2 block-split target: when `s ∉ ℤ` but `2s ∈ ℤ`, the order-two
monodromy split kills the sign-changing `Ψ` block and leaves the invariant residual `Φ + Θ = 0`.
This is the proved replacement for the generic three-eigenvalue split in the missing N=2 branch. -/
def HurwitzN2HalfIntegerBlockSplitTarget : Prop :=
  ∀ (s : ℂ) (n : ℕ), (∀ k : ℤ, s ≠ (k : ℂ)) → (∃ k : ℤ, 2 * s = (k : ℂ)) →
  ∀ (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ)
      (R : Fin 3 → ℂ → ℂ),
    (∀ k z, R k (z + 2 * (Real.pi : ℂ) * Complex.I) = R k z) →
    ∀ {B : ℝ} {z0 : ℂ}, z0.re < B → -Real.pi < z0.im → z0.im < Real.pi →
    AnalyticOnNhd ℂ
      (fun z => HurwitzN2Main.PhiB s n q z + HurwitzN2Main.PsiB s n q l R z
        + HurwitzN2Main.ThetaB s n q l cc R z) {z : ℂ | z.re < B} →
    (∀ z : ℂ, z.re < B → -Real.pi < z.im → z.im < Real.pi →
      HurwitzN2Main.PhiB s n q z + HurwitzN2Main.PsiB s n q l R z
        + HurwitzN2Main.ThetaB s n q l cc R z = 0) →
    (∀ z : ℂ, z.re < B → HurwitzN2Main.PsiB s n q l R z = 0)
      ∧ (∀ z : ℂ, z.re < B →
        HurwitzN2Main.PhiB s n q z + HurwitzN2Main.ThetaB s n q l cc R z = 0)

/-- Formal wrapper for the newly proved half-integer Hurwitz N=2 block split. -/
theorem hurwitz_n2_half_integer_block_split_card : HurwitzN2HalfIntegerBlockSplitTarget := by
  intro s n hs h2s q l cc R hRper B z0 h0re h0im1 h0im2 hanalytic hrel
  exact HurwitzN2HalfInteger.n2_blocks_order_two_split s n hs h2s q l cc R hRper
    h0re h0im1 h0im2 hanalytic hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Exact Lean target for `hurwitz-quadratic-n2-density-shadow.md`: the previous generic wrapper's
`2s ∉ ℤ` side condition is removed by the half-integer branch in `Hurwitz.N2HalfInteger`. -/
def HurwitzN2DensityShadowTarget (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, (k : ℂ) ≠ s) →
  ∀ (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ)
      (N : ℕ),
    (∀ n, N ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval (-(n : ℂ) + Complex.exp z) *
          ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin 3, (l k).eval (-(n : ℂ) + Complex.exp z) *
            (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) →
    q 0 0 = 0 ∧ q 2 2 = 0 ∧ q 1 1 = 0 ∧ q 0 2 + q 2 0 = 0
      ∧ l 2 = 0 ∧ l 0 = 0 ∧ l 1 = 0 ∧ cc = 0

/-- Formal wrapper for the exact N=2 Hurwitz density-shadow card, including the half-integer branch. -/
theorem hurwitz_quadratic_n2_density_shadow (s : ℂ) :
    HurwitzN2DensityShadowTarget s := by
  intro hs1 hsZ q l cc N hrel
  exact HurwitzN2HalfInteger.hurwitz_n2_unconditional_all_noninteger
    (s := s) (N := N) hs1 hsZ q l cc hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Singleton harmonic pole-root target for the all-`N` Hurwitz card. The `N = 0` provider is fully
proved from the existing singleton rational-tail finite-difference obstruction, so it carries no
`HarmonicPoleRootInput` hypothesis. -/
def HurwitzHarmonicPoleRootN0Target : Prop :=
  ∀ s : ℂ, (∀ k : ℤ, s ≠ (k : ℂ)) →
    HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput 0 s

/-- Formal wrapper for the unconditional `N = 0` harmonic pole-root provider. -/
theorem hurwitz_harmonic_pole_root_N0 : HurwitzHarmonicPoleRootN0Target := by
  intro s hsZ
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicPoleRootInput_zero (s := s) hsZ

/-- Singleton-ladder relation-level close for the all-`N` Hurwitz card: in the `N = 0` case, a genuine
local degree-`≤ 2` relation forces the single quadratic coefficient, linear coefficient, and constant
coefficient to vanish, without any extra pole-root/tail-independence provider hypothesis. -/
def HurwitzN0CoefficientsCloseTarget (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (q : Fin (0 + 1) → Fin (0 + 1) → Polynomial ℂ)
    (l : Fin (0 + 1) → Polynomial ℂ) (cc : Polynomial ℂ),
    (∀ i j, q i j = q j i) →
    ∀ {M : ℕ},
      (∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
        z.im < Real.pi →
        (∑ i : Fin (0 + 1), ∑ j : Fin (0 + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
            * ((Complex.exp (-(s + (i : ℂ)) * z) + HurwitzN2Tail.tailFactored s (i : ℕ) n (Complex.exp z))
              * (Complex.exp (-(s + (j : ℂ)) * z) + HurwitzN2Tail.tailFactored s (j : ℕ) n (Complex.exp z))))
          + (∑ k : Fin (0 + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
              * (Complex.exp (-(s + (k : ℂ)) * z) + HurwitzN2Tail.tailFactored s (k : ℕ) n (Complex.exp z)))
          + cc.eval (-(n : ℂ) + Complex.exp z) = 0) →
      (∀ i j : Fin (0 + 1), q i j = 0) ∧ (∀ j : Fin (0 + 1), l j = 0) ∧ cc = 0

/-- Formal wrapper for the unconditional singleton-ladder relation close. -/
theorem hurwitz_N0_coefficients_close_from_relation (s : ℂ) :
    HurwitzN0CoefficientsCloseTarget s := by
  intro hs1 hsZ q l cc hSymm M hrel
  exact HurwitzAllNRelationClose.all_coefficients_close_of_genuine_relation_N0
    (s := s) (M := M) hs1 hsZ q l cc hSymm hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Singleton-ladder shifted-Hurwitz row/constant close with no harmonic-tail or pole-root provider
hypothesis. This is the `N = 0` downstream row-close target after the singleton harmonic tail has been
fully discharged. -/
def HurwitzHzetaRowCloseN0Target (s : ℂ) : Prop :=
  1 < s.re → (∀ k : ℤ, s ≠ (k : ℂ)) →
    ∀ (q : Fin (0 + 1) → Fin (0 + 1) → Polynomial ℂ)
      (l : Fin (0 + 1) → Polynomial ℂ) (cc : Polynomial ℂ),
      (∀ j : Fin (0 + 1), ∃ M : ℕ, ∀ n, M ≤ n →
        (l j).eval (-(n : ℂ)) +
          (∑ i : Fin (0 + 1),
            (q i j).eval (-(n : ℂ)) *
              (2 * HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))) = 0) →
      (∃ M : ℕ, ∀ n, M ≤ n → cc.eval (-(n : ℂ)) = 0) →
      (∀ i j, q i j = 0) ∧ (∀ j, l j = 0) ∧ cc = 0

/-- Formal wrapper for the unconditional singleton-ladder shifted-Hurwitz row close. -/
theorem hurwitz_hzeta_row_close_N0 (s : ℂ) : HurwitzHzetaRowCloseN0Target s := by
  intro hs1 hsZ q l cc hrow hcc
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.rows_and_constant_close_of_hzeta_shift_neg_nat_N0
    hs1 hsZ q l cc hrow hcc

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Singleton-ladder relation-level close with no symmetry premise. This is the exact `N = 0` card-facing
form: the only remaining assumptions are the analytic parameter conditions and the genuine local
relation. -/
def HurwitzN0CoefficientsCloseNoSymmTarget (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (q : Fin (0 + 1) → Fin (0 + 1) → Polynomial ℂ)
    (l : Fin (0 + 1) → Polynomial ℂ) (cc : Polynomial ℂ),
    ∀ {M : ℕ},
      (∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
        z.im < Real.pi →
        (∑ i : Fin (0 + 1), ∑ j : Fin (0 + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
            * ((Complex.exp (-(s + (i : ℂ)) * z) + HurwitzN2Tail.tailFactored s (i : ℕ) n (Complex.exp z))
              * (Complex.exp (-(s + (j : ℂ)) * z) + HurwitzN2Tail.tailFactored s (j : ℕ) n (Complex.exp z))))
          + (∑ k : Fin (0 + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
              * (Complex.exp (-(s + (k : ℂ)) * z) + HurwitzN2Tail.tailFactored s (k : ℕ) n (Complex.exp z)))
          + cc.eval (-(n : ℂ) + Complex.exp z) = 0) →
      (∀ i j : Fin (0 + 1), q i j = 0) ∧ (∀ j : Fin (0 + 1), l j = 0) ∧ cc = 0

/-- Formal wrapper for the symmetry-free singleton-ladder relation close. -/
theorem hurwitz_N0_coefficients_close_from_relation_noSymm (s : ℂ) :
    HurwitzN0CoefficientsCloseNoSymmTarget s := by
  intro hs1 hsZ q l cc M hrel
  exact HurwitzAllNRelationClose.all_coefficients_close_of_genuine_relation_N0_noSymm
    (s := s) (M := M) hs1 hsZ q l cc hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Scalar singleton-ladder relation close for the Hurwitz card. This is the cleanest `N = 0` target:
one quadratic coefficient polynomial, one linear coefficient polynomial, and one constant coefficient
polynomial all vanish from a genuine local degree-`≤ 2` relation. -/
def HurwitzN0ScalarCoefficientsCloseTarget (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ q l cc : Polynomial ℂ,
    ∀ {M : ℕ},
      (∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
        z.im < Real.pi →
        q.eval (-(n : ℂ) + Complex.exp z)
            * ((Complex.exp (-s * z) + HurwitzN2Tail.tailFactored s 0 n (Complex.exp z))
              * (Complex.exp (-s * z) + HurwitzN2Tail.tailFactored s 0 n (Complex.exp z)))
          + l.eval (-(n : ℂ) + Complex.exp z)
              * (Complex.exp (-s * z) + HurwitzN2Tail.tailFactored s 0 n (Complex.exp z))
          + cc.eval (-(n : ℂ) + Complex.exp z) = 0) →
      q = 0 ∧ l = 0 ∧ cc = 0

/-- Formal wrapper for the scalar singleton-ladder relation close. -/
theorem hurwitz_N0_scalar_coefficients_close_from_relation (s : ℂ) :
    HurwitzN0ScalarCoefficientsCloseTarget s := by
  intro hs1 hsZ q l cc M hrel
  exact HurwitzAllNRelationClose.all_coefficients_close_of_genuine_relation_N0_scalar
    (s := s) (M := M) hs1 hsZ q l cc hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Scalar singleton-ladder shifted-Hurwitz row close. If the one row equation
`l(-n)+2*q(-n)*ζ(s,-n)=0` holds eventually and the residual constant coefficient vanishes eventually,
then all three coefficient polynomials vanish. -/
def HurwitzHzetaRowCloseN0ScalarTarget (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ q l cc : Polynomial ℂ,
    (∃ M : ℕ, ∀ n, M ≤ n →
      l.eval (-(n : ℂ)) + q.eval (-(n : ℂ)) *
        (2 * HurwitzZetaShift.hzeta s (-(n : ℂ))) = 0) →
    (∃ M : ℕ, ∀ n, M ≤ n → cc.eval (-(n : ℂ)) = 0) →
    q = 0 ∧ l = 0 ∧ cc = 0

/-- Formal wrapper for the scalar singleton-ladder shifted-Hurwitz row close. -/
theorem hurwitz_hzeta_row_close_N0_scalar (s : ℂ) :
    HurwitzHzetaRowCloseN0ScalarTarget s := by
  intro hs1 hsZ q l cc hrow hcc
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.rows_and_constant_close_of_hzeta_shift_neg_nat_N0_scalar
    hs1 hsZ q l cc hrow hcc

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Finite shifted-power obstruction target for the Hurwitz all-`N` tail work: any eventual polynomial
relation among the powers `n^(-(s+i))`, `0 ≤ i ≤ N`, has zero compressed coefficient polynomial after
multiplication by `n^N`. -/
def HurwitzFiniteShiftedPowerObstructionTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ),
    (∀ᶠ n : ℕ in Filter.atTop,
      (∑ i : Fin (N + 1), (coeff i).eval (n : ℂ) * (n : ℂ) ^ (-(s + (i : ℂ))))
        = P.eval (n : ℂ)) →
    HurwitzNonRat.shiftedPowerPolynomial N coeff = 0

/-- Formal wrapper for the finite shifted-power obstruction extracted from the non-rationality theorem. -/
theorem hurwitz_finite_shifted_power_obstruction (N : ℕ) :
    HurwitzFiniteShiftedPowerObstructionTarget N := by
  intro s hs coeff P hrel
  exact HurwitzNonRat.shiftedPowerPolynomial_eq_zero_of_eventually_cpow_sum_eq_poly hs coeff P hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Constant-coefficient shifted-power obstruction target: no eventual polynomial function can equal a
nontrivial scalar linear combination of `n^(-(s+i))`, `0 ≤ i ≤ N`, when `s` is nonintegral. -/
def HurwitzConstantShiftedPowerObstructionTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (c : Fin (N + 1) → ℂ) (P : Polynomial ℂ),
    (∀ᶠ n : ℕ in Filter.atTop,
      (∑ i : Fin (N + 1), c i * (n : ℂ) ^ (-(s + (i : ℂ)))) = P.eval (n : ℂ)) →
    (∀ i : Fin (N + 1), c i = 0) ∧ P = 0

/-- Formal wrapper for the constant-coefficient shifted-power obstruction. -/
theorem hurwitz_constant_shifted_power_obstruction (N : ℕ) :
    HurwitzConstantShiftedPowerObstructionTarget N := by
  intro s hs c P hrel
  exact HurwitzNonRat.const_coefficients_eq_zero_of_eventually_cpow_sum_eq_poly hs c P hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Tower-free U0 Kummer re-pick target. Per relation degree, a finite carrier whose root maps to
`φ_b`, whose base element maps to `u₀`, and whose deck has order larger than the degree already gives
the card carrier independence. -/
def U0PhiIndependenceRepickCarrierTarget {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b) : Prop :=
  (∀ d : ℕ,
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∃ (M : Type) (_ : Field M) (_ : Algebra (RatFunc ℂ) M)
      (ψ : M →ₐ[RatFunc ℂ] meroField U) (Fk Gk ζ : M) (σ : M ≃ₐ[RatFunc ℂ] M),
      Function.Injective ψ ∧ ψ Fk = phiMero b hU_esc ∧
      ψ Gk = algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext) ∧
      Fk ≠ 0 ∧ d < orderOf ζ ∧ σ Gk = Gk ∧ σ ζ = ζ ∧ σ Fk = ζ * Fk) →
  U0PhiIndependenceCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for the tower-free U0 Kummer re-pick route. -/
theorem u0_phi_independence_repick_card {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b) :
    U0PhiIndependenceRepickCarrierTarget hUo hUc hUne hUinf hU_ext hU_esc := by
  intro data
  exact U0KummerRepick.u0_phib_noRelation_repick hUo hUc hUne hUinf hU_ext hU_esc data

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Constant-coefficient harmonic-tail obstruction for the Hurwitz all-`N` card. This is a genuine
provider-free subcase of the harmonic-tail rational independence target: a single finite difference
reduces the relation to the shifted-power obstruction. -/
def HurwitzHarmonicTailConstantCoeffTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (c : Fin (N + 1) → ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (Polynomial.C (c i)).eval (-(n : ℂ)) *
        HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s i n)
        = P.eval (-(n : ℂ))) →
    (∀ i : Fin (N + 1), c i = 0) ∧ P = 0

/-- Formal wrapper for the constant-coefficient harmonic-tail obstruction. -/
theorem hurwitz_harmonic_tail_constant_coefficients (N : ℕ) :
    HurwitzHarmonicTailConstantCoeffTarget N := by
  intro s hsZ c P M hrel
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.constant_coefficients_zero_of_harmonicTail_relation
    (N := N) (s := s) hsZ c P hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Constant-coefficient pole-root bridge for the Hurwitz all-`N` card. In the constant-coefficient
subcase, the finite-difference obstruction already forces the harmonic-tail relation to be trivial, so
all Gamma pole-root identities follow without an extra analytic provider. -/
def HurwitzHarmonicPoleRootConstantCoeffTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (c : Fin (N + 1) → ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (Polynomial.C (c i)).eval (-(n : ℂ)) *
        HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s i n)
        = P.eval (-(n : ℂ))) →
    ∀ (d n : ℕ),
      (∑ i : Fin (N + 1),
        (Polynomial.C (c i)).coeff d * Complex.Gamma (1 - s - (i : ℂ)) *
          (HurwitzPolylogPoleTower.twoPiI * ((n + 1 : ℕ) : ℂ)) ^ (i : ℕ)) = 0

/-- Formal wrapper for the constant-coefficient pole-root bridge. -/
theorem hurwitz_harmonic_pole_root_constant_coefficients (N : ℕ) :
    HurwitzHarmonicPoleRootConstantCoeffTarget N := by
  intro s hsZ c P M hrel d n
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicPoleRootInput_constant_coeff_relation
    (N := N) (s := s) hsZ c P hrel d n

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Constant-coefficient actual shifted-Hurwitz obstruction for the all-`N` card. This is the
provider-free subcase for the genuine values `ζ(s+i,-n)`: finite differencing gives the shifted-power
obstruction with nonzero phase factors. -/
def HurwitzHzetaShiftConstantCoeffTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, 1 < s.re → (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (c : Fin (N + 1) → ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (Polynomial.C (c i)).eval (-(n : ℂ)) *
        HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ))) = P.eval (-(n : ℂ))) →
    (∀ i : Fin (N + 1), c i = 0) ∧ P = 0

/-- Formal wrapper for the constant-coefficient actual shifted-Hurwitz obstruction. -/
theorem hurwitz_hzeta_shift_constant_coefficients (N : ℕ) :
    HurwitzHzetaShiftConstantCoeffTarget N := by
  intro s hs1 hsZ c P M hrel
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.constant_coefficients_zero_of_hzeta_shift_neg_nat_relation
    (N := N) (s := s) hs1 hsZ c P hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Polynomial-coefficient finite-difference transform for the all-`N` Hurwitz harmonic-tail provider.
This is the exact induction brick: a harmonic-tail relation implies a new relation with coefficient
finite differences plus explicit shifted-power terms. -/
def HurwitzHarmonicTailRelationFiniteDifferenceTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ} (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) *
        HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s i n)
        = P.eval (-(n : ℂ))) →
    ∀ n, M + 1 ≤ n →
      (∑ i : Fin (N + 1),
        ((coeff i).comp (-X) - (coeff i).comp (1 - X)).eval (n : ℂ) *
          HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s i n) +
      (∑ i : Fin (N + 1),
        ((coeff i).comp (1 - X)).eval (n : ℂ) * (n : ℂ) ^ (-(s + (i : ℂ)))) =
      (P.comp (-X) - P.comp (1 - X)).eval (n : ℂ)

/-- Formal wrapper for the polynomial-coefficient harmonic-tail finite-difference transform. -/
theorem hurwitz_harmonic_tail_relation_finite_difference (N : ℕ) :
    HurwitzHarmonicTailRelationFiniteDifferenceTarget N := by
  intro s coeff P M hrel n hn
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail_relation_finite_difference
    (N := N) (s := s) coeff P hrel n hn

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Polynomial-coefficient finite-difference transform for actual shifted-Hurwitz values. This is the
actual-value analogue of `HurwitzHarmonicTailRelationFiniteDifferenceTarget`, with the nonzero phase
factors made explicit. -/
def HurwitzHzetaShiftRelationFiniteDifferenceTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, 1 < s.re →
  ∀ (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) *
        HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ))) = P.eval (-(n : ℂ))) →
    ∀ n, M + 1 ≤ n →
      (∑ i : Fin (N + 1),
        ((coeff i).comp (-X) - (coeff i).comp (1 - X)).eval (n : ℂ) *
          HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ))) +
      (∑ i : Fin (N + 1),
        ((coeff i).comp (1 - X)).eval (n : ℂ) *
          (Complex.exp (-((Real.pi : ℂ) * Complex.I * (s + (i : ℂ)))) *
            (n : ℂ) ^ (-(s + (i : ℂ))))) =
      (P.comp (-X) - P.comp (1 - X)).eval (n : ℂ)

/-- Formal wrapper for the polynomial-coefficient shifted-Hurwitz finite-difference transform. -/
theorem hurwitz_hzeta_shift_relation_finite_difference (N : ℕ) :
    HurwitzHzetaShiftRelationFiniteDifferenceTarget N := by
  intro s hs1 coeff P M hrel n hn
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.hzeta_shift_neg_nat_relation_finite_difference
    (N := N) (s := s) hs1 coeff P hrel n hn

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Algebraic finite-difference-zero target: a polynomial with `p(-X)=p(1-X)` is constant. -/
def HurwitzPolynomialZeroFiniteDifferenceTarget : Prop :=
  ∀ p : Polynomial ℂ, p.comp (-Polynomial.X) = p.comp (1 - Polynomial.X) → p = Polynomial.C (p.eval 0)

/-- Formal wrapper for the polynomial finite-difference-zero lemma. -/
theorem hurwitz_polynomial_zero_finite_difference_constant :
    HurwitzPolynomialZeroFiniteDifferenceTarget := by
  intro p h
  exact HurwitzAllNTailIndependence.polynomial_eq_C_of_comp_neg_eq_comp_oneSub h

/-- Harmonic-tail close under zero coefficient finite differences. This is the first provider-free
subcase using the polynomial-coefficient finite-difference induction brick: if all coefficient finite
differences already vanish, all coefficients are constant and the constant-coefficient obstruction
closes the relation. -/
def HurwitzHarmonicTailZeroFiniteDifferenceCoeffTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ i : Fin (N + 1), (coeff i).comp (-Polynomial.X) - (coeff i).comp (1 - Polynomial.X) = 0) →
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) *
        HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s i n)
        = P.eval (-(n : ℂ))) →
    (∀ i : Fin (N + 1), coeff i = 0) ∧ P = 0

/-- Formal wrapper for harmonic-tail relations with zero coefficient finite differences. -/
theorem hurwitz_harmonic_tail_zero_finite_difference_coefficients (N : ℕ) :
    HurwitzHarmonicTailZeroFiniteDifferenceCoeffTarget N := by
  intro s hsZ coeff P M hdiff0 hrel
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.coefficients_zero_of_harmonicTail_relation_of_zero_finite_difference
    (N := N) (s := s) hsZ coeff P hdiff0 hrel

/-- Actual shifted-Hurwitz close under zero coefficient finite differences. -/
def HurwitzHzetaShiftZeroFiniteDifferenceCoeffTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, 1 < s.re → (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ i : Fin (N + 1), (coeff i).comp (-Polynomial.X) - (coeff i).comp (1 - Polynomial.X) = 0) →
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) *
        HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ))) = P.eval (-(n : ℂ))) →
    (∀ i : Fin (N + 1), coeff i = 0) ∧ P = 0

/-- Formal wrapper for shifted-Hurwitz relations with zero coefficient finite differences. -/
theorem hurwitz_hzeta_shift_zero_finite_difference_coefficients (N : ℕ) :
    HurwitzHzetaShiftZeroFiniteDifferenceCoeffTarget N := by
  intro s hs1 hsZ coeff P M hdiff0 hrel
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.coefficients_zero_of_hzeta_shift_relation_of_zero_finite_difference
    (N := N) (s := s) hs1 hsZ coeff P hdiff0 hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Weighted-degree extraction target for compressed shifted-power combinations: a nonzero coefficient
with unique maximal `natDegree + shift` forces the compressed polynomial to be nonzero. -/
def HurwitzShiftedPowerUniqueWeightedDegreeTarget (N : ℕ) : Prop :=
  ∀ (coeff : Fin (N + 1) → Polynomial ℂ) (k : Fin (N + 1)),
    coeff k ≠ 0 →
    (∀ i : Fin (N + 1), i ≠ k →
      (coeff i).natDegree + (N - (i : ℕ)) < (coeff k).natDegree + (N - (k : ℕ))) →
    HurwitzNonRat.shiftedPowerPolynomial N coeff ≠ 0

/-- Formal wrapper for the unique weighted-degree shifted-power extraction. -/
theorem hurwitz_shifted_power_unique_weighted_degree (N : ℕ) :
    HurwitzShiftedPowerUniqueWeightedDegreeTarget N := by
  intro coeff k hk huniq
  exact HurwitzNonRat.shiftedPowerPolynomial_ne_zero_of_unique_weighted_natDegree hk huniq

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Collision form of the weighted-degree shifted-power extraction: if the compressed polynomial is zero,
then any nonzero coefficient must have another coefficient with at least the same weighted degree. -/
def HurwitzShiftedPowerWeightedDegreeCollisionTarget (N : ℕ) : Prop :=
  ∀ (coeff : Fin (N + 1) → Polynomial ℂ) (k : Fin (N + 1)),
    HurwitzNonRat.shiftedPowerPolynomial N coeff = 0 →
    coeff k ≠ 0 →
    ∃ i : Fin (N + 1), i ≠ k ∧
      (coeff k).natDegree + (N - (k : ℕ)) ≤ (coeff i).natDegree + (N - (i : ℕ))

/-- Formal wrapper for the weighted-degree collision theorem. -/
theorem hurwitz_shifted_power_weighted_degree_collision (N : ℕ) :
    HurwitzShiftedPowerWeightedDegreeCollisionTarget N := by
  intro coeff k hD hk
  exact HurwitzNonRat.exists_weighted_natDegree_ge_of_shiftedPowerPolynomial_eq_zero hD hk

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Relation-level weighted-degree collision target for shifted powers: any eventual polynomial relation
among the shifted powers forces every nonzero coefficient to have a competing coefficient of at least
the same weighted degree. -/
def HurwitzShiftedPowerRelationWeightedDegreeCollisionTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ),
    (∀ᶠ n : ℕ in Filter.atTop,
      (∑ i : Fin (N + 1), (coeff i).eval (n : ℂ) * (n : ℂ) ^ (-(s + (i : ℂ))))
        = P.eval (n : ℂ)) →
    ∀ k : Fin (N + 1), coeff k ≠ 0 →
      ∃ i : Fin (N + 1), i ≠ k ∧
        (coeff k).natDegree + (N - (k : ℕ)) ≤ (coeff i).natDegree + (N - (i : ℕ))

/-- Formal wrapper for the relation-level weighted-degree collision theorem. -/
theorem hurwitz_shifted_power_relation_weighted_degree_collision (N : ℕ) :
    HurwitzShiftedPowerRelationWeightedDegreeCollisionTarget N := by
  intro s hs coeff P hrel k hk
  exact HurwitzNonRat.exists_weighted_natDegree_ge_of_eventually_cpow_sum_eq_poly hs coeff P hrel hk

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Unique weighted-degree vanishing target for compressed shifted-power polynomials: if the compressed
polynomial is zero, a coefficient with unique maximal `natDegree + shift` must vanish. -/
def HurwitzShiftedPowerUniqueWeightedDegreeVanishTarget (N : ℕ) : Prop :=
  ∀ (coeff : Fin (N + 1) → Polynomial ℂ) (k : Fin (N + 1)),
    HurwitzNonRat.shiftedPowerPolynomial N coeff = 0 →
    (∀ i : Fin (N + 1), i ≠ k →
      (coeff i).natDegree + (N - (i : ℕ)) < (coeff k).natDegree + (N - (k : ℕ))) →
    coeff k = 0

/-- Formal wrapper for unique weighted-degree vanishing in a compressed shifted-power polynomial. -/
theorem hurwitz_shifted_power_unique_weighted_degree_vanish (N : ℕ) :
    HurwitzShiftedPowerUniqueWeightedDegreeVanishTarget N := by
  intro coeff k hD huniq
  exact HurwitzNonRat.coeff_eq_zero_of_shiftedPowerPolynomial_eq_zero_of_unique_weighted_natDegree hD huniq

/-- Relation-level unique weighted-degree vanishing target for shifted powers. -/
def HurwitzShiftedPowerRelationUniqueWeightedDegreeVanishTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ),
    (∀ᶠ n : ℕ in Filter.atTop,
      (∑ i : Fin (N + 1), (coeff i).eval (n : ℂ) * (n : ℂ) ^ (-(s + (i : ℂ))))
        = P.eval (n : ℂ)) →
    ∀ k : Fin (N + 1),
      (∀ i : Fin (N + 1), i ≠ k →
        (coeff i).natDegree + (N - (i : ℕ)) < (coeff k).natDegree + (N - (k : ℕ))) →
      coeff k = 0

/-- Formal wrapper for relation-level unique weighted-degree vanishing. -/
theorem hurwitz_shifted_power_relation_unique_weighted_degree_vanish (N : ℕ) :
    HurwitzShiftedPowerRelationUniqueWeightedDegreeVanishTarget N := by
  intro s hs coeff P hrel k huniq
  exact HurwitzNonRat.coeff_eq_zero_of_eventually_cpow_sum_eq_poly_of_unique_weighted_natDegree
    hs coeff P hrel k huniq

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Exact compression identity target for shifted powers: on positive naturals, the finite shifted-power
sum equals the compressed polynomial times the lowest shifted power. -/
def HurwitzShiftedPowerCompressionIdentityTarget (N : ℕ) : Prop :=
  ∀ s : ℂ, ∀ coeff : Fin (N + 1) → Polynomial ℂ,
    ∀ᶠ n : ℕ in Filter.atTop,
      (∑ i : Fin (N + 1), (coeff i).eval (n : ℂ) * (n : ℂ) ^ (-(s + (i : ℂ)))) =
        (n : ℂ) ^ (-(s + (N : ℂ))) *
          (HurwitzNonRat.shiftedPowerPolynomial N coeff).eval (n : ℂ)

/-- Formal wrapper for the shifted-power compression identity. -/
theorem hurwitz_shifted_power_compression_identity (N : ℕ) :
    HurwitzShiftedPowerCompressionIdentityTarget N := by
  intro s coeff
  exact HurwitzNonRat.eventually_cpow_sum_eq_cpow_mul_shiftedPowerPolynomial_eval (N := N) s coeff

/-- Exact shifted-power relation close target: an eventual polynomial relation forces both the compressed
coefficient polynomial and the polynomial right side to vanish. -/
def HurwitzShiftedPowerExactRelationCloseTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ),
    (∀ᶠ n : ℕ in Filter.atTop,
      (∑ i : Fin (N + 1), (coeff i).eval (n : ℂ) * (n : ℂ) ^ (-(s + (i : ℂ))))
        = P.eval (n : ℂ)) →
    HurwitzNonRat.shiftedPowerPolynomial N coeff = 0 ∧ P = 0

/-- Formal wrapper for the exact shifted-power relation close. -/
theorem hurwitz_shifted_power_exact_relation_close (N : ℕ) :
    HurwitzShiftedPowerExactRelationCloseTarget N := by
  intro s hs coeff P hrel
  exact HurwitzNonRat.shiftedPowerPolynomial_eq_zero_and_rhs_eq_zero_of_eventually_cpow_sum_eq_poly
    hs coeff P hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Mixed finite-difference landing target for harmonic tails. -/
def HurwitzHarmonicTailMixedFiniteDifferenceTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ} (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) *
        HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s i n)
        = P.eval (-(n : ℂ))) →
    ∀ n, M + 1 ≤ n →
      (∑ i : Fin (N + 1),
        ((coeff i).comp (-X) - (coeff i).comp (1 - X)).eval (n : ℂ) *
          HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s i n) +
      (∑ i : Fin (N + 1),
        ((coeff i).comp (1 - X)).eval (n : ℂ) * (n : ℂ) ^ (-(s + (i : ℂ)))) =
      (P.comp (-X) - P.comp (1 - X)).eval (n : ℂ)

/-- Formal wrapper for the mixed finite-difference landing. -/
theorem hurwitz_harmonic_tail_mixed_finite_difference (N : ℕ) :
    HurwitzHarmonicTailMixedFiniteDifferenceTarget N := by
  intro s coeff P M hrel n hn
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail_relation_finite_difference_mixed
    (N := N) (s := s) coeff P hrel n hn

/-- Two-ray finite-difference landing target for mixed harmonic/shifted-power relations. -/
def HurwitzMixedTailTwoRayFiniteDifferenceTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ} (hcoeff scoeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (hcoeff i).eval (n : ℂ) *
        HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s i n) +
        (∑ i : Fin (N + 1), (scoeff i).eval (n : ℂ) *
          (n : ℂ) ^ (-(s + (i : ℂ)))) = P.eval (n : ℂ)) →
    ∀ n, M + 1 ≤ n →
      (∑ i : Fin (N + 1),
        (hcoeff i - (hcoeff i).comp (X - 1)).eval (n : ℂ) *
          HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s i n) +
      (∑ i : Fin (N + 1),
        ((hcoeff i).comp (X - 1) + scoeff i).eval (n : ℂ) *
          (n : ℂ) ^ (-(s + (i : ℂ)))) -
      (∑ i : Fin (N + 1),
        ((scoeff i).comp (X - 1)).eval (n : ℂ) *
          (((n - 1 : ℕ) : ℂ) ^ (-(s + (i : ℂ))))) =
      (P - P.comp (X - 1)).eval (n : ℂ)

/-- Formal wrapper for the two-ray mixed finite-difference landing. -/
theorem hurwitz_mixed_tail_two_ray_finite_difference (N : ℕ) :
    HurwitzMixedTailTwoRayFiniteDifferenceTarget N := by
  intro s hcoeff scoeff P M hrel n hn
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.mixedTail_relation_finite_difference_twoRay
    (N := N) (s := s) hcoeff scoeff P hrel n hn

/-- Shifted-power close in the eventual-lower-bound form produced by mixed relations. -/
def HurwitzShiftedPowerEventuallyGeCloseTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (coeff i).eval (n : ℂ) * (n : ℂ) ^ (-(s + (i : ℂ)))) =
        P.eval (n : ℂ)) →
    HurwitzNonRat.shiftedPowerPolynomial N coeff = 0 ∧ P = 0

/-- Formal wrapper for the shifted-power eventual-lower-bound close. -/
theorem hurwitz_shifted_power_eventually_ge_close (N : ℕ) :
    HurwitzShiftedPowerEventuallyGeCloseTarget N := by
  intro s hs coeff P M hrel
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.shiftedPower_relation_close_of_eventually_ge
    (N := N) (s := s) hs coeff P hrel

/-- Previous-ray shifted-power close in the eventual-lower-bound form produced by two-ray mixed
finite differences. -/
def HurwitzShiftedPowerPrevEventuallyGeCloseTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (coeff i).eval (n : ℂ) *
        (((n - 1 : ℕ) : ℂ) ^ (-(s + (i : ℂ))))) = P.eval (n : ℂ)) →
    HurwitzNonRat.shiftedPowerPolynomial N (fun i => (coeff i).comp (X + 1)) = 0 ∧ P = 0

/-- Formal wrapper for the previous-ray shifted-power close. -/
theorem hurwitz_shifted_power_prev_eventually_ge_close (N : ℕ) :
    HurwitzShiftedPowerPrevEventuallyGeCloseTarget N := by
  intro s hs coeff P M hrel
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.shiftedPower_prev_relation_close_of_eventually_ge
    (N := N) (s := s) hs coeff P hrel

/-- Singleton previous-ray shifted-power close in coefficient form. -/
def HurwitzShiftedPowerPrevCloseN0CoeffTarget : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (coeff : Fin (0 + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ n, M ≤ n →
      (∑ i : Fin (0 + 1), (coeff i).eval (n : ℂ) *
        (((n - 1 : ℕ) : ℂ) ^ (-(s + (i : ℂ))))) = P.eval (n : ℂ)) →
    (∀ i : Fin (0 + 1), coeff i = 0) ∧ P = 0

/-- Formal wrapper for the singleton previous-ray shifted-power coefficient close. -/
theorem hurwitz_shifted_power_prev_close_N0_coefficients :
    HurwitzShiftedPowerPrevCloseN0CoeffTarget := by
  intro s hs coeff P M hrel
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.shiftedPower_prev_relation_close_N0_coefficients
    (s := s) hs coeff P hrel

/-- Pure two-ray shifted-power close when the previous ray is already absent. -/
def HurwitzShiftedPowerTwoRayZeroPrevCloseTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (current prev : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ i : Fin (N + 1), prev i = 0) →
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (current i).eval (n : ℂ) *
        (n : ℂ) ^ (-(s + (i : ℂ)))) -
      (∑ i : Fin (N + 1), (prev i).eval (n : ℂ) *
        (((n - 1 : ℕ) : ℂ) ^ (-(s + (i : ℂ))))) = P.eval (n : ℂ)) →
    HurwitzNonRat.shiftedPowerPolynomial N current = 0 ∧ P = 0

/-- Formal wrapper for the zero-previous-ray two-ray shifted-power close. -/
theorem hurwitz_shifted_power_twoRay_zero_prev_close (N : ℕ) :
    HurwitzShiftedPowerTwoRayZeroPrevCloseTarget N := by
  intro s hs current prev P M hprev hrel
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.shiftedPower_twoRay_close_of_zero_prev
    (N := N) (s := s) hs current prev P hprev hrel

/-- Pure two-ray shifted-power close when the current ray is already absent. -/
def HurwitzShiftedPowerTwoRayZeroCurrentCloseTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (current prev : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ i : Fin (N + 1), current i = 0) →
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (current i).eval (n : ℂ) *
        (n : ℂ) ^ (-(s + (i : ℂ)))) -
      (∑ i : Fin (N + 1), (prev i).eval (n : ℂ) *
        (((n - 1 : ℕ) : ℂ) ^ (-(s + (i : ℂ))))) = P.eval (n : ℂ)) →
    HurwitzNonRat.shiftedPowerPolynomial N (fun i => (prev i).comp (X + 1)) = 0 ∧ P = 0

/-- Formal wrapper for the zero-current-ray two-ray shifted-power close. -/
theorem hurwitz_shifted_power_twoRay_zero_current_close (N : ℕ) :
    HurwitzShiftedPowerTwoRayZeroCurrentCloseTarget N := by
  intro s hs current prev P M hcurrent hrel
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.shiftedPower_twoRay_close_of_zero_current
    (N := N) (s := s) hs current prev P hcurrent hrel

/-- Two-ray shifted-power bridge after both one-ray compressed obstructions vanish. -/
def HurwitzShiftedPowerTwoRayCompressedZeroRhsTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ} (current prev : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    HurwitzNonRat.shiftedPowerPolynomial N current = 0 →
    HurwitzNonRat.shiftedPowerPolynomial N (fun i => (prev i).comp (X + 1)) = 0 →
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (current i).eval (n : ℂ) *
        (n : ℂ) ^ (-(s + (i : ℂ)))) -
      (∑ i : Fin (N + 1), (prev i).eval (n : ℂ) *
        (((n - 1 : ℕ) : ℂ) ^ (-(s + (i : ℂ))))) = P.eval (n : ℂ)) →
    P = 0

/-- Formal wrapper for the compressed-zero two-ray shifted-power bridge. -/
theorem hurwitz_shifted_power_twoRay_compressed_zero_rhs (N : ℕ) :
    HurwitzShiftedPowerTwoRayCompressedZeroRhsTarget N := by
  intro s current prev P M hcurrent hprev hrel
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.shiftedPower_twoRay_rhs_zero_of_compressed_zero
    (N := N) (s := s) current prev P hcurrent hprev hrel

/-- Mixed relation close in the subcase where the harmonic coefficients are already zero. -/
def HurwitzMixedTailZeroHarmonicCloseTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (hcoeff scoeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ i : Fin (N + 1), hcoeff i = 0) →
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (hcoeff i).eval (n : ℂ) *
        HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s i n) +
      (∑ i : Fin (N + 1), (scoeff i).eval (n : ℂ) * (n : ℂ) ^ (-(s + (i : ℂ)))) =
        P.eval (n : ℂ)) →
    (∀ i : Fin (N + 1), hcoeff i = 0) ∧
      HurwitzNonRat.shiftedPowerPolynomial N scoeff = 0 ∧ P = 0

/-- Formal wrapper for the zero-harmonic subcase of mixed relation close. -/
theorem hurwitz_mixed_tail_zero_harmonic_close (N : ℕ) :
    HurwitzMixedTailZeroHarmonicCloseTarget N := by
  intro s hs hcoeff scoeff P M hh hrel
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.mixedTailIndependent_zero_harmonic_part
    (N := N) (s := s) hs hcoeff scoeff P hh hrel

/-- Singleton mixed relation close in coefficient form when the harmonic coefficients are already
zero.  For `N = 0`, the compressed shifted-power polynomial is exactly the remaining shifted
coefficient. -/
def HurwitzMixedTailZeroHarmonicCloseN0CoeffTarget : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (hcoeff scoeff : Fin (0 + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ i : Fin (0 + 1), hcoeff i = 0) →
    (∀ n, M ≤ n →
      (∑ i : Fin (0 + 1), (hcoeff i).eval (n : ℂ) *
        HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := 0) s i n) +
      (∑ i : Fin (0 + 1), (scoeff i).eval (n : ℂ) * (n : ℂ) ^ (-(s + (i : ℂ)))) =
        P.eval (n : ℂ)) →
    (∀ i : Fin (0 + 1), hcoeff i = 0) ∧ (∀ i : Fin (0 + 1), scoeff i = 0) ∧ P = 0

/-- Formal wrapper for the singleton zero-harmonic mixed-tail coefficient close. -/
theorem hurwitz_mixed_tail_zero_harmonic_close_N0_coefficients :
    HurwitzMixedTailZeroHarmonicCloseN0CoeffTarget := by
  intro s hsZ hcoeff scoeff P M hh hrel
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.mixedTailIndependent_zero_harmonic_part_N0_coefficients
    (s := s) hsZ hcoeff scoeff P hh hrel

/-- Mixed relation close in the subcase where the shifted-power coefficients are already zero, assuming
the harmonic-tail rational-independence provider. -/
def HurwitzMixedTailZeroShiftedCloseFromHarmonicTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ},
  HurwitzAllNTailIndependence.RationalTailIndependent (N := N)
    (HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s) →
  ∀ (hcoeff scoeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ i : Fin (N + 1), scoeff i = 0) →
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (hcoeff i).eval (n : ℂ) *
        HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s i n) +
      (∑ i : Fin (N + 1), (scoeff i).eval (n : ℂ) * (n : ℂ) ^ (-(s + (i : ℂ)))) =
        P.eval (n : ℂ)) →
    (∀ i : Fin (N + 1), hcoeff i = 0) ∧
      HurwitzNonRat.shiftedPowerPolynomial N scoeff = 0 ∧ P = 0

/-- Formal wrapper for the zero-shifted mixed-tail close from harmonic-tail independence. -/
theorem hurwitz_mixed_tail_zero_shifted_close_from_harmonic (N : ℕ) :
    HurwitzMixedTailZeroShiftedCloseFromHarmonicTarget N := by
  intro s hTail hcoeff scoeff P M hs hrel
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.mixedTailIndependent_zero_shifted_part_of_rationalTailIndependent
    (N := N) (s := s) hTail hcoeff scoeff P hs hrel

/-- Unconditional singleton mixed relation close in the zero shifted-power subcase. -/
def HurwitzMixedTailZeroShiftedCloseN0Target : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
  ∀ (hcoeff scoeff : Fin (0 + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ i : Fin (0 + 1), scoeff i = 0) →
    (∀ n, M ≤ n →
      (∑ i : Fin (0 + 1), (hcoeff i).eval (n : ℂ) *
        HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := 0) s i n) +
      (∑ i : Fin (0 + 1), (scoeff i).eval (n : ℂ) * (n : ℂ) ^ (-(s + (i : ℂ)))) =
        P.eval (n : ℂ)) →
    (∀ i : Fin (0 + 1), hcoeff i = 0) ∧
      HurwitzNonRat.shiftedPowerPolynomial 0 scoeff = 0 ∧ P = 0

/-- Formal wrapper for the unconditional singleton zero-shifted mixed-tail close. -/
theorem hurwitz_mixed_tail_zero_shifted_close_N0 :
    HurwitzMixedTailZeroShiftedCloseN0Target := by
  intro s hsZ hcoeff scoeff P M hs hrel
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.mixedTailIndependent_zero_shifted_part_N0
    (s := s) hsZ hcoeff scoeff P hs hrel

/-- A full mixed-tail independence provider is enough to close the original harmonic-tail provider. -/
def HurwitzHarmonicTailFromMixedTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
    HurwitzAllNTailIndependence.HurwitzZetaTail.MixedTailIndependent N s →
    HurwitzAllNTailIndependence.RationalTailIndependent (N := N)
      (HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s)

/-- Formal wrapper for closing harmonic-tail independence from mixed-tail independence. -/
theorem hurwitz_harmonic_tail_from_mixed (N : ℕ) :
    HurwitzHarmonicTailFromMixedTarget N := by
  intro s hs hMixed
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.rationalTailIndependent_harmonic_of_mixedTailIndependent
    (N := N) (s := s) hs hMixed

/-- A full mixed-tail independence provider also supplies the pole-root bridge used by the polylog path. -/
def HurwitzHarmonicPoleRootFromMixedTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
    HurwitzAllNTailIndependence.HurwitzZetaTail.MixedTailIndependent N s →
    HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s

/-- Formal wrapper for the pole-root bridge from mixed-tail independence. -/
theorem hurwitz_harmonic_pole_root_from_mixed (N : ℕ) :
    HurwitzHarmonicPoleRootFromMixedTarget N := by
  intro s hs hMixed
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicPoleRootInput_of_mixedTailIndependent
    (N := N) (s := s) hs hMixed

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Full relation-level all-`N` coefficient close from mixed-tail independence:
the mixed provider supplies the pole-root bridge, and the existing relation-level
descent then closes every symmetric quadratic coefficient, every linear coefficient,
and the residual constant coefficient. -/
def HurwitzAllNCoefficientsCloseFromRelationMixedTarget (N : ℕ) (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, s ≠ (k : ℂ)) →
  HurwitzAllNTailIndependence.HurwitzZetaTail.MixedTailIndependent N s →
  ∀ (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) (M : ℕ),
    (∀ i j, q i j = q j i) →
    (∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
      z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) →
    (∀ i j : Fin (N + 1), q i j = 0) ∧ (∀ j : Fin (N + 1), l j = 0) ∧ cc = 0

/-- Formal wrapper for full all-`N` coefficient close from mixed-tail independence. -/
theorem hurwitz_allN_coefficients_close_from_relation_mixed (N : ℕ) (s : ℂ) :
    HurwitzAllNCoefficientsCloseFromRelationMixedTarget N s := by
  intro hs1 hsZ hMixed q l cc M hSymm hrel
  exact HurwitzAllNRelationClose.all_coefficients_close_of_genuine_relation_poleRootInput
    (N := N) (s := s) (M := M) hs1 hsZ
    (HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicPoleRootInput_of_mixedTailIndependent
      (N := N) (s := s) hsZ hMixed)
    q l cc hSymm hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Mixed pole-root bridge target: the analytic polylog step for mixed relations supplies Gamma
pole-root identities for the harmonic coefficients. -/
def HurwitzMixedPoleRootInputTarget (N : ℕ) (s : ℂ) : Prop :=
  HurwitzAllNTailIndependence.HurwitzZetaTail.MixedPoleRootInput N s

/-- Mixed pole-root input closes the full mixed-tail provider. -/
def HurwitzMixedTailFromMixedPoleRootTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
    HurwitzAllNTailIndependence.HurwitzZetaTail.MixedPoleRootInput N s →
    HurwitzAllNTailIndependence.HurwitzZetaTail.MixedTailIndependent N s

/-- Formal wrapper for mixed-tail independence from mixed pole-root input. -/
theorem hurwitz_mixed_tail_from_mixed_pole_root (N : ℕ) :
    HurwitzMixedTailFromMixedPoleRootTarget N := by
  intro s hs hpole
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.mixedTailIndependent_of_mixedPoleRootInput
    (N := N) (s := s) hs hpole

/-- Mixed pole-root input closes the original harmonic-tail rational independence provider. -/
def HurwitzHarmonicTailFromMixedPoleRootTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
    HurwitzAllNTailIndependence.HurwitzZetaTail.MixedPoleRootInput N s →
    HurwitzAllNTailIndependence.RationalTailIndependent (N := N)
      (HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicTail (N := N) s)

/-- Formal wrapper for harmonic-tail independence from mixed pole-root input. -/
theorem hurwitz_harmonic_tail_from_mixed_pole_root (N : ℕ) :
    HurwitzHarmonicTailFromMixedPoleRootTarget N := by
  intro s hs hpole
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.rationalTailIndependent_harmonic_of_mixedPoleRootInput
    (N := N) (s := s) hs hpole

/-- Full relation-level all-`N` coefficient close from mixed pole-root input. This packages the exact
analytic provider needed by the finite-difference mixed route, then reuses the existing all-`N` descent. -/
def HurwitzAllNCoefficientsCloseFromRelationMixedPoleRootTarget (N : ℕ) (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, s ≠ (k : ℂ)) →
  HurwitzAllNTailIndependence.HurwitzZetaTail.MixedPoleRootInput N s →
  ∀ (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) (M : ℕ),
    (∀ i j, q i j = q j i) →
    (∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
      z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) →
    (∀ i j : Fin (N + 1), q i j = 0) ∧ (∀ j : Fin (N + 1), l j = 0) ∧ cc = 0

/-- Formal wrapper for full all-`N` coefficient close from mixed pole-root input. -/
theorem hurwitz_allN_coefficients_close_from_relation_mixed_pole_root (N : ℕ) (s : ℂ) :
    HurwitzAllNCoefficientsCloseFromRelationMixedPoleRootTarget N s := by
  intro hs1 hsZ hpole q l cc M hSymm hrel
  exact hurwitz_allN_coefficients_close_from_relation_mixed N s hs1 hsZ
    (HurwitzAllNTailIndependence.HurwitzZetaTail.mixedTailIndependent_of_mixedPoleRootInput
      (N := N) (s := s) hsZ hpole)
    q l cc M hSymm hrel

/-- Card-name theorem for the current honest all-`N` Hurwitz close: the final coefficient vanishing
follows once the explicit mixed pole-root provider is supplied. -/
theorem hurwitz_quadratic_all_n_tail_independence_from_mixed_pole_root (N : ℕ) (s : ℂ) :
    HurwitzAllNCoefficientsCloseFromRelationMixedPoleRootTarget N s :=
  hurwitz_allN_coefficients_close_from_relation_mixed_pole_root N s

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- The sharper mixed pole-root bridge supplies the older harmonic pole-root input. -/
def HurwitzHarmonicPoleRootFromMixedPoleRootTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, (∀ k : ℤ, s ≠ (k : ℂ)) →
    HurwitzAllNTailIndependence.HurwitzZetaTail.MixedPoleRootInput N s →
    HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s

/-- Formal wrapper for harmonic pole-root input from mixed pole-root input. -/
theorem hurwitz_harmonic_pole_root_from_mixed_pole_root (N : ℕ) :
    HurwitzHarmonicPoleRootFromMixedPoleRootTarget N := by
  intro s hs hpole
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicPoleRootInput_of_mixedPoleRootInput
    (N := N) (s := s) hs hpole

/-- Actual shifted-Hurwitz rational-tail independence from the sharper mixed pole-root bridge. -/
def HurwitzHzetaTailFromMixedPoleRootTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, 1 < s.re → (∀ k : ℤ, s ≠ (k : ℂ)) →
    HurwitzAllNTailIndependence.HurwitzZetaTail.MixedPoleRootInput N s →
    HurwitzAllNTailIndependence.RationalTailIndependent (N := N)
      (fun i n => HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))

/-- Formal wrapper for actual shifted-Hurwitz rational-tail independence from mixed pole-root input. -/
theorem hurwitz_hzeta_tail_from_mixed_pole_root_card (N : ℕ) :
    HurwitzHzetaTailFromMixedPoleRootTarget N := by
  intro s hs1 hsZ hpole
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.rationalTailIndependent_hzeta_shift_neg_nat_of_mixedPoleRootInput
    (N := N) hs1 hsZ hpole

/-- Actual shifted-Hurwitz row/constant close from the sharper mixed pole-root bridge. -/
def HurwitzHzetaRowCloseFromMixedPoleRootTarget (N : ℕ) : Prop :=
  ∀ {s : ℂ}, 1 < s.re → (∀ k : ℤ, s ≠ (k : ℂ)) →
    HurwitzAllNTailIndependence.HurwitzZetaTail.MixedPoleRootInput N s →
    ∀ (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
      (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ),
      (∀ j : Fin (N + 1), ∃ M : ℕ, ∀ n, M ≤ n →
        (l j).eval (-(n : ℂ)) +
          (∑ i : Fin (N + 1),
            (q i j).eval (-(n : ℂ)) *
              (2 * HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))) = 0) →
      (∃ M : ℕ, ∀ n, M ≤ n → cc.eval (-(n : ℂ)) = 0) →
      (∀ i j, q i j = 0) ∧ (∀ j, l j = 0) ∧ cc = 0

/-- Formal wrapper for actual shifted-Hurwitz row/constant close from mixed pole-root input. -/
theorem hurwitz_hzeta_row_close_from_mixed_pole_root_card (N : ℕ) :
    HurwitzHzetaRowCloseFromMixedPoleRootTarget N := by
  intro s hs1 hsZ hpole q l cc hrow hcc
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.rows_and_constant_close_of_hzeta_shift_neg_nat_of_mixedPoleRootInput
    hs1 hsZ hpole q l cc hrow hcc

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Exact Hurwitz mixed-provider target: for nonintegral `s`, the mixed pole-root input is precisely
the mixed harmonic-tail/shifted-power independence provider produced by the finite-difference route. -/
def HurwitzMixedPoleRootExactTarget : Prop :=
  ∀ (N : ℕ) (s : ℂ), (∀ k : ℤ, s ≠ (k : ℂ)) →
    (HurwitzAllNTailIndependence.HurwitzZetaTail.MixedTailIndependent N s ↔
      HurwitzAllNTailIndependence.HurwitzZetaTail.MixedPoleRootInput N s)

/-- Formal wrapper: the mixed pole-root bridge has exactly the same Lean content as the mixed-tail
provider. This pins the remaining all-`N` Hurwitz analytic input to one explicit interface. -/
theorem hurwitz_mixed_pole_root_exact_target : HurwitzMixedPoleRootExactTarget := by
  intro N s hsZ
  exact HurwitzAllNTailIndependence.HurwitzZetaTail.mixedTailIndependent_iff_mixedPoleRootInput hsZ

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Exact dyadic multiplier target for `not-new-but-required/bottcher-exact-pruefer-monodromy.md`:
the depth-`n` scalar multiplier has order exactly `2^n`. -/
def BottcherExactPrueferDyadicMultiplierOrderTarget : Prop :=
  ∀ n : ℕ,
    orderOf (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ))) = 2 ^ n

/-- Formal wrapper for the exact order of the dyadic Prüfer multipliers. This is the algebraic
order component of the exact disconnected Böttcher monodromy theorem. -/
theorem bottcher_exact_pruefer_dyadic_multiplier_order :
    BottcherExactPrueferDyadicMultiplierOrderTarget := by
  intro n
  exact Bottcher.orderOf_dyadicRoot n

/-- Exact dyadic multipliers imply the finite-type absence order target used by the C11 support card. -/
def BottcherDyadicUnboundedOrderFromExactPrueferTarget : Prop :=
  BottcherExactPrueferDyadicMultiplierOrderTarget → BottcherDyadicUnboundedOrderTarget

/-- Formal wrapper: the exact Prüfer multiplier theorem supplies unbounded dyadic order. -/
theorem bottcher_dyadic_unbounded_order_from_exact_pruefer :
    BottcherDyadicUnboundedOrderFromExactPrueferTarget := by
  intro h d
  refine ⟨Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)), ?_⟩
  rw [h d]
  exact Nat.lt_two_pow_self

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Symmetric algebraic target for
`not-new-but-required/unbounded-one-coordinate-monodromy-obstruction.md`: the same obstruction applies
when the monodromy fixes the first coordinate and scales the second. -/
def UnboundedOneCoordinateMonodromySymmTarget
    {K M : Type*} [Field K] [Field M] [Algebra K M] (F G : M) : Prop :=
  Transcendental K F →
  G ≠ 0 →
  (∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
    d < m ∧ orderOf ζ = m ∧ σ F = F ∧ σ ζ = ζ ∧ σ G = ζ * G) →
  ∀ P : Polynomial (Polynomial K),
    (P.map (aeval F : Polynomial K →ₐ[K] M).toRingHom).eval G = 0 →
    P = 0

/-- Formal wrapper for the symmetric one-coordinate monodromy obstruction. -/
theorem unbounded_one_coordinate_monodromy_obstruction_symm_card
    {K M : Type*} [Field K] [Field M] [Algebra K M] (F G : M) :
    UnboundedOneCoordinateMonodromySymmTarget (K := K) (M := M) F G := by
  intro hF hG mono P hrel
  exact Bottcher.algIndep_of_unbounded_monodromy (K := K) (M := M) G F hF hG mono P hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Multiplicative scalar-monodromy finite-cover target: finite-index source subgroups have finite-index
image inside the scalar monodromy image, so every nontrivial power-divisible subgroup of that image
survives on the cover subgroup. This is the direct multiplicative form of
`bottcher-pruefer-monodromy-no-finite-cover.md`. -/
def BottcherMultiplicativeFiniteIndexImageDivisibleSubgroupTarget : Prop :=
  (∀ {G A : Type} [Group G] [Group A] (H : Subgroup G), H.FiniteIndex →
    (ρ : G →* A) → (H.map ρ.rangeRestrict).FiniteIndex) ∧
  (∀ {G A : Type} [Group G] [CommGroup A] (H : Subgroup G), H.FiniteIndex →
    (ρ : G →* A) → (D : Subgroup ρ.range) →
    (∀ n : ℕ, 0 < n → ∀ d : ρ.range, d ∈ D → ∃ e : ρ.range, e ∈ D ∧ e ^ n = d) →
    D ≤ H.map ρ.rangeRestrict ∧ (H.map ρ.rangeRestrict) ⊓ D = D) ∧
  (∀ {G A : Type} [Group G] [CommGroup A] (H : Subgroup G), H.FiniteIndex →
    (ρ : G →* A) → (D : Subgroup ρ.range) →
    (∀ n : ℕ, 0 < n → ∀ d : ρ.range, d ∈ D → ∃ e : ρ.range, e ∈ D ∧ e ^ n = d) →
    (∃ d : ρ.range, d ∈ D ∧ d ≠ 1) → ∃ h : G, h ∈ H ∧ ρ h ≠ 1) ∧
  (∀ {G A : Type} [Group G] [CommGroup A] (H : Subgroup G), H.FiniteIndex →
    (ρ : G →* A) → (D : Subgroup ρ.range) →
    (∀ n : ℕ, 0 < n → ∀ d : ρ.range, d ∈ D → ∃ e : ρ.range, e ∈ D ∧ e ^ n = d) →
    (∃ d : ρ.range, d ∈ D ∧ d ≠ 1) → ¬ ∀ h : G, h ∈ H → ρ h = 1)

/-- Formal wrapper: finite covers cannot kill a scalar monodromy image containing a nontrivial
power-divisible Prüfer-type subgroup. -/
theorem bottcher_pruefer_multiplicative_finite_index_image_divisible_subgroup_obstruction :
    BottcherMultiplicativeFiniteIndexImageDivisibleSubgroupTarget := by
  constructor
  · intro G A hG hA H hfinite ρ
    haveI : H.FiniteIndex := hfinite
    exact Bottcher.subgroup_map_rangeRestrict_finiteIndex H ρ
  constructor
  · intro G A hG hA H hfinite ρ D hdiv
    haveI : H.FiniteIndex := hfinite
    exact ⟨Bottcher.subgroup_le_map_rangeRestrict_of_powerDivisible_finiteIndex H ρ D hdiv,
      Bottcher.subgroup_inf_map_rangeRestrict_eq_right_of_powerDivisible_finiteIndex H ρ D hdiv⟩
  constructor
  · intro G A hG hA H hfinite ρ D hdiv hne
    haveI : H.FiniteIndex := hfinite
    exact Bottcher.exists_mem_finiteIndex_subgroup_apply_ne_one_of_powerDivisible_nontrivial
      H ρ D hdiv hne
  · intro G A hG hA H hfinite ρ D hdiv hne
    haveI : H.FiniteIndex := hfinite
    exact Bottcher.not_forall_mem_finiteIndex_subgroup_apply_eq_one_of_powerDivisible_nontrivial
      H ρ D hdiv hne

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Exact Prüfer tower coherence target for `bottcher-exact-pruefer-monodromy.md`: the named depth-`n`
multiplier has order `2^n`, the depth `n+1` multiplier squares to it, and the square root again has
exact Prüfer order. -/
def BottcherExactPrueferDyadicTowerCoherenceTarget : Prop :=
  ∀ n : ℕ,
    orderOf (Bottcher.dyadicRoot n) = 2 ^ n ∧
    Bottcher.dyadicRoot (n + 1) ^ 2 = Bottcher.dyadicRoot n ∧
    ∃ η : ℂ, η ^ 2 = Bottcher.dyadicRoot n ∧ orderOf η = 2 ^ (n + 1)

/-- Formal wrapper for the exact coherent dyadic Prüfer multiplier tower. -/
theorem bottcher_exact_pruefer_dyadic_tower_coherence :
    BottcherExactPrueferDyadicTowerCoherenceTarget := by
  intro n
  exact ⟨Bottcher.orderOf_dyadicRoot_named n, Bottcher.dyadicRoot_succ_sq n,
    Bottcher.dyadicRoot_square_root n⟩

/-- Card-name theorem for `bottcher-exact-pruefer-monodromy.md`, exposed as the exact coherent
dyadic multiplier tower. -/
theorem bottcher_exact_pruefer_monodromy :
    BottcherExactPrueferDyadicTowerCoherenceTarget :=
  bottcher_exact_pruefer_dyadic_tower_coherence

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Ambient scalar-monodromy finite-cover target: if an ambient target subgroup `D` is contained in the
monodromy image and is power-divisible, then every finite-index source subgroup still maps onto `D` and
therefore has nontrivial scalar monodromy whenever `D` is nontrivial. This is the card-facing form of
`bottcher-pruefer-monodromy-no-finite-cover.md`, avoiding an extra subtype-of-`ρ.range` packaging step. -/
def BottcherMultiplicativeFiniteIndexAmbientDivisibleSubgroupTarget : Prop :=
  (∀ {G A : Type} [Group G] [CommGroup A] (H : Subgroup G), H.FiniteIndex →
    (ρ : G →* A) → (D : Subgroup A) → D ≤ ρ.range →
    (∀ n : ℕ, 0 < n → ∀ d : A, d ∈ D → ∃ e : A, e ∈ D ∧ e ^ n = d) →
    D ≤ H.map ρ) ∧
  (∀ {G A : Type} [Group G] [CommGroup A] (H : Subgroup G), H.FiniteIndex →
    (ρ : G →* A) → (D : Subgroup A) → D ≤ ρ.range →
    (∀ n : ℕ, 0 < n → ∀ d : A, d ∈ D → ∃ e : A, e ∈ D ∧ e ^ n = d) →
    (∃ d : A, d ∈ D ∧ d ≠ 1) → ∃ h : G, h ∈ H ∧ ρ h ≠ 1) ∧
  (∀ {G A : Type} [Group G] [CommGroup A] (H : Subgroup G), H.FiniteIndex →
    (ρ : G →* A) → (D : Subgroup A) → D ≤ ρ.range →
    (∀ n : ℕ, 0 < n → ∀ d : A, d ∈ D → ∃ e : A, e ∈ D ∧ e ^ n = d) →
    (∃ d : A, d ∈ D ∧ d ≠ 1) → ¬ ∀ h : G, h ∈ H → ρ h = 1)

/-- Formal wrapper for the ambient subgroup version of the finite-cover Prüfer obstruction. -/
theorem bottcher_pruefer_multiplicative_finite_index_ambient_divisible_subgroup_obstruction :
    BottcherMultiplicativeFiniteIndexAmbientDivisibleSubgroupTarget := by
  constructor
  · intro G A hG hA H hfinite ρ D hDρ hdiv
    haveI : H.FiniteIndex := hfinite
    exact Bottcher.subgroup_le_map_of_powerDivisible_finiteIndex_of_le_range H ρ D hDρ hdiv
  constructor
  · intro G A hG hA H hfinite ρ D hDρ hdiv hne
    haveI : H.FiniteIndex := hfinite
    exact Bottcher.exists_mem_finiteIndex_subgroup_apply_ne_one_of_powerDivisible_nontrivial_of_le_range
      H ρ D hDρ hdiv hne
  · intro G A hG hA H hfinite ρ D hDρ hdiv hne
    haveI : H.FiniteIndex := hfinite
    exact Bottcher.not_forall_mem_finiteIndex_subgroup_apply_eq_one_of_powerDivisible_nontrivial_of_le_range
      H ρ D hDρ hdiv hne

/-- Card-name theorem for `bottcher-pruefer-monodromy-no-finite-cover.md` in the ambient subgroup
form used by the current Lean API. -/
theorem bottcher_pruefer_monodromy_no_finite_cover :
    BottcherMultiplicativeFiniteIndexAmbientDivisibleSubgroupTarget :=
  bottcher_pruefer_multiplicative_finite_index_ambient_divisible_subgroup_obstruction

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Concrete root-of-unity input for the finite-cover Prüfer obstruction: the torsion subgroup of
`ℂˣ` is power-divisible and nontrivial.  This supplies a reusable, fully proved source for the
`hdiv`/`hne` hypotheses in the scalar finite-cover algebra whenever the monodromy image contains the
relevant complex root-of-unity subgroup. -/
def BottcherComplexUnitTorsionPowerDivisibleTarget : Prop :=
  (∀ n : ℕ, 0 < n → ∀ d : ℂˣ, d ∈ CommGroup.torsion ℂˣ →
    ∃ e : ℂˣ, e ∈ CommGroup.torsion ℂˣ ∧ e ^ n = d) ∧
  (∃ d : ℂˣ, d ∈ CommGroup.torsion ℂˣ ∧ d ≠ 1)

/-- Formal wrapper: complex roots of unity form a nontrivial power-divisible subgroup of `ℂˣ`. -/
theorem bottcher_complex_unit_torsion_power_divisible :
    BottcherComplexUnitTorsionPowerDivisibleTarget := by
  exact ⟨Bottcher.complex_units_torsion_powerDivisible,
    Bottcher.complex_units_torsion_nontrivial⟩

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- U0 provider reduction target: radical data canonically supplies finite square-root deck data by
adjoining a square root of the radicand. -/
def U0PhibSquareRootDeckDataFromRadicalDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc →
    U0CardTheorems.PhibSquareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for the radical-data-to-square-root-deck U0 provider reduction. -/
theorem u0_phib_squareRootDeckData_from_radicalData :
    U0PhibSquareRootDeckDataFromRadicalDataTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc hRadical
  exact U0CardTheorems.phibSquareRootDeckData_of_radicalData
    hUo hUc hUne hUinf hU_ext hU_esc hRadical

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- U0 provider equivalence target: radical data and finite square-root deck data carry the same Lean
content for the Kummer radicand. -/
def U0PhibRadicalDataIffSquareRootDeckDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc ↔
      U0CardTheorems.PhibSquareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for the U0 radical-data/square-root-deck-data provider equivalence. -/
theorem u0_phib_radicalData_iff_squareRootDeckData :
    U0PhibRadicalDataIffSquareRootDeckDataTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc
  exact U0CardTheorems.phibRadicalData_iff_squareRootDeckData
    hUo hUc hUne hUinf hU_ext hU_esc

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- U0 provider-reduction target: full Kummer inputs already supply radical data, because dyadic
Kummer irreducibility forces the radicand to be non-square. -/
def U0PhibRadicalDataFromKummerInputsTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc →
    U0CardTheorems.PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for the U0 Kummer-inputs-to-radical-data provider reduction. -/
theorem u0_phib_radicalData_from_kummerInputs :
    U0PhibRadicalDataFromKummerInputsTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc hKummer
  exact U0CardTheorems.phibRadicalData_of_kummerInputs
    hUo hUc hUne hUinf hU_ext hU_esc hKummer

/-- U0 provider equivalence target: the original Kummer-input provider and the radical-data provider
carry the same Lean content. -/
def U0PhibKummerInputsIffRadicalDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc ↔
      U0CardTheorems.PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for the U0 Kummer-input/radical-data provider equivalence. -/
theorem u0_phib_kummerInputs_iff_radicalData :
    U0PhibKummerInputsIffRadicalDataTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc
  exact U0CardTheorems.phibKummerInputs_iff_radicalData
    hUo hUc hUne hUinf hU_ext hU_esc

/-- U0 provider equivalence target: the original Kummer-input provider and finite square-root deck
provider are directly equivalent; radical data is only the intermediate normal form. -/
def U0PhibKummerInputsIffSquareRootDeckDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc ↔
      U0CardTheorems.PhibSquareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for the direct U0 Kummer-input/square-root-deck provider equivalence. -/
theorem u0_phib_kummerInputs_iff_squareRootDeckData :
    U0PhibKummerInputsIffSquareRootDeckDataTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc
  exact U0CardTheorems.phibKummerInputs_iff_squareRootDeckData
    hUo hUc hUne hUinf hU_ext hU_esc

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- U0 provider obstruction target: any valid radical-data map is necessarily non-surjective.  This
formally rules out the naive base-field choice equal to the carrier already containing `φ_b`; the
remaining provider must use a proper descent/cover base. -/
def U0PhibRadicalDataNonSurjectiveMapsTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc →
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ d : ℕ, ∃ (B : Type) (_ : Field B) (_ : Algebra (RatFunc ℂ) B)
        (i : B →ₐ[RatFunc ℂ] meroField U) (a GB : B) (k : ℕ),
        1 ≤ k ∧ d < 2 ^ k ∧ (∀ x : B, x ^ 2 ≠ a) ∧
        phiMero b hU_esc ^ (2 ^ k) = i a ∧
        i GB = algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext) ∧
        ¬ Function.Surjective i

/-- Formal wrapper for the U0 radical-provider non-surjectivity obstruction. -/
theorem u0_phib_radicalData_nonSurjective_maps :
    U0PhibRadicalDataNonSurjectiveMapsTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc hRadical
  exact U0CardTheorems.phibRadicalData_nonSurjective_maps
    hUo hUc hUne hUinf hU_ext hU_esc hRadical

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- U0 deep-provider target: the Böttcher deep odd-period loop data, plus containment of the deep domain
inside the U0 exterior, constructs the actual `PhibRadicalData` provider consumed by the U0 cards. -/
def U0PhibRadicalDataFromDeepDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    (∀ d : ℕ, ∃ (Ext : Set ℂ)
      (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
      (_hUExt : U ⊆ Ext)
      (_hExtesc : ∀ z ∈ Ext, (quadratic b)^[d+1] z ∈ escapeOpen b)
      (_hExtU0 : Ext ⊆ U0NaturalBoundary.Ext)
      (aExt : analyticSubring Ext),
      (aExt : Germ (𝓟 Ext) ℂ)
          = (↑(fun z => bottcherCoord b ((quadratic b)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
      (∀ T : Set ℂ, T.Countable →
        ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
          (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
          (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
          γ (2 * Real.pi) = γ 0 ∧
          (∀ θ : ℝ, (quadratic b)^[d+1] (γ θ) ∉ T) ∧
          (∫ θ in (0:ℝ)..(2 * Real.pi),
              logDeriv (fun z => bottcherCoord b ((quadratic b)^[d+1] z)) (γ θ) * γ' θ)
            = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) →
    U0CardTheorems.PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for the U0 deep-data-to-radical-data provider. -/
theorem u0_phib_radicalData_from_deepData :
    U0PhibRadicalDataFromDeepDataTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc deepdata
  exact U0CardTheorems.phibRadicalData_of_deepData
    hUo hUc hUne hUinf hU_ext hU_esc deepdata

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- U0 carrier-independence target from deep data: once the per-depth deep odd-period domains are
supplied, the actual `NoRelation ℂ(z) φ_b u₀` statement follows in the faithful meromorphic carrier. -/
def U0PhiIndependenceCarrierFromDeepDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    (∀ d : ℕ, ∃ (Ext : Set ℂ)
      (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
      (_hUExt : U ⊆ Ext)
      (_hExtesc : ∀ z ∈ Ext, (quadratic b)^[d+1] z ∈ escapeOpen b)
      (_hExtU0 : Ext ⊆ U0NaturalBoundary.Ext)
      (aExt : analyticSubring Ext),
      (aExt : Germ (𝓟 Ext) ℂ)
          = (↑(fun z => bottcherCoord b ((quadratic b)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
      (∀ T : Set ℂ, T.Countable →
        ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
          (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
          (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
          γ (2 * Real.pi) = γ 0 ∧
          (∀ θ : ℝ, (quadratic b)^[d+1] (γ θ) ∉ T) ∧
          (∫ θ in (0:ℝ)..(2 * Real.pi),
              logDeriv (fun z => bottcherCoord b ((quadratic b)^[d+1] z)) (γ θ) * γ' θ)
            = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) →
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext))

/-- Formal wrapper for U0 carrier independence from deep data. -/
theorem u0_phi_independence_carrier_from_deepData :
    U0PhiIndependenceCarrierFromDeepDataTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc deepdata
  exact U0CardTheorems.u0_phi_independence_carrier_deepData
    hUo hUc hUne hUinf hU_ext hU_esc deepdata

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- U0 escape-carrier deep-data target: on a Böttcher escape carrier, the U0 exterior containment is
automatic, so deep odd-period data directly gives the `NoRelation ℂ(z) φ_b u₀` theorem. -/
def U0PhiIndependenceEscapeCarrierFromDeepDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    (∀ d : ℕ, ∃ (Ext : Set ℂ)
      (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
      (_hUExt : U ⊆ Ext)
      (_hExtesc : ∀ z ∈ Ext, (quadratic b)^[d+1] z ∈ escapeOpen b)
      (_hExtU0 : Ext ⊆ U0NaturalBoundary.Ext)
      (aExt : analyticSubring Ext),
      (aExt : Germ (𝓟 Ext) ℂ)
          = (↑(fun z => bottcherCoord b ((quadratic b)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
      (∀ T : Set ℂ, T.Countable →
        ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
          (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
          (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
          γ (2 * Real.pi) = γ 0 ∧
          (∀ θ : ℝ, (quadratic b)^[d+1] (γ θ) ∉ T) ∧
          (∫ θ in (0:ℝ)..(2 * Real.pi),
              logDeriv (fun z => bottcherCoord b ((quadratic b)^[d+1] z)) (γ θ) * γ' θ)
            = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) →
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U)
        (u0AnSub (hU_esc.trans (U0CardTheorems.escapeOpen_subset_U0Ext b))))

/-- Formal wrapper for U0 escape-carrier independence from deep data. -/
theorem u0_phi_independence_escapeCarrier_from_deepData :
    U0PhiIndependenceEscapeCarrierFromDeepDataTarget := by
  intro U hUo hUc hUne hUinf b hU_esc deepdata
  exact U0CardTheorems.u0_phi_independence_escapeCarrier_deepData
    hUo hUc hUne hUinf hU_esc deepdata

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Connected U0 card wrapper from escape-carrier deep data. -/
theorem u0_phi_independence_connected_escapeCarrier_from_deepData :
    U0PhiIndependenceEscapeCarrierFromDeepDataTarget := by
  intro U hUo hUc hUne hUinf b hU_esc deepdata
  exact U0CardTheorems.u0_phi_independence_connected_escapeCarrier_deepData
    hUo hUc hUne hUinf hU_esc deepdata

/-- Disconnected U0 card wrapper from escape-carrier deep data. -/
theorem u0_phi_independence_disconnected_escapeCarrier_from_deepData :
    U0PhiIndependenceEscapeCarrierFromDeepDataTarget := by
  intro U hUo hUc hUne hUinf b hU_esc deepdata
  exact U0CardTheorems.u0_phi_independence_disconnected_escapeCarrier_deepData
    hUo hUc hUne hUinf hU_esc deepdata

/-- All-parameter U0 card wrapper from escape-carrier deep data. -/
theorem u0_phi_independence_all_parameters_escapeCarrier_from_deepData :
    U0PhiIndependenceEscapeCarrierFromDeepDataTarget := by
  intro U hUo hUc hUne hUinf b hU_esc deepdata
  exact U0CardTheorems.u0_phi_independence_all_parameters_escapeCarrier_deepData
    hUo hUc hUne hUinf hU_esc deepdata

/-- U0 topological deep-provider target: odd image-winding data constructs the actual
`PhibRadicalData` provider consumed by the U0 cards. -/
def U0PhibRadicalDataFromImageWindingDeepDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibImageWindingDeepData U b →
    U0CardTheorems.PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for the U0 image-winding-data-to-radical-data provider. -/
theorem u0_phib_radicalData_from_imageWindingDeepData :
    U0PhibRadicalDataFromImageWindingDeepDataTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc deepdata
  exact U0CardTheorems.phibRadicalData_of_imageWindingDeepData
    hUo hUc hUne hUinf hU_ext hU_esc deepdata

/-- U0 topological deep-provider target: odd image-winding data constructs the original
`PhibKummerInputs` provider. -/
def U0PhibKummerInputsFromImageWindingDeepDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibImageWindingDeepData U b →
    U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for the U0 image-winding-data-to-Kummer-inputs provider. -/
theorem u0_phib_kummerInputs_from_imageWindingDeepData :
    U0PhibKummerInputsFromImageWindingDeepDataTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc deepdata
  exact U0CardTheorems.phibKummerInputs_of_imageWindingDeepData
    hUo hUc hUne hUinf hU_ext hU_esc deepdata

/-- U0 topological deep-provider target: odd image-winding data constructs the equivalent
`PhibSquareRootDeckData` provider. -/
def U0PhibSquareRootDeckDataFromImageWindingDeepDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibImageWindingDeepData U b →
    U0CardTheorems.PhibSquareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for the U0 image-winding-data-to-square-root-deck provider. -/
theorem u0_phib_squareRootDeckData_from_imageWindingDeepData :
    U0PhibSquareRootDeckDataFromImageWindingDeepDataTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc deepdata
  exact U0CardTheorems.phibSquareRootDeckData_of_imageWindingDeepData
    hUo hUc hUne hUinf hU_ext hU_esc deepdata

/-- U0 carrier-independence target from topological image-winding deep data. -/
def U0PhiIndependenceCarrierFromImageWindingDeepDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibImageWindingDeepData U b →
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext))

/-- Formal wrapper for U0 carrier independence from topological image-winding deep data. -/
theorem u0_phi_independence_carrier_from_imageWindingDeepData :
    U0PhiIndependenceCarrierFromImageWindingDeepDataTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc deepdata
  exact U0CardTheorems.u0_phi_independence_carrier_imageWindingDeepData
    hUo hUc hUne hUinf hU_ext hU_esc deepdata

/-- U0 escape-carrier target from topological image-winding deep data. -/
def U0PhiIndependenceEscapeCarrierFromImageWindingDeepDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibImageWindingDeepData U b →
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U)
        (u0AnSub (hU_esc.trans (U0CardTheorems.escapeOpen_subset_U0Ext b))))

/-- Formal wrapper for U0 escape-carrier independence from topological image-winding deep data. -/
theorem u0_phi_independence_escapeCarrier_from_imageWindingDeepData :
    U0PhiIndependenceEscapeCarrierFromImageWindingDeepDataTarget := by
  intro U hUo hUc hUne hUinf b hU_esc deepdata
  exact U0CardTheorems.u0_phi_independence_escapeCarrier_imageWindingDeepData
    hUo hUc hUne hUinf hU_esc deepdata

/-- Connected U0 card wrapper from escape-carrier topological image-winding deep data. -/
theorem u0_phi_independence_connected_escapeCarrier_from_imageWindingDeepData :
    U0PhiIndependenceEscapeCarrierFromImageWindingDeepDataTarget := by
  intro U hUo hUc hUne hUinf b hU_esc deepdata
  exact U0CardTheorems.u0_phi_independence_connected_escapeCarrier_imageWindingDeepData
    hUo hUc hUne hUinf hU_esc deepdata

/-- Disconnected U0 card wrapper from escape-carrier topological image-winding deep data. -/
theorem u0_phi_independence_disconnected_escapeCarrier_from_imageWindingDeepData :
    U0PhiIndependenceEscapeCarrierFromImageWindingDeepDataTarget := by
  intro U hUo hUc hUne hUinf b hU_esc deepdata
  exact U0CardTheorems.u0_phi_independence_disconnected_escapeCarrier_imageWindingDeepData
    hUo hUc hUne hUinf hU_esc deepdata

/-- All-parameter U0 card wrapper from escape-carrier topological image-winding deep data. -/
theorem u0_phi_independence_all_parameters_escapeCarrier_from_imageWindingDeepData :
    U0PhiIndependenceEscapeCarrierFromImageWindingDeepDataTarget := by
  intro U hUo hUc hUne hUinf b hU_esc deepdata
  exact U0CardTheorems.u0_phi_independence_all_parameters_escapeCarrier_imageWindingDeepData
    hUo hUc hUne hUinf hU_esc deepdata

/-- U0 escape-local topological deep-provider target: if the deep domains already lie in
`escapeOpen b`, the `U0NaturalBoundary.Ext` containment required by the older provider is automatic. -/
def U0PhibRadicalDataFromImageWindingEscapeDeepDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibImageWindingEscapeDeepData U b →
    U0CardTheorems.PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for escape-local image-winding-data to U0 radical data. -/
theorem u0_phib_radicalData_from_imageWindingEscapeDeepData :
    U0PhibRadicalDataFromImageWindingEscapeDeepDataTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc deepdata
  exact U0CardTheorems.phibRadicalData_of_imageWindingEscapeDeepData
    hUo hUc hUne hUinf hU_ext hU_esc deepdata

/-- U0 escape-local topological deep-provider target: escape-local image-winding data constructs the
original `PhibKummerInputs` provider. -/
def U0PhibKummerInputsFromImageWindingEscapeDeepDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibImageWindingEscapeDeepData U b →
    U0CardTheorems.PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for escape-local image-winding-data to U0 Kummer inputs. -/
theorem u0_phib_kummerInputs_from_imageWindingEscapeDeepData :
    U0PhibKummerInputsFromImageWindingEscapeDeepDataTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc deepdata
  exact U0CardTheorems.phibKummerInputs_of_imageWindingEscapeDeepData
    hUo hUc hUne hUinf hU_ext hU_esc deepdata

/-- U0 escape-local topological deep-provider target: escape-local image-winding data constructs the
equivalent `PhibSquareRootDeckData` provider. -/
def U0PhibSquareRootDeckDataFromImageWindingEscapeDeepDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibImageWindingEscapeDeepData U b →
    U0CardTheorems.PhibSquareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc

/-- Formal wrapper for escape-local image-winding-data to U0 square-root deck data. -/
theorem u0_phib_squareRootDeckData_from_imageWindingEscapeDeepData :
    U0PhibSquareRootDeckDataFromImageWindingEscapeDeepDataTarget := by
  intro U hUo hUc hUne hUinf hU_ext b hU_esc deepdata
  exact U0CardTheorems.phibSquareRootDeckData_of_imageWindingEscapeDeepData
    hUo hUc hUne hUinf hU_ext hU_esc deepdata

/-- U0 escape-carrier target from escape-local topological image-winding deep data. -/
def U0PhiIndependenceEscapeCarrierFromImageWindingEscapeDeepDataTarget : Prop :=
  ∀ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (b : ℂ) (hU_esc : U ⊆ escapeOpen b),
    U0CardTheorems.PhibImageWindingEscapeDeepData U b →
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U)
        (u0AnSub (hU_esc.trans (U0CardTheorems.escapeOpen_subset_U0Ext b))))

/-- Formal wrapper for U0 escape-carrier independence from escape-local image-winding deep data. -/
theorem u0_phi_independence_escapeCarrier_from_imageWindingEscapeDeepData :
    U0PhiIndependenceEscapeCarrierFromImageWindingEscapeDeepDataTarget := by
  intro U hUo hUc hUne hUinf b hU_esc deepdata
  exact U0CardTheorems.u0_phi_independence_escapeCarrier_imageWindingEscapeDeepData
    hUo hUc hUne hUinf hU_esc deepdata

/-- Connected U0 card wrapper from escape-local topological image-winding deep data. -/
theorem u0_phi_independence_connected_escapeCarrier_from_imageWindingEscapeDeepData :
    U0PhiIndependenceEscapeCarrierFromImageWindingEscapeDeepDataTarget := by
  intro U hUo hUc hUne hUinf b hU_esc deepdata
  exact U0CardTheorems.u0_phi_independence_connected_escapeCarrier_imageWindingEscapeDeepData
    hUo hUc hUne hUinf hU_esc deepdata

/-- Disconnected U0 card wrapper from escape-local topological image-winding deep data. -/
theorem u0_phi_independence_disconnected_escapeCarrier_from_imageWindingEscapeDeepData :
    U0PhiIndependenceEscapeCarrierFromImageWindingEscapeDeepDataTarget := by
  intro U hUo hUc hUne hUinf b hU_esc deepdata
  exact U0CardTheorems.u0_phi_independence_disconnected_escapeCarrier_imageWindingEscapeDeepData
    hUo hUc hUne hUinf hU_esc deepdata

/-- All-parameter U0 card wrapper from escape-local topological image-winding deep data. -/
theorem u0_phi_independence_all_parameters_escapeCarrier_from_imageWindingEscapeDeepData :
    U0PhiIndependenceEscapeCarrierFromImageWindingEscapeDeepDataTarget := by
  intro U hUo hUc hUne hUinf b hU_esc deepdata
  exact U0CardTheorems.u0_phi_independence_all_parameters_escapeCarrier_imageWindingEscapeDeepData
    hUo hUc hUne hUinf hU_esc deepdata

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-! ## Hurwitz genuine-`hzeta` capstones

Bridge closure: the model capstones (`exp + tailFactored` blocks) restated against the ACTUAL
Hurwitz zeta `hzeta s a = ∑' m, (m+a)^{-s}`.  The relation hypothesis is imposed at
`a = -n + x` with `0 < Im x` (upper side of the negative-integer ray) — the honest window, since
the principal-branch split of the Hurwitz tail matches the analytic factored tail exactly there;
the identity theorem then extends the model relation to the full strip. -/

/-- Genuine-`hzeta` N=2 target: a polynomial-coefficient quadratic relation among the actual
`hzeta (s+k) ·` (`k ≤ 2`) near the negative-integer ray (upper side) has only zero coefficients;
only `Re s > 1` and `s ∉ ℤ` are assumed. -/
def HurwitzN2HZetaUnconditionalTarget (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, (k : ℂ) ≠ s) →
  ∀ (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ) (N : ℕ),
    (∀ n, N ≤ n → ∀ x : ℂ, ‖x‖ < 1 / 2 → 0 < x.im →
      (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval (-(n : ℂ) + x)
          * (HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ) + x)
            * HurwitzZetaShift.hzeta (s + (j : ℂ)) (-(n : ℂ) + x)))
        + (∑ k : Fin 3, (l k).eval (-(n : ℂ) + x)
            * HurwitzZetaShift.hzeta (s + (k : ℂ)) (-(n : ℂ) + x))
        + cc.eval (-(n : ℂ) + x) = 0) →
    q 0 0 = 0 ∧ q 2 2 = 0 ∧ q 1 1 = 0 ∧ q 0 2 + q 2 0 = 0
      ∧ l 2 = 0 ∧ l 0 = 0 ∧ l 1 = 0 ∧ cc = 0

/-- Genuine-`hzeta` N=2 capstone, proved. -/
theorem hurwitz_n2_hzeta_unconditional (s : ℂ) : HurwitzN2HZetaUnconditionalTarget s := by
  intro hs1 hsZ q l cc N hrel
  exact HurwitzN2HZeta.hurwitz_n2_hzeta_unconditional hs1 hsZ q l cc (N := N) hrel

/-- Genuine-`hzeta` N=2 target, upper-half-plane form: the same conclusion assuming the relation
at every `a` in the upper half-plane. -/
def HurwitzN2HZetaUpperHalfPlaneTarget (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, (k : ℂ) ≠ s) →
  ∀ (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ),
    (∀ a : ℂ, 0 < a.im →
      (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval a
          * (HurwitzZetaShift.hzeta (s + (i : ℂ)) a * HurwitzZetaShift.hzeta (s + (j : ℂ)) a))
        + (∑ k : Fin 3, (l k).eval a * HurwitzZetaShift.hzeta (s + (k : ℂ)) a)
        + cc.eval a = 0) →
    q 0 0 = 0 ∧ q 2 2 = 0 ∧ q 1 1 = 0 ∧ q 0 2 + q 2 0 = 0
      ∧ l 2 = 0 ∧ l 0 = 0 ∧ l 1 = 0 ∧ cc = 0

/-- Genuine-`hzeta` N=2 upper-half-plane capstone, proved. -/
theorem hurwitz_n2_hzeta_upper_half_plane (s : ℂ) : HurwitzN2HZetaUpperHalfPlaneTarget s := by
  intro hs1 hsZ q l cc hrel
  exact HurwitzN2HZeta.hurwitz_n2_hzeta_upper_half_plane hs1 hsZ q l cc hrel

/-- Genuine-`hzeta` all-`N` quadratic-block target: a polynomial-coefficient quadratic relation
among the actual `hzeta (s+k) ·` (`0 ≤ k ≤ N`) near the negative-integer ray (upper side) kills
the entire quadratic filtration `AqN`. -/
def HurwitzAllNHZetaQuadraticBlockTarget (N : ℕ) (s : ℂ) : Prop :=
  1 < s.re →
  (∀ k : ℤ, (k : ℂ) ≠ s) →
  ∀ (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ) (l : Fin (N + 1) → Polynomial ℂ)
      (cc : Polynomial ℂ) (M : ℕ),
    (∀ n, M ≤ n → ∀ x : ℂ, ‖x‖ < 1 / 2 → 0 < x.im →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + x)
          * (HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ) + x)
            * HurwitzZetaShift.hzeta (s + (j : ℂ)) (-(n : ℂ) + x)))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + x)
            * HurwitzZetaShift.hzeta (s + (k : ℂ)) (-(n : ℂ) + x))
        + cc.eval (-(n : ℂ) + x) = 0) →
    ∀ w, w ≤ 2 * N → HurwitzAllNQuadFilt.AqN q w = 0

/-- Genuine-`hzeta` all-`N` quadratic-block capstone, proved. -/
theorem hurwitz_all_n_hzeta_quadratic_block (N : ℕ) (s : ℂ) :
    HurwitzAllNHZetaQuadraticBlockTarget N s := by
  intro hs1 hsZ q l cc M hrel
  exact HurwitzN2HZeta.hurwitz_allN_hzeta_quadratic_block N hs1 hsZ q l cc (M := M) hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-! ## u₀ ⟂ φ — the circle-window reduction

The corrected reduction of the `u0-phi-independence` cards.  The previously registered
image-winding deep-data interface is unsatisfiable (every component of the escape bad set
carries an even count of `f^[k]`-zeros, so all avoidable windings are even); the honest
remaining analytic input is the window continuation `(Ω, φ)` of the Böttcher coordinate to a
connected window touching the unit circle, and this target consumes exactly that. -/

/-- Circle-window target: given a window continuation `(Ω, φ)` touching the unit circle with
`Ω ∩ Ext` preconnected, no nonzero positive-`u₀`-degree polynomial relation
`P(z, φ(z), u₀(z)) = 0` (with separable-specialization data at some `w ∈ Ω`) can hold on any
nonempty open piece of `Ω ∩ Ext`. -/
def U0PhiCircleWindowTarget : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → IsPreconnected Ω →
    IsPreconnected (Ω ∩ U0NaturalBoundary.Ext) →
  ∀ (φ : ℂ → ℂ), AnalyticOnNhd ℂ φ Ω →
  ∀ (P : (Polynomial (Polynomial ℂ))[X]), 1 ≤ P.natDegree →
  ∀ w, w ∈ Ω →
    ((∑ i : Fin (P.natDegree + 1),
      C ((P.coeff i).eval₂ (evalRingHom w) (φ w)) * X ^ (i : ℕ) : ℂ[X]).coeff
        P.natDegree ≠ 0) →
    ((∑ i : Fin (P.natDegree + 1),
      C ((P.coeff i).eval₂ (evalRingHom w) (φ w)) * X ^ (i : ℕ) : ℂ[X]).Separable) →
  ∀ z₁, z₁ ∈ Ω → ‖z₁‖ = 1 →
  ∀ (V : Set ℂ), IsOpen V → V.Nonempty → V ⊆ Ω ∩ U0NaturalBoundary.Ext →
    (∀ z ∈ V, P.eval₂ (eval₂RingHom (evalRingHom z) (φ z)) (U0.u0 z) = 0) →
  False

/-- The circle-window reduction, proved. -/
theorem u0_phi_circle_window : U0PhiCircleWindowTarget := by
  intro Ω hΩo hΩc hDc φ hφ P hd w hw hleadw hsepw z₁ hz₁ hz₁norm V hVo hVne hVD hrel
  exact U0PhiCircleWindow.u0_phi_windowed_no_relation_3var hΩo hΩc hDc hφ P hd hw
    hleadw hsepw hz₁ hz₁norm hVo hVne hVD hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-! ## u₀ ⟂ φ — the `b = 4` window instance (window object CONSTRUCTED)

`U0PhiFourWindow.phiFour z = exp(½·bottcherLog 4 (z²+4))` is analytic on the open disk
`ball 0 (21/20)` — containing the whole unit circle — and is a canonical Böttcher branch
(`phiFour_sq : phiFour z ^ 2 = bottcherCoord 4 (z²+4)`).  The circle-window reduction therefore
fires unconditionally at `b = 4`. -/

/-- `b = 4` window target: no positive-`u₀`-degree polynomial relation between `u₀` and the
constructed Böttcher branch `phiFour` (with separable specialization data) on any nonempty open
subset of the annulus `{1 < ‖z‖ < 21/20}`. -/
def U0PhiFourWindowTarget : Prop :=
  ∀ (P : (Polynomial (Polynomial ℂ))[X]), 1 ≤ P.natDegree →
  ∀ w, w ∈ Metric.ball (0 : ℂ) (21 / 20) →
    ((∑ i : Fin (P.natDegree + 1),
      C ((P.coeff i).eval₂ (evalRingHom w) (U0PhiFourWindow.phiFour w)) * X ^ (i : ℕ) : ℂ[X]).coeff
        P.natDegree ≠ 0) →
    ((∑ i : Fin (P.natDegree + 1),
      C ((P.coeff i).eval₂ (evalRingHom w) (U0PhiFourWindow.phiFour w)) * X ^ (i : ℕ) :
        ℂ[X]).Separable) →
  ∀ (V : Set ℂ), IsOpen V → V.Nonempty →
    V ⊆ Metric.ball (0 : ℂ) (21 / 20) ∩ U0NaturalBoundary.Ext →
    (∀ z ∈ V, P.eval₂ (eval₂RingHom (evalRingHom z) (U0PhiFourWindow.phiFour z)) (U0.u0 z) = 0) →
  False

/-- The `b = 4` window instance, proved — the window continuation is no longer a hypothesis. -/
theorem u0_phi_four_window : U0PhiFourWindowTarget := by
  intro P hd w hw hleadw hsepw V hVo hVne hVD hrel
  exact U0PhiFourWindow.u0_phiFour_no_relation P hd hw hleadw hsepw hVo hVne hVD hrel

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-! ## u₀ ⟂ φ — separability-free window closure

The min-poly/separability normalization is now internal (`U0WindowNormalization`): a windowed
relation needs only its nondegeneracy witness (some positive-index coefficient function not
identically zero).  With the constructed `b = 4` window this closes the u₀-side of the card at
`b = 4` with no analytic side conditions at all. -/

/-- `b = 4` separability-free target: a polynomial relation `P(z, phiFour z, u₀ z) = 0` on a
nonempty open piece of the annulus, together with a nondegeneracy witness for some positive
`u₀`-degree coefficient, is contradictory. -/
def U0PhiFourNondegenerateTarget : Prop :=
  ∀ (P : (Polynomial (Polynomial ℂ))[X]) (i₀ : ℕ), 1 ≤ i₀ →
  (∃ z ∈ Metric.ball (0 : ℂ) (21 / 20) ∩ U0NaturalBoundary.Ext,
    U0WindowNormalization.coeffFun U0PhiFourWindow.phiFour (P.coeff i₀) z ≠ 0) →
  ∀ (V : Set ℂ), IsOpen V → V.Nonempty →
    V ⊆ Metric.ball (0 : ℂ) (21 / 20) ∩ U0NaturalBoundary.Ext →
    (∀ z ∈ V, P.eval₂ (eval₂RingHom (evalRingHom z) (U0PhiFourWindow.phiFour z)) (U0.u0 z) = 0) →
  False

/-- The `b = 4` separability-free closure, proved. -/
theorem u0_phi_four_nondegenerate : U0PhiFourNondegenerateTarget := by
  intro P i₀ hi₀ hnondeg V hVo hVne hVD hrel
  exact U0PhiFourWindow.u0_phiFour_no_relation_nondegenerate P hi₀ hnondeg hVo hVne hVD hrel

end FullyProvenNewTargets

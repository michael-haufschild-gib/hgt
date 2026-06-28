/-
# `2-fully-proven/new` Lean targets, excluding the hRigid path

Door grade: BRIDGE / formal ledger.  This file adds no mathematical shortcut: it
collects the Lean proof objects currently serving the cards in
`docs/drafts/pipeline/2-fully-proven/new`, with the hRigid branch deliberately
left out because that path is owned by the parallel agent.

The rule here is strict.  A declaration below is either:
* a theorem wrapper around an existing proof object, or
* a target `Prop` whose proof is supplied immediately by an existing theorem.

For cards whose paper statement is wider than the present Lean theorem, the
wrapper name says which branch is proved.
-/
import GaloisForLFunctions.Hurwitz.N2Final
import GaloisForLFunctions.Hurwitz.NonRationality
import GaloisForLFunctions.Hurwitz.N2HalfInteger
import GaloisForLFunctions.Hurwitz.AllNQuadFilt
import GaloisForLFunctions.Hurwitz.AllNHalfInteger
import GaloisForLFunctions.Hurwitz.AllNRowExtraction
import GaloisForLFunctions.Hurwitz.AllNRelationClose
import GaloisForLFunctions.Hurwitz.AllNTailIndependence
import GaloisForLFunctions.Hurwitz.MonodromyScalar
import GaloisForLFunctions.Hurwitz.PolylogPoleTower
import GaloisForLFunctions.U0.U0CardTheorems
import GaloisForLFunctions.U0.U0CoverMono
import GaloisForLFunctions.U0.U0CoverTransport
import GaloisForLFunctions.U0.U0PhiLifts
import GaloisForLFunctions.U0.U0PhiCard
import GaloisForLFunctions.Bottcher.AlgIndep
import GaloisForLFunctions.Bottcher.CoverMonodromy
import GaloisForLFunctions.Bottcher.DyadicMonodromy
import GaloisForLFunctions.Bottcher.MonodromyMultiplier
import GaloisForLFunctions.Bottcher.Q62DeepDataAssembly
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

/-- Order-only target for
`not-new-but-required/bottcher-dyadic-monodromy-finite-type-absence.md`. -/
def BottcherDyadicUnboundedOrderTarget : Prop :=
  ∀ d : ℕ, ∃ ζ : ℂ, d < orderOf ζ

/-- Formal wrapper: dyadic multipliers have unbounded order. -/
theorem bottcher_dyadic_monodromy_finite_type_absence_order :
    BottcherDyadicUnboundedOrderTarget :=
  Bottcher.exists_complex_orderOf_gt

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

/-- Existing hDisc deep-data close for q62; exposed as a Lean object so the card
mapping has a stable name without importing the hRigid path. -/
def q62_both_disconnected_deep_data_escape_formal_proof :=
  @Bottcher.q62_disconnected_of_deepData_escape

/-- Existing additive loop/deck close for q62 both-disconnected; exposed for the
same card mapping. -/
def q62_both_disconnected_additive_loop_deck_formal_proof :=
  @Bottcher.q62_independence_disconnected_of_dyadic_additive_loop_and_two_zfixing_decks

/-- Existing vertical-strip loop/deck close for q62 both-disconnected; exposed for
the same card mapping. -/
def q62_both_disconnected_vertical_strip_loop_deck_formal_proof :=
  @Bottcher.q62_independence_disconnected_of_dyadic_verticalStrip_loop_and_two_zfixing_decks

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

end FullyProvenNewTargets

namespace FullyProvenNewTargets

/-- Escape-form deep-data q62 disconnected close where `φ₂` compatibility and transcendence are both
built from supplied escape/radical data rather than separate premises. -/
def q62_disconnected_deep_data_escape_two_radical_formal_proof :=
  @Bottcher.q62_disconnected_of_deepData_escape_two_radical

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

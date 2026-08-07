import GaloisForLFunctions.RHTower.DeningerFreeSheafAcyclic

/-!
# Finite filtrations with acyclic graded pieces

A finite filtration of sheaves whose successive quotients are acyclic has acyclic total object, by
iterating the two-out-of-three property of acyclicity in a short exact sequence.  Consequently the
sections of every step of the filtration surject onto the sections of its quotient, and a section of
a step that dies in the quotient comes from the previous step: the filtration of global sections has
the same graded pieces as the filtration of sheaves.

This is the induction over a finite relative cell filtration: the graded pieces of such a filtration
on a character stage are free analytic sheaves of finite rank, which are acyclic, so ordinary global
sections compute the attachment.

* `RHTower.deningerAcyclicOn_of_filtration` : the total object of the filtration is acyclic.
* `RHTower.deningerFiltration_sections_surjective` : sections of a step surject onto the quotient.
* `RHTower.deningerFiltration_sections_exact` : sections are exact in the middle.
* `RHTower.deningerFreeCellFiltration_acyclic` : a filtration by free sheaves of finite rank on
  `(ℂ^×)^n` is acyclic.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite TopCat

universe w u

section Filtration

variable {X : TopCat.{u}} [CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]
  {F G : ℕ → TopCat.Sheaf AddCommGrpCat.{u} X} {f : ∀ i, F i ⟶ F (i + 1)}
  {g : ∀ i, F (i + 1) ⟶ G i} {hzero : ∀ i, f i ≫ g i = 0}

/-- The `i`-th step of a filtration: the previous stage, the current stage, and the graded piece. -/
abbrev deningerFiltrationStep (f : ∀ i, F i ⟶ F (i + 1)) (g : ∀ i, F (i + 1) ⟶ G i)
    (hzero : ∀ i, f i ≫ g i = 0) (i : ℕ) : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (f i) (g i) (hzero i)

/-- **A finite filtration with acyclic graded pieces has acyclic stages.**  Each stage is the middle
term of a short exact sequence whose ends are the previous stage and the graded piece, and acyclicity
is a two-out-of-three property there. -/
theorem deningerAcyclicOn_of_filtration
    (hSE : ∀ i, (deningerFiltrationStep f g hzero i).ShortExact) (U : Opens X)
    (h0 : DeningerAcyclicOn.{w} (F 0) U) (hgr : ∀ i, DeningerAcyclicOn.{w} (G i) U) :
    ∀ N, DeningerAcyclicOn.{w} (F N) U := by
  intro N
  induction N with
  | zero => exact h0
  | succ p ih => exact deningerAcyclicOn_middle (hSE p) U ih (hgr p)

/-- **The sections of a stage surject onto the sections of the graded piece.**  The obstruction is
the first cohomology of the previous stage, which the filtration makes vanish. -/
theorem deningerFiltration_sections_surjective
    (hSE : ∀ i, (deningerFiltrationStep f g hzero i).ShortExact) (U : Opens X)
    (h0 : DeningerAcyclicOn.{w} (F 0) U) (hgr : ∀ i, DeningerAcyclicOn.{w} (G i) U) (i : ℕ) :
    Function.Surjective (ConcreteCategory.hom ((g i).1.app (op U))) :=
  deningerSections_surjective_of_acyclic (hSE i) U
    (deningerAcyclicOn_of_filtration hSE U h0 hgr i)

omit [CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)] in
/-- **The sections of a filtration step are exact in the middle**: a section of a stage that dies in
the graded piece comes from the previous stage. -/
theorem deningerFiltration_sections_exact
    (hSE : ∀ i, (deningerFiltrationStep f g hzero i).ShortExact) (U : Opens X) (i : ℕ)
    (b : ToType ((F (i + 1)).1.obj (op U)))
    (hb : ConcreteCategory.hom ((g i).1.app (op U)) b = 0) :
    ∃ a : ToType ((F i).1.obj (op U)), ConcreteCategory.hom ((f i).1.app (op U)) a = b :=
  deningerSections_exact (hSE i) U b hb

end Filtration

section CharacterStage

open Complex

variable {n : ℕ}
  [CategoryTheory.HasExt.{w}
    (TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace (deningerPunctured n)))]
  {F : ℕ → TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace (deningerPunctured n))}
  {J : ℕ → Type} [∀ i, Fintype (J i)]
  {f : ∀ i, F i ⟶ F (i + 1)}
  {g : ∀ i, F (i + 1) ⟶ deningerFreeHolomorphicSheaf (deningerPunctured n) (J i)}
  {hzero : ∀ i, f i ≫ g i = 0}

/-- **A relative cell filtration on a character stage is acyclic for global sections.**  The graded
pieces are free analytic sheaves of finite rank, which Cartan's theorem B makes acyclic, and
acyclicity propagates up the filtration. -/
theorem deningerFreeCellFiltration_acyclic
    (hSE : ∀ i, (deningerFiltrationStep f g hzero i).ShortExact)
    (J₀ : Type) [Fintype J₀]
    (e : F 0 ≅ deningerFreeHolomorphicSheaf (deningerPunctured n) J₀) (N : ℕ) :
    DeningerAcyclicOn.{w} (F N) ⊤ :=
  deningerAcyclicOn_of_filtration.{w} hSE ⊤
    (deningerAcyclicOn_of_iso.{w} e.symm ⊤ (deningerFree_acyclicOn_punctured.{w} J₀))
    (fun i => deningerFree_acyclicOn_punctured.{w} (J i)) N

/-- **Ordinary global sections compute a relative cell attachment on a character stage.**  The
sections of a stage surject onto the sections of the attached free cell, and a section killed by the
attachment comes from the previous stage; so the filtration of global sections has the graded pieces
of the filtration of sheaves. -/
theorem deningerFreeCellFiltration_sections_surjective
    (hSE : ∀ i, (deningerFiltrationStep f g hzero i).ShortExact)
    (J₀ : Type) [Fintype J₀]
    (e : F 0 ≅ deningerFreeHolomorphicSheaf (deningerPunctured n) J₀) (i : ℕ) :
    Function.Surjective (ConcreteCategory.hom ((g i).1.app
      (op (⊤ : Opens (deningerSpace (deningerPunctured n)))))) :=
  deningerFiltration_sections_surjective.{w} hSE ⊤
    (deningerAcyclicOn_of_iso.{w} e.symm ⊤ (deningerFree_acyclicOn_punctured.{w} J₀))
    (fun j => deningerFree_acyclicOn_punctured.{w} (J j)) i

end CharacterStage

end RHTower

import GaloisForLFunctions.HTGeometry.ReducedH1FirstBetti
import GaloisForLFunctions.HTGeometry.GeneralKoszulComplex
import GaloisForLFunctions.HTGeometry.StanleyReisnerHollowSimplexRank
import GaloisForLFunctions.HTGeometry.HigherCycleTorsionFree

/-!
# Hochster realization for the 4-cycle: algebraic `Tor₂` matches topological `H̃¹`

Hochster's formula reads the multigraded Tor of a Stanley–Reisner ring off the reduced simplicial
cohomology of restricted subcomplexes:

`Torᵢ(k[Δ], k)_W ≅ H̃^{|W|−i−1}(Δ|W; k)`.

For the boundary of a square — the `4`-cycle `C₄`, a one-dimensional complex — and the full vertex
set `W` (`|W| = 4`), the top algebraic degree `i = 2` matches `H̃^{4−2−1} = H̃¹`.  The `1`-skeleton of
a one-dimensional complex is the complex itself, so the simplicial `H̃¹(C₄)` coincides with the graph
reduced first cohomology of `finrank_reducedH1`.

This file computes that topological side — `dim H̃¹(C₄) = 1`, hence nonzero — and packages it with the
already-established algebraic side `srC4KoszulTor_ne_zero` (the general vertex-Koszul `Tor₂` class of
the `C₄` Stanley–Reisner ring is nonzero).  Both invariants are nonzero of the same dimension `1`,
the concrete realization of Hochster's iso predicted at this instance.
-/

namespace GaloisForLFunctions.HTGeometry

open SimpleGraph

noncomputable section

/-- A connected finite graph has exactly one connected component: every component is the class of a
fixed base vertex, since any vertex is reachable from it. -/
theorem card_connectedComponent_eq_one {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : G.Connected) : Fintype.card G.ConnectedComponent = 1 := by
  rw [Fintype.card_eq_one_iff]
  obtain ⟨v⟩ := h.nonempty
  refine ⟨G.connectedComponentMk v, fun c => ?_⟩
  induction c using SimpleGraph.ConnectedComponent.ind with
  | _ u => exact SimpleGraph.ConnectedComponent.sound (h u v)

/-- **Reduced first cohomology of the `4`-cycle is one-dimensional.**  From the first-Betti-number
formula `dim H̃¹ = |E| − |V| + components` with `|E| = 4`, `|V| = 4`, and `components = 1` (the cycle
is connected): `dim H̃¹(C₄) = 4 − (4 − 1) = 1`. -/
theorem finrank_reducedH1_cycleGraph4 (F : Type*) [Field F] :
    Module.finrank F ((orientedEdges (cycleGraph 4) → F)
      ⧸ LinearMap.range (orientedCoboundary (cycleGraph 4) F)) = 1 := by
  rw [finrank_reducedH1, card_connectedComponent_eq_one (cycleGraph 4) cycleGraph_connected,
    show (orientedEdges (cycleGraph 4)).card = 4 from by decide, Fintype.card_fin]

/-- The reduced first cohomology of the `4`-cycle is nontrivial (nonzero) — the topological witness of
Hochster's `Tor₂`-class for `C₄`. -/
theorem reducedH1_cycleGraph4_nontrivial (F : Type*) [Field F] :
    Nontrivial ((orientedEdges (cycleGraph 4) → F)
      ⧸ LinearMap.range (orientedCoboundary (cycleGraph 4) F)) :=
  Module.nontrivial_of_finrank_eq_succ (finrank_reducedH1_cycleGraph4 F)

/-- **Hochster realization for `C₄`: both sides of the iso are nonzero.**  For any Stanley–Reisner
configuration realizing the `4`-cycle (four distinct vertices whose consecutive pairs are edges and
whose two diagonals are non-faces), the algebraic top Koszul homology `Tor₂` and the topological
reduced first cohomology `H̃¹(C₄)` are simultaneously nonzero — the concrete instance of
`Torᵢ(k[Δ], k)_W ≅ H̃^{|W|−i−1}(Δ|W)` at `i = 2`, `|W| = 4`. -/
theorem hochster_C4_both_nonzero {α : Type*} [DecidableEq α] [Fintype α] (F : Type*) [Field F]
    (facets : Finset (Finset α)) {a b c d : α}
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (had : a ≠ d) (hac : a ≠ c) (hbd : b ≠ d)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (had_f : IsFaceOf (↑facets : Set (Finset α)) {a, d})
    (hac_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (hbd_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {b, d}) :
    Nontrivial ((orientedEdges (cycleGraph 4) → F)
        ⧸ LinearMap.range (orientedCoboundary (cycleGraph 4) F))
      ∧ Submodule.Quotient.mk (⟨srC4KoszulCycle facets a b c d,
          srC4KoszulCycle_mem_koszulCycles facets hac hac_nf hbd hbd_nf⟩ :
          koszulCycles (srVertexX F facets)) ≠ (0 : koszulTor (srVertexX F facets)) :=
  ⟨reducedH1_cycleGraph4_nontrivial F,
    srC4KoszulTor_ne_zero facets hab hbc hcd had hac hbd ha hb hc hd hab_f hbc_f hcd_f had_f
      hac_nf hbd_nf⟩

/-- The `4`-cycle Stanley–Reisner complex on `Fin 4`: the four square edges as maximal faces. -/
def c4Facets : Finset (Finset (Fin 4)) := {{0, 1}, {1, 2}, {2, 3}, {0, 3}}

theorem c4_ne_02 : (0 : Fin 4) ≠ 2 := by decide

theorem c4_ne_13 : (1 : Fin 4) ≠ 3 := by decide

/-- The diagonal `{0,2}` is a non-face of `C₄`. -/
theorem c4_ac_not_face : ¬ IsFaceOf (↑c4Facets : Set (Finset (Fin 4))) {0, 2} := by
  simp only [IsFaceOf, c4Facets, Finset.mem_coe]; decide

/-- The diagonal `{1,3}` is a non-face of `C₄`. -/
theorem c4_bd_not_face : ¬ IsFaceOf (↑c4Facets : Set (Finset (Fin 4))) {1, 3} := by
  simp only [IsFaceOf, c4Facets, Finset.mem_coe]; decide

/-- **Fully unconditional Hochster realization for `C₄`.**  Instantiating `hochster_C4_both_nonzero`
at the concrete square complex `c4Facets` (vertices `0,1,2,3`; edges the four sides; diagonals `{0,2}`
and `{1,3}` non-faces), the algebraic top Koszul homology `Tor₂` and the topological reduced first
cohomology `H̃¹(C₄)` are both nonzero with no remaining hypotheses. -/
theorem hochster_C4_realization (F : Type*) [Field F] :
    Nontrivial ((orientedEdges (cycleGraph 4) → F)
        ⧸ LinearMap.range (orientedCoboundary (cycleGraph 4) F))
      ∧ Submodule.Quotient.mk (⟨srC4KoszulCycle c4Facets 0 1 2 3,
          srC4KoszulCycle_mem_koszulCycles c4Facets c4_ne_02 c4_ac_not_face c4_ne_13 c4_bd_not_face⟩ :
          koszulCycles (srVertexX F c4Facets)) ≠ (0 : koszulTor (srVertexX F c4Facets)) :=
  hochster_C4_both_nonzero F c4Facets
    (by decide) (by decide) (by decide) (by decide) c4_ne_02 c4_ne_13
    (by simp only [IsFaceOf, c4Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c4Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c4Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c4Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c4Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c4Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c4Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c4Facets, Finset.mem_coe]; decide)
    c4_ac_not_face c4_bd_not_face

/-! ## Empty triangle `C₃`: the `Tor₁` strand of Hochster's formula meets `H̃¹`

The empty triangle `∂Δ²` (three edges, no filling `2`-face) is the one hollow simplex that is still a
graph, so its reduced `H̃¹` is computed by `finrank_reducedH1`.  Under Hochster's formula its hole sits
in `Tor₁` at `|σ| = 3` (`H̃^{3−1−1} = H̃¹`), realized algebraically by
`srEmptyTriangle_firstKoszulHomology_nonzero`.  This bridges the card's *primary* first-Koszul
hollow-simplex strand — distinct from the general `koszulTor` `Tor₂` used for `C₄` — to the topological
side. -/

/-- **Reduced first cohomology of the triangle `C₃` is one-dimensional** (`3 − (3 − 1) = 1`). -/
theorem finrank_reducedH1_cycleGraph3 (F : Type*) [Field F] :
    Module.finrank F ((orientedEdges (cycleGraph 3) → F)
      ⧸ LinearMap.range (orientedCoboundary (cycleGraph 3) F)) = 1 := by
  rw [finrank_reducedH1, card_connectedComponent_eq_one (cycleGraph 3) cycleGraph_connected,
    show (orientedEdges (cycleGraph 3)).card = 3 from by decide, Fintype.card_fin]

/-- The reduced first cohomology of the triangle `C₃` is nontrivial. -/
theorem reducedH1_cycleGraph3_nontrivial (F : Type*) [Field F] :
    Nontrivial ((orientedEdges (cycleGraph 3) → F)
      ⧸ LinearMap.range (orientedCoboundary (cycleGraph 3) F)) :=
  Module.nontrivial_of_finrank_eq_succ (finrank_reducedH1_cycleGraph3 F)

/-- **Hochster realization for the empty triangle `C₃` (`Tor₁` strand): both sides nonzero.**  For any
complex realizing an empty triangle `{a,b,c}` (three edges present, the triangle itself a non-face), the
algebraic first Koszul homology class `x_b x_c · e_a` and the topological reduced first cohomology
`H̃¹(C₃)` are simultaneously nonzero — the `i = 1`, `|W| = 3` instance of Hochster's iso, via the card's
first-Koszul hollow-simplex strand. -/
theorem hochster_C3_both_nonzero {α : Type*} [DecidableEq α] [Fintype α] (F : Type*) [Field F]
    (facets : Finset (Finset α)) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hfab : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hfbc : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hfac : IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c})
    (hnf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, b, c}) :
    Nontrivial ((orientedEdges (cycleGraph 3) → F)
        ⧸ LinearMap.range (orientedCoboundary (cycleGraph 3) F))
      ∧ (srKoszulRelation facets
            (fun v => if v = a then srVertexX F facets b * srVertexX F facets c else 0) = 0
          ∧ ¬ ∃ cc : α → α → stanleyReisnerRing F facets,
            srKoszulBoundary facets cc
              = (fun v => if v = a then srVertexX F facets b * srVertexX F facets c else 0)) :=
  ⟨reducedH1_cycleGraph3_nontrivial F,
    srEmptyTriangle_firstKoszulHomology_nonzero facets hab hac hbc hfab hfbc hfac ha hb hc hnf⟩

/-- The empty-triangle complex on `Fin 3`: the three edges, no filling `2`-face. -/
def c3Facets : Finset (Finset (Fin 3)) := {{0, 1}, {1, 2}, {0, 2}}

/-- The triangle `{0,1,2}` itself is a non-face of `C₃`. -/
theorem c3_abc_not_face : ¬ IsFaceOf (↑c3Facets : Set (Finset (Fin 3))) {0, 1, 2} := by
  simp only [IsFaceOf, c3Facets, Finset.mem_coe]; decide

/-- **Fully unconditional Hochster realization for the empty triangle `C₃`.**  Instantiating
`hochster_C3_both_nonzero` at the concrete triangle-boundary complex `c3Facets`, both the algebraic
`Tor₁` class `x₁x₂ · e₀` and the topological `H̃¹(C₃)` are nonzero with no remaining hypotheses. -/
theorem hochster_C3_realization (F : Type*) [Field F] :
    Nontrivial ((orientedEdges (cycleGraph 3) → F)
        ⧸ LinearMap.range (orientedCoboundary (cycleGraph 3) F))
      ∧ (srKoszulRelation c3Facets
            (fun v => if v = 0 then srVertexX F c3Facets 1 * srVertexX F c3Facets 2 else 0) = 0
          ∧ ¬ ∃ cc : Fin 3 → Fin 3 → stanleyReisnerRing F c3Facets,
            srKoszulBoundary c3Facets cc
              = (fun v => if v = 0 then srVertexX F c3Facets 1 * srVertexX F c3Facets 2 else 0)) :=
  hochster_C3_both_nonzero F c3Facets (a := 0) (b := 1) (c := 2) (by decide) (by decide) (by decide)
    (by simp only [IsFaceOf, c3Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c3Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c3Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c3Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c3Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c3Facets, Finset.mem_coe]; decide)
    c3_abc_not_face

/-- **Exact Hochster iso at `C₃`: both sides are exactly one-dimensional.**  For the concrete empty
triangle, the topological reduced first cohomology `H̃¹(C₃)` has dimension exactly `1`, and the
algebraic multidegree-`{0,1,2}` first-Koszul syzygy space collapses exactly by the coefficient sum
(`w(l)` is a boundary iff `∑ l = 0`) — the exact-rank Hochster equality `Tor_{1,σ} ≅ H̃¹(∂Δ²)` at this
concrete complex, upgrading `hochster_C3_realization` from both-nonzero to both-dimension-`1`. -/
theorem hochster_C3_exact_rank (F : Type*) [Field F] :
    Module.finrank F ((orientedEdges (cycleGraph 3) → F)
        ⧸ LinearMap.range (orientedCoboundary (cycleGraph 3) F)) = 1
      ∧ ∀ l : Fin 3 → F, (∃ cc : Fin 3 → Fin 3 → stanleyReisnerRing F c3Facets,
          srKoszulBoundary c3Facets cc = srHollowSimplexSyzygyVec F c3Facets Finset.univ l)
        ↔ ∑ i, l i = 0 :=
  ⟨finrank_reducedH1_cycleGraph3 F,
    fun l => srHollowSimplexSyzygyVec_boundary_iff c3Facets Finset.univ Finset.univ_nonempty
      (fun i _ => by fin_cases i <;> (simp only [IsFaceOf, c3Facets, Finset.mem_coe]; decide)) l⟩

/-- Every proper face of the empty triangle `{0,1,2}` is present. -/
theorem c3_univ_hface : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
    IsFaceOf (↑c3Facets : Set (Finset (Fin 3))) ((Finset.univ : Finset (Fin 3)).erase i) :=
  fun i _ => by fin_cases i <;> (simp only [IsFaceOf, c3Facets, Finset.mem_coe]; decide)

/-- **Concrete degree-1 Hochster module iso at `C₃`.**  The topological reduced first cohomology
`H̃¹(C₃)` is one-dimensional, and (algebraic side) the descended `σ`-detector is `1` on the base first
Koszul homology class — so `R` is a *direct summand* of the first Koszul homology of the concrete empty
triangle (via the embedding `srHollowClassEquiv` and this retraction).  Both sides realize the same rank-
one `Tor_{1,{0,1,2}} ≅ H̃¹(∂Δ²)` at the module level. -/
theorem hochster_C3_direct_summand (F : Type*) [Field F] :
    Module.finrank F ((orientedEdges (cycleGraph 3) → F)
        ⧸ LinearMap.range (orientedCoboundary (cycleGraph 3) F)) = 1
      ∧ srHollowDetectorTor F c3Facets Finset.univ c3_univ_hface
          (srHollowBaseClass F c3Facets Finset.univ 0) = 1 :=
  ⟨finrank_reducedH1_cycleGraph3 F,
    srHollowDetectorTor_base c3Facets Finset.univ c3_univ_hface (Finset.mem_univ 0)⟩

/-! ## Higher cycles `C₅` (`Tor₃`) and `C₆` (`Tor₄`) meet `H̃¹`

Hochster's formula places the hole of the `n`-cycle in `Tor_{n−2}` at the full vertex set
(`H̃^{n−n+... } = H̃¹`): `Tor₃` for `C₅` (`|W| = 5`, `H̃^{5−3−1} = H̃¹`) and `Tor₄` for `C₆`
(`|W| = 6`, `H̃^{6−4−1} = H̃¹`).  The algebraic classes are the module `Tor` embeddings
`srPentTripleTorClass` / `srHexTupleTorClass`; the topological side is again the graph reduced first
cohomology, one-dimensional for every `n`-cycle. -/

/-- **Reduced first cohomology of the `5`-cycle is one-dimensional** (`5 − (5 − 1) = 1`). -/
theorem finrank_reducedH1_cycleGraph5 (F : Type*) [Field F] :
    Module.finrank F ((orientedEdges (cycleGraph 5) → F)
      ⧸ LinearMap.range (orientedCoboundary (cycleGraph 5) F)) = 1 := by
  rw [finrank_reducedH1, card_connectedComponent_eq_one (cycleGraph 5) cycleGraph_connected,
    show (orientedEdges (cycleGraph 5)).card = 5 from by decide, Fintype.card_fin]

/-- The reduced first cohomology of the `5`-cycle is nontrivial. -/
theorem reducedH1_cycleGraph5_nontrivial (F : Type*) [Field F] :
    Nontrivial ((orientedEdges (cycleGraph 5) → F)
      ⧸ LinearMap.range (orientedCoboundary (cycleGraph 5) F)) :=
  Module.nontrivial_of_finrank_eq_succ (finrank_reducedH1_cycleGraph5 F)

/-- **Reduced first cohomology of the `6`-cycle is one-dimensional** (`6 − (6 − 1) = 1`). -/
theorem finrank_reducedH1_cycleGraph6 (F : Type*) [Field F] :
    Module.finrank F ((orientedEdges (cycleGraph 6) → F)
      ⧸ LinearMap.range (orientedCoboundary (cycleGraph 6) F)) = 1 := by
  rw [finrank_reducedH1, card_connectedComponent_eq_one (cycleGraph 6) cycleGraph_connected,
    show (orientedEdges (cycleGraph 6)).card = 6 from by decide, Fintype.card_fin]

/-- The reduced first cohomology of the `6`-cycle is nontrivial. -/
theorem reducedH1_cycleGraph6_nontrivial (F : Type*) [Field F] :
    Nontrivial ((orientedEdges (cycleGraph 6) → F)
      ⧸ LinearMap.range (orientedCoboundary (cycleGraph 6) F)) :=
  Module.nontrivial_of_finrank_eq_succ (finrank_reducedH1_cycleGraph6 F)

/-- **Hochster realization for `C₅` (`Tor₃` strand): both sides nonzero.**  For any complex realizing a
pentagon (five distinct vertices, consecutive pairs edges, one skip-diagonal `{c,e}` a non-face), the
algebraic third Koszul homology class `srPentTripleTorClass` and the topological `H̃¹(C₅)` are
simultaneously nonzero — the `i = 3`, `|W| = 5` instance of Hochster's iso. -/
theorem hochster_C5_both_nonzero {α : Type*} [DecidableEq α] [Fintype α] (F : Type*) [Field F]
    (facets : Finset (Finset α)) {a b c d e : α}
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hea : e ≠ a)
    (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hea_f : IsFaceOf (↑facets : Set (Finset α)) {e, a})
    (hce_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {c, e}) :
    Nontrivial ((orientedEdges (cycleGraph 5) → F)
        ⧸ LinearMap.range (orientedCoboundary (cycleGraph 5) F))
      ∧ srPentTripleTorClass F facets a b c d e ≠ 0 :=
  ⟨reducedH1_cycleGraph5_nontrivial F,
    srPentTripleTorClass_ne_zero F facets hab hbc hcd hde hea hac hbd hce ha hb hc hd he
      hab_f hbc_f hcd_f hde_f hea_f hce_nf⟩

/-- The `5`-cycle Stanley–Reisner complex on `Fin 5`: the five pentagon edges as maximal faces. -/
def c5Facets : Finset (Finset (Fin 5)) := {{0, 1}, {1, 2}, {2, 3}, {3, 4}, {0, 4}}

/-- The skip-diagonal `{2,4}` is a non-face of `C₅`. -/
theorem c5_ce_not_face : ¬ IsFaceOf (↑c5Facets : Set (Finset (Fin 5))) {2, 4} := by
  simp only [IsFaceOf, c5Facets, Finset.mem_coe]; decide

/-- **Fully unconditional Hochster realization for `C₅`.**  At the concrete pentagon `c5Facets`, the
algebraic `Tor₃` class and the topological `H̃¹(C₅)` are both nonzero with no remaining hypotheses. -/
theorem hochster_C5_realization (F : Type*) [Field F] :
    Nontrivial ((orientedEdges (cycleGraph 5) → F)
        ⧸ LinearMap.range (orientedCoboundary (cycleGraph 5) F))
      ∧ srPentTripleTorClass F c5Facets 0 1 2 3 4 ≠ 0 :=
  hochster_C5_both_nonzero F c5Facets
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (by simp only [IsFaceOf, c5Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c5Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c5Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c5Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c5Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c5Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c5Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c5Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c5Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c5Facets, Finset.mem_coe]; decide)
    c5_ce_not_face

/-- **Hochster realization for `C₆` (`Tor₄` strand): both sides nonzero.**  For any complex realizing a
hexagon (six distinct vertices, consecutive pairs edges, one skip-diagonal `{d,f}` a non-face), the
algebraic fourth Koszul homology class `srHexTupleTorClass` and the topological `H̃¹(C₆)` are
simultaneously nonzero — the `i = 4`, `|W| = 6` instance of Hochster's iso. -/
theorem hochster_C6_both_nonzero {α : Type*} [DecidableEq α] [Fintype α] (F : Type*) [Field F]
    (facets : Finset (Finset α)) {a b c d e f : α}
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hef : e ≠ f) (hfa : f ≠ a)
    (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e) (hdf : d ≠ f)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (he : IsFaceOf (↑facets : Set (Finset α)) {e}) (hf : IsFaceOf (↑facets : Set (Finset α)) {f})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (hde_f : IsFaceOf (↑facets : Set (Finset α)) {d, e})
    (hef_f : IsFaceOf (↑facets : Set (Finset α)) {e, f})
    (hfa_f : IsFaceOf (↑facets : Set (Finset α)) {f, a})
    (hdf_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {d, f}) :
    Nontrivial ((orientedEdges (cycleGraph 6) → F)
        ⧸ LinearMap.range (orientedCoboundary (cycleGraph 6) F))
      ∧ srHexTupleTorClass F facets a b c d e f ≠ 0 :=
  ⟨reducedH1_cycleGraph6_nontrivial F,
    srHexTupleTorClass_ne_zero F facets hab hbc hcd hde hef hfa hac hbd hce hdf ha hb hc hd he hf
      hab_f hbc_f hcd_f hde_f hef_f hfa_f hdf_nf⟩

/-- The `6`-cycle Stanley–Reisner complex on `Fin 6`: the six hexagon edges as maximal faces. -/
def c6Facets : Finset (Finset (Fin 6)) := {{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 5}, {0, 5}}

/-- The skip-diagonal `{3,5}` is a non-face of `C₆`. -/
theorem c6_df_not_face : ¬ IsFaceOf (↑c6Facets : Set (Finset (Fin 6))) {3, 5} := by
  simp only [IsFaceOf, c6Facets, Finset.mem_coe]; decide

/-- **Fully unconditional Hochster realization for `C₆`.**  At the concrete hexagon `c6Facets`, the
algebraic `Tor₄` class and the topological `H̃¹(C₆)` are both nonzero with no remaining hypotheses. -/
theorem hochster_C6_realization (F : Type*) [Field F] :
    Nontrivial ((orientedEdges (cycleGraph 6) → F)
        ⧸ LinearMap.range (orientedCoboundary (cycleGraph 6) F))
      ∧ srHexTupleTorClass F c6Facets 0 1 2 3 4 5 ≠ 0 :=
  hochster_C6_both_nonzero F c6Facets
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by simp only [IsFaceOf, c6Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c6Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c6Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c6Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c6Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c6Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c6Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c6Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c6Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c6Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c6Facets, Finset.mem_coe]; decide)
    (by simp only [IsFaceOf, c6Facets, Finset.mem_coe]; decide)
    c6_df_not_face

end

end GaloisForLFunctions.HTGeometry

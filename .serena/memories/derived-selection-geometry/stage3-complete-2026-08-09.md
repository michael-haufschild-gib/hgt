# derived-selection-geometry: card fully formalized, promoted to stage 3

Card `universal-monodromy-cartier-torsion-fitting-energy-law.md` moved
`2-fully-proven/derived-selection-geometry/` → `3-formalized/derived-selection-geometry/`.
The stage-2 folder is now empty and removed. Ledger entry appended to
`docs/drafts/pipeline/_stage2-to-3-ledger.md`.

Lean home: `formal/GaloisForLFunctions/HTGeometry/DerivedSelectionGeometry/` (21 modules),
namespace `GaloisForLFunctions.HTGeometry.DerivedSelection`, all wired into
`GaloisForLFunctions.HTGeometry`. `#print axioms` on every card theorem: only
`propext, Classical.choice, Quot.sound`.

## Modules added in the closing session

| module | content |
|---|---|
| `TwoTermResolution` | replaces the old `CyclicResolution`; a short exact sequence with projective left terms IS a length-one projective resolution of its cokernel (`twoTermResolution`), plus `presShortComplex`/`presResolution` for modules |
| `DerivedFibre` | `Ext¹`/`Tor₁` from a two-term resolution: `extOneIso`, `torOneIso`, higher vanishing; helpers `homologyIsoQuotRange`, `homologyIsoKer`, `kerEquivOfComp` |
| `QuotientDerived` | regular-scalar case `N ⧸ tN`: `extOneSmulIso`, `torOneSmulIso`, `extCongrLeft`, `torCongrLeft`, `ker_smul_id_eq_top` |
| `IncompatDerived` | (4.2)/(4A.9): `extOneIncompatIso : Ext¹(Q,R) ≅ Q`, `torOneIncompatIso : Tor₁(Q,R⧸I) ≅ (R⧸I)²`, `extOneSrcIso`, `torOneSrcIso` |
| `NormalDefect` | (4.5): inclusion `B_min ⊗ R⧸I → U ⊗ R⧸I` is zero, yet `B_min ⊗ R⧸I ≅ (R⧸I)² ≅ Tor₁` |
| `DerivedPullback` | (8A.1)/(8A.2): `torOnePullbackIso ≅ Ann_A(u−1)`, `tensorPullbackEquiv ≅ A⧸(u−1)`, field points |
| `RiemannPullback` | `specializeHom`, `exists_riemann_specialization`, `riemann_pullback_nontrivial_iff` (Cor 8A.3) |
| `SupportSelection` | (8A.4) `endQuotEquiv : End_R(R⧸I) ≃+* R⧸I`; annihilator-closure lemmas; `subsingleton_localizedModule` |
| `NormalCone` | Thm 5.4: `gradedPiece`, `gradedMul`, `pieceEquiv`, `pieceEquiv_mul` (gr_I R ≅ (R⧸I)[e]); `inI_monodromyRefl_wall`, `inI_curvature`, `inI_energy`, `inI_pow_sub_one`, `inI_energyPow`, `inI_wall_ne_zero` |
| `SourceNormalEquation` | (7.3) `coordSum_srcDefect`; `srcBoundary_eq_antidiagonal_of_eq_one` |

## Which mathlib pieces made it work

- OLD `Ext` (root-level `Ext R C n : Cᵒᵖ ⥤ C ⥤ ModuleCat R`, NOT `CategoryTheory.Abelian.Ext`)
  plus `CategoryTheory.ProjectiveResolution.isoExt` and `ChainComplex.linearYonedaObj` — this is
  the ModuleCat-valued Ext, so the results are R-linear isos for free.
- `CategoryTheory.Tor'` (left-derives in the FIRST factor) + `ProjectiveResolution.isoLeftDerivedObj`.
- `ShortComplex.moduleCatHomologyIso` gives `homology ≅ ker g ⧸ range toCycles`; specialise with
  `Subsingleton X₃` (⇒ cokernel) or `Subsingleton X₁` (⇒ kernel).
- `HomologicalComplex.homologyIsoSc' K i j k` to name the three-term window.
- `quotTensorEquivQuotSMul`, `TensorProduct.prodLeft`, `LinearMap.coprodEquiv`,
  `LinearMap.ringLmapEquivSelf`, `ModuleCat.homLinearEquiv`, `Iso.toLinearEquiv`.
- mathlib has NO Fitting ideals, NO associated graded ring, NO `Module.Tor`.

## Traps hit this session

- Defeq-but-not-syntactic `ModuleCat` object mismatches (`(twoTermTensor Y).X 1` vs
  `F.obj ((twoTermCplx S).X 1)`) make `rw`/`simp` fail with "target not type-correct under
  instances transparency". Fix: introduce a named `def` with the *ascribed* type
  (e.g. `tensorIso₁ : (twoTermTensor Y).X 1 ≅ F.obj S.X₁`), then everything matches.
- Prefer a general helper stated over *generic* objects (`kerEquivOfComp`) so the defeq
  unification happens at the application site.
- `Subsingleton`/`IsZero` side conditions must be explicit arguments, not instances
  (`instance` declarations with non-inferable args are rejected).
- `Functor.map_id` resolves to the monad lemma; write `CategoryTheory.Functor.map_id`.
- `isUnit_of_mul_eq_one` does not exist here; build the `Units` structure by hand.
- `Submodule.span_singleton_neg` does not exist; prove `span{-x} = span{x}` by antisymmetry.
- `Ideal.Quotient.mk_surjective` + `← map_smul` fails (RingHom has no `MulActionHomClass`);
  use `p.mkQ_surjective` and `rfl` for `r • mk x = mk (r • x)`.
- `mk₂`/`LinearMap` obligations over subtype coercions: `push_cast; ring` after
  `rw [← inI_add]`, with a dedicated `inI_congr` congruence lemma.

## Concurrent-agent note

Another agent was writing `HTGeometry/Constitutive*` and `ConstraintRelativity/*` modules in the
same tree during this session; the four `owned module unreachable from umbrella` lint errors at
close belong to that work, not to this card.

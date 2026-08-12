# Global essential-duality formation producer program

- **ID:** ULF-EFM-2
- **Stage:** 1-in-progress
- **Type:** FIELD PRODUCER CONJECTURE / RH SELECTION GATE
- **Status:** [MECHANISM LEVEL] [SOURCE-PRE-ZERO REQUIRED] [FALSIFIABLE]
  [CONSUMER LEAN-PROVED] [PRODUCER OPEN] [NOT RH]
- **Certified consumer:** `HTGeometry.ConstitutiveEssentialFormationMechanics`

## 1. Question

Which law makes reciprocal source executions agree after quotienting only finite total formation
work?

This asks for a mechanism, not another receiver object.  The target is a formation law whose local
cells, interactions, work ideal, and reciprocal transport are all generated before any route or
zero is chosen.

## 2. Required mechanism

Let `S` be a source-state family with reciprocal involution `j`.  A global formation mechanism must
produce:

1. a countable interaction ledger `A_s:P->R` from source interventions;
2. an absolutely summable work ideal `L1(P)` fixed independently of `s`;
3. a reciprocal transport `J_s` preserving that ideal;
4. a prime interaction shadow `a_sigma`, with `sigma=2 Re(s)`;
5. three finite-work comparisons
   \[
   a_\sigma\sim_{\rm ess}A_s,
   \qquad
   A_s\sim_{\rm ess}J_sA_{j(s)},
   \qquad
   J_sA_{j(s)}\sim_{\rm ess}a_{2-\sigma}.
   \tag{GED.1}
   \]

The Lean-certified global bridge consumer composes `(GED.1)` and forces `sigma=1`.

## 3. Formation laws that must be constructed

### Law I — endogenous generation

`A_s` must be generated from a source intervention grammar.  It cannot be declared from a target
zero, route endpoint, desired kernel, or chosen positive form.

### Law II — coefficient-faithful reconstruction

The full interaction packet of `A_s`, with its source marks, must reconstruct the generated source
state up to the declared work ideal.  Otherwise `A_s=0` gives a vacuous bridge.

### Law III — passive work conservation

Every allowed finite-complexity observer must split total work into visible work plus nonnegative
hidden work.  Serial observations add hidden bands.  This fixes which errors count as finite work
instead of choosing the ideal after seeing the answer.

### Law IV — cofinal formation properness

Formation is admitted precisely when its total interaction work is summable.  Every fixed finite
observer may remain regular while an escaping formation moves all work to increasing complexity.

### Law V — reciprocal finite-work conservation

Source duality may redistribute formation among local cells, interaction degrees, and an
archimedean/global port, but its total mismatch must lie in the predeclared summable work ideal.
This is the new producer theorem.

### Law VI — executor independence

Route realizations may turn the same ledger into Hilbert energy, QFI, recurrence cost, determinant
depth, differential prolongation, or boundary flux.  Selection is performed before those
executions.  No individual executor is allowed to define reciprocal conservation.

## 4. Proof strategy

1. **Generate:** start from the full pre-zero arithmetic source and construct the local activation
   and higher interaction ledger under its native interventions.
2. **Reconstruct:** prove a joint reconstruction theorem for the marked ledger, preventing the
   zero-ledger and scalar-summary countermodels.
3. **Conserve:** derive reciprocal transport from the global source symmetry and prove a cutoff
   conservation identity in which all interior interaction work cancels and only a controlled
   boundary remainder remains.
4. **Globalize:** prove those boundary remainders are Cauchy in total variation, yielding the three
   summable differences `(GED.1)`.
5. **Select:** invoke `essentialFormationSelection_of_sourceBridge`; only after that translate
   `sigma=1` to `Re(s)=1/2` for spectral states.

The critical research step is 3: find the conservation law whose finite-aperture boundary terms
compose telescopically.  The correct source may be a signed interaction current, a determinant-line
balance, an entropy-production identity, or a higher reciprocity law.  Curvature language is not
assumed.

## 5. Mandatory hostile tests

Reject a candidate producer if any of the following occurs:

1. the work ideal depends on `s`, a zero, or the chosen route;
2. the comparison exists only after scalar contraction and loses coefficient faithfulness;
3. finite apertures match but the total boundary remainder is not summable;
4. reciprocal transport is a moving-ideal gauge that makes every state tautologically horizontal;
5. the source formation is identically zero or admits arbitrary compensators;
6. duality preserves only the coarse tight/escaping label but provides no summable comparison;
7. the construction uses the critical line to normalize its coefficients.

## 6. Predictions across organs

If the mechanism is correct, route executors must obey:

1. finite/local repairs can move coefficients but cannot change admitted versus escaping phase;
2. nontrivial selection must be cofinal—no fixed aperture can prove it;
3. hypertranscendental growth appears as unbounded interaction/prolongation formation, not as
   generic topological noncompactness;
4. recurrence may stay compact after projection while lifted formation work escapes;
5. positivity supplies a work ledger, while phase/orientation survives only in marked interaction
   coefficients or duality transport;
6. every successful route must either realize `(GED.1)` or expose a nonsummable boundary term that
   precisely explains its obstruction.

These are corpus-wide tests.  They do not privilege Route R, L, G, O, or any other endpoint.

## 7. Acceptance gate

- [x] exact essential quotient and selection consumer proved on paper and in Lean
- [x] all-degree formation, reconstruction, passive work, and QFI conservation seed constructed
- [x] prime formation/properness wall and reciprocal fixed phase proved in Lean
- [ ] source-generated global ledger independent of route execution
- [ ] joint coefficient-faithful reconstruction modulo the fixed work ideal
- [ ] finite-aperture reciprocal conservation identity
- [ ] summable cofinal boundary theorem establishing `(GED.1)`
- [ ] pre-zero application to every relevant spectral state
- [ ] RH consequence

## 8. Global properness mechanism now closed on paper

The operator-level properness question is no longer vague. The Stage-2 theorem

`../formation-laplacian-properness-mechanics/compact-formation-semifredholm-transduction-joint-recovery-and-carrier-defect-bifurcation-law.md`

proves the exact fusion law. If the coefficient-faithful local source channel `A` is compact and
the cofinal boundary transducer is `R`, then `(A,R)` is bounded below exactly when:

1. `R` has closed range;
2. `ker R` is finite-dimensional;
3. `A` is injective on `ker R`.

It also constructs the joint recovery map

```text
L(y,z)=S z + J(y-A S z)
```

and proves carrier--defect bifurcation: structural `R` must remain present, while a separate
relative channel `delta R` may vanish in the compact quotient at selection. FE and common-recovery
packet lifts preserve all formation margins and information exactly.

This closes **Law IV as an abstract formation theorem** and sharpens Law V. Reciprocal finite-work
conservation cannot be implemented by making the sole carrier vanish. The producer must construct:

```text
one retained semi-Fredholm transducer
  + one FE-covariant relative defect on that carrier.
```

The remaining source problem is not “find a noncompact archimedean operator.” The corpus already
has those. Nor is pointwise Calkin frame coverage sufficient. The Stage-2 theorem

`../formation-laplacian-properness-mechanics/formation-quotient-interchange-tight-recovery-and-residual-coverage-law.md`

proves that countable formation does not commute with quotienting by local compact operators:
rank-one residuals can assemble into a noncompact projection with infinite kernel, and finite-rank
local leakage can make the global analysis map non-Bessel. The exact source gate is therefore:

1. construct the formed source analysis operator;
2. prove its directed Gram residual converges to a bounded operator `G`;
3. prove `2 I + G` has closed range and finite-dimensional kernel (the stronger sufficient bound
   is `||G|| < 2`);
4. prove the compact coefficient packet separates that kernel;
5. only then derive the reciprocal defect comparison `(GED.1)` without fitting it from a Xi fibre.

Functional equation conjugates this residual and its decoder, hence is information-neutral. It
cannot improve the global lower frame margin.

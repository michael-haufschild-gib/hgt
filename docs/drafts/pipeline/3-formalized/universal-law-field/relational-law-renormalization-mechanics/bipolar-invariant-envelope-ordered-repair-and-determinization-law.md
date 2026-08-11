# Bipolar invariant envelope, ordered repair, and determinization law

- **ID:** ULF-RLR-2
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** ULF-LSM-2 least executable repair + ULF-OPM-5 greatest future reporter envelope +
  ULF-RLR-1 observer-induced relational execution
- **Statement:** Every observer equivalence has canonical finest and coarsest law-executable
  repairs; their opposite compositions absorb rather than commute, and they commute exactly when
  no repair is needed.
- **Status:** [PROVED HERE] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [BIPOLAR REPAIR] [ORDERED HISTORY] [DETERMINIZATION] [LEAN-PROVED]
  [AXIOM-AUDITED] [UMBRELLA-BUILT]
  [AXIOM-AUDITED] [NOT RH]

## Goal

Classify, without choosing a route or target theorem, the two universal ways to repair a
deterministic source law that becomes nondeterministic under observation:

1. remember more source distinctions; or
2. forget more observed distinctions.

The load-bearing result is not existence of two closure operators.  It is their exact ordered
exchange law: applying one repair makes the other inert, so opposite repair schedules retain
maximal history unless the original observer already admits every source law.

## 1. Setup

Let `X` be a set, let `F` be a family of unary source laws `f:X->X`, and let `E` be an observer
equivalence relation on `X`.  A relation is **executable** when it is an equivalence preserved by
every `f` in `F`.

Define the least executable coarsening

\[
 C_F(E)=\bigcap\{R:E\subseteq R,\ R\text{ executable}\}.
 \tag{BR.1}
\]

For a finite word `w=(f_1,...,f_n)` in `F`, write `w x=f_n...f_1x`, with the empty word acting as
the identity.  Define the greatest executable refinement

\[
 x\,I_F(E)\,y
 \quad\Longleftrightarrow\quad
 (wx)\,E\,(wy)\text{ for every finite word }w\text{ in }F.
 \tag{BR.2}
\]

`C_F` repairs execution by erasing distinctions.  `I_F` repairs execution by retracting unstable
identifications.

## 2. Bipolar invariant-envelope theorem

### Theorem 2.1 -- extremal repairs and adjunction laws

For every equivalence `E`:

1. `C_F(E)` and `I_F(E)` are executable equivalence relations;
2. they sandwich the original observer:

   \[
   \boxed{I_F(E)\subseteq E\subseteq C_F(E);}
   \tag{BR.3}
   \]

3. for every executable equivalence `R`,

   \[
   \boxed{C_F(E)\subseteq R\iff E\subseteq R,}
   \qquad
   \boxed{R\subseteq I_F(E)\iff R\subseteq E;}
   \tag{BR.4}
   \]

4. `C_F(E)=E` iff `I_F(E)=E` iff every law in `F` preserves `E`.

Thus executable observers form both a reflective and coreflective sector of the inclusion-ordered
observer lattice: `C_F` is the least executable world above `E`, while `I_F` is the greatest
executable world below it.

### Proof

The properties of `C_F` follow by intersecting all executable equivalences containing `E`; the
universal relation ensures the family is nonempty.  Intersections preserve equivalence and
`F`-invariance, proving executability, extensivity, and the first equivalence in `(BR.4)`.

For `I_F`, equivalence holds word by word because `E` is an equivalence.  The empty word proves
`I_F(E) subset E`.  If `f in F` and `x I_F(E) y`, then testing `fx,fy` by a word `w` is the same as
testing `x,y` by the word obtained by prefixing `f`; hence every `f` preserves `I_F(E)`.

Let `R` be executable and contained in `E`.  If `xRy`, repeated preservation along any word gives
`(wx)R(wy)`, hence `(wx)E(wy)`.  Therefore `R subset I_F(E)`.  The converse follows from
`I_F(E) subset E`, proving the second equivalence in `(BR.4)`.

If `E` is executable, both extremal properties force `C_F(E)=E=I_F(E)`.  Conversely either equality
identifies `E` with an executable relation.  QED.

## 3. Ordered-repair absorption theorem

### Theorem 3.1

For every observer equivalence `E`,

\[
\boxed{C_F(I_F(E))=I_F(E),\qquad I_F(C_F(E))=C_F(E).}
\tag{BR.5}
\]

Consequently the following are equivalent:

1. the two opposite repair schedules agree at `E`;
2. `C_F(I_F(E))=I_F(C_F(E))`;
3. `I_F(E)=C_F(E)`;
4. `I_F(E)=E=C_F(E)`;
5. every source law in `F` preserves `E`.

### Proof

Both `I_F(E)` and `C_F(E)` are executable by Theorem 2.1.  The fixed-point clause of that theorem
therefore gives the two identities in `(BR.5)`.  Hence equality of the two schedules is exactly
`I_F(E)=C_F(E)`.  The sandwich `(BR.3)` then forces both to equal `E`, and Theorem 2.1 identifies
this with executability.  The converse is immediate.  QED.

### Mechanism meaning

This is stronger than generic failure of commuting closures.  The two repairs are oppositely
absorbing:

```text
remember first, then forget  = remember-repair endpoint
forget first, then remember  = forget-repair endpoint
```

Once one extremal repair has made the laws executable, the opposite repair has no legal work left
to do.  Repair order is therefore a retained mathematical history, and it disappears exactly in
the already-executable chamber.

## 4. Exact relation determinization

Let `q_E:X->X/E` be the quotient observer.  For `f:X->X`, let

\[
 b\,\mathcal R_E(f)\,c
 \quad\Longleftrightarrow\quad
 \exists x,\ q_E(x)=b\text{ and }q_E(fx)=c.
 \tag{BR.6}
\]

### Corollary 4.1

For every `f in F`:

1. `R_E(f)` is right-unique iff `f` preserves `E`;
2. quotienting by `C_F(E)` gives the least coarsening of `E` on which every `R(f)` is a function;
3. quotienting by `I_F(E)` gives the greatest refinement of `E` on which every `R(f)` is a
   function;
4. the two universal determinizations agree iff the original observed laws were already
   deterministic.

### Proof

Right-uniqueness is exactly kernel preservation: two representatives with the same `E`-class must
have images in the same `E`-class.  The extremal claims are `(BR.4)`, and agreement is Theorem 3.1.
QED.

## 5. Sharp three-state cell

Let `X={a,b,c}`.  Define

\[
 f(a)=a,\qquad f(b)=c,\qquad f(c)=c,
 \tag{BR.7}
\]

and let `E` have classes `{a,b}` and `{c}`.

Then `f` does not preserve `E`: `a E b`, but `f(a)=a` and `f(b)=c` are not `E`-related.  Moreover,

\[
\boxed{I_{\{f\}}(E)=\Delta_X,\qquad C_{\{f\}}(E)=X\times X.}
\tag{BR.8}

Indeed, the one-step future separates `a` from `b`, while `c` was already separated from their
class, so the invariant refinement is equality.  For the coarsening, `a E b` and preservation force
`a C_F(E)c`; transitivity then joins all three states.

Thus

\[
C_F(I_F(E))=\Delta_X,
\qquad
I_F(C_F(E))=X\times X.
\tag{BR.9}

The observed class `{a,b}` has two possible outputs under `R_E(f)`, while both extremal repairs
restore determinism by opposite information changes.  This proves the exchange failure can span the
entire observer lattice even in the smallest nontrivial cell.

## 6. Consequences for the universal-law programme

1. **Nondeterminism is a repair fork, not a scalar defect.**  The canonical exact responses point
   in opposite information directions.
2. **Forgetting and remembering are not gauges of one endpoint.**  Their schedules land at opposite
   invariant envelopes unless the original law descended.
3. **Adaptive future testing is the fine repair.**  `I_F(E)` is exactly agreement under every
   finite future experiment generated by the laws.
4. **Law saturation is the coarse repair.**  `C_F(E)` is exactly the mandatory identification
   closure required to execute the laws on a quotient.
5. **Observer-induced relations are the unrepaired middle phase.**  They retain every branch rather
   than selecting one extremal determinization.
6. **The next field law is topological/admissible exchange.**  Completion or positivity may forbid
   one or both extremal repairs; that is additional mathematics and cannot be inferred from this
   set-level theorem.

## 7. Parent boundary and sharp scope

The ingredients are classical invariant-equivalence closure, future/Nerode equivalence, adjunction
to a full fixed-point subposet, and relational quotient semantics.  No priority claim is made.  The
new field use is the exact coupling and ordered-repair interpretation.

This theorem does not supply:

- a source selector between the fine and coarse repair;
- topology, completion, positivity, cost, or analytic admission;
- partial, unbounded, or higher-arity laws;
- recursive generation of new laws from a failed repair;
- a route endpoint or RH statement.

## 8. Lean target

Formalize the exact paper theorem as

`GaloisForLFunctions.HTGeometry.ConstitutiveBipolarObserverRepair`.

Required capstones:

1. generic interior equivalence, preservation, containment, and greatestness;
2. closure/interior fixed-point equivalence;
3. both absorption identities;
4. exchange iff original executability;
5. the exact three-state equality/universal cell; and
6. one unconditional bundled theorem.

No numerical decision procedure, project axiom, premise, `sorry`, `admit`, `opaque`, or `unsafe`
declaration is permitted.

## Gates

- [x] 0 -> 1: source-pure mechanism, exact attack, no route data
- [x] 1 -> 2: dependency-closed paper proof and sharp countercell
- [x] 2 -> 3: Lean theorem, foreground check, owned-module reachability, axiom audit, final umbrella build
- [ ] 3 -> 4: publication-ready theorem paper

## Log

- 2026-08-10 -- least coarsening and greatest future refinement combined into one exact bipolar
  repair calculus; ordered absorption and the maximal three-state cell proved on paper.
- 2026-08-10 -- Lean module passed direct elaboration and a 2,999-job leaf build.  The universal-law
  umbrella passed with 11,578 jobs.  Axiom prints report only `propext` and `Quot.sound`.  Full-tree
  lint reached this module but remains red on two unrelated concurrent unwired modules,
  `RHTower.DeningerPrimeLogHeightForms` and
  `HTGeometry.ConstraintRelativity.CongruenceOrderTraceDual`; no lint defect belongs to this card.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.

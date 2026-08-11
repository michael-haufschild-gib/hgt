# Weak-star compact calibration globalization and cofinal escape law

- **ID:** `ulf-grm-weak-star-calibration-globalization`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / NO-GO WITH POSITIVE SURVIVOR
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [CLASSICAL COMPACTNESS]`
  `[ROUTE-INDEPENDENT] [LEAN-CERTIFIED] [NOT RH]`

## 1. Setup

Let `V` be a real seminormed vector space and let `(v_i)_(i in I)` be an arbitrary family. Write
`V*` for its continuous dual and

\[
 B^*=\{\varphi\in V^*:\|\varphi\|\le1\}.
\]

For `v in V`, define its norming face

\[
 N(v)=\{\varphi\in B^*: \varphi(v)=\|v\|\}.
 \tag{WCG.1}
\]

## 2. Globalization theorem

### Theorem 2.1 — finite calibration globalizes

The following are equivalent:

1. there exists `phi in B*` with `phi(v_i)=||v_i||` for every `i in I`;
2. for every finite `F subset I`, there exists `phi_F in B*` with
   `phi_F(v_i)=||v_i||` for every `i in F`.

Equivalently, if no global common normer exists, some finite packet already has no common normer.

### Proof

Equip `V*` with its weak-star topology. Banach--Alaoglu makes `B*` compact. Evaluation at any fixed
`v` is weak-star continuous, so `N(v)` is closed in `B*`. Hahn--Banach makes every individual
`N(v)` nonempty, including `v=0`.

Assumption 2 says the closed family `(N(v_i))` has the finite-intersection property inside compact
`B*`. Hence its total intersection is nonempty. Any element of that intersection is the required
global normer. The converse is restriction to a finite set. Negating the equivalence gives the
finite-witness statement. QED.

## 3. Fusion consequence

For every finite packet `F`, Norming-Face Fusion Mechanics proves

\[
 \sum_{i\in F}\|v_i\|-\left\|\sum_{i\in F}v_i\right\|=0
 \quad\Longleftrightarrow\quad
 \bigcap_{i\in F}N(v_i)\ne\varnothing.
 \tag{WCG.2}
\]

Theorem 2.1 therefore gives the infinite calibration law

\[
 \boxed{
 \text{every finite fusion defect vanishes}
 \Longleftrightarrow
 \text{one functional norms the entire family}.}
 \tag{WCG.3}
\]

No new cofinal incompatibility can be hidden inside one fixed weak-star compact calibration
doctrine.

## 4. Exact escape classification

Consider any proposed global obstruction represented by constraints `C_i` in one calibrator space
`K`. If:

1. `K` is compact;
2. every `C_i` is closed in `K`;
3. every finite intersection is nonempty;

then the total intersection is nonempty. Thus any purported obstruction invisible on every finite
packet must violate at least one typed premise:

- the calibrator space is noncompact or loses equicontinuity;
- some admission constraint is not closed;
- a finite packet already fails;
- calibrator doctrine changes with aperture/intervention and has no common compact embedding.

In source-execution problems a fifth, independent possibility occurs: a common calibrator exists,
but straight-path admission radii collapse to zero. Norming faces do not encode that radius;
Generative Response Mechanics retains it separately through `kappa` and `rho`.

This is a conditional classification of escape from the fixed compact model, not a claim that every
possible mathematical obstruction is topological.

## 5. Frontier prediction

Any live route claiming a genuinely cofinal failure after every finite calibration succeeds must
exhibit an explicit escape datum:

1. singular/nonclosed source domain (`C1,L,R,CCM-FU`);
2. loss of compactness/equicontinuity or reporter closure (`D2,E,T`);
3. changing adaptive face/calibrator doctrine (`G,U`);
4. coercive radius collapse (`O`);
5. unattained positive carrier (`P,Q`).

Merely increasing vector dimension, arity, prime count, or number of fixed norming faces cannot
produce such an obstruction.

## 6. Hostile boundaries

1. **Weak-star compactness is optional.** False. In a noncompact calibrator space, closed sets may
   have the finite-intersection property and empty total intersection.
2. **Closedness is optional.** False. In compact `[0,1]`, the nonclosed sets `(0,1/n)` have every
   finite intersection nonempty and empty total intersection.
3. **Finite-dimensional Helly is required.** False. Banach--Alaoglu replaces dimension bounds;
   witness cardinality is finite but not uniformly bounded.
4. **Global common normer gives executable source history.** False. It supplies calibration only;
   cofinal straight-path admission requires a separate positive lower radius.
5. **This is the universal field.** False. It is an exact no-go eliminating fixed-calibrator
   geometry as the full field and forcing doctrine mutation or admission dynamics.
6. **This proves RH.** False. It only restricts the type of a viable RH selector.

## 7. Lean certification

Formalized without new axioms in
`GaloisForLFunctions.HTGeometry.CompactCalibrationGlobalization`:

- weak-star norming face;
- closedness and nonemptiness of each face;
- finite-intersection globalization via `WeakDual.isCompact_closedBall`;
- common-normer equivalence;
- finite witness for failure.

The module is wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`. The final foreground
umbrella build passes with 11,615 jobs. Axiom prints for globalization, equivalence, and finite
witness report only `propext`, `Classical.choice`, and `Quot.sound`. The existing Norming-Face
Fusion Lean module supplies finite defect/common-normer laws separately.

## 8. Significance

Parent ingredients are classical Banach--Alaoglu, Hahn--Banach, and compact finite-intersection
theory. No novelty claim is made. The field-level use is sharp: it falsifies an entire proposed
explanation of the frontier and identifies exactly why the higher mechanism must include changing
admission doctrine and cofinal execution radius.

## Log

- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.

# Conservative carrier genesis, bipolar repair base change, and fresh-return defect law

- **ID:** ULF-ERM-1
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / ROUTE-INDEPENDENT MECHANISM LAW
- **Statement:** Under a two-sided conservative extension of unary law language, future-retaining
  repair obeys exact carrier base change, whereas future-forgetting repair is only lax; a compatible
  semantic retraction restores exactness, and a three-state cell proves strictness without changing
  any old law execution.
- **Status:** [PROVED HERE] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT] [LEAN-CERTIFIED]
  [CLASSICAL BASE-CHANGE PARENTS] [NOT RH]

## 1. Setup

Let `j : X -> Y` be injective.  Let `F` be a family of unary laws on `X`, and `G` a family
of unary laws on `Y`.  Call `G` a **two-sided conservative extension** of `F` along `j` when:

1. every old law has a lift:

   \[
   \forall f\in F\ \exists g\in G,\qquad g j=j f;
   \tag{ERM1.1}
   \]

2. every new law restricts to an old law:

   \[
   \forall g\in G\ \exists f\in F,\qquad g j=j f.
   \tag{ERM1.2}
   \]

Let `E_X` and `E_Y` be equivalence relations with exact old-carrier restriction

\[
 E_X(x,x')\quad\Longleftrightarrow\quad E_Y(jx,jx').
 \tag{ERM1.3}
\]

Write `I_F(E)` for the greatest equivalence contained in `E` and preserved by every finite
`F`-word.  Write `C_F(E)` for the least equivalence containing `E` and preserved by every law in
`F`.  These are the future-retaining and future-forgetting repairs of ULF-RLR-2.

## 2. Theorem

### Theorem 2.1 -- conservative-genesis repair asymmetry

Under `(ERM1.1)`--`(ERM1.3)`:

1. **Exact future-retaining base change.** For all `x,x' in X`,

   \[
   I_G(E_Y)(jx,jx')\quad\Longleftrightarrow\quad I_F(E_X)(x,x').
   \tag{ERM1.4}
   \]

2. **Lax future-forgetting base change.** For all `x,x' in X`,

   \[
   C_F(E_X)(x,x')\quad\Longrightarrow\quad C_G(E_Y)(jx,jx').
   \tag{ERM1.5}
   \]

3. **Retraction exactness chamber.** Suppose there is `r : Y -> X` such that

   \[
   rj=\mathrm{id}_X,
   \tag{ERM1.6}
   \]

   \[
   E_Y(y,y')\Longrightarrow E_X(ry,ry'),
   \tag{ERM1.7}
   \]

   and every `g in G` descends through `r` to some `f in F`:

   \[
   \forall g\in G\ \exists f\in F,\qquad rg=fr.
   \tag{ERM1.8}
   \]

   Then future-forgetting repair is also exact:

   \[
   C_G(E_Y)(jx,jx')\quad\Longleftrightarrow\quad C_F(E_X)(x,x').
   \tag{ERM1.9}
   \]

The relation

\[
 \Delta_C(x,x'):
 C_G(E_Y)(jx,jx')\ \wedge\ \neg C_F(E_X)(x,x')
 \tag{ERM1.10}
\]

is the **fresh-return defect**.  It measures identifications among old states made possible only
after passing through the enlarged carrier.  Clause 3 says a compatible semantic retraction
annihilates it.

## 3. Proof

### 3.1 Word transport

By induction on word length, `(ERM1.2)` implies that every finite `G`-word `w` restricts along `j`
to an `F`-word `v`:

\[
 wj=jv.
 \tag{ERM1.11}
\]

Conversely, repeated use of `(ERM1.1)` lifts every finite `F`-word to a `G`-word with the same
intertwining identity.  The order convention is irrelevant provided both word evaluators use the
same convention.

### 3.2 Proof of exact future-retaining base change

Assume `I_G(E_Y)(jx,jx')`.  Given any admitted `F`-word, lift it to a `G`-word by `(ERM1.1)` and
`(ERM1.11)`.  The `G`-interior gives `E_Y(jvx,jvx')`; `(ERM1.3)` gives `E_X(vx,vx')`.  Hence
`I_F(E_X)(x,x')`.

Conversely assume `I_F(E_X)(x,x')`.  Given any admitted `G`-word, restrict it to an `F`-word by
`(ERM1.2)` and `(ERM1.11)`.  The `F`-interior and `(ERM1.3)` give the required `E_Y` relation.
This proves `(ERM1.4)`.

### 3.3 Proof of lax future-forgetting base change

Define on `X`

\[
 R(x,x'):\Longleftrightarrow C_G(E_Y)(jx,jx').
 \tag{ERM1.12}
\]

It is an equivalence.  It contains `E_X` by `(ERM1.3)` and extensivity of `C_G`.  For every
`f in F`, choose a lift `g in G`.  Preservation of `C_G` by `g` and `gj=jf` show that `R` is
preserved by `f`.  By minimality of `C_F(E_X)`,

\[
 C_F(E_X)\subseteq R,
\]

which is `(ERM1.5)`.

### 3.4 Proof of the retraction chamber

Define on `Y`

\[
 S(y,y'):\Longleftrightarrow C_F(E_X)(ry,ry').
 \tag{ERM1.13}
\]

It is an equivalence.  Clause `(ERM1.7)` and extensivity of `C_F` show that it contains `E_Y`.
Given `g in G`, choose `f in F` using `(ERM1.8)`.  Preservation of `C_F` by `f` shows that `S`
is preserved by `g`.  Minimality of `C_G(E_Y)` gives `C_G(E_Y) subseteq S`.  Evaluating at
`jx,jx'` and using `rj=id` proves the reverse implication in `(ERM1.9)`; `(ERM1.5)` supplies the
forward implication.  This proves the theorem.

## 4. Sharp three-state strict cell

Let

\[
 X=\{a,b\},\qquad Y=\{a,b,c\},\qquad j(a)=a,\ j(b)=b.
\]

Take the old law family `F={id_X}`.  Let `G={g}` with

\[
 g(a)=a,\qquad g(b)=b,\qquad g(c)=b.
 \tag{ERM1.14}
\]

Thus `g` restricts to `id_X`; every old execution is unchanged.  Let `E_X` be equality, and let
`E_Y` have classes `{a,c}` and `{b}`.  Its restriction to `X` is equality.

The old repairs are both equality.  The new future-retaining repair restricts to equality by
Theorem 2.1.  But `E_Y(a,c)` and `G`-invariance force

\[
 C_G(E_Y)(g(a),g(c))=C_G(E_Y)(a,b).
\]

Hence the new future-forgetting repair identifies the two old states and its restriction is the
universal relation.  Therefore `(ERM1.5)` is strict.

No retraction satisfying `(ERM1.6)`--`(ERM1.8)` exists.  Relation preservation would force
`r(c)=a` from `E_Y(a,c)`, while law compatibility would force
`r(g(c))=r(b)=b=id_X(r(c))=a`, a contradiction.

This cell is minimal in fresh carrier size: strict change of old-carrier repair requires at least
two old states and at least one state outside their image.

## 5. Mechanism interpretation

Conservative syntax growth is not neutral.  It has a directed effect on the two extremal repairs:

- **remembering is cartesian:** every future test on old states remains an old future test, so the
  greatest stable refinement pulls back exactly;
- **forgetting is op-lax:** equivalence generation may travel through fresh states and return to
  the old carrier, producing new old-state identifications;
- **semantic retraction is a no-defect certificate:** if every new state, relation, and law can be
  consistently interpreted back in the old calculus, no fresh-return defect survives.

This is not a selector between remembering and forgetting.  It predicts which direction can gain
history when a source-generated challenge expands the carrier.

## 6. Hostile conjecture loops

1. **Both repairs satisfy exact Beck--Chevalley under conservative law restriction.** Falsified by
   the three-state cell.  Survivor: exact fine / lax coarse asymmetry.
2. **Changing old execution is necessary to change old repair.** Falsified: `g|_X=id_X` while the
   coarse repair on `X` changes from equality to universal.  Survivor: fresh-mediated return paths
   are sufficient.
3. **Any set-theoretic retraction removes the defect.** Falsified in principle: the retraction must
   preserve both the base equivalence and law action.  Survivor: `(ERM1.6)`--`(ERM1.8)`.
4. **The defect is an intrinsic scalar curvature.** Rejected.  It is a relation-valued base-change
   failure and may have many incomparable pairs.
5. **This proves universal law genesis.** Rejected.  The theorem assumes a supplied conservative
   carrier extension.  ULF-DJG-1 supplies one Boolean source-normal extension; general production
   remains ERM-A.

## 7. Parent boundary and scope

The proof is elementary invariant-equivalence calculus and a Beck--Chevalley-style base-change
comparison.  Indexed closure operators, fibred doctrines, and categorical logic are established
parents.  The theorem's role is the exact coupling of the corpus's independently certified
source-normal carrier genesis and bipolar repair mechanisms.  No external novelty claim is made.

No topology, probability, positivity, admission, higher arity, cofinal limit, RH endpoint, or route
specialization is used.  Those are later tests of the mechanism.

## 8. Lean certification

Formalized in
`formal/GaloisForLFunctions/HTGeometry/ConstitutiveCarrierGenesisRepair.lean`:

1. word restriction and lifting;
2. exact interior pullback;
3. lax closure pullback;
4. compatible-retraction closure exactness;
5. the unconditional three-state strict cell;
6. one capstone theorem bundling the mechanism.

The module is wired into
`formal/GaloisForLFunctions/HTGeometry/UniversalLawField.lean`. Direct foreground elaboration,
the 3,000-job leaf build, the 11,580-job final umbrella build, and formal lint all pass. Axiom prints
report only `propext` and `Quot.sound`; no project axiom or unproved premise enters the capstone.
The companion Stage-3 certification card records declaration-level coverage.

## Log

- 2026-08-10 -- theorem frozen from the post-frontier interaction of ULF-DJG-1 and ULF-RLR-2;
  complete paper proof and strict cell recorded.
- 2026-08-10 -- Lean certification completed; direct, leaf, umbrella, lint, and axiom audits pass.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.

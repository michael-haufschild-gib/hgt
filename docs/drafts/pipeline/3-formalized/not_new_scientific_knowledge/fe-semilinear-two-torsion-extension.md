# A genuine FE-semilinear two-torsion extension and its Witt activation

- **ID:** fe-semilinear-two-torsion-extension
- **Stage:** 3-formalized
- **Type:** THEOREM / NEW NATIVE OBJECT / LOCAL WITT BRIDGE, `[PROVED HERE]`
- **Date:** 2026-07-10
- **Parents:** `fe-semilinear-upper-shear-exhaustion.md`,
  `weld-krein-rate-blindness.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/FESemilinearTwoTorsionExtension.lean`
- **Statement:** `[PROVED]` The two-torsion family `[[X^a,f],[0,X^b]]` has an exact FE parity
  equation.  For `b=1`, FE requires `f` to be even and row splitting is equivalent to `f(0)=0`.
  Thus the constant residue is the exact extension invariant.  The unit class
  `[[X^m,1],[0,X]]` is FE-semilinear, has determinant `X^(m+1)`, and for `m>0` is not any two-sided
  polynomial transform of `diag(X^m,X)`.  Mapping the constant residue to the canonical FE-weld
  Gram makes row nonsplitting equivalent to local Krein negativity.  Local-coordinate reflection
  preserves the residue, splitting class, and Gram; the unit extension remains equivariant and
  nonsplit.  Hence this genuine extension is still reflection-orbit-blind and is not by itself an
  RH detector.

## 1. Two torsion lanes change the FE parity equation

Let

`A_(a,b,f)=[[X^a,f(X)],[0,X^b]]`.

Keep target coefficient parity `R_t=diag(-1,1)`.  Since FE sends `X` to `-X`, the diagonal equations
force source parity

`R_s(a,b)=diag(-(-1)^a,(-1)^b)`.                                 (1)

Both `R_t` and `R_s`, combined with `X -> -X`, are involutions.  The remaining upper-right equation
is

`-f(-X)=(-1)^b f(X)`.                                            (2)

Equation (2) is necessary and sufficient for FE semilinearity.  In particular:

- `b` even forces `f` odd;
- `b` odd forces `f` even.

The unit-lane case had `b=0`, so a constant shear was forbidden.  The smallest second torsion lane
has `b=1`, where the constant class is allowed.

## 2. Exact order-one extension criterion

Fix `b=1`.  Equation (2) becomes

`f(-X)=f(X)`: `f` is even.                                       (3)

The presentation is a target-row transform of the split matrix `diag(X^a,X)` exactly when

`X | f`.                                                          (4)

Indeed, if `f=Xg`, then `[[1,g],[0,1]] diag(X^a,X)=A_(a,1,f)`.  Conversely, the upper-right entry of
any equality `A_(a,1,f)=U diag(X^a,X)` writes `f` as a multiple of `X`.

Over `Q[X]`, (4) is equivalent to `f(0)=0`.  Therefore

> `A_(a,1,f)` is FE-semilinear and row-nonsplit
> iff `f` is even and `f(0) != 0`.                                (5)

The extension obstruction is not an arbitrary presentation coordinate: it is the constant residue
of the FE-even polynomial modulo the row-gauge ideal `(X)`.

## 3. Canonical unit extension

Set

`E_m=A_(m,1,1)=[[X^m,1],[0,X]]`.                                 (6)

By (3), `E_m` is FE-semilinear.  Its determinant is

`det(E_m)=X^(m+1)`.                                               (7)

For `m>0`, every entry of `diag(X^m,X)` vanishes at `X=0`; consequently every entry of

`U diag(X^m,X) V`                                                (8)

vanishes there for arbitrary polynomial matrices `U,V`.  But the `(0,1)` entry of `E_m` is `1`.
Hence `E_m` is not of the form (8), without even assuming that `U,V` are invertible or FE-compatible.

This is a genuine two-torsion extension, not a coordinate shear of the old torsion-plus-unit object.

## 4. Extension residue to FE-Witt block

For an order-one two-torsion extension define

`H_f=[[0,f(0)],[f(0),0]]`.                                       (9)

This is the canonical FE-weld Gram at the constant extension residue.  The rate-blindness theorem
gives

`KreinNonneg(H_f) <-> f(0)=0`.                                   (10)

Combining (4) and (10),

`A_(a,1,f) row-splits <-> KreinNonneg(H_f)`,                      (11)

`A_(a,1,f) is row-nonsplit <-> H_f has a negative direction`.    (12)

Thus local Witt activation is no longer an external coefficient or a prime-source count.  It is
read from the exact gauge-invariant residue of a genuine FE-semilinear extension.

## 5. Joint-reflection attack: the genuine extension is still position-blind

For a center on the critical line, the existing fixed-germ identity is

`lineReflection(s)-rho = -conj(s-rho)`.

Over the rational polynomial model, Schwarz fixes coefficients, so the induced action on the formal
local coordinate is the same `X -> -X` reflection already present in the FE-semilinear equations.
The constant extension residue satisfies

`(f(-X))(0)=f(0)`.                                                (13)

Consequently:

`A_(a,1,f(-X)) row-splits <-> A_(a,1,f) row-splits`,              (14)

`H_(f(-X))=H_f`.                                                  (15)

For the unit class `f=1`, reflection fixes the presentation; for every `m>0` it is simultaneously
FE-semilinear and genuinely two-sided nonsplit.  Thus fixed-germ descent does not annihilate the
extension class.  Free two-point reflection orbits and critical-line fixed germs can carry the same
nonzero residue and the same negative Witt block.

This kills the hoped automatic RH mechanism: neither genuine nonsplitting nor its local Witt image
sees whether the base point is fixed by critical-line reflection.

## Attack and scope

- `[PROVED NATIVE OBJECT]` Two positive torsion lengths permit a constant FE-compatible extension
  that a unit second lane forbids.
- `[PROVED NONSPLITTING]` For `m>0`, the unit class is not even two-sided polynomial-equivalent to
  the split two-torsion matrix.
- `[PROVED LOCAL INTERFACE]` The constant extension residue activates exactly the canonical local
  FE hyperbolic block, with splitting equivalent to nonnegativity.
- `[PROVED POSITION-BLINDNESS]` Local-coordinate reflection preserves the residue, row-splitting
  class, and Witt block; the canonical unit class survives fixed-germ equivariance.
- `[NOT RH-BEARING]` The construction has not been derived from the actual completed divisor pair,
  and the formal reflection audit proves it cannot distinguish the critical-line fixed locus by
  itself.
- `[TAUTOLOGY CHECK]` The residue is computed from the presentation, not defined as
  `analyticOrderAt xi`; however, choosing the presentation or its torsion lengths from the desired
  divisor answer would still be circular.

## New open core

> `[OPEN CORE]` Add a genuinely location-sensitive completed incidence invariant to the two-torsion
> extension.  It must distinguish a fixed germ from a free reflection orbit while not being a
> function of the factorwise order profile, the extension residue, or a carrier.  The candidate
> datum must live in the gluing of the paired base-point germs, not in their identical local
> polynomial extension class.

The next question is therefore a descent/gluing question across the orbit groupoid: which fixed
completed compatibility class exists on a two-point FE-Schwarz orbit but collapses on a fixed germ,
or conversely?  Local Ext and local Witt data have now been proved insufficient.

The attempted integral follow-up is retired in
`../../5-failed/integral-fixed-free-tate-extension.md`.  Its fixed/free Tate residue reduces exactly
to the existing mod-two orbit-cardinality theorem, so assigning the unit class would merely repackage
whether the orbit is fixed.  The live gluing invariant must contain compatibility data beyond local
residue and stabilizer parity.

## Novelty and significance gates

- **NOVEL:** The standard existence of extensions between torsion modules is only background.  The
  new branch-specific result is the exact interaction of the two torsion lengths with FE
  semilinearity, the constant-term classification for the order-one lane, and the derived equality
  between extension splitting and FE-Witt nonnegativity.
- **SIGNIFICANT:** This is the first carrier-free, factorwise-invisible extension in the route that
  survives ordinary and FE-equivariant gauge audits and supplies its own local Witt activation.  The
  reflection theorem also prevents that genuine local novelty from being mistaken for an RH
  detector.
- **HONEST LIMIT:** No global divisor attachment or RH implication is claimed; local reflection
  blindness is formally established.

## Gates

- [x] two-torsion FE condition proved.
- [x] constant-term extension classification proved.
- [x] genuine two-sided nonsplitting of the unit class proved for positive first length.
- [x] local extension-to-Witt activation proved.
- [x] local-coordinate reflection invariance and fixed-germ survival proved.
- [ ] a nonlocal orbit-gluing invariant and completed-divisor attachment.

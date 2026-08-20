# Strict-convex nonlinear exchange, dissipation, and global selection law

- **ID:** ULF-ALCM-2
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Status:** `[PROVED HERE] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT]`
  `[GLOBAL FORMATION/PROPERNESS] [LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS]`
  `[SELECTION MECHANISM] [NOT RH]`
- **Lean:** `GaloisForLFunctions.HTGeometry.ConstitutiveAsymptoticLawCoreRigidity`
- **Parent:**
  `asymptotic-law-core-formation-affine-exchange-recovery-and-exactification-law.md`
- **Statement:** A convergent continuous strictly convex energy either collapses the complete
  asymptotic law core to one law or exposes a strict Jensen-dissipation law invisible to the scalar
  energy history. Compact energy sublevels generate the compact formation carrier automatically.

## 1. Why affine exchange cannot select

For a history `x : N -> E`, write

\[
 \mathfrak F(x)=\bigcap_{N\ge0}\overline{\operatorname{co}}
 \{x_n:n\ge N\}.
 \tag{SCE.1}
\]

ULF-ALCM-1 proves exact exchange

\[
 A(\mathfrak F(x))=\mathfrak F(Ax)
 \tag{SCE.2}
\]

for every continuous affine reporter `A`. This is information-neutral and therefore cannot by
itself choose one element of a non-singleton core. Selection first appears when a nonlinear law is
required to exchange exactly with convex formation.

Let `W : E -> R` be a continuous energy and suppose

\[
 W(x_n)\longrightarrow c.
 \tag{SCE.3}
\]

Then the scalar energy core is the singleton

\[
 \mathfrak F(Wx)=\{c\}.
 \tag{SCE.4}
\]

## 2. Convex formation cannot create limiting energy

### Theorem 2.1 -- energy upper law

Assume the history is contained in a compact convex set `K`, `W` is continuous and convex on `K`,
and `(SCE.3)` holds. Then

\[
 \boxed{y\in\mathfrak F(x)\Longrightarrow W(y)\le c.}
 \tag{SCE.5}
\]

### Proof

Fix `y in F(x)` and suppose `W(y)>c`. Put

\[
 \varepsilon=\frac{W(y)-c}{2}>0.
\]

Eventually `W(x_n)<c+epsilon`. The sublevel

\[
 S=K\cap\{z:W(z)\le c+\varepsilon\}
\]

is closed and convex. It contains a complete tail, hence it contains the closed convex hull of that
tail. Since `y` belongs to every tail hull, `y in S`, which gives
`W(y)<=c+epsilon<W(y)`, contradiction. QED.

The inequality is one-sided and sharp. Convex formation may lower energy even when every tail point
has asymptotic energy `c`.

## 3. Strict Jensen dissipation is the exact obstruction

### Theorem 3.1 -- explicit dissipation witness

Assume `K` is compact, `x_n in K`, `W` is continuous and strictly convex on `K`, and `(SCE.3)`
holds. If `F(x)` is not a singleton, then there exists `m` such that

\[
 \boxed{
 m\in\mathfrak F(x),\qquad W(m)<c,\qquad
 W(m)\notin\mathfrak F(Wx).
 }
 \tag{SCE.6}
\]

### Proof

Compact formation makes `F(x)` nonempty. Choose distinct `a,y in F(x)` and put

\[
 m=\frac{a+y}{2}.
\]

Convexity of `F(x)` gives `m in F(x)`. Theorem 2.1 gives `W(a)<=c` and `W(y)<=c`, while strict
convexity gives

\[
 W(m)<\frac{W(a)+W(y)}2\le c.
\]

Equation `(SCE.4)` now implies `W(m) notin F(Wx)`. QED.

Thus the nonlinear exchange defect has a concrete sign: formation dissipates the conserved tail
energy. It is not an unspecified curvature class.

### Corollary 3.2 -- exact alternative

Under the same hypotheses, exactly the following proof-level alternative is available:

\[
 \boxed{
 (\exists a,\ \mathfrak F(x)=\{a\})
 \quad\text{or}\quad
 (\exists m\text{ satisfying }(\mathrm{SCE}.6)).
 }
 \tag{SCE.7}
\]

No topology, phase, recurrence, or route label occurs in this alternative.

## 4. Nonlinear no-loss forces selection

### Theorem 4.1 -- no-loss rigidity

Under the hypotheses of Theorem 3.1, assume only

\[
 W(\mathfrak F(x))\subseteq\mathfrak F(Wx).
 \tag{SCE.8}
\]

Then

\[
 \boxed{\exists a,\ \mathfrak F(x)=\{a\}.}
 \tag{SCE.9}
\]

In particular exact nonlinear exchange

\[
 W(\mathfrak F(x))=\mathfrak F(Wx)
 \tag{SCE.10}
\]

forces the same conclusion.

### Proof

By `(SCE.4)` and `(SCE.8)`, every point of `F(x)` has energy exactly `c`. If two distinct points
`a,y` belonged to the core, their midpoint would also belong to the core, but strict convexity would
give energy strictly below `c`, contradiction. QED.

This is the first genuine selection law in asymptotic law-core mechanics. Affine exchange is always
neutral; strict nonlinear exchange is rigid.

## 5. Global formation/properness selection

The compact carrier in the previous theorems need not be supplied independently.

### Theorem 5.1 -- proper-energy formation alternative

Let `E` be a real normed vector space. Assume:

1. `W : E -> R` is continuous;
2. `W` is strictly convex on all of `E`;
3. every sublevel `{z : W(z)<=r}` is compact;
4. `W(x_n)->c`.

Then

\[
 \boxed{
 (\exists a,\ \mathfrak F(x)=\{a\})
 \quad\text{or}\quad
 (\exists m\text{ satisfying }(\mathrm{SCE}.6)).
 }
 \tag{SCE.11}
\]

### Proof

Convergence makes the range of `W(x_n)` bounded above. Choose `C` with `W(x_n)<=C` for all `n`.
The sublevel

\[
 K_C=\{z:W(z)\le C\}
\]

is compact by properness and convex by convexity of `W`; it contains the whole history. Restricting
strict convexity to `K_C`, Corollary 3.2 applies. QED.

This is the global formation/properness theorem required by the field programme. Properness is not
an extra compactification object: it is the law ensuring that a bounded-energy history already has
an admitted compact formation domain.

### Corollary 5.2 -- global no-loss selection

Under the same global properness hypotheses, if

\[
 W(\mathfrak F(x))\subseteq\mathfrak F(Wx),
\]

then `F(x)` is a singleton. Indeed, energy convergence bounds the history in one compact sublevel,
and Theorem 4.1 applies on that source-generated carrier.

## 6. Exact mechanism and fourth-organ prediction

The mechanism has three stages:

1. **Formation:** cofinal tail histories generate `F(x)`.
2. **Conservation:** scalar energy history collapses to `{c}`.
3. **Nonlinear exchange:** a non-singleton formed law set necessarily creates strict Jensen
   dissipation; forbidding that dissipation selects one law.

Therefore every claimed conserved proper strictly convex field energy must satisfy the following
route-independent prediction:

> A nontrivial recurrent, corona, operator, or packet law core cannot remain simultaneously
> energy-sharp and nonlinear-exchange neutral. It must either collapse to one law, dissipate below
> its tail energy, or leave every compact energy sublevel.

This prediction is falsifiable in any fourth organ by producing all three: a non-singleton core,
compact sublevels, and exact no-loss. The theorem says those data are inconsistent.

## 7. Nonisomorphic calibration examples

1. **Scalar recurrence.** For `x_n=(-1)^n` and `W(t)=t^2`,
   `F(x)=[-1,1]`, `F(Wx)={1}`, and the formed midpoint has energy `0<1`.
2. **Finite-dimensional unitary recurrence.** A nontrivial norm-constant recurrent orbit has
   `W(v)=||v||^2` constant; any distinct pair of formed laws yields a midpoint with smaller squared
   norm. Recurrence does not preserve purity under convex formation.
3. **Probability formation.** For distinct probability laws, squared Hilbert norm or any strictly
   convex integral energy decreases under a genuine mixture. A pure/energy-sharp packet core can be
   nontrivial only by admitting dissipation or losing properness.
4. **Operator/corona prediction.** If escaping states have a non-singleton corona core while a
   source energy remains constant, that energy cannot be both proper and exactly preserved by
   formation. Hence a claimed operator selector must identify which of properness, conservation, or
   nonlinear exchange fails.

These are calibrations of one theorem, not a declaration that the organs are identical.

## 8. Sharp boundaries

1. Strict convexity is load-bearing. An affine or merely convex energy may be constant on a segment.
2. Energy convergence is load-bearing. Oscillating scalar energy can have a non-singleton energy
   core without any exchange contradiction.
3. Proper compact sublevels are load-bearing only for the global theorem; compact containment may
   instead be supplied by another source law.
4. The theorem selects a unique formed law but does not identify it with the critical RH law.
5. An RH application still must construct a source-native `W`, prove convergence of `W(x_n)`, and
   prove no-loss or exact nonlinear exchange before divisor specialization. Declaring such an energy
   by hand is circular.

## 9. Lean correspondence

The Lean module proves, without project axioms:

- `convex_energy_le_limit_on_asymptoticLawCore`;
- `exists_strictConvex_formationDissipation_of_nonsingleton`;
- `asymptoticLawCore_singleton_or_strictConvex_dissipation`;
- `properStrictConvex_asymptoticLawCore_singleton_or_dissipation`;
- `asymptoticLawCore_singleton_of_strictConvex_noLoss`;
- `asymptoticLawCore_singleton_of_strictConvex_exchange`.
- `properStrictConvex_asymptoticLawCore_singleton_of_noLoss`.

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

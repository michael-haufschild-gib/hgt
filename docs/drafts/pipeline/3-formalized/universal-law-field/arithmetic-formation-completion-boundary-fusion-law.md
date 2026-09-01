# Arithmetic formation--completion boundary fusion law

Status: fully proved and formalized in Lean 4.

Lean module:
`GaloisForLFunctions.RHTower.ArithmeticFormationCompletionBoundaryFusion`.

Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.

## Higher-law interpretation

Finite arithmetic effectivity and completed physical effectivity are different notions.  For the
literal rational-adelic Meyer--Tate source, the off-critical horizontal class is exactly the law
born in the topological closure of finite source boundaries but absent from the finite source
graph itself.  Thus the same class appears as:

1. a formation--completion boundary;
2. a reflection-odd Roos `lim^1` class;
3. a nonzero completed Xi Green vertical boundary;
4. a nonzero strict Gamma/Sonin physical response.

This is a route-independent mechanism statement: the obstruction is failure of finite arithmetic
effectivity under completion, not a property invented separately by four receivers.

## Corpus inputs

Fresh `scripts/formal_tools.py research` searches locate:

- `deningerGammaSixCofinalFiniteGraph_closure_eq_top`;
- `deningerGammaSixCofinalMeyerTateCompletedDifferential_dense`;
- `tendsto_deningerGammaSixCofinalMeyerTateCompletedDifferential_xiGreenChain`;
- `deningerGammaSixCofinalXiGreenVerticalBoundary_eq_zero_iff`;
- `deningerGammaSixCofinalGraphPhysicalTransport_xiGreenBoundary_eq_zero_iff`;
- `preDivisorTransverseDerivedCompletionClass_ne_zero_iff`.

The missing statement is only the finite-effectivity classification of the vertical line.

## Definitions

Let

`i : (N ->_0 C) -> ell^2(N,C)`

be finite-packet admission, `tau` the algebraic unit trace, and

`G_fin = range(c |-> (i(c), tau(c))) <= ell^2(N,C) direct-sum C`.

Let `v = (0,1)` be the singular vertical generator and

`B_q = g_q v`

the completed Xi Green vertical boundary of a multiplicity-labelled Xi copy `q`.  Define the
arithmetic formation--completion boundary

`partial_F G_fin = closure(G_fin) \ G_fin`.

## Theorem

For every Xi zero copy `q`:

1. `i` is injective.
2. For every scalar `a`, `a v` belongs to `G_fin` iff `a = 0`.
3. `B_q` always belongs to `closure(G_fin)`.
4. The following are equivalent:
   - `B_q` belongs to `partial_F G_fin`;
   - `B_q` does not belong to `G_fin`;
   - the pre-divisor transverse Roos class at `q` is nonzero;
   - the strict completed Gamma/Sonin physical response at `q` is nonzero;
   - `Re(q) != 1/2`.

Consequently the Xi formation--completion boundary is empty on every divisor copy iff RH holds.

## Proof

For (1), if `i(c)=0`, then its `n`th coordinate is `c(n)` by
`deningerGammaSixCofinalFinitePacketAdmission_apply`; hence every coefficient of `c` is zero.

For (2), suppose `a v` lies in `G_fin`.  Then some finite packet `c` satisfies
`(i(c),tau(c))=(0,a)`.  The first coordinate gives `i(c)=0`, so (1) gives `c=0`; the second
coordinate then gives `a=tau(0)=0`.  Conversely `0 v=0` belongs to every submodule.

For (3), `closure(G_fin)=top` by the exact graph-saturation theorem, so every `B_q` belongs to it.

For (4), membership in `partial_F G_fin` is (3) together with nonmembership in `G_fin`.  By (2),
that nonmembership is exactly `g_q != 0`.  The corpus theorem
`deningerGammaSixCofinalXiGreenVerticalBoundary_eq_zero_iff` identifies `g_q=0` with
`Re(q)=1/2`.  The Roos and strict physical-response equivalences follow respectively from
`preDivisorTransverseDerivedCompletionClass_ne_zero_iff` and
`deningerGammaSixCofinalGraphPhysicalTransport_xiGreenBoundary_eq_zero_iff`.

Finally, universal absence of the boundary says every Xi divisor copy has real part `1/2`, which is
the corpus characterization of RH.  No step assumes RH, critical-line placement, an extra axiom,
or a fitted divisor-dependent operation.

## Exact RH use

This theorem does not assert boundary absence.  It changes the open producer into one precise
source law: prove that the completed Xi Meyer--Tate boundary remains finitely effective in the
literal source graph.  Any such proof forces `B_q in G_fin`, hence `B_q=0`, hence `Re(q)=1/2` for
every Xi copy and therefore RH.  Universal continuous annihilation cannot supply this law because
the finite arithmetic boundary range is dense; the needed mechanism must use extra arithmetic
effectivity, not boundary blindness.

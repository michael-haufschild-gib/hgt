# Source-compatible scale transport and its global boundary

## Actual source and statements

Let f be a nonzero compact real C2 arithmetic test, and x_t its complete graph lift
after literal translation f(u-t). The full Weil value W(x_t)=W(f) is constant;
the two exponential pole moments scale by exp(t/2) and exp(-t/2).

For every B>=0 there is c>0 such that, for every real t,

c exp(B|t|) <= ||x_t||^2.

For every scalar amplitude a, the same choice of c satisfies

c exp(B|t|) |W(a x_t)| <= |W(f)| ||a x_t||^2.

In particular every fixed exponential amplitude leaves an exponentially growing
graph orbit. Each nonzero compact translation orbit eventually leaves the actual
fixed coercive arithmetic carrier.

Let P be its Weil projection, R=1-P, and C_W the full pairing bound. For all graph
sources x,

||x||^2 <= 4W(x)+(4C_W+2)||Rx||^2.

Thus the actual residual retains all-rate growth:

c exp(B|t|)-4W(f) <= (4C_W+2)||R x_t||^2.

## Positive replacement

For fixed aperture R and shift range T, there is C>=1 such that, simultaneously
for every compact source f supported in [-R,R] and every |t|<=T,

||x_t||^2 <= C||x_0||^2 and ||x_0||^2 <= C||x_t||^2.

The constants are uniform over all source profiles in the specified window.
They are allowed to depend on the window and shift range. The statement uses the
original source graph and the full Weil form, without discarding either pole.

## Dependency-closed proof

The actual weighted source mass is integral f(u)^2 cosh(u/2)/Phi(u), bounded above
by the complete graph norm squared. Theta arithmetic gives Phi(u)<=K exp(-B|u|)
for every B>=0. Since cosh(u/2)>=1, exp(B|u|) is bounded by a constant times the
source mass weight. On the translated support, |u|>=|t|-R_f. Integrating gives
an exponential lower bound with coefficient
mass(f) exp(-B R_f)/K, positive because f is continuous and nonzero.

Full Weil translation invariance is inherited from the arithmetic scaling
surface. Quadratic scalar homogeneity gives the joint energy/graph bound for
arbitrary amplitudes. Choosing a higher raw exponential rate defeats any fixed
exponential amplitude normalization.

For residual growth, decompose x=Px+Rx and use the triangle-square inequality,
||Px||^2<=2W(Px), the exact Schur identity W(x)=W(Px)+W(Rx), and
-W(Rx)<=C_W||Rx||^2. These yield the stated reconstruction inequality. No sign
of W(Rx) is used. Carrier coercivity and constant Weil energy then exclude all
sufficiently large translations from that carrier.

For the positive replacement, the B=0 theta estimate bounds ordinary mass by
K||x_0||^2. The exact source weight has a finite positive maximum M on each
enlarged compact window. The imported graph estimate
||x_t||^2<=W(f)+sourceGraphMassPenalty*weightedMass(f translated by t), together
with |W(f)|<=C_W||x_0||^2, gives the forward bound. Apply it to the translated
source and shift -t on the larger window to obtain the reverse bound.

## Lean status

Programme: `formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/`.

`TranslationPreservesWeilEnergyButEscapesEveryExponentialGraphBound.lean`:

- `translatedSourceGraph_all_exponential_lower_bounds`
- `exponentialRenormalization_graph_lower`
- `graph_norm_sq_le_weil_add_residual`
- `translated_residual_all_exponential_lower_bounds`
- `scalarRenormalization_energy_graph_bound`
- `translatedSourceGraph_eventually_outside_carrier`

`BoundedWindowsAdmitSourceCompatibleScaleTransport.lean`:

- `exists_sectionMass_le_graph_norm_sq`
- `exists_boundedWindow_scaleTransport`
- `exists_boundedWindow_two_sided_scaleTransport`

Both modules pass individual Lean checks. Printed capstones depend only on
`propext`, `Classical.choice`, `Quot.sound`. The positive replacement is formalized,
so the obstruction is accompanied by a nontrivial surviving source domain.

## Scope

This rules out global graph control along the stated scalar-normalized translation
orbits. It does not prove that each fixed translation has no bounded extension
on the entire graph, or rule out every different topology or form-preserving
quotient. Those alternatives need their own source and pole comparisons.
No residual sign, growing Ramanujan complement or critical-energy upper bound
follows from these estimates alone.

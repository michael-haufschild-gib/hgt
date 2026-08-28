# C5 atom–likelihood six-jet no-go and literal theta orientation (2026-08-28)

## Formal modules

- `GaloisForLFunctions.HilbertMetric.FifthRootAtomLikelihoodRiccatiNoGo`
- `GaloisForLFunctions.RHTower.ThetaCuspReflectedLikelihoodSixJetOrientation`

Both are wired into their theorem-area umbrellas. Targeted `lake env lean` checks and targeted `lake build` audits passed. Core theorem axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact abstract obstruction

Use
`q(t)=2t²+t⁴/5+t⁶`,
`q_atom(t)=201/100 t²+21/100 t⁴+101/100 t⁶`,
`q_like(t)=-(t²+t⁴+t⁶)/100`.
Then `q=q_atom+q_like` and `exp(-q)=exp(-q_atom) exp(-q_like)`.

The likelihood action and all reflected likelihood jets 1–6 are strictly negative for positive time:
- l1 = `-t/50-t³/25-3t⁵/50`
- l2 = `-1/50-3t²/25-3t⁴/10`
- l3 = `-6t/25-6t³/5`
- l4 = `-6/25-18t²/5`
- l5 = `-36t/5`
- l6 = `-36/5`.

The likelihood Riccati margin is positive:
`M_like=t/1250(301+1508t²+30t⁴+48t⁶+45t⁸)`.
Cross interference is negative, but atom plus cross stays positive:
`M_atom+cross=t/1250(33699-119508t²+364770t⁴+95952t⁶+449955t⁸)>0`.
The quadratic core follows from
`364770(33699-119508y+364770y²)=(364770y-59754)²+8721843714`.

Nevertheless the total fifth-root obstruction is locally positive and later negative at `t=sqrt(1/2)`, while the profile has strict radial second-level Laguerre concavity and global Riccati/angle concavity. Thus isolated likelihood sign data through sixth order, separate positive margins, negative cross interference, atom domination, exact factorization, and local C5 positivity still do not force global C5.

## Literal completed-theta result

For source log partition `L`, define reflected likelihood cumulant jets:
- J4 = `-L⁽⁴⁾(u+t)-L⁽⁴⁾(u-t)`
- J5 = `L⁽⁵⁾(u-t)-L⁽⁵⁾(u+t)`
- J6 = `-L⁽⁶⁾(u+t)-L⁽⁶⁾(u-t)`.

Using corpus source signs L4>0, L5<0, L6>0 and monotonicity of L5 from L6, the new module proves J4<0, J5<0, J6<0 and the exact derivative chain. Combined with earlier J1–J3, this proves literal reflected likelihood jets 1–6 are negative on `0<t≤u`.

## Surviving hard burden

More pointwise jet signs are structurally insufficient. C5 depends nonlocally on accumulated action `q` through `r=e^q-1` and on its first two jets. Next viable target is an exact completed-theta accumulated-action/jet coupling, equivalently the logistic defect inequality
`5 t y'(u,t) ≤ y(u,t)(10+y(u,t))`,
with `y=(2A-tD)/A∈[0,2]`.
Attack it through integral representations or likelihood-ratio order for the literal partition measure, not by optimizing constants or adding isolated finite-order signs.
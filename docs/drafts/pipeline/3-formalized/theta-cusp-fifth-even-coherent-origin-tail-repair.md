# Coupled repair of the fifth even theta source

- **Stage:** 3-formalized; canonical Lean checks and standard-axiom audits complete.
- **Wall:** Σ6; global integrated rank-nine positivity remains open.
- **Claim:** Two positive coupled flux loads repair the origin and a cofinal tail,
  preserve every mixed entry, and leave the positive scale-seven witness unchanged.

Let `H(x)` be the actual native even five-dimensional theta matrix, and
`G(x)=3Φ(x)²+2xΦ(x)Φ′(x)`. Put

`u₁=(0,0,1,420,0)`, `u₂=(0,0,0,1,1568)`, `N=u₁u₁ᵀ+u₂u₂ᵀ`.

Both load vectors annihilate the established scale-seven vector
`v=(-658560,47040,-420,1,-1/1568)`. Their common kernel is
`span(e₀,e₁,h)`, with `h=-420e₂+e₃-e₄/1568`.

## Origin kernel

Write the complete normalized seam moments as `p_j(X)`, so the actual
moments are `M²p_j(X)`, with `M>0` and `19.1<X<19.2`. Set

`a=p₀`, `b=p₁`, `c=p₂`,
`u=-420p₂+p₃-p₄/1568`, `w=-420p₃+p₄-p₅/1568`,
`t=176400p₄-840p₅+(1+840/1568)p₆-2p₇/1568+p₈/1568²`.

The kernel Gram determinant is

`M⁶[(ac-b²)t-(cu²-2buw+aw²)] > 0`.

After `X=(191+z)/10`, its normalized polynomial has strictly positive
coefficients through degree sixteen. The native two-dimensional head is
positive definite, so Schur elimination proves the whole kernel positive.
The actual kernel theorem is formalized as
`EvenFiveOrigin.coherentKernel_zero_posDef`.

The single load along `u₂` cannot repair the origin. Its kernel contains
`span(e₀,e₁,e₂,e₃-e₄/1568)`, whose Gram determinant is strictly negative.
For its degree-twenty-two polynomial, coefficients through degree fifteen
are negative; the positive remaining terms, bounded using `0≤z≤1`, are
smaller than the negative constant term. The actual kernel theorem is
`EvenFiveOrigin.singleCoherentKernel_zero_not_posSemidef`.
Both pass canonical Lean checks and use only standard axioms.

## Positive coupled repair

Use the basis with columns `e₀,e₁,h,e₂,e₃-420e₂`. It is invertible, and
`N` becomes `diag(0,0,0,1,1)` under congruence. Let `S` be the actual
remaining symmetric two-dimensional Schur matrix at zero and set

`L=|S₀₀|+|S₀₁|+|S₁₁|`, `C=(L+Φ(0)²)/Φ(0)² > 0`.

For every real pair `y`, `yᵀSy≥-L‖y‖²`. Since `G(0)=3Φ(0)²`, the
corrected Schur matrix is strictly positive. Thus `H(0)+C G(0)N` is
positive definite; continuity gives a nontrivial origin neighborhood.

Every nonzero entry of `N` has index sum at least four. With first theta
atom `f₁` and scale `q=πe^(2x)`, the proved source asymptotics give
`Φ/f₁→1`, `Φ′/(f₁q)→-2`, and `x/q³→0`. Hence
`G/(f₁²q⁴)→0`. Every balanced correction entry vanishes, leaving the
positive five-dimensional Gaussian moment matrix. Thus the same fixed
repair is positive on a cofinal ray.

For `w_a(r)=r sinh(ar)` and the established zero-boundary flux `K_a`, use

`W_a(r)=w_a(r)H(r/2)+C K_a′(r)N`.

Its correction is entrywise integrable with zero integral for `0<a<1/2`.
Since `K_a′-w_aG(r/2)≥0` and `N` is positive semidefinite, native repaired
positivity gives weighted positivity near zero and on the same cofinal ray,
simultaneously for every positive aperture.

At scale seven, `Nv=0`, so both native and weighted directional energies
are exactly their already proved positive uncorrected values. The previous
diagonal obstruction therefore does not apply to this coupled repair.
The [equal-coefficient obstruction](../5-failed/theta-cusp-fifth-even-common-coupled-obstruction.md)
now excludes global positivity for every common coefficient. The origin
and tail conclusions remain valid; independent coefficients remain a separate route.

Lean: `ThetaCuspSections/FifthEvenCoherentRepair.lean`, namespace
`GaloisForLFunctions.ThetaCuspSections.EvenFiveCoherent`.
`repair_zero_posDef`, `repair_posDef_near_zero`, and
`repair_posDef_eventually` prove the actual source repair.
`weightedRepair_integral` preserves every mixed entry;
`weightedRepair_compact_gap` gives aperture-uniform origin and tail positivity.
`repair_witness_energy` and `weightedRepair_witness_energy` preserve the
witness at every center; both scale-seven positivity theorems are unconditional.
`single_load_fails` excludes every real coefficient of the last-pair load alone.
These seventeen declarations use only `propext`, `Classical.choice`,
and `Quot.sound`. The canonical check is clean; the owner umbrella imports the module.

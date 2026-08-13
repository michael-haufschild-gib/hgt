# Xi depth-successor Stokes normal layer

- **ID:** `xi-depth-successor-stokes-normal-layer`
- **Stage:** 3 — formalized in Lean 4
- **Type:** EXACT DOUBLE-SCALING THEOREM / SOURCE-NORMAL RH INTERFACE
- **Scientific status:** `[LEAN-PROVED] [CORPUS-NEW SYNTHESIS]`
  `[NO EXTERNAL NOVELTY CLAIM] [NOT RH]`
- **Parents:**
  - `../not_new_scientific_knowledge/wold-depth-xi-essential-amplification-law.md`;
  - `../../1-in-progress/reflected-character-singular-splitting-bockstein-law.md`;
  - `gamma-copoisson-sonin-full-quotient-flatness-syzygy.md`;
  - `../../prime-first-trace-essential-normal-bockstein.md`.
- **Formal modules:**
  `formal/GaloisForLFunctions/RHTower/XiDepthSuccessorStokesNormalLayer.lean`;
  `formal/GaloisForLFunctions/RHTower/XiDepthMobiusGammaOuterInnerWeld.lean`.

## 1. Frontier

The all-orders-flat theorem proves that no operator family of one fixed finite Rees norm order can
sew the reflected irregular sector to the vacuum half-density sector, in any dimension. The
Wold-depth theorem then identifies the first required essential action:
\[
 {\cal A}_2=\frac{\log 2}{2}.
\tag{1}
\]
Essential growth alone is not selective: diagonal gauges and standard Weyl transport cross
off-line sectors by changing the source action.

What was still missing was an explicit nonperturbative divisor profile carried by the same depth
successor whose fixed-spectral-point limit is
\[
 -u\,\frac{\Xi'(u)}{\Xi(u)}.
\tag{2}
\]
The limit `(2)` is nonuniform at a zero. Blowing up that boundary layer gives a finite universal
profile which retains both zero location and full multiplicity.

## 2. Universal moving-zero theorem

Let \(f\) be analytic near \(\rho\), with a zero of finite order \(m\):
\[
 f(u)=(u-\rho)^m g(u),\qquad g(\rho)\ne0.
\tag{3}
\]
Define one depth-successor step
\[
 B_\varepsilon(u)
 =\frac{f(u)}{f((1+\varepsilon)u)}.
\tag{4}
\]
For fixed \(z\ne-\rho\), put \(u=\rho+\varepsilon z\). Then
\[
 \boxed{\quad
 \lim_{\varepsilon\to0,\ \varepsilon\ne0}
 B_\varepsilon(\rho+\varepsilon z)
 =
 P_{\rho,m}(z)
 :=
 \left(\frac{z}{z+\rho}\right)^m.
 \quad}
\tag{5}
\]

### Proof

The two local arguments are
\[
\begin{aligned}
 u-\rho&=\varepsilon z,\\
 (1+\varepsilon)u-\rho
 &=\varepsilon(z+\rho+\varepsilon z).
\end{aligned}
\]
Using `(3)`,
\[
 B_\varepsilon(\rho+\varepsilon z)
 =
 \left(\frac{z}{z+\rho+\varepsilon z}\right)^m
 \frac{g(\rho+\varepsilon z)}
 {g(\rho+\varepsilon(z+\rho+\varepsilon z))}.
\tag{6}
\]
The cofactor ratio tends to one, proving `(5)`. `QED`

The algebraic identity
\[
 (z+\rho)^mP_{\rho,m}(z)=z^m
\tag{7}
\]
shows that the profile has a zero of order \(m\) at \(z=0\) and a pole of order \(m\) at
\(z=-\rho\). Thus the double-scaling limit retains the complete principal multiplicity; it is
not a zeroth-order detector.

For the actual depth defect
\[
 R_\varepsilon(u)=B_\varepsilon(u)-1,
\tag{8}
\]
the moving-zero layer is \(P_{\rho,m}(z)-1\), whereas its outer, fixed-\(u\) limit after division
by \(\varepsilon\) is `(2)`. The matching law
\[
 z\bigl(P_{\rho,m}(z)-1\bigr)\longrightarrow-m\rho
 \qquad (z\to\infty)
\tag{9}
\]
is the binomial expansion of `(5)`. It is exactly the pole residue of the outer logarithmic
connection. Hence `(5)` is its genuine inner boundary layer, not a second unrelated invariant.

## 3. Balanced normal layer from two literal endpoint steps

The functional equation fixes the center \(c=\tfrac12\). The affine normal form is
\[
 B_{\varepsilon,c}(u)
 =
 \frac{f(u)}
 {f\!\left(c+(1+\varepsilon)(u-c)\right)}.
\tag{10}
\]
The same proof gives
\[
 \boxed{\quad
 B_{\varepsilon,c}(\rho+\varepsilon z)
 \longrightarrow
 P_{\rho-c,m}(z)
 =
 \left(\frac{z}{z+\rho-c}\right)^m.
 \quad}
\tag{11}
\]
It is not necessary to declare this centered transport as a new source operation. Put
\[
 L_\delta(u)=(1+\delta)u,\qquad
 U_\delta(u)=1-(1+\delta)(1-u).
\tag{11a}
\]
Then two actual endpoint-depth operations at \(\delta=\varepsilon/2\) compose to
\[
 T_\varepsilon(u)
 =U_{\varepsilon/2}(L_{\varepsilon/2}(u))
 =u+\varepsilon\left(u-\frac12\right)+\frac{\varepsilon^2u}{4}.
\tag{11b}
\]
The literal source quotient
\[
 \widetilde B_\varepsilon(u)=\frac{f(u)}{f(T_\varepsilon(u))}
\tag{11c}
\]
has the same moving-zero limit `(11)`. Indeed, at \(u=\rho+\varepsilon z\),
\[
 T_\varepsilon(u)-\rho
 =
 \varepsilon\!\left[
 z+\rho-\frac12
 +\varepsilon\left(z+\frac{\rho}{4}\right)
 +\frac{\varepsilon^2z}{4}
 \right].
\tag{11d}
\]
Thus higher-order imbalance disappears in the normal layer while its first normal velocity is
exactly \(u-\tfrac12\).

For \(f=\Xi\), \(c=\tfrac12\), and
\[
 a_\rho=\rho-\frac12,
\tag{12}
\]
the exact balanced Xi nearby cycle is
\[
 P_{a_\rho,m_\rho}(z)
 =
 \left(\frac{z}{z+a_\rho}\right)^{m_\rho}.
\tag{13}
\]

This is the concrete normal-layer object hidden by the earlier phrase “Xi Stokes Bockstein.”
The beyond-all-orders Wold shell supplies its exponentially small source monomial with action
`(1)`; `(13)` is the finite coefficient extracted from that monomial by two literal endpoint
depth successors.

The inner layer also matches the already-formalized outer centered Xi current:
\[
 \lim_{w\to0,\ w\ne0}
 w^{-1}\!\left(P_{a,m}(w^{-1})-1\right)=-ma.
\tag{13a}
\]
The singular Möbius--Gamma graph reconstructs
\[
 \mathcal G_\Xi(s)=-2\,\frac{\Xi'(s)}{\Xi(s)}
\tag{13b}
\]
on its safe Euler domain after the strict-right correction. Therefore
\[
 \frac{s-\frac12}{2}\,\mathcal G_\Xi(s)
 =-\left(s-\frac12\right)\frac{\Xi'(s)}{\Xi(s)}
\tag{13c}
\]
is exactly the outer connection of `(11c)`, and its residue at \(\rho\) is the same charge
\(-m_\rho a_\rho\) as `(13a)`. The source graph and rational nearby cycle are outer and inner
charts of one singularity.

## 4. Literal inverse-versus-adjoint geometry

For a centered shift \(a\), the source-inverse profile is \(P_{-a,m}\), while complex Hilbert
adjunction sends the shift to \(\bar a\), hence gives \(P_{\bar a,m}\). Their pole coordinates are
\[
 \operatorname{pole}(P_{-a,m})=a,
 \qquad
 \operatorname{pole}(P_{\bar a,m})=-\bar a.
\tag{14}
\]
Because \(m>0\) at an actual zero, equality of these meromorphic nearby cycles forces equality of
their pole divisors:
\[
 a=-\bar a.
\tag{15}
\]
For \(a=a_\rho\), `(15)` is
\[
 \rho-\frac12
 =
 -\left(\bar\rho-\frac12\right),
\qquad\text{hence}\qquad
 \boxed{\Re\rho=\frac12.}
\tag{16}
\]

This is the same algebra as inverse-character \(=\) adjoint-character, but no longer as an
abstract scalar slogan. It is equality of two explicit source-generated normal-layer poles.

## 5. What theorem remains

The RH-bearing theorem is now narrower:

`[OPEN CORE — GAMMA_COPOISSON_SONIN_BALANCED_NEARBY_DAGGER_LANDING]`

> Construct the strict source-normal map from the Wold depth-successor shell to the literal
> Gamma/co-Poisson/Sonin source-error syzygy and prove that, after Xi Cartier specialization, its
> nonzero top class identifies the source-inverse profile \(P_{-a_\rho,m_\rho}\) with the
> analytic-adjoint profile \(P_{\bar a_\rho,m_\rho}\) on the same fibre.

The target connection, all finite higher coherence, local factorial confluence jets, depth
successor, essential source action, and exact normal-layer profile are now closed. The missing
content is strict cross-landing and same-fibre dagger.

## 6. Hostile audit

1. **Not RH.** The theorem constructs the two profiles and proves what their equality would
   imply. It does not prove the Gamma/co-Poisson/Sonin landing identifies them.
2. **Not another essential-growth criterion.** Every off-line zero has the profile `(13)`.
   External essential transport can carry it after retuning the source horizon.
3. **Not divisor data inserted by hand.** The family \(B_\varepsilon\) is the already-proved
   exponent-depth successor of the bounded-exponent source. The zero enters only when taking its
   normal layer.
4. **Not multiplicity loss.** Equation `(7)` retains exact order \(m_\rho\).
5. **Not a generic irregular-RH proof.** Local analytic factorization and rational normal
   profiles are standard. Arithmetic content still required is the literal ordinary-prime
   source landing into Burnol's quotient.
6. **Generalized-prime falsifier survives until landing.** A fitted generalized-prime carrier
   has the same local profile at any off-line zero. Only source-first ordinary-integer
   Gamma/co-Poisson/Sonin cross-landing can distinguish it.
7. **No finite-Rees fallback.** The Wold shell producing `(13)` is exponentially flat with action
   `(1)`; every fixed finite-Rees realization kills it.

## 7. Lean status

The formal module proves unconditionally:

- generic moving-zero limit `(5)`;
- literal depth-defect moving-zero limit `(8)` and its outer
  fixed-spectral-point difference quotient `(2)`;
- centered limit `(11)`;
- literal two-endpoint source factorization `(11a)`--`(11c)`, exact affine
  identity `(11b)`, exact moving-zero expansion `(11d)`, and its moving-zero
  limit;
- multiplicity identity `(7)`, exact zero order `m`, and exact pole order
  `-m` for every nonzero displacement;
- exact outer matching law `(13a)`;
- actual Xi limits, uncentered and balanced;
- positivity of Xi multiplicity at a zero and exact Xi-centered zero/pole
  orders;
- full-profile equality implies pole-divisor equality, and the nearby-cycle
  consumer `(14)`--`(16)` follows without assuming pole-coordinate equality.

Exact new closure theorems are:

- `tendsto_depthSuccessorTransportDefect_movingZero`;
- `tendsto_depthSuccessorTransportDefect_differenceQuotient`;
- `tendsto_xiDepthSuccessorTransportDefect_movingZero`;
- `tendsto_xiDepthSuccessorTransportDefect_differenceQuotient`;
- `twoEndpointBalancedDepthSuccessor_argument_eq`;
- `twoEndpointBalancedDepthSuccessor_argument_movingZero_sub`;
- `meromorphicOrderAt_depthSuccessorNearbyCycle_zero`;
- `meromorphicOrderAt_depthSuccessorNearbyCycle_pole`;
- `re_eq_zero_of_inverse_adjoint_nearbyCycle_eq`;
- `inverse_adjoint_nearbyPole_eq_of_nearbyCycle_eq`;
- `meromorphicOrderAt_xiCenteredNearbyCycle_zero`;
- `meromorphicOrderAt_xiCenteredNearbyCycle_pole`;
- `criticalLine_of_inverse_adjoint_nearbyCycle_eq`.

The outer/inner chart weld remains formalized by
`xiDepthNearby_outerCharge_and_affineResidue_match` in
`XiDepthMobiusGammaOuterInnerWeld.lean`.

The module uses no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration. The Burnol
co-Poisson/Sonin landing remains outside the formal tree because its analytic source interfaces
have not yet been constructed.

Verification:

- direct `lake env lean` check passed for
  `XiDepthSuccessorStokesNormalLayer.lean`;
- `lake build GaloisForLFunctions.RHTower.XiDepthMobiusGammaOuterInnerWeld`
  built both formal modules successfully;
- `#print axioms` on generic limits, exact order theorems, full-profile
  consumer, Xi specializations, and outer/inner weld reports only `propext`,
  `Classical.choice`, and `Quot.sound`.

## 8. Literature boundary

Finite-order analytic factorization, deformation to the normal cone, and nearby-cycle/Stokes
language are established mathematics. No external novelty is claimed for `(5)` in isolation.
The corpus contribution is the exact weld:

```text
bounded-exponent ordinary-prime depth successor
  -> Wold all-orders-flat shell with action (log 2)/2
  -> two-endpoint Xi moving-zero normal profile
  -> Möbius--Gamma outer / rational-nearby inner chart weld
  -> explicit inverse/adjoint nearby-pole comparison
  -> literal Gamma/co-Poisson/Sonin landing target.
```

## Gates

- [x] fixed-point Xi depth connection
- [x] moving-zero double-scaling theorem
- [x] exact multiplicity retention
- [x] balanced critical-center profile
- [x] literal two-endpoint source realization
- [x] outer logarithmic-current / inner nearby-profile charge weld
- [x] inverse/adjoint full-profile and pole consumers
- [x] unconditional Lean formalization
- [ ] strict Wold-depth to Gamma/co-Poisson/Sonin source map
- [ ] nonzero top Xi Cartier landing
- [ ] same-fibre inverse/adjoint identification
- [ ] RH

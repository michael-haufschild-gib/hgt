# Quadratic-exponent monomial corank-one mixed-chart law

- **ID:** `cfr-monomial-four-axis-mixed-chart`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / FINITE FIELD CALIBRATION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [NON-RH MODEL] [NO LEAN WRITTEN OR BUILT]`
- **Statement:** One universal quadratic-exponent monomial source matrix has compatible arithmetic and phase-valuated realizations, a valuation exponent not collapsed with its prolongation exponent, a Gram quotient that loses anchored orientation, compact closed phase monodromy with nonzero lifted winding, and exponentially degenerating aperture reconstruction.

## Goal

Prove that four proposed shadows can coexist without all collapsing to one exponent vector in one
literal object. Product packaging does not pass this test. Every shadow below must be computed from
one matrix over one source ring.

## 1. Universal source matrix

Fix `n>=2`, let

\[
 E_n=\{1,\ldots,n,\infty\},
 \qquad
 S_n={n(n+1)\over2},
\]

and work over

\[
 R=\mathbb Z[T,U,U^{-1}].
\]

Define

\[
 \mathscr A_n(T,U)=
 \left[
 TUe_1\mid T^2U^4e_2\mid\cdots\mid T^nU^{n^2}e_n\mid\mathbf1_n
 \right]
 \in R^{n\times(n+1)}.
\tag{1}
\]

Deleting row `n+1` and column `n+1` from `A_(n+1)` while retaining the `infinity` column gives
`A_n`. Thus `(A_n)` is an aperture-compatible system.

Put `Q_n=n(n+1)(2n+1)/6`. For `B_infinity=E_n\{infinity}` and
`B_k=E_n\{k}`, direct expansion gives

\[
 \Delta_{B_\infty}=T^{S_n}U^{Q_n},
 \qquad
 \Delta_{B_k}=(-1)^{n+k}T^{S_n-k}U^{Q_n-k^2}.
\tag{2}
\]

## 2. The theorem

### Theorem 2.1 — one object realizes four noncollapsed shadows

The system `(1)` has the following properties.

1. Its phase-valuated realization over `C((t))` and its arithmetic realization over `Z` have the
   same support matroid `U_(n,n+1)`.
2. Its Gram image does not determine the labeled anchored circuit orientation.
3. Its first logarithmic `U`-prolongation is nonconstant although support remains
   `U_(n,n+1)`.
4. The loop `U=e^(i theta)`, `0<=theta<=2pi`, closes in the compact projective phase chart but has
   nonzero lifted deck class.
5. At `T=rho`, `0<rho<1`, the best right-inverse norm

   \[
    \kappa_n(\rho)
    =\inf\{\|R\|:R\in\operatorname{Hom}(\mathbb C^n,\mathbb C^{n+1}),\ 
      \mathscr A_n(\rho,e^{i\theta})R=I_n\}
   \tag{3}
   \]

   obeys

   \[
    \boxed{
    {\sqrt2\over\sqrt{1+\rho^2}}\rho^{-(n-1)}
    \le\kappa_n(\rho)\le\rho^{-n}.}
   \tag{4}
   \]

   The distinguished diagonal reconstruction loses the exact factor `rho^-1` at every aperture
   extension.

## 3. Common support, different coefficient shadows

Every maximal minor in `(2)` is nonzero. Hence every `n`-subset of `E_n` is a basis and the
underlying matroid is `U_(n,n+1)`.

Under

\[
 T\mapsto t,\qquad U\mapsto e^{i\theta}
\]

in `C((t))`, one gets

\[
 \nu\!\left(\sum_{r\ge r_0}a_rt^r\right)=r_0,
 \qquad
 \operatorname{ph}\!\left(\sum_{r\ge r_0}a_rt^r\right)
 ={a_{r_0}\over|a_{r_0}|}.
\]

Thus

\[
 \nu(\Delta_{B_\infty})=S_n,
 \qquad
   \operatorname{ph}(\Delta_{B_\infty})=e^{iQ_n\theta},
\]

\[
 \nu(\Delta_{B_k})=S_n-k,
 \qquad
 \operatorname{ph}(\Delta_{B_k})
 =(-1)^{n+k}e^{i(Q_n-k^2)\theta}.
\tag{5}
\]

Under the arithmetic base change `T->2`, `U->1`, define
`m(B)=|Delta_B(2,1)|`. The integer maximal-minor multiplicities are

\[
 m(B_\infty)=2^{S_n},
 \qquad
 m(B_k)=2^{S_n-k}.
\tag{6}
\]

Thus the arithmetic, valuation, and phase shadows differ while their common support is exact.

## 4. Gram orientation loss

Set

\[
 A_n(\rho,\theta)=\mathscr A_n(\rho,e^{i\theta}).
\]

All vector norms below are standard Euclidean norms and all map norms are induced operator norms.
The unique circuit, normalized to last coordinate one, is

\[
 c_n(\rho,\theta)=
 \left(
 -\rho^{-1}e^{-i\theta},
 -\rho^{-2}e^{-4i\theta},\ldots,
 -\rho^{-n}e^{-in^2\theta},1
 \right)^t,
\tag{7}
\]

because `A_n c_n=-sum_j e_j+1_n=0`.

Let `Lambda=diag(-1,1,...,1)` on the column space and put `A'_n=A_n Lambda`. Then

\[
 A'_n(A'_n)^*=A_nA_n^*,
\tag{8}
\]

while the normalized circuit is `c'_n=Lambda c_n`, whose first anchored coordinate has opposite
phase. At `theta=0`, the first circuit coordinate changes from `-rho^-1` to `+rho^-1` while the
Gram matrix is identical.

This proves item 2. If column rephasing is deliberately declared gauge, the anchored orientation
is deliberately quotiented out; the theorem identifies that loss rather than denying the gauge.

## 5. Prolongation at fixed support

Here “prolongation” means only the explicitly defined first logarithmic jet of maximal-minor
functions. No Kolchin prolongation or categorical jet functor is asserted.

Let

\[
 D=U{\partial\over\partial U}.
\]

Equation `(2)` gives

\[
 {D\Delta_{B_\infty}\over\Delta_{B_\infty}}=Q_n,
 \qquad
 {D\Delta_{B_k}\over\Delta_{B_k}}=Q_n-k^2.
\tag{9}
\]

The first logarithmic prolongation vector is therefore

\[
 J_n=(Q_n,Q_n-1,Q_n-4,\ldots,Q_n-n^2),
\tag{10}
\]

which is nonconstant. Its quadratic exponent differences do not collapse to the linear
`T`-valuation differences `(0,-1,...,-n)`. For all `T,U != 0`, every maximal minor remains
nonzero. Hence the bare support matroid cannot determine this first prolongation. This proves item
3. It does not prove logical independence of prolongation and phase winding, which are two faces
of the same `U`-character.

## 6. Closed observed phase and open lifted history

Along `U=e^(i theta)`, `0<=theta<=2pi`, every source entry and every phase-valuated Plücker
coordinate returns exactly to its initial value. The projective phase lies in

\[
 \mathbb P_{ph,n}=(S^1)^{n+1}/S^1.
\]

A lift of its phase arguments has winding vector `(10)`. After one loop it changes by `2pi J_n`.
Modulo common projective winding,

\[
 [J_n]=[0,-1,-4,\ldots,-n^2]
 \in\mathbb Z^{n+1}/\mathbb Z(1,\ldots,1),
\tag{11}
\]

which is nonzero. Thus the compact projective observer closes while its lifted history remains
open. This is a deck class/monodromy statement, not holonomy of a constructed connection. It
proves item 4.

This is a kinematic phase-history theorem, not yet a quantum recurrence or wormhole theorem. A physical
realization additionally needs a Hamiltonian, cost, and source interpretation of the lift.

## 7. Quantitative aperture inverse loss

Write

\[
 D_n(\rho,\theta)=\operatorname{diag}
 (\rho e^{i\theta},\rho^2e^{4i\theta},\ldots,\rho^ne^{in^2\theta}).
\]

Then

\[
 A_n=[D_n\mid\mathbf1_n],
 \qquad
 A_nA_n^*
 =\operatorname{diag}(\rho^2,\rho^4,\ldots,\rho^{2n})
  +\mathbf1_n\mathbf1_n^*.
\tag{12}
\]

The Gram matrix is independent of `theta`. Since `A_n` is onto, the least norm of a right inverse
is

\[
 \kappa_n(\rho)=\sigma_{\min}(A_n)^{-1}.
\tag{13}
\]

Indeed, let `u` be a unit left singular vector for `sigma_min(A_n)`. For every right inverse `R`,

\[
 1=|\langle A_nRu,u\rangle|
 =|\langle Ru,A_n^*u\rangle|
 \le\|R\|\sigma_{\min}(A_n).
\]

Hence `||R||>=sigma_min(A_n)^-1`. The Moore--Penrose right inverse
`A_n^*(A_nA_n^*)^-1` attains equality.

The right inverse `R_n y=(D_n^-1 y,0)` has norm `rho^-n`, proving the upper bound in `(4)`.

For the lower bound, take

\[
 x={e_{n-1}-e_n\over\sqrt2}.
\]

Then `x` is orthogonal to `1_n`, so

\[
 x^*A_nA_n^*x
 ={\rho^{2(n-1)}+\rho^{2n}\over2}.
\tag{14}
\]

The least eigenvalue is at most this Rayleigh quotient. Taking inverse square roots gives the lower
bound in `(4)`. Finally,

\[
 \|D_{n+1}^{-1}\|=\rho^{-(n+1)}
 =\rho^{-1}\|D_n^{-1}\|.
\tag{15}
\]

This proves item 5. `[PROVED HERE]`

## 8. What this model proves and does not prove

One source matrix carries four simultaneous operations:

\[
 \boxed{
 \text{coefficient base change}
 \times
 \text{prolongation}
 \times
 \text{aperture}
 \times
 \text{transport}.}
\]

Their outputs are not all collapsed to one monomial character:

- arithmetic multiplicity and phase valuation share support but retain different coefficients;
- Gram reduction erases anchored orientation;
- the quadratic prolongation exponent differs from the linear valuation exponent at fixed support;
- phase closes while the lifted deck class does not;
- aperture reconstruction becomes exponentially singular.

The model proves simultaneous realizability and nonconservativity of several forgetful maps. It
does not prove categorical coherence or full pairwise independence. The model is engineered. It
does not derive primes, Gamma factors, Stokes forms, Fredholm events,
hypertranscendence, physical recurrence, or RH. Its role is stronger and narrower: it supplies one
non-product finite consistency witness for the four-output data schema.

## Gates

- [x] one source ring
- [x] compatible arithmetic and phase-valuated base changes
- [x] explicit Gram orientation loss
- [x] nonconstant prolongation at fixed support
- [x] nontrivial lifted loop cocycle
- [x] quantitative cofinal inverse loss
- [x] dependency-closed proof
- [x] hostile scope audit
- [ ] source-native HGT realization
- [ ] Lean formalization

## Log

- 2026-08-09 — constructed as the first exact four-axis mixed chart after literature and corpus audits rejected static enriched matroids as the field core.

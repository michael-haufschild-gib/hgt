# Deninger Weil--Arakelov complementary-weight duality

- **ID:** `deninger-weil-arakelov-complementary-duality`
- **Stage:** 2-fully-proven
- **Type:** DERIVED COCHAIN DUALITY
- **Parent:** `deninger-weil-arakelov-dynamical-lift`

## Statement

Let
\[
  L^0\xrightarrow{d^0}L^1\xrightarrow{d^1}L^2
\]
be a three-term cochain complex with endpoint pairing
\(B_{02}:L^0\times L^2\to R\), skew middle pairing
\(B_{11}:L^1\times L^1\to R\), and chain compatibility
\[
  B_{11}(d^0x,y)+B_{02}(x,d^1y)=0.                    \tag{1}
\]
Let \(\Theta\) preserve the complex and have weight one:
\[
\begin{aligned}
 B_{02}(\Theta^0x,z)+B_{02}(x,\Theta^2z)&=B_{02}(x,z),\\
 B_{11}(\Theta^1x,y)+B_{11}(x,\Theta^1y)&=B_{11}(x,y).
\end{aligned}                                         \tag{2}
\]
For \(n\in R\), let \(F_n=\operatorname{Fib}(\Theta-n)\), in degrees \(0,\ldots,3\).
Then \(F_n\) and \(F_{1-n}\) carry a canonical total-degree-three cochain pairing:
\[
\begin{aligned}
 P_{03}(x,z)&=B_{02}(x,z),\\
 P_{12}((y,x),(z,y'))&=-B_{11}(y,y')+B_{02}(x,z),\\
 P_{21}((z,y),(y',x))&=B_{02}(x,z)+B_{11}(y,y'),\\
 P_{30}(z,x)&=B_{02}(x,z).
\end{aligned}                                         \tag{3}
\]
For homogeneous degree \(i\),
\[
  P(d_{F_n}a,b)+(-1)^iP(a,d_{F_{1-n}}b)=0.            \tag{4}
\]

## Proof

Equation `(2)` implies complementary vertical adjointness:
\[
\begin{aligned}
 B_{02}((\Theta^0-n)x,z)
 +B_{02}(x,(\Theta^2-(1-n))z)&=0,\\
 B_{11}((\Theta^1-n)y,y')
 +B_{11}(y,(\Theta^1-(1-n))y')&=0.
\end{aligned}                                         \tag{5}
\]
Skew-symmetry and `(1)` also give
\[
  B_{11}(y,d^0x)=B_{02}(x,d^1y).                      \tag{6}
\]
Insert the four mapping-fiber differentials
\[
\begin{aligned}
\delta^0_nx&=(d^0x,(\Theta^0-n)x),\\
\delta^1_n(y,x)&=(d^1y,(\Theta^1-n)y-d^0x),\\
\delta^2_n(z,y)&=(\Theta^2-n)z-d^1y
\end{aligned}
\]
into `(3)`.  In degrees \(0,1,2\), respectively, every term cancels by `(1)`,
`(5)`, and `(6)`.  This proves `(4)`.

## Consequence

Whenever the source three-term pairing is perfect and the standard finiteness hypotheses
needed to pass cochain duality to cohomology hold, `(3)` induces
\[
  H^i(F_n)\times H^{3-i}(F_{1-n})\longrightarrow R.
\]
Thus the weight reflection \(n\leftrightarrow1-n\) is forced before any Xi-divisor
comparison.  This is the Weil--Arakelov chain-level functional equation required by the
arithmetic-cohomology construction.

For an arithmetic scheme of pure dimension \(d\), Flach--Morin Remark 4.12 predicts
\[
 R\Gamma_{\mathrm{ar},c}(X,\widetilde{\mathbb C}(n))
 \simeq
 R\operatorname{Hom}\!\left(
   R\Gamma_{\mathrm{ar}}(X,\widetilde{\mathbb C}(d-n)),
   \mathbb C[-2d-1]
 \right).
\]
The theorem above is its explicit mapping-fiber cochain realization for the proper arithmetic
curve \(d=1\), where complementary weight is \(1-n\) and total degree is \(3\).

## Status

- Paper proof: dependency-closed.
- Lean: implementation written in
  `formal/GaloisForLFunctions/RHTower/DeningerArithmeticWeilArakelovDuality.lean`;
  direct check pending shared Lean-load clearance.
- Positivity/RH: not used and not implied.

## Reference

- Matthias Flach, Baptiste Morin,
  *Deninger's conjectures and Weil--Arakelov cohomology*, Conjecture 4.1 and Remark 4.12:
  https://www.math.u-bordeaux.fr/~bmorin/Deninger-WA5.pdf

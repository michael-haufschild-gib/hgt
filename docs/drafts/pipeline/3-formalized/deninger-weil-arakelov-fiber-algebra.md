# Deninger three-term Weil--Arakelov fiber algebra

- **ID:** `deninger-weil-arakelov-fiber-algebra`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** `deninger-weil-arakelov-dynamical-lift`
- **Novelty:** `[REDISCOVERED]` standard mapping-fiber algebra, specialized to exact program

## Statement

Let
\[
  A^0\xrightarrow{d^0}A^1\xrightarrow{d^1}A^2
\]
be a complex of modules, and let \(v^q:A^q\to A^q\) be a chain endomorphism.  Define
\[
  F^0=A^0,\quad
  F^1=A^1\oplus A^0,\quad
  F^2=A^2\oplus A^1,\quad
  F^3=A^2
\]
and
\[
\begin{aligned}
  \delta^0(x)&=(d^0x,v^0x),\\
  \delta^1(y,x)&=(d^1y,v^1y-d^0x),\\
  \delta^2(z,y)&=v^2z-d^1y.
\end{aligned}
\]
Then \(\delta^1\delta^0=0\) and \(\delta^2\delta^1=0\).  Moreover:

1. \(\ker\delta^0=\ker d^0\cap\ker v^0\).
2. \((y,x)\in\ker\delta^1\) iff \(d^1y=0\) and \(v^1y=d^0x\).
3. \((z,y)\in\ker\delta^2\) iff \(v^2z=d^1y\).
4. \(\operatorname{im}\delta^2=\operatorname{im}v^2+\operatorname{im}d^1\).

## Proof

The first composite is
\[
  \delta^1\delta^0(x)
  =
  (d^1d^0x,\;v^1d^0x-d^0v^0x)=(0,0).
\]
The second is
\[
\begin{aligned}
  \delta^2\delta^1(y,x)
    &=v^2d^1y-d^1(v^1y-d^0x)\\
    &=(v^2d^1-d^1v^1)y+d^1d^0x=0.
\end{aligned}
\]
Items 1--3 follow by reading coordinates.  Every top boundary has form
\(v^2z-d^1y\), so it lies in the sum of the two images; conversely
\(v^2z+d^1y=\delta^2(z,-y)\).

For Deninger's program take \(v=\Theta-n\).  This is the explicit four-term complex in
Flach--Morin's conjectural equivalence between Weil--Arakelov cohomology and
\(\operatorname{Fib}(\Theta-n)\).

## Formalization

- `[PAPER-PROVED]` Proof above.
- `[LEAN-PROVED]`
  `formal/GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticWeilArakelovFiber.lean`.
- Direct command:
  `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticWeilArakelovFiber.lean`
  exits successfully with no output.
- Source has no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Full module build and axiom print remain deferred to final audit.

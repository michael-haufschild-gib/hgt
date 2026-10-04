# RN-P-7x: positive finite-pair transport primitive

Status: formalized, direct-file and axiom audits passed, 2026-10-03/04.

For the literal complete theta source k, its first-moment kernel H, and
J=H(0,0), define

    O_x(t)=H(0,x)*H(t,t)-J*H(t,t+x),
    B_x(t)=O_x(t)/(x*J*k(t)*k(t+x)).

For every x,t>0, the new unconditional source theorem is

    O_x(t)>x*t*J*k(t)*k(t+x)>0, equivalently B_x(t)>t.

The proof retains both signed source densities. Their total integral is zero;
their ratio is strictly decreasing, so every finite prefix is positive.
For the corrected prefix, the ratio is
(1+x*(p(t)+p(t+x))/2)*k(t+x)/k(t). Its decrease follows from the actual
fourth-jet inequality c''<2c^2, which gives (p^2-c)'=2pc-c'>0 and the strict
finite secant energy in ThetaTailTransportPrimitiveFloor. Schwartz decay
justifies both zero tail limits.

The first leaf also proves the exact transport system, with
a_x(t)=(1-H(0,x)*k(t)/(J*k(t+x)))/x:

    a'=(p(t+x)-p(t))*(a-1/x),
    B'=1+2t*a+(p(t)+p(t+x))*B, B(0)=0, B'(0)=1.

Lean namespace: RHTower.ThetaFiniteTransport.
Leaves:
- ThetaTailPositiveBalancePrimitive.lean: 16 public theorems.
- ThetaTailTransportPrimitiveFloor.lean: 9 public theorems.
- ThetaTailFinitePairTransport.lean: 14 public theorems.

All three targeted `lake --old build` commands passed. All three actual source files
passed `lake env lean` with empty diagnostic logs. All 39 public theorems
were checked with `#print axioms` from /tmp: exactly propext,
Classical.choice, Quot.sound; no added axioms. All three leaves are wired into
RHTower. No full or umbrella build was run. No numerical experiment or
heartbeat increase was used.

Repository lint ran and reported 12 unrelated unreachable modules; none of
the new leaves was reported. Global lint is therefore not claimed clean.

The third leaf closes the exact improper transport:

    integral [k(t+x)*k(t+y)/(k(x)*k(y))]*(a_x(t)+s_y(t)*B_x(t)) dt
      = (H(x,y)-H(0,x)*H(0,y)/J)/(x*y*k(x)*k(y)),
    s_y(t)=(p(t+y)-p(t))/y.

Integrability of the whole density is proved. The new positive flux
G=(p(t+y)-p(t))*k(t+y)*O_x(t)/k(t) has a primitive with a finite limit;
the nonnegative-derivative theorem proves its integrability. The exact
Schwartz-product remainder and the bounded-ratio flux establish the identity
without an integrability premise.

Contribution: closes the positive-primitive and strict corrected-primitive
problems and the exact integral transfer for every finite positive pair. The signed packet a is still
essential. The full finite-pair coordinate-current sign, general-anchor
port signs, arbitrary-rank positivity, and arithmetic RH transfer remain open.
Ongoing successor: ../../1-in-progress/rn-finite-pair-positive-transport-primitive.md.

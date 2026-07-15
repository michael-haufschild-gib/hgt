# Library ticket: Euler-safe critical-logderivative Cauchy-loss contraction

- **Date:** 2026-07-15
- **Owner:** unassigned
- **Source card:**
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/critical-logderivative-euler-safe-cauchy-loss-law.md`
- **Target areas:** `formal/GaloisForLFunctions/HTGeometry`,
  `formal/GaloisForLFunctions/RHTower`
- **Status:** paper refinement complete; formalization deferred; no build run

## Door registration request

Register the source card as the arbitrary-offset, complex-node, boundary-density refinement of the
existing paper-proven bridge `ccm-safe-kernel-diagonal-fock-lift-rh-law.md`, with the exact chain

```text
absolute-Euler Cauchy--Laplace observability
  -> critical logarithmic-derivative kernel positivity
  -> RH.
```

Record that the unconditional shifted Carathéodory kernel and the positive Hardy--Cauchy loss are
separate positive objects, while their domination remains open.  Do not register this as an
independent route and do not describe the card as an RH proof.

## Reusable HTGeometry infrastructure

Add reusable half-plane kernel interfaces only after checking existing mathlib support:

1. the positive-real/Carathéodory kernel theorem

   ```text
   Re F>0 on Re(z)>a
     -> (F(z)+conjugate(F(w)))/(z+conjugate(w)-2a) is positive;
   ```

2. the Laplace Gram representation

   ```text
   2a/(z+conjugate(w))
     =integral_0^infinity 2a exp(-z x)exp(-conjugate(w)x) dx;
   ```

3. the Schur product of positive kernels;

4. the finite-kernel/RKHS lemma saying that

   ```text
   e_z -> e_z tensor c_z
   ```

   is a well-defined contraction exactly when `K circle C<=K`;

5. the half-plane Herglotz boundary realization when the positive-real function extends across the
   boundary and has sublinear growth, including removal of the linear mass at infinity.

These should be general `HTGeometry` theorems, not Xi-named wrappers.

## RHTower specialization

For

```text
X(w)=xi(1/2+w),
L(w)=X'(w)/X(w),
a>1/2,
K_a(w,v)=(L(w)+conjugate(L(v)))/(w+conjugate(v)-2a),
C_a(w,v)=2a/(w+conjugate(v)),
K_0(w,v)=(L(w)+conjugate(L(v)))/(w+conjugate(v)),
```

formalize the exact identity

```text
K_0=K_a-K_a circle C_a.
```

Then connect it to the existing critical logarithmic-derivative/Weil endpoint and state the
conditional capstone

```text
K_a circle C_a<=K_a -> RiemannHypothesis.
```

The substantive analytic inputs are horizontal Xi monotonicity on `Re(s)>1` and
Nevanlinna--Pick extension from the Euler uniqueness half-plane.  Do not postulate either as a
local assumption merely to obtain a thin wrapper.

## Source boundary specialization

At `w=a+it`, define

```text
h_a(t)=Re L(a+it).
```

Once the Herglotz infrastructure is available, prove that the kernel domination is equivalent to
the finite inequality

```text
2a * integral_R h_a(t) integral_0^infinity
       |sum_j c_j exp(-w_j*x)/(w_j-a-i*t)|^2 dx dt
 <= integral_R h_a(t)
       |sum_j c_j/(w_j-a-i*t)|^2 dt.
```

Use the existing prime--Gamma logarithmic-derivative formula to identify `h_a` on
`Re(s)=1/2+a>1`.  The specialization should interface with, but not duplicate,

```text
RHTower/XiWeilResolventSource.lean
RHTower/XiWeilOneCauchyGate.lean
RHTower/XiHurwitzOrientationCauchyClosure.lean
```

The new source family stays wholly inside absolute Euler convergence.  Do not discharge it by
importing the continued-strip anti-Herglotz predicate or any theorem already equivalent to RH.

## Countable criterion

For fixed rational `a>1/2`, prove by continuity that nodes and coefficients in `Q(i)` suffice.
Package this only after the real/complex finite-kernel theorem is in place.

## Circularity firewall

Formalize or retain as a paper regression theorem the two-node counterexample `F(w)=1/(w-a)`:

```text
det [1-2a/(x_i+x_j)]_(i,j=1)^2
 =-a*(x+y-a)*(x-y)^2/(x*y*(x+y)^2)<0
```

for distinct real `x,y>a`.  This prevents a future proof from incorrectly inferring matrix
domination from `Re F>0` and the diagonal estimate `C_a(w,w)<1`.

## Verification constraint

No Lean build, lint, numerical test, or scratch computation was run while producing the source
paper theorem, following the active user instruction.  When formalization begins, use narrow
file-level checks only and coordinate with other active agents before invoking Lean.

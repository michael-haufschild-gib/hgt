# A prescribed clock curvature has one linear integration fiber

- **ID:** `linear-clock-integration-fiber`
- **Stage:** 3-formalized
- **Type:** GENERAL LINEAR INTEGRATION THEOREM / UNIFIED OBSTRUCTION SKELETON
- **Scientific status:** `[LEAN-FORMALIZED] [BRIDGE] [NOT BY ITSELF NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `../1-in-progress/constraint-curvature-integration-stack.md`
- **Statement:** For a linear curvature map, continuation failure and boundary-condition ambiguity
  are respectively emptiness and the kernel torsor of one fiber.

## The theorem

Let

```text
I:P -> C                                                     (1)
```

be a linear integration-to-curvature map and fix `kappa in C`. Define

```text
Fib_I(kappa)={p in P | I(p)=kappa}.                          (2)
```

Then

```text
Fib_I(kappa) is nonempty  <=>  kappa in range(I).             (3)
```

If `p_0` is one point of the fiber, subtraction from `p_0` gives an equivalence

```text
Fib_I(kappa) ~= ker(I).                                      (4)
```

The inverse translates a kernel element by `p_0`. Thus the fiber is either empty or an affine
torsor under the kernel. Failure of existence and nonuniqueness are not separate constructions.

## Lean declarations

`GaloisForLFunctions.HTGeometry.ClockDescentAnomaly` contains:

- `clockIntegrationFiber`;
- `nonempty_clockIntegrationFiber_iff_mem_range`;
- `clockIntegrationFiberEquivKernel`.

The existing module cache was reused and the touched source file passed direct Lean verification.
No build was run.

## Scientific boundary

Equations `(3)` and `(4)` are elementary affine linear algebra and are not new scientific
knowledge. Their role is to pin down the exact linear skeleton that a nonlinear/derived HT
integration stack must refine:

- emptiness becomes continuation or extension failure;
- connected components become boundary conditions;
- stabilizers and loops become monodromy;
- derived tangent kernel/cokernel becomes spectral incompleteness;
- a reflected form on that tangent becomes the positivity question.

The proposed new content begins only when the curvature and integration map are constructed
canonically from one actual HT source and two genuinely different analytic chains are proved to
realize the same fiber.

## Gates

- [x] fiber defined
- [x] nonempty/range criterion formalized
- [x] nonempty fiber identified with kernel torsor
- [ ] nonlinear derived integration stack constructed
- [ ] source-derived curvature supplied in one nontrivial model
- [ ] two analytic realizations identified

# Route R prime/depth BV--Wold curved source differential

- **Stage:** 3 — formalized in Lean 4
- **Status:** `[UNCONDITIONAL CORE] [CORPUS-NEW ARITHMETIC COUPLING] [ANNIHILATION OPEN] [NOT RH]`
- **Paper card:**
  `../../1-in-progress/route-r-prime-depth-bv-wold-curved-source-differential.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.PrimeDepthBVWoldCurvedSourceDifferential`

## Formalized new knowledge

For `i=(p,e)`, Lean constructs the Wold depth cell of the singular BV first trace and the regular
depth clock

```text
m_i=(1-p⁻¹)p⁻ᵉ,
lambda_i=log(p^(e+1)),
theta(i,j)=m_i lambda_j-m_j lambda_i.
```

The depth-zero `m_(p,0)` is formally tied to the residue-one reading of the relative Wold--BV
spectral-zeta class.  The connection is diagonal-zero, antisymmetric, and sign-indefinite.

On `(2,0),(2,1),(2,2)`, Lean proves

```text
delta theta = -log(2)/8 != 0.
```

Therefore no vertex potential generates `theta`.  More strongly, the adjacent clock gaps are both
`log 2`, while their connection coefficients differ by `log(2)/4`; hence no function of clock
difference alone generates `theta`.  This is the strict escape from the previously formalized
prime/depth vertex-gauge class.

For `U_a(i,j)=exp(a theta(i,j))`, the complex-linear exterior covariant maps satisfy

```text
(D1_a D0_a f)(i,j,k)
  = (U_a(i,j)U_a(j,k)-U_a(i,k)) f(k).
```

After pointwise specialization `a_rho=2 Re(rho)-1`, reflection inverts transport and every output
retains divisor plus all prime/depth vertices.  Witness-square vanishing is equivalent to
`Re(rho)=1/2`; global flatness is equivalent to RH.  No flatness or RH premise is assumed.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/PrimeDepthBVWoldCurvedSourceDifferential.lean`:
  passed.
- `lake build GaloisForLFunctions.RHTower.PrimeDepthBVWoldCurvedSourceDifferential`:
  passed.
- `#print axioms` on residue provenance, curvature, both nonseparability theorems, curved square,
  witness criterion, and RH equivalence: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import added to `GaloisForLFunctions/RHTower.lean`.
- Repository-wide `scripts/formal_tools.py lint`: blocked by unrelated concurrent
  umbrella-unreachable CCM/cyclic modules; no error named this module.

## Frontier boundary

Construction is complete.  Arithmetic annihilation is not.  Proving this divisor-resolved
connection flat from the source would prove RH; current Lean theorem records that equivalence and
does not launder it as an unconditional vanishing statement.

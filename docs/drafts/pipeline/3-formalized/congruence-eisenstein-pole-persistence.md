# Congruence Eisenstein constant terms preserve every zeta pole

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ8, scattering continuation below `Re(2s) = 1`.
- **Statement:** For every principal congruence level `N ≥ 3` and positive height,
  the actual Poincaré constant term at infinity has a meromorphic continuation whose pole
  divisor on `0 < Re s < 1/2` is exactly the zero divisor of `ζ(2s)`, with multiplicity.

## Proof

Put `E_M(w)=∏_(p|M)(1−p^(−w))` and
`S(s)=√π Γ(s−1/2) ζ(2s−1)/(Γ(s) ζ(2s))`.

1. On `Re w>1`, the convolution identity
   `(μχ₀)*χ₀=δ₁` gives `L(μχ₀,w)=1/L(χ₀,w)`.
   The principal-character Euler identity gives `L(χ₀,w)=ζ(w)E_M(w)`.
2. The existing literal Poincaré Fourier extraction gives
   `2 pref_N(s,y) φ(N²) L(μχ₀,N²;2s) ζ(2s−1)`.
   Scaling and the beta integral evaluate its kernel integral as
   `(y/N)^(1−s)√π Γ(s−1/2)/Γ(s)`.
   Hence its continuation is `U_N,y(s)S(s)`, where
   `U_N,y(s)=2 exp(−s log N²) exp(−s log N) (y/N)^(1−s)
   φ(N²)/(φ(N)E_(N²)(2s))`.
   Since `φ(N²)=Nφ(N)` and `E_(N²)=E_N`, this simplifies to
   `U_N,y(s)=2N^(−2s)y^(1−s)/E_N(2s)`.
3. Every factor of `U_N,y` is holomorphic and nonzero on `Re s>0`:
   the exponential and positive-base powers never vanish, both totients
   are positive, and `|p^(−2s)|<1`. Thus multiplication by `U_N,y`
   preserves meromorphic order.
4. The established level-one scattering theorem gives
   `ord_(w/2) S = −ord_w ζ` for `0<Re w<1`.
   Therefore the reflected congruence term has exactly the same order,
   for every level and height, including multiple zeros.
5. The incoming term `y^s` is entire and nonzero. At a pole, its order zero
   exceeds the reflected term's negative order, so their sum has the same
   pole order. Away from those poles both summands have nonnegative order.
   Thus the full constant coefficient also has exactly the zeta pole divisor.

Dependencies: `eisenstein_eq`, `fourier_ker0_zero`, `integral_ker01`,
`DirichletCharacter.LSeries.mul_mu_eq_one`, the principal Euler identity,
and `MayerBoundaryResolvent.scattering_order`. No zero-location or
noncancellation premise is assumed.

## Lean

`RenormalizedIntersectionTheory/MayerScattering/CongruencePolePersistence.lean`,
namespace `CongruenceScattering`:

- Source comparison: `constantTerm_eq`, `poincare_eq`, `levelFactor_eq`.
- Continuation: `meromorphicOn_fullConstantTerm` on `Re s>0`.
- Exact pole divisor: `fullConstantTerm_pole_iff`, `fullConstantTerm_order_of_zero`.
- Reflected term's order at every strip point: `constantTerm_order`.

Direct source audit passes with `lake --old env lean`; transitive axioms:
`propext`, `Classical.choice`, `Quot.sound`. Wired into the RIT umbrella.

## Scope

Level-one scattering continuation and its Mayer comparison already exist.
The new claim concerns the literal `Γ(N)` Poincaré constant term at every level.
Resonance exclusion and positivity of the complete realization remain open.

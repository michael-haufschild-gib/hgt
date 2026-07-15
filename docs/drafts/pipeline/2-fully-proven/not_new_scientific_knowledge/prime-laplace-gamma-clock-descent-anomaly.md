# Prime--Laplace unit translation has the exact Gamma clock descent anomaly

- **ID:** `prime-laplace-gamma-clock-descent-anomaly`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / FINITE COMPARISON SQUARE / HT-TO-RH BRIDGE
- **Scientific status:** `[PROVED HERE] [NOT FORMALIZED]
  [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `prime-laplace-gamma-jet-incidence-phase-transition.md` and
  `../../1-in-progress/source-anomaly-boundary-colligation-field.md`
- **Statement:** Multiplication of time-one weighted prime coefficients by `p^(-1)` is exactly
  unit translation of their prime--Laplace transform.  Under finite raw-jet observation, the
  canonical Gamma Taylor matrix is its finite shadow, the source descent anomaly is the omitted
  Taylor tail, and the adjacent-clock Bianchi defect is the formalized factorial boundary
  transfer.

## Source operation and observation

Let `a in ell^2(Primes)` and define

```text
F_a(z)=sum_p a_p sqrt(w_1(p))p^(-z),       Re z>0,       (1)

(S a)_p=p^(-1)a_p.                                       (2)
```

Then, identically on the right half-plane,

```text
F_(S a)(z)=F_a(z+1).                                    (3)
```

Fix `x_0>1` and let

```text
(J_N a)_i=F_a^(i)(x_0),       0<=i<N.                   (4)
```

The prime--jet incidence theorem proves that every `J_N` is Hilbert--Schmidt and that all `J_N`
together are faithful.

## Gamma Taylor shadow

Let `E_N` be the existing Gamma clock translation

```text
(E_N y)_i=sum_(j=i)^(N-1)y_j/(j-i)!.                    (5)
```

Since the disk of radius greater than one about `x_0` stays in `Re z>0`, Taylor's theorem gives

```text
F_a^(i)(x_0+1)
 =sum_(k>=0) F_a^(i+k)(x_0)/k!.                         (6)
```

Combining `(3)`--`(6)`, the source-to-clock descent anomaly

```text
alpha_N=E_N J_N-J_N S                                   (7)
```

has the exact coordinate formula

```text
(alpha_N a)_i
 =-sum_(k>=N-i)F_a^(i+k)(x_0)/k!.                       (8)
```

Thus the finite Gamma clock is not an exact descent of prime translation.  Its complete failure
is neither abstract nor fitted: it is the convergent omitted Taylor tail of the actual source
transform.

## Adjacent-resolution Bianchi law

Let `p_N` forget the highest raw derivative.  The already formalized clock-descent Bianchi identity
applied to `(7)` gives

```text
p_N alpha_(N+1)-alpha_N
 =kappa_N J_(N+1),                                      (9)
```

where

```text
(kappa_N y)_i=y_N/(N-i)!.                               (10)
```

Equation `(10)` is exactly Gamma's rank-one factorial boundary transfer.  It also follows
directly by subtracting the two tails in `(8)`: every term cancels except the newly exposed
derivative `F_a^(N)(x_0)/(N-i)!`.

Consequently the safe finite comparison diagram

```text
prime coefficients --J_N--> raw N-jets
       | S                    | E_N
       v                      v
prime coefficients --J_N--> raw N-jets                  (11)
```

commutes up to the explicit source anomaly `(8)`, and its change with resolution is exactly the
HTGeometry boundary current `(10)`.

## Reflected Euler specialization

For the two time-one reflected vectors

```text
c_rho^+(p)=sqrt(w_1(p))(log p)p^(-rho),
c_rho^-(p)=sqrt(w_1(p))(log p)p^(-(1-conjugate(rho))),   (12)
```

linearity gives the same square and anomaly for their difference.  Its observed jet is the
time-one seam transform

```text
V_rho(z)=M_1(z+rho)-M_1(z+1-conjugate(rho)).             (13)
```

Thus the finite Euler anti-reflection tangent is now literally an object of the Gamma clock
descent-anomaly calculus at every resolution.

## No-go and nontrivial positive successor

Equation `(8)` kills exact finite descent: no finite Gamma Taylor matrix intertwines the complete
prime translation unless the omitted tail vanishes.  This is expected for a source with infinite
clock capacity.

The positive successor is the full exact comparison skeleton `(7)`--`(10)`:

1. the source operation `S` is fixed;
2. the finite observation `J_N` is fixed and Hilbert--Schmidt;
3. the finite shadow `E_N` is the existing Gamma clock;
4. the descent anomaly is an explicit analytic tail;
5. its covariant variation is the formalized factorial boundary vector.

No further finite operator needs to be invented.  The remaining RH theorem is to show that, on an
Xi zero orbit, the FE and Schwarz reflected sections of this same comparison object lie in one
asymptotically calibrated source fibre and preserve the affine Mertens boundary support.

## Parent-theory boundary

Taylor's theorem, derivative evaluation of Dirichlet series, and the tail formula are classical.
The result is bridge infrastructure.  Its value is that the proposed HT-to-RH comparison now has
an exact finite source operation, observation, shadow, anomaly, and Bianchi current.

## Gates

- [x] construct the exact prime source translation
- [x] identify the Gamma finite shadow
- [x] compute the complete descent anomaly
- [x] identify its adjacent-resolution Bianchi boundary
- [x] specialize to the reflected time-one seam
- [x] replace exact-descent failure by the complete finite comparison skeleton
- [ ] formalize when the zero-orbit comparison consumes this skeleton

# Lattice-carry transgression, invariant current, and counterflow law

- **ID:** ULF-TAFM-8
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Status:** `[PROVED HERE]`
- **Dependencies:** finite invariant measure; real `L¹` integration; elementary positive/negative
  part identities; elementary limits

## 1. Formation system

Let `(X, Σ, μ)` be a finite measure space, let `T : X → X` preserve `μ`, let `L > 0`,
and let `χ ∈ ℝ`.  Let `u : X → ℝ` and `k : X → ℝ` be integrable.  The intended
application has `k(x) ∈ ℤ` almost everywhere, but the balance theorem needs only integrability.
Assume the compensated lift equation

`u(Tx) - u(x) + L k(x) = χ` almost everywhere.                         `(8.1)`

Write

`J(k) = ∫ k dμ`, `V(k) = ∫ |k| dμ`,

and, when `μ` is a probability measure,

`J⁺(k) = ∫ max(k,0) dμ`, `J⁻(k) = ∫ max(-k,0) dμ`.

When `k` is integer-valued, it is the microscopic lattice carry, `J(k)` is its oriented mean
current, and `V(k)` is phase-blind traffic.

## 2. Theorem

### Theorem 8.1 -- invariant drift-current reconstruction

Under `(8.1)`,

`μ(X) χ = L J(k)`.                                                     `(8.2)`

In particular, for probability `μ`, `χ = L J(k)`.  If `μ(X) ≠ 0` and `k = 0` almost
everywhere, then `χ = 0`.

### Theorem 8.2 -- lattice-gauge invariance

Let `h : X → ℝ` be integrable and suppose `h ∘ T` is integrable; measure preservation gives this
automatically.  Define

`u_h = u + Lh`, `k_h = k + h - h ∘ T`.                                `(8.3)`

Then `(u_h,k_h)` satisfies the same compensated lift equation with drift `χ`, and

`J(k_h)=J(k)`.                                                         `(8.4)`

If `k` and `h` are integer-valued almost everywhere, so is `k_h`.  Thus microscopic sections
change carry by a coboundary but do not change invariant current.

### Theorem 8.3 -- Hahn traffic/counterflow identity

Assume `μ` is a probability measure.  Then

`L V(k) - |χ| = 2L min(J⁺(k),J⁻(k))`.                                 `(8.5)`

Consequently phase-blind traffic equals oriented drift magnitude exactly when carry is one-sided
almost everywhere.  At zero drift, all traffic is paired counterflow:

`L V(k)=2LJ⁺(k)=2LJ⁻(k)`.

### Theorem 8.4 -- serial formation

If `(8.1)` holds pointwise, then for every `n ∈ ℕ`,

`u(T^n x)-u(x)+L Σ_{j<n} k(T^j x)=nχ`.                                 `(8.6)`

Thus drift and lattice current compose additively, and compact observer recurrence can coexist
with open lifted history only through accumulated carry (or through failure of the integrability,
finite-mass, or exact-covariance hypotheses).

### Theorem 8.5 -- exact winding-rate prediction

Let `X_n,K_n,r_n : ℕ → ℝ`, let `L>0`, and suppose

`X_n = L K_n + r_n`, `0 ≤ r_n < L`                                    `(8.7)`

for every `n`.  If `X_n/n → c`, then

`K_n/n → c/L`.                                                        `(8.8)`

For an integer history reduced modulo an integer `m>0`, take `r_n` to be its Euclidean residue
and `K_n` its integer winding.  A biased `±1` lift of asymptotic velocity `2p-1` therefore has
carry rate `(2p-1)/m`, even when the mod-`m` observer returns infinitely often.

## 3. Proof

### Proof of Theorem 8.1

Measure preservation and integrability give

`∫ u∘T dμ = ∫u dμ`.

Integrate `(8.1)`.  Linearity of the integral gives

`0 + L∫k dμ = ∫χ dμ = μ(X)χ`,

which is `(8.2)`.  If `k=0` almost everywhere and `μ(X)≠0`, the right side is zero and division by
the nonzero mass gives `χ=0`.  ∎

### Proof of Theorem 8.2

Direct substitution into the left side of `(8.1)` gives

`u_h∘T-u_h+Lk_h`
`= (u∘T-u)+L(h∘T-h)+L(k+h-h∘T)`
`= u∘T-u+Lk`
`= χ`.

Moreover,

`J(k_h)=J(k)+∫h dμ-∫h∘T dμ=J(k)`

by invariance.  Integer-valuedness is closed under addition and subtraction.  ∎

### Proof of Theorem 8.3

Put `a=J⁺(k)` and `b=J⁻(k)`.  Both are nonnegative and

`J(k)=a-b`, `V(k)=a+b`.

Theorem 8.1 and probability normalization give `χ=L(a-b)`.  Since `L>0`,

`L V(k)-|χ| = L(a+b)-L|a-b|`
`= L(a+b-|a-b|)`
`= 2L min(a,b)`.

This is `(8.5)`.  The equality and zero-drift statements follow immediately.  ∎

### Proof of Theorem 8.4

Induct on `n`.  The case `n=0` is zero equals zero.  If `(8.6)` holds at `n`, apply `(8.1)` at
`T^n x`:

`u(T^(n+1)x)-u(T^n x)+Lk(T^n x)=χ`.

Add this equality to the induction hypothesis and use the finite-sum successor identity.  The
middle potentials cancel, giving `(8.6)` at `n+1`.  ∎

### Proof of Theorem 8.5

From `(8.7)`,

`K_n/n = (X_n/n-r_n/n)/L`                                             `(8.9)`

whenever `n>0`.  The bounds on `r_n` give

`0 ≤ r_n/n ≤ L/n`.

Since `L/n→0`, squeezing gives `r_n/n→0`.  Taking limits in `(8.9)` yields `(8.8)`.  ∎

## 4. Hostile audit and exact boundary

1. **Not extension curvature of the Hedenmalm interval anomaly.**  The corpus already proves that
   anomaly is a flat exact monoid cocycle.  ULF-TAFM-8 does not relabel it as curvature.
2. **Microscopic, not macroscopic, quantization.**  `k(x)` may be lattice-valued while `J(k)` is an
   arbitrary real expectation.
3. **No existence theorem hidden in the statement.**  The law classifies admitted compensated
   lifts.  It does not construct a compact source model.
4. **Sharp escape chambers.**  Nonintegrable sections, infinite invariant mass, absent lattice
   carry, or inexact covariance can support nonzero drift without contradicting the theorem.
5. **Global FE cancellation is nonselective.**  Reflection changes `χ` and `J` to their negatives.
   A reflected pair therefore has zero total current off wall as well as on wall.
6. **Positivity is phase-blind.**  `V(k)` can be positive when `J(k)=0`; `(8.5)` identifies the
   erased orientation as exact counterflow.

The theorem therefore rejects global zero current as an RH producer.  It predicts the missing
source theorem precisely: componentwise detailed balance, or a source-predeclared one-sided law
that forbids counter-circulation before any zero is chosen.

## 5. Cross-organ reconstruction and RH interface

- ULF-TAFM Law XII is the chamber `k=0`: integrable compact descent kills open drift.
- Constitutive/Kummer carries are the microscopic transgression `k`.
- Closed-observer/open-history recurrence is linear growth of the serial sum in `(8.6)`.
- Hahn/positivity sees `V(k)`; oriented decision current sees `J(k)`; `(8.5)` reconstructs their
  exact information gap.
- For a modular rapidity `χρ=2(Reρ-1/2)`, any admitted compact phase realization satisfies
  `J(kρ)=χρ/L`.  Hence `J(kρ)=0` iff `Reρ=1/2`.  The statement is a sharp interface, not a
  source proof that `J(kρ)=0`.

## 6. Literature boundary

Neighboring ingredients are rotation/asymptotic-cycle theory, integer skew-product cocycles,
extension cohomology, and stationary nonequilibrium currents.  Relevant primary sources include
<https://arxiv.org/abs/1210.3556>, <https://arxiv.org/abs/1109.2999>,
<https://arxiv.org/abs/2410.07255>, <https://arxiv.org/abs/2604.09093>, and
<https://arxiv.org/abs/2004.08677>.  Claimed contribution is synthesis and reinterpretation, not
novelty of these ingredients separately.

## 7. Lean certification

Theorems 8.1--8.5 are formalized in the route-independent module
`GaloisForLFunctions.HTGeometry.TopologicallyAdmittedLatticeCarryCurrent`. Scratch and project-path
elaboration pass; targeted leaf build passes (`8701/8701`). Batched axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. The module is wired into
`HTGeometry.UniversalLawField`; no umbrella build was run.

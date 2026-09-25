# Finite theta heads have infinitely many negative Hankel diagonals

- **Stage:** In progress; paper proof below, Lean formalization pending.
- **Routes:** CLG/TTF, S6F, TCD.
- **Status:** Source-specific order-of-limits obstruction, not an RH proof.

For `N≥1` and `x≥0`, let `h_N(z)=∑_{1≤n≤N} thetaCuspComplexSourceTerm(z,n)` and
`G_{N,x}(z)=h_N(x+z)h_N(x-z)`. The complex source term is the existing literal
polynomial–Gaussian theta atom, not a surrogate. Then, more strongly,

```text
{j≥1 : G_{N,x}⁽⁴ʲ⁾(0) < 0} and
{j≥1 : G_{N,x}⁽⁴ʲ⁾(0) > 0} are both infinite.
```

Consequently the all-order pointwise Fourier-signed even Hankel matrix of every
nonempty finite theta head fails positive semidefiniteness at unbounded diagonal
indices: its diagonal entry at index `j` is `(-1)^(2j) G⁽⁴ʲ⁾(0) < 0`.
No correction changing only finitely many jets can repair this pointwise
all-order cone. This is compatible with positivity of prescribed finite depths
on suitable tails; it does not decide the **integrated** native
cone, where center integration and the infinite source must precede the
all-order sign test.

## Paper proof

Each atom is entire in logarithmic coordinate and anti-periodic under
`z↦z+2πi`; thus `G` is entire, even, and periodic under `z↦z+2πi`.
The finite real head is positive at every `x≥0` because each seed polynomial
has `2πn²e^(2x)-3>0`, so `G(0)>0`. Every fixed finite atom tends to zero on
both ends of the real logarithmic line; hence `G(t)→0` as `t→+∞`.

Entire Taylor expansion, evenness, and fourth-root-of-unity filtering give,
for real `t≥0`,

```text
F(t):=(G(t)+G(it))/2 = Σ_(j≥0) a_j t^(4j),
a_j:=G⁽⁴ʲ⁾(0)/(4j)! ∈ ℝ.
```

At `t=2πk`, periodicity gives `G(it)=G(0)`, while real-axis decay gives
`F(t)→G(0)/2`. Thus `F` is bounded on this unbounded lattice, but is not a
constant polynomial since `F(0)=G(0)>0`.

Suppose the `a_j` are eventually nonnegative. Split `F=P+R`, with `P` a finite
initial polynomial and `R` a nonnegative-coefficient tail. If any coefficient
of `R` is strictly positive, then on the lattice `R(t)` dominates a positive
monomial of degree strictly larger than `deg P`, contradicting boundedness of
`F(t)`. Hence `R=0`, so `F=P`; a polynomial bounded on the unbounded lattice
is constant, again contradicting its two values above. Thus infinitely many
`a_j<0`. Apply the same argument to `-F` to get infinitely many `a_j>0`.

The analytic argument is general: any real-even entire function with a
nonzero value at zero, an imaginary period, and real-axis decay has infinitely
many Taylor coefficients of both signs in its fourth-order subsequence. The
literal finite theta heads instantiate it. This is a singular-completion
obstruction, not an RH proof.

## Scientific scope

This rules out proving the RH-bearing all-order integrated cone by first
establishing pointwise all-order positivity on any finite literal theta head,
or by a finite-jet repair of that step. A positive Hadamard multiplier with
strictly positive diagonal also retains each negative diagonal, so the
regularization criterion in `HadamardRegularizationLaw.lean` cannot rescue
this pointwise route merely by entrywise positive damping.
It does not rule out integration-first positivity or the infinite theta sum.
The infinite source series ceases to converge when `cos(2 Im z)≤0`, as proved
in `ThetaCuspComplexClockSector.lean`. More sharply, the unbounded center
integral already creates a sector boundary for **one finite atom**, so the
pointwise entire argument cannot be moved past center integration either.

## Failed extension: finite-head center integration is not entire

The tempting stronger claim was that center integration preserves the finite
head's entire imaginary-periodic continuation, forcing negative *integrated*
diagonals. It is false at its analytic premise. Put `h₁(z)` equal to the literal
single complex source term and, for `0<a<1/2`, define on `|Im z|<π/4`

```text
J_a(z)=∫_(r>0) r sinh(a r) h₁(r/2+z)h₁(r/2−z) dr.
```

The integral is holomorphic in that strip by compact-local Gaussian
domination. For `z=i v`, `0≤v<π/4`, its integrand is nonnegative because
the two source factors are conjugate. At the boundary `v=π/4`, with `x=r/2`,
the literal seed formula gives the exact modulus square

```text
|h₁(x+iπ/4)|²
 = (2π)² e^x [(2π)² e^(8x) + 9e^(4x)].
```

The Gaussian has unit modulus there; the displayed expression makes the
weighted boundary integral infinite. Fatou's lemma therefore gives
`J_a(i v)→+∞` as `v↑π/4`. In particular no holomorphic continuation of
this literal center-integrated germ crosses `iπ/4`, and its Taylor series
at zero cannot be evaluated at the imaginary period `2πi`. The extension
of the pointwise sign-oscillation argument to integrated heads fails.

**Whole-route meaning:** center integration is itself a singular analytic
operation, even before the infinite prime assembly. Finite-head integrated
positivity remains a legitimate, separate question; the prior pointwise no-go
does not answer it. Any proposed all-order proof must retain this order of
operations and the sector boundary rather than transporting entire Taylor
signs through the center integral.

External priority and Lean closure remain to audit. Do not promote to a
formalized or publication-ready claim until both are complete.

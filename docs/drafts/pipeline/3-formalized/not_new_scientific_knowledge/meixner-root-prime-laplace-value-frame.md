# A common prime-Laplace value frame for every Gamma--Meixner root domain

- **ID:** `meixner-root-prime-laplace-value-frame`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Parents:** `archimedean-meixner-root-seam-scale.md`, uniqueness of Dirichlet series, and the
  finite Gram/Riesz criterion
- **Lean inputs:** `PrimeLaplaceGramStrict.lean`, `PrimeLogCauchySeamRank.lean`,
  `GammaDampedPrimeLogCauchyDomain.lean`, and `XiPrimeSeamEulerZeroTangent.lean`
- **Statement:** `[PROVED HERE]` The prime exponentials `p |-> p^(-x)`, `x>1/2`, form a common
  algebraic core which is dense in every Gamma--Meixner root Hilbert space.  The reflected Xi seam
  belongs to one of those spaces exactly when its explicit Meixner-weighted prime-zeta derivative
  values satisfy a finite Gram bound on this core.  The countable nodes `x_n=1+1/n` suffice.

## The root Hilbert spaces

For `theta>0`, let

```text
w_theta(p)=(cosh(2*log p))^(-theta/2)
```

and define

```text
H_theta=ell^2({primes},w_theta),
||a||_(H_theta)^2=sum_p w_theta(p)|a_p|^2.                (1)
```

The exact Gamma--Meixner calculation in the parent card gives

```text
p^(-theta)<=w_theta(p)<=2^(theta/2)p^(-theta).           (2)
```

For `x>1/2`, put

```text
e_x(p)=p^(-x).                                           (3)
```

Then `e_x` belongs to every `H_theta`, because `(2)` gives

```text
sum_p w_theta(p)|e_x(p)|^2
 <=2^(theta/2)sum_p p^(-(theta+2*x))<infinity.           (4)
```

The exponent is greater than one for every `theta>0`.

## Common-core density theorem

For every `theta>0`,

```text
closure(span_C{e_x:x>1/2})=H_theta.                      (5)
```

### Proof

Let `h in H_theta` be orthogonal to every `e_x` and define

```text
F_h(z)=sum_p w_theta(p) conjugate(h_p) p^(-z).           (6)
```

For `Re z>1/2`, Cauchy--Schwarz and `(2)` give absolute locally uniform convergence:

```text
sum_p |w_theta(p)conjugate(h_p)p^(-z)|
 <=||h||_(H_theta)
   (sum_p w_theta(p)p^(-2*Re z))^(1/2)<infinity.         (7)
```

Hence `F_h` is holomorphic there.  Orthogonality says `F_h(x)=0` for every real `x>1/2`, so the
identity theorem gives `F_h=0`.  Uniqueness of a Dirichlet series supported on the increasing prime
sequence forces every coefficient `w_theta(p)conjugate(h_p)` to vanish.  Since every weight is
strictly positive, `h=0`.  The orthogonal complement of the span is therefore zero, proving `(5)`.

The smaller family with `x>1` is still dense, since vanishing on that real interval again forces
`F_h=0`.  This is the convenient frame for seam values: it lies far enough inside the absolute
prime-series domain for every open-strip point.  The continuum is unnecessary.  The nodes

```text
x_n=1+1/n,  n>=1,                                       (8)
```

have an interior accumulation point at `1`, so the same proof gives

```text
closure(span_C{e_(x_n):n>=1})=H_theta.                   (9)
```

Thus one countable source frame works simultaneously for all positive convolution times.

## Exact value relation for the seam functional

Define the Meixner-weighted prime-zeta function on its absolute-convergence domain by

```text
P_theta(s)=sum_p w_theta(p)p^(-s),
M_theta(s)=-P_theta'(s)=sum_p w_theta(p)log(p)p^(-s).     (10)
```

For a strip point `rho`, the conjugate of the canonical prime seam is

```text
conjugate(C_p(rho))
 =log(p)(p^(-rho)-p^(-(1-conjugate(rho)))).              (11)
```

Consequently, for `x>1`, the absolutely convergent value of its Hilbert functional on the common
exponential vector is

```text
V_(theta,rho)(x)
 :=sum_p w_theta(p)conjugate(C_p(rho))p^(-x)
  =M_theta(x+rho)-M_theta(x+1-conjugate(rho)).            (12)
```

Indeed, `0<Re(rho)<1`, `theta>0`, and `x>1` put both arguments strictly inside the relevant
absolute-convergence half-planes.  Equation `(12)` then supplies the canonical analytic
continuation wherever the two weighted prime-zeta derivatives continue.

There is also an explicit ordinary-prime-zeta expansion.  Since

```text
w_theta(p)
 =2^(theta/2)p^(-theta)(1+p^(-4))^(-theta/2),            (13)
```

the binomial series gives, locally uniformly on an absolute-convergence half-plane,

```text
P_theta(s)
 =2^(theta/2) sum_(k>=0)
    (-1)^k (theta/2)_k/k! P(s+theta+4*k),                (14)
```

where `P` is the ordinary prime zeta function.  Differentiating `(14)` gives the corresponding
formula for `M_theta`.  Thus every entry in `(12)` is an explicit reflected value relation among
ordinary prime-zeta derivatives at an arithmetic progression of shifts; no Xi divisor sum or
limiting measure defines it.

## Finite Gram characterization

The Gram kernel of the common frame is

```text
G_theta(x,y)
 =<e_x,e_y>_(H_theta)
 =P_theta(x+y).                                          (15)
```

By the density of the subframe `x>1` and the Riesz representation theorem, the seam vector
`C(rho)=(C_p(rho))_p` belongs to `H_theta` if and only if there is a finite constant `B>=0` such
that for every finite family `x_1,...,x_N>1` and `c_1,...,c_N in C`,

```text
|sum_i c_i V_(theta,rho)(x_i)|^2
 <=B sum_(i,j) conjugate(c_i)c_j P_theta(x_i+x_j).       (16)
```

For the reverse implication, the bound first produces a Riesz vector `h in H_theta` with the
values `(12)`.  The Dirichlet series of the coefficient difference
`w_theta(p)(conjugate(C_p(rho))-conjugate(h_p))` converges for `Re x>1` and vanishes there.
Dirichlet-series uniqueness identifies every coefficient, so `h=C(rho)`; the bound has not merely
constructed an unrelated interpolant.  When `(16)` holds, the least possible `B` is exactly

```text
B_min=||C(rho)||_(H_theta)^2.                             (17)
```

It is enough to impose `(16)` only at the countable nodes `(8)`, because their span is dense.

This is the requested finite coefficient/value interface.  It does not assume a real-rooted
polynomial, an anti-Herglotz measure, or a chosen limiting distribution.  Every matrix entry is the
source value `(14)`, and the only infinite assertion is uniform boundedness of the finite Gram
quotients.

## Countable top-down RH chain

The root-scale theorem proves that, for an actual Xi divisor fibre,

```text
C(rho) in H_(1/m) for every m>=1
  -> Re(rho)=1/2.                                        (18)
```

Combining `(16)` and `(18)` gives the fully explicit source-value chain

```text
for every Xi divisor fibre rho and every m>=1,
  the countable values
    M_(1/m)(x_n+rho)-M_(1/m)(x_n+1-conjugate(rho))
  satisfy the finite Gram bounds (16)

  -> every Xi seam lies in every Gamma--Meixner root domain
  -> every horizontal charge vanishes
  -> xiHurwitzOrientationEnergy=0
  -> RH.                                                 (19)
```

The live research problem is now a value inequality: derive `(16)` from the completed
Euler--Gamma source or a relative trace.  Merely showing that each individual value in `(12)` is
finite is insufficient; one needs one bound compatible with all finite combinations at a fixed
`theta,rho`.

## Why the regular-Cauchy closure cannot be reused directly

Let

```text
R(t)=sum_(j=1)^N c_j/(z_j-t)                             (20)
```

be a nonzero finite regular-Cauchy packet with distinct nonreal nodes.  It is a nonzero proper
rational function, so for some integer `r>=1` and nonzero `A`,

```text
R(t)=A*t^(-r)+O(t^(-r-1))                               (21)
```

as `t->+infinity`.  Hence `|R(log p)|^2` is bounded above and below by positive multiples of
`(log p)^(-2*r)` for all large primes.  Equations `(2)` and the elementary comparison

```text
p^(1-theta)>(log p)^(2*r) eventually                    (22)
```

show that for `0<theta<1`,

```text
sum_p w_theta(p)|R(log p)|^2=infinity,                  (23)
```

because the tail dominates a positive multiple of `sum_p 1/p`.  At `theta=1`, the same series
converges by comparison with `sum_(n>=2)1/(n(log n)^2)`.  Therefore

```text
span{regular Cauchy packets} intersect H_theta={0},
  0<theta<1,                                             (24)
```

whereas the complete finite regular-Cauchy span lies in the time-one Gamma-damped domain.

This is a sharp phase transition, not a failure of density.  The positive successor is the common
prime-Laplace frame `(3)`--`(9)`.  Any attempt to descend the already-proved time-one Cauchy closure
must first perform a source-specific relative cancellation or unbounded deconvolution; ordinary
Hilbert interpolation cannot do it.

## Existing corpus contribution

- `PrimeLaplaceGramStrict.lean` already supplies resolved exponential prime-power features and
  strict positive Laplace Gram matrices for the von Mangoldt source.
- `GammaDampedPrimeLogCauchyDomain.lean` proves the time-one side of the Cauchy phase transition.
- `PrimeLogCauchySeamRank.lean` proves the undamped/transported non-summability mechanism for every
  nonzero finite Cauchy packet.
- `XiPrimeSeamEulerZeroTangent.lean` identifies `C_p(rho)` with the exact degree-one local Euler
  coefficient required in `(12)`.
- The new work is the common-root density theorem, the exact reflected value formula, and the
  finite Gram equivalence.

## Status and gates

- [x] construct one algebraic source core contained in every positive root domain
- [x] prove that core is dense in each root domain, including a countable common frame
- [x] identify every seam-frame value with an exact weighted prime-zeta reflection difference
- [x] reduce root-domain membership to finite source-value Gram inequalities
- [x] prove the regular-Cauchy phase transition and exclude direct downward interpolation of the
      existing closure theorem
- [x] formalize the ordinary-prime-zeta binomial expansion `(14)` and its differentiated
      prime-zeta-derivative companion
- [ ] derive the Gram bounds `(16)` from a completed Euler--Gamma value relation or relative trace
- [x] formalize the common frame, phase transition, and finite Gram consumer in Lean
- [x] formalize the countable top-down RH equivalence `(19)` without assuming RH
- [ ] RH

## Lean formalization

Completed 2026-08-23 in
`formal/GaloisForLFunctions/RHTower/MeixnerRootPrimeLaplaceValueFrame.lean`.

Key declarations:

- `isCompleteSystem_meixnerPrimeLaplaceFrame`: countable common-frame density for every
  nonnegative Meixner time;
- `inner_meixnerPrimeLaplaceFrame_eq_weightedPrimeZeta`: exact Gram kernel `(15)`;
- `meixnerWeightedPrimeZeta_eq_binomialPrimeZeta` and
  `primeSeamTransform_eq_binomialPrimeZetaDeriv`: exact absolutely convergent expansions `(14)`
  and its differentiated companion;
- `meixnerPrimeSeamValue_eq_reflected_transform`: exact reflected seam value `(12)`;
- `finiteValueGramBoundSq_iff_exists_riesz`,
  `summable_meixnerSeamEnergy_iff_exists_finiteGramBound`, and
  `isLeast_meixnerPrimeSeamFiniteGramBound`: finite Gram/Riesz criterion `(16)` and sharp least
  constant `(17)`;
- `riemannHypothesis_iff_meixnerPrimeSeamFiniteGramBounds`: unconditional countable RH
  equivalence `(19)`;
- `meixnerPrimeLogCauchyPacket_sharp_phaseTransition`: exclusion below time one and admission at
  time one.

Verification:

- `lake env lean GaloisForLFunctions/RHTower/MeixnerRootPrimeLaplaceValueFrame.lean` — passed;
- `lake build GaloisForLFunctions.RHTower.MeixnerRootPrimeLaplaceValueFrame` — passed;
- capstone `#print axioms` audit — only `propext`, `Classical.choice`, and `Quot.sound`;
- module imported by `GaloisForLFunctions/RHTower.lean`; umbrella build intentionally not run.

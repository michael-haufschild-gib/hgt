# Positive cubic amplification of the actual Gauss operator

- **ID:** gauss-positive-cubic-critical-mass
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / THEOREM (Lean)
- **Source:** rh-current-frontier-map.md · C1/CCM-FU propagated-iterate wall
- **Statement:** Every actual three-component Gauss quasi-inner block has eventually positive two-sided cubic Fourier diagonal bounded below by one quarter of its critical sampled energy; consequently its cubic diagonal partial sums diverge.

## Goal

Close the first genuinely open propagated depth, `m = 3`, without a triple-defect chain.  The
source operator is already a positive Gram operator.  Positivity converts its relatively controlled
first diagonal into a cubic lower bound by moment log-convexity.  This is source-pure and does not
assume divisor location, Weil positivity, or RH.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `tendsto_gaussCubeTwoSidedDiagonal_sum_atTop`; targeted module build passes; axiom audit has only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Fix `k : Fin 3`, prime `p`, and write `G` for the full actual Gauss quasi-inner block.  Let
`e_i` be the unit Fourier vector and

~~~
q_i = Re <e_i, G e_i>,
E_n = gaussComponentPrimeMagnitudeEnergy k p n.
~~~

The proof uses four already source-derived facts: the folded Gauss factorization, the relative
rank-one diagonal estimate, vanishing of its cofactor at both signs, and the exact critical
magnitude law `E_n ~ log(p)/(n+1)`.

## Paper proof

### Lemma 1: cubic moment amplification

Let `T` be a positive operator on a complex Hilbert space and let `x` be a unit vector.  Put

~~~
a = Re <x, T x>,
b = ||T x||^2,
c = Re <T x, T(T x)>.
~~~

Ordinary Cauchy--Schwarz gives `a^2 <= b`.  Cauchy--Schwarz for the positive semidefinite form
`B(u,v)=<T u,v>` gives `b^2 <= a c`.  Positivity gives `a,c >= 0`.  If `a=0`, then
`a^3 <= c`.  If `a>0`, then

~~~
a^4 <= b^2 <= a c,
~~~

and division by `a` gives `a^3 <= c`.  Symmetry of `T` identifies
`c = Re <x,T^3 x>`.  Therefore

~~~
(Re <x,T x>)^3 <= Re <x,T^3 x>.                 (1)
~~~

### Lemma 2: positivity of the actual Gauss block

For the unscaled block,

~~~
G0 = p B D B^(-2) D* B.
~~~

`B` and `B^(-2)` are real multiplication operators, `D*` is the Hilbert adjoint of `D`, and
`B^(-2)` has pointwise symbol `p^(x-1)>0`.  Hence for every `u`, with `w=D*Bu`,

~~~
<u,G0 u> = p <w,B^(-2)w> >= 0,
~~~

and the same folded identity with two inputs proves symmetry.  Thus `G0` is positive.  The full
block is `G = a_3^2 G0`, where `a_3=gaussArchScale 3>0`, so `G` is positive as well.

### Lemma 3: uniform floor for the moving amplitude

For `0 <= delta < 1` and `p>1`,

~~~
A_1(delta) = (1-delta)p^delta + delta p^(delta-1).
~~~

Since `p^delta >= 1` and `p^(delta-1) >= p^(-1)`,

~~~
A_1(delta) >= 1-delta + delta/p >= 1/p.          (2)
~~~

### Lemma 4: eventual first-diagonal floor

Let `sigma_i=p|d_i|^2`.  The established relative diagonal law says

~~~
|<e_i,G0 e_i> - sigma_i A_1(delta_i)| <= sigma_i F_i,
~~~

where `F_i>=0` and `F_i -> 0` along either escaping sign.  By (2), eventually at both
`i=+(n+1)` and `i=-(n+1)`,

~~~
Re <e_i,G0 e_i> >= sigma_i/(2p) = |d_i|^2/2.
~~~

Scaling gives

~~~
q_i >= a_3^2 |d_i|^2/2.                          (3)
~~~

### Theorem: actual cubic critical mass

Apply (1) to positive `G`, the unit vector `e_i`, and then (3):

~~~
Re <e_i,G^3 e_i> >= q_i^3
                  >= a_3^6 |d_i|^6/8.
~~~

The sampled-value bridge identifies `a_3^6|d_{n+1}|^6=E_n`, and reflection gives the same
magnitude at `-(n+1)`.  Adding both orientations yields, eventually,

~~~
E_n/4 <= Re(<e_(n+1),G^3 e_(n+1)> + <e_-(n+1),G^3 e_-(n+1)>).   (4)
~~~

Finally `E_n >= c/(n+1)` for some `c>0`, by the existing uniform critical-energy bound.
Summing (4) and comparing with the harmonic series proves that the real two-sided cubic diagonal
partial sums tend to `+infinity`.  This proves the statement.  `[PROVED HERE]`

## Hostile audit

- Absolute iterate convergence is insufficient after division by the critical scalar; this proof
  does not use it.
- First-vector convergence alone does not determine third moments for arbitrary self-adjoint
  operators; positivity supplies the missing log-convex inequality.
- The result is a one-sided critical residue, not the exact principal-model residue.  It therefore
  bypasses, but does not falsely claim, triple-defect asymptotics.
- Local positive divergence does not force Hodge-mass annihilation.  Remaining scientific premise
  is still the arithmetic global compressed-trace/anomalous-Ward identity identifying this source
  mass with the Weil/intersection trace whose boundary law kills it.
- Generic inequality (1) is classical.  Novel content is its coefficient-faithful application to
  the literal Gauss source operator, which closes the open `m=3` actual-operator lower-residue gate.

## Novelty audit

Internal search found no theorem applying positive moment amplification to the actual Gauss block;
existing files stop at the exact `m=2` residue and name depth-two defect propagation as open.
Recent CCM/Connes--Consani/Suzuki work audited for the frontier supplies semilocal or conjectural
global positivity, not this literal local operator theorem.  Classification: **new local source
theorem and route-compression bridge**, not an RH proof.

## Log

- 2026-08-11 — conjectured operator-power relative convergence; failed because normalized-step
  norms are not uniformly bounded.
- 2026-08-11 — pivoted to positive cubic moment amplification; paper proof closed.

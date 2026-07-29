# Deninger bilateral prime-angle moderation selector

- **ID:** `deninger-bilateral-prime-angle-moderation-selector`
- **Stage:** 1-in-progress
- **Type:** SOURCE-CATEGORY REFINEMENT / RH SELECTOR
- **Scientific status:** `[PAPER-PROVED BRIDGE] [CORPUS-NEW SYNTHESIS]`
  `[EXTERNAL NOVELTY UNVERIFIED] [SOURCE SEWING CONJECTURAL] [NOT RH]`
- **Parents:**
  - `deninger-poisson-mertens-boundary-jet-fracture.md`;
  - `deninger-mertens-adiabatic-exponential-corner.md`;
  - `adelic-high-shell-prime-dilation-purity-or-escape.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/prime-translation-koszul-off-unitary-contractibility.md`;
  - `high-shell-critical-hardy-conormal-uniformization.md`;
  - `zeta-source-effectivity-arithmetic-equivalence-principle.md`.
- **RH used:** no
- **Computation used:** no
- **Lean:** not authorized; the proved selector is parent distribution theory, while the
  arithmetic sewing theorem is open.

## 1. Why the third completion needs two different regularities

The adiabatic-corner theorem proves that the Euler-time boundary must retain:

```text
all h-jets at h=0
+ exponentially flat rates as epsilon_p=1/log(p) -> 0.
```

That forces a hyperfunction/enhanced-ind-sheaf type completion in the Euler-time variable.  It
does **not** follow that the transverse prime-angle variable should also be hyperfunctional.
Making both variables hyperfunctional admits every off-unitary prime character and destroys the
only spectral rigidity supplied by prime dilation.

The exact category predicted here is anisotropic:

```text
Euler/Poisson time:     hyperfunction or enhanced exponential object;
bilateral prime angle:  distribution / moderate boundary value.              (1)
```

The distinction is forced by the already-proved source formulas.  Every fixed Mertens logarithmic
grade has only polynomial Fourier growth in the prime angle, even though the collection of all
grades has infinite order in Euler time.

## 2. One-sided Hardy halves

Fix a rational prime `p`, put `L_p=log p`, and use the angular coordinate

```text
theta in R/(2 pi Z).
```

For `s in C`, define the critical half-density character

```text
lambda_p(s)=p^(1/2-s)
           =exp((1/2-s)L_p).                              (2)
```

Its modulus is

```text
|lambda_p(s)|=p^(1/2-Re(s)).                              (3)
```

If `Re(s)>1/2`, the positive Hardy half

```text
H_(p,s)^+(theta)
 =sum_(e>=0) lambda_p(s)^e exp(i e theta)                 (4)
```

is an honest Hardy vector.  Functional-equation reflection

```text
s#=1-conjugate(s)
```

satisfies

```text
lambda_p(s#)=1/conjugate(lambda_p(s)).                    (5)
```

After Schwarz conjugation and reversal of valuation orientation, the reflected Hardy half has
negative Fourier coefficients

```text
lambda_p(s)^e,     e<=0.                                 (6)
```

Thus the only coefficientwise bilateral sewing compatible with the prime clock and reflection is

```text
B_(p,s)(theta)
 =sum_(e in Z) lambda_p(s)^e exp(i e theta).             (7)
```

Equation `(7)` is initially a formal Laurent boundary value.  The question is its regularity.

## 3. Bilateral moderation theorem

For `k>=0`, include the complete logarithmic-jet grade

```text
B_(p,s,k)(theta)
 =sum_(e in Z) e^k lambda_p(s)^e exp(i e theta).         (8)
```

`[THEOREM] [BILATERAL_PRIME_ANGLE_MODERATION]`

For every prime `p`, complex `s`, and integer `k>=0`, the following are equivalent:

1. `(8)` is the Fourier series of a distribution on the circle;
2. its Fourier coefficients have polynomial two-sided growth;
3. `|lambda_p(s)|=1`;
4. `Re(s)=1/2`.

When these conditions hold, write

```text
s=1/2+i gamma.
```

Then `(8)` is, up to the Fourier-normalization scalar, the `k`-th angular derivative of the point
conormal at

```text
theta=gamma log p     mod 2 pi.                         (9)
```

If `Re(s)!=1/2`, `(8)` is only a formal bilateral exponential object on the fixed real circle; it
is neither a distribution nor a periodic hyperfunction there.  Indeed, with
`z=exp(i theta)`, multiplication by `z-lambda_p(s)` is invertible in every sheaf of analytic
boundary germs near the unit circle when `|lambda_p(s)|!=1`.  A nonzero solution of
`(z-lambda_p(s))B=0` therefore cannot exist in ordinary hyperfunctions or analytic functionals on
that circle.  The formal series can be retained only after enlarging the base to a moving complex
annulus or an enhanced exponential/Stokes object which records the off-circle support.

### Proof

A Fourier series on the circle represents a distribution exactly when its coefficients have
polynomial growth.  The coefficient in `(8)` has modulus

```text
|e|^k |lambda_p(s)|^e.                                  (10)
```

If `|lambda_p(s)|>1`, `(10)` grows exponentially as `e->+infinity`.  If
`|lambda_p(s)|<1`, it grows exponentially as `e->-infinity`.  Hence polynomial two-sided growth
is possible exactly when `|lambda_p(s)|=1`.  Equation `(3)` makes this equivalent to
`Re(s)=1/2`.

On the critical line,

```text
lambda_p(s)^e=exp(-i e gamma log p),
```

so `(7)` is the Fourier series of the point conormal `(9)`.  Multiplication of the coefficients
by `e^k` is angular differentiation, proving the final assertion.

No zeta value, zero, functional equation for Xi, or positivity premise is used.

### Finite-packet and all-prime corollary

For a nonempty finite prime set `P`, put

```text
B_(P,s)(theta)
 =sum_(e in Z^P)
    exp((1/2-s) sum_(p in P)e_p log p)
    exp(i sum_(p in P)e_p theta_p).                     (10a)
```

Then `(10a)` is a distribution on the finite prime torus exactly when
`Re(s)=1/2`.  Indeed, restriction to any coordinate axis is the one-prime theorem, while on the
critical line all coefficients are bounded.  At `s=1/2+i gamma`, it is the point conormal at

```text
(theta_p)_(p in P)=(gamma log p mod 2 pi)_(p in P).     (10b)
```

The point conormals `(10b)` are compatible under every prime-forgetting projection.  They
therefore define the Dirac measure at the prime-log Kronecker point in the full product torus.
Consequently the moderation selector has no finite-packet or countable-product loss: an off-line
character already fails on every one-prime marginal, while a critical character has a coherent
all-prime distributional realization.

## 4. Compatibility with the complete Mertens jet

The source-curved Deninger kernel is

```text
K_p(h,e)=p^(-he).                                       (11)
```

Its `r`-th Euler-time boundary derivative is

```text
partial_h^r K_p(0,e)=(-e log p)^r.                      (12)
```

For each fixed `r`, `(12)` is polynomial in the bilateral Fourier grade `e`, hence gives a
finite-order circle distribution after critical sewing.  Therefore the complete Mertens jet does
not require hyperfunction growth in prime angle:

```text
infinite order in h
  is compatible with
finite distribution order in theta at every graded h-symbol.                (13)
```

This removes a false category dilemma.  One may retain every Mertens grade through an
Euler-time hyperfunction or Rees object while retaining spectral moderation in every prime-angle
grade.

For an off-line character, the positive and reflected one-sided halves separately exist in their
natural one-sided chambers, but they do not sew to any ordinary hyperfunction on the fixed prime
circle.  Their only common carrier is a moving-annulus or enhanced exponential object, and its
off-circle displacement is exactly `Re(s)-1/2`.

## 5. Relation to the adelic purity-or-escape theorem

The finite-adelic prime-dilation theorem uses the self-adjoint contraction

```text
K_p=(U_p+U_p^*)/2
```

and character

```text
kappa_p(s)=cosh((s-1/2)log p).
```

It needs a bounded Xi conormal functional to invoke Hilbert-space spectral purity.  The present
theorem needs less: a nonzero **distributional** bilateral eigencharacter already lies on the
unitary prime spectrum.

Equivalently, multiplication by

```text
exp(i theta)-lambda_p(s)
```

is invertible on circle distributions when `|lambda_p(s)|!=1`, because its reciprocal is smooth.
Thus every distributional Koszul class with that off-unitary character vanishes.  This is the
distributional form of the existing Neumann/Koszul contraction, but it remains valid with an
arbitrary hyperfunction or enhanced coefficient in the independent Euler-time variable.

The improvement is categorical, not an RH proof:

```text
old sufficient attachment:  nonzero bounded Hilbert conormal;
new sufficient attachment:  nonzero moderate bilateral distributional conormal.              (14)
```

## 6. RH-bearing source conjecture

`[CONJECTURE] [ARITHMETIC_MODERATE_BILATERAL_SEWING]`

The enhanced Euler--Gamma/Tate--Milnor/Calderon source comparison from
`deninger-mertens-adiabatic-exponential-corner.md` has a source-defined moderate boundary functor
with these properties:

1. **Pre-divisor definition.**  It is constructed from the positive prime-power source, Gaussian
   real-place kernel, Gamma transgression, Poisson summation, and prime-orbit orientations before
   a zero is selected.
2. **Two chiral restrictions.**  Its positive and negative prime-angle restrictions are the two
   Hardy halves `(4)` and `(6)`.
3. **Bilateral moderation.**  Their functional-equation sewing lands in circle distributions,
   grade by grade in the complete Euler-time/Mertens filtration, not merely in periodic
   hyperfunctions.
4. **Conormal conservativity.**  At every Xi zero `rho` and every nonzero multiplicity grade, the
   sewn class is nonzero and has prime character `lambda_p(rho)` for at least one ordinary prime
   `p`.
5. **Gauge sensitivity.**  Centered rational-quartet and generalized-prime surgeries that create
   off-line zeros fail clause 3 or clause 4; the construction does not factor through functional
   equation, positive Euler coefficients, or bare hypertranscendence alone.

If this conjecture holds, every Xi zero `rho` produces a nonzero distribution
`B_(p,rho,k)`.  The bilateral moderation theorem forces

```text
Re(rho)=1/2,
```

so RH follows.

The conjecture is not promoted as a theorem.  Clauses 3--4 are the source-effectivity content.

## 7. Why this is sharper than the previous completion target

The adiabatic-corner card correctly asks for moderate/rapid nearby cycles but does not specify
which regularity carries the RH selector.  The present theorem fixes that ambiguity:

```text
moderate in the bilateral prime angle
  <=> critical half-density character.                  (15)
```

Therefore the next construction should not first seek a positive Hilbert norm or a Green-form
inequality.  It should compute the enhanced comparison's angle-direction moderate boundary and
test whether the two chiral Euler--Gamma conormal values sew there.  Positivity becomes relevant
after this support/regularity theorem, not as a replacement for it.

This also explains the third completion's apparent contradiction:

- ordinary positive-time Hardy spaces retain right-half characters but are one-sided;
- bilateral adelic `L2` restores unitarity but loses all point fibres;
- the mixed completion retains point conormals as distributions on the unitary prime-angle
  boundary while using Euler-time hyperfunctions to retain every logarithmic and exponential
  grade.

## 8. Hostile audit

1. **Functional equation alone does not give moderation.**  It supplies the reflected half and
   the formal coefficient sewing `(7)`, but an off-line pair lives only in a moving-annulus or
   enhanced exponential category, not in periodic hyperfunctions on the fixed real circle.
2. **One-sided distributionality is useless.**  For `Re(s)>1/2`, `(4)` is smoother than a
   distribution.  The selector appears only after the negative Fourier grades are retained.
3. **A hyperfunction in both variables is too large.**  It admits `(7)` at every strip point and
   makes `(15)` false.
4. **Finite jets do not prove RH.**  Every fixed `h`-jet is moderate once the prime character is
   on the unit circle, but no finite jet constructs the bilateral source sewing.
5. **No zero-selected topology.**  Declaring the class moderate at a listed zero is exactly the
   desired conclusion.  Moderation must follow from the global completed source comparison.
6. **No generalized-prime overclaim.**  The known explicit off-line positive Euler systems can
   retain one-sided Hardy data and hyperfunction sewing.  They falsify any version replacing
   clause 3 by positivity, functional equation, entire completion, or hypertranscendence.
7. **No hidden Hilbert eigenvector.**  The target class may be a delta derivative, not an `L2`
   vector.  Ambient continuous spectrum is therefore compatible with the desired critical-line
   fibre.
8. **Potential circularity remains.**  If the only proof of clause 3 expands the Xi divisor and
   discards exponentially growing off-line coefficients, the route is a re-encoding of RH.

## 9. Smallest next theorem

For one finite prime packet, lift the already-constructed Tate--Milnor/Calderon exponential
intersection to the real oriented adiabatic blow-up and compute its two prime-angle boundary
restrictions.  The required finite theorem is a no-cohomology calculation:

```text
finite Euler gauge
  -> completed positive Hardy restriction
     and reflected negative Hardy restriction
  -> exact transition/Stokes cocycle and zero divisor cohomology.              (16)
```

The multiplier ideal must remain present during the calculation.  Since every finite Euler factor
is invertible, any finite-packet divisor class would be an error.  After `(16)`, form the strict
all-prime enhanced source object before specialization and prove that the cofinal gauge
trivializations fail strictly while their connection converges to the completed logarithmic Green
current.  The first possible nonzero class is this strict all-prime defect.  The RH-bearing theorem
is that its full Xi principal conormal, including multiplicity jets, survives in the fixed-circle
moderate boundary.  If the strict limit remains exact, the route is dead; if it is nonexact but its
class lives only in the moving-annulus exponential sector, the moderation selector does not apply.

## 10. Literature boundary

The characterization of circle distributions by polynomial Fourier-coefficient growth is
standard distribution theory.  Analytic boundary germs are locally invertible under multiplication
by a holomorphic function nonvanishing on the real circle; therefore an off-unitary formal
eigencharacter requires a moving complex support or enhanced exponential object rather than an
ordinary periodic hyperfunction.  Deninger's arithmetic periodic orbits and Hepler--Hohl
moderate/rapid nearby cycles of enhanced ind-sheaves are external parents.

Targeted searches found no work combining:

```text
Deninger prime-orbit Poisson time
+ complete Mertens boundary jets
+ FE-sewn bilateral half-density characters
+ moderate angle boundary as an RH selector.            (17)
```

Search noncollision is not a priority certificate.  The proved theorem in Section 3 is a bridge,
not new distribution theory.  Potentially new mathematical content begins with the arithmetic
source sewing `(16)` and its strict countable-prime compatibility.

Primary external parents:

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  `arXiv:1807.06400`;
- Brian Hepler and Andreas Hohl, *Moderate Growth and Rapid Decay Nearby Cycles via Enhanced
  Ind-Sheaves*, `arXiv:2206.06095`.

## Gates

- [x] distinguish Euler-time hyperfunction regularity from prime-angle moderation
- [x] derive the two reflected Hardy halves and their unique bilateral coefficient sewing
- [x] prove the bilateral distribution criterion
- [x] identify every fixed Mertens grade with a delta-derivative grade on the critical line
- [x] recover the off-unitary Koszul contraction in distributional form
- [x] state the source sewing theorem before proof design
- [x] run initial corpus collision and external-parent audits
- [ ] independently audit Fourier and reflection conventions
- [ ] compute the finite-packet exact transition/Stokes cocycle and verify zero divisor cohomology
- [ ] construct the strict all-prime gauge defect before specialization
- [ ] prove its bilateral moderate realization modulo the completed Xi multiplier ideal
- [ ] prove conormal conservativity
- [ ] pass to the strict countable-prime Ind-limit
- [ ] derive RH
- [ ] formalize only after a dependency-closed arithmetic source theorem exists

## Log

- 2026-07-29 — Rejected ordinary Fredholm/K-theory index as a new mechanism after collision with
  the zero-index prime co-shift complex and the existing boundary-index specification.  Replaced
  bounded-Hilbert conormal attachment by a weaker anisotropic target: hyperfunction in Euler time,
  distribution in bilateral prime angle.  Proved that FE-sewn prime coefficients are moderate
  exactly on the critical line, and isolated arithmetic moderate bilateral sewing as the
  source-effectivity theorem.
- 2026-07-29 — Hostile correction: an off-unitary formal bilateral eigencharacter is not a
  hyperfunction on the fixed prime circle, since its analytic multiplier is invertible near that
  circle.  It requires moving-annulus/enhanced support.  Also replaced the impossible finite-packet
  Xi sewing target: finite Euler gauges are exact, so only the strict all-prime gauge defect can
  carry divisor cohomology.

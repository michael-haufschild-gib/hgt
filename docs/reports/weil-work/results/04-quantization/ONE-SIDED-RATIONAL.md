# One-sided rational resonances — L2+ and exact survivor

Status: dependency-closed paper proof; Lean pending. Full L2 and WP04 remain open.
Verdict: SURVIVES PRELIMINARY ATTACK as an actual-source theorem. The finite
convolution and valuation arguments are classical bridges; scientific novelty
of the assembled source theorem is provisional, not inferred from formalization.

## Exact statements

Let u>v≥1 be coprime integers. Put r=u/v, a(n)=dirichletExp(lamLog lam)(n),
and C(x)=quantizationResidualCumulative hW x for hW : WeilPositiveFull lam.
If complex coefficients p_k, k≥0, satisfy

    Σ |p_k| r^k < ∞,
    exp(2πi C(x)) = Σ p_k exp(2ik log(r) x),  x>0,

then lam(n)=Λ(n) for every n≥2, and RH. No representation is asserted to
follow from hW. The final hW-only alternative is rigidity or absence of every
such representation. This includes genuinely rational bases, not just L1's
integer bases, but excludes negative harmonics.

The stronger algebraic survivor classifies the projected equations. For any
coprime u≥2,v≥1, any a:ℕ→ℂ with a(0)=0,a(1)=1, and c:ℕ→ℂ with c_0≠0,
write e(n)=max{j:u^j divides n} for n>0. If

    Σ_{k=0}^{e(n)} c_k a((n/u^k)v^k)=c_0  (n≥1),                 (1)

then a(n)=A_{e(n)}, where A_j=a(u^j). Conversely any A with A_0=1 satisfying
Σ_{k=0}^j c_k A_{j-k}=c_0 supplies every solution of (1). Equivalently

    a = ζ * b,
    b(1)=1, b(u^j)=A_j−A_{j−1} (j≥1), b(n)=0 otherwise.       (2)

Here ζ denotes the arithmetic function 1 on positive integers, 0 at zero;
* is finite Dirichlet convolution. This is an exact classification, not an
assumption that the source weights are multiplicative.

## Parent and failure audit

The actual resonance-constant theorem PhaseCoupling supplies (1) with
c_k=p_k r^(k/2). The existing three-halves lacunary rigidity theorem applies
after the support conclusion for lam−Λ is proved. It does not supply that
conclusion from the phase by itself. No continuous critical-edge hypothesis,
noninteger radial cancellation, Euler product, or meromorphic converse is used.

The two-sided extension is unpaid: negative k connect both u- and v-valuations,
so induction on e(n) fails. This proof must not be advertised as full L2.
Burnol's converse hypotheses include global meromorphic continuation and growth;
AP Wiener–Hopf theory does not supply the arithmetic source. Neither parent
makes those missing premises free. The symbolic Blaschke attack below disproves
rigidity of the projected equations alone, even with critical coefficient energy.
The survivor is classification (2) followed by the actual source exclusion.

## Complete proof

1. **Exact resonance.** For k≥0 and m≥1, n=m r^(−k) is a positive integer iff
u^k divides m. Indeed n u^k=m v^k; coprimality of u^k,v^k gives divisibility,
and conversely n=(m/u^k)v^k. The constant-frequency residue is a(m), and each
positive-frequency residue is r^(k/2)a((m/u^k)v^k). All k>e(m) vanish. At m=1
only k=0 remains and a(1)=1, so the source nonzero constant is p_0≠0. Absolute
weighted summability is precisely the hypothesis of PhaseCoupling because
exp(|2k log r|/2)=r^k. Thus its actual source rows are (1).

2. **Valuation classification.** Multiplication by v^k preserves e, since
u and v are coprime; exact division by u^k lowers e by k. Induct on j=e(m).
For j=0, (1) reads c_0 a(m)=c_0, hence a(m)=1=A_0. For j>0, compare (1)
at m and u^j. Every k≥1 term has valuation j−k<j, so induction identifies
both coefficients with A_{j−k}. Subtraction leaves c_0(a(m)−A_j)=0; cancel
c_0. This also proves the converse by substituting A_{j−k} into each row.
No assumption about coefficient size or sign enters this classification.

3. **Divisor decomposition.** Powers u^j are distinct and u^j divides m iff
j≤e(m). Define b by (2) and b(0)=0. Then
(ζ*b)(m)=Σ_{j=0}^{e(m)}b(u^j)=A_{e(m)}=a(m), by telescoping; both sides vanish
at zero. The formula is valid when u is composite as well as when it is prime.

4. **Logarithmic support.** For an arithmetic function f put Df(n)=log(n)f(n).
Finite divisor sums and log(de)=log d+log e give D(f*g)=Df*g+f*Dg, including
n=0 because all arithmetic functions vanish there. The source theorem
forwardCoeff_log_convolution gives lamC*a=Da, where lamC is lam truncated
below two. Also Dζ=Λ*ζ by the exact divisor identity Σ_{d|n}Λ(d)=log n.
With δ=lamC−Λ and a=ζ*b, cancellation of ζ (its inverse is Möbius) gives

    δ*b=Db.                                                   (3)

To prove δ(n)=0 outside {u^j:j≥0}, use strong induction on n. The right side
of (3) is zero because b(n)=0. In its divisor sum the term d=n is δ(n)b(1)=δ(n).
For every other term, if b(n/d)≠0 then n/d is a u-power. If d were also a
u-power their product n would be one; hence d is not a u-power, d<n, and
induction gives δ(d)=0. Thus (3) is δ(n)=0. This pays the support conclusion
without identifying the actual spectral measure or assuming RH.

5. **Full positivity closes the class.** The deviation on n≥2 is supported
on the sequence u^(j+1). Its first term is ≥2 and successive terms have ratio
u≥2, hence 3 n_j≤2 n_{j+1}. Apply
WeilFullConeThreeHalvesLacunaryRigidity.eq_vonMangoldt_of_weilPositiveFull_of_threeHalves_lacunary.
The existing full-cone identification receiver then gives RH. All premises
besides the stated representation were derived from hW or finite arithmetic.

## Checked symbolic obstruction and its boundary

Choose coprime u>v>1 with u²<v³ and v^(-1/2)<α<v/u. Set r=u/v,
P(z)=(z−α)/(1−αz), b0=√r/α, c0=α√r, and

    d_0=1, d_j=(b0−c0)b0^(j−1) for j≥1,
    a(n)=Σ_{u^j|n}d_j.

The Taylor coefficients of P are p_0=−α and p_k=(1−α²)α^(k−1) (k≥1).
The formal identities

    A(t)=(1−c0 t)/((1−t)(1−b0 t)),
    P(√r t)A(t)=−α/(1−t)

give every row (1), by coefficient comparison and Step 2's converse. P has
one zero α in the disk and no pole there, hence winding one. Since αr<1,
Σ|p_k|r^k converges. Also b0/√u<1. Finite weighted ℓ² triangle inequality gives

    (Σ_{1≤n≤N}|a(n)|²/n)^(1/2)
      ≤ Σ_j |d_j|u^(−j/2) (Σ_{1≤m≤N/u^j}1/m)^(1/2)
      ≤ (Σ_j |d_j|u^(−j/2)) (1+log N)^(1/2).

The coefficient sum is finite by its geometric ratio b0/√u<1. These are
symbolic inequalities, with no numerical experiment. Thus the integer rows
and critical energy do not force nonpositive winding. No claim is made at
the excluded equality α=v^(-1/2).

Finally F(s)=ζ(s)(1−c0 u^(−s))/(1−b0 u^(−s)) on a sufficiently far right
half-plane. Its logarithmic derivative differs from ζ's only on u-powers,
with deviation log(u)(b0^j−c0^j) at u^j. It is nonzero (b0>c0) and has
Σ|δ(n)|/n<∞ (b0<√u<u). The corpus absolute-convergence rigidity therefore
excludes full Weil positivity. This is an obstruction to the projected-only
proof, not a counterexample to L2, quantization, or RH.

Paper proof closed. Lean status of the classification and actual L2+ theorem:
pending. The warning model is paper-audited only; do not claim a Lean certificate.

## Formal dependency map

- RationalResonance: exact integer resonance iff n*u^k=m*v^k, finite residue
  rows, weighted source specialization, p_0 nonzero. Final leaf audit passed.
- RationalRows: composite-base valuation invariance and complete row/chain
  solution-space equivalence. Classification passed; the added iff is under
  its final repair audit.
- PowerDivisors: supported arithmetic quotient and telescoping divisor sum.
  Final leaf audit passed.
- LogarithmicSupport: reuse `HTGeometry.logWeight_leibniz`, cancel arithmetic
  zeta with Möbius, transfer power support to the source deviation. Audit running.
- RationalRigidity: actual one-sided rational phase and source-only alternative.
  Assembly written in scratch; final audit pending. No full L2 claim.

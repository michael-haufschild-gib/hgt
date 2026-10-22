# BAG complete rational-dilation orthogonality

- **ID:** BAG-C28.56ab, exact rational statements formalized.
- **Route:** BAG arithmetic-to-physical cubic bridge.
- **Prior progress:** C28.56aa closes the complete compact-test arithmetic
  boundary. It does not prove rational reindexing or physical transfer.

## Conjecture and corpus basis

For sigma>1 let m_sigma(a)=mu(den(a))/prod_(p|den(a))(p^sigma-1),
for a positive rational a. Prove an absolutely convergent identity

    sum_(a positive rational) m_sigma(a)*m_sigma(a*b)*a^(-sigma)
       = if b=1 then zeta(sigma)^2 else 0.

The complete cubic trace already has all local valuation pairs and an
explicit convergent absolute Euler product. Its paper card exposes the
stronger fixed-dilation identity; it is not yet a checked global sum.
PMPowerDampedMobiusRamanujanWeights identifies the actual denominator
coefficient. The corpus search for rational reindexing was nonpartial,
inventory65483/65483; unrelated matrix eigenbasis reindexing and Hecke lifts
do not establish the needed identity.

## Proof mechanism to formalize

For z=p^(-sigma), c(i)=1 for i>=0, c(-1)=-z/(1-z), c(i)=0 otherwise.
For j>0 the exact local dilation row is

    c(i)c(i+j)z^i = geometric(z,i) - (1-z)^(-1)*atom(-1,i).

Its sum is zero and its absolute mass is 2/(1-z). At j=0 its sum is
(1-z)^(-2). Negative j follows by an exact integer translation with
factor z^(-j). No cancellation is inferred from the cubic row after
division by c(j), since that coefficient can vanish.

Finite-prime products give the exact local-to-global partial sums. Promote
to one unconditional sum over finitely supported prime valuations by
bounding arbitrary finite subsums inside their union of prime supports.
Absolute Euler-product convergence supplies the uniform mass bound;
dominated convergence over support cutoffs identifies the full sum.
Finally identify the finite-support prime lattice with positive rationals
and its coefficient with the literal normalized Ramanujan denominator.
The same exhaustion proves the positive-rational double-sum reindexing.

Physical prime contraction matching and finite-height near-resonances still
need separate proofs. In particular arithmetic a=1 is not automatically
the discrete p=r diagonal, and this exact-resonance identity does not
justify a coupled damping/band limit. RH remains open.


## Checked lattice stage

Production ChiRamanujanFinsuppTrace now passes direct foreground audit47237
with no diagnostics. Local dilation cancellation is proved for every integer
shift, including negative shifts by exact translation. A support-exhaustion
Euler theorem bounds each finite subsum inside the union of its supports;
Tannery then identifies the full unconditional sum. Applied to the actual
cubic, it proves one full-lattice HasSum and its exact absolute mass.

The actual square-energy sum is zeta(sigma)^2. For a fixed lattice dilation j,
the absolute row is bounded by energy(v)+weight(j)^(-1)*energy(v+j).
Translation preserves summability. Every finite-prime row containing the
support of nonzero j is zero by one local zero factor; exhaustion therefore
proves the unconditional full-lattice orthogonality, valuationDilation_hasSum.

This is mathematical progress beyond directed partial traces. The rational
reindexing is still being built: explicit prime-product map, inverse from
numerator/denominator factorizations, and identification with the literal
Ramanujan denominator coefficient. No physical contraction match is claimed.

Second corpus search (finite support Euler sum) was nonpartial, inventory
65483/65483; all candidate/source/proof/ingredient sections inspected. Existing
natural-number Euler products and finite geometric models do not by themselves
supply the integer prime-lattice exhaustion; it was proved directly.


## Rational coefficient identification: paper proof

The explicit map v |-> product_p p^(v_p) is positive and injective: applying
the p-adic rational valuation recovers each coordinate. For a positive reduced
rational q=n/d, the inverse is factorization(n)-factorization(d), with natural
exponents cast to integers and restricted to primes. Natural factorization
reconstruction proves surjectivity and multiplication corresponds to addition.

Coprimality implies that at each denominator prime the numerator valuation is
zero. Away from denominator primes the remaining nonnegative coefficient is
one. Hence the source coefficient depends only on -factorization(d). At each
prime power p^k with k>0, its factor is exactly mu(p^k)/(p^sigma-1): the k=1
case is the corpus coefficient_primeWeight_neg_one identity; every k>1 gives
zero on both sides. The corpus multiplicative-factorization theorem for mu
therefore gives mu(d)/product_(p|d)(p^sigma-1), the literal normalized
Ramanujan weight. Positive real power laws identify the prime weight with
q^(-sigma). These are algebraic identities, not asymptotic assumptions.

The positive-rational equivalence stage has checked in scratch; the literal
coefficient and real-power identifications are currently being checked.
Their production/axiom audits remain pending. The intended final theorem
transports the already-audited full-lattice orthogonality through this explicit
equivalence, with no conditional summability premise.


## Literal rational orthogonality checked

Production ChiRamanujanPositiveRationalTrace passes direct foreground
audit84654, no diagnostics. rationalDilation_hasSum is now the stated
positive-rational identity with the literal mu(den)/RamanujanDenominator
coefficient, not a renamed prime-lattice coefficient. Its absolute
summability is separately proved. rationalRamanujanCoefficient_source links
it exactly to pmPowerDampedRamanujanWeight divided by the corpus density.

The complete rational cubic and literal two-axis mask are now transported
through an explicit pair equivalence. This uses the proved full lattice
absolute mass, not an unproved iterated-sum interchange. Production95789
passed, as did all52 public-theorem axiom queries91107 (only standard logical
axioms). Three leaves wired. Exact statement and dependency-closed proof:
P3 bag-complete-rational-cubic-orthogonality.md. Index/lint evidence goes in
the working log. No physical prime-diagonal claim is made.

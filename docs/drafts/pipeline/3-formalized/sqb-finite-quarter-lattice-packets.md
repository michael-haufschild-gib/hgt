# Complete finite quarter-lattice Eisenstein packet admission

Status: dependency-closed paper proof and complete Lean audit passed. RH remains open. Frontier map is read-only.

## Exact result and occurrence consequence

For an actual Xi zero copy rho, put

    u_j = (rho−1)/2 + j/4,                 j in Z,
    P_J(z) = sum_{j in J} w_j E*(z,1/2+u_j),

where J is any finite set, weights are arbitrary complex numbers, and E* is
the original complete scalar Eisenstein field. Then

    P_J belongs to native cusp L²  iff  every w_j, j in J, is zero.

This includes critical Xi copies. Every shifted Casimir has the same full
entire-transform value F((rho/2)(1−rho/2)); that scalar equality does not
produce native spectral occurrence.

The theorem retains both original Weyl terms and every Fourier mode. The
native norm is exactly the unit-width cusp integral above height two with
density dx dy/y². No critical-line hypothesis, numerical evidence, extra
axiom, or asserted occurrence enters the proof.

There is also an exact obstruction to native-norm resummation. For any
admitted candidate v, the native error P_J−v is L² iff all finite packet
weights vanish. For a sequence of varying finite supports and weights,
eventually L² errors against v force eventually zero weights. Thus a
nonzero locally defined resummation cannot inherit the entire-operator
equation by ordinary native-norm completion of these literal partial sums.

## Positive survivor: exact finite Mellin admission

For distinct complex exponents a_i and arbitrary complex coefficients c_i,

    G(t) = sum_i c_i exp(a_i t)

belongs to L²(0,infinity) iff every nonzero c_i has Re(a_i)<0. This includes
oscillatory ties of real parts and the threshold Re(a_i)=0.

Proof: discard zero coefficients and choose k with maximal real exponent.
Normalizing by exp(−a_k t) gives a finite exponential polynomial with
nonpositive real exponents and constant term c_k. The existing exact
window-mean law gives, for every T>=0,

    | integral_0^T exp(−a_k t)G(t)dt − T c_k | <= K,

where K is finite and independent of T. If Re(a_k)>=0 and the energy
prefixes of G are bounded by M, the normalized packet has the same energy
upper bound. The weighted path-energy theorem with constant weight one
then gives

    | integral_0^T exp(−a_k t)G(t)dt |² <= T M.

For c_k nonzero, take T larger than both 2K/|c_k| and 4M/|c_k|². The two
bounds contradict each other. Maximality therefore forces all active
exponents to have strictly negative real part. Conversely, every active
mode is square integrable and finite sums preserve L².

The literal substitution y=exp(log(2)+t) transports the necessary condition
to the half-density y^(−1/2)G(log y) above the actual cusp cutoff. Every
finite interval and its Jacobian are retained; its squared norm density is
exactly |G(log y)|²/y.

## Application to the complete original source

The shifted field has principal part

    Lambda(2u_j) y^(1/2−u_j) + Lambda(1+2u_j) y^(1/2+u_j).

After including the native half-density, its two relative exponents are
−u_j and +u_j. Since Im(rho) is nonzero, the two branches have opposite
nonzero imaginary parts. Distinct integers separate exponents within each
branch. Consequently all exponents in the finite principal packet are
distinct.

Each complete Fourier tail is native L² by the existing arbitrary-weight
tail theorem. Finite sums preserve this admission, so subtracting the
complete tail from an assumed admitted full packet gives an admitted
principal packet. Product-measure preservation by the height coordinate
then transfers its norm to the one-dimensional Mellin test above.

Fix a nonzero weight w_j. If Re(u_j)>=0, the incoming coefficient
Lambda(1+2u_j) is nonzero by Gamma nonvanishing and the proved zeta zero-free
closed right half-plane. Its relative exponent +u_j has nonnegative real
part. If Re(u_j)<0, functional reflection makes Lambda(2u_j) nonzero, while
the outgoing exponent −u_j has positive real part. Both cases contradict
the exact finite Mellin admission condition. Therefore all weights vanish.
Zero weights trivially give the zero admitted packet, completing the iff.

## Scope of the remaining hardest obstacle

Full proof chain: original Xi/modular source → independent full-Xi entire
spectral occurrence → real-spectrum classification → critical-line
placement → RH.

Independent occurrence remains unproved. This theorem excludes finite
complete quarter-lattice packets and their native-norm completion as its
producer. It does not exclude a weaker locally convergent resummation or
families with spatial cutoffs and changing coefficients. Either proposal
must independently establish a nonzero admitted source, its actual entire
operator domain, and its zero normalized full-Xi residual. A formal
termwise Casimir identity supplies none of these steps.

## Lean surface and audit

- `SelbergFiniteMellinPacket.lean`: exact finite exponential L² criterion,
  coefficient extraction and literal native Mellin transport.
- `SelbergScatteringFiniteQuarterPacket.lean`: complete original-source
  admission iff all weights vanish, exact error criterion, eventual error
  obstruction, and the shared scalar entire-transform value.

Source checks used `lake env lean <file>`. Final audits use only the two
named module targets, with preflight checks; no umbrella build is run.
Both source checks and final leaf builds passed. Preflights identified only
the named leaf as needing compilation after removing an unused import;
no dependency or umbrella build was launched. All 31 public declarations
were audited with `#print axioms` in `/tmp/sqb23_axioms.lean`: only `propext`,
`Classical.choice`, and `Quot.sound` occur. No added axiom, proof hole or
computational certificate occurs. Each declaration is indexed exactly once,
each module is wired once into `RHTower.lean`, whitespace checks passed,
and `scripts/formal_tools.py lint` passed with existing large-file warnings.

Local audit artifacts: `/tmp/sqb23_mellin_source.log`,
`/tmp/sqb23_quarter_source.log`, `/tmp/sqb23_mellin_preflight.log`,
`/tmp/sqb23_quarter_preflight.log`, `/tmp/sqb23_mellin_build.log`,
`/tmp/sqb23_quarter_build.log`, `/tmp/sqb23_axioms.log`,
`/tmp/sqb23_indexed_declarations.json`, `/tmp/sqb23_index.log`, and
`/tmp/sqb23_lint.log`. All owned Lean/Lake processes reached terminal exit.

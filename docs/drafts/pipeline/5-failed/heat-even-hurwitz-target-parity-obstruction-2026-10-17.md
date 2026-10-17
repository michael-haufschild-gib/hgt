# Raw even heat vectors cannot approximate the original Hurwitz witness

Status: dependency-closed paper proof and final Lean audits complete.

## Exact obstruction

Let R be functional-equation reflection on exact Xi multiplicity copies,
z the centered spectral coordinate, and u the canonical Hurwitz orientation
vector. The source formula gives
`u(rho)=-sin(2*pi*Re rho)/|rho-1/2|`, so u(Rq)=-u(q). Every Gaussian vector
depending only on z_q^2 is R-even, as is its linear span and Hilbert closure.
For any R-even vector v, reindexing the Hilbert inner product through R gives
`<u,v>=-<u,v>=0`. Hence

`||u-v||^2 = E + ||v||^2`,

where E is the Hurwitz orientation energy. The distance to the entire even
space is exactly sqrt(E), attained by v=0. Thus approximation of this
particular target by an even heat core would already force E=0, equivalently RH.

## Strongest positive survivor

This obstruction concerns the chosen target, not the adequacy of FE-even
tests for RH. The source height gap gives |Re z_q|>4. Deninger's orientation
epsilon_q is therefore sign(Re z_q), real with square one. It reverses
under R and is fixed by critical-line reflection J, because J sends z to
conj(z). Multiplication Dv(q)=epsilon_q*v(q) is an involutive complex-linear
isometry that commutes with J and exchanges the two R-parity sectors.

For arbitrary Hilbert vectors v,w,
`<J Dv,Dw>=<Jv,w>`. Thus every Weil Gram entry and sign survives this parity
exchange. In particular Du is FE-even, has norm squared E, and has Weil
square exactly -E. Positivity at Du is equivalent to RH. The complete Weil
positivity requirements on FE-even and FE-odd vectors are equivalent.

This supplies an exact energy-preserving replacement target. It does not
show the source sign or claim that the discontinuous orientation multiplier
has already been realized by an arithmetic test-function operation.

## Positive survivor: explicit signed-heat construction

The replacement target now has a uniform spectral heat construction. Put
`a_N(z)=z/sqrt(pi) * integral_[-N,N] exp(-z^2*t^2) dt` and
`A_N v(q)=a_N(z_q)v(q)`. The complex Gaussian integral gives
`a_infinity(z_q)=sign(Re z_q)=epsilon_q`. The actual source gap and sector
bound imply `Re(z_q^2)>=2` and `|z_q|^2<=2 Re(z_q^2)`. Outside [-N,N],
split off `exp(-N^2)` and integrate the remaining Gaussian with coefficient
`Re(z_q^2)/2`; this proves `||A_N-D||<=2 exp(-N^2)`.

Each multiplier is odd under z -> -z, so `A_N u` is FE-even and converges
in norm to Du. Continuity of the Weil form gives `Q(A_N u)->-E`. Off RH,
these finite-time witnesses are eventually strictly negative; their eventual
nonnegativity is equivalent to RH. This establishes an explicit spectral
heat operation, with no claim of arithmetic source positivity.

The dependency-closed paper proof and Lean proofs are complete in
`ComplexSignedGaussianHeat.lean`, `XiSignedHeatOrientation.lean`, and
`XiSignedHeatOrientationConvergence.lean`. All three narrow builds and final
per-file Lean checks passed without module warnings. All 34 declarations
have only `propext`, `Classical.choice`, and `Quot.sound` in their axiom
closure. This is contribution 4 in the parent research card.

## Formalization

- `RHTower/XiWeilFunctionalEquationParity.lean`: Hilbert orientation
  isometry, involution, reflection commutation, full Weil preservation,
  parity exchange, and equivalence of sector positivity.
- `RHTower/XiHurwitzFunctionalEquationEvenWitness.lean`: FE-odd original
  witness, FE-even replacement, exact energy, RH criteria, orthogonality,
  and sharp approximation law.

Parents are actual corpus theorems: Deninger orientation, unconditional Xi
height gap, exact reflection operators, and the Hurwitz orientation source
formula. No zero-location, positivity, or simplicity premise remains in the
construction. Both narrow `:olean` builds and final individual
`lake env lean` audits passed without warnings. All 24 public declarations
have only `propext`, `Classical.choice`, and `Quot.sound` in their axiom
closure. Imports and index refresh passed. Repository lint exited 1 on 26
unrelated unreachable modules; neither module in this contribution has a
lint error.

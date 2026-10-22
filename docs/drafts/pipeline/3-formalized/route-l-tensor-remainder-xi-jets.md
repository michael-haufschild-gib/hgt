# Route L: the complete Gamma-six tensor remainder retains Xi jets

Date: 2026-09-11.
Status: formalized; all 22 theorem axiom audits, targeted module build and formal lint passed. RH remains unproved.
Module: `GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixTensorRemainderXiJets`.

## Positive result

C21 requires a bounded prime-cyclic comparison to kill the leading tensor
image. C22 showed that its one-factor tail still carries every Xi divisor's
first nonzero internal jet. C23 reaches the complete tensor remainder in
the original product-measure Hilbert space.

Let `a_m=6^(-m/2)`, `H_k` be the physical internally promoted theta source,
and `T_(k,6,m)` its complete strict arithmetic tail. Define before any
spectral or divisor selection

`S_(k,m)=a_m*(H_k+T_(k,6,m))`, `P_(k,m)=a_m*H_k`,

`R_(k,l,m)=S_(k,m) tensor S_(l,m)-P_(k,m) tensor P_(l,m)`.

At internal orders `(0,0)` this is exactly the existing
`deningerGammaSixSourceTensorRemainder`; neither source nor tensor carrier
has been replaced. The full remainder includes leading--tail,
tail--leading and tail--tail. Each term is separately absolutely admitted
in the product-measure Fourier--Laplace integral.

For `|Im(w)|,|Im(z)|<1` and the actual depth convergence bounds
`1/m<Re(1/2+i*w),Re(1/2+i*z)`, that literal integral equals

`a_m^2*(M_6(m,w)*M_6(m,z)-1)*XiC^(k)(w)*XiC^(l)(z)`.

The physical `2*pi` coordinate occurs in both factor phases and in the
representative bridge. The square of the forced half-density remains in
the answer.

## Nonzero divisor data and normalization

On the diagonal, the complete remainder multiplier is

`C_m(w)=M_6(m,w)^2-1=(M_6(m,w)-1)*(M_6(m,w)+1)`.

For every `Re(1/2+i*w)>0`, `M_6` tends to `mu(6)=1`. C22 proves that its
strict-tail difference is eventually nonzero. The second factor tends to
`2`, so `C_m(w)` is eventually nonzero although it tends to zero. No
nonvanishing assumption is supplied.

For each actual Xi divisor of multiplicity `q`, specialize the already
constructed source family to the two adjacent order pairs `(q-1,q)` and
`(q,q)`. Their evaluations form

`(0,a_m^2*C_m(w)*[XiC^(q)(w)]^2)`,

with nonzero second entry at every sufficiently large depth. This is an
internal source-jet statement; the internal moments are inserted before
translation, rather than silently differentiating the entire multiplier.

Let `r` be the first integer greater than six with nonzero Möbius
coefficient and `N_m(w)=(r/6)^(m*(1/2+i*w))`. Exact successor transport gives

`N_m(w)*C_m(w) -> 2*mu(r)`.

Removing the known half-density from the *actual tensor integral* and
applying the same source-derived scale therefore gives

`N_m(w)*a_m^(-2)*FL(R_(k,l,m))(w,w)
  -> 2*mu(r)*XiC^(k)(w)*XiC^(l)(w)`.

Its multiplicity-top value is nonzero. These depth-dependent factors are
singular; they are not a fixed physical reader.

## Dependency-closed proof

1. Identify the normalized physical theta-jet representative with its
   rescaled theta-cusp integrand almost everywhere. The previously proved
   strip integrability and literal change of variables give its admitted
   complex integral and exact Xi derivative.
2. Use C22's complete Hilbert-tail representative and integrability, with
   the same change of variables, to admit the tail's physical integral.
3. Addition and scalar multiplication are passed through actual L2
   representatives almost everywhere. They give admitted factor integrals
   `a_m*M_6*XiC^(k)` and `a_m*XiC^(k)`.
4. The existing separated-product representative identifies the tensor
   integrand with a product of admitted factor integrands. Product
   integrability and Fubini yield the product of their integrals. Apply
   this also to each of the three cross contributions, then subtract the
   admitted principal tensor to obtain the complete two-variable formula.
5. Factor the diagonal multiplier. C22 gives the first factor's eventual
   nonvanishing; convergence to two gives the second's. Apply the existing
   Xi multiplicity vanishing/nonvanishing theorem only after step 4.
6. Multiply C22's exact successor-normalized tail limit by `M_6+1` to get
   `2*mu(r)`. Cancel the proved nonzero half-density in the actual integral
   identity and use its eventual convergence domain to obtain the stated
   normalized integral limit.

## Remaining hard obstacle

Leading-image removal does not erase the complete tensor remainder's
conormal data. The positive survivor is the actual admitted tensor source,
its full two-variable integral, every multiplicity-top coefficient and
its forced singular normalization.

No source-to-Sonin map, all-prime cyclicity, fixed-reader agreement,
horizontal-anchor annihilation or RH theorem follows here. A proposed
comparison must now account for this complete surviving tensor data, not
only its leading image or its Hilbert norm. The exact physical-reader
comparison remains open.

## Searches and external method checks

Two deep searches examined product-measure remainder evaluation and
Mellin/tensor contraction mechanisms. Both reported partial source/compiler
coverage: 706108 ready and 779 stale method records. Applicable retrieved
sources included the actual Gamma-six remainder decomposition and
`integral_prod_mul`; both were read and checked in Lean. The convolution
search retrieved an admitted Mellin product theorem, which requires its
factor convergence and measurable representatives. It does not identify
this tensor with a Sonin quotient reader. Its use is deferred to a concrete
source-domain comparison; no such map is assumed.

Broad arXiv terms were `polarization`, `scattering` and `correlation`, with
June--September 2026 preference. The [September 1 scattering paper](https://arxiv.org/html/2609.00985v1)
separates subenergy discontinuities and uses explicit crossing/analyticity
and an inhomogeneous integral equation to obtain three-body unitarity
(Section IV). These are source-specific requirements, not arithmetic
comparison hypotheses supplied here. The [September 8 unequal-mass paper](https://arxiv.org/html/2609.09282v1)
adds an Omnès restriction on an otherwise uncontrolled discontinuity to
recover numerical bounds (Section 6); that extra restriction gives no
unconditional RH input. No numerical experiment was performed for this
work.

## Verification

- `lake env lean /tmp/route_l_tensor_remainder.lean`: all 22 theorems passed without warnings.
- `lake build GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixTensorRemainderXiJets`: passed.
- `lake env lean /tmp/route_l_tensor_remainder_axioms.lean`: all 22 theorems use only `propext`, `Classical.choice`, and `Quot.sound`; no added axioms.
- `scripts/formal_tools.py lint`: passed with existing file-size warnings.
- Umbrella import wired; no full or umbrella build.

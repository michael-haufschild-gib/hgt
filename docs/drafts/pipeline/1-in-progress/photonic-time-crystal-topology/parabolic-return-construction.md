# Parabolic temporal transport and its return defects

**Status:** derived construction `[BRIDGE]`, with a paper derivation below and a Lean certificate for its transfer, series, analytic-reduction, and flux statements. This is not a proof of RH. The proposed observable includes a Laplace–Mellin transformation of the return history. It is not an assertion that an ordinary transmission experiment already measures this transformation. No numerical experiments are used.

## Physical starting point

The starting primitive is a periodic temporal Maxwell system and all repetitions of its physical cell. The [PTC geometry paper](https://arxiv.org/abs/2511.17317) identifies its two-mode monodromy with a disk isometry. A noncentral parabolic monodromy is a band-edge degeneracy: it has a repeated multiplier but only one eigenline. The sign of that multiplier is lost on passing to the projective disk, so the linear lift must be retained.

Use dimensionless units with fixed nonzero spatial momentum and permeability equal to one. In a constant-permittivity slab, the displacement equation is

\[
D''+\omega^2D=0,\qquad \omega=\epsilon^{-1/2}.
\]

In the state coordinates `(D,D')`, a slab of phase advance `θ` has transport

\[
A_\omega(\theta)=
\begin{pmatrix}\cos\theta&\sin\theta/\omega\\
-\omega\sin\theta&\cos\theta\end{pmatrix}.
\]

This follows by differentiating the displayed sine–cosine solutions and evaluating their initial data. At the ideal switches used here, `D` and `D'` are continuous: Maxwell gives `D'` proportional to the magnetic field for the fixed nonzero momentum and constant permeability. The zero-momentum degeneracy of these state coordinates is therefore avoided.

Choose `θ=arctan(4/3)`, so `cos θ=3/5`, `sin θ=4/5`. A binary cell with permittivities `1` and `1/16`, and durations `θ` and `θ/4`, has the exact monodromy

\[
M=A_4(\theta)A_1(\theta)
=\begin{pmatrix}1/5&3/5\\-12/5&-11/5\end{pmatrix}.
\]

Its determinant is one, its trace is `−2`, and `M+I` is nonzero with square zero. All values specifying this cell are independent of zeta and its zeros. Passing to its physical two-cell cover gives

\[
P=M^2=I+N,
\qquad N=\begin{pmatrix}-12/5&-6/5\\24/5&12/5\end{pmatrix},
\qquad N^2=0.
\]

Thus this is a nontrivial modulated medium, not a constant medium with identity transport. This realization is an exact ideal-model derivation; no claim about dispersion, loss, or experimental fabrication is included.

It is also a genuine crossing when spatial momentum varies with the medium and durations fixed. The one-cell trace is `2−(25/4)sin²(kθ)`, whose derivative at `k=1` is `−6θ<0`. Thus a stable band and a momentum gap meet at this parabolic point.

## Derive the family from return history

An impulse followed for `n` two-cells has state `P^n v`. Induction using `N²=0` gives

\[
P^n=I+nN.
\]

For positive dimensionless damping `u`, the Laplace-weighted return history is

\[
G(u)=\sum_{n\ge1}e^{-nu}P^n
=\frac{1}{e^u-1}I+\frac{e^u}{(e^u-1)^2}N.
\]

Both sums converge absolutely because their entries are bounded by a constant times `(1+n)e^{-nu}`. The scalar formulas follow from the geometric series and its derivative. Equivalently, `G(u)=e^{-u}P(I-e^{-u}P)^{-1}`; this is the resolvent of the discrete return map, with the zero-return term removed.

Now take its normalized Mellin transform:

\[
\mathcal R(s)=\frac{1}{\Gamma(s)}\int_0^\infty u^{s-1}G(u)\,du,
\qquad\Re s>2.
\]

The Mellin parameter is the complex scaling exponent of the damping variable. It is not spatial momentum, laboratory time, or quasifrequency. Absolute interchange is justified entrywise by
`∑(1+n)∫₀∞u^{σ−1}e^{-nu}du = Γ(σ)∑(n^{-σ}+n^{1−σ}) < ∞` for `σ>2`. Substitution `v=nu` in each integral then proves

\[
\boxed{\mathcal R(s)=\sum_{n\ge1}n^{-s}P^n
=\zeta(s)I+\zeta(s-1)N.}
\]

The right side supplies the unique meromorphic continuation from that half-plane. The full matrix has an additional pole at `s=2` in its nilpotent part, even though its determinant does not. No convergence of the original undamped series inside the critical strip is asserted.

**Meaning for the route:** zeta is produced by an explicit repeated-cell response, with the nontrivial photonic extension retained. The Mellin analysis is an added, specified operation on physical histories. Establishing it as a preferred geometric observable remains a separate task; calling it bare band topology would overstate the derivation.

## What its zeros are

Let `S={s:0<Re s<1}`. On this strip, the two coefficients are holomorphic, and `b(s)=ζ(s−1)` never vanishes. To see the latter without RH, put `w=s−1`, so `−1<Re w<0`. In the ordinary functional equation for `ζ(w)`, the factor `ζ(1−w)` lies in `Re(1−w)>1` and is nonzero by its Euler product. The gamma and exponential factors are nonzero, and the sine factor vanishes only at even real integers, none in this strip.

In the constant basis `v=(1,−2)`, `w=(0,−5/6)`, one has `Nv=0`, `Nw=v`. Therefore

\[
\mathcal R(s)\sim
\begin{pmatrix}a(s)&b(s)\\0&a(s)\end{pmatrix},
\qquad a(s)=\zeta(s),\quad b(s)=\zeta(s-1).
\]

In particular,

\[
\det\mathcal R(s)=\zeta(s)^2.
\]

This turns the nontrivial zeros into **failures of invertibility of the continued return response**. They are not band-edge locations as a function of momentum, temporal-interface bound states, or isolated exceptional points of this matrix family. The two eigenvalues of this family coincide everywhere; a zeta zero is where the common eigenvalue vanishes.

There is a stronger description than the determinant identity. Since `b` is an analytic unit on `S`, analytic invertible row and column operations reduce this matrix to

\[
\begin{pmatrix}1&0\\0&a(s)^2\end{pmatrix}.
\]

Proof: swap the columns, giving `[[b,a],[a,0]]`; subtract `a/b` times row one from row two; subtract `a/b` times column one from column two; then multiply the rows by `b⁻¹` and `−b`. Each operation is invertible throughout `S`.

Consequently the cokernel sheaf of the return map is

\[
\operatorname{coker}\mathcal R\simeq\mathcal O_S/(\zeta^2).
\]

At a zero of multiplicity `m`, the local torsion length is `2m`, while the kernel and cokernel of the matrix evaluated at that point each have dimension one. Equivalently, the winding of its nonzero determinant along a small positively oriented loop is `2m`. The nilpotent extension joins the two diagonal channels into one cyclic torsion module; replacing the full system by two independent scalar copies would lose this information.

The two-term complex `[V → V]` used in this cokernel description has differential `𝓡(s)`. It is a newly constructed return-response complex. It is not being identified with the usual cellular complex `[V → V]` with differential `P−I` for a flat bundle on the temporal circle.

## Independence from period grouping

For any positive integer `m`, the `m`-fold cover of the two-cell transport has `P^m=I+mN`, so its response is `ζ(s)I+mζ(s−1)N`. Its determinant remains `ζ(s)^2`; the preceding analytic reduction and local torsion lengths are unchanged. If dimensional return times rather than cell counts are used, a further factor `(mT)^{-s}` multiplies the response. It is everywhere nonzero and does not change the divisor.

The primitive binary cell has `M=−I+K`, where `K=M+I` and `K²=0`. Its ungrouped response is instead

\[
\sum_{n\ge1}n^{-s}M^n
=-\eta(s)I+\eta(s-1)K,
\qquad\eta(s)=(1-2^{1-s})\zeta(s).
\]

Its determinant is `η(s)^2`. The factor `1−2^{1−s}` has zeros only on `Re s=1`, and the analogous factor in `η(s−1)` only on `Re s=2`. Thus on `S` the same local torsion description holds up to analytic units. Passing to a two-cell cover removes a sign-dependent Euler factor, without creating or removing nontrivial zeros in the open strip.

**Meaning for the route:** the nontrivial defect divisor survives a genuine ambiguity of temporal-cell choice. This is more useful than choosing a cell convention merely to write down zeta.

## Critical line: the construction still owes a duality

The canonical parabolic filtration is `0 ⊂ ker N = im N ⊂ V`. Transport on both one-dimensional graded quotients is the identity for `P` and minus the identity for the primitive `M`. Hence the period circle and its Fourier lattice are attached to the system's actual graded flat bundle, rather than an unrelated arithmetic operator.

On the normalized untwisted temporal circle, its standard quadratic heat trace is
`Θ(u)=∑_{n∈Z}exp(−πn²u)`. Fourier duality gives `Θ(u)=u^{-1/2}Θ(1/u)`. Its Mellin transform, with constant mode removed, gives `π^{-s/2}Γ(s/2)ζ(s)` for `Re s>1`. Splitting the integral at one and applying that transformation to the lower interval gives the convergent continuation formula

\[
\Lambda(s)=-\frac1s-\frac1{1-s}
+\int_1^\infty\frac{\Theta(u)-1}{2}
\left(u^{s/2}+u^{(1-s)/2}\right)\frac{du}{u}.
\]

The integral is entire by Gaussian decay, locally uniformly in `s`. The displayed expression proves `Λ(s)=Λ(1−s)`. Thus `ξ(s)=s(s−1)Λ(s)/2` is entire and reflection invariant. Conjugation gives the antilinear involution `s↦1−conj(s)`, whose fixed locus is `Re s=1/2`.

On `S`, multiplying `𝓡(s)` by the analytic nonvanishing factor `s(s−1)π^{-s/2}Γ(s/2)/2` therefore makes its determinant `ξ(s)^2` without changing its defects.

This is an exact **spectral-geometric completion** using a clock metric and the graded bundle. It does not yet prove that temporal Maxwell evolution selects this heat operator, completion, or duality on the full return complex. The heat variable and damping variable are different variables. Their transforms recover the same scalar Dirichlet series in overlapping domains; that agreement alone is not a physical identification of their kernels.

## Attack on the proposed confinement mechanism

The preserved flux in `(D,D')` coordinates is represented, up to a nonzero real convention factor, by

\[
J=\begin{pmatrix}0&-i\\i&0\end{pmatrix}.
\]

Real determinant-one slab matrices preserve this Hermitian form. At every return defect, `ker 𝓡=im 𝓡=L=C(1,−2)`. For all `x,y∈L`, `x*Jy=0`. Hence the flux restricted to the defect line is identically zero. It cannot supply a positive norm on those modes or exclude off-line support by positivity.

The positive survivor is exact: `L=L^{⊥_J}`, so flux induces a nondegenerate sesquilinear pairing

\[
L\times(V/L)\longrightarrow\mathbb C.
\]

It is well-defined because `L` is isotropic. It is nondegenerate because the annihilator of `L` in `V` is exactly `L` and `J` is nondegenerate. This pairs the kernel and cokernel; it does not identify either with a positive Hilbert space.

**Meaning for the whole route:** this model does create a candidate topological object carrying exactly the nontrivial zero divisor, while its native flux supplies duality between cohomological degrees rather than positivity within a degree. The hard problem is now the construction and sign of an additional, source-derived structure on the return family. Flux conservation alone does not solve it.

## Exact research claim and remaining work

Within the specified Laplace–Mellin response and spectral completion, RH is equivalent to:

> The return-response torsion of this parabolic temporal crystal is supported on the fixed locus of Fourier–Mellin conjugate duality in the nontrivial strip.

This is a proposed **reframing with an explicit ideal medium and an explicit response**, not a proof of its confinement statement. The analytic identities used are classical. Searches have not established priority for this PTC interpretation; no novelty claim is made. The construction was selected with its proof visible, so the scientific-method classification is `[BRIDGE]`, not a primary universal conjecture.

Next attacks are specific: establish the functorial relation between physical temporal-cover transport and this analytic return complex; derive a duality acting on that full complex; determine whether a nondegenerate sign structure exists despite the null flux line.

The module `RHTower/PhotonicParabolicReturn.lean` certifies the rational slab product, basis intertwining for every cover, convergent return series, analytic reduction with unit determinants, RH equivalence, defect kernel, and flux annihilator. Its targeted build passed. The Maxwell ODE, Laplace–Mellin integral interchange, sheaf/winding interpretation, cell-regrouping comparison, and full physical duality are not formalized by that certificate. The first four have paper arguments above; the full physical duality remains open.

One immediate regularity test cannot be skipped: detuning momentum away from a parabolic edge and continuing the Mellin order need not commute. The scalar Jonquière expansion contains a singular power of the Floquet phase and a regular zeta coefficient. In the critical strip the singular power does not disappear in the neutral-holonomy limit. Therefore the response defined by continuation at the exact parabolic cell must not be described as the unrenormalized continuous limit of neighboring band responses. The next geometric identification must specify its full singular subtraction and prove compatibility with physical detuning.

## Sources and corpus discrimination

- [Original PTC topology](https://arxiv.org/abs/1803.08731): distinct band holonomy and temporal-interface problem.
- [PTC disk geometry](https://arxiv.org/abs/2511.17317): physical parabolic monodromy; no arithmetic quotient is inferred.
- [NIST polylogarithms](https://dlmf.nist.gov/25.12): classical winding sums and boundary continuation.
- [NIST theta transformation](https://dlmf.nist.gov/20.7.E32) and [zeta reflection](https://dlmf.nist.gov/25.4): spectral completion identities.
- Corpus `RHTower/JonquiereExpansion.lean` distinguishes the singular Floquet-holonomy germ from its regular zeta coefficient. It supports seeking a return object, not equating a Berry phase with a zero.
- Deep searches for matrix polylogarithms and nilpotent return powers found existing nilpotent/unipotent algebra, but no verified theorem identifying this Maxwell return family with its analytic torsion. Search coverage is partial and compiler applicability remains unchecked.
- [Driven-qubit experiment](https://arxiv.org/abs/1903.07819) uses designed drives to read Riemann zeros. Its abstract supplies a novelty warning, not a derivation of the present topology.

# FZZ-P research facts

- RH chain: source-fixed integrated mixed Ward cancellation → zero momentum → torus passivity → Mellin completeness → RH.
- First plane mark: exact zero set is chart line `y=0` (`fzzScreeningPlaneMarkedMoment_first_eq_zero_iff`).
- Cubic cutoff/jet: closed; marked finite part is `-141π/8`, ratio `47/224`.
- Reflected/paired radial mixed receiver: zero iff momentum is zero.
- Compact opposite-winding mixed response: `C(k)L`, with `C(k)<0`, and ranges over all reals as separation moves.
- New kill: momentum-fitted separation yields one Ward cancellation at every momentum; cannot select critical wall.
- Full depth-one annular Hessian: `C(k)(L+μ(-e^u))+k²V(-e^u)` (contact + connected radial fluctuation).
- Full depth-one response has both signs and one neutral geometry at every level; no universal Ward orientation comes from this factor alone.
- HJ prescription excludes reflected radial wave. For physical one-sided receiver,
  `2 Re ψ′(1+iq)=q⁻²-π²/sinh²(πq)>0` (`q≠0`), with `Re ψ′(1)>0`.
- New kill: one-sided radial mixed derivative has strictly negative imaginary part at every momentum;
  no real compact Hessian can satisfy vanishing Ward identity, including at zero momentum.
- One-sided real component is odd under momentum reflection and vanishes iff momentum is zero.
- New kill: for nonzero momentum, no single complex compact response—regardless of phase—can cancel
  both reflected one-sided receivers. Exact existence classification: common cancellation iff momentum is zero.
- Positive survivor: orientation-dependent cancelling compact responses must obey
  `C(-p)=-conj(C(p))`; conjugate-even/common response is impossible off the wall.
- Vacuum anchor `C₀=-D(0)` is target-independent; cancellation of `D(p)+C₀` and `D(-p)+C₀` is equivalent
  to `p=0` (formalized). Setting `p=Re ρ-1/2` gives the direct Mellin-completeness/RH chain.
- Survivor/open core: prove literal fractional/all-depth compact source response equals vacuum anchor,
  retaining physical normalization and cross-charge weighting. Required imaginary part is strictly positive.
- [L] FZZ-P premise = dyadic clock pencil bound: canonical-twist area response `R(ρ)=3/4+(‖2^{ρ−½}‖²+‖2^{(1−ρ̄)−½}‖²)/8`; divisor passivity ⟺ every window's Cesàro energy of `Σ m_ρ 2^{n(ρ−½)}` bounded (`FZZParityAreaResponseDyadicClockBridge`). Physical layer adds nothing beyond the prime-2 clock; producer = bound on zero-indexed dyadic pencil (explicit-formula form: single-base lag, open only in non-attained regime).
- [L] Literal parity source has non-passive modes: `Γ(s)(1−2^{1−s})ζ(s)=0` at `1+2πik/log 2` (k≠0), area response `17/16` (`FZZParityDyadicNonPassiveModes`). Uniform source-mode passivity is false; producer must be strip-restricted. [P] every finite dilation regularization of the Bose delay has spurious modes near Re s=1; the spurious-free subtraction B(t)−1/t is the Nyman–Beurling sawtooth.
- PM-7 (paper): PM source completeness = outer-function property of `Γ(s)(1−2^{1−s})ζ(s)` on `Re s>½` modulo the explicit Blaschke factor at `1+2πik/log 2`; ⟺ RH; physical inverse (blackbody/Fermi) problem = Möbius inversion ⇒ PM ≡ MC.
- PM-8 (no-go): Putnam-type exact-progression exclusion cannot reach PM-2's sparse approximate dyadic combs (generic on the line by equidistribution of `γ log 2/2π`); Bohr mean along `s₀+2πik/log 2` excludes only positive-density exact combs.
- [L] PM-9: FZZ-P divisor-selective Hermitian identity made explicit (`FermiNymanBeurlingDyadicWitness`): witnesses of the alternating NB system = spurious dyadic self-similar `t^{−2πik/log 2}` ∪ zero witnesses `t^{ρ̄−1}`; class is dyadically invariant; `q(w)=∫_0^{1/2}|w|²−½∫_0^1|w|² ≡ 0` on witnesses ⟹ RH; self-similar ⟹ RH; FZZ response `=3/4+(m+m⁻¹)/8`, `m` = witness mass fraction.
- [L] PM-11: Haar target `h = −1_{(0,½]} + 1_{(½,1]}` has Mellin pairing `(1−2^{1−s})/s`: kills spurious witnesses exactly, sees all strip zeros; approximation floor `(2β−1)|1−2^{1−ρ}|²/|ρ|²`; `h` approximable by alternating generators ⟹ RH (`FermiNymanBeurlingHaarTarget`). Physical problem = Báez-Duarte with weight `|1−2^{1−s}|² ∈ [(√2−1)²,(√2+1)²]` on the line.
- [L] PM-12: witness class is a vector space; spurious/zero cross term `(2^{−ρ}−½)/(s̄_k+ρ−1) ≠ 0` ⟹ off-line zero makes `q` indefinite; `q ≥ 0` on witnesses (dyadic dilation non-contracting) ⟹ RH; generators are `−1_{⌊1/(at)⌋ odd}`: witnesses = zero integral on every dilate of `E₁ = {⌊1/t⌋ odd}` (`FermiNymanBeurlingWitnessSignature`).
- [L] PM-13: `L^p` ladder — all `L^p` witnesses self-similar ⟹ no zero with `1−1/p < Re ρ < 1`; p=2 RH, p=∞ PNT endpoint ([P] bounded witnesses are self-similar via Mellin + PL + `1/ζ(1+it)=O(log t)`). Physical identity = PNT on `L^∞`, RH on `L²`; gap = exponent `1/p` from 0 to ½.
- [L] PM-14: bounded witnesses of the alternating NB system are dyadically self-similar, unconditionally (`IsBoundedFermiWitness.selfSimilar`; entire `U(z)=2^z(V−∫_{½}^1)` of growth `(1+|z|)^{11}` from `ZetaInvBnd`/`ZetaInvBound2`/`ZetaZeroFree`, Liouville, Fourier uniqueness). Sharp w.r.t. known input: any `p<∞` version is a zero-free half-plane.
- [L] PM-15: sharp unconditional boundary — witnesses of Mellin exponent 0 are self-similar (`IsMellinFermiWitness.selfSimilar`); growth by maximum modulus between Titchmarsh IX.7 heights, no zero-free region needed. Exponent `a>0` ⟺ zero-free half-plane.
- [L] PM-16: `RH ↔ every continuous L² witness of the alternating NB system is dyadically self-similar` (`riemannHypothesis_iff_fermiNymanWitness_selfSimilar`), also `↔` half-mass identity and `↔ q ≥ 0`. RH enters the converse only as pole-freeness of `V_w` on `Re z<½`; critical-line removability is automatic from the L² rate.

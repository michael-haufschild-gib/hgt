## Exact ordinate coincidence.
RH is ordinate injectivity. The collision charge has a full quantum of margin (<2) and a two-prime arithmetic form. The claim is that exact coincidence, unlike closeness, is detected without the one-log loss.

### Statement to prove

RH ⟺ the collision charge K(T) = Σ_{|Im ρ|≤T} ord_ρ·(H(Im ρ) − ord_ρ) satisfies K(T) < 2 for all T. Here H(t) is the total multiplicity on the slice Im s = t, and K is even-valued [L] (xi §4.A.16).

The claim: the source-side form holds. The two-prime Cesàro excess built from the χ₂, χ₃ carriers is eventually < 2 ([L] ⟺ RH; endpoint family F0237). The proof would be an exact identity between the thin-slice pair current of ξ and that arithmetic excess, followed by a bound that is uniform in height.

### Ledger evidence

- **RH is ordinate injectivity.**
  - Each slice Im s = t is finite and stable under the reflection. Its fixed part has at most one point. A zero alone on its slice is critical [L].
  - Slice count = [ξ(½+it) = 0] + 2·(number of free orbits).
  - RH ⟺ distinct zeros have distinct ordinates (xi §3.2, §4.A.16; MUST-401, MUST-403, MUST-404).
- **This target has never been attempted.** The ledger separates excluding a small displacement (resolution), where every method stops one log short, from excluding an exact coincidence of two ordinates. The latter is a scale-insensitive transversality condition "never attempted" (CANNOT-402).
- **The integer is analytic and needs no zero enumeration.** The collision charge is the cutoff-independent thin-slice limit of the pair Poincaré–Lelong current of ξ [L] (xi §4.A.28). Thin-strip contours are invariant under every finite exponential Euler gauge [L] (xi §8.16).
- **The margin is a full quantum.** Unlike the slack-free endpoints (Λ=0), any bound strictly below 2 suffices. F0237 lists several such sub-quantum source forms:
  - two-prime Cesàro excess < 2;
  - prime Cayley information loss < 2 (xi §4.A.21);
  - Ward–Green Cayley reflection energy < 32;
  - exterior packet energy below 4(96/145)².
- **Two prime clocks separate ordinates; one does not.** γ ↦ (2^{2iγ}, 3^{2iγ}) is injective, while one clock aliases ordinates modulo 2π/log p [L] (xi §2.6). Pointwise, β = ½ ⟺ p^{ρ−½} + p^{½−ρ} is real for p = 2 and p = 3 [P] (xi §4.A.14).
- **Discrete means detect exact coincidence at every scale.**
  - A Cesàro mean over the two-prime lattice {k log 2 + l log 3} of e^{i(γ−γ')(k log 2 + l log 3)} is 1 if γ = γ' and 0 otherwise. The alternative, (γ−γ')log 2 and (γ−γ')log 3 both in 2πℤ, is impossible for γ ≠ γ'.
  - So an exact coincidence is weighed fully whatever the displacement δ, while distinct ordinates, however close, average out.
  - Absolutely continuous clocks erase every nonzero prime-log character (F190), so the detector must be discrete, as this one is.
- **The problem is local.** The far field costs one log, and it enters only as a normalization (MUST-457). The pair field is bounded by one-sided fields at the two zeros (MUST-446, MUST-447). Everything reduces to the at most 40 log(180|t|) zeros within distance 1 of the slice [L] (xi §3.3).

### Program

1. **Decisive first check (cheap).** From the Lean definition behind the two-prime Cesàro carrier, determine the excess's unconditional growth over a height window. If it is of the order of the Cauchy-weighted local density, C·log T, the route stops (CANNOT-437; xi §2.21, LocalCountBound).
2. **Two-variable explicit formula.**
   - Express the thin-slice pair current (pairs at equal ordinate, real shift h ∈ (0,1)) through prime sums on the lattice log 2·ℤ + log 3·ℤ, plus archimedean and near-field terms.
   - The lag function is already decided on this lattice [L]: RH ⟺ Φ(k log p + l log q) is bounded above (xi §4.A.3).
3. **Near field at an absolute constant.**
   - This is where every earlier attempt stopped (CANNOT-437).
   - The claim to establish: in the Cesàro limit only exact same-ordinate pairs survive. The ~log T near zeros at distinct ordinates then contribute 0 rather than O(log T), and the log never appears.
   - Inputs: MUST-446, MUST-447 and MUST-457.
4. **Close.** An excess below 2 gives K < 2 and hence RH.
5. **Deformation audit.** Both deformations must violate a named step:
   - the quartet gauge P·ξ, which keeps FE, order one and hypertranscendence (xi §7.1);
   - ζ(s)²(1−2^{θ−s}) with a complex planted zero (MUST-389).

### Falsification arm

- A collision is a pair of zeros at one ordinate, so the arm is to certify, at a candidate ordinate, a nonzero Euler-shift Pick energy below −2δ.
- The cleanest finite certificate in the ledger is the Euler-shift prime Pick witness: ¬RH ⟺ there exist a rational shift ω, Gaussian-rational nodes, a finite prime set and a rational δ whose finite-S Pick energy is at most −2δ within δ of the exact value [L] (endpoints F0257; xi §4.A.12, §4.A.25).
- The collision picture says where to place the nodes: at the candidate ordinate, with ω below the displacement (the Hardy leakage switches on exactly for 0 < ω < a; xi §4.A.18, §4.A.25).
- The height bound of xi §3.1 [C] applies.

### Main risks

- **Collapse onto an existing receiver.** On lattice lags the arithmetic side is the Chebyshev remainder at x = 2^k3^l. Its Cesàro mean square may reduce to Cramér's mean-square criterion. The mean-square, positive-part, Herglotz and Hardy forms of the lag criterion are one receiver (MUST-269), and no known tool reaches the one-sided √X lag scale (CANNOT-326). If step 2 lands there, the route stops.
- **Growth of the excess.** If the unconditional excess grows like log T, step 1 stops the route.
- **Neighbouring collision routes already closed:**
  - HC bounded-diagonal reception (F0102);
  - the HC filtered Gamma-six landing (F0228);
  - Chen–Gupta–Li packets, whose envelope is ≥ 288 (xi §8.6);
  - window enlargement: blocks larger than a pair are strictly harder to collapse (CANNOT-453).
- **Adjacency to the shifted-Euler (Suzuki) family.** The collision-by-real-shift picture is close to that de Branges-type family, which the ledger treats as a receiver (F0202, F0197).
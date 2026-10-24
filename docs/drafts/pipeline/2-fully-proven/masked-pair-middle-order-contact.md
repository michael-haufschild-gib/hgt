# Exact middle-order contact for centrally masked pairs

- **ID:** masked-pair-middle-order-contact
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; formalization pending)
- **Source:** Arithmetic Local Divisor Geometry; central-multiplicity full heat cone
- **Statement:** For `P_m=X^(2m)(X²−a)²`, `a>0`, the first nonnegative coefficient cone under `exp(sD²)` is reached through the single even coefficient indexed by `j=m+1−⌊m/2⌋`. Its exact threshold is the larger root of the corresponding quadratic index weight. Thus the contact order grows with multiplicity; zeroth-order contact is absent.

## Dependency and novelty gates

- [x] Candidate extracted from the dependency-closed quadratic-index and rational-bracket proof.
- [x] Audit against existing masked-pair threshold and contact declarations; the existing all-order moment formula and top/double-order examples do not identify this exact minimizing order.
- [x] Complete paper audit, including uniqueness and all small multiplicities.
- [ ] Formalize the exact minimizing index, threshold and contact classification.
- [ ] Transitive axiom audit.

## Symbolic mechanism

Use `B=(2m+2)(2m+1)`, `C=(2m+4)(2m+3)`, `d=C−B=8m+10`, `e=8m+5`, and `t=s/a`. Existing paper work gives `1/d≤σ_m/a≤1/e` and

`F_t(k)=(k−Bt+1/2)²+Bdt²−Bt−1/4`.

For integer indices the minimum is attained at `floor(Bt)`, clipped to `[0,m+1]`. This follows from

`F_t(k)−F_t(h)=(k−h)(k+h+1−2Bt)`.

Throughout the entire threshold bracket, `floor(Bt)=floor(m/2)`. Put `h=floor(m/2)`. For `m=2l`, `B−dl=2l+2>0` and `e(l+1)−B=9l+3>0`. For `m=2l+1`, those two differences are `10l+12>0` and `l+1>0`. Therefore `h<B/d≤Bt≤B/e<h+1`, including `m=0,1`.

The full cone in that bracket is therefore equivalent to `F_t(h)≥0`. For `k>h`, `k≥h+1` makes both factors in the index difference positive; for `k<h`, `k≤h−1` makes both negative. Thus the minimum is strict. At `t=1/d`, `F_t(h)=(h−B/d)(h+1−B/d)<0`. At the upper bound every index is positive. The derivative in `t` is `2B(Ct−h−1)>0` throughout the bracket, since `Ct=Bt+dt>h+1`. The intermediate value theorem therefore gives one crossing there, and it is the larger quadratic root

`r_m=[B(h+1)+sqrt(B(h+1)(B−dh))]/(BC)`.

The global threshold is `σ_m=a r_m`. Semigroup monotonicity excludes earlier disconnected cone components. For nonintegral `Bt`, the minimizing integer is unique. In the bracket `h<Bt<h+1`, hence all other index weights are strictly larger. At threshold exactly the coefficient of degree `2(m+1−h)` vanishes among the even coefficients up to the degree; every other even coefficient is positive. Odd coefficients vanish identically by parity and are not contacts. The leading coefficient remains one.

The active coefficient degree is exactly `2(m+1−floor(m/2))=m+2+(m mod 2)`. In particular it is never zero and is asymptotic to half the total degree `2m+4`.

This is a model calibration for contact rigidity, not a theorem about the arithmetic Xi source. The exact contact classification is the positive result; a generic zeroth-order-contact principle fails for this growing family. No worldwide novelty claim is made. The classical heat-monomial mechanism is described, for example, by [Hile–Stanoyevitch, Heat Polynomial Generalizations](https://stanoyevitch.net/papers/no14_w_Hile_AMRT_02.pdf); the contribution under audit here is the exact multiplicity-dependent coefficient contact.

## Hermite normalization

The existing `maskedPairMoment b λ m j` equals

`λ^j (2j)! [X^(2j)] exp((λ/2)D²)[X^(2m)(X²−b²)²]`.

Thus the Gaussian moment threshold is `λ=2b² r_m`, and the sign is unchanged for positive `λ`. This identity follows termwise from the Gaussian even moment and falling-factorial cancellation. It must be formalized before transferring the constants to the existing actual-Xi cofactor-error receiver. The cofactor bound itself remains unproved.

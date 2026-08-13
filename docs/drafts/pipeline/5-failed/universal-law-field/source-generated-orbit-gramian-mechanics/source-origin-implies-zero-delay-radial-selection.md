# Source origin implies zero-delay radial selection

- **ID:** ULF-SGOGM-FAIL-3
- **Stage:** 5 — failed/retired
- **Type:** FALSE SOURCE-SELECTION INFERENCE
- **Claim:** A canonical source origin forces every reflected radial defect to have zero causal
  delay, hence selects the critical line.
- **Verdict:** `[FALSE] [ANCHOR/LATENCY CONFLATION] [RH-EQUIVALENT ESCAPE KILLED]`
- **Positive survivor:**
  `../../../2-fully-proven/universal-law-field/source-generated-orbit-gramian-mechanics/causal-delay-radial-drift-work-cusp-and-information-undercapacity-law.md`

## 1. Exact countermechanism

A causal source can have a canonical boundary `t=0` while an admitted defect history begins at any
delay `b>0`. For the radial window law,

\[
 h_{\delta,b,T}
 ={1\over T}\big(
 \mathbf1_{[b-\delta,b-\delta+T]}
 -\mathbf1_{[b,b+T]}\big).
 \tag{SOF.1}
\]

Every `b>=max(0,delta)` is causal. Translating both intervals by `c>=0` preserves the `L^2` norm
exactly. Therefore a marked origin does not force the defect to touch it.

## 2. Literal corpus falsifier

`RHTower/SourceZeroHedenmalmOrientationRigidity.lean` proves:

1. unconditional source equivariance sends the causal flow at `alpha` to the anti-causal flow at
   `conj alpha`;
2. at an `XiC` zero it transports the causal flow to the causal flow at the reflected copy;
3. equality/fixedness of those causal flows is equivalent to `Re rho=1/2`.

Thus source origin and source equivariance are unconditional, while source fixedness is already an
RH classifier. Replacing “zero delay” by “source fixedness” imports the desired conclusion.

## 3. Positive survivor

The coordinate-free invariant is not absolute delay. It is **causal entrance latency**:

\[
 \ell_+(\delta)=\max(0,\delta),
 \qquad
 \ell_{\rm pair}(\delta)=|\delta|.
 \tag{SOF.2}
\]

Once admitted, common extra delay is gauge and work is unchanged. A valid selection theorem must
derive zero entrance latency for one parameter-free global defect before zeros are chosen.

## 4. Status

- [x] origin/latency inference falsified;
- [x] exact delay-gauge countermodel proved;
- [x] actual source fixedness shown RH-equivalent by existing Lean theorem;
- [x] entrance-latency survivor retained;
- [ ] parameter-free zero-slack source operation.

No Lean was written or built during this research pass.

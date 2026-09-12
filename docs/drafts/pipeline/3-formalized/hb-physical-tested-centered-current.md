# HB: complete physical scalar test on the centered native current

- **ID:** HB-QTCC
- **Stage:** 3-formalized
- **Parent:** [Original complete response current](hb-full-response-cusp-current.md)
- **Continuation:** [Tested means and contacts](../1-in-progress/hb-physical-tested-mean-contact-current.md)
- **Route:** Literal theta cusp → Xi occurrence → retained spin two → physical causal radial/left-QNM action → fixed common Hawking-clock extinction → RH

The original physical scalar test, including its complete Fourier tail, now
admits a source-derived centered bilinear response current with zero upper
cusp trace under every complex height weight. Its differentiated law retains
six terms. The integral of that complete density retains the negative lower
current. Full tested mean/contact cancellation and physical-action extinction
are not proved.

## Exact source law

Let M be the literal unit-period mean, R_b the original native forced
response, F_b its original forcing, alpha_b its unchanged parameter, and
T the entire scalar at `physicalAngularParameter q`. Define

```
V_T(F,G) = M[T(F-MF)(G-MG)]
         = M[TFG]-MF*M[TG]-MG*M[TF]+MF*MG*MT,
L_ab = V_T(R_a,y,R_b).
```

The test is not centered and no conjugation enters this identity. All four
original moments are differentiated using source smoothness. The product
rule gives `V_{T_y}(F,G)+V_T(F_y,G)+V_T(F,G_y)`. Literal period-one matching
cancels the horizontal side flux and gives

```
V_T(F_xx,G) = -V_T(F_x,G_x)-V_{T_x}(F_x,G).
```

Substituting the original forced response equation proves

```
L_ab' = V_{T_y}(R_a,y,R_b) + V_T(R_a,y,R_b,y)
      + V_T(R_a,x,R_b,x) + V_{T_x}(R_a,x,R_b)
      + alpha_a/y^2*V_T(R_a,R_b) + 1/y^2*V_T(F_a,R_b).
```

The two test-derivative contributions, inverse-square metric coefficient and
complete forcing work remain. No clock covariance, current conservation,
extinction or boundary-vanishing premise occurs in the source theorem.

## Source estimates and upper trace

At the physical Xi parameter the original principal part is
`Lambda(rho-1)*y^(1-rho/2)`. Its real exponent is below one and its derivative
has negative real exponent. The literal signed Fourier family bounds the
entire tail and both first derivatives above height three. Thus an original
source constant C, independent of horizontal position and response branches,
satisfies

```
|T(x,y)| <= C*y,       |T_y(x,y)| <= C,       |T_x(x,y)| <= C.
```

Centered finite-cell Young gives
`2|V_T(F,G)| <= sup|T|*(Var F+Var G)`. Original Parseval identifies response
variance with its nonconstant mass, and
`2 Var(R_b,y)+Var(R_b,x)=E_b`. The nonzero integer-frequency gap bounds mass
by E_b. Complete forcing Parseval gives
`Var F_b<=y^4*forcingMass_b`. These exact source quantities yield

```
|L_ab| <= C*y*(E_a+E_b),
|L_ab'| <= C*y*((|alpha_a|+5)*(E_a+E_b)+y^4*forcingMass_a).
```

For a natural N, energy admission at N+1 and forcing decay at N+3 dominate
both `y^N L_ab` and its actual derivative by integrable functions. W1,1 then
forces the zero upper trace. A larger integer exponent dominates any complex
height power. This proves `y^w L_ab(y) -> 0` for every complex w.

Both original finite endpoints are retained in
`integral_l^r L_ab'=L_ab(r)-L_ab(l)`. Therefore

```
lim_(r->infinity) integral_l^r L_ab' = -L_ab(l).
```

This is the precise surviving boundary contribution, not a zero integral.
The original uncentered tested product is restored exactly as

```
M[T R_a,y R_b] = L_ab + (MR_a)'*M[T R_b]
              + MR_b*M[T R_a,y] - (MR_a)'*MR_b*MT.
```

The remaining linear moments, original full response means/particular terms
and Q contacts require their own boundary analysis. The next card gives a
scaled Young mechanism for the linear moments. Independent scalar/scalar,
scalar/vector and vector/vector action assembly, retained spin two,
remaining metric weights and horizon/characteristic/source-contact faces
are not removed by this centered upper trace.

## Extinction interface and failed transfers

The exact total-cokernel transduction remains
`K_n(q)=-Sigma_n(q)*|D_n(q)|^2`, with `Sigma_n(q)>0`. A source-derived
nonnegative real orientation of the same complete physical left-QNM action,
together with physical-action identification, would force D=0. The present
norm bounds supply no such sign. Assuming the missing orientation or a
one-unit physical-clock covariance law would not prove the source theorem
requested for RH. No clock has been retuned.

The deep scalar-jet query used available partial results: 57,213 inventoried
files, pending compiler metadata, unmeasured semantic coverage and reported
semantic/reranking timeout or cancellation. The source/method views did not
produce an applicable new ingredient set. Exhaustive source search located
`physicalScalar_vertical_cusp_bound`; reusing it avoids re-proving the full
vertical principal/tail derivative. The horizontal source formula and
explicit period moments supply the other applicable ingredients. A separate
hybrid physical-action search returned the exact transduction and unit-step
equivalence, with 57,218 inventoried files and no retrieval errors; its
semantic coverage remained unmeasured.

Broad recent arXiv reciprocity and entropy searches tested two transfers.
[Mechanical reciprocity](https://arxiv.org/html/2609.04169v1) derives response
constraints from an invertible transpose-symmetric operator; its positivity
condition has a separate role. It does not identify the nonlinear causal
left-QNM reader and all boundary faces with that operator. This repeats the
source-identification obstruction recorded in the parent card.
[Two-fluid entropy balance](https://arxiv.org/html/2609.10393v1) combines
exchange terms before imposing dissipation and adds a model-specific balance
anchoring axiom. It motivates retaining the differentiated-test/source work
but supplies neither a matching HB real entropy nor an admissible new premise.
Neither transfer produces complete physical-action orientation.

## Lean implementation and audit

Four definitions and eight public theorems are in
[ThetaCuspHawkingBMQuarticTestedNativeCurrent.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticTestedNativeCurrent.lean).
The implementation uses two narrow cached imports, explicit derivative and
finite-integral equalities, typed integrability witnesses, and bounded local
algebra. All 1,029 lines passed the assembled scratch without diagnostics at
default Lean limits. No heartbeat/depth/transparency override, numerical
certificate or axiom-printing step was used.

Source SHA256:
`76d58e156541c5ca69dffd1fdc3e5ec8e0a7b618b137b8ff8eb817f224dc201e`.
The final isolated `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticTestedNativeCurrent`
passed in 153 seconds and published the exact matching leaf artifacts. One
umbrella import is wired; no full or umbrella build was run. Generated index
and lint results are recorded below.

The generated index includes all four definitions and eight public theorems.
`python3 scripts/formal_tools.py lint --check-generated` passed with exit 0;
existing large-file warnings remain elsewhere in the repository. The exact
leaf source hash is unchanged. All owned Lean/check/audit processes ended,
and the temporary audit directory was removed. No commit or push was made.

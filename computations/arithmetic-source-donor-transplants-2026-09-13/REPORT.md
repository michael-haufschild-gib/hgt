# Arithmetic source-divisor transplantation — report

60 saved tasks; 60 passed their implemented checks, 0 recorded failures. Whole-family wall time 105.978s. Original downloaded checksums verified. Exact environment, executable code, frozen parameters, source provenance and raw failed starts are retained.

Let Phi_R(x)=sum_{n>=1} exp(x/2)(4q_n^2-6q_n)exp(-q_n), q_n=pi*n^2*exp(2x). Its Fourier transform F(w)=integral Phi_R(x)exp(iwx)dx is xi(1/2+iw). Other arithmetic hosts use Phi_c(x)=2exp((a+1/2)x)sum c_n n^a exp(-pi*n^2*exp(2x)/q), with completion (q/pi)^((s+a)/2)Gamma((s+a)/2)q^(-s)sum_r c_r HurwitzZeta(s,r/q). B4 has(q,a,c)=(4,1,[0,1,0,-1]); L5=(5,0,[0,1,-1,-1,1]); actual Davenport-Heilbronn D=(5,1,[0,1,k,-k,-1]), k=(sqrt5/2-sin(2pi/5))/sin(4pi/5). These are independently checked source/completion objects; D is not the corpus's finite fake-coefficient witness.

For an off-axis source node z, P_z(x)=(1-x^2/z^2)(1-x^2/conj(z)^2). For z=ia, P=1+x^2/a^2. Multiplying by P inserts a divisor; dividing is allowed only for an actual host node. Sources are mass-normalized for spectral comparisons. Variance mode scales donor coordinates by sqrt(Var_host/Var_R); it is a fixed control, not an optimized parameter. Positivity of the actual D/L5 source is sampled in this computation; it is not a new unconditional theorem.

## Question and outcome

Does transplanting an actual zeta-source divisor produce a host-independent spectral response, or is its effect attached to the residual arithmetic source? The starting context-free hypothesis was already contradicted by within-zeta data; this experiment asks which nonlocal responses survive host/width changes. Completion controls passed before dependent calculations.

| Case | Real sign brackets | Found nonreal roots | Failed starts |
|---|---:|---:|---:|
| B4-0-native | 47 | 3 | 22 |
| B4-0-variance | 47 | 4 | 22 |
| B4-0_4-native | 51 | 0 | 21 |
| B4-0_4-variance | 51 | 0 | 22 |
| B4-1-native | 51 | 0 | 22 |
| B4-1-variance | 51 | 0 | 22 |
| B4-12-native | 51 | 0 | 22 |
| B4-12-variance | 51 | 0 | 22 |
| B4-4-native | 51 | 0 | 21 |
| B4-4-variance | 51 | 0 | 22 |
| B4-7-native | 51 | 0 | 21 |
| B4-7-variance | 51 | 0 | 22 |
| B4-7_8-native | 51 | 0 | 21 |
| B4-7_8-variance | 51 | 0 | 22 |
| B4-8-native | 51 | 0 | 21 |
| B4-8-variance | 51 | 0 | 22 |
| B4-none-native | 50 | 0 | 22 |
| D-0-native | 54 | 0 | 23 |
| D-0-variance | 50 | 4 | 23 |
| D-0_4-native | 55 | 0 | 23 |
| D-0_4-variance | 54 | 0 | 24 |
| D-1-native | 54 | 0 | 23 |
| D-1-variance | 54 | 0 | 23 |
| D-12-native | 54 | 0 | 23 |
| D-12-variance | 54 | 0 | 23 |
| D-4-native | 54 | 0 | 23 |
| D-4-variance | 54 | 0 | 23 |
| D-7-native | 54 | 0 | 23 |
| D-7-variance | 54 | 0 | 23 |
| D-7_8-native | 55 | 0 | 23 |
| D-7_8-variance | 54 | 0 | 23 |
| D-8-native | 54 | 0 | 23 |
| D-8-variance | 50 | 3 | 23 |
| D-none-native | 52 | 2 | 23 |
| L5-0-native | 50 | 2 | 23 |
| L5-0-variance | 48 | 5 | 23 |
| L5-0_4-native | 54 | 0 | 23 |
| L5-0_4-variance | 54 | 0 | 23 |
| L5-1-native | 54 | 0 | 23 |
| L5-1-variance | 54 | 0 | 23 |
| L5-12-native | 54 | 0 | 23 |
| L5-12-variance | 54 | 0 | 23 |
| L5-4-native | 54 | 0 | 23 |
| L5-4-variance | 54 | 0 | 23 |
| L5-7-native | 54 | 0 | 24 |
| L5-7-variance | 54 | 0 | 23 |
| L5-7_8-native | 54 | 0 | 23 |
| L5-7_8-variance | 54 | 0 | 23 |
| L5-8-native | 52 | 0 | 22 |
| L5-8-variance | 52 | 1 | 23 |
| L5-none-native | 54 | 0 | 23 |
| R-0-native | 14 | 12 | 13 |
| R-0_4-native | 30 | 0 | 12 |
| R-1-native | 29 | 0 | 12 |
| R-12-native | 28 | 2 | 13 |
| R-4-native | 30 | 0 | 13 |
| R-7-native | 30 | 0 | 13 |
| R-7_8-native | 30 | 0 | 12 |
| R-8-native | 24 | 4 | 14 |
| R-none-native | 29 | 0 | 15 |

The same donor z=1.018240818353035+.765996945998912i produces independently validated nonreal spectral roots32.2464819270+.8779634697i for R,11.4975427915+.4820966941i for B4 and9.8647471851+.6601496930i for L5 in native coordinates. For D, native insertion locally heals its original off-axis pair (subsequent transport/fold challenge); variance-matched insertion instead has nonreal roots40.3685784203+.3804567000i and85.4995541827+.5230357184i. The native D scan found no nonreal root in its search, which is not a global repair claim.

## Interpretation and positive salvage

Actual divisor placements interact with the host and coordinate scale. A donor list alone does not supply a spectral selector. Near-cancellation of nearby divisor factors and generic derivative healing are predictable controls, not discoveries. The useful surviving object is the whole divisor/residual-source attachment; any proposed transferable law must account for width and nonlocal pair creation. The next discriminating question changes positive-source representation while preserving the original spectral zero set, rather than modifying the arithmetic function again.

## Scope

These numerical observations are not interval certificates, new Lean proofs, a complete zero census or RH counterexamples. No claim of historical priority is established. Counts are roots found by declared starts; failed searches never prove absence. Polynomial-modified sources change arithmetic functions. Source-node cancellation uses high-precision numerical coordinates. SS/SV/VV actions, physical remainders, onset/contact and boundary work are outside these arithmetic calculations, not omitted zero terms. No HB identification or extinction claim follows. No Lean builds were run.

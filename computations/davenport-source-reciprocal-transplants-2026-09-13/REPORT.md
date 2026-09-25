# Arithmetic source-divisor transplantation — report

33 saved tasks; 33 passed their implemented checks, 0 recorded failures. Whole-family wall time 87.369s. Original downloaded checksums verified. Exact environment, executable code, frozen parameters, source provenance and raw failed starts are retained.

Let Phi_R(x)=sum_{n>=1} exp(x/2)(4q_n^2-6q_n)exp(-q_n), q_n=pi*n^2*exp(2x). Its Fourier transform F(w)=integral Phi_R(x)exp(iwx)dx is xi(1/2+iw). Other arithmetic hosts use Phi_c(x)=2exp((a+1/2)x)sum c_n n^a exp(-pi*n^2*exp(2x)/q), with completion (q/pi)^((s+a)/2)Gamma((s+a)/2)q^(-s)sum_r c_r HurwitzZeta(s,r/q). B4 has(q,a,c)=(4,1,[0,1,0,-1]); L5=(5,0,[0,1,-1,-1,1]); actual Davenport-Heilbronn D=(5,1,[0,1,k,-k,-1]), k=(sqrt5/2-sin(2pi/5))/sin(4pi/5). These are independently checked source/completion objects; D is not the corpus's finite fake-coefficient witness.

For an off-axis source node z, P_z(x)=(1-x^2/z^2)(1-x^2/conj(z)^2). For z=ia, P=1+x^2/a^2. Multiplying by P inserts a divisor; dividing is allowed only for an actual host node. Sources are mass-normalized for spectral comparisons. Variance mode scales donor coordinates by sqrt(Var_host/Var_R); it is a fixed control, not an optimized parameter. Positivity of the actual D/L5 source is sampled in this computation; it is not a new unconditional theorem.

## Question and outcome

Does transplanting an actual zeta-source divisor produce a host-independent spectral response, or is its effect attached to the residual arithmetic source? The starting context-free hypothesis was already contradicted by within-zeta data; this experiment asks which nonlocal responses survive host/width changes. Completion controls passed before dependent calculations.

| Case | Real sign brackets | Found nonreal roots | Failed starts |
|---|---:|---:|---:|
| D-erase-0 | 5 | 24 | 25 |
| D-erase-1 | 18 | 18 | 23 |
| D-erase-2 | 30 | 12 | 22 |
| D-exchange-0-R0-native | 5 | 25 | 32 |
| D-exchange-0-R0-variance | 5 | 24 | 25 |
| D-exchange-0-R4-native | 52 | 2 | 23 |
| D-exchange-0-R4-variance | 5 | 29 | 26 |
| D-exchange-0-R7-native | 23 | 26 | 24 |
| D-exchange-0-R7-variance | 5 | 27 | 26 |
| D-exchange-0-R8-native | 7 | 26 | 33 |
| D-exchange-0-R8-variance | 5 | 24 | 25 |
| D-exchange-1-R0-native | 18 | 21 | 21 |
| D-exchange-1-R0-variance | 18 | 18 | 22 |
| D-exchange-1-R4-native | 29 | 17 | 23 |
| D-exchange-1-R4-variance | 18 | 21 | 23 |
| D-exchange-1-R7-native | 29 | 19 | 23 |
| D-exchange-1-R7-variance | 18 | 20 | 23 |
| D-exchange-1-R8-native | 20 | 22 | 23 |
| D-exchange-1-R8-variance | 18 | 18 | 22 |
| D-exchange-2-R0-native | 48 | 5 | 23 |
| D-exchange-2-R0-variance | 30 | 12 | 21 |
| D-exchange-2-R4-native | 31 | 15 | 22 |
| D-exchange-2-R4-variance | 31 | 13 | 22 |
| D-exchange-2-R7-native | 31 | 14 | 22 |
| D-exchange-2-R7-variance | 31 | 13 | 22 |
| D-exchange-2-R8-native | 37 | 12 | 22 |
| D-exchange-2-R8-variance | 30 | 12 | 21 |
| R-exchange-0-D0 | 26 | 2 | 11 |
| R-exchange-0-D1 | 26 | 2 | 11 |
| R-exchange-0-D2 | 29 | 0 | 14 |
| R-exchange-4-D0 | 23 | 5 | 13 |
| R-exchange-4-D1 | 5 | 14 | 14 |
| R-exchange-4-D2 | 5 | 13 | 17 |

Three distinct D source nodes were found and independently checked at100/160digits, with numerical winding1: .1555769047+.7003261020i, .6018853884+.7695597508i, .9998376360+.7752985670i. This is not a complete node list. Removing the first produces a checked spectral witness14.9491140338+3.5917396201i. Replacing it by zeta donor4 in native coordinates retains a witness85.6829512409+.3589091731i; variance matching instead produces14.1654630143+2.5031899639i. Reverse exchange into R, deleting its donor4 and inserting D node0, gives60.0334045090+.6362295787i.

## Interpretation and positive salvage

Actual divisor placements interact with the host and coordinate scale. A donor list alone does not supply a spectral selector. Near-cancellation of nearby divisor factors and generic derivative healing are predictable controls, not discoveries. The useful surviving object is the whole divisor/residual-source attachment; any proposed transferable law must account for width and nonlocal pair creation. The next discriminating question changes positive-source representation while preserving the original spectral zero set, rather than modifying the arithmetic function again.

## Scope

These numerical observations are not interval certificates, new Lean proofs, a complete zero census or RH counterexamples. No claim of historical priority is established. Counts are roots found by declared starts; failed searches never prove absence. Polynomial-modified sources change arithmetic functions. Source-node cancellation uses high-precision numerical coordinates. SS/SV/VV actions, physical remainders, onset/contact and boundary work are outside these arithmetic calculations, not omitted zero terms. No HB identification or extinction claim follows. No Lean builds were run.

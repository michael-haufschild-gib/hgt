# Arithmetic source-divisor transplantation — report

6 saved tasks; 6 passed their implemented checks, 0 recorded failures. Whole-family wall time 27.197s. Original downloaded checksums verified. Exact environment, executable code, frozen parameters, source provenance and raw failed starts are retained.

Let Phi_R(x)=sum_{n>=1} exp(x/2)(4q_n^2-6q_n)exp(-q_n), q_n=pi*n^2*exp(2x). Its Fourier transform F(w)=integral Phi_R(x)exp(iwx)dx is xi(1/2+iw). Other arithmetic hosts use Phi_c(x)=2exp((a+1/2)x)sum c_n n^a exp(-pi*n^2*exp(2x)/q), with completion (q/pi)^((s+a)/2)Gamma((s+a)/2)q^(-s)sum_r c_r HurwitzZeta(s,r/q). B4 has(q,a,c)=(4,1,[0,1,0,-1]); L5=(5,0,[0,1,-1,-1,1]); actual Davenport-Heilbronn D=(5,1,[0,1,k,-k,-1]), k=(sqrt5/2-sin(2pi/5))/sin(4pi/5). These are independently checked source/completion objects; D is not the corpus's finite fake-coefficient witness.

For an off-axis source node z, P_z(x)=(1-x^2/z^2)(1-x^2/conj(z)^2). For z=ia, P=1+x^2/a^2. Multiplying by P inserts a divisor; dividing is allowed only for an actual host node. Sources are mass-normalized for spectral comparisons. Variance mode scales donor coordinates by sqrt(Var_host/Var_R); it is a fixed control, not an optimized parameter. Positivity of the actual D/L5 source is sampled in this computation; it is not a new unconditional theorem.

## Independent challenge

Production source integrals were replaced by a periodic-character Fourier expansion into Jacobi theta derivatives and evaluated on contours shifted by+.15 and-.1. Grid denominators increased from64 to128 and256 at100 and160digits. Insertion-only witnesses additionally use the full differential operator on the Hurwitz/gamma completion, retaining all gamma derivatives. Source-node checks include32-point numerical winding. Spectral endpoint checks use residual/derivative errors; no spectral winding was computed in these families.

The independently checked local collision is w=85.328590046698709,lambda=.0871559526042790, with positive quadratic branch coefficient2.0525043660. Below the collision the pair is nonreal; above it two real roots appear. Four local branch errors are below1.20e-74 at100digits and3.01e-134 at160digits. Endpoint roots84.225565272257387 and85.606611609454952 also pass independent completion-operator checks. No global absence claim is made.

| Task | Precision | Status | Witness / error |
|---|---:|---|---|
| 0 | 100 | ok | 85.3285900467, 0 |
| 0 | 160 | ok | 85.3285900467, 0 |
| 1 | 100 | ok | 84.22556527226, 0 |
| 1 | 160 | ok | 84.22556527226, 0 |
| 2 | 100 | ok | 85.60661160945, 0 |
| 2 | 160 | ok | 85.60661160945, 0 |

## Meaning and limits of the survivor

These checks distinguish stable numerical witnesses from search/selection failure. They support host-dependent divisor response and one local pair-healing mechanism. A global source-specific composition law and any connection to HB action remain open.

## Scope

These numerical observations are not interval certificates, new Lean proofs, a complete zero census or RH counterexamples. No claim of historical priority is established. Counts are roots found by declared starts; failed searches never prove absence. Polynomial-modified sources change arithmetic functions. Source-node cancellation uses high-precision numerical coordinates. SS/SV/VV actions, physical remainders, onset/contact and boundary work are outside these arithmetic calculations, not omitted zero terms. No HB identification or extinction claim follows. No Lean builds were run.

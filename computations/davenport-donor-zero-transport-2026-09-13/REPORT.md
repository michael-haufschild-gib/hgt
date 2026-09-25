# Arithmetic source-divisor transplantation — report

10 saved tasks; 8 passed their implemented checks, 2 recorded failures. Whole-family wall time 9.158s. Original downloaded checksums verified. Exact environment, executable code, frozen parameters, source provenance and raw failed starts are retained.

Let Phi_R(x)=sum_{n>=1} exp(x/2)(4q_n^2-6q_n)exp(-q_n), q_n=pi*n^2*exp(2x). Its Fourier transform F(w)=integral Phi_R(x)exp(iwx)dx is xi(1/2+iw). Other arithmetic hosts use Phi_c(x)=2exp((a+1/2)x)sum c_n n^a exp(-pi*n^2*exp(2x)/q), with completion (q/pi)^((s+a)/2)Gamma((s+a)/2)q^(-s)sum_r c_r HurwitzZeta(s,r/q). B4 has(q,a,c)=(4,1,[0,1,0,-1]); L5=(5,0,[0,1,-1,-1,1]); actual Davenport-Heilbronn D=(5,1,[0,1,k,-k,-1]), k=(sqrt5/2-sin(2pi/5))/sin(4pi/5). These are independently checked source/completion objects; D is not the corpus's finite fake-coefficient witness.

For an off-axis source node z, P_z(x)=(1-x^2/z^2)(1-x^2/conj(z)^2). For z=ia, P=1+x^2/a^2. Multiplying by P inserts a divisor; dividing is allowed only for an actual host node. Sources are mass-normalized for spectral comparisons. Variance mode scales donor coordinates by sqrt(Var_host/Var_R); it is a fixed control, not an optimized parameter. Positivity of the actual D/L5 source is sampled in this computation; it is not a new unconditional theorem.

## Failed conjecture and recovery

An earlier direct Newton fold check initialized at85.7 failed because it selected an inadmissible negative interpolation parameter. This run bracketed W=F0 F1'-F0' F1 in75..105, finding an admitted fold w=85.3285900467,lambda=.0871559526043, and an inadmissible fold w=85.9279930707,lambda=-.0490069294034. F0 is mass-normalized D; F1 is D multiplied by donor0 and normalized.

Both real-parameter paths reached the step floor just below the admitted double zero; these two tasks remain recorded as failures. All eight small complex-detour paths reached one of the real endpoints84.2255652723 and85.6066116095. Conjugate/reverse detours exchange the endpoint labels. Detours are branch bookkeeping, not positive physical sources.

## Meaning

The disappearance from the original scan was a local collision, supported by subsequent independent100/160digit fold/branch/endpoint checks. Unbracketed Newton selection was the failed inference. This does not establish global real-rootedness or restore Euler arithmetic. A count of visible off-axis pairs is too weak to assess an RH proof mechanism.

## Scope

These numerical observations are not interval certificates, new Lean proofs, a complete zero census or RH counterexamples. No claim of historical priority is established. Counts are roots found by declared starts; failed searches never prove absence. Polynomial-modified sources change arithmetic functions. Source-node cancellation uses high-precision numerical coordinates. SS/SV/VV actions, physical remainders, onset/contact and boundary work are outside these arithmetic calculations, not omitted zero terms. No HB identification or extinction claim follows. No Lean builds were run.

SQB75 completed positive progress; RH, global rank-seven signed positivity, common correction coefficient, and all-rank propagation OPEN. Goal remains active. No external blocker. Frontier map READ ONLY, untouched. Universal ledger untouched (results route-specific). No computations/numerics, Git, launch.sh, subagents. One foreground Lean/Lake at a time. All owned processes completed.

Prior math: u,k,J,t=9-u² actual modular orbit; T=t(k+1/3)=3A/4; amp=H*t/12; v=k-1/6; Phi=amp*v; B=u/3-J>=0; U=B/T in [0,1/12); Psi=amp²B; Q_a=x*sinh(2ax)*Psi. Q' absolutely integrable and integral0 from existing ThetaCuspModularBarrierFlux; old reserve=Psi/(18x), positive on x>=2/3; exists K0>0 making native even4 last entry +L G+K0*oldreserve PD there, L=10^12. Inner/global sign not proved.

NEW installed/wired/audited:
1. formal/GaloisForLFunctions/RHTower/ThetaCuspModularBarrierCost.lean (~349 lines), namespace RHTower.ThetaCuspModularRatio.
normalizedDefect=U, normalizedDriftDefect=W=U-u/36.
W'=cW+F, c=4u(k+1/3)-2J>=0,
F=4/3-5kt/36+u²/27-uJ/18.
F'=ut(36k²-1)/162+B[t(k/3+5/54)+u²(k+2/3)/9]>=0.
If W(b)>0,F(b)<0, fencing from W0=0 contradicts crossing. If F(b)>=0, forward fencing and u(b)>0 make W grow at fixed positive rate, contradict bounded U. Thus U<=u/36. Kinetic gap implies u'<12 hence U<=x/3.
Public:
 normalizedDefect_le_drift line100
 normalizedDefect_le_center line182
 barrierFlux_deriv_inner_cost line246
 barrierFlux_deriv_global_cost line284
 barrierFlux_deriv_polynomial_cost line299.
Global cost: Q' <= (504/169)*[4x sinh(2ax)]*Phi² for 0<=a<=1/2,x>=0.
Inner proof Psi<=amp²T*x/3, Psi'<=amp²T/12; T<=72/5 and Phi²>=169amp²/144. Upper ray already Q'<=0.
STRONGER SIGNED bound: Q'<=weight*amp²*P,
P=(T/12)[6-3k+(u(k-2/3)-J)/4].
Uses Psi'<=amp²T(4/3-k), retains sign, removes x using center inequality.
Scratch /tmp/sqb75_normalized_cost.lean passes; four printed capstones only propext,Classical.choice,Quot.sound.
Final narrow lake build GaloisForLFunctions.RHTower.ThetaCuspModularBarrierCost passes104s/2jobs in /tmp/sqb75-barrier-cost-leaf-audit, actual source/cached deps.

2. formal/GaloisForLFunctions/RHTower/ThetaCuspModularBarrierGain.lean (~162 lines).
ratio_ge_physical_scale line88: q/3-5/6<=k if q=pi exp(2x)>=15/2.
Proof full exact likelihood derivative: Phi'=f'(1+R)-2q f M with R,M>=0, Phi=f(1+R). f' <= (5-2q)f since polynomial difference exp(x/2-q)*q*(2q-15)>=0. Modular source gives -6kPhi<=Phi'. No replacement of full source by first atom.
Degree4 Taylor bound of exp(4/3), pi_gt_d2, gives q>=23/2 for x>=2/3.
ratio_ge_three_on_upper_ray line110: k>=3 there.
barrierFlux_deriv_gap_gain line116:
 weight*(5/48)*amp²T <= -Q' on same upper ray, 0<=a<=1/2.
From signed P upper <=T*(22-9k)/48<=-5T/48.
barrierGapReserve=(5/48)amp²T.
barrierGapReserve_ge_fifteen line138: 15*oldreserve<=barrierGapReserve for x>=2/3, using B<T/12 and x>=2/3.
Scratch /tmp/sqb75_barrier_gain.lean passes, all4 printed capstones standard axioms only.
Final narrow lake build GaloisForLFunctions.RHTower.ThetaCuspModularBarrierGain passes80s/2jobs in /tmp/sqb75-barrier-gain-leaf-audit, actual source/cached deps.
Both imports wired once RHTower.lean. Global formal lint PASSED /tmp/sqb75_formal_lint.txt (existing large-file warnings only). No full/umbrella builds.

CURRENT HARD TARGET:
Same admitted flux now has explicit inner cost and >=15x earlier outer reserve. If old outer K0 supplied PD with oldreserve, K0/15 against actual new flux suffices on upper ray. This does NOT bound K0 numerically or pay inner cost. Need ONE compatible coefficient, or prove signed polynomial determinant lower positive directly:
 H^8*evenLowerDet +amp²*(L*compensationReserve-K*P)*det(nativeEvenHead)>0, L=10^12,K>=0.
This determinant implication is paper deduction via existing affine last-entry determinant formula and new flux bound; no global sign proved.
Constant-cost inner sufficient target: nativeEvenFourSchur+L G>(504/169)K Phi² on [0,2/3], plus outer repair for SAME K.
Retain signed P when possible. Do not prove another arbitrary compact repair or generic receiver and call it global progress.
Private dNormalized now Lean; derivative of N=amp²U from previous card remains analytical, not installed.

Current research card updated:
docs/drafts/pipeline/1-in-progress/sqb-native-spectral-source-comparison.md, section An explicit inner budget from the normalized drift (line454), signed P target, physical-scale gain, audits, exact remaining common coefficient. Frontier and universal ledger unchanged.

Searches all-view incl method, OR/singleword + mechanisms, deep:
 /tmp/sqb75_transport_search.json, balance_search, majorization_search, successor_search (120s before updated instructions)
 /tmp/sqb75_confinement_search.json (confinement Riccati OR)
 /tmp/sqb75_multiplier_search.json (derivative margin budget)
 /tmp/sqb75_starshaped_search.json (starshaped concavity OR)
 /tmp/sqb75_slope_search.json (full-source leading atom slope mechanism).
Last4 used300s allviews no-refresh. All terminal. Inspected declaration/candidate/source-argument/idea/group views. Partial and stale compiler/source coverage (last files56257 indexed56052,204stale,43801 compilerpending,793methodstale); earlier malformed/interrupted/deadline stages. Groups generally retain needed derivative, convexity, or different-equation premises. No absence claims.

Own arxiv broad terms included elasticity, buckling, entrainment, caustics, resilience, pinning. Direct pinning date-sorted search recovered and read analytical theorem/proof of https://arxiv.org/html/2609.09384v1 (Networked Admissibility-Preserving Control for Directed Safe Coordination, Sept8 2026). Exact cascade preserves initial realization mismatch; one-sided gains are priced before invariant-domain bootstrap. Useful method analogy for signed P, no imported premise. elasticity found 2609.04817 upload of 2022 paper, not new2026 research. Many web searches returned old papers/cachemiss/one429. Original requested2607.08139 read in prior work.

Potential unexplored conjecture (NOT proved/used): B/[x*(k-1/6)^2] decreasing would compare Q directly to original center flux and could improve coefficient compatibility; starshape search gave unrelated radial concavity, no join. Do not assert it. No experiment conducted.
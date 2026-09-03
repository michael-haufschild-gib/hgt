# Prime-Hodge singular residue clock (2026-09-03)

Paper theorem ULF-PHSR-001:
- Source survival shift C has m_k=105/((2k+3)(2k+5)(2k+7)).
- D_N=I-C*^N C^N is diagonal d_(N,k)=1-m_(k+N)/m_k, strictly decreasing compact, k d_(N,k)->3N.
- Hence D_N is measurable weak S1, not S1, in every S_p for p>1, logarithmic/Dixmier residue 3N.
- Cocycle D_(N+M)=D_N+C*^N D_M C^N. Exit E_j=C*^jD_1C^j=D_(j+1)-D_j has diagonal w_(k+j)/m_k~3/k, residue3. E_j-E_l is trace class.
- Exact partial fraction: d_(N,k)=A_N/(2k+2N+3)+B_N/(2k+2N+5)+C_N/(2k+2N+7), A=N(N-1)(N-2), B=-2N(N-1)(N+1), C=N(N+1)(N+2).
- Coordinate finite part FP(D_N)=-1/2[A psi(N+3/2)+B psi(N+5/2)+C psi(N+7/2)]; FP(D_1)=-3psi(9/2).
- Marked readout <e0,E_j e0>=w_j=Tr(P_j T), sum=Tr T=1.
- In CCRHD record carrier u_j=(E S^j Omega_H)/sqrt(w_j), clock D_N and actual prime-formed T are diagonal: T u_j=w_j u_j. Thus Res(D_N+T)=3N and FP(D_N+T)=FP(D_N)+1. T is a pre-divisor integral nuclear unit translation in residue-clock leaf.
- Fixed nonzero theta moments q_n have ratios rho_n increasing to1; hazards h_n=1-rho_n decrease to0 but sum_(n<N)h_n/logN->infinity because q_n=o(n^-K) for all K. Theta hazard is compact but not weak S1. No trace-class correction identifies it with source clock.

Retired ULF-FRRD-001:
- C-S in S2\\S1; direct det2 of compact quasinilpotent weighted shift is 1, no winding.
- Degree7 is only finite rational-inner coarse observer, already incompatible with polynomial full tail.

Live ULF-ARCFP-001:
- Poisson must derive history-dependent theta clock landing in D_1+S1, preserve odd unsquared formation, and unique Szego anomaly must fix finite-part origin.
- Source T provides proved +1 translation. Each strict-right horizon is target rank-one trace1.
- Need prove common-frame horizon additivity and exhaustion/no compensating S1 spectator; relative FP conservation then gives k=0 and RH.
- Residue alone is trace-class/finitary-horizon blind.

Files:
- docs/drafts/pipeline/2-fully-proven/universal-law-field/restricted-grassmannian-formation-geometry/prime-hodge-singular-residue-clock-law.md
- docs/drafts/pipeline/1-in-progress/universal-law-field/restricted-grassmannian-formation-geometry/archimedean-residue-clock-finite-part-selection.md
- docs/drafts/pipeline/5-failed/universal-law-field/restricted-grassmannian-formation-geometry/four-leg-relative-return-degree-selection.md
- STATUS F518-F520, FAIL-86, CANNOT-239, MUST-161.

No Lean written/built in current read-only research phase.
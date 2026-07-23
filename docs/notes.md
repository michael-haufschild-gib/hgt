RH iff counter-phased prime mass never exceeds aligned prime mass plus strictly positive Γ–polar budget.

Proved unconditionally in Lean:
\[
\pi B_1(L)=C(L)+P_+(L)-P_-(L),
\]where \(C(L)>0\) is exact Γ–polar midpoint-reflection budget and \(P_\pm\ge0\) are aligned/counter-phased prime-power masses. Consequently,
\[
\mathrm{RH}\iff
\forall L\ge\pi/2,\quad P_-(L)\le C(L)+P_+(L).
\]This removes Γ orientation completely. Remaining RH obstruction is now solely nonlocal outer-to-inner prime-power transport; atomwise reflection cannot work because \(\log k\mapsto L-\log k\) does not preserve prime-power logarithms.


Current frontier is exact and Lean-certified: prove the half-wave transport \(P_-(L)\le C(L)+P_+(L)\) for every \(L\ge \pi/2\), or derive a contradiction from its failure. Local positivity, parity compression, same-prime pairing, and single-product Selberg fibres are already closed. I’m now testing the corpus’s sole surviving nonlocal mechanism: Type-II transport coupling different semiprime products across the moving CCM aperture.
# Unit spacing and relative comb width

For windows $(N,N+M_N]$, the necessary and sufficient criterion for an arbitrarily large uniform unit-spacing mass floor is $M_N/N\to0$. The finite lower estimate loses $H_{M_N}$ against a diagonal $\log N$, leaving $\log(N/M_N)-O(1)$ when $0<M_N\le N$. Empty windows satisfy every floor.

If $M_N\ge\varepsilon N$ infinitely often, fix an integer $R>4/\varepsilon$ and set $b=\lfloor N/R\rfloor+1$. For all large such $N$, $(Rb,Rb+b]\subset(N,N+M_N]$. The flat vector on this block has a finite Rayleigh limit as $b\to\infty$. It obstructs a divergent floor along that subsequence. This criterion allows the width to vary arbitrarily with the cutoff.

For every fixed real aperture $\theta>0$, an arbitrarily large floor on $(N,N+\lfloor\theta N\rfloor]$ therefore holds exactly at integer spacings $d\ge2$. A flat block inside each sufficiently wide unit-spaced window supplies the upper obstruction. A fixed positive unit-spacing floor for every fixed ratio remains equivalent to RH.

Lean proves `divergent_unit_floor_iff_relative_width_zero` and `divergent_comb_floor_at_any_aperture_iff`. [Formal proof](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/TheSpacingThresholdForDivergentCombFloors.lean)

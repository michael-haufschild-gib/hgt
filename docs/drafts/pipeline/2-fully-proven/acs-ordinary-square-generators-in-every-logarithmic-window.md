# Ordinary square generators in every logarithmic window

One integer $B>0$ suffices at some conductor in every sufficiently late window $|2\log n-T|\le10\log(T+2)$. At that conductor $d_{\rm ord}(mD_n)\le B^{m^2}$ for every positive multiplicity, including $m=n$.

Write $L(u)=4h(u)-2h(u+\log4)$ for the continuous long lags. Its translated mean against the positive theta source vanishes. If $L(u)<-1$ throughout $|u-T|\le8\log(T+2)$, the function $-L(u)-1$ is nonnegative there. Its theta mean equals minus the total theta mass, yet its contribution from outside the window is bounded below by $-Ce^{-T}$. Indeed the strip bound for $L$ and the theta moment of order $T+1/2$ give this tail bound. Positivity of the total mass gives a contradiction at every large $T$. [Theta leakage estimate](../../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/PositiveKernelLeakage.lean)

Choose such a point with $L(u)\ge-1$ and round $e^{u/2}$ upward. The displacement in $2\log n$ is at most two. The difference $Q(D_n)-L(u)$ tends to the fixed short-lag limit as $u\to\infty$, so $Q(D_n)$ is bounded below and the integrated ordinary contact is bounded above on these conductors. After restoring the floors the mesh error costs $O(n)$ at any multiplicity. For $1\le m\le n$ the actual floors save $cn^2$. For $m>n$ the mesh error costs at most $O(m^2)$. One base therefore bounds the ordinary generators simultaneously. [Mesh error](../3-formalized/acs-the-mesh-error-at-diagonal-multiplicity.md) · [Ordinary floors](../3-formalized/acs-prime-floor-loss-on-the-diagonal.md)

The open pointwise comparison requires the same bound at each prescribed conductor.

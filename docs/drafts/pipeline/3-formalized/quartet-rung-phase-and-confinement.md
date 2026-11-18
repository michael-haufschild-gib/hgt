# Phase and confinement of the two quartet rungs

Both Lean modules passed the direct source check. The three phase theorems and the joint confinement bound depend only on `propext`, `Classical.choice` and `Quot.sound`.

Assume a single off-line quartet with right zero $\rho=1/2+\delta+i\gamma$ and multiplicity $m$. Write $L_\pm F=\mathcal LF(\pm\delta+i\gamma)$ and $a(R)$ for the confinement coefficient at ratio $R$.

## Recovering both phases

On every negative plane spanned by $F,G$, the real determinants of the two pairs $(L_+F,L_+G)$ and $(L_-F,L_-G)$ have the same nonzero sign. For $H=sF+tG$, the quartet contribution to its energy is $4m\Re(L_+H\overline{L_-H})$. The on-line and confinement contributions are nonnegative. Thus this real quadratic form in $(s,t)$ is negative definite. If $P$ is the matrix of the four pairings $\Re(L_+F_i\overline{L_-F_j})$, then $\det P=\det((P+P^\mathsf T)/2)+(P_{12}-P_{21})^2/4>0$. Factoring $P$ into the two real coordinate matrices gives the claim.

The two confined rungs span such a plane at every ratio above the second rung. Their averaged amplitudes multiply each right sample by the same nonzero complex symbol and by a nonzero real rung factor. Hence their two readings $\Re(Az),\Re(Bz)$ still determine $z$. For $x=e^t$ there are fixed complex $u,v$ for which

$$H(t)=e^{17t/2}\big(u\,\mathrm{averagedState}(F,t)+v\,\mathrm{averagedState}(G,t)\big)
       =x^\rho/\rho+O(\sqrt{x}).$$

Indeed the inverse map has weights $i\overline B/\det(A,B)$ and $-i\overline A/\det(A,B)$. Apply it to the two state expansions, divide by $2m\rho$, and multiply by $e^{17t/2}$. The ordinary prime wave then gives $\psi(x)-x+2m\Re H(t)=O(\sqrt{x}\log^2x)$ for $x\ge16$. [Lean source](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheTwoQuartetRungsRecoverTheComplexPrimeWave.lean)

## A joint upper bound

At distinct confined rungs $R,S$,

$$a(R)+a(S)\le m\left((16-\delta^2)^{-1/2}-\tfrac14\right).$$

Normalize each null vector $F$ to unit confinement mass. Its null equation gives $st\,a(R)\le m|sL_+F-tL_-F|^2$ for $s,t>0$, by adding the nonnegative square $m|sL_+F+tL_-F|^2$ and the on-line energy. The two normalized rung vectors are orthogonal in the confinement inner product. Bessel's inequality bounds the sum of the squared readouts by the squared norms of the real and imaginary parts of the difference of the representing modes.

The cosine and sine pair at a common frequency has combined inner product $1/(8+\Re z+\Re w)$ by half-line integration. Thus the two difference-mode norms sum to $s^2/(8+2\delta)+t^2/(8-2\delta)-st/4$. Taking $s=\sqrt{8+2\delta}$ and $t=\sqrt{8-2\delta}$ gives the bound. An independent arithmetic lower bound for the confinement remains open. [Lean source](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheQuartetDepthBoundsBothConfinements.lean)

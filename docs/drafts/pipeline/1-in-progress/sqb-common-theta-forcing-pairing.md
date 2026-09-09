# SQB39 — common-forcing scalar pairing

Proof chain: literal theta source -> normalized packets with vanishing full native residual at every Xi target -> occurrence -> critical line -> RH.

Hardest obstacle: actual scalar pairing m(q) controlling the complete native Gram. Conjecture under analytical/Lean audit: with P the complete positive theta periodization, J(y)=integral_[0,1) P(x+iy) dx, and h_q the actual common-forcing height profile,

  <P,W_q> = integral_(0,infinity) y^-2 J(y) h_q(y) dy;
  m(q) = -1/4 [integral y^-2 J(y) h_q(y) dy - M^2/(V(1+z_q^2))].

J is strictly positive and independent of q; V=<1,1>, M=sourceMass. Every primitive row is retained in P. No normalized small-residual estimate is asserted.

Analytical proof: modular invariance plus reduction to the fundamental domain upgrades the already proved cell bound for P to a global bound. All-power bounds for h_q admit its strip integral, hence h_q P by bounded multiplication. Full absolute primitive-row unfolding gives the native product. Strip Fubini isolates J. Orthogonality to the true constant vector gives the displayed correction.

This uses actual source producers (all-power theta bounds, modular invariance, absolute row unfolding), not an assumed equal-Gram interface. The remaining task after this identity is a source estimate on these literal integrals that produces normalized small residuals.

# HagedornBootstrap: hexagon 2611.00174 / 2611.00175 transferred to the Lean corpus

Papers: hexagon 2611.00175 (Hawking–Page transition at weak coupling), 2611.00174 (spinless modular bootstrap slope Λ_V).
Lean folder: formal/GaloisForLFunctions/HagedornBootstrap/ ; umbrella formal/GaloisForLFunctions/HagedornBootstrap.lean (imported by MainTheorems.lean).
Status: 23 modules, each checked clean with `lake --old env lean`; 354 theorems; axioms only propext, Classical.choice, Quot.sound.

## Modules
- LetterCounting — N=4 letter census 2(k²−1), z(y)=2y²(3−y)/(1−y)³, Hagedorn point y_H=2−√3, slope 3/2, d₁(x_H)=3/2, T_H·(1+2g²)
- QuadraticUnits — e^{nβ₀/2}=Pell numbers (corpus pell_three); arsinh 1 = log of ℤ[√2] unit (corpus SqrtTwo)
- BootstrapSlope — Λ(x)=1/(1/12+x²/3), Λ_V=12π²/(π²+4arsinh²1), 9.12<Λ_V<9.13
- GrossWittenWall — density ≥0 iff |u|≤1/2 (sharpens corpus degree-one cosine lemma), GWW potential C², third-derivative jump 8, wall ≍ (4/3)ε³
- PolyakovLandau — heavy-mode exchange = corpus heavyChannel Schur complement, first-order coexistence (b<0), second order = corpus Landau minimum (b>0)
- CumulantAndScheme — scheme invariance of b, cumulant/convexity of log Z
- HagedornPole — Σz^m pole at y_H, divergence of confined free energy, Duhamel divided differences
- HagedornNecklaces — pure YM x_H=2−√3, T_H(YM)=2T_H(N=4); necklace series radius 1/a (corpus NecklaceGrowth)
- EinsteinHawkingPage — corpus AdS Gauss–Bonnet thermodynamics at ℓ=q=0: exact HP at 3/(2π), T_min=√2/π, thermal AdS always stable
- TanhGaussianFloor — −z²/3 ≤ log(|tanh z|/|z|) ≤ 0
- OneSidedEulerMaclaurin — midpoint/trapezoid/centred-monotone bounds; log n!, H_n ≤ log(2n+1)
- SlitStripMap — vacuum tan(π/8), tips 1±√2, folding of the boundary map
- EdgeFunction, ZeroLawAndDeficit, TipsWallsAndCounts — edge function convexity, zero law concavity and linear bounds, Cardy deficit κ(δ)>0, counting bounds, Hellerman = edge tip, far minimum ε*=½√(B/2−m)
- StripBlaschke — T1–T4 toolkit, detuned pairs, detuning cost e^{2ε²/d²}, site-weight derivative
- CardyWeight, CardyKernelBessel, BesselSeries, EdgeRootAndKernel — Cardy kernel series and Laplace identity, vacuum = Cardy continuum, V ≥ 8π⁴t², half-mass; corpus I₀ (series) = corpus I₀ (integral); corpus J₀ series; J₀(4π√(st)) = K_{−s}(t); ‖I₀(z)‖ ≤ I₀(Re z), edge Cardy growth
- CrossingKernelFourier — 𝓕Ξ_β = −Ξ_β, f(0) = −∫f, Cohn–Elkies dictionary
- EigenIdentity — Laplace transform of K_α at every real α; planar transform with one kernel K_{−s} (corpus J₀ for s ≥ 0); crossing kernel and its finite combinations are −1 eigenfunctions at every real s; eigen-identity g(−α) = −2π∫gK_α; vacuum value = −2π∫gV
- CurieWeissTwin — sheet map involution, tanh law, Curie point ξ₁=1/π², band offset ∫₀¹artanh ρ/ρ = π²/8 (corpus odd Basel)

## Open
- Laguerre −1 eigenfunctions and the planar Hankel transform (paper 174 §2.3) not formalized.
- Potential-theoretic optimality (paper 174 Thms 3, 4, 7) needs harmonic measure on the slit strip; not in the corpus.

# BAG signed transfer of the complete growing source

01av. Route BAG; RH goal active. Corpus basis: M1
ChiRamanujanMixedCompletedSource, M2 ChiRamanujanMixedProfileCancellation,
U3 ChiRamanujanUniformSourceEnvelope. All refer to the actual complete
labelled source with both cofactors, both masks and allowed collision.

Conjecture U4: for fixed positive rho_i and every fixed Schwartz Phi on R²,
the integral of Z_N(t1,t2)*Phi(t1,t2), divided by L=logN, tends to zero.
No physical-profile substitution is authorized by this statement.

Paper proof: partition into |t1|<=|t2| and its strict complement. In the
first sector put t1=x/L,t2=y. The normalized integral becomes the integral
of 1_[|x|<=L|y|]*Z_N(x/L,y)/L²*Phi(x/L,y). The U3 second axis kernel is
bounded by its first axis kernel on this sector. Schwartz decay of order
56 cancels U3's polynomial weight and leaves the integrable product
2*C*B/((1+|x|)²*(1+|y|)²), independently of N. For y!=0 the indicator tends
to one and M1 gives exp(-2gamma)*G(rho1+i*x)*Phi(0,y). M2 makes its x
integral zero. The exceptional line y=0 is null. Dominated convergence
therefore cancels the whole first sector. Exact source exchange of the
first two labels gives the second sector, with rho2 and Phi(y,x).
Their partition is exact, including its boundary. This avoids any extra
compact-uniform remainder or separate joint-box estimate for fixed tests.

Formal obligations: source symmetry/measurability, decay majorant,
rescaling/Fubini, almost-everywhere M1, dominated convergence, assembly.
These are not yet Lean proved. The actual moving physical profile has
shrinking cutoff edges; its source-weighted tail/compactness or direct
signed cancellation remains the next hard mathematical problem.

Search67960 nonpartial65997files; coverage generation1248279=current;
noerrors, background refresh incomplete. All20 candidates+20 source
arguments inspected. Broad semantic hits mostly unrelated; exact M1/M2/U3
source and actual local definitions inspected instead. No numerical
experiment, added premise, heartbeat change or route pivot.

U4 formalization01av: exact first/second source exchange and arithmetic
measurability developed, followed by nearest-axis rescaling, uniform
product majorant and almost-everywhere mixed-profile limit. Scratch
/tmp/bag-signed-sectors-01av.lean now through dominated-convergence
cancellation. Final unscaled integral partition/assembly remains. Not
yet Lean audited. Source imports hit one missing shared olean; restored
only needed Sieve/MoebiusSavingKappaTwo via foreground5864emptyPASS.
No full/umbrella build. Final source audit still pending.

Shared dependency cache is being rebuilt externally: scratch36939 failed
on missing MoebiusKappaTwoTerms; it was restored externally. Scratch10624
then failed on missing MoebiusKappaTwoRate. Owned restore88063 was cancelled
exactPIDs16650/16597,terminal143, after detecting a preexisting external
compiler writing the same olean. No external process touched. Only other
missing dependency XiMassHyperbolicCurvedContourDecay is now being restored
with a single owned foreground leaf audit. U4 scratch includes complete
full-plane assembly,still unverified; no source theorem marked complete.

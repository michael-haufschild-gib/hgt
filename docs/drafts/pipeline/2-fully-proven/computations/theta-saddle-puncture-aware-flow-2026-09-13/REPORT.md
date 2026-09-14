# Bounded theta-source saddle flow: exploratory outcome

All16target calculations reached their finite stopping rules in16.18seconds. They produced312finite trajectory records from78numerical saddle instances. This fixes the previous pilot's unbounded integration problem, but it is not evidence that the resulting contour decomposition is complete or correct.

The source is Phi(z)=sum(n>=1)exp(z/2)(4q_n^2−6q_n)exp(−q_n), q_n=pi*n^2*exp(2z). For the literal integrand Phi(z)exp(−iwz), the action is locally S=−log Phi+iwz. Saddles solve Phi'−iwPhi=0. The16frozen targets combine selected real zeta ordinates, neighboring midpoints and explicitly nonzero/nonreal controls. Those labels do not confer zero status on the controls.

Across312paths,280have wrapped phase drift below1e-6. The32remaining paths hit the iteration budget; some drift by as much as0.1102radians. Their endpoint labels and apparent lack of intersections are inconclusive. The retained paths approach source nodes or the finite domain boundary, and some cross the real axis. Counts vary between targets, but these data do not establish thimble coefficients, complete saddle coverage or a relation to spectral zeros. No flow-topology observation is added to the shared fact ledger.

The numerical changes were RK4 step doubling, step limits tied to Newton distance from source zeros and distance from the domain boundary, and explicit node/boundary/critical-point/iteration/arclength stopping. The physical source itself was unchanged. Source zeros are regular zeros ofPhi and singularities only of the chosen logarithmic action.

Interpretation for RH: numerical flow termination cannot be treated as extinction, a missing saddle cannot be treated as absence, and an unassigned integration cycle cannot be replaced by a guessed coefficient. The useful survivor is a finite set of source-saddle seeds and reasonably phase-stable path segments for a future, independently justified contour reconstruction. The experiment supplies neither complete HB action identification nor source-enforced selection.

After the user's stricter novelty instruction, further standalone flow scans or step-size tuning are not admitted as discovery. A possible technical validation method would lift rays of the normalized integrand directly, combining inverse-function continuation with source contours; that method has not been launched and is not claimed as a research breakthrough. Any future experiment must attack a new structural assumption through an unusual, justified mechanism.

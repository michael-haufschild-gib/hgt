# Fixed-time phase-graph Sobolev blindness and entropy traps (2026-08-10)

Created `docs/drafts/pipeline/2-fully-proven/fixed-time-phase-graph-sobolev-blindness-law.md`.

## Exact results
- For any probability space Omega, measurable phase map Phi: Omega -> T^d, graph law mu(domega) delta_Phi(omega), and conditional completion mu x Haar, d>=3, there are phase-smooth 0<=F_epsilon<=1 with graph expectation 1 but completed mean/variance O(epsilon^d) and phase Dirichlet energy O(epsilon^(d-2)).
- Scaled bump proof extends to every integer phase Sobolev order k with 2k<d: H^k norm squared is O(epsilon^(d-2k)) while graph expectation stays 1.
- In maximal-projective-rank D-dimensional quantum systems d=D-1, any generic Sobolev restriction method requires order at least (D-1)/2. For n qubits, every poly(n)-order derivative hierarchy is structurally blind.
- Separate Duhamel/metric-entropy theorem: for H(theta)=sum theta_j h_j, theta in radius-R subset of R^m, B=(sum ||h_j||op^2)^1/2, the time-t state image has epsilon-cover size <= (1+2R|t|B/epsilon)^m.
- For m=O(n), RB=poly(n), |t|<=2^n, the whole fixed-time ensemble image needs only O(n^2) arbitrary codebook index bits. Thus source entropy/selector bits cannot witness exponential circuit complexity; cover centers may themselves be exponentially hard.

## Conjecturing loop
- C0 low Dirichlet influence -> fixed-time graph mixing: falsified.
- C1 poly(n) higher derivatives repair it: falsified generically.
- C2 transverse phase smoothing: valid but changes autonomous static model.
- C3 selector information/rate distortion reaches Brown scale: falsified by the small arbitrary-cover theorem.
- C4 survivor: prove gate-generated tracking-capacity bound. Need use Hamiltonian-independent shallow local circuit incidence, not target count, source entropy, minimum action, generic phase smoothness, or completed variance.

## Corpus updates
- Parent `low-replica-complete-incidence-influence-law.md` exact-next-move was corrected: generic Dirichlet-dual mixing retired.
- `static-circuit-two-memory-orthogonality-law.md` gained normalized angle Corollary B.1: below baseline fraction beta, any shortcut forces explicit positive cosine between oscillatory static memory and circuit-preparation memory.
- Publication paper untouched.
- Lean deferred under active corpus-refactor instruction; no Lean process started.
- Structural audit: unique tags, no trailing whitespace, git diff --check clean.

## Honest significance
Underlying scaled-bump/Sobolev trace and Duhamel covering engines are classical. New project-level knowledge is decisive falsification of two proposed Brown-proof architectures and sharpening of the open invariant to local-circuit tracking capacity. Brown growth remains unproved.
# Second- and third-band renormalized defect calculus

- **ID:** thim-second-third-band-defect-calculus
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Complementary quotient laws and damped divisor envelopes control renormalized prefix defects through the second and third horizon bands.

## Requirements and plan
- [x] Read the current field README completely and search current corpus; preserve README.
- [ ] Prove trans-horizon Möbius identity and three-valued response at odd checkpoints through 3N, and nonpositivity on the entire requested interval including its sub-horizon part.
- [ ] Prove damped nonpositivity, removing the prime-or-envelope restriction by reusing the newly available mass bound.
- [ ] Prove the corrected third-band identity above N, and nonpositivity throughout the full 6-coprime range through 4N.
- [ ] Develop exact prime deletion/switching calculus where it broadens these ranges.
- [ ] Compile original sources using `lake --old env lean`, audit all declarations' axioms, wire umbrella, refresh index, run formal lint, remove scratch files, save knowledge and evidence.

## Structural correction and positive survivor
The requested assertion s_N(mu,k)=-mu(k) on all 2<=k<=4N with k coprime to 6 is false below the horizon: for 2<=k<=N the full divisor sum is zero, whereas -mu(k) need not vanish. The correct identity is piecewise, zero below the horizon and -mu(k) above it. This preserves the full claimed nonpositivity range because both branches have absolute value at most one. Record a general squarefree witness family, not a numerical counterexample.

## Corpus inputs and proof design
- `ComplementaryQuotientAndSecondOctaveLaw` supplies odd/6-coprime tail collapse and exact deleted quotient terms through 3N and 4N.
- `two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary` is the all-horizon polarization identity underlying Pillar VII.
- `AllHorizonRadicalSawtoothAndDefectReduction.pmPowerDampedDivisorCoeff_add_abs_weight_le_one` is a concurrent source theorem located by corpus search. Reuse after its dependency is compiled; do not duplicate its proof.
- For epsilon>=0, |tau_epsilon(k)-c_epsilon(k)|<=tau_epsilon(k)+|c_epsilon(k)|<=1. Below the horizon, tau lies in [0,1]. Thus rough band tail collapse gives the desired envelope, then polarization gives D<=-energy/2<=0.
- Candidate strengthening: for prime p and k=p*u, tau(k)-c(k)-c(u) is tau(u)-c(u) when p|u, and (1-p^(-epsilon))(tau(u)-c(u)) otherwise. This should bound every second-band checkpoint and third-band checkpoints with at most one of 2,3 dividing k.

## Constraints and evidence
No RH focus, hgtl7, numerical experiments, added axioms, conjectural premises, heartbeat changes, full builds, or unrelated edits. Prime/domain conditions specify the problem, not unproved hypotheses. Serena symbol tools reject ignored Lean paths (verified earlier this session), so direct source reads and patch edits are used. `update_plan` is unavailable; this card persists the plan. Existing live work in `AllHorizonRadicalSawtoothAndDefectReduction` belongs to another agent and remains read-only.

## Dependency-closed paper proof
Let c(n)=mu(n)n^(-epsilon), tau(n)=sum_{d|n}c(d), epsilon>=0. The existing mass bound tau(k)+|c(k)|<=1 for k>=2 implies |tau(k)-c(k)|<=1. Below the horizon, s_N(k)=tau(k) lies in [0,1]. For a B-rough k<= (B+1)N, the only omitted divisor above the horizon is k itself, giving s_N(k)=tau(k)-c(k). Thus the unit envelope holds on both sides of the horizon.

For prime p and k=p*u, multiplicativity and squarefree support give c(p*u)=0 if p|u, and c(p*u)=-p^(-epsilon)c(u) otherwise. The already proved radical formula gives tau(p*u)=F*tau(u), where F=1 if p|u and F=1-p^(-epsilon) otherwise. Consequently tau(p*u)-c(p*u)-c(u)=F*(tau(u)-c(u)). Since 0<=F<=1, this deleted-prime response has absolute value at most one for u>=2.

In the second band 2N<k<=3N, the response deletes k and, only when even, k/2. The odd branch is the basic terminal-deleted bound; the even branch is the prime-deletion contraction with p=2 and u=k/2>=2. Hence every k in [2,3N] has unit envelope, without a parity condition. In the third band 3N<k<=4N, at most one prime quotient is deleted whenever either 2 or 3 does not divide k. Apply the same contraction with p=2 or p=3. This includes every odd endpoint through 4N, not merely the originally requested odd range through 3N.

For M>=1, polarization says 2D_N(M)=-E_N(M)+s_N(M+1)^2-s_N(1)^2. All ranges above force N>=1 and s_N(1)=1. The envelope therefore yields 2D_N(M)<=-E_N(M)<=0. Zero damping specializes to literal Möbius weights.

## No-go closure for the unsplit third-band identity
- **Obstruction:** For every prime p>3 and N>=p, p is coprime to six, s_N(mu,p)=0, and -mu(p)=1. Thus the original all-range response identity fails as a family, not just at one numerical example.
- **Positive survivor:** Exact piecewise response is zero below the horizon and -mu(k) above it; the full requested defect nonpositivity range survives. Prime-deletion contraction further extends nonpositivity to every checkpoint through 3N and to all endpoints missing either two or three through 4N.
- **Lean declarations:** `sieveSeq_moebiusReal_coprime_six_subhorizon_counterfamily`, both `*_through_*` response theorems, and `sieveRenormalizedPrefixDefect_*_three_mul_nonpos` / `*_four_mul_nonpos` in the target. Final compiler and axiom audit pending.

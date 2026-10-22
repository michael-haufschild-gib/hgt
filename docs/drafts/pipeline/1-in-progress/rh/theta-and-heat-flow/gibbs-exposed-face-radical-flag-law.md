# Gibbs exposed-face radical flag law

- **ID:** `gibbs-exposed-face-radical-flag-law`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE; `[NOVELTY UNVERIFIED]`
- **Source:** source-marked isoradical Gibbs geometry
- **Statement:** A finite positive Gibbs ray remains in one Gram-radical chamber at every finite temperature, but its canonically normalized zero-temperature boundary is exactly the Gram form restricted to the exposed maximum-energy face; successive energy levels determine a canonical nested radical flag.

## Goal

Let `P` be finite, let `c_j(p)` be a finite coefficient packet, let `a_p>0`, and let `E_p` be a
real source marking.  Define

\[
  G_k(q)=\sum_{p\in P}a_p e^{kE_p}
       \left|\sum_jq_jc_j(p)\right|^2,
  \qquad R=\max_{p\in P}E_p.
\]

At every finite `k`, positivity of all weights gives the same radical:

\[
  \ker G_k=\left\{q:\sum_jq_jc_j(p)=0\text{ for every }p\in P\right\}.
\]

The new boundary statement is

\[
  e^{-kR}G_k(q)\longrightarrow
  G_R(q):=\sum_{E_p=R}a_p
       \left|\sum_jq_jc_j(p)\right|^2,
\]

and therefore

\[
  \ker G_R=\left\{q:\sum_jq_jc_j(p)=0\text{ on the exposed top face }E_p=R\right\}.
\]

If the distinct energy levels are `R=r_1>...>r_m`, the exact decomposition

\[
  G_k=\sum_{h=1}^m e^{kr_h}G_{r_h}
\]

gives the nested cumulative radical flag

\[
  \ker G_{r_1}\supseteq
  \ker(G_{r_1}+G_{r_2})\supseteq\cdots\supseteq
  \ker(G_{r_1}+\cdots+G_{r_m})=\ker G_k.
\]

Thus a Gibbs ray has an interior matroid and a canonical exposed-face boundary flag.  The geometry
is a constraint degeneration, not a flow generating the HT object.

## Positive route constraint

Any proof mechanism based on cooling a positive metric must acquire its new information through
the exposed-face radical flag.  Finite-temperature positivity alone stays in the interior
radical chamber.  A nontrivial critical statement must force the exposed top face to equal a
specified source face, or control how the face behaves under cofinal growth.

## RH audit

For the Xi projective energy

\[
  E_\rho=|\Re\rho-1/2|,
\]

RH is equivalent to the statement that every energy is zero.  Hence every finite divisor aperture
has the whole aperture as its top face.  If RH is false, any aperture containing both a critical
zero and a zero with positive displacement exposes a proper face at zero temperature.  With a
point-separating coefficient packet this becomes a strict boundary-rank loss.  The remaining
global issue is cofinal face escape when the supremal displacement is not attained.

## Dual gate

- **Novelty:** The individual Laplace principle, diagonal torus action, and matroid restriction
  are classical.  Candidate novelty is the exact interior-radical/exposed-boundary-radical flag
  law for source-marked HT coefficient carriers, especially its cofinal infinite-support form.
- **Significance:** The law identifies the only geometric locus where a cooling argument can gain
  arithmetic information and converts temperature asymptotics into a canonical sequence of
  differential-matroid contractions/restrictions.
- **Retirement condition:** Move to `not_new_scientific_knowledge` if an equivalent
  Gibbs-to-exposed-matroid-radical flag theorem is found in toric Grassmannian or tropical
  exponential-family literature.

## Approach

1. Prove the exact finite energy-level decomposition.
2. Prove the top-face normalized limit and its exact radical.
3. Prove the cumulative radical inclusions and equality criteria.
4. Instantiate on signed prime-Dirichlet coefficient packets.
5. Isolate the cofinal infinite-support face-escape alternative.

## Gates

- [x] 0 -> 1: exact source-pure statement and proof architecture
- [ ] 1 -> 2: complete finite and cofinal paper proofs
- [ ] 2 -> 3: unconditional formal theorems and touched-file verification
- [ ] Novelty gate: toric/tropical parent-theory audit
- [ ] Significance gate: non-zeta HT specialization and a nontrivial RH consequence

## Log

- 2026-07-14 -- Created after the simpler isoradical/free-energy product statement collided with
  classical torus-orbit and tropical thermodynamic geometry.  The new target is the radical jump
  and canonical flag at the tropical boundary.

# Suzuki admissible shifts evacuate transversely under false RH

- **ID:** `suzuki-admissible-shift-transverse-evacuation`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [FORMALIZATION IN PROGRESS] [EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Source:** Suzuki's shift condition `lambda<lambda_0(a)` plus
  `smooth-regularization-transverse-weil-floor-amplification.md`
- **Statement:** Every false-RH admissible Suzuki shift schedule has arbitrarily late negative
  excursions faster than every subcritical transverse power. Equivalently, an eventually
  bounded-below admissible schedule exists exactly under RH.

## Goal

Classify the absolute shift scale before studying projective carriers. Previous Route-G text
treated a finite absolute shift cluster as a possible unconditional compactness mechanism. The
literal restricted-Weil floor decides that question completely.

## Setup

At logarithmic apertures `a_n=(1/2)log n`, let `lambda_0(n)` denote Suzuki's true restricted-Weil
spectral floor and

```text
eta(n)=max(0,-lambda_0(n)).                              (1)
```

A Suzuki shift schedule `sigma(n)` is admissible when

```text
sigma(n)<lambda_0(n).                                   (2)
```

The inward-regularization theorem proves that, under false RH, for every
`0<=alpha<delta_*`, `C>=0`, and `N_0`, some `n>=N_0` satisfies

```text
C n^alpha<eta(n),                                      (3)
```

where `delta_*>0` is the right-transverse Xi supremum.

## Transverse shift evacuation

At an index supplied by `(3)`, the right side is positive, so `(1)` forces

```text
C n^alpha<-lambda_0(n).
```

Combining with `(2)` gives

```text
sigma(n)<lambda_0(n)<-C n^alpha.                        (4)
```

Thus every admissible schedule, without regularity or convergence assumptions, has arbitrarily
late negative excursions beyond every subcritical transverse power.

## Exact RH equivalence

Suppose an admissible schedule is eventually bounded below: for some `B` and all large `n`,

```text
B<=sigma(n)<lambda_0(n).                                (5)
```

If RH were false, apply `(3)` with `alpha=0` and
`C=max(-B,0)+1`. Then

```text
max(-B,0)+1<max(0,-lambda_0(n)).                        (6)
```

But `(5)` gives `-lambda_0(n)<-B`, hence

```text
max(0,-lambda_0(n))<=max(0,-B),                         (7)
```

contradicting `(6)`. Therefore an eventually bounded-below admissible schedule implies RH.

Conversely, under RH every restricted-Weil floor is nonnegative. The constant schedule
`sigma(n)=-1` is admissible and bounded below. Hence

```text
RH
 iff there exists an admissible Suzuki shift schedule bounded below on one tail.  (8)
```

No limit `sigma(n)->0` is required. This strictly strengthens the already known zero-shift and
vanishing-shift criteria.

## Route-G consequence

- A finite absolute shift cluster, compact absolute shift window, or any tail lower bound is
  already RH-strength. It cannot be assumed by an unconditional Suzuki producer.
- Under false RH the whole admissible half-line translates left at transverse exponential scale.
- This does **not** kill ground-centered schedules
  `sigma(n)=lambda_0(n)-tau(n)`: their absolute values evacuate with the floor while their
  projective gap `tau(n)>0` can retain nontrivial centered resolvent geometry.
- Therefore the live producer is not “choose a compact family of shifts.” It is a centered
  spectral-measure problem for `A_a-lambda_0(a)I`, with the far-free and ground-Cayley boundaries
  removed and the even/odd source transport controlled.

## Novelty audit

- Suzuki proves the finite-aperture admissibility inequality.
- Existing project work proves zero-shift and shifts tending to zero are RH-equivalent.
- Existing floor work proves transverse amplification but does not compose it with arbitrary
  Suzuki schedules.
- Repository and targeted arXiv searches found no bounded-below-schedule equivalence or
  quantitative transverse evacuation law `(4)`.
- The order argument is elementary; candidate novelty is the exact literal Suzuki/Weil
  classification and its removal of the finite-shift-cluster frontier.

## Gates

- [x] 0 → 1 in-progress: literal source theorem, exact proof, survivor identified
- [ ] 1 → 2 fully-proven: hostile paper audit
- [ ] 2 → 3 formalized: `SuzukiAdmissibleShiftEvacuation.lean`, axioms, lint, targeted build,
  umbrella wiring
- [ ] 3 → 4 publication-ready: external novelty audit and integration into Suzuki manuscript

## Log

- 2026-08-07 — Combined Suzuki admissibility with transverse restricted-floor amplification;
  closed bounded-below absolute schedules exactly at RH and isolated centered gap geometry as the
  only surviving shift scale.

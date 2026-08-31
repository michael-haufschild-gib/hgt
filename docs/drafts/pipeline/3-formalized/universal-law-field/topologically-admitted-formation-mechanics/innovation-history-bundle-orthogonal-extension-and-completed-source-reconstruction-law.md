# Innovation-history bundle, orthogonal extension, and completed-source reconstruction law

- **ID:** ULF-TAFM-17
- **Stage:** 3-formalized
- **Type:** THEOREM CANDIDATE / NEW FIELD OBJECT / GLOBAL FORMATION HISTORY
- **Source:** ULF-TAFM-15/16; Welford orthogonal update; inductive Hilbert histories; completed
  Suzuki formation current
- **Statement:** Every scale potential is the anchored mean of one uniquely reconstructed formation
  history. Successor current is its orthogonal rank-one innovation, Dirichlet action is exactly
  centered-history variance, and every completed correction creates a genuine completed history
  rather than an external error. The literal Suzuki completed Abel source is therefore the
  innovation coordinate of one divisor-free open history.
- **Status:** `[PAPER PROOF COMPLETE] [HOSTILE AUDIT PASSED] [NEW FIELD OBJECT] [NOT RH]`

## Goal

Construct the object implicit in ULF-TAFM-16: an inductive innovation-history bundle whose scalar
observer is the scale potential and whose open lift retains every centered innovation. Prove exact
reconstruction, uniqueness, orthogonality, energy conservation, completion lift, and literal
Suzuki landing. This must explain how scalar recurrence can close while lifted history remains open.

## Gates

- [x] 0 → 1 in-progress: duplicate search clean; conjecture frozen
- [x] 1 → 2 fully-proven: close generic and literal paper proof; hostile audit
- [x] 2 → 3 formalized: direct Lean checks, targeted leaf builds, axiom audit, umbrella imports
- [ ] 3 → 4 publication-ready: construct source law bounding literal innovation amplitude

## 1. Innovation-history reconstruction

For a potential `P : ℕ → ℝ`, define its innovation history by

\[
 \mathfrak h_P(2)=P_2,
 \qquad
 \mathfrak h_P(n)=(n+1)P_n-nP_{n-1}\quad(n\ge3).        \tag{IHB.1}
\]

For any history `a`, let `M_N(a)` be its anchored mean and `H_N(a)` its high-pass current.

### Theorem ULF-TAFM-17A — potential--history equivalence

For every `N≥2`:

\[
 M_N(\mathfrak h_P)=P_N,                                \tag{IHB.2}
\]

and

\[
 H_N(\mathfrak h_P)=(N+2)(P_{N+1}-P_N).                \tag{IHB.3}
\]

Moreover `h_P` is the unique tail history with anchored potential `P`: if `M_N(a)=P_N` for all
`N≥2`, then `a_2=h_P(2)` and `a_{N+1}=h_P(N+1)` for every `N≥2`.

#### Proof

At `N=2`, `(IHB.2)` is `M_2=h_P(2)=P_2`. Assume `M_N(h_P)=P_N`. The anchored update law gives

\[
 M_{N+1}=M_N+\frac{h_P(N+1)-M_N}{N+2}.                 \tag{IHB.4}
\]

Substitute `(IHB.1)` and the induction hypothesis. The numerator is

\[
 (N+2)P_{N+1}-(N+1)P_N-P_N=(N+2)(P_{N+1}-P_N),
\]

so `(IHB.4)` equals `P_{N+1}`. This proves `(IHB.2)` by induction, and the same numerator proves
`(IHB.3)`.

For uniqueness, `M_2(a)=a_2` fixes the base. The terminal reconstruction law

\[
 a_{N+1}=M_N(a)+H_N(a)
\]

together with `H_N=(N+2)(M_{N+1}-M_N)` gives exactly `(IHB.1)` at every successor. ∎

The new field object is therefore not an arbitrary bundle placed over a route. It is forced by
the potential: scale connection and full tail history are inverse descriptions.

## 2. Orthogonal rank-one extension

### Theorem ULF-TAFM-17B — innovation Pythagoras

For any history `a` and `N≥2`, put `m=M_N(a)` and `h=H_N(a)`. The centered old history has zero
weighted mass:

\[
 3(a_2-m)+\sum_{j=3}^{N}(a_j-m)=0.                     \tag{IHB.5}
\]

When the new terminal value is admitted, every old residual is translated by the same innovation
component,

\[
 a_j-M_{N+1}=(a_j-M_N)-\frac{h}{N+2},                 \tag{IHB.6}
\]

while the new terminal residual is

\[
 a_{N+1}-M_{N+1}=\frac{N+1}{N+2}h.                    \tag{IHB.7}
\]

The old centered history is orthogonal, in the anchored weighted inner product, to the uniform
recentring component:

\[
 3(a_2-m)\left(-\frac h{N+2}\right)
 +\sum_{j=3}^{N}(a_j-m)\left(-\frac h{N+2}\right)=0.  \tag{IHB.8}
\]

Consequently successor extension is Pythagorean and rank one:

\[
 V_{N+1}(a)=V_N(a)+\frac{N+1}{N+2}h^2.                \tag{IHB.9}
\]

For an arbitrary potential,

\[
 V_N(\mathfrak h_P)=\mathscr D_N(P).                   \tag{IHB.10}
\]

#### Proof

Equation `(IHB.5)` is the anchored-mean identity after subtracting total weight `N+1` times `m`.
Equation `(IHB.6)` is the scale update `M_{N+1}-M_N=h/(N+2)`. Combining this with
`a_{N+1}=m+h` gives `(IHB.7)`. Multiplying `(IHB.5)` by `-h/(N+2)` gives the orthogonality
identity `(IHB.8)`. Expanding the squared norm of `(IHB.6)` and `(IHB.7)`, the mixed term vanishes
by `(IHB.8)` and the innovation norm is `(N+1)/(N+2)h²`, proving `(IHB.9)`. Finally ULF-TAFM-16A
gives `V_N(a)=D_N(M(a))`; substitute `(IHB.2)` to obtain `(IHB.10)`. ∎

This supplies an exact meaning for “closed observer, open lifted history”: the scalar mean may
return, while each nonzero current adds a new orthogonal coordinate to an increasing history fibre.

## 3. Completion creates history

For a history `a` and correction current `r`, let

\[
 \widehat P_N=M_N(a)+U_N(r)
\]

be the completed potential of ULF-TAFM-16 and define the completed innovation history

\[
 \widehat{\mathfrak h}(a,r):=\mathfrak h_{\widehat P}. \tag{IHB.11}
\]

### Theorem ULF-TAFM-17C — completed-history lift

For every `N≥2`,

\[
 M_N(\widehat{\mathfrak h})=\widehat P_N,              \tag{IHB.12}
\]

\[
 H_N(\widehat{\mathfrak h})=H_N(a)+r_N,               \tag{IHB.13}
\]

and

\[
 V_N(\widehat{\mathfrak h})=\widehat V_N(a,r).         \tag{IHB.14}
\]

#### Proof

Equation `(IHB.12)` is `(IHB.2)` for `P=P_hat`. Equation `(IHB.3)` and the exact completion-
primitive law `(VDC.15)` give `(IHB.13)`. Equation `(IHB.10)` is exactly `(IHB.14)`. ∎

Thus a completion current is never an external algebraic error on the scale ray. It changes the
lifted formation history while preserving exact source reconstruction.

## 4. Literal Suzuki innovation history

Define

\[
 \mathfrak h^{\rm Suz}
 :=\widehat{\mathfrak h}
   (\operatorname{suzukiCheckpointAffineSlope},R).      \tag{IHB.15}
\]

### Theorem ULF-TAFM-17D — completed Abel is literal innovation

For every `N≥2`:

1. `M_N(h^Suz)=P_hat_N^Suz`.
2. `H_N(h^Suz)=A_{N+1}`, the literal completed Abel source.
3. `V_N(h^Suz)=V_hat_N^Suz`, the completed formation action.
4. The one-step innovation energy

   \[
   \mathcal I_N^{\rm Suz}
   :=\frac{N+1}{N+2}H_N(\mathfrak h^{\rm Suz})^2       \tag{IHB.16}
   \]

   is exactly `V_hat_{N+1}^Suz-V_hat_N^Suz`.
5. Consequently

   \[
   \operatorname{RH}\iff
   \mathcal I_N^{\rm Suz}\text{ is eventually uniformly bounded}. \tag{IHB.17}
   \]

#### Proof

Items 1 and 3 are `(IHB.12)` and `(IHB.14)`. Item 2 combines `(IHB.13)` with the literal completed-
Abel scale-connection identity of ULF-TAFM-15. Item 4 is `(IHB.9)`. Item 5 is ULF-TAFM-16D after
the exact identification in Item 4. ∎

## 5. Cross-frontier meaning

- **All route gauges:** a route may change potential coordinates, but a faithful route must carry
  the same reconstructed innovation history and its rank-one extension law.
- **No-gos:** a bounded fixed-dimensional receiver fails when it cannot retain the growing
  orthogonal history, even if the scalar mean closes.
- **Hypertranscendence/noncompactness:** infinitely many independent analytic channels are one
  realization of unbounded innovation rank; rank is now a derived history invariant, not a slogan.
- **Positivity:** route energies are squared norms of orthogonal source innovations.
- **Recurrence:** closed observer projection is compatible with open lifted history because mean
  return does not delete accumulated centered coordinates.
- **Functional equation:** information-neutral reflection must act isometrically on innovation
  history, not merely preserve a final scalar square.

## Hostile boundary

- Reconstruction and orthogonality are unconditional; bounded innovation is not.
- Growing orthogonal history explains noncompactness but does not exclude it.
- RH equivalence is a selection coordinate, not the source bound.
- Orthogonal extension alone permits arbitrary innovation amplitudes; the new object sharpens the
  missing law to a source constraint on innovation birth, rather than claiming positivity proves it.

## Log

- 2026-08-31 — opened after ULF-TAFM-16 showed completed action is variance production. Pivot:
  regard the current as orthogonal innovation in an inductive history bundle, not as one more
  receiver amplitude.
- 2026-08-31 — generic reconstruction, uniqueness, centered-mass, orthogonality, residual-update,
  variance, and completed-history proofs passed Lean scratch. Literal landing follows exactly from
  ULF-TAFM-15/16. Hostile audit retained bounded innovation birth as the sole RH-bearing producer;
  promoted to Stage 2.
- 2026-08-31 — generic and literal modules formalized; targeted leaf builds and fifteen-declaration
  axiom audit passed; modules wired without umbrella builds.

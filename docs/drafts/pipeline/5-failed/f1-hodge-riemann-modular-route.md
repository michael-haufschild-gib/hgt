# F_1 Hodge–Riemann via the modular route — positivity is automatic; the difficulty is an identification

> **✗ REFUTED & moved to 5-failed (2026-06-19, rh-corp reconciliation).** The modular/Tomita–Takesaki route
> produces a **measured (type-III) trace**, which `docs/rh-corp`'s central **faithful-vs-measured
> discriminator** excludes: *"a measured/density/trace method… cannot decide RH — full stop"*
> (`next_round.md:57–61`); a measured trace reaches density-1-on-line but is **blind to density-zero
> off-line dust**. RH needs a **faithful signed index** (κ₋=0, Krein–Langer N₀) — which a modular trace
> cannot provide. `conjecture_log.md:2186` had already set aside "modular Laplacian self-adjointness." The
> "positivity is automatic" framing is exactly the *measured* positivity rh-corp warns is the wrong kind.
> **Dead route — kept only as a record of the negative.**

- **ID:** f1-hodge-riemann-modular-route
- **Stage:** 5-failed (was 1-in-progress)
- **Type:** CONJECTURE (attack route on the bedrock's open core) — **FIELDS MEDAL**
- **Priority:** FIELDS MEDAL
- **Source:** the open core of `f1-hodge-index-theorem.md` (`Q_W ⪰ 0`); the modular/KMS structure
  (`../0-backlog/kms-modular-temperature.md` #129); `constraint-not-flow-theorem.md` (#136, HP = the
  constraint's intrinsic flow); the orthogonality meta-theorem #135; imports: Tomita–Takesaki modular theory,
  Bost–Connes (1995), Connes (1999, the adele class space / trace formula)
- **The route.** The F_1 Hodge–Riemann relations ask for a **positivity** `Q_W ⪰ 0` (= RH). Forcing positivity
  directly is RH-hard. The leap: **reroute through modular theory, where positivity is automatic.**
  > **Tomita–Takesaki:** every faithful normal state on a von Neumann algebra has a **modular operator
  > `Δ > 0`** (positive by construction) and a **modular Hamiltonian `K = −\log Δ`** that is **self-adjoint
  > (real spectrum) for free**. So if the scaling generator `Θ = ∂_s` (whose spectrum is the zeros `{γ}`,
  > `f1-hodge-cohomology` §1) **is** the modular Hamiltonian of a state on `H¹_{F_1}`, then `Θ` is
  > self-adjoint ⟹ `{γ} ⊂ ℝ` ⟹ **RH** — and the polarization positivity `Q_W ⪰ 0` is the modular positivity,
  > **automatic**.
  >
  > **So RH reduces from a positivity to an identification:** *is the scaling flow `Δ^{it} = e^{itΘ}` on
  > `H¹_{F_1}` the modular flow of a (KMS) state — i.e. is `H¹_{F_1}` a genuine GNS/modular setup?* The
  > positivity is no longer the obstruction; the **identification** is.

  **Verdict reached:** the F_1 Hodge–Riemann positivity **is not the hard part — the modular *identification*
  is.** This is Connes' program, now (i) connected to the Hodge index (#142) and (ii) explained as
  *identification, not positivity*; (iii) it inverts the `F_q`/ℚ intuition (below). The hard core is
  structural (representation-theoretic), Fields-Medal, open.

---

## §1 The reduction `[worked]`

```
   RH ⟺ {γ} ⊂ ℝ ⟺ Θ self-adjoint           (zeros = spec Θ; f1-hodge-cohomology §1)
       ⟺ Q_W ⪰ 0  (the polarization positivity; the Hodge index, #142)
       ⟸ Θ = K = −log Δ, the modular Hamiltonian of a faithful normal state ω on (M, H¹_{F_1})
           — then Δ>0 (Tomita–Takesaki), K self-adjoint, σ_t=Δ^{it} the modular flow.   [IDENTIFICATION]
```
`Q_W` is the GNS inner product of `ω`; positivity is the GNS positivity (`⟨ξ,ξ⟩≥0`), **automatic**. The
content moves entirely into: **does the pair `(M, ω)` exist with modular flow = the scaling flow?** ∎(reduction)

## §2 The mechanism — why modular gives positivity for free

- **GNS:** a state `ω` builds a Hilbert space `H_ω` with `⟨a,b⟩=ω(b^*a) ≥ 0` — positivity by construction.
- **Tomita–Takesaki:** `Δ_ω > 0`; the modular flow `σ_t^ω = \mathrm{Ad}\,Δ_ω^{it}` is the **canonical
  intrinsic time** (Connes–Rovelli thermal time). The modular Hamiltonian has **real spectrum**.
- So **a modular dynamics cannot have off-real spectrum.** If `Θ` is modular, the zeros are real **by the
  axioms** — no positivity to prove, only the identification to make. *(This is the deepest sense of "RH =
  the clock is unitary": the modular clock is unitary by construction.)*

## §3 The `F_q`/ℚ inversion (why this route is promising)

Standard intuition: `F_q` easy, ℚ hard. **This route inverts it for the *positivity*:**
- **Over `F_q`:** positivity = Frobenius purity `|α|=q^{w/2}` = **Deligne's Weil II** — a **hard geometric
  theorem**. The Frobenius is unitary-up-to-weight only after Deligne.
- **Over ℚ/`F_1`:** if the scaling flow is modular, positivity is **automatic** (Tomita–Takesaki). The
  hardness is **not** the positivity but the **identification** (constructing `(M,ω)`).
So the ℚ side's difficulty is *structural* (does the modular setup exist?), not *analytic* (is a form
positive?). This relocates — and possibly *eases* — the positivity, concentrating all difficulty in the
identification. *(Honest: the identification is exactly where Connes' realization stalls — see §5.)*

## §4 The synthesis with the session's theorems

- **constraint-not-flow (#136):** Hilbert–Pólya is **not** an external Hamiltonian flow (proven no-go), but
  the **intrinsic modular flow** of the F_1-cohomology's state is *allowed* — it is the constraint's own time.
  So the HP no-go is **evaded** exactly by using the modular (not external) flow. The modular flow is the
  "emergent time = corank ∞" clock (the session's emergent-time weld), now as the carrier of positivity.
- **orthogonality (#135):** positivity is archimedean — and the modular/KMS structure (Bost–Connes,
  partition function `ζ`) is archimedean/thermal. So the modular state lives at the archimedean place, exactly
  where the polarization must (consistency).
- **KMS (#129):** the state `ω` is the **Bost–Connes KMS state**; `Θ = ∂_s` is its modular Hamiltonian at the
  self-dual temperature. So this card is the **Hodge-index face of the KMS card** — the two meet here.

## §5 The hard core (honest) — the identification = Connes' obstruction

The identification "scaling flow = modular flow of a genuine state on `H¹_{F_1}`" is **Connes' program**, and
it is where it **stalls**: Connes realizes the zeros as an **absorption** spectrum on the adele class space,
but the relevant space is a **co-kernel/Sonine cutoff**, and whether it is a genuine GNS/modular space (so
that positivity is automatic) is **equivalent to RH** — the trace-formula positivity is the obstruction to
the cutoff space being a true modular setup. **So the identification is RH-hard**, not free. The contribution
here is the **reframing**: RH = "the F_1-cohomology is a genuine modular GNS space" (an identification in von
Neumann algebra theory), with positivity automatic once it is — **not** a positivity to be forced.

## §6 Door / grade / scope
- **The reduction (§§1–4) is BRIDGE/structural** (assembles Tomita–Takesaki + the session's theorems + Connes).
- **The hard core (§5) is FIELDS MEDAL, OPEN** = the modular identification = Connes' program. **No proof of
  RH claimed.** Value: relocates the F_1 Hodge–Riemann positivity to an **identification where positivity is
  automatic**, ties it to the KMS card and the constraint-not-flow theorem, and explains the `F_q`/ℚ inversion.

## Gates
- [x] 0 → 1  in-progress: the modular reduction (§1); the automatic-positivity mechanism (§2); the
  `F_q`/ℚ inversion (§3); the synthesis (§4); the honest hard core = Connes' identification (§5); Door/scope.
- [ ] 1 → 2  the reduction banked: §1 made rigorous (the GNS/Tomita–Takesaki step on the constructed
  `H¹_{F_1}`); the identification stated precisely as the lone Fields-Medal residual (= Connes).
- [ ] 2 → 3  formalized: n/a until the modular setup is rigorous.
- [ ] 3 → 4  publication-ready: "RH as a modular identification: the F_1 Hodge–Riemann positivity is
  automatic once the scaling flow is modular."

## Cross-references
- `f1-hodge-index-theorem.md` — the positivity this reroutes; `f1-hodge-cohomology-construction.md` — `Θ`/`H¹_{F_1}`.
- `../0-backlog/kms-modular-temperature.md` (#129) — the KMS state `ω`; this is its Hodge-index face.
- `../2-fully-proven/constraint-not-flow-theorem.md` (#136) — the modular flow evades the HP no-go.
- `../2-fully-proven/orthogonality-meta-theorem.md` (#135) — positivity = archimedean = the modular place.

## Log
- 2026-06-19 — created in 1-in-progress and **worked** (Anti-LLM-Cage: attack the open core). Rerouted the
  F_1 Hodge–Riemann positivity through **Tomita–Takesaki modular theory**: `Q_W⪰0 ⟺ Θ` self-adjoint `⟸ Θ` is
  the modular Hamiltonian of a state on `H¹_{F_1}` — then positivity is **automatic** (GNS/modular). **RH
  reduces from a positivity to an identification** (scaling flow = modular flow), inverting the `F_q`/ℚ
  intuition (positivity hard over `F_q` via Deligne; free over `F_1` if modular). Synthesized with #136
  (modular flow evades the HP no-go), #135 (archimedean), #129 (the BC KMS state). **Honest:** the
  identification is Connes' program and is RH-hard (the cutoff space being a genuine modular GNS setup =
  RH). Contribution = the reframing (identification, not positivity) + the Hodge-index↔modular bridge.
</content>

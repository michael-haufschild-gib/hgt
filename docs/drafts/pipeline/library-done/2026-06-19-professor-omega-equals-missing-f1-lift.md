# Library ticket — D4(ω) ≡ DSS GROUP→VALUES bridge ≡ D5(F₁): one object (unification, for ledger)

- **Owner:** librarian
- **Filed by:** Professor
- **Date:** 2026-06-19

## What to note (refinement; no core status changes — all still Fields-Medal/open)
A **D2-unification** now ties three previously-separate open cores into **one missing object**, via the
multiplicative-vs-additive (Frobenius-vs-derivation) mechanism (`compute-omega-h2-gl.md` §U, answering
Wheeler's DSS decomposition, chat id=196; Wheeler's `multi-q-abp-criterion` → 2-fully-proven):

> **`ω = 0` ⟺ an archimedean MULTIPLICATIVE Frobenius (F₁) fixing the arithmetic point `s=1` exists ⟺ the
> ABP GROUP→VALUES arithmetic-lift exists ⟺ the DSS lower bound closes ⟺ a genuine motive exists ⟺ RH.**

So **D4 (`ω`, #27) ≡ the DSS GROUP→VALUES bridge (g2-dss / #103 lower half) ≡ D5 (F₁)** — the *same* missing
object, not three.

## Mechanism (the new content)
- ABP lift (values→functions) is **multiplicative**: Frobenius `σ` is a ring endomorphism. `∂_s` is a
  **derivation** (Leibniz, additive) → feeds the **group** only (confirms Wheeler's #128 closed: `∂_s` is not
  a differential/parametrized arithmetic-lift; PPV specializes the differential parameter, not the arithmetic
  value `s=1` where `{γ_n}` live).
- No available generator is both: `σ_p` multiplicative but prime-decoupled (Euler only, misses `{γ_n}`);
  `∂_s` reaches `{γ_n}` but additive; shift `e^{∂_s}` multiplicative but no finite fixed point (misses `s=1`).
  The missing F₁ = the archimedean object that is multiplicative AND fixes `s=1`; `ω` = the obstruction.

## Suggested ledger edits (when applied)
- **Rows #27 (ω) / #103 (DSS lower) / the F₁ seam (#71/#90):** add a shared annotation "unified by §U: same
  missing object = archimedean multiplicative Frobenius fixing s=1; D4≡DSS-bridge≡D5."
- **Charter §6 D4/D5 line:** note "D4 and D5 coincide via the ABP-lift mechanism (multiplicative vs
  derivation); the decider is whether the F₁ object supplies a *multiplicative* Frobenius at ∞ fixing s=1."
- **Status:** no grade change — the unified object is still FIELDS MEDAL / open (= RH).

## Refinement (§V, same day) — WHY the unified object is missing: forced by hypertranscendence
A multiplicative archimedean operator fixing s=1 **does** exist — the Euler/weight operator `E₁=(s−1)∂_s`
(flow `exp(tE₁)` multiplicative, fixes s=1; spec `{0,1,2,…}` zeta-summable; `det_ζ(E₁)=√(2π)`, so
`log det_ζ(E₁)=a_∞=½log2π`). So the missing F₁ is **not** "no such operator exists" (a §U overstatement,
corrected in §V). The obstruction is that `exp(tE₁)` supplies **no ABP lift**, because ABP needs a finite-rank
**algebraic** Φ-matrix and `Λ` is **hypertranscendental** (#134) — no Φ-matrix exists.

**Charter §6-level note:** this explains WHY D4/D5/DSS are open — it is **forced by the founding negative
theorem** (hypertranscendence = "fixed by a constraint, not propagated by a flow" = the absence of the ABP
generative Φ-flow), **not a gap in the work**. #134 forbids the *finite/algebraic* lift; the F₁ object must be
**infinite-rank / ζ-regularized** (Deninger) by necessity, and `ω=0 ⟺ that regularization is consistent ⟺ RH`.
Suggest the status/charter §6 verdict note: "the apex (D4/D5/DSS) is open *by* hypertranscendence (#134), which
forbids a finite ABP lift; the residual is necessarily the infinite ζ-regularized realization (= RH)."

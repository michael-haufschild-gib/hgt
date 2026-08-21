# ULF-FTGM-1 — Lean certification record

**Card:** `poisson-boolean-information-transfer-cocycle-and-boundary-germ-tomography-law.md`
**Status:** fully formalized, unconditional, axiom-clean.

## Modules

| Module | Public declarations |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/ConstitutiveFormationTransferGerm.lean` | abstract mechanism core (pre-existing) |
| `formal/GaloisForLFunctions/HTGeometry/PoissonSuperpositionSaturationProperness.lean` | Boolean occupancy work, saturation, exact Jeffreys formula (pre-existing) |
| `formal/GaloisForLFunctions/HTGeometry/PoissonBooleanTransferGerm.lean` | 47 (new) |
| `formal/GaloisForLFunctions/RHTower/StokesChamberGermReconstruction.lean` | 5 (new) |

Both new modules are wired into `GaloisForLFunctions.HTGeometry`,
`GaloisForLFunctions.HTGeometry.UniversalLawField` and `GaloisForLFunctions.RHTower`.

## Card result → Lean declaration

| Card | Statement | Lean |
|---|---|---|
| §2 | `q_{mn} = 1-(1-q_m)^n` for the OR observer | `map_orObserver_bernoulli`, `orParam_poissonOccupancyUnit`, `occupancyReport_or` |
| (2.1) | `mC = B_m + H_m` | `formation_conservation` (pre-existing) |
| (2.2) | `B_m = K_m^+ + K_m^-` | `booleanForwardWork_add` |
| (2.3) | `T_{m,n}^\pm \ge 0`, `T_{m,n} \ge 0` | `booleanForwardWork_subadditive`, `directedFormationTransfer_nonneg`, `symmetricFormationTransfer_nonneg` |
| (2.4) | scale-transfer cocycle | `booleanForwardWork_cocycle`, `formationBooleanWork_cocycle` |
| (2.5) | `H_{mn} = nH_m + T_{m,n}` | `formationHistoryWork_mul` |
| (2.6) | `T_{m,n}/(mn) = B_m/m - B_{mn}/(mn)` | `formationInformationTransfer_div` |
| (3.1) | one-step transfer density | `booleanTransferDensity`, `booleanTransferDensity_eq_transfer` |
| (3.3) | exact Bernoulli formula for `B_m` | `formationBooleanWork_eq` (pre-existing) |
| (3.4) | `B_m/m ~ Δ e^{-mb}` | `isEquivalent_formationBooleanWork_div` |
| (3.5) | `g_j ~ Δ e^{-b m_j}`; eventual positivity | `isEquivalent_booleanTransferDensity`, `eventually_booleanTransferDensity_pos` |
| (3.6) | `b = lim -\log g_j / m_j` | `tendsto_neg_log_booleanTransferDensity` (abstract form `tendsto_neg_log_germ_div`) |
| (3.7) | `lim g_{j+1}/g_j^d = Δ^{1-d}`, `Δ = (\lim)^{-1/(d-1)}` | `tendsto_booleanTransferDensity_scale`, `rpow_scaleRatio_recovery`, `booleanTransferDensity_gap_of_scale_limit` |
| (4.1) | directed densities, `g_j = g_j^+ + g_j^-` | `directedTransferDensity`, `directedTransferDensity_add` |
| (4.5) | `K_m^+ = (1-A)(\log(1-A)-\log(1-B)) - mΔA` | `booleanForwardWork_eq` |
| (4.6) | `K_m^-` (same identity with the rates exchanged) | `booleanForwardWork_eq` applied to `(β,α)` |
| (4.7) | `K_m^+ ~ e^{-mb}`, `K_m^- ~ mΔ e^{-mb}` | `isEquivalent_booleanForwardWork`, `isEquivalent_booleanBackwardWork` |
| (4.2) | `g_j^+ ~ e^{-bm_j}/m_j`, `g_j^- ~ Δ e^{-bm_j}` | `isEquivalent_directedTransferDensity_forward`, `isEquivalent_directedTransferDensity_reverse` |
| (4.3) | `Δ = \lim \max/(m_j \min)` | `tendsto_directedTransferDensity_ratio`, `tendsto_directedTransferDensity_maxmin` |
| (4.4) | orientation `α>β ⟺ g_j^+ < g_j^-` eventually | `eventually_directedTransferDensity_lt` |
| (5.1) | label exchange fixes `g_j`, exchanges the directed legs | `booleanTransferDensity_swap`, `directedTransferDensity_add` |
| (5.2) | `α_p(t)=\log(1+p^{t-1})`, `β_p(t)=\log(1+p^{-t-1})` | `reflectedSourceRate` (pre-existing), `coe_reflectedSourceRate` |
| (5.3) | `t = (2\log p)^{-1}\log((e^{α}-1)/(e^{β}-1))` | `reflectedSourceRate_recovery`; sign/ordering `reflectedSourceRate_lt_iff`; germ instance `tendsto_reflectedTransferDensity_maxmin` |
| Cor 5.2, (5.4)–(5.5) | Stokes-chamber reconstruction `s = 1-2t`, exponent `2+2(1-2t)e`, coefficient `√2 t (e+1)^{-2}` | `stokesReflectionParameter`, `stokesChamber_recovery`, `isEquivalent_stokesCoenergy_reflected` |
| §6.1 | limiting observer point is `(1,1)` for every positive pair | `tendsto_poissonOccupancy_depth` (pre-existing) |
| §6.3 | the symmetric germ is exchange-invariant | `booleanTransferDensity_swap` |

## Supporting new results

* `tendsto_log_one_add_div` — `\log(1+u)/u \to 1` at `0` from the derivative of `\log(1+x)`.
* `tendsto_logRatio_div` — `\log((1-A_m)/(1-B_m))/B_m \to 1`, the shared engine of both directed
  asymptotics.
* `isLittleO_of_eventuallyEq_mul`, `isLittleO_shift_of_tendsto_ratio`,
  `isEquivalent_geometricDifference` — reusable asymptotic plumbing for geometric depth schedules.
* `orObserver`, `preimage_orObserver_false`, `orParam`, `map_orObserver_bernoulli` — the OR observer
  as a measurable map pushing a Bernoulli product to a Bernoulli law.

## Verification

* `lake env lean` on both modules: 0 errors, 0 warnings.
* `#print axioms` on all 52 public declarations: only
  `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`; no hypotheses beyond `0 < β`, `β < α`,
  `1 < d`, `0 < m` — the positivity/nondegeneracy conditions the card itself states.

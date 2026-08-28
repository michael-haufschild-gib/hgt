# HC73 retarded/advanced reciprocity--Schwarz causal rigidity (2026-08-28)

Formalized module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingRetardedAdvancedReciprocitySchwarzCausalRigidity.lean`.
Card: `docs/drafts/pipeline/3-formalized/hb-retarded-advanced-reciprocity-schwarz-causal-rigidity.md`.

Result: on the arbitrary global finite-support Xi carrier, one retarded/advanced pairing reciprocity law and one retarded-to-advanced canonical Schwarz exchange law imply that `Gret - Gadv` is Peierls-skew and channel-Schwarz odd. Pairing symmetry derives reverse reciprocity; Schwarz involutivity derives reverse exchange. Conversely every arbitrary global skew, Schwarz-odd propagator `Delta` is exactly the jump of `Gret = (1/2) • Delta`, `Gadv = -((1/2) • Delta)`, and this pair satisfies reciprocity and Schwarz exchange. Therefore minimal abstract Green-pair structure and HC72's monolithic operator laws define exactly the same class. Existence of such a pair whose jump realizes universal literal unit BM incidence is iff RH.

Scope: maps are abstract response maps, not yet physical Green operators. PDE inverse, support/causality, gauge fixing, and literal nonlinear Einstein--Teukolsky BM incidence remain producer burdens. Structural retarded/advanced splitting adds no hidden restriction beyond HC72.

Verification: direct `lake env lean` passed; target-only build passed `12024/12024`; all 11 theorem axiom audits use only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired. Global lint has no HC73 finding and fails only pre-existing unrelated unreachable modules.
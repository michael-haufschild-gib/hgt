import Mathlib.Tactic.Basic

/-!
# Simp sets for the Birmingham–Mokhtari jet tables

Two registered simp sets. `bmJetEntry` collects the entry tables of the background jet and of
the fundamental scalar jet; `bmJetTable` collects the Christoffel-variation tables of the scalar
jet. Proofs downstream write `simp only [bmJetEntry]` instead of naming hundreds of lemmas, so the
simp set is built once per file rather than once per proof.
-/

register_simp_attr bmJetEntry
register_simp_attr bmJetTable

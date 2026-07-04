/-
Doc 49 §2 (task #130): first bricks of the Gauss phase lattice.

The tower phases obey `φ_{N−m} ≡ φ_N − 4πp·m − π·m² (mod 2π)`; the integer
skeleton of its coherence structure is machine-checked here:

* `pi_msq_phase_alternates` — `m² ≡ m (mod 2)`: at `p ≈ 0` the lattice phases
  alternate `0, π, 0, π, …` (consecutive sub-marginal entries anti-phased —
  the marginal term's dominance at resonance).
* `lattice_coherent_iff` — `m(m + a)` is even for EVERY `m` iff `a` is odd:
  with `a = 4p`, full tower coherence happens exactly at `p ∈ {1/4, 3/4}`
  (4p an odd integer) — the sharp quarter-phase prediction.
* `norm_geom_sum_le` — the geometric-sum bound `‖Σ w^m‖ ≤ 2/‖1 − w‖` on the
  unit circle, the elementary ingredient of Weyl differencing for the
  collective-push bounds (doc 49 §2(3)).

Cross-lane: the equidistribution side (Weyl moment criterion) has its analytic
backbone banked in `SatoTateMoment` (orthogonality integrals); these bricks are
the finite/discrete complement.
-/
import Mathlib

namespace RHTower

/-- `m² − m` is always even: the `πm²` lattice phase alternates `0, π, 0, π…`. -/
theorem pi_msq_phase_alternates (m : ℤ) : Even (m ^ 2 - m) := by
  have h := Int.even_mul_succ_self (m - 1)
  have : (m - 1) * (m - 1 + 1) = m ^ 2 - m := by ring
  rwa [this] at h

/-- **The quarter-phase coherence law**: the lattice increment `m(m + a)` is
even for every integer `m` iff `a` is odd — with `a = 4p`, the tower is fully
coherent exactly at `p = 1/4, 3/4 (mod 1)`. -/
theorem lattice_coherent_iff (a : ℤ) :
    (∀ m : ℤ, Even (m * (m + a))) ↔ Odd a := by
  constructor
  · intro h
    have h1 := h 1
    rcases Int.even_or_odd a with ha | ha
    · exfalso
      rcases ha with ⟨b, hb⟩
      rcases h1 with ⟨k, hk⟩
      omega
    · exact ha
  · intro ha m
    rcases Int.even_or_odd m with hm | hm
    · rcases hm with ⟨b, hb⟩
      exact ⟨b * (m + a), by rw [hb]; ring⟩
    · rcases hm with ⟨b, hb⟩
      rcases ha with ⟨c, hc⟩
      exact ⟨m * (b + c + 1), by rw [hb, hc]; ring⟩

/-- Geometric-sum bound on the unit circle: the Weyl-differencing ingredient. -/
theorem norm_geom_sum_le {w : ℂ} (hw : ‖w‖ = 1) (hne : w ≠ 1) (K : ℕ) :
    ‖∑ m ∈ Finset.range K, w ^ m‖ ≤ 2 / ‖1 - w‖ := by
  have hsub : w - 1 ≠ 0 := sub_ne_zero.mpr hne
  rw [geom_sum_eq hne]
  rw [norm_div]
  have hnum : ‖w ^ K - 1‖ ≤ 2 := by
    calc ‖w ^ K - 1‖ ≤ ‖w ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_pow, hw, norm_one, one_pow]
      _ = 2 := by norm_num
  have hden : ‖w - 1‖ = ‖1 - w‖ := by
    rw [← norm_neg]; ring_nf
  rw [hden]
  have hpos : 0 < ‖1 - w‖ := by
    rw [← hden]
    exact norm_pos_iff.mpr hsub
  gcongr

end RHTower

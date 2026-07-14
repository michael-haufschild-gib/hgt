import GaloisForLFunctions.HTGeometry.MagnitudeInhomogeneousSurvival

/-!
# Grading of magnitude atoms

The balanced-atom argument of the log-superlacunary theorem is driven by two conserved gradings of
each contributing atom `ν = atomKeyOf n x` at coefficient level `N`:

* its **count** `∑ₙ ν n` equals the total jet-degree `∑ⱼ x.1 j.succ` of the underlying monomial;
* its **index-weighted sum** `∑ₙ n · ν n` equals `(∑ₜ x.2 t) + ∑ⱼ j · x.1 j.succ`, i.e. the residual
  `X`-degree carried by the antidiagonal split plus the differential order of the monomial.

Since the antidiagonal forces `∑ₜ x.2 t = N - x.1 0`, the index-weighted sum is `N` up to the
bounded shift `∑ⱼ j·x.1 j.succ − x.1 0`.  With bounded count and index-mass pinned near `N`, a
super-convex magnitude profile `b` is minimized by the balanced atom (indices `≈ N/D`), which is the
combinatorial heart of Steps 2–3 of the card.
-/

open Finset PowerSeries MvPolynomial

namespace GaloisForLFunctions

/-- Total count of an atom key: `∑ₙ (key h) n = D`. -/
theorem key_total_count {D : ℕ} (h : Fin D → ℕ) :
    (key h).sum (fun _ v => v) = D := by
  have hlift : (key h).sum (fun _ v => v)
      = Finsupp.liftAddHom (fun _ : ℕ => AddMonoidHom.id ℕ) (key h) := rfl
  rw [hlift, key, map_sum]
  simp [Finsupp.liftAddHom_apply_single]

/-- Index-weighted sum of an atom key: `∑ₙ n · (key h) n = ∑ₜ h t`. -/
theorem key_weighted_sum {D : ℕ} (h : Fin D → ℕ) :
    (key h).sum (fun n v => n * v) = ∑ t, h t := by
  have hlift : (key h).sum (fun n v => n * v)
      = Finsupp.liftAddHom (fun n : ℕ => (AddMonoidHom.mulLeft n)) (key h) := rfl
  rw [hlift, key, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [Finsupp.liftAddHom_apply_single]

/-- The canonical flattening realizes the total differential order: `∑ₜ flatOrder e t = ∑ⱼ j · e j`. -/
theorem flatOrder_sum {n : ℕ} (e : Fin (n + 1) → ℕ) :
    ∑ i, flatOrder e i = ∑ j, j * e j := by
  classical
  set eqv := (Fintype.equivFinOfCardEq (by rw [Fintype.card_sigma]; simp :
      Fintype.card (Σ j : Fin (n + 1), Fin (e j)) = ∑ j, e j)) with heqv
  have hrw : ∑ i, flatOrder e i = ∑ p : Σ j : Fin (n + 1), Fin (e j), ((p.1 : ℕ)) := by
    rw [← Equiv.sum_comp eqv.symm (fun p => ((p.1 : ℕ)))]
    rfl
  rw [hrw, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- The count grading of a magnitude atom equals the total jet-degree of its monomial. -/
theorem atomKeyOf_count (n : ℕ)
    (x : Σ m : Fin (n + 2) →₀ ℕ, Fin (∑ j : Fin (n + 1), m j.succ) →₀ ℕ) :
    (atomKeyOf n x).sum (fun _ v => v) = ∑ j : Fin (n + 1), x.1 j.succ := by
  rw [atomKeyOf, key_total_count]

/-- The index-weighted grading of a magnitude atom: residual antidiagonal degree plus the total
differential order of the monomial. -/
theorem atomKeyOf_weighted_sum (n : ℕ)
    (x : Σ m : Fin (n + 2) →₀ ℕ, Fin (∑ j : Fin (n + 1), m j.succ) →₀ ℕ) :
    (atomKeyOf n x).sum (fun i v => i * v)
      = (∑ t, x.2 t) + ∑ j : Fin (n + 1), j * x.1 j.succ := by
  rw [atomKeyOf, key_weighted_sum]
  rw [← flatOrder_sum (fun j => x.1 j.succ), ← Finset.sum_add_distrib]

/-- On atoms of `sigmaIdx n N Q`, the antidiagonal fixes the residual degree: `∑ₜ x.2 t = N − x.1 0`. -/
theorem sigmaIdx_antidiag_sum {n N : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {x : Σ m : Fin (n + 2) →₀ ℕ, Fin (∑ j : Fin (n + 1), m j.succ) →₀ ℕ}
    (hx : x ∈ sigmaIdx n N Q) :
    (∑ t, x.2 t) = N - x.1 0 := by
  classical
  rw [sigmaIdx, Finset.mem_sigma] at hx
  obtain ⟨_, hxanti⟩ := hx
  exact (Finset.mem_finsuppAntidiag.mp hxanti).1

/-- Index-weighted sum is at most `(max index) · (count)`: the pigeonhole flooring the max index. -/
theorem weighted_sum_le_max_mul_count {ν : ℕ →₀ ℕ} (hne : ν.support.Nonempty) :
    (ν.sum (fun i v => i * v)) ≤ ν.support.max' hne * (ν.sum (fun _ v => v)) := by
  rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  exact Nat.mul_le_mul_right _ (Finset.le_max' _ i hi)

/-- **Valuation floor from index-mass.**  An atom of count `≤ D` carrying index-mass `W > K·D` has a
support index exceeding `K`, hence valuation at least `b (K+1)`.  Under a super-increasing profile
this forces every atom whose index-mass exceeds the balanced value to dominate the balanced atom. -/
theorem valuation_ge_b_succ_of_weighted_sum {ν : ℕ →₀ ℕ} {b : ℕ → ℝ} {D K : ℕ}
    (hbnn : ∀ n, 0 ≤ b n) (hbmono : Monotone b)
    (hcount : (ν.sum (fun _ v => v)) ≤ D) (hne : ν.support.Nonempty)
    (hW : K * D < ν.sum (fun i v => i * v)) :
    b (K + 1) ≤ ν.sum (fun n k => (k : ℝ) * b n) := by
  have hpig := weighted_sum_le_max_mul_count hne
  have hmaxD : ν.sum (fun i v => i * v) ≤ ν.support.max' hne * D :=
    le_trans hpig (Nat.mul_le_mul_left _ hcount)
  have hKmax : K < ν.support.max' hne := by
    by_contra h
    push_neg at h
    have : ν.support.max' hne * D ≤ K * D := Nat.mul_le_mul_right _ h
    omega
  calc b (K + 1) ≤ b (ν.support.max' hne) := hbmono hKmax
    _ ≤ ν.sum (fun n k => (k : ℝ) * b n) := valuation_ge_b_max hbnn hne

end GaloisForLFunctions

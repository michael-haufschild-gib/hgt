import GaloisForLFunctions.HTGeometry.MomentRealRootedness

/-!
# The Gauss quadrature nodes

The roots of `monicOrtho s (n+1)` are the nodes of the Gauss quadrature rule attached to the moment
sequence.  This module establishes that there are exactly `n+1` of them and that they are distinct.

Simplicity is the same argument that ruled out non-real roots, with the quadratic factor replaced by
a repeated real one: if `(X - r)²` divided `Q = monicOrtho s (n+1)`, the quotient `g` would have
degree `n-1`, hence be orthogonal to `Q`, while `Q g = ((X - r) g)²` has strictly positive moment
value.  No derivative of `Q` and no confluent form of the Christoffel--Darboux identity is needed.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **No repeated roots.**  A square factor would produce a quotient orthogonal to `Q` whose pairing
with `Q` is nevertheless a positive moment square. -/
theorem monicOrtho_not_sq_dvd (h : PositiveMomentForm s) (n : ℕ) (r : ℝ) :
    ¬ (((X - C r) ^ 2 : Polynomial ℝ) ∣ monicOrtho s (n + 1)) := by
  rintro ⟨g, hg⟩
  have hsqne : ((X - C r) ^ 2 : Polynomial ℝ) ≠ 0 := pow_ne_zero 2 (X_sub_C_ne_zero r)
  have hgne : g ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hg
    exact monicOrtho_ne_zero s (n + 1) hg
  have hnd : (monicOrtho s (n + 1)).natDegree = 2 * 1 + g.natDegree := by
    rw [hg, natDegree_mul hsqne hgne, natDegree_pow, natDegree_X_sub_C]
  have hQnd : (monicOrtho s (n + 1)).natDegree = n + 1 :=
    natDegree_eq_of_degree_eq_some (monicOrtho_degree s (n + 1))
  have hglt : g.natDegree < n + 1 := by omega
  have hgdeg : g.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hgne]
    exact_mod_cast hglt
  have hzero : momentInner s (monicOrtho s (n + 1)) g = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt h (n + 1) (n + 1) le_rfl g hgdeg
  have hpoly : ((X - C r) ^ 2 : Polynomial ℝ) * g * g
      = ((X - C r) * g) * ((X - C r) * g) := by ring
  have hexp : momentInner s (monicOrtho s (n + 1)) g
      = momentInner s ((X - C r) * g) ((X - C r) * g) := by
    rw [hg, momentInner_def, hpoly, momentInner_def]
  have hne : (X - C r) * g ≠ 0 := mul_ne_zero (X_sub_C_ne_zero r) hgne
  rw [hexp] at hzero
  exact absurd hzero (ne_of_gt (h.pos_of_ne_zero _ hne))

/-- Every root of `monicOrtho s (n+1)` is simple. -/
theorem monicOrtho_rootMultiplicity_le_one (h : PositiveMomentForm s) (n : ℕ) (r : ℝ) :
    rootMultiplicity r (monicOrtho s (n + 1)) ≤ 1 := by
  by_contra hc
  have hc2 : 2 ≤ rootMultiplicity r (monicOrtho s (n + 1)) := not_le.mp hc
  exact monicOrtho_not_sq_dvd h n r
    (dvd_trans (pow_dvd_pow _ hc2) (pow_rootMultiplicity_dvd _ _))

theorem monicOrtho_roots_nodup (h : PositiveMomentForm s) (n : ℕ) :
    (monicOrtho s (n + 1)).roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro r
  rw [count_roots]
  exact monicOrtho_rootMultiplicity_le_one h n r

/-- Counted with multiplicity there are `n+1` roots, because the polynomial splits. -/
theorem monicOrtho_roots_card (h : PositiveMomentForm s) (n : ℕ) :
    Multiset.card (monicOrtho s (n + 1)).roots = n + 1 := by
  rw [← (monicOrtho_splits h n).natDegree_eq_card_roots]
  exact natDegree_eq_of_degree_eq_some (monicOrtho_degree s (n + 1))

/-- The nodes of the Gauss quadrature rule of level `n`. -/
noncomputable def gaussNodes (s : ℕ → ℝ) (n : ℕ) : Finset ℝ :=
  (monicOrtho s (n + 1)).roots.toFinset

theorem mem_gaussNodes_iff (n : ℕ) (r : ℝ) :
    r ∈ gaussNodes s n ↔ (monicOrtho s (n + 1)).eval r = 0 := by
  classical
  rw [gaussNodes, Multiset.mem_toFinset, mem_roots']
  constructor
  · rintro ⟨-, hr⟩
    exact hr
  · intro hr
    exact ⟨monicOrtho_ne_zero s (n + 1), hr⟩

/-- **There are exactly `n+1` nodes.** -/
theorem gaussNodes_card (h : PositiveMomentForm s) (n : ℕ) :
    (gaussNodes s n).card = n + 1 := by
  classical
  rw [gaussNodes, Multiset.toFinset_card_of_nodup (monicOrtho_roots_nodup h n),
    monicOrtho_roots_card h n]

end HTGeometry

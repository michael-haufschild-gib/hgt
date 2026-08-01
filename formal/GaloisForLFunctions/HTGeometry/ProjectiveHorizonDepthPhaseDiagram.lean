import GaloisForLFunctions.HTGeometry.ProjectiveHorizonOneSidedCollapse

/-!
# The depth phase diagram of two projective horizons

Two chart directions each retain their transvections up to a depth.  As soon as either depth
reaches two, the common observables collapse to the constants: the deeper chart contributes the
extra velocity mode that the one-sided chain propagates to every depth on every row.

The statement is symmetric in the two charts, so the whole positive-depth phase diagram outside the
single lattice point `(1,1)` is covered, at every projective dimension.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- **The depth phase diagram.**  If two distinct chart directions retain their transvections to
positive depths and either depth reaches two, every common jet observable is constant. -/
theorem exists_algebraMap_of_depthPair_annihilation [CharZero K] {i j : n} (hij : i ≠ j)
    {m p : ℕ} (hm : 1 ≤ m) (hp : 1 ≤ p) (hdeep : 2 ≤ m ∨ 2 ≤ p)
    {f : HomogeneousJetField n K}
    (hH : ∀ (x : n) (k : ℕ), k < m → x ≠ i →
      jetLoopDerivation k (Matrix.single x i (1 : K)) f = 0)
    (hK : ∀ (x : n) (k : ℕ), k < p → x ≠ j →
      jetLoopDerivation k (Matrix.single x j (1 : K)) f = 0) :
    ∃ c : K, f = algebraMap K (HomogeneousJetField n K) c := by
  rcases hdeep with hm2 | hp2
  · exact exists_algebraMap_of_oneSided_annihilation hij
      (fun x hx => hH x 0 (by omega) hx) (fun x hx => hH x 1 (by omega) hx)
      (fun x hx => hK x 0 (by omega) hx)
  · exact exists_algebraMap_of_oneSided_annihilation (Ne.symm hij)
      (fun x hx => hK x 0 (by omega) hx) (fun x hx => hK x 1 (by omega) hx)
      (fun x hx => hH x 0 (by omega) hx)

/-- Equal-depth specialisation: every common depth at least two collapses. -/
theorem exists_algebraMap_of_equalDepth_annihilation [CharZero K] {i j : n} (hij : i ≠ j)
    {m : ℕ} (hm : 2 ≤ m) {f : HomogeneousJetField n K}
    (hH : ∀ (x : n) (k : ℕ), k < m → x ≠ i →
      jetLoopDerivation k (Matrix.single x i (1 : K)) f = 0)
    (hK : ∀ (x : n) (k : ℕ), k < m → x ≠ j →
      jetLoopDerivation k (Matrix.single x j (1 : K)) f = 0) :
    ∃ c : K, f = algebraMap K (HomogeneousJetField n K) c :=
  exists_algebraMap_of_depthPair_annihilation hij (by omega) (by omega) (Or.inl hm) hH hK

/-- The minimal asymmetric trigger: one chart at depth one, the other at depth two. -/
theorem exists_algebraMap_of_depthOneTwo_annihilation [CharZero K] {i j : n} (hij : i ≠ j)
    {f : HomogeneousJetField n K}
    (hH : ∀ x : n, x ≠ i → jetLoopDerivation 0 (Matrix.single x i (1 : K)) f = 0)
    (hK : ∀ (x : n) (k : ℕ), k < 2 → x ≠ j →
      jetLoopDerivation k (Matrix.single x j (1 : K)) f = 0) :
    ∃ c : K, f = algebraMap K (HomogeneousJetField n K) c :=
  exists_algebraMap_of_depthPair_annihilation (m := 1) (p := 2) hij le_rfl (by omega)
    (Or.inr le_rfl) (fun x k hk hx => by
      rw [show k = 0 from by omega]
      exact hH x hx) hK

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.MvHankelHypersurface
import GaloisForLFunctions.HTGeometry.MvResultantElimination

/-!
# The top jet coefficient of a fibre, at any depth

Each point of the fibre gives a hypersurface of degree the second depth containing all the others,
so a choice of `m` fibre points produces a square system of `m` equations of degree `n` in the `m`
unknown jet coefficients.  Running the elimination tower on that system leaves one polynomial in one
variable, of degree at most `n^(2^(m-1))`, vanishing at the top jet coefficient of every remaining
fibre point.

So at every pair of depths the top jet coefficient of the fibre takes finitely many values, bounded
explicitly, as soon as the tower does not degenerate.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] {k n : ℕ}

/-- The square system of Hankel hypersurfaces attached to a choice of fibre points. -/
noncomputable def hankelSystem {U V : K[X]} (base : Fin (k + 1) → criticalFibre K (k + 1) n U V)
    (U' : K[X]) : Fin (k + 1) → MvPolynomial (Fin (k + 1)) K :=
  fun i => (hankelMvMatrix ((base i).1.1 + U') U' (k + 1) n).det

theorem totalDegree_hankelSystem_le {U V : K[X]}
    (base : Fin (k + 1) → criticalFibre K (k + 1) n U V) (U' : K[X]) (i : Fin (k + 1)) :
    (hankelSystem base U' i).totalDegree ≤ n :=
  totalDegree_det_hankelMvMatrix_le _ _

/-- **The top jet coefficient of the fibre takes at most `n^(2^k)` values.**  The bound holds for
every observation and every depth, once the elimination tower of the chosen base points does not
vanish identically. -/
theorem card_top_coeff_le (hn : 0 < n) {U V : K[X]}
    (hU : (X : K[X]) ^ (k + 1) ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (base : Fin (k + 1) → criticalFibre K (k + 1) n U V)
    (htower : elimTower k (hankelSystem base U) n ≠ 0)
    (s : Finset K)
    (hs : ∀ y ∈ s, ∃ q : criticalFibre K (k + 1) n U V,
      (∀ i, base i ≠ q) ∧ q.1.1.coeff k = y) :
    s.card ≤ n ^ (2 ^ k) := by
  refine card_last_coord_le (hankelSystem base U) n (by omega)
    (totalDegree_hankelSystem_le base U) htower s fun y hy => ?_
  obtain ⟨q, hne, hcoeff⟩ := hs y hy
  refine ⟨fun i : Fin (k + 1) => q.1.1.coeff (i : ℕ), ?_, fun i => ?_⟩
  · rw [← hcoeff]
    congr 1
  · exact eval_det_hankelMvMatrix_eq_zero (by omega) hn hU hV hU0 hV0 (base i) q (hne i)


/-! ## Any coordinate, by renaming the variables -/

/-- The system with its variables permuted, so that a chosen coordinate becomes the last. -/
noncomputable def hankelSystemPerm {U V : K[X]}
    (base : Fin (k + 1) → criticalFibre K (k + 1) n U V) (U' : K[X])
    (σ : Equiv.Perm (Fin (k + 1))) : Fin (k + 1) → MvPolynomial (Fin (k + 1)) K :=
  fun i => MvPolynomial.rename (σ.symm) (hankelSystem base U' i)

theorem totalDegree_hankelSystemPerm_le {U V : K[X]}
    (base : Fin (k + 1) → criticalFibre K (k + 1) n U V) (U' : K[X])
    (σ : Equiv.Perm (Fin (k + 1))) (i : Fin (k + 1)) :
    (hankelSystemPerm base U' σ i).totalDegree ≤ n := by
  rw [hankelSystemPerm]
  exact le_trans (MvPolynomial.totalDegree_rename_le _ _)
    (totalDegree_hankelSystem_le base U' i)

/-- **Every jet coefficient of the fibre takes at most `n^(2^k)` values.**  Permuting the variables
puts the chosen coordinate last, which the elimination tower then bounds. -/
theorem card_coeff_le (hn : 0 < n) {U V : K[X]}
    (hU : (X : K[X]) ^ (k + 1) ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (base : Fin (k + 1) → criticalFibre K (k + 1) n U V) (σ : Equiv.Perm (Fin (k + 1)))
    (htower : elimTower k (hankelSystemPerm base U σ) n ≠ 0)
    (s : Finset K)
    (hs : ∀ y ∈ s, ∃ q : criticalFibre K (k + 1) n U V,
      (∀ i, base i ≠ q) ∧ q.1.1.coeff ((σ (Fin.last k) : ℕ)) = y) :
    s.card ≤ n ^ (2 ^ k) := by
  refine card_last_coord_le (hankelSystemPerm base U σ) n (by omega)
    (totalDegree_hankelSystemPerm_le base U σ) htower s fun y hy => ?_
  obtain ⟨q, hne, hcoeff⟩ := hs y hy
  refine ⟨fun i : Fin (k + 1) => q.1.1.coeff ((σ i : ℕ)), hcoeff, fun i => ?_⟩
  rw [hankelSystemPerm, MvPolynomial.eval_rename]
  have hcomp : ((fun i : Fin (k + 1) => q.1.1.coeff ((σ i : ℕ))) ∘ (σ.symm))
      = fun i : Fin (k + 1) => q.1.1.coeff (i : ℕ) := by
    funext i
    simp
  rw [hcomp]
  exact eval_det_hankelMvMatrix_eq_zero (by omega) hn hU hV hU0 hV0 (base i) q (hne i)


/-! ## The fibre at any depth -/

/-- **Every jet coefficient of the fibre lies in an explicit finite set.** -/
theorem exists_finset_coeff (hn : 0 < n) {U V : K[X]}
    (hU : (X : K[X]) ^ (k + 1) ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (base : Fin (k + 1) → criticalFibre K (k + 1) n U V) (σ : Equiv.Perm (Fin (k + 1)))
    (htower : elimTower k (hankelSystemPerm base U σ) n ≠ 0) :
    ∃ s : Finset K, s.card ≤ n ^ (2 ^ k) ∧
      ∀ q : criticalFibre K (k + 1) n U V, (∀ i, base i ≠ q) →
        q.1.1.coeff ((σ (Fin.last k) : ℕ)) ∈ s := by
  obtain ⟨s, hcard, hmem⟩ := exists_finset_last_coord (hankelSystemPerm base U σ) n (by omega)
    (totalDegree_hankelSystemPerm_le base U σ) htower
  refine ⟨s, hcard, fun q hne => ?_⟩
  have hpt := hmem (fun i : Fin (k + 1) => q.1.1.coeff ((σ i : ℕ))) (fun i => ?_)
  · exact hpt
  · rw [hankelSystemPerm, MvPolynomial.eval_rename]
    have hcomp : ((fun i : Fin (k + 1) => q.1.1.coeff ((σ i : ℕ))) ∘ (σ.symm))
        = fun i : Fin (k + 1) => q.1.1.coeff (i : ℕ) := by
      funext i
      simp
    rw [hcomp]
    exact eval_det_hankelMvMatrix_eq_zero (by omega) hn hU hV hU0 hV0 (base i) q (hne i)

/-- **The fibre at any depth is finite, with an explicit bound.**  Each of the `m` jet coefficients
is confined to a set of at most `n^(2^(m-1))` values by the elimination tower of the system
permuted to put that coefficient last, and a fibre point is determined by its coefficients. -/
theorem nat_card_criticalFibre_le_of_towers (hn : 0 < n) {U V : K[X]}
    (hU : (X : K[X]) ^ (k + 1) ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (base : Fin (k + 1) → criticalFibre K (k + 1) n U V)
    (σ : Fin (k + 1) → Equiv.Perm (Fin (k + 1)))
    (hσ : ∀ j, (σ j) (Fin.last k) = j)
    (htower : ∀ j, elimTower k (hankelSystemPerm base U (σ j)) n ≠ 0) :
    Nat.card (criticalFibre K (k + 1) n U V) ≤ (k + 1) + (n ^ (2 ^ k)) ^ (k + 1) := by
  classical
  choose S hScard hSmem using fun j =>
    exists_finset_coeff hn hU hV hU0 hV0 base (σ j) (htower j)
  set T : Finset (Fin (k + 1) → K) :=
    (Finset.univ.image fun i => fun j : Fin (k + 1) => (base i).1.1.coeff (j : ℕ))
      ∪ Fintype.piFinset S with hT
  have hmemT : ∀ q : criticalFibre K (k + 1) n U V,
      (fun j : Fin (k + 1) => q.1.1.coeff (j : ℕ)) ∈ T := by
    intro q
    by_cases hb : ∃ i, base i = q
    · obtain ⟨i, rfl⟩ := hb
      exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩)
    · push Not at hb
      refine Finset.mem_union_right _ (Fintype.mem_piFinset.2 fun j => ?_)
      have := hSmem j q fun i => hb i
      rwa [hσ j] at this
  have hinj : Function.Injective
      (fun q : criticalFibre K (k + 1) n U V =>
        (⟨fun j : Fin (k + 1) => q.1.1.coeff (j : ℕ), hmemT q⟩ : T)) := by
    intro q r hqr
    have hcoeff : ∀ j : Fin (k + 1), q.1.1.coeff (j : ℕ) = r.1.1.coeff (j : ℕ) := fun j =>
      congrFun (congrArg Subtype.val hqr) j
    refine criticalFibre_fst_injective (by omega) hn hU0 hV0 ?_
    show q.1.1 = r.1.1
    refine Polynomial.ext fun i => ?_
    by_cases hi : i < k + 1
    · exact hcoeff ⟨i, hi⟩
    · rw [Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le q.2.1 (by exact_mod_cast (by omega : k + 1 ≤ i))),
        Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le r.2.1 (by exact_mod_cast (by omega : k + 1 ≤ i)))]
  calc Nat.card (criticalFibre K (k + 1) n U V)
      ≤ Nat.card T := Nat.card_le_card_of_injective _ hinj
    _ = T.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ (Finset.univ.image fun i => fun j : Fin (k + 1) => (base i).1.1.coeff (j : ℕ)).card
          + (Fintype.piFinset S).card := Finset.card_union_le _ _
    _ ≤ (k + 1) + (n ^ (2 ^ k)) ^ (k + 1) := by
        refine Nat.add_le_add ?_ ?_
        · exact le_trans (Finset.card_image_le) (by simp)
        · rw [Fintype.card_piFinset]
          calc ∏ j : Fin (k + 1), (S j).card ≤ ∏ _j : Fin (k + 1), n ^ (2 ^ k) :=
                Finset.prod_le_prod' fun j _ => hScard j
            _ = (n ^ (2 ^ k)) ^ (k + 1) := by simp

end GaloisForLFunctions.HTGeometry

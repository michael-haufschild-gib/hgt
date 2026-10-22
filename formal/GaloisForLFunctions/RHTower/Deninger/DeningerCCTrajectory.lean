import GaloisForLFunctions.RHTower.Deninger.DeningerCCColimit

/-!
# Enumeration indices along the tower

The enumeration of a stage keeps the indices of the previous stages and devotes the block of index
the stage number to a fresh surjection, so an index used at one stage denotes the image of the same
element at every later stage.  The structure maps of the colimit identify all of these images.

* `deningerCCMap` : the transition maps of the tower.
* `deningerCCIota_map` : compatibility with the structure maps of the colimit.
* `deningerCCTower_hist_bound` : every element of a stage is enumerated by an index of an earlier
  block.
* `deningerCCTower_hist_map` : such an index denotes the image at every later stage.
-/

namespace RHTower

open CategoryTheory Monoid

universe u

namespace RootAdjunction

/-- The transition maps of the tower. -/
noncomputable def deningerCCMap (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ) {n m : ℕ}
    (h : n ≤ m) : (deningerCCTower S₀ sched n).carrier →* (deningerCCTower S₀ sched m).carrier :=
  ((deningerCCDiagram S₀ sched).map (homOfLE h)).hom

/-- **The structure maps of the colimit identify the transition maps.** -/
theorem deningerCCIota_map (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ) {n m : ℕ} (h : n ≤ m)
    (x : (deningerCCTower S₀ sched n).carrier) :
    deningerCCIota S₀ sched m (deningerCCMap S₀ sched h x) = deningerCCIota S₀ sched n x := by
  have hw := (GrpCat.FilteredColimits.colimitCocone (deningerCCDiagram S₀ sched)).w (homOfLE h)
  exact congrArg (fun f : GrpCat.of ((deningerCCTower S₀ sched n).carrier) ⟶
    deningerCCColimit S₀ sched => f.hom x) hw

/-- **The transition map to the next stage is the embedding.** -/
theorem deningerCCMap_succ (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ) (n : ℕ)
    (x : (deningerCCTower S₀ sched n).carrier) :
    deningerCCMap S₀ sched (Nat.le_succ n) x = deningerCCEmbed S₀ sched n x := by
  have hstep : ((deningerCCDiagram S₀ sched).map (homOfLE (Nat.le_succ n))).hom =
      deningerCCEmbed S₀ sched n := by
    show ((Functor.ofSequence
      (fun k => GrpCat.ofHom (deningerCCEmbed S₀ sched k))).map (homOfLE (Nat.le_succ n))).hom = _
    rw [Functor.ofSequence_map_homOfLE_succ]
    rfl
  exact congrArg (fun f => f x) hstep

/-- **The transition maps compose.** -/
theorem deningerCCMap_trans (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ) {n m k : ℕ}
    (h₁ : n ≤ m) (h₂ : m ≤ k) (x : (deningerCCTower S₀ sched n).carrier) :
    deningerCCMap S₀ sched h₂ (deningerCCMap S₀ sched h₁ x) =
      deningerCCMap S₀ sched (h₁.trans h₂) x := by
  have hcomp : (deningerCCDiagram S₀ sched).map (homOfLE (h₁.trans h₂)) =
      (deningerCCDiagram S₀ sched).map (homOfLE h₁) ≫
        (deningerCCDiagram S₀ sched).map (homOfLE h₂) := by
    rw [← Functor.map_comp]
    congr 1
  exact (congrArg (fun f : GrpCat.of ((deningerCCTower S₀ sched n).carrier) ⟶
    GrpCat.of ((deningerCCTower S₀ sched k).carrier) => f.hom x) hcomp).symm

/-- **Every element of a stage is enumerated by an index whose block is at most the stage
number.** -/
theorem deningerCCTower_hist_bound (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) (hgood : DeningerCCGood S₀)
    (h₀ : ∀ w : S₀.carrier, ∃ p : ℕ, (Nat.unpair p).1 = 0 ∧ S₀.hist p = w) (n : ℕ)
    (w : (deningerCCTower S₀ sched n).carrier) :
    ∃ p : ℕ, (Nat.unpair p).1 ≤ n ∧ (deningerCCTower S₀ sched n).hist p = w := by
  induction n with
  | zero =>
    obtain ⟨p, hp, hw⟩ := h₀ w
    exact ⟨p, by omega, hw⟩
  | succ n _ =>
    have hcount : Countable (deningerCCTower S₀ sched (n + 1)).carrier :=
      (deningerCCTower_good S₀ sched hs hgood (n + 1)).countable
    obtain ⟨i, hi⟩ := deningerCCFresh_surjective
      (deningerCCTower S₀ sched (n + 1)).carrier w
    refine ⟨Nat.pair (n + 1) i, ?_, ?_⟩
    · rw [Nat.unpair_pair]
    · show (if (Nat.unpair (Nat.pair (n + 1) i)).1 = n + 1 then _ else _) = w
      rw [Nat.unpair_pair, if_pos rfl]
      exact hi

/-- **An index of an earlier block denotes the image of the same element at every later stage.** -/
theorem deningerCCTower_hist_map (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ) (p n : ℕ)
    (hp : (Nat.unpair p).1 ≤ n) (m : ℕ) (hm : n ≤ m) :
    (deningerCCTower S₀ sched m).hist p =
      deningerCCMap S₀ sched hm ((deningerCCTower S₀ sched n).hist p) := by
  induction m, hm using Nat.le_induction with
  | base =>
    have h1 : deningerCCMap S₀ sched (le_refl n) ((deningerCCTower S₀ sched n).hist p) =
        (deningerCCTower S₀ sched n).hist p := by
      show ((deningerCCDiagram S₀ sched).map (homOfLE (le_refl n))).hom _ = _
      rw [Subsingleton.elim (homOfLE (le_refl n)) (𝟙 n), (deningerCCDiagram S₀ sched).map_id]
      rfl
    rw [h1]
  | succ m hm ih =>
    have hstep : (deningerCCTower S₀ sched (m + 1)).hist p =
        deningerCCEmbed S₀ sched m ((deningerCCTower S₀ sched m).hist p) := by
      show (if (Nat.unpair p).1 = m + 1 then _ else _) = _
      rw [if_neg (by omega)]
      rfl
    rw [hstep, ih, ← deningerCCMap_succ S₀ sched m,
      deningerCCMap_trans S₀ sched hm (Nat.le_succ m)]

end RootAdjunction

end RHTower

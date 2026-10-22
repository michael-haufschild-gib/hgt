import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixBigWittStokesSource

/-!
# All-cross big-Witt determinant ghost transmutation

Exact low-degree ghost calculation for the all-cross Teichmüller source. Under the two centered
first-moment identities, ghost degrees one through three vanish and degree four is exactly the
quadratic-pairing determinant term.
-/

namespace RHTower

noncomputable section

open scoped BigOperators

variable {A E F : Type*} [CommRing A]
variable [Fintype E] [Fintype F]

def allCrossWittSource (ell : E → A) (r : F → A) : DeningerBigWittRing A :=
  ∑ e, ∑ f, deningerBigWittTeichmullerCrossEffect (ell e) (r f)

def wittPowerMoment (x : E → A) (j : ℕ) : A := ∑ e, x e ^ j

private theorem crossGhost_two (a b : A) :
    deningerBigWittGhostComponent 2 (by omega)
        (deningerBigWittTeichmullerCrossEffect a b) = -2 * a * b := by
  simp [deningerBigWittTeichmullerCrossEffect]
  ring

private theorem crossGhost_three (a b : A) :
    deningerBigWittGhostComponent 3 (by omega)
        (deningerBigWittTeichmullerCrossEffect a b) =
      -(a ^ (2 : ℕ) * b * 3) - a * b ^ (2 : ℕ) * 3 := by
  simp [deningerBigWittTeichmullerCrossEffect]
  ring

private theorem crossGhost_four (a b : A) :
    deningerBigWittGhostComponent 4 (by omega)
        (deningerBigWittTeichmullerCrossEffect a b) =
      -(a ^ (3 : ℕ) * b * 4) - a ^ (2 : ℕ) * b ^ (2 : ℕ) * 6 - a * b ^ (3 : ℕ) * 4 := by
  simp [deningerBigWittTeichmullerCrossEffect]
  ring

private theorem doublePowerSum (ell : E → A) (r : F → A) (i j : ℕ) :
    (∑ e, ∑ f, ell e ^ i * r f ^ j) =
      wittPowerMoment ell i * wittPowerMoment r j := by
  exact (Finset.sum_mul_sum Finset.univ Finset.univ
    (fun e => ell e ^ i) (fun f => r f ^ j)).symm

private theorem doublePowerSum_mul (ell : E → A) (r : F → A) (i j : ℕ) (c : A) :
    (∑ e, ∑ f, ell e ^ i * r f ^ j * c) =
      wittPowerMoment ell i * wittPowerMoment r j * c := by
  calc
    (∑ e, ∑ f, ell e ^ i * r f ^ j * c) =
        ∑ e, (∑ f, ell e ^ i * r f ^ j) * c := by
          apply Finset.sum_congr rfl
          intro e he
          exact (Finset.sum_mul Finset.univ (fun f => ell e ^ i * r f ^ j) c).symm
    _ = (∑ e, ∑ f, ell e ^ i * r f ^ j) * c :=
      (Finset.sum_mul Finset.univ (fun e => ∑ f, ell e ^ i * r f ^ j) c).symm
    _ = _ := by rw [doublePowerSum]

/-- Exact ACW-2 transmutation: centering kills ghosts one through three and leaves the stated
degree-four determinant term. -/
theorem allCrossWittSource_lowDegreeTransmutation
    (ell : E → A) (r : F → A)
    (hL : wittPowerMoment ell 1 = 0) (hR : wittPowerMoment r 1 = 0) :
    deningerBigWittGhostComponent 1 (by omega) (allCrossWittSource ell r) = 0 ∧
      deningerBigWittGhostComponent 2 (by omega) (allCrossWittSource ell r) = 0 ∧
      deningerBigWittGhostComponent 3 (by omega) (allCrossWittSource ell r) = 0 ∧
      deningerBigWittGhostComponent 4 (by omega) (allCrossWittSource ell r) =
        -6 * wittPowerMoment ell 2 * wittPowerMoment r 2 := by
  have h1 : deningerBigWittGhostComponent 1 (by omega)
      (allCrossWittSource ell r) = 0 := by
    simp [allCrossWittSource, deningerBigWittTeichmullerCrossEffect]
  have h2 : deningerBigWittGhostComponent 2 (by omega)
      (allCrossWittSource ell r) = 0 := by
    simp only [allCrossWittSource, map_sum, crossGhost_two]
    have hsum := doublePowerSum ell r 1 1
    simp only [pow_one] at hsum
    rw [show (∑ e, ∑ f, -2 * ell e * r f) =
        -2 * (∑ e, ∑ f, ell e * r f) by
      simp_rw [Finset.mul_sum]
      ring]
    rw [hsum, hL, hR]
    ring
  have h3 : deningerBigWittGhostComponent 3 (by omega)
      (allCrossWittSource ell r) = 0 := by
    simp only [allCrossWittSource, map_sum, crossGhost_three,
      Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    have h21 := doublePowerSum_mul ell r 2 1 3
    have h12 := doublePowerSum_mul ell r 1 2 3
    simp only [pow_one] at h21 h12
    rw [h21, h12]
    rw [hL, hR]
    ring
  have h4 : deningerBigWittGhostComponent 4 (by omega)
      (allCrossWittSource ell r) =
        -6 * wittPowerMoment ell 2 * wittPowerMoment r 2 := by
    simp only [allCrossWittSource, map_sum, crossGhost_four,
      Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    have h31 := doublePowerSum_mul ell r 3 1 4
    have h22 := doublePowerSum_mul ell r 2 2 6
    have h13 := doublePowerSum_mul ell r 1 3 4
    simp only [pow_one] at h31 h13
    rw [h31, h22, h13, hL, hR]
    ring
  exact ⟨h1, h2, h3, h4⟩

end

end RHTower

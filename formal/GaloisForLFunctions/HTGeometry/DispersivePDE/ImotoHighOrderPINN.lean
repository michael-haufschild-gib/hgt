import GaloisForLFunctions.HTGeometry.DispersivePDE.ScalarSolitons

/-!
# Exact seventh-order profiles from arXiv:2609.03768
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE

noncomputable section

structure RealEvolutionJet7 extends RealEvolutionJet5 where
  uxxxxxx : ℝ → ℝ → ℝ
  uxxxxxxx : ℝ → ℝ → ℝ
  hasDerivAt_space_five : ∀ (t x : ℝ),
    HasDerivAt (toRealEvolutionJet5.uxxxxx t) (uxxxxxx t x) x
  hasDerivAt_space_six : ∀ (t x : ℝ),
    HasDerivAt (uxxxxxx t) (uxxxxxxx t x) x

def SolvesSeventhOrderHierarchy (nu b d g : ℝ) (J : RealEvolutionJet7) : Prop :=
  ∀ t x, J.ut t x + nu * J.u t x * J.ux t x + b * J.uxxx t x +
    d * J.uxxxxx t x + g * J.uxxxxxxx t x = 0

def SolvesLaxSeventh (J : RealEvolutionJet7) : Prop :=
  ∀ t x, J.ut t x + 140 * J.u t x ^ (3 : ℕ) * J.ux t x +
    280 * J.u t x * J.ux t x * J.uxx t x +
    70 * J.u t x ^ (2 : ℕ) * J.uxxx t x + 70 * J.ux t x ^ (3 : ℕ) +
    42 * J.ux t x * J.uxxxx t x + 14 * J.u t x * J.uxxxxx t x +
    70 * J.uxx t x * J.uxxx t x + J.uxxxxxxx t x = 0

def SolvesLinearSeventh (J : RealEvolutionJet7) : Prop :=
  ∀ t x, J.ut t x + J.uxxxxxxx t x = 0

structure RealProfileJet7 where
  f0 : ℝ → ℝ
  f1 : ℝ → ℝ
  f2 : ℝ → ℝ
  f3 : ℝ → ℝ
  f4 : ℝ → ℝ
  f5 : ℝ → ℝ
  f6 : ℝ → ℝ
  f7 : ℝ → ℝ
  hasDerivAt_zero : ∀ x, HasDerivAt f0 (f1 x) x
  hasDerivAt_one : ∀ x, HasDerivAt f1 (f2 x) x
  hasDerivAt_two : ∀ x, HasDerivAt f2 (f3 x) x
  hasDerivAt_three : ∀ x, HasDerivAt f3 (f4 x) x
  hasDerivAt_four : ∀ x, HasDerivAt f4 (f5 x) x
  hasDerivAt_five : ∀ x, HasDerivAt f5 (f6 x) x
  hasDerivAt_six : ∀ x, HasDerivAt f6 (f7 x) x

def profileTravelingWave (P : RealProfileJet7) (A k c t x : ℝ) : ℝ :=
  A * P.f0 (k * (x - c * t))

def profileTravelingWaveJet7 (P : RealProfileJet7) (A k c : ℝ) :
    RealEvolutionJet7 where
  toRealEvolutionJet5 := {
    toRealEvolutionJet3 := {
      u := profileTravelingWave P A k c
      ut := fun t x => -A * k * c * P.f1 (k * (x - c * t))
      ux := fun t x => A * k * P.f1 (k * (x - c * t))
      uxx := fun t x => A * k ^ (2 : ℕ) * P.f2 (k * (x - c * t))
      uxxx := fun t x => A * k ^ (3 : ℕ) * P.f3 (k * (x - c * t))
      hasDerivAt_time := by
        intro t x
        have hz : HasDerivAt (fun s : ℝ => k * (x - c * s)) (k * (0 - c * 1)) t := by
          have hz0 :=
            ((hasDerivAt_const t x).sub ((hasDerivAt_id t).const_mul c)).const_mul k
          apply hz0.congr_of_eventuallyEq
          filter_upwards with y
          rfl
        have h := ((P.hasDerivAt_zero (k * (x - c * t))).comp t hz).const_mul A
        apply h.congr_deriv
        ring
      hasDerivAt_space := by
        intro t x
        have hz : HasDerivAt (fun y : ℝ => k * (y - c * t)) k x := by
          simpa only [id_eq, mul_one] using
            ((hasDerivAt_id x).sub_const (c * t)).const_mul k
        have h := ((P.hasDerivAt_zero (k * (x - c * t))).comp x hz).const_mul A
        apply h.congr_deriv
        ring
      hasDerivAt_space_one := by
        intro t x
        have hz : HasDerivAt (fun y : ℝ => k * (y - c * t)) k x := by
          simpa only [id_eq, mul_one] using
            ((hasDerivAt_id x).sub_const (c * t)).const_mul k
        have h := ((P.hasDerivAt_one (k * (x - c * t))).comp x hz).const_mul (A * k)
        apply h.congr_deriv
        ring
      hasDerivAt_space_two := by
        intro t x
        have hz : HasDerivAt (fun y : ℝ => k * (y - c * t)) k x := by
          simpa only [id_eq, mul_one] using
            ((hasDerivAt_id x).sub_const (c * t)).const_mul k
        have h := ((P.hasDerivAt_two (k * (x - c * t))).comp x hz).const_mul (A * k ^ (2 : ℕ))
        apply h.congr_deriv
        ring
    }
    uxxxx := fun t x => A * k ^ (4 : ℕ) * P.f4 (k * (x - c * t))
    uxxxxx := fun t x => A * k ^ (5 : ℕ) * P.f5 (k * (x - c * t))
    hasDerivAt_space_three := by
      intro t x
      have hz : HasDerivAt (fun y : ℝ => k * (y - c * t)) k x := by
        simpa only [id_eq, mul_one] using
          ((hasDerivAt_id x).sub_const (c * t)).const_mul k
      have h := ((P.hasDerivAt_three (k * (x - c * t))).comp x hz).const_mul (A * k ^ (3 : ℕ))
      apply h.congr_deriv
      ring
    hasDerivAt_space_four := by
      intro t x
      have hz : HasDerivAt (fun y : ℝ => k * (y - c * t)) k x := by
        simpa only [id_eq, mul_one] using
          ((hasDerivAt_id x).sub_const (c * t)).const_mul k
      have h := ((P.hasDerivAt_four (k * (x - c * t))).comp x hz).const_mul (A * k ^ (4 : ℕ))
      apply h.congr_deriv
      ring
  }
  uxxxxxx := fun t x => A * k ^ (6 : ℕ) * P.f6 (k * (x - c * t))
  uxxxxxxx := fun t x => A * k ^ (7 : ℕ) * P.f7 (k * (x - c * t))
  hasDerivAt_space_five := by
    intro t x
    have hz : HasDerivAt (fun y : ℝ => k * (y - c * t)) k x := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id x).sub_const (c * t)).const_mul k
    have h := ((P.hasDerivAt_five (k * (x - c * t))).comp x hz).const_mul (A * k ^ (5 : ℕ))
    apply h.congr_deriv
    ring
  hasDerivAt_space_six := by
    intro t x
    have hz : HasDerivAt (fun y : ℝ => k * (y - c * t)) k x := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id x).sub_const (c * t)).const_mul k
    have h := ((P.hasDerivAt_six (k * (x - c * t))).comp x hz).const_mul (A * k ^ (6 : ℕ))
    apply h.congr_deriv
    ring

def solitonS (x : ℝ) : ℝ := solitonQ x ^ (3 : ℕ)
def solitonS1 (x : ℝ) : ℝ := -6 * solitonT x * solitonQ x ^ (3 : ℕ)
def solitonS2 (x : ℝ) : ℝ := 36 * solitonQ x ^ (3 : ℕ) - 42 * solitonQ x ^ (4 : ℕ)
def solitonS3 (x : ℝ) : ℝ := -216 * solitonT x * solitonQ x ^ (3 : ℕ) + 336 * solitonT x * solitonQ x ^ (4 : ℕ)
def solitonS4 (x : ℝ) : ℝ := 1296 * solitonQ x ^ (3 : ℕ) - 4200 * solitonQ x ^ (4 : ℕ) + 3024 * solitonQ x ^ (5 : ℕ)
def solitonS5 (x : ℝ) : ℝ := -7776 * solitonT x * solitonQ x ^ (3 : ℕ) + 33600 * solitonT x * solitonQ x ^ (4 : ℕ) - 30240 * solitonT x * solitonQ x ^ (5 : ℕ)
def solitonS6 (x : ℝ) : ℝ := 46656 * solitonQ x ^ (3 : ℕ) - 323232 * solitonQ x ^ (4 : ℕ) + 604800 * solitonQ x ^ (5 : ℕ) - 332640 * solitonQ x ^ (6 : ℕ)
def solitonS7 (x : ℝ) : ℝ := -279936 * solitonT x * solitonQ x ^ (3 : ℕ) + 2585856 * solitonT x * solitonQ x ^ (4 : ℕ) - 6048000 * solitonT x * solitonQ x ^ (5 : ℕ) + 3991680 * solitonT x * solitonQ x ^ (6 : ℕ)

theorem hasDerivAt_solitonS (x : ℝ) : HasDerivAt solitonS (solitonS1 x) x := by
  have h := (hasDerivAt_solitonQ x).pow 3
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonS]
  · simp [solitonS1, solitonQ1]
    ring

theorem hasDerivAt_solitonS1 (x : ℝ) : HasDerivAt solitonS1 (solitonS2 x) x := by
  have h := ((hasDerivAt_solitonT x).mul ((hasDerivAt_solitonQ x).pow 3)).const_mul (-6 : ℝ)
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonS1]
    ring
  · simp [solitonS2, solitonQ1, solitonQ]
    ring

theorem hasDerivAt_solitonS2 (x : ℝ) : HasDerivAt solitonS2 (solitonS3 x) x := by
  have h := ((hasDerivAt_solitonQ x).pow 3).const_mul (36 : ℝ) |>.sub
    (((hasDerivAt_solitonQ x).pow 4).const_mul (42 : ℝ))
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonS2]
  · simp [solitonS3, solitonQ1]
    ring

theorem hasDerivAt_solitonS3 (x : ℝ) : HasDerivAt solitonS3 (solitonS4 x) x := by
  have h := (((hasDerivAt_solitonT x).mul ((hasDerivAt_solitonQ x).pow 3)).const_mul (-216 : ℝ)).add
    (((hasDerivAt_solitonT x).mul ((hasDerivAt_solitonQ x).pow 4)).const_mul (336 : ℝ))
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonS3]
    ring
  · simp [solitonS4, solitonQ1, solitonQ]
    ring

theorem hasDerivAt_solitonS4 (x : ℝ) : HasDerivAt solitonS4 (solitonS5 x) x := by
  have h := ((((hasDerivAt_solitonQ x).pow 3).const_mul (1296 : ℝ)).sub
    (((hasDerivAt_solitonQ x).pow 4).const_mul (4200 : ℝ))).add
    (((hasDerivAt_solitonQ x).pow 5).const_mul (3024 : ℝ))
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonS4]
  · simp [solitonS5, solitonQ1]
    ring

theorem hasDerivAt_solitonS5 (x : ℝ) : HasDerivAt solitonS5 (solitonS6 x) x := by
  have h := ((((hasDerivAt_solitonT x).mul ((hasDerivAt_solitonQ x).pow 3)).const_mul (-7776 : ℝ)).add
    (((hasDerivAt_solitonT x).mul ((hasDerivAt_solitonQ x).pow 4)).const_mul (33600 : ℝ))).sub
    (((hasDerivAt_solitonT x).mul ((hasDerivAt_solitonQ x).pow 5)).const_mul (30240 : ℝ))
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonS5]
    ring
  · simp [solitonS6, solitonQ1, solitonQ]
    ring

theorem hasDerivAt_solitonS6 (x : ℝ) : HasDerivAt solitonS6 (solitonS7 x) x := by
  have h := (((((hasDerivAt_solitonQ x).pow 3).const_mul (46656 : ℝ)).sub
    (((hasDerivAt_solitonQ x).pow 4).const_mul (323232 : ℝ))).add
    (((hasDerivAt_solitonQ x).pow 5).const_mul (604800 : ℝ))).sub
    (((hasDerivAt_solitonQ x).pow 6).const_mul (332640 : ℝ))
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonS6]
  · simp [solitonS7, solitonQ1]
    ring

def solitonSProfileJet7 : RealProfileJet7 where
  f0 := solitonS
  f1 := solitonS1
  f2 := solitonS2
  f3 := solitonS3
  f4 := solitonS4
  f5 := solitonS5
  f6 := solitonS6
  f7 := solitonS7
  hasDerivAt_zero := hasDerivAt_solitonS
  hasDerivAt_one := hasDerivAt_solitonS1
  hasDerivAt_two := hasDerivAt_solitonS2
  hasDerivAt_three := hasDerivAt_solitonS3
  hasDerivAt_four := hasDerivAt_solitonS4
  hasDerivAt_five := hasDerivAt_solitonS5
  hasDerivAt_six := hasDerivAt_solitonS6

def imotoSeventhOrderSolitonJet (k : ℝ) : RealEvolutionJet7 :=
  profileTravelingWaveJet7 solitonSProfileJet7 1 k (230400 * k ^ (6 : ℕ))

theorem imotoSeventhOrderSoliton_solves (k : ℝ) :
    SolvesSeventhOrderHierarchy (665280 * k ^ (6 : ℕ)) (12304 * k ^ (4 : ℕ)) (-200 * k ^ (2 : ℕ)) 1
      (imotoSeventhOrderSolitonJet k) := by
  intro t x
  simp only [imotoSeventhOrderSolitonJet, profileTravelingWaveJet7, profileTravelingWave,
    solitonSProfileJet7]
  simp [solitonS, solitonS1, solitonS3, solitonS5, solitonS7]
  ring

def solitonQ6 (x : ℝ) : ℝ :=
  64 * solitonQ x - 2016 * solitonQ x ^ (2 : ℕ) + 6720 * solitonQ x ^ (3 : ℕ) - 5040 * solitonQ x ^ (4 : ℕ)
def solitonQ7 (x : ℝ) : ℝ :=
  -128 * solitonT x * solitonQ x + 8064 * solitonT x * solitonQ x ^ (2 : ℕ) -
    40320 * solitonT x * solitonQ x ^ (3 : ℕ) + 40320 * solitonT x * solitonQ x ^ (4 : ℕ)

theorem hasDerivAt_solitonQ5 (x : ℝ) : HasDerivAt solitonQ5 (solitonQ6 x) x := by
  have h := ((((hasDerivAt_solitonT x).mul (hasDerivAt_solitonQ x)).const_mul (-32 : ℝ)).add
    (((hasDerivAt_solitonT x).mul ((hasDerivAt_solitonQ x).pow 2)).const_mul (480 : ℝ))).sub
    (((hasDerivAt_solitonT x).mul ((hasDerivAt_solitonQ x).pow 3)).const_mul (720 : ℝ))
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonQ5]
    ring
  · simp [solitonQ6, solitonQ1, solitonQ]
    ring

theorem hasDerivAt_solitonQ6 (x : ℝ) : HasDerivAt solitonQ6 (solitonQ7 x) x := by
  have h := ((((hasDerivAt_solitonQ x).const_mul (64 : ℝ)).sub
    (((hasDerivAt_solitonQ x).pow 2).const_mul (2016 : ℝ))).add
    (((hasDerivAt_solitonQ x).pow 3).const_mul (6720 : ℝ))).sub
    (((hasDerivAt_solitonQ x).pow 4).const_mul (5040 : ℝ))
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonQ6]
  · simp [solitonQ7, solitonQ1]
    ring

def solitonQProfileJet7 : RealProfileJet7 where
  f0 := solitonQ
  f1 := solitonQ1
  f2 := solitonQ2
  f3 := solitonQ3
  f4 := solitonQ4
  f5 := solitonQ5
  f6 := solitonQ6
  f7 := solitonQ7
  hasDerivAt_zero := hasDerivAt_solitonQ
  hasDerivAt_one := hasDerivAt_solitonQ1
  hasDerivAt_two := hasDerivAt_solitonQ2
  hasDerivAt_three := hasDerivAt_solitonQ3
  hasDerivAt_four := hasDerivAt_solitonQ4
  hasDerivAt_five := hasDerivAt_solitonQ5
  hasDerivAt_six := hasDerivAt_solitonQ6

def laxSeventhSolitonJet : RealEvolutionJet7 :=
  profileTravelingWaveJet7 solitonQProfileJet7 (1 / 2) (1 / 2) 1

theorem laxSeventhSoliton_solves : SolvesLaxSeventh laxSeventhSolitonJet := by
  intro t x
  simp only [laxSeventhSolitonJet, profileTravelingWaveJet7, profileTravelingWave,
    solitonQProfileJet7]
  simp [solitonQ1, solitonQ2, solitonQ3, solitonQ4, solitonQ5, solitonQ7,
    solitonQ]
  ring

def coshProfileJet7 : RealProfileJet7 where
  f0 := Real.cosh
  f1 := Real.sinh
  f2 := Real.cosh
  f3 := Real.sinh
  f4 := Real.cosh
  f5 := Real.sinh
  f6 := Real.cosh
  f7 := Real.sinh
  hasDerivAt_zero := Real.hasDerivAt_cosh
  hasDerivAt_one := Real.hasDerivAt_sinh
  hasDerivAt_two := Real.hasDerivAt_cosh
  hasDerivAt_three := Real.hasDerivAt_sinh
  hasDerivAt_four := Real.hasDerivAt_cosh
  hasDerivAt_five := Real.hasDerivAt_sinh
  hasDerivAt_six := Real.hasDerivAt_cosh

def linearSeventhCoshJet (mu : ℝ) : RealEvolutionJet7 :=
  profileTravelingWaveJet7 coshProfileJet7 1 mu (mu ^ (6 : ℕ))

theorem linearSeventhCosh_solves (mu : ℝ) :
    SolvesLinearSeventh (linearSeventhCoshJet mu) := by
  intro t x
  simp [linearSeventhCoshJet, profileTravelingWaveJet7, coshProfileJet7]
  ring

end


end GaloisForLFunctions.HTGeometry.DispersivePDE

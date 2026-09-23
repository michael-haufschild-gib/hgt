import GaloisForLFunctions.HilbertMetric.ThreePointCorrelationLocal

/-!
# The fourth-jet wall at a coalesced three-point corner

For an even smooth radial profile, the second jet in the first gap of the three-point
correlation determinant vanishes to fourth order as the second gap coalesces.  This file proves
the exact fourth derivative and the resulting one-sided cusp theorem.  It is a generic analytic
bridge: no positive-definiteness or spectral hypothesis is assumed.
-/

open Set

namespace HilbertMetric

/-- The scalar wall left by the second first-gap derivative at `0,x,x+y`. -/
def threePointCoalescedWall
    (f f₁ f₂ : ℝ → ℝ) (y : ℝ) : ℝ :=
  (-f₂ 0) * (f 0 ^ (2 : ℕ) - f y ^ (2 : ℕ)) - f 0 * f₁ y ^ (2 : ℕ)

def threePointCoalescedWallFirstJet
    (f f₁ f₂ : ℝ → ℝ) (y : ℝ) : ℝ :=
  2 * f₁ y * (f₂ 0 * f y - f 0 * f₂ y)

def threePointCoalescedWallSecondJet
    (f f₁ f₂ f₃ : ℝ → ℝ) (y : ℝ) : ℝ :=
  2 * f₂ y * (f₂ 0 * f y - f 0 * f₂ y) +
    2 * f₁ y * (f₂ 0 * f₁ y - f 0 * f₃ y)

def threePointCoalescedWallThirdJet
    (f f₁ f₂ f₃ f₄ : ℝ → ℝ) (y : ℝ) : ℝ :=
  2 * f₃ y * (f₂ 0 * f y - f 0 * f₂ y) +
    4 * f₂ y * (f₂ 0 * f₁ y - f 0 * f₃ y) +
      2 * f₁ y * (f₂ 0 * f₂ y - f 0 * f₄ y)

def threePointCoalescedWallFourthJet
    (f f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ) (y : ℝ) : ℝ :=
  2 * f₄ y * (f₂ 0 * f y - f 0 * f₂ y) +
    6 * f₃ y * (f₂ 0 * f₁ y - f 0 * f₃ y) +
      6 * f₂ y * (f₂ 0 * f₂ y - f 0 * f₄ y) +
        2 * f₁ y * (f₂ 0 * f₃ y - f 0 * f₅ y)

theorem hasDerivAt_threePointCoalescedWall
    {f f₁ f₂ : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x) (y : ℝ) :
    HasDerivAt (threePointCoalescedWall f f₁ f₂)
      (threePointCoalescedWallFirstJet f f₁ f₂ y) y := by
  have h := ((((hf y).mul (hf y)).const_mul (f₂ 0)).sub
    (((hf₁ y).mul (hf₁ y)).const_mul (f 0))).add_const
      ((-f₂ 0) * f 0 ^ (2 : ℕ))
  unfold threePointCoalescedWall threePointCoalescedWallFirstJet
  convert! h using 1 <;>
    (try funext x) <;>
    (try simp only [Pi.mul_apply, Pi.sub_apply]) <;>
    ring

theorem hasDerivAt_threePointCoalescedWallFirstJet
    {f f₁ f₂ f₃ : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x, HasDerivAt f₂ (f₃ x) x) (y : ℝ) :
    HasDerivAt (threePointCoalescedWallFirstJet f f₁ f₂)
      (threePointCoalescedWallSecondJet f f₁ f₂ f₃ y) y := by
  have h := ((hf₁ y).const_mul 2).mul
    (((hf y).const_mul (f₂ 0)).sub ((hf₂ y).const_mul (f 0)))
  unfold threePointCoalescedWallFirstJet threePointCoalescedWallSecondJet
  exact h

theorem hasDerivAt_threePointCoalescedWallSecondJet
    {f f₁ f₂ f₃ f₄ : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hf₃ : ∀ x, HasDerivAt f₃ (f₄ x) x) (y : ℝ) :
    HasDerivAt (threePointCoalescedWallSecondJet f f₁ f₂ f₃)
      (threePointCoalescedWallThirdJet f f₁ f₂ f₃ f₄ y) y := by
  have hA := ((hf₂ y).const_mul 2).mul
    (((hf y).const_mul (f₂ 0)).sub ((hf₂ y).const_mul (f 0)))
  have hB := ((hf₁ y).const_mul 2).mul
    (((hf₁ y).const_mul (f₂ 0)).sub ((hf₃ y).const_mul (f 0)))
  unfold threePointCoalescedWallSecondJet threePointCoalescedWallThirdJet
  convert! hA.add hB using 1 ;
    (try simp only [Pi.sub_apply]) ;
    ring

theorem hasDerivAt_threePointCoalescedWallThirdJet
    {f f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hf₃ : ∀ x, HasDerivAt f₃ (f₄ x) x)
    (hf₄ : ∀ x, HasDerivAt f₄ (f₅ x) x) (y : ℝ) :
    HasDerivAt (threePointCoalescedWallThirdJet f f₁ f₂ f₃ f₄)
      (threePointCoalescedWallFourthJet f f₁ f₂ f₃ f₄ f₅ y) y := by
  have hA := ((hf₃ y).const_mul 2).mul
    (((hf y).const_mul (f₂ 0)).sub ((hf₂ y).const_mul (f 0)))
  have hB := ((hf₂ y).const_mul 4).mul
    (((hf₁ y).const_mul (f₂ 0)).sub ((hf₃ y).const_mul (f 0)))
  have hC := ((hf₁ y).const_mul 2).mul
    (((hf₂ y).const_mul (f₂ 0)).sub ((hf₄ y).const_mul (f 0)))
  unfold threePointCoalescedWallThirdJet threePointCoalescedWallFourthJet
  convert! (hA.add hB).add hC using 1 ;
    (try simp only [Pi.sub_apply]) ;
    ring

theorem threePointCoalescedWallFourthJet_zero
    {f f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ}
    (h₁ : f₁ 0 = 0) (h₃ : f₃ 0 = 0) :
    threePointCoalescedWallFourthJet f f₁ f₂ f₃ f₄ f₅ 0 =
      -6 * f₂ 0 * (f 0 * f₄ 0 - f₂ 0 ^ (2 : ℕ)) := by
  simp [threePointCoalescedWallFourthJet, h₁, h₃]
  ring

/-- A negative center curvature and a strict fourth derivative Hankel determinant open a
positive wall for every sufficiently small positive second gap. -/
theorem exists_threePointCoalescedWall_pos_right
    {f f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hf₃ : ∀ x, HasDerivAt f₃ (f₄ x) x)
    (hf₄ : ∀ x, HasDerivAt f₄ (f₅ x) x)
    (hf₅ : Continuous f₅)
    (h₁ : f₁ 0 = 0) (h₃ : f₃ 0 = 0)
    (h₂ : f₂ 0 < 0) (h₄ : 0 < f 0 * f₄ 0 - f₂ 0 ^ (2 : ℕ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y, 0 < y → y < δ →
      0 < threePointCoalescedWall f f₁ f₂ y := by
  let W := threePointCoalescedWall f f₁ f₂
  let W₁ := threePointCoalescedWallFirstJet f f₁ f₂
  let W₂ := threePointCoalescedWallSecondJet f f₁ f₂ f₃
  let W₃ := threePointCoalescedWallThirdJet f f₁ f₂ f₃ f₄
  let W₄ := threePointCoalescedWallFourthJet f f₁ f₂ f₃ f₄ f₅
  have hW : ∀ y, HasDerivAt W (W₁ y) y := fun y =>
    hasDerivAt_threePointCoalescedWall hf hf₁ y
  have hW₁ : ∀ y, HasDerivAt W₁ (W₂ y) y := fun y =>
    hasDerivAt_threePointCoalescedWallFirstJet hf hf₁ hf₂ y
  have hW₂ : ∀ y, HasDerivAt W₂ (W₃ y) y := fun y =>
    hasDerivAt_threePointCoalescedWallSecondJet hf hf₁ hf₂ hf₃ y
  have hW₃ : ∀ y, HasDerivAt W₃ (W₄ y) y := fun y =>
    hasDerivAt_threePointCoalescedWallThirdJet hf hf₁ hf₂ hf₃ hf₄ y
  have hcont (g g' : ℝ → ℝ) (hg : ∀ y, HasDerivAt g (g' y) y) : Continuous g :=
    continuous_iff_continuousAt.mpr fun y => (hg y).continuousAt
  have hW₄ : Continuous W₄ := by
    have h0 := hcont f f₁ hf
    have h1 := hcont f₁ f₂ hf₁
    have h2 := hcont f₂ f₃ hf₂
    have h3 := hcont f₃ f₄ hf₃
    have h4 := hcont f₄ f₅ hf₄
    dsimp [W₄]
    unfold threePointCoalescedWallFourthJet
    fun_prop
  have hWzero : W 0 = 0 := by
    simp [W, threePointCoalescedWall, h₁]
  have hW₁zero : W₁ 0 = 0 := by
    simp [W₁, threePointCoalescedWallFirstJet, h₁]
  have hW₂zero : W₂ 0 = 0 := by
    dsimp [W₂]
    simp only [threePointCoalescedWallSecondJet, h₁]
    ring
  have hW₃zero : W₃ 0 = 0 := by
    simp [W₃, threePointCoalescedWallThirdJet, h₁, h₃]
  have hW₄pos : 0 < W₄ 0 := by
    rw [show W₄ 0 = -6 * f₂ 0 * (f 0 * f₄ 0 - f₂ 0 ^ (2 : ℕ)) by
      exact threePointCoalescedWallFourthJet_zero h₁ h₃]
    exact mul_pos (mul_pos_of_neg_of_neg (by norm_num) h₂) h₄
  rcases exists_pos_right_of_secondJet_pos hW₂ hW₃ hW₄ hW₂zero hW₃zero hW₄pos with
    ⟨δ, hδ, hW₂pos⟩
  refine ⟨δ, hδ, ?_⟩
  exact pos_right_of_secondJet_posOn hW hW₁ hWzero hW₁zero hδ fun y hy => by
    have hy' : 0 < y ∧ y < δ := by simpa [interior_Icc, hδ.ne'] using hy
    exact hW₂pos y hy'.1 hy'.2

end HilbertMetric

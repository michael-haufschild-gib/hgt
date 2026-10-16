import GaloisForLFunctions.RHTower.PaperThetaNativeContourBlocks

/-! # Gaussian source regularization pays the complete native contour series

The original good-height schedule supplies reciprocal Xi control. A fixed
theta strip supplies one spatial increment control. Their product is summable
after actual Gaussian source regularization, without separating any zeros.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction DeningerMeyerNaturalTopology

namespace RHTower.PaperThetaEndpoint

theorem gaussian_nativeXiBlock_control (S : DeningerMeyerXiContourSchedule)
    (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ → ℝ, Summable c ∧ ∀ n,
      0 ≤ c n ∧
      ‖nativeXiBlock S (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g))
        (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable n‖ ≤ c n ∧
      ∀ x y,
        ‖nativeXiBlock S (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g))
            (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable n y-
          nativeXiBlock S (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g))
            (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable n x‖ ≤
          c n*|stripCutControl (3/2) y-stripCutControl (3/2) x| := by
  let F := deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g)
  have hF : Differentiable ℂ F := (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable
  obtain ⟨A, hA, hmass⟩ := S.gaussian_quotient g hε
  obtain ⟨C₀, hC₀, hnorm₀, hinc₀⟩ := nativeXiBlock_central_control S F hF
  let W := 1+stripTailControl (3/2) 0
  have hW : 0 ≤ W := by dsimp [W]; linarith [stripTailControl_nonneg (3/2) 0]
  let c : ℕ → ℝ
    | 0 => C₀
    | n+1 => 16*A*(S.height n+5)^S.exponent*(1+(S.height n+6)^2)*W/Real.pi*
        Real.exp ((Real.pi/4)*S.height n-ε*(S.height n)^2)
  have hc : ∀ n, 0 ≤ c n := by
    intro n
    cases n with
    | zero => exact hC₀
    | succ n => dsimp [c]; have ht := S.height_pos n; positivity
  have hblock : ∀ n, ‖nativeXiBlock S F hF n‖ ≤ c n ∧ ∀ x y,
      ‖nativeXiBlock S F hF n y-nativeXiBlock S F hF n x‖ ≤
        c n*|stripCutControl (3/2) y-stripCutControl (3/2) x| := by
    intro n
    cases n with
    | zero => exact ⟨hnorm₀, hinc₀⟩
    | succ n =>
      let U := S.height n
      let mass := A*(U+5)^S.exponent*Real.exp ((Real.pi/4)*U-ε*U^2)
      let P := 1+(U+6)^2
      let D := 8*mass*P*W/Real.pi
      have hU : 0 < U := S.height_pos n
      have hm : 0 ≤ mass := by dsimp [mass]; positivity
      have hP : 0 ≤ P := by dsimp [P]; positivity
      have hTP : 1+(U+7) ≤ P := by dsimp [P]; nlinarith
      have hstep (a b : ℂ) (hnz : ∀ s ∈ RectangleBorder a b, xi s ≠ 0)
          (hlen : |b.re-a.re|+|b.im-a.im| ≤ 8)
          (hb : ∀ s ∈ RectangleBorder a b, ‖F s/xi s‖ ≤ mass ∧
            |(thetaContourParameter s).im| ≤ 3/2 ∧ ‖thetaContourParameter s‖ ≤ U+7) :
          ‖nativeXiContourBCF F hF a b hnz‖ ≤ D ∧ ∀ x y,
            ‖nativeXiContourBCF F hF a b hnz y-nativeXiContourBCF F hF a b hnz x‖ ≤
              D*|stripCutControl (3/2) y-stripCutControl (3/2) x| := by
        obtain ⟨_, hnorm, hinc⟩ := nativeXiContour_control hF hnz hm (by linarith : 0 ≤ U+7) hb
        have hcoef : (|b.re-a.re|+|b.im-a.im|)*mass*(1+(U+7))*W/Real.pi ≤ D := by
          dsimp [D]
          gcongr
        exact ⟨hnorm.trans hcoef, fun x y => (hinc x y).trans
          (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _))⟩
      have hgap := S.height_next_gap n
      have hu := hstep (deningerXiContourLeft U) (deningerXiContourRight (S.height (n+1)))
        (S.upper_nonzero n) (by
          simp only [deningerXiContourRight_re, deningerXiContourLeft_re,
            deningerXiContourRight_im, deningerXiContourLeft_im]
          rw [abs_of_nonneg (by dsimp [U]; linarith : 0 ≤ S.height (n+1)-U)]
          norm_num
          dsimp [U]
          linarith)
        (fun s hs => by
          obtain ⟨hr₁, hr₂, _, hi, _⟩ := S.upper_geometry n hs
          exact ⟨hmass n s (Or.inl hs), thetaContourParameter_strip hr₁ hr₂,
            by simpa [U, add_assoc] using thetaContourParameter_norm hr₁ hr₂ hi⟩)
      have hl := hstep (deningerXiContourLeft (-S.height (n+1))) (deningerXiContourRight (-U))
        (S.lower_nonzero n) (by
          simp only [deningerXiContourRight_re, deningerXiContourLeft_re,
            deningerXiContourRight_im, deningerXiContourLeft_im, sub_neg_eq_add]
          rw [abs_of_nonneg (by dsimp [U]; linarith : 0 ≤ -U+S.height (n+1))]
          norm_num
          dsimp [U]
          linarith)
        (fun s hs => by
          obtain ⟨hr₁, hr₂, _, hi, _⟩ := S.lower_geometry n hs
          exact ⟨hmass n s (Or.inr hs), thetaContourParameter_strip hr₁ hr₂,
            by simpa [U, add_assoc] using thetaContourParameter_norm hr₁ hr₂ hi⟩)
      have hcd : c (n+1) = 2*D := by dsimp [c, D, mass, P, U]; ring
      rw [hcd]
      constructor
      · exact (norm_add_le _ _).trans (by linarith [hu.1, hl.1])
      · intro x y
        change ‖(nativeXiContour F _ _ 0 y+nativeXiContour F _ _ 0 y)-
          (nativeXiContour F _ _ 0 x+nativeXiContour F _ _ 0 x)‖ ≤ _
        rw [show nativeXiContour F (deningerXiContourLeft U) (deningerXiContourRight (S.height (n+1))) 0 y+
            nativeXiContour F (deningerXiContourLeft (-S.height (n+1))) (deningerXiContourRight (-U)) 0 y-
            (nativeXiContour F (deningerXiContourLeft U) (deningerXiContourRight (S.height (n+1))) 0 x+
            nativeXiContour F (deningerXiContourLeft (-S.height (n+1))) (deningerXiContourRight (-U)) 0 x) =
            (nativeXiContour F (deningerXiContourLeft U) (deningerXiContourRight (S.height (n+1))) 0 y-
            nativeXiContour F (deningerXiContourLeft U) (deningerXiContourRight (S.height (n+1))) 0 x)+
            (nativeXiContour F (deningerXiContourLeft (-S.height (n+1))) (deningerXiContourRight (-U)) 0 y-
            nativeXiContour F (deningerXiContourLeft (-S.height (n+1))) (deningerXiContourRight (-U)) 0 x) by ring]
        exact (norm_add_le _ _).trans (by
          have hx := hu.2 x y
          have hy := hl.2 x y
          simp only [nativeXiContourBCF_apply] at hx hy
          linarith)
  have ht : ∀ i : ℕ, (i : ℝ) ≤ S.height (i-1) := by
    intro i
    cases i with
    | zero => simpa using (S.height_pos 0).le
    | succ n =>
        simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one]
        linarith [S.height_ge n, Nat.cast_nonneg (α := ℝ) n]
  have he := deningerGaussianContourMass_eventually hε (Real.pi/4) (16*A*W/Real.pi)
    (by positivity) S.exponent 1 (fun i => S.height (i-1)) ht
  have hcs : Summable c := by
    apply Summable.of_norm_bounded_eventually deningerMeyerContourMajorant_summable
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [he, eventually_ge_atTop 1] with i hi hi₁
    cases i with
    | zero => omega
    | succ n =>
        rw [Real.norm_eq_abs, abs_of_nonneg (hc (n+1))]
        have heq : c (n+1) = (16*A*W/Real.pi)*(S.height n+5)^S.exponent*
            (1+(S.height n+6)^2)^1*Real.exp ((Real.pi/4)*S.height n-ε*(S.height n)^2) := by
          dsimp [c]
          ring
        rw [heq]
        simpa only [Nat.succ_sub_one] using hi
  exact ⟨c, hcs, fun n => ⟨hc n, (hblock n).1, (hblock n).2⟩⟩

theorem gaussian_nativeXiBlock_summable (S : DeningerMeyerXiContourSchedule)
    (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε) :
    Summable (nativeXiBlock S
      (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g))
      (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable) := by
  obtain ⟨c, hc, hb⟩ := gaussian_nativeXiBlock_control S g hε
  exact hc.of_norm_bounded (fun n => (hb n).2.1)

def nativeGaussianSource (S : DeningerMeyerXiContourSchedule)
    (g : DeningerMeyerStrongLogTarget) (ε : ℝ) (hε : 0 < ε) : NativeContinuousSpace :=
  ∑' n, nativeXiBlock S
    (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g))
    (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable n

end RHTower.PaperThetaEndpoint

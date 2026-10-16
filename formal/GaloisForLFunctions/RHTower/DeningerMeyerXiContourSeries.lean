import GaloisForLFunctions.RHTower.DeningerMeyerXiContourSource
import GaloisForLFunctions.RHTower.DeningerMeyerXiContourQuotient
import GaloisForLFunctions.RHTower.DeningerMeyerGaussianContourMass
import GaloisForLFunctions.RHTower.DeningerMeyerSourceSeries

/-! # Summable actual Xi contour blocks in the original source -/

open Complex Set Filter Topology
open HTGeometry GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology

namespace DeningerMeyerXiContourSchedule

variable (S : DeningerMeyerXiContourSchedule)

theorem central_nonzero : ∀ z ∈ RectangleBorder (deningerXiContourLeft (-S.height 0))
    (deningerXiContourRight (S.height 0)), xi z ≠ 0 := by
  intro z hz
  exact S.band_nonzero (by linarith [S.height_pos 0])
    ⟨0, by rw [abs_neg, abs_of_pos (S.height_pos 0)]⟩
    ⟨0, abs_of_pos (S.height_pos 0)⟩ hz

theorem upper_nonzero (n : ℕ) : ∀ z ∈ RectangleBorder (deningerXiContourLeft (S.height n))
    (deningerXiContourRight (S.height (n+1))), xi z ≠ 0 := by
  intro z hz
  exact S.band_nonzero (by linarith [(S.height_next_gap n).1])
    ⟨n, abs_of_pos (S.height_pos n)⟩ ⟨n+1, abs_of_pos (S.height_pos (n+1))⟩ hz

theorem lower_nonzero (n : ℕ) : ∀ z ∈ RectangleBorder (deningerXiContourLeft (-S.height (n+1)))
    (deningerXiContourRight (-S.height n)), xi z ≠ 0 := by
  intro z hz
  exact S.band_nonzero (by linarith [(S.height_next_gap n).1])
    ⟨n+1, by rw [abs_neg, abs_of_pos (S.height_pos (n+1))]⟩
    ⟨n, by rw [abs_neg, abs_of_pos (S.height_pos n)]⟩ hz

def xiBlock (F : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => deningerMeyerXiContour F (deningerXiContourLeft (-S.height 0))
      (deningerXiContourRight (S.height 0))
  | n+1 => fun z =>
      deningerMeyerXiContour F (deningerXiContourLeft (S.height n))
        (deningerXiContourRight (S.height (n+1))) z +
      deningerMeyerXiContour F (deningerXiContourLeft (-S.height (n+1)))
        (deningerXiContourRight (-S.height n)) z

theorem xiBlock_regular {F : ℂ → ℂ} (hF : Differentiable ℂ F) (n : ℕ) :
    DeningerEntireMellinRegular (S.xiBlock F n) := by
  cases n with
  | zero =>
      exact deningerMeyerXiContour_entireRegular hF (by simp) (by simp)
        (by simp; linarith [S.height_pos 0]) S.central_nonzero
  | succ n =>
      have hu := deningerMeyerXiContour_entireRegular hF
        (a := deningerXiContourLeft (S.height n)) (b := deningerXiContourRight (S.height (n+1)))
        (by simp) (by simp) (by simp; linarith [(S.height_next_gap n).1]) (S.upper_nonzero n)
      have hl := deningerMeyerXiContour_entireRegular hF
        (a := deningerXiContourLeft (-S.height (n+1))) (b := deningerXiContourRight (-S.height n))
        (by simp) (by simp) (by simp; linarith [(S.height_next_gap n).1]) (S.lower_nonzero n)
      exact fun a b => (hu a b).add (hl a b)

def xiBlockSource (F : ℂ → ℂ) (hF : Differentiable ℂ F) (n : ℕ) :
    DeningerMeyerStrongLogTarget :=
  deningerMeyerInverseMellinSource (S.xiBlock F n) (S.xiBlock_regular hF n)

@[simp] theorem xiBlockSource_mellin (F : ℂ → ℂ) (hF : Differentiable ℂ F) (n : ℕ) (z : ℂ) :
    deningerMeyerStrongLogMellin (S.xiBlockSource F hF n) z = S.xiBlock F n z :=
  deningerMeyerInverseMellinSource_mellin _ _

theorem gaussian_xiBlock_weighted_eventually (g : DeningerMeyerStrongLogTarget)
    {ε : ℝ} (hε : 0 < ε) (r : ℝ) (K : ℕ) :
    ∀ᶠ i in cofinite, ∀ z : ℂ, |z.re| ≤ r →
      ‖S.xiBlock (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g)) i z‖*
        (1+z.im^2)^K ≤ deningerMeyerContourMajorant i := by
  let F := deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g)
  have hF : Differentiable ℂ F := (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable
  obtain ⟨C, hC, hcontour⟩ := deningerMeyerXiContour_weighted_bound r K
  obtain ⟨A, hA, hmass⟩ := S.gaussian_quotient g hε
  have ht : ∀ i : ℕ, (i : ℝ) ≤ S.height (i-1) := by
    intro i
    cases i with
    | zero => simpa using (S.height_pos 0).le
    | succ n =>
        simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one]
        linarith [S.height_ge n, Nat.cast_nonneg (α := ℝ) n]
  have he := deningerGaussianContourMass_eventually hε (Real.pi/4) (16*C*A)
    (by positivity) S.exponent K (fun i => S.height (i-1)) ht
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [he, eventually_ge_atTop 1] with i hi hi₁
  cases i with
  | zero => omega
  | succ n =>
    intro z hz
    let U := S.height n
    let mass := A*(U+5)^S.exponent*Real.exp ((Real.pi/4)*U-ε*U^2)
    have hU : 0 < U := S.height_pos n
    have hm : 0 ≤ mass := by dsimp [mass]; positivity
    have hstep (a b : ℂ) (ha : a.re = -1) (hb : b.re = 2) (hab : a.im ≤ b.im)
        (haU : -(U+5) ≤ a.im) (hbU : b.im ≤ U+5)
        (hnz : ∀ w ∈ RectangleBorder a b, xi w ≠ 0)
        (hquot : ∀ w ∈ RectangleBorder a b, ‖F w/xi w‖ ≤ mass)
        (hgap : |b.im-a.im| ≤ 5) :
        ‖deningerMeyerXiContour F a b z‖*(1+z.im^2)^K ≤
          8*C*mass*(1+(U+6)^2)^K := by
      have h := hcontour F hF a b ha hb hab (U+5) mass (by positivity) haU hbU hm hnz hquot z hz
      have hw : (U+5)+1 = U+6 := by ring
      rw [hw] at h
      calc
        ‖deningerMeyerXiContour F a b z‖*(1+z.im^2)^K ≤
            C*(3+|b.im-a.im|)*mass*(1+(U+6)^2)^K := h
        _ ≤ C*8*mass*(1+(U+6)^2)^K := by gcongr; linarith
        _ = 8*C*mass*(1+(U+6)^2)^K := by ring
    have hgap := S.height_next_gap n
    have hu := hstep (deningerXiContourLeft U) (deningerXiContourRight (S.height (n+1)))
      (by simp) (by simp) (by simp; dsimp [U]; linarith)
      (by simp; linarith) (by simp; dsimp [U]; linarith) (S.upper_nonzero n)
      (fun w hw => hmass n w (Or.inl hw)) (by simp; rw [abs_of_nonneg (by dsimp [U]; linarith)]; exact hgap.2)
    have hl := hstep (deningerXiContourLeft (-S.height (n+1))) (deningerXiContourRight (-U))
      (by simp) (by simp) (by simp; dsimp [U]; linarith)
      (by simp; dsimp [U]; linarith) (by simp; linarith) (S.lower_nonzero n)
      (fun w hw => hmass n w (Or.inr hw)) (by
        simp only [deningerXiContourRight_im, deningerXiContourLeft_im, sub_neg_eq_add]
        have h : -U+S.height (n+1) = S.height (n+1)-S.height n := by dsimp [U]; ring
        rw [h, abs_of_nonneg (by linarith)]
        exact hgap.2)
    calc
      ‖S.xiBlock F (n+1) z‖*(1+z.im^2)^K ≤
          (‖deningerMeyerXiContour F (deningerXiContourLeft U) (deningerXiContourRight (S.height (n+1))) z‖+
           ‖deningerMeyerXiContour F (deningerXiContourLeft (-S.height (n+1))) (deningerXiContourRight (-U)) z‖)*
            (1+z.im^2)^K := mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
      _ ≤ 16*C*mass*(1+(U+6)^2)^K := by rw [add_mul]; linarith
      _ = (16*C*A)*(U+5)^S.exponent*(1+(U+6)^2)^K*Real.exp ((Real.pi/4)*U-ε*U^2) := by
        dsimp [mass]; ring
      _ ≤ deningerMeyerContourMajorant (n+1) := by simpa only [Nat.succ_sub_one] using hi

theorem gaussian_xiBlockSource_summable (g : DeningerMeyerStrongLogTarget)
    {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n => S.xiBlockSource
      (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g))
      (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable n) :=
  deningerMeyerInverseMellinSource_summable
    (fun n => S.xiBlock_regular (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable n)
    deningerMeyerContourMajorant_summable (S.gaussian_xiBlock_weighted_eventually g hε)

end DeningerMeyerXiContourSchedule

end
end RHTower

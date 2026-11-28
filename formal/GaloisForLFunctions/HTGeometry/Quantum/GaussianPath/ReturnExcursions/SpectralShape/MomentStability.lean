import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic

/-! # Stability of standardized spectral skewness under a uniform error -/

open Finset
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
noncomputable section
variable {I : Type*} [Fintype I] [Nonempty I]

def moment (k : ℕ) (u : I → ℝ) : ℝ := 𝔼 i, u i^k

/-- Squared standardized third moment of a centered template. -/
def shape (u : I → ℝ) : ℝ := moment 3 u^2 / moment 2 u^3

private theorem pointwise_change {x y δ : ℝ} (h : |y-x|≤δ) (hd : δ≤1) :
    |y^2-x^2|≤δ*(x^2+2) ∧ |y^3-x^3|≤δ*(5*x^2+3) := by
  let a := |x|
  let d := y-x
  have hd' : |d|≤1 := h.trans hd
  have ha : 2*a≤x^2+1 := by nlinarith only [sq_nonneg (a-1),sq_abs x]
  have hh : 0≤δ := (abs_nonneg d).trans h
  have h2 : |y+x|≤2*a+1 := calc
    _ = |x+x+d| := by dsimp only [d]; congr 1; ring
    _ ≤ (|x|+|x|)+|d| := (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
    _ ≤ _ := by linarith only [hd']
  have h3 : |y^2+y*x+x^2|≤5*x^2+3 := by
    have he : y^2+y*x+x^2=3*x^2+3*x*d+d^2 := by dsimp only [d]; ring
    rw [he]
    have hl := (abs_add_le (3*x^2+3*x*d) (d^2)).trans
      (add_le_add (abs_add_le (3*x^2) (3*x*d)) le_rfl)
    rw [abs_of_nonneg (by positivity : 0≤3*x^2),abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3),
      abs_of_nonneg (sq_nonneg d)] at hl
    have hxd := mul_le_mul_of_nonneg_left hd' (by positivity : 0≤3*|x|)
    have hdd := pow_le_pow_left₀ (abs_nonneg d) hd' 2
    rw [sq_abs,one_pow] at hdd
    exact hl.trans (by dsimp only [a] at ha; nlinarith only [hxd,hdd,ha,sq_nonneg x])
  constructor
  · rw [show y^2-x^2=(y-x)*(y+x) by ring,abs_mul]
    exact mul_le_mul h (h2.trans (by linarith only [ha])) (abs_nonneg _) hh
  · rw [show y^3-x^3=(y-x)*(y^2+y*x+x^2) by ring,abs_mul]
    exact mul_le_mul h h3 (abs_nonneg _) hh

private theorem moment_change (u v : I → ℝ) {δ : ℝ} (hd : δ≤1)
    (h : ∀ i, |v i-u i|≤δ) (hu : moment 2 u=1) :
    |moment 2 v-1|≤3*δ ∧ |moment 3 v-moment 3 u|≤8*δ := by
  have hb (k : ℕ) (a b : ℝ) (hp : ∀ i, |v i^k-u i^k|≤δ*(a*u i^2+b)) :
      |moment k v-moment k u|≤δ*(a+b) := by
    unfold moment
    rw [←expect_sub_distrib]
    apply (abs_expect_le _ _).trans ((expect_le_expect (fun i _ => hp i)).trans ?_)
    rw [←mul_expect,expect_add_distrib,←mul_expect,Fintype.expect_const]
    change δ*(a*moment 2 u+b)≤_
    rw [hu,mul_one]
  constructor
  · rw [←hu]
    have h₂ := hb 2 1 2 (fun i => by simpa only [one_mul] using (pointwise_change (h i) hd).1)
    linarith only [h₂]
  · have h₃ := hb 3 5 3 (fun i => (pointwise_change (h i) hd).2)
    linarith only [h₃]

/-- With unit variance and fourth moment at most 43, changing every energy by
at most δ changes squared standardized skewness by at most 8000δ. The template
has positive variance throughout this range. -/
theorem shape_stability (u v : I → ℝ) {δ : ℝ} (hd₀ : 0≤δ) (hd : δ≤1/8)
    (h : ∀ i, |v i-u i|≤δ) (hu : moment 2 u=1) (hu₄ : moment 4 u≤43) :
    1/2≤moment 2 v ∧ |moment 3 u^2-shape v|≤8000*δ := by
  let A := moment 3 u
  let B := moment 3 v
  let V := moment 2 v
  obtain ⟨hV,hB⟩ := moment_change u v (hd.trans (by norm_num)) h hu
  have hVl : 1/2≤V := by linarith only [(abs_le.mp hV).1,hd]
  have hVu : V≤3/2 := by linarith only [(abs_le.mp hV).2,hd]
  have hA : |A|≤7 := by
    have hs := expect_mul_sq_le_sq_mul_sq univ u (fun i => u i^2)
    simp_rw [show ∀ i, u i*u i^2=u i^3 from fun i => by ring,
      show ∀ i, (u i^2)^2=u i^4 from fun i => by ring] at hs
    change A^2≤moment 2 u*moment 4 u at hs
    rw [hu,one_mul] at hs
    nlinarith only [hs,hu₄,sq_abs A,abs_nonneg A]
  have hB' : |B|≤8 := calc
    _ = |B-A+A| := by rw [sub_add_cancel]
    _ ≤ |B-A|+|A| := abs_add_le ..
    _ ≤ _ := by linarith only [hB,hA,hd]
  have hdiff : |A^2-B^2|≤120*δ := by
    rw [show A^2-B^2=(B-A)*(-(A+B)) by ring,abs_mul,abs_neg]
    have hs := (abs_add_le A B).trans (add_le_add hA hB')
    exact (mul_le_mul hB hs (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hc : |shape v|≤512 := by
    change |B^2/V^3|≤_
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (pow_nonneg (by linarith only [hVl]) _))]
    apply (div_le_iff₀ (pow_pos (by linarith only [hVl]) 3)).mpr
    have h₁ := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hVl 3
    have h₂ := pow_le_pow_left₀ (abs_nonneg B) hB' 2
    rw [sq_abs] at h₂
    linarith only [h₁,h₂]
  have h3 : |V^3-1|≤15*δ := by
    rw [show V^3-1=(V-1)*(V^2+V+1) by ring,abs_mul,
      abs_of_nonneg (by nlinarith only [hVl,sq_nonneg V] : 0≤V^2+V+1)]
    have hs : V^2+V+1≤5 := by
      nlinarith only [pow_le_pow_left₀ (by linarith only [hVl]) hVu 2,hVu]
    exact (mul_le_mul hV hs (by nlinarith only [hVl,sq_nonneg V]) (by positivity)).trans_eq (by ring)
  have he : shape v*V^3=B^2 := div_mul_cancel₀ _ (pow_ne_zero _ (by linarith only [hVl]))
  refine ⟨hVl,?_⟩
  change |A^2-shape v|≤_
  rw [show A^2-shape v=(A^2-B^2)+shape v*(V^3-1) by rw [mul_sub,he]; ring]
  apply (abs_add_le ..).trans
  rw [abs_mul]
  linarith only [hdiff,mul_le_mul hc h3 (abs_nonneg _) (by norm_num),hd₀]

#print axioms shape_stability
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape

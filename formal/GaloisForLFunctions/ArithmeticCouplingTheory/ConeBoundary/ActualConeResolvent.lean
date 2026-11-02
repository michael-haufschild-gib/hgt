import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.SplineResidueDecay
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.TwoClockResolvent
import GaloisForLFunctions.SquareRootThreshold.LagRateBoundsTheDeBruijnNewmanHeatTime

/-!
# The actual two-clock boundary resolvent

Mixed differences turn bounded natural-cone coupling into bounded mixed
moments of the actual spline residues. Averaging the two clock parameters
before summing the geometric series gives a first-order resolvent bounded
uniformly in its center and radial distance whenever maximal width is positive.
-/

open Complex Finset Filter Topology
open Zeta23
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.SquareRootThreshold
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
open ConeCoupling

lemma summable_mixedResidue_moment (a b : ℝ) (m n : ℕ) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      mixedResidue a b ρ*mult a ρ^m*mult b ρ^n := by
  have hh := (((summable_mult_pow a b (m+1) (n+1)).sub
    (summable_mult_pow a b (m+1) n)).sub (summable_mult_pow a b m (n+1))).add
    (summable_mult_pow a b m n)
  refine hh.congr fun ρ => ?_
  simp only [mixedResidue,pow_succ]
  ring

/-- Mixed second differences of bounded cone coupling bound every residue moment. -/
lemma norm_mixedResidue_moment_le_of_coneBound {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {M : ℝ} (hM : ∀ m n : ℕ,
      ‖coupling zetaKernel (primeElt hp^m) (primeElt hq^n)‖ ≤ M) (m n : ℕ) :
    ‖∑' ρ : zetaZeroConfig.carrier, mixedResidue (Real.log p) (Real.log q) ρ*
      mult (Real.log p) ρ^m*mult (Real.log q) ρ^n‖ ≤ 4*M := by
  have hM' (a b : ℕ) :
      ‖coupling zetaKernel (primeElt hp^(-(a:ℤ))) (primeElt hq^(-(b:ℤ)))‖ ≤ M := by
    rw [zpow_neg,zpow_neg,zpow_natCast,zpow_natCast,
      norm_coupling_inv_inv isHermKernel_zetaKernel]
    exact hM a b
  have hsC (a b : ℕ) : Summable fun ρ : zetaZeroConfig.carrier =>
      (mult (Real.log p) ρ^a-1)*(mult (Real.log q) ρ^b-1)*wt ρ := by
    have hh := (((summable_mult_pow (Real.log p) (Real.log q) a b).sub
      (summable_mult_pow (Real.log p) (Real.log q) a 0)).sub
      (summable_mult_pow (Real.log p) (Real.log q) 0 b)).add
      (summable_mult_pow (Real.log p) (Real.log q) 0 0)
    refine hh.congr fun ρ => ?_
    simp only [pow_zero]
    ring
  have he : (∑' ρ : zetaZeroConfig.carrier, mixedResidue (Real.log p) (Real.log q) ρ*
      mult (Real.log p) ρ^m*mult (Real.log q) ρ^n) =
      coupling zetaKernel (primeElt hp^(-((m+1:ℕ):ℤ))) (primeElt hq^(-((n+1:ℕ):ℤ))) -
      coupling zetaKernel (primeElt hp^(-((m+1:ℕ):ℤ))) (primeElt hq^(-(n:ℤ))) -
      coupling zetaKernel (primeElt hp^(-(m:ℤ))) (primeElt hq^(-((n+1:ℕ):ℤ))) +
      coupling zetaKernel (primeElt hp^(-(m:ℤ))) (primeElt hq^(-(n:ℤ))) := by
    rw [coupling_negCone,coupling_negCone,coupling_negCone,coupling_negCone,
      ← ((((hsC (m+1) (n+1)).hasSum.sub (hsC (m+1) n).hasSum).sub
        (hsC m (n+1)).hasSum).add (hsC m n).hasSum).tsum_eq]
    apply tsum_congr
    intro ρ
    simp only [mixedResidue,pow_succ]
    ring
  rw [he]
  calc
    _ ≤ _ := norm_sub_sub_add_le _ _ _ _
    _ ≤ M+M+M+M := add_le_add (add_le_add (add_le_add (hM' _ _) (hM' _ _))
      (hM' _ _)) (hM' _ _)
    _ = _ := by ring

/-- The averaged exponential denominator centered above the maximal width. -/
def boundaryClock (a b γ s : ℝ) (ρ : zetaZeroConfig.carrier) : ℂ :=
  (Complex.exp ((a:ℂ)*((ρ:ℂ)-1/2-(zetaZeroWidth+s:ℝ)-(γ:ℂ)*I))+
   Complex.exp ((b:ℂ)*((ρ:ℂ)-1/2-(zetaZeroWidth+s:ℝ)-(γ:ℂ)*I)))/2

def boundaryParameter (a γ s : ℝ) : ℂ :=
  Complex.exp (-((a:ℂ)*((zetaZeroWidth+s:ℝ)+(γ:ℂ)*I)))/2

lemma boundaryClock_eq (a b γ s : ℝ) (ρ : zetaZeroConfig.carrier) :
    boundaryClock a b γ s ρ =
      boundaryParameter a γ s*mult a ρ+boundaryParameter b γ s*mult b ρ := by
  unfold boundaryClock boundaryParameter mult
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div,← Complex.exp_add,← Complex.exp_add,← add_div]
  congr 2 <;> ring

lemma norm_boundaryParameter (a γ s : ℝ) :
    ‖boundaryParameter a γ s‖ = Real.exp (-a*(zetaZeroWidth+s))/2 := by
  rw [boundaryParameter,norm_div,Complex.norm_two,Complex.norm_exp]
  congr 2
  simp only [Complex.neg_re,Complex.add_re,Complex.ofReal_re,
    Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  ring

lemma norm_boundaryClock_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (γ s : ℝ) (ρ : zetaZeroConfig.carrier) :
    ‖boundaryClock a b γ s ρ‖ ≤ (Real.exp (-a*s)+Real.exp (-b*s))/2 := by
  have hwidth : (ρ:ℂ).re-1/2 ≤ zetaZeroWidth :=
    (le_abs_self _).trans (abs_re_sub_half_le_zetaZeroWidth ρ.2)
  have hbound (c : ℝ) (hc : 0 ≤ c) :
      ‖boundaryParameter c γ s*mult c ρ‖ ≤ Real.exp (-c*s)/2 := by
    rw [norm_mul,norm_boundaryParameter,norm_mult,div_mul_eq_mul_div,← Real.exp_add]
    apply div_le_div_of_nonneg_right _ zero_le_two
    exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hwidth hc])
  rw [boundaryClock_eq]
  exact (norm_add_le _ _).trans ((add_le_add (hbound a ha) (hbound b hb)).trans_eq (by ring))

lemma norm_boundaryClock_inverse_le {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s) (γ : ℝ) (ρ : zetaZeroConfig.carrier) :
    ‖(1-boundaryClock a b γ s ρ)⁻¹‖ ≤
      1/(1-(Real.exp (-a*s)+Real.exp (-b*s))/2) := by
  have hea : Real.exp (-a*s) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos ha hs])
  have heb : Real.exp (-b*s) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos hb hs])
  have hden : 0 < 1-(Real.exp (-a*s)+Real.exp (-b*s))/2 := by linarith only [hea,heb]
  have hh := norm_sub_norm_le (1:ℂ) (boundaryClock a b γ s ρ)
  rw [norm_one] at hh
  have hlow : 1-(Real.exp (-a*s)+Real.exp (-b*s))/2 ≤ ‖1-boundaryClock a b γ s ρ‖ := by
    linarith only [hh,norm_boundaryClock_le ha.le hb.le γ s ρ]
  rw [norm_inv,← one_div]
  exact div_le_div_of_nonneg_left zero_le_one hden hlow

lemma summable_boundary_resolvent {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s) (γ : ℝ) :
    Summable fun ρ : zetaZeroConfig.carrier => mixedResidue a b ρ/(1-boundaryClock a b γ s ρ) := by
  refine Summable.of_norm_bounded ((summable_norm_mixedResidue ha.le hb.le).mul_right
    (1/(1-(Real.exp (-a*s)+Real.exp (-b*s))/2))) fun ρ => ?_
  rw [div_eq_mul_inv,norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_boundaryClock_inverse_le ha hb hs γ ρ) (norm_nonneg _)

/-- Linear radial damping controls the entire resolvent tail. -/
lemma exists_boundaryClock_inverse_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ γ s : ℝ, 0 < s → s ≤ 1 →
      ∀ ρ : zetaZeroConfig.carrier, ‖(1-boundaryClock a b γ s ρ)⁻¹‖ ≤ K/s := by
  let c := 1-(Real.exp (-a)+Real.exp (-b))/2
  have hea : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
  have heb : Real.exp (-b) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hb)
  have hc : 0 < c := by dsimp only [c]; linarith only [hea,heb]
  refine ⟨1/c,one_div_pos.mpr hc,?_⟩
  intro γ s hs hs1 ρ
  have hA := mul_one_sub_exp_le (ℓ := a) hs.le hs1
  have hB := mul_one_sub_exp_le (ℓ := b) hs.le hs1
  have hden : s*c ≤ 1-(Real.exp (-a*s)+Real.exp (-b*s))/2 := by
    simp only [neg_mul] at hA hB ⊢
    dsimp only [c]
    nlinarith only [hA,hB]
  calc
    _ ≤ 1/(1-(Real.exp (-a*s)+Real.exp (-b*s))/2) :=
      norm_boundaryClock_inverse_le ha hb hs γ ρ
    _ ≤ 1/(s*c) := div_le_div_of_nonneg_left zero_le_one (mul_pos hs hc) hden
    _ = (1/c)/s := by ring

/-- Positive width and bounded natural-cone coupling give a uniformly bounded
first-order resolvent, for every ordinate center and every positive inward radius. -/
theorem exists_uniform_boundary_resolvent_bound {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0 < zetaZeroWidth)
    (hcone : ∃ M : ℝ, ∀ m n : ℕ,
      ‖coupling zetaKernel (primeElt hp^m) (primeElt hq^n)‖ ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ γ s : ℝ, 0 < s →
      ‖∑' ρ : zetaZeroConfig.carrier,
        mixedResidue (Real.log p) (Real.log q) ρ/
          (1-boundaryClock (Real.log p) (Real.log q) γ s ρ)‖ ≤ B := by
  obtain ⟨M,hM⟩ := hcone
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 0)
  have ha : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  let R := (Real.exp (-Real.log p*zetaZeroWidth)+Real.exp (-Real.log q*zetaZeroWidth))/2
  have hR : R < 1 := by
    have hp' : Real.exp (-Real.log p*zetaZeroWidth) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos ha hD])
    have hq' : Real.exp (-Real.log q*zetaZeroWidth) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos hb hD])
    dsimp only [R]
    linarith only [hp',hq']
  have hden : 0 < 1-R := sub_pos.mpr hR
  refine ⟨4*M/(1-R),div_nonneg (mul_nonneg (by norm_num) hM0) hden.le,?_⟩
  intro γ s hs
  let x := boundaryParameter (Real.log p) γ s
  let y := boundaryParameter (Real.log q) γ s
  have hxy : ‖x‖+‖y‖ ≤ R := by
    dsimp only [x,y,R]
    rw [norm_boundaryParameter,norm_boundaryParameter]
    have hp' := Real.exp_le_exp.mpr (show -Real.log p*(zetaZeroWidth+s) ≤ -Real.log p*zetaZeroWidth by
      nlinarith only [mul_nonneg ha.le hs.le])
    have hq' := Real.exp_le_exp.mpr (show -Real.log q*(zetaZeroWidth+s) ≤ -Real.log q*zetaZeroWidth by
      nlinarith only [mul_nonneg hb.le hs.le])
    linarith only [hp',hq']
  let r := (Real.exp (-Real.log p*s)+Real.exp (-Real.log q*s))/2
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hr : r < 1 := by
    have hp' : Real.exp (-Real.log p*s) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos ha hs])
    have hq' : Real.exp (-Real.log q*s) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos hb hs])
    dsimp only [r]
    linarith only [hp',hq']
  have hbound := norm_tsum_clock_resolvent_le (summable_norm_mixedResidue ha.le hb.le)
    (summable_mixedResidue_moment (Real.log p) (Real.log q))
    (norm_mixedResidue_moment_le_of_coneBound hp hq hM)
    x y (hxy.trans_lt hR) hr0 hr (fun ρ => by
      change ‖boundaryParameter (Real.log p) γ s*mult (Real.log p) ρ+
        boundaryParameter (Real.log q) γ s*mult (Real.log q) ρ‖ ≤ r
      rw [← boundaryClock_eq]
      exact norm_boundaryClock_le ha.le hb.le γ s ρ)
  simp only [x,y,← boundaryClock_eq] at hbound
  exact hbound.trans (div_le_div_of_nonneg_left (by positivity) hden
    (sub_le_sub_left hxy 1))

#print axioms norm_mixedResidue_moment_le_of_coneBound
#print axioms exists_boundaryClock_inverse_bound
#print axioms exists_uniform_boundary_resolvent_bound
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary

import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Transference
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.LinearFlowAffineCharacterWindow

/-! # Simultaneous error bounds for rectangular winding boxes -/

open Finset
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
open KleinbockMargulis
noncomputable section
variable {n : ℕ}

/-- The sides may differ or vanish. More than q grid points guarantee
a nonzero frequency perpendicular to the approximate numerator modulo q. -/
theorem rectangular_frequency {q : ℕ} (hq : 0<q) (p : Fin n→ℤ) (s : Fin n→ℕ)
    (hsize : q < ∏ i, (s i+1)) :
    ∃ a : Fin n→ℤ, a≠0 ∧ (∀ i, |a i|≤(s i:ℤ)) ∧ (q:ℤ) ∣ dotInt a p := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  let B := (i : Fin n) → Fin (s i+1)
  have hc : Fintype.card (ZMod q)<Fintype.card B := by
    simpa only [B,ZMod.card,Fintype.card_pi,Fintype.card_fin] using hsize
  obtain ⟨x,y,hne,hxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun x : B => ((∑ i, (x i:ℤ)*p i : ℤ) : ZMod q)) hc
  refine ⟨fun i => (x i:ℤ)-(y i:ℤ),?_,?_,?_⟩
  · intro he
    apply hne
    funext i
    have hh := congrFun he i
    simp only [Pi.zero_apply,sub_eq_zero] at hh
    exact Fin.ext (by exact_mod_cast hh)
  · intro i
    have hx := (x i).isLt
    have hy := (y i).isLt
    change |(x i:ℤ)-(y i:ℤ)|≤(s i:ℤ)
    rw [abs_le]
    constructor <;> omega
  have he : dotInt (fun i => (x i:ℤ)-(y i:ℤ)) p=(∑ i, (x i:ℤ)*p i)-∑ i, (y i:ℤ)*p i := by
    simp only [dotInt,sub_mul,sum_sub_distrib]
  rw [he,←ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,hxy,sub_self]

/-- A single constant controls every simultaneous approximation and every
integer rectangle of multiplicative height at most its denominator. -/
theorem rectangular_error_bound {y : Fin n→ℝ} (hy : ¬VWMA y) {δ : ℝ} (hδ : 0<δ) :
    ∃ C≥(1:ℝ), ∀ (q : ℕ), 0<q → ∀ (p : Fin n→ℤ) (s : Fin n→ℕ),
      (∏ i, max 1 (s i)) ≤ q → q < ∏ i, (s i+1) →
      (q:ℝ)^(-δ) ≤ C*∑ i, (s i:ℝ)*|(q:ℝ)*y i-(p i:ℝ)| := by
  obtain ⟨C,hC,hdual⟩ := exists_global_affineMultiplicativeLinearForm_lower hy hδ
  refine ⟨C,hC,?_⟩
  intro q hq p s hheight hsize
  obtain ⟨a,ha,hs,c,hc⟩ := rectangular_frequency hq p s hsize
  have h₁ (i : Fin n) : |(a i:ℝ)|≤(s i:ℝ) := by exact_mod_cast hs i
  have hheight' : PiPlus a≤(q:ℝ) := by
    have hh : (∏ i, max (1:ℝ) (s i:ℝ))≤(q:ℝ) := by exact_mod_cast hheight
    refine (prod_le_prod (fun i _ => zero_le_one.trans (le_max_right |(a i:ℝ)| 1))
      (fun i _ => max_le ((h₁ i).trans (le_max_right _ _)) (le_max_left _ _))).trans hh
  have hdot : (∑ i, (a i:ℝ)*(p i:ℝ))=(q:ℝ)*(c:ℝ) := by
    exact_mod_cast (show (∑ i, a i*p i)=(q:ℤ)*c from hc)
  have herr : (q:ℝ)*(dotProd a y+((-c:ℤ):ℝ))=∑ i, (a i:ℝ)*((q:ℝ)*y i-(p i:ℝ)) := by
    rw [Int.cast_neg,←sub_eq_add_neg,mul_sub,←hdot,dotProd,mul_sum,←sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  have hnorm : (q:ℝ)*|dotProd a y+((-c:ℤ):ℝ)|≤∑ i, (s i:ℝ)*|(q:ℝ)*y i-(p i:ℝ)| := by
    rw [show (q:ℝ)*|dotProd a y+((-c:ℤ):ℝ)|=|∑ i, (a i:ℝ)*((q:ℝ)*y i-(p i:ℝ))| by
      simp only [←herr,abs_mul,abs_of_nonneg (Nat.cast_nonneg q : 0≤(q:ℝ))]]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro i _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (h₁ i) (abs_nonneg _)
  have hleft : (q:ℝ)^(-δ) ≤ PiPlus a^(-δ) :=
    Real.rpow_le_rpow_of_nonpos (PiPlus_pos a) hheight' (neg_nonpos.mpr hδ.le)
  calc (q:ℝ)^(-δ) ≤ C*|dotProd a y+((-c:ℤ):ℝ)| *PiPlus a :=
         hleft.trans (hdual (-c) a (Or.inr ha))
       _ ≤ C*|dotProd a y+((-c:ℤ):ℝ)| *(q:ℝ) := mul_le_mul_of_nonneg_left hheight'
         (mul_nonneg (zero_le_one.trans hC) (abs_nonneg _))
       _ = C*((q:ℝ)*|dotProd a y+((-c:ℤ):ℝ)|) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (zero_le_one.trans hC)

#print axioms rectangular_error_bound
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted

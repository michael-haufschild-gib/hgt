import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Subperiods.Midpoint.GapLifts

/-! # The primitive relative winding of an empty-circuit excursion -/

open Set
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint
open EmptyVisitFlux
noncomputable section
variable {I : Type*} {w : I → ℝ}

/-- In a strict semicircle the differences of the integer phase lifts
are unique. Changing the scalar phase shifts only their common offset. -/
theorem lifted_difference_unique {t r c b : ℝ} {p q : I → ℤ} (hr : r<1/2)
    (hp : lifted w t r c p) (hq : lifted w t r b q) (i j : I) :
    p i-p j=q i-q j := by
  let k := (p i-p j)-(q i-q j)
  have hh : (-1:ℝ)<(k:ℝ) ∧ (k:ℝ)<1 := by
    dsimp only [k]
    push_cast
    constructor <;> linarith only [(hp i).1,(hp i).2,(hp j).1,(hp j).2,
      (hq i).1,(hq i).2,(hq j).1,(hq j).2,hr]
  have hZ : (-1:ℤ)<k ∧ k<1 := by exact_mod_cast hh
  exact sub_eq_zero.mp (show k=0 by omega)

/-- If all relative windings share a divisor d, interpolation by one dth
of the elapsed time keeps all lifted residuals within the original arc. -/
theorem interpolate_divisor [Fintype I] [Nonempty I] {u v r c b : ℝ} {p q : I → ℤ}
    (hp : lifted w u r c p) (hq : lifted w v r b q) (i₀ : I) {d : ℕ} (hd : 0<d)
    (hdiv : ∀ i, (d:ℤ)∣(q i-p i)-(q i₀-p i₀)) :
    flow w (u+(v-u)/d) ∈ enclosingUnitArc r := by
  have hd₀ : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hd₁ : (1:ℝ)≤d := by exact_mod_cast (show 1≤d by omega)
  have hr : 0≤r := (hp i₀).1.trans (hp i₀).2
  let f := (1:ℝ)/d
  have hf₀ : 0≤f := (one_div_pos.mpr hd₀).le
  have hf₁ : f≤1 := (div_le_one hd₀).mpr hd₁
  let n := q i₀-p i₀
  choose y hy using hdiv
  apply (arc_iff_lifted hr).mpr
  refine ⟨(1-f)*c+f*b+f*(n:ℝ),fun i => p i+y i,fun i => ?_⟩
  let E := u*w i-c-(p i:ℝ)
  let F := v*w i-b-(q i:ℝ)
  have hE : E∈Icc (0:ℝ) r := hp i
  have hF : F∈Icc (0:ℝ) r := hq i
  have hwind : (q i:ℝ)-(p i:ℝ)-(n:ℝ)=(d:ℝ)*(y i:ℝ) := by exact_mod_cast hy i
  have hmean : (u+(v-u)/(d:ℝ))*w i-((1-f)*c+f*b+f*(n:ℝ))-((p i+y i:ℤ):ℝ)=(1-f)*E+f*F := by
    dsimp only [E,F,f]
    push_cast
    field_simp [hd₀.ne']
    linarith only [hwind]
  rw [hmean]
  have hn := sub_nonneg.mpr hf₁
  refine ⟨add_nonneg (mul_nonneg hn hE.1) (mul_nonneg hf₀ hF.1),?_⟩
  calc
    (1-f)*E+f*F ≤ (1-f)*r+f*r := add_le_add (mul_le_mul_of_nonneg_left hE.2 hn)
      (mul_le_mul_of_nonneg_left hF.2 hf₀)
    _ = r := by ring

/-- Every bounded component between scalar visits carries a primitive
integer winding modulo the common phase, at the original approximation error. -/
theorem primitive_gap_winding [Fintype I] [Nonempty I] {u v r c b : ℝ} (huv : u<v)
    {p q : I → ℤ} (hp : lifted w u r c p) (hq : lifted w v r b q)
    (hgap : ∀ t∈Ioo u v, flow w t∉enclosingUnitArc r) (i₀ : I) {d : ℕ} (hd : 2≤d) :
    ¬∀ i, (d:ℤ)∣(q i-p i)-(q i₀-p i₀) := by
  intro h
  have hd₀ : 0<d := by omega
  have hd₁ : (1:ℝ)<d := by exact_mod_cast (show 1<d by omega)
  have hpos := sub_pos.mpr huv
  have hlt := div_lt_self hpos hd₁
  exact hgap _ ⟨lt_add_of_pos_right _ (div_pos hpos (Nat.cast_pos.mpr hd₀)),
    by linarith only [hlt]⟩ (interpolate_divisor hp hq i₀ hd₀ h)

#print axioms lifted_difference_unique
#print axioms primitive_gap_winding
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint

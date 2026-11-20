import GaloisForLFunctions.ExceptionalLayerTheory.LevelWidthsOfAReflectedHadamardPair

/-!
# Inferring a reflected pair from two horizontal level edges

For a pair of poles at ±δ of common residue m, the first abscissa at
which a negative level −L is reached satisfies x²+2mx/L=δ². Two level
edges determine both parameters. At high levels the boundary distance
from the pole also determines m and the finite part m/(2δ).
-/

noncomputable section
open Filter Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Left edge of the negative level in the interior half of a reflected pair. -/
def reflectedLevelEdge (m δ L : ℝ) : ℝ := Real.sqrt (δ^2+(m/L)^2)-m/L

private theorem edge_balance (m δ L : ℝ) :
    (reflectedLevelEdge m δ L)^2+2*(m/L)*reflectedLevelEdge m δ L=δ^2 := by
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg δ) (sq_nonneg (m/L)))
  unfold reflectedLevelEdge
  linarith only [hs]

private theorem edge_inside {m δ L : ℝ} (hm : 0 < m) (hd : 0 < δ) (hL : 0 < L) :
    0 < reflectedLevelEdge m δ L ∧ reflectedLevelEdge m δ L < δ := by
  have hc := div_pos hm hL
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg δ) (sq_nonneg (m/L)))
  have hp : m/L < Real.sqrt (δ^2+(m/L)^2) := by
    apply (sq_lt_sq₀ hc.le (Real.sqrt_nonneg _)).mp
    rw [hs]
    linarith only [sq_pos_of_pos hd]
  have hx : 0 < reflectedLevelEdge m δ L := sub_pos.mpr hp
  refine ⟨hx,(sq_lt_sq₀ hx.le hd.le).mp ?_⟩
  linarith only [edge_balance m δ L,mul_pos hc hx]

/-- A level occurs somewhere on the vertical line at x precisely when
x lies strictly past its edge. -/
theorem reflected_level_past_edge {m δ L x : ℝ} (hm : 0 < m) (hL : 0 < L)
    (hx : 0 < x) (hδ : x < δ) :
    (∃ y, m*reflectedPairReading x δ y < -L) ↔ reflectedLevelEdge m δ L < x := by
  have hp := div_pos hL hm
  have hreading (y : ℝ) : m*reflectedPairReading x δ y < -L ↔
      reflectedPairReading x δ y < -(L/m) := by
    rw [←neg_div,lt_div_iff₀ hm,mul_comm m]
  simp only [hreading,reflected_pair_level_onset hp hx hδ]
  let q := reflectedLevelEdge m δ L
  have hq : 0 < q := (edge_inside hm (hx.trans hδ) hL).1
  have hb := edge_balance m δ L
  have he : L*(δ^2-x^2)-2*m*x = (q-x)*(L*(q+x)+2*m) := by
    change q^2+2*(m/L)*q=δ^2 at hb
    rw [←hb]
    field_simp [hL.ne'] <;> ring
  have hfactor : 0 < L*(q+x)+2*m := by positivity
  have hscaled : L/m*(δ^2-x^2)<2*x ↔ L*(δ^2-x^2)-2*m*x<0 := by
    rw [div_mul_eq_mul_div,div_lt_iff₀ hm]
    constructor <;> intro h <;> linarith only [h]
  rw [hscaled,he,mul_neg_iff_of_pos_right hfactor,sub_neg]

/-- Two distinct levels give the common pole residue and squared pole
offset by rational operations on their two edge positions. -/
theorem reflected_two_edges_invert {m δ A B : ℝ} (hm : 0 < m) (hd : 0 < δ)
    (hA : 0 < A) (hAB : A < B) :
    let x := reflectedLevelEdge m δ A
    let y := reflectedLevelEdge m δ B
    x < y ∧ y/B < x/A ∧
      (y^2-x^2)/(2*(x/A-y/B))=m ∧ x^2+2*m*(x/A)=δ^2 := by
  let x := reflectedLevelEdge m δ A
  let y := reflectedLevelEdge m δ B
  have hB := hA.trans hAB
  have hx : 0 < x := (edge_inside hm hd hA).1
  have hy : 0 < y := (edge_inside hm hd hB).1
  have h₁ : x^2+2*(m/A)*x=δ^2 := edge_balance ..
  have h₂ : y^2+2*(m/B)*y=δ^2 := edge_balance ..
  have hratio : m/B<m/A := (div_lt_div_iff₀ hB hA).mpr (mul_lt_mul_of_pos_left hAB hm)
  have hxy : x < y := by
    by_contra! h
    have hsq := (sq_le_sq₀ hy.le hx.le).mpr h
    have hh := (mul_lt_mul_of_pos_right hratio hy).trans_le
      (mul_le_mul_of_nonneg_left h (div_pos hm hA).le)
    linarith only [h₁,h₂,hsq,hh]
  have hdiff : y^2-x^2=2*m*(x/A-y/B) := by
    linear_combination h₂-h₁
  have horder : 0 < 2*m*(x/A-y/B) := hdiff ▸ sub_pos.mpr ((sq_lt_sq₀ hx.le hy.le).mpr hxy)
  have hgap := (mul_pos_iff_of_pos_left (by positivity : 0 < 2*m)).mp horder
  refine ⟨hxy,sub_pos.mp hgap,(div_eq_iff (mul_pos (by norm_num) hgap).ne').mpr ?_,?_⟩
  · rw [hdiff]; ring
  · calc x^2+2*m*(x/A) = x^2+2*(m/A)*x := by ring
         _ = _ := h₁

private theorem edge_error {δ L : ℝ} (hd : 0 < δ) (hL : L≠0) (m : ℝ) :
    L*(m-L*(δ-reflectedLevelEdge m δ L)) =
      m^2/(Real.sqrt (δ^2+(m/L)^2)+δ) := by
  let s := Real.sqrt (δ^2+(m/L)^2)
  have hs : s^2=δ^2+(m/L)^2 := Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hn : 0 < s+δ := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hd
  change L*(m-L*(δ-(s-m/L)))=_
  apply (eq_div_iff hn.ne').mpr
  calc _ = L^2*(s^2-δ^2) := by field_simp [hL] <;> ring
       _ = _ := by rw [hs]; field_simp [hL] <;> ring

/-- At high levels the deficit is m/L−m²/(2δL²)+o(L⁻²).
The second coefficient measures the influence of the reflected pole. -/
theorem reflected_level_edge_asymptotics {δ : ℝ} (hd : 0 < δ) (m : ℝ) :
    Tendsto (fun L : ℝ => L*(δ-reflectedLevelEdge m δ L)) atTop (𝓝 m) ∧
    Tendsto (fun L : ℝ => L*(m-L*(δ-reflectedLevelEdge m δ L))) atTop (𝓝 (m^2/(2*δ))) := by
  have hc := (tendsto_const_nhds (x:=m)).div_atTop (tendsto_id (α:=ℝ))
  have hs := (tendsto_const_nhds (x:=δ^2)).add (hc.pow 2)
  have hs' := (Real.continuous_sqrt.tendsto _).comp hs
  simp only [zero_pow (by decide : 2≠0),add_zero,Real.sqrt_sq hd.le] at hs'
  have hden := hs'.add_const δ
  have h₂ := (tendsto_const_nhds (x:=m^2)).div hden (add_pos hd hd).ne'
  rw [←two_mul] at h₂
  have he : Tendsto (fun L : ℝ => L*(m-L*(δ-reflectedLevelEdge m δ L))) atTop
      (𝓝 (m^2/(2*δ))) := by
    apply h₂.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    exact (edge_error hd hL.ne' m).symm
  have hsmall := he.div_atTop (tendsto_id (α:=ℝ))
  have h₁ := (tendsto_const_nhds (x:=m)).sub hsmall
  rw [sub_zero] at h₁
  refine ⟨h₁.congr' ?_,he⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  change m-L*(m-L*(δ-reflectedLevelEdge m δ L))/L=_
  field_simp [hL.ne'] <;> ring

#print axioms reflected_level_past_edge
#print axioms reflected_two_edges_invert
#print axioms reflected_level_edge_asymptotics
end GaloisForLFunctions.ExceptionalLayerTheory

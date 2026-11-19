import GaloisForLFunctions.HTGeometry.CoppoKerrPhaseGeometry

/-!
# Paired critical bubbles and the Kerr threshold

In dimension four the four-component interaction of Fan–Giaretto–Soave,
Theorem 1.8, is multilinear. If two pairs have equal self-couplings,
synchronization forces equality within each pair. The remaining squared
amplitudes solve a two-by-two linear system. Its determinant also controls
the loss of a lower bound in the two-site Kerr energy.
-/

noncomputable section
open Filter Topology
namespace HTGeometry

/-- Positive four-component bubble amplitudes with paired self-couplings.
Each equation has been multiplied by its own amplitude. -/
def pairedBubbleAmplitudes (A B b x y z w : ℝ) : Prop :=
  0<x ∧ 0<y ∧ 0<z ∧ 0<w ∧
    A*x^4 = x^2+b*(x*y*z*w) ∧ A*y^4 = y^2+b*(x*y*z*w) ∧
    B*z^4 = z^2+b*(x*y*z*w) ∧ B*w^4 = w^2+b*(x*y*z*w)

private theorem lock_pair {A C x y : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hx : 0 < x) (hy : 0 < y) (h₁ : A*x^4 = x^2+C) (h₂ : A*y^4 = y^2+C) : x=y := by
  have hpos : 0 < A*x^2-1 := by
    by_contra! h
    have hle := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) h
    nlinarith only [h₁,hle,hC]
  have he : (x^2-y^2)*(A*(x^2+y^2)-1) = 0 := by linarith only [h₁,h₂]
  have hstrict : 0 < A*(x^2+y^2)-1 := by linarith only [hpos,mul_pos hA (sq_pos_of_pos hy)]
  have hxy := (mul_eq_zero.mp he).resolve_right hstrict.ne'
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp (sub_eq_zero.mp hxy)).resolve_right (by linarith only [hx,hy])

private theorem paired_reduction {A B b x y z w : ℝ} (hA : 0 < A) (hB : 0 < B) (hb : 0 < b) :
    pairedBubbleAmplitudes A B b x y z w ↔
      0<x ∧ 0<z ∧ y=x ∧ w=z ∧ A*x^2-b*z^2=1 ∧ B*z^2-b*x^2=1 := by
  constructor
  · rintro ⟨hx,hy,hz,hw,h₁,h₂,h₃,h₄⟩
    have hC : 0 < b*(x*y*z*w) := by positivity
    obtain rfl := lock_pair hA hC hx hy h₁ h₂
    obtain rfl := lock_pair hB hC hz hw h₃ h₄
    refine ⟨hx,hz,rfl,rfl,?_,?_⟩
    · apply mul_left_cancel₀ (sq_pos_of_pos hx).ne'
      linarith only [h₁]
    · apply mul_left_cancel₀ (sq_pos_of_pos hz).ne'
      linarith only [h₃]
  · rintro ⟨hx,hz,rfl,rfl,h₁,h₂⟩
    have hA' := congrArg (fun t : ℝ => x^2*t) h₁
    have hB' := congrArg (fun t : ℝ => z^2*t) h₂
    refine ⟨hx,hx,hz,hz,?_,?_,?_,?_⟩ <;> linarith only [hA',hB']

/-- All four amplitudes are determined explicitly. Beyond the geometric
mean coupling the same equations exclude every positive synchronized state. -/
theorem paired_bubble_classification {A B b : ℝ} (hA : 0<A) (hB : 0<B) (hb : 0<b)
    (x y z w : ℝ) :
    pairedBubbleAmplitudes A B b x y z w ↔
      b^2 < A*B ∧ x=Real.sqrt ((B+b)/(A*B-b^2)) ∧ y=x ∧
        z=Real.sqrt ((A+b)/(A*B-b^2)) ∧ w=z := by
  rw [paired_reduction hA hB hb]
  constructor
  · rintro ⟨hx,hz,rfl,rfl,h₁,h₂⟩
    have ex : (A*B-b^2)*x^2=B+b := by
      linarith only [congrArg (B*·) h₁,congrArg (b*·) h₂]
    have ez : (A*B-b^2)*z^2=A+b := by
      linarith only [congrArg (b*·) h₁,congrArg (A*·) h₂]
    have hd : 0 < A*B-b^2 := pos_of_mul_pos_left (ex ▸ add_pos hB hb) (sq_nonneg x)
    refine ⟨sub_pos.mp hd,?_,rfl,?_,rfl⟩
    · rw [← ex,mul_div_cancel_left₀ _ hd.ne',Real.sqrt_sq hx.le]
    · rw [← ez,mul_div_cancel_left₀ _ hd.ne',Real.sqrt_sq hz.le]
  · rintro ⟨h,rfl,rfl,rfl,rfl⟩
    have hd := sub_pos.mpr h
    have hL := div_pos (add_pos hB hb) hd
    have hR := div_pos (add_pos hA hb) hd
    refine ⟨Real.sqrt_pos.mpr hL,Real.sqrt_pos.mpr hR,rfl,rfl,?_,?_⟩ <;>
      rw [Real.sq_sqrt hL.le,Real.sq_sqrt hR.le] <;> field_simp [hd.ne'] <;> ring

/-- Crossing the threshold from below forces both squared amplitudes
to diverge at a simple pole with explicit residues in the determinant. -/
theorem paired_bubble_residues {A B b x y z w : ℝ} (hA : 0<A) (hB : 0<B) (hb : 0<b)
    (h : pairedBubbleAmplitudes A B b x y z w) :
    (A*B-b^2)*x^2=B+b ∧ (A*B-b^2)*z^2=A+b ∧ (B+b)*z^2=(A+b)*x^2 := by
  obtain ⟨hc,hx,_,hz,_⟩ := (paired_bubble_classification hA hB hb x y z w).mp h
  have hd := sub_pos.mpr hc
  rw [hx,hz,Real.sq_sqrt (div_pos (add_pos hB hb) hd).le,
    Real.sq_sqrt (div_pos (add_pos hA hb) hd).le]
  constructor
  · field_simp
  constructor <;> field_simp

/-- Approaching the geometric mean from below, the two squared amplitudes
have simple poles as functions of the coupling. Their residues need not
agree when the self-couplings differ. -/
theorem paired_bubble_threshold_limits {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    let s := Real.sqrt (A*B)
    Tendsto (fun b => (s-b)*((B+b)/(A*B-b^2))) (𝓝[<] s) (𝓝 ((B+s)/(2*s))) ∧
    Tendsto (fun b => (s-b)*((A+b)/(A*B-b^2))) (𝓝[<] s) (𝓝 ((A+s)/(2*s))) := by
  intro s
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos hA hB)
  have hs₂ : s^2=A*B := Real.sq_sqrt (mul_pos hA hB).le
  have pole (C : ℝ) : Tendsto (fun b => (s-b)*((C+b)/(A*B-b^2))) (𝓝[<] s) (𝓝 ((C+s)/(2*s))) := by
    have h : ContinuousAt (fun b : ℝ => (C+b)/(s+b)) s :=
      (continuousAt_const.add continuousAt_id).div (continuousAt_const.add continuousAt_id) (by positivity)
    have ht := h.continuousWithinAt (s:=Set.Iio s)
    change Tendsto (fun b : ℝ => (C+b)/(s+b)) (𝓝[<] s) (𝓝 ((C+s)/(s+s))) at ht
    rw [←two_mul] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (lt_mem_nhds hs)] with b hl hb
    change b<s at hl
    have hden : A*B-b^2=(s-b)*(s+b) := by rw [←hs₂]; ring
    rw [hden]
    field_simp [(sub_pos.mpr hl).ne',(add_pos hs hb).ne']
  exact ⟨pole B,pole A⟩

#print axioms paired_bubble_threshold_limits

/-- At negative interaction parameter the two-site Kerr energy is bounded
below precisely before the same competitive threshold. At the endpoint
the quartic term vanishes on the diagonal and the mass term drives escape. -/
theorem kerr_competitive_threshold (mass b : ℝ) (hm : 0 < mass) (hb : 0 ≤ b) :
    (∃ C : ℝ, ∀ x y : ℝ, C ≤ coppoKerrEnergy mass (-b) x y) ↔ b < 1 := by
  constructor
  · rintro ⟨C,hC⟩
    by_contra! hc
    let t := Real.sqrt ((|C|+1)/(4*mass))
    have ht : t^2=(|C|+1)/(4*mass) := Real.sq_sqrt (by positivity)
    have he : coppoKerrEnergy mass (-b) t t = 2*(1-b)*t^4-4*mass*t^2 := by
      unfold coppoKerrEnergy
      ring
    have h := hC t t
    rw [he,ht,mul_div_cancel₀ _ (by positivity)] at h
    have hn := mul_nonpos_of_nonpos_of_nonneg (show 2*(1-b) ≤ 0 by linarith only [hc]) (by positivity : 0≤t^4)
    linarith only [h,hn,neg_abs_le C]
  · intro h
    refine ⟨-2*mass^2/(1-b),fun x y => ?_⟩
    have hd := sub_pos.mpr h
    have id : coppoKerrEnergy mass (-b) x y + 2*mass^2/(1-b) =
        (1-b)/2*(x^2+y^2-2*mass/(1-b))^2 + (1+b)/2*(x^2-y^2)^2 := by
      dsimp only [coppoKerrEnergy]
      field_simp [hd.ne']
      ring
    have h₀ : 0 ≤ (1-b)/2*(x^2+y^2-2*mass/(1-b))^2+(1+b)/2*(x^2-y^2)^2 := by positivity
    linarith only [id,h₀]

#print axioms paired_bubble_classification
#print axioms paired_bubble_residues
#print axioms kerr_competitive_threshold
end HTGeometry

import GaloisForLFunctions.HTGeometry.DispersivePDE.TheEnergyGapOfFourUnequalCriticalBubbles
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The geometric-mean threshold for four unequal modes

Homogenizing the common load of a synchronized quartet gives four
positive quadratic roots on a compact interval. A single sign change
constructs the positive solution below the geometric mean. The limiting
endpoint supplies the escape ray at and above threshold.
-/

noncomputable section
namespace HTGeometry.CriticalQuartet

private def branch (a z : ℝ) : ℝ :=
  (z+Real.sqrt (z^2+4*a*(1-z)^2))/(2*a)

private theorem quad {a : ℝ} (ha : 0<a) (z : ℝ) :
    a*(branch a z)^2 = z*branch a z+(1-z)^2 := by
  have rad : 0≤z^2+4*a*(1-z)^2 := by positivity
  have lin : 2*a*branch a z-z=Real.sqrt (z^2+4*a*(1-z)^2) := by
    unfold branch
    rw [mul_comm (2*a),div_mul_cancel₀ _ (by positivity),add_sub_cancel_left]
  have sq : (2*a*branch a z-z)^2=z^2+4*a*(1-z)^2 := by rw [lin,Real.sq_sqrt rad]
  have final : a*(a*(branch a z)^2-z*branch a z-(1-z)^2)=0 := by linarith only [sq]
  linarith only [(mul_eq_zero.mp final).resolve_left ha.ne']

private theorem branch_pos {a : ℝ} (ha : 0<a) {z : ℝ} (hz : 0≤z) : 0<branch a z := by
  rcases hz.eq_or_lt with h|h
  · rw [←h]
    unfold branch
    positivity
  · exact div_pos (add_pos_of_pos_of_nonneg h (Real.sqrt_nonneg _)) (by positivity)

theorem product_mul (x y : Fin 4 → ℝ) :
    product (fun i => x i*y i)=product x*product y := by unfold product; ring

private theorem product_sq (x : Fin 4 → ℝ) :
    product (fun i => (x i)^2)=(product x)^2 := by unfold product; ring

theorem product_fourth (x : Fin 4 → ℝ) :
    product (fun i => (x i)^4)=(product x)^4 := by unfold product; ring

private theorem product_lt {x y : Fin 4 → ℝ} (hx : ∀ i, 0<x i) (hlt : ∀ i, x i<y i) :
    product x<product y := by
  have step {a b c d : ℝ} (hab : a<b) (hcd : c<d) (hc : 0<c) (hb : 0<b) : a*c < b*d :=
    (mul_lt_mul_of_pos_right hab hc).trans (mul_lt_mul_of_pos_left hcd hb)
  have hy i := (hx i).trans (hlt i)
  exact step (step (step (hlt 0) (hlt 1) (hx 1) (hy 0)) (hlt 2) (hx 2)
    (mul_pos (hy 0) (hy 1))) (hlt 3) (hx 3) (mul_pos (mul_pos (hy 0) (hy 1)) (hy 2))

private theorem threshold_of_solution {μ x : Fin 4 → ℝ} {m b : ℝ} (hm : 0 < m) (hb : 0<b)
    (h : Synchronized μ m b x) : b^4<product μ := by
  have hp := product_pos h.1
  have cost := mul_pos hb hp
  have lt (i : Fin 4) : b*product x < μ i*x i^4 := by
    rw [h.2 i]
    exact lt_add_of_pos_left _ (mul_pos hm (sq_pos_of_pos (h.1 i)))
  have p := product_lt (fun _ => cost) lt
  rw [product_mul μ (fun i => x i^4),product_fourth x] at p
  change b*product x*(b*product x)*(b*product x)*(b*product x)<_ at p
  have q : b^4*(product x)^4 < product μ*(product x)^4 := by linarith only [p]
  exact lt_of_mul_lt_mul_right q (pow_nonneg hp.le 4)

private theorem endpoint {μ : Fin 4 → ℝ} (hμ : ∀ i, 0<μ i) :
    product μ*(product (fun i => branch (μ i) 0))^2=1 := by
  have site i : μ i*(branch (μ i) 0)^2=1 := by simpa using quad (hμ i) 0
  rw [←product_sq,←product_mul]
  simp [product,site]

/-- Four arbitrary self-couplings admit exactly one positive synchronized
state precisely below their geometric mean. -/
theorem unique_positive_iff {μ : Fin 4 → ℝ} {m b : ℝ} (hμ : ∀ i, 0<μ i)
    (hm : 0 < m) (hb : 0<b) : (∃! x, Synchronized μ m b x) ↔ b^4<product μ := by
  constructor
  · rintro ⟨x,hx,_⟩
    exact threshold_of_solution hm hb hx
  · intro sub
    let v (z : ℝ) (i : Fin 4) := branch (μ i) z
    let f (z : ℝ) := b^2*product (v z)-(1-z)^4
    have cont : Continuous f := by
      dsimp [f,v,product,branch]
      fun_prop
    have ep : product μ*(product (v 0))^2=1 := endpoint hμ
    have hprod := product_pos hμ
    have gap : b^2*product (v 0)<1 := by
      have id : (b^2*product (v 0))^2*product μ=b^4 := by
        calc _ = b^4*(product μ*(product (v 0))^2) := by ring
             _ = _ := by rw [ep,mul_one]
      have small : (b^2*product (v 0))^2<1 := by
        have comp : (b^2*product (v 0))^2*product μ < 1*product μ := by rwa [id,one_mul]
        exact lt_of_mul_lt_mul_right comp hprod.le
      by_contra! hn
      have hle := mul_self_le_mul_self (by norm_num : (0:ℝ)≤1) hn
      linarith only [small,hle]
    have lo : f 0<0 := by simpa [f] using sub_neg.mpr gap
    have hi : 0<f 1 := by
      have p : 0<product (v 1) := product_pos fun i => branch_pos (hμ i) zero_le_one
      simpa [f] using mul_pos (sq_pos_of_pos hb) p
    obtain ⟨z,hz,hf⟩ := intermediate_value_Icc (show (0:ℝ)≤1 by norm_num) cont.continuousOn ⟨lo.le,hi.le⟩
    have hz0 : 0<z := hz.1.lt_of_ne (fun eq => by subst z; exact lo.ne hf)
    have load : b^2*product (v z)=(1-z)^4 := sub_eq_zero.mp hf
    let x (i : Fin 4) := Real.sqrt ((m/z)*v z i)
    have pos i : 0<x i := Real.sqrt_pos.mpr (mul_pos (div_pos hm hz0) (branch_pos (hμ i) hz0.le))
    have xx i : (x i)^2=(m/z)*v z i := Real.sq_sqrt (mul_pos (div_pos hm hz0) (branch_pos (hμ i) hz0.le)).le
    have xp : (product x)^2=(m/z)^4*product (v z) := by
      rw [←product_sq]
      unfold product
      simp only [xx]
      ring
    have p : b*product x=(m/z)^2*(1-z)^2 := by
      apply (sq_eq_sq₀ (mul_pos hb (product_pos pos)).le (mul_nonneg (sq_nonneg _) (sq_nonneg _))).mp
      rw [mul_pow,xp]
      calc _ = (m/z)^4*(b^2*product (v z)) := by ring
           _ = _ := by rw [load]; ring
    have hsol : Synchronized μ m b x := by
      refine ⟨pos,fun i => ?_⟩
      rw [show x i^4=(x i^2)^2 by ring,xx,p,mul_pow]
      have id := quad (hμ i) z
      change μ i*(v z i)^2=z*v z i+(1-z)^2 at id
      have q := congrArg (fun t : ℝ => (m/z)^2*t) id
      have cancel : (m/z)^2*z=m*(m/z) := by field_simp [hz0.ne']
      have lin := congrArg (fun t : ℝ => t*v z i) cancel
      change (m/z)^2*(μ i*(v z i)^2)=(m/z)^2*(z*v z i+(1-z)^2) at q
      change (m/z)^2*z*v z i=m*(m/z)*v z i at lin
      linarith only [q,lin]
    exact ⟨x,hsol,fun y hy => synchronized_unique hm hb hy hsol⟩

/-- The same threshold characterizes boundedness below. At the critical
coupling a direction with zero quartic cost still has negative quadratic
energy diverging to minus infinity. -/
theorem energy_bounded_below_iff {μ : Fin 4 → ℝ} {m b : ℝ} (hμ : ∀ i, 0<μ i)
    (hm : 0 < m) (hb : 0<b) : (∃ C : ℝ, ∀ y, C ≤ energy μ m b y) ↔ b^4<product μ := by
  constructor
  · rintro ⟨C,hC⟩
    by_contra! h
    let r (i : Fin 4) := Real.sqrt (branch (μ i) 0)
    have hr (i : Fin 4) : 0<r i := Real.sqrt_pos.mpr (branch_pos (hμ i) le_rfl)
    have site (i : Fin 4) : μ i*r i^4=1 := by
      rw [show r i^4=(r i^2)^2 by ring,show r i^2=branch (μ i) 0 from Real.sq_sqrt (branch_pos (hμ i) le_rfl).le]
      simpa using quad (hμ i) 0
    have prod : product μ*(product r)^4=1 := by
      rw [←product_fourth,←product_mul]
      simp [product,site]
    have nonpos : 1≤b*product r := by
      by_contra! hn
      have low := pow_lt_one₀ (mul_pos hb (product_pos hr)).le hn (show (4:ℕ)≠0 by decide)
      rw [mul_pow] at low
      have lower := mul_le_mul_of_nonneg_right h (pow_nonneg (product_pos hr).le 4)
      rw [prod] at lower
      exact low.not_ge lower
    let U := total (fun i => r i^2)
    have hU : 0<U := (sq_pos_of_pos (hr 0)).trans_le (le_total (fun i => sq_nonneg (r i)) 0)
    let t := Real.sqrt ((|C|+1)/(2*m*U))
    have ht : t^2=(|C|+1)/(2*m*U) := Real.sq_sqrt (by positivity)
    have expansion : energy μ m b (fun i => t*r i) = (4*(1-b*product r))*t^4-2*m*U*t^2 := by
      unfold energy
      have mass : product (fun i => t*r i)=t^4*product r := by unfold product; ring
      rw [mass]
      dsimp only [U,total]
      linear_combination t^4*(site 0)+t^4*(site 1)+t^4*(site 2)+t^4*(site 3)
    have esc := hC (fun i => t*r i)
    have quart := mul_nonpos_of_nonpos_of_nonneg
      (show 4*(1-b*product r)≤0 by linarith only [nonpos]) (by positivity : 0≤t^4)
    rw [expansion,ht,mul_div_cancel₀ _ (mul_pos (mul_pos (by norm_num : (0:ℝ)<2) hm) hU).ne'] at esc
    linarith only [esc,quart,neg_abs_le C]
  · intro hs
    obtain ⟨x,hx,_⟩ := (unique_positive_iff hμ hm hb).mpr hs
    exact ⟨energy μ m b x,global_min hm hb hx⟩

#print axioms unique_positive_iff
#print axioms energy_bounded_below_iff
end HTGeometry.CriticalQuartet

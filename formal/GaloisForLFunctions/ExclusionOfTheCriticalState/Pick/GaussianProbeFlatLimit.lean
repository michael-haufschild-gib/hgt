import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.GaussianLimitOfProbeDephasing
import GaloisForLFunctions.HilbertMetric.Kernels.GaussianCollocation
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exact short-time volume of a Gaussian jump probe

For two independent ordered grids of n momenta, the Gaussian cross
determinant opens to order n(n−1)/2. Its leading coefficient is the
product of the two Vandermonde determinants divided by the Taylor
factorials and by the appropriate power of four. Inverse Vandermonde
rows kill precisely the lower Taylor moments of each exponential.
-/

noncomputable section
open Matrix Finset Filter
open scoped Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.GaussianVolume
variable {n : ℕ}

def order (n : ℕ) : ℕ := ∑ k : Fin n, k.val

theorem twice_order (n : ℕ) : order n*2=n*(n-1) := by
  rw [order,Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n]
  exact sum_range_id_mul_two n

def determinant {n : ℕ} (x y : Fin n → ℝ) (t : ℝ) :=
  (Matrix.of fun i j => Real.exp (-t*gapCost (x i) (y j))).det

private def kernel (x y : Fin n → ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.exp ((x i*y j)*t)

private def taylor (k : ℕ) (z : ℝ) := ∑ m ∈ range (k+1), z^m/(m.factorial:ℝ)

private theorem remainder_limit (k : ℕ) (c : ℝ) :
    Tendsto (fun t : ℝ => (Real.exp (c*t)-taylor k (c*t))/t^k) (𝓝[≠] 0) (𝓝 0) := by
  have h := (Real.exp_sub_sum_range_succ_isLittleO_pow k).tendsto_div_nhds_zero
  have hc : Tendsto (fun t : ℝ => c*t) (𝓝[≠] 0) (𝓝 0) :=
    (continuous_const.mul continuous_id).tendsto' _ _ (mul_zero c) |>.mono_left nhdsWithin_le_nhds
  have hp := ((h.comp hc).mul_const (c^k))
  rw [zero_mul] at hp
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin (s:=({0}:Set ℝ)ᶜ) (a:=0)] with t ht
  have ht' : t≠0 := ht
  change (Real.exp (c*t)-taylor k (c*t))/(c*t)^k*c^k=_
  by_cases cz : c=0
  · subst c
    have e : taylor k 0=1 := by
      unfold taylor
      rw [sum_eq_single 0]
      · simp
      · intro m _ hm
        simp [zero_pow hm]
      · simp
    simp [e]
  · rw [mul_pow]
    field_simp [ht',cz]

private theorem vdet_pos (x : Fin n ↪o ℝ) : 0<(vandermonde (x : Fin n → ℝ)).det := by
  rw [det_vandermonde]
  exact prod_pos fun i _ => prod_pos fun j h => sub_pos.mpr (x.strictMono (mem_Ioi.mp h))

private def inverseRows (x : Fin n ↪o ℝ) := (vandermonde (x : Fin n → ℝ))⁻¹

private theorem moment (x : Fin n ↪o ℝ) (k p : Fin n) :
    ∑ i, inverseRows x k i*(x i)^p.val=if k=p then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M k p)
    (nonsing_inv_mul (vandermonde (x : Fin n → ℝ)) (vdet_pos x).ne'.isUnit)
  simpa only [Matrix.mul_apply,vandermonde_apply,Matrix.one_apply,inverseRows] using h

private theorem truncated_row (x : Fin n ↪o ℝ) (k : Fin n) (y t : ℝ) :
    ∑ i, inverseRows x k i*taylor k.val ((x i*y)*t)=(y*t)^k.val/(k.val.factorial:ℝ) := by
  simp only [taylor,mul_sum]
  rw [sum_comm]
  have term (m : ℕ) (hm : m∈range (k.val+1)) :
      ∑ i, inverseRows x k i*((x i*y*t)^m/(m.factorial:ℝ)) =
        if m=k.val then (y*t)^k.val/(k.val.factorial:ℝ) else 0 := by
    let p : Fin n := ⟨m,by have h := mem_range.mp hm; omega⟩
    have factor : (∑ i, inverseRows x k i*((x i*y*t)^m/(m.factorial:ℝ))) =
        (∑ i, inverseRows x k i*(x i)^p.val)*((y*t)^m/(m.factorial:ℝ)) := by
      rw [sum_mul]
      exact sum_congr rfl fun i _ => by simp only [p,mul_pow]; ring
    rw [factor,moment]
    by_cases he : m=k.val
    · subst m
      simp [p]
    · have ne : k≠p := fun e => he (congrArg Fin.val e).symm
      simp [he,ne]
  rw [sum_congr rfl term]
  simp

private def normalizedRow (x : Fin n ↪o ℝ) (y : Fin n → ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (inverseRows x*kernel x y t) i j/t^i.val

private def leading (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun k j => (y j)^k.val/(k.val.factorial:ℝ)

private theorem row_limit (x : Fin n ↪o ℝ) (y : Fin n → ℝ) :
    Tendsto (normalizedRow x y) (𝓝[≠] 0) (𝓝 (leading y)) := by
  apply tendsto_pi_nhds.mpr
  intro k
  apply tendsto_pi_nhds.mpr
  intro j
  have h := tendsto_finsetSum univ (fun i _ => (remainder_limit k.val (x i*y j)).const_mul (inverseRows x k i))
  simp only [mul_zero,sum_const_zero] at h
  have ha := h.add_const ((y j)^k.val/(k.val.factorial:ℝ))
  rw [zero_add] at ha
  apply ha.congr'
  filter_upwards [self_mem_nhdsWithin (s:=({0}:Set ℝ)ᶜ) (a:=0)] with t ht
  have hn : t^k.val≠0 := pow_ne_zero _ (show t≠0 from ht)
  change (∑ i, inverseRows x k i*((Real.exp (x i*y j*t)-taylor k.val (x i*y j*t))/t^k.val))+
      (y j)^k.val/(k.val.factorial:ℝ)=_
  have term (i : Fin n) : inverseRows x k i*((Real.exp (x i*y j*t)-taylor k.val (x i*y j*t))/t^k.val) =
      (inverseRows x k i*Real.exp (x i*y j*t)-inverseRows x k i*taylor k.val (x i*y j*t))/t^k.val := by ring
  have cancel : ((y j*t)^k.val/(k.val.factorial:ℝ))/t^k.val=(y j)^k.val/(k.val.factorial:ℝ) := by
    rw [mul_pow]
    field_simp [hn]
  let E := ∑ i, inverseRows x k i*Real.exp (x i*y j*t)
  let B := ∑ i, inverseRows x k i*taylor k.val (x i*y j*t)
  have delta : (∑ i, inverseRows x k i*((Real.exp (x i*y j*t)-taylor k.val (x i*y j*t))/t^k.val))=
      (E-B)/t^k.val := by
    calc
      _ = ∑ i : Fin n, (inverseRows x k i*Real.exp (x i*y j*t)-inverseRows x k i*taylor k.val (x i*y j*t))/t^k.val :=
        sum_congr rfl fun i _ => term i
      _ = _ := by rw [← sum_div,sum_sub_distrib]
  have approx : B=(y j*t)^k.val/(k.val.factorial:ℝ) := truncated_row x k (y j) t
  change (∑ i, inverseRows x k i*((Real.exp (x i*y j*t)-taylor k.val (x i*y j*t))/t^k.val))+
    (y j)^k.val/(k.val.factorial:ℝ)=E/t^k.val
  rw [delta,approx,sub_div,cancel,sub_add_cancel]

private theorem leading_det (y : Fin n → ℝ) :
    (leading y).det=(∏ k : Fin n, (k.val.factorial:ℝ)⁻¹)*(vandermonde y).det := by
  have he : leading y=Matrix.of fun i j => (i.val.factorial:ℝ)⁻¹*(vandermonde y).transpose i j := by
    ext i j
    simp only [leading,Matrix.of_apply,transpose_apply,vandermonde_apply,div_eq_inv_mul]
  rw [he,det_mul_column,det_transpose]

/-- Leading coefficient of an exponential sampling determinant on two
independent grids. Only the first grid needs distinct nodes in the proof. -/
theorem exponential_flat_limit (x : Fin n ↪o ℝ) (y : Fin n → ℝ) :
    Tendsto (fun t : ℝ => (kernel x y t).det/t^(order n)) (𝓝[≠] 0)
      (𝓝 ((vandermonde (x : Fin n → ℝ)).det*((∏ k : Fin n, (k.val.factorial:ℝ)⁻¹)*(vandermonde y).det))) := by
  have h := ((continuous_id.matrix_det.tendsto (leading y)).comp (row_limit x y)).const_mul
    (vandermonde (x : Fin n → ℝ)).det
  simp only [id_eq,Function.comp_apply,leading_det] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin (s:=({0}:Set ℝ)ᶜ) (a:=0)] with t ht
  have he : normalizedRow x y t=Matrix.of fun i j => (t^i.val)⁻¹*(inverseRows x*kernel x y t) i j := by
    ext i j
    simp only [normalizedRow,of_apply,div_eq_inv_mul]
  change (vandermonde (x : Fin n → ℝ)).det*(normalizedRow x y t).det=_
  rw [he,det_mul_column,prod_inv_distrib,prod_pow_eq_pow_sum,det_mul,inverseRows,det_nonsing_inv,Ring.inverse_eq_inv]
  unfold order
  field_simp [(vdet_pos x).ne',show t≠0 from ht]

/-- The exact Gaussian volume coefficient. The second Vandermonde absorbs
the factor 4 to the power n(n−1)/2 in the Gaussian exponent. -/
def coefficient (x y : Fin n → ℝ) :=
  (vandermonde x).det*((∏ k : Fin n, (k.val.factorial:ℝ)⁻¹)*(vandermonde (fun j => y j/4)).det)

private def envelope (x : Fin n → ℝ) (t : ℝ) := ∏ i, Real.exp (-t*(x i)^2/8)

private theorem split_kernel (x y : Fin n → ℝ) (t : ℝ) :
    determinant x y t=envelope x t*(envelope y t*(kernel x (fun j => y j/4) t).det) := by
  let M := kernel x (fun j => y j/4) t
  have he : (Matrix.of fun i j => Real.exp (-t*gapCost (x i) (y j)))=
      Matrix.of fun i j => Real.exp (-t*(x i)^2/8)*(Matrix.of fun u v => Real.exp (-t*(y v)^2/8)*M u v) i j := by
    ext i j
    simp only [of_apply,M,kernel,← Real.exp_add,gapCost]
    congr 1
    ring
  rw [determinant,he,det_mul_column,det_mul_row]
  rfl

/-- Exact order and coefficient of the physical Gaussian jump determinant
at time zero. Both grids may be irregular and need not coincide. -/
theorem gaussian_flat_limit (x y : Fin n ↪o ℝ) :
    0<coefficient x y ∧
    Tendsto (fun t : ℝ => determinant x y t/t^(order n)) (𝓝[≠] 0) (𝓝 (coefficient x y)) := by
  let v : Fin n ↪o ℝ := OrderEmbedding.ofStrictMono (fun j => y j/4)
    (fun _ _ h => div_lt_div_of_pos_right (y.strictMono h) (by norm_num))
  refine ⟨mul_pos (vdet_pos x) (mul_pos (prod_pos fun k _ => by positivity) (vdet_pos v)),?_⟩
  have env (a : Fin n → ℝ) : Tendsto (envelope a) (𝓝[≠] 0) (𝓝 1) := by
    have hc : Continuous (envelope a) := by unfold envelope; fun_prop
    exact hc.tendsto' _ _ (by simp [envelope]) |>.mono_left nhdsWithin_le_nhds
  have h := (env x).mul ((env y).mul (exponential_flat_limit x v))
  simp only [one_mul] at h
  apply h.congr' (Eventually.of_forall ?_)
  intro t
  change envelope x t*(envelope y t*((kernel x (fun j => y j/4) t).det/t^(order n)))=
    determinant x y t/t^(order n)
  rw [split_kernel]
  ring

#print axioms twice_order
#print axioms exponential_flat_limit
#print axioms gaussian_flat_limit
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.GaussianVolume

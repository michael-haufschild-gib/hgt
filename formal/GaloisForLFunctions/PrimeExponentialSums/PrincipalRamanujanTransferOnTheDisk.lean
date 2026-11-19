import GaloisForLFunctions.RHTower.MobiusRamanujanTwoLevelConservation
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The principal prime-power transfer on the unit disk

The two divisibility layers of the Ramanujan sum give Gou's local
transfer factor by summing two geometric tails. A positive quadratic
identity determines its unique extremizer at every radius and controls
the loss away from that point.
-/

noncomputable section
open Finset RHTower
namespace GaloisForLFunctions.PrimeExponentialSums.PrincipalRamanujan

/-- Principal Möbius factor, before multiplication by the conductor monomial. -/
def fraction (p : ℝ) (z : ℂ) : ℂ := (p : ℂ)*(1-z)/(p-z)

/-- Transfer for conductor p^(k+1). -/
def transfer (p : ℝ) (k : ℕ) (z : ℂ) : ℂ := -(z^k)*fraction p z

private theorem geom_tail (x : ℂ) (hx : ‖x‖<1) (a : ℕ) :
    HasSum (fun j : ℕ => if a≤j then x^j else 0) (x^a*(1-x)⁻¹) := by
  apply (hasSum_nat_add_iff' a).mp
  have he : ∑ j ∈ range a, (if a≤j then x^j else 0)=0 :=
    sum_eq_zero (fun j hj => if_neg (not_le_of_gt (mem_range.mp hj)))
  rw [he,sub_zero]
  apply ((hasSum_geometric_of_norm_lt_one hx).mul_left (x^a)).congr_fun
  intro n
  rw [if_pos (by omega),pow_add,mul_comm]

/-- Sum of the actual Ramanujan coefficients of p^j, weighted by (z/p)^j.
This identity holds on the full open disk of convergence. -/
theorem hasSum_transfer (p : Nat.Primes) (k : ℕ) {z : ℂ} (hz : ‖z‖<(p.val : ℝ)) :
    HasSum (fun j : ℕ => cglRamanujanAdditiveSum (mobiusPrimePowerModulus p k) (p.val^j) *
      (z/p.val)^j) (transfer p.val k z) := by
  let P : ℂ := p.val
  let x : ℂ := z/P
  have hp : 0<(p.val : ℝ) := Nat.cast_pos.mpr p.property.pos
  have hP : P≠0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hx : ‖x‖<1 := by simpa only [x,P,norm_div,Complex.norm_natCast,div_lt_one hp] using hz
  have ht (a : ℕ) := (geom_tail x hx a).mul_left (P^a)
  have hmul (a : ℕ) : P^a*x^a=z^a := by
    rw [← mul_pow,show P*x = P*z/P from (mul_div_assoc P z P).symm,mul_div_cancel_left₀ _ hP]
  have hn : P-z ≠ 0 := by
    intro he
    rw [← sub_eq_zero.mp he] at hz
    simpa only [P,Complex.norm_natCast,lt_self_iff_false] using hz
  have hden : (1-x)⁻¹ = P/(P-z) := by
    unfold x
    field_simp
  have value : P^(k+1)*(x^(k+1)*(1-x)⁻¹) - P^k*(x^k*(1-x)⁻¹) = transfer p.val k z := by
    rw [← mul_assoc,← mul_assoc,hmul,hmul,hden]
    unfold transfer fraction
    change z^(k+1)*(P/(P-z)) - z^k*(P/(P-z)) = -(z^k)*(P*(1-z)/(P-z))
    rw [pow_succ]
    ring
  rw [← value]
  apply ((ht (k+1)).sub (ht k)).congr_fun
  intro j
  have hl := ramanujanPrimePower_two_divisibility_layers p k (p.val^j)
  rw [Nat.cast_pow] at hl
  rw [hl]
  simp only [Nat.pow_dvd_pow_iff_le_right p.property.one_lt]
  by_cases h₁ : k+1≤j <;> by_cases h₀ : k≤j <;>
    simp only [h₁,h₀,ite_true,ite_false,sub_mul,zero_mul,mul_zero,P,x,Nat.cast_pow]

private theorem real_sub_ne {p r : ℝ} (h : r<p) {z : ℂ} (hz : ‖z‖≤r) (hp : 0≤p) :
    (p : ℂ)-z≠0 := by
  rintro he
  have h' := sub_eq_zero.mp he
  rw [← h',Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp] at hz
  linarith only [hz,h]

/-- The loss from the sharp edge value splits exactly into angular and
radial terms. Both coefficients are positive when 0<r≤1<p. -/
theorem deficit_identity (p r : ℝ) (z : ℂ) :
    r*((1+r)^2 * ‖(p : ℂ)-z‖^2 - (p+r)^2 * ‖(1 : ℂ)-z‖^2) =
      (p-1)*(p-r^2)*‖z+(r : ℂ)‖^2 + (p-1)*(p+r)*(1+r)*(r^2-‖z‖^2) := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im]
  ring

private theorem squared_bounds (p r : ℝ) (z : ℂ) (hp : 1<p) (hr : 0<r) (hr₁ : r≤1)
    (hz : ‖z‖≤r) : (p+r)^2 * ‖(1 : ℂ)-z‖^2 ≤ (1+r)^2 * ‖(p : ℂ)-z‖^2 := by
  have hpr : 0<p-r^2 := by nlinarith only [hp,hr,hr₁,mul_nonneg hr.le (sub_nonneg.mpr hr₁)]
  have hrz := sub_nonneg.mpr (sq_le_sq₀ (norm_nonneg _) hr.le |>.2 hz)
  have h := deficit_identity p r z
  have h₁ := mul_nonneg (mul_nonneg (sub_nonneg.mpr hp.le) hpr.le) (sq_nonneg ‖z+(r:ℂ)‖)
  have h₂ := mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hp.le)
    (by linarith only [hp,hr] : 0≤p+r)) (by linarith only [hr] : 0≤1+r)) hrz
  apply sub_nonneg.mp
  apply (mul_nonneg_iff_of_pos_left hr).mp
  rw [h]
  exact add_nonneg h₁ h₂

theorem fraction_bound {p r : ℝ} (hp : 1<p) (hr : 0<r) (hr₁ : r≤1) {z : ℂ} (hz : ‖z‖≤r) :
    ‖fraction p z‖ ≤ p*(1+r)/(p+r) := by
  have hn := real_sub_ne (hr₁.trans_lt hp) hz (zero_lt_one.trans hp).le
  have h₁ := squared_bounds p r z hp hr hr₁ hz
  have h₂ : (p+r)*‖(1:ℂ)-z‖ ≤ (1+r)*‖(p:ℂ)-z‖ := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simpa only [mul_pow] using h₁
  rw [fraction,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (zero_lt_one.trans hp),div_le_div_iff₀ (norm_pos_iff.mpr hn) (by linarith only [hp,hr])]
  calc
    _ = p*((p+r)*‖(1:ℂ)-z‖) := by ring
    _ ≤ p*((1+r)*‖(p:ℂ)-z‖) := mul_le_mul_of_nonneg_left h₂ (zero_lt_one.trans hp).le
    _ = _ := by ring

theorem fraction_at_edge {p r : ℝ} (hp : 1<p) (hr : 0≤r) :
    fraction p (-(r : ℂ)) = ((p*(1+r)/(p+r) : ℝ) : ℂ) := by
  unfold fraction
  push_cast
  ring

/-- At positive radius, equality forces z=-r. Thus cancellation has a
unique worst phase, including on the unit circle. -/
theorem fraction_eq_iff {p r : ℝ} (hp : 1<p) (hr : 0<r) (hr₁ : r≤1) {z : ℂ} (hz : ‖z‖≤r) :
    ‖fraction p z‖ = p*(1+r)/(p+r) ↔ z= -(r : ℂ) := by
  constructor
  · intro he
    have hpp := zero_lt_one.trans hp
    have hn := real_sub_ne (hr₁.trans_lt hp) hz hpp.le
    rw [fraction,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpp,
      div_eq_div_iff (norm_ne_zero_iff.mpr hn) (by positivity : p+r≠0)] at he
    have h₀ : (p+r)*‖(1:ℂ)-z‖=(1+r)*‖(p:ℂ)-z‖ := by
      apply mul_left_cancel₀ hpp.ne'
      linear_combination he
    have hs := congrArg (fun a : ℝ => a^2) h₀
    simp only [mul_pow] at hs
    have h := deficit_identity p r z
    rw [hs,sub_self,mul_zero] at h
    have hpr : 0 < p-r^2 := by nlinarith only [hp,hr,hr₁,mul_nonneg hr.le (sub_nonneg.mpr hr₁)]
    have hrz := sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) hr.le).2 hz)
    have h₂ : 0≤(p-1)*(p+r)*(1+r)*(r^2-‖z‖^2) :=
      mul_nonneg (by positivity) hrz
    have hz₀ : ((p-1)*(p-r^2))*‖z+(r:ℂ)‖^2=0 :=
      le_antisymm (by linarith only [h,h₂]) (by positivity)
    have hz' := (mul_eq_zero.mp hz₀).resolve_left (mul_pos (sub_pos.mpr hp) hpr).ne'
    exact eq_neg_of_add_eq_zero_left (norm_eq_zero.mp (sq_eq_zero_iff.mp hz'))
  · rintro rfl
    rw [fraction_at_edge hp hr.le,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]

/-- Sharp bound with the conductor monomial, attained at the same negative
real point for every depth. -/
theorem transfer_bound {p r : ℝ} (hp : 1<p) (hr : 0<r) (hr₁ : r≤1) (k : ℕ)
    {z : ℂ} (hz : ‖z‖≤r) : ‖transfer p k z‖ ≤ r^k*(p*(1+r)/(p+r)) := by
  rw [transfer,norm_mul,norm_neg,norm_pow]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz k)
    (fraction_bound hp hr hr₁ hz) (norm_nonneg _) (pow_nonneg hr.le k)

theorem transfer_edge_iff {p r : ℝ} (hp : 1<p) (hr : 0<r) (hr₁ : r≤1) (k : ℕ)
    {z : ℂ} (hz : ‖z‖≤r) :
    ‖transfer p k z‖=r^k*(p*(1+r)/(p+r)) ↔ z= -(r : ℂ) := by
  rw [transfer,norm_mul,norm_neg,norm_pow]
  constructor
  · intro he
    apply (fraction_eq_iff hp hr hr₁ hz).1
    apply le_antisymm (fraction_bound hp hr hr₁ hz)
    by_contra! ht
    have h₀ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz k)
      (norm_nonneg (fraction p z))
    linarith only [he,h₀,mul_lt_mul_of_pos_left ht (pow_pos hr k)]
  · rintro rfl
    rw [fraction_at_edge hp hr.le,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hr,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]

end GaloisForLFunctions.PrimeExponentialSums.PrincipalRamanujan

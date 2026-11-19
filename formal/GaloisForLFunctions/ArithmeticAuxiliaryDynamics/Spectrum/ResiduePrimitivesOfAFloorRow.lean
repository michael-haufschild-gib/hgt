import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheHalfScaleOfTheRate

/-!
# The incomplete-period term of a balanced floor row

Discrete summation by parts, as in Pain (arXiv:2603.08959, §4), integrates
each centred sawtooth exactly. Its primitive is a quadratic in the last
residue. This gives a signed boundary correction on every window. On a
common period it vanishes and yields a reciprocal square-root floor on
the producer rate without a logarithm.
-/

noncomputable section
open Finset
open GaloisForLFunctions.ArithmeticKreinLangerTheory

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- Discrete quadratic primitive of minus the normalized centred residue. -/
def residuePrimitive (k n : ℕ) : ℝ :=
  ((n%k:ℕ):ℝ)*((k:ℝ)-((n%k:ℕ):ℝ))/(2*(k:ℝ))

/-- Signed incomplete-period correction from the letters of the row. -/
def floorRowPrimitive (c : ℕ →₀ ℤ) (n : ℕ) : ℝ :=
  ∑ k ∈ c.support, (c k:ℝ)*residuePrimitive k n

theorem residue_primitive_step {k : ℕ} (hk : 0 < k) (n : ℕ) :
    residuePrimitive k (n+1)-residuePrimitive k n = -(residue k n)/(k:ℝ) := by
  have hk₀ : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  have hr := Nat.mod_lt n hk
  have he : (n+1)%k = (n%k+1)%k := by rw [Nat.mod_add_mod]
  rw [residuePrimitive,residuePrimitive,residue,he]
  by_cases hs : n%k+1 < k
  · rw [Nat.mod_eq_of_lt hs,Nat.cast_succ]
    field_simp; ring
  · have hwrap : n%k+1 = k := by omega
    have hcast : ((n%k:ℕ):ℝ)+1 = (k:ℝ) := by exact_mod_cast hwrap
    rw [hwrap,Nat.mod_self,Nat.cast_zero,zero_mul,zero_div,zero_sub]
    rw [←hcast]
    have hr₀ : 0 < ((n%k:ℕ):ℝ)+1 := by positivity
    field_simp
    ring

/-- Centring the multiplicity at half its peak gives the exact first
difference of the residue primitive. -/
theorem floor_row_primitive_step {c : ℕ →₀ ℤ} (hc : c 0 = 0) (hb : IsBalanced c) (n : ℕ) :
    (stepWeight c n:ℝ)-(peak c:ℝ)/2 = floorRowPrimitive c (n+1)-floorRowPrimitive c n := by
  rw [stepWeight_eq_mean_add hc hb,add_sub_cancel_left,floorRowPrimitive,floorRowPrimitive,←sum_sub_distrib]
  apply sum_congr rfl
  intro k hk
  have hk₀ : 0 < k := Nat.pos_of_ne_zero (fun h => by subst k; exact Finsupp.mem_support_iff.mp hk hc)
  rw [←mul_sub,residue_primitive_step hk₀]
  ring

/-- A window has just two signed boundary terms, for every starting point
and length. -/
theorem floor_row_window_primitive {c : ℕ →₀ ℤ} (hc : c 0 = 0) (hb : IsBalanced c) (n L : ℕ) :
    (∑ j ∈ range L, (stepWeight c (n+j):ℝ)) - (L:ℝ)*(peak c:ℝ)/2 =
      floorRowPrimitive c (n+L)-floorRowPrimitive c n := by
  have hh := sum_congr (s₁ := range L) rfl fun i _ => floor_row_primitive_step hc hb (n+i)
  simp only [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul] at hh
  have ht := sum_range_sub (fun i => floorRowPrimitive c (n+i)) L
  simp only [Nat.add_zero,←Nat.add_assoc,sum_sub_distrib] at ht
  linarith only [hh,ht]

/-- The exact signed price of a low-rate row at two endpoints. -/
theorem IsProducer.residue_window_necessary {c : ℕ →₀ ℤ} {m B n : ℕ} (hP : IsProducer c m B)
    (hn : 1 ≤ n) (L : ℕ) :
    (L:ℝ)*((peak c:ℝ)/2-m) + floorRowPrimitive c (n+L)-floorRowPrimitive c n ≤
      ((n:ℝ)+L)^2*excess c m B := by
  have hh := hP.sum_sub_le_excess hn L
  rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul] at hh
  linarith only [hh,floor_row_window_primitive hP.zero hP.balanced n L]

private theorem primitive_period {c : ℕ →₀ ℤ} {L : ℕ} (hL : ∀ k ∈ c.support, k ∣ L) (n : ℕ) :
    floorRowPrimitive c (n+L) = floorRowPrimitive c n := by
  apply sum_congr rfl
  intro k hk
  simp only [residuePrimitive,Nat.add_mod,Nat.mod_eq_zero_of_dvd (hL k hk),Nat.add_zero,Nat.mod_mod]

/-- A common period bounds the normalized peak with no smoothing loss. -/
theorem IsProducer.peak_le_at_common_period {c : ℕ →₀ ℤ} {m B L : ℕ} (hP : IsProducer c m B)
    (hL : 1 ≤ L) (hdiv : ∀ k ∈ c.support, k ∣ L) :
    IsProducer.peakRatio c m ≤ 2+8*(L:ℝ)*rate c m B := by
  have hl : (1:ℝ) ≤ L := Nat.one_le_cast.mpr hL
  have hl₀ := zero_lt_one.trans_le hl
  have h := hP.residue_window_necessary (n:=1) le_rfl L
  rw [primitive_period hdiv,add_sub_cancel_right,Nat.cast_one] at h
  have he := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+L) (by linarith only [hl] : (1:ℝ)+L ≤ 2*L) 2)
    hP.excess_pos.le
  have hr := mul_le_mul_of_nonneg_left hP.excess_le (sq_nonneg (2*(L:ℝ)))
  rw [IsProducer.peakRatio,div_le_iff₀ hP.m_pos]
  apply (mul_le_mul_iff_right₀ hl₀).mp
  linarith only [h,he,hr]

/-- Every producer has rate at least a constant divided by the square root
of any positive common period of its support. -/
theorem common_period_half_floor :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ →₀ ℤ) (m B L : ℕ), IsProducer c m B → 1 ≤ L →
      (∀ k ∈ c.support, k ∣ L) → C/Real.sqrt L ≤ rate c m B := by
  obtain ⟨a,ha,ha₁,hlaw⟩ := exists_uncertainty_constant
  refine ⟨a/10,by positivity,fun c m B L hP hL hdiv => ?_⟩
  have hl : (1:ℝ) ≤ L := Nat.one_le_cast.mpr hL
  have hs := Real.one_le_sqrt.mpr hl
  have hs₀ := zero_lt_one.trans_le hs
  let e := rate c m B
  let y := e*Real.sqrt L
  have he : 0 < e := hP.rate_pos
  have hey : e ≤ y := le_mul_of_one_le_right he.le hs
  rw [div_le_iff₀ hs₀]
  by_contra! hsmall
  change y < a/10 at hsmall
  have hy : y ≤ 1 := by linarith only [hsmall,ha₁]
  have he₁ := hey.trans hy
  have hu := (hlaw c m B hP he₁).trans
    (mul_le_mul_of_nonneg_left (hP.peak_le_at_common_period hL hdiv) he.le)
  have hy₂ : y^2 = e^2*(L:ℝ) := by dsimp only [y]; rw [mul_pow,Real.sq_sqrt (zero_le_one.trans hl)]
  have hyy := mul_le_mul_of_nonneg_left hy (he.le.trans hey)
  change a ≤ e*(2+8*(L:ℝ)*e) at hu
  nlinarith only [hu,hyy,hy₂,hey,hsmall]

/-- The largest possible translation error of a single residue primitive is
its value at the translation length. Starting at zero attains equality. -/
theorem residue_primitive_translation {k : ℕ} (hk : 0 < k) (n L : ℕ) :
    |residuePrimitive k (n+L)-residuePrimitive k n| ≤ residuePrimitive k L := by
  let u := n%k
  let r := L%k
  have hu : u < k := Nat.mod_lt n hk
  have hr : r < k := Nat.mod_lt L hk
  have hk₀ : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  have hur : (n+L)%k = (u+r)%k := Nat.add_mod _ _ _
  simp only [residuePrimitive,hur,←sub_div,abs_div,abs_of_pos (mul_pos (by norm_num : (0:ℝ) < 2) hk₀)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  change |(((u+r)%k:ℕ):ℝ)*((k:ℝ)-(((u+r)%k:ℕ):ℝ))-(u:ℝ)*((k:ℝ)-u)| ≤ (r:ℝ)*((k:ℝ)-r)
  rw [abs_le]
  by_cases h : u+r < k
  · rw [Nat.mod_eq_of_lt h,Nat.cast_add]
    have hsum : (u:ℝ)+r ≤ k := by exact_mod_cast h.le
    constructor <;> nlinarith only [mul_nonneg (Nat.cast_nonneg r : 0 ≤ (r:ℝ))
      (sub_nonneg.mpr hsum), mul_nonneg (Nat.cast_nonneg u : 0 ≤ (u:ℝ)) (Nat.cast_nonneg r)]
  · have hh := le_of_not_gt h
    have he : (u+r)%k = u+r-k := by
      conv_lhs => rw [show u+r = (u+r-k)+k by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    rw [he,Nat.cast_sub hh,Nat.cast_add]
    have hsum : (k:ℝ) ≤ u+r := by exact_mod_cast hh
    have hkr := sub_nonneg.mpr (Nat.cast_le.mpr hr.le : (r:ℝ) ≤ k)
    have hku := sub_nonneg.mpr (Nat.cast_le.mpr hu.le : (u:ℝ) ≤ k)
    constructor <;> nlinarith only [mul_nonneg hkr (sub_nonneg.mpr hsum),mul_nonneg hku hkr]

/-- Absolute signed-letter cost of an incomplete window; it vanishes on
every common period of the active alphabet. -/
def incompletePeriodCost (c : ℕ →₀ ℤ) (L : ℕ) : ℝ :=
  ∑ k ∈ c.support, |(c k:ℝ)| * residuePrimitive k L

theorem floor_row_boundary_le {c : ℕ →₀ ℤ} (hc : c 0 = 0) (n L : ℕ) :
    |floorRowPrimitive c (n+L)-floorRowPrimitive c n| ≤ incompletePeriodCost c L := by
  rw [floorRowPrimitive,floorRowPrimitive,←sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  rw [←mul_sub,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  refine residue_primitive_translation (Nat.pos_of_ne_zero fun he => ?_) n L
  subst k
  exact Finsupp.mem_support_iff.mp hk hc

/-- A producer close to zero rate must have a large incomplete-period cost
at every sufficiently short length. This quantifies how far its active
letters must be from sharing a common period. -/
theorem short_windows_force_residue_cost :
    ∃ a : ℝ, 0 < a ∧ ∀ (c : ℕ →₀ ℤ) (m B L : ℕ), IsProducer c m B → 1 ≤ L →
      rate c m B ≤ a/8 → (L:ℝ)*(rate c m B)^2 ≤ a/32 →
      a*L*m ≤ 4*rate c m B*incompletePeriodCost c L := by
  obtain ⟨a,ha,ha₁,hlaw⟩ := exists_uncertainty_constant
  refine ⟨a,ha,fun c m B L hP hL he hlen => ?_⟩
  let e := rate c m B
  have he₀ : 0 < e := hP.rate_pos
  have hl : (1:ℝ) ≤ L := Nat.one_le_cast.mpr hL
  have hl₀ := zero_lt_one.trans_le hl
  have h := hP.residue_window_necessary (n:=1) le_rfl L
  rw [Nat.cast_one] at h
  have hb := (abs_le.mp (floor_row_boundary_le hP.zero 1 L)).1
  have hscale := (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+L) (by linarith only [hl] : (1:ℝ)+L ≤ 2*L) 2)
    hP.excess_pos.le).trans (mul_le_mul_of_nonneg_left hP.excess_le (sq_nonneg (2*(L:ℝ))))
  have hupper : (L:ℝ)*(peak c:ℝ) ≤ 2*L*m+8*(L:ℝ)^2*m*e+2*incompletePeriodCost c L := by
    dsimp only [e]; linarith only [h,hb,hscale]
  have hlow := hlaw c m B hP (by linarith only [he,ha₁])
  rw [IsProducer.peakRatio,←mul_div_assoc,le_div_iff₀ hP.m_pos] at hlow
  have h₁ := mul_le_mul_of_nonneg_left hupper he₀.le
  have h₂ := mul_le_mul_of_nonneg_left hlow hl₀.le
  have h₃ := mul_le_mul_of_nonneg_right he (mul_nonneg hl₀.le hP.m_pos.le)
  have h₄ := mul_le_mul_of_nonneg_right hlen (mul_nonneg hl₀.le hP.m_pos.le)
  dsimp only [e] at h₁
  linarith only [h₁,h₂,h₃,h₄]

#print axioms residue_primitive_translation
#print axioms short_windows_force_residue_cost
#print axioms floor_row_window_primitive
#print axioms IsProducer.residue_window_necessary
#print axioms common_period_half_floor

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics

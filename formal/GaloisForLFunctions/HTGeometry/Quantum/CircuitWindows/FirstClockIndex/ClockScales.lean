import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! # Exponential scales for a block of near-independent harmonics -/
open Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.FirstClockIndex
noncomputable section

/-- A linear factor can be absorbed into any strictly larger exponential base. -/
theorem linear_mul_pow_eventually_lt (C : ℝ) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    ∀ᶠ d : ℕ in atTop, C*((d:ℝ)+1)*u^d < v^d := by
  have hz : 1 < v/u := (one_lt_div hu).mpr huv
  have h (j : ℕ) := tendsto_pow_const_div_const_pow_of_one_lt j hz
  have ht : Tendsto (fun d : ℕ => C*((d:ℝ)+1)/(v/u)^d) atTop (𝓝 0) := by
    simpa only [pow_one,pow_zero,zero_add,mul_zero,←add_div,mul_div_assoc] using
      ((h 1).add (h 0)).const_mul C
  filter_upwards [ht.eventually_lt_const zero_lt_one] with d hd
  have hle := (div_lt_one (pow_pos (div_pos (hu.trans huv) hu) d)).mp hd
  simpa only [←mul_pow,div_mul_cancel₀ _ hu.ne'] using mul_lt_mul_of_pos_right hle (pow_pos hu d)

/-- The binomial excess is at most twice its linear term when dz≤1/2. -/
private theorem binomial_excess {z : ℝ} (hz : 0 ≤ z) (d : ℕ) (h : (d:ℝ)*z ≤ 1/2) :
    (1+z)^d-1 ≤ 2*(d:ℝ)*z := by
  have hprod (n : ℕ) : (1+z)^n*(1-(n:ℝ)*z) ≤ 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ,Nat.cast_succ,mul_assoc]
      apply le_trans (mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) _)) ih
      nlinarith only [mul_nonneg (add_nonneg (Nat.cast_nonneg (α := ℝ) n) zero_le_one) (sq_nonneg z)]
  have hp : 0 < 1-(d:ℝ)*z := by linarith
  have ht : (1+z)^d ≤ 1+2*((d:ℝ)*z) := by
    apply (mul_le_mul_iff_left₀ hp).mp
    apply (hprod d).trans
    nlinarith only [mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hz) (show 0 ≤ 1-2*((d:ℝ)*z) by linarith)]
  linarith only [ht]

/-- Below the reciprocal arc scale, a strictly wider exponential deadline
contains a block whose second-moment miss bound decays exponentially. -/
theorem clock_blocks {l x : ℝ} (hl : 0 < l) (hlx : l < x) (hx : x < 1/2) :
    ∃ c ∈ Ioo (0:ℝ) 1, ∀ᶠ d : ℕ in atTop, ∃ Q R : ℕ,
      0 < Q ∧ 0 < R ∧ (Q:ℝ)+R < (1/l)^d ∧ x+(R:ℝ)/Q ≤ 1/2 ∧
      1/((R:ℝ)*x^d)+((1+(R:ℝ)/Q/x)^d-1) < c^d := by
  have hxp := hl.trans hlx
  have hinv := one_div_lt_one_div_of_lt hl hlx
  obtain ⟨A,hxA,hA⟩ := exists_between hinv
  obtain ⟨B,hAB,hBl⟩ := exists_between hA
  have h1x : 1 < 1/x := (one_lt_div hxp).mpr (by linarith)
  have h1A := h1x.trans hxA
  have h1B := h1A.trans hAB
  have hAp := zero_lt_one.trans h1A
  have hBp := zero_lt_one.trans h1B
  let u := 1/(A*x)
  let v := A/B
  have hup : 0 < u := by dsimp [u]; positivity
  have hvp : 0 < v := div_pos hAp hBp
  have hu : u < 1 := (div_lt_one (mul_pos hAp hxp)).mpr ((div_lt_iff₀ hxp).mp hxA)
  have hv : v < 1 := (div_lt_one hBp).mpr hAB
  obtain ⟨c,hc,hc1⟩ := exists_between (max_lt hu hv)
  have huc := (le_max_left u v).trans_lt hc
  have hvc := (le_max_right u v).trans_lt hc
  have hcp := hup.trans huc
  refine ⟨c,⟨hcp,hc1⟩,?_⟩
  filter_upwards [linear_mul_pow_eventually_lt 4 hBp hBl,
    linear_mul_pow_eventually_lt 4 hup huc,linear_mul_pow_eventually_lt (8/x) hvp hvc,
    linear_mul_pow_eventually_lt (2/(1/2-x)) hvp hv] with d hdate hmean hcorr hnear
  let Q := ⌈B^d⌉₊
  let R := ⌈A^d⌉₊
  have hQ₀ : 0 < Q := Nat.ceil_pos.mpr (pow_pos hBp _)
  have hR₀ : 0 < R := Nat.ceil_pos.mpr (pow_pos hAp _)
  have hQp := Nat.cast_pos (α := ℝ).mpr hQ₀
  have hRp := Nat.cast_pos (α := ℝ).mpr hR₀
  have hQ : B^d ≤ (Q:ℝ) := Nat.le_ceil _
  have hR : A^d ≤ (R:ℝ) := Nat.le_ceil _
  have ceilBound (a : ℝ) (ha : 1 ≤ a) : (⌈a^d⌉₊:ℝ) ≤ 2*a^d := by
    linarith only [Nat.ceil_lt_add_one (pow_nonneg (zero_le_one.trans ha) d),one_le_pow₀ ha (n := d)]
  have hR' : (R:ℝ) ≤ 2*A^d := ceilBound _ h1A.le
  have hQ' : (Q:ℝ) ≤ 2*B^d := ceilBound _ h1B.le
  have hd := Nat.cast_nonneg (α := ℝ) d
  have hratio : (R:ℝ)/Q ≤ 2*v^d := by
    rw [show v^d=A^d/B^d from div_pow ..,←mul_div_assoc]
    exact div_le_div₀ (by positivity) hR' (pow_pos hBp _) hQ
  have hnear' : 2*v^d < 1/2-x := by
    rw [one_pow] at hnear
    have hh : (2/(1/2-x))*v^d < 1 :=
      lt_of_le_of_lt (by nlinarith only [mul_nonneg (mul_nonneg (div_nonneg (by norm_num : (0:ℝ)≤2)
        (sub_pos.mpr hx).le) hd) (pow_nonneg hvp.le d)]) hnear
    rwa [div_mul_eq_mul_div,div_lt_one (sub_pos.mpr hx)] at hh
  refine ⟨Q,R,hQ₀,hR₀,?_,by linarith only [hratio,hnear'],?_⟩
  · have hpow := pow_le_pow_left₀ hAp.le hAB.le d
    nlinarith only [hQ',hR',hpow,hdate,mul_nonneg hd (pow_nonneg hBp.le d)]
  have hfirst : 1/((R:ℝ)*x^d) ≤ u^d := by
    rw [show u^d=1/(A^d*x^d) by dsimp [u]; rw [div_pow,one_pow,mul_pow]]
    exact one_div_le_one_div_of_le (mul_pos (pow_pos hAp _) (pow_pos hxp _))
      (mul_le_mul_of_nonneg_right hR (pow_nonneg hxp.le _))
  let z := (R:ℝ)/Q/x
  have hz : 0 ≤ z := div_nonneg (div_nonneg hRp.le hQp.le) hxp.le
  have hz' : z ≤ 2*v^d/x := div_le_div_of_nonneg_right hratio hxp.le
  have hdz : 4*((d:ℝ)*z) < c^d := by
    apply lt_of_le_of_lt _ hcorr
    calc
      4*((d:ℝ)*z) ≤ 4*((d:ℝ)*(2*v^d/x)) := by gcongr
      _ ≤ (8/x)*((d:ℝ)+1)*v^d := by
        rw [show 4*((d:ℝ)*(2*v^d/x)) = (8/x)*(d:ℝ)*v^d by ring]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one)
          (by positivity)) (pow_nonneg hvp.le d)
  have hcsmall := pow_le_one₀ hcp.le hc1.le (n := d)
  have hbin := binomial_excess hz d (by linarith only [hdz,hcsmall])
  change 1/((R:ℝ)*x^d)+((1+z)^d-1) < c^d
  nlinarith only [hfirst,hbin,hdz,hmean,mul_nonneg hd (pow_nonneg hup.le d),pow_nonneg hcp.le d]

#print axioms clock_blocks
end
end GaloisForLFunctions.HTGeometry.FirstClockIndex

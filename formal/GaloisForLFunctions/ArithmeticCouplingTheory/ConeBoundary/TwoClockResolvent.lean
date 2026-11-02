import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# First-order resolvents of two cone clocks

A linear combination of two clocks retains bounded cone moments. Summing
its geometric series gives one resolvent, whose real part is positive in
the unit disk. This preserves the sign of nearby aligned residues.
-/

open Complex Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary

lemma summable_clock_power {ι : Type*} {d X Y : ι → ℂ}
    (hs : ∀ m n : ℕ, Summable fun i => d i*X i^m*Y i^n)
    (x y : ℂ) (k m n : ℕ) :
    Summable fun i => d i*X i^m*Y i^n*(x*X i+y*Y i)^k := by
  induction k generalizing m n with
  | zero => simpa only [pow_zero,mul_one] using hs m n
  | succ k ih =>
    have h := ((ih (m+1) n).mul_left x).add ((ih m (n+1)).mul_left y)
    refine h.congr fun i => ?_
    simp only [pow_succ]
    ring

/-- Averages of cone clocks inherit a geometric bound from all mixed moments. -/
lemma norm_tsum_clock_power_le {ι : Type*} {d X Y : ι → ℂ} {M : ℝ}
    (hs : ∀ m n : ℕ, Summable fun i => d i*X i^m*Y i^n)
    (hM : ∀ m n : ℕ, ‖∑' i, d i*X i^m*Y i^n‖ ≤ M)
    (x y : ℂ) (k m n : ℕ) :
    ‖∑' i, d i*X i^m*Y i^n*(x*X i+y*Y i)^k‖ ≤ M*(‖x‖+‖y‖)^k := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 0)
  induction k generalizing m n with
  | zero => simpa only [pow_zero,mul_one] using hM m n
  | succ k ih =>
    have he : (∑' i, d i*X i^m*Y i^n*(x*X i+y*Y i)^(k+1)) =
        x*(∑' i, d i*X i^(m+1)*Y i^n*(x*X i+y*Y i)^k)+
        y*(∑' i, d i*X i^m*Y i^(n+1)*(x*X i+y*Y i)^k) := by
      rw [← tsum_mul_left,← tsum_mul_left,← Summable.tsum_add
        ((summable_clock_power hs x y k (m+1) n).mul_left x)
        ((summable_clock_power hs x y k m (n+1)).mul_left y)]
      apply tsum_congr
      intro i
      simp only [pow_succ]
      ring
    rw [he]
    calc
      _ ≤ ‖x‖*‖∑' i, d i*X i^(m+1)*Y i^n*(x*X i+y*Y i)^k‖+
          ‖y‖*‖∑' i, d i*X i^m*Y i^(n+1)*(x*X i+y*Y i)^k‖ := by
        simpa only [norm_mul] using norm_add_le
          (x*(∑' i, d i*X i^(m+1)*Y i^n*(x*X i+y*Y i)^k))
          (y*(∑' i, d i*X i^m*Y i^(n+1)*(x*X i+y*Y i)^k))
      _ ≤ ‖x‖*(M*(‖x‖+‖y‖)^k)+‖y‖*(M*(‖x‖+‖y‖)^k) :=
        add_le_add (mul_le_mul_of_nonneg_left (ih (m+1) n) (norm_nonneg x))
          (mul_le_mul_of_nonneg_left (ih m (n+1)) (norm_nonneg y))
      _ = _ := by rw [pow_succ]; ring

/-- The two-clock first-order resolvent is bounded by the cone moment bound. -/
theorem norm_tsum_clock_resolvent_le {ι : Type*} {d X Y : ι → ℂ} {M r : ℝ}
    (hd : Summable fun i => ‖d i‖)
    (hs : ∀ m n : ℕ, Summable fun i => d i*X i^m*Y i^n)
    (hM : ∀ m n : ℕ, ‖∑' i, d i*X i^m*Y i^n‖ ≤ M)
    (x y : ℂ) (hxy : ‖x‖+‖y‖ < 1) (hr0 : 0 ≤ r) (hr : r < 1)
    (hclock : ∀ i, ‖x*X i+y*Y i‖ ≤ r) :
    ‖∑' i, d i/(1-(x*X i+y*Y i))‖ ≤ M/(1-(‖x‖+‖y‖)) := by
  let F : ι → ℕ → ℂ := fun i k => d i*(x*X i+y*Y i)^k
  have hFs : Summable (Function.uncurry F) := by
    refine Summable.of_norm_bounded
      (hd.mul_of_nonneg (summable_geometric_of_lt_one hr0 hr)
        (fun i => norm_nonneg (d i)) (fun k => pow_nonneg hr0 k)) fun ik => ?_
    change ‖d ik.1*(x*X ik.1+y*Y ik.1)^ik.2‖ ≤ ‖d ik.1‖*r^ik.2
    rw [norm_mul,norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hclock ik.1) ik.2) (norm_nonneg _)
  have he : (∑' i, d i/(1-(x*X i+y*Y i))) = ∑' k, ∑' i, F i k := by
    rw [hFs.tsum_comm]
    apply tsum_congr
    intro i
    simp only [F,tsum_mul_left,tsum_geometric_of_norm_lt_one ((hclock i).trans_lt hr),div_eq_mul_inv]
  rw [he]
  have hgeo := (hasSum_geometric_of_lt_one (add_nonneg (norm_nonneg x) (norm_nonneg y)) hxy).mul_left M
  have h := tsum_of_norm_bounded hgeo (fun k => by
    simpa only [F,pow_zero,mul_one] using norm_tsum_clock_power_le hs hM x y k 0 0)
  simpa only [div_eq_mul_inv] using h

/-- A first-order disk resolvent has positive real part. -/
lemma re_clock_resolvent_pos {u : ℂ} (hu : ‖u‖ < 1) :
    0 < ((1-u)⁻¹).re := by
  have hreal : u.re < 1 := (Complex.re_le_norm u).trans_lt hu
  have hne : 1-u ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re,Complex.one_re,Complex.zero_re] at hh
    linarith only [hreal,hh]
  rw [Complex.inv_re]
  exact div_pos (by simpa only [Complex.sub_re,Complex.one_re] using sub_pos.mpr hreal)
    (Complex.normSq_pos.mpr hne)

/-- The denominator of the averaged exponential clocks. -/
def clockDefect (a b : ℝ) (z : ℂ) : ℂ :=
  1-(Complex.exp ((a:ℂ)*z)+Complex.exp ((b:ℂ)*z))/2

/-- Explicit simple-zero bound for the two-clock denominator. -/
lemma clockDefect_lower_near_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z : ℂ} (hz : ‖z‖ ≤ 1/(2*(a+b))) :
    (a+b)/4*‖z‖ ≤ ‖clockDefect a b z‖ := by
  have hk : 0 < a+b := add_pos ha hb
  have hkn : (a+b)*‖z‖ ≤ 1/2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2*(a+b))).1 hz
    nlinarith only [h]
  have haN : ‖(a:ℂ)*z‖=a*‖z‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
  have hbN : ‖(b:ℂ)*z‖=b*‖z‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb]
  have hea := Complex.norm_exp_sub_one_sub_id_le (x := (a:ℂ)*z)
    (by rw [haN]; nlinarith only [hkn,mul_nonneg hb.le (norm_nonneg z)])
  have heb := Complex.norm_exp_sub_one_sub_id_le (x := (b:ℂ)*z)
    (by rw [hbN]; nlinarith only [hkn,mul_nonneg ha.le (norm_nonneg z)])
  rw [haN] at hea
  rw [hbN] at heb
  have he : clockDefect a b z+(((a+b)/2:ℝ):ℂ)*z =
      -((Complex.exp ((a:ℂ)*z)-1-(a:ℂ)*z)+
        (Complex.exp ((b:ℂ)*z)-1-(b:ℂ)*z))/2 := by
    unfold clockDefect
    push_cast
    ring
  have herr : ‖clockDefect a b z+(((a+b)/2:ℝ):ℂ)*z‖ ≤
      ((a+b)*‖z‖)^2/2 := by
    rw [he,norm_div,norm_neg,Complex.norm_two]
    have htri := norm_add_le
      (Complex.exp ((a:ℂ)*z)-1-(a:ℂ)*z)
      (Complex.exp ((b:ℂ)*z)-1-(b:ℂ)*z)
    have hab : 0 ≤ (a*‖z‖)*(b*‖z‖) := by positivity
    nlinarith only [htri,hea,heb,hab]
  have herr' : ‖clockDefect a b z+(((a+b)/2:ℝ):ℂ)*z‖ ≤
      (a+b)/4*‖z‖ := by
    have hprod := mul_le_mul_of_nonneg_left hkn (mul_nonneg hk.le (norm_nonneg z))
    nlinarith only [herr,hprod]
  have htri := norm_sub_norm_le ((((a+b)/2:ℝ):ℂ)*z) (-clockDefect a b z)
  rw [norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (a+b)/2)] at htri
  have he' : (((a+b)/2:ℝ):ℂ)*z-(-clockDefect a b z)=
      clockDefect a b z+(((a+b)/2:ℝ):ℂ)*z := by ring
  rw [he'] at htri
  linarith only [herr',htri]

#print axioms norm_tsum_clock_resolvent_le
#print axioms clockDefect_lower_near_zero
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary

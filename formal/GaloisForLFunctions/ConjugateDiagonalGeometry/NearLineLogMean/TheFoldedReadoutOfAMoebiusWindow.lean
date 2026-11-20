import GaloisForLFunctions.RHTower.Sieve.LogWindowKernel
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact folded readings of Möbius window energy

The normalized sawtooth construction of Shi–Chen–Huang–Wang
(arXiv:2611.23979, §3.1) approximates squaring at logarithmic depth.
On an integer interval the same folds interpolate the square exactly.
Every logarithmic Möbius-window reading belongs to such an interval,
so its mean square admits an exact finite-depth rectified readout.
-/

noncomputable section
open Finset MeasureTheory RHTower.Sieve
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.FoldedWindow

/-- Fold a scalar interval of width h about its midpoint. -/
def foldAt (h x : ℝ) := min x (h-x)

/-- A fold uses two rectified affine functions. -/
theorem fold_relu (h x : ℝ) :
    foldAt h x=h/2-max (x-h/2) 0-max (h/2-x) 0 := by
  rcases le_total x (h/2) with hx | hx
  · rw [foldAt,min_eq_left (by linarith),max_eq_right (by linarith),max_eq_left (by linarith)]
    ring
  · rw [foldAt,min_eq_right (by linarith),max_eq_left (by linarith),max_eq_right (by linarith)]
    ring

/-- Linear interpolation of the integer squares on [0,2^d], using d folds. -/
def foldedSquare : ℕ → ℝ → ℝ
  | 0, x => x
  | d+1, x =>
    let H := (2:ℝ)^(d+1)
    let y := foldAt H x
    foldedSquare d y+H*(x-y)

private theorem fold_mem {h x : ℝ} (hx : x∈Set.Icc 0 (2*h)) : foldAt (2*h) x∈Set.Icc 0 h := by
  constructor
  · exact le_min hx.1 (sub_nonneg.mpr hx.2)
  · rcases le_total x h with h₁ | h₁
    · exact (min_le_left _ _).trans h₁
    · exact (min_le_right _ _).trans (by linarith)

private theorem square_transport (h x : ℝ) :
    x^2=(foldAt h x)^2+h*(x-foldAt h x) := by
  rcases le_total x (h-x) with h₁ | h₁
  · rw [foldAt,min_eq_left h₁]; ring
  · rw [foldAt,min_eq_right h₁]; ring

/-- All depths have the same one-sided absolute error on the integer grid
scale. Normalizing the input and output divides this error by 4^d. -/
theorem folded_error (d : ℕ) {x : ℝ} (hx : x∈Set.Icc 0 ((2:ℝ)^d)) :
    0≤foldedSquare d x-x^2 ∧ foldedSquare d x-x^2≤1/4 := by
  induction d generalizing x with
  | zero =>
    change 0≤x-x^2 ∧ x-x^2≤1/4
    have h₁ : x≤1 := by simpa using hx.2
    exact ⟨by nlinarith only [mul_nonneg hx.1 (sub_nonneg.mpr h₁)],
      by nlinarith only [sq_nonneg (x-1/2)]⟩
  | succ d ih =>
    let H := (2:ℝ)^(d+1)
    have hH : H=2*(2:ℝ)^d := pow_succ' _ _
    have hy : foldAt H x∈Set.Icc 0 ((2:ℝ)^d) := by
      rw [hH]; exact fold_mem (show x∈Set.Icc 0 (2*(2:ℝ)^d) by simpa only [←hH] using hx)
    have he : foldedSquare (d+1) x-x^2=foldedSquare d (foldAt H x)-(foldAt H x)^2 := by
      change foldedSquare d (foldAt H x)+H*(x-foldAt H x)-x^2=_
      linear_combination -(square_transport H x)
    rw [he]
    exact ih hy

/-- Unit normalization gives worst-case error at most 4^(-d-1). -/
def unitSquare (d : ℕ) (x : ℝ) := foldedSquare d ((2:ℝ)^d*x)/((2:ℝ)^d)^2

theorem unit_square_error (d : ℕ) {x : ℝ} (hx : x∈Set.Icc 0 1) :
    0≤unitSquare d x-x^2 ∧ unitSquare d x-x^2≤1/(4*((2:ℝ)^d)^2) := by
  let H := (2:ℝ)^d
  have hH : 0<H := by dsimp [H]; positivity
  have h := folded_error d (show H*x∈Set.Icc 0 H from
    ⟨mul_nonneg hH.le hx.1,mul_le_of_le_one_right hH.le hx.2⟩)
  have hid : unitSquare d x-x^2=(foldedSquare d (H*x)-(H*x)^2)/H^2 := by
    dsimp only [unitSquare,H]; field_simp
  rw [hid]
  exact ⟨div_nonneg h.1 (sq_nonneg _),
    (div_le_div_of_nonneg_right h.2 (sq_nonneg _)).trans_eq (div_div ..)⟩

private theorem fold_distance (h x y : ℝ) : |foldAt h x-foldAt h y|≤|x-y| := by
  rcases le_total x (h-x) with hx | hx <;> rcases le_total y (h-y) with hy | hy
  · simp only [foldAt,min_eq_left hx,min_eq_left hy,le_refl]
  · simp only [foldAt,min_eq_left hx,min_eq_right hy]
    rw [abs_of_nonpos (show x-y≤0 by linarith),abs_le]; constructor <;> linarith
  · simp only [foldAt,min_eq_right hx,min_eq_left hy]
    rw [abs_of_nonneg (show 0≤x-y by linarith),abs_le]; constructor <;> linarith
  · simp only [foldAt,min_eq_right hx,min_eq_right hy]
    rw [show h-x-(h-y)= -(x-y) by ring,abs_neg]

/-- Slopes stay between the first and last secants of the square.
Consequently the unit-normalized Lipschitz constant is strictly below two. -/
theorem folded_secants (d : ℕ) {x y : ℝ} (hx : 0≤x) (hxy : x≤y) (hy : y≤(2:ℝ)^d) :
    y-x≤foldedSquare d y-foldedSquare d x ∧
     foldedSquare d y-foldedSquare d x≤(2*(2:ℝ)^d-1)*(y-x) := by
  induction d generalizing x y with
  | zero => simp only [foldedSquare,pow_zero,mul_one,show (2:ℝ)-1=1 by norm_num,one_mul,le_refl,and_self]
  | succ d ih =>
    let h := (2:ℝ)^d
    let H := 2*h
    have hH : (2:ℝ)^(d+1)=H := pow_succ' _ _
    have hh : 1≤h := one_le_pow₀ (by norm_num)
    have hH1 : 0≤H-1 := by dsimp [H]; linarith only [hh]
    have hy' : y≤H := hH ▸ hy
    let u := foldAt H x
    let v := foldAt H y
    have hu : u∈Set.Icc 0 h := fold_mem ⟨hx,hxy.trans hy'⟩
    have hv : v∈Set.Icc 0 h := fold_mem ⟨hx.trans hxy,hy'⟩
    have hfold : |v-u|≤y-x := by simpa only [abs_of_nonneg (sub_nonneg.mpr hxy)] using fold_distance H y x
    have hc (a b : ℝ) (ha : a∈Set.Icc 0 h) (hb : b∈Set.Icc 0 h) (hab : a≤b) :
        |(foldedSquare d b-H*b)-(foldedSquare d a-H*a)|≤(H-1)*(b-a) := by
      have ⟨hl,hr⟩ := ih ha.1 hab hb.2
      change foldedSquare d b-foldedSquare d a≤(H-1)*(b-a) at hr
      rw [abs_le]
      constructor <;> linarith only [hl,hr,sub_nonneg.mpr hab,mul_nonneg hH1 (sub_nonneg.mpr hab)]
    have hdist : |(foldedSquare d v-H*v)-(foldedSquare d u-H*u)|≤(H-1)*|v-u| := by
      rcases le_total u v with h | h
      · rw [abs_of_nonneg (sub_nonneg.mpr h)]; exact hc _ _ hu hv h
      · rw [abs_sub_comm,abs_of_nonpos (sub_nonpos.mpr h),neg_sub]; exact hc _ _ hv hu h
    have he := abs_le.mp (hdist.trans (mul_le_mul_of_nonneg_left hfold hH1))
    simp only [foldedSquare,hH]
    change _≤foldedSquare d v+H*(y-v)-(foldedSquare d u+H*(x-u)) ∧ _
    constructor <;> linarith only [he.1,he.2]

theorem unit_square_lipschitz (d : ℕ) {x y : ℝ} (hx : x∈Set.Icc 0 1) (hy : y∈Set.Icc 0 1) :
    |unitSquare d x-unitSquare d y|≤(2-((2:ℝ)^d)⁻¹)*|x-y| := by
  wlog hxy : y≤x generalizing x y
  · rw [abs_sub_comm,abs_sub_comm x]; exact this hy hx (le_of_not_ge hxy)
  let H := (2:ℝ)^d
  have hp : 0<H := by dsimp [H]; positivity
  have ⟨hl,hr⟩ := folded_secants d (mul_nonneg hp.le hy.1) (mul_le_mul_of_nonneg_left hxy hp.le)
    (mul_le_of_le_one_right hp.le hx.2)
  change |foldedSquare d (H*x)/H^2-foldedSquare d (H*y)/H^2| ≤ _
  rw [← sub_div,abs_div,abs_of_pos (sq_pos_of_pos hp),abs_of_nonneg (by linarith only [hl,mul_le_mul_of_nonneg_left hxy hp.le]),
    abs_of_nonneg (sub_nonneg.mpr hxy),div_le_iff₀ (sq_pos_of_pos hp)]
  exact hr.trans_eq (by change (2*H-1)*(H*x-H*y)=(2-H⁻¹)*(x-y)*H^2; field_simp [hp.ne'])

/-- Every integer in the original range gives the exact square. -/
theorem folded_integer (d k : ℕ) (hk : k≤2^d) : foldedSquare d (k:ℝ)=(k:ℝ)^2 := by
  induction d generalizing k with
  | zero =>
    have h : k=0 ∨ k=1 := by simp only [pow_zero] at hk; omega
    rcases h with rfl | rfl <;> simp [foldedSquare]
  | succ d ih =>
    let H := 2^(d+1)
    let j := min k (H-k)
    have hpow : H=2*2^d := pow_succ' _ _
    have hj : j≤2^d := by
      rcases le_total k (2^d) with h | h
      · exact (min_le_left _ _).trans h
      · exact (min_le_right _ _).trans (by omega)
    have hy : foldAt ((2:ℝ)^(d+1)) k=(j:ℝ) := by
      dsimp only [j,foldAt,H]
      rw [Nat.cast_min,Nat.cast_sub hk,Nat.cast_pow,Nat.cast_ofNat]
    rw [foldedSquare,hy,ih j hj]
    simpa only [hy] using (square_transport ((2:ℝ)^(d+1)) (k:ℝ)).symm

/-- Integer readout of the shift of a Möbius window, at arbitrary real bandwidth. -/
def mobiusWindow (s : Finset ℕ) (w u : ℝ) : ℤ := by
  classical
  exact ∑ n ∈ s, if u∈logWindow w n then ArithmeticFunction.moebius n else 0

private theorem abs_window_le (s : Finset ℕ) (w u : ℝ) : |mobiusWindow s w u|≤(s.card:ℤ) := by
  classical
  unfold mobiusWindow
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hc := sum_le_sum (s:=s) (fun n _ => show |if u∈logWindow w n then ArithmeticFunction.moebius n else 0|≤(1:ℤ) by
    split_ifs <;> simp [ArithmeticFunction.abs_moebius_le_one])
  simpa only [sum_const,nsmul_eq_mul,mul_one] using hc

private theorem window_complex (s : Finset ℕ) (w u : ℝ) :
    logWindowSum (fun n => (ArithmeticFunction.moebius n : ℂ)) s w u=(mobiusWindow s w u:ℂ) := by
  classical
  simp only [logWindowSum,mobiusWindow,Int.cast_sum]
  apply sum_congr rfl
  intro n _
  by_cases h : u∈logWindow w n <;> simp [h]

/-- With capacity 2^d, the exact Möbius window energy is the integral of
a depth-d folded readout, simultaneously at all bandwidths and offsets. -/
theorem mobius_window_energy_exact (d : ℕ) (s : Finset ℕ) (hs : s.card≤2^d) (w : ℝ) :
    (∫ u : ℝ, foldedSquare d |(mobiusWindow s w u:ℝ)|) =
      ∑ n∈s, ∑ m∈s, ((ArithmeticFunction.moebius n:ℤ):ℝ)*((ArithmeticFunction.moebius m:ℤ):ℝ)*
        max (w-|Real.log n-Real.log m|) 0 := by
  have hp (u : ℝ) : foldedSquare d |(mobiusWindow s w u:ℝ)| =
      ‖logWindowSum (fun n => (ArithmeticFunction.moebius n:ℂ)) s w u‖^2 := by
    let z := mobiusWindow s w u
    have hcast : (z.natAbs:ℝ)=|(z:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
    have hcard : z.natAbs≤s.card := by
      exact_mod_cast ((Int.natCast_natAbs z).trans_le (abs_window_le s w u))
    rw [window_complex]
    change foldedSquare d |(z:ℝ)|=‖(z:ℂ)‖^2
    rw [← hcast,folded_integer d z.natAbs (hcard.trans hs),hcast,←Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  simp_rw [hp]
  rw [integral_normSq_logWindowSum]
  refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_
  simp [←Int.cast_mul]

#print axioms folded_error
#print axioms unit_square_lipschitz
#print axioms folded_integer
#print axioms mobius_window_energy_exact
end GaloisForLFunctions.ConjugateDiagonalGeometry.FoldedWindow

import GaloisForLFunctions.ArithmeticPositiveDuality.TheLiouvilleLawForTwoCommutingTranslations
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.SpecialFunctions.Choose

/-!
# The binomial expansion of a harmonic second moment

For a two-translation law, differencing the second moment in time inserts
the square of a spatial contrast. Harmonicity is preserved by this contrast,
so every coefficient in the Gregory–Newton expansion is a weighted square.
-/

noncomputable section
open Finset Filter
open scoped Topology
namespace GaloisForLFunctions.ArithmeticPositiveDuality.TranslationLaw

variable {G : Type*} [AddCommGroup G]

private theorem contrast_iter_harmonic (w : ℝ) (a b : G) {f : G → ℝ}
    (hf : mean w a b f=f) (k : ℕ) :
    mean w a b ((contrast a b)^[k] f)=(contrast a b)^[k] f := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply',mean_contrast,ih]

private theorem moment_increment (w : ℝ) (a b : G) {f : G → ℝ} (hf : mean w a b f=f)
    (n : ℕ) (x : G) :
    walk w a b (n+1) (fun y => f y^2) x-walk w a b n (fun y => f y^2) x =
      w*(1-w)*walk w a b n (fun y => contrast a b f y^2) x := by
  rw [harmonic_variance _ _ _ hf (n+1) x,harmonic_variance _ _ _ hf n x,sum_range_succ]
  ring

/-- The k-th forward difference of the second moment equals the transported
square of the k-th spatial contrast, with its exact Bernoulli factor. -/
theorem moment_time_difference (w : ℝ) (a b : G) {f : G → ℝ} (hf : mean w a b f=f)
    (k n : ℕ) (x : G) :
    (fwdDiff (1:ℕ))^[k] (fun j => walk w a b j (fun y => f y^2) x) n =
      (w*(1-w))^k*walk w a b n (fun y => ((contrast a b)^[k] f y)^2) x := by
  induction k generalizing n with
  | zero => simp only [Function.iterate_zero,id_eq,pow_zero,one_mul]
  | succ k ih =>
    rw [Function.iterate_succ_apply' (fwdDiff (1:ℕ))]
    change (fwdDiff (1:ℕ))^[k] _ (n+1) - (fwdDiff (1:ℕ))^[k] _ n = _
    rw [ih,ih,← mul_sub,moment_increment w a b (contrast_iter_harmonic w a b hf k),
      Function.iterate_succ_apply' (contrast a b),pow_succ]
    ring

/-- Exact binomial expansion of the whole time profile at one starting point.
No boundedness, continuity or moment conditions are required. -/
theorem binomial_walk_second_moment (w : ℝ) (a b : G) {f : G → ℝ} (hf : mean w a b f=f)
    (n : ℕ) (x : G) :
    walk w a b n (fun y => f y^2) x = ∑ k ∈ range (n+1),
      (n.choose k:ℝ)*((w*(1-w))^k*((contrast a b)^[k] f x)^2) := by
  have h := shift_eq_sum_fwdDiff_iter (1:ℕ) (fun j => walk w a b j (fun y => f y^2) x) n 0
  simpa only [nsmul_eq_mul,Nat.cast_id,mul_one,zero_add,moment_time_difference w a b hf,walk] using h

/-- Each individual nonzero spatial contrast forces growth at its own
binomial order. Positive terms of other orders cannot cancel it. -/
theorem contrast_forces_binomial_growth (w : ℝ) (hw : w ∈ Set.Icc 0 1) (a b : G)
    {f : G → ℝ} (hf : mean w a b f=f) (k n : ℕ) (hk : k≤n) (x : G) :
    (n.choose k:ℝ)*((w*(1-w))^k*((contrast a b)^[k] f x)^2) ≤
      walk w a b n (fun y => f y^2) x := by
  rw [binomial_walk_second_moment _ _ _ hf]
  have hvar := mul_nonneg hw.1 (sub_nonneg.mpr hw.2)
  exact single_le_sum (fun j _ => mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (pow_nonneg hvar _) (sq_nonneg _))) (mem_range.mpr (Nat.lt_succ_of_le hk))

/-- The time profile of the second moment determines every squared contrast
at the starting point by finite differences, including its zeros. -/
theorem moment_difference_zero_iff (w : ℝ) (hw : w ∈ Set.Ioo 0 1) (a b : G) {f : G → ℝ}
    (hf : mean w a b f=f) (k : ℕ) (x : G) :
    (fwdDiff (1:ℕ))^[k] (fun j => walk w a b j (fun y => f y^2) x) 0=0 ↔
      (contrast a b)^[k] f x=0 := by
  rw [moment_time_difference w a b hf,walk]
  simp only [mul_eq_zero,pow_ne_zero k (mul_pos hw.1 (sub_pos.mpr hw.2)).ne',
    false_or,sq_eq_zero_iff]

private theorem scaled_choose_limit (k : ℕ) :
    Tendsto (fun n : ℕ => (n.choose k:ℝ)/(n:ℝ)^k) atTop (𝓝 (1/(k.factorial:ℝ))) := by
  have he := (isEquivalent_choose k).div
    (Asymptotics.IsEquivalent.refl (u:=fun n : ℕ => (n:ℝ)^k) (l:=atTop))
  apply he.symm.tendsto_nhds
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  change 1/(k.factorial:ℝ)=((n:ℝ)^k/k.factorial)/(n:ℝ)^k
  field_simp [(Nat.cast_pos (α:=ℝ).mpr hn).ne']

/-- Sub-binomial growth on any cofinal sequence kills the corresponding
contrast at the observation point. No control at the intervening times
or at other starting points is required. -/
theorem contrast_zero_of_cofinal_moment {ι : Type*} {l : Filter ι} [NeBot l]
    (w : ℝ) (hw : w ∈ Set.Ioo 0 1) (a b : G) {f : G → ℝ} (hf : mean w a b f=f)
    (k : ℕ) (x : G) (N : ι → ℕ) (hN : Tendsto N l atTop)
    (hs : Tendsto (fun i => walk w a b (N i) (fun y => f y^2) x/(N i:ℝ)^k) l (𝓝 0)) :
    (contrast a b)^[k] f x=0 := by
  let A := (w*(1-w))^k*((contrast a b)^[k] f x)^2
  have hb := ((scaled_choose_limit k).comp hN).mul_const A
  have lower : (1/(k.factorial:ℝ))*A ≤ 0 := by
    apply le_of_tendsto_of_tendsto hb hs
    filter_upwards [hN.eventually_ge_atTop k] with i hi
    have h := div_le_div_of_nonneg_right
      (contrast_forces_binomial_growth w ⟨hw.1.le,hw.2.le⟩ a b hf k (N i) hi x)
      (pow_nonneg (Nat.cast_nonneg _) k)
    simpa only [Function.comp_apply,div_mul_eq_mul_div,A] using h
  by_contra hn
  have hc := pow_pos (mul_pos hw.1 (sub_pos.mpr hw.2)) k
  exact (mul_pos (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos k)))
    (mul_pos hc (sq_pos_of_ne_zero hn))).not_ge lower

/-- A vanished global contrast cuts the binomial expansion off exactly.
Conversely, equality with this finite expansion forces the next contrast
to vanish everywhere. -/
theorem truncated_moment_iff (w : ℝ) (hw : w ∈ Set.Ioo 0 1) (a b : G) {f : G → ℝ}
    (hf : mean w a b f=f) (m : ℕ) :
    (∀ x, (contrast a b)^[m+1] f x=0) ↔
      ∀ n x, walk w a b n (fun y => f y^2) x = ∑ k ∈ range (min n m+1),
        (n.choose k:ℝ)*((w*(1-w))^k*((contrast a b)^[k] f x)^2) := by
  let D := contrast a b
  have hz : D (0:G → ℝ)=0 := by funext x; simp [D,contrast]
  constructor
  · intro h n x
    rw [binomial_walk_second_moment _ _ _ hf]
    apply (sum_subset_zero_on_sdiff (fun j hj => mem_range.mpr
      ((mem_range.mp hj).trans_le (Nat.add_le_add_right (min_le_left n m) 1))) ?_ (fun _ _ => rfl)).symm
    intro j hj
    obtain ⟨hjn,hjm⟩ := mem_sdiff.mp hj
    have hlarge : m+1≤j := by
      simp only [mem_range,not_lt] at hjn hjm
      omega
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hlarge
    have hzero : D^[j] f=0 := by
      rw [hd,Nat.add_comm,Function.iterate_add_apply,show D^[m+1] f=0 from funext h]
      exact Function.iterate_fixed hz d
    simp only [show (contrast a b)^[j] f=0 from hzero,Pi.zero_apply,zero_pow (by decide : 2≠0),mul_zero]
  · intro h x
    have he := h (m+1) x
    rw [binomial_walk_second_moment _ _ _ hf,sum_range_succ,min_eq_right (Nat.le_succ m),
      Nat.choose_self,Nat.cast_one,one_mul,add_eq_left] at he
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left
      (pow_pos (mul_pos hw.1 (sub_pos.mpr hw.2)) _).ne')

end GaloisForLFunctions.ArithmeticPositiveDuality.TranslationLaw

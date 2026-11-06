import GaloisForLFunctions.FiniteFreeProbability.JensenCountsOffLineZeros
import GaloisForLFunctions.FiniteFreeProbability.XiJensenCircleFormula

/-!
# A Gaussian factor contracts the root strip of a Jensen polynomial

For a polynomial `q` with conjugation symmetry, the shift average `(q(z + iη) + q(z - iη))/2` moves the
root strip from `|Im z|² ≤ B` to `|Im z|² ≤ max(B - η², 0)`: for a conjugate pair of roots with imaginary
part `b`, the two products at `z ± iη` differ by `8 y η (x² + y² + η² - b²)`.

The symbol of the average is `cos(ηw)`, and `cos(√(2c/n) w)^n → e^{-cw²}`. So if `f(w) e^{cw²}` has size
`M` on the circle `|w| = r`, then Cauchy bounds put the roots of `R_d(f e^{c·²})` in the disc of radius
`(1 + M) d / r`, and `R_d(f)` is real-rooted as soon as `2c` exceeds the square of this radius.
-/

open Polynomial Filter Topology Complex Set
open GaloisForLFunctions.HTGeometry RHTower
open scoped ComplexConjugate

namespace FiniteFreeProbability

noncomputable section

/-! ## One shift average -/

/-- The difference of the two pair products at `z ± iη`. -/
theorem pair_product_sub (x y η b : ℝ) :
    ((x ^ 2 + (y + η - b) ^ 2) * (x ^ 2 + (y + η + b) ^ 2)) -
        ((x ^ 2 + (y - η - b) ^ 2) * (x ^ 2 + (y - η + b) ^ 2)) =
      8 * y * η * (x ^ 2 + y ^ 2 + η ^ 2 - b ^ 2) := by
  ring

theorem norm_pair_lt {z r : ℂ} {η : ℝ} (hy : 0 < z.im) (hη : 0 < η)
    (hr : r.im ^ 2 < z.im ^ 2 + η ^ 2) :
    ‖z - I * η - r‖ * ‖conj (z - I * η) - r‖ < ‖z + I * η - r‖ * ‖conj (z + I * η) - r‖ := by
  set x := z.re - r.re with hx
  set y := z.im with hy'
  set b := r.im with hb
  have h1 : ‖z - I * η - r‖ ^ 2 = x ^ 2 + (y - η - b) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hx, hy', hb]
    ring
  have h2 : ‖conj (z - I * η) - r‖ ^ 2 = x ^ 2 + (y - η + b) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hx, hy', hb]
    ring
  have h3 : ‖z + I * η - r‖ ^ 2 = x ^ 2 + (y + η - b) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hx, hy', hb]
    ring
  have h4 : ‖conj (z + I * η) - r‖ ^ 2 = x ^ 2 + (y + η + b) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hx, hy', hb]
    ring
  apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
  rw [mul_pow, mul_pow, h1, h2, h3, h4]
  have h5 := pair_product_sub x y η b
  have h6 : 0 < 8 * y * η * (x ^ 2 + y ^ 2 + η ^ 2 - b ^ 2) := by
    apply mul_pos (mul_pos (mul_pos (by norm_num) hy) hη)
    nlinarith only [hr, sq_nonneg x]
  linarith only [h5, h6]

theorem prod_lt_of_forall_lt {ι : Type*} (s : Multiset ι) (hs : s ≠ 0) {A B : ι → ℝ}
    (hB : ∀ i ∈ s, 0 ≤ B i) (hAB : ∀ i ∈ s, B i < A i) :
    (s.map B).prod < (s.map A).prod := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    have ha := hAB a (Multiset.mem_cons_self a s)
    have hb0 := hB a (Multiset.mem_cons_self a s)
    have hBs : ∀ i ∈ s, 0 ≤ B i := fun i hi => hB i (Multiset.mem_cons_of_mem hi)
    have hABs : ∀ i ∈ s, B i < A i := fun i hi => hAB i (Multiset.mem_cons_of_mem hi)
    have hP0 : 0 ≤ (s.map B).prod := Multiset.prod_nonneg (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 hx
      exact hBs i hi)
    by_cases h0 : s = 0
    · simpa [h0] using ha
    · have hlt := ih h0 hBs hABs
      exact mul_lt_mul'' ha hlt hb0 hP0

theorem norm_multiset_map_prod (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).prod‖ = (s.map fun r => ‖f r‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [norm_mul, ih]

theorem cos_real_mul_conj (η : ℝ) (w : ℂ) :
    Complex.cos (η * conj w) = conj (Complex.cos (η * w)) := by
  rw [← Complex.cos_conj, map_mul, Complex.conj_ofReal]

/-- **The shift average contracts the root strip.** -/
theorem im_sq_le_of_shift_average {p q : ℂ[X]} {η : ℝ} (hη : 0 < η) (hq0 : q ≠ 0)
    (hconj : ∀ z, q.eval (conj z) = conj (q.eval z))
    (h : ∀ z, p.eval z = (q.eval (z + I * η) + q.eval (z - I * η)) / 2) {B : ℝ}
    (hB : ∀ z, q.eval z = 0 → z.im ^ 2 ≤ B) :
    ∀ z, p.eval z = 0 → z.im ^ 2 ≤ max (B - η ^ 2) 0 := by
  have hpconj : ∀ z, p.eval (conj z) = conj (p.eval z) := by
    intro z
    have e1 : conj (z + I * η) = conj z - I * η := by simp [sub_eq_add_neg]
    have e2 : conj (z - I * η) = conj z + I * η := by simp [sub_eq_add_neg]
    have h2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
    rw [h, h, map_div₀, map_add, ← hconj, ← hconj, e1, e2, h2, add_comm]
  -- It suffices to treat roots in the upper half-plane.
  have hkey : ∀ z, 0 < z.im → B - η ^ 2 < z.im ^ 2 → p.eval z ≠ 0 := by
    intro z hy hzB h0
    have hroots : ∀ r ∈ q.roots, r.im ^ 2 < z.im ^ 2 + η ^ 2 := fun r hr => by
      have := hB r ((mem_roots hq0).1 hr)
      linarith only [this, hzB]
    have hsum : q.eval (z + I * η) + q.eval (z - I * η) = 0 := by
      rw [h] at h0
      linear_combination 2 * h0
    have hsplit := (IsAlgClosed.splits q).eq_prod_roots
    set c := q.leadingCoeff with hc
    have hc0 : c ≠ 0 := leadingCoeff_ne_zero.2 hq0
    have heval (w : ℂ) : q.eval w = c * (q.roots.map fun r => w - r).prod := by
      conv_lhs => rw [hsplit]
      rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
      simp
    by_cases hemp : q.roots = 0
    · rw [heval, heval, hemp] at hsum
      simp only [Multiset.map_zero, Multiset.prod_zero, mul_one] at hsum
      exact hc0 (by linear_combination hsum / 2)
    -- Compare the two values through the conjugate products.
    have hnorm (w : ℂ) : ‖q.eval w‖ ^ 2 =
        ‖c‖ ^ 2 * (q.roots.map fun r => ‖w - r‖ * ‖conj w - r‖).prod := by
      have h1 : ‖q.eval w‖ ^ 2 = ‖q.eval w‖ * ‖q.eval (conj w)‖ := by
        rw [hconj, Complex.norm_conj, sq]
      rw [h1, heval w, heval (conj w), norm_mul, norm_mul, norm_multiset_map_prod,
        norm_multiset_map_prod]
      have h2 : (q.roots.map fun r => ‖w - r‖ * ‖conj w - r‖).prod =
          (q.roots.map fun r => ‖w - r‖).prod * (q.roots.map fun r => ‖conj w - r‖).prod := by
        rw [Multiset.prod_map_mul]
      rw [h2]
      ring
    have hlt := prod_lt_of_forall_lt q.roots hemp
      (A := fun r => ‖z + I * η - r‖ * ‖conj (z + I * η) - r‖)
      (B := fun r => ‖z - I * η - r‖ * ‖conj (z - I * η) - r‖)
      (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun r hr => norm_pair_lt hy hη (hroots r hr))
    have hc2 : 0 < ‖c‖ ^ 2 := pow_pos (norm_pos_iff.2 hc0) 2
    have hn : ‖q.eval (z - I * η)‖ ^ 2 < ‖q.eval (z + I * η)‖ ^ 2 := by
      rw [hnorm, hnorm]
      exact mul_lt_mul_of_pos_left hlt hc2
    have heq : ‖q.eval (z + I * η)‖ = ‖q.eval (z - I * η)‖ := by
      rw [eq_neg_of_add_eq_zero_left hsum, norm_neg]
    rw [heq] at hn
    exact lt_irrefl _ hn
  intro z hz
  by_contra hcon
  push Not at hcon
  have h1 : B - η ^ 2 < z.im ^ 2 := lt_of_le_of_lt (le_max_left _ _) hcon
  have h2 : 0 < z.im ^ 2 := lt_of_le_of_lt (le_max_right _ _) hcon
  have him : z.im ≠ 0 := fun h0 => by
    rw [h0] at h2
    norm_num at h2
  rcases lt_or_gt_of_ne him with hneg | hpos
  · have hp : p.eval (conj z) = 0 := by rw [hpconj, hz, map_zero]
    refine hkey (conj z) (by rw [Complex.conj_im]; linarith only [hneg]) ?_ hp
    rw [Complex.conj_im, neg_sq]
    exact h1
  · exact hkey z hpos h1 hz

/-! ## The symbol of the shift average -/

theorem eval_jensen_cos_mul {g : ℂ → ℂ} (hg : Differentiable ℂ g) (η : ℝ) (d : ℕ) (z : ℂ) :
    (jensenRev d (taylorPS fun w => Complex.cos (η * w) * g w)).eval z =
      ((jensenRev d (taylorPS g)).eval (z + I * η) + (jensenRev d (taylorPS g)).eval (z - I * η)) / 2 := by
  have hcg : Differentiable ℂ fun w => Complex.cos (η * w) * g w :=
    ((Complex.differentiable_cos.comp (by fun_prop))).mul hg
  rw [eval_jensenRev_taylorPS hcg, eval_jensenRev_taylorPS hg, eval_jensenRev_taylorPS hg]
  have hfun : (fun w => Complex.exp (z * w) * (Complex.cos (η * w) * g w)) =
      (1 / 2 : ℂ) • ((fun w => Complex.exp ((z + I * η) * w) * g w) +
        fun w => Complex.exp ((z - I * η) * w) * g w) := by
    funext w
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.cos]
    have e1 : Complex.exp ((z + I * η) * w) = Complex.exp (z * w) * Complex.exp ((η * w) * I) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have e2 : Complex.exp ((z - I * η) * w) = Complex.exp (z * w) * Complex.exp (-(η * w) * I) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [e1, e2]
    ring
  have hu (a : ℂ) : ContDiffAt ℂ d (fun w => Complex.exp (a * w) * g w) 0 :=
    ((((Complex.differentiable_exp.comp (by fun_prop)).mul hg)).contDiff).contDiffAt
  rw [hfun, iteratedDeriv_const_smul_field, iteratedDeriv_add (hu _) (hu _)]
  simp only [smul_eq_mul]
  ring

/-- Iterating the shift average contracts the strip by `k η²`. -/
theorem im_sq_le_of_cos_pow {H : ℂ → ℂ} (hH : Differentiable ℂ H) (hreal : ∀ w, H (conj w) = conj (H w))
    (h0 : H 0 = 1) (d : ℕ) {η : ℝ} (hη : 0 < η) {B : ℝ}
    (hB : ∀ z, (jensenRev d (taylorPS H)).eval z = 0 → z.im ^ 2 ≤ B) (k : ℕ) :
    ∀ z, (jensenRev d (taylorPS fun w => Complex.cos (η * w) ^ k * H w)).eval z = 0 →
      z.im ^ 2 ≤ max (B - k * η ^ 2) 0 := by
  induction k with
  | zero =>
    intro z hz
    simp only [pow_zero, one_mul] at hz
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    exact (hB z hz).trans (le_max_left _ _)
  | succ k ih =>
    set g : ℂ → ℂ := fun w => Complex.cos (η * w) ^ k * H w with hgdef
    have hgd : Differentiable ℂ g :=
      ((Complex.differentiable_cos.comp (by fun_prop)).pow k).mul hH
    have hfun : (fun w => Complex.cos (η * w) ^ (k + 1) * H w) =
        fun w => Complex.cos (η * w) * g w := by
      funext w
      simp only [hgdef]
      ring
    have hg0 : g 0 = 1 := by simp [hgdef, h0]
    have hgreal : ∀ w, g (conj w) = conj (g w) := by
      intro w
      simp only [hgdef]
      rw [hreal, cos_real_mul_conj, map_mul, map_pow]
    -- The polynomial `R_d(g)` is nonzero and conjugation symmetric.
    have hq0 : jensenRev d (taylorPS g) ≠ 0 := by
      intro h
      have hco : (jensenRev d (taylorPS g)).coeff d = 1 := by
        rw [coeff_jensenRev_self, taylorPS, PowerSeries.constantCoeff_mk]
        simp [hg0]
      rw [h, coeff_zero] at hco
      exact zero_ne_one hco
    have hconj : ∀ z, (jensenRev d (taylorPS g)).eval (conj z) =
        conj ((jensenRev d (taylorPS g)).eval z) := by
      intro z
      rw [jensenRev_eq_sum, eval_finsetSum, eval_finsetSum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hd := iteratedDeriv_conj_of_schwarzReal hgreal i 0
      rw [map_zero] at hd
      have ha : conj (PowerSeries.coeff i (taylorPS g)) = PowerSeries.coeff i (taylorPS g) := by
        rw [taylorPS, PowerSeries.coeff_mk, map_div₀, map_natCast, ← hd]
      rw [eval_mul, eval_mul, eval_C, eval_C, eval_pow, eval_pow, eval_X, eval_X, map_mul, map_mul,
        map_pow, map_natCast, ha]
    intro z hz
    rw [hfun] at hz
    have hstep := im_sq_le_of_shift_average hη hq0 hconj
      (fun w => eval_jensen_cos_mul hgd η d w) ih z hz
    refine hstep.trans (max_le ?_ (le_max_right _ _))
    rcases le_total (B - k * η ^ 2) 0 with h' | h'
    · rw [max_eq_right h']
      exact le_trans (by nlinarith only [sq_nonneg η]) (le_max_right _ _)
    · rw [max_eq_left h']
      refine le_trans (le_of_eq ?_) (le_max_left _ _)
      push_cast
      ring

/-! ## The Gaussian as a limit of cosine powers -/

theorem norm_cos_sub_exp_le {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖Complex.cos u - Complex.exp (-(u ^ 2 / 2))‖ ≤ ‖u‖ ^ 4 := by
  have h1 := Complex.cos_bound hu
  have hx : ‖-(u ^ 2 / 2)‖ = ‖u‖ ^ 2 / 2 := by
    rw [norm_neg, norm_div, norm_pow, Complex.norm_two]
  have hx1 : ‖-(u ^ 2 / 2)‖ ≤ 1 := by
    rw [hx]
    nlinarith only [hu, norm_nonneg u]
  have h2 := Complex.norm_exp_sub_one_sub_id_le hx1
  rw [hx] at h2
  have e : Complex.cos u - Complex.exp (-(u ^ 2 / 2)) =
      (Complex.cos u - (1 - u ^ 2 / 2)) - (Complex.exp (-(u ^ 2 / 2)) - 1 - -(u ^ 2 / 2)) := by
    ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h4 : 0 ≤ ‖u‖ ^ 4 := by positivity
  nlinarith only [h1, h2, h4]

theorem norm_cos_le_exp (u : ℂ) : ‖Complex.cos u‖ ≤ Real.exp (‖u‖ ^ 2 / 2) := by
  have h1 : ‖Complex.cos u‖ ≤ Real.cosh u.im := by
    rw [Complex.cos, norm_div, Complex.norm_two, Real.cosh_eq]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_exp, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.I_im, Complex.neg_im, mul_zero,
      mul_one, zero_sub]
    ring_nf
  have h2 := Real.cosh_le_exp_half_sq u.im
  have h3 : u.im ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [← sq_abs u.im]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm u) 2
  exact h1.trans (h2.trans (Real.exp_le_exp.2 (by linarith only [h3])))

theorem norm_pow_sub_pow_le {a b : ℂ} {A : ℝ} (hA : 1 ≤ A) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ A) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ n * A ^ n * ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    have hA0 : 0 ≤ A := by linarith only [hA]
    have hAn : A ^ n ≤ A ^ (n + 1) := pow_le_pow_right₀ hA (Nat.le_succ n)
    have h1 : ‖a * (a ^ n - b ^ n)‖ ≤ A * (n * A ^ n * ‖a - b‖) := by
      rw [norm_mul]
      exact mul_le_mul ha ih (norm_nonneg _) hA0
    have h2 : ‖(a - b) * b ^ n‖ ≤ ‖a - b‖ * A ^ (n + 1) := by
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        ((pow_le_pow_left₀ (norm_nonneg _) hb n).trans hAn) (norm_nonneg _)
    rw [e]
    refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
    push_cast
    ring

/-- `cos(√(2c/n) w)^n → e^{-cw²}`, uniformly on bounded sets. -/
theorem tendstoLocallyUniformly_cos_pow {c : ℝ} (hc : 0 < c) :
    TendstoLocallyUniformly
      (fun (n : ℕ) (w : ℂ) => Complex.cos ((Real.sqrt (2 * c / (n + 1)) : ℝ) * w) ^ (n + 1))
      (fun w => Complex.exp (-(c * w ^ 2))) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R := max R₀ 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hKR : ∀ w ∈ K, ‖w‖ ≤ R := fun w hw => by
    have := hR₀ hw
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set D := Real.exp (c * R ^ 2) * (4 * c ^ 2 * R ^ 4) with hD
  have hD0 : 0 ≤ D := by positivity
  filter_upwards [eventually_gt_atTop ⌈D / ε⌉₊, eventually_gt_atTop ⌈2 * c * R ^ 2⌉₊] with n hn hn2 w hw
  have hnR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set N : ℝ := (n : ℝ) + 1 with hN
  have hn1 : D / ε < N := by
    have h1 := Nat.le_ceil (D / ε)
    have h2 : ((⌈D / ε⌉₊ : ℕ) : ℝ) < n := by exact_mod_cast hn
    rw [hN]
    linarith only [h1, h2]
  have hn3 : 2 * c * R ^ 2 < N := by
    have h1 := Nat.le_ceil (2 * c * R ^ 2)
    have h2 : ((⌈2 * c * R ^ 2⌉₊ : ℕ) : ℝ) < n := by exact_mod_cast hn2
    rw [hN]
    linarith only [h1, h2]
  set η := Real.sqrt (2 * c / N) with hη
  have hη2 : η ^ 2 = 2 * c / N := Real.sq_sqrt (by positivity)
  have hη0 : 0 ≤ η := Real.sqrt_nonneg _
  set u : ℂ := (η : ℂ) * w with hu
  have hun : ‖u‖ = η * ‖w‖ := by
    rw [hu, norm_mul, Complex.norm_real, Real.norm_of_nonneg hη0]
  have hwR := hKR w hw
  have hu2 : ‖u‖ ^ 2 ≤ 2 * c * R ^ 2 / N := by
    rw [hun, mul_pow, hη2, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hnR]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg _) hwR 2
  have hu1 : ‖u‖ ≤ 1 := by
    apply (sq_le_one_iff₀ (norm_nonneg _)).mp
    refine hu2.trans ?_
    rw [div_le_one hnR]
    exact hn3.le
  set A := Real.exp (‖u‖ ^ 2 / 2) with hA
  have hA1 : 1 ≤ A := Real.one_le_exp (by positivity)
  have hb : ‖Complex.exp (-(u ^ 2 / 2))‖ ≤ A := by
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 (le_of_eq ?_))
    rw [norm_neg, norm_div, norm_pow, Complex.norm_two]
  have hmain := norm_pow_sub_pow_le hA1 (norm_cos_le_exp u) hb (n + 1)
  have hexp : Complex.exp (-(u ^ 2 / 2)) ^ (n + 1) = Complex.exp (-(c * w ^ 2)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    have hηC : ((η : ℂ)) ^ 2 = 2 * c / (N : ℂ) := by
      rw [← Complex.ofReal_pow, hη2]
      push_cast
      ring
    have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hnR.ne'
    rw [hu, mul_pow, hηC]
    have hcast : ((n + 1 : ℕ) : ℂ) = (N : ℂ) := by
      rw [hN]
      push_cast
      ring
    rw [hcast]
    field_simp
  rw [dist_comm, dist_eq_norm, ← hexp]
  have hAn : A ^ (n + 1) ≤ Real.exp (c * R ^ 2) := by
    rw [hA, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hcast : ((n + 1 : ℕ) : ℝ) = N := by
      rw [hN]
      push_cast
      ring
    rw [hcast]
    have := mul_le_mul_of_nonneg_left hu2 hnR.le
    have e : N * (2 * c * R ^ 2 / N) = 2 * c * R ^ 2 := by field_simp
    rw [e] at this
    linarith only [this]
  have hu4 : ‖u‖ ^ 4 ≤ (2 * c * R ^ 2 / N) ^ 2 := by
    have h4 : ‖u‖ ^ 4 = (‖u‖ ^ 2) ^ 2 := by ring
    rw [h4]
    exact pow_le_pow_left₀ (by positivity) hu2 2
  have hdiff := norm_cos_sub_exp_le hu1
  have hfinal : ((n + 1 : ℕ) : ℝ) * A ^ (n + 1) *
      ‖Complex.cos u - Complex.exp (-(u ^ 2 / 2))‖ ≤ D / N := by
    have hcast : ((n + 1 : ℕ) : ℝ) = N := by
      rw [hN]
      push_cast
      ring
    rw [hcast]
    calc
      N * A ^ (n + 1) * ‖Complex.cos u - Complex.exp (-(u ^ 2 / 2))‖ ≤
          N * Real.exp (c * R ^ 2) * (2 * c * R ^ 2 / N) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hAn hnR.le) (hdiff.trans hu4) (norm_nonneg _)
          (by positivity)
      _ = D / N := by
        rw [hD]
        field_simp
        ring
  have hlt : D / N < ε := by
    rw [div_lt_iff₀ hnR]
    rw [div_lt_iff₀ hε] at hn1
    linarith only [hn1]
  exact lt_of_le_of_lt (hmain.trans hfinal) hlt

/-! ## The root disc of a Jensen polynomial -/

/-- Cauchy bounds on a circle confine the roots of `R_d(H)`. -/
theorem norm_le_of_eval_jensen_eq_zero {H : ℂ → ℂ} (hH : Differentiable ℂ H) (h0 : H 0 = 1) (d : ℕ)
    {r M : ℝ} (hr : 0 < r) (hM0 : 0 ≤ M) (hM : ∀ w : ℂ, ‖w‖ = r → ‖H w‖ ≤ M) {z : ℂ}
    (hz : (jensenRev d (taylorPS H)).eval z = 0) : ‖z‖ ≤ (1 + M) * d / r := by
  by_contra hcon
  push Not at hcon
  have hS0 : 0 ≤ (1 + M) * d / r := by positivity
  have hzpos : 0 < ‖z‖ := lt_of_le_of_lt hS0 hcon
  set t : ℝ := d / (r * ‖z‖) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t * (1 + M) < 1 := by
    rw [ht, div_mul_eq_mul_div, div_lt_one (by positivity)]
    rw [div_lt_iff₀ hr] at hcon
    linarith only [hcon]
  have hlt1 : t < 1 := by nlinarith only [ht1, ht0, hM0]
  -- Taylor coefficients.
  have hcoef (i : ℕ) : ‖PowerSeries.coeff i (taylorPS H)‖ ≤ M / r ^ i := by
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le i hr
      (f := H) (c := 0) (C := M) hH.diffContOnCl (fun w hw => hM w (by simpa using hw))
    rw [taylorPS, PowerSeries.coeff_mk, norm_div, Complex.norm_natCast,
      div_le_iff₀ (by exact_mod_cast Nat.factorial_pos i)]
    calc _ ≤ _ := hcauchy
      _ = _ := by ring
  rw [jensenRev_eq_sum, eval_finsetSum, Finset.sum_range_succ'] at hz
  simp only [eval_mul, eval_C, eval_pow, eval_X] at hz
  have h00 : PowerSeries.coeff 0 (taylorPS H) = 1 := by
    rw [taylorPS, PowerSeries.coeff_mk]
    simp [h0]
  simp only [h00, Nat.descFactorial_zero, Nat.cast_one, mul_one, one_mul, Nat.sub_zero] at hz
  have hterm (i : ℕ) (hi : i ∈ Finset.range d) :
      ‖PowerSeries.coeff (i + 1) (taylorPS H) * (d.descFactorial (i + 1) : ℂ) * z ^ (d - (i + 1))‖ ≤
        ‖z‖ ^ d * (M * t ^ (i + 1)) := by
    have hle : i + 1 ≤ d := Finset.mem_range.1 hi
    have hdesc : (d.descFactorial (i + 1) : ℝ) ≤ (d : ℝ) ^ (i + 1) := by
      exact_mod_cast Nat.descFactorial_le_pow d (i + 1)
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
    have hz1 : ‖z‖ ^ d = ‖z‖ ^ (d - (i + 1)) * ‖z‖ ^ (i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have ht1' : t ^ (i + 1) = (d : ℝ) ^ (i + 1) / (r ^ (i + 1) * ‖z‖ ^ (i + 1)) := by
      rw [ht, div_pow, mul_pow]
    calc
      _ ≤ (M / r ^ (i + 1)) * (d : ℝ) ^ (i + 1) * ‖z‖ ^ (d - (i + 1)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (hcoef _) hdesc (by positivity) (by positivity)) (by positivity)
      _ = _ := by
        rw [hz1, ht1']
        field_simp
  have hsum : ‖∑ i ∈ Finset.range d, PowerSeries.coeff (i + 1) (taylorPS H) *
      (d.descFactorial (i + 1) : ℂ) * z ^ (d - (i + 1))‖ ≤
      ‖z‖ ^ d * (M * ∑ i ∈ Finset.range d, t ^ (i + 1)) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans (le_of_eq ?_))
    rw [Finset.mul_sum, Finset.mul_sum]
  have hgeom : (∑ i ∈ Finset.range d, t ^ (i + 1)) * (1 - t) ≤ t := by
    have e : (∑ i ∈ Finset.range d, t ^ (i + 1)) = t * ∑ i ∈ Finset.range d, t ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, mul_assoc, geom_sum_mul_neg]
    nlinarith only [ht0, pow_nonneg ht0 d]
  have hMt : M * ∑ i ∈ Finset.range d, t ^ (i + 1) < 1 := by
    have h1t : 0 < 1 - t := by linarith only [hlt1]
    have hs : ∑ i ∈ Finset.range d, t ^ (i + 1) ≤ t / (1 - t) := by
      rw [le_div_iff₀ h1t]
      exact hgeom
    have h2 : M * (t / (1 - t)) < 1 := by
      rw [mul_div_assoc', div_lt_one h1t]
      nlinarith only [ht1]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hs hM0) h2
  have heq : z ^ d = -∑ i ∈ Finset.range d, PowerSeries.coeff (i + 1) (taylorPS H) *
      (d.descFactorial (i + 1) : ℂ) * z ^ (d - (i + 1)) := by
    linear_combination hz
  have hnorm : ‖z‖ ^ d ≤ ‖z‖ ^ d * (M * ∑ i ∈ Finset.range d, t ^ (i + 1)) := by
    calc ‖z‖ ^ d = ‖z ^ d‖ := (norm_pow _ _).symm
      _ = _ := by rw [heq, norm_neg]
      _ ≤ _ := hsum
  have hzd : 0 < ‖z‖ ^ d := pow_pos hzpos d
  nlinarith only [hnorm, hzd, hMt]

/-! ## The tail theorem -/

theorem eval_map_ofReal_conj (t : ℝ[X]) (w : ℂ) :
    (t.map Complex.ofRealHom).eval (conj w) = conj ((t.map Complex.ofRealHom).eval w) := by
  have h : (starRingEnd ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
    ext x
    simp
  rw [eval_map, eval_map, Polynomial.hom_eval₂, h]

/-- Real form of `R_d` of a function real on the real line. -/
theorem map_jensenRev_realTaylorCoeff {G : ℂ → ℂ} (hs : ∀ w, G (conj w) = conj (G w)) (d : ℕ) :
    (jensenRev d (PowerSeries.mk (realTaylorCoeff G))).map Complex.ofRealHom =
      jensenRev d (taylorPS G) := by
  rw [jensenRev_eq_sum, jensenRev_eq_sum, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, PowerSeries.coeff_mk, taylorPS,
    PowerSeries.coeff_mk, Complex.ofRealHom_eq_coe]
  congr 2
  push_cast
  rw [ofReal_realTaylorCoeff hs, inv_mul_eq_div]

/-- **A Gaussian tail makes `R_d` real-rooted.** If `f = t` has `f(w) e^{cw²}` of size at most `M` on
`|w| = r` and `2c ≥ ((1 + M) d / r)²`, then `t(D) X^d` has only real roots. -/
theorem nonrealRootCount_diffOp_X_pow_eq_zero {t : ℝ[X]} (ht0 : t.coeff 0 = 1) (d : ℕ) {c r M : ℝ}
    (hc : 0 < c) (hr : 0 < r) (hM0 : 0 ≤ M)
    (hH : ∀ w : ℂ, ‖w‖ = r → ‖(t.map Complex.ofRealHom).eval w * Complex.exp (c * w ^ 2)‖ ≤ M)
    (hS : ((1 + M) * d / r) ^ 2 ≤ 2 * c) :
    nonrealRootCount (diffOp t (X ^ d)) = 0 := by
  set F : ℂ → ℂ := fun w => (t.map Complex.ofRealHom).eval w with hF
  have hFd : Differentiable ℂ F := Polynomial.differentiable _
  set H : ℂ → ℂ := fun w => F w * Complex.exp (c * w ^ 2) with hHdef
  have hHd : Differentiable ℂ H := hFd.mul (by fun_prop)
  have hFreal : ∀ w, F (conj w) = conj (F w) := eval_map_ofReal_conj t
  have hHreal : ∀ w, H (conj w) = conj (H w) := by
    intro w
    simp only [hHdef, map_mul, hFreal, ← Complex.exp_conj, map_pow, Complex.conj_ofReal]
  have hF0 : F 0 = 1 := by
    simp only [hF]
    rw [← coeff_zero_eq_eval_zero, coeff_map, ht0, map_one]
  have hH0 : H 0 = 1 := by simp [hHdef, hF0]
  -- The strip of `R_d(H)`.
  have hB : ∀ z, (jensenRev d (taylorPS H)).eval z = 0 → z.im ^ 2 ≤ ((1 + M) * d / r) ^ 2 := by
    intro z hz
    have h1 := norm_le_of_eval_jensen_eq_zero hHd hH0 d hr hM0 hH hz
    have h2 := Complex.abs_im_le_norm z
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h2.trans h1) 2
  -- The cosine approximants.
  let η : ℕ → ℝ := fun n => Real.sqrt (2 * c / (n + 1))
  have hηpos (n : ℕ) : 0 < η n := Real.sqrt_pos.2 (by positivity)
  have hηsq (n : ℕ) : ((n + 1 : ℕ) : ℝ) * η n ^ 2 = 2 * c := by
    simp only [η]
    rw [Real.sq_sqrt (by positivity)]
    push_cast
    field_simp
  let φ : ℕ → ℂ → ℂ := fun n w => Complex.cos ((η n : ℝ) * w) ^ (n + 1) * H w
  have hφd (n : ℕ) : Differentiable ℂ (φ n) :=
    ((Complex.differentiable_cos.comp (by fun_prop)).pow (n + 1)).mul hHd
  have hφreal (n : ℕ) : ∀ w, φ n (conj w) = conj (φ n w) := by
    intro w
    simp only [φ]
    rw [hHreal, cos_real_mul_conj, map_mul (starRingEnd ℂ) (Complex.cos ((η n : ℝ) * w) ^ (n + 1)) (H w),
      map_pow]
  have hφ0 (n : ℕ) : φ n 0 = 1 := by simp [φ, hH0]
  have hreal_roots (n : ℕ) : ∀ z, (jensenRev d (taylorPS (φ n))).eval z = 0 → z.im = 0 := by
    intro z hz
    have h1 := im_sq_le_of_cos_pow hHd hHreal hH0 d (hηpos n) hB (n + 1) z hz
    rw [hηsq n, max_eq_right (by linarith only [hS])] at h1
    exact pow_eq_zero_iff (by norm_num) |>.1 (le_antisymm h1 (sq_nonneg _))
  -- Real polynomials.
  let S : ℕ → ℝ[X] := fun n => jensenRev d (PowerSeries.mk (realTaylorCoeff (φ n)))
  have hSmap (n : ℕ) : (S n).map Complex.ofRealHom = jensenRev d (taylorPS (φ n)) :=
    map_jensenRev_realTaylorCoeff (hφreal n) d
  have hSne (n : ℕ) : S n ≠ 0 := by
    intro h
    have h1 := hSmap n
    rw [show S n = 0 from h, Polynomial.map_zero] at h1
    have hco : (jensenRev d (taylorPS (φ n))).coeff d = 1 := by
      rw [coeff_jensenRev_self, taylorPS, PowerSeries.constantCoeff_mk]
      simp [hφ0 n]
    rw [← h1, coeff_zero] at hco
    exact zero_ne_one hco
  have hScount (n : ℕ) : nonrealRootCount (S n) ≤ 0 := by
    rw [nonrealRootCount_eq, hSmap n]
    apply le_of_eq
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro z hz him
    exact him (hreal_roots n z ((mem_roots (by
      intro h
      have h1 := hSmap n
      rw [h] at h1
      exact hSne n ((Polynomial.map_eq_zero_iff Complex.ofRealHom.injective).1 h1))).1 hz))
  -- The limit symbol is `t`.
  have hcoslim := tendstoLocallyUniformly_cos_pow hc
  have hφlim : TendstoLocallyUniformly φ F atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact] at hcoslim ⊢
    intro K hK
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hHd.continuous.continuousOn
    have hC0 : 0 ≤ max C 1 := le_trans zero_le_one (le_max_right _ _)
    have hcosK := hcoslim K hK
    rw [Metric.tendstoUniformlyOn_iff] at hcosK ⊢
    intro ε hε
    have hε' : 0 < ε / (max C 1) := div_pos hε (lt_of_lt_of_le one_pos (le_max_right _ _))
    filter_upwards [hcosK _ hε'] with n hn w hw
    have h1 := hn w hw
    have hFeq : F w = Complex.exp (-(c * w ^ 2)) * H w := by
      simp only [hHdef]
      rw [mul_comm (F w), ← mul_assoc, ← Complex.exp_add]
      simp
    have hCw : ‖H w‖ ≤ max C 1 := (hC w hw).trans (le_max_left _ _)
    rw [hFeq, dist_eq_norm, ← sub_mul, norm_mul]
    rw [dist_eq_norm] at h1
    have hpos : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    calc
      _ ≤ ‖Complex.exp (-(c * w ^ 2)) - Complex.cos ((η n : ℝ) * w) ^ (n + 1)‖ * max C 1 :=
        mul_le_mul_of_nonneg_left hCw (norm_nonneg _)
      _ < ε / max C 1 * max C 1 := mul_lt_mul_of_pos_right h1 hpos
      _ = ε := div_mul_cancel₀ _ hpos.ne'
  have hcoeff (k : ℕ) : Tendsto (fun n => (PowerSeries.coeff k (taylorPS (φ n)) : ℂ)) atTop
      (𝓝 (((t.coeff k : ℝ)) : ℂ)) := by
    have h := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform isOpen_univ
      (tendstoLocallyUniformlyOn_univ.2 hφlim)
      (Eventually.of_forall fun n => (hφd n).differentiableOn) k (Set.mem_univ 0)
    have h2 := h.div_const ((k.factorial : ℂ))
    have hcoefF := congrArg (PowerSeries.coeff k) (taylorPS_polynomial (t.map Complex.ofRealHom))
    rw [taylorPS, PowerSeries.coeff_mk, Polynomial.coeff_coe, coeff_map] at hcoefF
    change Tendsto _ _ (𝓝 _) at h2
    simp only [taylorPS, PowerSeries.coeff_mk]
    have heqF : iteratedDeriv k F 0 / (k.factorial : ℂ) = ((t.coeff k : ℝ) : ℂ) := hcoefF
    rw [← heqF]
    exact h2
  have hLdeg : (diffOp t (X ^ d)).natDegree ≤ d :=
    (natDegree_diffOp_le _ _).trans (natDegree_X_pow_le d)
  have hL0 : diffOp t (X ^ d) ≠ 0 := by
    intro h
    have hco := coeff_diffOp_X_pow t (le_refl d)
    rw [h, coeff_zero] at hco
    simp only [Nat.sub_self, Nat.descFactorial_zero, Nat.cast_one, mul_one] at hco
    rw [ht0] at hco
    exact zero_ne_one hco
  have hSdeg (n : ℕ) : (S n).natDegree ≤ d := by
    simp only [S]
    rw [jensenRev]
    exact (natDegree_diffOp_le _ _).trans (natDegree_X_pow_le d)
  have hconv : TendstoLocallyUniformly (fun n z => ((S n).map Complex.ofRealHom).eval z)
      (fun z => ((diffOp t (X ^ d)).map Complex.ofRealHom).eval z) atTop := by
    refine tendstoLocallyUniformly_eval_of_coeff (D := d)
      (fun n => natDegree_map_le.trans (hSdeg n)) (natDegree_map_le.trans hLdeg) fun j => ?_
    rcases le_or_gt j d with hj | hj
    · have hSj (n : ℕ) : ((S n).map Complex.ofRealHom).coeff j =
          PowerSeries.coeff (d - j) (taylorPS (φ n)) * (d.descFactorial (d - j) : ℂ) := by
        rw [hSmap n, jensenRev_eq_sum, finsetSum_coeff, Finset.sum_eq_single (d - j)]
        · rw [coeff_C_mul_X_pow, if_pos (by omega)]
        · intro i hi hij
          rw [coeff_C_mul_X_pow, if_neg (by have := Finset.mem_range.1 hi; omega)]
        · intro h'
          exact absurd (Finset.mem_range.2 (by omega)) h'
      have hLj : ((diffOp t (X ^ d)).map Complex.ofRealHom).coeff j =
          ((t.coeff (d - j) : ℝ) : ℂ) * (d.descFactorial (d - j) : ℂ) := by
        rw [coeff_map, coeff_diffOp_X_pow t hj]
        push_cast
        simp
      simp only [hSj, hLj]
      exact (hcoeff (d - j)).mul_const _
    · have h1 : ((diffOp t (X ^ d)).map Complex.ofRealHom).coeff j = 0 :=
        coeff_eq_zero_of_natDegree_lt (natDegree_map_le.trans_lt (hLdeg.trans_lt hj))
      have h2 : ∀ n, ((S n).map Complex.ofRealHom).coeff j = 0 := fun n =>
        coeff_eq_zero_of_natDegree_lt (natDegree_map_le.trans_lt ((hSdeg n).trans_lt hj))
      simp only [h1, h2, tendsto_const_nhds_iff]
  exact Nat.le_zero.1 (nonrealRootCount_le_of_tendsto hL0 hSne hScount hconv)

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.im_sq_le_of_shift_average
#print axioms FiniteFreeProbability.tendstoLocallyUniformly_cos_pow
#print axioms FiniteFreeProbability.nonrealRootCount_diffOp_X_pow_eq_zero

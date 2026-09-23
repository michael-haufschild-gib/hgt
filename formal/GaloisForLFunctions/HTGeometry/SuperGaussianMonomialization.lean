import GaloisForLFunctions.HTGeometry.SuperGaussianNewtonPlateau
import GaloisForLFunctions.HTGeometry.ExpJetPolynomial

/-!
# Mid-plateau monomialization

On a Newton plateau of width `B` carried by the index `n`, the geometric midpoint radius
`t = e^{T + B/2}` separates the `n`-th Taylor term from every other one by a factor
`e^{-|m-n| B/2}`.  Consequently *every* fixed derivative of the entire function is, uniformly on the
circle `|z| = t`, exponentially close to the single monomial `(n)_j a_n z^{n-j}`.

* `idxDist` — the natural-number distance `|m − n|`.
* `term_le_midplateau` — the exponential mid-plateau separation.
* `tailWeight`, `tailConst` — the summable geometric weight controlling the discarded terms.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

variable {a : ℕ → ℂ}

/-! ## The index distance -/

/-- The natural-number distance `|m − n|`. -/
def idxDist (m n : ℕ) : ℕ := max m n - min m n

theorem idxDist_comm (m n : ℕ) : idxDist m n = idxDist n m := by
  unfold idxDist; rw [max_comm, min_comm]

theorem idxDist_self (n : ℕ) : idxDist n n = 0 := by simp [idxDist]

theorem idxDist_eq_sub_of_le {m n : ℕ} (h : n ≤ m) : idxDist m n = m - n := by
  simp [idxDist, max_eq_left h, min_eq_right h]

theorem idxDist_eq_sub_of_ge {m n : ℕ} (h : m ≤ n) : idxDist m n = n - m := by
  simp [idxDist, max_eq_right h, min_eq_left h]

theorem idxDist_pos {m n : ℕ} (h : m ≠ n) : 0 < idxDist m n := by
  rcases Nat.lt_or_ge m n with hlt | hge
  · rw [idxDist_eq_sub_of_ge hlt.le]; omega
  · rw [idxDist_eq_sub_of_le hge]; omega

/-- The two one-sided differences reconstruct the distance whenever the weight vanishes at `0`. -/
theorem idxDist_split (h : ℕ → ℝ) (h0 : h 0 = 0) (m n : ℕ) :
    h (idxDist m n) = h (n - m) + h (m - n) := by
  rcases Nat.lt_or_ge m n with hlt | hge
  · rw [idxDist_eq_sub_of_ge hlt.le, show m - n = 0 by omega, h0, add_zero]
  · rw [idxDist_eq_sub_of_le hge, show n - m = 0 by omega, h0, zero_add]

/-! ## Mid-plateau separation -/

/-- Terms of index at least the plateau index decay at the ratio `t/v`. -/
theorem term_le_of_centralIndex_right (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {v : ℝ} (hv : 0 < v) {n : ℕ} (hcv : centralIndex a v = n)
    {t : ℝ} (ht : 0 < t) {m : ℕ} (hm : n ≤ m) :
    ‖a m‖ * t ^ m ≤ ‖a n‖ * t ^ n * (t / v) ^ (m - n) := by
  have hmax : ‖a n‖ * v ^ n = maxTerm a v := by
    rw [← hcv]; exact term_centralIndex_eq ha hv hn₀
  have hkey : ‖a m‖ * v ^ m ≤ ‖a n‖ * v ^ n := by
    rw [hmax]; exact term_le_maxTerm ha hv m
  have hc : (0 : ℝ) < t / v := div_pos ht hv
  have hvt : v * (t / v) = t := by field_simp
  have hstep := mul_le_mul_of_nonneg_right hkey (pow_nonneg hc.le m)
  have hpow : (t / v) ^ m = (t / v) ^ n * (t / v) ^ (m - n) := by
    rw [← pow_add]; congr 1; omega
  have hL : ‖a m‖ * v ^ m * (t / v) ^ m = ‖a m‖ * t ^ m := by
    rw [mul_assoc, ← mul_pow, hvt]
  have hR : ‖a n‖ * v ^ n * (t / v) ^ m = ‖a n‖ * t ^ n * (t / v) ^ (m - n) := by
    calc ‖a n‖ * v ^ n * (t / v) ^ m
        = ‖a n‖ * (v ^ n * (t / v) ^ n) * (t / v) ^ (m - n) := by rw [hpow]; ring
      _ = ‖a n‖ * t ^ n * (t / v) ^ (m - n) := by rw [← mul_pow, hvt]
  rw [hL, hR] at hstep
  exact hstep

/-- Terms of index at most the plateau index decay at the ratio `u/t`. -/
theorem term_le_of_centralIndex_left (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {u : ℝ} (hu : 0 < u) {n : ℕ} (hcu : centralIndex a u = n)
    {t : ℝ} (ht : 0 < t) {m : ℕ} (hm : m ≤ n) :
    ‖a m‖ * t ^ m ≤ ‖a n‖ * t ^ n * (u / t) ^ (n - m) := by
  have hmax : ‖a n‖ * u ^ n = maxTerm a u := by
    rw [← hcu]; exact term_centralIndex_eq ha hu hn₀
  have hkey : ‖a m‖ * u ^ m ≤ ‖a n‖ * u ^ n := by
    rw [hmax]; exact term_le_maxTerm ha hu m
  have hc : (0 : ℝ) < t / u := div_pos ht hu
  have hut : u * (t / u) = t := by field_simp
  have hstep := mul_le_mul_of_nonneg_right hkey (pow_nonneg hc.le m)
  have hL : ‖a m‖ * u ^ m * (t / u) ^ m = ‖a m‖ * t ^ m := by
    rw [mul_assoc, ← mul_pow, hut]
  have hR : ‖a n‖ * u ^ n * (t / u) ^ m = ‖a n‖ * t ^ n * (u / t) ^ (n - m) := by
    have hpowu : u ^ n = u ^ m * u ^ (n - m) := by rw [← pow_add]; congr 1; omega
    have hpowt : t ^ n = t ^ m * t ^ (n - m) := by rw [← pow_add]; congr 1; omega
    have htne : (t : ℝ) ≠ 0 := ne_of_gt ht
    have hune : (u : ℝ) ≠ 0 := ne_of_gt hu
    rw [hpowu, hpowt, div_pow, div_pow]
    field_simp
  rw [hL, hR] at hstep
  exact hstep

/-- **Mid-plateau separation.**  At the geometric midpoint of a plateau of width `B` carried by the
index `n`, every other Taylor term is smaller by the factor `e^{-|m−n|·B/2}`. -/
theorem term_le_midplateau (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {T B : ℝ} {n : ℕ}
    (hcu : centralIndex a (Real.exp T) = n)
    (hcv : centralIndex a (Real.exp (T + B)) = n) (m : ℕ) :
    ‖a m‖ * Real.exp (T + B / 2) ^ m
      ≤ ‖a n‖ * Real.exp (T + B / 2) ^ n * Real.exp (-(B / 2) * (idxDist m n : ℝ)) := by
  have ht : (0 : ℝ) < Real.exp (T + B / 2) := Real.exp_pos _
  have hu : (0 : ℝ) < Real.exp T := Real.exp_pos _
  have hv : (0 : ℝ) < Real.exp (T + B) := Real.exp_pos _
  have hratio_r : Real.exp (T + B / 2) / Real.exp (T + B) = Real.exp (-(B / 2)) := by
    rw [← Real.exp_sub]; congr 1; ring
  have hratio_l : Real.exp T / Real.exp (T + B / 2) = Real.exp (-(B / 2)) := by
    rw [← Real.exp_sub]; congr 1; ring
  have hexp : ∀ d : ℕ, Real.exp (-(B / 2)) ^ d = Real.exp (-(B / 2) * (d : ℝ)) := by
    intro d
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rcases Nat.lt_or_ge m n with hlt | hge
  · rw [idxDist_eq_sub_of_ge hlt.le]
    have h := term_le_of_centralIndex_left ha hn₀ hu hcu ht hlt.le
    rw [hratio_l, hexp] at h
    exact h
  · rw [idxDist_eq_sub_of_le hge]
    have h := term_le_of_centralIndex_right ha hn₀ hv hcv ht hge
    rw [hratio_r, hexp] at h
    exact h

/-! ## The summable tail weight -/

/-- The geometric weight `(4k)^j e^{-k}`, forced to vanish at `k = 0`. -/
noncomputable def tailWeight (j k : ℕ) : ℝ :=
  if k = 0 then 0 else (4 * (k : ℝ)) ^ j * Real.exp (-(k : ℝ))

theorem tailWeight_nonneg (j k : ℕ) : 0 ≤ tailWeight j k := by
  unfold tailWeight
  split
  · exact le_rfl
  · positivity

theorem tailWeight_zero (j : ℕ) : tailWeight j 0 = 0 := by simp [tailWeight]

theorem tailWeight_le (j k : ℕ) : tailWeight j k ≤ (4 * (k : ℝ)) ^ j * Real.exp (-(k : ℝ)) := by
  unfold tailWeight
  split
  · positivity
  · exact le_rfl

theorem summable_tailWeight (j : ℕ) : Summable (tailWeight j) := by
  have hgeom : Summable fun k : ℕ => ((k : ℝ)) ^ j * (Real.exp (-1)) ^ k := by
    refine summable_pow_mul_geometric_of_norm_lt_one j ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-1) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
      _ = 1 := Real.exp_zero
  have hscaled : Summable fun k : ℕ => (4 : ℝ) ^ j * ((k : ℝ) ^ j * (Real.exp (-1)) ^ k) :=
    hgeom.mul_left _
  refine Summable.of_nonneg_of_le (fun k => tailWeight_nonneg j k) (fun k => ?_) hscaled
  refine le_trans (tailWeight_le j k) (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]
  ring_nf

/-- The finite constant governing the discarded terms of the `j`-th derivative. -/
noncomputable def tailConst (j : ℕ) : ℝ := 2 * (∑' k : ℕ, tailWeight j k) + 1

theorem tailConst_pos (j : ℕ) : 0 < tailConst j := by
  have h : 0 ≤ ∑' k : ℕ, tailWeight j k :=
    tsum_nonneg fun k => tailWeight_nonneg j k
  unfold tailConst; linarith

/-- **The two-sided tail sum.**  Summing the weight along the distance to a fixed index costs at
most twice the one-sided sum. -/
theorem tsum_tailWeight_idxDist_le (j i₀ : ℕ) :
    ∑' i : ℕ, tailWeight j (idxDist i i₀) ≤ 2 * ∑' k : ℕ, tailWeight j k := by
  classical
  set h : ℕ → ℝ := tailWeight j with hh
  have h0 : h 0 = 0 := tailWeight_zero j
  have hnn : ∀ k, 0 ≤ h k := fun k => tailWeight_nonneg j k
  have hsum : Summable h := summable_tailWeight j
  -- the left piece is finitely supported
  have hleftsupp : ∀ i : ℕ, i ∉ Finset.range (i₀ + 1) → h (i₀ - i) = 0 := by
    intro i hi
    have : i₀ - i = 0 := by
      simp only [Finset.mem_range, not_lt] at hi; omega
    rw [this, h0]
  have hleftsummable : Summable fun i : ℕ => h (i₀ - i) :=
    summable_of_hasFiniteSupport (Set.Finite.subset (Finset.range (i₀ + 1)).finite_toSet
      (by intro i hi; by_contra hc; exact hi (hleftsupp i (by simpa using hc))))
  have hleft : (∑' i : ℕ, h (i₀ - i)) ≤ ∑' k : ℕ, h k := by
    rw [tsum_eq_sum hleftsupp]
    have hrefl : ∑ i ∈ Finset.range (i₀ + 1), h (i₀ - i)
        = ∑ i ∈ Finset.range (i₀ + 1), h i := by
      have := Finset.sum_range_reflect h (i₀ + 1)
      simpa using this
    rw [hrefl]
    exact Summable.sum_le_tsum _ (fun i _ => hnn i) hsum
  -- the right piece is a shift
  have hrightsummable : Summable fun i : ℕ => h (i - i₀) := by
    refine (summable_nat_add_iff i₀).mp ?_
    refine hsum.congr fun k => ?_
    congr 1
    omega
  have hright : (∑' i : ℕ, h (i - i₀)) = ∑' k : ℕ, h k := by
    have hshift := Summable.sum_add_tsum_nat_add (f := fun i : ℕ => h (i - i₀)) i₀ hrightsummable
    have hzero : ∑ i ∈ Finset.range i₀, h (i - i₀) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have : i - i₀ = 0 := by simp only [Finset.mem_range] at hi; omega
      rw [this, h0]
    have hshifted : (∑' i : ℕ, h (i + i₀ - i₀)) = ∑' k : ℕ, h k := by
      refine tsum_congr fun k => ?_
      congr 1
      omega
    rw [hzero, zero_add, hshifted] at hshift
    exact hshift.symm
  have hsplit : ∀ i : ℕ, h (idxDist i i₀) = h (i₀ - i) + h (i - i₀) :=
    fun i => idxDist_split h h0 i i₀
  calc ∑' i : ℕ, h (idxDist i i₀)
      = ∑' i : ℕ, (h (i₀ - i) + h (i - i₀)) := by exact tsum_congr fun i => hsplit i
    _ = (∑' i : ℕ, h (i₀ - i)) + ∑' i : ℕ, h (i - i₀) :=
        hleftsummable.tsum_add hrightsummable
    _ ≤ (∑' k : ℕ, h k) + ∑' k : ℕ, h k := by rw [hright]; linarith [hleft]
    _ = 2 * ∑' k : ℕ, h k := by ring


theorem summable_tailWeight_idxDist (j i₀ : ℕ) :
    Summable fun i : ℕ => tailWeight j (idxDist i i₀) := by
  classical
  set h : ℕ → ℝ := tailWeight j with hh
  have h0 : h 0 = 0 := tailWeight_zero j
  have hsum : Summable h := summable_tailWeight j
  have hleftsupp : ∀ i : ℕ, i ∉ Finset.range (i₀ + 1) → h (i₀ - i) = 0 := by
    intro i hi
    have : i₀ - i = 0 := by
      simp only [Finset.mem_range, not_lt] at hi; omega
    rw [this, h0]
  have hleftsummable : Summable fun i : ℕ => h (i₀ - i) :=
    summable_of_hasFiniteSupport (Set.Finite.subset (Finset.range (i₀ + 1)).finite_toSet
      (by intro i hi; by_contra hc; exact hi (hleftsupp i (by simpa using hc))))
  have hrightsummable : Summable fun i : ℕ => h (i - i₀) := by
    refine (summable_nat_add_iff i₀).mp ?_
    refine hsum.congr fun k => ?_
    congr 1
    omega
  have hcongr : (fun i : ℕ => h (idxDist i i₀)) = fun i : ℕ => h (i₀ - i) + h (i - i₀) := by
    funext i
    exact idxDist_split h h0 i i₀
  rw [hcongr]
  exact hleftsummable.add hrightsummable

/-! ## The jets of an entire function in Taylor form -/

/-- Composing iterated derivatives adds the orders. -/
theorem iteratedDeriv_iteratedDeriv_superGaussianMonomialization (i j : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv i (iteratedDeriv j f) = iteratedDeriv (i + j) f := by
  simp only [iteratedDeriv_eq_iterate]
  rw [Function.iterate_add_apply]

/-- **The Taylor expansion of a fixed jet.**  The `j`-th derivative of an entire function is the
power series `∑ (m)_j a_m z^{m-j}`, written with the shift `m = i + j`. -/
theorem hasSum_iteratedDeriv_taylor {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a : ℕ → ℂ}
    (hcoeff : ∀ k : ℕ, iteratedDeriv k f 0 = (Nat.factorial k : ℂ) * a k) (j : ℕ) (z : ℂ) :
    HasSum (fun i : ℕ => (((i + j).descFactorial j : ℕ) : ℂ) * a (i + j) * z ^ i)
      (iteratedDeriv j f z) := by
  have hfj : Differentiable ℂ (iteratedDeriv j f) := differentiable_iteratedDeriv_of_entire hf j
  have h := Complex.hasSum_taylorSeries_of_entire hfj 0 z
  refine h.congr_fun fun i => ?_
  have hstep : iteratedDeriv i (iteratedDeriv j f) 0 = ((Nat.factorial (i + j) : ℕ) : ℂ) * a (i + j) := by
    rw [iteratedDeriv_iteratedDeriv_superGaussianMonomialization, hcoeff]
  have hfac : ((Nat.factorial i : ℕ) : ℂ) * (((i + j).descFactorial j : ℕ) : ℂ)
      = ((Nat.factorial (i + j) : ℕ) : ℂ) := by
    have hnat : Nat.factorial i * (i + j).descFactorial j = Nat.factorial (i + j) := by
      have h := Nat.factorial_mul_descFactorial (n := i + j) (k := j) (by omega)
      simpa using h
    exact_mod_cast congrArg (fun k : ℕ => (k : ℂ)) hnat
  have hine : ((Nat.factorial i : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  simp only [sub_zero, smul_eq_mul, hstep]
  field_simp
  rw [← hfac]
  ring

/-! ## The descending-factorial comparison -/

/-- A falling factorial at any index is controlled by the one at the plateau index, at the cost of
a factor `(4k)^j` in the index distance. -/
theorem descFactorial_le_mul_pow {j n m k : ℕ} (hj : 2 * j ≤ n)
    (hmk : m ≤ 2 * k * n) : m.descFactorial j ≤ n.descFactorial j * (4 * k) ^ j := by
  have hstep1 : m.descFactorial j ≤ (2 * k * n) ^ j :=
    le_trans (Nat.descFactorial_le_pow m j) (Nat.pow_le_pow_left hmk j)
  have hbase : n ≤ 2 * (n + 1 - j) := by omega
  have hstep2 : n ^ j ≤ 2 ^ j * n.descFactorial j := by
    calc n ^ j ≤ (2 * (n + 1 - j)) ^ j := Nat.pow_le_pow_left hbase j
      _ = 2 ^ j * (n + 1 - j) ^ j := by rw [mul_pow]
      _ ≤ 2 ^ j * n.descFactorial j :=
          Nat.mul_le_mul_left _ (Nat.pow_sub_le_descFactorial n j)
  calc m.descFactorial j ≤ (2 * k * n) ^ j := hstep1
    _ = 2 ^ j * k ^ j * n ^ j := by rw [mul_pow, mul_pow]
    _ ≤ 2 ^ j * k ^ j * (2 ^ j * n.descFactorial j) :=
        Nat.mul_le_mul_left _ hstep2
    _ = n.descFactorial j * (4 * k) ^ j := by
        rw [mul_pow]
        have h4 : (4 : ℕ) ^ j = 2 ^ j * 2 ^ j := by
          rw [← mul_pow]; norm_num
        rw [h4]; ring


/-! ## The monomialization estimate -/

/-- **Theorem 1 (2)–(3): mid-plateau monomialization.**  On the circle of radius `t` at the
geometric midpoint of a plateau of width `B ≥ 6` carried by an index `n ≥ 2j`, the `j`-th
derivative of the entire function differs from the single monomial `(n)_j a_n z^{n-j}` by at most
`C_j e^{-B/3}` times that monomial's size.  The constant `C_j = tailConst j` depends only on `j`. -/
theorem norm_iteratedDeriv_sub_monomial_le
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a : ℕ → ℂ}
    (hcoeff : ∀ k : ℕ, iteratedDeriv k f 0 = (Nat.factorial k : ℂ) * a k)
    {j n : ℕ} (hjn : 2 * j ≤ n) (hn : 1 ≤ n)
    {t B : ℝ} (ht : 0 < t) (hB : 6 ≤ B)
    (hsep : ∀ m : ℕ, ‖a m‖ * t ^ m
      ≤ ‖a n‖ * t ^ n * Real.exp (-(B / 2) * (idxDist m n : ℝ)))
    {z : ℂ} (hz : ‖z‖ = t) :
    ‖iteratedDeriv j f z - ((n.descFactorial j : ℕ) : ℂ) * a n * z ^ (n - j)‖
      ≤ tailConst j * Real.exp (-(B / 3)) * ((n.descFactorial j : ℕ) : ℝ) * ‖a n‖
          * t ^ (n - j) := by
  classical
  set i₀ : ℕ := n - j with hi₀def
  have hi₀j : i₀ + j = n := by omega
  set F : ℕ → ℂ := fun i => (((i + j).descFactorial j : ℕ) : ℂ) * a (i + j) * z ^ i with hFdef
  have hFsum : HasSum F (iteratedDeriv j f z) := hasSum_iteratedDeriv_taylor hf hcoeff j z
  have hFi₀ : F i₀ = ((n.descFactorial j : ℕ) : ℂ) * a n * z ^ (n - j) := by
    simp only [hFdef, hi₀def]
    rw [show n - j + j = n from by omega]
  have hupd : HasSum (Function.update F i₀ 0) (iteratedDeriv j f z - F i₀) := by
    have h := hFsum.update i₀ 0
    have hrw : (0 : ℂ) - F i₀ + iteratedDeriv j f z = iteratedDeriv j f z - F i₀ := by ring
    rw [hrw] at h
    exact h
  set M : ℝ := ((n.descFactorial j : ℕ) : ℝ) * ‖a n‖ * t ^ (n - j) * Real.exp (-(B / 3)) with hMdef
  have hMnonneg : 0 ≤ M := by
    have : (0:ℝ) ≤ t ^ (n - j) := pow_nonneg ht.le _
    positivity
  set G : ℕ → ℝ := fun i => M * tailWeight j (idxDist i i₀) with hGdef
  have hGsummable : Summable G := (summable_tailWeight_idxDist j i₀).mul_left M
  -- the pointwise majorant
  have hbound : ∀ i : ℕ, ‖Function.update F i₀ 0 i‖ ≤ G i := by
    intro i
    by_cases hii : i = i₀
    · subst hii
      simp [hGdef, idxDist_self, tailWeight_zero]
    · rw [Function.update_of_ne hii]
      set m : ℕ := i + j with hmdef
      set k : ℕ := idxDist i i₀ with hkdef
      have hk1 : 1 ≤ k := idxDist_pos hii
      have hdist : idxDist m n = k := by
        simp only [hmdef, hkdef, idxDist]
        omega
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      -- the index comparison
      have hmk : m ≤ 2 * k * n := by
        have h1 : n ≤ k * n := Nat.le_mul_of_pos_left n hk1
        have h2 : k ≤ k * n := Nat.le_mul_of_pos_right k hn
        rcases Nat.lt_or_ge i₀ i with hlt | hge
        · have hkval : k = i - i₀ := by
            rw [hkdef, idxDist_eq_sub_of_le hlt.le]
          have hmn : m = n + k := by omega
          calc m = n + k := hmn
            _ ≤ k * n + k * n := Nat.add_le_add h1 h2
            _ = 2 * k * n := by ring
        · have hmn : m ≤ n := by omega
          calc m ≤ n := hmn
            _ ≤ k * n := h1
            _ ≤ k * n + k * n := Nat.le_add_right _ _
            _ = 2 * k * n := by ring
      have hA : ((m.descFactorial j : ℕ) : ℝ)
          ≤ ((n.descFactorial j : ℕ) : ℝ) * (4 * (k : ℝ)) ^ j := by
        have hnat := descFactorial_le_mul_pow (j := j) (n := n) (m := m) (k := k) hjn hmk
        have := (Nat.cast_le (α := ℝ)).mpr hnat
        calc ((m.descFactorial j : ℕ) : ℝ)
            ≤ ((n.descFactorial j * (4 * k) ^ j : ℕ) : ℝ) := this
          _ = ((n.descFactorial j : ℕ) : ℝ) * (4 * (k : ℝ)) ^ j := by push_cast; ring
      -- the coefficient comparison
      have htj : (0 : ℝ) < t ^ j := pow_pos ht j
      have hexpk : Real.exp (-(B / 2) * (k : ℝ))
          ≤ Real.exp (-(B / 3)) * Real.exp (-(k : ℝ)) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hkR, hB]
      have hC : ‖a m‖ * t ^ i
          ≤ ‖a n‖ * t ^ (n - j) * (Real.exp (-(B / 3)) * Real.exp (-(k : ℝ))) := by
        have hsm := hsep m
        rw [hdist] at hsm
        have hsplitm : t ^ m = t ^ i * t ^ j := by rw [← pow_add]
        have hsplitn : t ^ n = t ^ (n - j) * t ^ j := by rw [← pow_add]; congr 1; omega
        rw [hsplitm, hsplitn] at hsm
        have hstep : (‖a m‖ * t ^ i) * t ^ j
            ≤ (‖a n‖ * t ^ (n - j) * Real.exp (-(B / 2) * (k : ℝ))) * t ^ j := by
          nlinarith [hsm]
        have hdiv := le_of_mul_le_mul_right hstep htj
        refine le_trans hdiv ?_
        have hnn : (0:ℝ) ≤ ‖a n‖ * t ^ (n - j) := by positivity
        nlinarith [hexpk, hnn]
      -- combine
      have hFnorm : ‖F i‖ = ((m.descFactorial j : ℕ) : ℝ) * (‖a m‖ * t ^ i) := by
        simp only [hFdef, norm_mul, norm_pow, Complex.norm_natCast, hz, hmdef]
        ring
      rw [hFnorm]
      have hnonneg1 : (0:ℝ) ≤ ((m.descFactorial j : ℕ) : ℝ) := Nat.cast_nonneg _
      have hnonneg2 : (0:ℝ) ≤ ‖a n‖ * t ^ (n - j) * (Real.exp (-(B / 3)) * Real.exp (-(k : ℝ))) := by
        have : (0:ℝ) ≤ t ^ (n - j) := pow_nonneg ht.le _
        positivity
      have hprod := mul_le_mul hA hC (by positivity) (by positivity)
      refine le_trans hprod (le_of_eq ?_)
      have htw : tailWeight j k = (4 * (k : ℝ)) ^ j * Real.exp (-(k : ℝ)) := by
        unfold tailWeight
        rw [if_neg (by omega : ¬ k = 0)]
      rw [hGdef]
      simp only [← hkdef, htw, hMdef]
      ring
  have hnormsummable : Summable fun i => ‖Function.update F i₀ 0 i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbound hGsummable
  have hle : ‖iteratedDeriv j f z - F i₀‖ ≤ ∑' i, G i := by
    rw [← hupd.tsum_eq]
    exact le_trans (norm_tsum_le_tsum_norm hnormsummable)
      (Summable.tsum_le_tsum hbound hnormsummable hGsummable)
  have hGsum : ∑' i, G i ≤ M * tailConst j := by
    have h1 : ∑' i, G i = M * ∑' i : ℕ, tailWeight j (idxDist i i₀) := by
      rw [hGdef, tsum_mul_left]
    rw [h1]
    have h2 := tsum_tailWeight_idxDist_le j i₀
    have h3 : (2 : ℝ) * (∑' k : ℕ, tailWeight j k) ≤ tailConst j := by
      unfold tailConst; linarith
    exact mul_le_mul_of_nonneg_left (le_trans h2 h3) hMnonneg
  rw [hFi₀] at hle
  refine le_trans (le_trans hle hGsum) (le_of_eq ?_)
  rw [hMdef]
  ring


/-! ## Theorem 1, assembled -/

/-- Choosing the plateau width to beat a prescribed relative error. -/
theorem exists_width_mul_exp_le {C ε : ℝ} (hCpos : 0 < C) (hε : 0 < ε) :
    ∃ B : ℝ, 6 ≤ B ∧ C * Real.exp (-(B / 3)) ≤ ε := by
  refine ⟨max 6 (3 * Real.log (C / ε)), le_max_left _ _, ?_⟩
  have hquot : 0 < C / ε := div_pos hCpos hε
  have hB3 : Real.log (C / ε) ≤ max 6 (3 * Real.log (C / ε)) / 3 := by
    have h := le_max_right (6 : ℝ) (3 * Real.log (C / ε))
    linarith
  have hexp : Real.exp (-(max 6 (3 * Real.log (C / ε)) / 3)) ≤ ε / C := by
    have h1 : Real.exp (-(max 6 (3 * Real.log (C / ε)) / 3))
        ≤ Real.exp (-Real.log (C / ε)) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-Real.log (C / ε)) = ε / C := by
      rw [Real.exp_neg, Real.exp_log hquot, inv_div]
    linarith [h1, h2.le, h2.ge]
  calc C * Real.exp (-(max 6 (3 * Real.log (C / ε)) / 3)) ≤ C * (ε / C) :=
        mul_le_mul_of_nonneg_left hexp hCpos.le
    _ = ε := by field_simp

/-- **Theorem 1, assembled: super-Gaussian decay monomializes every fixed jet.**  For every
derivative order `j`, every relative accuracy `ε` and every index bound `N`, there is a plateau
index `n ≥ N` with `a n ≠ 0` and a radius `t` on whose circle the `j`-th derivative agrees with the
single Taylor monomial `(n)_j a_n z^{n-j}` to within the relative error `ε`. -/
theorem exists_monomialization
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a : ℕ → ℂ}
    (hcoeff : ∀ k : ℕ, iteratedDeriv k f 0 = (Nat.factorial k : ℂ) * a k)
    (hSG : SuperGaussianCoeffs a) (htrans : ∀ N : ℕ, ∃ n, N ≤ n ∧ a n ≠ 0)
    (j : ℕ) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ (n : ℕ) (t : ℝ), N ≤ n ∧ 2 * j < n ∧ 0 < t ∧ a n ≠ 0 ∧
      ∀ z : ℂ, ‖z‖ = t →
        ‖iteratedDeriv j f z - ((n.descFactorial j : ℕ) : ℂ) * a n * z ^ (n - j)‖
          ≤ ε * (((n.descFactorial j : ℕ) : ℝ) * ‖a n‖ * t ^ (n - j)) := by
  classical
  have ha : EntireCoeffs a := entireCoeffs_of_superGaussian hSG
  obtain ⟨n₀, -, hn₀⟩ := htrans 0
  obtain ⟨B, hB6, hBε⟩ := exists_width_mul_exp_le (tailConst_pos j) hε
  obtain ⟨n, T, hnN, -, hTpos, hcu, hcv⟩ :=
    exists_wide_plateau hSG htrans (by linarith : (0:ℝ) < B) (max N (2 * j + 1)) 0
  have hnN' : N ≤ n := le_trans (le_max_left _ _) hnN
  have hnj : 2 * j + 1 ≤ n := le_trans (le_max_right _ _) hnN
  have hane : a n ≠ 0 := by
    rw [← hcu]; exact coeff_centralIndex_ne_zero ha (Real.exp_pos T) hn₀
  refine ⟨n, Real.exp (T + B / 2), hnN', by omega, Real.exp_pos _, hane, fun z hz => ?_⟩
  have hsep := term_le_midplateau ha hn₀ hcu hcv
  have hmain := norm_iteratedDeriv_sub_monomial_le hf hcoeff (by omega : 2 * j ≤ n)
    (by omega : 1 ≤ n) (Real.exp_pos (T + B / 2)) hB6 hsep hz
  refine le_trans hmain ?_
  · have hpos : (0:ℝ) ≤ ((n.descFactorial j : ℕ) : ℝ) * ‖a n‖ * Real.exp (T + B / 2) ^ (n - j) := by
      positivity
    calc tailConst j * Real.exp (-(B / 3)) * ((n.descFactorial j : ℕ) : ℝ) * ‖a n‖
            * Real.exp (T + B / 2) ^ (n - j)
        = (tailConst j * Real.exp (-(B / 3)))
            * (((n.descFactorial j : ℕ) : ℝ) * ‖a n‖ * Real.exp (T + B / 2) ^ (n - j)) := by ring
      _ ≤ ε * (((n.descFactorial j : ℕ) : ℝ) * ‖a n‖ * Real.exp (T + B / 2) ^ (n - j)) :=
          mul_le_mul_of_nonneg_right hBε hpos


/-! ## The falling factorial is asymptotically the power -/

/-- **`(n)_j` is `n^j` up to a relative error `j²/n`.**  Multiplied out to stay inside `ℕ`. -/
theorem pow_succ_le_descFactorial_bound (n : ℕ) :
    ∀ j : ℕ, n * n ^ j ≤ n * n.descFactorial j + j * j * n ^ j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      have hkey : n * n * n.descFactorial j
          ≤ n * ((n - j) * n.descFactorial j) + n * j * n.descFactorial j := by
        have hbase : n * n ≤ n * (n - j) + n * j := by
          rcases Nat.le_total j n with h | h
          · have hh : n * (n - j) + n * j = n * n := by
              have h1 : n - j + j = n := by omega
              calc n * (n - j) + n * j = n * (n - j + j) := by ring
                _ = n * n := by rw [h1]
            exact le_of_eq hh.symm
          · calc n * n ≤ n * j := Nat.mul_le_mul_left n h
              _ ≤ n * (n - j) + n * j := Nat.le_add_left _ _
        calc n * n * n.descFactorial j ≤ (n * (n - j) + n * j) * n.descFactorial j :=
              Nat.mul_le_mul_right _ hbase
          _ = n * ((n - j) * n.descFactorial j) + n * j * n.descFactorial j := by ring
      have hdesc : (n.descFactorial (j + 1)) = (n - j) * n.descFactorial j :=
        Nat.descFactorial_succ n j
      have hjd : n * j * n.descFactorial j ≤ (2 * j + 1) * (n * n ^ j) := by
        have h1 : n.descFactorial j ≤ n ^ j := Nat.descFactorial_le_pow n j
        calc n * j * n.descFactorial j ≤ n * j * n ^ j := Nat.mul_le_mul_left _ h1
          _ = j * (n * n ^ j) := by ring
          _ ≤ (2 * j + 1) * (n * n ^ j) := Nat.mul_le_mul_right _ (by omega)
      calc n * n ^ (j + 1) = n * (n * n ^ j) := by ring
        _ ≤ n * (n * n.descFactorial j + j * j * n ^ j) := Nat.mul_le_mul_left n ih
        _ = n * n * n.descFactorial j + j * j * (n * n ^ j) := by ring
        _ ≤ (n * ((n - j) * n.descFactorial j) + n * j * n.descFactorial j)
              + j * j * (n * n ^ j) := by
            exact Nat.add_le_add_right hkey _
        _ ≤ (n * ((n - j) * n.descFactorial j) + (2 * j + 1) * (n * n ^ j))
              + j * j * (n * n ^ j) := by
            exact Nat.add_le_add_right (Nat.add_le_add_left hjd _) _
        _ = n * n.descFactorial (j + 1) + (j + 1) * (j + 1) * n ^ (j + 1) := by
            rw [hdesc]; ring

/-- The relative defect of the falling factorial, in real form. -/
theorem descFactorial_relative_defect {n j : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ j - ((n.descFactorial j : ℕ) : ℝ) ≤ ((j : ℝ) * j / n) * (n : ℝ) ^ j := by
  have hnat := pow_succ_le_descFactorial_bound n j
  have hcast : (n : ℝ) * (n : ℝ) ^ j
      ≤ (n : ℝ) * ((n.descFactorial j : ℕ) : ℝ) + (j : ℝ) * j * (n : ℝ) ^ j := by
    exact_mod_cast (Nat.cast_le (α := ℝ)).mpr hnat
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_mul_eq_mul_div, le_div_iff₀ hnR]
  nlinarith [hcast]

/-! ## The plateau package -/

/-- **The plateau package.**  For every accuracy `δ` and smallness target `ρ` there is a single
plateau radius `t` at which the maximum term is at least `1`, the plateau index `n` is below `ρ·t`,
`t^Q` is below `ρ` times the maximum term, and every derivative of order at most `m` agrees with the
model monomial `n^j a_n z^{n-j}` to within the relative error `δ`. -/
theorem exists_monomialization_package
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a : ℕ → ℂ}
    (hcoeff : ∀ k : ℕ, iteratedDeriv k f 0 = (Nat.factorial k : ℂ) * a k)
    (hSG : SuperGaussianCoeffs a) (htrans : ∀ N : ℕ, ∃ n, N ≤ n ∧ a n ≠ 0)
    (m Q : ℕ) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    ∃ (n : ℕ) (t : ℝ), 1 ≤ t ∧ 2 * m < n ∧ a n ≠ 0 ∧
      1 ≤ ‖a n‖ * t ^ n ∧ (n : ℝ) ≤ ρ * t ∧
      t ^ Q ≤ ρ * (‖a n‖ * t ^ n) ∧
      ∀ j : ℕ, j ≤ m → ∀ z : ℂ, ‖z‖ = t →
        ‖iteratedDeriv j f z - ((n : ℂ) ^ j) * a n * z ^ (n - j)‖
          ≤ δ * ((n : ℝ) ^ j * ‖a n‖ * t ^ (n - j)) := by
  classical
  have ha : EntireCoeffs a := entireCoeffs_of_superGaussian hSG
  obtain ⟨n₀, -, hn₀⟩ := htrans 0
  obtain ⟨n₁, hn₁Q, hn₁⟩ := htrans (Q + 1)
  have hn₁pos : (0 : ℝ) < ‖a n₁‖ := norm_pos_iff.mpr hn₁
  set C : ℝ := ∑ j ∈ Finset.range (m + 1), tailConst j with hCdef
  have hCpos : 0 < C := by
    refine Finset.sum_pos (fun j _ => tailConst_pos j) ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨B, hB6, hBδ⟩ := exists_width_mul_exp_le hCpos (by linarith : (0:ℝ) < δ / 2)
  obtain ⟨Dc, hDc⟩ := centralIndex_le_of_superGaussian hSG hn₀ (one_pos)
  set T₀ : ℝ := max (max 1 (8 / ρ)) (max |Dc|
      (max (Real.log (1 / (ρ * ‖a n₁‖))) (Real.log (1 / ‖a n₁‖)))) with hT₀def
  set N : ℕ := max (2 * m + 1) (Nat.ceil (2 * (m : ℝ) ^ (2 : ℕ) / δ)) with hNdef
  obtain ⟨n, T, hnN, hTT₀, hTpos, hcu, hcv⟩ :=
    exists_wide_plateau hSG htrans (by linarith : (0:ℝ) < B) N T₀
  have hT' : T₀ ≤ T + B / 2 := by linarith
  have hT'1 : (1:ℝ) ≤ T + B / 2 :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT'
  have hT'D : |Dc| ≤ T + B / 2 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT'
  have hT'ρ : 8 / ρ ≤ T + B / 2 :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT'
  have hT'L1 : Real.log (1 / (ρ * ‖a n₁‖)) ≤ T + B / 2 :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hT'
  have hT'L2 : Real.log (1 / ‖a n₁‖) ≤ T + B / 2 :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hT'
  set t : ℝ := Real.exp (T + B / 2) with htdef
  have ht1 : (1:ℝ) ≤ t := Real.one_le_exp (by linarith)
  have htpos : (0:ℝ) < t := lt_of_lt_of_le one_pos ht1
  -- the plateau index is the central index at the midpoint radius
  have hν : centralIndex a t = n := by
    have h1 : centralIndex a (Real.exp T) ≤ centralIndex a t :=
      centralIndex_mono ha (Real.exp_pos T) (Real.exp_le_exp.mpr (by linarith)) hn₀
    have h2 : centralIndex a t ≤ centralIndex a (Real.exp (T + B)) :=
      centralIndex_mono ha (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith)) hn₀
    omega
  have hmax : ‖a n‖ * t ^ n = maxTerm a t := by
    rw [← hν]; exact term_centralIndex_eq ha htpos hn₀
  have hane : a n ≠ 0 := by rw [← hν]; exact coeff_centralIndex_ne_zero ha htpos hn₀
  have hmaxlb : ‖a n₁‖ * t ^ n₁ ≤ ‖a n‖ * t ^ n := by
    rw [hmax]; exact term_le_maxTerm ha htpos n₁
  have hn2m : 2 * m + 1 ≤ n := le_trans (le_max_left _ _) hnN
  have hnδ : 2 * (m : ℝ) ^ (2 : ℕ) / δ ≤ (n : ℝ) := by
    have h1 : Nat.ceil (2 * (m : ℝ) ^ (2 : ℕ) / δ) ≤ n := le_trans (le_max_right _ _) hnN
    have h2 : (2 * (m : ℝ) ^ (2 : ℕ) / δ) ≤ (Nat.ceil (2 * (m : ℝ) ^ (2 : ℕ) / δ) : ℝ) := Nat.le_ceil _
    have h3 : ((Nat.ceil (2 * (m : ℝ) ^ (2 : ℕ) / δ) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : (1:ℕ) ≤ n := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  -- the maximum term is at least one
  have hone : (1:ℝ) ≤ ‖a n‖ * t ^ n := by
    have hpow : t ≤ t ^ n₁ := by
      calc t = t ^ (1 : ℕ) := (pow_one t).symm
        _ ≤ t ^ n₁ := pow_le_pow_right₀ ht1 (by omega)
    have hinv : 1 / ‖a n₁‖ ≤ t := by
      calc 1 / ‖a n₁‖ = Real.exp (Real.log (1 / ‖a n₁‖)) :=
            (Real.exp_log (by positivity)).symm
        _ ≤ t := Real.exp_le_exp.mpr hT'L2
    have : (1:ℝ) ≤ ‖a n₁‖ * t := by
      rw [div_le_iff₀ hn₁pos] at hinv; linarith
    calc (1:ℝ) ≤ ‖a n₁‖ * t := this
      _ ≤ ‖a n₁‖ * t ^ n₁ := mul_le_mul_of_nonneg_left hpow hn₁pos.le
      _ ≤ ‖a n‖ * t ^ n := hmaxlb
  -- the power `t^Q` is negligible against the maximum term
  have hQ : t ^ Q ≤ ρ * (‖a n‖ * t ^ n) := by
    have hinv : 1 / (ρ * ‖a n₁‖) ≤ t := by
      calc 1 / (ρ * ‖a n₁‖) = Real.exp (Real.log (1 / (ρ * ‖a n₁‖))) :=
            (Real.exp_log (by positivity)).symm
        _ ≤ t := Real.exp_le_exp.mpr hT'L1
    have hge1 : (1:ℝ) ≤ ρ * ‖a n₁‖ * t := by
      rw [div_le_iff₀ (by positivity)] at hinv; linarith
    have hpow : t ^ (Q + 1) ≤ t ^ n₁ := pow_le_pow_right₀ ht1 (by omega)
    calc t ^ Q = 1 * t ^ Q := (one_mul _).symm
      _ ≤ (ρ * ‖a n₁‖ * t) * t ^ Q := mul_le_mul_of_nonneg_right hge1 (by positivity)
      _ = ρ * ‖a n₁‖ * t ^ (Q + 1) := by rw [pow_succ]; ring
      _ ≤ ρ * ‖a n₁‖ * t ^ n₁ := by
          have := mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ) ≤ ρ * ‖a n₁‖)
          linarith
      _ = ρ * (‖a n₁‖ * t ^ n₁) := by ring
      _ ≤ ρ * (‖a n‖ * t ^ n) := mul_le_mul_of_nonneg_left hmaxlb hρ.le
  -- the plateau index is small against the radius
  have hsmall : (n : ℝ) ≤ ρ * t := by
    have hbound := hDc (T + B / 2) (by linarith)
    rw [hν] at hbound
    have hDcdiv : Dc / (T + B / 2) ≤ |Dc| := by
      rcases le_total Dc 0 with hneg | hpos
      · exact le_trans (div_nonpos_of_nonpos_of_nonneg hneg (by linarith)) (abs_nonneg Dc)
      · rw [div_le_iff₀ (by linarith)]
        calc Dc = Dc * 1 := (mul_one Dc).symm
          _ ≤ |Dc| * (T + B / 2) :=
              mul_le_mul (le_abs_self Dc) (by linarith) zero_le_one (abs_nonneg Dc)
    have hlin : (n : ℝ) ≤ |Dc| + (T + B / 2) := by
      have h1 : (T + B / 2) / 1 = T + B / 2 := by norm_num
      rw [h1] at hbound
      linarith
    have hexpsq : (T + B / 2) ^ (2 : ℕ) / 4 ≤ t := by
      have hhalf := Real.add_one_le_exp ((T + B / 2) / 2)
      have hsq : Real.exp ((T + B / 2) / 2) * Real.exp ((T + B / 2) / 2) = t := by
        rw [← Real.exp_add, htdef]; congr 1; ring
      have hpos : (0:ℝ) < Real.exp ((T + B / 2) / 2) := Real.exp_pos _
      nlinarith [hhalf, hsq, hpos, hT'1]
    have hquad : |Dc| + (T + B / 2) ≤ ρ * ((T + B / 2) ^ (2 : ℕ) / 4) := by
      have h8 : 8 ≤ ρ * (T + B / 2) := by
        rw [div_le_iff₀ hρ] at hT'ρ; linarith
      nlinarith [hT'D, hT'1, hρ, h8]
    calc (n : ℝ) ≤ |Dc| + (T + B / 2) := hlin
      _ ≤ ρ * ((T + B / 2) ^ (2 : ℕ) / 4) := hquad
      _ ≤ ρ * t := mul_le_mul_of_nonneg_left hexpsq hρ.le
  refine ⟨n, t, ht1, by omega, hane, hone, hsmall, hQ, ?_⟩
  intro j hjm z hz
  have hjn : 2 * j ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hsep := term_le_midplateau ha hn₀ hcu hcv
  rw [← htdef] at hsep
  have hmain := norm_iteratedDeriv_sub_monomial_le hf hcoeff hjn hn1 htpos hB6 hsep hz
  set M : ℝ := (n : ℝ) ^ j * ‖a n‖ * t ^ (n - j) with hMdef
  have hMnn : (0:ℝ) ≤ M := by
    have : (0:ℝ) ≤ t ^ (n - j) := pow_nonneg htpos.le _
    rw [hMdef]; positivity
  have hnnaz : (0:ℝ) ≤ ‖a n‖ * t ^ (n - j) := by
    have : (0:ℝ) ≤ t ^ (n - j) := pow_nonneg htpos.le _
    positivity
  -- the tail constant part
  have hrhs : tailConst j * Real.exp (-(B / 3)) * ((n.descFactorial j : ℕ) : ℝ) * ‖a n‖
      * t ^ (n - j) ≤ (δ / 2) * M := by
    have h1 : tailConst j ≤ C := by
      rw [hCdef]
      exact Finset.single_le_sum (f := fun i => tailConst i)
        (fun i _ => (tailConst_pos i).le) (Finset.mem_range.mpr (by omega))
    have h2 : ((n.descFactorial j : ℕ) : ℝ) ≤ (n : ℝ) ^ j := by
      have hnat := Nat.descFactorial_le_pow n j
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      calc ((n.descFactorial j : ℕ) : ℝ) ≤ ((n ^ j : ℕ) : ℝ) := this
        _ = (n : ℝ) ^ j := by push_cast; ring
    have hE : (0:ℝ) < Real.exp (-(B / 3)) := Real.exp_pos _
    calc tailConst j * Real.exp (-(B / 3)) * ((n.descFactorial j : ℕ) : ℝ) * ‖a n‖ * t ^ (n - j)
        = (tailConst j * Real.exp (-(B / 3)))
            * (((n.descFactorial j : ℕ) : ℝ) * (‖a n‖ * t ^ (n - j))) := by ring
      _ ≤ (C * Real.exp (-(B / 3))) * ((n : ℝ) ^ j * (‖a n‖ * t ^ (n - j))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right h1 hE.le)
            (mul_le_mul_of_nonneg_right h2 hnnaz) (by positivity) (by positivity)
      _ ≤ (δ / 2) * ((n : ℝ) ^ j * (‖a n‖ * t ^ (n - j))) :=
          mul_le_mul_of_nonneg_right hBδ (by positivity)
      _ = (δ / 2) * M := by rw [hMdef]; ring
  -- the falling-factorial correction
  have hcorr : ‖((n.descFactorial j : ℕ) : ℂ) * a n * z ^ (n - j)
      - ((n : ℂ) ^ j) * a n * z ^ (n - j)‖ ≤ (δ / 2) * M := by
    have hid : ((n.descFactorial j : ℕ) : ℂ) * a n * z ^ (n - j)
        - ((n : ℂ) ^ j) * a n * z ^ (n - j)
        = (((n.descFactorial j : ℕ) : ℂ) - (n : ℂ) ^ j) * (a n * z ^ (n - j)) := by ring
    have hnorm : ‖(((n.descFactorial j : ℕ) : ℂ) - (n : ℂ) ^ j)‖
        = (n : ℝ) ^ j - ((n.descFactorial j : ℕ) : ℝ) := by
      have hc : ((n.descFactorial j : ℕ) : ℂ) - (n : ℂ) ^ j
          = ((((n.descFactorial j : ℕ) : ℝ) - (n : ℝ) ^ j : ℝ) : ℂ) := by push_cast; ring
      have hle : ((n.descFactorial j : ℕ) : ℝ) ≤ (n : ℝ) ^ j := by
        have hnat := Nat.descFactorial_le_pow n j
        have := (Nat.cast_le (α := ℝ)).mpr hnat
        calc ((n.descFactorial j : ℕ) : ℝ) ≤ ((n ^ j : ℕ) : ℝ) := this
          _ = (n : ℝ) ^ j := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have hdefect := descFactorial_relative_defect (n := n) (j := j) (by omega)
    have hratio : (j : ℝ) * j / n ≤ δ / 2 := by
      have hjm' : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
      have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      have hnum : (j : ℝ) * j ≤ (m : ℝ) ^ (2 : ℕ) := by
        have hmm := mul_le_mul hjm' hjm' hj0 (le_trans hj0 hjm')
        calc (j : ℝ) * j ≤ (m : ℝ) * (m : ℝ) := hmm
          _ = (m : ℝ) ^ (2 : ℕ) := by ring
      have hmain : 2 * (m : ℝ) ^ (2 : ℕ) ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hnδ
      rw [div_le_iff₀ hnpos]
      linarith [hnum, hmain]
    rw [hid, norm_mul, hnorm, norm_mul, norm_pow, hz]
    have hstep : (n : ℝ) ^ j - ((n.descFactorial j : ℕ) : ℝ) ≤ (δ / 2) * (n : ℝ) ^ j := by
      have hpow : (0:ℝ) ≤ (n : ℝ) ^ j := by positivity
      have h2 := mul_le_mul_of_nonneg_right hratio hpow
      linarith [hdefect, h2]
    calc ((n : ℝ) ^ j - ((n.descFactorial j : ℕ) : ℝ)) * (‖a n‖ * t ^ (n - j))
        ≤ ((δ / 2) * (n : ℝ) ^ j) * (‖a n‖ * t ^ (n - j)) :=
          mul_le_mul_of_nonneg_right hstep hnnaz
      _ = (δ / 2) * M := by rw [hMdef]; ring
  have hsplit : ‖iteratedDeriv j f z - ((n : ℂ) ^ j) * a n * z ^ (n - j)‖
      ≤ ‖iteratedDeriv j f z - ((n.descFactorial j : ℕ) : ℂ) * a n * z ^ (n - j)‖
        + ‖((n.descFactorial j : ℕ) : ℂ) * a n * z ^ (n - j)
            - ((n : ℂ) ^ j) * a n * z ^ (n - j)‖ := by
    have hid : iteratedDeriv j f z - ((n : ℂ) ^ j) * a n * z ^ (n - j)
        = (iteratedDeriv j f z - ((n.descFactorial j : ℕ) : ℂ) * a n * z ^ (n - j))
          + (((n.descFactorial j : ℕ) : ℂ) * a n * z ^ (n - j)
            - ((n : ℂ) ^ j) * a n * z ^ (n - j)) := by ring
    rw [hid]
    exact norm_add_le _ _
  calc ‖iteratedDeriv j f z - ((n : ℂ) ^ j) * a n * z ^ (n - j)‖
      ≤ ‖iteratedDeriv j f z - ((n.descFactorial j : ℕ) : ℂ) * a n * z ^ (n - j)‖
        + ‖((n.descFactorial j : ℕ) : ℂ) * a n * z ^ (n - j)
            - ((n : ℂ) ^ j) * a n * z ^ (n - j)‖ := hsplit
    _ ≤ (δ / 2) * M + (δ / 2) * M := add_le_add (le_trans hmain hrhs) hcorr
    _ = δ * M := by ring

end GaloisForLFunctions.HTGeometry

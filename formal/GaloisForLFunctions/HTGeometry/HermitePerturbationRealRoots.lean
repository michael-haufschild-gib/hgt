import GaloisForLFunctions.HTGeometry.LaguerreShiftSplits
import GaloisForLFunctions.HTGeometry.HermiteGaussianMomentBounds
import GaloisForLFunctions.HTGeometry.RealRootedCoefficientLimit

/-!
# Gaussian shifts and perturbed Hermite polynomials

**Gaussian shift** (`splits_gaussShift`).  For a real polynomial `p` that splits over `ℝ` and
`β ≥ 0`, the Gaussian shift `X·p − β·p′` splits over `ℝ`.  The Gaussian gauge `e^{−x²/(2β)} p(x)`
has derivative `−β⁻¹ e^{−x²/(2β)} (X·p − β·p′)(x)` (`hasDerivAt_gaussGauge`).  Rolle's theorem gives
a root of the shift between consecutive roots of `p`, and a root to the right of the largest root,
because the gauge vanishes at `+∞` (`exists_root_gaussShift_gt`); multiplicities drop by at most one.
So the shift has at least `deg p` real roots, and a real polynomial of degree `deg p + 1` cannot miss
exactly one root (`natDegree_ne_card_roots_succ`).

**Hermite polynomials** (`splits_hermiteReal`).  `He_{n+1} = X·He_n − He_n′` is the Gaussian shift at
`β = 1`, so every `He_n` splits over `ℝ`.

**Perturbed Hermite polynomials: the threshold law.**  For real `c` put `P = He_{m+2} + c·He_m`.
`P` is real-rooted iff `c ≤ 2j + 1` when `m = 2j` (`splits_hermiteReal_add_smul_iff_even`) and iff
`c ≤ 2j + 3` when `m = 2j + 1` (`splits_hermiteReal_add_smul_iff_odd`).

* If `c ≤ m + 1`, `P` is the Gaussian shift of `He_{m+1}` at `β = (m+1−c)/(m+1)`, since
  `He′_{m+1} = (m+1)He_m` (`splits_hermiteReal_add_smul_of_le`).
* Odd window `m + 1 < c < m + 2` (`splits_hermiteReal_add_smul_odd_window`).  `H = He_{m+1}` is even
  with `H(0) ≠ 0` and simple zeros (`nodup_roots_hermiteReal`).  `P` is odd, has the sign of `H(0)`
  just right of `0` (`P′(0) = H(0)(m + 2 − c)`) and the opposite sign at the least positive zero `x₊`
  of `H` (`P(x₊) = (c − m − 1)He_m(x₊)`, `H′(x₊) = (m+1)He_m(x₊)`).  So the middle gap `(−x₊, x₊)`
  carries three zeros `0, ±r`, and Rolle's theorem for the gauge of the Gaussian shift gives one in
  each other gap: `m + 2` distinct real zeros.  The endpoint `c = m + 2` follows by coefficientwise
  limits (`splits_hermiteReal_add_smul_odd_endpoint`).
* Beyond the threshold `P` vanishes at some `iy`, `y > 0`
  (`exists_imaginary_root_hermiteReal_add_smul`).  On the imaginary axis `He_n(iy) = iⁿ h_n(y)` with
  `h_0 = 1`, `h_1 = y`, `h_{n+2} = y h_{n+1} + (n+1) h_n` (`hermiteI`, `aeval_I_mul_hermite`), so
  `P(iy) = i^m F(y)` with `F = (c − m − 1)h_m − y h_{m+1}`; `F` is positive at (or, for odd `m`, just
  right of) `0` and negative for large `y`.

Under `e^{−tD²}zⁿ = (2t)^{n/2} He_n(z/√(2t))` and `c = b²/(2t)`, the heat flow of `z^m(z² + b²)` is
real-rooted exactly for `t ≥ b²/(2(m+1))` when `m` is even and exactly for `t ≥ b²/(2(m+2))` when
`m` is odd.
-/

open Polynomial Filter Topology Set Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The Gaussian shift -/

/-- The Gaussian shift `X·p − β·p′`. -/
def gaussShift (β : ℝ) (p : ℝ[X]) : ℝ[X] := X * p - C β * derivative p

@[simp] theorem eval_gaussShift (β : ℝ) (p : ℝ[X]) (x : ℝ) :
    (gaussShift β p).eval x = x * p.eval x - β * (derivative p).eval x := by
  simp [gaussShift]

/-- The Gaussian gauge `e^{−x²/(2β)} p(x)`. -/
def gaussGauge (β : ℝ) (p : ℝ[X]) (x : ℝ) : ℝ := Real.exp (-(x ^ 2 / (2 * β))) * p.eval x

theorem continuous_gaussGauge (β : ℝ) (p : ℝ[X]) : Continuous (gaussGauge β p) := by
  unfold gaussGauge
  fun_prop

theorem hasDerivAt_gaussGauge {β : ℝ} (hβ : β ≠ 0) (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (gaussGauge β p)
      (-(β⁻¹ * Real.exp (-(x ^ 2 / (2 * β)))) * (gaussShift β p).eval x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / (2 * β))) (-(x / β)) x := by
    have h := ((hasDerivAt_pow 2 x).div_const (2 * β)).neg
    refine h.congr_deriv ?_
    rw [Nat.cast_ofNat, show 2 - 1 = 1 from rfl, pow_one, mul_div_mul_left x β two_ne_zero]
  have hmul : HasDerivAt (gaussGauge β p)
      (Real.exp (-(x ^ 2 / (2 * β))) * -(x / β) * p.eval x
        + Real.exp (-(x ^ 2 / (2 * β))) * (derivative p).eval x) x :=
    h1.exp.mul (p.hasDerivAt x)
  refine hmul.congr_deriv ?_
  rw [eval_gaussShift]
  field_simp
  ring

theorem gaussShift_eval_eq_zero_of_mul {β : ℝ} (hβ : β ≠ 0) {p : ℝ[X]} {c : ℝ}
    (h : -(β⁻¹ * Real.exp (-(c ^ 2 / (2 * β)))) * (gaussShift β p).eval c = 0) :
    (gaussShift β p).eval c = 0 :=
  (mul_eq_zero.mp h).resolve_left
    (neg_ne_zero.mpr (mul_ne_zero (inv_ne_zero hβ) (Real.exp_ne_zero _)))

/-- Between two roots of `p` there is a root of the Gaussian shift. -/
theorem exists_root_gaussShift_of_lt {β : ℝ} (hβ : β ≠ 0) {p : ℝ[X]} {u v : ℝ} (huv : u < v)
    (hu : p.eval u = 0) (hv : p.eval v = 0) :
    ∃ c ∈ Ioo u v, (gaussShift β p).eval c = 0 := by
  obtain ⟨c, hc, hd⟩ := exists_hasDerivAt_eq_zero huv (continuous_gaussGauge β p).continuousOn
    (by simp [gaussGauge, hu, hv]) (fun x _ => hasDerivAt_gaussGauge hβ p x)
  exact ⟨c, hc, gaussShift_eval_eq_zero_of_mul hβ hd⟩

/-- For `β > 0` the Gaussian gauge tends to `0` at `+∞`. -/
theorem tendsto_gaussGauge_atTop {β : ℝ} (hβ : 0 < β) (p : ℝ[X]) :
    Tendsto (gaussGauge β p) atTop (𝓝 0) := by
  have h2β : (0 : ℝ) < 2 * β := by positivity
  have hterm : ∀ i : ℕ, Tendsto (fun y : ℝ => y ^ i * Real.exp (-(y / (2 * β)))) atTop (𝓝 0) := by
    intro i
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero i).comp
      (tendsto_id.atTop_div_const h2β)).const_mul ((2 * β) ^ i)
    rw [mul_zero] at h
    refine h.congr fun y => ?_
    simp only [Function.comp, id, div_pow]
    field_simp
  set N := p.natDegree + 1
  have hsum : Tendsto (fun y : ℝ =>
      ∑ i ∈ Finset.range N, p.coeff i * (y ^ i * Real.exp (-(y / (2 * β))))) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range N) fun i _ => (hterm i).const_mul (p.coeff i)
  refine squeeze_zero_norm' ?_ (by simpa using hsum.norm)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  have hsplit : Real.exp (-(y ^ 2 / (2 * β)))
      = Real.exp (-(y / (2 * β))) * Real.exp (-((y ^ 2 - y) / (2 * β))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heq : gaussGauge β p y = (∑ i ∈ Finset.range N,
      p.coeff i * (y ^ i * Real.exp (-(y / (2 * β))))) * Real.exp (-((y ^ 2 - y) / (2 * β))) := by
    rw [gaussGauge, eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul, hsplit]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hle : ‖Real.exp (-((y ^ 2 - y) / (2 * β)))‖ ≤ 1 := by
    rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_one_iff]
    have h0 : 0 ≤ y ^ 2 - y := by nlinarith
    have h1 : 0 ≤ (y ^ 2 - y) / (2 * β) := div_nonneg h0 h2β.le
    linarith
  rw [heq, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hle

/-- To the right of the largest root of `p` there is a root of the Gaussian shift. -/
theorem exists_root_gaussShift_gt {β : ℝ} (hβ : 0 < β) {p : ℝ[X]} {a : ℝ} (ha : p.eval a = 0)
    (hgt : ∀ x, a < x → p.eval x ≠ 0) :
    ∃ c, a < c ∧ (gaussShift β p).eval c = 0 := by
  set f := gaussGauge β p with hf
  have hfa : f a = 0 := by simp [hf, gaussGauge, ha]
  set s := f (a + 1) with hs
  have hs0 : s ≠ 0 := mul_ne_zero (Real.exp_ne_zero _) (hgt _ (by linarith))
  have hs2 : 0 < s ^ 2 := by positivity
  have hlim : Tendsto (fun y => s * f y) atTop (𝓝 0) := by
    simpa using (tendsto_gaussGauge_atTop hβ p).const_mul s
  obtain ⟨z, hz2, hz1⟩ :=
    ((hlim.eventually_lt_const hs2).and (eventually_gt_atTop (a + 1))).exists
  have hcont : ContinuousOn (fun y => s * f y) (Icc a z) :=
    (continuous_const.mul (continuous_gaussGauge β p)).continuousOn
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by linarith)) hcont
  have hge : s ^ 2 ≤ s * f c := by
    have h := hmax (show a + 1 ∈ Icc a z from ⟨by linarith, hz1.le⟩)
    simp only [Set.mem_setOf_eq] at h
    rw [sq]
    exact h
  have hca : c ≠ a := by
    rintro rfl
    rw [hfa, mul_zero] at hge
    linarith
  have hcz : c ≠ z := by
    rintro rfl
    linarith
  have hcI : c ∈ Ioo a z := ⟨lt_of_le_of_ne hc.1 (Ne.symm hca), lt_of_le_of_ne hc.2 hcz⟩
  have hloc : IsLocalMax (fun y => s * f y) c := hmax.isLocalMax (Icc_mem_nhds hcI.1 hcI.2)
  have h0 := hloc.hasDerivAt_eq_zero ((hasDerivAt_gaussGauge hβ.ne' p c).const_mul s)
  exact ⟨c, hcI.1, gaussShift_eval_eq_zero_of_mul hβ.ne' ((mul_eq_zero.mp h0).resolve_left hs0)⟩

/-- The multiplicity of a root of `p` in the Gaussian shift drops by at most one. -/
theorem le_rootMultiplicity_gaussShift {β : ℝ} {p : ℝ[X]} (hp : p ≠ 0)
    (hq : gaussShift β p ≠ 0) (x : ℝ) :
    rootMultiplicity x p - 1 ≤ rootMultiplicity x (gaussShift β p) := by
  classical
  set m : ℕ := rootMultiplicity x p with hm
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  rw [le_rootMultiplicity_iff hq]
  have hdvd_p : ((X - C x) ^ (m - 1) : ℝ[X]) ∣ p :=
    dvd_trans (pow_dvd_pow _ (by omega)) (pow_rootMultiplicity_dvd p x)
  have hroot : p.IsRoot x := by
    rw [← rootMultiplicity_pos hp]
    omega
  have hdvd_d : ((X - C x) ^ (m - 1) : ℝ[X]) ∣ derivative p := by
    have hd0 : derivative p ≠ 0 := by
      intro h0
      have hdeg : p.natDegree = 0 := Polynomial.derivative_eq_zero.1 h0
      have hpc := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      rw [hpc] at hroot
      rw [Polynomial.IsRoot, Polynomial.eval_C] at hroot
      exact hp (by rw [hpc, hroot, map_zero])
    rw [← le_rootMultiplicity_iff hd0, derivative_rootMultiplicity_of_root hroot]
  exact dvd_sub (Dvd.dvd.mul_left hdvd_p _) (Dvd.dvd.mul_left hdvd_d _)

theorem natDegree_gaussShift {β : ℝ} {p : ℝ[X]} (hp : p ≠ 0) :
    (gaussShift β p).natDegree = p.natDegree + 1 := by
  have h1 : (X * p).natDegree = p.natDegree + 1 := natDegree_X_mul hp
  have h2 : (C β * derivative p).natDegree < (X * p).natDegree := by
    rw [h1]
    calc (C β * derivative p).natDegree ≤ (derivative p).natDegree := natDegree_C_mul_le _ _
      _ ≤ p.natDegree - 1 := natDegree_derivative_le p
      _ < p.natDegree + 1 := by omega
  rw [gaussShift, natDegree_sub_eq_left_of_natDegree_lt h2, h1]

theorem gaussShift_ne_zero {β : ℝ} {p : ℝ[X]} (hp : p ≠ 0) : gaussShift β p ≠ 0 := by
  intro h
  have := natDegree_gaussShift (β := β) hp
  rw [h, natDegree_zero] at this
  omega

/-- The distinct roots of `p` are at most the new distinct roots of the Gaussian shift. -/
theorem card_roots_toFinset_le_gaussShift_sdiff {β : ℝ} (hβ : 0 < β) {p : ℝ[X]} (hp : p ≠ 0) :
    p.roots.toFinset.card ≤ ((gaussShift β p).roots.toFinset \ p.roots.toFinset).card := by
  classical
  have hq := gaussShift_ne_zero (β := β) hp
  set S := p.roots.toFinset with hS
  set T := (gaussShift β p).roots.toFinset with hT
  have memS : ∀ x, x ∈ S ↔ p.eval x = 0 := fun x => by
    rw [hS, Multiset.mem_toFinset, mem_roots hp, IsRoot.def]
  have memT : ∀ x, x ∈ T ↔ (gaussShift β p).eval x = 0 := fun x => by
    rw [hT, Multiset.mem_toFinset, mem_roots hq, IsRoot.def]
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hSe, Finset.card_empty]
    exact Nat.zero_le _
  set a := S.max' hSne with ha
  have hpa : p.eval a = 0 := (memS a).1 (S.max'_mem hSne)
  have hgt : ∀ x, a < x → p.eval x ≠ 0 := fun x hx h0 =>
    absurd (S.le_max' x ((memS x).2 h0)) (not_le.mpr hx)
  obtain ⟨c, hac, hc⟩ := exists_root_gaussShift_gt hβ hpa hgt
  have hcT : c ∈ T := (memT c).2 hc
  have hcS : c ∉ S := fun h => absurd (S.le_max' c h) (not_le.mpr hac)
  have hinter : S.card ≤ (T.erase c \ S).card + 1 := by
    refine Finset.card_le_sdiff_of_interleaved fun x hx y hy hxy _ => ?_
    obtain ⟨z, hz1, hz2⟩ := exists_root_gaussShift_of_lt hβ.ne' hxy ((memS x).1 hx) ((memS y).1 hy)
    have hya : y ≤ a := S.le_max' y hy
    refine ⟨z, Finset.mem_erase.mpr ⟨fun hzc => ?_, (memT z).2 hz2⟩, hz1.1, hz1.2⟩
    rw [hzc] at hz1
    linarith [hz1.2]
  have hcard : (T.erase c \ S).card + 1 = (T \ S).card := by
    rw [Finset.erase_sdiff_comm, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hcT, hcS⟩)]
    have : 0 < (T \ S).card := Finset.card_pos.mpr ⟨c, Finset.mem_sdiff.mpr ⟨hcT, hcS⟩⟩
    omega
  omega

/-- Counted with multiplicity, the Gaussian shift has at least as many real roots as `p`. -/
theorem card_roots_le_gaussShift {β : ℝ} (hβ : 0 < β) {p : ℝ[X]} (hp : p ≠ 0) :
    Multiset.card p.roots ≤ Multiset.card (gaussShift β p).roots := by
  classical
  have hq := gaussShift_ne_zero (β := β) hp
  calc
    Multiset.card p.roots = ∑ x ∈ p.roots.toFinset, p.roots.count x :=
      (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x ∈ p.roots.toFinset, (p.roots.count x - 1 + 1) :=
      (Eq.symm <| Finset.sum_congr rfl fun _ hx => tsub_add_cancel_of_le <|
        Nat.succ_le_iff.2 <| Multiset.count_pos.2 <| Multiset.mem_toFinset.1 hx)
    _ = (∑ x ∈ p.roots.toFinset, (p.rootMultiplicity x - 1)) + p.roots.toFinset.card := by
      simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones, count_roots]
    _ ≤ (∑ x ∈ p.roots.toFinset, (gaussShift β p).rootMultiplicity x) +
          ((gaussShift β p).roots.toFinset \ p.roots.toFinset).card :=
      add_le_add
        (Finset.sum_le_sum fun _ _ => le_rootMultiplicity_gaussShift hp hq _)
        (card_roots_toFinset_le_gaussShift_sdiff hβ hp)
    _ ≤ (∑ x ∈ p.roots.toFinset, (gaussShift β p).roots.count x) +
          (∑ x ∈ (gaussShift β p).roots.toFinset \ p.roots.toFinset,
            (gaussShift β p).roots.count x) := by
      simp only [← count_roots, Finset.card_eq_sum_ones]
      gcongr with x hx
      rw [Nat.succ_le_iff, Multiset.count_pos, ← Multiset.mem_toFinset]
      exact (Finset.mem_sdiff.1 hx).1
    _ = Multiset.card (gaussShift β p).roots := by
      rw [← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_self_eq_union, ← Multiset.toFinset_sum_count_eq,
        ← Finset.sum_subset Finset.subset_union_right]
      intro x _ hx₂
      simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx₂

/-- **The Gaussian shift preserves real-rootedness.**  If `p` splits over `ℝ` and `β ≥ 0`, so does
`X·p − β·p′`. -/
theorem splits_gaussShift {p : ℝ[X]} (hp : p.Splits) {β : ℝ} (hβ : 0 ≤ β) :
    (gaussShift β p).Splits := by
  classical
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [show gaussShift β 0 = 0 by simp [gaussShift]]
    exact Splits.of_natDegree_le_one (by simp)
  rcases hβ.eq_or_lt with rfl | hβ'
  · rw [show gaussShift 0 p = X * p by simp [gaussShift]]
    exact Splits.X.mul hp
  have hq := gaussShift_ne_zero (β := β) hp0
  have hdeg := natDegree_gaussShift (β := β) hp0
  have hlow := card_roots_le_gaussShift hβ' hp0
  rw [splits_iff_card_roots] at hp ⊢
  have hupper := card_roots' (gaussShift β p)
  have hne := natDegree_ne_card_roots_succ hq
  omega

/-! ## Hermite polynomials -/

/-- The probabilists' Hermite polynomial `He_n` over `ℝ`. -/
abbrev hermiteReal (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

theorem hermiteReal_succ (n : ℕ) : hermiteReal (n + 1) = gaussShift 1 (hermiteReal n) := by
  simp only [hermiteReal, gaussShift, hermite_succ, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.derivative_map, map_one, one_mul]

theorem derivative_hermiteReal_succ (n : ℕ) :
    derivative (hermiteReal (n + 1)) = C ((n : ℝ) + 1) * hermiteReal n := by
  rw [hermiteReal, Polynomial.derivative_map, derivative_hermite_add_one, Polynomial.map_mul]
  simp [hermiteReal, C_add]

/-- **Hermite polynomials are real-rooted.** -/
theorem splits_hermiteReal (n : ℕ) : (hermiteReal n).Splits := by
  induction n with
  | zero => simp [hermiteReal, hermite_zero]
  | succ n ih =>
    rw [hermiteReal_succ]
    exact splits_gaussShift ih zero_le_one

/-- `He_{m+2} + c·He_m` is the Gaussian shift of `He_{m+1}` at `β = (m+1−c)/(m+1)`. -/
theorem hermiteReal_add_smul_eq_gaussShift (m : ℕ) (c : ℝ) :
    hermiteReal (m + 2) + C c * hermiteReal m
      = gaussShift (((m : ℝ) + 1 - c) / ((m : ℝ) + 1)) (hermiteReal (m + 1)) := by
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  have h1 : C (((m : ℝ) + 1 - c) / ((m : ℝ) + 1)) * (C ((m : ℝ) + 1) * hermiteReal m)
      = (C ((m : ℝ) + 1) - C c) * hermiteReal m := by
    rw [← mul_assoc, ← C_mul, ← C_sub]
    congr 2
    field_simp
  rw [hermiteReal_succ (m + 1), gaussShift, gaussShift, derivative_hermiteReal_succ, h1, C_1, one_mul]
  ring

/-- **Below the threshold the perturbed Hermite polynomial is real-rooted.**  If `c ≤ m + 1`, then
`He_{m+2} + c·He_m` splits over `ℝ`. -/
theorem splits_hermiteReal_add_smul_of_le {m : ℕ} {c : ℝ} (hc : c ≤ (m : ℝ) + 1) :
    (hermiteReal (m + 2) + C c * hermiteReal m).Splits := by
  rw [hermiteReal_add_smul_eq_gaussShift]
  exact splits_gaussShift (splits_hermiteReal (m + 1)) (div_nonneg (by linarith) (by positivity))

/-! ## The imaginary axis -/

/-- The imaginary-axis companions of the Hermite polynomials: `h_0 = 1`, `h_1 = X`,
`h_{n+2} = X·h_{n+1} + (n+1)·h_n`, so that `He_n(iy) = iⁿ h_n(y)`. -/
def hermiteI : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => X * hermiteI (n + 1) + C ((n : ℝ) + 1) * hermiteI n

theorem hermiteI_add_two (n : ℕ) :
    hermiteI (n + 2) = X * hermiteI (n + 1) + C ((n : ℝ) + 1) * hermiteI n := rfl

theorem eval_hermiteI_add_two (n : ℕ) (y : ℝ) :
    (hermiteI (n + 2)).eval y = y * (hermiteI (n + 1)).eval y + ((n : ℝ) + 1) * (hermiteI n).eval y := by
  rw [hermiteI_add_two]
  simp

/-- `He_{n+2}(z) = z He_{n+1}(z) − (n+1) He_n(z)` at complex points. -/
theorem aeval_hermite_add_two_complex (n : ℕ) (z : ℂ) :
    aeval z (hermite (n + 2)) = z * aeval z (hermite (n + 1)) - ((n : ℂ) + 1) * aeval z (hermite n) := by
  rw [hermite_succ (n + 1), map_sub, map_mul, aeval_X, derivative_hermite_add_one, map_mul]
  simp

/-- **`He_n(iy) = iⁿ h_n(y)`.** -/
theorem aeval_I_mul_hermite (n : ℕ) (y : ℝ) :
    aeval (I * (y : ℂ)) (hermite n) = I ^ n * (((hermiteI n).eval y : ℝ) : ℂ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hermite_zero, hermiteI]
  | one => simp [hermiteI]
  | more n ih₀ ih₁ =>
    rw [aeval_hermite_add_two_complex, ih₀, ih₁, eval_hermiteI_add_two]
    push_cast
    linear_combination (-((n : ℂ) + 1) * (((hermiteI n).eval y : ℝ) : ℂ) * I ^ n) * I_sq

theorem eval_hermiteI_nonneg {y : ℝ} (hy : 0 ≤ y) (n : ℕ) : 0 ≤ (hermiteI n).eval y := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hermiteI]
  | one => simpa [hermiteI] using hy
  | more n ih₀ ih₁ =>
    rw [eval_hermiteI_add_two]
    positivity

theorem eval_hermiteI_pos {y : ℝ} (hy : 0 < y) (n : ℕ) : 0 < (hermiteI n).eval y := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hermiteI]
  | one => simpa [hermiteI] using hy
  | more n ih₀ ih₁ =>
    rw [eval_hermiteI_add_two]
    positivity

theorem eval_hermiteI_even_pos {y : ℝ} (hy : 0 ≤ y) (j : ℕ) : 0 < (hermiteI (2 * j)).eval y := by
  induction j with
  | zero => simp [hermiteI]
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, eval_hermiteI_add_two]
    have := eval_hermiteI_nonneg hy (2 * j + 1)
    positivity

theorem mul_eval_hermiteI_le_succ {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    y * (hermiteI n).eval y ≤ (hermiteI (n + 1)).eval y := by
  rcases n with _ | n
  · simp [hermiteI]
  · rw [eval_hermiteI_add_two]
    have := eval_hermiteI_nonneg hy n
    nlinarith

theorem derivative_hermiteI_succ (n : ℕ) :
    derivative (hermiteI (n + 1)) = C ((n : ℝ) + 1) * hermiteI n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hermiteI]
  | one =>
    rw [hermiteI_add_two]
    simp [hermiteI]
    ring
  | more n ih₀ ih₁ =>
    rw [show n + 2 + 1 = (n + 1) + 2 by ring, hermiteI_add_two (n + 1), derivative_add,
      derivative_mul, derivative_X, one_mul, derivative_mul, derivative_C, zero_mul, zero_add, ih₁,
      ih₀, show n + 1 + 1 = n + 2 by ring, hermiteI_add_two n]
    simp only [map_add, map_natCast, map_one]
    push_cast
    ring

/-- The imaginary-axis value of the perturbed Hermite polynomial:
`P(iy) = i^m ((c − m − 1) h_m(y) − y h_{m+1}(y))`. -/
theorem aeval_I_mul_hermiteReal_add_smul (m : ℕ) (c y : ℝ) :
    aeval (I * (y : ℂ)) (hermiteReal (m + 2) + C c * hermiteReal m)
      = I ^ m * ((((c - m - 1) * (hermiteI m).eval y - y * (hermiteI (m + 1)).eval y : ℝ)) : ℂ) := by
  have hR : ∀ n, aeval (I * (y : ℂ)) (hermiteReal n) = aeval (I * (y : ℂ)) (hermite n) := fun n => by
    rw [hermiteReal, ← algebraMap_int_eq, aeval_map_algebraMap]
  rw [map_add, map_mul, aeval_C, hR, hR, aeval_I_mul_hermite, aeval_I_mul_hermite,
    eval_hermiteI_add_two]
  push_cast
  simp only [Complex.coe_algebraMap]
  linear_combination ((((hermiteI (m + 1)).eval y : ℝ) : ℂ) * y
    + ((m : ℂ) + 1) * (((hermiteI m).eval y : ℝ) : ℂ)) * I ^ m * I_sq

theorem eval_hermiteI_odd_zero (j : ℕ) : (hermiteI (2 * j + 1)).eval 0 = 0 := by
  induction j with
  | zero => simp [hermiteI]
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, eval_hermiteI_add_two, ih]
    ring

theorem eval_hermiteI_even_succ_zero (j : ℕ) :
    (hermiteI (2 * j + 2)).eval 0 = (2 * (j : ℝ) + 1) * (hermiteI (2 * j)).eval 0 := by
  rw [eval_hermiteI_add_two]
  push_cast
  ring

/-- A real polynomial vanishing at `0` with positive derivative there is positive somewhere in
`(0, Y)`. -/
theorem exists_pos_eval_of_derivative_pos {F : ℝ[X]} (hF0 : F.eval 0 = 0)
    (hD : 0 < (derivative F).eval 0) {Y : ℝ} (hY : 0 < Y) :
    ∃ ε : ℝ, 0 < ε ∧ ε < Y ∧ 0 < F.eval ε := by
  have hslope := (hasDerivAt_iff_tendsto_slope_zero.mp (F.hasDerivAt 0)).mono_left
    (nhdsWithin_mono (0 : ℝ) (show Ioi (0 : ℝ) ⊆ {0}ᶜ from fun t ht => ne_of_gt ht))
  have hev := (hslope.eventually_const_lt hD).and (Ioo_mem_nhdsGT hY)
  obtain ⟨ε, hpos, hεI⟩ := hev.exists
  refine ⟨ε, hεI.1, hεI.2, ?_⟩
  rw [zero_add, hF0, sub_zero, smul_eq_mul] at hpos
  exact (mul_pos_iff_of_pos_left (inv_pos.2 hεI.1)).1 hpos

/-- **Above the threshold the perturbed Hermite polynomial has an imaginary zero.**  If `m` is even
and `c > m + 1`, or `m` is odd and `c > m + 2`, then `He_{m+2} + c·He_m` vanishes at `iy` for some
`y > 0`. -/
theorem exists_imaginary_root_hermiteReal_add_smul {m : ℕ} {c : ℝ}
    (hc : (Even m ∧ (m : ℝ) + 1 < c) ∨ (Odd m ∧ (m : ℝ) + 2 < c)) :
    ∃ y : ℝ, 0 < y ∧ aeval (I * (y : ℂ)) (hermiteReal (m + 2) + C c * hermiteReal m) = 0 := by
  have hc1 : (m : ℝ) + 1 < c := by rcases hc with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
  set F : ℝ[X] := C (c - m - 1) * hermiteI m - X * hermiteI (m + 1) with hF
  have hFeval : ∀ y, F.eval y = (c - m - 1) * (hermiteI m).eval y - y * (hermiteI (m + 1)).eval y :=
    fun y => by simp [hF]
  -- negative far out
  set Y : ℝ := c + 1 with hY
  have hY0 : 0 < Y := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hFY : F.eval Y < 0 := by
    rw [hFeval]
    have hpos := eval_hermiteI_pos hY0 m
    have hsucc := mul_eval_hermiteI_le_succ hY0.le m
    have hY2 : c - m - 1 < Y * Y := by nlinarith
    nlinarith
  -- positive near zero
  obtain ⟨ε, hε0, hεY, hFε⟩ : ∃ ε : ℝ, 0 ≤ ε ∧ ε < Y ∧ 0 < F.eval ε := by
    rcases hc with ⟨⟨j, rfl⟩, _⟩ | ⟨⟨j, rfl⟩, hc2⟩
    · refine ⟨0, le_rfl, hY0, ?_⟩
      rw [hFeval, zero_mul, sub_zero, show j + j = 2 * j by ring]
      exact mul_pos (by push_cast at hc1 ⊢; linarith) (eval_hermiteI_even_pos le_rfl j)
    · have hF0 : F.eval 0 = 0 := by
        rw [hFeval, eval_hermiteI_odd_zero]
        ring
      have hD : (derivative F).eval 0
          = (2 * (j : ℝ) + 1) * (hermiteI (2 * j)).eval 0 * (c - (2 * j + 1) - 2) := by
        rw [hF, derivative_sub, derivative_mul, derivative_mul, derivative_C, zero_mul, zero_add,
          derivative_X, one_mul, derivative_hermiteI_succ, show 2 * j + 1 + 1 = 2 * j + 2 by ring]
        simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, zero_mul, add_zero]
        rw [eval_hermiteI_even_succ_zero]
        push_cast
        ring
      have hDpos : 0 < (derivative F).eval 0 := by
        rw [hD]
        have h0 := eval_hermiteI_even_pos le_rfl j
        push_cast at hc2
        have : 0 < c - (2 * (j : ℝ) + 1) - 2 := by linarith
        positivity
      obtain ⟨ε, hε, hεY, hFε⟩ := exists_pos_eval_of_derivative_pos hF0 hDpos hY0
      exact ⟨ε, hε.le, hεY, hFε⟩
  -- the intermediate value theorem on `[ε, Y]`
  obtain ⟨y, hyI, hFy⟩ := intermediate_value_Ioo' hεY.le F.continuous.continuousOn
    (show (0 : ℝ) ∈ Ioo (F.eval Y) (F.eval ε) from ⟨hFY, hFε⟩)
  refine ⟨y, lt_of_le_of_lt hε0 hyI.1, ?_⟩
  have hFy' : F.eval y = 0 := hFy
  rw [aeval_I_mul_hermiteReal_add_smul, ← hFeval, hFy']
  simp

/-! ## Parity, values at the origin and simple roots of `He_n` -/

theorem hermiteReal_add_two (n : ℕ) :
    hermiteReal (n + 2) = X * hermiteReal (n + 1) - C ((n : ℝ) + 1) * hermiteReal n := by
  rw [hermiteReal_succ (n + 1), gaussShift, derivative_hermiteReal_succ, C_1, one_mul]

theorem eval_hermiteReal_add_two (n : ℕ) (x : ℝ) :
    (hermiteReal (n + 2)).eval x
      = x * (hermiteReal (n + 1)).eval x - ((n : ℝ) + 1) * (hermiteReal n).eval x := by
  rw [hermiteReal_add_two]
  simp

@[simp] theorem eval_hermiteReal_zero (x : ℝ) : (hermiteReal 0).eval x = 1 := by
  simp [hermiteReal, hermite_zero]

@[simp] theorem eval_hermiteReal_one (x : ℝ) : (hermiteReal 1).eval x = x := by
  simp [hermiteReal]

theorem hermiteReal_ne_zero (n : ℕ) : hermiteReal n ≠ 0 :=
  ((hermite_monic n).map (Int.castRingHom ℝ)).ne_zero

theorem natDegree_hermiteReal (n : ℕ) : (hermiteReal n).natDegree = n := by
  rw [hermiteReal, (hermite_monic n).natDegree_map, natDegree_hermite]

/-- `He_n(−x) = (−1)ⁿ He_n(x)`. -/
theorem eval_neg_hermiteReal (n : ℕ) (x : ℝ) :
    (hermiteReal n).eval (-x) = (-1) ^ n * (hermiteReal n).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ =>
    rw [eval_hermiteReal_add_two, eval_hermiteReal_add_two, ih₀, ih₁]
    ring

theorem eval_hermiteReal_odd_zero (j : ℕ) : (hermiteReal (2 * j + 1)).eval 0 = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring, eval_hermiteReal_add_two, ih]
    ring

theorem eval_hermiteReal_even_zero_ne (j : ℕ) : (hermiteReal (2 * j)).eval 0 ≠ 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, eval_hermiteReal_add_two, zero_mul, zero_sub,
      neg_ne_zero]
    exact mul_ne_zero (by positivity) ih

/-- Consecutive Hermite polynomials have no common zero. -/
theorem eval_hermiteReal_ne_zero_of_succ (n : ℕ) (x : ℝ) :
    (hermiteReal (n + 1)).eval x = 0 → (hermiteReal n).eval x ≠ 0 := by
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h h0
    have h2 := eval_hermiteReal_add_two n x
    rw [h, h0, mul_zero, zero_sub, eq_comm, neg_eq_zero] at h2
    exact ih h0 ((mul_eq_zero.mp h2).resolve_left (by positivity))

/-- **The zeros of `He_n` are simple.** -/
theorem nodup_roots_hermiteReal (n : ℕ) : (hermiteReal n).roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro x
  rw [count_roots]
  by_contra hlt
  push Not at hlt
  obtain ⟨hr, hd⟩ := (one_lt_rootMultiplicity_iff_isRoot (hermiteReal_ne_zero n)).1 hlt
  rcases n with _ | n
  · simp [IsRoot] at hr
  · rw [IsRoot.def, derivative_hermiteReal_succ, eval_mul, eval_C] at hd
    exact eval_hermiteReal_ne_zero_of_succ n x hr
      ((mul_eq_zero.mp hd).resolve_left (by positivity))

theorem card_roots_toFinset_hermiteReal (n : ℕ) : (hermiteReal n).roots.toFinset.card = n := by
  classical
  rw [Multiset.toFinset_card_of_nodup (nodup_roots_hermiteReal n),
    splits_iff_card_roots.mp (splits_hermiteReal n), natDegree_hermiteReal]

/-! ## The odd window `m + 1 < c ≤ m + 2` -/

/-- A real polynomial vanishing at `a`, of one sign `s` just left of `a`, has `s·p′(a) ≤ 0`. -/
theorem mul_eval_derivative_nonpos_of_left {p : ℝ[X]} {a s : ℝ} (ha : p.eval a = 0)
    (hleft : ∀ x ∈ Ico 0 a, 0 < s * p.eval x) (ha0 : 0 < a) :
    s * (derivative p).eval a ≤ 0 := by
  have hslope := (hasDerivAt_iff_tendsto_slope.mp (p.hasDerivAt a)).mono_left
    (nhdsWithin_mono a (show Iio a ⊆ {a}ᶜ from fun x hx => ne_of_lt hx))
  have hlim := hslope.const_mul s
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT ha0] with x hx
  rw [slope_def_field, ha, sub_zero]
  have hxa : x - a < 0 := by linarith [hx.2]
  have hpos := hleft x ⟨hx.1.le, hx.2⟩
  rw [mul_div_assoc', div_nonpos_iff]
  left
  exact ⟨hpos.le, hxa.le⟩

/-- **The odd window.**  For `m = 2j + 1` and `m + 1 < c < m + 2`, `He_{m+2} + c·He_m` splits over
`ℝ`.  With `H = He_{m+1}` (even, `H(0) ≠ 0`, simple zeros) and `x₊` its least positive zero:
`P = He_{m+2} + c·He_m` is odd and has the sign of `H(0)` just right of `0`
(`P′(0) = H(0)(m + 2 − c)`), the opposite sign at `x₊` (`P(x₊) = (c − m − 1)He_m(x₊)` and
`H′(x₊) = (m+1)He_m(x₊)`), so it has zeros `0, ±r` in the middle gap `(−x₊, x₊)`; each other gap of
`H` carries a zero by Rolle's theorem for the gauge of the Gaussian shift.  That is `m + 2` distinct
real zeros. -/
theorem splits_hermiteReal_add_smul_odd_window {j : ℕ} {c : ℝ}
    (hc1 : 2 * (j : ℝ) + 2 < c) (hc2 : c < 2 * (j : ℝ) + 3) :
    (hermiteReal (2 * j + 3) + C c * hermiteReal (2 * j + 1)).Splits := by
  classical
  set H := hermiteReal (2 * j + 2) with hH
  set P := hermiteReal (2 * j + 3) + C c * hermiteReal (2 * j + 1) with hP
  set s₀ := H.eval 0 with hs₀
  have hs₀ne : s₀ ≠ 0 := by
    rw [hs₀, hH, show 2 * j + 2 = 2 * (j + 1) by ring]
    exact eval_hermiteReal_even_zero_ne (j + 1)
  have hHne : H ≠ 0 := hermiteReal_ne_zero _
  -- `P` as a Gaussian shift of `H`
  have hPshift :
      P = gaussShift ((((2 * j + 1 : ℕ) : ℝ) + 1 - c) / (((2 * j + 1 : ℕ) : ℝ) + 1)) H := by
    rw [hP, hH, ← hermiteReal_add_smul_eq_gaussShift]
  have hβ : (((2 * j + 1 : ℕ) : ℝ) + 1 - c) / (((2 * j + 1 : ℕ) : ℝ) + 1) ≠ 0 := by
    push_cast
    exact div_ne_zero (by linarith) (by positivity)
  have hPeval : ∀ x, P.eval x
      = x * H.eval x - (2 * (j : ℝ) + 2) * (hermiteReal (2 * j + 1)).eval x
        + c * (hermiteReal (2 * j + 1)).eval x := by
    intro x
    rw [hP, show 2 * j + 3 = (2 * j + 1) + 2 by ring]
    simp only [eval_add, eval_mul, eval_C]
    rw [eval_hermiteReal_add_two, hH]
    push_cast
    ring
  have hPodd : ∀ x, P.eval (-x) = -P.eval x := by
    intro x
    rw [hP]
    simp only [eval_add, eval_mul, eval_C]
    rw [eval_neg_hermiteReal, eval_neg_hermiteReal]
    rw [show (-1 : ℝ) ^ (2 * j + 3) = -1 by rw [pow_succ, pow_succ, pow_succ, pow_mul]; norm_num,
      show (-1 : ℝ) ^ (2 * j + 1) = -1 by rw [pow_succ, pow_mul]; norm_num]
    ring
  have hHeven : ∀ x, H.eval (-x) = H.eval x := by
    intro x
    rw [hH, eval_neg_hermiteReal, show (-1 : ℝ) ^ (2 * j + 2) = 1 by
      rw [pow_succ, pow_succ, pow_mul]; norm_num, one_mul]
  have hP0 : P.eval 0 = 0 := by
    have := hPodd 0
    rw [neg_zero] at this
    linarith
  -- roots of `H`
  set S := H.roots.toFinset with hS
  have memS : ∀ x, x ∈ S ↔ H.eval x = 0 := fun x => by
    rw [hS, Multiset.mem_toFinset, mem_roots hHne, IsRoot.def]
  have hScard : S.card = 2 * j + 2 := card_roots_toFinset_hermiteReal _
  have h0S : (0 : ℝ) ∉ S := fun h => hs₀ne ((memS 0).1 h)
  have hposNe : (S.filter (0 < ·)).Nonempty := by
    obtain ⟨x, hx⟩ : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; omega)
    rcases lt_or_gt_of_ne (show x ≠ 0 from fun h => h0S (h ▸ hx)) with hneg | hpos
    · refine ⟨-x, Finset.mem_filter.mpr ⟨(memS _).2 ?_, by linarith⟩⟩
      rw [hHeven]
      exact (memS x).1 hx
    · exact ⟨x, Finset.mem_filter.mpr ⟨hx, hpos⟩⟩
  set xp := (S.filter (0 < ·)).min' hposNe with hxp
  have hxpmem := Finset.mem_filter.mp ((S.filter (0 < ·)).min'_mem hposNe)
  have hxp0 : 0 < xp := hxpmem.2
  have hHxp : H.eval xp = 0 := (memS xp).1 hxpmem.1
  have hxp_le : ∀ x, 0 < x → H.eval x = 0 → xp ≤ x := fun x hx h0 =>
    (S.filter (0 < ·)).min'_le x (Finset.mem_filter.mpr ⟨(memS x).2 h0, hx⟩)
  -- `H` has the sign of `H(0)` on `[0, x₊)`
  have hHsign : ∀ y ∈ Ico 0 xp, 0 < s₀ * H.eval y := by
    intro y hy
    by_contra hle
    push Not at hle
    have hcont : ContinuousOn (fun x => s₀ * H.eval x) (Icc 0 y) :=
      (continuous_const.mul H.continuous).continuousOn
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hy.1 hcont
      (show (0 : ℝ) ∈ Icc (s₀ * H.eval y) (s₀ * H.eval 0) from ⟨hle, by rw [show H.eval 0 = s₀ from hs₀.symm]; exact mul_self_nonneg s₀⟩)
    have hHz : H.eval z = 0 := (mul_eq_zero.mp hz0).resolve_left hs₀ne
    rcases eq_or_lt_of_le hz.1 with hz0' | hzpos
    · have hz00 : z = 0 := hz0'.symm
      rw [hz00] at hHz
      exact hs₀ne (by rw [hs₀]; exact hHz)
    · exact absurd (hxp_le z hzpos hHz) (not_le.mpr (lt_of_le_of_lt hz.2 hy.2))
  -- `H(0)·He_m(x₊) < 0`
  have hHm : s₀ * (hermiteReal (2 * j + 1)).eval xp < 0 := by
    have hder := mul_eval_derivative_nonpos_of_left hHxp hHsign hxp0
    rw [hH, show 2 * j + 2 = (2 * j + 1) + 1 by ring, derivative_hermiteReal_succ, eval_mul,
      eval_C] at hder
    have hne : (hermiteReal (2 * j + 1)).eval xp ≠ 0 :=
      eval_hermiteReal_ne_zero_of_succ (2 * j + 1) xp (by rw [← hH]; exact hHxp)
    have hpos : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) + 1 := by positivity
    rcases lt_or_eq_of_le (show s₀ * (hermiteReal (2 * j + 1)).eval xp * (((2 * j + 1 : ℕ) : ℝ) + 1) ≤ 0
      by linarith [hder]) with hlt | heq
    · exact neg_of_mul_neg_left hlt hpos.le
    · exact absurd ((mul_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right hpos.ne')).resolve_left hs₀ne) hne
  -- `H(0)·P(x₊) < 0`
  have hPxp : s₀ * P.eval xp < 0 := by
    rw [hPeval, hHxp, mul_zero, zero_sub]
    have : s₀ * (-(2 * (j : ℝ) + 2) * (hermiteReal (2 * j + 1)).eval xp
        + c * (hermiteReal (2 * j + 1)).eval xp)
        = (c - (2 * j + 2)) * (s₀ * (hermiteReal (2 * j + 1)).eval xp) := by ring
    rw [show -((2 * (j : ℝ) + 2) * (hermiteReal (2 * j + 1)).eval xp)
        + c * (hermiteReal (2 * j + 1)).eval xp
        = -(2 * (j : ℝ) + 2) * (hermiteReal (2 * j + 1)).eval xp
        + c * (hermiteReal (2 * j + 1)).eval xp by ring, this]
    exact mul_neg_of_pos_of_neg (by linarith) hHm
  -- `H(0)·P′(0) > 0`
  have hPder : 0 < (derivative (C s₀ * P)).eval 0 := by
    have hHe2j : H.eval 0 = -(2 * (j : ℝ) + 1) * (hermiteReal (2 * j)).eval 0 := by
      rw [hH, eval_hermiteReal_add_two, eval_hermiteReal_odd_zero]
      push_cast
      ring
    rw [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C, hP, derivative_add,
      derivative_mul, derivative_C, zero_mul, zero_add, show 2 * j + 3 = (2 * j + 2) + 1 by ring,
      derivative_hermiteReal_succ, derivative_hermiteReal_succ]
    simp only [eval_add, eval_mul, eval_C]
    rw [← hH, ← hs₀]
    have hrel : (hermiteReal (2 * j)).eval 0 = -s₀ / (2 * (j : ℝ) + 1) := by
      rw [hs₀, hHe2j]; field_simp
    rw [hrel]
    push_cast
    have h2j : (0 : ℝ) < 2 * j + 1 := by positivity
    have : s₀ * ((2 * (j : ℝ) + 2 + 1) * s₀ + c * ((2 * j + 1) * (-s₀ / (2 * j + 1))))
        = s₀ ^ 2 * (2 * j + 3 - c) := by field_simp; ring
    rw [this]
    have : 0 < s₀ ^ 2 := by positivity
    nlinarith
  -- a zero `r ∈ (0, x₊)`
  obtain ⟨ε, hε0, hεx, hPε⟩ := exists_pos_eval_of_derivative_pos (F := C s₀ * P)
    (by rw [eval_mul, eval_C, hP0, mul_zero]) hPder hxp0
  rw [eval_mul, eval_C] at hPε
  obtain ⟨r, hrI, hr0⟩ := intermediate_value_Ioo' hεx.le
    ((continuous_const.mul P.continuous).continuousOn (s := Icc ε xp))
    (show (0 : ℝ) ∈ Ioo (s₀ * P.eval xp) (s₀ * P.eval ε) from ⟨hPxp, hPε⟩)
  have hPr : P.eval r = 0 := (mul_eq_zero.mp hr0).resolve_left hs₀ne
  have hr0' : 0 < r := lt_trans hε0 hrI.1
  have hrxp : r < xp := hrI.2
  -- counting distinct zeros
  have hPne : P ≠ 0 := by
    rw [hPshift]
    exact gaussShift_ne_zero hHne
  have hPdeg : P.natDegree = 2 * j + 3 := by
    rw [hPshift, natDegree_gaussShift hHne, hH, natDegree_hermiteReal]
  set T := P.roots.toFinset with hT
  have memT : ∀ x, x ∈ T ↔ P.eval x = 0 := fun x => by
    rw [hT, Multiset.mem_toFinset, mem_roots hPne, IsRoot.def]
  have hrT : r ∈ T := (memT r).2 hPr
  have hnrT : -r ∈ T := (memT _).2 (by rw [hPodd, hPr, neg_zero])
  have hrS : r ∉ S := fun h => by
    have := hHsign r ⟨hr0'.le, hrxp⟩
    rw [(memS r).1 h, mul_zero] at this
    exact lt_irrefl _ this
  have hnrS : -r ∉ S := fun h => hrS ((memS r).2 (by rw [← hHeven]; exact (memS _).1 h))
  have hrne : r ≠ -r := by intro h; linarith
  have hinter : S.card ≤ ((T.erase r).erase (-r) \ S).card + 1 := by
    refine Finset.card_le_sdiff_of_interleaved fun x hx y hy hxy _ => ?_
    have hx0 : x ≠ 0 := fun h => h0S (h ▸ hx)
    have hy0 : y ≠ 0 := fun h => h0S (h ▸ hy)
    by_cases hmid : x < 0 ∧ 0 < y
    · refine ⟨0, Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, (memT 0).2 hP0⟩⟩,
        hmid.1, hmid.2⟩
      · intro h; linarith
      · exact fun h => (lt_irrefl _ (h ▸ hr0'))
    · obtain ⟨z, hz1, hz2⟩ := exists_root_gaussShift_of_lt hβ hxy ((memS x).1 hx) ((memS y).1 hy)
      rw [← hPshift] at hz2
      have hfar : xp ≤ z ∨ z ≤ -xp := by
        rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
        · have hyneg : y < 0 := by
            rcases lt_or_gt_of_ne hy0 with h | h
            · exact h
            · exact absurd ⟨hxneg, h⟩ hmid
          right
          have := hxp_le (-y) (by linarith) (by rw [hHeven]; exact (memS y).1 hy)
          linarith [hz1.2]
        · left
          have := hxp_le x hxpos ((memS x).1 hx)
          linarith [hz1.1]
      refine ⟨z, Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, (memT z).2 hz2⟩⟩,
        hz1.1, hz1.2⟩
      · intro h; rcases hfar with h' | h' <;> linarith
      · intro h; rcases hfar with h' | h' <;> linarith
  have hsd : ((T.erase r).erase (-r) \ S).card + 2 = (T \ S).card := by
    rw [Finset.erase_sdiff_comm, Finset.erase_sdiff_comm,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hrne.symm, Finset.mem_sdiff.mpr ⟨hnrT, hnrS⟩⟩),
      Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hrT, hrS⟩)]
    have h2 : 2 ≤ (T \ S).card := by
      have hsub : ({r, -r} : Finset ℝ) ⊆ T \ S := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_sdiff.mpr ⟨hrT, hrS⟩
        · rw [Finset.mem_singleton.mp hw]; exact Finset.mem_sdiff.mpr ⟨hnrT, hnrS⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hrne] at this
      exact this
    omega
  have hTcard : 2 * j + 3 ≤ T.card := by
    have := Finset.card_le_card (Finset.sdiff_subset (s := T) (t := S))
    omega
  rw [splits_iff_card_roots, hPdeg]
  have hle := card_roots' P
  have hge : T.card ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
  omega

/-- The endpoint `c = m + 2` of the odd window, by coefficientwise limits. -/
theorem splits_hermiteReal_add_smul_odd_endpoint (j : ℕ) :
    (hermiteReal (2 * j + 3) + C (2 * (j : ℝ) + 3) * hermiteReal (2 * j + 1)).Splits := by
  set cs : ℕ → ℝ := fun n => 2 * (j : ℝ) + 3 - 1 / ((n : ℝ) + 2) with hcs
  have hdeg : ∀ c : ℝ, (hermiteReal (2 * j + 3) + C c * hermiteReal (2 * j + 1)).natDegree
      ≤ 2 * j + 3 := by
    intro c
    refine (natDegree_add_le _ _).trans (max_le (by rw [natDegree_hermiteReal]) ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_hermiteReal]
    omega
  refine splits_of_tendsto_coeff (qs := fun n => hermiteReal (2 * j + 3) + C (cs n) * hermiteReal (2 * j + 1))
    (fun n => hdeg _) (hdeg _) (fun n => ?_) (fun i => ?_) ?_
  · have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have h2 : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact splits_hermiteReal_add_smul_odd_window (by simp only [hcs]; linarith)
      (by simp only [hcs]; linarith)
  · simp only [coeff_add, coeff_C_mul]
    refine tendsto_const_nhds.add (Tendsto.mul_const _ ?_)
    have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h := h0.comp (tendsto_add_atTop_nat 1)
      refine h.congr fun n => ?_
      simp only [Function.comp, Nat.cast_add, Nat.cast_one]
      ring
    have hconst : Tendsto (fun _ : ℕ => 2 * (j : ℝ) + 3) atTop (𝓝 (2 * (j : ℝ) + 3)) :=
      tendsto_const_nhds
    simpa [hcs] using hconst.sub this
  · intro h0
    have := congrArg natDegree h0
    rw [natDegree_zero] at this
    have hd : (hermiteReal (2 * j + 3) + C (2 * (j : ℝ) + 3) * hermiteReal (2 * j + 1)).natDegree
        = 2 * j + 3 := by
      rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_hermiteReal]
      refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
      rw [natDegree_hermiteReal, natDegree_hermiteReal]
      omega
    omega

/-- **The threshold law, even order.**  `He_{2j+2} + c·He_{2j}` is real-rooted iff `c ≤ 2j + 1`. -/
theorem splits_hermiteReal_add_smul_iff_even (j : ℕ) (c : ℝ) :
    (hermiteReal (2 * j + 2) + C c * hermiteReal (2 * j)).Splits ↔ c ≤ 2 * (j : ℝ) + 1 := by
  constructor
  · intro hs
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy, hroot⟩ := exists_imaginary_root_hermiteReal_add_smul (m := 2 * j) (c := c)
      (Or.inl ⟨even_two_mul j, by push_cast; linarith⟩)
    have hne : hermiteReal (2 * j + 2) + C c * hermiteReal (2 * j) ≠ 0 := by
      rw [hermiteReal_add_smul_eq_gaussShift]
      exact gaussShift_ne_zero (hermiteReal_ne_zero _)
    have := im_eq_zero_of_splits hs hne hroot
    simp at this
    linarith
  · intro hc
    exact splits_hermiteReal_add_smul_of_le (m := 2 * j) (by push_cast; linarith)

/-- **The threshold law, odd order.**  `He_{2j+3} + c·He_{2j+1}` is real-rooted iff `c ≤ 2j + 3`. -/
theorem splits_hermiteReal_add_smul_iff_odd (j : ℕ) (c : ℝ) :
    (hermiteReal (2 * j + 3) + C c * hermiteReal (2 * j + 1)).Splits ↔ c ≤ 2 * (j : ℝ) + 3 := by
  constructor
  · intro hs
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy, hroot⟩ := exists_imaginary_root_hermiteReal_add_smul (m := 2 * j + 1) (c := c)
      (Or.inr ⟨odd_two_mul_add_one j, by push_cast; linarith⟩)
    rw [show 2 * j + 1 + 2 = 2 * j + 3 by ring] at hroot
    have hne : hermiteReal (2 * j + 3) + C c * hermiteReal (2 * j + 1) ≠ 0 := by
      rw [show 2 * j + 3 = (2 * j + 1) + 2 by ring, hermiteReal_add_smul_eq_gaussShift]
      exact gaussShift_ne_zero (hermiteReal_ne_zero _)
    have := im_eq_zero_of_splits hs hne hroot
    simp at this
    linarith
  · intro hc
    rcases le_or_gt c (2 * (j : ℝ) + 2) with h1 | h1
    · have := splits_hermiteReal_add_smul_of_le (m := 2 * j + 1) (c := c) (by push_cast; linarith)
      rwa [show 2 * j + 1 + 2 = 2 * j + 3 by ring] at this
    · rcases lt_or_eq_of_le hc with h2 | h2
      · exact splits_hermiteReal_add_smul_odd_window h1 h2
      · rw [h2]
        exact splits_hermiteReal_add_smul_odd_endpoint j

end

end GaloisForLFunctions.HTGeometry

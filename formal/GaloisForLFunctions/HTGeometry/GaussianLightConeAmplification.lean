import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Light-cone amplification of exponential sums

Let `S(ε) = Σ_i c_i exp(-ε w_i)` be an absolutely convergent exponential sum in a real parameter
`ε ≥ ε₀ ≥ 0`, with complex exponents `w_i` and coefficients that depend only on the exponent
(`w_i = w_j → c_i = c_j`).  Suppose the light-cone set `{i | Re w_i < 0}` is finite, and the terms
outside it admit a summable majorant `m_i ≥ 0`, uniform in `ε ≥ ε₀`.

* If no exponent has negative real part, `‖S(ε)‖ ≤ Σ m` for all `ε ≥ ε₀`
  (`norm_tsum_mul_exp_neg_le_of_re_nonneg`).
* If some exponent has negative real part and the light-cone coefficients do not vanish, `S` is
  unbounded on `[ε₀, ∞)` (`exists_lt_norm_tsum_mul_exp_neg_of_re_neg`).

The proof picks the most negative real part `-M` in the finite light cone and normalizes by
`exp(ε w*)`, where `w*` attains it.  Averaging over windows `[S, S + T]` keeps the full mass of the
exponents equal to `w*`.  Their coefficients agree, so this mass is `#{i : w_i = w*} · c* ≠ 0`.
Every other light-cone exponent has nonnegative relative real part and contributes `O(1/T)`.  Some
point of each long window therefore carries `e^{εM}` times a fixed positive amount.
-/

open Complex Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem re_sub_ofReal_sq (z : ℂ) (t : ℝ) :
    ((z - t) ^ 2).re = (z.re - t) ^ 2 - z.im ^ 2 := by
  simp only [sq, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
    Complex.ofReal_im, sub_zero]

/-- The translated Gaussian has modulus `exp(-σ((Re z - t)² - (Im z)²))`. -/
theorem norm_exp_neg_mul_sub_sq (t σ : ℝ) (z : ℂ) :
    ‖Complex.exp (-(σ : ℂ) * (z - t) ^ 2)‖ =
      Real.exp (-(σ * ((z.re - t) ^ 2 - z.im ^ 2))) := by
  rw [Complex.norm_exp]
  congr 1
  rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul, re_sub_ofReal_sq]

/-- `‖∫_S^{S+T} exp(b x) dx‖ ≤ 2/‖b‖` when `Re b ≤ 0` and `0 ≤ S`. -/
theorem norm_integral_exp_mul_le_two_div {b : ℂ} (hb : b ≠ 0) (hre : b.re ≤ 0) {S T : ℝ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) :
    ‖∫ x in S..S + T, Complex.exp (b * x)‖ ≤ 2 / ‖b‖ := by
  rw [integral_exp_mul_complex hb, norm_div]
  have hle : ∀ x : ℝ, 0 ≤ x → ‖Complex.exp (b * x)‖ ≤ 1 := fun x hx => by
    rw [Complex.norm_exp, Complex.re_mul_ofReal, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hre hx
  gcongr
  calc ‖Complex.exp (b * ↑(S + T)) - Complex.exp (b * ↑S)‖
      ≤ ‖Complex.exp (b * ↑(S + T))‖ + ‖Complex.exp (b * ↑S)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (hle _ (by linarith)) (hle _ hS)
    _ = 2 := by norm_num

/-- **Closed cone.**  With every exponent in the closed right half-plane the exponential sum is
bounded by its majorant. -/
theorem norm_tsum_mul_exp_neg_le_of_re_nonneg {ι : Type*} {w c : ι → ℂ} {ε₀ : ℝ}
    {m : ι → ℝ} (hm : Summable m)
    (hmaj : ∀ i, 0 ≤ (w i).re → ∀ ε, ε₀ ≤ ε → ‖c i * Complex.exp (-(ε : ℂ) * w i)‖ ≤ m i)
    (hsum : ∀ ε, ε₀ ≤ ε → Summable (fun i => ‖c i * Complex.exp (-(ε : ℂ) * w i)‖))
    (hcone : ∀ i, 0 ≤ (w i).re) {ε : ℝ} (hε : ε₀ ≤ ε) :
    ‖∑' i, c i * Complex.exp (-(ε : ℂ) * w i)‖ ≤ ∑' i, m i :=
  (norm_tsum_le_tsum_norm (hsum ε hε)).trans
    ((hsum ε hε).tsum_le_tsum (fun i => hmaj i (hcone i) ε hε) hm)

/-- **Open light cone.**  One exponent with negative real part makes the exponential sum unbounded
in `ε`. -/
theorem exists_lt_norm_tsum_mul_exp_neg_of_re_neg {ι : Type*} {w c : ι → ℂ} {ε₀ : ℝ}
    (hε₀ : 0 ≤ ε₀)
    (hcoef : ∀ i j, w i = w j → c i = c j)
    (hc : ∀ i, (w i).re < 0 → c i ≠ 0)
    (hfin : {i | (w i).re < 0}.Finite)
    {m : ι → ℝ} (hm0 : ∀ i, 0 ≤ m i) (hm : Summable m)
    (hmaj : ∀ i, 0 ≤ (w i).re → ∀ ε, ε₀ ≤ ε → ‖c i * Complex.exp (-(ε : ℂ) * w i)‖ ≤ m i)
    (hsum : ∀ ε, ε₀ ≤ ε → Summable (fun i => ‖c i * Complex.exp (-(ε : ℂ) * w i)‖))
    (hneg : ∃ i, (w i).re < 0) (C : ℝ) :
    ∃ ε : ℝ, ε₀ ≤ ε ∧ C < ‖∑' i, c i * Complex.exp (-(ε : ℂ) * w i)‖ := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ι, P = hfin.toFinset := ⟨_, rfl⟩
  have hmemP : ∀ i, i ∈ P ↔ (w i).re < 0 := fun i => by
    rw [hPdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  obtain ⟨i₀, hi₀⟩ := hneg
  obtain ⟨is, hisP, hmax⟩ := P.exists_max_image (fun i => -(w i).re) ⟨i₀, (hmemP i₀).2 hi₀⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = -(w is).re := ⟨_, rfl⟩
  have hM : 0 < M := by
    have := (hmemP is).1 hisP
    linarith
  obtain ⟨b, hb⟩ : ∃ b : ι → ℂ, ∀ i, b i = -(w i - w is) := ⟨_, fun _ => rfl⟩
  have hbre : ∀ i ∈ P, (b i).re ≤ 0 := fun i hi => by
    have := hmax i hi
    rw [hb, Complex.neg_re, Complex.sub_re]
    linarith
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℂ, ∀ x : ℝ, g x = ∑ i ∈ P, c i * Complex.exp (b i * x) :=
    ⟨_, fun _ => rfl⟩
  have hPsum : ∀ ε : ℝ,
      ∑ i ∈ P, c i * Complex.exp (-(ε : ℂ) * w i) =
        Complex.exp (-(ε : ℂ) * w is) * g ε := fun ε => by
    rw [hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb, mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  have hnormWs : ∀ ε : ℝ, ‖Complex.exp (-(ε : ℂ) * w is)‖ = Real.exp (ε * M) := fun ε => by
    rw [Complex.norm_exp, neg_mul, Complex.neg_re, Complex.re_ofReal_mul, hMdef]
    ring_nf
  -- the mass carried by the leading exponent and the error budget of the others
  obtain ⟨Z, hZdef⟩ : ∃ Z : Finset ι, Z = P.filter (fun i => b i = 0) := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : Finset ι, N = P.filter (fun i => ¬ b i = 0) := ⟨_, rfl⟩
  have hisZ : is ∈ Z := by
    rw [hZdef, Finset.mem_filter, hb, sub_self, neg_zero]
    exact ⟨hisP, rfl⟩
  have hcZ : ∀ i ∈ Z, c i = c is := fun i hi => by
    rw [hZdef, Finset.mem_filter, hb, neg_eq_zero, sub_eq_zero] at hi
    exact hcoef i is hi.2
  have hcis : c is ≠ 0 := hc is ((hmemP is).1 hisP)
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (Z.card : ℝ) * ‖c is‖ := ⟨_, rfl⟩
  have hA : 0 < A := by
    have hcard : (0 : ℝ) < Z.card := by exact_mod_cast Finset.card_pos.2 ⟨is, hisZ⟩
    rw [hAdef]
    exact mul_pos hcard (norm_pos_iff.2 hcis)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = ∑ i ∈ N, ‖c i‖ * (2 / ‖b i‖) := ⟨_, rfl⟩
  have hK : 0 ≤ K := by
    rw [hKdef]
    exact Finset.sum_nonneg fun i _ => by positivity
  have hint : ∀ S T : ℝ, 0 ≤ S → 0 ≤ T →
      T * A - K ≤ ‖∫ x in S..S + T, g x‖ := by
    intro S T hS hT
    have hsplit : ∫ x in S..S + T, g x =
        ∑ i ∈ P, c i * ∫ x in S..S + T, Complex.exp (b i * x) := by
      simp_rw [hg]
      rw [intervalIntegral.integral_finsetSum (f := fun i x => c i * Complex.exp (b i * x))
        fun i _ => ((continuous_const.mul (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))).intervalIntegrable _ _)]
      exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
    have hZsum : ∑ i ∈ Z, c i * ∫ x in S..S + T, Complex.exp (b i * x) =
        (Z.card : ℂ) * c is * T := by
      have : ∀ i ∈ Z, c i * ∫ x in S..S + T, Complex.exp (b i * x) = c is * T := by
        intro i hi
        have hb0 : b i = 0 := by
          rw [hZdef, Finset.mem_filter] at hi
          exact hi.2
        rw [hcZ i hi, hb0]
        simp
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
      ring
    have hNsum : ‖∑ i ∈ N, c i * ∫ x in S..S + T, Complex.exp (b i * x)‖ ≤ K := by
      rw [hKdef]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      rw [hNdef, Finset.mem_filter] at hi
      rw [norm_mul]
      gcongr
      exact norm_integral_exp_mul_le_two_div hi.2 (hbre i hi.1) hS hT
    have hfilt := Finset.sum_filter_add_sum_filter_not P (fun i => b i = 0)
      (fun i => c i * ∫ x in S..S + T, Complex.exp (b i * x))
    rw [← hZdef, ← hNdef, hZsum] at hfilt
    rw [hsplit, ← hfilt]
    have hmain : ‖(Z.card : ℂ) * c is * (T : ℂ)‖ = T * A := by
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hT, hAdef]
      ring
    have := norm_sub_norm_le ((Z.card : ℂ) * c is * (T : ℂ))
      (-(∑ i ∈ N, c i * ∫ x in S..S + T, Complex.exp (b i * x)))
    rw [sub_neg_eq_add, norm_neg, hmain] at this
    linarith
  -- window length and starting point
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = ∑' i, m i := ⟨_, rfl⟩
  have hH : 0 ≤ H := hHdef ▸ tsum_nonneg hm0
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = A / 4 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 2 * (K + 1) / A := ⟨_, rfl⟩
  have hT : 0 < T := by rw [hTdef]; positivity
  have hTA : T * A = 2 * (K + 1) := by rw [hTdef]; field_simp
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ε₀ + (|C| + H + 1) / (δ * M) := ⟨_, rfl⟩
  have hS₀ : ε₀ ≤ S := by
    have : 0 ≤ (|C| + H + 1) / (δ * M) := by positivity
    rw [hSdef]; linarith
  have hS : 0 ≤ S := hε₀.trans hS₀
  obtain ⟨ε, hεmem, hεg⟩ : ∃ ε ∈ Set.Ioc S (S + T), δ < ‖g ε‖ := by
    by_contra hcon
    push Not at hcon
    have hbound : ‖∫ x in S..S + T, g x‖ ≤ δ * |S + T - S| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => by
        rw [Set.uIoc_of_le (by linarith)] at hx
        exact hcon x hx
    have hlow := hint S T hS hT.le
    rw [show S + T - S = T by ring, abs_of_pos hT] at hbound
    have : δ * T = (K + 1) / 2 := by
      have h4 : δ * T * 4 = T * A := by rw [hδdef]; ring
      linarith
    linarith
  have hε₀ε : ε₀ ≤ ε := hS₀.trans hεmem.1.le
  refine ⟨ε, hε₀ε, ?_⟩
  -- split into the light cone and a bounded remainder
  have hsumm : Summable (fun i => c i * Complex.exp (-(ε : ℂ) * w i)) := (hsum ε hε₀ε).of_norm
  have hdecomp := hsumm.sum_add_tsum_compl (s := P)
  obtain ⟨R, hRdef⟩ : ∃ R : ℂ, R = ∑' x : ↥((↑P : Set ι)ᶜ),
      c x * Complex.exp (-(ε : ℂ) * w x) := ⟨_, rfl⟩
  have hR : ‖R‖ ≤ H := by
    have hnormsub : Summable (fun x : ↥((↑P : Set ι)ᶜ) =>
        ‖c x * Complex.exp (-(ε : ℂ) * w x)‖) := (hsum ε hε₀ε).subtype _
    rw [hRdef, hHdef]
    refine (norm_tsum_le_tsum_norm hnormsub).trans ?_
    refine (hnormsub.tsum_le_tsum (g := fun x : ↥((↑P : Set ι)ᶜ) => m x)
      (fun x => ?_) (hm.subtype _)).trans ?_
    · have hx : (x : ι) ∉ P := x.2
      rw [hmemP, not_lt] at hx
      exact hmaj x hx ε hε₀ε
    · exact Summable.tsum_subtype_le m _ hm0 hm
  have hcone : ‖∑ i ∈ P, c i * Complex.exp (-(ε : ℂ) * w i)‖ = Real.exp (ε * M) * ‖g ε‖ := by
    rw [hPsum, norm_mul, hnormWs]
  have hexp : |C| + H + 1 ≤ Real.exp (ε * M) * δ := by
    have h0 : (S - ε₀) * M ≤ ε * M := by
      have : S - ε₀ ≤ ε := by linarith [hεmem.1]
      exact mul_le_mul_of_nonneg_right this hM.le
    have h2 : ε * M ≤ Real.exp (ε * M) := by
      have := Real.add_one_le_exp (ε * M); linarith
    have h3 : (S - ε₀) * M * δ = |C| + H + 1 := by
      rw [hSdef]; field_simp; ring
    nlinarith
  have hgt : Real.exp (ε * M) * δ < ‖∑ i ∈ P, c i * Complex.exp (-(ε : ℂ) * w i)‖ := by
    rw [hcone]
    exact mul_lt_mul_of_pos_left hεg (Real.exp_pos _)
  have htri := norm_sub_norm_le (∑ i ∈ P, c i * Complex.exp (-(ε : ℂ) * w i)) (-R)
  rw [sub_neg_eq_add, norm_neg] at htri
  have htotal : ∑' i, c i * Complex.exp (-(ε : ℂ) * w i) =
      ∑ i ∈ P, c i * Complex.exp (-(ε : ℂ) * w i) + R := by
    rw [← hdecomp, hRdef]
  rw [htotal]
  have := le_abs_self C
  linarith

/-! ## One-sided form: the real part is unbounded below -/

/-- `|∫_S^{S+T} cos(κ x) dx| ≤ 2/|κ|` for `κ ≠ 0`. -/
theorem abs_integral_cos_mul_window_le {κ : ℝ} (hκ : κ ≠ 0) (S T : ℝ) :
    |∫ x in S..S + T, Real.cos (κ * x)| ≤ 2 / |κ| := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hκ, integral_cos,
    smul_eq_mul, abs_mul, abs_inv]
  rw [div_eq_inv_mul]
  gcongr
  calc |Real.sin (κ * (S + T)) - Real.sin (κ * S)|
      ≤ |Real.sin (κ * (S + T))| + |Real.sin (κ * S)| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
    _ = 2 := by norm_num

/-- `∫_S^{S+T} cos(κ x) dx ≥ -b(κ)` with `b(0) = 0` and `b(κ) = 2/|κ|` otherwise. -/
theorem neg_le_integral_cos_mul (κ S : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    -(if κ = 0 then 0 else 2 / |κ|) ≤ ∫ x in S..S + T, Real.cos (κ * x) := by
  by_cases hκ : κ = 0
  · subst hκ
    simp only [if_pos, zero_mul, Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul,
      mul_one, neg_zero]
    linarith
  · rw [if_neg hκ]
    exact neg_le_of_abs_le (abs_integral_cos_mul_window_le hκ S T)

/-- Window integral of `α cos(ν x) - α (cos(a x) + cos(b x))/2`. -/
theorem integral_cos_sub_half_cos_add_cos (S T α ν a b : ℝ) :
    ∫ x in S..S + T, (α * Real.cos (ν * x) - α * ((Real.cos (a * x) + Real.cos (b * x)) / 2)) =
      α * (∫ x in S..S + T, Real.cos (ν * x)) -
        α * ((∫ x in S..S + T, Real.cos (a * x)) + (∫ x in S..S + T, Real.cos (b * x))) / 2 := by
  rw [intervalIntegral.integral_sub (f := fun x => α * Real.cos (ν * x))
      (g := fun x => α * ((Real.cos (a * x) + Real.cos (b * x)) / 2))
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_div,
    intervalIntegral.integral_add (f := fun x => Real.cos (a * x)) (g := fun x => Real.cos (b * x))
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-- **Open light cone, one-sided.**  If every light-cone exponent carries a nonzero frequency and
the light-cone coefficients are positive reals, the real part of the exponential sum is unbounded
below.  The leading term is `e^{εM} Σ c_i cos(ε ν_i)` with all `ν_i ≠ 0`, a trigonometric
polynomial of mean zero.  Against the nonnegative kernel `1 - cos(ν* ε)` its window integral is
`-(T/2)(c* + ⋯) + O(1)`, which forces values `≤ -c*/8` in every long window. -/
theorem exists_re_tsum_mul_exp_neg_lt_of_re_neg {ι : Type*} {w : ι → ℂ} {c : ι → ℝ} {ε₀ : ℝ}
    (hc : ∀ i, (w i).re < 0 → 0 < c i)
    (hfreq : ∀ i, (w i).re < 0 → (w i).im ≠ 0)
    (hfin : {i | (w i).re < 0}.Finite)
    {m : ι → ℝ} (hm0 : ∀ i, 0 ≤ m i) (hm : Summable m)
    (hmaj : ∀ i, 0 ≤ (w i).re → ∀ ε, ε₀ ≤ ε →
      ‖(c i : ℂ) * Complex.exp (-(ε : ℂ) * w i)‖ ≤ m i)
    (hsum : ∀ ε, ε₀ ≤ ε → Summable (fun i => ‖(c i : ℂ) * Complex.exp (-(ε : ℂ) * w i)‖))
    (hneg : ∃ i, (w i).re < 0) (C : ℝ) :
    ∃ ε : ℝ, ε₀ ≤ ε ∧ (∑' i, (c i : ℂ) * Complex.exp (-(ε : ℂ) * w i)).re < -C := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ι, P = hfin.toFinset := ⟨_, rfl⟩
  have hmemP : ∀ i, i ∈ P ↔ (w i).re < 0 := fun i => by
    rw [hPdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  obtain ⟨i₀, hi₀⟩ := hneg
  obtain ⟨is, hisP, hmax⟩ := P.exists_max_image (fun i => -(w i).re) ⟨i₀, (hmemP i₀).2 hi₀⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = -(w is).re := ⟨_, rfl⟩
  have hM : 0 < M := by
    have := (hmemP is).1 hisP
    linarith
  have hMle : ∀ i ∈ P, -(w i).re ≤ M := fun i hi => hMdef ▸ hmax i hi
  obtain ⟨Z, hZdef⟩ : ∃ Z : Finset ι, Z = P.filter (fun i => -(w i).re = M) := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : Finset ι, N = P.filter (fun i => ¬ -(w i).re = M) := ⟨_, rfl⟩
  have hisZ : is ∈ Z := by
    rw [hZdef, Finset.mem_filter]
    exact ⟨hisP, hMdef.symm⟩
  have hZP : ∀ i ∈ Z, i ∈ P := fun i hi => by
    rw [hZdef, Finset.mem_filter] at hi; exact hi.1
  have hZM : ∀ i ∈ Z, (w i).re = -M := fun i hi => by
    rw [hZdef, Finset.mem_filter] at hi; linarith [hi.2]
  have hNgap : ∀ i ∈ N, 0 < (w i).re + M := fun i hi => by
    rw [hNdef, Finset.mem_filter] at hi
    have := hMle i hi.1
    have hne := hi.2
    by_contra hcon
    exact hne (by linarith)
  set ν : ι → ℝ := fun i => (w i).im with hνdef
  set cs := c is with hcsdef
  have hcs : 0 < cs := hc is ((hmemP is).1 hisP)
  have hνs : ν is ≠ 0 := hfreq is ((hmemP is).1 hisP)
  set g : ℝ → ℝ := fun ε => ∑ i ∈ Z, c i * Real.cos (ν i * ε) with hgdef
  set b : ℝ → ℝ := fun κ => if κ = 0 then 0 else 2 / |κ| with hbdef
  have hb0 : ∀ κ, 0 ≤ b κ := fun κ => by
    simp only [hbdef]; split_ifs <;> positivity
  set K₁ : ℝ := ∑ i ∈ Z, c i * b (ν i) with hK₁def
  set K₂ : ℝ := ∑ i ∈ Z, c i * ((b (ν i + ν is) + b (ν i - ν is)) / 2) with hK₂def
  have hK₁ : 0 ≤ K₁ := Finset.sum_nonneg fun i hi => mul_nonneg (hc i ((hmemP i).1 (hZP i hi))).le
    (hb0 _)
  have hK₂ : 0 ≤ K₂ := Finset.sum_nonneg fun i hi => mul_nonneg (hc i ((hmemP i).1 (hZP i hi))).le
    (by have := hb0 (ν i + ν is); have := hb0 (ν i - ν is); positivity)
  have hcont : ∀ κ : ℝ, Continuous fun x : ℝ => Real.cos (κ * x) := fun κ => by fun_prop
  -- kernel identity bound on every window
  have hkernel : ∀ S T : ℝ, 0 ≤ T →
      ∫ x in S..S + T, g x * (1 - Real.cos (ν is * x)) ≤ K₁ + K₂ - T / 2 * cs := by
    intro S T hT
    have hexp : (fun x => g x * (1 - Real.cos (ν is * x))) = fun x =>
        ∑ i ∈ Z, (c i * Real.cos (ν i * x) -
          c i * ((Real.cos ((ν i + ν is) * x) + Real.cos ((ν i - ν is) * x)) / 2)) := by
      funext x
      simp only [hgdef, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h := Real.cos_add_cos ((ν i + ν is) * x) ((ν i - ν is) * x)
      rw [show ((ν i + ν is) * x + (ν i - ν is) * x) / 2 = ν i * x by ring,
        show ((ν i + ν is) * x - (ν i - ν is) * x) / 2 = ν is * x by ring] at h
      rw [h]
      ring
    rw [hexp, intervalIntegral.integral_finsetSum (f := fun i x => c i * Real.cos (ν i * x) -
        c i * ((Real.cos ((ν i + ν is) * x) + Real.cos ((ν i - ν is) * x)) / 2))
      fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _]
    have hterm : ∀ i ∈ Z, ∫ x in S..S + T, (c i * Real.cos (ν i * x) -
        c i * ((Real.cos ((ν i + ν is) * x) + Real.cos ((ν i - ν is) * x)) / 2)) ≤
          c i * b (ν i) + c i * ((b (ν i + ν is) + b (ν i - ν is)) / 2) -
            (if i = is then T / 2 * cs else 0) := by
      intro i hi
      have hci : 0 < c i := hc i ((hmemP i).1 (hZP i hi))
      rw [integral_cos_sub_half_cos_add_cos]
      have h1 : ∫ x in S..S + T, Real.cos (ν i * x) ≤ b (ν i) := by
        simp only [hbdef]
        split_ifs with h0
        · exfalso; exact hfreq i ((hmemP i).1 (hZP i hi)) h0
        · exact (le_abs_self _).trans (abs_integral_cos_mul_window_le h0 S T)
      have h2 : -b (ν i + ν is) ≤ ∫ x in S..S + T, Real.cos ((ν i + ν is) * x) :=
        neg_le_integral_cos_mul (ν i + ν is) S hT
      have h3 : -b (ν i - ν is) ≤ ∫ x in S..S + T, Real.cos ((ν i - ν is) * x) :=
        neg_le_integral_cos_mul (ν i - ν is) S hT
      have h1' := mul_le_mul_of_nonneg_left h1 hci.le
      have h2' := mul_le_mul_of_nonneg_left h2 hci.le
      have h3' := mul_le_mul_of_nonneg_left h3 hci.le
      split_ifs with his
      · subst his
        have hsub : ∫ x in S..S + T, Real.cos ((ν i - ν i) * x) = T := by simp
        have hb : b (ν i - ν i) = 0 := by simp [hbdef]
        rw [hsub, hb]
        rw [hsub] at h3'
        nlinarith
      · nlinarith
    calc ∑ i ∈ Z, ∫ x in S..S + T, (c i * Real.cos (ν i * x) -
          c i * ((Real.cos ((ν i + ν is) * x) + Real.cos ((ν i - ν is) * x)) / 2))
        ≤ ∑ i ∈ Z, (c i * b (ν i) + c i * ((b (ν i + ν is) + b (ν i - ν is)) / 2) -
            (if i = is then T / 2 * cs else 0)) := Finset.sum_le_sum hterm
      _ = K₁ + K₂ - T / 2 * cs := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' Z is,
          if_pos hisZ]
  -- window length, threshold and starting point
  set δ : ℝ := cs / 8 with hδdef
  have hδ : 0 < δ := by positivity
  set T : ℝ := 4 * (K₁ + K₂ + 1) / cs with hTdef
  have hT : 0 < T := by positivity
  have hwindow : ∀ S : ℝ, ∃ ε ∈ Set.Icc S (S + T), g ε < -δ := by
    intro S
    by_contra hcon
    push Not at hcon
    have hlow : ∫ x in S..S + T, (-(2 * δ)) ≤ ∫ x in S..S + T, g x * (1 - Real.cos (ν is * x)) := by
      refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (((continuous_finsetSum _ fun i _ => (hcont _).const_smul (c i)).mul
          (continuous_const.sub (hcont _))).intervalIntegrable _ _) fun x hx => ?_
      have hg := hcon x hx
      have hk0 : 0 ≤ 1 - Real.cos (ν is * x) := by linarith [Real.cos_le_one (ν is * x)]
      have hk2 : 1 - Real.cos (ν is * x) ≤ 2 := by linarith [Real.neg_one_le_cos (ν is * x)]
      nlinarith
    have hup := hkernel S T hT.le
    rw [intervalIntegral.integral_const, smul_eq_mul, show S + T - S = T by ring] at hlow
    have hTcs : T * cs = 4 * (K₁ + K₂ + 1) := by rw [hTdef]; field_simp
    nlinarith
  -- the subleading part decays relative to `e^{εM}`
  set ρ : ℝ → ℝ := fun ε => ∑ i ∈ N, c i * Real.exp (-(ε * ((w i).re + M))) with hρdef
  have hρlim : Filter.Tendsto ρ Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun ε : ℝ => ∑ i ∈ N, c i * Real.exp (-(ε * ((w i).re + M))))
        Filter.atTop (nhds (∑ i ∈ N, c i * 0)) := by
      refine tendsto_finsetSum _ fun i hi => (Real.tendsto_exp_atBot.comp ?_).const_mul _
      exact Filter.tendsto_neg_atTop_atBot.comp
        (Filter.tendsto_id.atTop_mul_const (hNgap i hi))
    simpa using this
  obtain ⟨S₁, hS₁⟩ := Filter.eventually_atTop.1
    (hρlim.eventually (Metric.ball_mem_nhds 0 (by positivity : (0 : ℝ) < δ / 2)))
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = ∑' i, m i := ⟨_, rfl⟩
  have hH : 0 ≤ H := hHdef ▸ tsum_nonneg hm0
  set S : ℝ := max (max ε₀ S₁) ((|C| + H + 1) / (δ / 2 * M)) with hSdef
  have hS₀ : ε₀ ≤ S := le_trans (le_max_left _ _) (le_max_left _ _)
  have hSS₁ : S₁ ≤ S := le_trans (le_max_right _ _) (le_max_left _ _)
  have hSbig : (|C| + H + 1) / (δ / 2 * M) ≤ S := le_max_right _ _
  obtain ⟨ε, hεmem, hgε⟩ := hwindow S
  have hε₀ε : ε₀ ≤ ε := hS₀.trans hεmem.1
  refine ⟨ε, hε₀ε, ?_⟩
  have hρε : |ρ ε| < δ / 2 := by
    have := hS₁ ε (hSS₁.trans hεmem.1)
    simpa [Real.dist_eq] using this
  -- split the real part
  have hsumm : Summable (fun i => (c i : ℂ) * Complex.exp (-(ε : ℂ) * w i)) :=
    (hsum ε hε₀ε).of_norm
  have hdecomp := hsumm.sum_add_tsum_compl (s := P)
  obtain ⟨R, hRdef⟩ : ∃ R : ℂ, R = ∑' x : ↥((↑P : Set ι)ᶜ),
      (c x : ℂ) * Complex.exp (-(ε : ℂ) * w x) := ⟨_, rfl⟩
  have hR : ‖R‖ ≤ H := by
    have hnormsub : Summable (fun x : ↥((↑P : Set ι)ᶜ) =>
        ‖(c x : ℂ) * Complex.exp (-(ε : ℂ) * w x)‖) := (hsum ε hε₀ε).subtype _
    rw [hRdef, hHdef]
    refine (norm_tsum_le_tsum_norm hnormsub).trans ?_
    refine (hnormsub.tsum_le_tsum (g := fun x : ↥((↑P : Set ι)ᶜ) => m x)
      (fun x => ?_) (hm.subtype _)).trans ?_
    · have hx : (x : ι) ∉ P := x.2
      rw [hmemP, not_lt] at hx
      exact hmaj x hx ε hε₀ε
    · exact Summable.tsum_subtype_le m _ hm0 hm
  have hre_term : ∀ i, ((c i : ℂ) * Complex.exp (-(ε : ℂ) * w i)).re =
      c i * Real.exp (-(ε * (w i).re)) * Real.cos (ν i * ε) := fun i => by
    rw [Complex.re_ofReal_mul, Complex.exp_re]
    simp only [neg_mul, Complex.neg_re, Complex.neg_im, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul, Real.cos_neg, hνdef]
    ring_nf
  have hPre : (∑ i ∈ P, (c i : ℂ) * Complex.exp (-(ε : ℂ) * w i)).re ≤
      Real.exp (ε * M) * (g ε + |ρ ε|) := by
    rw [Complex.re_sum]
    simp_rw [hre_term]
    have hsplitP := Finset.sum_filter_add_sum_filter_not P (fun i => -(w i).re = M)
      (fun i => c i * Real.exp (-(ε * (w i).re)) * Real.cos (ν i * ε))
    rw [← hZdef, ← hNdef] at hsplitP
    rw [← hsplitP]
    have hZeq : ∑ i ∈ Z, c i * Real.exp (-(ε * (w i).re)) * Real.cos (ν i * ε) =
        Real.exp (ε * M) * g ε := by
      rw [hgdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hZM i hi]
      ring_nf
    have hNle : ∑ i ∈ N, c i * Real.exp (-(ε * (w i).re)) * Real.cos (ν i * ε) ≤
        Real.exp (ε * M) * |ρ ε| := by
      have hρnn : 0 ≤ ρ ε := Finset.sum_nonneg fun i hi =>
        mul_nonneg (hc i ((hmemP i).1 (by rw [hNdef, Finset.mem_filter] at hi; exact hi.1))).le
          (Real.exp_pos _).le
      rw [abs_of_nonneg hρnn, hρdef, Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      have hci : 0 < c i := hc i ((hmemP i).1 (by rw [hNdef, Finset.mem_filter] at hi; exact hi.1))
      have hexp : Real.exp (ε * M) * (c i * Real.exp (-(ε * ((w i).re + M)))) =
          c i * Real.exp (-(ε * (w i).re)) := by
        rw [mul_left_comm, ← Real.exp_add]
        ring_nf
      rw [hexp]
      have := Real.cos_le_one (ν i * ε)
      have hpos : 0 < c i * Real.exp (-(ε * (w i).re)) := by positivity
      nlinarith
    rw [hZeq]
    nlinarith [hNle]
  have hmain : (∑ i ∈ P, (c i : ℂ) * Complex.exp (-(ε : ℂ) * w i)).re ≤
      -(Real.exp (ε * M) * (δ / 2)) := by
    refine hPre.trans ?_
    have : g ε + |ρ ε| ≤ -(δ / 2) := by linarith
    nlinarith [Real.exp_pos (ε * M)]
  have hexpbig : |C| + H + 1 ≤ Real.exp (ε * M) * (δ / 2) := by
    have hSε : S ≤ ε := hεmem.1
    have h1 : (|C| + H + 1) / (δ / 2 * M) * M ≤ ε * M :=
      mul_le_mul_of_nonneg_right (hSbig.trans hSε) hM.le
    have h2 : ε * M ≤ Real.exp (ε * M) := by
      have := Real.add_one_le_exp (ε * M); linarith
    have h3 : (|C| + H + 1) / (δ / 2 * M) * M * (δ / 2) = |C| + H + 1 := by field_simp
    nlinarith
  have htotal : ∑' i, (c i : ℂ) * Complex.exp (-(ε : ℂ) * w i) =
      ∑ i ∈ P, (c i : ℂ) * Complex.exp (-(ε : ℂ) * w i) + R := by
    rw [← hdecomp, hRdef]
  rw [htotal, Complex.add_re]
  have hRre : R.re ≤ H := (Complex.re_le_norm R).trans hR
  have := le_abs_self C
  linarith

end

end GaloisForLFunctions.HTGeometry

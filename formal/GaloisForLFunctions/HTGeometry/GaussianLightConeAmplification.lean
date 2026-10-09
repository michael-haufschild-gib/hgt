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

end

end GaloisForLFunctions.HTGeometry

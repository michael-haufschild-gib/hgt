import GaloisForLFunctions.HTGeometry.BuresWasserstein.OperatorLogRpow
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinBounds

/-!
# The Lie–Trotter limit of the Wasserstein barycentre

As the exponent `p` tends to `0` the Wasserstein barycentre of the powers `A₁^p, …, A_m^p`,
renormalized by the exponent, converges to the log-Euclidean mean

`lim_{p ↓ 0} Ω(ω; A₁^p, …, A_m^p)^{1/p} = exp(∑ wᵢ log Aᵢ)`.

The proof is the Loewner sandwich of Theorem 6.2 together with the first-order expansion
`p⁻¹(A^p − 1) → log A`: the sandwich forces `Ω(ω; 𝔸^p) = 1 + p·M_p` with `M_p → ∑ wᵢ log Aᵢ`, and
the scalar comparison `(1 + pu)^{1/p} → e^u` — uniform for `|u|` bounded — transfers through the
continuous functional calculus of `1 + p·M_p`.
-/

open scoped NNReal Ring Topology BigOperators Pointwise
open Filter

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry CFC

/-! ### The scalar comparison -/

/-- The logarithm is its own first-order Taylor polynomial up to a quadratic error. -/
lemma abs_log_one_add_sub_le {v : ℝ} (hv : |v| ≤ 1 / 2) :
    |Real.log (1 + v) - v| ≤ 2 * v ^ 2 := by
  have hlt : |(-v)| < 1 := by
    rw [_root_.abs_neg]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le hlt 1
  simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one,
    sub_neg_eq_add] at h
  have habs : |Real.log (1 + v) - v| = |-v + Real.log (1 + v)| := by
    rw [show -v + Real.log (1 + v) = Real.log (1 + v) - v by ring]
  rw [habs]
  refine h.trans ?_
  have h1 : |(-v)| = |v| := _root_.abs_neg v
  rw [h1]
  have h2 : (1 : ℝ) / 2 ≤ 1 - |v| := by
    have := abs_nonneg v
    linarith
  have h3 : |v| ^ (1 + 1) = v ^ 2 := by
    rw [show (1 : ℕ) + 1 = 2 from rfl, ← abs_pow, abs_of_nonneg (sq_nonneg v)]
  rw [h3]
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - |v|)]
  nlinarith [sq_nonneg v, abs_nonneg v]

/-- **The scalar Lie–Trotter comparison.**  `(1 + pu)^{1/p}` is within `O(p)` of `eᵘ`,
uniformly for `|u| ≤ C`. -/
lemma abs_rpow_sub_exp_le {C u p : ℝ} (hu : |u| ≤ C) (hp : 0 < p)
    (h1 : p * C ≤ 1 / 2) (h2 : 2 * p * C ^ 2 ≤ 1) :
    |(1 + p * u) ^ p⁻¹ - Real.exp u| ≤ 4 * Real.exp C * p * C ^ 2 := by
  have hC : (0 : ℝ) ≤ C := le_trans (abs_nonneg u) hu
  have hv : |p * u| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hp]
    calc p * |u| ≤ p * C := mul_le_mul_of_nonneg_left hu hp.le
      _ ≤ 1 / 2 := h1
  have hpos : (0 : ℝ) < 1 + p * u := by
    have := abs_le.mp hv
    linarith [this.1]
  have hrpow : (1 + p * u) ^ p⁻¹ = Real.exp (p⁻¹ * Real.log (1 + p * u)) := by
    rw [Real.rpow_def_of_pos hpos, mul_comm]
  have hd : |p⁻¹ * Real.log (1 + p * u) - u| ≤ 2 * p * C ^ 2 := by
    have hid : p⁻¹ * Real.log (1 + p * u) - u
        = p⁻¹ * (Real.log (1 + p * u) - p * u) := by
      field_simp
    rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hp)]
    have hb := abs_log_one_add_sub_le hv
    have hu2 : (p * u) ^ 2 ≤ p ^ 2 * C ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hu hp.le
      have hpu : |p * u| ≤ p * C := by rw [abs_mul, abs_of_pos hp]; exact h
      nlinarith [abs_nonneg (p * u), sq_abs (p * u), mul_nonneg hp.le hC]
    calc p⁻¹ * |Real.log (1 + p * u) - p * u| ≤ p⁻¹ * (2 * (p * u) ^ 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ p⁻¹ * (2 * (p ^ 2 * C ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
      _ = 2 * p * C ^ 2 := by field_simp
  have hdiff : |p⁻¹ * Real.log (1 + p * u) - u| ≤ 1 := hd.trans h2
  set a := p⁻¹ * Real.log (1 + p * u) with hadef
  have hfac : Real.exp a - Real.exp u = Real.exp u * (Real.exp (a - u) - 1) := by
    rw [Real.exp_sub]
    field_simp
  have hb1 : |Real.exp (a - u) - 1| ≤ 2 * |a - u| := Real.abs_exp_sub_one_le hdiff
  rw [hrpow]
  calc |Real.exp a - Real.exp u| = Real.exp u * |Real.exp (a - u) - 1| := by
        rw [hfac, abs_mul, abs_of_pos (Real.exp_pos u)]
    _ ≤ Real.exp C * (2 * (2 * p * C ^ 2)) := by
        refine mul_le_mul ?_ (hb1.trans ?_) (abs_nonneg _) (Real.exp_pos C).le
        · exact Real.exp_le_exp.mpr (le_trans (le_abs_self u) hu)
        · exact mul_le_mul_of_nonneg_left hd (by norm_num)
    _ = 4 * Real.exp C * p * C ^ 2 := by ring

/-! ### The operator comparison -/

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Points of the spectrum are within the norm of the shift. -/
lemma abs_sub_one_le_of_mem_spectrum {T : A} {x : ℝ} (hx : x ∈ spectrum ℝ T) :
    |x - 1| ≤ ‖T - 1‖ := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exfalso
    have hempty : (spectrum ℝ T) = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false, spectrum.mem_iff, not_not]
      exact isUnit_of_subsingleton _
    rw [hempty] at hx
    exact hx
  · have hmem : x - 1 ∈ spectrum ℝ (T - (1 : A)) := by
      have h := spectrum.sub_singleton_eq (R := ℝ) T 1
      have hx1 : x - 1 ∈ spectrum ℝ T - ({1} : Set ℝ) := ⟨x, hx, 1, rfl, rfl⟩
      rw [h] at hx1
      simpa using hx1
    have h := spectrum.norm_le_norm_of_mem (𝕜 := ℝ) hmem
    rwa [Real.norm_eq_abs] at h

/-- **The operator Lie–Trotter comparison.**  Near the identity the `1/p`-th power and the
exponential of `p⁻¹(T − 1)` differ by `O(p)`. -/
theorem norm_rpow_sub_exp_le {T : A} (hT : IsStrictlyPositive T) {p C : ℝ}
    (hp : 0 < p) (hTb : ‖T - 1‖ ≤ p * C)
    (h1 : p * C ≤ 1 / 2) (h2 : 2 * p * C ^ 2 ≤ 1) :
    ‖T ^ p⁻¹ - NormedSpace.exp (p⁻¹ • (T - 1))‖ ≤ 4 * Real.exp C * p * C ^ 2 := by
  have hTsa : IsSelfAdjoint T := hT.isSelfAdjoint
  have hcE : ContinuousOn (fun x : ℝ => p⁻¹ * (x - 1)) (spectrum ℝ T) := by fun_prop
  have hEid : cfc (fun x : ℝ => x - 1) T = T - 1 := by
    rw [cfc_sub _ _ T (by fun_prop) (by fun_prop), cfc_id' ℝ T, cfc_const_one ℝ T]
  have hE : p⁻¹ • (T - 1) = cfc (fun x : ℝ => p⁻¹ * (x - 1)) T := by
    rw [show (fun x : ℝ => p⁻¹ * (x - 1)) = (fun x : ℝ => p⁻¹ • (x - 1)) from rfl,
      cfc_smul _ _ T (by fun_prop), hEid]
  have hEsa : IsSelfAdjoint (p⁻¹ • (T - 1)) :=
    IsSelfAdjoint.smul (star_trivial _) (hTsa.sub (IsSelfAdjoint.one A))
  have hexp : NormedSpace.exp (p⁻¹ • (T - 1))
      = cfc (fun x : ℝ => Real.exp (p⁻¹ * (x - 1))) T := by
    rw [← CFC.real_exp_eq_normedSpace_exp hEsa, hE,
      ← cfc_comp' Real.exp (fun x : ℝ => p⁻¹ * (x - 1)) T (by fun_prop) hcE]
  have hrp : T ^ p⁻¹ = cfc (fun x : ℝ => x ^ p⁻¹) T := rpow_eq_cfc_real hT.nonneg
  have hcr : ContinuousOn (fun x : ℝ => x ^ p⁻¹) (spectrum ℝ T) := by
    refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro x hx
    exact Or.inl (ne_of_gt (IsStrictlyPositive.spectrum_pos (𝕜 := ℝ) hT hx))
  have hce : ContinuousOn (fun x : ℝ => Real.exp (p⁻¹ * (x - 1))) (spectrum ℝ T) := by fun_prop
  rw [hrp, hexp, ← cfc_sub _ _ T hcr hce]
  refine norm_cfc_le (by positivity) fun x hx => ?_
  rw [Real.norm_eq_abs]
  set u : ℝ := p⁻¹ * (x - 1) with hudef
  have hxu : 1 + p * u = x := by
    rw [hudef, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hp), one_mul]
    ring
  have hun : |u| ≤ C := by
    have hb : |x - 1| ≤ p * C := (abs_sub_one_le_of_mem_spectrum hx).trans hTb
    rw [hudef, abs_mul, abs_of_pos (inv_pos.mpr hp)]
    calc p⁻¹ * |x - 1| ≤ p⁻¹ * (p * C) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C := by field_simp
  have hval := abs_rpow_sub_exp_le hun hp h1 h2
  rw [hxu] at hval
  exact hval

/-! ### The Lie–Trotter limit -/

/-- The inverse of a real power is the power of the inverse. -/
lemma ringInverse_rpow {a : A} (ha : IsStrictlyPositive a) {p : ℝ} (hp : 0 < p) :
    ((a ^ p)⁻¹ʳ : A) = (a⁻¹ʳ : A) ^ p := by
  have hap : IsStrictlyPositive (a ^ p) := IsStrictlyPositive.rpow a p ha
  rw [CFC.inverse_eq_rpow_neg_one hap, CFC.inverse_eq_rpow_neg_one ha,
    CFC.rpow_rpow a p (-1) (ne_of_gt hp) ha, CFC.rpow_rpow a (-1) p (by norm_num) ha]
  ring_nf

variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → A}

/-- **Corollary 6.4 (Kim–Mer–Pálfia).**  The Wasserstein barycentre of the `p`-th powers,
renormalized by the exponent, converges to the log-Euclidean mean. -/
theorem tendsto_rpow_isWassersteinPoint_logEuclidean {X : ℝ → A}
    (hs : s.Nonempty) (hw : ∀ i ∈ s, 0 < w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hX : ∀ p : ℝ, 0 < p → IsWassersteinPoint s w (fun i => Av i ^ p) (X p)) :
    Tendsto (fun p : ℝ => (X p) ^ p⁻¹) (𝓝[>] 0)
      (𝓝 (NormedSpace.exp (∑ i ∈ s, w i • CFC.log (Av i)))) := by
  have hw' : ∀ i ∈ s, (0 : ℝ) ≤ w i := fun i hi => (hw i hi).le
  set Mlim : A := ∑ i ∈ s, w i • CFC.log (Av i) with hMlimdef
  set U : ℝ → A := fun p => ∑ i ∈ s, w i • (p⁻¹ • (Av i ^ p - 1)) with hUdef
  set L : ℝ → A := fun p => -∑ i ∈ s, w i • (p⁻¹ • ((Av i)⁻¹ʳ ^ p - (1 : A))) with hLdef
  -- the two envelopes converge to the log-Euclidean mean
  have hUlim : Tendsto U (𝓝[>] 0) (𝓝 Mlim) := by
    rw [hUdef, hMlimdef]
    exact tendsto_finsetSum s fun i hi =>
      (tendsto_rpow_sub_one_log (hA i hi)).const_smul (w i)
  have hLlim : Tendsto L (𝓝[>] 0) (𝓝 Mlim) := by
    have h : Tendsto (fun p : ℝ => ∑ i ∈ s, w i • (p⁻¹ • ((Av i)⁻¹ʳ ^ p - (1 : A))))
        (𝓝[>] 0) (𝓝 (∑ i ∈ s, w i • CFC.log ((Av i)⁻¹ʳ : A))) :=
      tendsto_finsetSum s fun i hi =>
        (tendsto_rpow_sub_one_log (hA i hi).ringInverse).const_smul (w i)
    have heq : ∑ i ∈ s, w i • CFC.log ((Av i)⁻¹ʳ : A) = -Mlim := by
      rw [hMlimdef, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i hi => by rw [log_ringInverse (hA i hi), smul_neg]
    rw [heq] at h
    rw [hLdef]
    simpa using h.neg
  -- the sandwich
  have hsand : ∀ p : ℝ, 0 < p → L p ≤ p⁻¹ • (X p - 1) ∧ p⁻¹ • (X p - 1) ≤ U p := by
    intro p hp
    have hAp : ∀ i ∈ s, IsStrictlyPositive (Av i ^ p) := fun i hi =>
      IsStrictlyPositive.rpow (Av i) p (hA i hi)
    have hpinv : (0 : ℝ) < p⁻¹ := inv_pos.mpr hp
    have hone : ∑ i ∈ s, w i • (1 : A) = 1 := by
      rw [← Finset.sum_smul, hwsum, one_smul]
    constructor
    · have hlow := (hX p hp).two_sub_harm_le hs hw hwsum hAp
      have e1 : ∑ i ∈ s, w i • (((Av i)⁻¹ʳ : A) ^ p - 1)
          = (∑ i ∈ s, w i • ((Av i ^ p)⁻¹ʳ : A)) - 1 := by
        have e2 : ∀ i ∈ s, w i • (((Av i)⁻¹ʳ : A) ^ p - 1)
            = w i • ((Av i ^ p)⁻¹ʳ : A) - w i • (1 : A) := fun i hi => by
          rw [ringInverse_rpow (hA i hi) hp, smul_sub]
        rw [Finset.sum_congr rfl e2, Finset.sum_sub_distrib, hone]
      have h2 : (2 : ℝ) • (1 : A) = (1 : A) + 1 := by
        rw [show (2 : ℝ) = (1 : ℝ) + 1 by norm_num, add_smul, one_smul]
      have hstep : -∑ i ∈ s, w i • (((Av i)⁻¹ʳ : A) ^ p - 1) ≤ X p - 1 := by
        have hid : -∑ i ∈ s, w i • (((Av i)⁻¹ʳ : A) ^ p - 1)
            = ((2 : ℝ) • (1 : A) - ∑ i ∈ s, w i • ((Av i ^ p)⁻¹ʳ : A)) - 1 := by
          rw [e1, h2]
          abel
        rw [hid]
        exact sub_le_sub_right hlow 1
      have hsm := smul_le_smul_of_nonneg_left hstep hpinv.le
      show L p ≤ p⁻¹ • (X p - 1)
      refine le_trans (le_of_eq ?_) hsm
      rw [hLdef]
      simp only
      rw [smul_neg, Finset.smul_sum]
      exact congrArg Neg.neg (Finset.sum_congr rfl fun i _ => (smul_comm _ _ _).symm)
    · have hup := (hX p hp).le_arithMean hw' hwsum hAp
      have e1 : ∑ i ∈ s, w i • (Av i ^ p - (1 : A)) = (∑ i ∈ s, w i • (Av i ^ p)) - 1 := by
        have e2 : ∀ i ∈ s, w i • (Av i ^ p - (1 : A))
            = w i • (Av i ^ p) - w i • (1 : A) := fun i _ => smul_sub _ _ _
        rw [Finset.sum_congr rfl e2, Finset.sum_sub_distrib, hone]
      have hstep : X p - 1 ≤ ∑ i ∈ s, w i • (Av i ^ p - (1 : A)) := by
        rw [e1]
        exact sub_le_sub_right hup 1
      have hsm := smul_le_smul_of_nonneg_left hstep hpinv.le
      show p⁻¹ • (X p - 1) ≤ U p
      refine hsm.trans (le_of_eq ?_)
      rw [hUdef]
      simp only
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  -- the renormalized barycentre converges to the log-Euclidean mean
  have hMlimit : Tendsto (fun p : ℝ => p⁻¹ • (X p - 1)) (𝓝[>] 0) (𝓝 Mlim) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hUn : Tendsto (fun p => ‖U p - Mlim‖) (𝓝[>] 0) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hUlim
    have hLn : Tendsto (fun p => ‖L p - Mlim‖) (𝓝[>] 0) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hLlim
    have hg : Tendsto (fun p => ‖U p - Mlim‖ + 2 * ‖L p - Mlim‖) (𝓝[>] 0) (𝓝 0) := by
      simpa using hUn.add (hLn.const_mul 2)
    refine squeeze_zero' (Filter.Eventually.of_forall fun p => norm_nonneg _) ?_ hg
    filter_upwards [self_mem_nhdsWithin] with p hp
    obtain ⟨h1, h2⟩ := hsand p hp
    have hpos : (0 : A) ≤ p⁻¹ • (X p - 1) - L p := sub_nonneg.mpr h1
    have hle : p⁻¹ • (X p - 1) - L p ≤ U p - L p := sub_le_sub_right h2 _
    have hn1 : ‖p⁻¹ • (X p - 1) - L p‖ ≤ ‖U p - L p‖ := norm_le_norm_of_le hpos hle
    have hn2 : ‖U p - L p‖ ≤ ‖U p - Mlim‖ + ‖L p - Mlim‖ := by
      have hid : U p - L p = (U p - Mlim) - (L p - Mlim) := by abel
      rw [hid]
      exact norm_sub_le _ _
    have hn3 : ‖p⁻¹ • (X p - 1) - Mlim‖
        ≤ ‖p⁻¹ • (X p - 1) - L p‖ + ‖L p - Mlim‖ := by
      have hid : p⁻¹ • (X p - 1) - Mlim = (p⁻¹ • (X p - 1) - L p) + (L p - Mlim) := by abel
      rw [hid]
      exact norm_add_le _ _
    linarith
  -- the eventual size bounds
  set C : ℝ := ‖Mlim‖ + 1 with hCdef
  have hC0 : (0 : ℝ) ≤ C := by positivity
  have hCpos : (0 : ℝ) < C := by
    have := norm_nonneg Mlim
    rw [hCdef]
    linarith
  have hMb : ∀ᶠ p in 𝓝[>] (0 : ℝ), ‖p⁻¹ • (X p - 1)‖ ≤ C := by
    have h := hMlimit
    rw [tendsto_iff_norm_sub_tendsto_zero] at h
    have h1 : ∀ᶠ p in 𝓝[>] (0 : ℝ), ‖p⁻¹ • (X p - 1) - Mlim‖ < 1 :=
      h.eventually_lt_const (by norm_num)
    filter_upwards [h1] with p hp
    have h2 : ‖p⁻¹ • (X p - 1)‖ ≤ ‖p⁻¹ • (X p - 1) - Mlim‖ + ‖Mlim‖ := by
      have hid : p⁻¹ • (X p - 1) = (p⁻¹ • (X p - 1) - Mlim) + Mlim := by abel
      rw [hid]
      exact (norm_add_le _ _).trans (by rw [add_sub_cancel_right])
    rw [hCdef]
    linarith
  have hsmall : ∀ᶠ p in 𝓝[>] (0 : ℝ), p * C ≤ 1 / 2 ∧ 2 * p * C ^ 2 ≤ 1 := by
    have hd : (0 : ℝ) < min (1 / (2 * C)) (1 / (2 * C ^ 2)) := by positivity
    have h1 : ∀ᶠ x in 𝓝 (0 : ℝ), x < min (1 / (2 * C)) (1 / (2 * C ^ 2)) :=
      Filter.eventually_iff_exists_mem.mpr ⟨Set.Iio _, Iio_mem_nhds hd, fun x hx => hx⟩
    filter_upwards [h1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with p hp hp0
    have hp1 : p < 1 / (2 * C) := lt_of_lt_of_le hp (min_le_left _ _)
    have hp2 : p < 1 / (2 * C ^ 2) := lt_of_lt_of_le hp (min_le_right _ _)
    constructor
    · rw [lt_div_iff₀ (by positivity)] at hp1
      linarith
    · rw [lt_div_iff₀ (by positivity)] at hp2
      linarith
  -- the comparison with the exponential
  have hcomp : ∀ᶠ p in 𝓝[>] (0 : ℝ),
      ‖(X p) ^ p⁻¹ - NormedSpace.exp (p⁻¹ • (X p - 1))‖ ≤ 4 * Real.exp C * p * C ^ 2 := by
    filter_upwards [hMb, hsmall, self_mem_nhdsWithin] with p hM hsm hp
    refine norm_rpow_sub_exp_le (hX p hp).1 hp ?_ hsm.1 hsm.2
    have hid : X p - 1 = p • (p⁻¹ • (X p - 1)) := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hp), one_smul]
    rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left hM hp.le
  have hg2 : Tendsto (fun p : ℝ => 4 * Real.exp C * p * C ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun p : ℝ => 4 * Real.exp C * p * C ^ 2) := by fun_prop
    have h0 : Tendsto (fun p : ℝ => 4 * Real.exp C * p * C ^ 2) (𝓝 0) (𝓝 0) := by
      simpa using hcont.tendsto 0
    exact h0.mono_left nhdsWithin_le_nhds
  have hdiff : Tendsto (fun p : ℝ => (X p) ^ p⁻¹ - NormedSpace.exp (p⁻¹ • (X p - 1)))
      (𝓝[>] 0) (𝓝 0) := squeeze_zero_norm' hcomp hg2
  have hexp : Tendsto (fun p : ℝ => NormedSpace.exp (p⁻¹ • (X p - 1))) (𝓝[>] 0)
      (𝓝 (NormedSpace.exp Mlim)) :=
    ((NormedSpace.exp_analytic (𝕂 := ℝ) Mlim).continuousAt.tendsto).comp hMlimit
  have hsum := hdiff.add hexp
  simpa using hsum

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein

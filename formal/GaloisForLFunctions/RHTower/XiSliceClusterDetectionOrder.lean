import GaloisForLFunctions.RHTower.XiSliceMixedOrdinateDetectionOrder
import GaloisForLFunctions.RHTower.XiSliceCoeffNearDoublePositivity
import GaloisForLFunctions.RHTower.XiSliceFiniteOrderReduction

/-!
# Detection order of an off-line zero shadowed by a cluster of nearby zeros

Let `ρ` be a zero of `ξ` off the critical line, with ordinate `γ` and displacement
`δ = |Re ρ − ½| > 0`.  Let `K` be a finite set of `k` zero copies within distance `ε` of `γ`,
containing every copy at `γ` itself.  The near-double positivity law
(`xiSliceCoeff_re_pos_of_exposed_nearDouble_card`) shows that such a cluster keeps the low slice
coefficients positive: a near-double shadow delays detection.  This file bounds the delay from
above.

Split the Hadamard product at `K`: `Ξ(z) = Ξ(0) Π_{q ∈ K} E₁(z/z_q) · P(z)` with `P` the canonical
product over the other copies.  The uniform pair identity
`E₁((γ − ix)/z) E₁((γ + ix)/z) = ((z − γ)² + x²) e^{2γ/z}/z²` (`weierstrassE1_pair_eq_sq_sub`, valid
also for `z = γ`) gives

  `g_γ(x) = A · Π_{q ∈ K} (x² + w_q) · Q(x)`,   `w_q = (z_q − γ)²`,  `|w_q| ≤ ε²`,

with `A ≠ 0` and `Q(x) = P(γ − ix) P(γ + ix)`, `Q(x)/Q(0) = Π_{q ∉ K} (1 + x²/w_q)`.  On `|x| = 2δ`:
`|Q| ≤ |Q(0)| B` with `B = 5^m e^{4δ²S}` as before, and `|Π(x² + w_q) − x^{2k}| ≤ (4δ²)^k η`,
`η = (1 + ε²/(4δ²))^k − 1`.  Cauchy's estimate for `A (Π(x² + w_q) − x^{2k}) Q` then gives

  `|c_{2k}(γ) − A Q(0)| ≤ |A| |Q(0)| B η`,

and the Cauchy tail estimate shifted by `2k` gives:

**Theorem** (`exists_re_xiSliceCoeff_neg_of_offLine_cluster`).  If at most `m` copies sit at
`γ ± iδ`, the copies outside `K` and away from `γ ± iδ` have `Σ 1/|z − γ|² ≤ S`, and
`2 B (1 + η) < 2^N (1 − B η)`, then some `c_n(γ)` with `n < 2k + N` has negative real part.

For `ε → 0` the condition tends to `2B < 2^N`: a cluster of `k` zeros collapsing onto the
ordinate delays detection by `2k` orders and no more, continuously in the cluster's diameter.

**Sharp bracket** (`exists_first_negative_xiSliceCoeff_of_critical_cluster`).  When the cluster
consists of critical zeros and also satisfies the near-double condition
`3k ε² Σ_{exposed} (Im z)²/|z − γ|⁴ ≤ 1`, every coefficient of order `≤ 2k` is nonnegative and some
coefficient of order in `(2k, 2k + N)` is negative.  The first negative slice coefficient at the
ordinate of an off-line zero shadowed by `k` nearby critical zeros lies strictly between `2k` and
`2k + N`.
-/

open Complex Filter Topology Metric

namespace RHTower

noncomputable section

/-- **The genus-one pair identity, uniform form.**  For `z ≠ 0`,
`E₁((t − σ)/z) E₁((t + σ)/z) = ((z − t)² − σ²) e^{2t/z}/z²`.  Unlike `weierstrassE1_pair_eq` it
holds also at `z = t`. -/
theorem weierstrassE1_pair_eq_sq_sub (t σ z : ℂ) (hz : z ≠ 0) :
    weierstrassE1 ((t - σ) / z) * weierstrassE1 ((t + σ) / z) =
      ((z - t) ^ 2 - σ ^ 2) * (Complex.exp (2 * t / z) / z ^ 2) := by
  unfold weierstrassE1
  have hexp : Complex.exp ((t - σ) / z) * Complex.exp ((t + σ) / z) = Complex.exp (2 * t / z) := by
    rw [← Complex.exp_add]
    congr 1
    field_simp
    ring
  calc (1 - (t - σ) / z) * Complex.exp ((t - σ) / z) * ((1 - (t + σ) / z) *
        Complex.exp ((t + σ) / z))
      = ((1 - (t - σ) / z) * (1 - (t + σ) / z)) *
          (Complex.exp ((t - σ) / z) * Complex.exp ((t + σ) / z)) := by ring
    _ = _ := by
        rw [hexp]
        field_simp
        ring

/-- **Product perturbation.**  If `‖b_q‖ ≤ e` for `q ∈ K`, then
`‖Π_K (a + b_q) − a^{|K|}‖ ≤ (‖a‖ + e)^{|K|} − ‖a‖^{|K|}`. -/
theorem norm_prod_add_sub_pow_le {ι : Type*} (K : Finset ι) (a : ℂ) (b : ι → ℂ) {e : ℝ}
    (hb : ∀ q ∈ K, ‖b q‖ ≤ e) :
    ‖∏ q ∈ K, (a + b q) - a ^ K.card‖ ≤ (‖a‖ + e) ^ K.card - ‖a‖ ^ K.card := by
  classical
  induction K using Finset.induction_on with
  | empty => simp
  | insert j K hj ih =>
    have hbK : ∀ q ∈ K, ‖b q‖ ≤ e := fun q hq => hb q (Finset.mem_insert_of_mem hq)
    have hbj : ‖b j‖ ≤ e := hb j (Finset.mem_insert_self j K)
    have he : 0 ≤ e := (norm_nonneg _).trans hbj
    have hIH := ih hbK
    have hprodle : ‖∏ q ∈ K, (a + b q)‖ ≤ (‖a‖ + e) ^ K.card := by
      rw [norm_prod]
      calc ∏ q ∈ K, ‖a + b q‖ ≤ ∏ _q ∈ K, (‖a‖ + e) :=
            Finset.prod_le_prod (fun q _ => norm_nonneg _)
              fun q hq => (norm_add_le _ _).trans (by linarith [hbK q hq])
        _ = (‖a‖ + e) ^ K.card := Finset.prod_const _
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    have e1 : (a + b j) * ∏ q ∈ K, (a + b q) - a ^ (K.card + 1) =
        (a + b j) * (∏ q ∈ K, (a + b q) - a ^ K.card) + b j * a ^ K.card := by ring
    rw [e1]
    have hpowle : ‖a‖ ^ K.card ≤ (‖a‖ + e) ^ K.card :=
      pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
    calc ‖(a + b j) * (∏ q ∈ K, (a + b q) - a ^ K.card) + b j * a ^ K.card‖
        ≤ ‖a + b j‖ * ‖∏ q ∈ K, (a + b q) - a ^ K.card‖ + ‖b j‖ * ‖a‖ ^ K.card := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_pow]
      _ ≤ (‖a‖ + e) * ((‖a‖ + e) ^ K.card - ‖a‖ ^ K.card) + e * ‖a‖ ^ K.card := by
          have h1 : ‖a + b j‖ ≤ ‖a‖ + e := (norm_add_le _ _).trans (by linarith)
          gcongr
      _ = (‖a‖ + e) ^ (K.card + 1) - ‖a‖ ^ (K.card + 1) := by ring

/-- The zero copies outside a finite set `K`. -/
abbrev XiZeroCopyOff (K : Finset XiZeroCopy) := ↥((K : Set XiZeroCopy)ᶜ)

/-- The canonical product over the zero copies outside `K`. -/
def xiCanonicalProductOff (K : Finset XiZeroCopy) : ℂ → ℂ :=
  canonicalProductE1Indexed (fun q : XiZeroCopyOff K => xiSpectralPoint q.1)

theorem xiCanonicalProductOff_inv_sq_summable (K : Finset XiZeroCopy) :
    Summable (fun q : XiZeroCopyOff K => 1 / ‖xiSpectralPoint q.1‖ ^ (2 : ℕ)) :=
  xiSpectralPoint_inv_sq_summable.comp_injective Subtype.val_injective

theorem differentiable_xiCanonicalProductOff (K : Finset XiZeroCopy) :
    Differentiable ℂ (xiCanonicalProductOff K) := fun z =>
  (canonicalProductE1Indexed_analytic (fun q : XiZeroCopyOff K => xiSpectralPoint q.1)
    (fun q => xiSpectralPoint_ne_zero q.1) (xiCanonicalProductOff_inv_sq_summable K) z
    (Set.mem_univ _)).differentiableAt

theorem xiCanonicalProductOff_ne_zero {K : Finset XiZeroCopy} {z : ℂ}
    (hz : ∀ q : XiZeroCopy, xiSpectralPoint q = z → q ∈ K) : xiCanonicalProductOff K z ≠ 0 :=
  canonicalProductE1Indexed_ne_zero (fun q : XiZeroCopyOff K => xiSpectralPoint q.1)
    (fun q => xiSpectralPoint_ne_zero q.1) (xiCanonicalProductOff_inv_sq_summable K)
    fun q h => q.2 (hz q.1 h.symm)

/-- **Splitting the canonical product at a finite set.** -/
theorem xiCanonicalProduct_eq_prod_mul_off (K : Finset XiZeroCopy) (z : ℂ) :
    xiCanonicalProduct z =
      (∏ q ∈ K, weierstrassE1 (z / xiSpectralPoint q)) * xiCanonicalProductOff K z := by
  set f : XiZeroCopy → ℂ := fun q => weierstrassE1 (z / xiSpectralPoint q) with hf
  have hs : Multipliable (f ∘ Subtype.val : ↥(K : Set XiZeroCopy) → ℂ) := Multipliable.of_finite
  have hgsum : Summable (fun q : XiZeroCopyOff K => weierstrassE1 (z / xiSpectralPoint q.1) - 1) :=
    (canonicalProductE1Indexed_sub_one_norm_summable
      (fun q : XiZeroCopyOff K => xiSpectralPoint q.1)
      (fun q => xiSpectralPoint_ne_zero q.1) (xiCanonicalProductOff_inv_sq_summable K) z).of_norm
  have hsc : Multipliable (f ∘ Subtype.val : ↥((K : Set XiZeroCopy)ᶜ) → ℂ) := by
    have hm := Complex.multipliable_one_add_of_summable hgsum
    convert hm using 1
    ext q
    simp only [Function.comp_apply, hf]
    ring
  rw [xiCanonicalProduct, canonicalProductE1Indexed, ← hs.tprod_mul_tprod_compl hsc,
    Finset.tprod_subtype']
  rfl

/-- **The off-`K` product along a horizontal slice.**  If `K` contains every copy at the real
point `t`, then `P(t − ix) P(t + ix)/P(t)² = lim Π_{q ∉ K} (1 + x²/(z_q − t)²)`. -/
theorem tendsto_prod_off_one_add_sq_div {K : Finset XiZeroCopy} {t : ℝ}
    (hK : ∀ q : XiZeroCopy, xiSpectralPoint q = t → q ∈ K) (x : ℂ) :
    Tendsto (fun F : Finset (XiZeroCopyOff K) => ∏ q ∈ F,
        (1 + x ^ 2 / (xiSpectralPoint q.1 - t) ^ 2)) atTop
      (𝓝 (xiCanonicalProductOff K ((t : ℂ) - I * x) * xiCanonicalProductOff K ((t : ℂ) + I * x) /
        xiCanonicalProductOff K t ^ 2)) := by
  have hP : TendstoLocallyUniformlyOn
      (fun (F : Finset (XiZeroCopyOff K)) w => ∏ q ∈ F, weierstrassE1 (w / xiSpectralPoint q.1))
      (xiCanonicalProductOff K) atTop Set.univ :=
    canonicalProductE1Indexed_hasProdLocallyUniformlyOn
      (fun q : XiZeroCopyOff K => xiSpectralPoint q.1) (fun q => xiSpectralPoint_ne_zero q.1)
      (xiCanonicalProductOff_inv_sq_summable K)
  have hpt : ∀ w : ℂ, Tendsto (fun F : Finset (XiZeroCopyOff K) =>
      ∏ q ∈ F, weierstrassE1 (w / xiSpectralPoint q.1)) atTop
        (𝓝 (xiCanonicalProductOff K w)) :=
    fun w => hP.tendsto_at (Set.mem_univ w)
  have hne : ∀ q : XiZeroCopyOff K, xiSpectralPoint q.1 ≠ t := fun q h => q.2 (hK q.1 h)
  have hE : ∀ q : XiZeroCopyOff K, weierstrassE1 ((t : ℂ) / xiSpectralPoint q.1) ≠ 0 := by
    intro q
    unfold weierstrassE1
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    rw [sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq (xiSpectralPoint_ne_zero q.1)]
    exact fun h => hne q h.symm
  have hlim := ((hpt ((t : ℂ) - I * x)).mul (hpt ((t : ℂ) + I * x))).div ((hpt (t : ℂ)).pow 2)
    (pow_ne_zero 2 (xiCanonicalProductOff_ne_zero hK))
  refine hlim.congr fun F => ?_
  have hden : (∏ q ∈ F, weierstrassE1 ((t : ℂ) / xiSpectralPoint q.1)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Finset.prod_ne_zero_iff.mpr fun q _ => hE q)
  simp only [Pi.div_apply]
  rw [div_eq_iff hden, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hpair := weierstrassE1_pair_eq (t : ℂ) (-(I * x)) (xiSpectralPoint q.1)
    (xiSpectralPoint_ne_zero q.1) (hne q)
  rw [← sub_eq_add_neg, sub_neg_eq_add] at hpair
  rw [hpair]
  have hsq : (-(I * x)) ^ 2 = -x ^ 2 := by ring_nf; rw [I_sq]; ring
  rw [hsq]
  ring

/-- **Detection order under a cluster shadow.**  Let `ρ` be a zero of `ξ` off the critical line,
`γ = Im ρ`, `δ = |Re ρ − ½|`.  Let `K` be a finite set of zero copies within distance `ε` of `γ`
containing every copy at `γ`.  Suppose at most `m` copies sit at `γ ± iδ`, and the copies outside
`K` and away from `γ ± iδ` have `Σ 1/|z − γ|² ≤ S`.  With `B = 5^m e^{4δ²S}` and
`η = (1 + ε²/(4δ²))^{|K|} − 1`, if `2B(1 + η) < 2^N (1 − Bη)` then some slice coefficient `c_n(γ)`
with `n < 2|K| + N` has negative real part. -/
theorem exists_re_xiSliceCoeff_neg_of_offLine_cluster {ρ : ℂ} (hρ : xi ρ = 0)
    (hne : ρ.re ≠ 1 / 2) (K : Finset XiZeroCopy) {ε : ℝ}
    (hK : ∀ q ∈ K, ‖xiSpectralPoint q - ρ.im‖ ≤ ε)
    (hKall : ∀ q : XiZeroCopy, xiSpectralPoint q = (ρ.im : ℂ) → q ∈ K) {m : ℕ}
    (hown : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) → F.card ≤ m)
    {S : ℝ} (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        ¬ (xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) ∧ q ∉ K) →
      ∑ q ∈ F, 1 / ‖xiSpectralPoint q - ρ.im‖ ^ 2 ≤ S)
    {N : ℕ}
    (hN : 2 * (5 ^ m * Real.exp (4 * |ρ.re - 1 / 2| ^ 2 * S)) *
        (1 + ε ^ 2 / (4 * |ρ.re - 1 / 2| ^ 2)) ^ K.card <
      2 ^ N * (1 - 5 ^ m * Real.exp (4 * |ρ.re - 1 / 2| ^ 2 * S) *
        ((1 + ε ^ 2 / (4 * |ρ.re - 1 / 2| ^ 2)) ^ K.card - 1))) :
    ∃ n < 2 * K.card + N, (xiSliceCoeff ρ.im n).re < 0 := by
  classical
  set t : ℝ := ρ.im with htdef
  set δ : ℝ := |ρ.re - 1 / 2| with hδdef
  set k : ℕ := K.card with hkdef
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
  set B : ℝ := 5 ^ m * Real.exp (4 * δ ^ 2 * S) with hB
  set η : ℝ := (1 + ε ^ 2 / (4 * δ ^ 2)) ^ k - 1 with hη
  have hS0 : 0 ≤ S := by simpa using hS ∅ (by simp)
  have hB1 : 1 ≤ B := by
    rw [hB]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (Real.one_le_exp (by positivity))
  have hη1 : (1 + ε ^ 2 / (4 * δ ^ 2)) ^ k = 1 + η := by rw [hη]; ring
  have hN' : 2 * B * (1 + η) < 2 ^ N * (1 - B * η) := by rw [hη1] at hN; exact hN
  have hη0 : 0 ≤ η := by
    rw [hη, sub_nonneg]
    exact one_le_pow₀ (le_add_of_nonneg_right (by positivity))
  -- the factorization of the slice
  set P : ℂ → ℂ := xiCanonicalProductOff K with hP
  set A : ℂ := XiC 0 ^ 2 * ∏ q ∈ K, (Complex.exp (2 * t / xiSpectralPoint q) /
    xiSpectralPoint q ^ 2) with hA
  set poly : ℂ → ℂ := fun x => ∏ q ∈ K, (x ^ 2 + (xiSpectralPoint q - t) ^ 2) with hpoly
  set Q : ℂ → ℂ := fun x => P ((t : ℂ) - I * x) * P ((t : ℂ) + I * x) with hQ
  have hXi : ∀ z, XiC z = XiC 0 * (∏ q ∈ K, weierstrassE1 (z / xiSpectralPoint q)) * P z := by
    intro z
    rw [hP, mul_assoc, ← xiCanonicalProduct_eq_prod_mul_off]
    simpa only [Pi.mul_apply] using congrFun XiC_eq_constant_mul_canonicalProduct z
  have hslice : ∀ x : ℂ, xiSliceProduct t x = A * poly x * Q x := by
    intro x
    have hpair : ∀ q ∈ K, weierstrassE1 (((t : ℂ) - I * x) / xiSpectralPoint q) *
        weierstrassE1 (((t : ℂ) + I * x) / xiSpectralPoint q) =
          (x ^ 2 + (xiSpectralPoint q - t) ^ 2) *
            (Complex.exp (2 * t / xiSpectralPoint q) / xiSpectralPoint q ^ 2) := by
      intro q _
      rw [weierstrassE1_pair_eq_sq_sub _ _ _ (xiSpectralPoint_ne_zero q)]
      have hsq : (I * x) ^ 2 = -x ^ 2 := by ring_nf; rw [I_sq]; ring
      rw [hsq]
      ring
    rw [xiSliceProduct_eq_XiC_mul, hXi ((t : ℂ) - I * x), hXi ((t : ℂ) + I * x)]
    calc XiC 0 * (∏ q ∈ K, weierstrassE1 (((t : ℂ) - I * x) / xiSpectralPoint q)) *
          P ((t : ℂ) - I * x) * (XiC 0 * (∏ q ∈ K, weierstrassE1 (((t : ℂ) + I * x) /
            xiSpectralPoint q)) * P ((t : ℂ) + I * x))
        = XiC 0 ^ 2 * (∏ q ∈ K, (weierstrassE1 (((t : ℂ) - I * x) / xiSpectralPoint q) *
            weierstrassE1 (((t : ℂ) + I * x) / xiSpectralPoint q))) * Q x := by
          rw [Finset.prod_mul_distrib, hQ]; ring
      _ = XiC 0 ^ 2 * (∏ q ∈ K, ((x ^ 2 + (xiSpectralPoint q - t) ^ 2) *
            (Complex.exp (2 * t / xiSpectralPoint q) / xiSpectralPoint q ^ 2))) * Q x := by
          rw [Finset.prod_congr rfl hpair]
      _ = A * poly x * Q x := by
          rw [Finset.prod_mul_distrib, hA, hpoly]; ring
  -- regularity and nonvanishing
  have hPd : Differentiable ℂ P := differentiable_xiCanonicalProductOff K
  have hQd : Differentiable ℂ Q := by
    simp only [hQ]
    exact (hPd.comp (by fun_prop)).mul (hPd.comp (by fun_prop))
  have hpolyd : Differentiable ℂ poly := by
    simp only [hpoly]
    exact Differentiable.fun_finsetProd fun q _ => by fun_prop
  have hP0 : P t ≠ 0 := xiCanonicalProductOff_ne_zero hKall
  have hQ0 : Q 0 ≠ 0 := by simp only [hQ, mul_zero, sub_zero, add_zero]; exact mul_ne_zero hP0 hP0
  have hA0 : A ≠ 0 := by
    rw [hA]
    refine mul_ne_zero (pow_ne_zero 2 XiC_zero_ne) (Finset.prod_ne_zero_iff.mpr fun q _ => ?_)
    exact div_ne_zero (Complex.exp_ne_zero _) (pow_ne_zero 2 (xiSpectralPoint_ne_zero q))
  have hAQ : 0 < ‖A‖ * ‖Q 0‖ := mul_pos (norm_pos_iff.mpr hA0) (norm_pos_iff.mpr hQ0)
  -- bounds on the circle `|x| = 2δ`
  have hQB : ∀ x : ℂ, ‖x‖ = 2 * δ → ‖Q x‖ ≤ ‖Q 0‖ * B := by
    intro x hx
    have hlim := (tendsto_prod_off_one_add_sq_div hKall x).norm
    have hle : ‖P ((t : ℂ) - I * x) * P ((t : ℂ) + I * x) / P t ^ 2‖ ≤ B := by
      refine le_of_tendsto hlim (Eventually.of_forall fun F => ?_)
      have hmap : ∏ q ∈ F, (1 + x ^ 2 / (xiSpectralPoint q.1 - t) ^ 2) =
          ∏ q ∈ F.map (Function.Embedding.subtype _),
            (1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2) := by
        rw [Finset.prod_map]; rfl
      rw [hmap]
      refine norm_prod_one_add_sq_div_le_of_mass hδ hown hS hx _ fun q hq => ?_
      obtain ⟨q', -, rfl⟩ := Finset.mem_map.mp hq
      exact q'.2
    have hQ0' : Q 0 = P t ^ 2 := by simp only [hQ, mul_zero, sub_zero, add_zero]; ring
    rw [norm_div, hQ0'.symm, div_le_iff₀ (norm_pos_iff.mpr hQ0)] at hle
    rw [mul_comm]
    exact hle
  have hw : ∀ q ∈ K, ‖(xiSpectralPoint q - t) ^ 2‖ ≤ ε ^ 2 := by
    intro q hq
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hK q hq) 2
  have hpolyB : ∀ x : ℂ, ‖x‖ = 2 * δ →
      ‖poly x - x ^ (2 * k)‖ ≤ (4 * δ ^ 2 + ε ^ 2) ^ k - (4 * δ ^ 2) ^ k := by
    intro x hx
    have h := norm_prod_add_sub_pow_le K (x ^ 2) (fun q => (xiSpectralPoint q - t) ^ 2) hw
    have hx2 : ‖x ^ 2‖ = 4 * δ ^ 2 := by rw [norm_pow, hx]; ring
    rw [hx2, ← pow_mul] at h
    simpa only [hpoly] using h
  have hpolyN : ∀ x : ℂ, ‖x‖ = 2 * δ → ‖poly x‖ ≤ (4 * δ ^ 2 + ε ^ 2) ^ k := by
    intro x hx
    have h1 := hpolyB x hx
    have h2 : ‖x ^ (2 * k)‖ = (4 * δ ^ 2) ^ k := by
      rw [norm_pow, hx, pow_mul]; ring
    calc ‖poly x‖ ≤ ‖poly x - x ^ (2 * k)‖ + ‖x ^ (2 * k)‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := by rw [h2]; linarith
  -- the scale identity
  have h2δ : (0 : ℝ) < (2 * δ) ^ (2 * k) := by positivity
  have hscale : (4 * δ ^ 2 + ε ^ 2) ^ k = (2 * δ) ^ (2 * k) * (1 + η) := by
    rw [hη, pow_mul]
    have : (4 * δ ^ 2 + ε ^ 2) = (2 * δ) ^ 2 * (1 + ε ^ 2 / (4 * δ ^ 2)) := by
      field_simp; ring
    rw [this, mul_pow]; ring
  have hscale0 : (4 * δ ^ 2) ^ k = (2 * δ) ^ (2 * k) := by rw [pow_mul]; ring
  -- the coefficient `c_{2k}` is close to `A Q(0)`
  set c : ℂ := xiSliceCoeff t (2 * k) with hcdef
  have hcoef : ‖c - A * Q 0‖ ≤ ‖A‖ * ‖Q 0‖ * B * η := by
    set G₁ : ℂ → ℂ := fun x => x ^ (2 * k) * (A * Q x) with hG₁
    set G₂ : ℂ → ℂ := fun x => A * (poly x - x ^ (2 * k)) * Q x with hG₂
    have hsplit : xiSliceProduct t = G₁ + G₂ := by
      funext x
      simp only [Pi.add_apply, hG₁, hG₂, hslice]
      ring
    have hG₁d : Differentiable ℂ G₁ := by
      simp only [hG₁]; exact (differentiable_pow _).mul (hQd.const_mul A)
    have hG₂d : Differentiable ℂ G₂ := by
      simp only [hG₂]; exact ((hpolyd.sub (differentiable_pow _)).const_mul A).mul hQd
    have hd : iteratedDeriv (2 * k) (xiSliceProduct t) 0 =
        iteratedDeriv (2 * k) G₁ 0 + iteratedDeriv (2 * k) G₂ 0 := by
      rw [hsplit]
      exact iteratedDeriv_add hG₁d.contDiff.contDiffAt hG₂d.contDiff.contDiffAt
    have h1 : ((2 * k).factorial : ℂ)⁻¹ * iteratedDeriv (2 * k) G₁ 0 = A * Q 0 := by
      have hAQan : AnalyticAt ℂ (fun x => A * Q x) 0 :=
        (hQd.const_mul A).analyticAt 0
      rw [hG₁, iteratedDeriv_pow_mul_zero_of_analyticAt hAQan, if_pos le_rfl, Nat.sub_self,
        iteratedDeriv_zero, Nat.choose_self, one_mul]
      have hf : ((2 * k).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      rw [← mul_assoc, inv_mul_cancel₀ hf, one_mul]
    have h2 : ‖((2 * k).factorial : ℂ)⁻¹ * iteratedDeriv (2 * k) G₂ 0‖ ≤
        ‖A‖ * ‖Q 0‖ * B * η := by
      have hbound : ∀ x ∈ sphere (0 : ℂ) (2 * δ), ‖G₂ x‖ ≤
          ‖A‖ * ((4 * δ ^ 2 + ε ^ 2) ^ k - (4 * δ ^ 2) ^ k) * (‖Q 0‖ * B) := by
        intro x hx
        have hx' : ‖x‖ = 2 * δ := mem_sphere_zero_iff_norm.mp hx
        have hd0 : 0 ≤ (4 * δ ^ 2 + ε ^ 2) ^ k - (4 * δ ^ 2) ^ k :=
          (norm_nonneg _).trans (hpolyB x hx')
        simp only [hG₂, norm_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hpolyB x hx') (norm_nonneg _)) (hQB x hx')
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) hd0)
      have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (2 * k)
        (by positivity : (0 : ℝ) < 2 * δ) hG₂d.diffContOnCl hbound
      have hfac : (0 : ℝ) < ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc ((2 * k).factorial : ℝ)⁻¹ * ‖iteratedDeriv (2 * k) G₂ 0‖
          ≤ ((2 * k).factorial : ℝ)⁻¹ * (((2 * k).factorial : ℝ) *
              (‖A‖ * ((4 * δ ^ 2 + ε ^ 2) ^ k - (4 * δ ^ 2) ^ k) * (‖Q 0‖ * B)) /
                (2 * δ) ^ (2 * k)) :=
            mul_le_mul_of_nonneg_left hC (inv_nonneg.mpr hfac.le)
        _ = ‖A‖ * ‖Q 0‖ * B * η := by
            rw [hscale, hscale0]
            field_simp
            ring
    have hc : c = A * Q 0 + ((2 * k).factorial : ℂ)⁻¹ * iteratedDeriv (2 * k) G₂ 0 := by
      rw [hcdef, xiSliceCoeff, hd, mul_add, h1]
    rw [hc, add_sub_cancel_left]
    exact h2
  -- the bound for the slice on the circle
  have hM : ∀ x ∈ sphere (0 : ℂ) (2 * δ), ‖xiSliceProduct t x‖ ≤
      ‖A‖ * (4 * δ ^ 2 + ε ^ 2) ^ k * (‖Q 0‖ * B) := by
    intro x hx
    have hx' : ‖x‖ = 2 * δ := mem_sphere_zero_iff_norm.mp hx
    rw [hslice, norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hpolyN x hx') (norm_nonneg _)) (hQB x hx')
      (norm_nonneg _) (mul_nonneg (norm_nonneg _) (by positivity))
  -- conclusion
  have hBη : B * η < 1 := by
    have hpos : 0 < 2 ^ N * (1 - B * η) := by
      have : 0 < 2 * B * (1 + η) := by positivity
      linarith
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    by_contra hcon
    have : 2 ^ N * (1 - B * η) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h2N.le (by linarith [not_lt.mp hcon])
    linarith
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · exfalso
      have : 2 * B * (1 + η) < 1 - B * η := by simpa using hN'
      nlinarith
    · exact h
  by_cases hcneg : c.re < 0
  · exact ⟨2 * k, by omega, hcneg⟩
  have hcre : ‖A‖ * ‖Q 0‖ * (1 - B * η) ≤ c.re := by
    have hcim : c.im = 0 := xiSliceCoeff_im_eq_zero t (2 * k)
    have hcn : ‖c‖ = c.re := by
      have hreal : c = (c.re : ℂ) :=
        Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact hcim)
      conv_lhs => rw [hreal]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (not_lt.mp hcneg)]
    have htri : ‖A * Q 0‖ ≤ ‖c‖ + ‖c - A * Q 0‖ := by
      have := norm_sub_le c (c - A * Q 0)
      rw [sub_sub_cancel] at this
      exact this
    rw [norm_mul] at htri
    nlinarith
  refine exists_re_xiSliceCoeff_neg_of_shifted_tail_lt hρ hδ (R := 2 * δ) (by linarith) hM
    (2 * k) (N := N) ?_
  have hhalf : δ / (2 * δ) = 1 / 2 := by field_simp
  rw [← hδdef, hhalf, hscale]
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have e : ‖A‖ * ((2 * δ) ^ (2 * k) * (1 + η)) * (‖Q 0‖ * B) / (2 * δ) ^ (2 * k) *
      (1 / 2) ^ N / (1 - 1 / 2) = ‖A‖ * ‖Q 0‖ * (2 * B * (1 + η) / 2 ^ N) := by
    rw [one_div_pow]; field_simp; ring
  rw [e]
  have hlt : 2 * B * (1 + η) / 2 ^ N < 1 - B * η := by
    rw [div_lt_iff₀ h2N]
    linarith
  calc ‖A‖ * ‖Q 0‖ * (2 * B * (1 + η) / 2 ^ N) < ‖A‖ * ‖Q 0‖ * (1 - B * η) :=
        mul_lt_mul_of_pos_left hlt hAQ
    _ ≤ c.re := hcre

/-- **The first negative order under a critical cluster.**  Let `ρ` be a zero of `ξ` off the
critical line with `Ξ(γ) ≠ 0`, `γ = Im ρ`, `δ = |Re ρ − ½|`.  Let `K` be a set of critical zero
copies within `ε` of `γ` with `3|K| ε² Σ_{exposed} (Im z)²/|z − γ|⁴ ≤ 1` over the exposed off-line
copies, at most `m` copies at `γ ± iδ`, and `Σ 1/|z − γ|² ≤ S` over the copies outside `K` and away
from `γ ± iδ`.  If `2B(1 + η) < 2^N (1 − Bη)` with `B = 5^m e^{4δ²S}`, `η = (1 + ε²/(4δ²))^{|K|} − 1`,
then all slice coefficients of order `≤ 2|K|` at `γ` are nonnegative and some coefficient of order
strictly between `2|K|` and `2|K| + N` is negative. -/
theorem exists_first_negative_xiSliceCoeff_of_critical_cluster {ρ : ℂ} (hρ : xi ρ = 0)
    (hne : ρ.re ≠ 1 / 2) (hΞ : XiC ρ.im ≠ 0) (K : Finset XiZeroCopy)
    (hcrit : ∀ q ∈ K, XiCopyCritical q) {ε : ℝ}
    (hK : ∀ q ∈ K, ‖xiSpectralPoint q - ρ.im‖ ≤ ε)
    (hexp : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q ∧
        |(xiSpectralPoint q).re - ρ.im| < |(xiSpectralPoint q).im|) →
      3 * K.card * (ε ^ 2 * ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 /
        ‖xiSpectralPoint q - ρ.im‖ ^ 4) ≤ 1) {m : ℕ}
    (hown : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) → F.card ≤ m)
    {S : ℝ} (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        ¬ (xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) ∧ q ∉ K) →
      ∑ q ∈ F, 1 / ‖xiSpectralPoint q - ρ.im‖ ^ 2 ≤ S)
    {N : ℕ}
    (hN : 2 * (5 ^ m * Real.exp (4 * |ρ.re - 1 / 2| ^ 2 * S)) *
        (1 + ε ^ 2 / (4 * |ρ.re - 1 / 2| ^ 2)) ^ K.card <
      2 ^ N * (1 - 5 ^ m * Real.exp (4 * |ρ.re - 1 / 2| ^ 2 * S) *
        ((1 + ε ^ 2 / (4 * |ρ.re - 1 / 2| ^ 2)) ^ K.card - 1))) :
    (∀ n ≤ 2 * K.card, 0 ≤ (xiSliceCoeff ρ.im n).re) ∧
      ∃ n, 2 * K.card < n ∧ n < 2 * K.card + N ∧ (xiSliceCoeff ρ.im n).re < 0 := by
  have hlow : ∀ n ≤ 2 * K.card, 0 ≤ (xiSliceCoeff ρ.im n).re := by
    intro n hn
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact (xiSliceCoeff_zero_re_pos hΞ).le
      · refine (xiSliceCoeff_re_pos_of_exposed_nearDouble_card hΞ hi K hcrit (by omega) hK
          fun F hF => ?_).le
        have h1 := hexp F hF
        have hsum : 0 ≤ ε ^ 2 * ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 /
            ‖xiSpectralPoint q - ρ.im‖ ^ 4 :=
          mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun q _ => by positivity)
        have hik : (i : ℝ) ≤ K.card := by exact_mod_cast (by omega : i ≤ K.card)
        nlinarith
    · rw [xiSliceCoeff_odd_eq_zero, Complex.zero_re]
  obtain ⟨n, hn, hneg⟩ := exists_re_xiSliceCoeff_neg_of_offLine_cluster hρ hne K hK
    (fun q hq => absurd hq (xiSpectralPoint_ne_ofReal hΞ q)) hown hS hN
  refine ⟨hlow, n, ?_, hn, hneg⟩
  by_contra hle
  exact absurd (hlow n (not_lt.mp hle)) (not_le.mpr hneg)

end

end RHTower

import GaloisForLFunctions.RHTower.PhotonicLosslessProductPortRH
import GaloisForLFunctions.RHTower.PhotonicIntegerClockHalfRate
import GaloisForLFunctions.RHTower.XiCosineShiftDefectDisks

/-!
# Lossless producers for the cosine family of `Ξ`

A function is a *lossless product-port limit* if it is a locally uniform limit of nonzero
multiples of finite products of displacement entries of lossless temporal stacks with positive
impedances and durations (`IsPtrProductPortLimit`). Such limits have only real zeros, and `Ξ` is
one exactly under RH (`riemannHypothesis_iff_XiC_limit_losslessProductPort`).

* `isPtrProductPortLimit_of_tendstoLocallyUniformly`: the class is closed under locally uniform
  limits (diagonal choice).
* `isPtrProductPortLimit_of_even_realZeros`: every even entire `f` with `f(0) ≠ 0`, the order-one
  envelope `‖f z‖ ≤ exp(C(1+‖z‖)log(2+‖z‖))` and only real zeros is a lossless product-port limit.
  Its Hadamard product `f(0)·∏ E₁(z/ζ)` is a locally uniform limit of products over finite
  reflection-symmetric sets of zeros. On such a set, `E₁(u)E₁(−u) = 1 − u²` pairs the factors
  into `∏(1 − z²/γ²)`, `γ > 0`. Each pair factor is a limit of two-slab entries.
* `isPtrProductPortLimit_cosineShift`: unconditionally, `cos(hD)Ξ = (Ξ(z+ih) + Ξ(z−ih))/2` is a
  lossless product-port limit for every `h ≥ ½`.
* `riemannHypothesis_iff_forall_isPtrProductPortLimit_cosineShift`: RH holds iff `cos(hD)Ξ` is a
  lossless product-port limit for every `h > 0`. The reverse direction lets `h → 0` and closes
  the class.

So the photonic receiver has an unconditional arithmetic producer family on `h ≥ ½`, and RH is
exactly the continuation of this producer to every `h > 0`.
-/

open Complex Set Filter Topology Metric
open GaloisForLFunctions.EntireZeroDivisor

namespace RHTower

noncomputable section

/-- `F` is a locally uniform limit of nonzero multiples of finite products of lossless
temporal-stack entries with positive impedances and durations. -/
def IsPtrProductPortLimit (F : ℂ → ℂ) : Prop :=
  ∃ (c : ℕ → ℂ) (L : ℕ → List (List (ℝ × ℝ))), (∀ n, c n ≠ 0) ∧
    (∀ n, ∀ l ∈ L n, ∀ x ∈ l, 0 < x.1 ∧ 0 < x.2) ∧
    TendstoLocallyUniformly (fun n => ptrLosslessProductPort (c n) (L n)) F atTop

/-! ## Closure under locally uniform limits -/

/-- **Diagonal closure.** A locally uniform limit of lossless product-port limits is one. -/
theorem isPtrProductPortLimit_of_tendstoLocallyUniformly {G : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hG : ∀ m, IsPtrProductPortLimit (G m)) (hconv : TendstoLocallyUniformly G F atTop) :
    IsPtrProductPortLimit F := by
  choose c L hc hL hcm using hG
  have hk : ∀ m : ℕ, ∃ n : ℕ, ∀ z ∈ closedBall (0 : ℂ) m,
      dist (G m z) (ptrLosslessProductPort (c m n) (L m n) z) < 1 / ((m : ℝ) + 1) := by
    intro m
    have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp (hcm m)) _
      (isCompact_closedBall (0 : ℂ) m)
    rw [Metric.tendstoUniformlyOn_iff] at hu
    exact (hu _ (by positivity)).exists
  choose N hN using hk
  refine ⟨fun m => c m (N m), fun m => L m (N m), fun m => hc m _, fun m => hL m _, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hGu := (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) K hK
  rw [Metric.tendstoUniformlyOn_iff] at hGu
  have h2 : ∀ᶠ m : ℕ in atTop, R ≤ m ∧ 1 / ((m : ℝ) + 1) < ε / 2 := by
    have ha := tendsto_natCast_atTop_atTop.eventually_ge_atTop R
    have hb := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds (half_pos hε))
    exact ha.and hb
  filter_upwards [hGu (ε / 2) (half_pos hε), h2] with m hm1 hm2 z hz
  have hzm : z ∈ closedBall (0 : ℂ) m := by
    have := hR hz
    rw [mem_closedBall] at this ⊢
    linarith [hm2.1]
  calc dist (F z) (ptrLosslessProductPort (c m (N m)) (L m (N m)) z)
      ≤ dist (F z) (G m z) + dist (G m z) (ptrLosslessProductPort (c m (N m)) (L m (N m)) z) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hm1 z hz) ((hN m z hzm).trans hm2.2)
    _ = ε := add_halves ε

/-! ## Finite pair products -/

/-- Every nonzero multiple of a finite product of pair factors `1 − z²/γ²`, `γ > 0`, is a
lossless product-port limit. -/
theorem isPtrProductPortLimit_const_mul_prod_pair {ι : Type*} {c : ℂ} (hc : c ≠ 0)
    (s : Finset ι) (γ : ι → ℝ) (hγ : ∀ i ∈ s, 0 < γ i) :
    IsPtrProductPortLimit (fun z => c * ∏ i ∈ s, (1 - z ^ 2 / (γ i : ℂ) ^ 2)) := by
  refine ⟨fun _ => c, fun n => s.toList.map fun i => ptrPairSlab (γ i) (ptrPairDuration (γ i) n),
    fun _ => hc, ?_, ?_⟩
  · intro n l hl x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    have hγi := hγ i (Finset.mem_toList.mp hi)
    have hτ : 0 < ptrPairDuration (γ i) n := by unfold ptrPairDuration; positivity
    have hγτ : γ i * ptrPairDuration (γ i) n = Real.pi / (4 * ((n : ℝ) + 1)) := by
      unfold ptrPairDuration; field_simp
    refine ptrPairSlab_pos hτ (mul_pos hγi hτ) ?_ x hx
    rw [hγτ, div_lt_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ 4 * ((n : ℝ) + 1) := by
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
    nlinarith [Real.pi_pos]
  · have hprod := tendstoLocallyUniformly_finset_prod s
      (F := fun i n z => ptrLosslessStackEntry (ptrPairSlab (γ i) (ptrPairDuration (γ i) n)) z)
      (f := fun i z => 1 - z ^ 2 / (γ i : ℂ) ^ 2)
      (fun i hi => tendstoLocallyUniformly_ptrPairSlab (hγ i hi)) (fun i _ => by fun_prop)
    have hcst : TendstoLocallyUniformly (fun (_ : ℕ) (_ : ℂ) => c) (fun _ => c) atTop := by
      rw [Metric.tendstoLocallyUniformly_iff]
      intro ε hε x
      exact ⟨univ, univ_mem, Eventually.of_forall fun n y _ => by simp [hε]⟩
    have hcont : Continuous fun z => ∏ i ∈ s, (1 - z ^ 2 / (γ i : ℂ) ^ 2) :=
      continuous_finsetProd _ fun i _ => by fun_prop
    have hmul := (tendstoLocallyUniformlyOn_univ.mpr hcst).mul₀
      (tendstoLocallyUniformlyOn_univ.mpr hprod) continuousOn_const hcont.continuousOn
    refine (tendstoLocallyUniformlyOn_univ.mp hmul).congr fun n z => ?_
    simp only [Pi.mul_apply, ptrLosslessProductPort, List.map_map, Finset.prod_map_toList,
      Function.comp_def]

/-! ## Pairing the genus-one factors -/

/-- On a finite set closed under an involution `σ` with `a ∘ σ = −a` and `Re a ≠ 0`, the genus-one
factors pair into `∏ (1 − z²/a²)` over the half with `Re a > 0`. -/
theorem prod_weierstrassE1_eq_prod_pair {ι : Type*} [DecidableEq ι] (a : ι → ℂ) (σ : ι → ι)
    (hσσ : ∀ i, σ (σ i) = i) (hσa : ∀ i, a (σ i) = -a i) (hre : ∀ i, (a i).re ≠ 0)
    (S : Finset ι) (hS : ∀ i ∈ S, σ i ∈ S) (z : ℂ) :
    ∏ i ∈ S, weierstrassE1 (z / a i) =
      ∏ i ∈ S.filter (fun i => 0 < (a i).re), (1 - z ^ 2 / a i ^ 2) := by
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun i => 0 < (a i).re)]
  have himg : S.filter (fun i => ¬ 0 < (a i).re) = (S.filter fun i => 0 < (a i).re).image σ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hi, hneg⟩
      refine ⟨σ i, ⟨hS i hi, ?_⟩, hσσ i⟩
      rw [hσa, Complex.neg_re]
      have h1 := hre i
      have h2 : (a i).re < 0 := lt_of_le_of_ne (not_lt.mp hneg) h1
      linarith
    · rintro ⟨j, ⟨hj, hpos⟩, rfl⟩
      refine ⟨hS j hj, ?_⟩
      rw [hσa, Complex.neg_re]
      linarith
  have hinj : Set.InjOn σ ↑(S.filter fun i => 0 < (a i).re) := fun x _ y _ h => by
    have := congrArg σ h
    rwa [hσσ, hσσ] at this
  rw [himg, Finset.prod_image hinj, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hai : a i ≠ 0 := fun h => hre i (by rw [h, Complex.zero_re])
  rw [hσa]
  unfold weierstrassE1
  have hexp : Complex.exp (z / a i) * Complex.exp (z / -a i) = 1 := by
    rw [← Complex.exp_add, div_neg, add_neg_cancel, Complex.exp_zero]
  calc (1 - z / a i) * Complex.exp (z / a i) * ((1 - z / -a i) * Complex.exp (z / -a i))
      = (1 - z / a i) * (1 - z / -a i) * (Complex.exp (z / a i) * Complex.exp (z / -a i)) := by
        ring
    _ = 1 - z ^ 2 / a i ^ 2 := by
        rw [hexp, mul_one, div_neg]
        field_simp
        ring

/-- The reflection of the zero copies of an even function is an involution. -/
theorem zeroCopyReflect_involutive {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (heven : ∀ z, f (-z) = f z) (q : ZeroCopy f) :
    OrderOneHadamard.zeroCopyReflect hf heven (OrderOneHadamard.zeroCopyReflect hf heven q) = q := by
  have hsnd : ∀ {α : Type} {β : α → Type} (e : α ≃ α) (F : ∀ a, β a ≃ β (e a)),
      (∀ a b, HEq (F a b) b) → ∀ x : Σ a, β a, HEq (e.sigmaCongr F x).2 x.2 := by
    intro α β e F hF x
    obtain ⟨a, b⟩ := x
    exact hF a b
  have hF : ∀ (a : ZeroSupport f) b, HEq ((fun w => Equiv.cast (by
      change Fin ((MeromorphicOn.divisor f univ) ((w : ZeroSupport f) : ℂ)).toNat =
        Fin ((MeromorphicOn.divisor f univ) (-((w : ZeroSupport f) : ℂ))).toNat
      rw [OrderOneHadamard.divisor_neg_of_even hf heven]) :
        ∀ w : ZeroSupport f, Fin ((MeromorphicOn.divisor f univ) (w : ℂ)).toNat ≃
          Fin ((MeromorphicOn.divisor f univ)
            ((OrderOneHadamard.zeroSupportReflect hf heven w : ZeroSupport f) : ℂ)).toNat)
        a b) b := fun a b => cast_heq _ _
  refine Sigma.ext ?_ ?_
  · apply Subtype.ext
    show -(-((q.1 : ℂ))) = q.1
    rw [neg_neg]
  · exact (hsnd _ _ hF _).trans (hsnd _ _ hF _)

/-! ## Even real-rooted functions of order one -/

/-- **Lossless producer for real canonical products.** If `a` is real, nonzero, odd under an
involution `σ`, and `Σ 1/‖a‖²` converges, then `c · ∏' E₁(z/a_i)` (`c ≠ 0`) is a lossless
product-port limit. -/
theorem isPtrProductPortLimit_const_mul_canonicalProduct {ι : Type*} (a : ι → ℂ) (σ : ι → ι)
    (hσσ : ∀ i, σ (σ i) = i) (hσa : ∀ i, a (σ i) = -a i) (him : ∀ i, (a i).im = 0)
    (hane : ∀ i, a i ≠ 0) (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) {c : ℂ} (hc : c ≠ 0) :
    IsPtrProductPortLimit (fun z => c * canonicalProductE1Indexed a z) := by
  classical
  have hre : ∀ i, (a i).re ≠ 0 := fun i h => hane i (Complex.ext h (him i))
  have hareal : ∀ i, a i = (((a i).re : ℝ) : ℂ) := fun i => Complex.ext (by simp) (by simp [him i])
  have hprod : TendstoLocallyUniformlyOn
      (fun (I : Finset ι) z => ∏ i ∈ I, weierstrassE1 (z / a i))
      (canonicalProductE1Indexed a) atTop univ :=
    canonicalProductE1Indexed_hasProdLocallyUniformlyOn a hane hsum
  -- a finite set of zeros, good on the ball of radius `m`
  have hk : ∀ m : ℕ, ∃ s₀ : Finset ι, ∀ s, s₀ ≤ s → ∀ z ∈ closedBall (0 : ℂ) m,
      dist (canonicalProductE1Indexed a z) (∏ i ∈ s, weierstrassE1 (z / a i)) <
        1 / (((m : ℝ) + 1) * (‖c‖ + 1)) := by
    intro m
    have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hprod
      (closedBall (0 : ℂ) m) (subset_univ _) (isCompact_closedBall (0 : ℂ) m)
    rw [Metric.tendstoUniformlyOn_iff] at hu
    exact Filter.eventually_atTop.mp (hu _ (by positivity))
  choose s₀ hs₀ using hk
  set S : ℕ → Finset ι := fun m => s₀ m ∪ (s₀ m).image σ with hSdef
  have hSσ : ∀ m, ∀ i ∈ S m, σ i ∈ S m := by
    intro m i hi
    simp only [hSdef, Finset.mem_union, Finset.mem_image] at hi ⊢
    rcases hi with hi | ⟨j, hj, rfl⟩
    · exact Or.inr ⟨i, hi, rfl⟩
    · exact Or.inl (by rw [hσσ]; exact hj)
  set G : ℕ → ℂ → ℂ := fun m z =>
    c * ∏ i ∈ (S m).filter (fun i => 0 < (a i).re), (1 - z ^ 2 / (((a i).re : ℝ) : ℂ) ^ 2)
    with hGdef
  have hG : ∀ m, IsPtrProductPortLimit (G m) := fun m =>
    isPtrProductPortLimit_const_mul_prod_pair hc _ (fun i => (a i).re)
      (fun i hi => (Finset.mem_filter.mp hi).2)
  have hGeq : ∀ m z, G m z = c * ∏ i ∈ S m, weierstrassE1 (z / a i) := by
    intro m z
    rw [prod_weierstrassE1_eq_prod_pair a σ hσσ hσa hre (S m) (hSσ m) z]
    simp only [hGdef]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hareal i]
  refine isPtrProductPortLimit_of_tendstoLocallyUniformly hG ?_
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have h2 : ∀ᶠ m : ℕ in atTop, R ≤ m ∧ 1 / ((m : ℝ) + 1) < ε := by
    have ha := tendsto_natCast_atTop_atTop.eventually_ge_atTop R
    have hb := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε)
    exact ha.and hb
  filter_upwards [h2] with m hm z hz
  have hzm : z ∈ closedBall (0 : ℂ) m := by
    have := hR hz
    rw [mem_closedBall] at this ⊢
    linarith [hm.1]
  have hd := hs₀ m (S m) Finset.subset_union_left z hzm
  rw [hGeq, dist_eq_norm, ← mul_sub, norm_mul, ← dist_eq_norm]
  have hn : ‖c‖ * dist (canonicalProductE1Indexed a z) (∏ i ∈ S m, weierstrassE1 (z / a i)) ≤
      ‖c‖ * (1 / (((m : ℝ) + 1) * (‖c‖ + 1))) :=
    mul_le_mul_of_nonneg_left hd.le (norm_nonneg _)
  have hq : ‖c‖ * (1 / (((m : ℝ) + 1) * (‖c‖ + 1))) ≤ 1 / ((m : ℝ) + 1) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [norm_nonneg c, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  exact lt_of_le_of_lt (hn.trans hq) hm.2

/-- **Lossless producer for even real-rooted functions of order one.** -/
theorem isPtrProductPortLimit_of_even_realZeros {f : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f univ) (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hreal : ∀ z, f z = 0 → z.im = 0) : IsPtrProductPortLimit f := by
  have hford := DeBruijn.analyticOrderAt_ne_top_of_ne_zero hf hf0
  have hfac := OrderOneHadamard.eq_const_mul_hadamardProduct_of_even hC hf hf0 hford heven hbound
  have h := isPtrProductPortLimit_const_mul_canonicalProduct (zeroCopyPoint f)
    (OrderOneHadamard.zeroCopyReflect hf heven) (zeroCopyReflect_involutive hf heven)
    (OrderOneHadamard.zeroCopyPoint_reflect hf heven)
    (fun q => hreal _ (DeBruijn.apply_zeroCopyPoint hf q)) (zeroCopyPoint_ne_zero hf hf0)
    (OrderOneHadamard.summable_inv_sq_zeroCopyPoint hC hf hf0 hbound) hf0
  have hfeq : f = fun z => f 0 * canonicalProductE1Indexed (zeroCopyPoint f) z := funext hfac
  rw [hfeq]
  exact h

/-! ## The cosine family -/

theorem isPtrProductPortLimit_cosineShift_of_zeros_real {h : ℝ}
    (hreal : ∀ z, (XiC (z + h * I) + XiC (z - h * I)) / 2 = 0 → z.im = 0) :
    IsPtrProductPortLimit (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2) := by
  have hg := DeBruijn.riemannKernel_mul_cosh_superExp h
  obtain ⟨C, hC0, hC⟩ := hg.exists_envelope
  have hF : DeBruijn.cosTransform (fun x => riemannKernelReal x * Real.cosh (h * x)) =
      fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2 :=
    funext (DeBruijn.cosTransform_riemannKernel_mul_cosh h)
  rw [← hF]
  refine isPtrProductPortLimit_of_even_realZeros hC0
    (hg.differentiable.differentiableOn.analyticOnNhd isOpen_univ) hg.cosTransform_zero_ne
    hg.cosTransform_neg hC (fun z hz => hreal z ?_)
  rw [hF] at hz
  exact hz

/-- **Unconditional producer.** For every `h ≥ ½`, `cos(hD)Ξ` is a lossless product-port limit. -/
theorem isPtrProductPortLimit_cosineShift {h : ℝ} (hh : 1 / 2 ≤ h) :
    IsPtrProductPortLimit (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2) := by
  refine isPtrProductPortLimit_cosineShift_of_zeros_real fun z hz => ?_
  have h1 := DeBruijn.cosineShift_zeros_im_sq_le (by linarith) hz
  have h2 : max (1 / 4 - h ^ 2) 0 = 0 := max_eq_right (by nlinarith)
  rw [h2] at h1
  exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (le_antisymm h1 (sq_nonneg _))

/-- The cosine shifts `cos(D/(n+1))Ξ` converge locally uniformly to `Ξ`. -/
theorem tendstoLocallyUniformly_cosineShift_XiC :
    TendstoLocallyUniformly
      (fun (n : ℕ) z => (XiC (z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) +
        XiC (z - ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I)) / 2) XiC atTop := by
  have hXd : Differentiable ℂ XiC := fun z => (XiC_analytic z (mem_univ z)).differentiableAt
  have hXc : Continuous XiC := hXd.continuous
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hK' : IsCompact (cthickening 1 K) := hK.cthickening
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.mp
    (hK'.uniformContinuousOn_of_continuous hXc.continuousOn) ε hε
  have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < min δ 1 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds (lt_min hδ one_pos))
  filter_upwards [hev] with n hn z hz
  set t : ℝ := 1 / ((n : ℝ) + 1) with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hzK : z ∈ cthickening 1 K := self_subset_cthickening K hz
  have hdist : ∀ s : ℂ, s = z + (t : ℂ) * I ∨ s = z - (t : ℂ) * I →
      s ∈ cthickening 1 K ∧ dist z s < δ := by
    rintro s (rfl | rfl)
    · have hd : dist (z + (t : ℂ) * I) z = t := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_of_nonneg ht0]
      refine ⟨Metric.mem_cthickening_of_dist_le _ z 1 K hz (by rw [hd]; linarith [min_le_right δ 1]),
        by rw [dist_comm, hd]; linarith [min_le_left δ 1]⟩
    · have hd : dist (z - (t : ℂ) * I) z = t := by
        rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_of_nonneg ht0]
      refine ⟨Metric.mem_cthickening_of_dist_le _ z 1 K hz (by rw [hd]; linarith [min_le_right δ 1]),
        by rw [dist_comm, hd]; linarith [min_le_left δ 1]⟩
  obtain ⟨hp1, hp2⟩ := hdist _ (Or.inl rfl)
  obtain ⟨hm1, hm2⟩ := hdist _ (Or.inr rfl)
  have e1 := hδu z hzK _ hp1 hp2
  have e2 := hδu z hzK _ hm1 hm2
  rw [dist_eq_norm] at e1 e2 ⊢
  have : XiC z - (XiC (z + (t : ℂ) * I) + XiC (z - (t : ℂ) * I)) / 2 =
      ((XiC z - XiC (z + (t : ℂ) * I)) + (XiC z - XiC (z - (t : ℂ) * I))) / 2 := by ring
  rw [this, norm_div, Complex.norm_two]
  have := norm_add_le (XiC z - XiC (z + (t : ℂ) * I)) (XiC z - XiC (z - (t : ℂ) * I))
  linarith

/-- **RH is the continuation of the lossless producer.** RH holds iff `cos(hD)Ξ` is a lossless
product-port limit for every `h > 0`. -/
theorem riemannHypothesis_iff_forall_isPtrProductPortLimit_cosineShift :
    RiemannHypothesis ↔
      ∀ h : ℝ, 0 < h → IsPtrProductPortLimit (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2) := by
  constructor
  · intro hRH h hh
    refine isPtrProductPortLimit_cosineShift_of_zeros_real fun z hz => ?_
    have hzeros : ∀ w, DeBruijn.cosTransform riemannKernelReal w = 0 → w.im ^ 2 ≤ 0 := by
      intro w hw
      rw [DeBruijn.cosTransform_riemannKernel_eq_XiC] at hw
      obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_XiC_eq_zero hw
      rw [← hq, xiSpectralPoint_im_eq_zero_of_rh hRH q]
      norm_num
    rw [← DeBruijn.cosTransform_riemannKernel_mul_cosh] at hz
    have h1 := DeBruijn.riemannKernel_superExp.zeros_mul_cosh le_rfl hzeros hh z hz
    have h2 : max (0 - h ^ 2) 0 = 0 := max_eq_right (by nlinarith)
    rw [h2] at h1
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (le_antisymm h1 (sq_nonneg _))
  · intro hall
    have hX : IsPtrProductPortLimit XiC :=
      isPtrProductPortLimit_of_tendstoLocallyUniformly
        (fun n => hall _ (by positivity)) tendstoLocallyUniformly_cosineShift_XiC
    exact riemannHypothesis_iff_XiC_limit_losslessProductPort.mpr hX

end

end RHTower

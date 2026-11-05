import GaloisForLFunctions.FiniteFreeProbability.ZeroFreeHalfPlaneStability
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelDeterminants

/-!
# Closed zero-free half-planes make the shifted Jensen polynomials strictly stable

If `ξ` has no zero on the closed half-plane `Re s ≥ σ`, then every root of every reversed Jensen
polynomial `R_d(ξ(σ + i·))`, `d ≥ 1`, lies in the open lower half-plane. In particular this holds
unconditionally for `σ ≥ 1`: a finite free form of the non-vanishing of `ζ` on `Re s = 1`.

Mechanism. Multiplying by a linear factor `1 − βw` acts on reversed Jensen polynomials as
`q ↦ q − βq'`. If the roots of `q` lie in `Im ≤ 0` and `Im β < 0`, every root of `q − βq'` which
is not a root of `q` lies in `Im < 0` (`q'/q = Σ 1/(x − r)` has `Im ≤ 0` on `Im x ≥ 0`, while
`1/β` has `Im > 0`), and a root of both is a multiple root of `q`. Starting from `X^d`, the root
`0` loses one multiplicity at each of `d` factors, leaving a polynomial strictly inside `Im < 0`.
Choosing `d` zeros of `Ξ` for these factors gives a fixed strictly stable piece; Walsh carries its
margin through the partial products of the Hadamard product and the closed-set Hurwitz limit.
-/

open Polynomial Filter Topology Complex Metric
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

/-! ## A Gauss–Lucas step -/

theorem im_multiset_sum_nonpos (s : Multiset ℂ) (h : ∀ z ∈ s, z.im ≤ 0) : s.sum.im ≤ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, add_im]
    have h1 := h a (Multiset.mem_cons_self a s)
    have h2 := ih fun z hz => h z (Multiset.mem_cons_of_mem hz)
    linarith

/-- If the roots of `q` lie in `Im ≤ 0`, `Im β < 0`, `q(x) ≠ 0` and `q(x) = β q'(x)`, then
`Im x < 0`. -/
theorem im_neg_of_eval_sub_mul_derivative {q : ℂ[X]} (hq : ∀ r ∈ q.roots, r.im ≤ 0) {β : ℂ}
    (hβ : β.im < 0) {x : ℂ} (hqx : q.eval x ≠ 0)
    (h : q.eval x - β * q.derivative.eval x = 0) : x.im < 0 := by
  by_contra hx
  push Not at hx
  have hβ0 : β ≠ 0 := fun h0 => by rw [h0] at hβ; simp at hβ
  have hs := (IsAlgClosed.splits q).eval_derivative_eq_eval_mul_sum hqx
  set S := (q.roots.map fun z => 1 / (x - z)).sum
  have hS : S = β⁻¹ := by
    rw [hs] at h
    have h1 : q.eval x * (1 - β * S) = 0 := by linear_combination h
    have h2 := (mul_eq_zero.1 h1).resolve_left hqx
    exact eq_inv_of_mul_eq_one_right (by linear_combination -h2)
  have hSim : S.im ≤ 0 := by
    refine im_multiset_sum_nonpos _ fun t ht => ?_
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 ht
    rw [one_div, Complex.inv_im]
    have : 0 ≤ (x - z).im := by rw [sub_im]; linarith [hq z hz]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 this) (Complex.normSq_nonneg _)
  have hpos : 0 < (β⁻¹).im := by
    rw [Complex.inv_im]
    exact div_pos (neg_pos.2 hβ) (Complex.normSq_pos.2 hβ0)
  rw [hS] at hSim
  linarith

/-- **Peeling one multiplicity of the root `0`.** -/
theorem exists_peel {m : ℕ} {r : ℂ[X]} (hr0 : r.eval 0 ≠ 0) (hr : ∀ x ∈ r.roots, x.im < 0)
    {β : ℂ} (hβ : β.im < 0) :
    ∃ r' : ℂ[X], X ^ (m + 1) * r - C β * derivative (X ^ (m + 1) * r) = X ^ m * r' ∧
      r'.eval 0 ≠ 0 ∧ ∀ x ∈ r'.roots, x.im < 0 := by
  have hβ0 : β ≠ 0 := fun h0 => by rw [h0] at hβ; simp at hβ
  set r' := X * r - C β * (((m : ℂ[X]) + 1) * r + X * derivative r)
  have hr'0 : r'.eval 0 ≠ 0 := by
    have : r'.eval 0 = -(β * (((m : ℂ) + 1) * r.eval 0)) := by simp [r']
    rw [this]
    exact neg_ne_zero.2 (mul_ne_zero hβ0 (mul_ne_zero (Nat.cast_add_one_ne_zero m) hr0))
  have hrne : r ≠ 0 := fun h => hr0 (by rw [h, eval_zero])
  refine ⟨r', ?_, hr'0, fun x hx => ?_⟩
  · simp only [r', derivative_mul, derivative_X_pow, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one, map_add, map_one, map_natCast]
    ring
  have hr'ne : r' ≠ 0 := fun h => hr'0 (by rw [h, eval_zero])
  have hxr' : r'.eval x = 0 := (mem_roots hr'ne).1 hx
  have hx0 : x ≠ 0 := by rintro rfl; exact hr'0 hxr'
  set q := X ^ (m + 1) * r
  have hqne : q ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hrne
  by_cases hqx : q.eval x = 0
  · have : r.eval x = 0 := by
      simp only [q, eval_mul, eval_pow, eval_X] at hqx
      exact (mul_eq_zero.1 hqx).resolve_left (pow_ne_zero _ hx0)
    exact hr x ((mem_roots hrne).2 this)
  · refine im_neg_of_eval_sub_mul_derivative (q := q) (fun z hz => ?_) hβ hqx ?_
    · rw [roots_mul hqne, roots_X_pow, Multiset.mem_add] at hz
      rcases hz with hz | hz
      · have : z = 0 := by simpa using hz
        rw [this]; simp
      · exact (hr z hz).le
    · have hident : q - C β * derivative q = X ^ m * r' := by
        simp only [q, r', derivative_mul, derivative_X_pow, Nat.add_sub_cancel, Nat.cast_add,
          Nat.cast_one, map_add, map_one, map_natCast]
        ring
      have := congrArg (eval x) hident
      simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, hxr', mul_zero] at this
      exact this

theorem jensenRev_mul_linear (d : ℕ) (hd : 1 ≤ d) (f : PowerSeries ℂ) (β : ℂ) :
    jensenRev d (f * ((1 - C β * X : ℂ[X]) : PowerSeries ℂ)) =
      jensenRev d f - C β * derivative (jensenRev d f) := by
  rw [jensenRev_mul, ffConv_jensenRev_right (natDegree_jensenRev_le _ _),
    PowerSeries.trunc_coe_eq_self (by
      calc (1 - C β * X : ℂ[X]).natDegree ≤ 1 := by
            refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
            exact (natDegree_C_mul_le _ _).trans (by simp)
        _ < d + 1 := by omega),
    diffOp_sub_left, diffOp_C_mul_left, diffOp_X]
  simp [diffOp]

/-- **`d` strictly stable linear factors remove the root at `0`.** If `|S| = k ≤ d` and every `β_j`
has `Im β_j < 0`, then `R_d(Π_{j∈S}(1 − β_j w)) = X^{d−k} r` with `r(0) ≠ 0` and all roots of `r` in
`Im < 0`. -/
theorem exists_jensenRev_prod_linear_eq {ι : Type*} [DecidableEq ι] (β : ι → ℂ) {d : ℕ}
    (S : Finset ι) (hβ : ∀ j ∈ S, (β j).im < 0) (hk : S.card ≤ d) :
    ∃ r : ℂ[X], jensenRev d ((∏ j ∈ S, (1 - C (β j) * X) : ℂ[X]) : PowerSeries ℂ) =
      X ^ (d - S.card) * r ∧ r.eval 0 ≠ 0 ∧ ∀ x ∈ r.roots, x.im < 0 := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, ?_, by simp, by simp⟩
    have e : (1 : PowerSeries ℂ) = PowerSeries.mk fun k => (0 : ℂ) ^ k / (k.factorial : ℂ) := by
      ext k; rcases k with _ | k <;> simp [PowerSeries.coeff_one]
    simp only [Finset.prod_empty, Polynomial.coe_one, Finset.card_empty, Nat.sub_zero, mul_one]
    rw [e, jensenRev_exp]; simp
  | insert a S ha ih =>
    rw [Finset.card_insert_of_notMem ha] at hk
    obtain ⟨r, hr, hr0, hroots⟩ := ih (fun j hj => hβ j (Finset.mem_insert_of_mem hj)) (by omega)
    obtain ⟨m, hm⟩ : ∃ m, d - S.card = m + 1 := ⟨d - S.card - 1, by omega⟩
    obtain ⟨r', hr', hr'0, hroots'⟩ := exists_peel (m := m) hr0 hroots (hβ a (Finset.mem_insert_self a S))
    refine ⟨r', ?_, hr'0, hroots'⟩
    rw [Finset.prod_insert ha, Polynomial.coe_mul, mul_comm,
      jensenRev_mul_linear d (by omega), hr, hm, hr', Finset.card_insert_of_notMem ha,
      show d - (S.card + 1) = m by omega]

/-- **Hurwitz for polynomials of bounded degree, with a limiting margin.** -/
theorem im_le_of_tendsto_coeff {P : ℕ → ℂ[X]} {L : ℂ[X]} {d : ℕ}
    (hdeg : ∀ n, (P n).natDegree ≤ d) (hLd : L.natDegree ≤ d) (hL : L ≠ 0)
    (hconv : ∀ j, Tendsto (fun n => (P n).coeff j) atTop (𝓝 (L.coeff j)))
    {τ : ℕ → ℝ} {c : ℝ} (hτ : Tendsto τ atTop (𝓝 c))
    (hroots : ∀ᶠ n in atTop, ∀ x, (P n).IsRoot x → x.im ≤ τ n)
    {x : ℂ} (hx : L.IsRoot x) : x.im ≤ c := by
  have hconv' : TendstoLocallyUniformly (fun n z => (P n).eval z) (fun z => L.eval z) atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
    set R := max R₀ 0
    have hKR : ∀ u ∈ K, ‖u‖ ≤ R := fun u hu => by
      have := hR₀ hu; rw [mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    set e : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (d + 1), ‖(P n).coeff j - L.coeff j‖ * R ^ j
    have he : Tendsto e atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.range (d + 1)) fun j (_ : j ∈ Finset.range (d + 1)) =>
        (((hconv j).sub (tendsto_const_nhds (x := L.coeff j))).norm).mul_const (R ^ j)
      simpa using this
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [he.eventually (gt_mem_nhds hε)] with n hn u hu
    rw [dist_eq_norm, eval_eq_sum_range' (n := d + 1) (by omega),
      eval_eq_sum_range' (n := d + 1) (lt_of_le_of_lt (hdeg n) (by omega)), ← Finset.sum_sub_distrib]
    refine lt_of_le_of_lt ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)) hn
    rw [← sub_mul, norm_mul, norm_sub_rev, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg u) (hKR u hu) j) (norm_nonneg _)
  obtain ⟨a, ha⟩ : ∃ a, L.eval a ≠ 0 := by
    by_contra h; push Not at h
    exact hL (Polynomial.funext fun a => by rw [h a, eval_zero])
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hmem := RHTower.zero_mem_closed_of_tendstoLocallyUniformly hconv'
    (fun w _ => (Polynomial.differentiable L).analyticAt w)
    (Eventually.of_forall fun n => Polynomial.differentiable _)
    (isClosed_le Complex.continuous_im continuous_const : IsClosed {z : ℂ | z.im ≤ c + ε})
    ((hroots.and (hτ.eventually (gt_mem_nhds (by linarith : c < c + ε)))).mono
      fun n hn w hw => (hn.1 w hw).trans hn.2.le) ha hx
  simpa using hmem

/-! ## Strict stability of the shifted partial products -/

/-- With `d` zeros reserved in `S ⊆ F`, the roots of the partial product satisfy
`Im ≤ −μ − Im Σ_F 1/a_q`, where `μ > 0` is the margin of the reserved factors. -/
theorem im_le_of_isRoot_jensenRev_shiftedPartialProduct_reserved {δ : ℝ}
    (hzf : ∀ q : XiZeroCopy, -δ ≤ (xiSpectralPoint q).im) {d : ℕ} (hd : 1 ≤ d)
    {S : Finset XiZeroCopy} {μ : ℝ}
    (hS : ∀ x, (jensenRev d ((∏ q ∈ S, (1 - C (1 / (xiSpectralPoint q + I * δ)) * X) : ℂ[X]) :
      PowerSeries ℂ)).IsRoot x → x.im ≤ -μ)
    {F : Finset XiZeroCopy} (hSF : S ⊆ F) {x : ℂ}
    (hx : (jensenRev d (taylorPS (shiftedPartialProduct δ F))).IsRoot x) :
    x.im ≤ -μ - (∑ q ∈ F, 1 / xiSpectralPoint q).im := by
  classical
  rw [taylorPS_shiftedPartialProduct, mul_comm, jensenRev_expSeries_mul] at hx
  have hroot : (jensenRev d ((∏ q ∈ F, shiftedFactorPoly δ (xiSpectralPoint q) : ℂ[X]) :
      PowerSeries ℂ)).IsRoot (x + ∑ q ∈ F, 1 / xiSpectralPoint q) := by
    rw [IsRoot, eval_comp, eval_add, eval_X, eval_C] at hx
    exact hx
  have hpoly : ∏ q ∈ F, shiftedFactorPoly δ (xiSpectralPoint q) =
      C (∏ q ∈ F, weierstrassE1 (-(I * δ) / xiSpectralPoint q)) *
        ((∏ q ∈ F \ S, (1 - C (1 / (xiSpectralPoint q + I * δ)) * X)) *
          ∏ q ∈ S, (1 - C (1 / (xiSpectralPoint q + I * δ)) * X)) := by
    rw [Finset.prod_sdiff hSF]
    simp only [shiftedFactorPoly, Finset.prod_mul_distrib, map_prod]
  rw [hpoly, Polynomial.coe_mul, Polynomial.coe_C, jensenRev_C_mul, IsRoot, eval_mul,
    eval_C] at hroot
  have hc : ∏ q ∈ F, weierstrassE1 (-(I * δ) / xiSpectralPoint q) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun q _ => weierstrassE1_ne_zero_of_ne_one fun h => by
      have := xiSpectralPoint_add_ne (δ := δ) q
      apply this
      have ha := xiSpectralPoint_ne_zero q
      field_simp at h
      linear_combination -h
  have hr := (mul_eq_zero.1 hroot).resolve_left hc
  rw [Polynomial.coe_mul, jensenRev_mul, ffConv_comm (natDegree_jensenRev_le _ _)
    (natDegree_jensenRev_le _ _)] at hr
  have hc1 := constantCoeff_coe_prod_linear S fun q => 1 / (xiSpectralPoint q + I * δ)
  have hc2 := constantCoeff_coe_prod_linear (F \ S) fun q => 1 / (xiSpectralPoint q + I * δ)
  have := ffConv_root_im_le (jensenRev_ne_zero (by rw [hc1]; exact one_ne_zero))
    (natDegree_jensenRev (by rw [hc1]; exact one_ne_zero))
    (jensenRev_ne_zero (by rw [hc2]; exact one_ne_zero)) (natDegree_jensenRev_le _ _)
    (a := -μ) (b := 0) hS
    (fun ν hν => im_le_zero_of_isRoot_jensenRev_prod_linear (F \ S) _ (fun q _ => by
      rw [one_div, Complex.inv_im]
      have him : 0 ≤ (xiSpectralPoint q + I * δ).im := by
        simp only [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add]
        linarith [hzf q]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 him) (Complex.normSq_nonneg _)) hd hν) hr
  rw [add_im] at this
  linarith

/-- **Strict stability from infinitely many strictly placed zeros.** If every zero of `Ξ` has
`Im a_q ≥ −δ` and infinitely many have `Im a_q > −δ`, every root of every
`R_d(ξ(1/2 + δ + i·))`, `d ≥ 1`, has `Im < 0`. -/
theorem im_neg_of_isRoot_jensenRev_xiShift_of_infinite {δ : ℝ}
    (hweak : ∀ q : XiZeroCopy, -δ ≤ (xiSpectralPoint q).im)
    (hinf : {q : XiZeroCopy | -δ < (xiSpectralPoint q).im}.Infinite) {d : ℕ} (hd : 1 ≤ d)
    {x : ℂ} (hx : (jensenRev d (PowerSeries.mk (xiShiftCoeff (1 / 2 + δ)))).IsRoot x) :
    x.im < 0 := by
  classical
  set σ : ℝ := 1 / 2 + δ
  have h0 : XiC 0 ≠ 0 := XiC_zero_ne
  set ℓ : ℕ → ℂ := fun k => xiShiftCoeff σ k / XiC 0
  have hmk : PowerSeries.mk (xiShiftCoeff σ) = PowerSeries.C (XiC 0) * PowerSeries.mk ℓ := by
    ext k; simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ℓ]; field_simp
  set L := jensenRev d (PowerSeries.mk ℓ)
  have hxL : L.IsRoot x := by
    rw [hmk, jensenRev_C_mul, IsRoot, eval_mul, eval_C] at hx
    exact (mul_eq_zero.1 hx).resolve_left h0
  have hℓ0 : ℓ 0 ≠ 0 := div_ne_zero (xiShiftCoeff_zero_ne σ) h0
  -- the reserved factors and their margin
  obtain ⟨S, hSsub, hScard⟩ := hinf.exists_subset_card_eq d
  set β : XiZeroCopy → ℂ := fun q => 1 / (xiSpectralPoint q + I * δ)
  have hβ : ∀ q ∈ S, (β q).im < 0 := fun q hq => by
    simp only [β, one_div, Complex.inv_im]
    have him : 0 < (xiSpectralPoint q + I * δ).im := by
      simp only [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add]
      linarith [show -δ < (xiSpectralPoint q).im from hSsub hq]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos him) (Complex.normSq_pos.2 fun h => by
      rw [h] at him; simp at him)
  obtain ⟨r, hr, hr0, hroots⟩ := exists_jensenRev_prod_linear_eq β S hβ hScard.le
  rw [hScard, Nat.sub_self, pow_zero, one_mul] at hr
  have hrne : r ≠ 0 := fun h => hr0 (by rw [h, eval_zero])
  obtain ⟨μ, hμ, hμroots⟩ : ∃ μ : ℝ, 0 < μ ∧ ∀ y ∈ r.roots, y.im ≤ -μ := by
    rcases r.roots.toFinset.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun y hy => absurd (Multiset.mem_toFinset.2 hy) (by rw [he]; simp)⟩
    · obtain ⟨y₀, hy₀, hmax⟩ := r.roots.toFinset.exists_max_image Complex.im hne
      exact ⟨-y₀.im, by linarith [hroots y₀ (Multiset.mem_toFinset.1 hy₀)],
        fun y hy => by linarith [hmax y (Multiset.mem_toFinset.2 hy)]⟩
  have hSroots : ∀ y, (jensenRev d ((∏ q ∈ S, (1 - C (1 / (xiSpectralPoint q + I * δ)) * X) :
      ℂ[X]) : PowerSeries ℂ)).IsRoot y → y.im ≤ -μ := fun y hy => by
    rw [show (∏ q ∈ S, (1 - C (1 / (xiSpectralPoint q + I * δ)) * X) : ℂ[X]) =
      ∏ q ∈ S, (1 - C (β q) * X) from rfl, hr] at hy
    exact hμroots y ((mem_roots hrne).2 hy)
  -- the limit along an exhausting sequence of finite sets of zeros
  obtain ⟨Fseq, hF⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset XiZeroCopy))
  have hLne : L ≠ 0 := fun h => by
    have := coeff_jensenRev d (PowerSeries.mk ℓ) (le_refl d)
    rw [← show L = jensenRev d (PowerSeries.mk ℓ) from rfl, h, coeff_zero, Nat.sub_self,
      PowerSeries.coeff_mk, Nat.descFactorial_zero, Nat.cast_one, mul_one] at this
    exact hℓ0 this.symm
  have hsum : HasSum (fun q : XiZeroCopy => (1 / xiSpectralPoint q).im) 0 := by
    have := summable_im_inv_xiSpectralPoint.hasSum
    rwa [tsum_im_inv_xiSpectralPoint] at this
  have hle := im_le_of_tendsto_coeff (P := fun n => jensenRev d (taylorPS
    (shiftedPartialProduct δ (Fseq n)))) (fun n => natDegree_jensenRev_le _ _)
    (natDegree_jensenRev_le _ _) hLne (fun j => ?_)
    (τ := fun n => -μ - (∑ q ∈ Fseq n, 1 / xiSpectralPoint q).im) (c := -μ - 0) ?_
    ((hF.eventually (eventually_ge_atTop S)).mono fun n hn y hy =>
      im_le_of_isRoot_jensenRev_shiftedPartialProduct_reserved hweak hd hSroots hn hy) hxL
  · linarith
  · rcases le_or_gt j d with hj | hj
    · simp only [coeff_jensenRev d _ hj, PowerSeries.coeff_mk]
      exact ((tendsto_coeff_taylorPS_shiftedPartialProduct δ (d - j)).comp hF).mul_const _
    · simp only [coeff_jensenRev_of_lt d _ hj]
      exact tendsto_const_nhds
  · have := (hsum.comp hF)
    refine (tendsto_const_nhds.sub this).congr fun n => ?_
    simp only [Function.comp_def]
    rw [Complex.im_sum]

/-- **Closed zero-free half-planes give strict stability.** If every zero of `Ξ` has `Im a_q > −δ`
(equivalently `ξ ≠ 0` on `Re s ≥ 1/2 + δ`), every root of every `R_d(ξ(1/2 + δ + i·))`, `d ≥ 1`, has
`Im < 0`. -/
theorem im_neg_of_isRoot_jensenRev_xiShift {δ : ℝ}
    (hzf : ∀ q : XiZeroCopy, -δ < (xiSpectralPoint q).im) {d : ℕ} (hd : 1 ≤ d) {x : ℂ}
    (hx : (jensenRev d (PowerSeries.mk (xiShiftCoeff (1 / 2 + δ)))).IsRoot x) : x.im < 0 := by
  haveI := infinite_xiZeroCopy
  exact im_neg_of_isRoot_jensenRev_xiShift_of_infinite (fun q => (hzf q).le)
    (by simpa [Set.setOf_forall, hzf] using Set.infinite_univ (α := XiZeroCopy)) hd hx

/-- **Strict stability right of a closed zero-free half-plane.** -/
theorem im_neg_of_closed_zeroFree {σ : ℝ} (hzf : ∀ ρ : ℂ, xi ρ = 0 → ρ.re < σ) {d : ℕ}
    (hd : 1 ≤ d) {x : ℂ} (hx : (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).IsRoot x) :
    x.im < 0 := by
  refine im_neg_of_isRoot_jensenRev_xiShift (δ := σ - 1 / 2) (fun q => ?_) hd
    (by rwa [show (1 / 2 : ℝ) + (σ - 1 / 2) = σ by ring])
  rw [xiSpectralPoint_im]
  have := hzf _ (xi_eq_zero_of_mem_divisor_support q.1)
  linarith

/-- **Unconditional strict finite free stability at `Re s ≥ 1`.** For `σ ≥ 1` and `d ≥ 1`, every
root of the reversed Jensen polynomial of `ξ(σ + i·)` lies in the open lower half-plane. -/
theorem im_neg_of_one_le {σ : ℝ} (hσ : 1 ≤ σ) {d : ℕ} (hd : 1 ≤ d) {x : ℂ}
    (hx : (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).IsRoot x) : x.im < 0 := by
  refine im_neg_of_isRoot_jensenRev_xiShift (δ := σ - 1 / 2) (fun q => ?_) hd
    (by rwa [show (1 / 2 : ℝ) + (σ - 1 / 2) = σ by ring])
  linarith [(xiSpectralPoint_im_mem_openHalf q).1]

/-! ## Right of the critical line, open and closed coincide -/

/-- For `δ > 0`, zeros on the line `Im a_q = −δ` reflect to `Im = δ > −δ`; so if no zero lies below
`−δ`, infinitely many lie strictly above it. -/
theorem infinite_strict_of_weak {δ : ℝ} (hδ : 0 < δ)
    (hweak : ∀ q : XiZeroCopy, -δ ≤ (xiSpectralPoint q).im) :
    {q : XiZeroCopy | -δ < (xiSpectralPoint q).im}.Infinite := by
  haveI := infinite_xiZeroCopy
  intro hfin
  refine Set.infinite_of_injOn_mapsTo (f := xiZeroCopyLineConjEquiv)
    xiZeroCopyLineConjEquiv.injective.injOn (fun q hq => ?_) hfin.infinite_compl hfin
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hq
  simp only [Set.mem_setOf_eq, xiSpectralPoint_lineConj, Complex.conj_im]
  have := hweak q
  linarith

/-- **Strict stability on lines right of the critical line.** For `σ > 1/2`, if `ξ` has no zero with
`Re ρ > σ`, every root of every `R_d(ξ(σ + i·))`, `d ≥ 1`, has `Im < 0`. -/
theorem im_neg_of_zeroFree {σ : ℝ} (hσ : 1 / 2 < σ) (hzf : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ σ)
    {d : ℕ} (hd : 1 ≤ d) {x : ℂ}
    (hx : (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).IsRoot x) : x.im < 0 := by
  have hweak : ∀ q : XiZeroCopy, -(σ - 1 / 2) ≤ (xiSpectralPoint q).im := fun q => by
    rw [xiSpectralPoint_im]
    have := hzf _ (xi_eq_zero_of_mem_divisor_support q.1)
    linarith
  exact im_neg_of_isRoot_jensenRev_xiShift_of_infinite hweak
    (infinite_strict_of_weak (by linarith) hweak) hd
    (by rwa [show (1 / 2 : ℝ) + (σ - 1 / 2) = σ by ring])

/-- **The finite free half-plane theorem, strict form.** For `σ > 1/2`, `ξ` has no zero with
`Re ρ > σ` iff every root of every `R_d(ξ(σ + i·))`, `d ≥ 1`, lies in the open lower half-plane. -/
theorem zeroFree_iff_forall_im_neg {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ σ) ↔
      ∀ d : ℕ, 1 ≤ d → ∀ x, (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).IsRoot x → x.im < 0 := by
  refine ⟨fun h d hd x hx => im_neg_of_zeroFree hσ h hd hx, fun h => ?_⟩
  refine (zeroFree_iff_exists_frequently_im_le σ).2 ⟨0, ?_⟩
  exact (eventually_ge_atTop 1).frequently.mono fun d hd x hx => (h d hd x hx).le

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.im_neg_of_one_le
#print axioms FiniteFreeProbability.zeroFree_iff_forall_im_neg

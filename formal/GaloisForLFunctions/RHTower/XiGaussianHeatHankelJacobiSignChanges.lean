import GaloisForLFunctions.RHTower.XiGaussianHeatHankelDeterminantSignLaw
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelDeterminantBlowup

/-!
# Jacobi's rule for the heat Hankel ladder: off-line zeros as sign changes

Let `Δ_N(a) = det(M_{i+j}(a))_{i,j<N}` (`Δ_0 = 1`) and let `ν_N(a)` be the negative inertia of the
`N`-th heat moment section.

* Adding one row and column changes the negative inertia by at most one:
  `ν_N ≤ ν_{N+1} ≤ ν_N + 1` (`hermNegIndex_heatMomentSection_le_succ`,
  `hermNegIndex_heatMomentSection_succ_le`).
* A nonzero determinant has sign `(−1)^{ν_N}` (`neg_one_pow_negIndex_mul_heatMomentDet_pos`).

Hence, at a heat time where `Δ_0, …, Δ_N` are nonzero,
`ν_{N+1} − ν_N = [Δ_N Δ_{N+1} < 0]` and

**Theorem** (`hermNegIndex_heatMomentSection_eq_signChanges`, Jacobi's rule).
`ν_N(a) = #{k < N : Δ_k(a) Δ_{k+1}(a) < 0}`.

With the index law the number of off-line zero quadruples is the number of sign changes of the
sequence `(Δ_N(a))_N` at every heat time where no `Δ_N(a)` vanishes
(`card_eq_signChanges_heatMomentDet`).  Infinitely many off-line quadruples give infinitely many
sign changes (`exists_lt_signChanges_heatMomentDet_of_infinite`).

Such heat times are dense: each `Δ_N` is real-analytic on `(0, ∞)` (its entries are real parts of
the holomorphic moments `M_n(τ)`) and positive in the window `a N ≤ κ`, so its zeros are isolated.
The Baire category theorem then gives, in every interval of `(0, ∞)`, a heat time at which no
`Δ_N` vanishes (`exists_mem_Ioo_forall_heatMomentDet_ne_zero`).  So the off-line count is the
sign-change count at a dense set of heat times, unconditionally
(`exists_heatTime_signChanges_eq_card`).
-/

open Complex Polynomial Matrix Filter Topology Set
open GaloisForLFunctions.HTGeometry (leadingMatrix hermQuad hermQuad_neg IsPosDefOn hermPosIndex
  hermNegIndex exists_isPosDefOn_finrank_eq_posIndex finrank_le_posIndex)

namespace RHTower

noncomputable section

/-! ## Extension by zero -/

/-- Extension of a coefficient vector by a zero top coefficient. -/
def heatCoeffExt (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] (Fin (N + 1) → ℂ) where
  toFun x i := if h : (i : ℕ) < N then x ⟨i, h⟩ else 0
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem heatCoeffExt_castSucc {N : ℕ} (x : Fin N → ℂ) (i : Fin N) :
    heatCoeffExt N x i.castSucc = x i := by
  simp [heatCoeffExt, i.2]

theorem heatCoeffExt_last {N : ℕ} (x : Fin N → ℂ) : heatCoeffExt N x (Fin.last N) = 0 := by
  simp [heatCoeffExt]

theorem heatCoeffExt_injective (N : ℕ) : Function.Injective (heatCoeffExt N) := by
  intro x y h
  funext i
  have := congrFun h i.castSucc
  rwa [heatCoeffExt_castSucc, heatCoeffExt_castSucc] at this

theorem heatCoeffPoly_heatCoeffExt {N : ℕ} (x : Fin N → ℂ) :
    heatCoeffPoly (heatCoeffExt N x) = heatCoeffPoly x := by
  rw [heatCoeffPoly, Fin.sum_univ_castSucc, heatCoeffExt_last]
  simp only [heatCoeffExt_castSucc, map_zero, zero_mul, add_zero]
  rfl

theorem hermQuad_heatMomentSection_heatCoeffExt {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 0 < N)
    (x : Fin N → ℂ) :
    hermQuad (heatMomentSection a (N + 1)) (heatCoeffExt N x) =
      hermQuad (heatMomentSection a N) x := by
  rw [hermQuad_heatMomentSection ha (Nat.succ_pos N), hermQuad_heatMomentSection ha hN,
    heatCoeffPoly_heatCoeffExt]

/-- A vector with zero top coordinate is the extension of its truncation. -/
theorem heatCoeffExt_truncate {N : ℕ} {x : Fin (N + 1) → ℂ} (hx : x (Fin.last N) = 0) :
    heatCoeffExt N (fun i => x i.castSucc) = x := by
  funext i
  simp only [heatCoeffExt, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with hi
  · exact congrArg x (Fin.ext rfl)
  · have : i = Fin.last N := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
    rw [this, hx]

/-! ## Interlacing of the negative inertia -/

theorem hermNegIndex_heatMomentSection_zero (a : ℝ) : hermNegIndex (heatMomentSection a 0) = 0 := by
  obtain ⟨W, hW, -⟩ := exists_isPosDefOn_finrank_eq_posIndex (-heatMomentSection a 0)
  rw [hermNegIndex, ← hW]
  have h := Submodule.finrank_le W
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

/-- The negative inertia does not decrease along the ladder. -/
theorem hermNegIndex_heatMomentSection_le_succ {a : ℝ} (ha : 0 < a) (N : ℕ) :
    hermNegIndex (heatMomentSection a N) ≤ hermNegIndex (heatMomentSection a (N + 1)) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [hermNegIndex_heatMomentSection_zero]; exact Nat.zero_le _
  obtain ⟨W, hW, hpos⟩ := exists_isPosDefOn_finrank_eq_posIndex (-heatMomentSection a N)
  rw [hermNegIndex, hermNegIndex, ← hW,
    ← LinearMap.finrank_range_of_inj (f := (heatCoeffExt N).comp W.subtype)
      ((heatCoeffExt_injective N).comp Subtype.val_injective)]
  refine finrank_le_posIndex fun y hy hy0 => ?_
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hy
  have hx0 : (x : Fin N → ℂ) ≠ 0 := by
    intro h
    apply hy0
    simp [h]
  have h := hpos x x.2 hx0
  rw [hermQuad_neg] at h ⊢
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
  rw [hermQuad_heatMomentSection_heatCoeffExt ha hN]
  exact h

/-- One more row and column raises the negative inertia by at most one. -/
theorem hermNegIndex_heatMomentSection_succ_le {a : ℝ} (ha : 0 < a) (N : ℕ) :
    hermNegIndex (heatMomentSection a (N + 1)) ≤ hermNegIndex (heatMomentSection a N) + 1 := by
  obtain ⟨W, hW, hpos⟩ := exists_isPosDefOn_finrank_eq_posIndex (-heatMomentSection a (N + 1))
  rw [hermNegIndex, ← hW]
  -- the top-coordinate functional on `W`
  obtain ⟨f, hf⟩ : ∃ f : W →ₗ[ℂ] ℂ, ∀ w : W, f w = (w : Fin (N + 1) → ℂ) (Fin.last N) :=
    ⟨(LinearMap.proj (Fin.last N)).comp W.subtype, fun _ => rfl⟩
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hr1 : Module.finrank ℂ (LinearMap.range f) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_self] at this
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h := Submodule.finrank_le W
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  -- truncate the kernel
  set Φ : LinearMap.ker f →ₗ[ℂ] (Fin N → ℂ) :=
    (LinearMap.funLeft ℂ ℂ Fin.castSucc).comp (W.subtype.comp (LinearMap.ker f).subtype) with hΦ
  have hlast : ∀ y : LinearMap.ker f, ((y : W) : Fin (N + 1) → ℂ) (Fin.last N) = 0 := fun y => by
    have h0 := LinearMap.mem_ker.1 y.2
    rwa [hf] at h0
  have hΦext : ∀ y : LinearMap.ker f, heatCoeffExt N (Φ y) = ((y : W) : Fin (N + 1) → ℂ) :=
    fun y => heatCoeffExt_truncate (hlast y)
  have hinj : Function.Injective Φ := by
    intro y z h
    have := congrArg (heatCoeffExt N) h
    rw [hΦext, hΦext] at this
    exact Subtype.ext (Subtype.ext this)
  have hneg : IsPosDefOn (-heatMomentSection a N) (LinearMap.range Φ) := by
    intro z hz hz0
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hz
    have hy0 : ((y : W) : Fin (N + 1) → ℂ) ≠ 0 := by
      intro h
      apply hz0
      rw [← hΦext y] at h
      exact (heatCoeffExt_injective N) (h.trans (map_zero _).symm)
    have h := hpos (y : W) (y : W).2 hy0
    rw [hermQuad_neg] at h ⊢
    rw [← hermQuad_heatMomentSection_heatCoeffExt ha hN, hΦext]
    exact h
  have hle := finrank_le_posIndex hneg
  rw [LinearMap.finrank_range_of_inj hinj] at hle
  rw [hermNegIndex]
  omega

/-! ## Signs of the determinants -/

/-- A nonzero heat Hankel determinant has sign `(−1)^{ν_N}`. -/
theorem neg_one_pow_negIndex_mul_heatMomentDet_pos {a : ℝ} {N : ℕ}
    (hN : (leadingMatrix (heatMomentArray a) N).det ≠ 0) :
    0 < (-1 : ℝ) ^ hermNegIndex (heatMomentSection a N) *
      (leadingMatrix (heatMomentArray a) N).det := by
  have h := neg_one_pow_negIndex_mul_det_re_nonneg (isHermitian_heatMomentSection a N)
  rw [det_heatMomentSection, ofReal_re] at h
  refine lt_of_le_of_ne h fun h0 => hN ?_
  rcases mul_eq_zero.1 h0.symm with h1 | h1
  · exact absurd h1 (pow_ne_zero _ (by norm_num))
  · exact h1

/-- **One step of Jacobi's rule.**  If `Δ_N, Δ_{N+1} ≠ 0`, then
`ν_{N+1} = ν_N + [Δ_N Δ_{N+1} < 0]`. -/
theorem hermNegIndex_heatMomentSection_succ_eq {a : ℝ} (ha : 0 < a) {N : ℕ}
    (hN : (leadingMatrix (heatMomentArray a) N).det ≠ 0)
    (hN1 : (leadingMatrix (heatMomentArray a) (N + 1)).det ≠ 0) :
    hermNegIndex (heatMomentSection a (N + 1)) = hermNegIndex (heatMomentSection a N) +
      (if (leadingMatrix (heatMomentArray a) N).det *
          (leadingMatrix (heatMomentArray a) (N + 1)).det < 0 then 1 else 0) := by
  have h1 := hermNegIndex_heatMomentSection_le_succ ha N
  have h2 := hermNegIndex_heatMomentSection_succ_le ha N
  have s1 := neg_one_pow_negIndex_mul_heatMomentDet_pos hN
  have s2 := neg_one_pow_negIndex_mul_heatMomentDet_pos hN1
  set ν := hermNegIndex (heatMomentSection a N)
  set ν' := hermNegIndex (heatMomentSection a (N + 1))
  set d := (leadingMatrix (heatMomentArray a) N).det
  set d' := (leadingMatrix (heatMomentArray a) (N + 1)).det
  rcases Nat.lt_or_ge ν' (ν + 1) with hlt | hge
  · -- `ν' = ν`: equal signs
    have he : ν' = ν := by omega
    rw [he] at s2
    have hprod : 0 < ((-1 : ℝ) ^ ν * d) * ((-1 : ℝ) ^ ν * d) := mul_pos s1 s1
    have : 0 < d * d' := by
      have hm := mul_pos s1 s2
      have hsq : ((-1 : ℝ) ^ ν) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      nlinarith [hsq]
    rw [if_neg (not_lt.2 this.le)]
    omega
  · -- `ν' = ν + 1`: opposite signs
    have he : ν' = ν + 1 := by omega
    rw [he, pow_succ] at s2
    have : d * d' < 0 := by
      have hm := mul_pos s1 s2
      have hsq : ((-1 : ℝ) ^ ν) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      nlinarith [hsq]
    rw [if_pos this, he]

/-! ## Jacobi's rule and the off-line count -/

/-- The number of sign changes in `Δ_0, …, Δ_N`. -/
def heatDetSignChanges (a : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun k => (leadingMatrix (heatMomentArray a) k).det *
    (leadingMatrix (heatMomentArray a) (k + 1)).det < 0).card

theorem heatDetSignChanges_succ (a : ℝ) (N : ℕ) :
    heatDetSignChanges a (N + 1) = heatDetSignChanges a N +
      (if (leadingMatrix (heatMomentArray a) N).det *
          (leadingMatrix (heatMomentArray a) (N + 1)).det < 0 then 1 else 0) := by
  unfold heatDetSignChanges
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

/-- **Jacobi's rule for the heat Hankel ladder.**  If `Δ_0(a), …, Δ_N(a)` are nonzero, the negative
inertia of the `N`-th section is the number of sign changes in `Δ_0(a), …, Δ_N(a)`. -/
theorem hermNegIndex_heatMomentSection_eq_signChanges {a : ℝ} (ha : 0 < a) {N : ℕ}
    (hne : ∀ k ≤ N, (leadingMatrix (heatMomentArray a) k).det ≠ 0) :
    hermNegIndex (heatMomentSection a N) = heatDetSignChanges a N := by
  induction N with
  | zero => rw [hermNegIndex_heatMomentSection_zero]; rfl
  | succ N ih =>
    rw [hermNegIndex_heatMomentSection_succ_eq ha (hne N (by omega)) (hne (N + 1) le_rfl),
      ih fun k hk => hne k (by omega), heatDetSignChanges_succ]

/-- **Off-line zeros as sign changes.**  If there are finitely many off-line zero quadruples and no
`Δ_N(a)` vanishes, their number is the total number of sign changes of `(Δ_N(a))_N`: the count is
eventually `#U`. -/
theorem card_eq_signChanges_heatMomentDet {a : ℝ} (ha : 0 < a) (hU : xiUpperFrequencies.Finite)
    (hne : ∀ N, (leadingMatrix (heatMomentArray a) N).det ≠ 0) :
    ∃ N₀, ∀ N ≥ N₀, heatDetSignChanges a N = hU.toFinset.card := by
  obtain ⟨N₀, hN₀⟩ := exists_hermNegIndex_heatMomentSection_eq ha hU
  exact ⟨N₀, fun N hN => (hermNegIndex_heatMomentSection_eq_signChanges ha
    fun k _ => hne k).symm.trans (hN₀ N hN)⟩

/-- Infinitely many off-line quadruples give infinitely many sign changes. -/
theorem exists_lt_signChanges_heatMomentDet_of_infinite {a : ℝ} (ha : 0 < a)
    (hU : xiUpperFrequencies.Infinite)
    (hne : ∀ N, (leadingMatrix (heatMomentArray a) N).det ≠ 0) (n : ℕ) :
    ∃ N₀, ∀ N ≥ N₀, n ≤ heatDetSignChanges a N := by
  obtain ⟨N₀, hN₀⟩ := exists_le_hermNegIndex_heatMomentSection_of_infinite ha hU n
  exact ⟨N₀, fun N hN => (hN₀ N hN).trans_eq
    (hermNegIndex_heatMomentSection_eq_signChanges ha fun k _ => hne k)⟩

/-! ## Heat times at which no determinant vanishes -/

theorem analyticAt_heatMomentArray {a : ℝ} (ha : 0 < a) (i j : ℕ) :
    AnalyticAt ℝ (fun b : ℝ => heatMomentArray b i j) a := by
  have hd : DifferentiableOn ℂ (xiHeatMoment (i + j)) {τ : ℂ | 0 < τ.re} := fun τ hτ =>
    (hasDerivAt_xiHeatMoment _ hτ).differentiableAt.differentiableWithinAt
  have han := hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  have h : AnalyticAt ℂ (xiHeatMoment (i + j)) (a : ℂ) := han _ (by simpa using ha)
  exact h.re_ofReal

/-- Each heat Hankel determinant is real-analytic on `(0, ∞)`. -/
theorem analyticAt_heatMomentDet {a : ℝ} (ha : 0 < a) (N : ℕ) :
    AnalyticAt ℝ (heatMomentDet N) a := by
  have hrw : heatMomentDet N = fun b : ℝ => ∑ σ : Equiv.Perm (Fin N),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i : Fin N, heatMomentArray b (σ i) i := by
    funext b
    rw [heatMomentDet, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    rfl
  rw [hrw]
  have hterm : ∀ σ : Equiv.Perm (Fin N), AnalyticAt ℝ (fun b : ℝ =>
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i : Fin N, heatMomentArray b (σ i) i) a := by
    intro σ
    refine analyticAt_const.mul ?_
    have := Finset.analyticAt_prod (𝕜 := ℝ) (f := fun (i : Fin N) (b : ℝ) =>
      heatMomentArray b (σ i) i) (c := a) Finset.univ fun i _ => analyticAt_heatMomentArray ha _ _
    have e : (∏ i : Fin N, fun b : ℝ => heatMomentArray b (σ i) i) =
        fun b : ℝ => ∏ i : Fin N, heatMomentArray b (σ i) i := by
      funext b
      rw [Finset.prod_apply]
    rwa [e] at this
  have := Finset.analyticAt_sum (𝕜 := ℝ) (f := fun (σ : Equiv.Perm (Fin N)) (b : ℝ) =>
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i : Fin N, heatMomentArray b (σ i) i) (c := a)
    Finset.univ fun σ _ => hterm σ
  have e : (∑ σ : Equiv.Perm (Fin N), fun b : ℝ =>
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i : Fin N, heatMomentArray b (σ i) i) =
      fun b : ℝ => ∑ σ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i : Fin N, heatMomentArray b (σ i) i := by
    funext b
    rw [Finset.sum_apply]
  rwa [e] at this

/-- The zeros of each `Δ_N` in `(0, ∞)` are isolated. -/
theorem eventually_heatMomentDet_ne_zero {a₀ : ℝ} (ha₀ : 0 < a₀) (N : ℕ) :
    ∀ᶠ a in 𝓝[≠] a₀, heatMomentDet N a ≠ 0 := by
  rcases (analyticAt_heatMomentDet ha₀ N).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hon : AnalyticOnNhd ℝ (heatMomentDet N) (Ioi 0) := fun a ha =>
      analyticAt_heatMomentDet ha N
    have hfreq : ∃ᶠ z in 𝓝[≠] a₀, heatMomentDet N z = 0 :=
      (h.filter_mono nhdsWithin_le_nhds).frequently
    have heq := hon.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_Ioi ha₀ hfreq
    set b := routeUCompletedPrimeGammaAperture / (N + 1) with hb
    have hκ := routeUCompletedPrimeGammaAperture_pos
    have hb0 : 0 < b := by positivity
    have hbN : b * N ≤ routeUCompletedPrimeGammaAperture := by
      rw [hb, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have hpos := heatMomentDet_pos_of_mul_le hb0 hbN
    have h0 := heq (mem_Ioi.2 hb0)
    simp only [Pi.zero_apply] at h0
    rw [heatMomentDet] at h0
    linarith
  · exact h

/-- **Generic heat times.**  Every interval of `(0, ∞)` contains a heat time at which no heat
Hankel determinant vanishes. -/
theorem exists_mem_Ioo_forall_heatMomentDet_ne_zero {a₁ a₂ : ℝ} (h0 : 0 ≤ a₁) (h : a₁ < a₂) :
    ∃ a ∈ Ioo a₁ a₂, ∀ N : ℕ, (leadingMatrix (heatMomentArray a) N).det ≠ 0 := by
  set U : ℕ → Set ℝ := fun N => Iio 0 ∪ (Ioi 0 ∩ heatMomentDet N ⁻¹' {0}ᶜ) with hU
  have hopen : ∀ N, IsOpen (U N) := fun N =>
    isOpen_Iio.union ((continuousOn_heatMomentDet N).isOpen_inter_preimage isOpen_Ioi
      isOpen_compl_singleton)
  have hdense : ∀ N, Dense (U N) := by
    intro N x
    rw [mem_closure_iff_frequently]
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · exact ((eventually_lt_nhds hx).mono fun y hy => Or.inl hy).frequently
    · exact (frequently_lt_nhds (0 : ℝ)).mono fun y hy => Or.inl hy
    · have h1 := eventually_heatMomentDet_ne_zero hx N
      have h2 : ∀ᶠ y in 𝓝[≠] x, 0 < y :=
        eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hx)
      exact ((h1.and h2).frequently.mono fun y hy => Or.inr ⟨hy.2, hy.1⟩).filter_mono
        nhdsWithin_le_nhds
  have hD := dense_iInter_of_isOpen_nat hopen hdense
  obtain ⟨a, ha, haU⟩ := hD.inter_open_nonempty (Ioo a₁ a₂) isOpen_Ioo (nonempty_Ioo.2 h)
  refine ⟨a, ha, fun N => ?_⟩
  rcases mem_iInter.1 haU N with hN | hN
  · exact absurd (lt_of_le_of_lt h0 ha.1) (not_lt.2 (le_of_lt (mem_Iio.1 hN)))
  · exact hN.2

/-- **Off-line zeros as sign changes, unconditionally.**  Every interval of `(0, ∞)` contains a heat
time `a` at which the number of off-line zero quadruples is the number of sign changes of
`(Δ_N(a))_N`: eventually `#U` sign changes if `U` is finite, and unboundedly many if `U` is
infinite. -/
theorem exists_heatTime_signChanges_eq_card {a₁ a₂ : ℝ} (h0 : 0 ≤ a₁) (h : a₁ < a₂) :
    ∃ a ∈ Ioo a₁ a₂,
      (∀ hU : xiUpperFrequencies.Finite, ∃ N₀, ∀ N ≥ N₀, heatDetSignChanges a N = hU.toFinset.card) ∧
      (xiUpperFrequencies.Infinite → ∀ n : ℕ, ∃ N₀, ∀ N ≥ N₀, n ≤ heatDetSignChanges a N) := by
  obtain ⟨a, ha, hne⟩ := exists_mem_Ioo_forall_heatMomentDet_ne_zero h0 h
  have ha0 : 0 < a := lt_of_le_of_lt h0 ha.1
  exact ⟨a, ha, fun hU => card_eq_signChanges_heatMomentDet ha0 hU hne,
    fun hU n => exists_lt_signChanges_heatMomentDet_of_infinite ha0 hU hne n⟩

end

end RHTower

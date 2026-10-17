import GaloisForLFunctions.HTGeometry.RieszProjectionPowerCalculus
import GaloisForLFunctions.HTGeometry.ConvexCompactComplementConnected

/-!
# Spectral circles of a power-decomposable operator

Let `T` be a bounded operator on a complex Banach space with `T^N = F + S`, `F` of finite rank and
`‖S‖ < a^N`.  Then the spectrum of `T` meets every annulus `a ≤ |z| ≤ b` in finitely many points,
so between any two radii `a < b` there is a circle in the resolvent set of `T`.

The proof is the finite-rank Fredholm determinant.  Writing `F v = Σ_i φ_i(v) e_i` in a basis of the
range, `w − T^N = (w − S)(1 − R_S(w) F)` for `|w| > ‖S‖`, and `1 − R_S(w)F` is invertible exactly
when the matrix `1 − (φ_j(R_S(w) e_k))` is (`isUnit_one_sub_mul_of_det_ne_zero`,
`exists_fixedPoint_of_det_eq_zero`).  The determinant `D(w)` is holomorphic on the connected set
`|w| > ‖S‖` and nonzero for large `|w|`, so its zeros are isolated; each spectral point `z` of `T`
in the annulus gives a zero `w = z^N` of `D`.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Filter Topology FiniteRank Module
open scoped Matrix

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ## Finite-rank factorization -/

section FiniteRankFactor

variable (F : E →L[ℂ] E) [FiniteDimensional ℂ (opRange F)]

/-- Index set of a basis of the range of `F`. -/
abbrev RankIndex := Fin (finrank ℂ (opRange F))

/-- The chosen basis of the range of `F`. -/
def rankBasis : Basis (RankIndex F) ℂ (opRange F) := Module.finBasis ℂ (opRange F)

/-- The basis vectors of the range of `F`, as vectors of `E`. -/
def rankVec (i : RankIndex F) : E := (rankBasis F i : E)

/-- The coordinate functionals `φ_i` with `F v = Σ_i φ_i(v) e_i`. -/
def rankCoord (i : RankIndex F) : E →L[ℂ] ℂ :=
  (LinearMap.toContinuousLinearMap ((rankBasis F).coord i)).comp
    (F.codRestrict (opRange F) (mem_opRange F))

theorem apply_eq_sum_rankCoord (v : E) : F v = ∑ i, rankCoord F i v • rankVec F i := by
  have h := (rankBasis F).sum_repr ⟨F v, mem_opRange F v⟩
  have h2 : (∑ i, ((rankBasis F).repr ⟨F v, mem_opRange F v⟩ i) • rankVec F i) = F v := by
    have h3 := congrArg Subtype.val h
    rw [Submodule.coe_sum] at h3
    simpa only [Submodule.coe_smul, rankVec] using h3
  rw [← h2]
  rfl

/-- The matrix `(φ_j(R e_k))` of the finite-rank part `R F`. -/
def rankMatrix (R : E →L[ℂ] E) : Matrix (RankIndex F) (RankIndex F) ℂ :=
  Matrix.of fun j k => rankCoord F j (R (rankVec F k))

theorem mul_apply_eq_sum (R : E →L[ℂ] E) (x : E) :
    (R * F) x = ∑ i, rankCoord F i x • R (rankVec F i) := by
  show R (F x) = _
  rw [apply_eq_sum_rankCoord F x, map_sum]
  simp [map_smul]

theorem rankCoord_mul_sum (R : E →L[ℂ] E) (c : RankIndex F → ℂ) (j : RankIndex F) :
    rankCoord F j (∑ i, c i • R (rankVec F i)) = (rankMatrix F R *ᵥ c) j := by
  simp [map_sum, map_smul, rankMatrix, Matrix.mulVec, dotProduct, mul_comm]

theorem mul_sum_eq (R : E →L[ℂ] E) (c : RankIndex F → ℂ) :
    (R * F) (∑ i, c i • R (rankVec F i)) = ∑ k, (rankMatrix F R *ᵥ c) k • R (rankVec F k) := by
  rw [mul_apply_eq_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [rankCoord_mul_sum]

/-- **`1 − R F` is invertible when the finite determinant is nonzero.** -/
theorem isUnit_one_sub_mul_of_det_ne_zero [CompleteSpace E] (R : E →L[ℂ] E)
    (h : (1 - rankMatrix F R).det ≠ 0) : IsUnit (1 - R * F) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  set M := rankMatrix F R
  have hu : IsUnit (1 - M).det := isUnit_iff_ne_zero.mpr h
  have hNM : (1 - M)⁻¹ * (1 - M) = 1 := Matrix.nonsing_inv_mul _ hu
  have hMN : (1 - M) * (1 - M)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  constructor
  · refine (injective_iff_map_eq_zero (1 - R * F)).mpr fun z hz => ?_
    have hz' : z - (R * F) z = 0 := hz
    have hzK : (R * F) z = z := (sub_eq_zero.mp hz').symm
    set c : RankIndex F → ℂ := fun i => rankCoord F i z
    have hc : (1 - M) *ᵥ c = 0 := by
      ext j
      have hj := congrArg (rankCoord F j) hzK
      rw [mul_apply_eq_sum, rankCoord_mul_sum] at hj
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply]
      rw [hj, sub_self]
    have hc0 : c = 0 := by
      have := congrArg (fun v => (1 - M)⁻¹ *ᵥ v) hc
      simpa [Matrix.mulVec_mulVec, hNM] using this
    rw [← hzK, mul_apply_eq_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : rankCoord F i z = 0 := congrFun hc0 i
    rw [this, zero_smul]
  · intro y
    set φy : RankIndex F → ℂ := fun i => rankCoord F i y
    set d : RankIndex F → ℂ := (1 - M)⁻¹ *ᵥ φy
    refine ⟨y + ∑ i, d i • R (rankVec F i), ?_⟩
    have hd : (1 - M) *ᵥ d = φy := by simp [d, Matrix.mulVec_mulVec, hMN]
    have hdk : ∀ k, d k - (M *ᵥ d) k = φy k := fun k => by
      have := congrFun hd k
      simpa [Matrix.sub_mulVec] using this
    show (y + ∑ i, d i • R (rankVec F i)) - (R * F) (y + ∑ i, d i • R (rankVec F i)) = y
    rw [map_add, mul_sum_eq, mul_apply_eq_sum]
    have hsum : ∑ i, d i • R (rankVec F i) - (∑ i, rankCoord F i y • R (rankVec F i)
        + ∑ k, (M *ᵥ d) k • R (rankVec F k)) = 0 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [← add_smul, ← sub_smul]
      have : d k - (rankCoord F k y + (M *ᵥ d) k) = 0 := by
        have := hdk k; simp only [φy] at this; linear_combination this
      rw [this, zero_smul]
    rw [show y + ∑ i, d i • R (rankVec F i) - (∑ i, rankCoord F i y • R (rankVec F i)
        + ∑ k, (M *ᵥ d) k • R (rankVec F k)) = y + (∑ i, d i • R (rankVec F i) -
        (∑ i, rankCoord F i y • R (rankVec F i) + ∑ k, (M *ᵥ d) k • R (rankVec F k))) by abel,
      hsum, add_zero]

/-- **A vanishing finite determinant produces a nonzero fixed point of `R F`.** -/
theorem exists_fixedPoint_of_det_eq_zero (R : E →L[ℂ] E) (h : (1 - rankMatrix F R).det = 0) :
    ∃ x : E, x ≠ 0 ∧ (R * F) x = x := by
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hMc : rankMatrix F R *ᵥ c = c := by
    have := hc
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    exact this.symm
  refine ⟨∑ i, c i • R (rankVec F i), fun hx => hc0 ?_, ?_⟩
  · funext j
    have := rankCoord_mul_sum F R c j
    rw [hx, map_zero, hMc] at this
    exact this.symm
  · rw [mul_sum_eq, hMc]

end FiniteRankFactor

/-! ## The spectral circle -/

/-- **Between any two radii above `‖S‖^{1/N}` there is a circle in the resolvent set.** -/
theorem exists_sphere_subset_resolventSet_of_pow_eq_add [CompleteSpace E] (T : E →L[ℂ] E)
    {N : ℕ} (hN : 1 ≤ N)
    (F S : E →L[ℂ] E) [FiniteDimensional ℂ (opRange F)] (hTFS : T ^ N = F + S)
    {a b : ℝ} (ha0 : 0 < a) (hS : ‖S‖ < a ^ N) (hab : a < b) :
    ∃ ρ ∈ Set.Ioo a b, ∀ z ∈ sphere (0 : ℂ) ρ, z ∈ resolventSet ℂ T := by
  set U : Set ℂ := {w | ‖S‖ < ‖w‖}
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hUc : IsPreconnected U := isPreconnected_norm_gt (norm_nonneg S)
  have hUres : ∀ w ∈ U, w ∈ resolventSet ℂ S := fun w hw =>
    spectrum.mem_resolventSet_of_norm_lt_mul (lt_of_le_of_lt
      (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le) hw)
  set D : ℂ → ℂ := fun w => (1 - rankMatrix F (resolvent S w)).det
  -- the determinant is holomorphic on `U`
  have hentry : ∀ j k, DifferentiableOn ℂ (fun w => rankMatrix F (resolvent S w) j k) U := by
    intro j k w hw
    have hR : DifferentiableAt ℂ (resolvent S) w :=
      (spectrum.hasDerivAt_resolvent_const_left (hUres w hw)).differentiableAt
    have hL : DifferentiableAt ℂ (fun w => (rankCoord F j).comp
        (ContinuousLinearMap.apply ℂ E (rankVec F k)) (resolvent S w)) w :=
      ((rankCoord F j).comp (ContinuousLinearMap.apply ℂ E (rankVec F k))).differentiableAt.comp
        w hR
    exact hL.differentiableWithinAt
  have hD : DifferentiableOn ℂ D U := by
    have hrw : D = fun w => ∑ σ : Equiv.Perm (RankIndex F), (Equiv.Perm.sign σ : ℂ) *
        ∏ i, ((if σ i = i then (1 : ℂ) else 0) - rankMatrix F (resolvent S w) (σ i) i) := by
      funext w
      simp only [D]
      rw [Matrix.det_apply']
      refine Finset.sum_congr rfl fun σ _ => congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
      simp [Matrix.one_apply]
    rw [hrw]
    refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.mul (differentiableOn_const _) ?_
    exact DifferentiableOn.fun_finsetProd fun i _ =>
      (differentiableOn_const _).sub (hentry (σ i) i)
  -- the determinant is nonzero somewhere in `U`
  have hw0 : ∃ w₀ ∈ U, D w₀ ≠ 0 := by
    have hev : ∀ᶠ w in Bornology.cobounded ℂ,
        ‖resolvent S w‖ < (‖F‖ + 1)⁻¹ ∧ ‖S‖ < ‖w‖ := by
      refine (spectrum.resolvent_tendsto_cobounded S |>.norm.eventually
        (gt_mem_nhds (by rw [norm_zero]; positivity))).and ?_
      exact tendsto_norm_cobounded_atTop.eventually_gt_atTop _
    obtain ⟨w₀, hR0, hw0U⟩ := hev.exists
    refine ⟨w₀, hw0U, fun hD0 => ?_⟩
    obtain ⟨x, hx0, hx⟩ := exists_fixedPoint_of_det_eq_zero F (resolvent S w₀) hD0
    have hle : ‖x‖ ≤ ‖resolvent S w₀‖ * ‖F‖ * ‖x‖ := by
      calc ‖x‖ = ‖(resolvent S w₀ * F) x‖ := by rw [hx]
        _ = ‖resolvent S w₀ (F x)‖ := rfl
        _ ≤ ‖resolvent S w₀‖ * ‖F x‖ := (resolvent S w₀).le_opNorm _
        _ ≤ ‖resolvent S w₀‖ * (‖F‖ * ‖x‖) :=
            mul_le_mul_of_nonneg_left (F.le_opNorm x) (norm_nonneg _)
        _ = ‖resolvent S w₀‖ * ‖F‖ * ‖x‖ := by ring
    have hsmall : ‖resolvent S w₀‖ * ‖F‖ < 1 := by
      calc ‖resolvent S w₀‖ * ‖F‖ ≤ (‖F‖ + 1)⁻¹ * ‖F‖ :=
            mul_le_mul_of_nonneg_right hR0.le (norm_nonneg _)
        _ < 1 := by rw [inv_mul_lt_iff₀ (by positivity)]; linarith
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    nlinarith
  -- finitely many zeros in the compact annulus
  set K : Set ℂ := closedBall 0 (b ^ N) ∩ (ball 0 (a ^ N))ᶜ
  have hK : IsCompact K := (isCompact_closedBall 0 _).inter_right isOpen_ball.isClosed_compl
  have hKU : K ⊆ U := by
    intro w hw
    have h2 : a ^ N ≤ ‖w‖ := by
      have := hw.2; rw [Set.mem_compl_iff, mem_ball_zero_iff, not_lt] at this; exact this
    exact lt_of_lt_of_le hS h2
  have hfin : {w | w ∈ K ∧ D w = 0}.Finite := by
    by_contra hinf
    obtain ⟨x, hxK, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hK
      (fun w hw => hw.1)
    have hfreq : ∃ᶠ w in 𝓝[≠] x, D w = 0 := by
      rw [frequently_nhdsWithin_iff]
      exact (accPt_iff_frequently.mp hacc).mono fun w hw => ⟨hw.2.2, hw.1⟩
    have hzero := (hD.analyticOnNhd hUo).eqOn_zero_of_preconnected_of_frequently_eq_zero hUc
      (hKU hxK) hfreq
    obtain ⟨w₀, hw₀U, hD0⟩ := hw0
    exact hD0 (hzero hw₀U)
  -- spectral points of `T` in the annulus give zeros of `D`
  have hspec : ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → z ∉ resolventSet ℂ T →
      z ^ N ∈ {w | w ∈ K ∧ D w = 0} := by
    intro z hza hzb hzT
    have hzN : ‖z ^ N‖ = ‖z‖ ^ N := norm_pow z N
    have hKz : z ^ N ∈ K := by
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall_zero_iff, hzN]; exact pow_le_pow_left₀ (norm_nonneg _) hzb N
      · rw [Set.mem_compl_iff, mem_ball_zero_iff, not_lt, hzN]
        exact pow_le_pow_left₀ ha0.le hza N
    refine ⟨hKz, ?_⟩
    by_contra hD0
    apply hzT
    set w := z ^ N
    have hwS : w ∈ resolventSet ℂ S := hUres w (hKU hKz)
    have hunit1 : IsUnit (algebraMap ℂ (E →L[ℂ] E) w - S) := hwS
    have hunit2 : IsUnit (1 - resolvent S w * F) := isUnit_one_sub_mul_of_det_ne_zero F _ hD0
    have hfac : algebraMap ℂ (E →L[ℂ] E) w - T ^ N
        = (algebraMap ℂ (E →L[ℂ] E) w - S) * (1 - resolvent S w * F) := by
      rw [mul_sub, mul_one, ← mul_assoc, sub_mul_resolvent hwS, one_mul, hTFS]
      abel
    have hunitN : IsUnit (algebraMap ℂ (E →L[ℂ] E) w - T ^ N) := by
      rw [hfac]; exact hunit1.mul hunit2
    set x := algebraMap ℂ (E →L[ℂ] E) z
    have hc : Commute x T := Algebra.commutes z T
    set G := ∑ i ∈ Finset.range N, x ^ i * T ^ (N - 1 - i)
    have hxN : algebraMap ℂ (E →L[ℂ] E) w = x ^ N := by simp [w, x, map_pow]
    have hleft : (x - T) * G = x ^ N - T ^ N := hc.mul_geom_sum₂ N
    have hright : G * (x - T) = x ^ N - T ^ N := hc.geom_sum₂_mul N
    have hcomm : Commute (x - T) G := hleft.trans hright.symm
    rw [hxN, ← hleft] at hunitN
    exact (hcomm.isUnit_mul_iff.mp hunitN).1
  -- choose a radius avoiding the finitely many moduli
  set bad : Set ℝ := (fun w : ℂ => ‖w‖ ^ ((N : ℝ)⁻¹)) '' {w | w ∈ K ∧ D w = 0}
  have hbad : bad.Finite := hfin.image _
  obtain ⟨ρ, hρ, hρbad⟩ := ((Set.Ioo_infinite hab).sdiff hbad).nonempty
  refine ⟨ρ, hρ, fun z hz => ?_⟩
  by_contra hzT
  have hzρ : ‖z‖ = ρ := mem_sphere_zero_iff_norm.mp hz
  have hmem := hspec z (by rw [hzρ]; exact hρ.1.le) (by rw [hzρ]; exact hρ.2.le) hzT
  apply hρbad
  refine ⟨z ^ N, hmem, ?_⟩
  show ‖z ^ N‖ ^ ((N : ℝ)⁻¹) = ρ
  rw [norm_pow, hzρ, Real.pow_rpow_inv_natCast (lt_trans ha0 hρ.1).le (by omega)]

end

end GaloisForLFunctions.HTGeometry

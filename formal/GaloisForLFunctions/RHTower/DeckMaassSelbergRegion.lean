import GaloisForLFunctions.RHTower.DeckMaassSelbergBounds
import GaloisForLFunctions.RHTower.SelbergPoincarePairing
import GaloisForLFunctions.RHTower.SelbergMaassSelbergSlab
import GaloisForLFunctions.RHTower.EisensteinMaassSelbergCuspIntegrals

/-!
# The deck Maass–Selberg relation in the region of absolute convergence

For `N ≥ 2`, `v, w ∈ V_∞`, `1 < Re u' < Re u` and `Y ≥ 1`, with the bilinear deck pairing,

`∫_𝒟 ⟨Λ^Y Ẽ(·, u; v), Λ^Y Ẽ(·, u'; w)⟩_β dμ =
   ⟨v, w⟩ Y^{u+u'-1}/(u+u'-1) + ⟨v, Φ̃(u')w⟩ Y^{u-u'}/(u-u')
     − ⟨Φ̃(u)v, w⟩ Y^{u'-u}/(u-u') − ⟨Φ̃(u)v, Φ̃(u')w⟩ Y^{1-u-u'}/(u+u'-1)`.

Proof: the constant term of `Ẽ(·, u'; w)` pairs to zero against the truncated series above
height `Y` (both are `T`-fixed pairings with vanishing horocycle mean); the truncated row sum
unfolds to the slab `∫_0^Y y^{u-2} ⟨v, CT_{u'}(y)⟩_β dy`; the subtracted `y^{1-u} Φ̃(u) v` gives the cusp
integral `∫_Y^∞ y^{-1-u} ⟨Φ̃(u) v, CT_{u'}(y)⟩_β dy`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate Pointwise

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-! ## Pairing with sums and horocycle integrals -/

theorem bil_tsum_left {X : gammaSet 1 1 0 → DeckSpace N} (hX : Summable X) (Y : DeckSpace N) :
    bil (∑' p, X p) Y = ∑' p, bil (X p) Y := by
  unfold bil
  have hc : ∀ q : Deck N, (∑' p, X p) q = ∑' p, X p q := fun q =>
    ((EuclideanSpace.proj q : DeckSpace N →L[ℂ] ℂ).map_tsum hX)
  simp_rw [hc, ← tsum_mul_right]
  exact (Summable.tsum_finsetSum fun q _ =>
    ((EuclideanSpace.proj q : DeckSpace N →L[ℂ] ℂ).summable hX).mul_right _).symm

theorem ofComplex_mk_eq_point (x y : ℝ) :
    ofComplex (⟨x, y⟩ : ℂ) = ofComplex (SelbergMaassMean.point x y) := by
  rw [point_eq_mk]

/-- A `1`-periodic continuous function has the same integral over `[-½, ½]`, `[0, 1)` and `0..1`. -/
theorem setIntegral_unitIcc_eq_of_periodic {g : ℝ → ℂ} (hper : Function.Periodic g 1) :
    ∫ x in RHTower.unitIcc, g x = ∫ x in (0 : ℝ)..1, g x := by
  rw [RHTower.unitIcc, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  have h := hper.intervalIntegral_add_eq (-(1 / 2)) 0
  rw [zero_add] at h
  rw [← h]
  norm_num

theorem setIntegral_Ico_eq_intervalIntegral (g : ℝ → ℂ) :
    ∫ x in Ico (0 : ℝ) 1, g x = ∫ x in (0 : ℝ)..1, g x := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ico_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]

/-- For continuous deck-equivariant `G` and `X ∈ V_T`, `x ↦ ⟨X, G(x + iy)⟩_β` has period `1`. -/
theorem periodic_bil {G : ℍ → DeckSpace N} (hGe : deckEquivariant N G) {X : DeckSpace N}
    (hX : deckRho N ModularGroup.T X = X) {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x : ℝ => bil X (G (ofComplex (SelbergMaassMean.point x y)))) 1 := by
  intro x
  have h := apply_ofComplex_point_add_int hGe hy 1 x
  simp only [Int.cast_one] at h
  change bil X (G (ofComplex (SelbergMaassMean.point (x + 1) y))) =
    bil X (G (ofComplex (SelbergMaassMean.point x y)))
  rw [h, bil_deckRho_T_right hX]

theorem continuous_bil_point {G : ℍ → DeckSpace N} (hGc : Continuous G) (X : DeckSpace N) {y : ℝ}
    (hy : 0 < y) : Continuous fun x : ℝ => bil X (G (ofComplex (SelbergMaassMean.point x y))) := by
  unfold bil
  exact continuous_finsetSum _ fun q _ => continuous_const.mul
    ((PiLp.continuous_apply 2 _ q).comp (hGc.comp (MaassFiniteDeckDirichlet.continuous_ofComplex_point hy)))

/-- The horocycle average of `Ẽ(·, u'; w)` against `X ∈ V_T` over `[-½, ½]`. -/
theorem setIntegral_unitIcc_bil_eisVec {u' : ℂ} (hu' : 1 < u'.re) {w : DeckSpace N} (hw : IsCuspVec w)
    {X : DeckSpace N} (hX : deckRho N ModularGroup.T X = X) {y : ℝ} (hy : 0 < y) :
    ∫ x in RHTower.unitIcc, bil X (eisVec u' w (ofComplex (SelbergMaassMean.point x y))) =
      bil X (eisCT u' w y) := by
  rw [setIntegral_unitIcc_eq_of_periodic (periodic_bil (deckEquivariant_eisVec hw.1) hX hy),
    intervalIntegral_bil_eisVec hu' hX hw hy]
  rfl

theorem isCuspVec_T {X : DeckSpace N} (hX : IsCuspVec X) : deckRho N ModularGroup.T X = X := hX.1

theorem eisCT_T {s : ℂ} {v : DeckSpace N} (hv : IsCuspVec v) (y : ℝ) :
    deckRho N ModularGroup.T (eisCT s v y) = eisCT s v y := by
  unfold eisCT
  rw [map_add, map_smul, map_smul, hv.1, (scatVec_isCuspVec hv s).1]

theorem measurable_bil {X : Type*} [MeasurableSpace X] {F G : X → DeckSpace N} (hF : Measurable F)
    (hG : Measurable G) : Measurable fun x => bil (F x) (G x) := by
  unfold bil
  refine Finset.measurable_sum _ fun q _ => ?_
  exact ((PiLp.continuous_apply 2 _ q).measurable.comp hF).mul
    ((PiLp.continuous_apply 2 _ q).measurable.comp hG)

/-! ## The constant term against the truncated series -/

theorem integrableOn_fd_bil_eisTrunc_eisCT (hN : 2 ≤ N) {u u' : ℂ} (hu : 1 < u.re) (hu' : 1 < u'.re)
    (huu : u'.re < u.re)
    {v w : DeckSpace N} (hv : IsCuspVec v) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun z : ℍ => bil (eisTrunc Y u v z) (eisCT u' w z.im)) fd volume := by
  obtain ⟨C, hC, hT⟩ := exists_norm_eisTrunc_le hN hu hv hY
  refine integrableOn_fd_of_norm_le_two
    (measurable_bil (measurable_eisTrunc hN hu hv Y) (measurable_eisCT_im u' w)).aestronglyMeasurable
    (β₁ := 1 - u.re + u'.re) (β₂ := 2 - u.re - u'.re) (C := C * (‖w‖ + ‖scatVec u' w‖))
    (by linarith) (by linarith) fun z hz => ?_
  have hy := z.im_pos
  refine (norm_bil_le _ _).trans ?_
  have h1 := hT z hz
  have h2 := norm_eisCT_le u' w hy
  have e1 : z.im ^ (1 - u.re) * z.im ^ u'.re = z.im ^ (1 - u.re + u'.re) := (Real.rpow_add hy _ _).symm
  have e2 : z.im ^ (1 - u.re) * z.im ^ (1 - u'.re) = z.im ^ (2 - u.re - u'.re) := by
    rw [← Real.rpow_add hy]; ring_nf
  have p1 := Real.rpow_nonneg hy.le (1 - u.re + u'.re)
  have p2 := Real.rpow_nonneg hy.le (2 - u.re - u'.re)
  calc ‖eisTrunc Y u v z‖ * ‖eisCT u' w z.im‖
      ≤ (C * z.im ^ (1 - u.re)) * (‖w‖ * z.im ^ u'.re + ‖scatVec u' w‖ * z.im ^ (1 - u'.re)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hy.le _))
    _ = C * (‖w‖ * z.im ^ (1 - u.re + u'.re) + ‖scatVec u' w‖ * z.im ^ (2 - u.re - u'.re)) := by
        rw [← e1, ← e2]; ring
    _ ≤ C * (‖w‖ + ‖scatVec u' w‖) * (z.im ^ (1 - u.re + u'.re) + z.im ^ (2 - u.re - u'.re)) := by
        have := norm_nonneg w
        have := norm_nonneg (scatVec u' w)
        nlinarith [mul_nonneg hC (mul_nonneg (norm_nonneg w) p2),
          mul_nonneg hC (mul_nonneg (norm_nonneg (scatVec u' w)) p1)]

/-- **The constant term pairs to zero with the truncated series above height `Y`.** -/
theorem integral_fd_above_bil_eisTrunc_eisCT (hN : 2 ≤ N) {u u' : ℂ} (hu : 1 < u.re)
    (hu' : 1 < u'.re) (huu : u'.re < u.re) {v w : DeckSpace N} (hv : IsCuspVec v) (hw : IsCuspVec w) {Y : ℝ}
    (hY : 1 ≤ Y) :
    ∫ z in fd ∩ {z : ℍ | Y < z.im}, bil (eisTrunc Y u v z) (eisCT u' w z.im) = 0 := by
  set F : ℝ × ℝ → ℂ := fun p =>
    bil (eisTrunc Y u v (ofComplex (SelbergMaassMean.point p.1 p.2))) (eisCT u' w p.2) with hFdef
  have hF : ∀ z : ℍ, bil (eisTrunc Y u v z) (eisCT u' w z.im) = F (z.re, z.im) := fun z => by
    simp only [hFdef, SelbergPoincarePairing.ofComplex_point]
  simp_rw [hF]
  have hint : IntegrableOn (fun p : ℝ × ℝ => F p / ((p.2 : ℝ) : ℂ) ^ 2) (RHTower.cuspRect Y) volume := by
    rw [← RHTower.integrableOn_coord_iff (RHTower.measurableSet_cuspRect Y)
      (fun p hp => RHTower.cuspRect_pos (by linarith) hp), RHTower.setOf_coord_cuspRect hY]
    simp_rw [← hF]
    exact (integrableOn_fd_bil_eisTrunc_eisCT hN hu hu' huu hv hY).mono_set inter_subset_left
  rw [RHTower.setIntegral_fd_above_eq hY, RHTower.cuspRect, RHTower.setIntegral_prod_eq_iterated hint]
  refine integral_eq_zero_of_ae ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_))
  have hy0 : 0 < y := by simp only [mem_Ioi] at hy; linarith
  have hYy : Y < y := hy
  have hpt : ∀ x : ℝ, eisTrunc Y u v (ofComplex (SelbergMaassMean.point x y)) =
      eisVec u v (ofComplex (SelbergMaassMean.point x y)) - eisCT u v y := by
    intro x
    have him : (ofComplex (SelbergMaassMean.point x y)).im = y := ofComplex_point_im hy0
    rw [eisTrunc_def, him, if_pos hYy, eisVec_eq_eisExt hN hu hv]
  have hX : deckRho N ModularGroup.T (eisCT u' w y) = eisCT u' w y := eisCT_T hw y
  have hc1 : Continuous fun x : ℝ => bil (eisCT u' w y) (eisVec u v (ofComplex (SelbergMaassMean.point x y))) :=
    continuous_bil_point (continuous_eisVec hu hv.1) _ hy0
  have hi1 : IntegrableOn (fun x : ℝ => bil (eisCT u' w y)
      (eisVec u v (ofComplex (SelbergMaassMean.point x y)))) RHTower.unitIcc volume :=
    hc1.continuousOn.integrableOn_compact isCompact_Icc
  change ∫ x in RHTower.unitIcc, F (x, y) / ((y : ℝ) : ℂ) ^ 2 = 0
  simp only [hFdef, hpt, bil_sub_left]
  rw [integral_div]
  simp_rw [bil_comm _ (eisCT u' w y)]
  rw [integral_sub hi1 (integrableOn_const (by simp [RHTower.unitIcc])),
    setIntegral_unitIcc_bil_eisVec hu hv hX hy0, setIntegral_const]
  simp only [RHTower.unitIcc, Measure.real, Real.volume_Icc]
  norm_num

/-! ## The cusp integral -/

theorem norm_eisVec_bil_bound (hN : 2 ≤ N) {u u' : ℂ} (hu' : 1 < u'.re) {w : DeckSpace N}
    (hw : IsCuspVec w) (X : DeckSpace N) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ fd, ‖(z.im : ℂ) ^ (1 - u) * bil X (eisVec u' w z)‖ ≤
      C * (z.im ^ (2 - u.re - u'.re) + z.im ^ (1 - u.re + u'.re)) := by
  obtain ⟨C, hC, hE⟩ := exists_norm_eisVec_le hN hu' hw
  refine ⟨‖X‖ * C, by positivity, fun z hz => ?_⟩
  have hy := z.im_pos
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.sub_re, Complex.one_re]
  have h1 := (norm_bil_le X (eisVec u' w z)).trans (mul_le_mul_of_nonneg_left (hE z hz) (norm_nonneg X))
  have e1 : z.im ^ (1 - u.re) * z.im ^ (1 - u'.re) = z.im ^ (2 - u.re - u'.re) := by
    rw [← Real.rpow_add hy]; ring_nf
  have e2 : z.im ^ (1 - u.re) * z.im ^ u'.re = z.im ^ (1 - u.re + u'.re) := (Real.rpow_add hy _ _).symm
  have p0 := Real.rpow_nonneg hy.le (1 - u.re)
  calc z.im ^ (1 - u.re) * ‖bil X (eisVec u' w z)‖
      ≤ z.im ^ (1 - u.re) * (‖X‖ * (C * (z.im ^ (1 - u'.re) + z.im ^ u'.re))) :=
        mul_le_mul_of_nonneg_left h1 p0
    _ = ‖X‖ * C * (z.im ^ (1 - u.re) * z.im ^ (1 - u'.re) + z.im ^ (1 - u.re) * z.im ^ u'.re) := by ring
    _ = _ := by rw [e1, e2]

/-- **The cusp integral**: `∫_{𝒟, y > Y} y^{1-u} ⟨Φ̃(u)v, Ẽ(·, u'; w)⟩_β dμ`. -/
theorem integral_fd_above_cusp (hN : 2 ≤ N) {u u' : ℂ} (hu' : 1 < u'.re) (huu : u'.re < u.re) {v w : DeckSpace N} (hv : IsCuspVec v) (hw : IsCuspVec w) {Y : ℝ}
    (hY : 1 ≤ Y) :
    ∫ z in fd ∩ {z : ℍ | Y < z.im}, (z.im : ℂ) ^ (1 - u) * bil (scatVec u v) (eisVec u' w z) =
      bil (scatVec u v) w * (Y : ℂ) ^ (u' - u) / (u - u') +
        bil (scatVec u v) (scatVec u' w) * (Y : ℂ) ^ (1 - u - u') / (u + u' - 1) := by
  have hYpos : 0 < Y := by linarith
  set X := scatVec u v with hXdef
  have hXT : deckRho N ModularGroup.T X = X := (scatVec_isCuspVec hv u).1
  set F : ℝ × ℝ → ℂ := fun p => ((p.2 : ℝ) : ℂ) ^ (1 - u) *
    bil X (eisVec u' w (ofComplex (SelbergMaassMean.point p.1 p.2))) with hFdef
  have hF : ∀ z : ℍ, (z.im : ℂ) ^ (1 - u) * bil X (eisVec u' w z) = F (z.re, z.im) := fun z => by
    simp only [hFdef, SelbergPoincarePairing.ofComplex_point]
  simp_rw [hF]
  have hint : IntegrableOn (fun p : ℝ × ℝ => F p / ((p.2 : ℝ) : ℂ) ^ 2) (RHTower.cuspRect Y) volume := by
    rw [← RHTower.integrableOn_coord_iff (RHTower.measurableSet_cuspRect Y)
      (fun p hp => RHTower.cuspRect_pos (by linarith) hp), RHTower.setOf_coord_cuspRect hY]
    simp_rw [← hF]
    obtain ⟨C, hC, hB⟩ := norm_eisVec_bil_bound hN (u := u) hu' hw X
    have hmeas : Measurable fun z : ℍ => (z.im : ℂ) ^ (1 - u) * bil X (eisVec u' w z) := by
      refine Measurable.mul ?_ (measurable_bil measurable_const (continuous_eisVec hu' hw.1).measurable)
      exact (Complex.continuous_ofReal.comp continuous_im).measurable.pow_const _
    exact (integrableOn_fd_of_norm_le_two hmeas.aestronglyMeasurable (by linarith) (by linarith)
      hB).mono_set inter_subset_left
  rw [RHTower.setIntegral_fd_above_eq hY, RHTower.cuspRect, RHTower.setIntegral_prod_eq_iterated hint]
  have hinner : ∀ y ∈ Ioi Y, (∫ x in RHTower.unitIcc, F (x, y) / ((y : ℝ) : ℂ) ^ 2) =
      bil X w * ((y : ℝ) : ℂ) ^ (u' - u - 1) + bil X (scatVec u' w) * ((y : ℝ) : ℂ) ^ (-u - u') := by
    intro y hy
    have hy0 : 0 < y := by simp only [mem_Ioi] at hy; linarith
    change ∫ x in RHTower.unitIcc, ((y : ℝ) : ℂ) ^ (1 - u) *
      bil X (eisVec u' w (ofComplex (SelbergMaassMean.point x y))) / ((y : ℝ) : ℂ) ^ 2 = _
    simp_rw [mul_div_right_comm]
    rw [integral_const_mul, setIntegral_unitIcc_bil_eisVec hu' hw hXT hy0]
    unfold eisCT
    rw [bil_add_right, bil_smul_right, bil_smul_right]
    have e1 : ((y : ℝ) : ℂ) ^ (1 - u) / ((y : ℝ) : ℂ) ^ 2 * ((y : ℝ) : ℂ) ^ u' =
        ((y : ℝ) : ℂ) ^ (u' - u - 1) := by
      rw [div_mul_eq_mul_div, RHTower.cpow_mul_cpow_div_sq hy0]; congr 1; ring
    have e2 : ((y : ℝ) : ℂ) ^ (1 - u) / ((y : ℝ) : ℂ) ^ 2 * ((y : ℝ) : ℂ) ^ (1 - u') =
        ((y : ℝ) : ℂ) ^ (-u - u') := by
      rw [div_mul_eq_mul_div, RHTower.cpow_mul_cpow_div_sq hy0]; congr 1; ring
    calc ((y : ℝ) : ℂ) ^ (1 - u) / ((y : ℝ) : ℂ) ^ 2 *
          (((y : ℝ) : ℂ) ^ u' * bil X w + ((y : ℝ) : ℂ) ^ (1 - u') * bil X (scatVec u' w))
        = bil X w * (((y : ℝ) : ℂ) ^ (1 - u) / ((y : ℝ) : ℂ) ^ 2 * ((y : ℝ) : ℂ) ^ u') +
          bil X (scatVec u' w) * (((y : ℝ) : ℂ) ^ (1 - u) / ((y : ℝ) : ℂ) ^ 2 *
            ((y : ℝ) : ℂ) ^ (1 - u')) := by ring
      _ = _ := by rw [e1, e2]
  rw [setIntegral_congr_fun measurableSet_Ioi hinner]
  have ha1 : (u' - u - 1).re < -1 := by simp; linarith
  have ha2 : (-u - u').re < -1 := by simp; linarith
  have hi1 : IntegrableOn (fun y : ℝ => bil X w * ((y : ℝ) : ℂ) ^ (u' - u - 1)) (Ioi Y) :=
    (integrableOn_Ioi_cpow_of_lt ha1 hYpos).const_mul _
  have hi2 : IntegrableOn (fun y : ℝ => bil X (scatVec u' w) * ((y : ℝ) : ℂ) ^ (-u - u')) (Ioi Y) :=
    (integrableOn_Ioi_cpow_of_lt ha2 hYpos).const_mul _
  rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul,
    integral_Ioi_cpow_of_lt ha1 hYpos, integral_Ioi_cpow_of_lt ha2 hYpos]
  have huv : u - u' ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have huv1 : u + u' - 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have e3 : u' - u - 1 + 1 = u' - u := by ring
  have e4 : -u - u' + 1 = 1 - u - u' := by ring
  rw [e3, e4]
  have hn1 : u' - u ≠ 0 := by intro h; apply huv; linear_combination -h
  have hn2 : 1 - u - u' ≠ 0 := by intro h; apply huv1; linear_combination -h
  field_simp
  ring

/-! ## The slab integral by unfolding -/

/-- The unfolded integrand `[Im ζ ≤ Y] (Im ζ)^u ⟨v, Ẽ(ζ, u'; w)⟩_β`. -/
def unfoldF (Y : ℝ) (u : ℂ) (v : DeckSpace N) (u' : ℂ) (w : DeckSpace N) (ζ : ℍ) : ℂ :=
  if ζ.im ≤ Y then (ζ.im : ℂ) ^ u * bil v (eisVec u' w ζ) else 0

theorem bil_truncRowTerm {u u' : ℂ} {w : DeckSpace N} (hw : IsCuspVec w) (Y : ℝ) (v : DeckSpace N)
    (p : gammaSet 1 1 0) (z : ℍ) :
    bil (truncRowTerm Y u v p z) (eisVec u' w z) = unfoldF Y u v u' w (gammaSetMatrix p • z) := by
  unfold truncRowTerm unfoldF
  by_cases h : RHTower.rowHeight p z ≤ Y
  · rw [if_pos h, if_pos (show (gammaSetMatrix p • z).im ≤ Y from h), eisTerm, bil_smul_left,
      bil_symm_deckRho_left, ← eisVec_smul hw.1]
  · rw [if_neg h, if_neg (show ¬ (gammaSetMatrix p • z).im ≤ Y from h), bil_zero_left]

theorem unfoldF_T {u u' : ℂ} {v w : DeckSpace N} (hv : IsCuspVec v) (hw : IsCuspVec w) (Y : ℝ) (n : ℤ)
    (ζ : ℍ) : unfoldF Y u v u' w (ModularGroup.T ^ n • ζ) = unfoldF Y u v u' w ζ := by
  unfold unfoldF
  rw [im_T_zpow_smul, eisVec_smul hw.1, bil_deckRho_T_right hv.1]

theorem measurable_unfoldF {u u' : ℂ} (hu' : 1 < u'.re) {w : DeckSpace N} (hw : IsCuspVec w) (Y : ℝ)
    (v : DeckSpace N) : Measurable (unfoldF Y u v u' w) := by
  refine Measurable.ite (measurableSet_le continuous_im.measurable measurable_const) ?_ measurable_const
  exact ((Complex.continuous_ofReal.comp continuous_im).measurable.pow_const _).mul
    (measurable_bil measurable_const (continuous_eisVec hu' hw.1).measurable)

theorem norm_unfoldF_smul_le {u u' : ℂ} {w : DeckSpace N} (hw : IsCuspVec w) (Y : ℝ) (v : DeckSpace N)
    (p : gammaSet 1 1 0) (z : ℍ) :
    ‖unfoldF Y u v u' w (gammaSetMatrix p • z)‖ ≤
      (if RHTower.rowHeight p z ≤ Y then RHTower.rowHeight p z ^ u.re else 0) *
        (‖v‖ * ‖eisVec u' w z‖) := by
  unfold unfoldF
  change ‖if RHTower.rowHeight p z ≤ Y then (RHTower.rowHeight p z : ℂ) ^ u *
    bil v (eisVec u' w (gammaSetMatrix p • z)) else 0‖ ≤ _
  split_ifs
  · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (RHTower.rowHeight_pos p z)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (RHTower.rowHeight_pos p z).le _)
    rw [eisVec_smul hw.1]
    exact (norm_bil_le _ _).trans (le_of_eq (by rw [LinearIsometryEquiv.norm_map]))
  · simp

theorem exists_unfold_majorant (hN : 2 ≤ N) {u u' : ℂ} (hu' : 1 < u'.re) (huu : u'.re < u.re)
    {v w : DeckSpace N} (hw : IsCuspVec w) {Y : ℝ} (hY : 1 ≤ Y) :
    ∃ K, 0 ≤ K ∧ ∀ z ∈ fd, RHTower.realTruncatedRowSum u.re Y z * (‖v‖ * ‖eisVec u' w z‖) ≤
      K * (z.im ^ (2 - u.re - u'.re) + z.im ^ (1 - u.re + u'.re)) := by
  have hu : 1 < u.re := hu'.trans huu
  obtain ⟨C, hC, hR⟩ := exists_realTruncatedRowSum_le hu hY
  obtain ⟨D, hD, hE⟩ := exists_norm_eisVec_le hN hu' hw
  refine ⟨C * ‖v‖ * D, by positivity, fun z hz => ?_⟩
  have hy := z.im_pos
  have e1 : z.im ^ (1 - u.re) * z.im ^ (1 - u'.re) = z.im ^ (2 - u.re - u'.re) := by
    rw [← Real.rpow_add hy]; ring_nf
  have e2 : z.im ^ (1 - u.re) * z.im ^ u'.re = z.im ^ (1 - u.re + u'.re) := (Real.rpow_add hy _ _).symm
  have hnn := RHTower.realTruncatedRowSum_nonneg u.re Y z
  calc RHTower.realTruncatedRowSum u.re Y z * (‖v‖ * ‖eisVec u' w z‖)
      ≤ (C * z.im ^ (1 - u.re)) * (‖v‖ * (D * (z.im ^ (1 - u'.re) + z.im ^ u'.re))) :=
        mul_le_mul (hR z hz) (mul_le_mul_of_nonneg_left (hE z hz) (norm_nonneg v)) (by positivity)
          (mul_nonneg hC (Real.rpow_nonneg hy.le _))
    _ = C * ‖v‖ * D * (z.im ^ (1 - u.re) * z.im ^ (1 - u'.re) + z.im ^ (1 - u.re) * z.im ^ u'.re) := by
        ring
    _ = _ := by rw [e1, e2]

theorem integrableOn_fd_majorant {u u' : ℂ} (hu' : 1 < u'.re) (huu : u'.re < u.re) (K : ℝ) :
    IntegrableOn (fun z : ℍ => K * (z.im ^ (2 - u.re - u'.re) + z.im ^ (1 - u.re + u'.re))) fd volume := by
  have hm : ∀ β : ℝ, β < 1 → IntegrableOn (fun z : ℍ => z.im ^ β) fd volume := fun β hβ => by
    have h : IntegrableOn (fun z : ℍ => ‖((z.im ^ β : ℝ) : ℂ)‖) fd volume :=
      (RHTower.integrableOn_fd_rpow hβ).norm
    refine h.congr_fun (fun z _ => ?_) isClosed_fd.measurableSet
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg z.im_pos.le β)]
  exact ((hm _ (by linarith)).add (hm _ (by linarith))).const_mul K

/-- **The slab integral**: the truncated row sum paired with `Ẽ(·, u'; w)` unfolds to
`∫_0^Y y^{u-2} ⟨v, CT_{u'}(y)⟩_β dy`. -/
theorem integral_fd_truncRowSum_bil (hN : 2 ≤ N) {u u' : ℂ} (hu' : 1 < u'.re) (huu : u'.re < u.re)
    {v w : DeckSpace N} (hv : IsCuspVec v) (hw : IsCuspVec w) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ z in fd, bil ((1 / 2 : ℂ) • ∑' p, truncRowTerm Y u v p z) (eisVec u' w z) =
      bil v w * (Y : ℂ) ^ (u + u' - 1) / (u + u' - 1) +
        bil v (scatVec u' w) * (Y : ℂ) ^ (u - u') / (u - u') := by
  have hu : 1 < u.re := hu'.trans huu
  have hYpos : 0 < Y := by linarith
  obtain ⟨K, hK, hmaj⟩ := exists_unfold_majorant hN hu' huu (v := v) hw hY
  have hsumz : ∀ z, Summable fun p : gammaSet 1 1 0 =>
      (if RHTower.rowHeight p z ≤ Y then RHTower.rowHeight p z ^ u.re else 0) *
        (‖v‖ * ‖eisVec u' w z‖) := fun z =>
    (RHTower.summable_realTruncated_term hu Y z).mul_right _
  have hterm : ∀ p : gammaSet 1 1 0, ∀ z ∈ fd,
      ‖unfoldF Y u v u' w (gammaSetMatrix p • z)‖ ≤
        K * (z.im ^ (2 - u.re - u'.re) + z.im ^ (1 - u.re + u'.re)) := by
    intro p z hz
    refine (norm_unfoldF_smul_le hw Y v p z).trans (le_trans ?_ (hmaj z hz))
    rw [RHTower.realTruncatedRowSum, ← tsum_mul_right]
    exact (hsumz z).le_tsum p fun q _ => mul_nonneg (RHTower.realTruncated_term_nonneg _ _ _ q)
      (by positivity)
  have hmeas : ∀ p : gammaSet 1 1 0, AEStronglyMeasurable
      (fun z => unfoldF Y u v u' w (gammaSetMatrix p • z)) (volume.restrict fd) := fun p =>
    ((measurable_unfoldF hu' hw Y v).comp (continuous_modular_smul _).measurable).aestronglyMeasurable
  have hint : ∀ p : gammaSet 1 1 0, IntegrableOn (fun z => unfoldF Y u v u' w (gammaSetMatrix p • z))
      fd volume := fun p =>
    Integrable.mono' (integrableOn_fd_majorant hu' huu K) (hmeas p)
      ((ae_restrict_iff' isClosed_fd.measurableSet).2 (Eventually.of_forall (hterm p)))
  have hsum : Summable fun p : gammaSet 1 1 0 => ∫ z in fd, ‖unfoldF Y u v u' w (gammaSetMatrix p • z)‖ := by
    refine summable_of_sum_le (fun p => integral_nonneg fun z => norm_nonneg _)
      (c := ∫ z in fd, K * (z.im ^ (2 - u.re - u'.re) + z.im ^ (1 - u.re + u'.re))) fun F => ?_
    rw [← integral_finsetSum F fun p _ => (hint p).norm]
    refine setIntegral_mono_on (integrable_finsetSum F fun p _ => (hint p).norm)
      (integrableOn_fd_majorant hu' huu K) isClosed_fd.measurableSet fun z hz => ?_
    refine le_trans ?_ (hmaj z hz)
    calc ∑ p ∈ F, ‖unfoldF Y u v u' w (gammaSetMatrix p • z)‖
        ≤ ∑ p ∈ F, (if RHTower.rowHeight p z ≤ Y then RHTower.rowHeight p z ^ u.re else 0) *
            (‖v‖ * ‖eisVec u' w z‖) := Finset.sum_le_sum fun p _ => norm_unfoldF_smul_le hw Y v p z
      _ ≤ ∑' p, (if RHTower.rowHeight p z ≤ Y then RHTower.rowHeight p z ^ u.re else 0) *
            (‖v‖ * ‖eisVec u' w z‖) :=
          (hsumz z).sum_le_tsum F fun q _ => mul_nonneg (RHTower.realTruncated_term_nonneg _ _ _ q)
            (by positivity)
      _ = _ := by rw [tsum_mul_right]; rfl
  obtain ⟨hstrip, hunfold⟩ := integral_fd_tsum_eq_two_mul_strip (unfoldF_T hv hw Y) hint hsum
  have hpt : ∀ z, bil ((1 / 2 : ℂ) • ∑' p, truncRowTerm Y u v p z) (eisVec u' w z) =
      (1 / 2 : ℂ) * ∑' p, unfoldF Y u v u' w (gammaSetMatrix p • z) := by
    intro z
    rw [bil_smul_left, bil_tsum_left ((summable_norm_truncRowTerm hu Y v z).of_norm)]
    simp_rw [bil_truncRowTerm hw]
  simp_rw [hpt]
  rw [integral_const_mul, hunfold, ← mul_assoc, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_mul,
    setIntegral_modularStrip_eq_iterated _ hstrip]
  have hinner : ∀ y ∈ Ioi (0 : ℝ), (y ^ 2)⁻¹ • ∫ x in Ico (0 : ℝ) 1, unfoldF Y u v u' w (ofComplex ⟨x, y⟩) =
      (Iic Y).indicator (fun y : ℝ => bil v w * ((y : ℝ) : ℂ) ^ (u + u' - 2) +
        bil v (scatVec u' w) * ((y : ℝ) : ℂ) ^ (u - u' - 1)) y := by
    intro y hy
    have hy0 : 0 < y := hy
    have him : ∀ x : ℝ, (ofComplex (⟨x, y⟩ : ℂ)).im = y := fun x => by
      rw [ofComplex_mk_eq_point]; exact ofComplex_point_im hy0
    have hf : ∀ x : ℝ, unfoldF Y u v u' w (ofComplex ⟨x, y⟩) = if y ≤ Y then
        ((y : ℝ) : ℂ) ^ u * bil v (eisVec u' w (ofComplex (SelbergMaassMean.point x y))) else 0 := by
      intro x
      unfold unfoldF
      rw [him x, ofComplex_mk_eq_point]
    simp_rw [hf]
    by_cases hyY : y ≤ Y
    · rw [Set.indicator_of_mem (show y ∈ Iic Y from hyY)]
      simp only [if_pos hyY]
      rw [integral_const_mul, setIntegral_Ico_eq_intervalIntegral,
        intervalIntegral_bil_eisVec hu' hv.1 hw hy0, bil_add_right, bil_smul_right, bil_smul_right,
        Complex.real_smul]
      have e1 : ((y : ℝ) : ℂ) ^ u * ((y : ℝ) : ℂ) ^ u' / ((y : ℝ) : ℂ) ^ 2 = ((y : ℝ) : ℂ) ^ (u + u' - 2) :=
        RHTower.cpow_mul_cpow_div_sq hy0 u u'
      have e2 : ((y : ℝ) : ℂ) ^ u * ((y : ℝ) : ℂ) ^ (1 - u') / ((y : ℝ) : ℂ) ^ 2 =
          ((y : ℝ) : ℂ) ^ (u - u' - 1) := by
        rw [RHTower.cpow_mul_cpow_div_sq hy0]; congr 1; ring
      push_cast
      rw [← e1, ← e2]
      ring
    · rw [Set.indicator_of_notMem (show y ∉ Iic Y from hyY)]
      simp only [if_neg hyY, integral_zero, smul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, setIntegral_indicator measurableSet_Iic,
    Ioi_inter_Iic]
  have hr1 : -1 < (u + u' - 2).re := by simp; linarith
  have hr2 : -1 < (u - u' - 1).re := by simp; linarith
  have hi : ∀ r : ℂ, -1 < r.re → IntegrableOn (fun y : ℝ => ((y : ℝ) : ℂ) ^ r) (Ioc 0 Y) := fun r hr =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hYpos.le).1
      (intervalIntegral.intervalIntegrable_cpow' hr)
  rw [integral_add ((hi _ hr1).const_mul _) ((hi _ hr2).const_mul _), integral_const_mul,
    integral_const_mul, SelbergMaassSelbergSlab.integral_Ioc_cpow hr1 hYpos,
    SelbergMaassSelbergSlab.integral_Ioc_cpow hr2 hYpos]
  have e3 : u + u' - 2 + 1 = u + u' - 1 := by ring
  have e4 : u - u' - 1 + 1 = u - u' := by ring
  rw [e3, e4]
  ring

/-! ## The Maass–Selberg relation -/

/-- The right side of the deck Maass–Selberg relation. -/
def msRHS (u u' : ℂ) (v w : DeckSpace N) (Y : ℝ) : ℂ :=
  bil v w * (Y : ℂ) ^ (u + u' - 1) / (u + u' - 1) + bil v (scatVec u' w) * (Y : ℂ) ^ (u - u') / (u - u') -
    bil (scatVec u v) w * (Y : ℂ) ^ (u' - u) / (u - u') -
    bil (scatVec u v) (scatVec u' w) * (Y : ℂ) ^ (1 - u - u') / (u + u' - 1)

/-- **The deck Maass–Selberg relation** in the region `1 < Re u' < Re u`, `Y ≥ 1`, `v, w ∈ V_∞`. -/
theorem deckMaassSelberg_region (hN : 2 ≤ N) {u u' : ℂ} (hu' : 1 < u'.re) (huu : u'.re < u.re)
    {v w : DeckSpace N} (hv : IsCuspVec v) (hw : IsCuspVec w) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ z in fd, bil (eisTrunc Y u v z) (eisTrunc Y u' w z) = msRHS u u' v w Y := by
  have hu : 1 < u.re := hu'.trans huu
  have hS : MeasurableSet {z : ℍ | Y < z.im} := measurableSet_lt measurable_const continuous_im.measurable
  -- the truncated series against the full series
  obtain ⟨C, hC, hT⟩ := exists_norm_eisTrunc_le hN hu hv hY
  obtain ⟨D, hD, hE⟩ := exists_norm_eisVec_le hN hu' hw
  have hbnd : ∀ z ∈ fd, ‖bil (eisTrunc Y u v z) (eisVec u' w z)‖ ≤
      C * D * (z.im ^ (2 - u.re - u'.re) + z.im ^ (1 - u.re + u'.re)) := by
    intro z hz
    have hy := z.im_pos
    have e1 : z.im ^ (1 - u.re) * z.im ^ (1 - u'.re) = z.im ^ (2 - u.re - u'.re) := by
      rw [← Real.rpow_add hy]; ring_nf
    have e2 : z.im ^ (1 - u.re) * z.im ^ u'.re = z.im ^ (1 - u.re + u'.re) := (Real.rpow_add hy _ _).symm
    calc ‖bil (eisTrunc Y u v z) (eisVec u' w z)‖ ≤ ‖eisTrunc Y u v z‖ * ‖eisVec u' w z‖ := norm_bil_le _ _
      _ ≤ (C * z.im ^ (1 - u.re)) * (D * (z.im ^ (1 - u'.re) + z.im ^ u'.re)) :=
        mul_le_mul (hT z hz) (hE z hz) (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hy.le _))
      _ = C * D * (z.im ^ (1 - u.re) * z.im ^ (1 - u'.re) + z.im ^ (1 - u.re) * z.im ^ u'.re) := by ring
      _ = _ := by rw [e1, e2]
  have hi1 : IntegrableOn (fun z => bil (eisTrunc Y u v z) (eisVec u' w z)) fd volume :=
    integrableOn_fd_of_norm_le_two (measurable_bil (measurable_eisTrunc hN hu hv Y)
      (continuous_eisVec hu' hw.1).measurable).aestronglyMeasurable (by linarith) (by linarith) hbnd
  have hi2 : IntegrableOn (fun z => {z : ℍ | Y < z.im}.indicator
      (fun z => bil (eisTrunc Y u v z) (eisCT u' w z.im)) z) fd volume :=
    (integrableOn_fd_bil_eisTrunc_eisCT hN hu hu' huu hv hY).indicator hS
  have hsplit : ∀ z, bil (eisTrunc Y u v z) (eisTrunc Y u' w z) =
      bil (eisTrunc Y u v z) (eisVec u' w z) -
        {z : ℍ | Y < z.im}.indicator (fun z => bil (eisTrunc Y u v z) (eisCT u' w z.im)) z := by
    intro z
    rw [eisTrunc_def Y u', ← eisVec_eq_eisExt hN hu' hw, bil_sub_right]
    by_cases h : Y < z.im
    · rw [if_pos h, Set.indicator_of_mem (show z ∈ {z : ℍ | Y < z.im} from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show z ∉ {z : ℍ | Y < z.im} from h), bil_zero_right]
  simp_rw [hsplit]
  rw [integral_sub hi1 hi2, setIntegral_indicator hS,
    integral_fd_above_bil_eisTrunc_eisCT hN hu hu' huu hv hw hY, sub_zero]
  -- the truncated row sum and the subtracted scattering term
  obtain ⟨K, hK, hmaj⟩ := exists_unfold_majorant hN hu' huu (v := v) hw hY
  have hrow : ∀ z ∈ fd, bil (eisTrunc Y u v z) (eisVec u' w z) =
      bil ((1 / 2 : ℂ) • ∑' p, truncRowTerm Y u v p z) (eisVec u' w z) -
        {z : ℍ | Y < z.im}.indicator
          (fun z => (z.im : ℂ) ^ (1 - u) * bil (scatVec u v) (eisVec u' w z)) z := by
    intro z hz
    rw [eisTrunc_eq_truncRowSum hN hu hv hY hz, bil_sub_left]
    by_cases h : Y < z.im
    · rw [if_pos h, Set.indicator_of_mem (show z ∈ {z : ℍ | Y < z.im} from h), bil_smul_left,
        bil_smul_left]
    · rw [if_neg h, Set.indicator_of_notMem (show z ∉ {z : ℍ | Y < z.im} from h), bil_zero_left]
  obtain ⟨B, hB0, hB⟩ := norm_eisVec_bil_bound hN (u := u) hu' hw (scatVec u v)
  have hj2 : IntegrableOn (fun z => {z : ℍ | Y < z.im}.indicator
      (fun z => (z.im : ℂ) ^ (1 - u) * bil (scatVec u v) (eisVec u' w z)) z) fd volume := by
    refine IntegrableOn.indicator ?_ hS
    have hmeas : Measurable fun z : ℍ => (z.im : ℂ) ^ (1 - u) * bil (scatVec u v) (eisVec u' w z) :=
      ((Complex.continuous_ofReal.comp continuous_im).measurable.pow_const _).mul
        (measurable_bil measurable_const (continuous_eisVec hu' hw.1).measurable)
    exact integrableOn_fd_of_norm_le_two hmeas.aestronglyMeasurable (by linarith) (by linarith) hB
  have hj1 : IntegrableOn (fun z => bil ((1 / 2 : ℂ) • ∑' p, truncRowTerm Y u v p z) (eisVec u' w z))
      fd volume := by
    refine (hi1.add hj2).congr_fun (fun z hz => ?_) isClosed_fd.measurableSet
    simp only [Pi.add_apply]
    rw [hrow z hz]
    ring
  rw [setIntegral_congr_fun isClosed_fd.measurableSet hrow, integral_sub hj1 hj2,
    setIntegral_indicator hS, integral_fd_truncRowSum_bil hN hu' huu hv hw hY,
    integral_fd_above_cusp hN hu' huu hv hw hY]
  unfold msRHS
  ring

end

end GaloisForLFunctions.RHTower.DeckPointPair

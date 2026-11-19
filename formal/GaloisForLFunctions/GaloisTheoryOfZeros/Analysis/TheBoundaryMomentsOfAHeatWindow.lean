import GaloisForLFunctions.GaloisTheoryOfZeros.TheLocalDiscriminantOfAHeatCollision
import GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.SharpStripZeroGrowthAndSqrtLowerBound
import GaloisForLFunctions.HTGeometry.SpectralDiscriminantPolynomial
import GaloisForLFunctions.RHTower.RectangleBoundaryPhaseWinding

/-!
# Reading a heat-window discriminant on its spatial boundary

Contour moments of the logarithmic derivative of the actual heat transform
give the power sums of the spatial zeros with multiplicity. Their Hankel
determinant is the squared Vandermonde. Both its dimension and its entries
are determined by the transform on the four edges of the spatial window.
-/

open Complex Set Filter Topology Metric
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
open RHTower GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section

/-- The spatial boundary reading with monomial weight of degree `k`. -/
def heatBoundaryMoment (τ l u : ℂ) (k : ℕ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * RHTower.rectIntegral
    (fun z => z ^ k * logDeriv (complexHeat τ) z) l u

/-- The zeroth moment is an integer on a zero-free boundary. -/
def heatBoundaryDegree (τ l u : ℂ) : ℕ :=
  ⌊(heatBoundaryMoment τ l u 0).re⌋₊

/-- A discriminant defined entirely by spatial contour integrals. -/
def heatBoundaryDiscriminant (τ l u : ℂ) : ℂ :=
  (Matrix.of fun i j : Fin (heatBoundaryDegree τ l u) =>
    heatBoundaryMoment τ l u ((i : ℕ) + (j : ℕ))).det

theorem heatBoundaryMoment_eq_weighted (τ l u : ℂ)
    (hx : l.re ≤ u.re) (hy : l.im ≤ u.im)
    (hb : ∀ t, complexHeat τ (RHTower.rectangleBoundaryPath l u t) ≠ 0) :
    ∃ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔ (l.re < z.re ∧ z.re < u.re ∧ l.im < z.im ∧ z.im < u.im) ∧
        complexHeat τ z = 0) ∧
      ∀ k, heatBoundaryMoment τ l u k =
        ∑ z ∈ Z, (analyticOrderNatAt (complexHeat τ) z : ℂ) * z ^ k := by
  classical
  have hp (k : ℕ) := ConjugateDiagonalGeometry.SzegoCollision.entire_rectIntegral_mul_logDeriv_eq_sum
    (f := complexHeat τ) (g := fun z : ℂ => z ^ k)
    (fun z _ => (differentiable_complexHeat τ).analyticAt z)
    (analyticOrderAt_complexHeat_ne_top τ) (fun _ _ => analyticAt_id.pow _) hx hy hb
  obtain ⟨Z,hZ,_⟩ := hp 0
  refine ⟨Z,hZ,fun k => ?_⟩
  obtain ⟨T,hT,hs⟩ := hp k
  have he : T = Z := Finset.ext fun z => (hT z).trans (hZ z).symm
  simpa only [he, heatBoundaryMoment, analyticOrderNatAt] using hs

/-- On every spatial rectangle with zero-free edges the contour determinant
is the squared Vandermonde of all enclosed zeros, repeated exactly according
to their orders. -/
theorem heatBoundaryDiscriminant_eq_vandermonde (τ l u : ℂ)
    (hx : l.re ≤ u.re) (hy : l.im ≤ u.im)
    (hb : ∀ t, complexHeat τ (RHTower.rectangleBoundaryPath l u t) ≠ 0) :
    ∃ v : Fin (heatBoundaryDegree τ l u) → ℂ,
      (∀ z, (Finset.univ.filter (fun i => v i = z)).card =
        if l.re < z.re ∧ z.re < u.re ∧ l.im < z.im ∧ z.im < u.im
        then analyticOrderNatAt (complexHeat τ) z else 0) ∧
      (∀ k, heatBoundaryMoment τ l u k = ∑ i, v i ^ k) ∧
      heatBoundaryDiscriminant τ l u = (Matrix.vandermonde v).det ^ 2 := by
  classical
  obtain ⟨Z,hZ,hm⟩ := heatBoundaryMoment_eq_weighted τ l u hx hy hb
  let m (z : ℂ) := analyticOrderNatAt (complexHeat τ) z
  let J := (p : Z) × Fin (m p)
  have hJ : Fintype.card J = ∑ z ∈ Z, m z := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin, Finset.sum_coe_sort]
  have h0 : heatBoundaryMoment τ l u 0 = (Fintype.card J : ℂ) := by
    rw [hm, hJ, Nat.cast_sum]
    simp [m]
  have hdeg : heatBoundaryDegree τ l u = Fintype.card J := by
    simp [heatBoundaryDegree, h0]
  let e : Fin (heatBoundaryDegree τ l u) ≃ J := (Fintype.equivFinOfCardEq hdeg.symm).symm
  let v (i : Fin (heatBoundaryDegree τ l u)) : ℂ := ((e i : J).1 : ℂ)
  have hsum (f : ℂ → ℂ) : (∑ i, f (v i)) = ∑ z ∈ Z, (m z : ℂ) * f z := by
    calc
      _ = ∑ j : J, f (j.1 : ℂ) := Fintype.sum_equiv e _ _ fun _ => rfl
      _ = _ := by
        simp [J, Fintype.sum_sigma]
        exact Finset.sum_attach Z (fun z => (m z : ℂ) * f z)
  refine ⟨v, ?_, fun k => (hm k).trans (hsum (· ^ k)).symm, ?_⟩
  · intro z
    have hs := hsum (fun w => if w = z then (1 : ℂ) else 0)
    rw [← Finset.sum_filter] at hs
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hs
    by_cases hz : z ∈ Z
    · rw [if_pos ((hZ z).mp hz).1]
      exact_mod_cast (show ((Finset.univ.filter (fun i => v i = z)).card : ℂ) = (m z : ℂ) by
        simpa [mul_ite, hz] using hs)
    · have hz0 : (Finset.univ.filter (fun i => v i = z)).card = 0 := by
        exact_mod_cast (show ((Finset.univ.filter (fun i => v i = z)).card : ℂ) = 0 by
          simpa [mul_ite, hz] using hs)
      rw [hz0]
      split_ifs with hin
      · have hne : complexHeat τ z ≠ 0 := fun h => hz ((hZ z).mpr ⟨hin,h⟩)
        rw [analyticOrderNatAt, ((differentiable_complexHeat τ).analyticAt z).analyticOrderAt_eq_zero.mpr hne]
        rfl
      · rfl
  · unfold heatBoundaryDiscriminant
    have hentry : ∀ k, heatBoundaryMoment τ l u k = ∑ i, v i ^ k :=
      fun k => (hm k).trans (hsum (· ^ k)).symm
    simp_rw [hentry]
    rw [det_powerSum_hankel, Matrix.det_vandermonde]

/-- A source boundary determinant vanishes exactly at a time when the
spatial window contains an actual collision. -/
theorem heatBoundaryDiscriminant_eq_zero_iff (τ l u : ℂ)
    (hx : l.re ≤ u.re) (hy : l.im ≤ u.im)
    (hb : ∀ t, complexHeat τ (RHTower.rectangleBoundaryPath l u t) ≠ 0) :
    heatBoundaryDiscriminant τ l u = 0 ↔ ∃ z : ℂ,
      (l.re < z.re ∧ z.re < u.re ∧ l.im < z.im ∧ z.im < u.im) ∧
      (τ,z) ∈ multipleZeros := by
  classical
  obtain ⟨v,hv,_,he⟩ := heatBoundaryDiscriminant_eq_vandermonde τ l u hx hy hb
  have hcoll (z : ℂ) : (τ,z) ∈ multipleZeros ↔ 2 ≤ analyticOrderNatAt (complexHeat τ) z := by
    rw [← heatIntersectionMultiplicity_ne_zero_iff, heatIntersectionMultiplicity,
      Nat.choose_ne_zero_iff]
  rw [he, sq_eq_zero_iff, Matrix.det_vandermonde_eq_zero_iff]
  constructor
  · rintro ⟨i,j,hij,hne⟩
    have hc : 1 < (Finset.univ.filter (fun k => v k = v i)).card := by
      by_contra! h
      exact hne (Finset.card_le_one.mp h i (by simp) j (by simp [hij]))
    rw [hv] at hc
    split_ifs at hc with hin
    · exact ⟨v i, hin, (hcoll _).mpr hc⟩
    · omega
  · rintro ⟨z,hin,hc⟩
    have h : 1 < (Finset.univ.filter (fun i => v i = z)).card := by
      rw [hv, if_pos hin]
      exact (hcoll z).mp hc
    obtain ⟨i,hi,j,hj,he⟩ := Finset.one_lt_card.mp h
    exact ⟨i,j,(Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm,he⟩


private def squareLower (z : ℂ) (d : ℝ) : ℂ := ⟨z.re-d,z.im-d⟩
private def squareUpper (z : ℂ) (d : ℝ) : ℂ := ⟨z.re+d,z.im+d⟩
private def inBox (l u w : ℂ) : Prop :=
  l.re < w.re ∧ w.re < u.re ∧ l.im < w.im ∧ w.im < u.im

private theorem inside_of_close {x z : ℂ} {d : ℝ} (h : dist x z < d) :
    inBox (squareLower z d) (squareUpper z d) x := by
  rw [dist_eq_norm] at h
  have hr := abs_lt.mp ((Complex.abs_re_le_norm (x-z)).trans_lt h)
  have hi := abs_lt.mp ((Complex.abs_im_le_norm (x-z)).trans_lt h)
  rw [Complex.sub_re] at hr
  rw [Complex.sub_im] at hi
  change z.re-d < x.re ∧ x.re < z.re+d ∧ z.im-d < x.im ∧ x.im < z.im+d
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem dist_le_of_in_closed_square {x z : ℂ} {d : ℝ}
    (h : x ∈ (Set.Icc (z.re-d) (z.re+d) ×ℂ Set.Icc (z.im-d) (z.im+d))) :
    dist x z ≤ 2*d := by
  obtain ⟨⟨hr,hr'⟩,⟨hi,hi'⟩⟩ := Complex.mem_reProdIm.mp h
  have he : |x.re-z.re| ≤ d := abs_le.mpr ⟨by linarith, by linarith⟩
  have hf : |x.im-z.im| ≤ d := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [dist_eq_norm]
  simpa only [Complex.sub_re, Complex.sub_im, two_mul] using
    (Complex.norm_le_abs_re_add_abs_im (x-z)).trans (add_le_add he hf)

private theorem boundary_not_inside (l u : ℂ) (t : ℝ) :
    ¬inBox l u (RHTower.rectangleBoundaryPath l u t) := by
  unfold RHTower.rectangleBoundaryPath RHTower.rectangleEdgePath inBox
  split_ifs <;> simp

private theorem source_det_of_moments {τ l u : ℂ} {m : ℕ} (v : Fin m → ℂ)
    (hm : ∀ k, heatBoundaryMoment τ l u k = ∑ i, v i ^ k) :
    heatBoundaryDiscriminant τ l u = (Matrix.vandermonde v).det ^ 2 := by
  have hdeg : heatBoundaryDegree τ l u = m := by simp [heatBoundaryDegree, hm 0]
  unfold heatBoundaryDiscriminant
  rw [hdeg]
  simp_rw [hm]
  rw [det_powerSum_hankel, Matrix.det_vandermonde]

private theorem source_moments_of_simple_sheet_list {τ l u : ℂ}
    (hx : l.re ≤ u.re) (hy : l.im ≤ u.im)
    (hb : ∀ t, complexHeat τ (RHTower.rectangleBoundaryPath l u t) ≠ 0)
    {m : ℕ} (v : Fin m → ℂ) (hinj : Function.Injective v)
    (hs : ∀ w, (inBox l u w ∧ complexHeat τ w = 0) ↔ ∃ i, w = v i)
    (hder : ∀ i, deriv (complexHeat τ) (v i) ≠ 0) :
    ∀ k, heatBoundaryMoment τ l u k = ∑ i, v i ^ k := by
  classical
  obtain ⟨Z,hZ,hM⟩ := heatBoundaryMoment_eq_weighted τ l u hx hy hb
  have hz : Z = Finset.univ.image v := by
    ext w
    simpa [Finset.mem_image, eq_comm] using (hZ w).trans (hs w)
  intro k
  rw [hM, hz, Finset.sum_image (fun i _ j _ e => hinj e)]
  apply Finset.sum_congr rfl
  intro i _
  have hzero := ((hs (v i)).mpr ⟨i,rfl⟩).2
  have hord := ((differentiable_complexHeat τ).analyticAt (v i)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    hzero (hder i)
  simp [analyticOrderNatAt, hord]

private theorem card_increasing_pairs (m : ℕ) :
    (∑ i : Fin m, (Finset.Ioi i).card) = m.choose 2 := by
  calc
    _ = ∑ i : Fin m, ((Fin.revPerm i : Fin m) : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Fin.card_Ioi]
      change m - 1 - i.val = m - (i.val + 1)
      omega
    _ = ∑ i : Fin m, (i : ℕ) := Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)
    _ = _ := by rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => k) m, Finset.sum_range_id, Nat.choose_two_right]

/-- On every sufficiently small spatial square, all contour moments are the
power sums of the Hermite sheets throughout a neighborhood of the collision. -/
theorem IsCollision.small_square_sheet_moments {τ z : ℂ} {m : ℕ} (hc : IsCollision τ z m) :
    let e := (profileRoots m).orderIsoOfFin (card_profileRoots m)
    ∃ R > 0, ∀ d : ℝ, 0 < d → d ≤ R → (∀ t, complexHeat τ (RHTower.rectangleBoundaryPath
        ⟨z.re-d,z.im-d⟩ ⟨z.re+d,z.im+d⟩ t) ≠ 0) ∧
      ∀ᶠ s in 𝓝 0, (∀ t, complexHeat (τ+s^2) (RHTower.rectangleBoundaryPath
        ⟨z.re-d,z.im-d⟩ ⟨z.re+d,z.im+d⟩ t) ≠ 0) ∧
        ∀ k, heatBoundaryMoment (τ+s^2) ⟨z.re-d,z.im-d⟩ ⟨z.re+d,z.im+d⟩ k =
          ∑ i : Fin m, (collisionZero τ z m ((e i : ℝ) : ℂ) s)^k := by
  classical
  obtain ⟨r,hr,hiso,hcover⟩ := exists_ball_zeros_eq_sheets hc
  refine ⟨r/4,by positivity,?_⟩
  intro d hd hdr
  let l := squareLower z d
  let u := squareUpper z d
  have hx : l.re ≤ u.re := by change z.re-d ≤ z.re+d; linarith
  have hy : l.im ≤ u.im := by change z.im-d ≤ z.im+d; linarith
  have hins (w : ℂ) (hw : inBox l u w) : w ∈ ball z r := by
    obtain ⟨h₁,h₂,h₃,h₄⟩ := hw
    have h := dist_le_of_in_closed_square (z := z) (d := d) (x := w)
      (Complex.mem_reProdIm.mpr ⟨⟨h₁.le,h₂.le⟩,⟨h₃.le,h₄.le⟩⟩)
    exact mem_ball.mpr (h.trans_lt (by linarith only [hdr,hr]))
  have hbound (t : ℝ) : RHTower.rectangleBoundaryPath l u t ∈ ball z r := by
    have h := RHTower.rectangleBoundaryPath_mem_reProdIm l u hx hy t
    rw [Set.uIcc_of_le hx, Set.uIcc_of_le hy] at h
    exact mem_ball.mpr ((dist_le_of_in_closed_square h).trans_lt (by linarith only [hdr,hr]))
  let e := (profileRoots m).orderIsoOfFin (card_profileRoots m)
  let y (i : Fin m) := collisionBranch τ z m ((e i : ℝ) : ℂ)
  let v (s : ℂ) (i : Fin m) := collisionZero τ z m ((e i : ℝ) : ℂ) s
  have hroot (i : Fin m) := heatModelFwd_profileRoot (e i).property
  have hY (i : Fin m) : AnalyticAt ℂ (y i) 0 := (collisionBranch_spec hc (hroot i)).1
  have hzero (i : Fin m) := complexHeat_collisionZero hc (hroot i)
  have hnear (i : Fin m) : ∀ᶠ s in 𝓝 0, dist (v s i) z < d := by
    have hcont : ContinuousAt (fun s => v s i) 0 :=
      continuousAt_const.add (continuousAt_id.mul (hY i).continuousAt)
    have ht : Tendsto (fun s => v s i) (𝓝 0) (𝓝 z) := by
      simpa [v, collisionZero] using hcont.tendsto
    exact ht.eventually (ball_mem_nhds _ hd)
  have hdiff (i j : Fin m) (hne : i ≠ j) := collisionZero_ne hc (hroot i) (hroot j)
    (fun h => hne (e.injective (Subtype.ext (Complex.ofReal_injective h))))
  have hseparate : ∀ᶠ s in 𝓝[≠] 0, Function.Injective (v s) := by
    have h' (i j : Fin m) : ∀ᶠ s in 𝓝[≠] 0, i ≠ j → v s i ≠ v s j := by
      by_cases h : i = j
      · simp [h]
      · exact (hdiff i j h).mono (fun _ hs _ => hs)
    filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (h' i))] with s hs i j hij
    exact by_contra (fun hn => hs i j hn hij)
  have hzi : inBox l u z := inside_of_close (by simpa using hd)
  have hwb (t : ℝ) (he : complexHeat τ (RHTower.rectangleBoundaryPath l u t) = 0) : False :=
    boundary_not_inside l u t ((hiso _ (hbound t) he).symm ▸ hzi)
  have hbase (k : ℕ) : heatBoundaryMoment τ l u k = ∑ i, v 0 i ^ k := by
    obtain ⟨Z,hZ,hM⟩ := heatBoundaryMoment_eq_weighted τ l u hx hy hwb
    rw [hM, Finset.sum_eq_single z]
    · simp [analyticOrderNatAt,isCollision_iff_analyticOrderAt.mp hc,v,collisionZero]
    · intro w hw hne
      obtain ⟨hin,hzero⟩ := (hZ w).mp hw
      exact (hne (hiso w (hins w hin) hzero)).elim
    · intro hno
      have hm : m = 0 := by
        by_contra h
        exact hno ((hZ z).mpr ⟨hzi,by simpa using hc.vanish 0 (Nat.pos_of_ne_zero h)⟩)
      simp [analyticOrderNatAt,isCollision_iff_analyticOrderAt.mp hc,hm]
  refine ⟨hwb,?_⟩
  rw [eventually_nhdsWithin_iff] at hcover hseparate
  filter_upwards [hcover,hseparate,Filter.eventually_all.mpr hnear,Filter.eventually_all.mpr hzero]
    with s hs hinj hclose hzero'
  by_cases hs0 : s = 0
  · subst s
    simpa only [zero_pow two_ne_zero, add_zero] using And.intro hwb hbase
  have hc' := hs (by simpa using hs0)
  have hlab {w : ℂ} (hw : w ∈ ball z r) (hz : complexHeat (τ+s^2) w = 0) :
      ∃ i, w = v s i := by
    obtain ⟨ρ,hρ,hw'⟩ := (hc'.1 w hw).mp hz
    obtain ⟨q,hq,rfl⟩ := heatModelFwd_eq_zero_iff.mp hρ
    obtain ⟨i,hi⟩ := e.surjective ⟨q,hq⟩
    exact ⟨i,by simpa [v,hi] using hw'⟩
  have hinside (i : Fin m) : inBox l u (v s i) := inside_of_close (hclose i)
  have hb (t : ℝ) (he : complexHeat (τ+s^2) (RHTower.rectangleBoundaryPath l u t) = 0) : False := by
    obtain ⟨i,hi⟩ := hlab (hbound t) he
    exact boundary_not_inside l u t (hi.symm ▸ hinside i)
  have hi (w : ℂ) : inBox l u w ∧ complexHeat (τ+s^2) w = 0 ↔ ∃ i, w = v s i := by
    constructor
    · exact fun h => hlab (hins w h.1) h.2
    · rintro ⟨i,rfl⟩
      exact ⟨hinside i,hzero' i⟩
  exact ⟨hb,source_moments_of_simple_sheet_list hx hy hb (v s) (hinj (by simpa using hs0)) hi
    (fun i => hc'.2.1 _ (hins _ (hinside i)) (hzero' i))⟩


/-- The source determinant in an isolating spatial square, in the time
coordinate `τ+s²`. Its remaining factor is holomorphic and nonzero at zero. -/
private theorem source_sheet_factor {τ z : ℂ} {m : ℕ} (hc : IsCollision τ z m) :
    ∃ d > 0, (∀ t, complexHeat τ (RHTower.rectangleBoundaryPath (squareLower z d) (squareUpper z d) t) ≠ 0) ∧
      ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ U 0 ≠ 0 ∧
      ∀ᶠ s in 𝓝 0, heatBoundaryDiscriminant (τ+s^2) (squareLower z d) (squareUpper z d) =
        (s^2) ^ (m.choose 2) * U s := by
  classical
  obtain ⟨d,hd,hall⟩ := hc.small_square_sheet_moments
  obtain ⟨hwb,hM⟩ := hall d hd le_rfl
  let e := (profileRoots m).orderIsoOfFin (card_profileRoots m)
  let y (i : Fin m) := collisionBranch τ z m ((e i : ℝ) : ℂ)
  let v (s : ℂ) (i : Fin m) := collisionZero τ z m ((e i : ℝ) : ℂ) s
  have hroot (i : Fin m) := heatModelFwd_profileRoot (e i).property
  have hY (i : Fin m) : AnalyticAt ℂ (y i) 0 := (collisionBranch_spec hc (hroot i)).1
  have hy₀ (i : Fin m) : y i 0 = ((e i : ℝ) : ℂ) := (collisionBranch_spec hc (hroot i)).2.1
  let P (s : ℂ) := ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (y j s - y i s)
  have hP : AnalyticAt ℂ P 0 := Finset.analyticAt_fun_prod _ (fun i _ =>
    Finset.analyticAt_fun_prod _ (fun j _ => (hY j).sub (hY i)))
  have hp : P 0 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    rw [hy₀,hy₀]
    exact sub_ne_zero.mpr (fun he => (Finset.mem_Ioi.mp hj).ne'
      (e.injective (Subtype.ext (Complex.ofReal_injective he))))
  have hv (s : ℂ) : (Matrix.vandermonde (v s)).det = s^(m.choose 2) * P s := by
    rw [Matrix.det_vandermonde]
    simp only [v, collisionZero, add_sub_add_left_eq_sub, ← mul_sub, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_pow_eq_pow_sum, card_increasing_pairs, P, y]
  have hfact (s : ℂ) : (Matrix.vandermonde (v s)).det ^ 2 =
      (s ^ 2) ^ (m.choose 2) * (P s)^2 := by
    rw [hv, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (m.choose 2) 2]
  refine ⟨d,hd,hwb,fun s => (P s)^2,hP.pow _,pow_ne_zero _ hp,?_⟩
  filter_upwards [hM] with s hs
  exact (source_det_of_moments (v s) hs.2).trans (hfact s)

/-- At a place of order `m` the boundary moments of an isolating
spatial rectangle give a time discriminant of order `m.choose 2`. Four
further edge integrals in time give this multiplicity using only the
original heat transform on the spatial boundary. -/
theorem IsCollision.boundaryMoment_regular_winding {τ z : ℂ} {m : ℕ}
    (hc : IsCollision τ z m) :
    ∃ l u : ℂ, (l.re < z.re ∧ z.re < u.re ∧ l.im < z.im ∧ z.im < u.im) ∧
      (∀ t, complexHeat τ (RHTower.rectangleBoundaryPath l u t) ≠ 0) ∧
      let D := fun w => heatBoundaryDiscriminant (τ + w) l u
      AnalyticAt ℂ D 0 ∧ analyticOrderAt D 0 = (m.choose 2 : ℕ∞) ∧
      ∃ R > 0, ∀ a b : ℂ, a.re < 0 → 0 < b.re → a.im < 0 → 0 < b.im →
        (uIcc a.re b.re ×ℂ uIcc a.im b.im) ⊆ ball 0 R →
        RHTower.rectIntegral (logDeriv D) a b = 2 * Real.pi * I * (m.choose 2 : ℂ) := by
  obtain ⟨d,hd,hb,U,hU,hu,he⟩ := source_sheet_factor hc
  let D (w : ℂ) := heatBoundaryDiscriminant (τ+w) (squareLower z d) (squareUpper z d)
  have ht : Tendsto (fun s : ℂ => -s) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using (continuous_neg (G := ℂ)).tendsto (0 : ℂ)
  have hev : ∀ᶠ s in 𝓝 0, U (-s) = U s := by
    filter_upwards [he,ht.eventually he] with s hs hn
    by_cases h : s = 0
    · simp [h]
    · simp only [neg_sq] at hn
      exact mul_left_cancel₀ (pow_ne_zero _ (pow_ne_zero _ h)) (hn.symm.trans hs)
  obtain ⟨r,hr,hrb⟩ := Metric.mem_nhds_iff.mp (hU.eventually_analyticAt.and hev)
  obtain ⟨V,hV,hsq⟩ := Bottcher.exists_analytic_factor_of_even hr
    (fun w hw => (hrb hw).1.differentiableAt.differentiableWithinAt) (fun w hw => (hrb hw).2)
  have hV₀ : V 0 = U 0 := by simpa using hsq 0 (mem_ball_self hr)
  have hv : V 0 ≠ 0 := hV₀.symm ▸ hu
  have hVa := hV.analyticAt (isOpen_ball.mem_nhds (mem_ball_self (sq_pos_of_pos hr)))
  have he' : ∀ᶠ s in 𝓝 (0 : ℂ), D (s ^ 2) = (s ^ 2) ^ (m.choose 2) * V (s ^ 2) := by
    filter_upwards [he,ball_mem_nhds (0 : ℂ) hr] with s hs hsb
    rw [hsq s hsb]
    exact hs
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp he'
  have heq : D =ᶠ[𝓝 0] fun w => w ^ (m.choose 2) * V w := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (pow_pos hδ 2)] with w hw
    obtain ⟨s,rfl⟩ := IsAlgClosed.exists_pow_nat_eq w (n := 2) two_pos
    apply hδb
    rw [mem_ball_zero_iff] at hw ⊢
    exact lt_of_pow_lt_pow_left₀ 2 hδ.le (by simpa only [norm_pow] using hw)
  have hD := ((analyticAt_id.pow (m.choose 2)).mul hVa).congr heq.symm
  refine ⟨squareLower z d,squareUpper z d,inside_of_close (by simpa using hd),hb,hD,
    hD.analyticOrderAt_eq_natCast.mpr ⟨V,hVa,hv,heq.mono (fun w hw => by simpa only [sub_zero, smul_eq_mul] using hw)⟩,?_⟩
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp
    (heq.and (hVa.eventually_analyticAt.and (hVa.continuousAt.eventually_ne hv)))
  refine ⟨R,hR,fun a b ha hb hc' hd' hsub => ?_⟩
  have hw := RHTower.rectIntegral_logDeriv_boxCount ({()} : Finset Unit) (fun _ => (0 : ℂ))
    (fun _ => m.choose 2) (f := D) (h := V) isOpen_ball (fun _ _ => ⟨ha,hb,hc',hd'⟩)
    hsub (fun w hw => (hball hw).2.1) (fun w hw => (hball hw).2.2)
    (fun w hw => by simpa using (hball hw).1)
  simpa using hw

/-- The spatial moments recover the order and the argument winding in time. -/
theorem IsCollision.boundaryMoment_winding {τ z : ℂ} {m : ℕ}
    (hc : IsCollision τ z m) :
    ∃ l u : ℂ, (l.re < z.re ∧ z.re < u.re ∧ l.im < z.im ∧ z.im < u.im) ∧
      let D := fun w => heatBoundaryDiscriminant (τ + w) l u
      AnalyticAt ℂ D 0 ∧ analyticOrderAt D 0 = (m.choose 2 : ℕ∞) ∧
      ∃ R > 0, ∀ a b : ℂ, a.re < 0 → 0 < b.re → a.im < 0 → 0 < b.im →
        (uIcc a.re b.re ×ℂ uIcc a.im b.im) ⊆ ball 0 R →
        RHTower.rectIntegral (logDeriv D) a b = 2 * Real.pi * I * (m.choose 2 : ℂ) := by
  obtain ⟨l,u,hin,_,h⟩ := hc.boundaryMoment_regular_winding
  exact ⟨l,u,hin,h⟩

/-- Every marked place of the actual heat family admits a spatial rectangle
whose contour moments recover its local intersection multiplicity. -/
theorem heatIntersectionMultiplicity_from_boundary (τ z : ℂ) :
    ∃ l u : ℂ, (l.re < z.re ∧ z.re < u.re ∧ l.im < z.im ∧ z.im < u.im) ∧
      let D := fun w => heatBoundaryDiscriminant (τ+w) l u
      AnalyticAt ℂ D 0 ∧ analyticOrderAt D 0 = (heatIntersectionMultiplicity (τ,z) : ℕ∞) ∧
      ∃ R > 0, ∀ a b : ℂ, a.re < 0 → 0 < b.re → a.im < 0 → 0 < b.im →
        (uIcc a.re b.re ×ℂ uIcc a.im b.im) ⊆ ball 0 R →
        RHTower.rectIntegral (logDeriv D) a b = 2 * Real.pi * I * (heatIntersectionMultiplicity (τ,z) : ℂ) := by
  have hc := isCollision_iff_analyticOrderAt.mpr
    (Nat.cast_analyticOrderNatAt (analyticOrderAt_complexHeat_ne_top τ z)).symm
  exact hc.boundaryMoment_winding

/-! ## A sheet crossing a height cut -/

/-- Adding a single sheet to a material window multiplies its moment
discriminant by the squared differences from that sheet. -/
theorem vandermonde_square_insert_sheet {n : ℕ} (q : ℂ) (v : Fin n → ℂ) :
    (Matrix.vandermonde (Fin.cons q v)).det ^ 2 =
      (Matrix.vandermonde v).det ^ 2 * ∏ i, (v i-q)^2 := by
  simp only [Matrix.det_vandermonde, Fin.prod_univ_succ (n := n), Fin.prod_Ioi_zero,
    Fin.prod_Ioi_succ, Fin.cons_zero, Fin.cons_succ]
  rw [mul_pow, Finset.prod_pow]
  ring

private def horizontalTrace (F : ℂ → ℂ) (a b h : ℝ) : ℂ :=
  ∫ x in a..b, logDeriv F ((x : ℂ) + h * I)

/-- Upward logarithmic-derivative integral on one vertical edge. -/
def verticalTrace (F : ℂ → ℂ) (x a b : ℝ) : ℂ :=
  ∫ y in a..b, logDeriv F ((x : ℂ) + y * I)

/-- The external edges of two adjacent time rectangles. Each arc uses
the discriminant of the sheets tracked on its side of the height cut. -/
def joinedBoundaryTrace (F G : ℂ → ℂ) (x c y a b : ℝ) : ℂ :=
  (horizontalTrace F x c a + horizontalTrace G c y a) -
    (horizontalTrace F x c b + horizontalTrace G c y b) +
    I * (verticalTrace G y a b - verticalTrace F x a b)

/-- Exact seam term for changing the tracked height window at time `c`.
Both copies of the shared edge cancel whenever the two readings agree. -/
theorem glued_discriminant_trace (F G : ℂ → ℂ) (x c y a b : ℝ) :
    RHTower.rectIntegral (logDeriv F) ⟨x,a⟩ ⟨c,b⟩ +
      RHTower.rectIntegral (logDeriv G) ⟨c,a⟩ ⟨y,b⟩ =
      joinedBoundaryTrace F G x c y a b +
        I * (verticalTrace F c a b - verticalTrace G c a b) := by
  unfold joinedBoundaryTrace RHTower.rectIntegral horizontalTrace verticalTrace
  simp only [smul_eq_mul]
  ring

/-- On a regular seam the correction is the logarithmic derivative of
the transition quotient. It can be integrated using the two edge readings. -/
theorem height_cut_transition (F G : ℂ → ℂ) (x a b : ℝ)
    (h : ∀ y ∈ uIcc a b, let w : ℂ := (x : ℂ) + y * I
      AnalyticAt ℂ F w ∧ F w ≠ 0 ∧ AnalyticAt ℂ G w ∧ G w ≠ 0) :
    verticalTrace F x a b - verticalTrace G x a b =
      ∫ y in a..b, logDeriv (fun w => F w / G w) ((x : ℂ) + y * I) := by
  let p (y : ℝ) : ℂ := (x : ℂ) + y * I
  have hp : Continuous p := by fun_prop
  have hcont (Q : ℂ → ℂ) (hQ : ∀ y ∈ uIcc a b, AnalyticAt ℂ Q (p y) ∧ Q (p y) ≠ 0) :
      ContinuousOn (fun y => logDeriv Q (p y)) (uIcc a b) := by
    intro y hy
    have hv := hQ y hy
    exact ((hv.1.deriv.continuousAt.div hv.1.continuousAt hv.2).comp hp.continuousAt).continuousWithinAt
  have hF : IntervalIntegrable (fun y => logDeriv F (p y)) MeasureTheory.volume a b :=
    (hcont F (fun y hy => ⟨(h y hy).1,(h y hy).2.1⟩)).intervalIntegrable
  have hG : IntervalIntegrable (fun y => logDeriv G (p y)) MeasureTheory.volume a b :=
    (hcont G (fun y hy => (h y hy).2.2)).intervalIntegrable
  unfold verticalTrace
  rw [← intervalIntegral.integral_sub hF hG]
  apply intervalIntegral.integral_congr
  intro y hy
  obtain ⟨hf,hf0,hg,hg0⟩ := h y hy
  exact (logDeriv_div _ hf0 hg0 hf.differentiableAt hg.differentiableAt).symm


/-! ## Thickening a real time interval -/

/-- The complex time rectangle of half-thickness `e` above the real box. -/
def thickenedHeatBox (r e : ℝ) : Set (ℂ × ℂ) :=
  (Icc (1/r) r ×ℂ Icc (-e) e) ×ˢ (Icc (-r) r ×ℂ Icc (-r) r)

/-- A sufficiently thin time contour counts precisely the real-time
collisions in the spatial window, even if complex branch times occur
elsewhere over the same interval of real parts. -/
theorem thin_heatBox_collisions (r : ℝ) :
    ∃ δ > 0, ∀ e : ℝ, 0 ≤ e → e ≤ δ →
      thickenedHeatBox r e ∩ multipleZeros = realTimeHeatBox r ∩ multipleZeros := by
  classical
  have hcomp : IsCompact (thickenedHeatBox r 1) :=
    (isCompact_Icc.reProdIm isCompact_Icc).prod (isCompact_Icc.reProdIm isCompact_Icc)
  obtain ⟨C,hC,_⟩ := compact_heatIntersectionMass _ hcomp
  have hev : ∀ᶠ e : ℝ in 𝓝 0, ∀ p ∈ C, p.1.im ≠ 0 → e < |p.1.im| := by
    rw [Filter.eventually_all_finset]
    intro p _
    by_cases h : p.1.im = 0
    · simp [h]
    · filter_upwards [gt_mem_nhds (abs_pos.mpr h)] with e he
      exact fun _ => he
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp (hev.and (gt_mem_nhds zero_lt_one))
  refine ⟨d/2,by positivity,fun e he he' => ?_⟩
  have he₀ : e ∈ ball (0 : ℝ) d := by
    rw [mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg he]
    linarith
  have he1 := (hball he₀).2
  ext p
  constructor
  · rintro ⟨⟨ht,hw⟩,hp⟩
    obtain ⟨hr,hi⟩ := Complex.mem_reProdIm.mp ht
    have hci : p ∈ C := (hC p).mpr ⟨⟨Complex.mem_reProdIm.mpr
      ⟨hr,⟨(neg_le_neg he1.le).trans hi.1,hi.2.trans he1.le⟩⟩,hw⟩,hp⟩
    have him : p.1.im = 0 := by
      by_contra hn
      exact (not_lt_of_ge (abs_le.mpr hi)) ((hball he₀).1 p hci hn)
    exact ⟨⟨⟨p.1.re,hr,Complex.ext rfl (by simpa using him.symm)⟩,hw⟩,hp⟩
  · rintro ⟨⟨⟨t,ht,heq⟩,hw⟩,hp⟩
    refine ⟨⟨?_,hw⟩,hp⟩
    rw [← heq]
    exact Complex.mem_reProdIm.mpr ⟨ht,⟨neg_nonpos.mpr he,he⟩⟩

/-- A collision-free boundary exhaustion with its exact integer windings.
Every positive thickness used in a given box can be reduced to the supplied
scale without acquiring a nonreal-time collision. -/
theorem exists_real_heat_boundary_windings :
    ∃ (R : ℕ → ℝ) (C : ℕ → Finset (ℂ × ℂ)), StrictMono R ∧
      (⋃ n, realTimeHeatBox (R n)) = {p | ∃ t : ℝ, 0 < t ∧ p.1 = (t : ℂ)} ∧
      (∀ n, ∃ δ > 0, ∀ e : ℝ, 0 < e → e ≤ δ →
        (∀ p, p ∈ C n ↔ p ∈ thickenedHeatBox (R n) e ∧ p ∈ multipleZeros) ∧
        RHTower.rectIntegral (logDeriv (projectedHeatDiscriminant (C n)))
          ⟨1/R n,-e⟩ ⟨R n,e⟩ =
          2 * Real.pi * I * ((∑ p ∈ C n, heatIntersectionMultiplicity p : ℕ) : ℂ)) ∧
      ((∀ n, ∑ p ∈ C n, heatIntersectionMultiplicity p = 0) ↔ RiemannHypothesis) := by
  classical
  obtain ⟨R,hR,_,_,hK,hi,hcover,hRH⟩ := exists_regular_heatBox_exhaustion
  choose C hC hmass using fun n => compact_heatIntersectionMass _ (hK n)
  refine ⟨R,C,hR,hcover,?_,?_⟩
  · intro n
    obtain ⟨δ,hδ,hthin⟩ := thin_heatBox_collisions (R n)
    refine ⟨δ,hδ,fun e he he' => ⟨fun p => ?_,?_⟩⟩
    · change p ∈ C n ↔ p ∈ thickenedHeatBox (R n) e ∩ multipleZeros
      rw [hthin e he.le he']
      exact hC n p
    · have hin (p) (hp : p ∈ C n) := hi n p ((hC n p).mp hp).1 ((hC n p).mp hp).2
      have him (p) (hp : p ∈ C n) : p.1.im = 0 := by
        obtain ⟨t,_,ht⟩ := ((hC n p).mp hp).1.1
        simpa using (congrArg Complex.im ht).symm
      have h := RHTower.rectIntegral_logDeriv_multi_zero (C n) Prod.fst heatIntersectionMultiplicity
        (z₁ := ⟨1/R n,-e⟩) (z₂ := ⟨R n,e⟩) (h := fun _ => (1 : ℂ))
        (fun p hp => ⟨(hin p hp).1,(hin p hp).2.1,
          by rw [him p hp]; exact neg_lt_zero.mpr he,
          by rw [him p hp]; exact he⟩) (Set.subset_univ _)
        (fun _ _ => analyticAt_const) (fun _ _ => one_ne_zero)
      unfold projectedHeatDiscriminant
      simpa using h
  · rw [← hRH]
    apply forall_congr'
    intro n
    rw [hmass n, ← Nat.cast_sum, Nat.cast_eq_zero]


#print axioms thin_heatBox_collisions
#print axioms exists_real_heat_boundary_windings
#print axioms heatBoundaryDiscriminant_eq_vandermonde
#print axioms heatBoundaryDiscriminant_eq_zero_iff
#print axioms IsCollision.boundaryMoment_winding
#print axioms IsCollision.boundaryMoment_regular_winding
#print axioms heatIntersectionMultiplicity_from_boundary
#print axioms vandermonde_square_insert_sheet
#print axioms glued_discriminant_trace
#print axioms height_cut_transition

end

end GaloisForLFunctions.GaloisTheoryOfZeros

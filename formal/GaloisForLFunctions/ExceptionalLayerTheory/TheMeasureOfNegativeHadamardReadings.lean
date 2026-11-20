import GaloisForLFunctions.ExceptionalLayerTheory.TheHeightErrorOfTheHadamardThreshold
import GaloisForLFunctions.RHTower.PrimeLagLandauContinuation

/-!
# Measure of negative Hadamard readings

In a bounded height window only finitely many zero disks can meet a
negative reading. At depth h their vertical chords have length
2√(δ²−h²). Integrating the corresponding rectangles bounds the area
of the entire negative region by a fractional power of the excess
depth above h. A zero strictly in the window forces positive area.
-/

noncomputable section
open Complex Set MeasureTheory Filter Topology Zeta23
open RHTower RHTower.BacklundConverse RHTower.LindelofSparse RHTower.DeBruijn
namespace GaloisForLFunctions.ExceptionalLayerTheory

private abbrev dep (q : XiZeroCopy) := (q.1:ℂ).re-1/2
private abbrev ord (q : XiZeroCopy) := (q.1:ℂ).im
private abbrev rad (q : XiZeroCopy) (h : ℝ) := Real.sqrt (dep q^2-h^2)
private def point (p : ℝ×ℝ) : ℂ := ⟨1/2+p.1,p.2⟩

/-- Zeros whose ordinate and horizontal depth allow a disk to meet the
observed rectangle. Multiplicities are counted. -/
def hadamardShadowZeros (h T : ℝ) : Finset XiZeroCopy := by
  classical
  exact (_root_.RHTower.finite_copies_abs_im_le (T+1/2)).toFinset.filter (fun q => h<dep q)

/-- The negative region in horizontal-depth and ordinate coordinates. -/
def negativeHadamardWindow (h T : ℝ) :=
  {p : ℝ×ℝ | h<p.1 ∧ |p.2|<T ∧ (logDeriv xi (point p)).re<0}

private theorem shadow {p : ℝ×ℝ} {h T : ℝ} (hh : 0≤h) (hp : p∈negativeHadamardWindow h T) :
    ∃ q ∈ hadamardShadowZeros h T, p.1<dep q ∧ |p.2-ord q|<rad q h := by
  obtain ⟨hx,hy,hn⟩ := hp
  have hs : 1/2<(point p).re := by change _<1/2+p.1; linarith only [hh,hx]
  obtain ⟨q,hq,hdisc⟩ := negative_reading_has_deeper_zero hs hn
  change 1/2+p.1 < (q.1:ℂ).re at hq
  change (1/2+p.1-1/2)^2+(p.2-ord q)^2 < dep q^2 at hdisc
  rw [add_sub_cancel_left] at hdisc
  have hxδ : p.1<dep q := by dsimp only [dep]; linarith only [hq]
  have hd0 := hh.trans_lt (hx.trans hxδ)
  have hdist := (sq_lt_sq₀ (abs_nonneg (p.2-ord q)) hd0.le).mp (by rw [sq_abs]; linarith only [hdisc,sq_nonneg p.1])
  have hmax := abs_spectral_im_lt_half q
  rw [spectral_im_eq,abs_sub_comm,abs_of_pos hd0] at hmax
  have hord : |ord q|≤T+1/2 := by
    have htri := abs_add_le (ord q-p.2) p.2
    rw [sub_add_cancel,abs_sub_comm (ord q)] at htri
    linarith only [hy,htri,hdist,hmax]
  have hpos : h^2 < dep q^2 := (sq_lt_sq₀ hh hd0.le).mpr (hx.trans hxδ)
  refine ⟨q,Finset.mem_filter.mpr ⟨Set.Finite.mem_toFinset.mpr hord,hx.trans hxδ⟩,hxδ,?_⟩
  apply (sq_lt_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt (sub_nonneg.mpr hpos.le)]
  linarith only [hdisc,(sq_lt_sq₀ hh (hh.trans hx.le)).mpr hx]

/-- Every negative vertical section in the observation window has
length bounded by the sum of the actual zero-disk chord lengths. -/
theorem negative_hadamard_section_measure {h T x : ℝ} (hh : 0≤h) (hx : h<x) :
    volume {y : ℝ | |y|<T ∧ (logDeriv xi (point (x,y))).re<0} ≤
      ∑ q ∈ hadamardShadowZeros h T, ENNReal.ofReal (2*rad q h) := by
  classical
  let I := fun q : XiZeroCopy => Ioo (ord q-rad q h) (ord q+rad q h)
  have cover : {y : ℝ | |y|<T ∧ (logDeriv xi (point (x,y))).re<0} ⊆
      ⋃ q ∈ hadamardShadowZeros h T, I q := by
    intro y hy
    obtain ⟨q,hq,_,hw⟩ := shadow hh (p:=(x,y)) ⟨hx,hy⟩
    exact mem_iUnion.mpr ⟨q,mem_iUnion.mpr ⟨hq,
      ⟨by linarith only [(abs_lt.mp hw).1],by linarith only [(abs_lt.mp hw).2]⟩⟩⟩
  apply (measure_mono cover).trans ((measure_biUnion_finset_le _ _).trans_eq ?_)
  apply Finset.sum_congr rfl
  intro q _
  rw [I,Real.volume_Ioo,show ord q+rad q h-(ord q-rad q h)=2*rad q h by ring]

/-- The two-dimensional negative area costs at most
2(δ−h)√(δ²−h²) per candidate zero of depth δ. -/
theorem negative_hadamard_window_area {h T : ℝ} (hh : 0≤h) :
    (volume.prod volume) (negativeHadamardWindow h T) ≤
      ∑ q ∈ hadamardShadowZeros h T, ENNReal.ofReal (2*(dep q-h)*rad q h) := by
  classical
  let R := fun q : XiZeroCopy => Ioo h (dep q) ×ˢ Ioo (ord q-rad q h) (ord q+rad q h)
  have cover : negativeHadamardWindow h T ⊆ ⋃ q ∈ hadamardShadowZeros h T, R q := by
    intro p hp
    obtain ⟨q,hq,hx,hw⟩ := shadow hh hp
    exact mem_iUnion.mpr ⟨q,mem_iUnion.mpr ⟨hq,⟨⟨hp.1,hx⟩,
      ⟨by linarith only [(abs_lt.mp hw).1],by linarith only [(abs_lt.mp hw).2]⟩⟩⟩⟩
  apply (measure_mono cover).trans ((measure_biUnion_finset_le _ _).trans_eq ?_)
  apply Finset.sum_congr rfl
  intro q hq
  have hd := (Finset.mem_filter.mp hq).2
  rw [R,Measure.prod_prod,Real.volume_Ioo,Real.volume_Ioo,←ENNReal.ofReal_mul (sub_nonneg.mpr hd.le)]
  congr 1; ring

private theorem negative_open (h T : ℝ) : IsOpen (negativeHadamardWindow h T) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨hx,hy,hn⟩ := hp
  have nz : xi (point p) ≠ 0 := by
    intro hz
    rw [logDeriv_xi_eq_zero_of_xi_eq_zero hz,Complex.zero_re] at hn
    exact lt_irrefl _ hn
  have hpnt : Continuous point := by
    have he : point=(fun p : ℝ×ℝ => ((1/2+p.1:ℝ):ℂ)+(p.2:ℂ)*I) :=
      funext fun p => (Complex.re_add_im (point p)).symm
    rw [he]
    fun_prop
  have ha := xi_differentiable.analyticAt (point p)
  have hc := Complex.continuous_re.continuousAt.comp ((ha.deriv.continuousAt.div ha.continuousAt nz).comp hpnt.continuousAt)
  have hh : ∀ᶠ z : ℝ×ℝ in 𝓝 p, (logDeriv xi (point z)).re < 0 := hc.eventually_lt_const hn
  exact (continuous_fst.continuousAt.eventually_const_lt hx).and
    ((continuous_snd.abs.continuousAt.eventually_lt_const hy).and hh)

/-- A right zero strictly within the observation rectangle forces
positive planar area of negative readings in that same rectangle. -/
theorem zero_forces_positive_hadamard_area {h T : ℝ} (q : XiZeroCopy)
    (hx : h<dep q) (hy : |ord q|<T) :
    0<(volume.prod volume) (negativeHadamardWindow h T) := by
  obtain ⟨u,_,hu,hn⟩ := exists_re_logDeriv_xi_neg_near_zero (xi_xiZeroCopy_eq_zero q) (sub_pos.mpr hx)
  apply (negative_open h T).measure_pos
  let p : ℝ×ℝ := (dep q-u,ord q)
  have eq : point p = (q.1:ℂ)-(u:ℂ) := by
    apply Complex.ext <;> simp [point,p,dep,ord] <;> ring
  refine ⟨p,by change h<dep q-u; linarith only [hu],hy,?_⟩
  rwa [eq]

/-- A zero-free strip above depth h is equivalent to zero
area on cofinally many height windows. Every right zero creates an open
patch which remains in all later windows. -/
theorem right_zeros_iff_negative_area_vanishes {h : ℝ} (hh : 0≤h) :
    (∀ q : XiZeroCopy, dep q ≤ h) ↔
      ∃ᶠ T : ℝ in atTop, (volume.prod volume) (negativeHadamardWindow h T)=0 := by
  classical
  constructor
  · intro hz
    apply Eventually.frequently (Eventually.of_forall ?_)
    intro T
    have hem : hadamardShadowZeros h T=∅ := Finset.filter_eq_empty_iff.mpr
      (fun q _ => not_lt.mpr (hz q))
    exact le_antisymm (by simpa only [hem,Finset.sum_empty] using negative_hadamard_window_area (T:=T) hh) bot_le
  · intro hc q
    by_contra! hq
    obtain ⟨T,hT,hzero⟩ := frequently_atTop.mp hc (|ord q|+1)
    have hp := zero_forces_positive_hadamard_area q hq (by linarith only [hT])
    exact hp.ne' hzero

/-- At a cut ε below a depth ceiling, every remaining disk costs at
most 2ε^(3/2) in negative area. The extra square root comes from the
narrow chord of a disk near its right endpoint. -/
theorem negative_hadamard_area_near_edge {h D T : ℝ} (hh : 0≤h) (hD : h≤D) (hD' : D≤1/2)
    (hzero : ∀ q ∈ hadamardShadowZeros h T, dep q≤D) :
    (volume.prod volume) (negativeHadamardWindow h T) ≤
      (hadamardShadowZeros h T).card • ENNReal.ofReal (2*(D-h)*Real.sqrt (D-h)) := by
  apply (negative_hadamard_window_area hh).trans
  rw [←Finset.sum_const]
  apply Finset.sum_le_sum
  intro q hq
  have hδ := (Finset.mem_filter.mp hq).2
  have hqD := hzero q hq
  have hsum : dep q+h≤1 := by linarith only [hD,hD',hqD]
  have hdiff : dep q^2-h^2≤D-h := by
    calc dep q^2-h^2 = (dep q-h)*(dep q+h) := by ring
         _ ≤ dep q-h := mul_le_of_le_one_right (sub_nonneg.mpr hδ.le) hsum
         _ ≤ D-h := sub_le_sub_right hqD h
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul (mul_le_mul_of_nonneg_left (sub_le_sub_right hqD h) (by norm_num))
    (Real.sqrt_le_sqrt hdiff) (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) (sub_nonneg.mpr hD))

#print axioms right_zeros_iff_negative_area_vanishes
#print axioms negative_hadamard_area_near_edge
#print axioms negative_hadamard_window_area
#print axioms zero_forces_positive_hadamard_area
end GaloisForLFunctions.ExceptionalLayerTheory

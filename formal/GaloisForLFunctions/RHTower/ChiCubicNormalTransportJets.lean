import GaloisForLFunctions.RHTower.ChiCubicPhysicalSliceJets
import GaloisForLFunctions.RHTower.ChiCubicNormalSymbol
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform jets of the complete normalized normal transport

Every iterate of the reciprocal-phase transport applied to the literal
three-slice coupled weight has all derivatives bounded at the moving edge
scale. Constants are uniform in edge width, logarithmic parameter and
reciprocal scale. The mixed second derivative costs one edge derivative
because its reciprocal-scale coefficient is at most the edge width.

This supplies the moving transport producer in the shrinking-cone exterior
argument. Physical conjugation, weighted Fourier estimates and the complete
source attachment remain separate obligations.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

private abbrev E := BAGPhysicalSpace
private abbrev Edge := {r : ℝ // r ∈ Ioo (0 : ℝ) (1/2)}
private abbrev LogParam := {r : ℝ // r ∈ Icc (0 : ℝ) 1}
private abbrev Family := Edge → LogParam → ℝ → E → ℂ
private def box : Set E := {v | ∀ i, v i ∈ Icc (1 : ℝ) 2}
private def upper : Set E := {v | 0 < v 2}
private def direction (i : Fin 3) : E := EuclideanSpace.single i 1
private def coordDeriv (i : Fin 3) (f : E → ℂ) (v : E) : ℂ := fderiv ℝ f v (direction i)
private def Smooth (f : Family) : Prop := ∀ δ h t, ContDiffOn ℝ ∞ (f δ h t) upper
private def Jets (d : ℕ) (f : Family) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ δ h t, |t| ≤ δ.1 → ∀ v ∈ box,
    ‖iteratedFDeriv ℝ n (f δ h t) v‖ ≤ C / δ.1^(n+d)

private theorem upper_open : IsOpen upper := by
  exact isOpen_lt continuous_const (EuclideanSpace.proj (2 : Fin 3)).continuous

private theorem box_upper {v : E} (hv : v ∈ box) : v ∈ upper :=
  lt_of_lt_of_le zero_lt_one (hv 2).1

private theorem fin_le_infty (n : ℕ) : (n : ℕ∞ω) ≤ ∞ := by
  exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)

private theorem smooth_partial {f : Family} (hf : Smooth f) (i : Fin 3) :
    Smooth (fun δ h t => coordDeriv i (f δ h t)) := by
  intro δ h t
  exact ((hf δ h t).fderiv_of_isOpen upper_open (m := ∞) (by simp)).clm_apply contDiffOn_const

private theorem jets_partial {d : ℕ} {f : Family} (hf : Smooth f) (hb : Jets d f)
    (i : Fin 3) : Jets (d+1) (fun δ h t => coordDeriv i (f δ h t)) := by
  intro n
  obtain ⟨C,hC,hbound⟩ := hb (n+1)
  refine ⟨C,hC,fun δ h t ht v hv => ?_⟩
  have hsm := (hf δ h t).contDiffAt (upper_open.mem_nhds (box_upper hv))
  have hd := norm_iteratedFDeriv_clm_apply_const (c := direction i)
    (hsm.fderiv_right (m := ∞) (by simp)) (fin_le_infty n)
  have he : ‖direction i‖ = 1 := by simp [direction]
  simp only [he, one_mul, norm_iteratedFDeriv_fderiv] at hd
  exact hd.trans (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound δ h t ht v hv)

private theorem jets_add {a : ℕ} {f g : Family} (hf : Smooth f) (hg : Smooth g)
    (hfb : Jets a f) (hgb : Jets a g) : Jets a (fun δ h t v => f δ h t v + g δ h t v) := by
  intro n
  obtain ⟨A,hA,hAb⟩ := hfb n
  obtain ⟨B,hB,hBb⟩ := hgb n
  refine ⟨A+B,add_pos hA hB,fun δ h t ht v hv => ?_⟩
  have hfv := ((hf δ h t).contDiffAt (upper_open.mem_nhds (box_upper hv))).of_le (fin_le_infty n)
  have hgv := ((hg δ h t).contDiffAt (upper_open.mem_nhds (box_upper hv))).of_le (fin_le_infty n)
  rw [fun_iteratedFDeriv_add_apply hfv hgv]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (f δ h t) v‖ + ‖iteratedFDeriv ℝ n (g δ h t) v‖ := norm_add_le _ _
    _ ≤ A/δ.1^(n+a) + B/δ.1^(n+a) := add_le_add (hAb δ h t ht v hv) (hBb δ h t ht v hv)
    _ = _ := by ring

private theorem product_jet_le {f g : E → ℂ} (hf : ContDiffOn ℝ ∞ f upper)
    (hg : ContDiffOn ℝ ∞ g upper) (n : ℕ) {v : E} (hv : v ∈ upper) :
    ‖iteratedFDeriv ℝ n (fun x => f x * g x) v‖ ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f v‖ *
        ‖iteratedFDeriv ℝ (n-i) g v‖ := by
  have he (j : ℕ) (F : E → ℂ) : iteratedFDerivWithin ℝ j F upper v = iteratedFDeriv ℝ j F v :=
    iteratedFDerivWithin_of_isOpen j upper_open hv
  simpa only [he] using norm_iteratedFDerivWithin_mul_le hf hg upper_open.uniqueDiffOn hv (fin_le_infty n)

private theorem jets_mul {a b : ℕ} {f g : Family} (hf : Smooth f) (hg : Smooth g)
    (hfb : Jets a f) (hgb : Jets b g) : Jets (a+b) (fun δ h t v => f δ h t v * g δ h t v) := by
  choose A hA hAb using hfb
  choose B hB hBb using hgb
  intro n
  let C := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*A i*B (n-i)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i).le) (hB (n-i)).le)
  refine ⟨C+1,by positivity,fun δ h t ht v hv => ?_⟩
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i (f δ h t) v‖ * ‖iteratedFDeriv ℝ (n-i) (g δ h t) v‖ :=
      product_jet_le (hf δ h t) (hg δ h t) n (box_upper hv)
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*(A i/δ.1^(i+a))*(B (n-i)/δ.1^(n-i+b)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hAb i δ h t ht v hv) (Nat.cast_nonneg _))
        (hBb (n-i) δ h t ht v hv) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (hA i).le (pow_nonneg δ.2.1.le _)))
    _ = C/δ.1^(n+(a+b)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have he : δ.1^(i+a) * δ.1^(n-i+b) = δ.1^(n+(a+b)) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        _ = ((n.choose i : ℝ)*A i*B (n-i))/(δ.1^(i+a)*δ.1^(n-i+b)) := by ring
        _ = _ := by rw [he]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (pow_nonneg δ.2.1.le _)

private theorem jets_smul {d : ℕ} {f : Family} (hf : Smooth f) (hb : Jets d f) (c : ℂ) :
    Jets d (fun δ h t v => c • f δ h t v) := by
  intro n
  obtain ⟨C,hC,hbC⟩ := hb n
  refine ⟨(‖c‖+1)*C,mul_pos (by positivity) hC,fun δ h t ht v hv => ?_⟩
  rw [iteratedFDeriv_const_smul_apply' (((hf δ h t).contDiffAt
    (upper_open.mem_nhds (box_upper hv))).of_le (fin_le_infty n)), norm_smul]
  calc
    _ ≤ ‖c‖*(C/δ.1^(n+d)) := mul_le_mul_of_nonneg_left (hbC δ h t ht v hv) (norm_nonneg c)
    _ ≤ (‖c‖+1)*(C/δ.1^(n+d)) := mul_le_mul_of_nonneg_right (by linarith)
      (div_nonneg hC.le (pow_nonneg δ.2.1.le _))
    _ = _ := by ring

private theorem jets_parameter {d : ℕ} {f : Family} (hf : Smooth f) (hb : Jets (d+1) f) :
    Jets d (fun δ h t v => t • f δ h t v) := by
  intro n
  obtain ⟨C,hC,hbC⟩ := hb n
  refine ⟨C,hC,fun δ h t ht v hv => ?_⟩
  rw [iteratedFDeriv_const_smul_apply' (((hf δ h t).contDiffAt
    (upper_open.mem_nhds (box_upper hv))).of_le (fin_le_infty n)), norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ δ.1*(C/δ.1^(n+(d+1))) :=
      mul_le_mul ht (hbC δ h t ht v hv) (norm_nonneg _) δ.2.1.le
    _ = C/δ.1^(n+d) := by rw [← Nat.add_assoc, pow_succ]; field_simp [δ.2.1.ne']

private theorem box_compact : IsCompact box := by
  have he : box = (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)) ⁻¹'
      (Set.univ.pi (fun _ : Fin 3 => Icc (1 : ℝ) 2)) := by
    ext v
    change (∀ i, v i ∈ Icc (1 : ℝ) 2) ↔
      ∀ i ∈ (Set.univ : Set (Fin 3)), v i ∈ Icc (1 : ℝ) 2
    simp only [Set.mem_univ, forall_const]
  rw [he]
  exact (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi (fun _ : Fin 3 => isCompact_Icc (a := (1 : ℝ)) (b := 2)))

private theorem jets_fixed (f : E → ℂ) (hf : ContDiffOn ℝ ∞ f upper) :
    Jets 0 (fun _ _ _ => f) := by
  intro n
  have hc : ContinuousOn (iteratedFDeriv ℝ n f) box := by
    intro v hv
    exact ((hf.contDiffAt (upper_open.mem_nhds (box_upper hv))).continuousAt_iteratedFDeriv
      (fin_le_infty n)).continuousWithinAt
  obtain ⟨C,hC⟩ := box_compact.exists_bound_of_continuousOn hc
  refine ⟨max C 0+1,by positivity,fun δ h t ht v hv => ?_⟩
  have hδ : 0 < δ.1 := δ.2.1
  have hp : δ.1^n ≤ 1 := pow_le_one₀ hδ.le (by linarith [δ.2.2])
  calc
    _ ≤ C := hC v hv
    _ ≤ max C 0+1 := by linarith [le_max_left C 0]
    _ ≤ (max C 0+1)/δ.1^(n+0) := by
      rw [Nat.add_zero]
      exact (le_div_iff₀ (pow_pos hδ n)).mpr (mul_le_of_le_one_right (by positivity) hp)

private def sliceFamily (i : Fin 3) : Family :=
  fun δ h _ v => bagCubicNormalizedSlice δ.1 h.1 (v i)

private theorem slice_smooth_all (i : Fin 3) (δ : Edge) (h : LogParam) (t : ℝ) :
    ContDiff ℝ ∞ (sliceFamily i δ h t) :=
  (bagCubicNormalizedSlice_properties δ h).1.comp
    (EuclideanSpace.proj i : E →L[ℝ] ℝ).contDiff

private theorem slice_family_jets (i : Fin 3) : Jets 0 (sliceFamily i) := by
  intro n
  obtain ⟨C,hC,hb⟩ := bagCubicNormalizedSlice_uniform_jets n
  let L : E →L[ℝ] ℝ := EuclideanSpace.proj i
  refine ⟨C*(‖L‖^n+1),mul_pos hC (by positivity),fun δ h t ht v hv => ?_⟩
  have hf : ContDiff ℝ (n : ℕ) (bagCubicNormalizedSlice δ.1 h.1) :=
    (bagCubicNormalizedSlice_properties δ h).1.of_le (fin_le_infty n)
  have he := L.iteratedFDeriv_comp_right hf v le_rfl
  change ‖iteratedFDeriv ℝ n (bagCubicNormalizedSlice δ.1 h.1 ∘ L) v‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (bagCubicNormalizedSlice δ.1 h.1) (L v)‖ * ‖L‖^n := by
      simpa using (iteratedFDeriv ℝ n (bagCubicNormalizedSlice δ.1 h.1) (L v)).norm_compContinuousLinearMap_le
        (fun _ : Fin n => L)
    _ = ‖iteratedDeriv n (bagCubicNormalizedSlice δ.1 h.1) (L v)‖ * ‖L‖^n := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    _ ≤ (C/δ.1^n)*‖L‖^n := mul_le_mul_of_nonneg_right (hb δ h (L v)) (pow_nonneg (norm_nonneg _) _)
    _ ≤ (C/δ.1^n)*(‖L‖^n+1) := mul_le_mul_of_nonneg_left (by linarith)
      (div_nonneg hC.le (pow_nonneg δ.2.1.le _))
    _ = _ := by simp only [Nat.add_zero]; ring

private def conjSliceFamily : Family := fun δ h t v => star (sliceFamily 2 δ h t v)

private theorem conj_slice_smooth (δ : Edge) (h : LogParam) (t : ℝ) :
    ContDiff ℝ ∞ (conjSliceFamily δ h t) :=
  Complex.conjCLE.contDiff.comp (slice_smooth_all 2 δ h t)

private theorem conj_slice_jets : Jets 0 conjSliceFamily := by
  intro n
  obtain ⟨C,hC,hb⟩ := slice_family_jets 2 n
  refine ⟨C,hC,fun δ h t ht v hv => ?_⟩
  have he := (Complex.conjCLE : ℂ →L[ℝ] ℂ).norm_iteratedFDeriv_comp_left
    (x := v) (slice_smooth_all 2 δ h t).contDiffAt (fin_le_infty n)
  simp only [Complex.conjCLE_norm, one_mul] at he
  exact he.trans (hb δ h t ht v hv)

private def geom (v : E) : ℂ := (bagPhysicalHeightWindow (v 0*v 1/v 2) : ℂ)

private theorem geom_smooth : ContDiffOn ℝ ∞ geom upper := by
  intro v hv
  have heval (i : Fin 3) : ContDiffAt ℝ ∞ (fun w : E => w i) v :=
    (EuclideanSpace.proj i : E →L[ℝ] ℝ).contDiff.contDiffAt
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp v
    (bagPhysicalHeightWindow.contDiff.contDiffAt.comp v
      (((heval 0).mul (heval 1)).div (heval 2) (ne_of_gt hv)))).contDiffWithinAt

/-- The literal normalized nonoscillatory weight, including ALL three
Gaussian/logarithmic slices and the coupled height window. -/
def bagCubicNormalizedPhysicalWeight (δ h : ℝ) (v : E) : ℂ :=
  bagCubicNormalizedSlice δ h (v 0) * bagCubicNormalizedSlice δ h (v 1) *
    star (bagCubicNormalizedSlice δ h (v 2)) * (bagPhysicalHeightWindow (v 0*v 1/v 2) : ℂ)

private def weightFamily : Family := fun δ h _ => bagCubicNormalizedPhysicalWeight δ.1 h.1

private theorem weight_smooth : Smooth weightFamily := by
  intro δ h t
  exact (((slice_smooth_all 0 δ h t).contDiffOn.mul
    (slice_smooth_all 1 δ h t).contDiffOn).mul (conj_slice_smooth δ h t).contDiffOn).mul geom_smooth

private theorem weight_jets : Jets 0 weightFamily := by
  have h0 : Smooth (sliceFamily 0) := fun δ h t => (slice_smooth_all 0 δ h t).contDiffOn
  have h1 : Smooth (sliceFamily 1) := fun δ h t => (slice_smooth_all 1 δ h t).contDiffOn
  have h2 : Smooth conjSliceFamily := fun δ h t => (conj_slice_smooth δ h t).contDiffOn
  have hg : Smooth (fun _ _ _ => geom) := fun _ _ _ => geom_smooth
  exact jets_mul (fun δ h t => ((h0 δ h t).mul (h1 δ h t)).mul (h2 δ h t)) hg
    (jets_mul (fun δ h t => (h0 δ h t).mul (h1 δ h t)) h2
      (jets_mul h0 h1 (slice_family_jets 0) (slice_family_jets 1)) conj_slice_jets)
    (jets_fixed geom geom_smooth)

private def ratio (i : Fin 3) (v : E) : ℂ := ((v i/v 2 : ℝ) : ℂ)

private theorem ratio_smooth (i : Fin 3) : ContDiffOn ℝ ∞ (ratio i) upper := by
  intro v hv
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp v
    (((EuclideanSpace.proj i).contDiff.contDiffAt).div
      (EuclideanSpace.proj (2 : Fin 3)).contDiff.contDiffAt (ne_of_gt hv))).contDiffWithinAt

/-- Normal transport after exact positive dilation; t is reciprocal scale. -/
def bagCubicNormalizedTransport (t : ℝ) (f : E → ℂ) (v : E) : ℂ :=
  coordDeriv 2 f v + ratio 0 v * coordDeriv 0 f v + ratio 1 v * coordDeriv 1 f v +
    (-Complex.I/(2*Real.pi : ℂ)) • (t • coordDeriv 0 (coordDeriv 1 f) v)

private theorem transport_smooth {f : Family} (hf : Smooth f) :
    Smooth (fun δ h t => bagCubicNormalizedTransport t (f δ h t)) := by
  intro δ h t
  exact ((((smooth_partial hf 2) δ h t).add ((ratio_smooth 0).mul ((smooth_partial hf 0) δ h t))).add
    ((ratio_smooth 1).mul ((smooth_partial hf 1) δ h t))).add
      (((smooth_partial (smooth_partial hf 1) 0) δ h t).const_smul t |>.const_smul _)

private theorem transport_jets {d : ℕ} {f : Family} (hf : Smooth f) (hb : Jets d f) :
    Jets (d+1) (fun δ h t => bagCubicNormalizedTransport t (f δ h t)) := by
  have hs (i : Fin 3) := smooth_partial hf i
  have hbD (i : Fin 3) := jets_partial hf hb i
  have hs2 := smooth_partial (hs 1) 0
  have hb2 := jets_partial (hs 1) (hbD 1) 0
  have hr (i : Fin 3) : Smooth (fun _ _ _ => ratio i) := fun _ _ _ => ratio_smooth i
  have htS : Smooth (fun δ h t v => t • coordDeriv 0 (coordDeriv 1 (f δ h t)) v) :=
    fun δ h t => (hs2 δ h t).const_smul t
  have htB := jets_smul htS (jets_parameter hs2 hb2) (-Complex.I/(2*Real.pi : ℂ))
  have hrB (i : Fin 3) : Jets (d+1) (fun δ h t v => ratio i v * coordDeriv i (f δ h t) v) := by
    simpa only [Nat.zero_add] using
      jets_mul (hr i) (hs i) (jets_fixed (ratio i) (ratio_smooth i)) (hbD i)
  have hA := jets_add (hs 2) (fun δ h t => (ratio_smooth 0).mul (hs 0 δ h t))
    (hbD 2) (hrB 0)
  have hB := jets_add (fun δ h t => (hs 2 δ h t).add ((ratio_smooth 0).mul (hs 0 δ h t)))
    (fun δ h t => (ratio_smooth 1).mul (hs 1 δ h t)) hA
    (hrB 1)
  exact jets_add (fun δ h t => ((hs 2 δ h t).add ((ratio_smooth 0).mul (hs 0 δ h t))).add
    ((ratio_smooth 1).mul (hs 1 δ h t))) (fun δ h t => (htS δ h t).const_smul _) hB htB

private theorem iterate_data : ∀ j : ℕ,
      Smooth (fun δ h t => (bagCubicNormalizedTransport t)^[j] (weightFamily δ h t)) ∧
      Jets j (fun δ h t => (bagCubicNormalizedTransport t)^[j] (weightFamily δ h t)) := by
  intro j
  induction j with
  | zero => exact ⟨weight_smooth,weight_jets⟩
  | succ j ih =>
    simpa only [Function.iterate_succ_apply'] using
      And.intro (transport_smooth ih.1) (transport_jets ih.1 ih.2)

/-- Every actual transport iterate is smooth where the reciprocal phase is
used. This regularity is produced together with the uniform jet bounds. -/
theorem bagCubicNormalizedTransport_iterate_contDiffOn (k : ℕ)
    (δ : {r : ℝ // r ∈ Ioo (0 : ℝ) (1/2)})
    (h : {r : ℝ // r ∈ Icc (0 : ℝ) 1}) (t : ℝ) :
    ContDiffOn ℝ ∞ ((bagCubicNormalizedTransport t)^[k]
      (bagCubicNormalizedPhysicalWeight δ.1 h.1)) {v : BAGPhysicalSpace | 0 < v 2} :=
  (iterate_data k).1 δ h t

/-- Every normal transport iterate of the ACTUAL coupled weight retains
all jets at the shrinking-edge scale, uniformly in reciprocal curvature.
No derivative, cancellation or source-norm premise is supplied. -/
theorem bagCubicNormalizedTransport_uniform_jets (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : {r : ℝ // r ∈ Ioo (0 : ℝ) (1/2)},
      ∀ h : {r : ℝ // r ∈ Icc (0 : ℝ) 1}, ∀ t : ℝ, |t| ≤ δ.1 →
        ∀ v : BAGPhysicalSpace, (∀ i, v i ∈ Icc (1 : ℝ) 2) →
          ‖iteratedFDeriv ℝ n ((bagCubicNormalizedTransport t)^[k]
            (bagCubicNormalizedPhysicalWeight δ.1 h.1)) v‖ ≤ C/δ.1^(n+k) :=
  (iterate_data k).2 n

end RHTower.BAGTrace

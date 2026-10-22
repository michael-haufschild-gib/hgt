import GaloisForLFunctions.RHTower.ChiRamanujanCubicCompensatedBoundary

/-!
# Complete critical boundary of the connected BAG arithmetic cubic

Exact reflection of all signed sectors, both finite parts, product principal value,
and the intersection mass. The arithmetic prime-coordinate limit is explicitly
identified with the tested kernel. No physical-prime limit exchange is asserted.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace RHTower.BAGTrace

private theorem integral_interval_reflection {f : ℝ → ℂ} (hf : Continuous f) (R : ℝ) :
    (∫ u in -R..R, f u) = ∫ u in (0 : ℝ)..R, f u+f (-u) := by
  have hfneg : Continuous (fun u : ℝ => f (-u)) := hf.comp continuous_neg
  have hadd : (∫ u in (0 : ℝ)..R, f u+f (-u)) =
      (∫ u in (0 : ℝ)..R, f u)+(∫ u in (0 : ℝ)..R, f (-u)) := by
    convert intervalIntegral.integral_add (μ := (volume : Measure ℝ))
      (f := f) (g := fun u : ℝ => f (-u)) (hf.intervalIntegrable (0 : ℝ) R)
      (hfneg.intervalIntegrable (0 : ℝ) R) using 1
  rw [hadd]
  have hn : (∫ u in (0 : ℝ)..R, f (-u)) = ∫ u in -R..0, f u := by
    simpa only [neg_zero] using intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := R) f
  rw [hn,add_comm]
  exact (intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
    (hf.intervalIntegrable _ _)).symm

private theorem integral_box_eq_iterated {G : ℝ × ℝ → ℂ} (hG : Continuous G)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ w : ℝ × ℝ in Icc (a,c) (b,d), G w) =
      ∫ u in a..b, ∫ v in c..d, G (u,v) := by
  have hi : IntegrableOn G (Icc a b ×ˢ Icc c d) (volume.prod volume) := by
    simpa only [Icc_prod_Icc] using hG.integrableOn_Icc
  have h := setIntegral_prod G hi
  simp_rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le hcd] at h
  convert h using 1
  rw [Icc_prod_Icc]
  rfl

private theorem continuous_first_reflection {G : ℝ × ℝ → ℂ} (hG : Continuous G) :
    Continuous (fun w : ℝ × ℝ => G w+G (-w.1,w.2)) := by
  have hs : Continuous (fun w : ℝ × ℝ => (-w.1,w.2)) := by fun_prop
  convert hG.add (hG.comp hs) using 1
  rfl

private theorem continuous_four_reflections {G : ℝ × ℝ → ℂ} (hG : Continuous G) :
    Continuous (fun w : ℝ × ℝ => G w+G (-w.1,w.2)+(G (w.1,-w.2)+G (-w.1,-w.2))) := by
  have h1 : Continuous (fun w : ℝ × ℝ => (-w.1,w.2)) := by fun_prop
  have h2 : Continuous (fun w : ℝ × ℝ => (w.1,-w.2)) := by fun_prop
  have h12 : Continuous (fun w : ℝ × ℝ => (-w.1,-w.2)) := by fun_prop
  convert (hG.add (hG.comp h1)).add ((hG.comp h2).add (hG.comp h12)) using 1
  rfl

private theorem integral_first_reflection {G : ℝ × ℝ → ℂ} (hG : Continuous G)
    {R a b : ℝ} (hR : 0 ≤ R) (hab : a ≤ b) :
    (∫ w : ℝ × ℝ in Icc (-R,a) (R,b), G w) =
      ∫ w : ℝ × ℝ in Icc (0,a) (R,b), G w+G (-w.1,w.2) := by
  rw [integral_box_eq_iterated hG (by linarith) hab,
    integral_box_eq_iterated (continuous_first_reflection hG) hR hab]
  have hc : Continuous (fun u : ℝ => ∫ v in a..b, G (u,v)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun u v : ℝ => G (u,v)) (by convert hG using 1; rfl) a b
  rw [integral_interval_reflection hc R]
  apply intervalIntegral.integral_congr
  intro u hu
  have h1 : Continuous (fun v : ℝ => G (u,v)) := hG.comp (continuous_const.prodMk continuous_id)
  have h2 : Continuous (fun v : ℝ => G (-u,v)) := hG.comp (continuous_const.prodMk continuous_id)
  exact (intervalIntegral.integral_add (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)).symm

private theorem integral_four_reflections {G : ℝ × ℝ → ℂ} (hG : Continuous G)
    {R : ℝ} (hR : 0 ≤ R) :
    (∫ w : ℝ × ℝ in Icc (-R,-R) (R,R), G w) =
      ∫ w : ℝ × ℝ in Icc (0,0) (R,R),
        G w+G (-w.1,w.2)+(G (w.1,-w.2)+G (-w.1,-w.2)) := by
  rw [integral_first_reflection hG hR (by linarith),
    integral_box_eq_iterated (continuous_first_reflection hG) hR (by linarith),
    integral_box_eq_iterated (continuous_four_reflections hG) hR hR]
  apply intervalIntegral.integral_congr
  intro u hu
  have hc : Continuous (fun v : ℝ => G (u,v)+G (-u,v)) :=
    (hG.comp (continuous_const.prodMk continuous_id)).add
      (hG.comp (continuous_const.prodMk continuous_id))
  exact integral_interval_reflection hc R


/-- The literal mixed kernel of the tested complete source, before reflection. -/
def cubicMixedKernel (Φ : ℝ × ℝ → ℂ) (ε : ℝ) (w : ℝ × ℝ) : ℂ :=
  ((w.1 : ℂ)*(w.2 : ℂ)*cubicTestedSource Φ ![1+ε,w.1,w.2]) /
    (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ))

/-- The literal first finite-part kernel, before reflection. -/
def cubicAxisKernel (Φ : ℝ × ℝ → ℂ) (ε : ℝ) (w : ℝ × ℝ) : ℂ :=
  cubicTestedAxisNumerator Φ ![1+ε,w.1,w.2] / ((ε^2+w.1^2 : ℝ) : ℂ)

theorem continuous_cubicMixedKernel {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {ε : ℝ} (hε : 0 < ε) : Continuous (cubicMixedKernel Φ ε) := by
  have hn : Continuous (fun w : ℝ × ℝ =>
      (w.1 : ℂ)*(w.2 : ℂ)*cubicTestedSource Φ ![1+ε,w.1,w.2]) :=
    ((Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_ofReal.comp continuous_snd)).mul
      (continuous_cubicTestedSlice hΦ (by linarith))
  have hd : Continuous (fun w : ℝ × ℝ =>
      (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ))) := by fun_prop
  apply hn.div hd
  intro w
  apply mul_ne_zero
  · exact_mod_cast (ne_of_gt (show 0 < ε^2+w.1^2 by positivity))
  · exact_mod_cast (ne_of_gt (show 0 < ε^2+w.2^2 by positivity))

theorem continuous_cubicAxisKernel {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {ε : ℝ} (hε : 0 < ε) : Continuous (cubicAxisKernel Φ ε) := by
  have hn := continuous_cubicTestedAxisSlice hΦ (σ := 1+ε) (by linarith)
  have hd : Continuous (fun w : ℝ × ℝ => ((ε^2+w.1^2 : ℝ) : ℂ)) := by fun_prop
  exact hn.div hd (fun w => by exact_mod_cast (ne_of_gt (show 0 < ε^2+w.1^2 by positivity)))

theorem cubicMixedKernel_reflections (Φ : ℝ × ℝ → ℂ) (ε : ℝ) (w : ℝ × ℝ) :
    cubicMixedKernel Φ ε w+cubicMixedKernel Φ ε (-w.1,w.2)+
      (cubicMixedKernel Φ ε (w.1,-w.2)+cubicMixedKernel Φ ε (-w.1,-w.2)) =
      ((w.1 : ℂ)*(w.2 : ℂ)*cubicMixedDifference Φ (1+ε) w) /
        (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ)) := by
  dsimp only [cubicMixedKernel,cubicMixedDifference]
  simp only [neg_sq,Complex.ofReal_neg]
  ring

theorem cubicAxisKernel_reflection (Φ : ℝ × ℝ → ℂ) (ε : ℝ) (w : ℝ × ℝ) :
    cubicAxisKernel Φ ε w+cubicAxisKernel Φ ε (-w.1,w.2) =
      cubicAxisDifference Φ (1+ε) w / ((ε^2+w.1^2 : ℝ) : ℂ) := by
  dsimp only [cubicAxisKernel,cubicAxisDifference]
  simp only [neg_sq]
  ring

/-- Reflection accounts for every quadrant of the original signed mixed kernel. -/
theorem integral_cubicMixedKernel_eq_reflected {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    (∫ w : ℝ × ℝ in Icc (-R,-R) (R,R), cubicMixedKernel Φ ε w) =
      ∫ w : ℝ × ℝ in Icc (0,0) (R,R),
        ((w.1 : ℂ)*(w.2 : ℂ)*cubicMixedDifference Φ (1+ε) w) /
          (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ)) := by
  rw [integral_four_reflections (continuous_cubicMixedKernel hΦ hε) hR]
  exact integral_congr_ae (ae_of_all _ fun w => cubicMixedKernel_reflections Φ ε w)

/-- The original full symmetric-box mixed kernel converges to the product PV action. -/
theorem tendsto_integral_cubicMixedKernel {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ in Icc (-R,-R) (R,R), cubicMixedKernel Φ ε w)
      (𝓝[>] 0) (𝓝 (∫ w : ℝ × ℝ in Icc (0,0) (R,R), cubicMixedQuotient Φ 1 w)) := by
  apply (tendsto_integral_literal_cubicMixed hΦ R).congr'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  exact (integral_cubicMixedKernel_eq_reflected hΦ hε hR).symm

/-- Reflection retains the full first finite-part kernel and its contraction subtraction. -/
theorem integral_cubicAxisKernel_eq_reflected {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    (∫ w : ℝ × ℝ in Icc (-R,-R) (R,R), cubicAxisKernel Φ ε w) =
      ∫ w : ℝ × ℝ in Icc (0,-R) (R,R),
        cubicAxisDifference Φ (1+ε) w / ((ε^2+w.1^2 : ℝ) : ℂ) := by
  rw [integral_first_reflection (continuous_cubicAxisKernel hΦ hε) hR (by linarith)]
  exact integral_congr_ae (ae_of_all _ fun w => cubicAxisKernel_reflection Φ ε w)

/-- The original full first finite-part kernel has the critical symmetric boundary action. -/
theorem tendsto_integral_cubicAxisKernel {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ in Icc (-R,-R) (R,R), cubicAxisKernel Φ ε w)
      (𝓝[>] 0) (𝓝 (∫ w : ℝ × ℝ in Icc (0,-R) (R,R), cubicAxisQuotient Φ 1 w)) := by
  apply (tendsto_integral_literal_cubicAxis hΦ R).congr'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  exact (integral_cubicAxisKernel_eq_reflected hΦ hε hR).symm


/-- The second finite part is obtained by exchanging frequency coordinates and the test. -/
def cubicOtherAxisKernel (Φ : ℝ × ℝ → ℂ) (ε : ℝ) (w : ℝ × ℝ) : ℂ :=
  (realCubicSource (1+ε) w.1 w.2-realAxisSource (1+ε) w.2)*Φ w /
    ((ε^2+w.2^2 : ℝ) : ℂ)

private theorem cubicOtherAxisKernel_eq_swap (Φ : ℝ × ℝ → ℂ) (ε : ℝ) (w : ℝ × ℝ) :
    cubicOtherAxisKernel Φ ε w = cubicAxisKernel (fun z => Φ (z.2,z.1)) ε w.swap := by
  dsimp [cubicOtherAxisKernel,cubicAxisKernel,cubicTestedAxisNumerator]
  rw [realCubicSource_swap (1+ε) w.2 w.1]

private theorem continuous_cubicOtherAxisKernel {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {ε : ℝ} (hε : 0 < ε) : Continuous (cubicOtherAxisKernel Φ ε) := by
  have hs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => Φ (z.2,z.1)) :=
    hΦ.comp (contDiff_snd.prodMk contDiff_fst)
  have hc : Continuous (fun w : ℝ × ℝ => w.swap) := by fun_prop
  have h := (continuous_cubicAxisKernel hs hε).comp hc
  simpa only [← cubicOtherAxisKernel_eq_swap,Function.comp_def] using h

private theorem integral_cubicOtherAxisKernel_eq_swap (Φ : ℝ × ℝ → ℂ) (ε R : ℝ) :
    (∫ w : ℝ × ℝ in Icc (-R,-R) (R,R), cubicOtherAxisKernel Φ ε w) =
      ∫ w : ℝ × ℝ in Icc (-R,-R) (R,R), cubicAxisKernel (fun z => Φ (z.2,z.1)) ε w := by
  simp_rw [cubicOtherAxisKernel_eq_swap]
  have h := setIntegral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (Icc (-R) R) (Icc (-R) R) (cubicAxisKernel (fun z => Φ (z.2,z.1)) ε)
  simp only [Icc_prod_Icc] at h
  convert h using 1 <;> rfl

theorem tendsto_integral_cubicOtherAxisKernel {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ in Icc (-R,-R) (R,R), cubicOtherAxisKernel Φ ε w)
      (𝓝[>] 0) (𝓝 (∫ w : ℝ × ℝ in Icc (0,-R) (R,R),
        cubicAxisQuotient (fun z => Φ (z.2,z.1)) 1 w)) := by
  simp_rw [integral_cubicOtherAxisKernel_eq_swap]
  exact tendsto_integral_cubicAxisKernel (hΦ.comp (contDiff_snd.prodMk contDiff_fst)) hR

/-- All literal summands of the complete tested connected trace. -/
def cubicConnectedKernel (Φ : ℝ × ℝ → ℂ) (ε : ℝ) (w : ℝ × ℝ) : ℂ :=
  cubicAxisKernel Φ ε w+cubicOtherAxisKernel Φ ε w-
    cubicIntersectionKernel ε w • (realCubicSource (1+ε) w.1 w.2*Φ w)-
    2*cubicMixedKernel Φ ε w+Φ w

/-- Full compact-test boundary action: both finite parts, intersection mass, mixed PV
and ordinary test integral. -/
def cubicCriticalBoundaryValue (Φ : ℝ × ℝ → ℂ) (R : ℝ) : ℂ :=
  (∫ w : ℝ × ℝ in Icc (0,-R) (R,R), cubicAxisQuotient Φ 1 w)+
  (∫ w : ℝ × ℝ in Icc (0,-R) (R,R), cubicAxisQuotient (fun z => Φ (z.2,z.1)) 1 w)-
    (Real.pi^2 : ℝ) • Φ (0,0)-
    2*(∫ w : ℝ × ℝ in Icc (0,0) (R,R), cubicMixedQuotient Φ 1 w)+
    ∫ w : ℝ × ℝ in Icc (-R,-R) (R,R), Φ w

private theorem integral_intersection_eq_box {Φ : ℝ × ℝ → ℂ} {R : ℝ}
    (hsupp : Function.support Φ ⊆ Icc (-R,-R) (R,R)) (ε : ℝ) :
    (∫ w : ℝ × ℝ in Icc (-R,-R) (R,R),
      cubicIntersectionKernel ε w • (realCubicSource (1+ε) w.1 w.2*Φ w)) =
    ∫ w : ℝ × ℝ, cubicIntersectionKernel ε w • (realCubicSource (1+ε) w.1 w.2*Φ w) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro w hw
  have hΦ0 : Φ w=0 := by
    by_contra h
    exact hw (hsupp h)
  simp only [hΦ0,mul_zero,smul_zero]

/-- Every singular term is retained in the critical boundary of the actual complete source.
The support condition only places the chosen compact test inside its integration box. -/
theorem tendsto_integral_cubicConnectedKernel_box {Φ : ℝ × ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) {R : ℝ} (hR : 0 ≤ R)
    (hsupp : Function.support Φ ⊆ Icc (-R,-R) (R,R)) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ in Icc (-R,-R) (R,R), cubicConnectedKernel Φ ε w)
      (𝓝[>] 0) (𝓝 (cubicCriticalBoundaryValue Φ R)) := by
  have hI : Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ in Icc (-R,-R) (R,R),
      cubicIntersectionKernel ε w • (realCubicSource (1+ε) w.1 w.2*Φ w))
      (𝓝[>] 0) (𝓝 ((Real.pi^2 : ℝ) • Φ (0,0))) := by
    simp_rw [integral_intersection_eq_box hsupp]
    exact tendsto_cubic_intersection hΦ.continuous hΦc
  have h := (((tendsto_integral_cubicAxisKernel hΦ hR).add
    (tendsto_integral_cubicOtherAxisKernel hΦ hR)).sub hI).sub
    ((tendsto_integral_cubicMixedKernel hΦ hR).const_mul 2)
  have hlim := h.add (tendsto_const_nhds (x := ∫ w : ℝ × ℝ in Icc (-R,-R) (R,R), Φ w))
  apply hlim.congr'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  have hA := (continuous_cubicAxisKernel hΦ hε).integrableOn_Icc
    (a := (-R,-R)) (b := (R,R)) (μ := (volume : Measure (ℝ × ℝ)))
  have hB := (continuous_cubicOtherAxisKernel hΦ hε).integrableOn_Icc
    (a := (-R,-R)) (b := (R,R)) (μ := (volume : Measure (ℝ × ℝ)))
  have hM := (continuous_cubicMixedKernel hΦ hε).integrableOn_Icc
    (a := (-R,-R)) (b := (R,R)) (μ := (volume : Measure (ℝ × ℝ)))
  have hII := (integrable_tested_cubicIntersectionKernel hε hΦ.continuous hΦc).integrableOn
    (s := Icc (-R,-R) (R,R))
  have hP := hΦ.continuous.integrableOn_Icc
    (a := (-R,-R)) (b := (R,R)) (μ := (volume : Measure (ℝ × ℝ)))
  symm
  unfold cubicConnectedKernel
  have hsum := integral_add (((hA.add hB).sub hII).sub (hM.const_mul 2)) hP
  rw [integral_sub' ((hA.add hB).sub hII) (hM.const_mul 2),
    integral_sub' (hA.add hB) hII,integral_add' hA hB,integral_const_mul] at hsum
  convert hsum using 1
  rfl

private theorem cubicConnectedKernel_identity (Φ : ℝ × ℝ → ℂ) (ε : ℝ) (w : ℝ × ℝ) :
      ((realCubicSource (1+ε) w.1 w.2-realAxisSource (1+ε) w.1)/((ε^2+w.1^2 : ℝ) : ℂ)+
      (realCubicSource (1+ε) w.1 w.2-realAxisSource (1+ε) w.2)/((ε^2+w.2^2 : ℝ) : ℂ)-
      (ε : ℂ)^2*realCubicSource (1+ε) w.1 w.2/
        (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ))-
      2*(w.1 : ℂ)*(w.2 : ℂ)*realCubicSource (1+ε) w.1 w.2/
        (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ))+1)*Φ w =
        cubicConnectedKernel Φ ε w := by
  unfold cubicConnectedKernel
  rw [cubicIntersectionKernel_smul]
  dsimp [cubicAxisKernel,cubicOtherAxisKernel,cubicMixedKernel,
    cubicTestedSource,cubicTestedAxisNumerator]
  ring

/-- The finite-prime limit is exactly the kernel whose full boundary is proved here. -/
theorem complete_weighted_offAxes_connectedKernel (Φ : ℝ × ℝ → ℂ)
    {ε : ℝ} (hε : 0 < ε) (w : ℝ × ℝ) :
    Tendsto (fun S : Finset Nat.Primes => weightedOffAxesTrace ((1+ε : ℝ) : ℂ)
      ((w.1 : ℂ)*Complex.I) ((w.2 : ℂ)*Complex.I) S * Φ w)
      atTop (𝓝 (cubicConnectedKernel Φ ε w)) := by
  have h := (complete_weighted_offAxes_regular_kernel (σ := 1+ε) (by linarith)
    w.1 w.2).mul_const (Φ w)
  simp only [add_sub_cancel_left] at h
  rw [cubicConnectedKernel_identity] at h
  exact h

theorem integral_cubicConnectedKernel_eq_box {Φ : ℝ × ℝ → ℂ} {R : ℝ}
    (hsupp : Function.support Φ ⊆ Icc (-R,-R) (R,R)) (ε : ℝ) :
    (∫ w : ℝ × ℝ in Icc (-R,-R) (R,R), cubicConnectedKernel Φ ε w) =
      ∫ w : ℝ × ℝ, cubicConnectedKernel Φ ε w := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro w hw
  have hz : Φ w=0 := by
    by_contra h
    exact hw (hsupp h)
  simp [cubicConnectedKernel,cubicAxisKernel,cubicOtherAxisKernel,cubicMixedKernel,
    cubicTestedSource,cubicTestedAxisNumerator,hz]

/-- Full-plane compact-test boundary of the complete connected arithmetic kernel. -/
theorem tendsto_integral_cubicConnectedKernel {Φ : ℝ × ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) {R : ℝ} (hR : 0 ≤ R)
    (hsupp : Function.support Φ ⊆ Icc (-R,-R) (R,R)) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ, cubicConnectedKernel Φ ε w)
      (𝓝[>] 0) (𝓝 (cubicCriticalBoundaryValue Φ R)) := by
  have h := tendsto_integral_cubicConnectedKernel_box hΦ hΦc hR hsupp
  simpa only [integral_cubicConnectedKernel_eq_box hsupp] using h

/-- Every smooth compact test has the complete critical boundary, with its explicit
finite-part, mixed-PV and intersection-mass formula. -/
theorem exists_cubicCriticalBoundary {Φ : ℝ × ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) :
    ∃ R > 0, Function.support Φ ⊆ Icc (-R,-R) (R,R) ∧
      Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ, cubicConnectedKernel Φ ε w)
        (𝓝[>] 0) (𝓝 (cubicCriticalBoundaryValue Φ R)) := by
  obtain ⟨R,hR,hbound⟩ := hΦc.isBounded.exists_pos_norm_le
  have hsupp : Function.support Φ ⊆ Icc (-R,-R) (R,R) := by
    intro w hw
    have hwR := hbound w (subset_closure hw)
    have hu : |w.1| ≤ R := (norm_fst_le w).trans hwR
    have hv : |w.2| ≤ R := (norm_snd_le w).trans hwR
    exact ⟨⟨(abs_le.mp hu).1,(abs_le.mp hv).1⟩,⟨(abs_le.mp hu).2,(abs_le.mp hv).2⟩⟩
  exact ⟨R,hR,hsupp,tendsto_integral_cubicConnectedKernel hΦ hΦc hR.le hsupp⟩

/-- For every positive damping, the full-plane tested kernel is genuinely integrable. -/
theorem integrable_cubicConnectedKernel {Φ : ℝ × ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (cubicConnectedKernel Φ ε) := by
  obtain ⟨R,_,hsupp,_⟩ := exists_cubicCriticalBoundary hΦ hΦc
  have hA := (continuous_cubicAxisKernel hΦ hε).integrableOn_Icc
    (a := (-R,-R)) (b := (R,R)) (μ := (volume : Measure (ℝ × ℝ)))
  have hB := (continuous_cubicOtherAxisKernel hΦ hε).integrableOn_Icc
    (a := (-R,-R)) (b := (R,R)) (μ := (volume : Measure (ℝ × ℝ)))
  have hM := (continuous_cubicMixedKernel hΦ hε).integrableOn_Icc
    (a := (-R,-R)) (b := (R,R)) (μ := (volume : Measure (ℝ × ℝ)))
  have hI := (integrable_tested_cubicIntersectionKernel hε hΦ.continuous hΦc).integrableOn
    (s := Icc (-R,-R) (R,R))
  have hP := hΦ.continuous.integrableOn_Icc
    (a := (-R,-R)) (b := (R,R)) (μ := (volume : Measure (ℝ × ℝ)))
  have hbox : IntegrableOn (cubicConnectedKernel Φ ε) (Icc (-R,-R) (R,R)) := by
    convert (((hA.add hB).sub hI).sub (hM.const_mul 2)).add hP using 1 <;> rfl
  apply hbox.integrable_of_forall_notMem_eq_zero
  intro w hw
  have hz : Φ w=0 := by
    by_contra h
    exact hw (hsupp h)
  simp [cubicConnectedKernel,cubicAxisKernel,cubicOtherAxisKernel,cubicMixedKernel,
    cubicTestedSource,cubicTestedAxisNumerator,hz]

/-- The explicit boundary action is independent of the containing integration box. -/
theorem cubicCriticalBoundaryValue_eq {Φ : ℝ × ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) {R S : ℝ}
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hΦR : Function.support Φ ⊆ Icc (-R,-R) (R,R))
    (hΦS : Function.support Φ ⊆ Icc (-S,-S) (S,S)) :
    cubicCriticalBoundaryValue Φ R = cubicCriticalBoundaryValue Φ S :=
  tendsto_nhds_unique (tendsto_integral_cubicConnectedKernel hΦ hΦc hR hΦR)
    (tendsto_integral_cubicConnectedKernel hΦ hΦc hS hΦS)

end RHTower.BAGTrace

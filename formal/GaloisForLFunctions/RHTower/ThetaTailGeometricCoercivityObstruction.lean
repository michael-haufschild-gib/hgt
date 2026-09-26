import GaloisForLFunctions.RHTower.ThetaTailGeometricAnalyticLocality
import GaloisForLFunctions.RHTower.ThetaTailGeometricReserveObstruction

/-!
# No positive geometric reserve on any theta tail

For every real threshold and positive comparison coefficient, a finite real
packet beyond that threshold is negative for the complete theta kernel minus
that coefficient times the geometric kernel. Analytic locality transports
the positive-node obstruction without truncating the source.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
namespace RHTower.ThetaGeometricBoundaryAudit
open DominatedL2Sections
open scoped InnerProductSpace

lemma negative_geometric_tail_packet {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    ∃ (S : Finset (Complex.ofReal '' Ioi (max a 0)))
      (b : (Complex.ofReal '' Ioi (max a 0)) → ℝ),
      ∑ i ∈ S, ∑ j ∈ S, b i*b j*(thetaTailFirstMomentKernel i.val.re j.val.re-
        ε*thetaTailGeometricKernel i.val.re j.val.re) < 0 := by
  obtain ⟨x, y, hx, hy, hneg⟩ := exists_negative_positive_geometric_reserve hε
  let R := geometricRealization completeThetaSource ε
  have hv : (inner ℂ (R.kernelSection (x:ℂ)-R.kernelSection (y:ℂ))
      (R.form (R.kernelSection (x:ℂ)-R.kernelSection (y:ℂ)))).re < 0 := by
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
    change (R.kernel (x:ℂ) (x:ℂ)-R.kernel (y:ℂ) (x:ℂ)-
      (R.kernel (x:ℂ) (y:ℂ)-R.kernel (y:ℂ) (y:ℂ))).re < 0
    rw [geometricRealization_kernel_real ε hx hx, geometricRealization_kernel_real ε hy hx,
      geometricRealization_kernel_real ε hx hy, geometricRealization_kernel_real ε hy hy]
    simp only [Complex.sub_re, Complex.ofReal_re]
    rw [thetaTailFirstMomentKernel_comm y x, thetaTailGeometricKernel_comm y x]
    linarith only [hneg]
  obtain ⟨d, hd⟩ := R.exists_negative_packet_on_accumulationSet
    (geometricTailAccumulationSet completeThetaSource ε a) hv
  have hk (z w : Complex.ofReal '' Ioi (max a 0)) :
      R.kernel z w =
        ((2*(thetaTailFirstMomentKernel z.val.re w.val.re-
          ε*thetaTailGeometricKernel z.val.re w.val.re):ℝ):ℂ) := by
    obtain ⟨r, hr, he⟩ := z.property
    obtain ⟨s, hs, hf⟩ := w.property
    rw [← he, ← hf, Complex.ofReal_re, Complex.ofReal_re]
    exact geometricRealization_kernel_real ε
      ((le_max_right a 0).trans_lt hr) ((le_max_right a 0).trans_lt hs)
  change (∑ i ∈ d.support, ∑ j ∈ d.support, star (d j)*d i*R.kernel i j).re < 0 at hd
  simp_rw [hk] at hd
  obtain ⟨b, hb⟩ := real_packet_of_negative_complex_packet d.support
    (fun i j => thetaTailFirstMomentKernel i.val.re j.val.re-
      ε*thetaTailGeometricKernel i.val.re j.val.re) d hd
  exact ⟨d.support, b, hb⟩

lemma exists_finite_negative_geometric_tail {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    ∃ (n : ℕ) (t b : Fin n → ℝ),
      (∀ i, max a 0 < t i) ∧
      (∑ i, ∑ j, b i*b j*(thetaTailFirstMomentKernel (t i) (t j)-
        ε*thetaTailGeometricKernel (t i) (t j))) < 0 := by
  classical
  obtain ⟨S, b, hb⟩ := negative_geometric_tail_packet hε a
  let e := S.equivFin.symm
  let t : Fin S.card → ℝ := fun i => (e i).val.val.re
  let c : Fin S.card → ℝ := fun i => b (e i).val
  let K : ℝ → ℝ → ℝ := fun x y => thetaTailFirstMomentKernel x y-ε*thetaTailGeometricKernel x y
  refine ⟨S.card, t, c, ?_, ?_⟩
  · intro i
    obtain ⟨r, hr, he⟩ := (e i).val.property
    change max a 0 < (e i).val.val.re
    rw [← he, Complex.ofReal_re]
    exact hr
  · have hi (z : Complex.ofReal '' Ioi (max a 0)) :
        (∑ j, b z*c j*K z.val.re (t j)) =
          ∑ w ∈ S, b z*b w*K z.val.re w.val.re := by
      dsimp [c, t, e]
      rw [Equiv.sum_comp S.equivFin.symm
        (fun w : S => b z*b w.val*K z.val.re w.val.val.re),
        Finset.univ_eq_attach,
        Finset.sum_attach S (fun w => b z*b w*K z.val.re w.val.re)]
    have he : (∑ i, ∑ j, c i*c j*K (t i) (t j)) =
        ∑ z ∈ S, ∑ w ∈ S, b z*b w*K z.val.re w.val.re := by
      change (∑ i, ∑ j, b (e i).val*c j*K (e i).val.val.re (t j)) = _
      simp_rw [hi]
      dsimp [e]
      rw [Equiv.sum_comp S.equivFin.symm
        (fun z : S => ∑ w ∈ S, b z.val*b w*K z.val.val.re w.val.re),
        Finset.univ_eq_attach,
        Finset.sum_attach S (fun z => ∑ w ∈ S, b z*b w*K z.val.re w.val.re)]
    exact he ▸ hb

end RHTower.ThetaGeometricBoundaryAudit

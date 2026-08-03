import GaloisForLFunctions.HTGeometry.ShiftedMassJetSmoothness
import GaloisForLFunctions.HTGeometry.UniformSpanningAtoms

/-!
# The mass parameter is a submersion onto the jets, uniformly in the shift

Exponential rescaling of finitely many masses moves the jet packet along the mass columns, so its
derivative is a positive diagonal times those columns: the image is the column span at *every*
parameter value, not only at the base point.

The mass columns span the packet space at every collision-free shift, so one finite atom family
spans over a whole compact shift patch, and the parameter derivative is surjective there.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The affine splitting of the shifted mass jet packet along the mass columns. -/
theorem shiftedMassJetPacket_eq {row : Type*} [Fintype row] {z : row → ℂ}
    (hupper : ∀ b, 0 < (z b).im) {r : ℕ} (ord : row × Fin r → ℕ) (x : ℕ → ℝ) {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) (hsum : Summable w) {K : ℕ} {a : Fin K → ℕ} (ha : Function.Injective a)
    (p : (Fin K → ℝ) × (Fin r → ℝ)) :
    shiftedMassJetPacket z ord x w a p
      = discreteJetPacket (combinedNodes z p.2) ord x w
        + ∑ k, (Real.exp (p.1 k) - 1) • massJetColumn (combinedNodes z p.2) ord x w (a k) := by
  funext u
  have hdiff := discreteJetPacket_perturbedWeight_sub ha p.1 hw hsum (combinedNodes z p.2)
    (fun v => (im_combinedNodes_pos hupper p.2 v).ne') ord x u
  have hsumapply : (∑ k, (Real.exp (p.1 k) - 1) • massJetColumn (combinedNodes z p.2) ord x w
      (a k)) u = ∑ k, (Real.exp (p.1 k) - 1) • massJetColumn (combinedNodes z p.2) ord x w
      (a k) u := by
    simp
  show discreteJetPacket (combinedNodes z p.2) ord x (perturbedWeight a p.1 w) u = _
  rw [Pi.add_apply, hsumapply, ← hdiff]
  ring

/-- **The parameter derivative is the mass columns scaled by a positive diagonal.** -/
theorem hasFDerivAt_shiftedMassJetPacket {row : Type*} [Fintype row] {z : row → ℂ}
    (hupper : ∀ b, 0 < (z b).im) {r : ℕ} (ord : row × Fin r → ℕ) (x : ℕ → ℝ) {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) (hsum : Summable w) {K : ℕ} {a : Fin K → ℕ} (ha : Function.Injective a)
    (t : Fin r → ℝ) (s₀ : Fin K → ℝ) :
    HasFDerivAt (fun s => shiftedMassJetPacket z ord x w a (s, t))
      (∑ k, ((Real.exp (s₀ k) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => ℝ) k).smulRight
        (massJetColumn (combinedNodes z t) ord x w (a k)))) s₀ := by
  have hval : (fun s => shiftedMassJetPacket z ord x w a (s, t))
      = fun s => discreteJetPacket (combinedNodes z t) ord x w
        + ∑ k, (Real.exp (s k) - 1) • massJetColumn (combinedNodes z t) ord x w (a k) := by
    funext s
    exact shiftedMassJetPacket_eq hupper ord x hw hsum ha (s, t)
  rw [hval]
  refine HasFDerivAt.const_add _ ?_
  refine HasFDerivAt.fun_sum fun k _ => ?_
  have hproj : HasFDerivAt (fun s : Fin K → ℝ => s k) (ContinuousLinearMap.proj k) s₀ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => ℝ) k).hasFDerivAt
  have hexp : HasFDerivAt (fun s : Fin K → ℝ => Real.exp (s k))
      (Real.exp (s₀ k) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => ℝ) k) s₀ := by
    have h := (Real.hasDerivAt_exp (s₀ k)).comp_hasFDerivAt s₀ hproj
    exact h
  exact (hexp.sub_const 1).smul_const _

/-- **The parameter derivative is surjective wherever the mass columns span.** -/
theorem surjective_fderiv_shiftedMassJetPacket {row : Type*} [Fintype row] {z : row → ℂ}
    (hupper : ∀ b, 0 < (z b).im) {r : ℕ} (ord : row × Fin r → ℕ) (x : ℕ → ℝ) {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) (hsum : Summable w) {K : ℕ} {a : Fin K → ℕ} (ha : Function.Injective a)
    (t : Fin r → ℝ) (s₀ : Fin K → ℝ)
    (hspan : Submodule.span ℝ
      (Set.range fun k => massJetColumn (combinedNodes z t) ord x w (a k)) = ⊤) :
    Function.Surjective (fderiv ℝ (fun s => shiftedMassJetPacket z ord x w a (s, t)) s₀) := by
  have hderiv := hasFDerivAt_shiftedMassJetPacket hupper ord x hw hsum ha t s₀
  rw [hderiv.fderiv]
  intro y
  obtain ⟨v, hv⟩ := (surjective_columnControl_iff
    (fun k => massJetColumn (combinedNodes z t) ord x w (a k))).mpr hspan y
  refine ⟨fun k => v k / Real.exp (s₀ k), ?_⟩
  rw [sum_apply]
  rw [columnControl_apply] at hv
  rw [← hv]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.smulRight_apply, smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  congr 1
  field_simp

/-! ## One atom family for a whole compact shift patch -/

/-- **Uniform mass controllability over a compact shift patch.**  One finite atom family makes the
mass columns span the jet packet space at every collision-free shift of the patch. -/
theorem exists_uniform_massJet_atoms {row : Type*} [Fintype row] [DecidableEq row] {z : row → ℂ}
    (hupper : ∀ b, 0 < (z b).im) (hsep : ∀ b b', b ≠ b' → (z b).im ≠ (z b').im) {r : ℕ}
    (ord : row × Fin r → ℕ) {x : ℕ → ℝ} (hx : Function.Injective x) {w : ℕ → ℝ}
    (hwne : ∀ n, w n ≠ 0) {Kset : Set (Fin r → ℝ)} (hK : IsCompact Kset)
    (hKinj : ∀ t ∈ Kset, Function.Injective t) :
    ∃ (K : ℕ) (a : Fin K → ℕ), Function.Injective a ∧ ∀ t ∈ Kset,
      Submodule.span ℝ (Set.range fun l =>
        massJetColumn (combinedNodes z t) ord x w (a l)) = ⊤ := by
  classical
  refine exists_uniform_spanning_atoms
    (fun n t => massJetColumn (combinedNodes z t) ord x w n) (fun n => ?_) hK (fun t ht => ?_)
  · refine continuous_pi fun u => ?_
    exact (contDiff_massJetColumn hupper ord x w n u).continuous
  · exact span_range_massJetColumn_eq_top (combinedNodes z t)
      (injective_combinedNodes hsep (hKinj t ht)) (im_combinedNodes_pos hupper t) ord x hx w hwne

end

end GaloisForLFunctions.HTGeometry

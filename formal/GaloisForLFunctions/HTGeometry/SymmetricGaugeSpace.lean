import GaloisForLFunctions.HTGeometry.SymmetricPassportPolynomial
import GaloisForLFunctions.HTGeometry.GaugeExpandedJetFamily
import GaloisForLFunctions.HTGeometry.SymmetricGaugeProbe

/-!
# The constrained gauge space

Entire gauges obeying the functional equation, Schwarz reality, and a prescribed finite jet
passport form a closed subset of the compact-open gauge space, hence a Baire space of its own.

The symmetric passport probe moves inside this constraint space, so it is a finite-dimensional
chart through every constrained gauge.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology

noncomputable section

/-- Gauges with the functional equation, Schwarz reality, and a prescribed finite jet passport. -/
def symGaugeSet (A : Finset ℂ) (dep : ℂ → ℕ) : Set EntireGauge :=
  {g | (∀ z : ℂ, (g : C(ℂ, ℂ)) (1 - z) = (g : C(ℂ, ℂ)) z)
    ∧ (∀ z : ℂ, (g : C(ℂ, ℂ)) ((starRingEnd ℂ) z) = (starRingEnd ℂ) ((g : C(ℂ, ℂ)) z))
    ∧ (∀ a ∈ A, ∀ j < dep a, iteratedDeriv j ⇑(g : C(ℂ, ℂ)) a = 0)}

theorem continuous_gaugeEval (w : ℂ) : Continuous (fun g : EntireGauge => (g : C(ℂ, ℂ)) w) := by
  have h := (continuous_gaugeJetEval 0).comp (continuous_id.prodMk (continuous_const (y := w)))
  simpa only [iteratedDeriv_zero, Function.comp_def, id_eq] using h

theorem continuous_gaugeJet (j : ℕ) (w : ℂ) :
    Continuous (fun g : EntireGauge => iteratedDeriv j ⇑(g : C(ℂ, ℂ)) w) :=
  (continuous_gaugeJetEval j).comp (continuous_id.prodMk (continuous_const (y := w)))

theorem isClosed_symGaugeSet (A : Finset ℂ) (dep : ℂ → ℕ) : IsClosed (symGaugeSet A dep) := by
  have h1 : IsClosed {g : EntireGauge | ∀ z : ℂ, (g : C(ℂ, ℂ)) (1 - z) = (g : C(ℂ, ℂ)) z} := by
    rw [show {g : EntireGauge | ∀ z : ℂ, (g : C(ℂ, ℂ)) (1 - z) = (g : C(ℂ, ℂ)) z}
        = ⋂ z : ℂ, {g : EntireGauge | (g : C(ℂ, ℂ)) (1 - z) = (g : C(ℂ, ℂ)) z} from by
      ext g; simp]
    exact isClosed_iInter fun z =>
      isClosed_eq (continuous_gaugeEval (1 - z)) (continuous_gaugeEval z)
  have h2 : IsClosed {g : EntireGauge |
      ∀ z : ℂ, (g : C(ℂ, ℂ)) ((starRingEnd ℂ) z) = (starRingEnd ℂ) ((g : C(ℂ, ℂ)) z)} := by
    rw [show {g : EntireGauge |
        ∀ z : ℂ, (g : C(ℂ, ℂ)) ((starRingEnd ℂ) z) = (starRingEnd ℂ) ((g : C(ℂ, ℂ)) z)}
        = ⋂ z : ℂ, {g : EntireGauge |
          (g : C(ℂ, ℂ)) ((starRingEnd ℂ) z) = (starRingEnd ℂ) ((g : C(ℂ, ℂ)) z)} from by
      ext g; simp]
    exact isClosed_iInter fun z =>
      isClosed_eq (continuous_gaugeEval ((starRingEnd ℂ) z))
        (Complex.continuous_conj.comp (continuous_gaugeEval z))
  have h3 : IsClosed {g : EntireGauge |
      ∀ a ∈ A, ∀ j < dep a, iteratedDeriv j ⇑(g : C(ℂ, ℂ)) a = 0} := by
    rw [show {g : EntireGauge | ∀ a ∈ A, ∀ j < dep a, iteratedDeriv j ⇑(g : C(ℂ, ℂ)) a = 0}
        = ⋂ a ∈ A, ⋂ j, ⋂ _ : j < dep a,
          {g : EntireGauge | iteratedDeriv j ⇑(g : C(ℂ, ℂ)) a = 0} from by
      ext g; simp]
    refine isClosed_biInter fun a _ => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
    exact isClosed_eq (continuous_gaugeJet j a) continuous_const
  exact (h1.inter (h2.inter h3))

theorem zero_mem_symGaugeSet (A : Finset ℂ) (dep : ℂ → ℕ) :
    (0 : EntireGauge) ∈ symGaugeSet A dep := by
  refine ⟨fun z => rfl, fun z => ?_, fun a _ j _ => ?_⟩
  · show (0 : ℂ) = (starRingEnd ℂ) 0
    simp
  · have hfun : ⇑((0 : EntireGauge) : C(ℂ, ℂ)) = fun _ : ℂ => (0 : ℂ) := rfl
    rw [hfun]
    induction j with
    | zero => simp
    | succ j ih => rw [iteratedDeriv_succ']; simp

instance nonempty_symGaugeSet (A : Finset ℂ) (dep : ℂ → ℕ) :
    Nonempty ↥(symGaugeSet A dep) := ⟨⟨0, zero_mem_symGaugeSet A dep⟩⟩

noncomputable instance completelyMetrizable_symGaugeSet (A : Finset ℂ) (dep : ℂ → ℕ) :
    TopologicalSpace.IsCompletelyMetrizableSpace ↥(symGaugeSet A dep) :=
  (isClosed_symGaugeSet A dep).isCompletelyMetrizableSpace

noncomputable instance baire_symGaugeSet (A : Finset ℂ) (dep : ℂ → ℕ) :
    BaireSpace ↥(symGaugeSet A dep) := by infer_instance

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Set Topology Polynomial

noncomputable section

variable {X : Type*} [Fintype X]

/-- The symmetric passport probe attached to a prescribed passport. -/
def passportProbe (X : Type*) [Fintype X] (A : Finset ℂ) (dep : ℂ → ℕ) (m N D : ℕ) :
    GaugeProbe X m D :=
  symProbe X (symPassportPoly A dep) m N D

theorem passportProbe_poly (A : Finset ℂ) (dep : ℂ → ℕ) (m N D : ℕ) (c : Fin D → ℂ) :
    (passportProbe X A dep m N D).poly c
      = symPassportPoly A dep * avgPoly (windowLin N D c) :=
  symProbe_poly _ m N D c

theorem probeGaugeChart_mem_symGaugeSet {A : Finset ℂ} {dep : ℂ → ℕ}
    (hA1 : ∀ a ∈ A, 1 - a ∈ A) (hdep1 : ∀ a ∈ A, dep (1 - a) = dep a)
    (hA2 : ∀ a ∈ A, (starRingEnd ℂ) a ∈ A)
    (hdep2 : ∀ a ∈ A, dep ((starRingEnd ℂ) a) = dep a)
    (m N D : ℕ) {g : EntireGauge} (hg : g ∈ symGaugeSet A dep) (c : Fin D → ℂ) :
    probeGaugeChart (passportProbe X A dep m N D) g c ∈ symGaugeSet A dep := by
  set P : Polynomial ℂ := (passportProbe X A dep m N D).poly c with hP
  have hrefl : reflectPoly P = P := by
    rw [hP, passportProbe]
    exact reflectPoly_symProbe_poly _ (reflectPoly_symPassportPoly hA1 hdep1) m N D c
  have hconj : conjPoly P = P := by
    rw [hP, passportProbe]
    exact conjPoly_symProbe_poly _ (conjPoly_symPassportPoly hA2 hdep2) m N D c
  have hdiffP : Differentiable ℂ (fun w => Polynomial.eval w P) := Polynomial.differentiable _
  refine ⟨fun z => ?_, fun z => ?_, fun a ha j hj => ?_⟩
  · rw [probeGaugeChart_apply, probeGaugeChart_apply, hg.1 z]
    congr 1
    rw [← hP]
    conv_lhs => rw [← hrefl]
    rw [eval_reflectPoly]
    congr 1
    ring
  · rw [probeGaugeChart_apply, probeGaugeChart_apply, hg.2.1 z, map_add]
    congr 1
    rw [← hP]
    have hev := eval_conjPoly P z
    rw [hconj] at hev
    rw [hev, Complex.conj_conj]
  · have hsum : ⇑((probeGaugeChart (passportProbe X A dep m N D) g c : EntireGauge) : C(ℂ, ℂ))
        = fun w => (g : C(ℂ, ℂ)) w + Polynomial.eval w P := by
      funext w
      exact probeGaugeChart_apply _ g c w
    rw [hsum, iteratedDeriv_add_entire g.2 hdiffP, hg.2.2 a ha j hj, zero_add,
      iteratedDeriv_polynomial_eval]
    rw [hP, passportProbe_poly]
    exact eval_iterate_derivative_symPassportPoly_mul ha hj _

/-- The symmetric passport chart on the constrained gauge space. -/
def symChart {A : Finset ℂ} {dep : ℂ → ℕ}
    (hA1 : ∀ a ∈ A, 1 - a ∈ A) (hdep1 : ∀ a ∈ A, dep (1 - a) = dep a)
    (hA2 : ∀ a ∈ A, (starRingEnd ℂ) a ∈ A)
    (hdep2 : ∀ a ∈ A, dep ((starRingEnd ℂ) a) = dep a)
    (X : Type*) [Fintype X] (m N D : ℕ)
    (g : ↥(symGaugeSet A dep)) (c : Fin D → ℂ) : ↥(symGaugeSet A dep) :=
  ⟨probeGaugeChart (passportProbe X A dep m N D) g.1 c,
    probeGaugeChart_mem_symGaugeSet hA1 hdep1 hA2 hdep2 m N D g.2 c⟩

theorem symChart_apply {A : Finset ℂ} {dep : ℂ → ℕ}
    (hA1 : ∀ a ∈ A, 1 - a ∈ A) (hdep1 : ∀ a ∈ A, dep (1 - a) = dep a)
    (hA2 : ∀ a ∈ A, (starRingEnd ℂ) a ∈ A)
    (hdep2 : ∀ a ∈ A, dep ((starRingEnd ℂ) a) = dep a)
    (X : Type*) [Fintype X] (m N D : ℕ)
    (g : ↥(symGaugeSet A dep)) (c : Fin D → ℂ) (w : ℂ) :
    (((symChart hA1 hdep1 hA2 hdep2 X m N D g c : ↥(symGaugeSet A dep)) : EntireGauge) :
        C(ℂ, ℂ)) w
      = ((g : EntireGauge) : C(ℂ, ℂ)) w
        + Polynomial.eval w ((passportProbe X A dep m N D).poly c) := rfl

theorem symChart_zero {A : Finset ℂ} {dep : ℂ → ℕ}
    (hA1 : ∀ a ∈ A, 1 - a ∈ A) (hdep1 : ∀ a ∈ A, dep (1 - a) = dep a)
    (hA2 : ∀ a ∈ A, (starRingEnd ℂ) a ∈ A)
    (hdep2 : ∀ a ∈ A, dep ((starRingEnd ℂ) a) = dep a)
    (X : Type*) [Fintype X] (m N D : ℕ) (g : ↥(symGaugeSet A dep)) :
    symChart hA1 hdep1 hA2 hdep2 X m N D g 0 = g := by
  refine Subtype.ext ?_
  exact probeGaugeChart_zero (passportProbe X A dep m N D) g.1

theorem continuous_symChart {A : Finset ℂ} {dep : ℂ → ℕ}
    (hA1 : ∀ a ∈ A, 1 - a ∈ A) (hdep1 : ∀ a ∈ A, dep (1 - a) = dep a)
    (hA2 : ∀ a ∈ A, (starRingEnd ℂ) a ∈ A)
    (hdep2 : ∀ a ∈ A, dep ((starRingEnd ℂ) a) = dep a)
    (X : Type*) [Fintype X] (m N D : ℕ) (g : ↥(symGaugeSet A dep)) :
    Continuous (symChart hA1 hdep1 hA2 hdep2 X m N D g) := by
  rw [continuous_induced_rng]
  exact continuous_probeGaugeChart (passportProbe X A dep m N D) g.1

end

end GaloisForLFunctions.HTGeometry

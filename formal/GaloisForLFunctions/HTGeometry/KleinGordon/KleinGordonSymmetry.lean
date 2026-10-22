import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonEigenEnvelope

/-!
# A symmetry of the background is a symmetry of the flow

The evolution is assembled from two ingredients: the free propagator and the source operator built
from the potential. An operator on `L²` that commutes with the free building blocks — `cos t⟨D⟩`,
`sin t⟨D⟩`, `⟨D⟩⁻¹` — and with the potential at every time therefore commutes with both, and the
uniqueness of the Duhamel solution promotes that to a commutation with the whole flow:

`Λ v(t) = v_{Λ datum}(t)`.

Two consequences. The monodromy of a periodic background commutes with any such symmetry, so its
spectral theory splits along the symmetry's eigenspaces. And a Cauchy datum fixed by the symmetry
stays fixed for all time: symmetric initial data generate symmetric solutions, which is the
conservation law attached to the symmetry.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- An operator on `L²` acting diagonally on the energy space. -/
def kgDiagOp (Λ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) :
    KGEnergy E →L[ℂ] KGEnergy E :=
  (kgPair E).comp ((Λ.comp (kgFst E)).prod (Λ.comp (kgSnd E)))

theorem kgDiagOp_apply (Λ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (v : KGEnergy E) : kgDiagOp Λ v = kgPair E (Λ v.fst, Λ v.snd) := rfl

theorem kgDiagOp_kgPair (Λ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (g h : Lp ℂ 2 (volume : Measure E)) : kgDiagOp Λ (kgPair E (g, h)) = kgPair E (Λ g, Λ h) := rfl

section Commutation

variable {Λ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}

/-- A symmetry of the free building blocks commutes with the free propagator. -/
theorem kgDiagOp_kgPropagator
    (hcos : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgCosOp t x) = kgCosOp t (Λ x))
    (hsin : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgSinOp t x) = kgSinOp t (Λ x))
    (t : ℝ) (v : KGEnergy E) :
    kgDiagOp Λ (kgPropagator t v) = kgPropagator t (kgDiagOp Λ v) := by
  have hL : kgDiagOp Λ (kgPropagator t v)
      = kgPair E (Λ (kgCosOp t v.fst + kgSinOp t v.snd),
          Λ (-(kgSinOp t v.fst) + kgCosOp t v.snd)) := rfl
  have hR : kgPropagator t (kgDiagOp Λ v)
      = kgPair E (kgCosOp t (Λ v.fst) + kgSinOp t (Λ v.snd),
          -(kgSinOp t (Λ v.fst)) + kgCosOp t (Λ v.snd)) := rfl
  rw [hL, hR, map_add, map_add, map_neg, hcos, hsin, hcos, hsin]

/-- A symmetry of the potential and of `⟨D⟩⁻¹` commutes with the source operator. -/
theorem kgDiagOp_kgSourceOp
    {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    (hinv : ∀ x : Lp ℂ 2 (volume : Measure E), Λ (kgFreqInvOp x) = kgFreqInvOp (Λ x))
    (hW : ∀ x : Lp ℂ 2 (volume : Measure E), Λ (W₀ x) = W₀ (Λ x)) (v : KGEnergy E) :
    kgDiagOp Λ (kgSourceOp W₀ v) = kgSourceOp W₀ (kgDiagOp Λ v) := by
  have hL : kgDiagOp Λ (kgSourceOp W₀ v)
      = kgPair E (Λ 0, Λ (W₀ (kgFreqInvOp v.fst))) := rfl
  have hR : kgSourceOp W₀ (kgDiagOp Λ v)
      = kgPair E (0, W₀ (kgFreqInvOp (Λ v.fst))) := rfl
  rw [hL, hR, map_zero, hW, hinv]

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- Hence it commutes with the Duhamel kernel. -/
theorem kgDiagOp_kgStateKernelT
    (hcos : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgCosOp t x) = kgCosOp t (Λ x))
    (hsin : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgSinOp t x) = kgSinOp t (Λ x))
    (hinv : ∀ x : Lp ℂ 2 (volume : Measure E), Λ (kgFreqInvOp x) = kgFreqInvOp (Λ x))
    (hW : ∀ (r : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (W r x) = W r (Λ x))
    (t s : ℝ) (v : KGEnergy E) :
    kgDiagOp Λ (kgStateKernelT W t s v) = kgStateKernelT W t s (kgDiagOp Λ v) := by
  rw [kgStateKernelT_apply, kgStateKernelT_apply, kgDiagOp_kgPropagator hcos hsin,
    kgDiagOp_kgSourceOp hinv (hW s)]

/-- And with the free state. -/
theorem kgDiagOp_kgStateFree
    (hcos : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgCosOp t x) = kgCosOp t (Λ x))
    (hsin : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgSinOp t x) = kgSinOp t (Λ x))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgDiagOp Λ (kgStateFree g h t) = kgStateFree (Λ g) (Λ h) t := by
  rw [kgStateFree, kgStateFree, kgDiagOp_kgPropagator hcos hsin, kgDiagOp_kgPair]

/-- **A symmetry of the background is a symmetry of the flow.** -/
theorem kgDiagOp_kgStateMildT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hcos : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgCosOp t x) = kgCosOp t (Λ x))
    (hsin : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgSinOp t x) = kgSinOp t (Λ x))
    (hinv : ∀ x : Lp ℂ 2 (volume : Measure E), Λ (kgFreqInvOp x) = kgFreqInvOp (Λ x))
    (hW : ∀ (r : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (W r x) = W r (Λ x))
    (g h : Lp ℂ 2 (volume : Measure E)) :
    (fun t : ℝ => kgDiagOp Λ (kgStateMildT W g h t)) = kgStateMildT W (Λ g) (Λ h) := by
  have hcont := continuous_kgStateMildT hb0 hWb hWs g h
  refine eq_kgStateMildT_of_duhamel hb0 hWb hWs (Λ g) (Λ h) ((kgDiagOp Λ).continuous.comp hcont)
    fun t => ?_
  have hI : IntervalIntegrable
      (fun s : ℝ => kgStateKernelT W t s (kgStateMildT W g h s)) volume 0 t :=
    (((strongKernel_kgStateKernelT hWb hWs) _ hcont).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t
  have hduh := kgStateMildT_eq hb0 hWb hWs g h t
  rw [hduh, map_add, kgDiagOp_kgStateFree hcos hsin,
    ← (kgDiagOp Λ).intervalIntegral_comp_comm hI]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  exact kgDiagOp_kgStateKernelT hcos hsin hinv hW t s _

/-- The symmetry law in the state register. -/
theorem kgFieldStateT_diag (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hcos : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgCosOp t x) = kgCosOp t (Λ x))
    (hsin : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgSinOp t x) = kgSinOp t (Λ x))
    (hinv : ∀ x : Lp ℂ 2 (volume : Measure E), Λ (kgFreqInvOp x) = kgFreqInvOp (Λ x))
    (hW : ∀ (r : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (W r x) = W r (Λ x))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldStateT W (Λ g) (Λ h) t = kgDiagOp Λ (kgFieldStateT W g h t) := by
  rw [kgFieldStateT_eq_kgStateMildT hb0 hWb hWs, kgFieldStateT_eq_kgStateMildT hb0 hWb hWs,
    ← kgDiagOp_kgStateMildT hb0 hWb hWs hcos hsin hinv hW g h]

/-- The symmetry law for the gradient. -/
theorem kgFieldGradT_diag (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hcos : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgCosOp t x) = kgCosOp t (Λ x))
    (hsin : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgSinOp t x) = kgSinOp t (Λ x))
    (hinv : ∀ x : Lp ℂ 2 (volume : Measure E), Λ (kgFreqInvOp x) = kgFreqInvOp (Λ x))
    (hW : ∀ (r : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (W r x) = W r (Λ x))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldGradT W (Λ g) (Λ h) t = Λ (kgFieldGradT W g h t) := by
  have hstate := kgFieldStateT_diag hb0 hWb hWs hcos hsin hinv hW g h t
  have hc := congrArg (fun v : KGEnergy E => v.fst) hstate
  simpa [kgFieldStateT, kgDiagOp_apply] using hc

/-- The symmetry law for the velocity. -/
theorem kgFieldVelT_diag (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hcos : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgCosOp t x) = kgCosOp t (Λ x))
    (hsin : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgSinOp t x) = kgSinOp t (Λ x))
    (hinv : ∀ x : Lp ℂ 2 (volume : Measure E), Λ (kgFreqInvOp x) = kgFreqInvOp (Λ x))
    (hW : ∀ (r : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (W r x) = W r (Λ x))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldVelT W (Λ g) (Λ h) t = Λ (kgFieldVelT W g h t) := by
  have hstate := kgFieldStateT_diag hb0 hWb hWs hcos hsin hinv hW g h t
  have hc := congrArg (fun v : KGEnergy E => v.snd) hstate
  simpa [kgFieldStateT, kgDiagOp_apply] using hc

/-- **The monodromy commutes with any symmetry of the background**, so its spectral theory splits
along the symmetry's eigenspaces. -/
theorem kgMonodromy_kgDiagOp_comm (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hcos : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgCosOp t x) = kgCosOp t (Λ x))
    (hsin : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgSinOp t x) = kgSinOp t (Λ x))
    (hinv : ∀ x : Lp ℂ 2 (volume : Measure E), Λ (kgFreqInvOp x) = kgFreqInvOp (Λ x))
    (hW : ∀ (r : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (W r x) = W r (Λ x)) (v : KGEnergy E) :
    kgMonodromy W b hb0 hWb hWs T (kgDiagOp Λ v)
      = kgDiagOp Λ (kgMonodromy W b hb0 hWb hWs T v) := by
  rw [kgMonodromy_apply, kgMonodromy_apply, kgPeriodMap_apply, kgPeriodMap_apply]
  have hstate := kgFieldStateT_diag hb0 hWb hWs hcos hsin hinv hW v.fst v.snd T
  simp only [kgDiagOp_apply, kgPair_fst, kgPair_snd]
  exact hstate

/-- **A datum fixed by a symmetry stays fixed for all time.** -/
theorem kgFieldStateT_fixed (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hcos : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgCosOp t x) = kgCosOp t (Λ x))
    (hsin : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgSinOp t x) = kgSinOp t (Λ x))
    (hinv : ∀ x : Lp ℂ 2 (volume : Measure E), Λ (kgFreqInvOp x) = kgFreqInvOp (Λ x))
    (hW : ∀ (r : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (W r x) = W r (Λ x))
    {g h : Lp ℂ 2 (volume : Measure E)} (hg : Λ g = g) (hh : Λ h = h) (t : ℝ) :
    kgDiagOp Λ (kgFieldStateT W g h t) = kgFieldStateT W g h t := by
  have hstate := kgFieldStateT_diag hb0 hWb hWs hcos hsin hinv hW g h t
  rw [hg, hh] at hstate
  exact hstate.symm

end Commutation

end GaloisForLFunctions.HTGeometry

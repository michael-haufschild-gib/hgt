import GaloisForLFunctions.HTGeometry.FiniteMemorySourceRecovery

/-!
# A complete linear source--history equivalence

The reconstruction mechanism in Zhang, arXiv:2608.22995v1, motivates more than
injectivity for the corpus's linear continuous Volterra equations. Their source
map is a bijective linear operator on all continuous histories. Compact-window
Picard convergence proves injectivity without a global kernel bound, then the
previous explicit left inverse supplies the right inverse. This is a statement
about these linear integral equations, not surjectivity for the paper's full
interacting electron--photon model.
-/

open MeasureTheory Filter
open scoped NNReal
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Actual continuous data have summable Picard increments at every time. -/
theorem summable_continuousVolterraIncrements
    (K : C(ℝ × ℝ, X →L[ℝ] X)) (f : C(ℝ, X)) (t : ℝ) :
    Summable (fun n : ℕ => volterraIterate f (fun t s => K (t, s)) (n + 1) t -
      volterraIterate f (fun t s => K (t, s)) n t) := by
  obtain ⟨M, F, hM, hF, hKb, hfb⟩ := continuousVolterra_locallyBounded f K |t| (abs_nonneg t)
  have hc := summable_volterraIncrements
    (continuous_volterraClampF |t| f.continuous)
    (continuous_volterraClampK |t| K.continuous) hM hF
    (norm_volterraClampK_le (abs_nonneg t) hKb)
    (norm_volterraClampF_le (abs_nonneg t) hfb) t
  have he (n : ℕ) : volterraIterate f (fun t s => K (t, s)) n t =
      volterraIterate (volterraClampF |t| f) (volterraClampK |t| (fun t s => K (t, s))) n t :=
    volterraIterate_congr_of_window (fun s hs => volterraClampF_eq (f := f) hs)
      (fun t s ht hs => volterraClampK_eq (K := fun t s => K (t, s)) ht hs) n t le_rfl
  exact hc.congr (fun n => by rw [he (n + 1), he n])

omit [CompleteSpace X] in
/-- Retarded-memory subtraction respects arbitrary superpositions. -/
theorem continuousVolterraSource_add (K : C(ℝ × ℝ, X →L[ℝ] X)) (u v : C(ℝ, X)) :
    continuousVolterraSource K (u + v) = continuousVolterraSource K u + continuousVolterraSource K v := by
  ext t
  have hi (w : C(ℝ, X)) : IntervalIntegrable (fun s => K (t, s) (w s)) volume 0 t :=
    ((K.continuous.comp (continuous_const.prodMk continuous_id)).clm_apply w.continuous).intervalIntegrable 0 t
  change (u t + v t) - (∫ s in (0 : ℝ)..t, K (t, s) (u s + v s)) =
    (u t - ∫ s in (0 : ℝ)..t, K (t, s) (u s)) + (v t - ∫ s in (0 : ℝ)..t, K (t, s) (v s))
  simp_rw [map_add]
  rw [intervalIntegral.integral_add (hi u) (hi v)]
  abel

omit [CompleteSpace X] in
/-- Retarded-memory subtraction respects arbitrary real amplitudes. -/
theorem continuousVolterraSource_smul (K : C(ℝ × ℝ, X →L[ℝ] X)) (u : C(ℝ, X)) (c : ℝ) :
    continuousVolterraSource K (c • u) = c • continuousVolterraSource K u := by
  ext t
  change c • u t - (∫ s in (0 : ℝ)..t, K (t, s) (c • u s)) =
    c • (u t - ∫ s in (0 : ℝ)..t, K (t, s) (u s))
  simp_rw [map_smul, intervalIntegral.integral_smul, smul_sub]

/-- The memory-subtraction map is injective on all continuous histories. -/
theorem continuousVolterraSource_injective (K : C(ℝ × ℝ, X →L[ℝ] X)) :
    Function.Injective (continuousVolterraSource K) := by
  intro u v huv
  let d : C(ℝ, X) := u - v
  have hhom (t : ℝ) : d t = ∫ s in (0 : ℝ)..t, K (t, s) (d s) := by
    have he := congrArg (fun f : C(ℝ, X) => f t) huv
    change u t - (∫ s in (0 : ℝ)..t, K (t, s) (u s)) =
      v t - (∫ s in (0 : ℝ)..t, K (t, s) (v s)) at he
    have hi (w : C(ℝ, X)) : IntervalIntegrable (fun s => K (t, s) (w s)) volume 0 t :=
      ((K.continuous.comp (continuous_const.prodMk continuous_id)).clm_apply w.continuous).intervalIntegrable 0 t
    change u t - v t = ∫ s in (0 : ℝ)..t, K (t, s) (u s - v s)
    simp_rw [map_sub]
    rw [intervalIntegral.integral_sub (hi u) (hi v)]
    exact sub_eq_sub_iff_sub_eq_sub.mp he
  have hi (n : ℕ) (t : ℝ) :
      volterraIterate d (fun t s => K (t, s)) (n + 1) t -
        volterraIterate d (fun t s => K (t, s)) n t = d t := by
    induction n generalizing t with
    | zero =>
      simp only [volterraIterate_succ, volterraIterate_zero, add_sub_cancel_left]
      exact (hhom t).symm
    | succ n ih =>
      rw [volterraIterate_succ d _ (n + 1), volterraIterate_succ d _ n,
        add_sub_add_left_eq_sub]
      have hInt (j : ℕ) : IntervalIntegrable
          (fun s => K (t, s) (volterraIterate d (fun t s => K (t, s)) j s)) volume 0 t :=
        ((K.continuous.comp (continuous_const.prodMk continuous_id)).clm_apply
          (continuous_volterraIterate d.continuous K.continuous j)).intervalIntegrable 0 t
      rw [← intervalIntegral.integral_sub (hInt (n + 1)) (hInt n)]
      simp_rw [← map_sub, ih]
      exact (hhom t).symm
  ext t
  have hs := summable_continuousVolterraIncrements K d t
  have hz : Tendsto (fun _ : ℕ => d t) atTop (nhds 0) := by
    simpa only [hi] using hs.tendsto_atTop_zero
  have hd : d t = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  exact sub_eq_zero.mp hd

/-- Every continuous history is the response to its explicitly recovered source. -/
theorem continuousVolterraResponse_source (K : C(ℝ × ℝ, X →L[ℝ] X)) (u : C(ℝ, X)) :
    continuousVolterraResponse K (continuousVolterraSource K u) = u := by
  apply continuousVolterraSource_injective K
  exact continuousVolterraSource_response K (continuousVolterraSource K u)

/-- The actual source operator is a linear equivalence on continuous histories. -/
def continuousVolterraSourceEquiv (K : C(ℝ × ℝ, X →L[ℝ] X)) : C(ℝ, X) ≃ₗ[ℝ] C(ℝ, X) where
  toFun := continuousVolterraSource K
  invFun := continuousVolterraResponse K
  left_inv := continuousVolterraResponse_source K
  right_inv := continuousVolterraSource_response K
  map_add' := continuousVolterraSource_add K
  map_smul' := fun c u => continuousVolterraSource_smul K u c

/-- Every continuous source and history are paired uniquely. -/
theorem continuousVolterraResponse_bijective (K : C(ℝ × ℝ, X →L[ℝ] X)) :
    Function.Bijective (continuousVolterraResponse K) :=
  (continuousVolterraSourceEquiv K).symm.bijective

/-- The existing Picard response respects source superposition. -/
theorem continuousVolterraResponse_add (K : C(ℝ × ℝ, X →L[ℝ] X)) (f g : C(ℝ, X)) :
    continuousVolterraResponse K (f + g) = continuousVolterraResponse K f + continuousVolterraResponse K g :=
  (continuousVolterraSourceEquiv K).symm.map_add f g

/-- The existing Picard response respects source amplitude scaling. -/
theorem continuousVolterraResponse_smul (K : C(ℝ × ℝ, X →L[ℝ] X)) (f : C(ℝ, X)) (c : ℝ) :
    continuousVolterraResponse K (c • f) = c • continuousVolterraResponse K f :=
  (continuousVolterraSourceEquiv K).symm.map_smul c f

/-- Finite baths have unique sources for all continuous histories, including resonant modes. -/
theorem finiteMemoryResponse_bijective {ι : Type*} [Fintype ι] (w : ι → ℝ≥0) (ω : ι → ℝ) :
    Function.Bijective (finiteMemoryResponse w ω) :=
  continuousVolterraResponse_bijective (finiteMemoryVolterraOperator w ω)

end
end GaloisForLFunctions.HTGeometry

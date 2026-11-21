import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.Itineraries

/-! # Shifting individual harmonic observation dates without enlarging the gate net -/
open Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.HarmonicRuns
noncomputable section
open SharpOccupation

/-- Affordable harmonics, with an independent fixed time offset at each observation. -/
def offsetRunSet {n m : ℕ} (H : selfAdjoint (Register n)) (s : ℕ) (ε : ℝ)
    (u : Fin m → ℝ) : Set ℝ :=
  {t | ∀ i : Fin m, ((i.val:ℝ)+1)*t+u i ∈ visitSet H s ε}

private def flow {n : ℕ} (H : selfAdjoint (Register n)) (t : ℝ) : Matrix.unitaryGroup (Fin n → Bool) ℂ :=
  ⟨unitaryEvolution H.val t,unitaryEvolution_mem_unitary H.2 t⟩

/-- At each harmonic an offset is absorbed into the target unitary by
right multiplication. Its location and size do not change the covering number. -/
theorem offset_run_subset_words {n m s : ℕ} (H : selfAdjoint (Register n)) (ε δ : ℝ)
    (u : Fin m → ℝ) (F : Finset (Matrix.unitaryGroup (Fin n → Bool) ℂ))
    (hcover : ∀ C : TwoQubitCircuit n, C.gateCount ≤ s → ∃ W ∈ F,
      ‖(C.eval : Register n)-(W : Register n)‖ ≤ δ) :
    ∃ W : (Fin m → F) → Fin m → Matrix.unitaryGroup (Fin n → Bool) ℂ,
      offsetRunSet H s ε u ⊆ ⋃ f, itinerary H (W f) (ε+δ) := by
  let W (f : Fin m → F) (i : Fin m) := (f i).val * flow H (-u i)
  refine ⟨W,?_⟩
  intro t ht
  let v (i : Fin m) := ((i.val:ℝ)+1)*t
  have hsel (i : Fin m) : ∃ w : F, ∃ c : ℂ, ‖c‖=1 ∧
      ‖unitaryEvolution H.val (v i+u i)-c • (w.val:Register n)‖ ≤ ε+δ := by
    obtain ⟨c,hc,C,hC,he⟩ := ht i
    obtain ⟨w,hw,hclose⟩ := hcover C hC
    refine ⟨⟨w,hw⟩,c,hc,(norm_sub_le_norm_sub_add_norm_sub _ (c • (C.eval : Register n)) _).trans
      (add_le_add he ?_)⟩
    rwa [←smul_sub,norm_smul,hc,one_mul]
  choose f c hc h using hsel
  refine mem_iUnion.mpr ⟨f,fun i => ⟨c i,hc i,?_⟩⟩
  have he := unitaryEvolution_sub_mul H (v i) (-u i)
  rw [sub_neg_eq_add] at he
  change ‖unitaryEvolution H.val (v i)-c i • ((f i).val.val*unitaryEvolution H.val (-u i))‖ ≤ _
  rw [←he,←Matrix.smul_mul,←Matrix.sub_mul,CStarRing.norm_mul_mem_unitary _ (unitaryEvolution_mem_unitary H.2 _)]
  exact h i

#print axioms offset_run_subset_words
end
end GaloisForLFunctions.HTGeometry.HarmonicRuns

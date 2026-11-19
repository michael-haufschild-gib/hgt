import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.CubicProbeExperimentDesign

/-!
# Four adaptive trials cannot identify an unknown squared component

Follow a deterministic strategy along zero responses. Its four frozen
measurements must be invertible on each four-dimensional model if the
strategy separates all signals. Each model can then produce the same
transcript (0,0,0,1). A common signal must be linear. Multiplying that
linear signal by x² minus the final squared x-coordinate produces a
nonzero coupling invisible to all four frozen trials.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.CubicRecovery.Design

/-- Arbitrary deterministic choices of the remaining input pairs given all
preceding scalar responses. No regularity of the decision functions is needed. -/
structure Strategy4 where
  first : ℝ × ℝ
  second : ℝ → ℝ × ℝ
  third : ℝ → ℝ → ℝ × ℝ
  fourth : ℝ → ℝ → ℝ → ℝ × ℝ

/-- Actual sequence of four measurements of a response function. -/
def transcript (T : Strategy4) (f : ℝ × ℝ → ℝ) : Fin 4 → ℝ :=
  let a := f T.first
  let b := f (T.second a)
  let c := f (T.third a b)
  ![a,b,c,f (T.fourth a b c)]

private def frozen (T : Strategy4) : Fin 4 → ℝ × ℝ :=
  ![T.first,T.second 0,T.third 0 0,T.fourth 0 0 0]

private def pulse (a : ℝ) : Fin 4 → ℝ := ![0,0,0,a]

private theorem frozen_transcript (T : Strategy4) (f : ℝ × ℝ → ℝ) (a : ℝ)
    (h : ∀ i, f (frozen T i) = pulse a i) : transcript T f = pulse a := by
  have h0 : f T.first=0 := h 0
  have h1 : f (T.second 0)=0 := h 1
  have h2 : f (T.third 0 0)=0 := h 2
  have h3 : f (T.fourth 0 0 0)=a := h 3
  simp only [transcript,h0,h1,h2,h3,pulse]

private def pack (c : Fin 4 → ℝ) : Row ℝ := ⟨c 0,c 1,c 2,c 3⟩

private def frozenMap (T : Strategy4) (b : Bool) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun c i := signal b (pack c) (frozen T i)
  map_add' c d := by funext i; simp only [signal,pack,response,Pi.add_apply]; ring
  map_smul' u c := by funext i; simp only [signal,pack,response,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

private theorem same_coefficients (b : Bool) (c d : Fin 4 → ℝ)
    (h : signal b (pack c) = signal b (pack d)) : c=d := by
  have he : measureRow b (pack c) = measureRow b (pack d) := by
    unfold measureRow
    congr 1
    · exact congrFun h (1,1)
    · exact congrFun h (1,-1)
    · exact congrFun h (2,2)
    · exact congrFun h (2,-2)
  have hh := congrArg recover he
  rw [recover_measure,recover_measure] at hh
  funext i
  fin_cases i
  · exact congrArg Row.linearX hh
  · exact congrArg Row.linearY hh
  · exact congrArg Row.cubicX hh
  · exact congrArg Row.cubicY hh

/-- No four-shot adaptive strategy separates all signals. Together with
the axis-selection construction this gives the exact adaptive threshold. -/
theorem four_adaptive_alias (T : Strategy4) :
    ∃ (b c : Bool) (r s : Row ℝ), transcript T (signal b r) = transcript T (signal c s) ∧
      signal b r ≠ signal c s := by
  classical
  by_contra! separates
  have inject (b : Bool) : Function.Injective (frozenMap T b) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    have hp : pulse 0 = 0 := by funext i; fin_cases i <;> rfl
    have zeroTranscript (v : Fin 4 → ℝ) (hv : frozenMap T b v=0) :
        transcript T (signal b (pack v)) = pulse 0 :=
      frozen_transcript T _ _ (fun i => congrFun (hv.trans hp.symm) i)
    exact same_coefficients b c 0 (separates b b _ _ ((zeroTranscript c hc).trans
      (zeroTranscript 0 (map_zero _)).symm))
  have surj (b : Bool) : Function.Surjective (frozenMap T b) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := frozenMap T b) rfl).mp (inject b)
  obtain ⟨u,hu⟩ := surj false (pulse 1)
  obtain ⟨v,hv⟩ := surj true (pulse 1)
  have eq := separates false true (pack u) (pack v) ((frozen_transcript T _ _ (fun i => congrFun hu i)).trans
    (frozen_transcript T _ _ (fun i => congrFun hv i)).symm)
  obtain ⟨_,_,u2,u3,_,_⟩ := (cross_model_eq_iff _ _).mp eq
  change u 2=0 at u2
  change u 3=0 at u3
  let ℓ := fun z : ℝ × ℝ => z.1*u 0+z.2*u 1
  have hp (i : Fin 4) : ℓ (frozen T i) = pulse 1 i := by
    have h := congrFun hu i
    change signal false (pack u) (frozen T i) = pulse 1 i at h
    simpa only [ℓ,signal,pack,response,Bool.false_eq_true,if_false,u2,u3,mul_zero,add_zero] using h
  let x := (frozen T 3).1
  let w : Fin 4 → ℝ := ![-x^2*u 0,-x^2*u 1,u 0,u 1]
  have factor (z : ℝ × ℝ) : signal false (pack w) z = (z.1^2-x^2)*ℓ z := by
    simp [signal,response,pack,w,ℓ]
    ring
  have hz : frozenMap T false w=0 := by
    funext i
    change signal false (pack w) (frozen T i)=0
    rw [factor,hp]
    fin_cases i <;> simp [pulse,x]
  have hw : w=0 := inject false (hz.trans (map_zero (frozenMap T false)).symm)
  have u0 : u 0=0 := congrFun hw 2
  have u1 : u 1=0 := congrFun hw 3
  have last := hp 3
  simp [ℓ,pulse,u0,u1] at last

#print axioms four_adaptive_alias
end GaloisForLFunctions.ExclusionOfTheCriticalState.CubicRecovery.Design

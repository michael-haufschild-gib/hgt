import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.CoupledCubicProbeRecovery

/-!
# Fixed and adaptive experiments for an unknown cubic coupling

The two wave couplings x²(cx+dy) and y²(cx+dy) agree on both diagonals.
Their difference space contains all four homogeneous cubics as well as both
linear terms. Six fixed trials identify the entire polynomial. Five fixed
trials always leave two different couplings indistinguishable. When a trial
may depend on earlier responses, one axis selected after the four diagonal
trials suffices.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.CubicRecovery.Design

/-- Response at a two-component input. -/
def signal (squareY : Bool) (r : Row ℝ) (z : ℝ × ℝ) := response squareY r z.1 z.2

/-- The difference space of the two possible models. Coordinates give the
two linear coefficients followed by those of x³, x²y, xy² and y³. -/
def oddCubic (c : Fin 6 → ℝ) (z : ℝ × ℝ) : ℝ :=
  z.1*c 0+z.2*c 1+z.1^2*(z.1*c 2+z.2*c 3)+z.2^2*(z.1*c 4+z.2*c 5)

/-- Four diagonal inputs and two single-component inputs. -/
def sixInputs : Fin 6 → ℝ × ℝ := ![(1,1),(1,-1),(2,2),(2,-2),(1,0),(0,1)]

/-- Diagonal polarization recovers the two linear terms and the sums of
cubic coefficients. The pure-axis readings separate each sum. -/
def reconstruct (z : Fin 6 → ℝ) : Fin 6 → ℝ :=
  let r := recover ⟨z 0,z 1,z 2,z 3⟩
  let x := z 4-r.linearX
  let y := z 5-r.linearY
  ![r.linearX,r.linearY,x,r.cubicY-y,r.cubicX-x,y]

theorem reconstruct_six (c : Fin 6 → ℝ) :
    reconstruct (fun i => oddCubic c (sixInputs i)) = c := by
  funext i
  fin_cases i <;> simp [reconstruct,recover,oddCubic,sixInputs] <;> ring

/-- Arbitrary six readings are realized by a unique linear-plus-cubic response. -/
theorem six_bijective : Function.Bijective (fun c i => oddCubic c (sixInputs i)) := by
  refine ⟨Function.LeftInverse.injective reconstruct_six,?_⟩
  apply Function.RightInverse.surjective (g := reconstruct)
  intro z
  funext i
  fin_cases i <;> simp [reconstruct,recover,oddCubic,sixInputs] <;> ring

private def putX (c : Fin 6 → ℝ) : Row ℝ := ⟨c 0,c 1,c 2,c 3⟩
private def putY (c : Fin 6 → ℝ) : Row ℝ := ⟨0,0,-c 4,-c 5⟩

private theorem subtract_models (c : Fin 6 → ℝ) (z : ℝ × ℝ) :
    signal false (putX c) z - signal true (putY c) z = oddCubic c z := by
  simp [signal,putX,putY,response,oddCubic]
  ring

private def fixedMap {k : ℕ} (shots : Fin k → ℝ × ℝ) : (Fin 6 → ℝ) →ₗ[ℝ] (Fin k → ℝ) where
  toFun c i := oddCubic c (shots i)
  map_add' c d := by funext i; simp only [oddCubic,Pi.add_apply]; ring
  map_smul' u c := by funext i; simp only [oddCubic,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

/-- Below six fixed inputs there is an explicit mathematical ambiguity:
one x² coupling and one y² coupling agree at every chosen input but differ
as response functions. -/
theorem fixed_design_alternative {k : ℕ} (shots : Fin k → ℝ × ℝ) :
    6 ≤ k ∨ ∃ r s : Row ℝ, (∀ i, signal false r (shots i) = signal true s (shots i)) ∧
      signal false r ≠ signal true s := by
  classical
  by_cases hk : 6 ≤ k
  · exact Or.inl hk
  right
  let L := fixedMap shots
  have hkern : ∃ c : Fin 6 → ℝ, c ≠ 0 ∧ L c = 0 := by
    by_contra! he
    have hker : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot'.mpr fun c hc => by
      by_contra hn
      exact he c hn hc
    have bound := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hker)
    exact hk (by simpa only [Module.finrank_pi,Fintype.card_fin] using bound)
  obtain ⟨c,hc,hL⟩ := hkern
  refine ⟨putX c,putY c,fun i => sub_eq_zero.mp ((subtract_models c _).trans (congrFun hL i)),?_⟩
  intro he
  apply hc
  apply six_bijective.injective
  funext i
  change oddCubic c (sixInputs i) = oddCubic 0 (sixInputs i)
  rw [← subtract_models,he,sub_self]
  simp [oddCubic]

private def encode (b : Bool) (r : Row ℝ) : Fin 6 → ℝ :=
  if b then ![r.linearX,r.linearY,0,0,r.cubicX,r.cubicY]
  else ![r.linearX,r.linearY,r.cubicX,r.cubicY,0,0]

private theorem encode_eval (b : Bool) (r : Row ℝ) (z : ℝ × ℝ) :
    oddCubic (encode b r) z = signal b r z := by cases b <;> simp [encode,oddCubic,signal,response]

/-- Globally coincident couplings with different squared components are
exactly the common linear signals. -/
theorem cross_model_eq_iff (r s : Row ℝ) : signal false r = signal true s ↔
    r.linearX=s.linearX ∧ r.linearY=s.linearY ∧ r.cubicX=0 ∧ r.cubicY=0 ∧ s.cubicX=0 ∧ s.cubicY=0 := by
  constructor
  · intro h
    have he : encode false r = encode true s := six_bijective.injective
      (funext fun i => (encode_eval false r _).trans ((congrFun h _).trans (encode_eval true s _).symm))
    exact ⟨congrFun he 0,congrFun he 1,congrFun he 2,congrFun he 3,(congrFun he 4).symm,(congrFun he 5).symm⟩
  · rintro ⟨h1,h2,h3,h4,h5,h6⟩
    funext z
    simp [signal,response,h1,h2,h3,h4,h5,h6]

/-- Choice of the fifth input from the recovered diagonal data. -/
def adaptiveAxis (r : Row ℝ) : ℝ × ℝ := if r.cubicX = 0 then (0,1) else (1,0)

/-- The fifth reading uses only information available from the preceding four. -/
def adaptiveFive (b : Bool) (r : Row ℝ) :=
  let d := measureRow b r
  (d,signal b r (adaptiveAxis (recover d)))

private theorem axis_distinguishes (r : Row ℝ)
    (h : signal false r (adaptiveAxis r) = signal true r (adaptiveAxis r)) :
    signal false r = signal true r := by
  by_cases hx : r.cubicX=0
  · have hy : r.cubicY=0 := by simpa [signal,response,adaptiveAxis,hx] using h.symm
    exact (cross_model_eq_iff r r).mpr ⟨rfl,rfl,hx,hy,hx,hy⟩
  · simp [signal,response,adaptiveAxis,hx] at h

/-- Five adaptive trials identify the response polynomial, even when the
squared component is unknown. -/
theorem adaptive_five_identifies (b c : Bool) (r s : Row ℝ) :
    adaptiveFive b r = adaptiveFive c s ↔ signal b r = signal c s := by
  constructor
  · intro h
    have hr := congrArg (fun z : Readings ℝ × ℝ => recover z.1) h
    change recover (measureRow b r) = recover (measureRow c s) at hr
    rw [recover_measure,recover_measure] at hr
    subst s
    have ha := congrArg Prod.snd h
    change signal b r (adaptiveAxis (recover (measureRow b r))) =
      signal c r (adaptiveAxis (recover (measureRow c r))) at ha
    rw [recover_measure,recover_measure] at ha
    cases b <;> cases c
    · rfl
    · exact axis_distinguishes r ha
    · exact (axis_distinguishes r ha.symm).symm
    · rfl
  · intro h
    have hd : measureRow b r = measureRow c s := by
      unfold measureRow
      congr 1
      · exact congrFun h (1,1)
      · exact congrFun h (1,-1)
      · exact congrFun h (2,2)
      · exact congrFun h (2,-2)
    simp only [adaptiveFive,hd,h]

#print axioms reconstruct_six
#print axioms six_bijective
#print axioms fixed_design_alternative
#print axioms cross_model_eq_iff
#print axioms adaptive_five_identifies
end GaloisForLFunctions.ExclusionOfTheCriticalState.CubicRecovery.Design

import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.MultiplexedPhases.ControlledNot

/-! # Linear gate cost for arbitrary diagonal phases, without ancillas -/
open Finset Matrix
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases
noncomputable section
variable {n : ℕ}

private def slice (f : Config n → ℝ) (j : Fin n) (b : Bool) (x : Config n) :=
  f (Function.update x j b)

/-- Removing a control splits an angle into its even and odd parts. -/
private theorem split_angle (f : Config n → ℝ) (j : Fin n) {S : Finset (Fin n)}
    (hf : DependsOn f (↑(insert j S) : Set (Fin n))) :
    ∃ a b : Config n → ℝ, DependsOn a (S:Set (Fin n)) ∧ DependsOn b (S:Set (Fin n)) ∧
      ∀ x, f x=a x+spin (x j)*b x := by
  let u := slice f j false
  let v := slice f j true
  have hs (bit : Bool) : DependsOn (slice f j bit) (S:Set (Fin n)) := by
    intro x y h
    apply hf
    intro i hi
    by_cases e : i=j
    · subst i; simp only [Function.update_self]
    · exact (Function.update_of_ne e _ _).trans
        ((h i ((mem_insert.mp hi).resolve_left e)).trans (Function.update_of_ne e _ _).symm)
  refine ⟨fun x => (u x+v x)/2,fun x => (u x-v x)/2,?_,?_,?_⟩
  · intro x y h
    change (u x+v x)/2=(u y+v y)/2
    rw [show u x=u y from hs false h,show v x=v y from hs true h]
  · intro x y h
    change (u x-v x)/2=(u y-v y)/2
    rw [show u x=u y from hs false h,show v x=v y from hs true h]
  · intro x
    change f x=(u x+v x)/2+spin (x j)*((u x-v x)/2)
    have he : slice f j (x j) x=f x := by simp [slice]
    cases hbit : x j with
    | false =>
      have hu : u x=f x := by simpa only [u,hbit] using he
      rw [hu]
      norm_num [spin]
      ring
    | true =>
      have hv : v x=f x := by simpa only [v,hbit] using he
      rw [hv]
      norm_num [spin]
      ring

/-- The two CNOTs conjugate the odd part. With j controls the
recurrence A(j+1)=2A(j)+2 and A(0)=1 gives 3·2ʲ−2 gates. -/
theorem target_rotation (hn : 2 ≤ n) (p : Fin n) (S : Finset (Fin n)) (hp : p∉S)
    (f : Config n → ℝ) (hf : DependsOn f (S:Set (Fin n))) :
    ∃ P : ℕ, P+2 ≤ 3*2^S.card ∧ Realizes P (phases fun x => spin (x p)*f x) := by
  induction S using Finset.induction_on generalizing f with
  | empty =>
    let t := f (fun _ => false)
    have hc (x) : f x=t := hf (by simp)
    exact ⟨1,by simp,by simpa only [hc] using onsite hn p t⟩
  | @insert j S hj ih =>
    have hps : p∉S := fun hm => hp (mem_insert_of_mem hm)
    have hjp : j≠p := fun e => hp (mem_insert.mpr (Or.inl e.symm))
    obtain ⟨a,b,ha,hb,hf⟩ := split_angle f j hf
    obtain ⟨A,hA,rA⟩ := ih hps a ha
    obtain ⟨B,hB,rB⟩ := ih hps b hb
    have hfactor : (fun x => spin (x p)*f x) =
        (fun x => spin (x p)*a x+spin (x p)*(spin (x j)*b x)) := by
      funext x; rw [hf x,mul_add]
    rw [hfactor,phases_add,card_insert_of_notMem hj,pow_succ]
    exact ⟨A+(1+B+1),by omega,rA.mul (control_sign hjp hps hb rB)⟩

/-- A diagonal angle depending on k physical wires needs at most
3(2ᵏ−1)−2k projective two-qubit gates on the original register. -/
theorem supported_angles (hn : 2 ≤ n) (S : Finset (Fin n)) (f : Config n → ℝ)
    (hf : DependsOn f (S:Set (Fin n))) :
    ∃ P : ℕ, P+(2*S.card+3) ≤ 3*2^S.card ∧ Realizes P (phases f) := by
  induction S using Finset.induction_on generalizing f with
  | empty =>
    let t := f (fun _ => false)
    let z := Complex.exp (-Complex.I*(t:ℂ))
    have hc (x) : f x=t := hf (by simp)
    have hz : ‖z‖=1 := by simp [z,Complex.norm_exp]
    refine ⟨0,by simp,z,hz,TwoQubitCircuit.one n,le_rfl,?_⟩
    rw [TwoQubitCircuit.one_eval]
    ext x y
    by_cases h : x=y
    · subst y; simp [phases,hc,z]
    · simp [phases,h]
  | @insert j S hj ih =>
    obtain ⟨a,b,ha,hb,hf⟩ := split_angle f j hf
    obtain ⟨A,hA,rA⟩ := ih a ha
    obtain ⟨B,hB,rB⟩ := target_rotation hn j S hj b hb
    rw [show f=(fun x => a x+spin (x j)*b x) from funext hf,phases_add,
      card_insert_of_notMem hj,pow_succ]
    exact ⟨A+B,by omega,rA.mul rB⟩

/-- Any diagonal unitary on the full register has an exact projective
circuit of at most three times the Hilbert dimension. The same bound
in terms of support size holds for phases depending on fewer wires. -/
theorem supported_phases (hn : 2 ≤ n) (S : Finset (Fin n)) (v : Config n → ℂ)
    (hv : ∀ x, ‖v x‖=1) (hs : DependsOn v (S:Set (Fin n))) :
    Realizes (2^S.card*3) (diagonal v) := by
  let f := fun x => -(v x).arg
  have hf : DependsOn f (S:Set (Fin n)) := fun _ _ h => congrArg (fun z : ℂ => -z.arg) (hs h)
  obtain ⟨P,hP,z,hz,C,hC,hfit⟩ := supported_angles hn S f hf
  have he x : Complex.exp (-Complex.I*(f x:ℂ))=v x := by
    have h := Complex.norm_mul_exp_arg_mul_I (v x)
    rw [hv,Complex.ofReal_one,one_mul] at h
    simpa [f,mul_comm] using h
  exact ⟨z,hz,C,by omega,by simpa only [phases,he] using hfit⟩

theorem full_register_phases (hn : 2 ≤ n) (v : Config n → ℂ) (hv : ∀ x, ‖v x‖=1) :
    Realizes (2^n*3) (diagonal v) := by
  simpa only [card_univ,Fintype.card_fin] using
    supported_phases hn univ v hv (by simpa only [coe_univ] using dependsOn_univ v)

#print axioms supported_phases
#print axioms full_register_phases
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases

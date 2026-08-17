import GaloisForLFunctions.HTGeometry.GeometricSkeletonBrownRamp

/-!
# The state-orbit hardening cone

Composing a preparation of an intermediate state with a uniform simulator of the remaining
evolution prepares the evolved state, with word lengths adding and errors adding.  Reading that
composition backwards turns a hard late endpoint into a hard early endpoint: the complexity at the
earlier time is at least the late separation minus the simulation cost of the elapsed increment.

The same composition applied to the seed itself shows that a hard endpoint forces its whole elapsed
evolution to be expensive to simulate: no fast simulator can coexist with an easily prepared seed
and a hard endpoint.
-/

namespace HTGeometry

noncomputable section

variable {X : Type*} [MetricSpace X] {Γ : Type*}

/-! ## Composition from an arbitrary intermediate state -/

/-- **The composition bound.**  A base state prepared to accuracy `epsBase` by `b` gates and a
uniform `gamma`-simulator of the elapsed evolution using `S` gates together prepare the evolved
state to accuracy `epsBase + gamma` using `b + S` gates. -/
theorem approxComplexity_evolved_le_add
    (act : Γ → X → X) (chi : X) (U : ℝ → X → X)
    (hUiso : ∀ u : ℝ, Isometry (U u))
    {epsBase gamma u : ℝ} {psi : X} {b S : ℕ}
    (hb : ∃ w : List Γ, w.length ≤ b ∧ dist psi (wordAct act w chi) ≤ epsBase)
    (hS : ∃ w : List Γ, w.length ≤ S ∧ ∀ x, dist (wordAct act w x) (U u x) ≤ gamma) :
    approxComplexity act chi (epsBase + gamma) (U u psi) ≤ b + S := by
  obtain ⟨w₁, hw₁, hd₁⟩ := hb
  obtain ⟨w₂, hw₂, hd₂⟩ := hS
  refine Nat.sInf_le ⟨w₂ ++ w₁, ?_, ?_⟩
  · rw [List.length_append]
    omega
  · rw [wordAct_append]
    have hstep : dist (U u psi) (U u (wordAct act w₁ chi)) ≤ epsBase := by
      rw [(hUiso u).dist_eq]
      exact hd₁
    have hsim : dist (U u (wordAct act w₁ chi)) (wordAct act w₂ (wordAct act w₁ chi)) ≤ gamma := by
      rw [dist_comm]
      exact hd₂ _
    have htri := dist_triangle (U u psi) (U u (wordAct act w₁ chi))
      (wordAct act w₂ (wordAct act w₁ chi))
    linarith

/-! ## Attaining the two infima -/

/-- A finite approximate complexity is attained by a word. -/
theorem exists_word_approxComplexity (act : Γ → X → X) (chi : X) (eps : ℝ) (x : X)
    (hne : {s : ℕ | ∃ w : List Γ, w.length ≤ s ∧ dist x (wordAct act w chi) ≤ eps}.Nonempty) :
    ∃ w : List Γ, w.length ≤ approxComplexity act chi eps x ∧
      dist x (wordAct act w chi) ≤ eps :=
  Nat.sInf_mem hne

/-- A finite uniform simulation complexity is attained by a word. -/
theorem exists_word_uniformSimComplexity (act : Γ → X → X) (U : ℝ → X → X) (gamma u : ℝ)
    (hne : {s : ℕ | ∃ w : List Γ, w.length ≤ s ∧
      ∀ x, dist (wordAct act w x) (U u x) ≤ gamma}.Nonempty) :
    ∃ w : List Γ, w.length ≤ uniformSimComplexity act U gamma u ∧
      ∀ x, dist (wordAct act w x) (U u x) ≤ gamma :=
  Nat.sInf_mem hne

/-! ## The backward cone -/

/-- **The robust hardening cone.**  If the endpoint at time `T` is hard at accuracy
`epsMinus + gamma`, then the endpoint at every earlier time `T - u` is hard at accuracy `epsMinus`
after subtracting only the cost of simulating the elapsed increment.  Locality enters solely
through that simulation cost. -/
theorem lt_add_uniformSimComplexity_of_lt_approxComplexity
    (act : Γ → X → X) (chi : X) (U : ℝ → X → X)
    (hUiso : ∀ u : ℝ, Isometry (U u))
    (hgroup : ∀ (a c : ℝ) (x : X), U a (U c x) = U (a + c) x)
    {epsMinus gamma T u : ℝ} {s : ℕ}
    (hearly : {k : ℕ | ∃ w : List Γ, w.length ≤ k ∧
      dist (U (T - u) chi) (wordAct act w chi) ≤ epsMinus}.Nonempty)
    (hsim : {k : ℕ | ∃ w : List Γ, w.length ≤ k ∧
      ∀ x, dist (wordAct act w x) (U u x) ≤ gamma}.Nonempty)
    (hhard : s < approxComplexity act chi (epsMinus + gamma) (U T chi)) :
    s < approxComplexity act chi epsMinus (U (T - u) chi)
        + uniformSimComplexity act U gamma u := by
  have hcomp := approxComplexity_evolved_le_add act chi U hUiso
    (epsBase := epsMinus) (gamma := gamma) (u := u) (psi := U (T - u) chi)
    (b := approxComplexity act chi epsMinus (U (T - u) chi))
    (S := uniformSimComplexity act U gamma u)
    (exists_word_approxComplexity act chi epsMinus (U (T - u) chi) hearly)
    (exists_word_uniformSimComplexity act U gamma u hsim)
  have hpoint : U u (U (T - u) chi) = U T chi := by
    rw [hgroup]
    congr 1
    ring
  rw [hpoint] at hcomp
  omega

/-- The signed form of the cone. -/
theorem sub_uniformSimComplexity_lt_approxComplexity
    (act : Γ → X → X) (chi : X) (U : ℝ → X → X)
    (hUiso : ∀ u : ℝ, Isometry (U u))
    (hgroup : ∀ (a c : ℝ) (x : X), U a (U c x) = U (a + c) x)
    {epsMinus gamma T u : ℝ} {s : ℕ}
    (hearly : {k : ℕ | ∃ w : List Γ, w.length ≤ k ∧
      dist (U (T - u) chi) (wordAct act w chi) ≤ epsMinus}.Nonempty)
    (hsim : {k : ℕ | ∃ w : List Γ, w.length ≤ k ∧
      ∀ x, dist (wordAct act w x) (U u x) ≤ gamma}.Nonempty)
    (hhard : s < approxComplexity act chi (epsMinus + gamma) (U T chi)) :
    (s : ℤ) - uniformSimComplexity act U gamma u
      < approxComplexity act chi epsMinus (U (T - u) chi) := by
  have h := lt_add_uniformSimComplexity_of_lt_approxComplexity act chi U hUiso hgroup
    hearly hsim hhard
  omega

/-! ## Hard endpoints force expensive simulation -/

/-- **An easy seed transfers all the hardness to the simulator.**  If the seed is prepared exactly
by `b` gates and the endpoint at time `T` is hard, then simulating the elapsed evolution to the
endpoint accuracy costs more than the separation minus `b`. -/
theorem lt_add_uniformSimComplexity_of_easy_seed
    (act : Γ → X → X) (chi : X) (U : ℝ → X → X)
    (hUiso : ∀ u : ℝ, Isometry (U u))
    {epsPlus T : ℝ} {psi : X} {b s : ℕ}
    (hseed : ∃ w : List Γ, w.length ≤ b ∧ dist psi (wordAct act w chi) ≤ 0)
    (hsim : {k : ℕ | ∃ w : List Γ, w.length ≤ k ∧
      ∀ x, dist (wordAct act w x) (U T x) ≤ epsPlus}.Nonempty)
    (hhard : s < approxComplexity act chi epsPlus (U T psi)) :
    s < b + uniformSimComplexity act U epsPlus T := by
  have hcomp := approxComplexity_evolved_le_add act chi U hUiso
    (epsBase := 0) (gamma := epsPlus) (u := T) (psi := psi) (b := b)
    (S := uniformSimComplexity act U epsPlus T) hseed
    (exists_word_uniformSimComplexity act U epsPlus T hsim)
  rw [zero_add] at hcomp
  omega

/-- The signed form of the seed bound. -/
theorem sub_lt_uniformSimComplexity_of_easy_seed
    (act : Γ → X → X) (chi : X) (U : ℝ → X → X)
    (hUiso : ∀ u : ℝ, Isometry (U u))
    {epsPlus T : ℝ} {psi : X} {b s : ℕ}
    (hseed : ∃ w : List Γ, w.length ≤ b ∧ dist psi (wordAct act w chi) ≤ 0)
    (hsim : {k : ℕ | ∃ w : List Γ, w.length ≤ k ∧
      ∀ x, dist (wordAct act w x) (U T x) ≤ epsPlus}.Nonempty)
    (hhard : s < approxComplexity act chi epsPlus (U T psi)) :
    (s : ℤ) - b < uniformSimComplexity act U epsPlus T := by
  have h := lt_add_uniformSimComplexity_of_easy_seed act chi U hUiso hseed hsim hhard
  omega

end

end HTGeometry

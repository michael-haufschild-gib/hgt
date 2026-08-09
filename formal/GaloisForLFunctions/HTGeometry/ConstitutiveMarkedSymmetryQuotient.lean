import Mathlib

/-!
# Marked-symmetry experiment quotient, recurrence, and lift

A compact group `H` acts on a space of laws.  A passive source law is invariant under all of `H`,
so nothing passive sees the group; a marked intervention law `ν` has stabilizer `K`, and the exact
experiment phase space is the homogeneous quotient `H ⧸ K`.

* `smul_eq_smul_iff_mem_stabilizer` and `markedResponse` — two transformations have the same marked
  response exactly when they lie in the same right `K`-coset, so the response descends to an
  injection of `H ⧸ K`, and `markedResponse_isClosedEmbedding` upgrades it to an embedding because
  `H ⧸ K` is compact and the law space is Hausdorff;
* `oneParameter_recurrence` — a continuous one-parameter subgroup of a compact group returns to
  every neighbourhood of the identity at arbitrarily large times, and
  `oneParameter_periodic` gives exact periodicity when it meets `K`;
* `liftPath_one_eq_of_nullhomotopicRel` and `monodromy_eq_self_iff_eq_one` — the response lift of a
  loop is closed as soon as the loop is null-homotopic, and for a universal (simply connected)
  covering the converse holds: the lift closes **exactly** when the class in the fundamental group
  is trivial;
* `halfTurnSubgroup`, `stabilizer_markedAxis`, `responseQuotientEquiv`, `halfTurnPath`,
  `responseLoop`, `liftedAngle`, `closed_response_open_lift` — the exact instantiation
  `H = SO(2)`, `K = {±1} = Stab(marked axis)`, `H/K ≅ S¹`: the half-turn intervention path projects
  to a generating response loop whose angle lift escapes through distinct deck translations;
* `character_norm_one` — a unitary character has constant positive modulus, so positive character
  data cannot carry phase history.
-/

namespace GaloisForLFunctions.HTGeometry

open Topology Pointwise

section ExperimentQuotient

variable {H : Type*} [Group H] {P : Type*} [MulAction H P]

/-- **Two transformations have the same marked response exactly on a right coset of the
stabilizer.** -/
theorem smul_eq_smul_iff_mem_stabilizer (ν : P) (g h : H) :
    g • ν = h • ν ↔ h⁻¹ * g ∈ MulAction.stabilizer H ν := by
  rw [MulAction.mem_stabilizer_iff, mul_smul]
  constructor
  · intro hgh
    rw [hgh, ← mul_smul, inv_mul_cancel, one_smul]
  · intro hgh
    have := congrArg (fun x => h • x) hgh
    simpa [← mul_smul] using this

/-- **Passive invisibility.**  An invariant source law is unchanged by every transformation. -/
theorem passive_invisible {μ : P} (hμ : ∀ h : H, h • μ = μ) (h : H) : h • μ = μ := hμ h

variable [TopologicalSpace H] [TopologicalSpace P]

/-- The marked response map on the experiment quotient. -/
def markedResponse (ν : P) : H ⧸ MulAction.stabilizer H ν → P :=
  Quotient.lift (fun g : H => g • ν) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ MulAction.stabilizer H ν := QuotientGroup.leftRel_apply.mp hab
    exact ((smul_eq_smul_iff_mem_stabilizer ν b a).mpr hab').symm)

omit [TopologicalSpace H] [TopologicalSpace P] in
@[simp] theorem markedResponse_mk (ν : P) (g : H) :
    markedResponse ν (QuotientGroup.mk g : H ⧸ MulAction.stabilizer H ν) = g • ν := rfl

omit [TopologicalSpace H] [TopologicalSpace P] in
/-- **The marked response is injective on the experiment quotient.** -/
theorem markedResponse_injective (ν : P) :
    Function.Injective (markedResponse (H := H) ν) := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with
  | H g =>
    induction y using QuotientGroup.induction_on with
    | H h =>
      rw [markedResponse_mk, markedResponse_mk] at hxy
      exact QuotientGroup.eq.mpr (by
        have := (smul_eq_smul_iff_mem_stabilizer ν h g).mp hxy.symm
        simpa using this)

variable [ContinuousSMul H P]

theorem markedResponse_continuous (ν : P) : Continuous (markedResponse (H := H) ν) := by
  refine continuous_quot_lift _ ?_
  exact (continuous_id.smul continuous_const)

/-- **The experiment quotient embeds in the law space.**  For a compact group and a Hausdorff law
space the marked response is a closed embedding of `H ⧸ K`. -/
theorem markedResponse_isClosedEmbedding [CompactSpace H] [T2Space P] (ν : P) :
    Topology.IsClosedEmbedding (markedResponse (H := H) ν) :=
  (markedResponse_continuous ν).isClosedEmbedding (markedResponse_injective ν)

end ExperimentQuotient

section Recurrence

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [TopologicalSpace H] [IsTopologicalGroup H] in
theorem oneParameter_zero {γ : ℝ → H} (hhom : ∀ s t, γ (s + t) = γ s * γ t) : γ 0 = 1 := by
  have h := hhom 0 0
  rw [add_zero] at h
  have h2 : (γ 0)⁻¹ * γ 0 = (γ 0)⁻¹ * (γ 0 * γ 0) := by rw [← h]
  simpa using h2.symm

omit [TopologicalSpace H] [IsTopologicalGroup H] in
theorem oneParameter_sub {γ : ℝ → H} (hhom : ∀ s t, γ (s + t) = γ s * γ t) (a b : ℝ) :
    γ a * (γ b)⁻¹ = γ (a - b) := by
  have h := hhom (a - b) b
  rw [sub_add_cancel] at h
  rw [h]
  group

/-- **Recurrence of a one-parameter subgroup in a compact group.**  It returns to every
neighbourhood of the identity at arbitrarily large times. -/
theorem oneParameter_recurrence [CompactSpace H] {γ : ℝ → H} (_hcont : Continuous γ)
    (hhom : ∀ s t, γ (s + t) = γ s * γ t) {U : Set H} (hU : U ∈ 𝓝 (1 : H)) {M : ℝ} (hM : 0 < M) :
    ∃ t : ℝ, M ≤ t ∧ γ t ∈ U := by
  classical
  obtain ⟨W, hW, hWU⟩ : ∃ W ∈ 𝓝 (1 : H), W * W ⊆ U := by
    obtain ⟨W, hW, hWU⟩ := exists_nhds_one_split hU
    exact ⟨W, hW, by rintro x ⟨a, ha, b, hb, rfl⟩; exact hWU a ha b hb⟩
  set V : Set H := W ∩ (fun x : H => x⁻¹) ⁻¹' W with hV
  have hVnhds : V ∈ 𝓝 (1 : H) := by
    refine Filter.inter_mem hW ?_
    have hc : ContinuousAt (fun x : H => x⁻¹) 1 := (continuous_inv (G := H)).continuousAt
    exact hc.preimage_mem_nhds (by simpa using hW)
  have hVU : ∀ a ∈ V, ∀ b ∈ V, a * b⁻¹ ∈ U := by
    intro a ha b hb
    exact hWU ⟨a, ha.1, b⁻¹, hb.2, rfl⟩
  -- an open cover of `H` by right translates of `V`
  set nbhd : H → Set H := fun g => (fun x : H => x * g⁻¹) ⁻¹' V with hnbhd
  have hnbhd_mem : ∀ g : H, nbhd g ∈ 𝓝 g := by
    intro g
    have hc : ContinuousAt (fun x : H => x * g⁻¹) g := (continuous_mul_const g⁻¹).continuousAt
    refine hc.preimage_mem_nhds ?_
    simpa using hVnhds
  obtain ⟨S, -, hS⟩ := isCompact_univ.elim_nhds_subcover nbhd (fun g _ => hnbhd_mem g)
  -- pigeonhole on the sample times `M, 2M, …`
  have hchoose : ∀ k : ℕ, ∃ g ∈ S, γ (M * k) ∈ nbhd g := by
    intro k
    have hmem : γ (M * k) ∈ ⋃ g ∈ S, nbhd g := hS (Set.mem_univ _)
    simpa using hmem
  choose f hfS hfmem using hchoose
  have hcard : S.card < (Finset.Icc 1 (S.card + 1)).card := by
    rw [Nat.card_Icc]
    omega
  obtain ⟨k₁, hk₁, k₂, hk₂, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := f) (fun k _ => hfS k)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨M * (k₂ - k₁ : ℕ), ?_, ?_⟩
    · have h1 : 1 ≤ (k₂ - k₁ : ℕ) := by omega
      have h1' : (1 : ℝ) ≤ ((k₂ - k₁ : ℕ) : ℝ) := by exact_mod_cast h1
      nlinarith [hM, h1']
    · have hsub : γ (M * (k₂ : ℕ)) * (γ (M * (k₁ : ℕ)))⁻¹ = γ (M * (k₂ - k₁ : ℕ)) := by
        rw [oneParameter_sub hhom]
        congr 1
        have : ((k₂ - k₁ : ℕ) : ℝ) = (k₂ : ℝ) - (k₁ : ℝ) := by
          have : k₁ ≤ k₂ := le_of_lt hlt
          push_cast [Nat.cast_sub this]
          ring
        rw [this]
        ring
      rw [← hsub]
      have e1 : γ (M * (k₂ : ℕ)) * (f k₂)⁻¹ ∈ V := hfmem k₂
      have e2 : γ (M * (k₁ : ℕ)) * (f k₁)⁻¹ ∈ V := hfmem k₁
      rw [heq] at e2
      have := hVU _ e1 _ e2
      have hrw : (γ (M * (k₂ : ℕ)) * (f k₂)⁻¹) * (γ (M * (k₁ : ℕ)) * (f k₂)⁻¹)⁻¹
          = γ (M * (k₂ : ℕ)) * (γ (M * (k₁ : ℕ)))⁻¹ := by group
      rwa [hrw] at this
  · refine ⟨M * (k₁ - k₂ : ℕ), ?_, ?_⟩
    · have h1 : 1 ≤ (k₁ - k₂ : ℕ) := by omega
      have h1' : (1 : ℝ) ≤ ((k₁ - k₂ : ℕ) : ℝ) := by exact_mod_cast h1
      nlinarith [hM, h1']
    · have hsub : γ (M * (k₁ : ℕ)) * (γ (M * (k₂ : ℕ)))⁻¹ = γ (M * (k₁ - k₂ : ℕ)) := by
        rw [oneParameter_sub hhom]
        congr 1
        have : ((k₁ - k₂ : ℕ) : ℝ) = (k₁ : ℝ) - (k₂ : ℝ) := by
          have : k₂ ≤ k₁ := le_of_lt hlt
          push_cast [Nat.cast_sub this]
          ring
        rw [this]
        ring
      rw [← hsub]
      have e1 : γ (M * (k₁ : ℕ)) * (f k₁)⁻¹ ∈ V := hfmem k₁
      have e2 : γ (M * (k₂ : ℕ)) * (f k₂)⁻¹ ∈ V := hfmem k₂
      rw [← heq] at e2
      have := hVU _ e1 _ e2
      have hrw : (γ (M * (k₁ : ℕ)) * (f k₁)⁻¹) * (γ (M * (k₂ : ℕ)) * (f k₁)⁻¹)⁻¹
          = γ (M * (k₁ : ℕ)) * (γ (M * (k₂ : ℕ)))⁻¹ := by group
      rwa [hrw] at this

omit [TopologicalSpace H] [IsTopologicalGroup H] in
/-- **Exact periodicity when the path meets the stabilizer.** -/
theorem oneParameter_periodic {P : Type*} [MulAction H P] {γ : ℝ → H}
    (hhom : ∀ s t, γ (s + t) = γ s * γ t) (ν : P) {T : ℝ}
    (hT : γ T ∈ MulAction.stabilizer H ν) (t : ℝ) :
    γ (t + T) • ν = γ t • ν := by
  rw [hhom, mul_smul, hT]

end Recurrence

section PositiveErasure

/-- **A unitary character has constant positive modulus.**  Positive character data therefore
cannot carry phase history. -/
theorem character_norm_one {H : Type*} [Group H] (χ : H →* Circle) (h : H) :
    ‖(χ h : ℂ)‖ = 1 := by
  simp

end PositiveErasure

section UniversalLift

open unitInterval

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- **A null-homotopic response loop lifts to a closed path.**  If the response loop is homotopic
rel endpoints to the constant loop, then its lift to any covering of the response space returns to
its starting point. -/
theorem liftPath_one_eq_of_nullhomotopicRel (cov : IsCoveringMap p) {γ : C(I, X)} {e : E}
    (γ_0 : γ 0 = p e)
    (h : γ.HomotopicRel (ContinuousMap.const I (p e)) {0, 1}) :
    cov.liftPath γ e γ_0 1 = e := by
  rw [cov.liftPath_apply_one_eq_of_homotopicRel h e γ_0 rfl, cov.liftPath_const rfl]
  rfl

/-- **Closed lift ⟺ trivial class, for a universal covering.**  When the covering space is simply
connected the monodromy of a class fixes a point of the fibre exactly when the class is trivial;
so the lifted history closes exactly when the response loop is null-homotopic. -/
theorem monodromy_eq_self_iff_eq_one {G : Type*} [Group G] [MulAction G E]
    (hp : IsQuotientCoveringMap p G) [SimplyConnectedSpace E] {x : X} (e : p ⁻¹' {x})
    (γ : FundamentalGroup X x) :
    hp.isCoveringMap.monodromy γ e = e ↔ γ = 1 := by
  constructor
  · intro h
    have hid : hp.isCoveringMap.monodromy γ = id := (hp.monodromy_eq_id_iff e).mpr h
    apply hp.monodromyPerm_injective
    ext e'
    rw [map_one]
    simp only [IsCoveringMap.coe_monodromyPerm, hid, id_eq, Equiv.Perm.coe_one]
  · rintro rfl
    rw [FundamentalGroup.one_def]
    exact congrFun hp.isCoveringMap.monodromy_refl e

end UniversalLift

section HalfTurnModel

open unitInterval

/-- The intervention stabilizer of the exact instantiation: the half-turn subgroup of the rotation
group, realised as the kernel of squaring. -/
noncomputable def halfTurnSubgroup : Subgroup Circle := (powMonoidHom 2 : Circle →* Circle).ker

/-- The half-turn subgroup is exactly `{1, -1}`. -/
theorem mem_halfTurnSubgroup_iff (z : Circle) : z ∈ halfTurnSubgroup ↔ z = 1 ∨ z = -1 := by
  simp only [halfTurnSubgroup, MonoidHom.mem_ker, powMonoidHom_apply]
  constructor
  · intro h
    have hz : (z : ℂ) ^ 2 = 1 := by
      have := congrArg (Subtype.val) h
      simpa using this
    have h2 : ((z : ℂ) - 1) * ((z : ℂ) + 1) = 0 := by linear_combination hz
    rcases mul_eq_zero.mp h2 with h3 | h3
    · left; apply Subtype.ext; push_cast; linear_combination h3
    · right; apply Subtype.ext; push_cast; linear_combination h3
  · rintro (rfl | rfl)
    · exact one_pow 2
    · exact neg_one_sq

/-- In the angle coordinate the stabilizer is exactly `πℤ`. -/
theorem exp_mem_halfTurnSubgroup_iff (t : ℝ) :
    Circle.exp t ∈ halfTurnSubgroup ↔ ∃ k : ℤ, t = k * Real.pi := by
  simp only [halfTurnSubgroup, MonoidHom.mem_ker, powMonoidHom_apply]
  rw [pow_two, ← Circle.exp_add, ← two_mul, Circle.exp_eq_one]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by linarith⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩

/-- The marked intervention datum: the real axis, the support of the law obtained after the
intervention that pins the first source coordinate. -/
def markedAxis : Set ℂ := Set.range (fun r : ℝ => (r : ℂ))

/-- **The half-turn subgroup is the stabilizer of the marked datum.**  This is clause (1) of the
theorem in the exact instantiation: `K = Stab_H(ν)`. -/
theorem stabilizer_markedAxis : MulAction.stabilizer Circle markedAxis = halfTurnSubgroup := by
  ext z
  rw [MulAction.mem_stabilizer_iff, mem_halfTurnSubgroup_iff]
  constructor
  · intro h
    have h1 : (z : ℂ) ∈ markedAxis := by
      rw [← h]
      exact ⟨(1 : ℂ), ⟨1, by norm_num⟩, by simp⟩
    obtain ⟨r, hr⟩ := h1
    have hn : ‖(z : ℂ)‖ = 1 := by simp
    rw [← hr] at hn
    have habs : |r| = 1 := by simpa using hn
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp habs with h2 | h2
    · left; apply Subtype.ext; push_cast; rw [← hr, h2]; norm_num
    · right; apply Subtype.ext; push_cast; rw [← hr, h2]; norm_num
  · rintro (rfl | rfl)
    · exact one_smul _ _
    · ext w
      simp only [markedAxis, Set.mem_range]
      constructor
      · rintro ⟨u, ⟨r, rfl⟩, rfl⟩
        exact ⟨-r, by simp⟩
      · rintro ⟨r, rfl⟩
        exact ⟨((-r : ℝ) : ℂ), ⟨-r, rfl⟩, by simp⟩

/-- Squaring is surjective on the rotation group. -/
theorem sq_surjective_circle : Function.Surjective (powMonoidHom 2 : Circle →* Circle) := by
  intro w
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective w
  refine ⟨Circle.exp (θ / 2), ?_⟩
  simp only [powMonoidHom_apply]
  rw [pow_two, ← Circle.exp_add]
  congr 1
  ring

/-- **The experiment quotient of the exact instantiation is again a circle**, with the projection
given by the squaring map — the double cover `S¹ → S¹ ≅ ℝP¹`. -/
noncomputable def responseQuotientEquiv : Circle ⧸ halfTurnSubgroup ≃* Circle :=
  QuotientGroup.quotientKerEquivOfSurjective _ sq_surjective_circle

@[simp] theorem responseQuotientEquiv_mk (z : Circle) :
    responseQuotientEquiv (QuotientGroup.mk z) = z ^ 2 := rfl

/-- The half-turn intervention path: it starts at the identity and ends inside the stabilizer. -/
noncomputable def halfTurnPath : C(I, Circle) :=
  ⟨fun t => Circle.exp (Real.pi * t), by fun_prop⟩

@[simp] theorem halfTurnPath_zero : halfTurnPath 0 = 1 := by
  simp [halfTurnPath]

@[simp] theorem halfTurnPath_one : halfTurnPath 1 = -1 := by
  show Circle.exp (Real.pi * ((1 : I) : ℝ)) = -1
  rw [Set.Icc.coe_one, mul_one]
  apply Subtype.ext
  rw [Circle.coe_exp]
  push_cast
  rw [Complex.exp_pi_mul_I]

/-- The half-turn path lands in the stabilizer, so its projected response is a loop. -/
theorem halfTurnPath_one_mem : halfTurnPath 1 ∈ halfTurnSubgroup := by
  rw [halfTurnPath_one, mem_halfTurnSubgroup_iff]
  exact Or.inr rfl

/-- The projected response loop, wound `n` times around the experiment quotient. -/
noncomputable def responseLoop (n : ℤ) : C(I, Circle) :=
  ⟨fun t => Circle.exp (2 * Real.pi * n * t), by fun_prop⟩

/-- The candidate angle lift of the response loop. -/
noncomputable def angleLift (n : ℤ) : C(I, ℝ) :=
  ⟨fun t => 2 * Real.pi * n * t, by fun_prop⟩

theorem responseLoop_zero_eq (n : ℤ) : responseLoop n 0 = Circle.exp 0 := by
  show Circle.exp (2 * Real.pi * n * ((0 : I) : ℝ)) = Circle.exp 0
  norm_num

/-- **The response is closed.** -/
@[simp] theorem responseLoop_one (n : ℤ) : responseLoop n 1 = 1 := by
  show Circle.exp (2 * Real.pi * n * ((1 : I) : ℝ)) = 1
  rw [Set.Icc.coe_one, mul_one, Circle.exp_eq_one]
  exact ⟨n, by ring⟩

/-- The projection of the half-turn path is the once-around response loop: the quotient map
`H → H/K ≅ S¹` is squaring. -/
theorem responseLoop_eq_sq (t : I) : responseLoop 1 t = halfTurnPath t ^ 2 := by
  show Circle.exp (2 * Real.pi * ((1 : ℤ) : ℝ) * t) = Circle.exp (Real.pi * t) ^ 2
  rw [pow_two, ← Circle.exp_add]
  congr 1
  push_cast
  ring

/-- The lifted angle history of the response loop, in the universal cover `ℝ` of the response
circle. -/
noncomputable def liftedAngle (n : ℤ) : C(I, ℝ) :=
  Circle.isCoveringMap_exp.liftPath (responseLoop n) 0 (responseLoop_zero_eq n)

theorem liftedAngle_eq (n : ℤ) : liftedAngle n = angleLift n := by
  refine ((Circle.isCoveringMap_exp.eq_liftPath_iff' _).mpr ⟨?_, ?_⟩).symm
  · funext t; rfl
  · show 2 * Real.pi * n * ((0 : I) : ℝ) = 0
    norm_num

@[simp] theorem liftedAngle_zero (n : ℤ) : liftedAngle n 0 = 0 := by
  rw [liftedAngle_eq]
  show 2 * Real.pi * n * ((0 : I) : ℝ) = 0
  norm_num

/-- **The lifted history is not closed: it ends at `2πn`.** -/
@[simp] theorem liftedAngle_one (n : ℤ) : liftedAngle n 1 = 2 * Real.pi * n := by
  rw [liftedAngle_eq]
  show 2 * Real.pi * n * ((1 : I) : ℝ) = 2 * Real.pi * n
  rw [Set.Icc.coe_one, mul_one]

theorem liftedAngle_one_ne_zero {n : ℤ} (hn : n ≠ 0) : liftedAngle n 1 ≠ 0 := by
  rw [liftedAngle_one]
  exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (Int.cast_ne_zero.mpr hn)

/-- **Distinct winding numbers escape through distinct deck translations.** -/
theorem liftedAngle_one_injective : Function.Injective fun n : ℤ => liftedAngle n 1 := by
  intro m n hmn
  simp only [liftedAngle_one] at hmn
  have h2 : (2 * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hc : (m : ℝ) = (n : ℝ) := mul_left_cancel₀ h2 hmn
  exact_mod_cast hc

/-- The lifted endpoint is the `n`-th power of the generating deck translation by `2π`. -/
theorem liftedAngle_one_zsmul (n : ℤ) : liftedAngle n 1 = n • (2 * Real.pi) := by
  rw [liftedAngle_one, zsmul_eq_mul]
  ring

/-- **The response loop is not null-homotopic once it winds.** -/
theorem responseLoop_not_nullhomotopicRel {n : ℤ} (hn : n ≠ 0) :
    ¬ (responseLoop n).HomotopicRel (ContinuousMap.const I (Circle.exp 0)) {0, 1} := by
  intro h
  exact liftedAngle_one_ne_zero hn
    (liftPath_one_eq_of_nullhomotopicRel Circle.isCoveringMap_exp (responseLoop_zero_eq n) h)

/-- **Theorem 3 in the exact instantiation.**  The marked half-turn intervention gives a response
that is exactly closed in the experiment quotient, an angle history that is open, endpoints that
escape through distinct deck translations by `2π`, and hence a response loop with a nontrivial
homotopy class. -/
theorem closed_response_open_lift {n : ℤ} (hn : n ≠ 0) :
    responseLoop n 0 = responseLoop n 1 ∧
      liftedAngle n 0 = 0 ∧
      liftedAngle n 1 = n • (2 * Real.pi) ∧
      liftedAngle n 1 ≠ liftedAngle n 0 ∧
      Function.Injective (fun m : ℤ => liftedAngle m 1) ∧
      ¬ (responseLoop n).HomotopicRel (ContinuousMap.const I (Circle.exp 0)) {0, 1} := by
  refine ⟨?_, liftedAngle_zero n, liftedAngle_one_zsmul n, ?_, liftedAngle_one_injective,
    responseLoop_not_nullhomotopicRel hn⟩
  · rw [responseLoop_one, responseLoop_zero_eq, Circle.exp_zero]
  · rw [liftedAngle_zero]
    exact liftedAngle_one_ne_zero hn

end HalfTurnModel

end GaloisForLFunctions.HTGeometry

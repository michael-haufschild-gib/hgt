import Mathlib

/-!
# Line directions of a closed additive subgroup

A closed additive subgroup `P` of a finite-dimensional real normed space splits into a linear part
and a discrete part.  The linear part is realized here without any choice as

`lineDirections P = {x | forall t : R, t • x in P}`,

the set of directions along which `P` contains the whole real line.  It is a submodule, it is
contained in `P`, and the two structural facts are:

* `exists_unit_mem_lineDirections` -- if nonzero elements of `P` accumulate at the origin then `P`
  contains a whole line.  The unit vectors of an accumulating sequence subconverge on the sphere,
  and integer multiples chosen by a floor function converge to an arbitrary point of the limiting
  line, which closedness then puts in `P`.
* `exists_pos_forall_mem_lineDirections` -- consequently `P` is discrete modulo its line
  directions: some ball around the origin meets `P` only inside `lineDirections P`.  A linear
  complement turns the accumulation hypothesis into a line lying in the complement, which meets the
  line directions only at zero.

Discreteness in this separated form is equivalent to discreteness of the image of `P` in the
quotient by its linear part, since the quotient distance from `x` to `lineDirections P` is realized
by translating `x` by an element of `P`.
-/

open Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The directions along which an additive subgroup contains the entire real line. -/
def lineDirections (P : AddSubgroup V) : Submodule ℝ V where
  carrier := {x | ∀ t : ℝ, t • x ∈ P}
  add_mem' := by
    intro x y hx hy t
    have h := P.add_mem (hx t) (hy t)
    rwa [← smul_add] at h
  zero_mem' := by
    intro t
    simp
  smul_mem' := by
    intro c x hx t
    have h := hx (t * c)
    rwa [mul_smul] at h

theorem mem_lineDirections {P : AddSubgroup V} {x : V} :
    x ∈ lineDirections P ↔ ∀ t : ℝ, t • x ∈ P := Iff.rfl

theorem lineDirections_le (P : AddSubgroup V) {x : V} (hx : x ∈ lineDirections P) : x ∈ P := by
  simpa using hx 1

/-- **A closed subgroup whose nonzero elements accumulate at the origin contains a line.** -/
theorem exists_unit_mem_lineDirections [FiniteDimensional ℝ V]
    {P : AddSubgroup V} (hP : IsClosed (P : Set V))
    {p : ℕ → V} (hmem : ∀ n, p n ∈ P) (hne : ∀ n, p n ≠ 0)
    (hlim : Tendsto p atTop (𝓝 0)) :
    ∃ u : V, ‖u‖ = 1 ∧ u ∈ lineDirections P := by
  have hnormpos : ∀ n, (0 : ℝ) < ‖p n‖ := fun n => norm_pos_iff.mpr (hne n)
  set q : ℕ → V := fun n => ‖p n‖⁻¹ • p n with hqdef
  have hqnorm : ∀ n, ‖q n‖ = 1 := by
    intro n
    simp only [hqdef, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hnormpos n).ne'
  have hqsphere : ∀ n, q n ∈ Metric.sphere (0 : V) 1 := by
    intro n
    simpa [Metric.mem_sphere, dist_zero_right] using hqnorm n
  have hcompact : IsCompact (Metric.sphere (0 : V) 1) := isCompact_sphere 0 1
  obtain ⟨u, hu, φ, hφ, hconv⟩ := hcompact.tendsto_subseq hqsphere
  have hunorm : ‖u‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hu
  refine ⟨u, hunorm, ?_⟩
  intro t
  have hrlim : Tendsto (fun k => ‖p (φ k)‖) atTop (𝓝 0) := by
    have h := (hlim.comp hφ.tendsto_atTop).norm
    simpa using h
  have hscal : Tendsto (fun k => ((⌊t / ‖p (φ k)‖⌋ : ℤ) : ℝ) * ‖p (φ k)‖) atTop (𝓝 t) := by
    have hbd : ∀ k, ‖((⌊t / ‖p (φ k)‖⌋ : ℤ) : ℝ) * ‖p (φ k)‖ - t‖ ≤ ‖p (φ k)‖ := by
      intro k
      set r : ℝ := ‖p (φ k)‖ with hrdef
      have hr0 : 0 < r := hnormpos (φ k)
      have h1 : ((⌊t / r⌋ : ℤ) : ℝ) ≤ t / r := Int.floor_le _
      have h2 : t / r < ((⌊t / r⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
      have h1' : ((⌊t / r⌋ : ℤ) : ℝ) * r ≤ t := (le_div_iff₀ hr0).mp h1
      have h2' : t < ((⌊t / r⌋ : ℤ) : ℝ) * r + r := by
        have h := (div_lt_iff₀ hr0).mp h2
        have hexp : (((⌊t / r⌋ : ℤ) : ℝ) + 1) * r = ((⌊t / r⌋ : ℤ) : ℝ) * r + r := by ring
        linarith
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hz := squeeze_zero_norm hbd hrlim
    have hz' := hz.add_const t
    simpa using hz'
  have hvec : Tendsto (fun k => (((⌊t / ‖p (φ k)‖⌋ : ℤ) : ℝ) * ‖p (φ k)‖) • q (φ k)) atTop
      (𝓝 (t • u)) := hscal.smul hconv
  have hmemk : ∀ k, (((⌊t / ‖p (φ k)‖⌋ : ℤ) : ℝ) * ‖p (φ k)‖) • q (φ k) ∈ P := by
    intro k
    have hrewrite : (((⌊t / ‖p (φ k)‖⌋ : ℤ) : ℝ) * ‖p (φ k)‖) • q (φ k)
        = (⌊t / ‖p (φ k)‖⌋ : ℤ) • p (φ k) := by
      have hnz : ‖p (φ k)‖ ≠ 0 := (hnormpos (φ k)).ne'
      simp only [hqdef, smul_smul]
      rw [mul_assoc, mul_inv_cancel₀ hnz, mul_one, Int.cast_smul_eq_zsmul]
    rw [hrewrite]
    exact P.zsmul_mem (hmem _) _
  exact hP.mem_of_tendsto hvec (Eventually.of_forall hmemk)

/-- **A closed subgroup is discrete modulo its line directions.** -/
theorem exists_pos_forall_mem_lineDirections [FiniteDimensional ℝ V]
    {P : AddSubgroup V} (hP : IsClosed (P : Set V)) :
    ∃ ε > 0, ∀ x ∈ P, ‖x‖ < ε → x ∈ lineDirections P := by
  obtain ⟨F, hF⟩ := (lineDirections P).exists_isCompl
  set Q : AddSubgroup V := P ⊓ F.toAddSubgroup with hQdef
  have hmemQ : ∀ x : V, x ∈ Q ↔ x ∈ P ∧ x ∈ F := by
    intro x
    rw [hQdef, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup]
  have hQclosed : IsClosed (Q : Set V) := by
    have hFclosed : IsClosed (F : Set V) := F.closed_of_finiteDimensional
    have hcoe : (Q : Set V) = (P : Set V) ∩ (F : Set V) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_inter_iff]
      exact hmemQ x
    rw [hcoe]
    exact hP.inter hFclosed
  -- A line inside `Q` would lie in both the line directions and their complement.
  have hQnoline : ∀ u : V, ‖u‖ = 1 → u ∉ lineDirections Q := by
    intro u hu hmem
    have huP : u ∈ lineDirections P := fun t => ((hmemQ _).mp (hmem t)).1
    have huF : u ∈ F := ((hmemQ u).mp (lineDirections_le Q hmem)).2
    have hbot : u ∈ lineDirections P ⊓ F := ⟨huP, huF⟩
    rw [hF.inf_eq_bot, Submodule.mem_bot] at hbot
    rw [hbot] at hu
    simp at hu
  -- Hence the origin is isolated in `Q`.
  have hQiso : ∃ ε > 0, ∀ x ∈ Q, ‖x‖ < ε → x = 0 := by
    by_contra hcon
    push Not at hcon
    have hchoice : ∀ n : ℕ, ∃ x, x ∈ Q ∧ ‖x‖ < 1 / (n + 1 : ℝ) ∧ x ≠ 0 := by
      intro n
      obtain ⟨x, hxQ, hxn, hx0⟩ := hcon (1 / (n + 1 : ℝ)) (by positivity)
      exact ⟨x, hxQ, hxn, hx0⟩
    choose p hpQ hpn hp0 using hchoice
    have hplim : Tendsto p atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => (hpn n).le) tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨u, hu1, hu2⟩ := exists_unit_mem_lineDirections hQclosed hpQ hp0 hplim
    exact hQnoline u hu1 hu2
  obtain ⟨ε, hε0, hε⟩ := hQiso
  -- Transport the isolation back through the projection onto the complement.
  set π : V →ₗ[ℝ] V := F.projection (lineDirections P) hF.symm with hπdef
  have hπcont : Continuous π := LinearMap.continuous_of_finiteDimensional π
  have hπ0 : π 0 = 0 := map_zero π
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp (hπcont.continuousAt (x := (0 : V))) ε hε0
  refine ⟨δ, hδ0, ?_⟩
  intro x hxP hxδ
  have hsplit : ((lineDirections P).projection F hF) x + π x = x :=
    Submodule.projection_add_projection_eq_self hF x
  have hρmem : ((lineDirections P).projection F hF) x ∈ lineDirections P :=
    Submodule.projection_apply_mem hF x
  have hπF : π x ∈ F := Submodule.projection_apply_mem hF.symm x
  have hπP : π x ∈ P := by
    rw [hπdef, Submodule.projection_eq_self_sub_projection hF x]
    exact P.sub_mem hxP (lineDirections_le P hρmem)
  have hπsmall : ‖π x‖ < ε := by
    have h := hδ (show dist x (0 : V) < δ by simpa [dist_zero_right] using hxδ)
    simpa [hπ0, dist_zero_right] using h
  have hπzero : π x = 0 := hε (π x) ((hmemQ _).mpr ⟨hπP, hπF⟩) hπsmall
  have hxeq : x = ((lineDirections P).projection F hF) x := by
    have h := hsplit
    rw [hπzero, add_zero] at h
    exact h.symm
  rw [hxeq]
  exact hρmem

end GaloisForLFunctions.HTGeometry

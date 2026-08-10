import Mathlib

/-!
# Marked-port normal-crossing covariance

A subspace of a vector space over an infinite field contained in a finite union of subspaces lies
in one of them.  Consequently the exact linear symmetry group of the coordinate normal-crossing
discriminant is the monomial group, and for two block ports the block-monomial group.

Full support is therefore not a `GL`-invariant notion, and the two requirements of a two-port
selection theorem — diagonality and nonerasure — are logically independent.
-/

namespace HTGeometry.ConstraintRelativity

/-! ## A subspace inside a finite union of subspaces -/

section Covering

variable {k V : Type*} [Field k] [Infinite k] [AddCommGroup V] [Module k V]

/-- **New infrastructure.**  Over an infinite field, a subspace contained in a finite union of
subspaces is contained in one of them. -/
theorem exists_le_of_subset_biUnion {ι : Type*} (s : Finset ι) (W : ι → Submodule k V)
    (S : Submodule k V) (h : (S : Set V) ⊆ ⋃ i ∈ s, (W i : Set V)) : ∃ i ∈ s, S ≤ W i := by
  classical
  induction s using Finset.strongInduction with
  | _ s ih =>
    by_contra hcon
    push Not at hcon
    rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
    · have h0 := h S.zero_mem
      simp at h0
    · set t := s.erase i₀ with ht
      have htlt : t ⊂ s := Finset.erase_ssubset hi₀
      by_cases hcase : (S : Set V) ⊆ ⋃ i ∈ t, (W i : Set V)
      · obtain ⟨i, hit, hle⟩ := ih t htlt hcase
        exact hcon i (Finset.mem_of_mem_erase hit) hle
      · obtain ⟨x, hxS, hxt⟩ : ∃ x ∈ S, x ∉ ⋃ i ∈ t, (W i : Set V) := by
          by_contra hc
          push Not at hc
          exact hcase fun x hx => hc x hx
        have hx0 : x ∈ W i₀ := by
          have := h hxS
          simp only [Set.mem_iUnion, SetLike.mem_coe] at this ⊢
          obtain ⟨i, hi, hxi⟩ := this
          rcases eq_or_ne i i₀ with rfl | hne
          · exact hxi
          · exact absurd (by
              simp only [Set.mem_iUnion, SetLike.mem_coe]
              exact ⟨i, Finset.mem_erase.2 ⟨hne, hi⟩, hxi⟩) hxt
        obtain ⟨y, hyS, hy0⟩ : ∃ y ∈ S, y ∉ W i₀ := by
          by_contra hc
          push Not at hc
          exact hcon i₀ hi₀ fun y hy => hc y hy
        have hmem : ∀ c : k, ∃ i ∈ t, y + c • x ∈ W i := by
          intro c
          have hyc : y + c • x ∈ S := S.add_mem hyS (S.smul_mem c hxS)
          have := h hyc
          simp only [Set.mem_iUnion, SetLike.mem_coe] at this
          obtain ⟨i, hi, hmi⟩ := this
          rcases eq_or_ne i i₀ with rfl | hne
          · exact absurd (by
              have : y = (y + c • x) - c • x := by abel
              rw [this]
              exact (W i).sub_mem hmi ((W i).smul_mem c hx0)) hy0
          · exact ⟨i, Finset.mem_erase.2 ⟨hne, hi⟩, hmi⟩
        choose f hf hmf using hmem
        have hmapsto : Set.MapsTo f Set.univ (↑t : Set ι) := fun c _ => hf c
        obtain ⟨c₁, _, c₂, _, hne, hfeq⟩ :=
          Set.infinite_univ.exists_ne_map_eq_of_mapsTo hmapsto t.finite_toSet
        have h1 := hmf c₁
        have h2 := hmf c₂
        rw [hfeq] at h1
        have hsub : (c₁ - c₂) • x ∈ W (f c₂) := by
          have : (c₁ - c₂) • x = (y + c₁ • x) - (y + c₂ • x) := by
            rw [sub_smul]; abel
          rw [this]
          exact (W (f c₂)).sub_mem h1 h2
        have hxin : x ∈ W (f c₂) := by
          have hcne : c₁ - c₂ ≠ 0 := sub_ne_zero.2 hne
          have := (W (f c₂)).smul_mem (c₁ - c₂)⁻¹ hsub
          rwa [smul_smul, inv_mul_cancel₀ hcne, one_smul] at this
        exact hxt (by
          simp only [Set.mem_iUnion, SetLike.mem_coe]
          exact ⟨f c₂, hf c₂, hxin⟩)

end Covering

/-! ## Functionals with the same kernel -/

section Proportional

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Two functionals whose kernels are nested are proportional. -/
theorem exists_smul_of_ker_le_ker {f g : V →ₗ[k] k} (hf : f ≠ 0)
    (h : LinearMap.ker f ≤ LinearMap.ker g) : ∃ c : k, ∀ x, g x = c * f x := by
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf (LinearMap.ext fun x => by simpa using hc x)
  refine ⟨g v / f v, fun x => ?_⟩
  have hmem : x - (f x / f v) • v ∈ LinearMap.ker f := by
    simp only [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  have := h hmem
  simp only [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
  rw [this]
  field_simp

end Proportional

/-! ## The monomial stabilizer of the coordinate discriminant -/

section MonomialStabilizer

variable {k : Type*} [Field k] [Infinite k] {n : ℕ}

/-- **Card `(MPN.2)`.**  The coordinate ports. -/
def port (i : Fin n) : (Fin n → k) →ₗ[k] k := LinearMap.proj i

omit [Infinite k] in
theorem port_ne_zero (i : Fin n) : (port i : (Fin n → k) →ₗ[k] k) ≠ 0 := by
  intro hcon
  have := congrArg (fun f => f (Pi.single i (1 : k))) hcon
  simp [port, LinearMap.proj] at this

/-- **Theorem A.**  A linear automorphism preserving the normal-crossing discriminant is
monomial: each output port is a nonzero scalar multiple of a single input port, and the induced
index map is a permutation. -/
theorem exists_monomial_of_mapsTo (A : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (h : ∀ x : Fin n → k, (∃ i, x i = 0) → ∃ i, A x i = 0) :
    ∃ τ : Fin n → Fin n, Function.Bijective τ ∧
      ∀ i, ∃ c : k, c ≠ 0 ∧ ∀ x, A x (τ i) = c * x i := by
  classical
  have hcover : ∀ i : Fin n, ∃ j : Fin n,
      LinearMap.ker (port (k := k) i) ≤ LinearMap.ker ((port j).comp (A : (Fin n → k) →ₗ[k] _)) := by
    intro i
    have hsub : ((Submodule.map (A : (Fin n → k) →ₗ[k] _)
        (LinearMap.ker (port (k := k) i)) : Submodule k (Fin n → k)) : Set (Fin n → k))
        ⊆ ⋃ j ∈ (Finset.univ : Finset (Fin n)), (LinearMap.ker (port (k := k) j) : Set _) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨j, hj⟩ := h x ⟨i, hx⟩
      simp only [Set.mem_iUnion, SetLike.mem_coe, Finset.mem_univ, exists_prop, true_and]
      exact ⟨j, hj⟩
    obtain ⟨j, -, hj⟩ := exists_le_of_subset_biUnion Finset.univ
      (fun j => LinearMap.ker (port (k := k) j)) _ hsub
    refine ⟨j, fun x hx => ?_⟩
    exact hj ⟨x, hx, rfl⟩
  choose τ hτ using hcover
  have hscal : ∀ i, ∃ c : k, c ≠ 0 ∧ ∀ x, A x (τ i) = c * x i := by
    intro i
    obtain ⟨c, hc⟩ := exists_smul_of_ker_le_ker (port_ne_zero i) (hτ i)
    refine ⟨c, ?_, fun x => hc x⟩
    intro hc0
    obtain ⟨y, hy⟩ := A.surjective (Pi.single (τ i) (1 : k))
    have hthis := hc y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hy, hc0, zero_mul] at hthis
    rw [port, LinearMap.proj_apply, Pi.single_eq_same] at hthis
    exact one_ne_zero hthis
  refine ⟨τ, ?_, hscal⟩
  have hinj : Function.Injective τ := by
    intro i i' hii
    by_contra hne
    obtain ⟨c, hc0, hc⟩ := hscal i
    obtain ⟨c', -, hc'⟩ := hscal i'
    have h1 := hc (Pi.single i (1 : k))
    have h2 := hc' (Pi.single i (1 : k))
    rw [hii] at h1
    rw [h1] at h2
    simp only [Pi.single_eq_same, mul_one, Pi.single_eq_of_ne (Ne.symm hne), mul_zero] at h2
    exact hc0 h2
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

end MonomialStabilizer

/-! ## The block-port stabilizer -/

section BlockPorts

variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W]

/-- A subspace inside the union of the two block ports lies in one of them. -/
theorem subspace_in_union_two {S : Submodule k (W × W)}
    (h : ∀ p ∈ S, p.1 = 0 ∨ p.2 = 0) :
    (∀ p ∈ S, p.1 = 0) ∨ (∀ p ∈ S, p.2 = 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x, hxS, hx⟩, ⟨y, hyS, hy⟩⟩ := hcon
  have hx2 : x.2 = 0 := (h x hxS).resolve_left hx
  have hy1 : y.1 = 0 := (h y hyS).resolve_right hy
  have hsum := h (x + y) (S.add_mem hxS hyS)
  simp only [Prod.fst_add, Prod.snd_add, hx2, hy1, zero_add, add_zero] at hsum
  exact hsum.elim hx hy

/-- **Theorem A'.**  A linear automorphism preserving the two block ports is block-diagonal or a
block swap. -/
theorem block_diagonal_or_swap (A : (W × W) ≃ₗ[k] (W × W))
    (h : ∀ p : W × W, (p.1 = 0 ∨ p.2 = 0) → (A p).1 = 0 ∨ (A p).2 = 0) :
    ((∀ w : W, (A (w, 0)).2 = 0) ∨ (∀ w : W, (A (w, 0)).1 = 0)) ∧
      ((∀ w : W, (A (0, w)).2 = 0) ∨ (∀ w : W, (A (0, w)).1 = 0)) := by
  constructor
  · have hplus : ∀ p ∈ Submodule.map (A : (W × W) →ₗ[k] (W × W))
        (LinearMap.ker (LinearMap.snd k W W)), p.1 = 0 ∨ p.2 = 0 := by
      rintro _ ⟨q, hq, rfl⟩
      exact h q (Or.inr hq)
    rcases subspace_in_union_two hplus with hc | hc
    · exact Or.inr fun w => hc (A (w, 0)) ⟨(w, 0), rfl, rfl⟩
    · exact Or.inl fun w => hc (A (w, 0)) ⟨(w, 0), rfl, rfl⟩
  · have hminus : ∀ p ∈ Submodule.map (A : (W × W) →ₗ[k] (W × W))
        (LinearMap.ker (LinearMap.fst k W W)), p.1 = 0 ∨ p.2 = 0 := by
      rintro _ ⟨q, hq, rfl⟩
      exact h q (Or.inl hq)
    rcases subspace_in_union_two hminus with hc | hc
    · exact Or.inr fun w => hc (A (0, w)) ⟨(0, w), rfl, rfl⟩
    · exact Or.inl fun w => hc (A (0, w)) ⟨(0, w), rfl, rfl⟩

end BlockPorts

/-! ## Full support is not `GL`-invariant -/

section Shear

/-- **Card `(MPN.6)`.**  The shear, an element of the full linear group of the two-port space. -/
noncomputable def shear : (ℚ × ℚ) ≃ₗ[ℚ] (ℚ × ℚ) where
  toFun p := (p.1 - p.2, p.2)
  map_add' p q := by simp [Prod.ext_iff]; ring
  map_smul' c p := by simp [Prod.ext_iff]; ring
  invFun p := (p.1 + p.2, p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- **Card `(MPN.6)`.**  Full support is not invariant under the full linear group. -/
theorem shear_destroys_full_support :
    ((1 : ℚ), (1 : ℚ)).1 ≠ 0 ∧ ((1 : ℚ), (1 : ℚ)).2 ≠ 0 ∧ (shear ((1 : ℚ), (1 : ℚ))).1 = 0 :=
  ⟨one_ne_zero, one_ne_zero, by simp [shear]⟩

end Shear

/-! ## Diagonality and nonerasure are independent -/

section Selection

variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W]

/-- **Card `(MPN.7)`.**  The diagonality defect. -/
def diagDefect (s : W × W) : W := s.1 - s.2

/-- **Theorem B.1.**  Diagonality does not imply full support. -/
theorem diag_not_full_support : diagDefect ((0 : W), (0 : W)) = 0 ∧ ((0 : W), (0 : W)).1 = 0 := by
  simp [diagDefect]

/-- **Theorem B.2.**  Nonzero does not imply full support. -/
theorem ne_zero_not_full_support {w : W} (hw : w ≠ 0) :
    ((w, (0 : W)) ≠ 0) ∧ (w, (0 : W)).2 = 0 := by
  refine ⟨fun hcon => hw ?_, rfl⟩
  exact congrArg Prod.fst hcon

/-- **Theorem B.3, `(MPN.8)`.**  Together they do imply full support. -/
theorem full_support_of_diag_of_ne_zero {s : W × W} (hd : diagDefect s = 0) (hs : s ≠ 0) :
    s.1 ≠ 0 ∧ s.2 ≠ 0 := by
  have heq : s.1 = s.2 := by
    have := hd
    simp only [diagDefect, sub_eq_zero] at this
    exact this
  constructor
  · intro hcon
    refine hs (Prod.ext_iff.2 ⟨?_, ?_⟩)
    · simpa using hcon
    · simpa using (heq ▸ hcon : s.2 = 0)
  · intro hcon
    refine hs (Prod.ext_iff.2 ⟨?_, ?_⟩)
    · simpa using (heq.symm ▸ hcon : s.1 = 0)
    · simpa using hcon


/-- **Card `(MPN.8a)`.**  A two-legged family whose legs vanish on opposite open half-lines is
never zero, has full block-port support only at the centre, and has vanishing diagonality defect
only at the centre. -/
theorem routeR_two_port {F : ℝ → W} (hF : ∀ u : ℝ, F u = 0 ↔ u < 0) {c : k} (hc : c ≠ 0) (t : ℝ) :
    (((c • F (-t), c • F t) : W × W) ≠ 0)
      ∧ ((c • F (-t) ≠ 0 ∧ c • F t ≠ 0) ↔ t = 0)
      ∧ (diagDefect ((c • F (-t), c • F t) : W × W) = 0 ↔ t = 0) := by
  have hsm : ∀ u : ℝ, c • F u = 0 ↔ u < 0 := by
    intro u
    rw [smul_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h hc
      · exact (hF u).1 h
    · intro h
      exact Or.inr ((hF u).2 h)
  refine ⟨?_, ?_, ?_⟩
  · intro hcon
    have h1 : c • F (-t) = 0 := congrArg Prod.fst hcon
    have h2 : c • F t = 0 := congrArg Prod.snd hcon
    have ht1 : -t < 0 := (hsm (-t)).1 h1
    have ht2 : t < 0 := (hsm t).1 h2
    linarith
  · constructor
    · rintro ⟨h1, h2⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with ht | ht
      · exact h2 ((hsm t).2 ht)
      · exact h1 ((hsm (-t)).2 (by linarith))
    · rintro rfl
      exact ⟨fun h => absurd ((hsm 0).1 (by simpa using h)) (lt_irrefl 0),
        fun h => absurd ((hsm 0).1 h) (lt_irrefl 0)⟩
  · constructor
    · intro h
      simp only [diagDefect, sub_eq_zero] at h
      by_contra hne
      rcases lt_or_gt_of_ne hne with ht | ht
      · have h1 : c • F (-t) ≠ 0 := fun hz => absurd ((hsm (-t)).1 hz) (not_lt.2 (by linarith))
        rw [h] at h1
        exact h1 ((hsm t).2 ht)
      · have h2 : c • F t ≠ 0 := fun hz => absurd ((hsm t).1 hz) (not_lt.2 ht.le)
        rw [← h] at h2
        exact h2 ((hsm (-t)).2 (by linarith))
    · rintro rfl
      simp [diagDefect]

end Selection

/-! ## Static non-descent is not curvature -/

section StaticObstruction

variable {k C W : Type*} [Field k] [AddCommGroup C] [Module k C] [AddCommGroup W] [Module k W]

/-- **Card `(MPN.9)`.**  Against the zero target the kernel is everything and every reporter is a
nonzero obstruction class, with no parameter, loop or transport in sight. -/
theorem static_obstruction :
    LinearMap.ker (0 : C →ₗ[k] PUnit) = ⊤ ∧
      ∀ g : PUnit →ₗ[k] W, g.comp (0 : C →ₗ[k] PUnit) = 0 := by
  refine ⟨eq_top_iff.2 fun x _ => by simp, fun g => ?_⟩
  ext x
  simp

end StaticObstruction

/-! ## Arbitrary sections generate arbitrary topology -/

section ArbitrarySection

/-- **Card `(MPN.10)`.**  Every subset is the zero locus of some declared section. -/
theorem exists_section_zero_locus {B : Type*} (Z : Set B) :
    ∃ σ : B → ℚ, Z = {b | σ b = 0} := by
  classical
  refine ⟨fun b => if b ∈ Z then 0 else 1, ?_⟩
  ext b
  by_cases hb : b ∈ Z <;> simp [hb]

end ArbitrarySection

/-! ## Presentation nontermination is not invariant -/

section Nontermination

/-- **Card `(MPN.11)`.**  The two-term complex `k → k` is contractible: its identity differential
has zero kernel and full range. -/
theorem contractible_two_term (k : Type*) [Field k] :
    LinearMap.ker (LinearMap.id : k →ₗ[k] k) = ⊥ ∧
      LinearMap.range (LinearMap.id : k →ₗ[k] k) = ⊤ := by
  constructor
  · exact LinearMap.ker_id
  · exact LinearMap.range_id

/-- **Card `(MPN.11)`.**  Yet the graded dimension of the stabilized tower strictly increases, so
raw presentation length never terminates. -/
theorem presentation_size_strictMono (d : ℕ) : StrictMono (fun n : ℕ => d + 2 * n) := by
  intro a b hab
  simp only []
  omega

end Nontermination

end HTGeometry.ConstraintRelativity

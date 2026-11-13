import GaloisForLFunctions.GaloisTheoryOfZeros.TheTransportOfAZeroDependsOnlyOnTheHomotopyClass

/-!
# The monodromy over a union of two regions comes from the regions

Transport of zeros along forward paths is multiplicative for the concatenation of paths, so
the forward monodromy satisfies a van Kampen law that needs no homotopy.

* `IsForwardPath.fibreEquiv`: the transport along a forward path as a bijection of the end
  fibres. It is multiplicative for concatenation (`IsForwardPath.fibreEquiv_join`) and inverts
  under reversal (`IsForwardPath.fibreEquiv_reverse`); the transports along the parts of one
  path compose (`IsForwardPath.arcEquiv_trans`).
* `LoopsIn A h N`: every forward loop inside `A` based at `h` has its transport in the subgroup
  `N` of the permutations of the fibre over `h`.
* **Gluing** (`loopsIn_union`). Let `A₁`, `A₂` be open, each joined to `h` by forward paths,
  with `LoopsIn A₁ h N` and `LoopsIn A₂ h N`. Suppose that over every time `x` of `A₁ ∩ A₂`
  there are paths from `h` to `x`, one inside `A₁` and one inside `A₂`, whose transports differ
  by an element of `N`. Then `LoopsIn (A₁ ∪ A₂) h N`.

  Proof: cut the loop into parts, each inside one region. The part of the loop up to a cut
  point, closed by any path back to `h` inside a region that contains the cut point, has its
  transport in `N`: passing one part multiplies by the transport of a loop inside one region
  and by a change of the return path, which lies in `N` by the junction hypothesis.
* Over a convex set of forward times without branch times `LoopsIn` holds for every `N`
  (`loopsIn_of_convex`).
-/

open Complex Set Metric
open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-- The fibre of the heat cover over the time `τ`: the zeros of `H_τ`. -/
abbrev Fibre (τ : ℂ) : Type := {z : ℂ // complexHeat τ z = 0}

variable {γ : ℝ → ℂ}

/-! ## Transport as a bijection of fibres -/

/-- The transport along a forward path from `τ` to `τ'` as a bijection of the fibres. -/
def IsForwardPath.fibreEquiv (hγ : IsForwardPath γ) {τ τ' : ℂ} (h0 : γ 0 = τ) (h1 : γ 1 = τ') :
    Fibre τ ≃ Fibre τ' :=
  (hγ.exists_fibreEquiv h0 h1).choose

theorem IsForwardPath.transports_fibreEquiv (hγ : IsForwardPath γ) {τ τ' : ℂ} (h0 : γ 0 = τ)
    (h1 : γ 1 = τ') (p : Fibre τ) : Transports γ p.1 (hγ.fibreEquiv h0 h1 p).1 :=
  (hγ.exists_fibreEquiv h0 h1).choose_spec p

theorem IsForwardPath.fibreEquiv_eq (hγ : IsForwardPath γ) {τ τ' : ℂ} (h0 : γ 0 = τ)
    (h1 : γ 1 = τ') {p : Fibre τ} {q : Fibre τ'} (h : Transports γ p.1 q.1) :
    hγ.fibreEquiv h0 h1 p = q :=
  Subtype.ext (hγ.transports_unique (hγ.transports_fibreEquiv h0 h1 p) h)

/-- Transport along a concatenation is the composition of the transports. -/
theorem IsForwardPath.fibreEquiv_join {γ₁ γ₂ : ℝ → ℂ} (h₁ : IsForwardPath γ₁)
    (h₂ : IsForwardPath γ₂) {τ τ' τ'' : ℂ} (e0 : γ₁ 0 = τ) (e1 : γ₁ 1 = τ') (f0 : γ₂ 0 = τ')
    (f1 : γ₂ 1 = τ'') (hj : IsForwardPath (pathJoin γ₁ γ₂)) (j0 : pathJoin γ₁ γ₂ 0 = τ)
    (j1 : pathJoin γ₁ γ₂ 1 = τ'') :
    hj.fibreEquiv j0 j1 = (h₁.fibreEquiv e0 e1).trans (h₂.fibreEquiv f0 f1) :=
  Equiv.ext fun p => hj.fibreEquiv_eq j0 j1
    ((h₁.transports_fibreEquiv e0 e1 p).trans (h₂.transports_fibreEquiv f0 f1 _))

/-- Transport along the reversed path is the inverse transport. -/
theorem IsForwardPath.fibreEquiv_reverse (hγ : IsForwardPath γ) {τ τ' : ℂ} (h0 : γ 0 = τ)
    (h1 : γ 1 = τ') (hr : IsForwardPath (pathRev γ)) (r0 : pathRev γ 0 = τ')
    (r1 : pathRev γ 1 = τ) : hr.fibreEquiv r0 r1 = (hγ.fibreEquiv h0 h1).symm :=
  Equiv.ext fun q => hr.fibreEquiv_eq r0 r1 (by
    have := (hγ.transports_fibreEquiv h0 h1 ((hγ.fibreEquiv h0 h1).symm q)).symm
    rwa [Equiv.apply_symm_apply] at this)

/-- Transport along a constant path does not move a zero. -/
theorem IsForwardPath.fibreEquiv_const_apply {τ τ₁ τ₂ : ℂ} (hc : IsForwardPath fun _ : ℝ => τ)
    (e0 : τ = τ₁) (e1 : τ = τ₂) (p : Fibre τ₁) : (hc.fibreEquiv e0 e1 p).1 = p.1 := by
  subst e0
  exact hc.transports_unique (hc.transports_fibreEquiv rfl e1 p) (Transports.refl p.2)

theorem IsForwardPath.fibreEquiv_const_symm_apply {τ τ₁ τ₂ : ℂ}
    (hc : IsForwardPath fun _ : ℝ => τ) (e0 : τ = τ₁) (e1 : τ = τ₂) (q : Fibre τ₂) :
    ((hc.fibreEquiv e0 e1).symm q).1 = q.1 := by
  have := hc.fibreEquiv_const_apply e0 e1 ((hc.fibreEquiv e0 e1).symm q)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

/-! ## Parts of a path -/

/-- The part of a path between the parameters `a` and `b`, parametrized by `[0, 1]`. -/
def subPath (γ : ℝ → ℂ) (a b : ℝ) (s : ℝ) : ℂ := γ (a + (b - a) * s)

theorem subPath_zero (γ : ℝ → ℂ) (a b : ℝ) : subPath γ a b 0 = γ a := by
  rw [subPath, mul_zero, add_zero]

theorem subPath_one (γ : ℝ → ℂ) (a b : ℝ) : subPath γ a b 1 = γ b := by
  rw [subPath, mul_one, add_sub_cancel]

theorem subPath_zero_one (γ : ℝ → ℂ) : subPath γ 0 1 = γ := by
  funext s
  rw [subPath, sub_zero, one_mul, zero_add]

theorem mapsTo_affine_Icc {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    MapsTo (fun s : ℝ => a + (b - a) * s) (Icc 0 1) (Icc 0 1) := fun s hs =>
  ⟨by nlinarith [mul_nonneg (sub_nonneg.2 hs.2) ha.1, mul_nonneg hs.1 hb.1],
    by nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 ha.2),
      mul_nonneg hs.1 (sub_nonneg.2 hb.2)]⟩

theorem IsForwardPath.sub (hγ : IsForwardPath γ) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) : IsForwardPath (subPath γ a b) :=
  ⟨hγ.continuousOn.comp (by fun_prop : Continuous fun s : ℝ => a + (b - a) * s).continuousOn
      (mapsTo_affine_Icc ha hb),
    fun _ hs => hγ.re_pos _ (mapsTo_affine_Icc ha hb hs),
    fun _ hs => hγ.simple _ (mapsTo_affine_Icc ha hb hs)⟩

/-- A lift of a path transports its value at `a` to its value at `b` along the part of the
path between `a` and `b`. -/
theorem IsZeroLift.transports_subPath {z : ℝ → ℂ} (hz : IsZeroLift γ 1 z) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    Transports (subPath γ a b) (z a) (z b) :=
  ⟨fun s => z (a + (b - a) * s),
    ⟨hz.continuousOn.comp (by fun_prop : Continuous fun s : ℝ => a + (b - a) * s).continuousOn
      (mapsTo_affine_Icc ha hb), fun _ hs => hz.zero _ (mapsTo_affine_Icc ha hb hs)⟩,
    by simp, by simp⟩

/-- Every zero over a point of a forward path lies on a lift of the whole path. -/
theorem IsForwardPath.exists_isZeroLift_through (hγ : IsForwardPath γ) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) {w : ℂ} (hw : complexHeat (γ a) w = 0) :
    ∃ z, IsZeroLift γ 1 z ∧ z a = w := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨q, hq⟩ := (hγ.sub ha h0).exists_transports (z₀ := w) (by rwa [subPath_zero])
  obtain ⟨-, z, hz, hz0, -⟩ := hγ.exists_transports (z₀ := q) (by
    have := hq.zero_right
    rwa [subPath_one] at this)
  refine ⟨z, hz, ?_⟩
  have h1 := hz.transports_subPath ha h0
  rw [hz0] at h1
  exact (hγ.sub ha h0).transports_injective h1 hq

/-- The transport along the part of a forward path between two parameters. -/
def IsForwardPath.arcEquiv (hγ : IsForwardPath γ) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) : Fibre (γ a) ≃ Fibre (γ b) :=
  (hγ.sub ha hb).fibreEquiv (subPath_zero γ a b) (subPath_one γ a b)

theorem IsForwardPath.arcEquiv_eq (hγ : IsForwardPath γ) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) {z : ℝ → ℂ} (hz : IsZeroLift γ 1 z) (p : Fibre (γ a))
    (hp : z a = p.1) : (hγ.arcEquiv ha hb p).1 = z b :=
  (hγ.sub ha hb).transports_unique ((hγ.sub ha hb).transports_fibreEquiv _ _ p)
    (hp ▸ hz.transports_subPath ha hb)

/-- The transports along consecutive parts of a path compose. -/
theorem IsForwardPath.arcEquiv_trans (hγ : IsForwardPath γ) {a b c : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1) :
    hγ.arcEquiv ha hc = (hγ.arcEquiv ha hb).trans (hγ.arcEquiv hb hc) := by
  refine Equiv.ext fun p => Subtype.ext ?_
  obtain ⟨z, hz, hza⟩ := hγ.exists_isZeroLift_through ha p.2
  rw [hγ.arcEquiv_eq ha hc hz p hza, Equiv.trans_apply,
    hγ.arcEquiv_eq hb hc hz _ (hγ.arcEquiv_eq ha hb hz p hza).symm]

theorem IsForwardPath.arcEquiv_self (hγ : IsForwardPath γ) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    hγ.arcEquiv ha ha = Equiv.refl _ := by
  refine Equiv.ext fun p => Subtype.ext ?_
  obtain ⟨z, hz, hza⟩ := hγ.exists_isZeroLift_through ha p.2
  rw [hγ.arcEquiv_eq ha ha hz p hza, hza]
  rfl

/-- The transport along the part from `b` to `a` inverts the transport from `a` to `b`. -/
theorem IsForwardPath.arcEquiv_symm (hγ : IsForwardPath γ) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) : (hγ.arcEquiv ha hb).symm = hγ.arcEquiv hb ha := by
  rw [Equiv.symm_eq_iff_trans_eq_refl, ← hγ.arcEquiv_trans ha hb ha, hγ.arcEquiv_self]

/-- The value of the transport along a whole path, in terms of its parts. -/
theorem IsForwardPath.fibreEquiv_val_eq_arcEquiv (hγ : IsForwardPath γ) {τ' : ℂ}
    (h1 : γ 1 = τ') (p : Fibre (γ 0)) :
    (hγ.fibreEquiv rfl h1 p).1 =
      (hγ.arcEquiv ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ p).1 := by
  obtain ⟨z, hz, hza⟩ := hγ.exists_isZeroLift_through ⟨le_rfl, zero_le_one⟩ p.2
  rw [hγ.arcEquiv_eq _ _ hz p hza]
  exact hγ.transports_unique (hγ.transports_fibreEquiv rfl h1 p) ⟨z, hz, hza, rfl⟩

/-- The transport along a path is the composition of the transports along its two parts. -/
theorem IsForwardPath.fibreEquiv_cut (hγ : IsForwardPath γ) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    {τ τ' τ'' : ℂ} (h0 : γ 0 = τ) (h1 : γ 1 = τ'') (hl : IsForwardPath (subPath γ 0 c))
    (l0 : subPath γ 0 c 0 = τ) (l1 : subPath γ 0 c 1 = τ') (hr : IsForwardPath (subPath γ c 1))
    (r0 : subPath γ c 1 0 = τ') (r1 : subPath γ c 1 1 = τ'') :
    hγ.fibreEquiv h0 h1 = (hl.fibreEquiv l0 l1).trans (hr.fibreEquiv r0 r1) := by
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine Equiv.ext fun q => hγ.fibreEquiv_eq h0 h1 ?_
  obtain ⟨z, hz, hz0⟩ := hγ.exists_isZeroLift_through h00 (w := q.1) (by rw [h0]; exact q.2)
  have e1 : (hl.fibreEquiv l0 l1 q).1 = z c :=
    hl.transports_unique (hl.transports_fibreEquiv l0 l1 q)
      (by rw [← hz0]; exact hz.transports_subPath h00 hc)
  have e2 : (hr.fibreEquiv r0 r1 (hl.fibreEquiv l0 l1 q)).1 = z 1 :=
    hr.transports_unique (hr.transports_fibreEquiv r0 r1 _)
      (by rw [e1]; exact hz.transports_subPath hc h11)
  rw [Equiv.trans_apply, e2]
  exact ⟨z, hz, hz0, rfl⟩

/-! ## Paths inside a region -/

theorem pathJoin_mem {γ₁ γ₂ : ℝ → ℂ} {A : Set ℂ} (h₁ : ∀ s ∈ Icc (0 : ℝ) 1, γ₁ s ∈ A)
    (h₂ : ∀ s ∈ Icc (0 : ℝ) 1, γ₂ s ∈ A) : ∀ s ∈ Icc (0 : ℝ) 1, pathJoin γ₁ γ₂ s ∈ A := by
  intro s hs
  rcases le_or_gt s (1 / 2) with hle | hlt
  · rw [pathJoin_of_le hle]
    exact h₁ _ (mapsTo_double ⟨hs.1, hle⟩)
  · rw [pathJoin_of_lt hlt]
    exact h₂ _ (mapsTo_double_sub_one ⟨hlt.le, hs.2⟩)

theorem pathRev_mem {A : Set ℂ} (h : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ A) :
    ∀ s ∈ Icc (0 : ℝ) 1, pathRev γ s ∈ A :=
  fun _ hs => h _ (mapsTo_one_sub hs)

theorem subPath_mem {A : Set ℂ} {a b : ℝ} (hab : a ≤ b) (h : ∀ s ∈ Icc a b, γ s ∈ A) :
    ∀ s ∈ Icc (0 : ℝ) 1, subPath γ a b s ∈ A :=
  fun s hs => h _ ⟨by nlinarith [mul_nonneg (sub_nonneg.2 hab) hs.1],
    by nlinarith [mul_nonneg (sub_nonneg.2 hab) (sub_nonneg.2 hs.2)]⟩

/-- A path inside the union of two open sets is cut into finitely many parts of equal length,
each inside one of the sets. -/
theorem exists_subdivision (hγ : ContinuousOn γ (Icc 0 1)) {A₁ A₂ : Set ℂ} (hA₁ : IsOpen A₁)
    (hA₂ : IsOpen A₂) (hin : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ A₁ ∪ A₂) :
    ∃ n : ℕ, 0 < n ∧ ∀ k < n,
      (∀ s ∈ Icc ((k : ℝ) / n) (((k + 1 : ℕ) : ℝ) / n), γ s ∈ A₁) ∨
        (∀ s ∈ Icc ((k : ℝ) / n) (((k + 1 : ℕ) : ℝ) / n), γ s ∈ A₂) := by
  obtain ⟨u₁, hu₁, e₁⟩ := continuousOn_iff'.1 hγ A₁ hA₁
  obtain ⟨u₂, hu₂, e₂⟩ := continuousOn_iff'.1 hγ A₂ hA₂
  have hcover : Icc (0 : ℝ) 1 ⊆ ⋃₀ {u₁, u₂} := by
    intro s hs
    rcases hin s hs with h | h
    · have : s ∈ u₁ ∩ Icc 0 1 := by
        rw [← e₁]
        exact ⟨h, hs⟩
      exact mem_sUnion.2 ⟨u₁, Or.inl rfl, this.1⟩
    · have : s ∈ u₂ ∩ Icc 0 1 := by
        rw [← e₂]
        exact ⟨h, hs⟩
      exact mem_sUnion.2 ⟨u₂, Or.inr rfl, this.1⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric_sUnion isCompact_Icc
    (by
      rintro t (rfl | rfl)
      exacts [hu₁, hu₂]) hcover
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m + 1, Nat.succ_pos m, fun k hk => ?_⟩
  have hnpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hm' : 1 / ((m + 1 : ℕ) : ℝ) < δ := by
    push_cast
    exact hm
  have hstep : ((k + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) =
      (k : ℝ) / ((m + 1 : ℕ) : ℝ) + 1 / ((m + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  have hk0 : 0 ≤ (k : ℝ) / ((m + 1 : ℕ) : ℝ) := by positivity
  have hk1 : ((k + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hnpos]
    exact_mod_cast Nat.succ_le_of_lt hk
  have hx : (k : ℝ) / ((m + 1 : ℕ) : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨hk0, le_trans (by rw [hstep]; linarith [one_div_pos.2 hnpos]) hk1⟩
  obtain ⟨t, ht, hsub⟩ := hball _ hx
  have hmem : ∀ s ∈ Icc ((k : ℝ) / ((m + 1 : ℕ) : ℝ)) (((k + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)),
      s ∈ t ∩ Icc (0 : ℝ) 1 := by
    intro s hs
    refine ⟨hsub ?_, hk0.trans hs.1, hs.2.trans hk1⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    have h2 := hs.2
    rw [hstep] at h2
    constructor <;> linarith [hs.1]
  rcases ht with rfl | rfl
  · refine Or.inl fun s hs => ?_
    have := hmem s hs
    rw [← e₁] at this
    exact this.1
  · refine Or.inr fun s hs => ?_
    have := hmem s hs
    rw [← e₂] at this
    exact this.1

/-! ## Loops inside a region -/

/-- Every forward loop inside `A` based at `h` has its transport in `N`. -/
def LoopsIn (A : Set ℂ) (h : ℂ) (N : Subgroup (Equiv.Perm (Fibre h))) : Prop :=
  ∀ (γ : ℝ → ℂ) (hγ : IsForwardPath γ) (h0 : γ 0 = h) (h1 : γ 1 = h),
    (∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ A) → hγ.fibreEquiv h0 h1 ∈ N

/-- Every forward time of `A` off the branch times is the end of a forward path inside `A`
that starts at `h`. -/
def JoinedIn (A : Set ℂ) (h : ℂ) : Prop :=
  ∀ x ∈ A, 0 < x.re → x ∉ branchTimes →
    ∃ η, IsForwardPath η ∧ η 0 = h ∧ η 1 = x ∧ ∀ s ∈ Icc (0 : ℝ) 1, η s ∈ A

/-- Over every time of `A₁ ∩ A₂` there are paths from `h`, one inside `A₁` and one inside
`A₂`, whose transports differ by an element of `N`. -/
def Junction (A₁ A₂ : Set ℂ) (h : ℂ) (N : Subgroup (Equiv.Perm (Fibre h))) : Prop :=
  ∀ x ∈ A₁ ∩ A₂, 0 < x.re → x ∉ branchTimes →
    ∃ (η₁ η₂ : ℝ → ℂ) (hη₁ : IsForwardPath η₁) (hη₂ : IsForwardPath η₂) (a0 : η₁ 0 = h)
      (a1 : η₁ 1 = x) (b0 : η₂ 0 = h) (b1 : η₂ 1 = x),
      (∀ s ∈ Icc (0 : ℝ) 1, η₁ s ∈ A₁) ∧ (∀ s ∈ Icc (0 : ℝ) 1, η₂ s ∈ A₂) ∧
        (hη₁.fibreEquiv a0 a1).trans (hη₂.fibreEquiv b0 b1).symm ∈ N

/-- Over a convex set of forward times without branch times every loop has the trivial
transport. -/
theorem loopsIn_of_convex {U : Set ℂ} (hU : Convex ℝ U) (hpos : ∀ τ ∈ U, 0 < τ.re)
    (hb : ∀ τ ∈ U, τ ∉ branchTimes) (h : ℂ) (N : Subgroup (Equiv.Perm (Fibre h))) :
    LoopsIn U h N := by
  intro γ hγ h0 h1 hin
  have : hγ.fibreEquiv h0 h1 = 1 := by
    refine Equiv.ext fun p => hγ.fibreEquiv_eq h0 h1 ?_
    exact transports_self_of_convex hU hpos hb hγ.continuousOn hin (h1.trans h0.symm)
      (by rw [h0]; exact p.2)
  rw [this]
  exact N.one_mem

variable {A₁ A₂ : Set ℂ} {h : ℂ} {N : Subgroup (Equiv.Perm (Fibre h))}

/-- Two forward paths inside `A` from the base to one time differ by an element of `N`. -/
theorem LoopsIn.trans_symm_mem {A : Set ℂ} (hL : LoopsIn A h N) {x : ℂ} {ζ η : ℝ → ℂ}
    (hζ : IsForwardPath ζ) (hη : IsForwardPath η) (ζ0 : ζ 0 = h) (ζ1 : ζ 1 = x) (η0 : η 0 = h)
    (η1 : η 1 = x) (hζA : ∀ s ∈ Icc (0 : ℝ) 1, ζ s ∈ A) (hηA : ∀ s ∈ Icc (0 : ℝ) 1, η s ∈ A) :
    (hζ.fibreEquiv ζ0 ζ1).trans (hη.fibreEquiv η0 η1).symm ∈ N := by
  have hr0 : pathRev η 0 = x := (pathRev_zero η).trans η1
  have hr1 : pathRev η 1 = h := (pathRev_one η).trans η0
  have hj : IsForwardPath (pathJoin ζ (pathRev η)) := hζ.join hη.reverse (ζ1.trans hr0.symm)
  have j0 : pathJoin ζ (pathRev η) 0 = h := (pathJoin_zero _ _).trans ζ0
  have j1 : pathJoin ζ (pathRev η) 1 = h := (pathJoin_one _ _).trans hr1
  have := hL _ hj j0 j1 (pathJoin_mem hζA (pathRev_mem hηA))
  rwa [hζ.fibreEquiv_join hη.reverse ζ0 ζ1 hr0 hr1 hj j0 j1,
    hη.fibreEquiv_reverse η0 η1 hη.reverse hr0 hr1] at this

/-- Two paths from the base to one time, each inside one of the two regions, differ by an
element of `N`. -/
private theorem switch_mem (h₁ : LoopsIn A₁ h N) (h₂ : LoopsIn A₂ h N)
    (hJ : Junction A₁ A₂ h N) {x : ℂ} {B B' : Set ℂ} (hB : B = A₁ ∨ B = A₂)
    (hB' : B' = A₁ ∨ B' = A₂) {ζ η : ℝ → ℂ} (hζ : IsForwardPath ζ) (hη : IsForwardPath η)
    (ζ0 : ζ 0 = h) (ζ1 : ζ 1 = x) (η0 : η 0 = h) (η1 : η 1 = x)
    (hζB : ∀ s ∈ Icc (0 : ℝ) 1, ζ s ∈ B) (hηB : ∀ s ∈ Icc (0 : ℝ) 1, η s ∈ B') :
    (hζ.fibreEquiv ζ0 ζ1).trans (hη.fibreEquiv η0 η1).symm ∈ N := by
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hxpos : 0 < x.re := ζ1 ▸ hζ.re_pos 1 h11
  have hxb : x ∉ branchTimes := ζ1 ▸ hζ.simple 1 h11
  have hxB : x ∈ B := ζ1 ▸ hζB 1 h11
  have hxB' : x ∈ B' := η1 ▸ hηB 1 h11
  rcases hB with rfl | rfl <;> rcases hB' with rfl | rfl
  · exact h₁.trans_symm_mem hζ hη ζ0 ζ1 η0 η1 hζB hηB
  · obtain ⟨η₁, η₂, hη₁, hη₂, a0, a1, b0, b1, hin₁, hin₂, hmem⟩ := hJ x ⟨hxB, hxB'⟩ hxpos hxb
    have e1 := h₁.trans_symm_mem hζ hη₁ ζ0 ζ1 a0 a1 hζB hin₁
    have e3 := h₂.trans_symm_mem hη₂ hη b0 b1 η0 η1 hin₂ hηB
    have := N.mul_mem (N.mul_mem e3 hmem) e1
    convert this using 2
    ext p
    simp [Equiv.Perm.mul_apply]
  · obtain ⟨η₁, η₂, hη₁, hη₂, a0, a1, b0, b1, hin₁, hin₂, hmem⟩ := hJ x ⟨hxB', hxB⟩ hxpos hxb
    have e1 := h₂.trans_symm_mem hζ hη₂ ζ0 ζ1 b0 b1 hζB hin₂
    have e3 := h₁.trans_symm_mem hη₁ hη a0 a1 η0 η1 hin₁ hηB
    have := N.mul_mem (N.mul_mem e3 (N.inv_mem hmem)) e1
    convert this using 2
    ext p
    simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
  · exact h₂.trans_symm_mem hζ hη ζ0 ζ1 η0 η1 hζB hηB

/-- The invariant of the gluing at the parameter `t`: the part of the loop up to `t`, closed
by any path back to the base inside one of the regions, has its transport in `N`. -/
private def GlueInv (A₁ A₂ : Set ℂ) (hγ : IsForwardPath γ)
    (N : Subgroup (Equiv.Perm (Fibre (γ 0)))) (t : ℝ) : Prop :=
  ∀ (ht : t ∈ Icc (0 : ℝ) 1) (B : Set ℂ), B = A₁ ∨ B = A₂ → ∀ (η : ℝ → ℂ)
    (hη : IsForwardPath η) (η0 : η 0 = γ 0) (η1 : η 1 = γ t), (∀ s ∈ Icc (0 : ℝ) 1, η s ∈ B) →
      (hγ.arcEquiv ⟨le_rfl, zero_le_one⟩ ht).trans (hη.fibreEquiv η0 η1).symm ∈ N

/-- The invariant passes a part of the loop that lies inside one of the regions. -/
private theorem glueInv_step {N : Subgroup (Equiv.Perm (Fibre (γ 0)))} (hγ : IsForwardPath γ)
    (h₁ : LoopsIn A₁ (γ 0) N) (h₂ : LoopsIn A₂ (γ 0) N) (hc₁ : JoinedIn A₁ (γ 0))
    (hc₂ : JoinedIn A₂ (γ 0)) (hJ : Junction A₁ A₂ (γ 0) N) {t t' : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1) (htt' : t ≤ t') {B : Set ℂ}
    (hB : B = A₁ ∨ B = A₂) (hpiece : ∀ s ∈ Icc t t', γ s ∈ B)
    (hinv : GlueInv A₁ A₂ hγ N t) : GlueInv A₁ A₂ hγ N t' := by
  unfold GlueInv at hinv ⊢
  intro ht'' B' hB' η hη η0 η1 hηB'
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hLB : LoopsIn B (γ 0) N := by
    rcases hB with rfl | rfl <;> assumption
  have hcB : JoinedIn B (γ 0) := by
    rcases hB with rfl | rfl <;> assumption
  -- paths inside `B` from the base to the two ends of the part
  obtain ⟨θ, hθ, θ0, θ1, hθB⟩ :=
    hcB (γ t) (hpiece t ⟨le_rfl, htt'⟩) (hγ.re_pos t ht) (hγ.simple t ht)
  obtain ⟨ζ, hζ, ζ0, ζ1, hζB⟩ :=
    hcB (γ t') (hpiece t' ⟨htt', le_rfl⟩) (hγ.re_pos t' ht') (hγ.simple t' ht')
  have ha := hinv ht B hB θ hθ θ0 θ1 hθB
  -- the loop through the part, inside `B`
  have hsub := hγ.sub ht ht'
  have hm := hLB.trans_symm_mem (hθ.join hsub (θ1.trans (subPath_zero γ t t').symm)) hζ
    ((pathJoin_zero _ _).trans θ0) ((pathJoin_one _ _).trans (subPath_one γ t t')) ζ0 ζ1
    (pathJoin_mem hθB (subPath_mem htt' hpiece)) hζB
  rw [hθ.fibreEquiv_join hsub θ0 θ1 (subPath_zero γ t t') (subPath_one γ t t')] at hm
  -- the change of the return path
  have hc := switch_mem h₁ h₂ hJ hB hB' hζ hη ζ0 ζ1 η0 η1 hζB hηB'
  have := N.mul_mem (N.mul_mem hc hm) ha
  convert this using 2
  rw [hγ.arcEquiv_trans h00 ht ht'']
  ext p
  simp [Equiv.Perm.mul_apply, IsForwardPath.arcEquiv]

/-- **Gluing.** If the loops inside each of two open regions have their transports in `N`,
the regions are joined to the base, and over the intersection the two regions have paths from
the base that differ by an element of `N`, then the loops inside the union have their
transports in `N`. -/
theorem loopsIn_union (hA₁ : IsOpen A₁) (hA₂ : IsOpen A₂) (h₁ : LoopsIn A₁ h N)
    (h₂ : LoopsIn A₂ h N) (hc₁ : JoinedIn A₁ h) (hc₂ : JoinedIn A₂ h)
    (hJ : Junction A₁ A₂ h N) : LoopsIn (A₁ ∪ A₂) h N := by
  intro γ hγ h0 h1 hin
  subst h0
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨n, hn, hpieces⟩ := exists_subdivision hγ.continuousOn hA₁ hA₂ hin
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have key : ∀ k : ℕ, k ≤ n → GlueInv A₁ A₂ hγ N ((k : ℝ) / n) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.cast_zero, zero_div]
      intro ht B hB η hη η0 η1 hηB
      have hL : LoopsIn B (γ 0) N := by
        rcases hB with rfl | rfl <;> assumption
      rw [hγ.arcEquiv_self ht, Equiv.refl_trans]
      exact N.inv_mem (hL η hη η0 η1 hηB)
    | succ k ih =>
      intro hk
      have hkn : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
        ⟨by positivity, (div_le_one hnpos).2 (by exact_mod_cast (Nat.le_of_succ_le hk))⟩
      have hk1 : ((k + 1 : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
        ⟨by positivity, (div_le_one hnpos).2 (by exact_mod_cast hk)⟩
      have hle : (k : ℝ) / n ≤ ((k + 1 : ℕ) : ℝ) / n := by
        apply div_le_div_of_nonneg_right _ hnpos.le
        exact_mod_cast Nat.le_succ k
      rcases hpieces k hk with hp | hp
      · exact glueInv_step hγ h₁ h₂ hc₁ hc₂ hJ hkn hk1 hle (Or.inl rfl) hp
          (ih (Nat.le_of_succ_le hk))
      · exact glueInv_step hγ h₁ h₂ hc₁ hc₂ hJ hkn hk1 hle (Or.inr rfl) hp
          (ih (Nat.le_of_succ_le hk))
  have hfin := key n le_rfl
  rw [div_self hnpos.ne'] at hfin
  -- close the whole loop by the constant path, inside a region that contains the base
  have hc := IsForwardPath.const (hγ.re_pos 0 h00) (hγ.simple 0 h00)
  obtain ⟨B, hB, hbB⟩ : ∃ B, (B = A₁ ∨ B = A₂) ∧ γ 0 ∈ B := by
    rcases hin 0 h00 with hb | hb
    exacts [⟨A₁, Or.inl rfl, hb⟩, ⟨A₂, Or.inr rfl, hb⟩]
  have := hfin h11 B hB (fun _ => γ 0) hc rfl h1.symm (fun _ _ => hbB)
  convert this using 2
  refine Equiv.ext fun p => Subtype.ext ?_
  rw [Equiv.trans_apply, hc.fibreEquiv_const_symm_apply]
  exact hγ.fibreEquiv_val_eq_arcEquiv h1 p

end

end GaloisForLFunctions.GaloisTheoryOfZeros

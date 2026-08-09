import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellSplitDefectStreams

/-!
# Free coefficient modules of a ramification power event

The support partition `A_{rm} = P_r(A_m) ⊔ X_{m,r}` becomes, on free coefficient modules, a
canonically split short exact sequence

`0 → V_m →^J V_{rm} →^Q E_{m,r} → 0`,   `R J = 1`,   `V_{rm} ≅ V_m ⊕ E_{m,r}`,

with `J e_k = e_{k^r}`.  The canonical excess partition `X_{m,sr} = X_{rm,s} ⊔ P_s(X_{m,r})` gives
the corresponding split sequence one level up,

`0 → E_{m,r} → E_{m,sr} → E_{rm,s} → 0`.

Both are instances of the route-independent cofiber sequence `0 → B/A → C/A → C/B → 0` for
`A ≤ B ≤ C`, recorded here as `quotient_cofiber_equiv`.
-/

namespace HTGeometry.ConstraintFrameRelativity

open RHTower

/-! ## Membership accessors -/

theorem mem_shellSupport_iff {m n : ℕ} : n ∈ shellSupport m ↔ shellIndicator m n = 1 := Iff.rfl

theorem mem_excessSupport_iff {m r N : ℕ} :
    N ∈ excessSupport m r ↔ shellIndicator (r * m) N = 1 ∧ ¬ IsRPow r N := Iff.rfl

theorem shellIndicator_of_mem_excess {m r N : ℕ} (h : N ∈ excessSupport m r) :
    shellIndicator (r * m) N = 1 := (mem_excessSupport_iff.mp h).1

theorem not_isRPow_of_mem_excess {m r N : ℕ} (h : N ∈ excessSupport m r) :
    ¬ IsRPow r N := (mem_excessSupport_iff.mp h).2

/-! ## The support splitting bijection -/

/-- The inclusion of the level-`m` shell support into the level-`r m` shell support. -/
def shellIncl {m r : ℕ} (hr : r ≠ 0) (k : ↥(shellSupport m)) : ↥(shellSupport (r * m)) :=
  ⟨(k : ℕ) ^ r, by
    have hk : shellIndicator m (k : ℕ) = 1 := mem_shellSupport_iff.mp k.2
    exact mem_shellSupport_iff.mpr (by rw [shellIndicator_pow hr]; exact hk)⟩

@[simp] theorem shellIncl_coe {m r : ℕ} (hr : r ≠ 0) (k : ↥(shellSupport m)) :
    ((shellIncl hr k : ↥(shellSupport (r * m))) : ℕ) = (k : ℕ) ^ r := rfl

theorem mem_shellSupport_rroot {m r N : ℕ} (hr : r ≠ 0) (hN : N ∈ shellSupport (r * m))
    (h : IsRPow r N) : rroot r N ∈ shellSupport m := by
  refine mem_shellSupport_iff.mpr ?_
  have h1 : shellIndicator (r * m) ((rroot r N) ^ r) = 1 := by
    rw [pow_rroot h]
    exact mem_shellSupport_iff.mp hN
  rwa [shellIndicator_pow hr] at h1

/-- **The split of the higher shell support.** -/
noncomputable def shellSplitEquiv {m r : ℕ} (hr : r ≠ 0) :
    ↥(shellSupport (r * m)) ≃ ↥(shellSupport m) ⊕ ↥(excessSupport m r) where
  toFun N := by
    classical
    exact if h : IsRPow r (N : ℕ) then
      Sum.inl ⟨rroot r (N : ℕ), mem_shellSupport_rroot hr N.2 h⟩
    else
      Sum.inr ⟨(N : ℕ), mem_excessSupport_iff.mpr ⟨mem_shellSupport_iff.mp N.2, h⟩⟩
  invFun x :=
    match x with
    | Sum.inl k => shellIncl hr k
    | Sum.inr N => ⟨(N : ℕ), mem_shellSupport_iff.mpr (shellIndicator_of_mem_excess N.2)⟩
  left_inv N := by
    classical
    by_cases h : IsRPow r (N : ℕ)
    · simp only [dif_pos h]
      exact Subtype.ext (pow_rroot h)
    · simp only [dif_neg h]
  right_inv x := by
    classical
    rcases x with k | N
    · have h : IsRPow r (((shellIncl hr k : ↥(shellSupport (r * m))) : ℕ)) :=
        isRPow_pow r (k : ℕ)
      simp only [dif_pos h]
      exact congrArg Sum.inl (Subtype.ext (rroot_pow hr (k : ℕ)))
    · have h : ¬ IsRPow r ((N : ℕ)) := not_isRPow_of_mem_excess N.2
      simp only [dif_neg h]

/-! ## The free coefficient modules -/

variable (K : Type*) [Semiring K]

/-- **The canonical splitting of the coefficient module.** -/
noncomputable def shellCoeffEquiv (m : ℕ) {r : ℕ} (hr : r ≠ 0) :
    (↥(shellSupport (r * m)) →₀ K) ≃ₗ[K]
      (↥(shellSupport m) →₀ K) × (↥(excessSupport m r) →₀ K) :=
  (Finsupp.domLCongr (shellSplitEquiv hr)).trans (Finsupp.sumFinsuppLEquivProdFinsupp K)

theorem shellIncl_injective {m r : ℕ} (hr : r ≠ 0) :
    Function.Injective (shellIncl (m := m) hr) := by
  intro a b hab
  have h : (a : ℕ) ^ r = (b : ℕ) ^ r := congrArg Subtype.val hab
  exact Subtype.ext (Nat.pow_left_injective hr h)

/-- The inherited inclusion `J`, sending `e_k` to `e_{k^r}`. -/
noncomputable def shellJ (m : ℕ) {r : ℕ} (hr : r ≠ 0) :
    (↥(shellSupport m) →₀ K) →ₗ[K] (↥(shellSupport (r * m)) →₀ K) :=
  Finsupp.lmapDomain K K (shellIncl hr)

/-- The root retraction `R`. -/
noncomputable def shellR (m : ℕ) {r : ℕ} (hr : r ≠ 0) :
    (↥(shellSupport (r * m)) →₀ K) →ₗ[K] (↥(shellSupport m) →₀ K) :=
  Finsupp.lcomapDomain (shellIncl hr) (shellIncl_injective hr)

/-- The excess projection `Q`. -/
noncomputable def shellQ (m : ℕ) {r : ℕ} (hr : r ≠ 0) :
    (↥(shellSupport (r * m)) →₀ K) →ₗ[K] (↥(excessSupport m r) →₀ K) :=
  (LinearMap.snd K _ _) ∘ₗ (shellCoeffEquiv K m hr).toLinearMap

@[simp] theorem shellJ_single (m : ℕ) {r : ℕ} (hr : r ≠ 0) (k : ↥(shellSupport m)) (c : K) :
    shellJ K m hr (Finsupp.single k c) = Finsupp.single (shellIncl hr k) c := by
  simp [shellJ]

@[simp] theorem shellR_apply (m : ℕ) {r : ℕ} (hr : r ≠ 0)
    (y : ↥(shellSupport (r * m)) →₀ K) (k : ↥(shellSupport m)) :
    (shellR K m hr y) k = y (shellIncl hr k) := rfl

theorem shellR_comp_shellJ (m : ℕ) {r : ℕ} (hr : r ≠ 0) :
    (shellR K m hr) ∘ₗ (shellJ K m hr) = LinearMap.id := by
  ext v k
  simp [shellR, shellJ]

theorem shellJ_injective (m : ℕ) {r : ℕ} (hr : r ≠ 0) :
    Function.Injective (shellJ K m hr) := by
  intro a b hab
  have h := congrArg (shellR K m hr) hab
  have hRJ := shellR_comp_shellJ K m hr
  have ha : (shellR K m hr) (shellJ K m hr a) = a := by
    have := congrArg (fun (f : (↥(shellSupport m) →₀ K) →ₗ[K] _) => f a) hRJ
    simpa using this
  have hb : (shellR K m hr) (shellJ K m hr b) = b := by
    have := congrArg (fun (f : (↥(shellSupport m) →₀ K) →ₗ[K] _) => f b) hRJ
    simpa using this
  rw [← ha, ← hb, h]

theorem shellCoeffEquiv_single_incl (m : ℕ) {r : ℕ} (hr : r ≠ 0) (k : ↥(shellSupport m))
    (c : K) :
    (shellCoeffEquiv K m hr) (Finsupp.single (shellIncl hr k) c) = (Finsupp.single k c, 0) := by
  have hval : shellSplitEquiv hr (shellIncl hr k) = Sum.inl k :=
    (shellSplitEquiv hr).apply_symm_apply (Sum.inl k)
  rw [shellCoeffEquiv]
  simp only [LinearEquiv.trans_apply]
  rw [Finsupp.domLCongr_single, hval]
  refine Prod.ext ?_ ?_ <;> ext j <;>
    simp [Finsupp.sumFinsuppLEquivProdFinsupp, Finsupp.single_apply]

/-- **The splitting sends the inherited part to the first summand.** -/
theorem shellCoeffEquiv_shellJ (m : ℕ) {r : ℕ} (hr : r ≠ 0) (v : ↥(shellSupport m) →₀ K) :
    (shellCoeffEquiv K m hr) (shellJ K m hr v) = (v, 0) := by
  refine Finsupp.induction_linear v ?_ ?_ ?_
  · simp [Prod.ext_iff]
  · intro f g hf hg
    rw [map_add, map_add, hf, hg]
    simp
  · intro a b
    rw [shellJ_single, shellCoeffEquiv_single_incl]

theorem shellQ_surjective (m : ℕ) {r : ℕ} (hr : r ≠ 0) :
    Function.Surjective (shellQ K m hr) := by
  intro y
  exact ⟨(shellCoeffEquiv K m hr).symm (0, y), by simp [shellQ]⟩

theorem range_shellJ_eq_ker_shellQ (m : ℕ) {r : ℕ} (hr : r ≠ 0) :
    LinearMap.range (shellJ K m hr) = LinearMap.ker (shellQ K m hr) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp [shellQ, shellCoeffEquiv_shellJ]
  · intro hy
    refine ⟨((shellCoeffEquiv K m hr) y).1, ?_⟩
    have h2 : ((shellCoeffEquiv K m hr) y).2 = 0 := by
      simpa [shellQ] using hy
    have hpair : (shellCoeffEquiv K m hr) y = (((shellCoeffEquiv K m hr) y).1, 0) := by
      rw [← h2]
    apply (shellCoeffEquiv K m hr).injective
    rw [shellCoeffEquiv_shellJ]
    exact hpair.symm

/-- **Strict composition of root retractions.** -/
theorem shellIncl_comp_coe {m r s : ℕ} (hr : r ≠ 0) (hs : s ≠ 0) (k : ↥(shellSupport m)) :
    ((shellIncl hs (shellIncl hr k) : ↥(shellSupport (s * (r * m)))) : ℕ) = (k : ℕ) ^ (s * r) := by
  rw [shellIncl_coe, shellIncl_coe, ← pow_mul, mul_comm r s]

theorem shellR_comp_apply (m : ℕ) {r s : ℕ} (hr : r ≠ 0) (hs : s ≠ 0)
    (y : ↥(shellSupport (s * (r * m))) →₀ K) (k : ↥(shellSupport m)) :
    (shellR K m hr (shellR K (r * m) hs y)) k = y (shellIncl hs (shellIncl hr k)) := by
  rw [shellR_apply, shellR_apply]

/-! ## The excess splitting one level up -/

theorem mem_excessSupport_rroot {m r s N : ℕ} (hs : s ≠ 0) (hN : N ∈ excessSupport m (s * r))
    (h : IsRPow s N) : rroot s N ∈ excessSupport m r := by
  rw [excessSupport_mul_eq_union hs] at hN
  rcases hN with hN | ⟨Kw, hKw, hKN⟩
  · exact absurd h (not_isRPow_of_mem_excess hN)
  · have hroot : rroot s N = Kw := by
      rw [← hKN, rroot_pow hs]
    rw [hroot]
    exact hKw

theorem mem_excessSupport_of_not_isRPow {m r s N : ℕ} (hs : s ≠ 0)
    (hN : N ∈ excessSupport m (s * r)) (h : ¬ IsRPow s N) : N ∈ excessSupport (r * m) s := by
  rw [excessSupport_mul_eq_union hs] at hN
  rcases hN with hN | ⟨Kw, -, hKN⟩
  · exact hN
  · exact absurd (hKN ▸ isRPow_pow s Kw) h

/-- **The split of the composed excess support.** -/
noncomputable def excessSplitEquiv {m r s : ℕ} (hs : s ≠ 0) :
    ↥(excessSupport m (s * r)) ≃ ↥(excessSupport m r) ⊕ ↥(excessSupport (r * m) s) where
  toFun N := by
    classical
    exact if h : IsRPow s (N : ℕ) then
      Sum.inl ⟨rroot s (N : ℕ), mem_excessSupport_rroot hs N.2 h⟩
    else
      Sum.inr ⟨(N : ℕ), mem_excessSupport_of_not_isRPow hs N.2 h⟩
  invFun x :=
    match x with
    | Sum.inl Kw => ⟨(Kw : ℕ) ^ s, by
        rw [excessSupport_mul_eq_union hs]
        exact Or.inr ⟨(Kw : ℕ), Kw.2, rfl⟩⟩
    | Sum.inr N => ⟨(N : ℕ), by
        rw [excessSupport_mul_eq_union hs]
        exact Or.inl N.2⟩
  left_inv N := by
    classical
    by_cases h : IsRPow s (N : ℕ)
    · simp only [dif_pos h]
      exact Subtype.ext (pow_rroot h)
    · simp only [dif_neg h]
  right_inv x := by
    classical
    rcases x with Kw | N
    · have h : IsRPow s ((Kw : ℕ) ^ s) := isRPow_pow s (Kw : ℕ)
      simp only [dif_pos h]
      exact congrArg Sum.inl (Subtype.ext (rroot_pow hs (Kw : ℕ)))
    · have h : ¬ IsRPow s ((N : ℕ)) := not_isRPow_of_mem_excess N.2
      simp only [dif_neg h]

/-- **The canonical splitting of the composed excess module.** -/
noncomputable def excessCoeffEquiv (m : ℕ) {r s : ℕ} (hs : s ≠ 0) :
    (↥(excessSupport m (s * r)) →₀ K) ≃ₗ[K]
      (↥(excessSupport m r) →₀ K) × (↥(excessSupport (r * m) s) →₀ K) :=
  (Finsupp.domLCongr (excessSplitEquiv hs)).trans (Finsupp.sumFinsuppLEquivProdFinsupp K)

/-! ## The universal inherited-observer criterion -/

/-- **Inherited-observer factorization criterion.**  A linear observer of the higher shell factors
through the root retraction exactly when it annihilates the excess. -/
theorem factors_through_shellR_iff {A : Type*} [Ring A] {Y : Type*} [AddCommGroup Y]
    [Module A Y] (m : ℕ) {r : ℕ} (hr : r ≠ 0)
    (T : (↥(shellSupport (r * m)) →₀ A) →ₗ[A] Y) :
    (∀ y, shellR A m hr y = 0 → T y = 0) ↔ ∃ T', T = T' ∘ₗ shellR A m hr := by
  constructor
  · intro hT
    refine ⟨T ∘ₗ shellJ A m hr, ?_⟩
    refine LinearMap.ext fun y => ?_
    have hRJ : shellR A m hr (shellJ A m hr (shellR A m hr y)) = shellR A m hr y := by
      have h := congrArg (fun (f : (↥(shellSupport m) →₀ A) →ₗ[A] _) => f (shellR A m hr y))
        (shellR_comp_shellJ A m hr)
      simpa using h
    have hker : shellR A m hr (y - shellJ A m hr (shellR A m hr y)) = 0 := by
      rw [map_sub, hRJ, sub_self]
    have := hT _ hker
    rw [map_sub, sub_eq_zero] at this
    simpa using this
  · rintro ⟨T', rfl⟩ y hy
    simp [hy]

/-! ## The route-independent cofiber sequence -/

/-- **The cofiber sequence of composable monomorphisms.**  For submodules `A ≤ B` of `C`,
`(C/A)/(B/A) ≅ C/B`. -/
noncomputable def quotient_cofiber_equiv {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (A B : Submodule R M) (h : A ≤ B) :
    ((M ⧸ A) ⧸ Submodule.map A.mkQ B) ≃ₗ[R] M ⧸ B :=
  Submodule.quotientQuotientEquivQuotient A B h

end HTGeometry.ConstraintFrameRelativity

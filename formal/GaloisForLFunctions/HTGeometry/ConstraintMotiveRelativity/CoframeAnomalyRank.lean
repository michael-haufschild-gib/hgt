import Mathlib

/-!
# The coframe-transport anomaly and its rank

A chain map `T` between degree-`n` chain data with matched families of closed coframes `φ` and `φ̂`
has **coframe-transport anomaly**

`A_T(x)_ℓ = φ̂_ℓ (T x) - φ_ℓ (x)`.

It kills boundaries, so it is a well-defined invariant of homology classes.  If the source carries
`N` cycles `u_p` dually normalized by the coframes, `φ_ℓ (u_p) = -δ_{ℓ p}`, then those classes are
independent, and if `T` exactifies all of them then `A_T (u_p) = e_p`.  Hence the anomaly restricted
to their span is an isomorphism onto `k^F`; it has rank `N`, cannot factor through a space of
smaller dimension, and its matrix in the matched ordered bases is the identity, so its top exterior
power is an isomorphism of determinant lines with scalar `1`.

Preservation of the coframes forces the anomaly to vanish and the transported classes to stay
independent, and the anomaly of a composite obeys the transport cocycle
`A_{S∘T} = A_T + A_S ∘ T`.
-/

namespace HTGeometry.ConstraintMotiveRelativity

section CoframeAnomaly

variable {k : Type*} [Field k]
variable {C E G : Type*} [AddCommGroup C] [Module k C] [AddCommGroup E] [Module k E]
  [AddCommGroup G] [Module k G]
variable {F : Type*} [Fintype F] [DecidableEq F]

/-- **The coframe-transport anomaly** `(VOD.3)`. -/
def coframeAnomaly (T : C →ₗ[k] E) (φ : F → (C →ₗ[k] k)) (φhat : F → (E →ₗ[k] k)) :
    C →ₗ[k] (F → k) where
  toFun x := fun ℓ => φhat ℓ (T x) - φ ℓ x
  map_add' x y := by
    funext ℓ
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' t x := by
    funext ℓ
    simp only [map_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    ring

omit [Fintype F] [DecidableEq F] in
@[simp] theorem coframeAnomaly_apply (T : C →ₗ[k] E) (φ : F → (C →ₗ[k] k))
    (φhat : F → (E →ₗ[k] k)) (x : C) (ℓ : F) :
    coframeAnomaly T φ φhat x ℓ = φhat ℓ (T x) - φ ℓ x := rfl

omit [Fintype F] [DecidableEq F] in
/-- **Well-definedness on homology.**  The anomaly kills boundaries. -/
theorem coframeAnomaly_eq_zero_of_boundary {T : C →ₗ[k] E} {φ : F → (C →ₗ[k] k)}
    {φhat : F → (E →ₗ[k] k)} {Bc : Submodule k C} {Be : Submodule k E}
    (hφ : ∀ ℓ, Bc ≤ LinearMap.ker (φ ℓ)) (hT : ∀ y ∈ Bc, T y ∈ Be)
    (hφhat : ∀ ℓ, Be ≤ LinearMap.ker (φhat ℓ)) {y : C} (hy : y ∈ Bc) :
    coframeAnomaly T φ φhat y = 0 := by
  funext ℓ
  rw [coframeAnomaly_apply, hφ ℓ hy, hφhat ℓ (hT y hy)]
  simp

/-- The dual normalization `(VOD.2)` of the marked cycles against the source coframes. -/
def CoframeNormalized (u : F → C) (φ : F → (C →ₗ[k] k)) : Prop :=
  ∀ ℓ p, φ ℓ (u p) = -(if ℓ = p then (1 : k) else 0)

theorem coframeNormalized_sum {u : F → C} {φ : F → (C →ₗ[k] k)}
    (hu : CoframeNormalized u φ) (a : F → k) (ℓ : F) :
    φ ℓ (∑ p, a p • u p) = -a ℓ := by
  classical
  rw [map_sum]
  have hterm : ∀ p : F, φ ℓ (a p • u p) = -(a p * (if ℓ = p then (1 : k) else 0)) := by
    intro p
    rw [map_smul, smul_eq_mul, hu ℓ p]
    ring
  rw [Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_eq_single ℓ]
  · simp
  · intro p _ hp
    simp [Ne.symm hp]
  · intro h
    exact absurd (Finset.mem_univ ℓ) h

/-- **Theorem 3.1 (1).**  Dually normalized cycles are independent modulo boundaries. -/
theorem coframe_independent {u : F → C} {φ : F → (C →ₗ[k] k)} {Bc : Submodule k C}
    (hu : CoframeNormalized u φ) (hφ : ∀ ℓ, Bc ≤ LinearMap.ker (φ ℓ))
    {a : F → k} (ha : ∑ p, a p • u p ∈ Bc) : a = 0 := by
  funext ℓ
  have h1 := coframeNormalized_sum hu a ℓ
  have h2 : φ ℓ (∑ p, a p • u p) = 0 := hφ ℓ ha
  rw [h2] at h1
  simpa using h1.symm

omit [Fintype F] in
/-- **Theorem 3.1 (2).**  Exactifying a marked cycle turns the anomaly into its dual basis
vector. -/
theorem coframeAnomaly_marked {T : C →ₗ[k] E} {φ : F → (C →ₗ[k] k)}
    {φhat : F → (E →ₗ[k] k)} {u : F → C} {Be : Submodule k E}
    (hu : CoframeNormalized u φ) (hTu : ∀ p, T (u p) ∈ Be)
    (hφhat : ∀ ℓ, Be ≤ LinearMap.ker (φhat ℓ)) (p : F) :
    coframeAnomaly T φ φhat (u p) = Pi.single p 1 := by
  funext ℓ
  rw [coframeAnomaly_apply, hφhat ℓ (hTu p), hu ℓ p, Pi.single_apply]
  by_cases h : ℓ = p
  · simp [h]
  · simp [h]

/-- **Theorem 3.1 (3).**  The anomaly is surjective from the span of the marked cycles. -/
theorem coframeAnomaly_surjective_on_span {T : C →ₗ[k] E} {φ : F → (C →ₗ[k] k)}
    {φhat : F → (E →ₗ[k] k)} {u : F → C} {Be : Submodule k E}
    (hu : CoframeNormalized u φ) (hTu : ∀ p, T (u p) ∈ Be)
    (hφhat : ∀ ℓ, Be ≤ LinearMap.ker (φhat ℓ)) (v : F → k) :
    ∃ x ∈ Submodule.span k (Set.range u), coframeAnomaly T φ φhat x = v := by
  classical
  refine ⟨∑ p, v p • u p, Submodule.sum_mem _ fun p _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩), ?_⟩
  rw [map_sum]
  funext ℓ
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul,
    coframeAnomaly_marked hu hTu hφhat, Pi.single_apply]
  rw [Finset.sum_eq_single ℓ]
  · simp
  · intro p _ hp
    simp [Ne.symm hp]
  · intro h
    exact absurd (Finset.mem_univ ℓ) h

/-- **Theorem 3.1 (4).**  Exactification cannot be mediated by a small port: if the anomaly on the
span factors through a space of dimension `r`, then `|F| ≤ r`. -/
theorem card_le_of_factorization {T : C →ₗ[k] E} {φ : F → (C →ₗ[k] k)}
    {φhat : F → (E →ₗ[k] k)} {u : F → C} {Be : Submodule k E}
    (hu : CoframeNormalized u φ) (hTu : ∀ p, T (u p) ∈ Be)
    (hφhat : ∀ ℓ, Be ≤ LinearMap.ker (φhat ℓ))
    {P : Type*} [AddCommGroup P] [Module k P] [FiniteDimensional k P]
    (f : C →ₗ[k] P) (g : P →ₗ[k] (F → k))
    (hfac : ∀ x ∈ Submodule.span k (Set.range u), g (f x) = coframeAnomaly T φ φhat x) :
    Fintype.card F ≤ Module.finrank k P := by
  classical
  have hgsurj : Function.Surjective g := by
    intro v
    obtain ⟨x, hx, hxv⟩ := coframeAnomaly_surjective_on_span hu hTu hφhat v
    exact ⟨f x, by rw [hfac x hx, hxv]⟩
  have hsum := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.2 hgsurj] at hsum
  have htop : Module.finrank k (⊤ : Submodule k (F → k)) = Module.finrank k (F → k) :=
    finrank_top k (F → k)
  rw [htop] at hsum
  have hquot : Module.finrank k (F → k) ≤ Module.finrank k P := by omega
  simpa using hquot

/-- **Corollary 3.2 — one-port impossibility.**  For at least two independently coframed classes,
no anomaly factoring through a single scalar line can exactify them all. -/
theorem no_scalar_factorization {T : C →ₗ[k] E} {φ : F → (C →ₗ[k] k)}
    {φhat : F → (E →ₗ[k] k)} {u : F → C} {Be : Submodule k E}
    (hu : CoframeNormalized u φ) (hTu : ∀ p, T (u p) ∈ Be)
    (hφhat : ∀ ℓ, Be ≤ LinearMap.ker (φhat ℓ)) (hcard : 2 ≤ Fintype.card F)
    (f : C →ₗ[k] k) (g : k →ₗ[k] (F → k)) :
    ¬ (∀ x ∈ Submodule.span k (Set.range u), g (f x) = coframeAnomaly T φ φhat x) := by
  intro hfac
  have h := card_le_of_factorization hu hTu hφhat f g hfac
  rw [Module.finrank_self] at h
  omega

omit [Fintype F] [DecidableEq F] in
/-- **Theorem 4.1 — preservation implies nonerasure.** -/
theorem coframeAnomaly_eq_zero_of_preserved {T : C →ₗ[k] E} {φ : F → (C →ₗ[k] k)}
    {φhat : F → (E →ₗ[k] k)} (hpres : ∀ ℓ, (φhat ℓ).comp T = φ ℓ) :
    coframeAnomaly T φ φhat = 0 := by
  ext x ℓ
  rw [coframeAnomaly_apply]
  have := congrArg (fun f : C →ₗ[k] k => f x) (hpres ℓ)
  simp only [LinearMap.comp_apply] at this
  rw [this]
  simp

theorem transported_independent {T : C →ₗ[k] E} {φ : F → (C →ₗ[k] k)}
    {φhat : F → (E →ₗ[k] k)} {u : F → C} {Be : Submodule k E}
    (hu : CoframeNormalized u φ) (hpres : ∀ ℓ, (φhat ℓ).comp T = φ ℓ)
    (hφhat : ∀ ℓ, Be ≤ LinearMap.ker (φhat ℓ))
    {a : F → k} (ha : T (∑ p, a p • u p) ∈ Be) : a = 0 := by
  funext ℓ
  have h1 := coframeNormalized_sum hu a ℓ
  have h2 : φ ℓ (∑ p, a p • u p) = φhat ℓ (T (∑ p, a p • u p)) := by
    have := congrArg (fun f : C →ₗ[k] k => f (∑ p, a p • u p)) (hpres ℓ)
    simpa using this.symm
  rw [h2, hφhat ℓ ha] at h1
  simpa using h1.symm

omit [Fintype F] [DecidableEq F] in
/-- **Theorem 4.2 — the anomaly transport cocycle** `(VOD.5)`. -/
theorem coframeAnomaly_comp (T : C →ₗ[k] E) (S : E →ₗ[k] G) (φ : F → (C →ₗ[k] k))
    (φhat : F → (E →ₗ[k] k)) (φtilde : F → (G →ₗ[k] k)) :
    coframeAnomaly (S.comp T) φ φtilde
      = coframeAnomaly T φ φhat + (coframeAnomaly S φhat φtilde).comp T := by
  ext x ℓ
  simp only [coframeAnomaly_apply, LinearMap.add_apply, LinearMap.comp_apply, Pi.add_apply]
  ring

/-! ## The determinant-line survivor -/

theorem coframe_linearIndependent {u : F → C} {φ : F → (C →ₗ[k] k)}
    (hu : CoframeNormalized u φ) : LinearIndependent k u := by
  rw [Fintype.linearIndependent_iff]
  intro a ha ℓ
  have h1 := coframeNormalized_sum hu a ℓ
  rw [ha, map_zero] at h1
  have hz : -a ℓ = 0 := h1.symm
  linear_combination -hz

/-- The anomaly read through the marked ordered basis of the source span. -/
noncomputable def coframeAnomalyMatrix (T : C →ₗ[k] E) (φ : F → (C →ₗ[k] k))
    (φhat : F → (E →ₗ[k] k)) (u : F → C) : (F → k) →ₗ[k] (F → k) :=
  (coframeAnomaly T φ φhat).comp (Fintype.linearCombination k u)

/-- **Theorem 5.1.**  In the matched ordered bases the anomaly is the identity matrix. -/
theorem coframeAnomalyMatrix_eq_id {T : C →ₗ[k] E} {φ : F → (C →ₗ[k] k)}
    {φhat : F → (E →ₗ[k] k)} {u : F → C} {Be : Submodule k E}
    (hu : CoframeNormalized u φ) (hTu : ∀ p, T (u p) ∈ Be)
    (hφhat : ∀ ℓ, Be ≤ LinearMap.ker (φhat ℓ)) :
    coframeAnomalyMatrix T φ φhat u = LinearMap.id := by
  classical
  ext a ℓ
  simp only [coframeAnomalyMatrix, LinearMap.comp_apply, Fintype.linearCombination_apply,
    map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.id_apply,
    coframeAnomaly_marked hu hTu hφhat, Pi.single_apply]
  rw [Finset.sum_eq_single ℓ]
  · simp
  · intro p _ hp
    simp [Ne.symm hp]
  · intro h
    exact absurd (Finset.mem_univ ℓ) h

/-- The determinant of the anomaly in matched ordered bases is `1`. -/
theorem det_coframeAnomalyMatrix {T : C →ₗ[k] E} {φ : F → (C →ₗ[k] k)}
    {φhat : F → (E →ₗ[k] k)} {u : F → C} {Be : Submodule k E}
    (hu : CoframeNormalized u φ) (hTu : ∀ p, T (u p) ∈ Be)
    (hφhat : ∀ ℓ, Be ≤ LinearMap.ker (φhat ℓ)) :
    LinearMap.det (coframeAnomalyMatrix T φ φhat u) = 1 := by
  rw [coframeAnomalyMatrix_eq_id hu hTu hφhat, LinearMap.det_id]

/-- **The determinant-line isomorphism** `(VOD.6)`.  The top exterior power of the anomaly read in
matched ordered bases is the identity of the determinant line, in particular bijective. -/
theorem exteriorPower_coframeAnomalyMatrix {T : C →ₗ[k] E} {φ : F → (C →ₗ[k] k)}
    {φhat : F → (E →ₗ[k] k)} {u : F → C} {Be : Submodule k E}
    (hu : CoframeNormalized u φ) (hTu : ∀ p, T (u p) ∈ Be)
    (hφhat : ∀ ℓ, Be ≤ LinearMap.ker (φhat ℓ)) :
    exteriorPower.map (Fintype.card F) (coframeAnomalyMatrix T φ φhat u) = LinearMap.id := by
  rw [coframeAnomalyMatrix_eq_id hu hTu hφhat, exteriorPower.map_id]

end CoframeAnomaly

/-! ## The algebra-map derivation defect -/

section DerivationDefect

variable {k A B : Type*} [Field k] [Ring A] [Algebra k A] [Ring B] [Algebra k B]

/-- The trace-derivation one-cochain `(VOD.7)`. -/
def traceDerCochain (τ : A →ₗ[k] k) (D : A →ₗ[k] A) : A → A → k := fun a b => τ (a * D b)

/-- Antisymmetry of the trace-derivation cochain when the trace kills the derivation. -/
theorem traceDerCochain_antisymm {τ : A →ₗ[k] k} {D : A →ₗ[k] A}
    (htr : ∀ x y : A, τ (x * y) = τ (y * x))
    (hleib : ∀ x y : A, D (x * y) = D x * y + x * D y)
    (hkill : ∀ x, τ (D x) = 0) (a b : A) :
    traceDerCochain τ D a b + traceDerCochain τ D b a = 0 := by
  have h : τ (D (a * b)) = 0 := hkill (a * b)
  rw [hleib a b, map_add] at h
  have hswap : τ (D a * b) = τ (b * D a) := htr _ _
  simp only [traceDerCochain]
  rw [hswap] at h
  linear_combination h

/-- The derivation-transport defect `(VOD.8)`. -/
noncomputable def derDefect (DA : A →ₗ[k] A) (DB : B →ₗ[k] B) (f : A →ₐ[k] B) : A →ₗ[k] B :=
  DB.comp f.toLinearMap - (f.toLinearMap).comp DA

@[simp] theorem derDefect_apply (DA : A →ₗ[k] A) (DB : B →ₗ[k] B) (f : A →ₐ[k] B) (b : A) :
    derDefect DA DB f b = DB (f b) - f (DA b) := rfl

/-- **Proposition 6.1.**  The coframe defect of a trace-preserving algebra map is the trace
pairing against its derivation-transport defect. -/
theorem traceDerCochain_defect {τA : A →ₗ[k] k} {τB : B →ₗ[k] k}
    (DA : A →ₗ[k] A) (DB : B →ₗ[k] B) (f : A →ₐ[k] B)
    (hf : ∀ x : A, τB (f x) = τA x) (a b : A) :
    traceDerCochain τB DB (f a) (f b) - traceDerCochain τA DA a b
      = τB (f a * derDefect DA DB f b) := by
  simp only [traceDerCochain, derDefect_apply, mul_sub, map_sub]
  have h : τA (a * DA b) = τB (f (a * DA b)) := (hf (a * DA b)).symm
  rw [h, map_mul f]

end DerivationDefect

/-! ## The Arakelov graph split countermodel -/

section ArakelovSplit

variable {k : Type*} [Field k] {F : Type*} [Fintype F] [DecidableEq F]
variable (lam : F → k)

/-- The weighted total functional `L`. -/
noncomputable def arakelovL : (F → k) →ₗ[k] k :=
  ∑ p, lam p • (LinearMap.proj p : (F → k) →ₗ[k] k)

omit [DecidableEq F] in
theorem arakelovL_apply (d : F → k) : arakelovL lam d = ∑ p, lam p * d p := by
  simp [arakelovL]

/-- The graph inclusion `(VOD.10)`. -/
noncomputable def arakelovB : (F → k) →ₗ[k] ((F → k) × k) :=
  LinearMap.prod LinearMap.id (-arakelovL lam)

omit [DecidableEq F] in
@[simp] theorem arakelovB_apply (d : F → k) : arakelovB lam d = (d, -arakelovL lam d) := rfl

/-- The trace functional `(VOD.10a)`. -/
noncomputable def arakelovTr : ((F → k) × k) →ₗ[k] k :=
  (arakelovL lam).comp (LinearMap.fst k (F → k) k) + LinearMap.snd k (F → k) k

omit [DecidableEq F] in
@[simp] theorem arakelovTr_apply (z : (F → k) × k) :
    arakelovTr lam z = arakelovL lam z.1 + z.2 := rfl

theorem arakelovTr_comp_arakelovB : (arakelovTr lam).comp (arakelovB lam) = 0 := by
  ext d
  simp

omit [DecidableEq F] in
/-- **Exactness of the graph sequence** `(VOD.10b)`. -/
theorem arakelov_ker_eq_range :
    LinearMap.ker (arakelovTr lam) = LinearMap.range (arakelovB lam) := by
  ext z
  constructor
  · intro hz
    refine ⟨z.1, ?_⟩
    have hz' : arakelovL lam z.1 + z.2 = 0 := hz
    refine Prod.ext rfl ?_
    show -arakelovL lam z.1 = z.2
    linear_combination -hz'
  · rintro ⟨d, rfl⟩
    show arakelovL lam d + -arakelovL lam d = 0
    ring

/-- The graph inclusion is split injective. -/
theorem arakelov_fst_comp_arakelovB :
    (LinearMap.fst k (F → k) k).comp (arakelovB lam) = LinearMap.id := by
  ext d
  simp

omit [DecidableEq F] in
/-- The trace is split surjective. -/
theorem arakelovTr_comp_section :
    (arakelovTr lam).comp ((LinearMap.inr k (F → k) k)) = LinearMap.id := by
  ext
  simp [arakelovL]

/-- **The graph carries no coframe anomaly** `(VOD.11)`.  Every coordinate reporter extends along
the graph inclusion, so the anomaly vanishes. -/
theorem arakelov_coframeAnomaly_eq_zero :
    coframeAnomaly (arakelovB lam) (fun p => (LinearMap.proj p : (F → k) →ₗ[k] k))
        (fun p => (LinearMap.proj p : (F → k) →ₗ[k] k).comp (LinearMap.fst k (F → k) k))
      = 0 := by
  refine coframeAnomaly_eq_zero_of_preserved ?_
  intro p
  ext d
  simp

end ArakelovSplit

end HTGeometry.ConstraintMotiveRelativity

import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.QuestionRelationBalance

/-!
# Source-word filtration and the fixed-action selection no-go

For a filtered algebra `A` acting on a module `M` and a seed subspace `V ⊆ M`, put

`P n = A_{≤n} ⊗ V`,  `ev(a ⊗ v) = a • v`,  `R n = ker ev ∩ P n`,  `K n = A_{≤n} V`.

Then `P n / R n ≅ K n`, the relation spaces intersect back exactly (`R m ∩ P n = R n` for `n ≤ m`),
the killed-old-freedom term of the associated question–relation event vanishes, and the graded
budget

`(dim R n − dim R (n−1)) + (dim K n − dim K (n−1)) = dim (A_{≤n}/A_{≤n−1}) · dim V`

holds.  Under the degree-one generation law `A_{≤n+1} = A_{≤n} + A_{≤1} A_{≤n}` a single plateau
`K (n+1) = K n` forces permanent stabilization `K n = A V`, with stabilization depth at most
`dim A V − dim V`.  The degree-one hypothesis is necessary: a filtration with a generator in
degree two has `K 0 = K 1` while `K 2` is strictly larger.

Consequently, longer words under one fixed action never perform selection.
-/

namespace HTGeometry.ConstraintRelativity

open Submodule LinearMap Module TensorProduct

/-! ## Filtered algebras -/

/-- An increasing, multiplicative, exhaustive filtration of a `k`-algebra by `k`-subspaces. -/
structure AlgebraFiltration (k A : Type*) [CommRing k] [Ring A] [Algebra k A] where
  /-- The filtration subspaces `A_{≤n}`. -/
  fil : ℕ → Submodule k A
  /-- The filtration is increasing. -/
  mono : Monotone fil
  /-- The unit lies in degree zero. -/
  one_mem : (1 : A) ∈ fil 0
  /-- The filtration is multiplicative. -/
  mul_le : ∀ m n, fil m * fil n ≤ fil (m + n)
  /-- The filtration is exhaustive. -/
  iSup_eq : ⨆ n, fil n = ⊤

namespace AlgebraFiltration

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A] (F : AlgebraFiltration k A)

theorem one_le_fil (n : ℕ) : (1 : Submodule k A) ≤ F.fil n :=
  Submodule.one_le.2 (F.mono (Nat.zero_le n) F.one_mem)

theorem directed : Directed (· ≤ ·) F.fil := fun m n =>
  ⟨max m n, F.mono (le_max_left m n), F.mono (le_max_right m n)⟩

/-- Every algebra element lies in some filtration stage. -/
theorem exists_mem (a : A) : ∃ n, a ∈ F.fil n := by
  have : a ∈ (⊤ : Submodule k A) := trivial
  rw [← F.iSup_eq, Submodule.mem_iSup_of_directed _ F.directed] at this
  exact this

end AlgebraFiltration

/-! ## Word spaces and the plateau theorem -/

section WordSpace

variable {k A M : Type*} [CommRing k] [Ring A] [Algebra k A] [AddCommGroup M] [Module k M]
  [Module A M] [IsScalarTower k A M]

/-- Associativity of the filtration product acting on a submodule. -/
theorem mul_smul_submodule (I J : Submodule k A) (N : Submodule k M) :
    (I * J) • N = I • (J • N) :=
  Submodule.smul_assoc I J N

/-- The word space `K n = A_{≤n} V` reachable from the seed `V` in at most `n` steps. -/
def wordSpace (F : AlgebraFiltration k A) (V : Submodule k M) (n : ℕ) : Submodule k M :=
  F.fil n • V

variable (F : AlgebraFiltration k A) (V : Submodule k M)

/-- The full reachable space `A V`, as the union of the word spaces. -/
def fullWordSpace : Submodule k M := ⨆ n, wordSpace F V n

theorem seed_le_wordSpace (n : ℕ) : V ≤ wordSpace F V n :=
  le_trans (le_of_eq (Submodule.one_smul V).symm)
    (Submodule.smul_mono_left (F.one_le_fil n))

theorem wordSpace_mono : Monotone (wordSpace F V) := fun _ _ h =>
  Submodule.smul_mono_left (F.mono h)

theorem wordSpace_le_full (n : ℕ) : wordSpace F V n ≤ fullWordSpace F V :=
  le_iSup (wordSpace F V) n

theorem seed_le_full : V ≤ fullWordSpace F V :=
  le_trans (seed_le_wordSpace F V 0) (wordSpace_le_full F V 0)

/-- The full reachable space is `A V`. -/
theorem fullWordSpace_eq_top_smul : fullWordSpace F V = (⊤ : Submodule k A) • V := by
  rw [fullWordSpace, ← F.iSup_eq, Submodule.iSup_smul]
  rfl

/-- A step of the word filtration adds exactly the degree-one translates. -/
theorem wordSpace_succ (hdeg : ∀ n, F.fil (n + 1) = F.fil n ⊔ F.fil 1 * F.fil n) (n : ℕ) :
    wordSpace F V (n + 1) = wordSpace F V n ⊔ F.fil 1 • wordSpace F V n := by
  rw [wordSpace, hdeg n, Submodule.sup_smul, mul_smul_submodule]
  rfl

/-- Under degree-one generation, a stage stable under the degree-one action is stable under the
whole algebra. -/
theorem smul_le_of_degreeOne_stable
    (hdeg : ∀ n, F.fil (n + 1) = F.fil n ⊔ F.fil 1 * F.fil n) {N : Submodule k M}
    (hN : F.fil 1 • N ≤ N) : ∀ m, F.fil m • N ≤ N := by
  intro m
  induction m with
  | zero => exact le_trans (Submodule.smul_mono_left (F.mono (Nat.zero_le 1))) hN
  | succ m ih =>
      rw [hdeg m, Submodule.sup_smul, mul_smul_submodule]
      exact sup_le ih (le_trans (Submodule.smul_mono le_rfl ih) hN)

/-- **Degree-one plateau theorem.**  Under `A_{≤n+1} = A_{≤n} + A_{≤1} A_{≤n}`, a single plateau
`K (n+1) = K n` forces `K n = A V`, and conversely. -/
theorem wordSpace_succ_eq_iff (hdeg : ∀ n, F.fil (n + 1) = F.fil n ⊔ F.fil 1 * F.fil n) (n : ℕ) :
    wordSpace F V (n + 1) = wordSpace F V n ↔ wordSpace F V n = fullWordSpace F V := by
  constructor
  · intro hplat
    have hstab : F.fil 1 • wordSpace F V n ≤ wordSpace F V n := by
      rw [wordSpace_succ F V hdeg n] at hplat
      exact le_trans le_sup_right (le_of_eq hplat)
    have hall : ∀ m, F.fil m • wordSpace F V n ≤ wordSpace F V n :=
      smul_le_of_degreeOne_stable F hdeg hstab
    refine le_antisymm (wordSpace_le_full F V n) ?_
    rw [fullWordSpace_eq_top_smul]
    refine le_trans (Submodule.smul_mono le_rfl (seed_le_wordSpace F V n)) ?_
    rw [← F.iSup_eq, Submodule.iSup_smul]
    exact iSup_le hall
  · intro hfull
    refine le_antisymm ?_ (wordSpace_mono F V (Nat.le_succ n))
    rw [hfull]
    exact wordSpace_le_full F V (n + 1)

/-- Before stabilization the word space grows strictly. -/
theorem wordSpace_lt_succ (hdeg : ∀ n, F.fil (n + 1) = F.fil n ⊔ F.fil 1 * F.fil n) {n : ℕ}
    (hne : wordSpace F V n ≠ fullWordSpace F V) : wordSpace F V n < wordSpace F V (n + 1) :=
  lt_of_le_of_ne (wordSpace_mono F V (Nat.le_succ n))
    (fun h => hne ((wordSpace_succ_eq_iff F V hdeg n).1 h.symm))

end WordSpace

/-! ## Finite stabilization depth -/

section StabilizationDepth

variable {k A M : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup M] [Module k M]
  [Module A M] [IsScalarTower k A M]
variable (F : AlgebraFiltration k A) (V : Submodule k M)

/-- Strictly growing word spaces have strictly growing dimension. -/
theorem finrank_wordSpace_succ [FiniteDimensional k (fullWordSpace F V)]
    (hdeg : ∀ n, F.fil (n + 1) = F.fil n ⊔ F.fil 1 * F.fil n) {n : ℕ}
    (hne : wordSpace F V n ≠ fullWordSpace F V) :
    finrank k (wordSpace F V n) < finrank k (wordSpace F V (n + 1)) := by
  have hfin : FiniteDimensional k (wordSpace F V (n + 1)) :=
    Submodule.finiteDimensional_of_le (wordSpace_le_full F V (n + 1))
  exact Submodule.finrank_lt_finrank_of_lt (wordSpace_lt_succ F V hdeg hne)

/-- Until stabilization, the word space has dimension at least `dim V + n`. -/
theorem finrank_wordSpace_ge [FiniteDimensional k (fullWordSpace F V)]
    (hdeg : ∀ n, F.fil (n + 1) = F.fil n ⊔ F.fil 1 * F.fil n) :
    ∀ n : ℕ, (∀ m, m < n → wordSpace F V m ≠ fullWordSpace F V) →
      finrank k V + n ≤ finrank k (wordSpace F V n) := by
  intro n
  induction n with
  | zero =>
      intro _
      have hfin : FiniteDimensional k (wordSpace F V 0) :=
        Submodule.finiteDimensional_of_le (wordSpace_le_full F V 0)
      simp only [Nat.add_zero]
      exact Submodule.finrank_mono (seed_le_wordSpace F V 0)
  | succ n ih =>
      intro hlt
      have hprev := ih fun m hm => hlt m (Nat.lt_succ_of_lt hm)
      have hstep := finrank_wordSpace_succ F V hdeg (hlt n (Nat.lt_succ_self n))
      omega

/-- **Finite stabilization depth.**  If `A V` is finite dimensional, the word space stabilizes at
depth at most `dim A V − dim V`. -/
theorem exists_wordSpace_eq_full [FiniteDimensional k (fullWordSpace F V)]
    (hdeg : ∀ n, F.fil (n + 1) = F.fil n ⊔ F.fil 1 * F.fil n) :
    ∃ n ≤ finrank k (fullWordSpace F V) - finrank k V, wordSpace F V n = fullWordSpace F V := by
  classical
  set D := finrank k (fullWordSpace F V) with hD
  set r := finrank k V with hr
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hne : ∀ m, m < D - r + 1 → wordSpace F V m ≠ fullWordSpace F V := by
    intro m hm
    exact hcon m (by omega)
  have hge := finrank_wordSpace_ge F V hdeg (D - r + 1) hne
  have hfinV : FiniteDimensional k V :=
    Submodule.finiteDimensional_of_le (seed_le_full F V)
  have hrD : r ≤ D := Submodule.finrank_mono (seed_le_full F V)
  have hle : finrank k (wordSpace F V (D - r + 1)) ≤ D :=
    Submodule.finrank_mono (wordSpace_le_full F V _)
  omega

end StabilizationDepth

/-! ## The presentation spaces and the exact word budget -/

section Presentation

variable {k A M : Type*} [CommRing k] [Ring A] [Algebra k A] [AddCommGroup M] [Module k M]

section NoAction

variable (F : AlgebraFiltration k A) (V : Submodule k M)

/-- The presentation space `P n = A_{≤n} ⊗ V`, realized inside `A ⊗ V`. -/
noncomputable def presentation (n : ℕ) : Submodule k (A ⊗[k] V) :=
  LinearMap.range (LinearMap.rTensor V (F.fil n).subtype)

theorem presentation_mono : Monotone (presentation F V) := by
  intro m n h
  rintro x ⟨y, rfl⟩
  refine ⟨LinearMap.rTensor V (Submodule.inclusion (F.mono h)) y, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  rfl

end NoAction

variable [Module A M] [IsScalarTower k A M]

/-- The action of `A` on the seed, as a `k`-bilinear map. -/
def seedAction (V : Submodule k M) : A →ₗ[k] (V →ₗ[k] M) where
  toFun a :=
    { toFun := fun v => a • (v : M)
      map_add' := fun x y => by simp [smul_add]
      map_smul' := fun c x => by
        simp only [Submodule.coe_smul, RingHom.id_apply]
        exact smul_comm a c (x : M) }
  map_add' a b := by ext v; simp [add_smul]
  map_smul' c a := by ext v; simp [smul_assoc]

/-- Evaluation `A ⊗ V → M`, `a ⊗ v ↦ a • v`. -/
noncomputable def wordEval (V : Submodule k M) : (A ⊗[k] V) →ₗ[k] M :=
  TensorProduct.lift (seedAction V)

@[simp]
theorem wordEval_tmul (V : Submodule k M) (a : A) (v : V) :
    wordEval V (a ⊗ₜ[k] v) = a • (v : M) := rfl

variable (F : AlgebraFiltration k A) (V : Submodule k M)

/-- The relation space `R n = ker ev ∩ P n`. -/
noncomputable def relationSpace (n : ℕ) : Submodule k (A ⊗[k] V) :=
  presentation F V n ⊓ LinearMap.ker (wordEval V)

theorem relationSpace_le_presentation (n : ℕ) : relationSpace F V n ≤ presentation F V n :=
  inf_le_left

/-- **The relation spaces intersect back exactly.**  `R m ∩ P n = R n` for `n ≤ m`; equivalently,
the killed-old-freedom term of the word event vanishes. -/
theorem relationSpace_inf_presentation {m n : ℕ} (h : n ≤ m) :
    relationSpace F V m ⊓ presentation F V n = relationSpace F V n := by
  rw [relationSpace, relationSpace, inf_right_comm,
    inf_eq_right.2 (presentation_mono F V h)]

/-- The word space is the image of the presentation space. -/
theorem map_wordEval_presentation (n : ℕ) :
    Submodule.map (wordEval V) (presentation F V n) = wordSpace F V n := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => exact Submodule.smul_mem_smul a.2 v.2
    | add y z hy hz =>
        simp only [map_add]
        exact Submodule.add_mem _ hy hz
  · refine Submodule.smul_le.2 fun a ha v hv => ?_
    exact ⟨LinearMap.rTensor V (F.fil n).subtype ((⟨a, ha⟩ : F.fil n) ⊗ₜ[k] (⟨v, hv⟩ : V)),
      ⟨_, rfl⟩, rfl⟩

/-- Evaluation descends to the quotient by the relation space. -/
noncomputable def wordEvalQ (n : ℕ) : ((A ⊗[k] V) ⧸ relationSpace F V n) →ₗ[k] M :=
  Submodule.liftQ (relationSpace F V n) (wordEval V) inf_le_right

@[simp]
theorem wordEvalQ_mk (n : ℕ) (x : A ⊗[k] V) :
    wordEvalQ F V n (Submodule.Quotient.mk x) = wordEval V x := rfl

/-- **`P n / R n ≅ K n`.**  Evaluation identifies the image of the presentation space in the
quotient by its relations — that is, `P n / R n` — with the word space `K n`. -/
noncomputable def presentationQuotEquivWordSpace (n : ℕ) :
    (Submodule.map (relationSpace F V n).mkQ (presentation F V n)) ≃ₗ[k] wordSpace F V n := by
  have hinj : Function.Injective
      ((wordEvalQ F V n).domRestrict
        (Submodule.map (relationSpace F V n).mkQ (presentation F V n))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ hker
    obtain ⟨p, hp, rfl⟩ := hx
    have h0 : wordEval V p = 0 := hker
    have hmem : p ∈ relationSpace F V n := ⟨hp, h0⟩
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).2 hmem
  have hrange : LinearMap.range
      ((wordEvalQ F V n).domRestrict
        (Submodule.map (relationSpace F V n).mkQ (presentation F V n)))
      = wordSpace F V n := by
    rw [LinearMap.range_domRestrict, ← Submodule.map_comp]
    have hcomp : (wordEvalQ F V n).comp (relationSpace F V n).mkQ = wordEval V := by
      ext x; rfl
    rw [hcomp, map_wordEval_presentation]
  exact (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange)

/-- **The graded kernel identity.**  A presentation element of degree `n+1` evaluates into the
word space of degree `n` exactly when it lies in `R (n+1) + P n`. -/
theorem presentation_inf_comap_wordSpace (n : ℕ) :
    presentation F V (n + 1) ⊓ Submodule.comap (wordEval V) (wordSpace F V n)
      = relationSpace F V (n + 1) ⊔ presentation F V n := by
  refine le_antisymm ?_ ?_
  · intro p hp
    have hp1 : p ∈ presentation F V (n + 1) := hp.1
    have hp2 : wordEval V p ∈ wordSpace F V n := hp.2
    rw [← map_wordEval_presentation F V n] at hp2
    obtain ⟨q, hq, hqe⟩ := hp2
    have hsub : p - q ∈ relationSpace F V (n + 1) := by
      refine ⟨Submodule.sub_mem _ hp1 (presentation_mono F V (Nat.le_succ n) hq), ?_⟩
      simp [LinearMap.mem_ker, hqe]
    have hdecomp : p = (p - q) + q := by abel
    rw [hdecomp]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hsub) (Submodule.mem_sup_right hq)
  · refine sup_le (le_inf inf_le_left ?_) (le_inf (presentation_mono F V (Nat.le_succ n)) ?_)
    · intro x hx
      have hzero : wordEval V x = 0 := hx.2
      show wordEval V x ∈ wordSpace F V n
      rw [hzero]
      exact Submodule.zero_mem _
    · intro x hx
      show wordEval V x ∈ wordSpace F V n
      rw [← map_wordEval_presentation F V n]
      exact ⟨x, hx, rfl⟩

end Presentation

/-! ## The exact dimension budget -/

section BudgetNoAction

variable {k A M : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup M] [Module k M]
variable (F : AlgebraFiltration k A) (V : Submodule k M)

/-- The presentation space is the tensor product `A_{≤n} ⊗ V`. -/
noncomputable def presentationEquivTensor (n : ℕ) :
    (F.fil n ⊗[k] V) ≃ₗ[k] presentation F V n :=
  LinearEquiv.ofInjective (LinearMap.rTensor V (F.fil n).subtype)
    (Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _))

theorem finrank_presentation [FiniteDimensional k A] [FiniteDimensional k V] (n : ℕ) :
    finrank k (presentation F V n) = finrank k (F.fil n) * finrank k V := by
  rw [← (presentationEquivTensor F V n).finrank_eq, Module.finrank_tensorProduct]

end BudgetNoAction

section Budget

variable {k A M : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup M] [Module k M]
  [Module A M] [IsScalarTower k A M]
variable (F : AlgebraFiltration k A) (V : Submodule k M)

/-- **The word budget in one degree.**  The presentation space splits exactly into its relations
and the word space it presents. -/
theorem finrank_relationSpace_add_finrank_wordSpace [FiniteDimensional k A]
    [FiniteDimensional k V] (n : ℕ) :
    finrank k (relationSpace F V n) + finrank k (wordSpace F V n)
      = finrank k (F.fil n) * finrank k V := by
  have := finrank_map_add_finrank_inf_ker (wordEval V) (presentation F V n)
  rw [map_wordEval_presentation] at this
  rw [← finrank_presentation F V n, ← this, relationSpace]
  omega

/-- **The exact graded budget.**
`(dim R (n+1) − dim R n) + (dim K (n+1) − dim K n) = dim (A_{≤n+1}/A_{≤n}) · dim V`. -/
theorem finrank_budget [FiniteDimensional k A] [FiniteDimensional k V] (n : ℕ) :
    ((finrank k (relationSpace F V (n + 1)) : ℤ) - finrank k (relationSpace F V n))
        + ((finrank k (wordSpace F V (n + 1)) : ℤ) - finrank k (wordSpace F V n))
      = ((finrank k (F.fil (n + 1)) : ℤ) - finrank k (F.fil n)) * finrank k V := by
  have h1 : (finrank k (relationSpace F V (n + 1)) : ℤ) + finrank k (wordSpace F V (n + 1))
      = (finrank k (F.fil (n + 1)) : ℤ) * finrank k V := by
    exact_mod_cast congrArg (Nat.cast (R := ℤ))
      (finrank_relationSpace_add_finrank_wordSpace F V (n + 1))
  have h2 : (finrank k (relationSpace F V n) : ℤ) + finrank k (wordSpace F V n)
      = (finrank k (F.fil n) : ℤ) * finrank k V := by
    exact_mod_cast congrArg (Nat.cast (R := ℤ))
      (finrank_relationSpace_add_finrank_wordSpace F V n)
  linarith

end Budget

/-! ## Necessity of the degree-one hypothesis -/

section DegreeTwo

variable (k : Type*) [Field k]

/-- A filtration of `k × k` whose only generator sits in degree two. -/
def degreeTwoFiltration : AlgebraFiltration k (k × k) where
  fil n := if n ≤ 1 then 1 else ⊤
  mono := by
    intro m n h
    by_cases hm : m ≤ 1
    · by_cases hn : n ≤ 1 <;> simp [hm, hn, le_top]
    · have hn : ¬ n ≤ 1 := fun h' => hm (le_trans h h')
      simp [hm, hn]
  one_mem := by simp [Submodule.one_le.symm]
  mul_le := by
    intro m n
    by_cases hmn : m + n ≤ 1
    · have hm : m ≤ 1 := by omega
      have hn : n ≤ 1 := by omega
      simp only [hm, hn, hmn, if_pos]
      rw [one_mul]
    · simp [hmn, le_top]
  iSup_eq := le_antisymm le_top (le_iSup_of_le 2 (by simp))

@[simp]
theorem degreeTwoFiltration_fil_of_le (n : ℕ) (h : n ≤ 1) :
    (degreeTwoFiltration k).fil n = 1 := by
  simp [degreeTwoFiltration, h]

@[simp]
theorem degreeTwoFiltration_fil_of_gt (n : ℕ) (h : ¬ n ≤ 1) :
    (degreeTwoFiltration k).fil n = ⊤ := by
  simp [degreeTwoFiltration, h]

/-- **The degree-one hypothesis is necessary.**  With a degree-two generator the word space has a
plateau at `n = 0` and grows again at `n = 2`, so a single plateau does not force stabilization. -/
theorem degreeTwo_plateau_not_stable :
    wordSpace (degreeTwoFiltration k) (1 : Submodule k (k × k)) 0
        = wordSpace (degreeTwoFiltration k) (1 : Submodule k (k × k)) 1 ∧
      wordSpace (degreeTwoFiltration k) (1 : Submodule k (k × k)) 1
        < wordSpace (degreeTwoFiltration k) (1 : Submodule k (k × k)) 2 := by
  have h0 : wordSpace (degreeTwoFiltration k) (1 : Submodule k (k × k)) 0 = 1 := by
    rw [wordSpace, degreeTwoFiltration_fil_of_le k 0 (by omega), Submodule.one_smul]
  have h1 : wordSpace (degreeTwoFiltration k) (1 : Submodule k (k × k)) 1 = 1 := by
    rw [wordSpace, degreeTwoFiltration_fil_of_le k 1 le_rfl, Submodule.one_smul]
  have h2 : wordSpace (degreeTwoFiltration k) (1 : Submodule k (k × k)) 2 = ⊤ := by
    rw [wordSpace, degreeTwoFiltration_fil_of_gt k 2 (by omega)]
    exact le_antisymm le_top (fun x _ => by
      have : x = x • (1 : k × k) := by rw [smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem_smul (Submodule.mem_top) (Submodule.one_le.1 le_rfl))
  refine ⟨by rw [h0, h1], ?_⟩
  rw [h1, h2]
  refine lt_of_le_of_ne le_top fun hcon => ?_
  have hrank : finrank k (1 : Submodule k (k × k)) = 1 := by
    rw [Submodule.one_eq_span]
    exact finrank_span_singleton (by simp)
  rw [hcon] at hrank
  simp only [finrank_top, Module.finrank_prod, Module.finrank_self] at hrank
  omega

end DegreeTwo

/-! ## The card's first consequence -/

section NoSelection

variable {k A M : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup M] [Module k M]
  [Module A M] [IsScalarTower k A M]

/-- **Card consequence 1.**  Longer words under one fixed action never perform selection: every
stage has vanishing killed-freedom, one plateau of the reachable space is permanent, and the
reachable space is exhausted by depth `dim AV − dim V`.  A nonzero killed-freedom term therefore
requires changing the action, module, quotient, admission domain or source law — not more words. -/
theorem longer_words_never_select (F : AlgebraFiltration k A) (V : Submodule k M)
    [FiniteDimensional k (fullWordSpace F V)]
    (hdeg : ∀ n, F.fil (n + 1) = F.fil n ⊔ F.fil 1 * F.fil n) :
    (∀ m n : ℕ, n ≤ m → relationSpace F V m ⊓ presentation F V n = relationSpace F V n)
      ∧ (∀ n : ℕ, wordSpace F V (n + 1) = wordSpace F V n ↔ wordSpace F V n = fullWordSpace F V)
      ∧ ∃ n ≤ Module.finrank k (fullWordSpace F V) - Module.finrank k V,
          wordSpace F V n = fullWordSpace F V :=
  ⟨fun _ _ h => relationSpace_inf_presentation F V h, wordSpace_succ_eq_iff F V hdeg,
    exists_wordSpace_eq_full F V hdeg⟩

end NoSelection

end HTGeometry.ConstraintRelativity

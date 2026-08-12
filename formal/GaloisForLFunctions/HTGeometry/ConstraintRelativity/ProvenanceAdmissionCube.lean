import Mathlib

/-!
# Provenance admission: the flat completion cube and the connecting law

Inserting formal completion operators between transports is flat.  Given monotone transports
`T_i` between posets and closure operators `c_i`, the vertex obtained by inserting the closures
indexed by a set `S` is monotone in `S`, so all insertion choices assemble into one coherent
Boolean cube; in the free abelian group on the target poset the edge differences telescope, so
every monotone path from the empty insertion to the full insertion has the same sum.  Formal
completion therefore cannot create higher holonomy on its own.

Curvature appears only when provenance refuses cells.  For a subcomplex `S ⊆ R` — source-admitted
cochains inside formal ones — the admission-curvature group

`E^k(R,S) = (d R^{k-1} ∩ S^k) / d S^{k-1}`

is canonically the kernel of `H^k(S) → H^k(R)`, that is the image of the connecting map from
`H^{k-1}(R/S)`.  A class is zero exactly when the formally exact, source-admitted cochain has a
source-admitted primitive.  Two countermodels show the group is genuinely nonzero: a two-term
complex over a field where the completed theory has vanishing `H^1` while the admitted theory has
`H^1 = k`, and the analytic model `ℓ¹ ⊂ ℓ²` where the harmonic sequence is an `ℓ²`-boundary with no
`ℓ¹` primitive.
-/

noncomputable section

namespace HTGeometry.ConstraintRelativity

/-! ## The closure-insertion cube -/

section ClosureCube

variable {P : ℕ → Type*} [∀ i, Preorder (P i)]

/-- **Card `(2.1)`.**  The stage-`m` value of the transport chain with the closures indexed by `S`
inserted. -/
def closureCubeStage (T : ∀ i : ℕ, P i → P (i + 1)) (c : ∀ i : ℕ, P i → P i)
    (S : Finset ℕ) (x : P 0) : (m : ℕ) → P m
  | 0 => x
  | m + 1 =>
      if (m + 1) ∈ S then c (m + 1) (T m (closureCubeStage T c S x m))
      else T m (closureCubeStage T c S x m)

omit [∀ i, Preorder (P i)] in
@[simp] theorem closureCubeStage_zero (T : ∀ i : ℕ, P i → P (i + 1)) (c : ∀ i : ℕ, P i → P i)
    (S : Finset ℕ) (x : P 0) : closureCubeStage T c S x 0 = x := rfl

omit [∀ i, Preorder (P i)] in
theorem closureCubeStage_succ (T : ∀ i : ℕ, P i → P (i + 1)) (c : ∀ i : ℕ, P i → P i)
    (S : Finset ℕ) (x : P 0) (m : ℕ) :
    closureCubeStage T c S x (m + 1) =
      if (m + 1) ∈ S then c (m + 1) (T m (closureCubeStage T c S x m))
      else T m (closureCubeStage T c S x m) := rfl

/-- **Theorem 2.1.**  Inserting more closures never decreases the stage value. -/
theorem closureCubeStage_mono {T : ∀ i : ℕ, P i → P (i + 1)} (hT : ∀ i, Monotone (T i))
    {c : ∀ i : ℕ, P i → P i} (hc : ∀ i, Monotone (c i)) (hcl : ∀ (i : ℕ) (y : P i), y ≤ c i y)
    {S S' : Finset ℕ} (hSS : S ⊆ S') (x : P 0) (m : ℕ) :
    closureCubeStage T c S x m ≤ closureCubeStage T c S' x m := by
  induction m with
  | zero => exact le_refl _
  | succ m ih =>
    rw [closureCubeStage_succ, closureCubeStage_succ]
    have hstep : T m (closureCubeStage T c S x m) ≤ T m (closureCubeStage T c S' x m) :=
      hT m ih
    by_cases hS : (m + 1) ∈ S
    · rw [if_pos hS, if_pos (hSS hS)]
      exact hc (m + 1) hstep
    · rw [if_neg hS]
      by_cases hS' : (m + 1) ∈ S'
      · rw [if_pos hS']
        exact hstep.trans (hcl (m + 1) _)
      · rw [if_neg hS']
        exact hstep

/-- **Card `(2.1)`.**  The cube vertex: the transport chain with the closures indexed by `S`
inserted, and the terminal closure always applied. -/
def closureCubeVertex (T : ∀ i : ℕ, P i → P (i + 1)) (c : ∀ i : ℕ, P i → P i)
    (S : Finset ℕ) (x : P 0) (n : ℕ) : P n :=
  c n (closureCubeStage T c S x n)

/-- **Theorem 2.1, card `(2.2)`.**  The assignment `S ↦ x_S` is monotone from the Boolean lattice
to `P n`. -/
theorem closureCubeVertex_mono {T : ∀ i : ℕ, P i → P (i + 1)} (hT : ∀ i, Monotone (T i))
    {c : ∀ i : ℕ, P i → P i} (hc : ∀ i, Monotone (c i)) (hcl : ∀ (i : ℕ) (y : P i), y ≤ c i y)
    {S S' : Finset ℕ} (hSS : S ⊆ S') (x : P 0) (n : ℕ) :
    closureCubeVertex T c S x n ≤ closureCubeVertex T c S' x n :=
  hc n (closureCubeStage_mono hT hc hcl hSS x n)

omit [∀ i, Preorder (P i)] in
/-- **Theorem 2.1.**  Every cube vertex is closed. -/
theorem closureCubeVertex_closed (T : ∀ i : ℕ, P i → P (i + 1)) {c : ∀ i : ℕ, P i → P i}
    (hidem : ∀ (i : ℕ) (y : P i), c i (c i y) = c i y) (S : Finset ℕ) (x : P 0) (n : ℕ) :
    c n (closureCubeVertex T c S x n) = closureCubeVertex T c S x n :=
  hidem n _

end ClosureCube

/-! ## The additive Bianchi law on the cube -/

section Bianchi

variable {P : Type*}

/-- **Card `(2.3)`.**  The oriented edge of the insertion cube in the free abelian group. -/
def provenanceEdge (a b : P) : FreeAbelianGroup P :=
  FreeAbelianGroup.of b - FreeAbelianGroup.of a

@[simp] theorem provenanceEdge_self (a : P) : provenanceEdge a a = 0 := by
  rw [provenanceEdge, sub_self]

/-- Edges telescope. -/
theorem provenanceEdge_trans (a b c : P) :
    provenanceEdge a b + provenanceEdge b c = provenanceEdge a c := by
  rw [provenanceEdge, provenanceEdge, provenanceEdge]
  abel

/-- **Proposition 2.2, card `(2.4)`.**  Every square face of the cube obeys the additive Bianchi
law. -/
theorem provenanceEdge_square (x xi xj xij : P) :
    provenanceEdge x xi + provenanceEdge xi xij =
      provenanceEdge x xj + provenanceEdge xj xij := by
  rw [provenanceEdge_trans, provenanceEdge_trans]

/-- **Proposition 2.2, card `(2.5)`.**  The sum along any monotone path is the difference of its
endpoints, so the cube is flat. -/
theorem provenanceEdge_path (v : ℕ → P) (m : ℕ) :
    ∑ i ∈ Finset.range m, provenanceEdge (v i) (v (i + 1)) = provenanceEdge (v 0) (v m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, provenanceEdge_trans]

end Bianchi

/-! ## The admission-curvature group -/

section Admission

variable {A : Type*} [Ring A]
variable {Mm M0 M1 M2 : Type*}
variable [AddCommGroup Mm] [Module A Mm] [AddCommGroup M0] [Module A M0]
variable [AddCommGroup M1] [Module A M1] [AddCommGroup M2] [Module A M2]
variable (d0 : Mm →ₗ[A] M0) (d1 : M0 →ₗ[A] M1) (d2 : M1 →ₗ[A] M2)
variable (S0 : Submodule A M0) (S1 : Submodule A M1)

/-- Source-admitted boundaries in degree `k`. -/
def admittedBoundaries : Submodule A M1 := Submodule.map d1 S0

/-- Source-admitted cocycles in degree `k`. -/
def admittedCocycles : Submodule A M1 := LinearMap.ker d2 ⊓ S1

/-- **Card `(3.2)`, numerator.**  Formally exact, source-admitted cochains. -/
def primitiveEscape : Submodule A M1 := LinearMap.range d1 ⊓ S1

variable {d1 d2 S0 S1}

theorem admittedBoundaries_le_primitiveEscape (hdS : Submodule.map d1 S0 ≤ S1) :
    admittedBoundaries d1 S0 ≤ primitiveEscape d1 S1 := by
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨⟨s, rfl⟩, hdS ⟨s, hs, rfl⟩⟩

theorem primitiveEscape_le_admittedCocycles (hd : d2.comp d1 = 0) :
    primitiveEscape d1 S1 ≤ admittedCocycles d2 S1 := by
  rintro y ⟨⟨x, rfl⟩, hy1⟩
  exact ⟨by simpa using LinearMap.congr_fun hd x, hy1⟩

theorem admittedCocycles_le_cocycles : admittedCocycles d2 S1 ≤ LinearMap.ker d2 :=
  fun _ h => h.1

/-- **Card `(3.2)`.**  The admission-curvature group `E^k(R,S)`. -/
abbrev AdmissionCurvature (d1 : M0 →ₗ[A] M1)
    (S0 : Submodule A M0) (S1 : Submodule A M1) : Type _ :=
  primitiveEscape d1 S1 ⧸
    (admittedBoundaries d1 S0).comap (primitiveEscape d1 S1).subtype

/-- Source cohomology in degree `k`. -/
abbrev AdmittedCohomology (d1 : M0 →ₗ[A] M1) (d2 : M1 →ₗ[A] M2)
    (S0 : Submodule A M0) (S1 : Submodule A M1) : Type _ :=
  admittedCocycles d2 S1 ⧸
    (admittedBoundaries d1 S0).comap (admittedCocycles d2 S1).subtype

/-- Formal cohomology in degree `k`. -/
abbrev FormalCohomology (d1 : M0 →ₗ[A] M1) (d2 : M1 →ₗ[A] M2) : Type _ :=
  LinearMap.ker d2 ⧸ (LinearMap.range d1).comap (LinearMap.ker d2).subtype

/-- The comparison map from source to formal cohomology. -/
def admittedToFormal :
    AdmittedCohomology d1 d2 S0 S1 →ₗ[A] FormalCohomology d1 d2 :=
  Submodule.mapQ _ _ (Submodule.inclusion (admittedCocycles_le_cocycles (d2 := d2) (S1 := S1)))
    (by
      rintro _ ⟨s, hs, hsy⟩
      exact ⟨s, hsy⟩)

/-- The map from the admission-curvature group to source cohomology. -/
def admissionToCohomology (hd : d2.comp d1 = 0) :
    AdmissionCurvature d1 S0 S1 →ₗ[A] AdmittedCohomology d1 d2 S0 S1 :=
  Submodule.mapQ _ _ (Submodule.inclusion (primitiveEscape_le_admittedCocycles (S1 := S1) hd))
    (fun _ hy => hy)

@[simp] theorem admissionToCohomology_mk (hd : d2.comp d1 = 0) (y : primitiveEscape d1 S1) :
    admissionToCohomology (S0 := S0) hd (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨(y : M1), primitiveEscape_le_admittedCocycles (S1 := S1) hd y.2⟩ :=
  rfl

/-- **Theorem 3.1, card `(3.3)`, injectivity.** -/
theorem admissionToCohomology_injective (hd : d2.comp d1 = 0) :
    Function.Injective (admissionToCohomology (d1 := d1) (d2 := d2) (S0 := S0) (S1 := S1) hd) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro a ha
  induction a using Submodule.Quotient.induction_on with
  | H y =>
    rw [LinearMap.mem_ker, admissionToCohomology_mk, Submodule.Quotient.mk_eq_zero] at ha
    rw [Submodule.Quotient.mk_eq_zero]
    exact ha

/-- **Theorem 3.1, card `(3.3)`, exactness.**  The admission-curvature group is exactly the kernel
of the comparison from source to formal cohomology: a source class dies formally precisely when it
is a formal boundary. -/
theorem range_admissionToCohomology (hd : d2.comp d1 = 0) :
    LinearMap.range (admissionToCohomology (d1 := d1) (d2 := d2) (S0 := S0) (S1 := S1) hd) =
      LinearMap.ker (admittedToFormal (d1 := d1) (d2 := d2) (S0 := S0) (S1 := S1)) := by
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      rw [admissionToCohomology_mk, LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact y.2.1
  · intro z hz
    induction z using Submodule.Quotient.induction_on with
    | H y =>
      have hker : (Submodule.Quotient.mk
          (⟨(y : M1), admittedCocycles_le_cocycles (d2 := d2) (S1 := S1) y.2⟩ :
            LinearMap.ker d2) : FormalCohomology d1 d2) = 0 := hz
      rw [Submodule.Quotient.mk_eq_zero] at hker
      have hy1 : (y : M1) ∈ LinearMap.range d1 := hker
      refine ⟨Submodule.Quotient.mk ⟨(y : M1), ⟨hy1, y.2.2⟩⟩, ?_⟩
      rw [admissionToCohomology_mk]

/-- **Theorem 3.1, card `(3.3)` boxed.**  The canonical isomorphism
`E^k(R,S) ≅ ker(H^k(S) → H^k(R))`. -/
def admissionCurvatureEquiv (hd : d2.comp d1 = 0) :
    AdmissionCurvature d1 S0 S1 ≃ₗ[A]
      LinearMap.ker (admittedToFormal (d1 := d1) (d2 := d2) (S0 := S0) (S1 := S1)) :=
  (LinearEquiv.ofInjective _ (admissionToCohomology_injective (S0 := S0) (S1 := S1) hd)).trans
    (LinearEquiv.ofEq _ _ (range_admissionToCohomology (S0 := S0) (S1 := S1) hd))

/-- **Theorem 3.1, cards `(3.4)`, `(3.5)`.**  The connecting witness: a formal primitive whose
boundary is source-admitted determines a class in the admission-curvature group. -/
def escapeClass {ell : M0} (hell : d1 ell ∈ S1) : AdmissionCurvature d1 S0 S1 :=
  Submodule.Quotient.mk ⟨d1 ell, ⟨⟨ell, rfl⟩, hell⟩⟩

/-- **Theorem 3.1, equivalence `1 ↔ 2`.**  The class vanishes exactly when the boundary has a
source-admitted primitive. -/
theorem escapeClass_eq_zero_iff {ell : M0} (hell : d1 ell ∈ S1) :
    escapeClass (S0 := S0) hell = 0 ↔ ∃ s ∈ S0, d1 s = d1 ell := by
  rw [escapeClass, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨s, hs, hsd⟩
    exact ⟨s, hs, hsd⟩
  · rintro ⟨s, hs, hsd⟩
    exact ⟨s, hs, hsd⟩

/-- **Theorem 3.1, equivalence `1 ↔ 4`.**  Having a source-admitted primitive is equivalent to the
quotient class of the formal primitive lying in the image of formal cohomology.  The right-hand
side is the unfolded statement that `[ℓ̄] ∈ im(H^{k-1}(R) → H^{k-1}(Q))`. -/
theorem exists_admitted_primitive_iff (hd01 : d1.comp d0 = 0) {ell : M0} :
    (∃ s ∈ S0, d1 s = d1 ell) ↔
      ∃ rho : M0, d1 rho = 0 ∧ ∃ m : Mm, ell - rho - d0 m ∈ S0 := by
  constructor
  · rintro ⟨s, hs, hsd⟩
    refine ⟨ell - s, ?_, 0, ?_⟩
    · rw [map_sub, hsd, sub_self]
    · rw [map_zero, sub_zero]
      simpa using hs
  · rintro ⟨rho, hrho, m, hm⟩
    refine ⟨ell - rho - d0 m, hm, ?_⟩
    rw [map_sub, map_sub, hrho, sub_zero]
    have : d1 (d0 m) = 0 := by simpa using LinearMap.congr_fun hd01 m
    rw [this, sub_zero]

end Admission

/-! ## The smallest algebraic countermodel -/

section AlgebraicCountermodel

variable (k : Type*) [Field k]

/-- **Card `(4.1)`.**  In the two-term model `S = (0 → k)` inside `R = (k →id→ k)` the
admission-curvature group is the whole field. -/
def algebraicAdmissionCurvatureEquiv :
    AdmissionCurvature (LinearMap.id : k →ₗ[k] k) (⊥ : Submodule k k) (⊤ : Submodule k k) ≃ₗ[k]
      k :=
  (Submodule.quotEquivOfEqBot _ (by
      rw [Submodule.eq_bot_iff]
      rintro y hy
      have hy' : (y : k) ∈ admittedBoundaries (LinearMap.id : k →ₗ[k] k) (⊥ : Submodule k k) := hy
      obtain ⟨s, hs, hsy⟩ := hy'
      have hs0 : s = 0 := by simpa using hs
      subst hs0
      exact Subtype.ext (by simpa using hsy.symm))).trans
    ((LinearEquiv.ofEq _ ⊤ (by
        rw [primitiveEscape, LinearMap.range_id, top_inf_eq])).trans (Submodule.topEquiv))

/-- The formal theory has vanishing first cohomology. -/
theorem algebraicFormalCohomology_eq_bot :
    (⊤ : Submodule k (FormalCohomology (LinearMap.id : k →ₗ[k] k) (0 : k →ₗ[k] k))) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z _
  induction z using Submodule.Quotient.induction_on with
  | H y =>
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨(y : k), rfl⟩

end AlgebraicCountermodel

/-! ## The singular analytic countermodel -/

section AnalyticCountermodel

open scoped ENNReal

/-- The harmonic sequence. -/
def harmonicSeq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)

theorem summable_harmonicSeq_sq : Summable (fun n : ℕ => ‖harmonicSeq n‖ ^ (2 : ℝ)) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have hshift : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr hbase
    refine this.congr fun n => ?_
    push_cast
    ring_nf
  refine hshift.congr fun n => ?_
  rw [harmonicSeq, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [div_pow, one_pow]

theorem not_summable_harmonicSeq : ¬ Summable (fun n : ℕ => ‖harmonicSeq n‖ ^ (1 : ℝ)) := by
  intro hsum
  have hshift : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    refine hsum.congr fun n => ?_
    rw [harmonicSeq, Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    rw [← summable_nat_add_iff 1]
    refine hshift.congr fun n => ?_
    push_cast
    ring_nf
  exact Real.not_summable_one_div_natCast hbase

theorem harmonicSeq_memℓp_two : Memℓp (fun n : ℕ => (harmonicSeq n : ℝ)) 2 := by
  refine (memℓp_gen_iff (by norm_num)).mpr ?_
  simpa using summable_harmonicSeq_sq

theorem harmonicSeq_not_memℓp_one : ¬ Memℓp (fun n : ℕ => (harmonicSeq n : ℝ)) 1 := by
  intro hmem
  refine not_summable_harmonicSeq ?_
  simpa using (memℓp_gen_iff (p := 1) (by norm_num)).mp hmem

/-- The source-admitted `ℓ¹` sequences, as a submodule of the formal `ℓ²` cochains. -/
def ellOneInsideEllTwo : Submodule ℝ (lp (fun _ : ℕ => ℝ) 2) where
  carrier := {f | Memℓp (f : ∀ _ : ℕ, ℝ) 1}
  zero_mem' := zero_memℓp
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c _ hf => hf.const_smul c

/-- The harmonic sequence as a formal `ℓ²` cochain. -/
def harmonicEllTwo : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨fun n : ℕ => harmonicSeq n, harmonicSeq_memℓp_two⟩

/-- **Card `(5.1)`.**  The harmonic sequence is a formal `ℓ²` boundary with no source-admitted
`ℓ¹` primitive. -/
theorem harmonicEllTwo_notMem : harmonicEllTwo ∉ ellOneInsideEllTwo :=
  harmonicSeq_not_memℓp_one

/-- **Card `(5.1)`.**  Its admission-curvature class in `ℓ² / ℓ¹` is nonzero. -/
theorem harmonicAdmissionClass_ne_zero :
    escapeClass (d1 := (LinearMap.id : lp (fun _ : ℕ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2))
        (S0 := ellOneInsideEllTwo) (S1 := ⊤) (ell := harmonicEllTwo) (by trivial) ≠ 0 := by
  rw [Ne, escapeClass_eq_zero_iff]
  rintro ⟨s, hs, hsd⟩
  have hseq : s = harmonicEllTwo := hsd
  rw [hseq] at hs
  exact harmonicEllTwo_notMem hs

end AnalyticCountermodel

end HTGeometry.ConstraintRelativity

end
